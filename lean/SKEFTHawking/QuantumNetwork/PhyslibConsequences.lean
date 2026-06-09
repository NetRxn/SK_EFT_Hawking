import SKEFTHawking.QuantumNetwork.PhyslibBridge
import QuantumInfo.Finite.Entropy.SSA
import QuantumInfo.Finite.Entanglement

/-!
# Phase 6AM Wave 3 — consuming PhysLib: SSA on the repo representation + operational REE

Discharges the previously-walled downstream targets by consuming PhysLib (arXiv:2510.08672)
through the Wave-2 bridge (`PhyslibBridge.lean`):

* `repo_strong_subadditivity` / `repo_subadditivity` — strong / ordinary subadditivity of the von
  Neumann entropy stated on a **repo** density operator (bridged via `toMState`), with PhysLib's
  `Sᵥₙ_strong_subadditivity` / `Sᵥₙ_subadditivity` invoked in the proof body (P6-faithful).
* `relEntEntanglement` — the **relative entropy of entanglement** `E_R(ρ) = ⨅_{σ separable} 𝐃(ρ‖σ)`,
  built on PhysLib's `IsSeparable` (separable states = free states of entanglement theory) and
  `qRelativeEnt`.
* `relEntEntanglement_le_log_card_sub_entropy` — the **operational** upper bound
  `E_R(ρ) ≤ log d − S(ρ)` (= `𝐃(ρ‖ I/d)`, the relative entropy to the maximally-mixed state), via
  the concrete separable witness `MState.uniform`.
* `relEntEntanglement_MES_le_log_four` — a **concrete numeric bound** on the maximally entangled
  two-qubit state: `E_R(|Φ⁺⟩) ≤ log 4`. This is the falsifiable, operational REE the 6AK.2 PLOB
  surrogate / negativity ladder could only surrogate.

The DPI half of Wave 3 (`krausMap_sandwichedRenyi_DPI`) already shipped in `PhyslibBridge.lean`.

Note on `RelativeEntResource`: PhysLib's abstract `RelativeEntResource` requires a
`FreeStateTheory` typeclass instance, whose `free_convex` field is a PhysLib *TODO* and whose
`free_closed` is the (substantial, standalone) "separable set is closed" theorem. Those are needed
only to wrap this **same** quantity in the abstract typeclass machinery (for the regularized /
Stein's-lemma theory) — NOT for the operational bound, which the gate asks for. `relEntEntanglement`
here is the textbook relative entropy of entanglement (inf over separable states), computed
concretely; the upper bound needs only one separable witness (`iInf₂_le`), no closedness/convexity.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`, zero project-local axioms,
no `maxHeartbeats`. No dependence on PhysLib `Relative.lean`'s single sorry — `#print axioms` clean.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

variable {d₁ d₂ d₃ : Type*}
  [Fintype d₁] [DecidableEq d₁] [Fintype d₂] [DecidableEq d₂] [Fintype d₃] [DecidableEq d₃]

/-! ## Strong subadditivity on the repo's bridged representation -/

/-- **Strong subadditivity** of the von Neumann entropy for a repo tripartite density operator
(`IsDensityOperator` on `Matrix (d₁ × d₂ × d₃) …`), via PhysLib's `Sᵥₙ_strong_subadditivity`
invoked on the bridged `MState`. -/
theorem repo_strong_subadditivity (ρ : Matrix (d₁ × d₂ × d₃) (d₁ × d₂ × d₃) ℂ)
    (hρ : IsDensityOperator ρ) :
    Sᵥₙ (toMState ρ hρ) + Sᵥₙ ((toMState ρ hρ).traceLeft.traceRight)
      ≤ Sᵥₙ ((toMState ρ hρ).assoc'.traceRight) + Sᵥₙ ((toMState ρ hρ).traceLeft) :=
  Sᵥₙ_strong_subadditivity (toMState ρ hρ)

/-- **Ordinary subadditivity** for a repo bipartite density operator. -/
theorem repo_subadditivity (ρ : Matrix (d₁ × d₂) (d₁ × d₂) ℂ) (hρ : IsDensityOperator ρ) :
    Sᵥₙ (toMState ρ hρ) ≤ Sᵥₙ ((toMState ρ hρ).traceRight) + Sᵥₙ ((toMState ρ hρ).traceLeft) :=
  Sᵥₙ_subadditivity (toMState ρ hρ)

/-! ## Relative entropy of entanglement (operational) -/

/-- **Relative entropy of entanglement** `E_R(ρ) = inf over separable σ of 𝐃(ρ‖σ)`, built on
PhysLib's `IsSeparable` and `qRelativeEnt`. -/
noncomputable def relEntEntanglement (ρ : MState (d₁ × d₂)) : ENNReal :=
  ⨅ σ ∈ {σ : MState (d₁ × d₂) | σ.IsSeparable}, qRelativeEnt ρ σ

/-- The REE is at most the relative entropy to **any** specific separable state. -/
theorem relEntEntanglement_le_of_separable {ρ σ₀ : MState (d₁ × d₂)} (hσ₀ : σ₀.IsSeparable) :
    relEntEntanglement ρ ≤ qRelativeEnt ρ σ₀ :=
  iInf₂_le σ₀ hσ₀

/-- The maximally mixed state is separable (it is the product `uniform ⊗ uniform`). -/
theorem uniform_IsSeparable [Nonempty d₁] [Nonempty d₂] :
    (MState.uniform : MState (d₁ × d₂)).IsSeparable := by
  have h : (MState.uniform : MState (d₁ × d₂))
      = (MState.uniform : MState d₁) ⊗ᴹ (MState.uniform : MState d₂) := by
    apply MState.ext
    simp only [MState.prod, MState.uniform, MState.coe_ofClassical, HermitianMat.kronecker_diagonal]
    congr 1
    funext p
    rw [ProbDistribution.uniform_def, ProbDistribution.uniform_def, ProbDistribution.uniform_def]
    simp only [Finset.card_univ, Fintype.card_prod, Nat.cast_mul]
    rw [one_div_mul_one_div]
  rw [h]
  exact MState.IsSeparable_prod _ _

/-- The maximally-mixed state's matrix is `(card)⁻¹ • 1`. -/
theorem uniform_M_eq [Nonempty (d₁ × d₂)] :
    (MState.uniform : MState (d₁ × d₂)).M = ((Fintype.card (d₁ × d₂) : ℝ))⁻¹ • 1 := by
  simp only [MState.uniform, MState.coe_ofClassical]
  have hfun : (fun x => (ProbDistribution.uniform (α := d₁ × d₂) x : ℝ))
      = fun _ => ((Fintype.card (d₁ × d₂) : ℝ))⁻¹ * 1 := by
    funext x
    rw [ProbDistribution.uniform_def]
    simp [Finset.card_univ, one_div]
  rw [hfun, HermitianMat.diagonal_mul]
  congr 1

/-- `𝐃(ρ ‖ I/d) = log d − S(ρ)`: the relative entropy to the maximally-mixed state. -/
theorem qRelativeEnt_uniform [Nonempty (d₁ × d₂)] (ρ : MState (d₁ × d₂)) :
    qRelativeEnt ρ MState.uniform
      = ENNReal.ofReal (Real.log (Fintype.card (d₁ × d₂)) - Sᵥₙ ρ) := by
  have hcard : (0 : ℝ) < (Fintype.card (d₁ × d₂) : ℝ) := by positivity
  -- log of the maximally mixed state is `-(log card) • 1`
  have hlog : (MState.uniform : MState (d₁ × d₂)).M.log
      = (-(Real.log (Fintype.card (d₁ × d₂)))) • (1 : HermitianMat (d₁ × d₂) ℂ) := by
    rw [uniform_M_eq, HermitianMat.log_smul_of_pos _ (by positivity),
      HermitianMat.supportProj_of_nonSingular, HermitianMat.log_one, add_zero,
      Real.log_inv]
  -- the kernel condition (uniform is full rank)
  have hc0 : ((Fintype.card (d₁ × d₂) : ℝ))⁻¹ ≠ 0 := by positivity
  have hker : (MState.uniform : MState (d₁ × d₂)).M.ker ≤ ρ.M.ker := by
    rw [uniform_M_eq, HermitianMat.ker_pos_smul (hc := hc0), HermitianMat.ker_one]
    exact bot_le
  -- the cross term `-⟪ρ.M, (uniform).M.log⟫ = log card`
  have hcross : -(inner (𝕜 := ℝ) ρ.M (MState.uniform : MState (d₁ × d₂)).M.log)
      = Real.log (Fintype.card (d₁ × d₂)) := by
    rw [hlog, real_inner_smul_right, HermitianMat.inner_one, ρ.tr]
    ring
  -- assemble
  have hval : (qRelativeEnt ρ (MState.uniform : MState (d₁ × d₂))).toEReal
      = ((Real.log (Fintype.card (d₁ × d₂)) - Sᵥₙ ρ : ℝ) : EReal) := by
    rw [qRelativeEnt_eq_neg_Sᵥₙ_add, if_pos hker,
      ← EReal.coe_neg (inner (𝕜 := ℝ) ρ.M _), hcross, EReal.coe_sub, sub_eq_add_neg]
    exact add_comm _ _
  have hnn : (0 : ℝ) ≤ Real.log (Fintype.card (d₁ × d₂)) - Sᵥₙ ρ :=
    sub_nonneg.mpr (Sᵥₙ_le_log_d ρ)
  refine EReal.coe_ennreal_injective ?_
  rw [hval, EReal.coe_ennreal_ofReal, max_eq_left hnn]

/-- **Operational REE upper bound**: `E_R(ρ) ≤ log d − S(ρ)`. -/
theorem relEntEntanglement_le_log_card_sub_entropy [Nonempty d₁] [Nonempty d₂]
    (ρ : MState (d₁ × d₂)) :
    relEntEntanglement ρ ≤ ENNReal.ofReal (Real.log (Fintype.card (d₁ × d₂)) - Sᵥₙ ρ) := by
  rw [← qRelativeEnt_uniform ρ]
  exact relEntEntanglement_le_of_separable uniform_IsSeparable

/-- **Concrete numeric bound**: the relative entropy of entanglement of the maximally entangled
two-qubit state `|Φ⁺⟩` is at most `log 4`. -/
theorem relEntEntanglement_MES_le_log_four :
    relEntEntanglement (MState.pure (Ket.MES (Fin 2)))
      ≤ ENNReal.ofReal (Real.log 4) := by
  have h := relEntEntanglement_le_log_card_sub_entropy (MState.pure (Ket.MES (Fin 2)))
  rwa [Sᵥₙ_of_pure_zero, sub_zero, show (Fintype.card (Fin 2 × Fin 2) : ℝ) = 4 by simp] at h

end SKEFTHawking.QuantumNetwork
