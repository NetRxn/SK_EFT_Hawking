import SKEFTHawking.QuantumNetwork.PauliChannel

/-!
# Negativity and the PPT criterion for two-qubit Bell-diagonal states (Phase 6AK, Wave FU-2)

The repeaterless-rate surrogate (6AK.2) formalizes properties of the PLOB bound *function*. A genuine
entanglement *measure* on an actual density matrix — rather than a function of an abstract parameter —
requires the partial transpose. This wave builds it for the two-qubit Bell-diagonal family, reusing the
Bell-block substrate already shipped for the Pauli-channel diamond distance (`PauliChannel.lean`):
`bellBlock i = |vec σᵢ⟩⟨vec σᵢ|` are the (unnormalised, `tr = 2`) Bell projectors, with
`Bᵢ Bⱼ = 2δᵢⱼ Bᵢ` and the real-combination trace norm `‖∑ᵢ cᵢ Bᵢ‖₁ = 2∑ᵢ|cᵢ|` (`traceNorm_bellCombo`).

A **Bell-diagonal state** `ρ(p) = ∑ᵢ pᵢ Pᵢ` (`Pᵢ = ½ Bᵢ` the normalised Bell projector, weights
`p : Fin 4 → ℝ`, `pᵢ ≥ 0`, `∑ pᵢ = 1`) has a partial transpose that is **again Bell-diagonal**. On the
Bell blocks the partial transpose acts as

`Tᵦ(Bᵢ) = Bᵢ − ½ yᵢ ∑ⱼ yⱼ Bⱼ`,  `y = (−1, 1, −1, 1)` the `σ_Y⊗σ_Y` parity of the Bell states

(verified: `P₀ = |Φ⁺⟩⟨Φ⁺|` maps to the swap `½(B₀+B₁−B₂+B₃)`, eigenvalues `{−½,½,½,½}`; the maximally
mixed state is fixed). The partial-transpose eigenvalue on the projector `Pⱼ` is therefore
`μⱼ(p) = pⱼ − ½ yⱼ ∑ᵢ yᵢ pᵢ` (`bellPTeig`).

Consequences (all kernel-pure, exact):
- `‖ρ(p)^Γ‖₁ = ∑ⱼ |μⱼ(p)|` (`traceNorm_pt2_bellDiagState`);
- **negativity** `N(ρ(p)) = ½(∑ⱼ|μⱼ(p)| − 1)`, nonnegative (`negativityBellDiag_eq`,
  `negativityBellDiag_nonneg`);
- **PPT criterion**: `N(ρ(p)) = 0 ↔ ∀ j, μⱼ(p) ≥ 0` (`ppt_bellDiagState_iff`) — the negativity vanishes
  exactly when the partial transpose is positive semidefinite; by the 2-qubit Horodecki theorem (cited,
  not formalised) this is equivalent to separability;
- **Werner state** (`wernerWeights F`, singlet fraction `F` on `B₂`): negativity `(2F − 1)/2` for
  `F ≥ ½` (`negativityBellDiag_werner`), PPT (hence separable) exactly at `F ≤ ½` (`ppt_werner_iff`) —
  the same `½` threshold as the BBPSSW/DEJMPS distillability cutoff.

The operational reading (negativity / log-negativity is an upper bound on distillable entanglement and on
the two-way secret-key rate) is the standard Vidal–Werner / Życzkowski citation; the Lean content is the
**exact computed entanglement measure**, not the LOCC-monotonicity theorem.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

/-- **Partial transpose on the second qubit:** `(Tᵦ ρ)((a,b),(c,d)) = ρ((a,d),(c,b))`. -/
noncomputable def pt2 (ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun p q => ρ (p.1, q.2) (q.1, p.2)

/-- The `Y⊗Y` parity `⟨σ_Y⊗σ_Y⟩` of the four Bell states (`|Φ⁺⟩,|Ψ⁺⟩,|Ψ⁻⟩,|Φ⁻⟩ ↔ B₀,B₁,B₂,B₃`,
where `B₂` is the singlet). It is the sign the second-factor transpose `σ_Yᵀ = −σ_Y` attaches to each
Bell block. -/
def bellY : Fin 4 → ℝ := ![-1, 1, -1, 1]

/-- **The partial transpose acts on the Bell blocks as** `Tᵦ(Bᵢ) = Bᵢ − ½ yᵢ ∑ⱼ yⱼ Bⱼ`, where
`yᵢ = ⟨σ_Y⊗σ_Y⟩` on the `i`-th Bell state. Equivalently the partial-transpose eigenvalue on the Bell
projector `Pⱼ = ½Bⱼ` is `μⱼ = pⱼ − ½ yⱼ ∑ᵢ yᵢ pᵢ`. (Only the `Y⊗Y` correlation flips sign;
`P₀ = |Φ⁺⟩⟨Φ⁺|` maps to the swap `½(B₀+B₁−B₂+B₃)`, the maximally mixed state is fixed.) -/
theorem pt2_bellBlock (i : Fin 4) :
    pt2 (bellBlock i) = bellBlock i - ((bellY i) / 2 : ℂ) • (∑ j, (bellY j : ℂ) • bellBlock j) := by
  ext p q
  obtain ⟨a, b⟩ := p
  obtain ⟨c, d⟩ := q
  simp only [pt2, Matrix.of_apply, Matrix.sub_apply, Matrix.smul_apply, Fin.sum_univ_four,
    Matrix.add_apply, smul_eq_mul, bellBlock_apply, bellY, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val]
  fin_cases i <;> fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;>
    simp [pauliOp, pauliX, pauliY, pauliZ] <;> ring

/-! ## Linearity of the partial transpose -/

theorem pt2_smul (c : ℂ) (M : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    pt2 (c • M) = c • pt2 M := by
  ext p q; simp only [pt2, Matrix.of_apply, Matrix.smul_apply]

theorem pt2_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ) :
    pt2 (∑ i ∈ s, f i) = ∑ i ∈ s, pt2 (f i) := by
  ext p q; simp only [pt2, Matrix.of_apply, Matrix.sum_apply]

/-- **Partial transpose of a Bell-block combination = the PT-eigenvalue combination.** For real
coefficients `c`, `Tᵦ(∑ᵢ cᵢ Bᵢ) = ∑ⱼ (cⱼ − ½ yⱼ ∑ᵢ yᵢ cᵢ) Bⱼ`. -/
theorem pt2_bellCombo (c : Fin 4 → ℝ) :
    pt2 (∑ i, (c i : ℂ) • bellBlock i)
      = ∑ j, ((c j - bellY j * (∑ i, bellY i * c i) / 2 : ℝ) : ℂ) • bellBlock j := by
  have hY : (∑ i, (bellY i : ℂ) • bellBlock i)
      = ∑ i, ((bellY i : ℝ) : ℂ) • bellBlock i := rfl
  rw [pt2_sum]
  simp_rw [pt2_smul, pt2_bellBlock, smul_sub, smul_smul]
  rw [Finset.sum_sub_distrib, ← Finset.sum_smul, Finset.smul_sum]
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_smul, ← sub_smul]
  congr 1
  push_cast
  rw [sub_right_inj, Finset.sum_mul, Finset.mul_sum, Finset.sum_div]
  exact Finset.sum_congr rfl fun i _ => by ring

/-! ## Bell-diagonal density matrix, partial transpose, and negativity -/

/-- A **two-qubit Bell-diagonal density matrix** with Bell weights `p` (`Pᵢ = ½Bᵢ` the normalised Bell
projectors): `ρ(p) = ∑ᵢ pᵢ Pᵢ = ∑ᵢ (pᵢ/2) Bᵢ`. -/
noncomputable def bellDiagState (p : Fin 4 → ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  ∑ i, ((p i / 2 : ℝ) : ℂ) • bellBlock i

/-- The `j`-th **partial-transpose eigenvalue** of `ρ(p)` (on the Bell projector `Pⱼ`):
`μⱼ(p) = pⱼ − ½ yⱼ ∑ᵢ yᵢ pᵢ`. -/
noncomputable def bellPTeig (p : Fin 4 → ℝ) (j : Fin 4) : ℝ :=
  p j - bellY j * (∑ i, bellY i * p i) / 2

theorem pt2_bellDiagState (p : Fin 4 → ℝ) :
    pt2 (bellDiagState p) = ∑ j, ((bellPTeig p j / 2 : ℝ) : ℂ) • bellBlock j := by
  rw [bellDiagState, pt2_bellCombo]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  rw [bellPTeig]
  have : (∑ i, bellY i * (p i / 2)) = (∑ i, bellY i * p i) / 2 := by
    rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [this]; ring

/-- **Trace norm of the partial transpose** = sum of absolute partial-transpose eigenvalues:
`‖ρ(p)^Γ‖₁ = ∑ⱼ |μⱼ(p)|`. -/
theorem traceNorm_pt2_bellDiagState (p : Fin 4 → ℝ) :
    traceNorm (pt2 (bellDiagState p)) = ∑ j, |bellPTeig p j| := by
  rw [pt2_bellDiagState, traceNorm_bellCombo, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [abs_div, abs_two]; ring

/-- **Negativity** of a Bell-diagonal state, `N(ρ) = ½(‖ρ^Γ‖₁ − 1)`. -/
noncomputable def negativityBellDiag (p : Fin 4 → ℝ) : ℝ :=
  (traceNorm (pt2 (bellDiagState p)) - 1) / 2

/-- **Negativity closed form:** `N(ρ(p)) = ½(∑ⱼ |μⱼ(p)| − 1)`. -/
theorem negativityBellDiag_eq (p : Fin 4 → ℝ) :
    negativityBellDiag p = (∑ j, |bellPTeig p j| - 1) / 2 := by
  rw [negativityBellDiag, traceNorm_pt2_bellDiagState]

theorem bellY_sum : ∑ j, bellY j = 0 := by
  simp [bellY, Fin.sum_univ_four]

/-- The partial-transpose eigenvalues sum to the trace `∑ᵢ pᵢ` (`= 1` for a density matrix). -/
theorem bellPTeig_sum (p : Fin 4 → ℝ) (h1 : ∑ i, p i = 1) : ∑ j, bellPTeig p j = 1 := by
  have hmul : (∑ j, bellY j * (∑ i, bellY i * p i) / 2)
      = (∑ j, bellY j) * ((∑ i, bellY i * p i) / 2) := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun j _ => by ring
  simp only [bellPTeig]
  rw [Finset.sum_sub_distrib, h1, hmul, bellY_sum, zero_mul, sub_zero]

/-- **Negativity is nonnegative** (for a normalised Bell-diagonal state). -/
theorem negativityBellDiag_nonneg (p : Fin 4 → ℝ) (h1 : ∑ i, p i = 1) :
    0 ≤ negativityBellDiag p := by
  rw [negativityBellDiag_eq]
  have : (1 : ℝ) ≤ ∑ j, |bellPTeig p j| := by
    rw [← bellPTeig_sum p h1]; exact Finset.sum_le_sum fun j _ => le_abs_self _
  linarith

/-- **The PPT (positive-partial-transpose) criterion for Bell-diagonal states:** the negativity
vanishes exactly when all partial-transpose eigenvalues are nonnegative. By the two-qubit Horodecki
theorem (cited, not formalised) this is equivalent to separability. -/
theorem ppt_bellDiagState_iff (p : Fin 4 → ℝ) (h1 : ∑ i, p i = 1) :
    negativityBellDiag p = 0 ↔ ∀ j, 0 ≤ bellPTeig p j := by
  rw [negativityBellDiag_eq, div_eq_zero_iff]
  have hle : ∀ k ∈ (Finset.univ : Finset (Fin 4)), bellPTeig p k ≤ |bellPTeig p k| :=
    fun k _ => le_abs_self _
  constructor
  · rintro (h | h)
    · intro j
      have hsum : ∑ k, bellPTeig p k = ∑ k, |bellPTeig p k| := by
        rw [bellPTeig_sum p h1]; linarith
      rw [(Finset.sum_eq_sum_iff_of_le hle).mp hsum j (Finset.mem_univ j)]; exact abs_nonneg _
    · norm_num at h
  · intro h
    left
    rw [Finset.sum_congr rfl fun j _ => abs_of_nonneg (h j), bellPTeig_sum p h1]; ring

/-! ## The Werner state: negativity and PPT threshold at `F = ½` -/

/-- **Werner state** with singlet fraction `F` (weight `F` on the singlet `B₂`, `(1−F)/3` on each
triplet). -/
noncomputable def wernerWeights (F : ℝ) : Fin 4 → ℝ := ![(1 - F) / 3, (1 - F) / 3, F, (1 - F) / 3]

theorem wernerWeights_sum (F : ℝ) : ∑ i, wernerWeights F i = 1 := by
  simp [wernerWeights, Fin.sum_univ_four]; ring

theorem bellPTeig_werner_zero (F : ℝ) : bellPTeig (wernerWeights F) 0 = (1 - 2 * F) / 2 := by
  simp [bellPTeig, wernerWeights, bellY, Fin.sum_univ_four]; ring

/-- **Negativity of an entangled Werner state** (`F ≥ ½`): `N = (2F − 1)/2`. The threshold `F = ½`
coincides with the BBPSSW/DEJMPS distillability cutoff. -/
theorem negativityBellDiag_werner (F : ℝ) (hF : 1 / 2 ≤ F) (_hF1 : F ≤ 1) :
    negativityBellDiag (wernerWeights F) = (2 * F - 1) / 2 := by
  have e0 : bellPTeig (wernerWeights F) 0 = (1 - 2 * F) / 2 := bellPTeig_werner_zero F
  have e1 : bellPTeig (wernerWeights F) 1 = (1 + 2 * F) / 6 := by
    simp [bellPTeig, wernerWeights, bellY, Fin.sum_univ_four]; ring
  have e2 : bellPTeig (wernerWeights F) 2 = (1 + 2 * F) / 6 := by
    simp [bellPTeig, wernerWeights, bellY, Fin.sum_univ_four]; ring
  have e3 : bellPTeig (wernerWeights F) 3 = (1 + 2 * F) / 6 := by
    simp [bellPTeig, wernerWeights, bellY, Fin.sum_univ_four]; ring
  rw [negativityBellDiag_eq, Fin.sum_univ_four, e0, e1, e2, e3,
    abs_of_nonpos (show (1 - 2 * F) / 2 ≤ 0 by linarith),
    abs_of_nonneg (show (0 : ℝ) ≤ (1 + 2 * F) / 6 by linarith)]
  ring

/-- **PPT criterion for the Werner state:** PPT (hence separable, by the 2-qubit Horodecki theorem)
exactly when `F ≤ ½` — the same threshold as distillability. -/
theorem ppt_werner_iff (F : ℝ) (hF0 : 0 ≤ F) (_hF1 : F ≤ 1) :
    negativityBellDiag (wernerWeights F) = 0 ↔ F ≤ 1 / 2 := by
  rw [ppt_bellDiagState_iff _ (wernerWeights_sum F)]
  constructor
  · intro h
    have h0 := h 0
    rw [bellPTeig_werner_zero] at h0
    linarith
  · intro hF j
    fin_cases j <;> simp [bellPTeig, wernerWeights, bellY, Fin.sum_univ_four] <;> linarith

end SKEFTHawking.QuantumNetwork
