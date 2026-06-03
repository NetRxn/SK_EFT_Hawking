import SKEFTHawking.QuantumNetwork.FidelityForwardBound
import SKEFTHawking.QuantumNetwork.FidelityForwardBoundPSD
import SKEFTHawking.QuantumNetwork.CPTPChannel
import SKEFTHawking.QuantumNetwork.GeneralStateNetwork

/-!
# General-CPTP fidelity data processing (Phase 6AJ — general Kraus generalization)

Lifts the mixed-unitary Uhlmann monotonicity (`sqrtFidelity_mixedUnitary_ge`) to an **arbitrary
trace-preserving Kraus channel** `Φ(·) = ∑ₖ Kₖ · Kₖᴴ` with `∑ₖ Kₖᴴ Kₖ = 1`. The mixed-unitary
proof generalizes directly: the block-transport `diagDil_conj_fidelityBlock` already holds for an
*arbitrary* matrix (not just a unitary), so conjugating the Alberti block `[[ρ,X],[Xᴴ,σ]]` by each
`Kₖ ⊕ Kₖ` and summing transports block-PSD feasibility from `(ρ,σ)` to `(Φρ,Φσ)`; the trace is
preserved by `∑ₖ Kₖᴴ Kₖ = 1` (`trace_krausMap`) instead of `∑ᵢ pᵢ = 1`. **No Stinespring, no Choi
dilation, no Lieb concavity.**

The forward Alberti bound (`re_trace_block_le_sqrtFidelity`) is proved via the Schur complement and
so requires the *output* states `Φρ, Φσ` to be positive **definite**. A general trace-preserving
channel may send a full-rank state to a rank-deficient one (e.g. the reset channel
`Kₖ = |0⟩⟨k|`), so the fully general statement carries the output-positive-definiteness as an explicit
hypothesis; it is discharged automatically for the broad class of channels whose "unital part"
`∑ₖ Kₖ Kₖᴴ` is positive definite (`posDef_krausMap_of_sumKrausKrausH_posDef`), which subsumes the
mixed-unitary case (`∑ᵢ pᵢ Uᵢ Uᵢᴴ = 1`).

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

variable {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι] [Nonempty ι]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- The fidelity block is additive: a finite sum of fidelity blocks is the fidelity block of the
finite sums (the off-diagonal `Xᴴ` is conjugate-linear, but a plain sum commutes with `ᴴ`). -/
theorem fidelityBlock_sum (A B C : Fin m → Matrix ι ι ℂ) :
    ∑ k, fidelityBlock (A k) (B k) (C k)
      = fidelityBlock (∑ k, A k) (∑ k, B k) (∑ k, C k) := by
  unfold fidelityBlock
  rw [Matrix.conjTranspose_sum]
  ext x y
  rcases x with x | x <;> rcases y with y | y <;>
    simp [Matrix.sum_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

omit [Nonempty ι] in
/-- **General-Kraus transport of the fidelity block.** For any Kraus operators `Kₖ`, the fidelity
block of the channel outputs `(Φρ, ΦX, Φσ)` is the sum of `(Kₖ⊕Kₖ)`-conjugations of the input block
`[[ρ,X],[Xᴴ,σ]]` — hence PSD whenever the input block is. A feasible Alberti witness `X` for `(ρ,σ)`
thus yields a feasible witness `Φ(X) = ∑ₖ Kₖ X Kₖᴴ` for `(Φρ, Φσ)`. -/
theorem fidelityBlock_krausMap_posSemidef (K : Fin m → Matrix ι ι ℂ) (ρ X σ : Matrix ι ι ℂ)
    (hblock : (fidelityBlock ρ X σ).PosSemidef) :
    (fidelityBlock (krausMap K ρ) (krausMap K X) (krausMap K σ)).PosSemidef := by
  unfold krausMap
  rw [← fidelityBlock_sum]
  refine Matrix.posSemidef_sum _ fun k _ => ?_
  rw [← diagDil_conj_fidelityBlock]
  have h := hblock.conjTranspose_mul_mul_same (diagDil (K k))ᴴ
  rwa [Matrix.conjTranspose_conjTranspose] at h

/-- **General-CPTP Uhlmann monotonicity (data processing for fidelity).** For an arbitrary
trace-preserving Kraus channel `Φ(·) = ∑ₖ Kₖ · Kₖᴴ` (`∑ₖ Kₖᴴ Kₖ = 1`) and positive-definite inputs
`ρ, σ` whose outputs `Φρ, Φσ` are again positive definite,
`F(Φρ, Φσ) ≥ F(ρ, σ)`. The optimal Alberti witness `X*` for `(ρ,σ)` (attainment) transports to a
feasible witness `Φ(X*)` for `(Φρ,Φσ)` with the same trace (trace preservation); the forward Alberti
bound at `(Φρ,Φσ)` then gives `F(Φρ,Φσ) ≥ Re tr Φ(X*) = Re tr X* = F(ρ,σ)`. -/
theorem sqrtFidelity_krausMap_ge {K : Fin m → Matrix ι ι ℂ} {ρ σ : Matrix ι ι ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) (hK : IsKrausChannel K)
    (hΦρ : (krausMap K ρ).PosDef) (hΦσ : (krausMap K σ).PosDef) :
    sqrtFidelity hρ.posSemidef hσ.posSemidef
      ≤ sqrtFidelity hΦρ.posSemidef hΦσ.posSemidef := by
  obtain ⟨X, hXblock, hXtr⟩ := exists_block_re_trace_eq_sqrtFidelity hρ hσ
  have hΦblock := fidelityBlock_krausMap_posSemidef K ρ X σ hXblock
  have hbound := re_trace_block_le_sqrtFidelity hΦρ hΦσ hΦblock
  rwa [show (krausMap K X).trace.re = X.trace.re from by rw [trace_krausMap hK], hXtr] at hbound

omit [DecidableEq ι] [Nonempty ι] in
/-- **Positive-definiteness preservation for unital-faithful Kraus channels.** If the channel's
"unital part" `∑ₖ Kₖ Kₖᴴ` is positive definite, then `Φ(ρ) = ∑ₖ Kₖ ρ Kₖᴴ` is positive definite for
positive-definite `ρ`. (A general trace-preserving channel can be rank-reducing; this is the broad
sufficient condition — it holds for mixed-unitary channels, where `∑ᵢ pᵢ Uᵢ Uᵢᴴ = 1`.)

Proof: in the quadratic form `⟨v, Φ(ρ) v⟩ = ∑ₖ ⟨Kₖᴴv, ρ (Kₖᴴv)⟩` every term is `≥ 0` (`ρ` PSD); if
*all* `Kₖᴴ v = 0` then `⟨v, (∑ₖ Kₖ Kₖᴴ) v⟩ = ∑ₖ ‖Kₖᴴv‖² = 0`, contradicting `(∑ₖ Kₖ Kₖᴴ)` positive
definite at `v ≠ 0`; so some `Kₖᴴ v ≠ 0`, making that term — hence the sum — strictly positive. -/
theorem posDef_krausMap_of_sum (K : Fin m → Matrix ι ι ℂ) {ρ : Matrix ι ι ℂ}
    (hρ : ρ.PosDef) (hKK : (∑ k, K k * (K k)ᴴ).PosDef) :
    (krausMap K ρ).PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos (krausMap_isHermitian K hρ.isHermitian) ?_
  intro v hv
  set w : Fin m → (ι → ℂ) := fun k => (K k)ᴴ *ᵥ v with hw
  have hexpand : star v ⬝ᵥ (krausMap K ρ) *ᵥ v = ∑ k, star (w k) ⬝ᵥ ρ *ᵥ (w k) := by
    unfold krausMap
    rw [Matrix.sum_mulVec, dotProduct_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [show K k * ρ * (K k)ᴴ = K k * (ρ * (K k)ᴴ) by rw [Matrix.mul_assoc],
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec,
      Matrix.star_mulVec, Matrix.conjTranspose_conjTranspose]
  rw [hexpand]
  have hnn : ∀ k, (0 : ℂ) ≤ star (w k) ⬝ᵥ ρ *ᵥ (w k) := fun k =>
    hρ.posSemidef.dotProduct_mulVec_nonneg _
  have hex : ∃ k, w k ≠ 0 := by
    by_contra hcon
    simp only [not_exists, ne_eq, not_not] at hcon
    have hzero : star v ⬝ᵥ (∑ k, K k * (K k)ᴴ) *ᵥ v = 0 := by
      rw [Matrix.sum_mulVec, dotProduct_sum]
      refine Finset.sum_eq_zero fun k _ => ?_
      rw [← Matrix.mulVec_mulVec, show (K k)ᴴ *ᵥ v = w k from rfl, hcon k]
      simp
    exact absurd hzero (ne_of_gt (hKK.dotProduct_mulVec_pos hv))
  obtain ⟨k₀, hk₀⟩ := hex
  exact Finset.sum_pos' (fun k _ => hnn k) ⟨k₀, Finset.mem_univ k₀, hρ.dotProduct_mulVec_pos hk₀⟩

/-- **General-CPTP fidelity DP, unital-faithful form (no output hypothesis).** For a trace-preserving
Kraus channel whose unital part `∑ₖ Kₖ Kₖᴴ` is positive definite, `F(Φρ, Φσ) ≥ F(ρ, σ)` for
positive-definite `ρ, σ` — the output positive-definiteness is discharged automatically. -/
theorem sqrtFidelity_krausMap_ge' {K : Fin m → Matrix ι ι ℂ} {ρ σ : Matrix ι ι ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) (hK : IsKrausChannel K)
    (hKK : (∑ k, K k * (K k)ᴴ).PosDef) :
    sqrtFidelity hρ.posSemidef hσ.posSemidef
      ≤ sqrtFidelity (posDef_krausMap_of_sum K hρ hKK).posSemidef
          (posDef_krausMap_of_sum K hσ hKK).posSemidef :=
  sqrtFidelity_krausMap_ge hρ hσ hK (posDef_krausMap_of_sum K hρ hKK)
    (posDef_krausMap_of_sum K hσ hKK)

/-- **General-CPTP fidelity DP, fully general form (no output hypothesis at all).** For *any*
trace-preserving Kraus channel `Φ(·) = ∑ₖ Kₖ · Kₖᴴ` and positive-definite inputs `ρ, σ`,
`F(Φρ, Φσ) ≥ F(ρ, σ)` — the channel outputs need not be positive definite (they may be
rank-deficient, e.g. a reset channel). This is the textbook Uhlmann data-processing inequality for
positive-definite inputs, with no full-rank-output regularity: it uses the positive-*semidefinite*
forward Alberti bound `re_trace_block_le_sqrtFidelity_psd` (ε-regularized along the commuting ray) at
the PSD outputs `Φρ, Φσ`. -/
theorem sqrtFidelity_krausMap_ge_psd {K : Fin m → Matrix ι ι ℂ} {ρ σ : Matrix ι ι ℂ}
    (hρ : ρ.PosDef) (hσ : σ.PosDef) (hK : IsKrausChannel K) :
    sqrtFidelity hρ.posSemidef hσ.posSemidef
      ≤ sqrtFidelity (krausMap_posSemidef K hρ.posSemidef)
          (krausMap_posSemidef K hσ.posSemidef) := by
  obtain ⟨X, hXblock, hXtr⟩ := exists_block_re_trace_eq_sqrtFidelity hρ hσ
  have hΦblock := fidelityBlock_krausMap_posSemidef K ρ X σ hXblock
  have hbound := re_trace_block_le_sqrtFidelity_psd (krausMap_posSemidef K hρ.posSemidef)
    (krausMap_posSemidef K hσ.posSemidef) hΦblock
  rwa [show (krausMap K X).trace.re = X.trace.re from by rw [trace_krausMap hK], hXtr] at hbound

/-! ## Joint concavity of the (root) fidelity

`(ρ,σ) ↦ F(ρ,σ)` is jointly concave — a direct consequence of the Alberti variational form
`F = max{Re tr X : block PSD}`: the convex combination of the two optimal witnesses is feasible for
the combined pair (the combined block is a nonneg-weighted sum of PSD blocks), and `Re tr` of it is
the convex combination of the optimal values. -/

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- Real-bilinear combination of two fidelity blocks: `a•[[ρ₁,X₁,σ₁]] + b•[[ρ₂,X₂,σ₂]]` is the
fidelity block of the entrywise `a,b`-combinations (real scalars commute with the off-diagonal `ᴴ`). -/
theorem fidelityBlock_smul_add_smul (a b : ℝ) (ρ₁ X₁ σ₁ ρ₂ X₂ σ₂ : Matrix ι ι ℂ) :
    (a : ℂ) • fidelityBlock ρ₁ X₁ σ₁ + (b : ℂ) • fidelityBlock ρ₂ X₂ σ₂
      = fidelityBlock ((a : ℂ) • ρ₁ + (b : ℂ) • ρ₂) ((a : ℂ) • X₁ + (b : ℂ) • X₂)
          ((a : ℂ) • σ₁ + (b : ℂ) • σ₂) := by
  have hX : ((a : ℂ) • X₁ + (b : ℂ) • X₂)ᴴ = (a : ℂ) • X₁ᴴ + (b : ℂ) • X₂ᴴ := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_smul, Matrix.conjTranspose_smul]; simp
  unfold fidelityBlock
  rw [hX, Matrix.fromBlocks_smul, Matrix.fromBlocks_smul, ← Matrix.fromBlocks_add]

omit [Fintype ι] [DecidableEq ι] [Nonempty ι] in
/-- A convex combination of positive-definite matrices is positive definite (`t ∈ [0,1]`). -/
theorem posDef_convex {A B : Matrix ι ι ℂ} (hA : A.PosDef) (hB : B.PosDef) {t : ℝ}
    (ht0 : 0 ≤ t) (ht1 : t ≤ 1) : ((t : ℂ) • A + ((1 - t : ℝ) : ℂ) • B).PosDef := by
  rcases eq_or_lt_of_le ht0 with h0 | h0
  · rw [← h0]; simpa using hB
  · refine (Matrix.PosDef.smul hA (by exact_mod_cast h0)).add_posSemidef ?_
    exact hB.posSemidef.smul (by exact_mod_cast (sub_nonneg.mpr ht1))

/-- **Joint concavity of the root fidelity.** For positive-definite `ρ₁,σ₁,ρ₂,σ₂` and `t ∈ [0,1]`,
`t·F(ρ₁,σ₁) + (1−t)·F(ρ₂,σ₂) ≤ F(t·ρ₁+(1−t)·ρ₂, t·σ₁+(1−t)·σ₂)`. The optimal Alberti witnesses
`X₁, X₂` combine to a feasible witness `t·X₁+(1−t)·X₂` for the convex-combined pair, whose `Re tr`
equals `t·F₁+(1−t)·F₂`; the forward bound at the combined pair closes it. -/
theorem sqrtFidelity_jointly_concave {ρ₁ σ₁ ρ₂ σ₂ : Matrix ι ι ℂ}
    (hρ₁ : ρ₁.PosDef) (hσ₁ : σ₁.PosDef) (hρ₂ : ρ₂.PosDef) (hσ₂ : σ₂.PosDef)
    {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    t * sqrtFidelity hρ₁.posSemidef hσ₁.posSemidef
        + (1 - t) * sqrtFidelity hρ₂.posSemidef hσ₂.posSemidef
      ≤ sqrtFidelity (posDef_convex hρ₁ hρ₂ ht0 ht1).posSemidef
          (posDef_convex hσ₁ hσ₂ ht0 ht1).posSemidef := by
  obtain ⟨X₁, hX₁b, hX₁t⟩ := exists_block_re_trace_eq_sqrtFidelity hρ₁ hσ₁
  obtain ⟨X₂, hX₂b, hX₂t⟩ := exists_block_re_trace_eq_sqrtFidelity hρ₂ hσ₂
  have hblock : (fidelityBlock ((t : ℂ) • ρ₁ + ((1 - t : ℝ) : ℂ) • ρ₂)
      ((t : ℂ) • X₁ + ((1 - t : ℝ) : ℂ) • X₂)
      ((t : ℂ) • σ₁ + ((1 - t : ℝ) : ℂ) • σ₂)).PosSemidef := by
    rw [← fidelityBlock_smul_add_smul]
    exact (hX₁b.smul (by exact_mod_cast ht0)).add
      (hX₂b.smul (by exact_mod_cast (sub_nonneg.mpr ht1)))
  have hbound := re_trace_block_le_sqrtFidelity (posDef_convex hρ₁ hρ₂ ht0 ht1)
    (posDef_convex hσ₁ hσ₂ ht0 ht1) hblock
  have htr : ((t : ℂ) • X₁ + ((1 - t : ℝ) : ℂ) • X₂).trace.re
      = t * X₁.trace.re + (1 - t) * X₂.trace.re := by
    rw [Matrix.trace_add, Matrix.trace_smul, Matrix.trace_smul]; simp [Complex.add_re, smul_eq_mul]
  rw [htr, hX₁t, hX₂t] at hbound
  exact hbound

/-! ## Fidelity-domain network monotonicity (chain corollary)

The fidelity analogue of the shipped trace-distance chain monotonicity `traceDist_applyChain_le`.
A repeater/swap network is a chain of CPTP steps; the root fidelity to a target reference is
*non-decreasing* along the chain — the opposite monotone direction from the trace distance
(`D ↓`, `F ↑`), consistent with Fuchs–van de Graaf. -/

/-- A **fidelity channel step**: it preserves positive-definiteness and does not *decrease* the root
fidelity (Uhlmann data processing). The fidelity-domain analogue of the trace-distance-contractive
`IsChannelStep`. -/
structure IsFidelityStep (Φ : Matrix ι ι ℂ → Matrix ι ι ℂ) : Prop where
  posDef : ∀ {ρ : Matrix ι ι ℂ}, ρ.PosDef → (Φ ρ).PosDef
  monotone : ∀ {ρ σ : Matrix ι ι ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef),
    sqrtFidelity hρ.posSemidef hσ.posSemidef
      ≤ sqrtFidelity (posDef hρ).posSemidef (posDef hσ).posSemidef

/-- A trace-preserving Kraus channel `Φ(·) = ∑ₖ Kₖ · Kₖᴴ` that preserves positive-definiteness is a
fidelity step (the monotonicity is `sqrtFidelity_krausMap_ge`). The positive-definiteness
preservation is the regularity needed for the Schur-complement forward bound; it holds in particular
when the channel's "unital part" `∑ₖ Kₖ Kₖᴴ` is positive definite (e.g. mixed-unitary channels). -/
theorem isFidelityStep_krausMap {m : ℕ} {K : Fin m → Matrix ι ι ℂ} (hK : IsKrausChannel K)
    (hpres : ∀ {ρ : Matrix ι ι ℂ}, ρ.PosDef → (krausMap K ρ).PosDef) :
    IsFidelityStep (krausMap K) where
  posDef := hpres
  monotone hρ hσ := sqrtFidelity_krausMap_ge hρ hσ hK (hpres hρ) (hpres hσ)

/-- A trace-preserving Kraus channel whose unital part `∑ₖ Kₖ Kₖᴴ` is positive definite is a fidelity
step (no separate preservation hypothesis — discharged by `posDef_krausMap_of_sum`). -/
theorem isFidelityStep_krausMap' {m : ℕ} {K : Fin m → Matrix ι ι ℂ} (hK : IsKrausChannel K)
    (hKK : (∑ k, K k * (K k)ᴴ).PosDef) : IsFidelityStep (krausMap K) :=
  isFidelityStep_krausMap hK fun hρ => posDef_krausMap_of_sum K hρ hKK

omit [Nonempty ι] in
/-- A chain of fidelity steps preserves positive-definiteness. -/
theorem applyChain_posDef {Φs : List (Matrix ι ι ℂ → Matrix ι ι ℂ)}
    (hΦs : ∀ Φ ∈ Φs, IsFidelityStep Φ) {ρ : Matrix ι ι ℂ} (hρ : ρ.PosDef) :
    (applyChain Φs ρ).PosDef := by
  induction Φs with
  | nil => simpa using hρ
  | cons Φ rest ih =>
    rw [applyChain_cons]
    exact (hΦs Φ List.mem_cons_self).posDef (ih fun Φ' h => hΦs Φ' (List.mem_cons_of_mem _ h))

omit [Nonempty ι] in
/-- **Fidelity-domain network data-processing monotonicity.** For positive-definite states and any
chain of fidelity steps (CPTP entanglement swaps / LOCC distillation / memory channels that preserve
positive-definiteness), the root fidelity to a target reference is non-decreasing along the chain:
`F(applyChain Φs ρ, applyChain Φs σ) ≥ F(ρ, σ)`. The mirror of `traceDist_applyChain_le`, in the
opposite monotone direction. -/
theorem sqrtFidelity_applyChain_ge {Φs : List (Matrix ι ι ℂ → Matrix ι ι ℂ)}
    (hΦs : ∀ Φ ∈ Φs, IsFidelityStep Φ) {ρ σ : Matrix ι ι ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    sqrtFidelity hρ.posSemidef hσ.posSemidef
      ≤ sqrtFidelity (applyChain_posDef hΦs hρ).posSemidef
          (applyChain_posDef hΦs hσ).posSemidef := by
  induction Φs with
  | nil => exact le_of_eq rfl
  | cons Φ rest ih =>
    have hrest : ∀ Φ' ∈ rest, IsFidelityStep Φ' := fun Φ' h => hΦs Φ' (List.mem_cons_of_mem _ h)
    exact le_trans (ih hrest)
      ((hΦs Φ List.mem_cons_self).monotone (applyChain_posDef hrest hρ) (applyChain_posDef hrest hσ))

omit [Nonempty ι] in
/-- **Single fidelity step** (the chain-of-one specialization): one CPTP segment that preserves
positive-definiteness does not decrease the root fidelity to the target. -/
theorem sqrtFidelity_step_ge {Φ : Matrix ι ι ℂ → Matrix ι ι ℂ} (hΦ : IsFidelityStep Φ)
    {ρ σ : Matrix ι ι ℂ} (hρ : ρ.PosDef) (hσ : σ.PosDef) :
    sqrtFidelity hρ.posSemidef hσ.posSemidef
      ≤ sqrtFidelity (hΦ.posDef hρ).posSemidef (hΦ.posDef hσ).posSemidef :=
  hΦ.monotone hρ hσ

end SKEFTHawking.QuantumNetwork
