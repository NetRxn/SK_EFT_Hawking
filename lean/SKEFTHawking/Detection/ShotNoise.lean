import SKEFTHawking.Detection.PoissonDiscrimination
import SKEFTHawking.Detection.GaussianThreshold
import SKEFTHawking.Detection.FilterFloors
import SKEFTHawking.QuantumNetwork.DiamondNormChoi
import SKEFTHawking.QuantumNetwork.HelstromDiscrimination
import SKEFTHawking.GrapheneNoiseFormula

/-!
# Shot-noise algebra and the quantum seam (Phase 6EA, Wave 3)

Two independent strands, joined by the file's guardrail:

**The quantum seam.** The classical discrimination floors of Wave 1 are the *commutative
shadow* of the project's quantum fidelity substrate (`QuantumNetwork/MixedState.lean`). Two things
are needed for that to be a claim and not a slogan, and both are here:

1. an *identification*: the Uhlmann root fidelity of two **diagonal** density matrices is the
   classical Bhattacharyya affinity of their diagonals (`diagonalState_sqrtFidelity_eq_affinity`),
   and the classical average assignment error is the Born-rule error of one particular POVM on
   those states (`povmAvgError_diagonal_eq_avgAssignmentError`);
2. a *quantum bound to restrict*: `QuantumNetwork/HelstromDiscrimination.lean`'s
   `quarter_sqrtFidelity_sq_le_povmAvgError` — `¼F(ρ,σ)² ≤ P_err` for **arbitrary** density
   operators and **arbitrary** two-outcome POVMs, from Holevo–Helstrom plus Fuchs–van de Graaf.

`poissonFloor_le_diagonalQuantumBound` is then the composition, and its second conjunct is
literally the restriction of (2) along (1). Without (2) the seam would be notational — (1) alone
makes the "quantum" quantity *equal* to a classical one, so a classical proof of the same
inequality would establish nothing.

**Shot-noise algebra.** The one-sided shot-noise PSD, its reference-plane transfer under a
transfer factor `η`, the pmf-level Poisson thinning identity, the single-binder bridge tying the
PSD `η` to the thinning `η`, and the Fano factor of a *filtered* count.

## Main results

* `psdSqrt_diagonal` — the PSD square root of a diagonal matrix is the entrywise `√`; the one
  net-new piece of mathematics in the identification step, via PSD-square-root uniqueness.
* `diagonalState_sqrtFidelity_eq_affinity` — **(S1)** `F(diag p, diag q) = ∑ᵢ √(pᵢqᵢ)`.
* `pushforwardFidelity_eq_binaryAffinity` — the two-outcome specialization.
* `declareSignalPOVM`, `isBinaryPOVM_declareSignal`,
  `povmAvgError_diagonal_eq_avgAssignmentError` — the classical binary decision exhibited as one
  POVM out of the whole admissible family, and its error as a *value* of the quantum error
  functional.
* `poissonFloor_le_diagonalQuantumBound` — **(S2)** the Wave-1 Poisson floor is sandwiched:
  classical data processing on the left, the quantum discrimination floor on the right.
* `shotPSD`, `shotPSD_eq_hawkingNoisePSD`, `shotPSD_plane_transfer`, `shotPSD_pos` — the
  one-sided shot-noise PSD, agreement of its leading `2` with the repo's `GrapheneNoiseFormula`
  convention (slot identity is *not* pinned — see that theorem), and the `η`-transfer.
* `hasSum_poisson_thinning` / `poisson_thinning` — the **pmf-level** thinning identity
  `Poisson N ↦ Poisson (ηN)`, in `HasSum` and `tsum` form.
* `shotPSD_thinnedMean_same_eta` — **the `η` bridge**: one `ℝ≥0` binder used in *both* the PSD
  transfer and the thinning kernel, with `shotPSD_thinnedMean_eta_exponent_load_bearing` showing
  the identity pins the two scaling exponents to agree. `poissonMean_thinning` is mean algebra
  only; `thinnedMean_eq_eta_mul` reduces the thinning sum but still binds its own `η`.
* `poissonMean_eq`, `poissonVariance_eq` — the second-moment computation for the *unfiltered*
  Poisson count.
* `IsShotFilteredMoments`, `shotFilteredMean_le_variance`,
  `shotFilteredVariance_boxcar_eq_mean`, `shotFilteredVariance_ramp_gt_mean` — the **filtered**
  count: at matched DC gain its Fano factor is `≥ 1`, with equality exactly at the boxcar and
  strict excess already at the ramp. "Variance = mean" is the boxcar case, not a property of
  filtered shot noise.
* `shotGaussian_avgError_gt_leCam_floor` — a concrete operating point at which a shot-limited
  Gaussian threshold model (branch widths `√N_b`, `√N_a`) errs by more than 3/2 of the Le Cam
  floor **value**, certifying the floor is not a disguised equality there. It does *not* exhibit
  a count rule beating its own floor: the Gaussian error pair is not claimed realizable by any
  `δ` (see the theorem's scope note).

## Guardrail

Floors and screens over abstract count means and noise parameters. No device claim: physical
identification of an abstract parameter with a measured quantity is the consuming phase's
declared hypothesis. In particular `η` is an abstract transfer factor here; reading it as a
*probability* (which is what makes `poisson_thinning` physical thinning) is a consumer-side
condition, deliberately not a hypothesis of the theorem.

Invariants (Phase 6EA): kernel-pure, zero sorry, no project-local axioms, no `maxHeartbeats`.
-/

namespace SKEFTHawking.Detection

open scoped NNReal Nat ComplexOrder

open ProbabilityTheory SKEFTHawking.QuantumNetwork

/-! ## The commutative shadow: diagonal states -/

section Diagonal

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
/-- The diagonal embedding of a nonnegative real vector is a positive-semidefinite matrix —
the "classical states sit inside the quantum states" embedding. -/
theorem diagonalPSD {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) :
    (Matrix.diagonal (fun i => (p i : ℂ))).PosSemidef :=
  Matrix.PosSemidef.diagonal fun i => Complex.zero_le_real.mpr (hp i)

/-- **`psdSqrt` of a PSD diagonal matrix is the entrywise `√`.** The only net-new mathematical
content of the seam; everything else composes existing lemmas.

The proof does **not** unfold the functional calculus: `psdSqrt` is `hM.isHermitian.cfc √`,
whose eigendecomposition *sorts* the eigenvalues, so on `diagonal d` the eigenvector matrix is a
permutation rather than `1`. Instead it uses the characterisation "PSD and squares to `M`":
both sides are PSD (`psdSqrt_posSemidef`, `diagonalPSD`), both square to `diagonal d`
(`psdSqrt_mul_self`; `Matrix.diagonal_mul_diagonal` with `Real.mul_self_sqrt`), and the PSD
square root is unique (`SKEFTHawking.QuantumNetwork.posSemidef_eq_of_mul_self_eq`). -/
theorem psdSqrt_diagonal {p : ι → ℝ} (hp : ∀ i, 0 ≤ p i) :
    psdSqrt (diagonalPSD hp) = Matrix.diagonal (fun i => (Real.sqrt (p i) : ℂ)) := by
  refine posSemidef_eq_of_mul_self_eq (psdSqrt_posSemidef _)
    (diagonalPSD fun i => Real.sqrt_nonneg (p i)) ?_
  rw [psdSqrt_mul_self, Matrix.diagonal_mul_diagonal]
  simp only [← Complex.ofReal_mul, Real.mul_self_sqrt (hp _)]

/-- **(S1) The commutative shadow.** For classical distributions `p q` on a finite alphabet, the
Uhlmann root fidelity of their diagonal embeddings is exactly the classical Bhattacharyya
affinity `∑ᵢ √(pᵢqᵢ)`.

This is the literal content of "the classical floors are the commutative shadow of the quantum
bounds", and it is a genuine cross-module bridge rather than a docstring reference: the proof
*calls* `sqrtFidelity` (`QuantumNetwork/MixedState.lean`), `psdSqrt_diagonal`, and the 6AE
linchpin `traceNorm_posSemidef`. No normalisation is assumed — `p` and `q` need only be
nonnegative, so the statement also covers sub-normalised (filtered) weights. -/
theorem diagonalState_sqrtFidelity_eq_affinity {p q : ι → ℝ}
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) :
    sqrtFidelity (diagonalPSD hp) (diagonalPSD hq) = ∑ i, Real.sqrt (p i * q i) := by
  have hprod : ∀ i, (0 : ℝ) ≤ Real.sqrt (q i) * Real.sqrt (p i) := fun i => by positivity
  rw [sqrtFidelity, psdSqrt_diagonal hq, psdSqrt_diagonal hp, Matrix.diagonal_mul_diagonal]
  simp only [← Complex.ofReal_mul]
  rw [traceNorm_posSemidef (diagonalPSD hprod), Matrix.trace_diagonal, Complex.re_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [Complex.ofReal_re, ← Real.sqrt_mul (hq i), mul_comm (q i) (p i)]

end Diagonal

/-! ## The two-outcome pushforward and the Wave-1 seam -/

/-- The two-outcome distribution `(e, 1 − e)` on the decision alphabet `Fin 2`
(`0` = "declare signal", `1` = "declare baseline"). -/
def binaryDist (e : ℝ) : Fin 2 → ℝ := ![e, 1 - e]

theorem binaryDist_nonneg {e : ℝ} (h : e ∈ Set.Icc (0 : ℝ) 1) : ∀ i, 0 ≤ binaryDist e i := by
  intro i
  fin_cases i <;> simp [binaryDist] <;> linarith [h.1, h.2]

/-- PSD witness for the diagonal embedding of the two-outcome pushforward `(e, 1 − e)`. -/
theorem binaryPSD {e : ℝ} (h : e ∈ Set.Icc (0 : ℝ) 1) :
    (Matrix.diagonal (fun i => (binaryDist e i : ℂ))).PosSemidef :=
  diagonalPSD (binaryDist_nonneg h)

/-- The diagonal embedding of a two-outcome distribution really is a **density operator** —
positive semidefinite *with unit trace*. This is what licenses reading the `ρ₀, ρ₁` of
`poissonFloor_le_diagonalQuantumBound` as quantum states rather than as bare PSD matrices, and
it keeps that reading a theorem instead of a docstring claim. -/
theorem binaryDensityOperator {e : ℝ} (h : e ∈ Set.Icc (0 : ℝ) 1) :
    IsDensityOperator (Matrix.diagonal (fun i => (binaryDist e i : ℂ))) := by
  refine ⟨binaryPSD h, ?_⟩
  rw [Matrix.trace_diagonal, Fin.sum_univ_two]
  simp only [binaryDist, Matrix.cons_val_zero, Matrix.cons_val_one, Complex.ofReal_sub,
    Complex.ofReal_one]
  ring

/-- **The two-outcome specialization of (S1).** The root fidelity of the diagonal pushforward
states `(e₀, 1−e₀)` and `(1−e₁, e₁)` is the binary Bhattacharyya affinity that Wave 1's
data-processing bound `affinity_le_binaryAffinity` produces. -/
theorem pushforwardFidelity_eq_binaryAffinity {e₀ e₁ : ℝ}
    (h₀ : e₀ ∈ Set.Icc (0 : ℝ) 1) (h₁ : (1 - e₁) ∈ Set.Icc (0 : ℝ) 1) :
    sqrtFidelity (binaryPSD h₀) (binaryPSD h₁)
      = Real.sqrt (e₀ * (1 - e₁)) + Real.sqrt ((1 - e₀) * e₁) := by
  have h := diagonalState_sqrtFidelity_eq_affinity (binaryDist_nonneg h₀) (binaryDist_nonneg h₁)
  rw [Fin.sum_univ_two] at h
  simpa [binaryDist] using h

/-- The false-alarm probability of an admissible count rule lies in `[0,1]`. -/
theorem falseAlarm_mem_Icc {r : ℝ≥0} {δ : ℕ → ℝ} (hδ : IsCountRule δ) :
    falseAlarm r δ ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨hasSum_le (fun n => mul_nonneg poissonPMFReal_nonneg (hδ n).1) hasSum_zero
      (hasSum_falseAlarm hδ),
    hasSum_le (fun n => mul_le_of_le_one_right poissonPMFReal_nonneg (hδ n).2)
      (hasSum_falseAlarm hδ) (poissonPMFRealSum r)⟩

/-- The miss probability of an admissible count rule lies in `[0,1]`. -/
theorem missProb_mem_Icc {r : ℝ≥0} {δ : ℕ → ℝ} (hδ : IsCountRule δ) :
    missProb r δ ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨hasSum_le (fun n => mul_nonneg poissonPMFReal_nonneg (by linarith [(hδ n).2])) hasSum_zero
      (hasSum_missProb hδ),
    hasSum_le (fun n => mul_le_of_le_one_right poissonPMFReal_nonneg (by linarith [(hδ n).1]))
      (hasSum_missProb hδ) (poissonPMFRealSum r)⟩

/-- Complement of the miss probability — the "declare signal" mass of the pushforward under the
signal hypothesis. -/
theorem one_sub_missProb_mem_Icc {r : ℝ≥0} {δ : ℕ → ℝ} (hδ : IsCountRule δ) :
    (1 - missProb r δ) ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨by linarith [(missProb_mem_Icc (r := r) hδ).2], by linarith [(missProb_mem_Icc (r := r) hδ).1]⟩

/-! ### The classical decision as a POVM -/

/-- **The computational-basis effect "declare signal"** on the two-outcome decision alphabet: the
rank-one projector onto outcome `0`. This is the measurement a classical count rule actually
performs on its pushforward states — the *one* POVM out of the whole admissible family
`{E : 0 ⪯ E ⪯ 1}` over which the Helstrom optimum below ranges. -/
def declareSignalPOVM : Matrix (Fin 2) (Fin 2) ℂ := Matrix.diagonal ![1, 0]

theorem isBinaryPOVM_declareSignal : IsBinaryPOVM declareSignalPOVM := by
  constructor
  · rw [show declareSignalPOVM = Matrix.diagonal (fun i => ((![1, 0] i : ℝ) : ℂ)) by
      rw [declareSignalPOVM]; ext i j; fin_cases i <;> fin_cases j <;> simp]
    exact diagonalPSD (by intro i; fin_cases i <;> norm_num)
  · rw [show (1 : Matrix (Fin 2) (Fin 2) ℂ) - declareSignalPOVM
        = Matrix.diagonal (fun i => ((![0, 1] i : ℝ) : ℂ)) by
      rw [declareSignalPOVM]; ext i j; fin_cases i <;> fin_cases j <;> simp]
    exact diagonalPSD (by intro i; fin_cases i <;> norm_num)

/-- **The diagonal restriction, exactly.** The classical average assignment error of a two-outcome
experiment with false-alarm `e₀` and miss `e₁` *is* the quantum average error `povmAvgError` of the
computational-basis POVM on the diagonal pushforward states `ρ = diag(1−e₁, e₁)` (signal) and
`σ = diag(e₀, 1−e₀)` (baseline).

This is the equation that makes "the classical floor is the diagonal restriction of a quantum
bound" a theorem rather than a figure of speech: the classical error is not merely *bounded by*
the quantum error functional, it is a *value* of it. Hypothesis-free — pure Born-rule algebra on
diagonal matrices, valid for any reals `e₀, e₁`. -/
theorem povmAvgError_diagonal_eq_avgAssignmentError (e₀ e₁ : ℝ) :
    povmAvgError (Matrix.diagonal (fun i => (binaryDist (1 - e₁) i : ℂ)))
        (Matrix.diagonal (fun i => (binaryDist e₀ i : ℂ))) declareSignalPOVM
      = avgAssignmentError e₀ e₁ := by
  have h1 : (1 : Matrix (Fin 2) (Fin 2) ℂ) - declareSignalPOVM = Matrix.diagonal ![0, 1] := by
    rw [declareSignalPOVM]; ext i j; fin_cases i <;> fin_cases j <;> simp
  rw [povmAvgError, h1, declareSignalPOVM, Matrix.diagonal_mul_diagonal,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal, Matrix.trace_diagonal,
    Fin.sum_univ_two, Fin.sum_univ_two, avgAssignmentError]
  simp [binaryDist]

/-- **(S2) The seam: the Wave-1 Poisson floor factors through a quantum fidelity.** For any
count rule `δ`, push the experiment forward to its two-outcome decision alphabet `Fin 2` and
embed the resulting distributions as diagonal density matrices `ρ₀, ρ₁` (genuinely density
operators — `binaryDensityOperator`). Then

* the classical Poisson floor `¼·exp(−(√N_a − √N_b)²)` is at most `¼·F(ρ₀,ρ₁)²`, and
* `¼·F(ρ₀,ρ₁)²` is itself a floor on the average assignment error.

So the Wave-1 floor is *the diagonal restriction of a quantum two-state discrimination bound*.
Both conjuncts are needed and neither implies the other, and they come from opposite sides:

* the left one is **classical data processing** — Wave 1's `affinity_le_binaryAffinity` composed
  with `poissonBhattacharyya_eq`: the distinguishability lost by collapsing the whole count
  record to a binary decision;
* the right one is **quantum**, and is where the word "quantum" is earned. It is
  `QuantumNetwork.quarter_sqrtFidelity_sq_le_povmAvgError` — the Holevo–Helstrom optimum
  `½(1 − D(ρ₀,ρ₁))` (least over *all* two-outcome POVMs, `helstrom_isLeast_povmAvgError`)
  combined with Fuchs–van de Graaf `D ≤ √(1 − F²)` — instantiated at these two diagonal states
  and at the one POVM the classical rule actually performs
  (`povmAvgError_diagonal_eq_avgAssignmentError`). It is **not** a re-expression of Wave 1's
  two-outcome AM–GM step: `binaryAffinity_sq_le_two_mul_add` is not called here, and the bound
  being restricted holds for arbitrary (non-commuting) density operators and arbitrary POVMs.

The distinction matters: without the second bullet the "quantum" content would be notational —
`pushforwardFidelity_eq_binaryAffinity` proves `F` of these states *equals* the classical binary
affinity, so a classical proof of the same inequality would establish nothing quantum. What makes
it a restriction is that the inequality being restricted is proved for objects the diagonal case
does not exhaust.

An `OptimalHypothesisRate` specialization is **not** available and is not attempted: that value
is `[Fintype d]`-bound and asymmetric (Neyman–Pearson), whereas Poisson lives on `ℕ` and Wave 1
bounds the symmetric Bayes/Le Cam average error. -/
theorem poissonFloor_le_diagonalQuantumBound {Nb Na : ℝ≥0} {δ : ℕ → ℝ} (hδ : IsCountRule δ) :
    (1 / 4) * Real.exp (-(√(Na : ℝ) - √(Nb : ℝ)) ^ 2)
        ≤ (1 / 4) * sqrtFidelity (binaryPSD (falseAlarm_mem_Icc (r := Nb) hδ))
            (binaryPSD (one_sub_missProb_mem_Icc (r := Na) hδ)) ^ 2
      ∧ (1 / 4) * sqrtFidelity (binaryPSD (falseAlarm_mem_Icc (r := Nb) hδ))
            (binaryPSD (one_sub_missProb_mem_Icc (r := Na) hδ)) ^ 2
          ≤ avgAssignmentError (falseAlarm Nb δ) (missProb Na δ) := by
  have hFA := falseAlarm_mem_Icc (r := Nb) hδ
  have h1MP := one_sub_missProb_mem_Icc (r := Na) hδ
  refine ⟨?_, ?_⟩
  · -- classical data processing: BC(Poisson Nb, Poisson Na) ≤ binary affinity = F(ρ₀,ρ₁)
    have hF := pushforwardFidelity_eq_binaryAffinity (e₀ := falseAlarm Nb δ) (e₁ := missProb Na δ)
      hFA h1MP
    have hCS := affinity_le_binaryAffinity (p := poissonPMFReal Nb) (q := poissonPMFReal Na)
      (fun _ => poissonPMFReal_nonneg) (fun _ => poissonPMFReal_nonneg)
      (poissonPMFRealSum Nb) (poissonPMFRealSum Na) hδ (hasSum_falseAlarm hδ) (hasSum_missProb hδ)
    rw [poissonBhattacharyya_eq, ← hF] at hCS
    have hexp : Real.exp (-(√(Nb : ℝ) - √(Na : ℝ)) ^ 2 / 2) ^ 2
        = Real.exp (-(√(Na : ℝ) - √(Nb : ℝ)) ^ 2) := by
      rw [sq, ← Real.exp_add]; congr 1; ring
    have := mul_self_le_mul_self (Real.exp_pos _).le hCS
    rw [← sq, ← sq, hexp] at this
    linarith
  · -- the quantum step: Holevo–Helstrom + Fuchs–van de Graaf, restricted to the diagonal POVM
    have hq := quarter_sqrtFidelity_sq_le_povmAvgError (binaryDensityOperator h1MP)
      (binaryDensityOperator hFA) isBinaryPOVM_declareSignal
    rw [povmAvgError_diagonal_eq_avgAssignmentError,
      sqrtFidelity_comm (binaryPSD h1MP) (binaryPSD hFA)] at hq
    exact hq

/-! ## Shot-noise PSD algebra -/

/-- **One-sided shot-noise PSD at a reference plane**, `S = 2·E_ph·P`. The leading `2` is the
one-sided convention (a two-sided PSD would carry `1`); it is fixed here once and carried in
every statement below rather than being left to a docstring. -/
noncomputable def shotPSD (E_ph P : ℝ) : ℝ := 2 * E_ph * P

/-- **The one-sided prefactor agrees with the repository's.** `shotPSD E_ph P` is the
unit-greybody, unit-occupation case of `GrapheneNoiseFormula.hawkingNoisePSD` — *propositionally*,
not definitionally: the proof needs `mul_one` twice, so `:= rfl` does not close it. Its leading
`2` is the same one-sided convention (its companion `johnsonNyquistPSD = 4·k_BT·σ_Q` carries the
matching `4`).

**Exactly what this pins (Stage-13, corrected 2026-07-29).** `hawkingNoisePSD a b c d` is the
plain product `2·a·b·c·d`, hence *symmetric in all four arguments*. So this identity is invariant
under every permutation of them, and it therefore pins only

* the leading numeral `2` — a `shotPSD` with any other prefactor breaks the line; and
* the monomial degree — that the greybody and occupation slots are set to `1`, not to `P`.

It pins **nothing about slot identity**: the earlier docstring's "change either definition's
convention and this line fails" was too strong, since swapping which argument carries the optical
power leaves the statement true. No slot-identifying statement is available here (a symmetric
function admits none), and none is claimed. In particular this does **not** assert that the
optical power `P` and the quantum-conductance slot `σ_Q` are the same physical quantity — they are
not. Physical identification of any slot remains the consuming phase's declared hypothesis, per
the module guardrail. -/
theorem shotPSD_eq_hawkingNoisePSD (E_ph P : ℝ) :
    shotPSD E_ph P = SKEFTHawking.GrapheneNoiseFormula.hawkingNoisePSD E_ph P 1 1 := by
  unfold shotPSD SKEFTHawking.GrapheneNoiseFormula.hawkingNoisePSD
  ring

/-- **Reference-plane transfer.** Referring an incident optical power to the absorbed plane
through a transfer factor `η` scales the one-sided shot PSD by exactly `η`. The factor is an
explicit argument, never absorbed into `shotPSD`.

No sign or range hypothesis on `η`: the identity is pure algebra and any `0 ≤ η ≤ 1`
side-condition would be an unused hypothesis.

**Honest accounting (Stage-13, 2026-07-28; corrected 2026-07-29).** This theorem is one `ring`
call and it does **not** test the one-sided `2`: the same statement holds verbatim for
`shotPSD' E P = 7·E·P`, so the constant is untested *here*. The `2` is pinned separately by
`shotPSD_eq_hawkingNoisePSD` against `GrapheneNoiseFormula`. What this theorem does carry is the
*placement* of `η` — outside the definition, as an explicit transfer factor rather than baked in.

What it does **not** carry is any tie to the count model. `thinnedMean_eq_eta_mul` was previously
cited here as supplying that tie; it does not, because its `η` is a *separately bound* `ℝ≥0` while
this one is an unconstrained `ℝ` — two theorems about two different variables that happen to share
a name. The statement that genuinely binds one `η` and uses it in both carriers is
`shotPSD_thinnedMean_same_eta`. -/
theorem shotPSD_plane_transfer (E_ph P η : ℝ) : shotPSD E_ph (η * P) = η * shotPSD E_ph P := by
  unfold shotPSD
  ring

/-- A shot-noise PSD at a plane carrying positive power is positive. Discharged *through* the
convention bridge, by the repo's `GrapheneNoiseFormula.hawkingNoisePSD_pos` rather than by a
bare `positivity` — so the cross-module reference in `shotPSD_eq_hawkingNoisePSD` is exercised
by a proof and cannot rot into a stale docstring. -/
theorem shotPSD_pos {E_ph P : ℝ} (hE : 0 < E_ph) (hP : 0 < P) : 0 < shotPSD E_ph P := by
  rw [shotPSD_eq_hawkingNoisePSD]
  exact SKEFTHawking.GrapheneNoiseFormula.hawkingNoisePSD_pos E_ph P 1 1 hE hP one_pos one_pos

/-! ## Poisson thinning (pmf level) -/

/-- **Poisson thinning, at the level of the pmf.** Binomially retaining each of `Poisson N`
counts with weight `η` produces `Poisson (η·N)`:
`∑ₘ Poisson(N)ₘ · C(m,n) · ηⁿ · (1−η)^{m−n} = Poisson(ηN)ₙ`.

**No `η ≤ 1` hypothesis.** Reindexing `m = n + k` gives
`e^{−N}(ηN)ⁿ/n! · ∑ₖ (N(1−η))ᵏ/k! = e^{−N}(ηN)ⁿ/n!·e^{N(1−η)} = e^{−ηN}(ηN)ⁿ/n!`, and the
exponential series converges absolutely for every real argument, so neither the algebra nor the
summability ever consults `η ≤ 1`. Adding it would ship an unused hypothesis; dropping it makes
the theorem strictly stronger. `η ≤ 1` is what licenses *reading* the kernel as a probability,
which is a consuming phase's declared hypothesis, not a fact about this identity.

The truncated subtraction `m − n` is harmless: every `m < n` term is killed by `m.choose n = 0`.

Stated in `HasSum` form, which is the workhorse: it carries the summability that every
downstream rewrite needs (the `tsum` form is `poisson_thinning`). -/
theorem hasSum_poisson_thinning (N η : ℝ≥0) (n : ℕ) :
    HasSum
      (fun m : ℕ => poissonPMFReal N m * (m.choose n : ℝ) * (η : ℝ) ^ n * (1 - (η : ℝ)) ^ (m - n))
      (poissonPMFReal (η * N) n) := by
  have hstep : ∀ j : ℕ, poissonPMFReal N (j + n) * (((j + n).choose n : ℕ) : ℝ) * (η : ℝ) ^ n
        * (1 - (η : ℝ)) ^ (j + n - n)
      = (Real.exp (-(N : ℝ)) * ((η : ℝ) * (N : ℝ)) ^ n / (n ! : ℝ))
        * (((N : ℝ) * (1 - (η : ℝ))) ^ j / (j ! : ℝ)) := by
    intro j
    have hc : ((j + n).choose n : ℕ) * n ! * j ! = (j + n)! := by
      have h := Nat.choose_mul_factorial_mul_factorial (Nat.le_add_left n j)
      rwa [Nat.add_sub_cancel] at h
    have hcR : (((j + n).choose n : ℕ) : ℝ) * (n ! : ℝ) * (j ! : ℝ) = ((j + n)! : ℝ) := by
      exact_mod_cast congrArg (fun x : ℕ => (x : ℝ)) hc
    have hn0 : ((n ! : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    have hj0 : ((j ! : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr j.factorial_ne_zero
    have hcpos : (0 : ℝ) < (((j + n).choose n : ℕ) : ℝ) :=
      Nat.cast_pos.mpr (Nat.choose_pos (Nat.le_add_left n j))
    rw [poissonPMFReal, Nat.add_sub_cancel, ← hcR, pow_add]
    simp only [mul_pow]
    field_simp
  have hser : HasSum (fun j : ℕ => ((N : ℝ) * (1 - (η : ℝ))) ^ j / (j ! : ℝ))
      (Real.exp ((N : ℝ) * (1 - (η : ℝ)))) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  have hconst : Real.exp (-(N : ℝ)) * ((η : ℝ) * (N : ℝ)) ^ n / (n ! : ℝ)
      * Real.exp ((N : ℝ) * (1 - (η : ℝ))) = poissonPMFReal (η * N) n := by
    rw [poissonPMFReal, NNReal.coe_mul]
    rw [show Real.exp (-(N : ℝ)) * ((η : ℝ) * (N : ℝ)) ^ n / (n ! : ℝ)
          * Real.exp ((N : ℝ) * (1 - (η : ℝ)))
        = (Real.exp (-(N : ℝ)) * Real.exp ((N : ℝ) * (1 - (η : ℝ))))
          * ((η : ℝ) * (N : ℝ)) ^ n / (n ! : ℝ) by ring]
    rw [← Real.exp_add,
      show -(N : ℝ) + (N : ℝ) * (1 - (η : ℝ)) = -((η : ℝ) * (N : ℝ)) by ring]
  have hshift := (hser.mul_left
    (Real.exp (-(N : ℝ)) * ((η : ℝ) * (N : ℝ)) ^ n / (n ! : ℝ)))
  rw [hconst] at hshift
  have hshift' : HasSum (fun j : ℕ => poissonPMFReal N (j + n) * (((j + n).choose n : ℕ) : ℝ)
      * (η : ℝ) ^ n * (1 - (η : ℝ)) ^ (j + n - n)) (poissonPMFReal (η * N) n) := by
    simpa only [hstep] using hshift
  have hvanish : ∀ i ∈ Finset.range n,
      poissonPMFReal N i * ((i.choose n : ℕ) : ℝ) * (η : ℝ) ^ n * (1 - (η : ℝ)) ^ (i - n) = 0 := by
    intro i hi
    rw [Nat.choose_eq_zero_of_lt (Finset.mem_range.mp hi)]
    simp
  have hmain := (hasSum_nat_add_iff (f := fun m : ℕ => poissonPMFReal N m * ((m.choose n : ℕ) : ℝ)
    * (η : ℝ) ^ n * (1 - (η : ℝ)) ^ (m - n)) n).mp hshift'
  rw [Finset.sum_congr rfl hvanish, Finset.sum_const_zero, add_zero] at hmain
  exact hmain

/-- **Poisson thinning, `tsum` form** — see `hasSum_poisson_thinning` for the statement's
content and for why no `η ≤ 1` hypothesis appears. -/
theorem poisson_thinning (N η : ℝ≥0) (n : ℕ) :
    ∑' m : ℕ, poissonPMFReal N m * (m.choose n : ℝ) * (η : ℝ) ^ n * (1 - (η : ℝ)) ^ (m - n)
      = poissonPMFReal (η * N) n :=
  (hasSum_poisson_thinning N η n).tsum_eq

/-! ## Poisson moments and the mean = variance scaling -/

/-- The mean count of a `Poisson N` source, defined as the first moment of the pmf (not as `N`
by fiat — see `poissonMean_eq`). -/
noncomputable def poissonMean (N : ℝ≥0) : ℝ := ∑' n : ℕ, poissonPMFReal N n * (n : ℝ)

/-- The variance of a `Poisson N` source, defined **independently** as the second central
moment of the pmf about its own mean. Defining it this way (rather than as `N`) is what gives
`poissonVariance_eq` content: it is a computation, not a definitional restatement.

*(This docstring previously justified a theorem named shot_variance_eq_mean
(de-backticked: it no longer exists), deleted 2026-07-29 as an
identity wrapper — its proof was one `rw` composing `poissonVariance_eq` and `poissonMean_eq`,
both of which already state `= (N : ℝ)`, and it had no consumers. The filtered-count layer
`shotFilteredMean_le_variance` / `shotFilteredVariance_boxcar_eq_mean` /
`shotFilteredVariance_ramp_gt_mean` carries the real content: variance equals the mean for the
boxcar only.)* -/
noncomputable def poissonVariance (N : ℝ≥0) : ℝ :=
  ∑' n : ℕ, poissonPMFReal N n * ((n : ℝ) - poissonMean N) ^ 2

/-- First moment: `∑ₙ n·Poisson(N)ₙ = N`. -/
theorem hasSum_poissonPMFReal_mul_id (N : ℝ≥0) :
    HasSum (fun n : ℕ => poissonPMFReal N n * (n : ℝ)) (N : ℝ) := by
  have hstep : ∀ n : ℕ, poissonPMFReal N (n + 1) * ((n + 1 : ℕ) : ℝ)
      = (N : ℝ) * poissonPMFReal N n := by
    intro n
    have hfac : ((n + 1)! : ℝ) = ((n + 1 : ℕ) : ℝ) * (n ! : ℝ) := by
      rw [Nat.factorial_succ]; push_cast; ring
    have hne : ((n + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    rw [poissonPMFReal, poissonPMFReal, hfac]
    field_simp
    ring
  -- v4.32: `poissonPMFRealSum` is now a deprecated *alias* of `hasSum_one_poissonMeasure`, whose
  -- statement spells the summand out (`exp (-N) * N ^ n / n !`) instead of `poissonPMFReal N n`.
  -- Re-fold it through an explicitly-typed `have` so `simpa only [hstep]` matches again.
  have hone : HasSum (fun n : ℕ => poissonPMFReal N n) 1 := poissonPMFRealSum N
  have hsum : HasSum (fun n : ℕ => poissonPMFReal N (n + 1) * ((n + 1 : ℕ) : ℝ)) ((N : ℝ) * 1) := by
    simpa only [hstep] using hone.mul_left (N : ℝ)
  have := (hasSum_nat_add_iff (f := fun n : ℕ => poissonPMFReal N n * (n : ℝ)) 1).mp (by
    simpa using hsum)
  simpa using this

/-- Second factorial moment: `∑ₙ n(n−1)·Poisson(N)ₙ = N²`. -/
theorem hasSum_poissonPMFReal_mul_descFactorial (N : ℝ≥0) :
    HasSum (fun n : ℕ => poissonPMFReal N n * ((n : ℝ) * ((n : ℝ) - 1))) ((N : ℝ) ^ 2) := by
  have hstep : ∀ n : ℕ, poissonPMFReal N (n + 2) * (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1))
      = (N : ℝ) ^ 2 * poissonPMFReal N n := by
    intro n
    have hfac : ((n + 2)! : ℝ) = (((n : ℝ) + 2) * ((n : ℝ) + 1)) * (n ! : ℝ) := by
      rw [Nat.factorial_succ, Nat.factorial_succ]; push_cast; ring
    rw [poissonPMFReal, poissonPMFReal, hfac]
    have h1 : ((n : ℝ) + 2) ≠ 0 := by positivity
    have h2 : ((n : ℝ) + 1) ≠ 0 := by positivity
    have h3 : ((n ! : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr n.factorial_ne_zero
    push_cast
    field_simp
    ring
  -- Same v4.32 re-folding as in `hasSum_poissonPMFReal_mul_id`.
  have hone : HasSum (fun n : ℕ => poissonPMFReal N n) 1 := poissonPMFRealSum N
  have hsum : HasSum
      (fun n : ℕ => poissonPMFReal N (n + 2) * (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1)))
      ((N : ℝ) ^ 2 * 1) := by
    simpa only [hstep] using hone.mul_left ((N : ℝ) ^ 2)
  have := (hasSum_nat_add_iff
    (f := fun n : ℕ => poissonPMFReal N n * ((n : ℝ) * ((n : ℝ) - 1))) 2).mp (by simpa using hsum)
  simpa [Finset.sum_range_succ] using this

/-- **The Poisson mean is the rate.** -/
theorem poissonMean_eq (N : ℝ≥0) : poissonMean N = (N : ℝ) :=
  (hasSum_poissonPMFReal_mul_id N).tsum_eq

/-- The mean of a `Poisson (η·N)` law is `η` times the mean of `Poisson N`. Pure consequence of
`poissonMean_eq`; it says nothing on its own about *thinning* — the statement that the thinned
law has this mean is `thinnedMean_eq_eta_mul`, which is the one that calls `poisson_thinning`. -/
theorem poissonMean_thinning (N η : ℝ≥0) : poissonMean (η * N) = (η : ℝ) * poissonMean N := by
  rw [poissonMean_eq, poissonMean_eq, NNReal.coe_mul]

/-- **The `η` of the plane transfer IS the `η` of the thinning — one transfer factor, two
carriers.** The mean of the *thinned* law — the law built by independently retaining each count
with probability `η`, written out as its defining sum — is exactly `η` times the original mean.
This is the theorem that makes referring shot noise across a reference plane consistent with
referring the count statistics across it: `shotPSD_plane_transfer` scales the one-sided shot PSD
by `η`, and this scales the count mean by the *same* `η`.

Unlike `poissonMean_thinning` (which is mean algebra on an already-`Poisson (η·N)` law), this
statement **calls `poisson_thinning`**: the thinning sum is reduced to `poissonPMFReal (η * N)`
before the mean is taken. Without it, the `η` of `shotPSD_plane_transfer` would be a bare
algebraic parameter with no proved tie to the count model.

**It is still not the bridge on its own** (Stage-13, 2026-07-29). This theorem's `η` is `ℝ≥0`
while `shotPSD_plane_transfer`'s is `ℝ`; two theorems about two separately-bound variables that
happen to share a name assert nothing about each other, and the PSD `η` even ranges over values
this one cannot represent. The single statement that binds *one* `η` and uses it in *both*
carriers is `shotPSD_thinnedMean_same_eta`. -/
theorem thinnedMean_eq_eta_mul (N η : ℝ≥0) :
    (∑' n : ℕ, (∑' m : ℕ, poissonPMFReal N m * (m.choose n : ℝ) * (η : ℝ) ^ n
        * (1 - (η : ℝ)) ^ (m - n)) * (n : ℝ)) = (η : ℝ) * poissonMean N := by
  simp only [poisson_thinning]
  rw [show (∑' n : ℕ, poissonPMFReal (η * N) n * (n : ℝ)) = poissonMean (η * N) from rfl,
    poissonMean_eq, poissonMean_eq, NNReal.coe_mul]

/-- **One transfer factor, two carriers — with one binder.** A *single* retention weight `η : ℝ≥0`
is used simultaneously in the reference-plane PSD transfer and in the thinning kernel, and the
resulting cross-carrier identity holds:

    S(η·P) · E[n]  =  S(P) · E[thinned n]

Both sides equal `η · S(P) · E[n]`, which is exactly the content: the factor by which referring
the optical power across the plane scales the shot PSD is the *same number* as the factor by which
retaining counts with weight `η` scales the count mean.

**Why this statement and not the conjunction of the two.** `shotPSD_plane_transfer` binds
`η : ℝ` and `thinnedMean_eq_eta_mul` binds `η : ℝ≥0`; separately bound variables sharing a name
assert nothing about each other, so their conjunction is not a bridge. Here the coercion
`(η : ℝ)` of one `ℝ≥0` binder appears in both carriers, so the theorem is false if either scaling
law changes — see `shotPSD_thinnedMean_eta_exponent_load_bearing`, which breaks it by squaring the
PSD-side factor alone.

`ℝ≥0` is the honest home for the shared binder: a retention weight cannot be negative (the
thinning kernel would not be a kernel), whereas the PSD identity is pure algebra valid for any
real. So the bridge instantiates the *more general* carrier at the *more constrained* one, rather
than weakening either. -/
theorem shotPSD_thinnedMean_same_eta (E_ph P : ℝ) (N η : ℝ≥0) :
    shotPSD E_ph ((η : ℝ) * P) * poissonMean N
      = shotPSD E_ph P * ∑' n : ℕ, (∑' m : ℕ, poissonPMFReal N m * (m.choose n : ℝ)
          * (η : ℝ) ^ n * (1 - (η : ℝ)) ^ (m - n)) * (n : ℝ) := by
  rw [shotPSD_plane_transfer, thinnedMean_eq_eta_mul]
  ring

/-- **The shared-`η` bridge is falsifiable in its exponent.** Squaring the transfer factor on the
PSD side alone breaks `shotPSD_thinnedMean_same_eta` at `E_ph = P = N = 1`, `η = 1/2`: the left
side becomes `1/2` while the right stays `1`. So the identity is not an artefact of both sides
being "some function of `η`" — it pins the two scaling exponents to be equal. -/
theorem shotPSD_thinnedMean_eta_exponent_load_bearing :
    shotPSD 1 (((1 / 2 : ℝ≥0) : ℝ) ^ 2 * 1) * poissonMean 1
      ≠ shotPSD 1 1 * ∑' n : ℕ, (∑' m : ℕ, poissonPMFReal 1 m * (m.choose n : ℝ)
          * ((1 / 2 : ℝ≥0) : ℝ) ^ n * (1 - ((1 / 2 : ℝ≥0) : ℝ)) ^ (m - n)) * (n : ℝ) := by
  rw [thinnedMean_eq_eta_mul, poissonMean_eq, shotPSD, shotPSD]
  push_cast
  norm_num

/-- **The Poisson variance is the rate** — computed from the independently-defined second
central moment, via `E[n(n−1)] = N²` and `E[n] = N`. -/
theorem poissonVariance_eq (N : ℝ≥0) : poissonVariance N = (N : ℝ) := by
  have hA := hasSum_poissonPMFReal_mul_descFactorial N
  have hB := (hasSum_poissonPMFReal_mul_id N).mul_left (1 - 2 * (N : ℝ))
  -- Same v4.32 re-folding as in `hasSum_poissonPMFReal_mul_id`.
  have hone : HasSum (fun n : ℕ => poissonPMFReal N n) 1 := poissonPMFRealSum N
  have hC := hone.mul_left ((N : ℝ) ^ 2)
  have hsum := (hA.add hB).add hC
  have hfun : (fun n : ℕ => poissonPMFReal N n * ((n : ℝ) * ((n : ℝ) - 1))
        + (1 - 2 * (N : ℝ)) * (poissonPMFReal N n * (n : ℝ)) + (N : ℝ) ^ 2 * poissonPMFReal N n)
      = fun n : ℕ => poissonPMFReal N n * ((n : ℝ) - poissonMean N) ^ 2 := by
    funext n
    rw [poissonMean_eq]
    ring
  rw [hfun] at hsum
  have hval : (N : ℝ) ^ 2 + (1 - 2 * (N : ℝ)) * (N : ℝ) + (N : ℝ) ^ 2 * 1 = (N : ℝ) := by ring
  rw [hval] at hsum
  exact hsum.tsum_eq

/-! ## The filtered count: Fano factor and the boxcar

**Correction (Stage-13, 2026-07-29).** Earlier text in this module asserted a "filtered-count
(`N_eff`) normalization" and a bare shot_variance_eq_mean : poissonVariance N = poissonMean N (removed).
Both were wrong-headed and are removed. `N_eff` was never defined anywhere in the Detection layer;
and the unfiltered identity was a one-`rw` composition of `poissonVariance_eq` and `poissonMean_eq`
(both of which state `= (N : ℝ)`), with no consumers — the identity-wrapper anti-pattern.

Worse, the physics it gestured at is false as stated: a *filtered* shot count does not have
variance equal to its mean. By Campbell's theorem the filtered output has mean `λ∫h` and variance
`λ∫h²`, so at matched DC gain the Fano factor is `∫h²/∫h ≥ 1` — **equality only for the boxcar**.
That is the content shipped below.
-/

open MeasureTheory in
/-- **Campbell's theorem for a filtered shot-noise count, declared as an explicit hypothesis.**
`M h` and `V h` are the mean and the variance of the output of a Poisson point source of rate
`lam` read out through the filter `h` over the window `[0,T]`:

    M h = lam · ∫₀ᵀ h        V h = lam · ∫₀ᵀ h²

*Why a `Prop` parameter and not a derived object.* Exactly the reasoning of the sibling
`FilterFloors.IsWhiteFilteredVariance`: the repo models no point processes, and Mathlib at pin
carries no Campbell theory (no shot-noise second-moment formula for a filtered Poisson process),
so an "abstract filtered-count moment functional" would have to be built from scratch to state
what is, physically, a modelling assumption about the source. Carrying it as a declared hypothesis
keeps it visible in every consuming binder list.

*Substantive load, disclosed.* Campbell's theorem itself — that the two moments take these forms —
lives in this definition. What the theorems below add is the *shape* consequence: the
Cauchy–Schwarz comparison of `∫h²` against `∫h` and its boxcar equality case. -/
def IsShotFilteredMoments (M V : (ℝ → ℝ) → ℝ) (lam T : ℝ) : Prop :=
  (∀ h : ℝ → ℝ, M h = lam * ∫ x in (0:ℝ)..T, h x)
    ∧ ∀ h : ℝ → ℝ, V h = lam * ∫ x in (0:ℝ)..T, h x ^ 2

open MeasureTheory in
/-- **A filtered shot count is never sub-Poissonian: `mean ≤ variance` at matched DC gain.**

Normalising the filter to the boxcar's DC gain (`∫₀ᵀ h = T`), the filtered count's variance
`lam·∫h²` is at least its mean `lam·T`, by the interval Cauchy–Schwarz bound
`FilterFloors.sq_integral_le`. So "Fano factor 1" is not a property of filtered shot noise; it is
an upper-extreme case, saturated by exactly one filter shape. -/
theorem shotFilteredMean_le_variance {M V : (ℝ → ℝ) → ℝ} {lam T : ℝ} (hlam : 0 ≤ lam)
    (hT : 0 < T) (hmom : IsShotFilteredMoments M V lam T) (h : ℝ → ℝ)
    (hint : IntervalIntegrable h volume 0 T)
    (hsq : IntervalIntegrable (fun x => h x ^ 2) volume 0 T)
    (hDC : (∫ x in (0:ℝ)..T, h x) = T) :
    M h ≤ V h := by
  have hCS := sq_integral_le h T hT hint hsq
  rw [hDC] at hCS
  have hTle : T ≤ ∫ x in (0:ℝ)..T, h x ^ 2 := by
    have := (mul_le_mul_iff_of_pos_left hT).mp (by nlinarith [hCS] :
      T * T ≤ T * ∫ x in (0:ℝ)..T, h x ^ 2)
    linarith
  rw [hmom.1 h, hmom.2 h, hDC]
  exact mul_le_mul_of_nonneg_left hTle hlam

/-- **The boxcar saturates it: for the matched single-shot integrator, variance = mean exactly.**
This is where "shot-limited, Fano factor 1" is actually true, and it is the *only* place: the
boxcar is the unique DC-matched shape with `∫h² = ∫h` (`FilterFloors.enbw_eq_half_iff_boxcar`
records the same extremality on the bandwidth side). Hypothesis-free in `lam`. -/
theorem shotFilteredVariance_boxcar_eq_mean {M V : (ℝ → ℝ) → ℝ} {lam T : ℝ} (hT : 0 ≤ T)
    (hmom : IsShotFilteredMoments M V lam T) : V (boxcar T) = M (boxcar T) := by
  rw [hmom.1, hmom.2, integral_boxcar T hT, integral_boxcar_sq T hT]

open MeasureTheory in
/-- **Non-vacuity: a non-boxcar shape is strictly super-Poissonian.** The DC-matched ramp
`h(x) = 2x` on `[0,1]` has `∫h = 1 = T` but `∫h² = 4/3`, so its filtered count's variance exceeds
its mean by a third. `shotFilteredMean_le_variance` is therefore a real inequality, and the claim
"variance = mean for the filtered count" is false as a general statement — which is exactly what
the removed shot_variance_eq_mean (removed) docstring asserted. -/
theorem shotFilteredVariance_ramp_gt_mean {M V : (ℝ → ℝ) → ℝ} {lam : ℝ} (hlam : 0 < lam)
    (hmom : IsShotFilteredMoments M V lam 1) :
    M (fun x => 2 * x) < V (fun x => 2 * x) := by
  have h1 : (∫ x in (0:ℝ)..1, 2 * x) = 1 := by
    rw [intervalIntegral.integral_const_mul, integral_id]; norm_num
  have h2 : (∫ x in (0:ℝ)..1, (2 * x) ^ 2) = 4 / 3 := by
    have : (fun x : ℝ => (2 * x) ^ 2) = fun x : ℝ => 4 * x ^ 2 := by funext x; ring
    rw [this, intervalIntegral.integral_const_mul, integral_pow]
    norm_num
  rw [hmom.1, hmom.2, h1, h2]
  linarith

/-! ## Non-vacuity: the floor family has slack -/

/-- **The Le Cam floor's *value* is strictly exceeded by a genuinely shot-limited Gaussian
model.** At baseline rate `N_b = 1` and signal rate `N_a = 9`, a Gaussian threshold classifier
with means `μ₀ = 1`, `μ₁ = 9`, **branch widths `σ₀ = √N_b` and `σ₁ = √N_a`** and threshold at the
midpoint of the means `t = 5` errs, on average, by more than **3/2 times** the Le Cam floor value
`¼·BC(Poisson 1, Poisson 9)²`.

**"Shot-limited" is in the statement, not the prose (corrected 2026-07-29).** The widths appear
literally as `√(1 : ℝ)` and `√(9 : ℝ)` — each branch carries the standard deviation of *its own*
Poisson law, which is what "shot-limited" means. The previous version used a single common
`σ = 2`, justified only as "the mean of the two shot widths `√1 = 1` and `√9 = 3`", which is not a
derivable surrogate and is not conservative: the common-`σ` model gives branch errors `Q(2)` each
(average `≈ 0.0228`), whereas the true unequal-variance model gives `½(Q(4) + Q(4/3)) ≈ 0.0456` —
a factor of two *larger*. The surrogate understated the error of the model it claimed to describe,
so it is removed rather than kept alongside.

The threshold `t = 5` is the midpoint of the means, which is **not** the likelihood-ratio-optimal
threshold once the widths differ; it is a declared, concrete operating point, and a suboptimal
threshold only raises the error, so it cannot manufacture the strict inequality.

**Scope — read this before citing it.** The Gaussian error pair is NOT claimed to be realizable by
any count rule `δ`, so this does **not** exhibit a count rule whose error strictly exceeds its own
floor; it compares the floor's numeric value against a different (Gaussian) model evaluated at the
same rates. What it certifies is narrower, and the narrowness is the point: at this operating
point the floor's value is strictly below the error of *a* concrete detection model, with a
quantified factor rather than a bare `≠`. It does **not** certify slack against attainable
count-rule error — that would need the realizability this note denies. The theorem that *does*
exhibit slack over the same experiment is `poisson_avgError_equalRates_eq_half`: at coincident
rates every count rule errs exactly `1/2` while the floor returns `1/4`, so the Le Cam constant is
provably loose there by a factor of two.

The statement is a real cross-wave call in both directions: the left side is Wave 1's affinity at
the Poisson pair (discharged through `poissonBhattacharyya_eq`) and the right side is Wave 2's
threshold-error pair, bounded through `gaussianTail_ge_window` (`gaussianQ_two_ge_rational` no
longer suffices: `Q(4/3)` is the load-bearing branch and lies outside its reach). -/
theorem shotGaussian_avgError_gt_leCam_floor :
    (3 / 2) * ((1 / 4) * affinity (poissonPMFReal 1) (poissonPMFReal 9) ^ 2)
      < avgAssignmentError (thrErr0 1 (√(1 : ℝ)) 5) (thrErr1 9 (√(9 : ℝ)) 5) := by
  have h1 : √(1 : ℝ) = 1 := Real.sqrt_one
  have h9 : √(9 : ℝ) = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
  have hBC : affinity (poissonPMFReal 1) (poissonPMFReal 9) ^ 2 = Real.exp (-(4 : ℝ)) := by
    rw [poissonBhattacharyya_eq]
    push_cast
    rw [h1, h9, sq, ← Real.exp_add]
    norm_num
  have hQ : avgAssignmentError (thrErr0 1 (√(1 : ℝ)) 5) (thrErr1 9 (√(9 : ℝ)) 5)
      = (gaussianQ 4 + gaussianQ (4 / 3)) / 2 := by
    unfold avgAssignmentError thrErr0 thrErr1
    rw [h1, h9]
    norm_num
  -- the floor value: exp(4) > 46.875, so ¼·exp(−4) < 1/187.5
  have hexp4 : (46.875 : ℝ) < Real.exp 4 := by
    have he : (2.718 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    have hp : (2.718 : ℝ) ^ 4 < Real.exp 1 ^ 4 := pow_lt_pow_left₀ he (by norm_num) (by norm_num)
    have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h4]
    linarith [hp, show (46.875 : ℝ) < 2.718 ^ 4 by norm_num]
  have hneg : Real.exp (-(4 : ℝ)) = 1 / Real.exp 4 := by
    rw [Real.exp_neg]; exact inv_eq_one_div _
  have hinv : 1 / Real.exp 4 < 1 / 46.875 := one_div_lt_one_div_of_lt (by norm_num) hexp4
  -- the wide branch: Q(4/3) ≥ (2/3)·φ(2) ≥ (2/3)/18.6, via the window bound at c = 2/3
  have hphi : (1 : ℝ) / 18.6 ≤ gaussianPDFReal 0 1 2 := by
    rw [gaussianPDF_std, show -(2 : ℝ) ^ 2 / 2 = -2 by norm_num]
    have hspos : (0 : ℝ) < √(2 * Real.pi) := Real.sqrt_pos.mpr (by positivity)
    have hsle : √(2 * Real.pi) ≤ 2.51 := by
      rw [show (2.51 : ℝ) = √(2.51 ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by nlinarith [Real.pi_lt_d2])
    have hA : (1 : ℝ) / 2.51 ≤ (√(2 * Real.pi))⁻¹ := by
      rw [inv_eq_one_div]; exact one_div_le_one_div_of_le hspos hsle
    have hE1 : Real.exp 1 < 2.7183 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    have hpow : Real.exp 2 = Real.exp 1 ^ 2 := by rw [← Real.exp_nat_mul]; norm_num
    have he2 : Real.exp 2 < 7.4 := by
      rw [hpow]; nlinarith [hE1, Real.exp_pos (1 : ℝ)]
    have hB : (1 : ℝ) / 7.4 ≤ Real.exp (-2) := by
      rw [Real.exp_neg, inv_eq_one_div]
      exact one_div_le_one_div_of_le (Real.exp_pos 2) he2.le
    have hApos : (0 : ℝ) < (√(2 * Real.pi))⁻¹ := by positivity
    nlinarith [hA, hB, hApos, Real.exp_pos (-2 : ℝ)]
  have hwin := gaussianTail_ge_window (z := 4 / 3) (c := 2 / 3) (by norm_num) (by norm_num)
  rw [show (4 : ℝ) / 3 + 2 / 3 = 2 by norm_num] at hwin
  rw [hBC, hQ, hneg]
  linarith [gaussianQ_nonneg 4, hphi, hwin, hinv]

end SKEFTHawking.Detection
