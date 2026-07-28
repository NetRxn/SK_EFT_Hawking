import SKEFTHawking.Detection.PoissonDiscrimination
import SKEFTHawking.Detection.GaussianThreshold
import SKEFTHawking.QuantumNetwork.DiamondNormChoi
import SKEFTHawking.GrapheneNoiseFormula

/-!
# Shot-noise algebra and the quantum seam (Phase 6EA, Wave 3)

Two independent strands, joined by the file's guardrail:

**The quantum seam.** The classical discrimination floors of Wave 1 are the *commutative
shadow* of the project's quantum fidelity substrate (`QuantumNetwork/MixedState.lean`). The
bridge is exact: the Uhlmann root fidelity of two **diagonal** density matrices is the classical
Bhattacharyya affinity of their diagonals (`diagonalState_sqrtFidelity_eq_affinity`), and the
Wave-1 Poisson floor factors through the root fidelity of the two-outcome pushforward states
(`poissonFloor_le_diagonalQuantumBound`).

**Shot-noise algebra.** The one-sided shot-noise PSD, its reference-plane transfer under
quantum efficiency `η`, the pmf-level Poisson thinning identity, and the mean/variance
identity in the filtered-count normalization.

## Main results

* `psdSqrt_diagonal` — the PSD square root of a diagonal matrix is the entrywise `√`; the one
  net-new piece of mathematics in the seam, via PSD-square-root uniqueness.
* `diagonalState_sqrtFidelity_eq_affinity` — **(S1)** `F(diag p, diag q) = ∑ᵢ √(pᵢqᵢ)`.
* `pushforwardFidelity_eq_binaryAffinity` — the two-outcome specialization.
* `poissonFloor_le_diagonalQuantumBound` — **(S2)** the Wave-1 Poisson floor is sandwiched:
  it is dominated by a quarter of the squared root fidelity of the diagonal pushforward
  states, which in turn is a floor on the average assignment error.
* `shotPSD`, `shotPSD_eq_hawkingNoisePSD`, `shotPSD_plane_transfer`, `shotPSD_pos` — the
  one-sided shot-noise PSD, its agreement with the repo's `GrapheneNoiseFormula` convention,
  and the `η`-transfer between reference planes.
* `hasSum_poisson_thinning` / `poisson_thinning` — the **pmf-level** thinning identity
  `Poisson N ↦ Poisson (ηN)`, in `HasSum` and `tsum` form.
* `poissonMean_eq`, `poissonVariance_eq`, `shot_variance_eq_mean` — the second-moment
  computation and the resulting mean = variance identity.
* `poissonMean_thinning` — mean algebra on a `Poisson (η·N)` law; `thinnedMean_eq_eta_mul` is
  the bridge proper, reducing the *thinning sum* through `poisson_thinning` to show the
  transfer factor of `shotPSD_plane_transfer` is the same `η` that scales the count mean.
* `shotGaussian_avgError_gt_leCam_floor` — a concrete operating point at which a shot-limited
  Gaussian threshold model errs by more than 3/2 of the Le Cam floor **value**, certifying the
  floor is not a disguised equality there. It does *not* exhibit a count rule beating its own
  floor: the Gaussian error pair is not claimed realizable by any `δ` (see the theorem's scope
  note).

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

/-- **(S2) The seam: the Wave-1 Poisson floor factors through a quantum fidelity.** For any
count rule `δ`, push the experiment forward to its two-outcome decision alphabet `Fin 2` and
embed the resulting distributions as diagonal density matrices `ρ₀, ρ₁` (genuinely density
operators — `binaryDensityOperator`). Then

* the classical Poisson floor `¼·exp(−(√N_a − √N_b)²)` is at most `¼·F(ρ₀,ρ₁)²`, and
* `¼·F(ρ₀,ρ₁)²` is itself a floor on the average assignment error.

So the Wave-1 floor is *the diagonal restriction of a quantum two-state discrimination bound*:
the quantum root fidelity sits between the classical exponential floor and the error, and the
first inequality is the data-processing loss of distinguishability incurred by collapsing the
whole count record to a binary decision. Both conjuncts are needed
and neither implies the other — the left one is data processing (Wave 1's
`affinity_le_binaryAffinity` composed with `poissonBhattacharyya_eq`), the right one is the
two-outcome AM–GM step (`binaryAffinity_sq_le_two_mul_add`) transported through
`pushforwardFidelity_eq_binaryAffinity`.

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
  have hMP := missProb_mem_Icc (r := Na) hδ
  have hF := pushforwardFidelity_eq_binaryAffinity (e₀ := falseAlarm Nb δ) (e₁ := missProb Na δ)
    hFA (one_sub_missProb_mem_Icc (r := Na) hδ)
  have hCS := affinity_le_binaryAffinity (p := poissonPMFReal Nb) (q := poissonPMFReal Na)
    (fun _ => poissonPMFReal_nonneg) (fun _ => poissonPMFReal_nonneg)
    (poissonPMFRealSum Nb) (poissonPMFRealSum Na) hδ (hasSum_falseAlarm hδ) (hasSum_missProb hδ)
  rw [poissonBhattacharyya_eq, ← hF] at hCS
  have hAM := binaryAffinity_sq_le_two_mul_add hFA hMP
  rw [← hF] at hAM
  have hexp : Real.exp (-(√(Nb : ℝ) - √(Na : ℝ)) ^ 2 / 2) ^ 2
      = Real.exp (-(√(Na : ℝ) - √(Nb : ℝ)) ^ 2) := by
    rw [sq, ← Real.exp_add]; congr 1; ring
  refine ⟨?_, ?_⟩
  · have := mul_self_le_mul_self (Real.exp_pos _).le hCS
    rw [← sq, ← sq, hexp] at this
    linarith
  · unfold avgAssignmentError
    linarith

/-! ## Shot-noise PSD algebra -/

/-- **One-sided shot-noise PSD at a reference plane**, `S = 2·E_ph·P`. The leading `2` is the
one-sided convention (a two-sided PSD would carry `1`); it is fixed here once and carried in
every statement below rather than being left to a docstring. -/
noncomputable def shotPSD (E_ph P : ℝ) : ℝ := 2 * E_ph * P

/-- **The one-sided convention agrees with the repository's.** `shotPSD E_ph P` is definitionally
the unit-greybody, unit-occupation case of `GrapheneNoiseFormula.hawkingNoisePSD`, whose leading
`2` is the same one-sided convention (its companion `johnsonNyquistPSD = 4·k_BT·σ_Q` carries the
matching `4`). Stating this as a theorem is what makes "matches the repo convention" checkable
instead of a claim in prose: change either definition's convention and this line fails.

**Scope (Stage-13, 2026-07-28):** this is an identity between two *dimensionless real formulas*,
asserting agreement of the one-sided prefactor and nothing more. It does **not** assert that the
optical power `P` of `shotPSD` and the quantum-conductance slot `σ_Q` of `hawkingNoisePSD` are
the same physical quantity — they are not, and no such identification is claimed anywhere in this
file. Physical identification of any slot remains the consuming phase's declared hypothesis, per
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

**Honest accounting (Stage-13, 2026-07-28).** This theorem is one `ring` call and it does **not**
test the one-sided `2`: the same statement holds verbatim for `shotPSD' E P = 7·E·P`, so the
constant is untested *here*. The `2` is pinned separately and genuinely, by
`shotPSD_eq_hawkingNoisePSD` against `GrapheneNoiseFormula`. What this theorem does carry is the
*placement* of `η` — outside the definition, as an explicit transfer factor rather than baked in.
And what makes that `η` more than a bare algebraic parameter is `thinnedMean_eq_eta_mul` (not
`poissonMean_thinning`, which is mean algebra and calls nothing): it reduces the thinning sum
through `poisson_thinning` and shows the *same* `η` scales the count mean. -/
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
moment of the pmf about its own mean. Defining it this way (rather than as `N`) is what makes
`shot_variance_eq_mean` a theorem with content rather than a tautology. -/
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
  have hsum : HasSum (fun n : ℕ => poissonPMFReal N (n + 1) * ((n + 1 : ℕ) : ℝ)) ((N : ℝ) * 1) := by
    simpa only [hstep] using (poissonPMFRealSum N).mul_left (N : ℝ)
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
  have hsum : HasSum
      (fun n : ℕ => poissonPMFReal N (n + 2) * (((n + 2 : ℕ) : ℝ) * (((n + 2 : ℕ) : ℝ) - 1)))
      ((N : ℝ) ^ 2 * 1) := by
    simpa only [hstep] using (poissonPMFRealSum N).mul_left ((N : ℝ) ^ 2)
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
algebraic parameter with no proved tie to the count model. -/
theorem thinnedMean_eq_eta_mul (N η : ℝ≥0) :
    (∑' n : ℕ, (∑' m : ℕ, poissonPMFReal N m * (m.choose n : ℝ) * (η : ℝ) ^ n
        * (1 - (η : ℝ)) ^ (m - n)) * (n : ℝ)) = (η : ℝ) * poissonMean N := by
  simp only [poisson_thinning]
  rw [show (∑' n : ℕ, poissonPMFReal (η * N) n * (n : ℝ)) = poissonMean (η * N) from rfl,
    poissonMean_eq, poissonMean_eq, NNReal.coe_mul]

/-- **The Poisson variance is the rate** — computed from the independently-defined second
central moment, via `E[n(n−1)] = N²` and `E[n] = N`. -/
theorem poissonVariance_eq (N : ℝ≥0) : poissonVariance N = (N : ℝ) := by
  have hA := hasSum_poissonPMFReal_mul_descFactorial N
  have hB := (hasSum_poissonPMFReal_mul_id N).mul_left (1 - 2 * (N : ℝ))
  have hC := (poissonPMFRealSum N).mul_left ((N : ℝ) ^ 2)
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

/-- **Mean = variance for a shot-limited count**, in the filtered-count (`N_eff`) normalization
— the scaling every downstream dominance argument uses. Substantive because `poissonVariance`
is the second central moment of the pmf, computed independently of the mean
(`hasSum_poissonPMFReal_mul_descFactorial`), not a definitional restatement of `N`. -/
theorem shot_variance_eq_mean (N : ℝ≥0) : poissonVariance N = poissonMean N := by
  rw [poissonVariance_eq, poissonMean_eq]

/-! ## Non-vacuity: the floor family has slack -/

/-- **The Le Cam floor's *value* is strictly exceeded by a shot-limited Gaussian model.** At
baseline rate `N_b = 1` and signal rate `N_a = 9`, a Gaussian threshold classifier with means
`μ₀ = 1`, `μ₁ = 9`, common width `σ = 2` and threshold at the midpoint `t = 5` has both branch
errors equal to `Q(2)`, and its average assignment error exceeds **3/2 times** the Le Cam floor
value `¼·BC(Poisson 1, Poisson 9)²`.

**Scope — read this before citing it.** The Gaussian error pair `(thrErr0 1 2 5, thrErr1 9 2 5)`
is NOT claimed to be realizable by any count rule `δ`, so this does **not** exhibit a count rule
whose error strictly exceeds its own floor; it compares the floor's numeric value against a
different (Gaussian) model evaluated at the same rates. What it certifies is that
`¼·exp(−(√N_a−√N_b)²)` is not an equality in disguise at this operating point — a floor that
coincided with attainable error everywhere would be useless as a screen — and it does so with a
quantified factor rather than a bare `≠`.

The statement is a real cross-wave call in both directions: the left side is Wave 1's affinity at
the Poisson pair (discharged through `poissonBhattacharyya_eq`) and the right side is Wave 2's
threshold-error pair (bounded through `gaussianQ_two_ge_rational`). -/
theorem shotGaussian_avgError_gt_leCam_floor :
    (3 / 2) * ((1 / 4) * affinity (poissonPMFReal 1) (poissonPMFReal 9) ^ 2)
      < avgAssignmentError (thrErr0 1 2 5) (thrErr1 9 2 5) := by
  have h1 : √(1 : ℝ) = 1 := Real.sqrt_one
  have h9 : √(9 : ℝ) = 3 := by
    rw [show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
  have hBC : affinity (poissonPMFReal 1) (poissonPMFReal 9) ^ 2 = Real.exp (-(4 : ℝ)) := by
    rw [poissonBhattacharyya_eq]
    push_cast
    rw [h1, h9, sq, ← Real.exp_add]
    norm_num
  have hQ : avgAssignmentError (thrErr0 1 2 5) (thrErr1 9 2 5) = gaussianQ 2 := by
    unfold avgAssignmentError thrErr0 thrErr1
    norm_num
  have hexp4 : (46.875 : ℝ) < Real.exp 4 := by
    have he : (2.718 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    have hp : (2.718 : ℝ) ^ 4 < Real.exp 1 ^ 4 := pow_lt_pow_left₀ he (by norm_num) (by norm_num)
    have h4 : Real.exp 4 = Real.exp 1 ^ 4 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h4]
    linarith [hp, show (46.875 : ℝ) < 2.718 ^ 4 by norm_num]
  have hneg : Real.exp (-(4 : ℝ)) = 1 / Real.exp 4 := by
    rw [Real.exp_neg]; exact inv_eq_one_div _
  rw [hBC, hQ, hneg]
  have hinv : 1 / Real.exp 4 < 1 / 46.875 :=
    one_div_lt_one_div_of_lt (by norm_num) hexp4
  linarith [gaussianQ_two_ge_rational, hinv]

end SKEFTHawking.Detection
