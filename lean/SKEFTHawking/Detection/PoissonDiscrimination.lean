import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Analysis.Complex.ExponentialBounds
import SKEFTHawking.QuantumNetwork.ReadoutRelaxationBound

/-!
# Poisson discrimination floors (Phase 6EA, Wave 1)

Kernel-verified universal floors for discriminating a `Poisson N_b` baseline from a
`Poisson N_a` signal at equal priors, over **arbitrary (possibly randomized) count-based
decision rules**, plus the two-sided refutation of the folklore exponential form.

## Main results

* `affinity_le_binaryAffinity` — data processing for the Bhattacharyya affinity through an
  arbitrary randomized rule (infinite Cauchy–Schwarz).
* `binaryAffinity_sq_le_two_mul_add` — the two-outcome AM–GM step.
* `avgError_ge_affinity_sq` — the **distribution-free** Le Cam two-point average-error floor.
* `poissonBhattacharyya_hasSum` / `poissonBhattacharyya_eq` — the closed form
  `∑ₙ √(Poisson(a)ₙ · Poisson(b)ₙ) = exp(−(√a − √b)²/2)`.
* `poisson_avgError_floor` — the headline: `(e₀+e₁)/2 ≥ ¼·exp(−(√N_a − √N_b)²)` for every rule;
  `poisson_avgError_floor_equalRates` pins its constant to the falsifiable number `¼`.
* `falseAlarm_zero`, `poisson_darkBaseline_miss_floor` / `_optimum` /
  `darkBaseline_zeroFalseAlarm_load_bearing` (with `isCountRule_thresholdRule` and
  `falseAlarm_thresholdRule_zero`) — the dark-baseline zero-false-alarm optimum, its
  attainment, and the proof that the zero-false-alarm hypothesis is non-droppable.
* `folklore_miss_floor_false`, `folklore_missFloor_beaten_sixfold`, `folkloreGap_split`,
  `folklore_avgFloor_unsound_of_bright`, `folklore_avg_floor_unsound`,
  `folklore_avgFloor_unsound_factor1000` — the two-sided refutation of the folklore floor
  `miss ≥ exp(−(N_a − N_b))`, in both the miss-error and average-error directions.

## Guardrail

Everything here is a **floor or screen on any detector**, stated over abstract count means.
No device claim, no hardware model, no platform assertion: physical identification of an
abstract rate with a measured quantity is the consuming phase's declared hypothesis.

Invariants (Phase 6EA): kernel-pure, zero sorry, no project-local axioms, no `maxHeartbeats`.
-/

namespace SKEFTHawking.Detection

open scoped NNReal Nat

open ProbabilityTheory SKEFTHawking.QuantumNetwork

/-! ## Decision rules and their error functionals -/

/-- A (possibly randomized) count-based decision rule: `δ n` is the probability of declaring
"signal present" on observing count `n`. Deterministic threshold rules are the `{0,1}`-valued
special case (`thresholdRule`); nothing below narrows to them. -/
def IsCountRule (δ : ℕ → ℝ) : Prop := ∀ n, δ n ∈ Set.Icc (0 : ℝ) 1

/-- False-alarm probability of `δ` against a `Poisson r` baseline. -/
noncomputable def falseAlarm (r : ℝ≥0) (δ : ℕ → ℝ) : ℝ := ∑' n, poissonPMFReal r n * δ n

/-- Miss probability of `δ` against a `Poisson r` signal. -/
noncomputable def missProb (r : ℝ≥0) (δ : ℕ → ℝ) : ℝ := ∑' n, poissonPMFReal r n * (1 - δ n)

/-- The deterministic "declare signal iff count ≥ k" rule. -/
def thresholdRule (k : ℕ) : ℕ → ℝ := fun n => if k ≤ n then 1 else 0

/-- Bhattacharyya coefficient (affinity) of two pmfs on `ℕ`. -/
noncomputable def affinity (p q : ℕ → ℝ) : ℝ := ∑' n, √(p n * q n)

/-- Every deterministic threshold counter is an admissible count rule. This is what makes the
`∀ δ, IsCountRule δ → …` quantifier of `poisson_avgError_floor` non-vacuous, and what licenses
the threshold-rule counterexamples of the folklore refutations below: they are refutations by
an *admissible* rule, not by an inadmissible one. -/
theorem isCountRule_thresholdRule (k : ℕ) : IsCountRule (thresholdRule k) := by
  intro n
  by_cases h : k ≤ n <;> simp [thresholdRule, h]

/-- The false-alarm series of any count rule against a Poisson baseline is summable, so
`falseAlarm` really is *the* sum it names. Dominated by the pmf itself. -/
theorem hasSum_falseAlarm {r : ℝ≥0} {δ : ℕ → ℝ} (hδ : IsCountRule δ) :
    HasSum (fun n => poissonPMFReal r n * δ n) (falseAlarm r δ) :=
  (Summable.of_nonneg_of_le (fun n => mul_nonneg poissonPMFReal_nonneg (hδ n).1)
    (fun n => mul_le_of_le_one_right poissonPMFReal_nonneg (hδ n).2)
    (poissonPMFRealSum r).summable).hasSum

/-- The miss series of any count rule against a Poisson signal is summable. -/
theorem hasSum_missProb {r : ℝ≥0} {δ : ℕ → ℝ} (hδ : IsCountRule δ) :
    HasSum (fun n => poissonPMFReal r n * (1 - δ n)) (missProb r δ) :=
  (Summable.of_nonneg_of_le
    (fun n => mul_nonneg poissonPMFReal_nonneg (by linarith [(hδ n).2]))
    (fun n => mul_le_of_le_one_right poissonPMFReal_nonneg (by linarith [(hδ n).1]))
    (poissonPMFRealSum r).summable).hasSum

/-! ## The generic (distribution-free) Le Cam chain -/

/-- **Data processing for the affinity through an arbitrary randomized rule.** Any rule `δ`
collapses the experiment to a two-outcome one with error pair `(e₀, e₁)`; the affinity cannot
decrease. -/
theorem affinity_le_binaryAffinity {p q δ : ℕ → ℝ} {e₀ e₁ : ℝ}
    (hp0 : ∀ n, 0 ≤ p n) (hq0 : ∀ n, 0 ≤ q n)
    (hp : HasSum p 1) (hq : HasSum q 1) (hδ : IsCountRule δ)
    (he₀ : HasSum (fun n => p n * δ n) e₀)
    (he₁ : HasSum (fun n => q n * (1 - δ n)) e₁) :
    affinity p q ≤ √(e₀ * (1 - e₁)) + √((1 - e₀) * e₁) := by
  have hd0 : ∀ n, 0 ≤ δ n := fun n => (hδ n).1
  have hd1 : ∀ n, δ n ≤ 1 := fun n => (hδ n).2
  have hd1' : ∀ n, (0 : ℝ) ≤ 1 - δ n := fun n => by linarith [hd1 n]
  have hqδ : HasSum (fun n => q n * δ n) (1 - e₁) := by
    have h := hq.sub he₁
    have hfun : (fun n => q n - q n * (1 - δ n)) = fun n => q n * δ n := by funext n; ring
    rwa [hfun] at h
  have hpδ : HasSum (fun n => p n * (1 - δ n)) (1 - e₀) := by
    have h := hp.sub he₀
    have hfun : (fun n => p n - p n * δ n) = fun n => p n * (1 - δ n) := by funext n; ring
    rwa [hfun] at h
  have he₀0 : 0 ≤ e₀ := hasSum_le (fun n => mul_nonneg (hp0 n) (hd0 n)) hasSum_zero he₀
  have he₀1 : e₀ ≤ 1 := hasSum_le (fun n => mul_le_of_le_one_right (hp0 n) (hd1 n)) he₀ hp
  unfold affinity
  refine Real.tsum_le_of_sum_le (fun n => Real.sqrt_nonneg _) fun u => ?_
  have hstep : ∀ n ∈ u, √(p n * q n)
      = √(p n * δ n) * √(q n * δ n) + √(p n * (1 - δ n)) * √(q n * (1 - δ n)) := by
    intro n _
    have hpq : (0 : ℝ) ≤ p n * q n := mul_nonneg (hp0 n) (hq0 n)
    have h1 : √(p n * δ n) * √(q n * δ n) = √(p n * q n) * δ n := by
      rw [← Real.sqrt_mul (mul_nonneg (hp0 n) (hd0 n)),
        show p n * δ n * (q n * δ n) = p n * q n * δ n ^ 2 by ring,
        Real.sqrt_mul hpq, Real.sqrt_sq (hd0 n)]
    have h2 : √(p n * (1 - δ n)) * √(q n * (1 - δ n)) = √(p n * q n) * (1 - δ n) := by
      rw [← Real.sqrt_mul (mul_nonneg (hp0 n) (hd1' n)),
        show p n * (1 - δ n) * (q n * (1 - δ n)) = p n * q n * (1 - δ n) ^ 2 by ring,
        Real.sqrt_mul hpq, Real.sqrt_sq (hd1' n)]
    rw [h1, h2]; ring
  rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
  have hA : ∑ n ∈ u, p n * δ n ≤ e₀ :=
    sum_le_hasSum u (fun n _ => mul_nonneg (hp0 n) (hd0 n)) he₀
  have hB : ∑ n ∈ u, q n * δ n ≤ 1 - e₁ :=
    sum_le_hasSum u (fun n _ => mul_nonneg (hq0 n) (hd0 n)) hqδ
  have hC : ∑ n ∈ u, p n * (1 - δ n) ≤ 1 - e₀ :=
    sum_le_hasSum u (fun n _ => mul_nonneg (hp0 n) (hd1' n)) hpδ
  have hD : ∑ n ∈ u, q n * (1 - δ n) ≤ e₁ :=
    sum_le_hasSum u (fun n _ => mul_nonneg (hq0 n) (hd1' n)) he₁
  have hcs1 : ∑ n ∈ u, √(p n * δ n) * √(q n * δ n)
      ≤ √(∑ n ∈ u, p n * δ n) * √(∑ n ∈ u, q n * δ n) :=
    Real.sum_sqrt_mul_sqrt_le u (fun n => mul_nonneg (hp0 n) (hd0 n))
      (fun n => mul_nonneg (hq0 n) (hd0 n))
  have hcs2 : ∑ n ∈ u, √(p n * (1 - δ n)) * √(q n * (1 - δ n))
      ≤ √(∑ n ∈ u, p n * (1 - δ n)) * √(∑ n ∈ u, q n * (1 - δ n)) :=
    Real.sum_sqrt_mul_sqrt_le u (fun n => mul_nonneg (hp0 n) (hd1' n))
      (fun n => mul_nonneg (hq0 n) (hd1' n))
  have hbd1 : √(∑ n ∈ u, p n * δ n) * √(∑ n ∈ u, q n * δ n) ≤ √(e₀ * (1 - e₁)) := by
    rw [Real.sqrt_mul he₀0]
    exact mul_le_mul (Real.sqrt_le_sqrt hA) (Real.sqrt_le_sqrt hB) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
  have hbd2 : √(∑ n ∈ u, p n * (1 - δ n)) * √(∑ n ∈ u, q n * (1 - δ n)) ≤ √((1 - e₀) * e₁) := by
    rw [Real.sqrt_mul (by linarith : (0 : ℝ) ≤ 1 - e₀)]
    exact mul_le_mul (Real.sqrt_le_sqrt hC) (Real.sqrt_le_sqrt hD) (Real.sqrt_nonneg _)
      (Real.sqrt_nonneg _)
  linarith

/-- **Two-outcome AM–GM.** Elementary, pure ℝ, no measure theory. Structural sibling of
`SKEFTHawking.QuantumNetwork.classical_fvdg` (`TV² + BC² ≤ 1`), which this is *not*: the two
statements bound different quantities and neither implies the other cheaply. `classical_fvdg`
is therefore cited but deliberately **not** imported — its file drags in the trace-norm/polar
tower, which `Detection/` has no need of. -/
theorem binaryAffinity_sq_le_two_mul_add {e₀ e₁ : ℝ}
    (h₀ : e₀ ∈ Set.Icc (0 : ℝ) 1) (h₁ : e₁ ∈ Set.Icc (0 : ℝ) 1) :
    (√(e₀ * (1 - e₁)) + √((1 - e₀) * e₁)) ^ 2 ≤ 2 * (e₀ + e₁) := by
  obtain ⟨ha0, ha1⟩ := h₀
  obtain ⟨hb0, hb1⟩ := h₁
  have ha : (0 : ℝ) ≤ e₀ * (1 - e₁) := by nlinarith
  have hb : (0 : ℝ) ≤ (1 - e₀) * e₁ := by nlinarith
  nlinarith [Real.sq_sqrt ha, Real.sq_sqrt hb, Real.sqrt_nonneg (e₀ * (1 - e₁)),
    Real.sqrt_nonneg ((1 - e₀) * e₁), sq_nonneg (√(e₀ * (1 - e₁)) - √((1 - e₀) * e₁))]

/-- **Le Cam two-point average-error floor, distribution-free.** For ANY pair of count
distributions and ANY (possibly randomized) count rule, the equal-prior average error is at
least a quarter of the squared affinity. Stated in the project's canonical error functional
`SKEFTHawking.QuantumNetwork.avgAssignmentError`
(`QuantumNetwork/ReadoutRelaxationBound.lean`), which this generalizes from the relaxation
model to arbitrary count statistics. -/
theorem avgError_ge_affinity_sq {p q δ : ℕ → ℝ} {e₀ e₁ : ℝ}
    (hp0 : ∀ n, 0 ≤ p n) (hq0 : ∀ n, 0 ≤ q n)
    (hp : HasSum p 1) (hq : HasSum q 1) (hδ : IsCountRule δ)
    (he₀ : HasSum (fun n => p n * δ n) e₀)
    (he₁ : HasSum (fun n => q n * (1 - δ n)) e₁) :
    (1 / 4) * (affinity p q) ^ 2 ≤ avgAssignmentError e₀ e₁ := by
  have hd0 : ∀ n, 0 ≤ δ n := fun n => (hδ n).1
  have hd1 : ∀ n, δ n ≤ 1 := fun n => (hδ n).2
  have he₀0 : 0 ≤ e₀ := hasSum_le (fun n => mul_nonneg (hp0 n) (hd0 n)) hasSum_zero he₀
  have he₀1 : e₀ ≤ 1 := hasSum_le (fun n => mul_le_of_le_one_right (hp0 n) (hd1 n)) he₀ hp
  have he₁0 : 0 ≤ e₁ :=
    hasSum_le (fun n => mul_nonneg (hq0 n) (by linarith [hd1 n])) hasSum_zero he₁
  have he₁1 : e₁ ≤ 1 :=
    hasSum_le (fun n => mul_le_of_le_one_right (hq0 n) (by linarith [hd0 n])) he₁ hq
  have hCS := affinity_le_binaryAffinity hp0 hq0 hp hq hδ he₀ he₁
  have hAM := binaryAffinity_sq_le_two_mul_add ⟨he₀0, he₀1⟩ ⟨he₁0, he₁1⟩
  have haff0 : 0 ≤ affinity p q := tsum_nonneg fun n => Real.sqrt_nonneg _
  unfold avgAssignmentError
  nlinarith [hCS, hAM, haff0, Real.sqrt_nonneg (e₀ * (1 - e₁)), Real.sqrt_nonneg ((1 - e₀) * e₁)]

/-! ## The Bhattacharyya identity -/

/-- **Poisson Bhattacharyya coefficient, closed form (`HasSum`).**
`∑ₙ √(Poisson(a)ₙ · Poisson(b)ₙ) = exp(−(√a − √b)²/2)`. The `HasSum` form is the workhorse: it
carries summability, which every downstream rewrite needs. -/
theorem poissonBhattacharyya_hasSum (a b : ℝ≥0) :
    HasSum (fun n => √(poissonPMFReal a n * poissonPMFReal b n))
      (Real.exp (-(√(a : ℝ) - √(b : ℝ)) ^ 2 / 2)) := by
  have hab : (0 : ℝ) ≤ (a : ℝ) * (b : ℝ) := by positivity
  have key : ∀ n : ℕ, √(poissonPMFReal a n * poissonPMFReal b n)
      = Real.exp (-((a : ℝ) + (b : ℝ)) / 2) * (√((a : ℝ) * (b : ℝ)) ^ n / (n ! : ℝ)) := by
    intro n
    have h2 : Real.exp (-((a : ℝ) + (b : ℝ)) / 2) ^ 2
        = Real.exp (-(a : ℝ)) * Real.exp (-(b : ℝ)) := by
      rw [sq, ← Real.exp_add, ← Real.exp_add]
      ring_nf
    have h3 : (√((a : ℝ) * (b : ℝ)) ^ n) ^ 2 = (a : ℝ) ^ n * (b : ℝ) ^ n := by
      rw [← pow_mul, mul_comm n 2, pow_mul, Real.sq_sqrt hab, mul_pow]
    have hsq : poissonPMFReal a n * poissonPMFReal b n
        = (Real.exp (-((a : ℝ) + (b : ℝ)) / 2) * (√((a : ℝ) * (b : ℝ)) ^ n / (n ! : ℝ))) ^ 2 := by
      simp only [poissonPMFReal]
      rw [mul_pow, div_pow, h2, h3]
      ring
    rw [hsq, Real.sqrt_sq (by positivity)]
  have hser : HasSum (fun n : ℕ => √((a : ℝ) * (b : ℝ)) ^ n / (n ! : ℝ))
      (Real.exp (√((a : ℝ) * (b : ℝ)))) := by
    rw [Real.exp_eq_exp_ℝ]
    exact NormedSpace.expSeries_div_hasSum_exp _
  have hconst : Real.exp (-((a : ℝ) + (b : ℝ)) / 2) * Real.exp (√((a : ℝ) * (b : ℝ)))
      = Real.exp (-(√(a : ℝ) - √(b : ℝ)) ^ 2 / 2) := by
    rw [← Real.exp_add, Real.sqrt_mul a.coe_nonneg]
    congr 1
    have hexp : (√(a : ℝ) - √(b : ℝ)) ^ 2
        = (a : ℝ) + (b : ℝ) - 2 * (√(a : ℝ) * √(b : ℝ)) := by
      rw [sub_sq, Real.sq_sqrt a.coe_nonneg, Real.sq_sqrt b.coe_nonneg]
      ring
    rw [hexp]; ring
  have hmul := hser.mul_left (Real.exp (-((a : ℝ) + (b : ℝ)) / 2))
  rw [hconst] at hmul
  exact (funext key : (fun n => √(poissonPMFReal a n * poissonPMFReal b n)) = _) ▸ hmul

/-- Closed form of the Poisson Bhattacharyya coefficient, `tsum` form. -/
theorem poissonBhattacharyya_eq (a b : ℝ≥0) :
    affinity (poissonPMFReal a) (poissonPMFReal b)
      = Real.exp (-(√(a : ℝ) - √(b : ℝ)) ^ 2 / 2) :=
  (poissonBhattacharyya_hasSum a b).tsum_eq

/-! ## The Poisson headline floor -/

/-- **The universal Poisson discrimination floor (Le Cam two-point bound).** For ANY (possibly
randomized) count-based decision rule, the equal-prior average of false-alarm and miss error
satisfies `(e₀+e₁)/2 ≥ ¼·exp(−(√N_a − √N_b)²)`. No false-alarm constraint, no threshold
structure, no monotone-likelihood assumption: the quantifier ranges over every
`δ : ℕ → [0,1]`. -/
theorem poisson_avgError_floor {Nb Na : ℝ≥0} {δ : ℕ → ℝ} (hδ : IsCountRule δ) :
    (1 / 4) * Real.exp (-(√(Na : ℝ) - √(Nb : ℝ)) ^ 2)
      ≤ avgAssignmentError (falseAlarm Nb δ) (missProb Na δ) := by
  have h := avgError_ge_affinity_sq (p := poissonPMFReal Nb) (q := poissonPMFReal Na)
    (fun _ => poissonPMFReal_nonneg) (fun _ => poissonPMFReal_nonneg)
    (poissonPMFRealSum Nb) (poissonPMFRealSum Na) hδ (hasSum_falseAlarm hδ) (hasSum_missProb hδ)
  rw [poissonBhattacharyya_eq] at h
  have hrw : Real.exp (-(√(Nb : ℝ) - √(Na : ℝ)) ^ 2 / 2) ^ 2
      = Real.exp (-(√(Na : ℝ) - √(Nb : ℝ)) ^ 2) := by
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  rwa [hrw] at h

/-- **The floor's constant is not vacuous.** Specialized to two *identical* Poisson sources the
universal floor reads `¼`: no count rule whatsoever — however cleverly randomized — separates
`Poisson N` from `Poisson N` with equal-prior average error below `1/4`. (The truth is `1/2`,
attained by every rule; the Le Cam constant costs a factor of two, and nothing more.) This is
the sanity check that pins the `¼·exp(…)` prefactor to a falsifiable number. -/
theorem poisson_avgError_floor_equalRates {N : ℝ≥0} {δ : ℕ → ℝ} (hδ : IsCountRule δ) :
    (1 / 4 : ℝ) ≤ avgAssignmentError (falseAlarm N δ) (missProb N δ) := by
  simpa using poisson_avgError_floor (Nb := N) (Na := N) hδ

/-! ## Dark baseline (zero-false-alarm optimum) -/

/-- **A dark baseline is a point mass at zero counts**: `Poisson 0` puts all its mass on `n = 0`
(Lean's `0 ^ 0 = 1`), so the false-alarm probability of any rule is exactly its value there.
This is what makes the zero-false-alarm hypothesis of `poisson_darkBaseline_miss_floor` a
constraint on `δ 0` alone. -/
theorem falseAlarm_zero (δ : ℕ → ℝ) : falseAlarm 0 δ = δ 0 := by
  unfold falseAlarm
  rw [tsum_eq_single 0 (fun n hn => by simp [poissonPMFReal, zero_pow hn])]
  simp [poissonPMFReal]

/-- **Dark-baseline zero-false-alarm miss floor.** When the baseline is dark (`N_b = 0`), every
rule with exactly zero false-alarm probability misses with probability at least `exp(−N_a)`.
The zero-false-alarm hypothesis is explicit and non-droppable — see
`darkBaseline_zeroFalseAlarm_load_bearing`. -/
theorem poisson_darkBaseline_miss_floor {Na : ℝ≥0} {δ : ℕ → ℝ}
    (hδ : IsCountRule δ) (hFA : falseAlarm 0 δ = 0) :
    Real.exp (-(Na : ℝ)) ≤ missProb Na δ := by
  have hδ0 : δ 0 = 0 := by rw [← falseAlarm_zero δ]; exact hFA
  have hterm : poissonPMFReal Na 0 * (1 - δ 0) = Real.exp (-(Na : ℝ)) := by
    simp [poissonPMFReal, hδ0]
  calc Real.exp (-(Na : ℝ)) = poissonPMFReal Na 0 * (1 - δ 0) := hterm.symm
    _ ≤ missProb Na δ :=
        le_hasSum (hasSum_missProb hδ) 0
          fun j _ => mul_nonneg poissonPMFReal_nonneg (by linarith [(hδ j).2])

/-- **The floor is attained**, by the ideal unit-threshold counter (`count ≥ 1`): it is a
zero-false-alarm rule whose miss probability is exactly `exp(−N_a)`. -/
theorem poisson_darkBaseline_miss_optimum (Na : ℝ≥0) :
    falseAlarm 0 (thresholdRule 1) = 0 ∧
      missProb Na (thresholdRule 1) = Real.exp (-(Na : ℝ)) := by
  refine ⟨by rw [falseAlarm_zero]; simp [thresholdRule], ?_⟩
  unfold missProb
  rw [tsum_eq_single 0 (fun n hn => by simp [thresholdRule, Nat.one_le_iff_ne_zero.mpr hn])]
  simp [poissonPMFReal, thresholdRule]

/-- **The always-declare rule saturates the false-alarm budget.** `thresholdRule 0` has
false-alarm probability exactly `1` against a dark baseline — the maximal violation of the
zero-false-alarm hypothesis. Together with `isCountRule_thresholdRule` this pins down *which*
hypothesis the counterexample of `darkBaseline_zeroFalseAlarm_load_bearing` drops: it is an
admissible rule that fails only `hFA`. -/
theorem falseAlarm_thresholdRule_zero : falseAlarm 0 (thresholdRule 0) = 1 := by
  rw [falseAlarm_zero]; simp [thresholdRule]

/-- **The zero-false-alarm hypothesis is load-bearing**: drop it and the floor is false. The
always-declare rule (`thresholdRule 0`) misses with probability `0 < exp(−N_a)`. It is an
admissible count rule (`isCountRule_thresholdRule`) whose only defect is a false-alarm
probability of `1` (`falseAlarm_thresholdRule_zero`), so `hFA` — and nothing else — is what
`poisson_darkBaseline_miss_floor` cannot do without. -/
theorem darkBaseline_zeroFalseAlarm_load_bearing (Na : ℝ≥0) :
    missProb Na (thresholdRule 0) < Real.exp (-(Na : ℝ)) := by
  have h : missProb Na (thresholdRule 0) = 0 := by unfold missProb; simp [thresholdRule]
  rw [h]
  exact Real.exp_pos _

/-! ## Refutation of the folklore exponential floor -/

/-- **The folklore miss floor `miss ≥ e^{−(N_a − N_b)}` is FALSE for every bright baseline.**
The ideal unit-threshold counter (`count ≥ 1`) misses with probability exactly `e^{−N_a}`,
undershooting the folklore floor by the factor `e^{N_b}`. The folklore form quotes no
false-alarm constraint, and this rule has none imposed; the correct constrained statement is
`poisson_darkBaseline_miss_floor`. -/
theorem folklore_miss_floor_false {Nb Na : ℝ≥0} (hNb : 0 < Nb) :
    missProb Na (thresholdRule 1) < Real.exp (-((Na : ℝ) - Nb)) := by
  rw [(poisson_darkBaseline_miss_optimum Na).2]
  exact Real.exp_lt_exp.mpr (by linarith [NNReal.coe_pos.mpr hNb])

/-- Quantitative form at the roadmap's operating point `N_b = 5, N_a = 10`: the unit-threshold
counter beats the folklore floor by at least a factor of 6. The constant comes from
`SKEFTHawking.QuantumNetwork.expNeg_enclosure` at `r = 5` (`e^{−5} ≤ 1/(1+5)`). -/
theorem folklore_missFloor_beaten_sixfold :
    6 * missProb 10 (thresholdRule 1) ≤ Real.exp (-((10 : ℝ) - 5)) := by
  have hm : missProb (10 : ℝ≥0) (thresholdRule 1) = Real.exp (-(10 : ℝ)) := by
    simpa using (poisson_darkBaseline_miss_optimum (10 : ℝ≥0)).2
  have hsplit : Real.exp (-(10 : ℝ)) = Real.exp (-(5 : ℝ)) * Real.exp (-(5 : ℝ)) := by
    rw [← Real.exp_add]; norm_num
  have h5 : Real.exp (-(5 : ℝ)) ≤ 1 / (1 + 5) := (expNeg_enclosure (by norm_num : (0 : ℝ) ≤ 5)).2
  rw [hm, hsplit, show -((10 : ℝ) - 5) = -(5 : ℝ) by norm_num]
  nlinarith [h5, Real.exp_pos (-(5 : ℝ))]

/-- **The exact folklore-vs-Le-Cam exponent gap**, in `exp` form (so `Real.log` never enters a
statement): `(N_a − N_b) − (√N_a − √N_b)² = 2√N_b(√N_a − √N_b)`. This identity — not any
inequality — is the algebraic content of the average-error refutation: it says the Le Cam
exponent beats the folklore exponent by exactly twice the baseline amplitude times the
amplitude separation, so the folklore form fails open precisely when the baseline is bright. -/
theorem folkloreGap_split {a b : ℝ} (hb : 0 ≤ b) (ha : 0 ≤ a) :
    Real.exp (-(√a - √b) ^ 2) = Real.exp (-(a - b)) * Real.exp (2 * √b * (√a - √b)) := by
  rw [← Real.exp_add]
  congr 1
  have hexp : (√a - √b) ^ 2 = a + b - 2 * (√a * √b) := by
    rw [sub_sq, Real.sq_sqrt ha, Real.sq_sqrt hb]; ring
  rw [hexp]
  linear_combination 2 * Real.mul_self_sqrt hb

/-- **The folklore form fails OPEN as an average-error screen.** Whenever
`4 < exp(2√N_b(√N_a − √N_b))` — i.e. whenever the baseline is bright relative to the
separation — the true Le Cam floor `¼·exp(−(√N_a−√N_b)²)` STRICTLY EXCEEDS the folklore value
`exp(−(N_a−N_b))`. A screen built on the folklore form therefore admits configurations that the
true floor forbids. -/
theorem folklore_avgFloor_unsound_of_bright {Nb Na : ℝ≥0}
    (h : (4 : ℝ) < Real.exp (2 * √(Nb : ℝ) * (√(Na : ℝ) - √(Nb : ℝ)))) :
    Real.exp (-((Na : ℝ) - Nb))
      < (1 / 4) * Real.exp (-(√(Na : ℝ) - √(Nb : ℝ)) ^ 2) := by
  rw [folkloreGap_split Nb.coe_nonneg Na.coe_nonneg]
  nlinarith [Real.exp_pos (-((Na : ℝ) - (Nb : ℝ))), h]

/-- **The `(N_b, N_a) = (50, 60)` operating point is bright.** The exponent gap
`2√50(√60 − √50) = 2√3000 − 100` exceeds `9.54` (true value `9.54451…`), via the rational
bracket `54.77 < √3000` (`54.77² = 2999.7529 < 3000`). This is the arithmetic core of both
`(50, 60)` witnesses below. -/
theorem brightGap_5060 : (9.54 : ℝ) < 2 * √(50 : ℝ) * (√(60 : ℝ) - √(50 : ℝ)) := by
  have hmul : √(50 : ℝ) * √(60 : ℝ) = √(3000 : ℝ) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 50)]; norm_num
  have hself : √(50 : ℝ) * √(50 : ℝ) = 50 := Real.mul_self_sqrt (by norm_num)
  have h3000 : (54.77 : ℝ) < √(3000 : ℝ) := by
    have hrw : (54.77 : ℝ) = √((54.77 : ℝ) ^ 2) := (Real.sqrt_sq (by norm_num)).symm
    rw [hrw]
    exact Real.sqrt_lt_sqrt (by positivity) (by norm_num)
  have he : 2 * √(50 : ℝ) * (√(60 : ℝ) - √(50 : ℝ))
      = 2 * (√(50 : ℝ) * √(60 : ℝ)) - 2 * (√(50 : ℝ) * √(50 : ℝ)) := by ring
  rw [he, hmul, hself]
  linarith

/-- Witness at `N_b = 50, N_a = 60`: the true Le Cam floor `0.1585…` exceeds the folklore value
`4.54e−5`. -/
theorem folklore_avg_floor_unsound :
    Real.exp (-((60 : ℝ) - 50))
      < (1 / 4) * Real.exp (-(√(60 : ℝ) - √(50 : ℝ)) ^ 2) := by
  have hbright : (4 : ℝ) < Real.exp (2 * √(50 : ℝ) * (√(60 : ℝ) - √(50 : ℝ))) := by
    linarith [Real.add_one_le_exp (2 * √(50 : ℝ) * (√(60 : ℝ) - √(50 : ℝ))), brightGap_5060]
  simpa using folklore_avgFloor_unsound_of_bright (Nb := 50) (Na := 60) (by simpa using hbright)

/-- **Quantitative form of the average-error refutation.** At `N_b = 50, N_a = 60` the true Le
Cam floor exceeds the folklore value by more than a factor of `1000` (the exact ratio is
`3491.96…`), so the folklore screen is not merely loose — it is off by three orders of
magnitude at an unremarkable operating point. The constant is discharged from
`Real.exp_one_gt_d9` through `exp 9 = (exp 1)^9 > 2.718^9 = 8095.5… > 4000`. -/
theorem folklore_avgFloor_unsound_factor1000 :
    1000 * Real.exp (-((60 : ℝ) - 50))
      < (1 / 4) * Real.exp (-(√(60 : ℝ) - √(50 : ℝ)) ^ 2) := by
  have hE : (4000 : ℝ) < Real.exp (2 * √(50 : ℝ) * (√(60 : ℝ) - √(50 : ℝ))) := by
    have h1 : (2.718 : ℝ) < Real.exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    have h9 : (2.718 : ℝ) ^ 9 < Real.exp 1 ^ 9 := pow_lt_pow_left₀ h1 (by norm_num) (by norm_num)
    have hexp9 : Real.exp 9 = Real.exp 1 ^ 9 := by rw [← Real.exp_nat_mul]; norm_num
    have h4000 : (4000 : ℝ) < Real.exp 9 := by
      rw [hexp9]; linarith [h9, show (4000 : ℝ) < 2.718 ^ 9 by norm_num]
    exact lt_trans h4000 (Real.exp_lt_exp.mpr (by linarith [brightGap_5060]))
  rw [folkloreGap_split (by norm_num : (0 : ℝ) ≤ 50) (by norm_num : (0 : ℝ) ≤ 60)]
  nlinarith [Real.exp_pos (-(10 : ℝ)), hE]

end SKEFTHawking.Detection
