# Phase 6EA — Stage 2 Statement Freeze

**Status: FROZEN (2026-07-27).** Resolves the three open UNKNOWNs of
[`Phase6EA_Roadmap.md`](Phase6EA_Roadmap.md) and freezes the exact Lean statement layer for
**Wave 1** (Poisson discrimination floors) and **Wave 2** (Gaussian threshold algebra), so a
Lean slot can execute them without re-deriving design decisions. **Wave 3** is scoped and
*recommended*, not frozen (it is serialized last).

**Publication target:** bundle **D12** — *Kernel-Verified Detector & Readout Metrology*
(authorized 2026-07-27, `PAPER_STRATEGY.md` §2.2). Per Invariant #14 this document is written
bundle-aware; **no on-disk scaffolding** (`_VALID_BUNDLE_TARGETS`, `papers/D12/`) is stood up
here — that executes at first content-lift.

> **⚠️ GUARDRAIL (inherited, unchanged).** Everything below states *floors and screens on any
> detector*, over abstract count means and noise parameters. No device claim, no hardware model,
> no platform assertion. Physical identification of an abstract parameter with a measured
> quantity is the consuming phase's declared hypothesis and is never smuggled into these
> statements.

> **⚠️ This document is Stage 2 only.** It contains no Lean files and no proofs. Every Lean
> snippet below is *frozen statement text* + a *proof recipe*; the executing slot still runs the
> MCP-first loop (`lean_goal` → `lean_multi_attempt` → write winner) and the Stage-3a
> preemptive-strengthening checklist per theorem.

---

## 0. Executive summary — what changed against the roadmap

Nine substrate facts were verified by reading the actual sources (Mathlib at pin `5e932f97`,
PhysLib at pin `085dab8f`, project `lean/SKEFTHawking/`). Five of them **change the roadmap's
plan**:

| # | Finding | Impact |
|---|---|---|
| F1 | Mathlib's Poisson module is `Mathlib.Probability.Distributions.Poisson.**Basic**` (roadmap cites `…Distributions.Poisson`), and the rate is **`ℝ≥0`**, not `ℝ`. | Import path + coercion discipline fixed below. |
| F2 | **Mathlib has NO `erf` / `erfc` / Gaussian CDF / `Q`-function at pin.** Verified by exhaustive declaration-level grep — zero hits. | Wave 2 must define `Q` project-locally from `gaussianPDFReal`; UNKNOWN-2 is *not* a choice between two library forms. |
| F3 | The PhysLib module path is **`QuantumInfo.Finite.ResourceTheory.HypothesisTesting`**, not `Physlib.QuantumInfo.…`. The package ships two `lean_lib`s (`Physlib`, `QuantumInfo`); the project already imports `QuantumInfo.*` directly (e.g. `LindbladGenerator.lean:1`). | Roadmap's Wave-3 brick path is wrong; corrected in §4. |
| F4 | `OptimalHypothesisRate` is `[Fintype d]`-bound (`MState d`), and PhysLib's classical carrier `ProbDistribution α` is `[Fintype α]`-bound. **Poisson lives on ℕ and cannot be an argument.** It is also an *asymmetric* Neyman–Pearson quantity (Type-II at Type-I tolerance ε), not the symmetric Bayes/Le Cam average error Wave 1 bounds. | UNKNOWN-3 option (b) — "an `OptimalHypothesisRate` specialization" — **does not survive contact with the API**. §4 gives the replacement. |
| F5 | `poissonTV_le_of_bhattacharyya` is **not on the critical path**. The Le Cam floor follows from Cauchy–Schwarz + elementary AM–GM with no total-variation object and no `√(1−BC²)`. | Wave-1 AC item demoted to optional; §5.6. |
| F6 | `classical_fvdg` is **not needed as a dependency** either — the required inequality is `(√(e₀(1−e₁)) + √((1−e₀)e₁))² ≤ 2(e₀+e₁)`, a *different* statement from FvdG's `TV² + BC² ≤ 1`. | `Detection/` avoids importing the heavy trace-norm tower. `classical_fvdg` stays a cited *structural sibling*, per the roadmap's own word "template". |
| F7 | `avgAssignmentError (e0 e1 : ℝ) : ℝ := (e0 + e1) / 2` **already exists** (`QuantumNetwork/ReadoutRelaxationBound.lean:143`). | Wave 1/2 reuse it rather than re-defining `(e₀+e₁)/2` — a real bridge-integrity call (checklist #3) and the concrete unification D12 claims. |
| F8 | The root `lean/SKEFTHawking.lean` is an explicit **1876-import aggregator** and the `lean_lib` declares no `globs`. A module not imported by the root is **not built by `lake build`**. | The roadmap's "root import lands in Wave 3" would leave Waves 1–2 outside the default build target, invisible to the zero-sorry gate, `ExtractDeps`, and counts. **Each wave adds its own root import in its own commit.** |
| F9 | Both folklore witnesses are **arithmetically correct**, and both admit strictly stronger **universally quantified** forms that the roadmap's `∃`-shape misses. | §6 — the refutation gets sharper, not weaker. |

Everything else in the roadmap's Wave-1/Wave-2 brick list survives verification.

---

## 1. Verified substrate inventory (read 2026-07-27)

### 1.1 Mathlib — Poisson (`Mathlib/Probability/Distributions/Poisson/Basic.lean`)

The **entire** public surface is five declarations:

```
noncomputable def poissonPMFReal (r : ℝ≥0) (n : ℕ) : ℝ := exp (-r) * r ^ n / n !
lemma poissonPMFRealSum   (r : ℝ≥0) : HasSum (fun n ↦ poissonPMFReal r n) 1
lemma poissonPMFReal_pos  {r : ℝ≥0} {n : ℕ} (hr : 0 < r) : 0 < poissonPMFReal r n
lemma poissonPMFReal_nonneg {r : ℝ≥0} {n : ℕ} : 0 ≤ poissonPMFReal r n
noncomputable def poissonPMF (r : ℝ≥0) : PMF ℕ            -- ℝ≥0∞-valued
noncomputable def poissonMeasure (r : ℝ≥0) : Measure ℕ
```

Load-bearing consequences:

* `poissonPMFRealSum` carries **no positivity hypothesis** — it holds at `r = 0`. This is what
  makes the dark-baseline wave item (`N_b = 0`) statable at all. (`poissonPMFReal 0 0 = 1`,
  `poissonPMFReal 0 n = 0` for `n ≥ 1`, since `0 ^ 0 = 1` in Lean.)
* There are **no** discrimination bounds, no affinity, no TV, no likelihood-ratio structure —
  exactly as the roadmap's sweep said.
* The proof of `poissonPMFRealSum` is a **direct template** for the Wave-1 Bhattacharyya
  identity: it factors `exp r` out with `(hasSum_mul_left_iff (exp_ne_zero r)).mp`, rewrites the
  summand to `r ^ i / i.factorial`, then closes with `exp_eq_exp_ℝ` +
  `NormedSpace.expSeries_div_hasSum_exp`. Wave 1's `poissonBhattacharyya_hasSum` is the same
  proof with `r := √(a·b)` and a `exp (-(a+b)/2)` prefactor.

### 1.2 Mathlib — Gaussian

* `ProbabilityTheory.gaussianPDFReal (μ : ℝ) (v : ℝ≥0) (x : ℝ)` — the pdf, with
  `gaussianPDFReal_nonneg`, `gaussianPDFReal_pos`, `integrable_gaussianPDFReal`,
  `integral_gaussianPDFReal_eq_one`, measurability. **Variance is `ℝ≥0`.**
* `Real.integral_gaussian (b : ℝ) : ∫ x, exp (-b * x ^ 2) = √(π / b)`
* `Real.integral_gaussian_Ioi (b : ℝ) : ∫ x in Ioi (0:ℝ), exp (-b * x ^ 2) = √(π / b) / 2`
  — **this is what pins `Q 0 = 1/2` for free.**
* **No `erf`, no `erfc`, no CDF, no `Q`** (F2). Verified with
  `grep -rnE "(def|theorem|lemma|noncomputable def) +(Real\.)?erfc? "` over all of Mathlib —
  zero matches. Every "erf" hit in the tree is a substring of `perform`/`interface`/…

### 1.3 Mathlib — the analysis lemmas the two waves actually need (all verified to exist)

| Lemma | Location | Used for |
|---|---|---|
| `NormedSpace.expSeries_div_hasSum_exp (x) : HasSum (fun n => x ^ n / n !) (exp x)` | `Analysis/Normed/Algebra/Exponential.lean:627` | Bhattacharyya series |
| `Real.exp_eq_exp_ℝ` | (as used by `poissonPMFRealSum`) | bridging `Real.exp` ↔ `NormedSpace.exp` |
| `Real.sum_sqrt_mul_sqrt_le (s) (hf) (hg) : ∑ i ∈ s, √(f i) * √(g i) ≤ √(∑ f) * √(∑ g)` | `Data/Real/Sqrt.lean:489` | Cauchy–Schwarz for the data-processing step |
| `Real.tsum_le_of_sum_le (hf : 0 ≤ f) (h : ∀ s, ∑ i ∈ s, f i ≤ c) : ∑' f ≤ c` | `Topology/Algebra/InfiniteSum/Real.lean:95` | lifting the Finset CS to `tsum` **against a constant RHS** |
| `Summable.of_nonneg_of_le` | `Topology/Algebra/InfiniteSum/ENNReal.lean:531` | summability of `p·δ` from `p` |
| `Real.add_one_le_exp (x) : x + 1 ≤ exp x` | `Analysis/Complex/Exponential.lean:646` | witness lower bounds |
| `Real.exp_lt_exp : exp x < exp y ↔ x < y` | `Analysis/Complex/Exponential.lean:312` | witness monotonicity |
| `Real.exp_nat_mul (x) (n) : exp (n * x) = exp x ^ n` | `Analysis/Complex/Exponential.lean:229` | `exp 9 = (exp 1)^9` sharpening |
| `Real.exp_one_gt_d9 : 2.7182818283 < exp 1` | `Analysis/Complex/ExponentialBounds.lean:34` | quantitative gap sharpening |
| `Real.lt_sqrt (hx : 0 ≤ x) : x < √y ↔ x ^ 2 < y` | `Data/Real/Sqrt.lean:378` | rational bracket on `√3000` |
| `Real.sq_sqrt`, `Real.mul_self_sqrt`, `Real.sqrt_mul` | `Data/Real/Sqrt.lean:175/146/349` | affinity algebra |
| `MeasureTheory.integral_Ioi_of_hasDerivAt_of_tendsto` | `MeasureTheory/Integral/IntegralEqImproper.lean:713` | Wave-2 **stretch** (Mills / Birnbaum) |
| `intervalIntegral.integral_hasDerivAt_right` | `MeasureTheory/Integral/IntervalIntegral/FundThmCalculus.lean:727` | Wave-2 `HasDerivAt Q (-φ z) z` |
| `strictMonoOn_of_deriv_pos`, `strictAntiOn_of_deriv_neg` | `Analysis/Calculus/Deriv/MeanValue.lean:374/442` | Wave-2 **stretch** |

### 1.4 Project substrate (all three roadmap "reuse" bricks confirmed present)

* `SKEFTHawking.QuantumNetwork.expNeg_enclosure {r} (hr : 0 ≤ r) : 1 - r ≤ exp (-r) ∧ exp (-r) ≤ 1 / (1 + r)`
  — `QuantumNetwork/NumericalBounds.lean:31`. Light import chain
  (`Mathlib.Analysis.SpecialFunctions.Exp` + `QuantumNetwork.Basic`).
* `SKEFTHawking.QuantumNetwork.avgAssignmentError (e0 e1 : ℝ) : ℝ := (e0 + e1) / 2`
  and `avgAssignmentError_rational_floor` — `QuantumNetwork/ReadoutRelaxationBound.lean:143/158`.
* `SKEFTHawking.QuantumNetwork.classical_fvdg` — `QuantumNetwork/FidelityUpperBound.lean:47`.
  Pure-ℝ statement `(½(|p₀−q₀|+|p₁−q₁|))² + (√(p₀q₀)+√(p₁q₁))² ≤ 1`, but its **file** imports
  `FidelityBounds` + `TraceNormCauchySchwarz` (the whole trace-norm/polar tower). See §5.4 for
  why Wave 1 cites it without importing it.

### 1.5 PhysLib (pin `085dab8f`)

* Module path: **`QuantumInfo.Finite.ResourceTheory.HypothesisTesting`** (568 lines).
* `noncomputable def OptimalHypothesisRate (ρ : MState d) (ε : Prob) (S : Set (MState d)) : Prob`
  with `variable {d : Type*} [Fintype d] [DecidableEq d]`, notation `β_ ε(ρ‖S)`.
* Available structure: `of_empty`, `le_of_subset`, `of_singleton`, `singleton_le_exp_val`,
  `le_sup_exp_val`, `exists_min`/`exists_min'` (the inf is attained), `iInf_IsCompact`,
  `iInf_IsConvex`, `optimalHypothesisRate_antitone` (data processing under a `CPTPMap`),
  `Lemma3`, `Ref81Lem5`, `rate_Continuous_singleton`.
* `MState.ofClassical` exists (`QuantumInfo/Finite/MState.lean:30`), taking
  `ProbDistribution d` — and `ProbDistribution α` requires `[Fintype α]`.

---

## 2. UNKNOWN-1 — Wave-1 pmf carrier

> *Roadmap:* "phrase Wave 1 over Mathlib `PMF`/`poissonPMFReal` sums vs. a self-contained
> `ℕ → ℝ` pmf with proved normalization. Decide by whichever makes `poisson_avgError_floor`'s
> 'arbitrary randomized decision rule' quantifier cleanest; the two-point bound must not silently
> narrow to deterministic threshold rules."

### 2.1 The decisive observation

**The randomized-rule quantifier is orthogonal to the pmf carrier.** A randomized rule is a
function `δ : ℕ → ℝ` with `δ n ∈ [0,1]` (the probability of declaring "signal" on count `n`);
the two error functionals are

```
e₀ = ∑' n, p n * δ n            (false alarm, under the baseline law p)
e₁ = ∑' n, q n * (1 - δ n)      (miss,        under the signal   law q)
```

Nothing in that construction touches the pmf's *type*. The trap the roadmap warns about — silent
narrowing to deterministic threshold rules — is avoided by **how the rule is quantified**, not by
the carrier. So the carrier decision is free to be made on reuse grounds.

Concretely, the Le Cam bound is proved *distribution-free* (§5.3, T2/T3/T4) over
`p q : ℕ → ℝ` with `HasSum p 1`, `HasSum q 1`, and the Poisson statement is a one-line
instantiation. That structure also makes the generic lemma directly reusable by 6EB/6EE for
non-Poisson count laws — a second reason to keep the carrier at the `ℕ → ℝ` interface.

### 2.2 Decision

**Use Mathlib's `ProbabilityTheory.poissonPMFReal (r : ℝ≥0) (n : ℕ) : ℝ` as the Poisson carrier,
and state the generic Le Cam machinery over bare `p q : ℕ → ℝ` with `HasSum … 1` hypotheses.**

**Rejected — `PMF ℕ` / `poissonPMF`.** Forces `ℝ≥0∞` arithmetic. Truncated subtraction and
`ENNReal`↔`Real.exp` interplay are hostile to every statement in this phase (the whole point is
real-valued `exp` floors), and a randomized rule would need an `ℝ≥0∞`-valued `δ` with an
awkward `≤ 1` side condition. Strong reject.

**Rejected — a self-contained `ℕ → ℝ` Poisson pmf with a re-proved normalization.** It buys a
real-valued rate (no `ℝ≥0` coercion) at the cost of (a) duplicating `poissonPMFRealSum`
verbatim, (b) weakening the headline claim from "kernel-checked floor on *the* Poisson
distribution" to "…on our definition of it", and (c) violating the project's reuse posture. The
coercion friction it avoids is small and mechanical.

### 2.3 Coercion discipline (the one real cost of the decision)

The rate is `ℝ≥0`; every real-valued statement carries `(r : ℝ)`. **Rules for the executing
slot:**

* Rates are bound as `{Nb Na : ℝ≥0}`. Wherever a real is needed write `(Nb : ℝ)`.
* Use **`Real.sqrt (Nb : ℝ)`**, never `NNReal.sqrt` — the whole `√` algebra below
  (`Real.sqrt_mul`, `Real.sq_sqrt`, `Real.mul_self_sqrt`, `Real.sum_sqrt_mul_sqrt_le`) is the
  `Real` API. Do **not** mix.
* `poissonPMFReal` already unfolds to `Real.exp (-↑r) * ↑r ^ n / ↑n !` — the coercion is
  *inside* the definition, so `simp [poissonPMFReal]` lands you in ℝ immediately.
* `push_cast` / `NNReal.coe_le_coe` / `NNReal.coe_pos` close the residual goals. Numeric
  literals: `((5 : ℝ≥0) : ℝ) = 5` by `norm_num` after `push_cast`.

---

## 3. UNKNOWN-2 — the Gaussian lower tail

> *Roadmap:* "the Gaussian lower-tail bound form (interval-restricted rational vs. `z/(1+z²)·φ(z)`
> global) — pick the one that composes with Wave-2's floor statements without side conditions
> leaking into 6EE."

### 3.1 The framing has to change first (F2)

Mathlib has **no** `Q`, `erf`, `erfc`, or Gaussian CDF. So Wave 2 is not choosing between two
library forms; it is defining `Q` and then proving bounds on its own definition:

```lean
/-- Standard-normal upper-tail probability. Mathlib carries no `erf`/`erfc`/Gaussian-CDF at
pin `5e932f97` (verified 2026-07-27), so this is project-local. -/
noncomputable def gaussianQ (z : ℝ) : ℝ :=
  ∫ x in Set.Ioi z, ProbabilityTheory.gaussianPDFReal 0 1 x
```

### 3.2 Why the interval-restricted rational is REJECTED

The cheap interval form is `Q z ≥ 1/2 − z/√(2π)` (from `Q 0 = 1/2` and `φ ≤ φ(0)`; the
roadmap's variant `(1/2)(1 − z/√(2π))` is the same shape). It goes **negative — hence vacuous —
at `z > √(2π)/2 ≈ 1.2533`.**

That is fatal for the stated selection criterion. Every regime 6EE cares about (a readout with
any usable fidelity) sits at `z ≳ 2`, where this bound says nothing. A floor that is vacuous
exactly where it is needed is the "trivially true floor is worthless" antipattern (checklist #4).
Its side condition does not merely *leak* into 6EE — it swallows 6EE's entire operating range.
**Reject.**

### 3.3 The decision: a two-tier lower tail

**Tier A — MUST-SHIP, the frozen Wave-2 lower tail (global, side-condition-free, cheap):**

```lean
/-- **Window lower bound on the Gaussian upper tail.** For every `z ≥ 0` and every window
width `c > 0`, `Q z ≥ c · φ(z + c)`. Global in `z`, parametric in `c`, no side condition:
each consumer picks its own `c`. The exponential order `exp(−z²/2)` is exact; only a bounded
constant is lost against the sharp bound. -/
theorem gaussianTail_ge_window {z c : ℝ} (hz : 0 ≤ z) (hc : 0 < c) :
    c * ProbabilityTheory.gaussianPDFReal 0 1 (z + c) ≤ gaussianQ z
```

Proof recipe (≈25 lines, low risk):
1. `Integrable (gaussianPDFReal 0 1)` (Mathlib) → `IntegrableOn … (Ioi z)` and `… (Ioi (z+c))`.
2. `∫_{Ioi z} = ∫_{z}^{z+c} + ∫_{Ioi (z+c)}` (`MeasureTheory.integral_Ioi_eq_...` / interval
   additivity), and the tail term is `≥ 0` by `gaussianPDFReal_nonneg` + `setIntegral_nonneg`.
3. `φ` is antitone on `[0,∞)`: `gaussianPDFReal 0 1 x = (1/√(2π))·exp(−x²/2)`; monotone `x²`
   on `[0,∞)` + `Real.exp_le_exp`.
4. `∫_z^{z+c} φ ≥ c · φ(z+c)` by `intervalIntegral.integral_mono_on` against the constant.

Calibration (so the constant loss is on the record): at `z = 3`, true `Q(3) = 1.34990e−3`; the
window bound at the optimal `c = (√(z²+4) − z)/2 = 0.302776` gives `5.16795e−4` (ratio 0.3828);
at `c = 1/z` it gives `5.14093e−4` (ratio 0.3808). Correct exponent, factor ≈2.6 constant loss.

**Tier B — STRETCH, the sharp global form the roadmap named:**

```lean
/-- **Birnbaum/Feller sharp lower tail**: `Q z ≥ (z/(1+z²))·φ(z)` for `z > 0`. -/
theorem gaussianTail_birnbaum {z : ℝ} (hz : 0 < z) :
    z / (1 + z ^ 2) * ProbabilityTheory.gaussianPDFReal 0 1 z ≤ gaussianQ z
```

Proof recipe (the *cheap* derivation — no monotone-antiderivative argument needed):
1. `F x := -φ(x)/x` satisfies `HasDerivAt F (φ x * (1 + 1/x²)) x` for `x > 0`
   (`φ' = −x·φ`; then `HasDerivAt.div`).
2. `integral_Ioi_of_hasDerivAt_of_tendsto` with `Tendsto F atTop (𝓝 0)` gives
   **`∫_{Ioi z} φ(x)(1 + 1/x²) dx = φ(z)/z`**, i.e. `Q z + ∫_{Ioi z} φ/x² = φ(z)/z`.
3. `1/x² ≤ 1/z²` on `Ioi z` ⟹ `∫_{Ioi z} φ/x² ≤ Q z / z²`.
4. Hence `Q z (1 + 1/z²) ≥ φ(z)/z`, i.e. `Q z ≥ z·φ(z)/(1+z²)`. ∎

Estimated 80–120 lines (the `HasDerivAt` computation and the `IntegrableOn` side goals are the
bulk). At `z = 3` it returns `1.32955e−3` against the true `1.34990e−3` — ratio 0.9849.

**Discipline:** ship Tier A *first* and unconditionally. Wave 2's downstream floor
(§7.5) is stated against a generic lower-tail hypothesis so that **substituting Tier B later
requires no restatement** of any consuming theorem. Tier A is never wasted: it is the only form
that yields a fully *rational* floor (no `π` in the constant) when `c` is chosen rational.

### 3.4 Companion decision on the UPPER tail (`gaussianTail_chernoff`)

The roadmap's AC names `gaussianTail_chernoff : Q z ≤ (1/2)·exp(−z²/2)` for `z ≥ 0`. Honest
cost accounting:

* For **`z ≥ 0.8`** it is a `norm_num` corollary of the Mills bound `Q z ≤ φ(z)/z`
  (`1/(z√(2π)) ≤ 1/2 ⟺ z ≥ 2/√(2π) = 0.79788`), and Mills follows from the *easier* half of
  the Tier-B machinery (antiderivative `−φ`, so `∫_{Ioi z} x·φ(x) dx = φ(z)`, then
  `φ(x) ≤ (x/z)φ(x)` on `Ioi z`).
* For **`0 ≤ z < 0.8`** the exact constant needs the monotone-derivative argument
  (`g(z) := (1/2)e^{−z²/2} − Q z`, `g(0) = 0`, `g' = e^{−z²/2}(1/√(2π) − z/2) ≥ 0` on
  `[0, 2/√(2π)]`), which needs `HasDerivAt gaussianQ (−φ z) z` +
  `strictMonoOn_of_deriv_pos`.

**Frozen:** ship `gaussianTail_chernoff_of_le_08` (hypothesis `(0.8 : ℝ) ≤ z`) as the must-ship,
plus the unconditional `gaussianQ_le_half` (`z ≥ 0`) as the trivial companion. The full `z ≥ 0`
Chernoff is a documented stretch. **Justification that this side condition does not leak:** the
upper tail is the *non*-load-bearing direction (the roadmap itself says "a lower bound on error
is a ceiling on fidelity — the load-bearing direction"), and `z ≥ 0.8` is satisfied by every
operating point any consumer will present. The condition is explicit in the statement, so no
consumer can use it silently.

---

## 4. UNKNOWN-3 — the quantum seam (RECOMMENDATION, not a freeze)

> *Roadmap:* "exact shape of the classical↔quantum seam theorem (diagonal-state restriction of
> Helstrom vs. an `OptimalHypothesisRate` specialization) — requires reading
> `Physlib…HypothesisTesting` in full before freezing."

Read in full (568 lines). **Two structural facts kill option (b) outright:**

1. **Type-level impossibility.** `OptimalHypothesisRate ρ ε S` takes `ρ : MState d` with
   `[Fintype d] [DecidableEq d]`; PhysLib's classical embedding `MState.ofClassical` takes
   `ProbDistribution α` with `[Fintype α]`. **`Poisson` on `ℕ` is not a `Fintype` and cannot be
   an argument to either.** There is no "specialization" of `OptimalHypothesisRate` that has the
   Wave-1 objects in it.
2. **Functional mismatch.** `OptimalHypothesisRate` is the *asymmetric* Neyman–Pearson value —
   the minimum Type-II error subject to Type-I `≤ ε`. Wave 1's floor is the *symmetric*
   Bayes/Le Cam average error at equal priors. These are different functionals; calling one a
   specialization of the other would be a category error, and a theorem asserting it would be
   either false or vacuous.

### 4.1 Recommendation

**Route the Wave-3 seam through the two-outcome *pushforward*, and state it as a diagonal
restriction of the project's own quantum bound — not as an `OptimalHypothesisRate`
specialization.**

The pushforward is already constructed by Wave 1: for any count rule `δ`, the pair
`P₀ = (1−e₀, e₀)` and `P₁ = (e₁, 1−e₁)` is a **two-outcome classical experiment on `Fin 2`** —
finite, so every PhysLib/`QuantumNetwork` object applies. Three candidate seam statements, in
increasing cost:

**(S1) — recommended must-ship.** *The classical affinity is the quantum fidelity of the
diagonal embedding.*

```
diagonalState_sqrtFidelity_eq_affinity :
  for p q : Fin k → ℝ nonneg with ∑ p = ∑ q = 1,
    sqrtFidelity (Matrix.diagonal (p ·)) (Matrix.diagonal (q ·)) = ∑ i, √(p i * q i)
```
This is the literal content of "the classical floors are the commutative shadow of the quantum
bounds". Non-vacuous, provable with the project's own `psdSqrt`/`FidelityBounds` substrate
(`psdSqrt` of a diagonal PSD matrix is the entrywise `√`). It is a genuine bridge (checklist #3):
the body *calls* `QuantumNetwork` fidelity machinery.

**(S2) — the composed headline.** Chain (S1) with `traceDist_le_sqrt_one_sub_sqrtFidelity_sq`
(the project's proven FvdG, `FidelityUpperBound.lean`) applied to the `Fin 2` pushforward, and
with Wave 1's `affinity_le_binaryAffinity`, to get: *the Wave-1 Poisson floor is implied by the
quantum two-state discrimination bound on the pushforward experiment.* This is the roadmap's
`classical_floor_le_quantum_optimum` in the only shape that is true.

**(S3) — the actual PhysLib consumption, if the phase wants it.** `β_ε(ofClassical P₁ ‖ {ofClassical P₀})`
on the `Fin 2` pushforward. Feasible (`of_singleton` + `singleton_le_exp_val` give the
inf-bounding lemmas; `exists_min` gives attainment), but requires (a) a
`ProbDistribution (Fin 2)` construction, (b) `MState.exp_val` computations on diagonal
`HermitianMat`s, (c) proving the optimum over general `0 ≤ T ≤ 1` is attained by a *diagonal*
`T` for commuting states. **Cost estimate: a wave of its own.** The project's existing
`QuantumNetwork/PhyslibBridge.lean` covers `CPTPMap`/`Entropy.DPI`, not `HypothesisTesting`, so
this is genuinely first-consumption work.

### 4.2 Scoping verdict for Wave 3

Ship **(S1) + (S2)**. Treat **(S3)** as an explicitly-deferred item — and if it is deferred,
**do not describe Wave 3 as "the first project consumption of `HypothesisTesting`"** in any
D12-facing text, because it would not be. Correct the roadmap's brick path to
`QuantumInfo.Finite.ResourceTheory.HypothesisTesting` (F3) regardless.

The remaining Wave-3 items (`poisson_thinning`, `shotPSD_plane_transfer`,
`shot_variance_eq_mean`) are untouched by this analysis and stand as written; `poisson_thinning`
is a clean pmf-level identity over `poissonPMFReal` (`Poisson (η·N)` with `η : ℝ≥0`, `η ≤ 1`, so
`η * N : ℝ≥0` needs no coercion).

---

## 5. FROZEN — Wave 1 statement layer

**File:** `lean/SKEFTHawking/Detection/PoissonDiscrimination.lean`
**Namespace:** `SKEFTHawking.Detection`
**Root import:** add `import SKEFTHawking.Detection.PoissonDiscrimination` to
`lean/SKEFTHawking.lean` **in the same commit** (F8 — otherwise `lake build` never sees it).

### 5.1 Header

```lean
import Mathlib.Probability.Distributions.Poisson.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.Topology.Algebra.InfiniteSum.Real
import SKEFTHawking.QuantumNetwork.ReadoutRelaxationBound

namespace SKEFTHawking.Detection

open scoped NNReal
open ProbabilityTheory Real SKEFTHawking.QuantumNetwork
```

`ReadoutRelaxationBound` is imported for **`avgAssignmentError`** (F7) and brings
`expNeg_enclosure` transitively. It is already in the root aggregator
(`SKEFTHawking.lean:4260`), so the marginal library build cost is nil. *Fallback if the slot
prefers a minimal edge:* state the floors with a bare `(e₀ + e₁) / 2` and add the bridge
`poissonFloor_eq_avgAssignmentError` in Wave 3, where the import is paid anyway. **The frozen
choice is to import.**

### 5.2 Definitions

```lean
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
```

### 5.3 The generic (distribution-free) Le Cam chain

```lean
/-- **Data processing for the affinity through an arbitrary randomized rule.** Any rule `δ`
collapses the experiment to a two-outcome one with error pair `(e₀, e₁)`; the affinity cannot
decrease. Proof: pointwise `√(p n q n) = √(p n δ n · q n δ n) + √(p n (1−δ n) · q n (1−δ n))`
over each `Finset`, then `Real.sum_sqrt_mul_sqrt_le` twice, then `Real.tsum_le_of_sum_le`
against the constant RHS. -/
theorem affinity_le_binaryAffinity {p q δ : ℕ → ℝ} {e₀ e₁ : ℝ}
    (hp0 : ∀ n, 0 ≤ p n) (hq0 : ∀ n, 0 ≤ q n)
    (hp : HasSum p 1) (hq : HasSum q 1) (hδ : IsCountRule δ)
    (he₀ : HasSum (fun n => p n * δ n) e₀)
    (he₁ : HasSum (fun n => q n * (1 - δ n)) e₁) :
    affinity p q ≤ √(e₀ * (1 - e₁)) + √((1 - e₀) * e₁)

/-- **Two-outcome AM–GM.** Elementary, pure ℝ, no measure theory. Structural sibling of
`SKEFTHawking.QuantumNetwork.classical_fvdg` (`TV² + BC² ≤ 1`), which this is NOT: the two
statements bound different quantities and neither implies the other cheaply. Proof: expand,
use `√(e₀(1−e₁))·√((1−e₀)e₁) = √(e₀(1−e₀))·√(e₁(1−e₁))` and `2√a√b ≤ a + b`, then `nlinarith`
with `Real.sq_sqrt` hints — the same shape as `classical_fvdg`'s own proof. -/
theorem binaryAffinity_sq_le_two_mul_add {e₀ e₁ : ℝ}
    (h₀ : e₀ ∈ Set.Icc (0 : ℝ) 1) (h₁ : e₁ ∈ Set.Icc (0 : ℝ) 1) :
    (√(e₀ * (1 - e₁)) + √((1 - e₀) * e₁)) ^ 2 ≤ 2 * (e₀ + e₁)

/-- **Le Cam two-point average-error floor, distribution-free.** For ANY pair of count
distributions and ANY (possibly randomized) count rule, the equal-prior average error is at
least a quarter of the squared affinity. Stated in the project's canonical error functional
`avgAssignmentError` (`QuantumNetwork/ReadoutRelaxationBound.lean`), which this generalizes
from the relaxation model to arbitrary count statistics. -/
theorem avgError_ge_affinity_sq {p q δ : ℕ → ℝ} {e₀ e₁ : ℝ}
    (hp0 : ∀ n, 0 ≤ p n) (hq0 : ∀ n, 0 ≤ q n)
    (hp : HasSum p 1) (hq : HasSum q 1) (hδ : IsCountRule δ)
    (he₀ : HasSum (fun n => p n * δ n) e₀)
    (he₁ : HasSum (fun n => q n * (1 - δ n)) e₁) :
    (1 / 4) * (affinity p q) ^ 2 ≤ avgAssignmentError e₀ e₁
```

**Why this is the right architecture (F5/F6).** `avgError_ge_affinity_sq` needs neither total
variation nor `√(1 − BC²)` nor `classical_fvdg`: the chain is
`affinity ≤ √(e₀(1−e₁)) + √((1−e₀)e₁)` (Cauchy–Schwarz) and
`(that)² ≤ 2(e₀+e₁)` (AM–GM), giving `affinity² ≤ 2(e₀+e₁) = 4·avgAssignmentError e₀ e₁`. Two
elementary steps, no measure-theoretic depth, and the only infinite-sum tool needed is
`Real.tsum_le_of_sum_le` **against a constant** — which is exactly the shape Mathlib provides.

### 5.4 The Bhattacharyya identity

```lean
/-- **Poisson Bhattacharyya coefficient, closed form (HasSum).**
`∑ₙ √(Poisson(a)ₙ · Poisson(b)ₙ) = exp(−(√a − √b)²/2)`. Proof template: the proof of Mathlib's
`poissonPMFRealSum`, with `r := √(ab)` — factor `exp(−(a+b)/2)` out with
`(hasSum_mul_left_iff (exp_ne_zero _)).mp`, reduce the summand to `√(ab) ^ n / n !`, close with
`Real.exp_eq_exp_ℝ` + `NormedSpace.expSeries_div_hasSum_exp`, then
`√(ab) − (a+b)/2 = −(√a − √b)²/2` by `Real.sqrt_mul` + `Real.sq_sqrt` + `ring`. -/
theorem poissonBhattacharyya_hasSum (a b : ℝ≥0) :
    HasSum (fun n => √(poissonPMFReal a n * poissonPMFReal b n))
      (Real.exp (-(√(a : ℝ) - √(b : ℝ)) ^ 2 / 2))

/-- Roadmap-named headline form. -/
theorem poissonBhattacharyya_eq (a b : ℝ≥0) :
    affinity (poissonPMFReal a) (poissonPMFReal b)
      = Real.exp (-(√(a : ℝ) - √(b : ℝ)) ^ 2 / 2) :=
  (poissonBhattacharyya_hasSum a b).tsum_eq
```

Freeze the **`HasSum`** form as the workhorse (it carries summability, which
`affinity_le_binaryAffinity` and every downstream rewrite need); `poissonBhattacharyya_eq` is
the one-line `tsum_eq` corollary that keeps the roadmap's name.

### 5.5 The Poisson headline floor

```lean
/-- **The universal Poisson discrimination floor (Le Cam two-point bound).** For ANY (possibly
randomized) count-based decision rule, the equal-prior average of false-alarm and miss error
satisfies `(e₀+e₁)/2 ≥ ¼·exp(−(√N_a − √N_b)²)`. No false-alarm constraint, no threshold
structure, no monotone-likelihood assumption: the quantifier ranges over every
`δ : ℕ → [0,1]`. -/
theorem poisson_avgError_floor {Nb Na : ℝ≥0} {δ : ℕ → ℝ} (hδ : IsCountRule δ) :
    (1 / 4) * Real.exp (-(√(Na : ℝ) - √(Nb : ℝ)) ^ 2)
      ≤ avgAssignmentError (falseAlarm Nb δ) (missProb Na δ)
```

Proof: `avgError_ge_affinity_sq` at `p := poissonPMFReal Nb`, `q := poissonPMFReal Na`
(`HasSum … 1` from `poissonPMFRealSum`; `HasSum (p·δ) (falseAlarm Nb δ)` from
`Summable.of_nonneg_of_le` + `Summable.hasSum`), then rewrite the affinity with
`poissonBhattacharyya_eq` and square: `exp(−d/2)² = exp(−d)` by `sq` + `← Real.exp_add` + `ring_nf`.

### 5.6 Dark baseline (zero-false-alarm optimum)

```lean
/-- **Dark-baseline zero-false-alarm miss floor.** When the baseline is dark (`N_b = 0`), every
rule with exactly zero false-alarm probability misses with probability at least `exp(−N_a)`.
The zero-false-alarm hypothesis is explicit and non-droppable — see
`darkBaseline_zeroFalseAlarm_load_bearing`. -/
theorem poisson_darkBaseline_miss_floor {Na : ℝ≥0} {δ : ℕ → ℝ}
    (hδ : IsCountRule δ) (hFA : falseAlarm 0 δ = 0) :
    Real.exp (-(Na : ℝ)) ≤ missProb Na δ

/-- **The floor is attained**, by the ideal unit-threshold counter (`count ≥ 1`): it is a
zero-false-alarm rule whose miss probability is exactly `exp(−N_a)`. -/
theorem poisson_darkBaseline_miss_optimum (Na : ℝ≥0) :
    falseAlarm 0 (thresholdRule 1) = 0 ∧
      missProb Na (thresholdRule 1) = Real.exp (-(Na : ℝ))

/-- **The zero-false-alarm hypothesis is load-bearing**: drop it and the floor is false. The
always-declare rule (`thresholdRule 0`) misses with probability `0 < exp(−N_a)`. -/
theorem darkBaseline_zeroFalseAlarm_load_bearing (Na : ℝ≥0) :
    missProb Na (thresholdRule 0) < Real.exp (-(Na : ℝ))
```

Key computations (both `simp`-level once unfolded):
* `falseAlarm 0 δ = δ 0`, because `poissonPMFReal 0 0 = 1` and `poissonPMFReal 0 n = 0` for
  `n ≥ 1` (`0 ^ 0 = 1`, `0 ^ (n+1) = 0`). Hence `hFA ⟺ δ 0 = 0`.
* `missProb Na δ ≥ poissonPMFReal Na 0 * (1 - δ 0) = exp(−N_a)` — a single-term lower bound on a
  nonneg `tsum` (`le_tsum` / `Summable.le_tsum`).
* `poissonPMFReal r 0 = Real.exp (-(r:ℝ))` by `simp [poissonPMFReal]` (`pow_zero`,
  `Nat.factorial_zero`).
* `thresholdRule 0 = fun _ => 1`, so `missProb Na (thresholdRule 0) = 0` and
  `0 < Real.exp _` by `Real.exp_pos`.

**Deviation from the roadmap's AC (documented):** the single AC bullet
`poisson_darkBaseline_miss_optimum` is split into three declarations. Reason — checklist #1
(bundle redundancy): folding "floor" + "attainment" + "hypothesis is load-bearing" into one
statement produces a 3-conjunct bundle whose parts are logically independent and separately
citable. The roadmap's name is retained on the attainment statement.

### 5.7 On the demoted AC item `poissonTV_le_of_bhattacharyya`

**Recommendation: drop it from Wave 1's must-ship list; keep the name for an optional
companion.** Two reasons:

1. It is not on the critical path (§5.3).
2. Stated about the *true* total variation between the two Poisson laws
   (`½∑'ₙ|p_b n − p_a n| ≤ √(1 − BC²)`), it needs the sup over rules to be *attained*, i.e. an
   explicit monotone-likelihood-ratio argument identifying the positive-part set
   `{n : p_b n > p_a n}` as an initial segment. That argument is **not in the roadmap's brick
   list** and is a real chunk of work.

If a TV-flavoured statement is wanted in Wave 1, freeze instead the *achievable* and
operationally meaningful form, which is one `classical_fvdg` application away (this **is** the
place where importing `FidelityUpperBound` would earn its keep):

```lean
/-- No count rule's discrimination margin exceeds `√(1 − BC²)`. -/
theorem poisson_ruleMargin_le {Nb Na : ℝ≥0} {δ : ℕ → ℝ} (hδ : IsCountRule δ) :
    |1 - falseAlarm Nb δ - missProb Na δ|
      ≤ √(1 - Real.exp (-(√(Na : ℝ) - √(Nb : ℝ)) ^ 2))
```

---

## 6. FROZEN — the refutation witnesses (verified arithmetic)

Both roadmap-suggested witnesses are **arithmetically correct**. Both admit a strictly stronger
universally-quantified form (F9) which is what should ship as the headline; the `norm_num`
witness then carries the *quantitative* gap.

All numbers below computed at 40-digit precision (`mpmath`); the script is throwaway and is not
committed.

### 6.1 W1 — `folklore_miss_floor_false` (`N_b = 5`, `N_a = 10`)

| quantity | value |
|---|---|
| `missProb 10 (thresholdRule 1) = poissonPMFReal 10 0 = exp(−10)` | `4.53999297625e−5` |
| folklore floor `exp(−(N_a − N_b)) = exp(−5)` | `6.73794699909e−3` |
| **violation factor `folklore / miss = exp(N_b) = e⁵`** | **`148.413159103`** |

**The general fact.** `miss(≥1 rule) = e^{−N_a}` and folklore `= e^{−(N_a−N_b)}`, so the folklore
floor is undershot by exactly `e^{N_b}` — **for every bright baseline, at every `N_a`**, with no
`N_b < N_a` needed. That is precisely the roadmap guardrail's "an ideal unit-threshold counter
beats it whenever the baseline is bright", now as a theorem rather than an example.

```lean
/-- **The folklore miss floor `miss ≥ e^{−(N_a − N_b)}` is FALSE for every bright baseline.**
The ideal unit-threshold counter (`count ≥ 1`) misses with probability exactly `e^{−N_a}`,
undershooting the folklore floor by the factor `e^{N_b}`. The folklore form quotes no
false-alarm constraint, and this rule has none imposed; the correct constrained statement is
`poisson_darkBaseline_miss_floor`. -/
theorem folklore_miss_floor_false {Nb Na : ℝ≥0} (hNb : 0 < Nb) :
    missProb Na (thresholdRule 1) < Real.exp (-((Na : ℝ) - Nb))
```
Proof: `missProb Na (thresholdRule 1) = poissonPMFReal Na 0 = exp(−N_a)` (§5.6), then
`Real.exp_lt_exp.mpr` with `-(Na:ℝ) < -(Na:ℝ) + Nb` from `NNReal.coe_pos.mpr hNb` + `linarith`.

**Quantitative companion** (checklist #2: put the numerical relationship in the statement, and
— checklist #3 — make a real call into the cited brick `expNeg_enclosure`):

```lean
/-- Quantitative form at the roadmap's operating point `N_b = 5, N_a = 10`: the unit-threshold
counter beats the folklore floor by at least a factor of 6. The constant comes from
`SKEFTHawking.QuantumNetwork.expNeg_enclosure` at `r = 5` (`e^{−5} ≤ 1/(1+5)`). -/
theorem folklore_missFloor_beaten_sixfold :
    6 * missProb 10 (thresholdRule 1) ≤ Real.exp (-((10 : ℝ) - 5))
```
Proof: LHS `= 6·exp(−10) = 6·exp(−5)·exp(−5)`; `(expNeg_enclosure (by norm_num : (0:ℝ) ≤ 5)).2`
gives `exp(−5) ≤ 1/6`; multiply. **Verified:** `6 × 4.53999e−5 = 2.72400e−4 ≤ 6.73795e−3`. ✓

*Optional sharpening to the true factor 148* (only if the slot wants it): `Real.exp_one_gt_d9`
→ `(2.718 : ℝ) < Real.exp 1` by transitivity, then `Real.exp_nat_mul` gives
`exp 5 = (exp 1)^5 > 2.718^5 = 148.3362 > 148` (verified). Not required.

### 6.2 W2 — `folklore_avg_floor_unsound` (`N_b = 50`, `N_a = 60`)

| quantity | value |
|---|---|
| `√60`, `√50` | `7.74596669241`, `7.07106781187` |
| `(√N_a − √N_b)² = N_a + N_b − 2√(N_a N_b) = 110 − 2√3000` | `0.455488498967` |
| `√3000` | `54.7722557505` |
| **Le Cam floor `¼·exp(−(√N_a−√N_b)²)`** | **`0.158534529115`** |
| **folklore `exp(−(N_a−N_b)) = exp(−10)`** | **`4.53999297625e−5`** |
| **ratio (true floor / folklore)** | **`3491.95538284`** |

Roadmap's quoted "`0.158… > 4.6e−5`" is **confirmed**.

**The general characterization.** With `a = √N_a`, `b = √N_b`,
`(N_a − N_b) − (√N_a − √N_b)² = (a−b)(a+b) − (a−b)² = 2b(a−b)`. So

> the Le Cam floor exceeds the folklore form **exactly when `2√N_b(√N_a − √N_b) > log 4`**,

i.e. whenever the baseline is bright relative to the separation. Stating the hypothesis in
`exp` form keeps `Real.log` out of the statement entirely and makes the witness a
`Real.add_one_le_exp` one-liner:

```lean
/-- **The folklore form fails OPEN as an average-error screen.** Whenever
`4 < exp(2√N_b(√N_a − √N_b))` — i.e. whenever the baseline is bright relative to the
separation — the true Le Cam floor `¼·exp(−(√N_a−√N_b)²)` STRICTLY EXCEEDS the folklore value
`exp(−(N_a−N_b))`. A screen built on the folklore form therefore admits configurations that the
true floor forbids. -/
theorem folklore_avgFloor_unsound_of_bright {Nb Na : ℝ≥0}
    (h : (4 : ℝ) < Real.exp (2 * √(Nb : ℝ) * (√(Na : ℝ) - √(Nb : ℝ)))) :
    Real.exp (-((Na : ℝ) - Nb))
      < (1 / 4) * Real.exp (-(√(Na : ℝ) - √(Nb : ℝ)) ^ 2)
```

Proof recipe (all `Real.exp` algebra, no `log`):
1. `(√Na − √Nb)² = (Na + Nb) − 2√Na√Nb` by `Real.sq_sqrt` (both rates `≥ 0` as `ℝ≥0` coercions).
2. Goal ⟺ `4 * exp(−(Na−Nb)) < exp(−(√Na−√Nb)²)`; divide through by `exp(−(Na−Nb)) > 0`
   (`mul_lt_mul_right (Real.exp_pos _)`) after `← Real.exp_sub`, reducing to
   `4 < exp((Na − Nb) − (√Na − √Nb)²)`.
3. `(Na − Nb) − (√Na − √Nb)² = 2√Nb(√Na − √Nb)` by `Real.sq_sqrt` + `ring`.
4. Apply `h`. ∎

```lean
/-- Roadmap-named witness at `N_b = 50, N_a = 60`. -/
theorem folklore_avg_floor_unsound :
    Real.exp (-((60 : ℝ) - 50))
      < (1 / 4) * Real.exp (-(√(60 : ℝ) - √(50 : ℝ)) ^ 2)
```

Discharge of the hypothesis at `(50, 60)` — **fully verified**:
* `2√50(√60 − √50) = 2√3000 − 100` via `← Real.sqrt_mul` (`√50·√60 = √3000`) and
  `Real.mul_self_sqrt` (`√50·√50 = 50`).
* `54.77 < √3000` by `Real.lt_sqrt (by norm_num) |>.mpr` with `54.77² = 2999.7529 < 3000`
  (`norm_num`). ✓
* Hence `2√3000 − 100 > 2(54.77) − 100 = 9.54`.
* `Real.add_one_le_exp 9.54` gives `exp(9.54) ≥ 10.54 > 4`. ✓
  (True value `exp(9.54451…) = 13967.82`.)

**Quantitative companion** (optional, checklist #2):

```lean
/-- The true floor exceeds the folklore value by more than a factor of 1000 at `(50, 60)`. -/
theorem folklore_avgFloor_unsound_factor1000 :
    1000 * Real.exp (-((60 : ℝ) - 50))
      < (1 / 4) * Real.exp (-(√(60 : ℝ) - √(50 : ℝ)) ^ 2)
```
Needs `exp(2√3000 − 100) > 4000`. Route: `exp(9.54) > exp 9 = (exp 1)^9`
(`Real.exp_nat_mul`, `Real.exp_lt_exp`), and `(exp 1)^9 > 2.718^9 = 8095.526 > 4000`
via `(2.718 : ℝ) < Real.exp 1` (transitivity through `Real.exp_one_gt_d9`) + `norm_num`.
**Verified:** true ratio `3491.96 > 1000`. ✓ *(Use `2.718`, not `2.7182818283`, to keep the
`norm_num` rational small.)*

### 6.3 Both witnesses: what makes them non-trivial

Neither reduces to `Real.exp_lt_exp` alone:

* W1's content is the **pmf evaluation** `missProb Na (thresholdRule 1) = poissonPMFReal Na 0`
  (a `tsum_eq_single` on the rule's `1 − δ` profile) plus the identification
  `poissonPMFReal r 0 = exp(−r)` — the miss probability is *computed from the Poisson pmf*, not
  asserted. The quantitative companion additionally calls `expNeg_enclosure`.
* W2's content is the **Bhattacharyya-exponent algebra** `(√N_a − √N_b)² = N_a + N_b − 2√(N_aN_b)`
  and the resulting exact characterization `2√N_b(√N_a − √N_b) > log 4`, which is a genuine,
  checkable condition on the physical parameters — not a rewrite.

---

## 7. FROZEN — Wave 2 statement layer

**File:** `lean/SKEFTHawking/Detection/GaussianThreshold.lean`
**Namespace:** `SKEFTHawking.Detection`
**Root import:** same-commit addition to `lean/SKEFTHawking.lean` (F8).

Wave 2 is **independent of Wave 1** (different file, disjoint substrate) — parallelizable, as the
roadmap says. It shares only `avgAssignmentError`.

### 7.1 Header + definitions

```lean
import Mathlib.Probability.Distributions.Gaussian.Real
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import SKEFTHawking.QuantumNetwork.ReadoutRelaxationBound

namespace SKEFTHawking.Detection
open ProbabilityTheory Real MeasureTheory SKEFTHawking.QuantumNetwork

/-- Standard-normal upper-tail probability. Mathlib carries no `erf`/`erfc`/Gaussian-CDF at
pin `5e932f97` (verified 2026-07-27); this is therefore project-local. -/
noncomputable def gaussianQ (z : ℝ) : ℝ := ∫ x in Set.Ioi z, gaussianPDFReal 0 1 x

/-- False-alarm branch error for a threshold classifier with baseline mean `μ₀`, common
standard deviation `σ > 0`, and threshold `t`. -/
noncomputable def thrErr0 (μ₀ σ t : ℝ) : ℝ := gaussianQ ((t - μ₀) / σ)

/-- Miss branch error for the same classifier with signal mean `μ₁`. -/
noncomputable def thrErr1 (μ₁ σ t : ℝ) : ℝ := gaussianQ ((μ₁ - t) / σ)
```

### 7.2 Structural lemmas (must-ship, all cheap)

```lean
/-- `Q 0 = 1/2`. From `Real.integral_gaussian_Ioi` at `b = 1/2`:
`∫_{Ioi 0} exp(−x²/2) = √(2π)/2`, and `gaussianPDFReal 0 1 x = (1/√(2π))·exp(−x²/2)`. -/
theorem gaussianQ_zero : gaussianQ 0 = 1 / 2

/-- `Q` is antitone (the tail integral shrinks as the cut moves right). -/
theorem gaussianQ_antitone : Antitone gaussianQ

/-- Reflection: `Q(−z) = 1 − Q(z)`. (Needed to write the miss branch as a `Q` value.) -/
theorem gaussianQ_neg (z : ℝ) : gaussianQ (-z) = 1 - gaussianQ z

/-- `0 ≤ Q z ≤ 1`, and `Q z ≤ 1/2` for `z ≥ 0`. -/
theorem gaussianQ_nonneg (z : ℝ) : 0 ≤ gaussianQ z
theorem gaussianQ_le_half {z : ℝ} (hz : 0 ≤ z) : gaussianQ z ≤ 1 / 2
```

### 7.3 Tail bounds — the UNKNOWN-2 freeze

```lean
-- MUST-SHIP (§3.3 Tier A)
theorem gaussianTail_ge_window {z c : ℝ} (hz : 0 ≤ z) (hc : 0 < c) :
    c * gaussianPDFReal 0 1 (z + c) ≤ gaussianQ z

-- MUST-SHIP (upper, §3.4)
theorem gaussianTail_mills {z : ℝ} (hz : 0 < z) :
    gaussianQ z ≤ gaussianPDFReal 0 1 z / z

theorem gaussianTail_chernoff_of_le_08 {z : ℝ} (hz : (0.8 : ℝ) ≤ z) :
    gaussianQ z ≤ (1 / 2) * Real.exp (-z ^ 2 / 2)

-- STRETCH (§3.3 Tier B) — substituting this changes NO consuming statement
theorem gaussianTail_birnbaum {z : ℝ} (hz : 0 < z) :
    z / (1 + z ^ 2) * gaussianPDFReal 0 1 z ≤ gaussianQ z
```

`gaussianTail_mills` and `gaussianTail_birnbaum` share one workhorse — build it first:

```lean
/-- `∫_{Ioi z} x · φ(x) dx = φ(z)`, from `integral_Ioi_of_hasDerivAt_of_tendsto` with
antiderivative `−φ` (`φ' = −x·φ`). -/
theorem gaussianPDF_moment_Ioi (z : ℝ) :
    ∫ x in Set.Ioi z, x * gaussianPDFReal 0 1 x = gaussianPDFReal 0 1 z
```
Mills is then `φ(x) ≤ (x/z)·φ(x)` on `Ioi z` + `setIntegral_mono` + this identity.
`gaussianTail_chernoff_of_le_08` follows from Mills: `φ(z)/z = e^{−z²/2}/(z√(2π))` and
`1/(z√(2π)) ≤ 1/2 ⟺ 2 ≤ z√(2π)`, discharged at `z ≥ 0.8` by
`(Real.le_sqrt (by norm_num) (by positivity)).mpr` on `2.5 ≤ √(2π)` — i.e. `6.25 ≤ 2π`, from
`Real.pi_gt_d2 : 3.14 < π` + `norm_num` — since `0.8 × 2.5 = 2`.
**Verified:** `1/(0.8·√(2π)) = 0.498678 ≤ 0.5`. ✓ *(`Real.pi_gt_three` is too weak here —
it gives only `2π > 6`; use `pi_gt_d2`.)*

### 7.4 Threshold algebra (must-ship)

```lean
/-- **Conservativity workhorse**: both branch errors increase with `σ` when the threshold lies
between the means. -/
theorem thrErr0_mono_in_sigma {μ₀ σ σ' t : ℝ} (hσ : 0 < σ) (hσ' : σ ≤ σ') (ht : μ₀ < t) :
    thrErr0 μ₀ σ t ≤ thrErr0 μ₀ σ' t
theorem thrErr1_mono_in_sigma {μ₁ σ σ' t : ℝ} (hσ : 0 < σ) (hσ' : σ ≤ σ') (ht : t < μ₁) :
    thrErr1 μ₁ σ t ≤ thrErr1 μ₁ σ' t

/-- **ROC tradeoff**: moving the threshold right trades false alarm against miss, monotonically
and in opposite directions. -/
theorem offCenter_threshold_tradeoff {μ₀ μ₁ σ t t' : ℝ} (hσ : 0 < σ) (h : t ≤ t') :
    thrErr0 μ₀ σ t' ≤ thrErr0 μ₀ σ t ∧ thrErr1 μ₁ σ t ≤ thrErr1 μ₁ σ t'

/-- **Midpoint symmetry, with the value.** At equal σ and the midpoint threshold the two branch
errors are equal AND equal to `Q` of the half-separation. -/
theorem midpoint_threshold_symmetric {μ₀ μ₁ σ : ℝ} (hσ : 0 < σ) :
    thrErr0 μ₀ σ ((μ₀ + μ₁) / 2) = gaussianQ ((μ₁ - μ₀) / (2 * σ)) ∧
      thrErr1 μ₁ σ ((μ₀ + μ₁) / 2) = gaussianQ ((μ₁ - μ₀) / (2 * σ))
```

> **Strengthening note (checklist #4, flagged now so the slot does not ship the weak form).**
> The roadmap's `midpoint_threshold_symmetric : equal σ → e₀ = e₁` alone is a
> definitional-unfolding tautology (`(t−μ₀)/σ = (μ₁−t)/σ` at the midpoint is `field_simp`). It
> is strengthened above by **naming the value** `gaussianQ ((μ₁−μ₀)/(2σ))`, which is what makes
> it composable with §7.5. Ship the strengthened form.

### 7.5 The load-bearing floor (must-ship + stretch)

```lean
/-- **Separation-budget error floor, uniform over thresholds.** If the mean separation in units
of σ is at most `2·z₀`, then NO threshold placement gets the average branch error below
`½·Q(z₀)`. This is the ceiling-on-fidelity direction: `Q` is bounded below by
`gaussianTail_ge_window`, so the floor is fully rational once a window `c` is chosen. -/
theorem avgError_ge_half_gaussianQ {μ₀ μ₁ σ t z₀ : ℝ}
    (hσ : 0 < σ) (hμ : μ₀ ≤ μ₁) (hz : (μ₁ - μ₀) / (2 * σ) ≤ z₀) :
    (1 / 2) * gaussianQ z₀ ≤ avgAssignmentError (thrErr0 μ₀ σ t) (thrErr1 μ₁ σ t)
```
Proof (cheap, ≈15 lines): let `m = (μ₀+μ₁)/2`. If `t ≥ m` then `(μ₁−t)/σ ≤ (μ₁−μ₀)/(2σ) ≤ z₀`,
so `thrErr1 ≥ gaussianQ z₀` by `gaussianQ_antitone`; if `t ≤ m` the symmetric argument gives
`thrErr0 ≥ gaussianQ z₀`. Either way `e₀ + e₁ ≥ gaussianQ z₀`, hence
`avgAssignmentError e₀ e₁ ≥ ½·gaussianQ z₀`. `rcases le_total t m`.

```lean
/-- **STRETCH — the sharp (factor-2 better) form.** The midpoint threshold minimizes the
average branch error at equal σ, so the floor is `Q(z₀)`, not `½·Q(z₀)`, and it is attained. -/
theorem avgError_ge_gaussianQ_sharp {μ₀ μ₁ σ t z₀ : ℝ}
    (hσ : 0 < σ) (hμ : μ₀ ≤ μ₁) (hz : (μ₁ - μ₀) / (2 * σ) ≤ z₀) :
    gaussianQ z₀ ≤ avgAssignmentError (thrErr0 μ₀ σ t) (thrErr1 μ₁ σ t)
```
Recipe: with `h := (μ₁−μ₀)/(2σ)` and `u := (t−μ₀)/σ` (so the miss argument is `2h − u`), use
`gaussianQ_neg` to write `Q(u) + Q(2h−u) = 1 + Q(u) − Q(u−2h)`, so the claim reduces to
*among all intervals of fixed length `2h`, the one centred at `0` maximizes `∫ φ`* — which
follows from `φ` even and antitone on `[0,∞)`. Ship the `avgError_ge_half_gaussianQ` form first;
this one supersedes it without restating any consumer (`(1/2)*` drops out).

---

## 8. Preemptive-strengthening checklist, applied per frozen theorem

Checklist per `docs/WAVE_EXECUTION_PIPELINE.md` Stage 3a. `Q1` bundle redundancy · `Q2`
numerical connection · `Q3` cross-module bridge integrity · `Q4` trivial discharge ·
`Q5` defining-the-conclusion.

| Declaration | Q1 | Q2 | Q3 | Q4 | Q5 | Note |
|---|---|---|---|---|---|---|
| `affinity_le_binaryAffinity` | ✓ | n/a | — | ✓ | ✓ | Content is infinite Cauchy–Schwarz; no rewrite closes it. |
| `binaryAffinity_sq_le_two_mul_add` | ✓ | n/a | cites `classical_fvdg` as **sibling, not dependency** — no call, and the docstring says so | ✓ | ✓ | `nlinarith` with `sq_sqrt` hints; not `rfl`-adjacent. |
| `avgError_ge_affinity_sq` | ✓ | n/a | **calls** `avgAssignmentError` (F7) | ✓ | ✓ | Distribution-free ⇒ reusable by 6EB/6EE. |
| `poissonBhattacharyya_hasSum` | ✓ | n/a | — | ✓ | ✓ | `HasSum` (not `tsum`) chosen deliberately: carries summability. |
| `poissonBhattacharyya_eq` | ✓ | n/a | **calls** the `HasSum` form | ✓ | ✓ | One-line corollary; kept for the roadmap's name. |
| `poisson_avgError_floor` | ✓ | ✓ (the `¼·exp(−(√N_a−√N_b)²)` constant is in the statement) | **calls** `avgAssignmentError` + `poissonBhattacharyya_eq` | ✓ | ✓ | ∀-quantified over every randomized rule — the roadmap's stated trap avoided. |
| `poisson_darkBaseline_miss_floor` | ✓ | ✓ | — | ✓ | ✓ | Zero-FA hypothesis explicit. |
| `poisson_darkBaseline_miss_optimum` | ⚠ 2 conjuncts, **independent** (zero-FA + exact value) → kept | ✓ | **calls** the floor | ✓ | ✓ | Split out of the roadmap's single AC bullet. |
| `darkBaseline_zeroFalseAlarm_load_bearing` | ✓ | ✓ | — | ⚠ closes by `Real.exp_pos` — **but that IS the content** (the hypothesis-drop refutation) | ✓ | Documented: cheap proof, substantive statement. |
| `folklore_miss_floor_false` | ✓ | ✓ | — | ✓ | ✓ | **∀, not ∃** — strengthened past the roadmap. |
| `folklore_missFloor_beaten_sixfold` | ✓ | ✓ (factor 6 in the statement) | **calls** `expNeg_enclosure` | ✓ | ✓ | The brick-reusing quantitative form. |
| `folklore_avgFloor_unsound_of_bright` | ✓ | ✓ | — | ✓ | ✓ | Hypothesis is a real, checkable parameter condition. |
| `folklore_avg_floor_unsound` | ✓ | ✓ | **calls** the general form | ✓ | ✓ | Roadmap's name + operating point. |
| `gaussianQ_zero` | ✓ | ✓ (`= 1/2`) | — | ✓ | ✓ | Pins the normalization; `integral_gaussian_Ioi`. |
| `gaussianTail_ge_window` | ✓ | ✓ | — | ✓ | ✓ | Global, parametric; no vacuity regime. |
| `gaussianTail_chernoff_of_le_08` | ✓ | ✓ | **calls** `gaussianTail_mills` | ✓ | ✓ | Side condition explicit (§3.4). |
| `midpoint_threshold_symmetric` | ⚠ 2 conjuncts, both **valued** | ✓ | — | ⚠ **strengthened** past the roadmap's `e₀ = e₁` tautology by naming the value | ✓ | See §7.4 note. |
| `avgError_ge_half_gaussianQ` | ✓ | ✓ | **calls** `avgAssignmentError` + `gaussianQ_antitone` | ✓ | ✓ | Uniform over `t`; the load-bearing floor. |

**Cross-cutting non-vacuity check.** Every floor in this document is verified strictly positive
at its stated operating point: `poisson_avgError_floor` at `(50, 60)` returns `0.1585`
(§6.2); `poisson_darkBaseline_miss_floor` at `N_a = 10` returns `4.54e−5`;
`gaussianTail_ge_window` at `z = 3, c = 1/3` returns `5.14e−4`. None is a "trivially true floor".

---

## 9. Deviations from `Phase6EA_Roadmap.md` — the lead's decision list

| # | Roadmap says | Freeze says | Requires lead sign-off? |
|---|---|---|---|
| D1 | Brick `Mathlib Probability.Distributions.Poisson` | `Mathlib.Probability.Distributions.Poisson.Basic`; rate is `ℝ≥0` | No — factual correction |
| D2 | Brick `Physlib.QuantumInfo.…HypothesisTesting` | `QuantumInfo.Finite.ResourceTheory.HypothesisTesting` | No — factual correction |
| D3 | Wave-1 AC `poissonTV_le_of_bhattacharyya` | **Demoted** to optional; replaced by `poisson_ruleMargin_le` if wanted (§5.6) | **Yes** — drops an AC bullet |
| D4 | Wave-1 AC `poisson_darkBaseline_miss_optimum` (one bullet) | **Split into 3** declarations (§5.6) | No — strictly more content |
| D5 | Wave-1 AC `folklore_miss_floor_false : ∃ …` | **Universally quantified** + a quantitative companion (§6.1) | No — strictly stronger |
| D6 | Wave-1 AC `folklore_avg_floor_unsound : ∃ …` | **General characterization** + the roadmap's witness (§6.2) | No — strictly stronger |
| D7 | Wave-2 AC `gaussianTail_chernoff` for `z ≥ 0` | `gaussianTail_chernoff_of_le_08` (+ `gaussianQ_le_half`); full `z ≥ 0` is a stretch (§3.4) | **Yes** — narrows an AC bullet |
| D8 | Wave-2 AC lower tail: "interval-restricted rational **or** `z/(1+z²)φ(z)`; pick at Stage 2" | **Interval-restricted form REJECTED** (vacuous at `z > 1.2533`). Must-ship = the window bound; `z/(1+z²)φ(z)` = stretch (§3.3) | No — this is the UNKNOWN-2 resolution the roadmap asked for |
| D9 | Wave-2 AC `midpoint_threshold_symmetric : equal σ → e₀ = e₁` | Strengthened to name the value (§7.4) | No — strictly stronger |
| D10 | Wave-2 AC `avg_error_ge_of_z_le` | `avgError_ge_half_gaussianQ` (uniform over `t`, factor-2 loose) must-ship; sharp form stretch (§7.5) | **Yes** — factor 2 vs the sharp constant |
| D11 | Wave-3 seam: "diagonal restriction of Helstrom **vs** an `OptimalHypothesisRate` specialization" | The `OptimalHypothesisRate` option is **type-level impossible** for Poisson (F4). Recommend (S1)+(S2); defer (S3) (§4) | **Yes** — changes Wave-3 scope |
| D12 | "The root `SKEFTHawking.lean` import addition lands in Wave 3" | **Each wave adds its own root import in its own commit** (F8) — otherwise Waves 1–2 are outside `lake build` and the zero-sorry gate | No — corrects a build-visibility defect |
| D13 | Wave-1 brick `classical_fvdg` | Cited as **structural sibling**; **not imported** — Wave 1's need is a different inequality (F6), and the import would pull the trace-norm tower into `Detection/` | No — the roadmap's own word is "template" |

**Four items (D3, D7, D10, D11) narrow or re-shape a roadmap AC bullet and need the lead's
sign-off.** All four are argued above from verified substrate; none is an expediency de-scope —
D7 and D10 ship the *provable* form now with the sharper form specified and non-breaking, and
D3/D11 remove statements that are respectively off-critical-path and type-level impossible.

---

## 10. Execution notes for the Lean slot

1. **Order.** Wave 1 and Wave 2 are independent — run them in two slots. Within Wave 1:
   §5.2 defs → `poissonBhattacharyya_hasSum` → §5.3 generic chain → `poisson_avgError_floor`
   → §5.6 dark baseline → §6 witnesses. Within Wave 2: §7.1–7.2 → `gaussianTail_ge_window`
   → `gaussianPDF_moment_Ioi` → Mills/Chernoff → §7.4 → §7.5.
2. **Root import in the same commit** (F8). `lean/SKEFTHawking.lean` is a single-writer file:
   if both slots are live, one takes the edit and the other rebases, or the lead applies both
   at merge. Do **not** defer it.
3. **Invariants.** Kernel-pure `{propext, Classical.choice, Quot.sound}` — confirm every
   headline with `lean_verify`. Zero `sorry`, zero `native_decide`, **no `maxHeartbeats` in any
   proof body**. If a proof walls on heartbeats, decompose into ≤12-term `have` sub-lemmas —
   the §5.3/§7.5 decompositions above are already sized for that. **No new project-local
   `axiom`** (none is needed anywhere in this freeze).
4. **`norm_num` hygiene.** Every witness constant above is rational and small. The only
   large-rational risk is the optional `folklore_avgFloor_unsound_factor1000`: use
   `(2.718 : ℝ) < Real.exp 1` (transitivity through `Real.exp_one_gt_d9`), **not**
   `2.7182818283` directly, so `norm_num` sees a 4-digit base rather than an 11-digit one.
5. **Do not re-derive UNKNOWN-2's rejected branch.** The interval-restricted rational lower tail
   is settled-dead for this phase (§3.2) — it is vacuous exactly in 6EE's operating range. If a
   proof attempt starts reconstructing `Q z ≥ 1/2 − z/√(2π)` as the headline lower tail, stop.
6. **Post-wave.** Run the ruthless post-wave strengthening audit (mandatory, §8 is the
   *prospective* pass only), refresh `SK_EFT_Hawking_Inventory.md` + the Inventory Index +
   `update_counts.py` for the new `Detection/` family, and log the audit in the phase notebook.

---

*Stage-2 freeze authored 2026-07-27 in worktree slot `py1` (branch `worktree-py1`). All Mathlib /
PhysLib / project claims above were verified by reading the cited source files at the pinned
revisions; both refutation witnesses were verified numerically at 40-digit precision before
being frozen.*
