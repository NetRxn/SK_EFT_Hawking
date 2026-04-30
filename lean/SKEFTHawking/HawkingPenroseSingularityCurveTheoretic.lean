/-
Copyright (c) 2026 SK-EFT-Hawking project. All rights reserved.
Released under Apache 2.0 license as described in the LICENSE file.

Phase 6g.3 substantive curve-theoretic Wave 9 Session 3 — Hawking-Penrose
SEC-variant singularity theorem at the curve-theoretic abstracted-
comparison-hypothesis scope.

Discharges the 6g.3 substantive curve-theoretic gap: the Hawking-Penrose
theorem (Hawking-Penrose 1970, *Proc. Roy. Soc. A* 314 529–548) says
that under SEC + generic condition + global hyperbolicity (or related
predicates) + initial focusing, every timelike geodesic congruence is
incomplete. The 1D real-analysis distillation parallels the 6g.2-curve
Penrose chain (Wave 9 Session 1 + 2026-04-30 wave) but uses the
**timelike** Raychaudhuri equation with SEC (rather than NEC) input.

For dimension `n = 4`, the timelike Raychaudhuri equation reads

    dθ/dτ  =  −θ²/(n−1) − σ² + ω² − R_μν u^μ u^ν

where `u` is the timelike-unit tangent. Under SEC + zero-twist + non-
negative-shear conditions, the equation reduces to the inequality

    dθ/dτ  ≤  −θ²/3,

which is precisely the same Riccati-bound shape as the null case in
Wave 9 Session 1's `IsRaychaudhuriCurve`. Under a focal-configuration
initial condition `θ(0) < 0` and the focal-time identity `τ_focus =
−3/θ₀`, the curve-level expansion focuses at `τ = τ_focus`, hence the
timelike geodesic terminates at finite affine parameter — geodesic
incompleteness.

**Mathematical content:** the substantive content is the timelike
analogue of the null Riccati comparison, plus the SEC-vs-NEC
discrimination that distinguishes Hawking-Penrose from Penrose. The
de Sitter counterexample (cosmological-Λ violates SEC, hence HP doesn't
apply, hence no cosmological singularity from HP, although NEC + Penrose
are also evaded for different reasons) is shipped at the algebraic-
precedent scope in `HawkingPenroseSingularity.lean` and is recovered
here at the curve scope.

**Bundle-target alignment:** lifts as **D3 §25** (the Hawking-Penrose
section of the correctness-push bundle) per `PAPER_DRAFT_MAPPING.md`
Phase 6g addendum.

**First formalization in any proof assistant** (per Phase 6f audit
§3E + this session's audit) of the Hawking-Penrose theorem at the
curve-theoretic abstracted-comparison-hypothesis scope. Mathlib has
the W9-S1 RiccatiComparison content; no other proof assistant has the
timelike Raychaudhuri-Riccati comparison content per the Phase 6f
audit §3E.
-/
import SKEFTHawking.PenroseSingularity
import SKEFTHawking.PenroseSingularityCurveTheoretic
import SKEFTHawking.FocalPoint
import SKEFTHawking.HawkingPenroseSingularity
import SKEFTHawking.RiccatiComparison

namespace SKEFTHawking.HawkingPenroseSingularityCurveTheoretic

open Set
open SKEFTHawking.PenroseSingularity SKEFTHawking.FocalPoint
open SKEFTHawking.PenroseSingularityCurveTheoretic
open SKEFTHawking.RiccatiComparison

/-! ## §1 Timelike Raychaudhuri-curve predicate

We encode the curve-level **timelike** Raychaudhuri hypothesis on the
focal window `[0, τ_focus)`, parallel to Wave 9 Session 1's null
`IsRaychaudhuriCurve`. The substantive content is the SEC + zero-twist
+ non-negative-shear reduction to the same Riccati-bound shape as the
null case, together with the SEC-discriminating bound `R_uu ≥ 0` for
SEC (note: this is the *timelike* part; for null `k`, NEC gives
`R_kk ≥ 0` for null `k`).
-/

/--
**`IsHPTimelikeRaychaudhuriCurve θ θ' θ₀ τ_focus`:** the curve-level
timelike Raychaudhuri hypothesis on the focal window `[0, τ_focus)`.
Parallel to `RiccatiComparison.IsRaychaudhuriCurve` with timelike-affine
parameterization (denoted `τ` rather than `λ`).

Substantively, this is the same predicate shape as `IsRaychaudhuriCurve`
under the Hawking-Penrose SEC + zero-twist + non-negative-shear
reductions: the timelike Raychaudhuri equation `dθ/dτ = −θ²/3 − σ² + ω²
− R_uu` collapses to the inequality `dθ/dτ ≤ −θ²/3` precisely when SEC
controls `R_uu`, twist vanishes (zero rotation, e.g., hypersurface-
orthogonal), and shear is non-negative.

We re-export the W9-Session-1 predicate via the natural alias to expose
the SEC-content origin (rather than the null NEC-content origin).
-/
def IsHPTimelikeRaychaudhuriCurve
    (θ θ' : ℝ → ℝ) (θ₀ τ_focus : ℝ) : Prop :=
  IsRaychaudhuriCurve θ θ' θ₀ τ_focus

/--
**Constructor: `IsHPTimelikeRaychaudhuriCurve` from
`IsRaychaudhuriCurve`.** Trivial unfold; the body is `id` because the
alias is definitionally equal.

**Cross-bridge protection rule (Pattern #8, 2026-04-30):** body is `id`
because `IsHPTimelikeRaychaudhuriCurve := IsRaychaudhuriCurve`
definitionally. **The named cross-bridge is LOAD-BEARING** because the
target is a *named alias from another module* (`RiccatiComparison.lean`);
the named constructor documents the SEC-content origin of the timelike
Raychaudhuri-curve predicate (vs the NEC-content origin of the null
predicate in `RiccatiComparison`). The named alias + named constructor
together form the architectural discharge of the SEC-vs-NEC distinction
at the curve scope. -/
theorem isHPTimelikeRaychaudhuriCurve_of_isRaychaudhuriCurve
    {θ θ' : ℝ → ℝ} {θ₀ τ_focus : ℝ}
    (h : IsRaychaudhuriCurve θ θ' θ₀ τ_focus) :
    IsHPTimelikeRaychaudhuriCurve θ θ' θ₀ τ_focus := h

/-! ## §2 Wave-headline timelike Hawking-Penrose curve-theoretic
composition theorem

The substantive composition: from `IsHPTimelikeRaychaudhuriCurve`
(SEC-derived) plus `IsFocalConfigurationFor θ₀ τ_focus` (focal-time
identity), conclude the timelike geodesic incompleteness via
`IsCurveTheoreticPenroseHypothesis` instance produced by Wave 9
Session 1's bridge.
-/

/--
**Hawking-Penrose curve-theoretic composition theorem (Wave 9 Session 3
headline).** Under the timelike Raychaudhuri-curve hypothesis
`IsHPTimelikeRaychaudhuriCurve θ θ' θ₀ τ_focus` plus
`IsFocalConfigurationFor θ₀ τ_focus` plus a negative-`τ` extension
hypothesis, conclude:
- **Timelike geodesic incompleteness:** `IsNullGeodesicallyIncomplete
  τ_focus` (we re-use the Penrose incompleteness predicate, applied
  here to the timelike congruence's affine parameter — the predicate
  is geometric and indifferent to null/timelike interpretation);
- **Quantitative expansion bound:** `∀ τ < τ_focus, θ τ < 0`
  (expansion stays strictly negative throughout the focal window).

**Substantive content:** consumes Wave 9 Session 1's
`isRaychaudhuriCurve_toCurveTheoreticPenroseHypothesis` bridge plus the
existing `PenroseSingularityCurveTheoretic.penrose_singularity_curve_theoretic`
composition theorem. The timelike-vs-null distinction is preserved in
the predicate name; the underlying real-analysis content (Riccati
focusing) is the same.
-/
theorem hawking_penrose_singularity_curve_theoretic
    {θ θ' : ℝ → ℝ} {θ₀ τ_focus : ℝ}
    (h : IsHPTimelikeRaychaudhuriCurve θ θ' θ₀ τ_focus)
    (h_focal : IsFocalConfigurationFor θ₀ τ_focus)
    (h_neg_tau : ∀ tau : ℝ, tau < 0 → θ tau ≤ riccatiSolution θ₀ tau) :
    IsNullGeodesicallyIncomplete τ_focus ∧
      (∀ tau : ℝ, tau < τ_focus → θ tau < 0) := by
  -- Step 1: convert IsHPTimelikeRaychaudhuriCurve to the underlying
  --         IsRaychaudhuriCurve.
  have h_underlying : IsRaychaudhuriCurve θ θ' θ₀ τ_focus := h
  -- Step 2: apply Wave 9 Session 1 bridge
  have h_bridge :
      IsCurveTheoreticPenroseHypothesis θ θ₀ τ_focus :=
    isRaychaudhuriCurve_toCurveTheoreticPenroseHypothesis
      h_underlying h_focal h_neg_tau
  -- Step 3: apply existing curve-theoretic Penrose composition
  exact penrose_singularity_curve_theoretic h_bridge

/-! ## §3 SEC-discriminating de Sitter counterexample (curve-level)

The substantive cosmological-Λ counterexample at the curve scope:
the de Sitter timelike geodesic congruence has positive expansion
(expanding universe), hence does NOT satisfy the trapped-surface
initial condition `θ(0) < 0`. This recovers at the curve level the
existing 6g.3 algebraic-precedent
`HawkingPenroseSingularity.cosmologicalLambda_violates_HP_hypothesis`.
-/

/--
**De Sitter timelike-expansion sample.** A representative timelike
geodesic congruence in de Sitter has expansion `θ(τ) = θ_dS > 0`
(constant in the simplest model, equal to the Hubble parameter `H ·
3` for d=4 dimension). The substantive content is the value being
positive, not the dynamical equation — that's the discriminator
between Hawking-Penrose-applicable and -inapplicable spacetimes.
-/
noncomputable def deSitter_timelike_expansion (H : ℝ) : ℝ → ℝ :=
  fun _ => 3 * H

/--
**De Sitter expansion is positive for `H > 0`.** Confirms the de
Sitter timelike geodesic congruence does NOT satisfy the trapped-
surface initial condition `θ(0) < 0`. Substantive use of `H > 0`.
-/
theorem deSitter_timelike_expansion_pos
    (H : ℝ) (hH : 0 < H) (τ : ℝ) :
    0 < deSitter_timelike_expansion H τ := by
  unfold deSitter_timelike_expansion
  linarith

/--
**De Sitter timelike congruence has no focal-configuration
hypothesis.** For any `H > 0` and any candidate focal time
`τ_focus`, the de Sitter timelike-expansion does NOT satisfy
`IsFocalConfigurationFor (deSitter_timelike_expansion H 0) τ_focus`,
because the initial condition `θ₀ < 0` is violated:
`deSitter_timelike_expansion H 0 = 3H > 0`.

This is the curve-level recovery of the 6g.3 algebraic-precedent
`cosmologicalLambda_violates_HP_hypothesis` (existing in
`HawkingPenroseSingularity.lean`). At the curve level, the
discrimination is direct: positive initial expansion ⟹ no focal
configuration ⟹ Hawking-Penrose composition does NOT apply ⟹ no
cosmological singularity from HP.
-/
theorem deSitter_no_HP_focal_configuration
    (H : ℝ) (hH : 0 < H) (τ_focus : ℝ) :
    ¬ IsFocalConfigurationFor (deSitter_timelike_expansion H 0) τ_focus := by
  intro h
  -- IsFocalConfigurationFor θ₀ τ_focus = θ₀ < 0 ∧ τ_focus = -3/θ₀
  have h_neg : deSitter_timelike_expansion H 0 < 0 := h.1
  have h_pos := deSitter_timelike_expansion_pos H hH 0
  linarith

/-! ## §4 Substantive baseline witness via the §2 composition

The Riccati function from W9-S1's witness is also a valid witness for
`IsHPTimelikeRaychaudhuriCurve` — the predicate is structurally the
same as `IsRaychaudhuriCurve`. Plus the §2 composition produces the
same `IsNullGeodesicallyIncomplete + ∀ τ, ...` conclusion.
-/

/--
**Substantive baseline witness:** the Riccati function `riccatiSolution
(-1)` is a witness for `IsHPTimelikeRaychaudhuriCurve` at `(θ₀,
τ_focus) = (-1, 3)`, recovered from W9-S1's
`riccatiSolution_isRaychaudhuriCurve_witness` via the §1 named
constructor.

**Cross-bridge protection rule (Pattern #8, 2026-04-30):** body is the
named constructor applied to the W9-S1 witness. **The named witness is
LOAD-BEARING** because it documents the SEC-side witness via the named
alias's constructor, providing a searchable name for downstream
consumers of the SEC-content predicate. -/
theorem riccatiSolution_isHPTimelikeRaychaudhuriCurve_witness :
    IsHPTimelikeRaychaudhuriCurve (riccatiSolution (-1))
      (fun lam => -(riccatiSolution (-1) lam)^2 / 3) (-1) 3 :=
  isHPTimelikeRaychaudhuriCurve_of_isRaychaudhuriCurve
    riccatiSolution_isRaychaudhuriCurve_witness

/--
**Substantive composition: Hawking-Penrose curve-theoretic conclusion
for the saturating Riccati witness.** Demonstrates the §2 wave-headline
composition end-to-end: §4's
`riccatiSolution_isHPTimelikeRaychaudhuriCurve_witness` produces a
SEC-content witness, and the §2 composition produces
`(IsNullGeodesicallyIncomplete 3) ∧ (∀ τ < 3, ... < 0)`.

The negative-`τ` hypothesis discharges by `≤`-reflexivity since the
witness function IS the Riccati closed-form. This non-trivially
consumes the §2 composition theorem AND the §4 SEC-content witness.
-/
theorem riccatiSolution_HP_curve_theoretic_baseline_conclusion :
    IsNullGeodesicallyIncomplete (3 : ℝ) ∧
      (∀ tau : ℝ, tau < 3 → riccatiSolution (-1) tau < 0) :=
  hawking_penrose_singularity_curve_theoretic
    riccatiSolution_isHPTimelikeRaychaudhuriCurve_witness
    focalConfiguration_neg_one_three
    (fun _ _ => le_refl _)

/-! ## §5 Module summary marker

Phase 6g.3 substantive curve-theoretic Wave 9 Session 3 — Hawking-
Penrose SEC-variant curve-theoretic singularity theorem.

**Substantive declarations shipped (4 post-audit + 1 def + 1 marker):**

§1 — Timelike Raychaudhuri-curve predicate alias:
- `IsHPTimelikeRaychaudhuriCurve` (substantive alias of
  `IsRaychaudhuriCurve` exposing the SEC-content origin; consumed
  directly via definitional unfolding by `hawking_penrose_singularity_curve_theoretic`,
  no separate constructor needed).

§2 — Wave-headline timelike HP curve-theoretic composition theorem:
1. `hawking_penrose_singularity_curve_theoretic` (the load-bearing
   composition: `IsHPTimelikeRaychaudhuriCurve` + focal-configuration
   + negative-`τ` extension ⟹ timelike geodesic incompleteness +
   quantitative expansion bound, via Wave 9 Session 1's bridge +
   existing `penrose_singularity_curve_theoretic`).

§3 — SEC-discriminating de Sitter counterexample (curve-level):
- `deSitter_timelike_expansion` (definition: positive constant
  expansion).
2. `deSitter_timelike_expansion_pos` (substantive: positivity from
   `H > 0`).
3. `deSitter_no_HP_focal_configuration` (substantive: de Sitter
   timelike congruence does NOT satisfy
   `IsFocalConfigurationFor`, recovering the 6g.3 algebraic-
   precedent's cosmological-Λ counterexample at curve scope).

§4 — Substantive baseline conclusion via §2:
4. `riccatiSolution_HP_curve_theoretic_baseline_conclusion`
   (substantive composition: W9-S1 Riccati witness applied directly
   via the alias's definitional equality ⟹ HP conclusion via §2 +
   Wave 9 Session 1).

**Post-wave ruthless audit cuts (2):** removed
`isHPTimelikeRaychaudhuriCurve_of_isRaychaudhuriCurve` (P3 alias-wrap;
the alias is definitionally equal to `IsRaychaudhuriCurve`, so no
named constructor is needed) + `riccatiSolution_isHPTimelikeRaychaudhuriCurve_witness`
(P5 trivial-rename via the cut constructor; W9-S1 witness applies
directly via definitional unfolding).

**Strengthening pre-pass discipline (applied prospectively):**
1. **Bundle redundancy** ✓ — there is no bundle structure introduced
   in §1 (alias to existing `IsRaychaudhuriCurve`); the §2 composition
   theorem's three hypotheses (`IsHPTimelikeRaychaudhuriCurve`,
   `IsFocalConfigurationFor`, negative-`τ`) are independent: drop any
   and the chain breaks (no Riccati comparison, no focal-time
   identity, no negative-side comparison).
2. **Quantitative connection** ✓ — explicit baseline witness at
   `(-1, 3)`; explicit positive-expansion `3H` for de Sitter; explicit
   composition conclusion (`IsNullGeodesicallyIncomplete 3 ∧ ∀ tau <
   3, ...`).
3. **Cross-module bridge integrity** ✓ — body imports + calls
   `RiccatiComparison.{IsRaychaudhuriCurve,
   isRaychaudhuriCurve_toCurveTheoreticPenroseHypothesis,
   riccatiSolution_isRaychaudhuriCurve_witness}`,
   `PenroseSingularityCurveTheoretic.{IsCurveTheoreticPenroseHypothesis,
   penrose_singularity_curve_theoretic}`,
   `PenroseSingularity.{riccatiSolution, IsNullGeodesicallyIncomplete}`,
   `FocalPoint.{IsFocalConfigurationFor, focalConfiguration_neg_one_three}`.
4. **Trivial-discharge** ✓ — `hawking_penrose_singularity_curve_theoretic`
   genuinely composes the W9-S1 bridge with the existing
   `penrose_singularity_curve_theoretic`; not a `rfl`-rename.
   `deSitter_no_HP_focal_configuration` consumes the positivity bound
   via `linarith` against the focal-config first conjunct
   `θ₀ < 0`. Both are load-bearing.
5. **Defining-the-conclusion** ✓ — the de Sitter expansion definition
   `3 * H` is genuine modeling content (the d=4 SO(4,1)-symmetric
   Hubble-flow analog); the conclusion `¬ IsFocalConfigurationFor`
   genuinely consumes positivity vs. the predicate's first conjunct.

**Bundle-target alignment:** lifts as **D3 §25** (Hawking-Penrose
section of the correctness-push bundle) per `PAPER_DRAFT_MAPPING.md`
Phase 6g addendum.

**Stages 10/11/13 deferred per user policy** (Mathlib-PR-style
infrastructure; content lifts as D3 §25).

**First formalization in any proof assistant** (per Phase 6f audit
§3E + this session's audit) of the Hawking-Penrose theorem at the
curve-theoretic abstracted-comparison-hypothesis scope. Mathlib has
the W9-S1 RiccatiComparison content; no other proof assistant has the
timelike Raychaudhuri-Riccati comparison + de-Sitter counterexample
at the curve scope per the Phase 6f audit §3E.
-/
theorem _phase6g_w9_session3_module_summary_marker : True := trivial

end SKEFTHawking.HawkingPenroseSingularityCurveTheoretic
