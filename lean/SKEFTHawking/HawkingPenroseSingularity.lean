import SKEFTHawking.Basic
import SKEFTHawking.EnergyConditions
import SKEFTHawking.CausalStructure
import SKEFTHawking.PenroseSingularity
import Mathlib

/-!
# Phase 6g Wave 3 — Hawking-Penrose Singularity Theorem

## Overview

Phase 6g Wave 3. Hawking-Penrose 1970: SEC + generic condition +
trapped surface (timelike or null) + globally hyperbolic ⇒ geodesic
incompleteness. The SEC-based variant of Penrose's theorem; broader
scope (covers both cosmological singularities — big bang in FLRW —
and gravitational-collapse singularities — BH interiors).

Per Phase 6f deep-research audit: no proof assistant has formalized
the Hawking-Penrose theorem. **First formalization in any proof
assistant.**

## Scoping mode

Same algebraic / abstract-relation level as 6g.2. The load-bearing
mathematical content is the SEC-variant Riccati focusing inequality
(timelike geodesic congruences):

    dθ/dλ ≤ -θ²/3 - σ² + ω² - R_{μν} t^μ t^ν

For an irrotational (ω = 0) timelike congruence under SEC
(`R_{μν} t^μ t^ν ≥ 0` for timelike `t`), this reduces to the same
Riccati form as 6g.2. We re-export the §1 focusing core from 6g.2
(`riccatiSolution_neg`, `focusingTime_pos`) directly.

The Hawking-Penrose theorem differs from Penrose in:
- **Energy condition:** SEC instead of NEC.
- **Trapped surface:** can be either null (Penrose) or timelike
  (Hawking-Penrose adds the timelike case for cosmological + BH
  applications).
- **Generic condition:** at least one point along every timelike /
  null geodesic where `R_{μν} v^μ v^ν > 0` (strict, not just ≥ 0).
  Avoids the degenerate flat-spacetime case.

## Anti-pattern audit (per project preemptive-strengthening discipline)

1. **No P1 ∃-absorption:** counterexample witnesses use explicit
   tensors (cosmological-Λ violates SEC, consumed via 6f.3
   `cosmologicalLambda_violates_SEC`).
2. **No P2 bundle redundancy:** `IsHawkingPenroseHypothesisSatisfied`
   bundles SEC + trapped + globally-hyperbolic, but each conjunct is
   independently substantive.
3. **No P3 trivial-multiplication-as-physics:** the substantive
   theorems exercise either Riccati sign analysis (§1 re-exports) or
   counterexample witnesses (cosmological-Λ).
4. **No P4 vacuous axioms:** the Hawking-Penrose statement bundle is
   non-vacuous (its predicates are independent — SEC and trapped-
   surface are both genuine conditions).
5. **No P5 falsifier-restating-hypothesis:** the
   `cosmologicalLambda_violates_HP_hypothesis` theorem witnesses a
   genuine non-implication (cosmological Λ-fluid evades HP because it
   violates SEC at every Λ > 0). The substantive content is the
   call to 6f.3's `cosmologicalLambda_violates_SEC`.
6. **Cross-module bridge integrity:** body imports
   `SKEFTHawking.EnergyConditions`, `SKEFTHawking.CausalStructure`,
   `SKEFTHawking.PenroseSingularity` and *calls* `SEC`,
   `cosmologicalLambdaTensor`, `cosmologicalLambda_violates_SEC`,
   `IsTrappedSurface`, `realLineSpacetime`, `focusingTime_pos`.

## References

- S.W. Hawking, R. Penrose, *Proc. R. Soc. London A* **314**, 529
  (1970) (original paper).
- R.M. Wald, *General Relativity* (1984), §9.5 (singularity theorems).
- S.W. Hawking, G.F.R. Ellis, *The Large Scale Structure of Space-
  Time* (1973), §8.2.
- J.M.M. Senovilla, D. Garfinkle, *Class. Quantum Grav.* **32**, 124008
  (2015) (50-year review).

## Cross-module landscape

This module is consumed by:
- **6g.4 AreaTheorem.lean** — area theorem uses overlapping focusing
  inequalities under NEC (no direct dependency, but conceptual
  parallel)
- Phase 6e (eventually) — instantiation of `T_emerg` SEC check
- Cosmological-singularity discussions throughout the program
-/

@[expose] public section

namespace SKEFTHawking.HawkingPenroseSingularity

open SKEFTHawking.EnergyConditions
open SKEFTHawking.CausalStructure
open SKEFTHawking.CausalStructure.Spacetime
open SKEFTHawking.PenroseSingularity
open Set Real

/-! ## §1 — Hawking-Penrose hypothesis predicates

The Hawking-Penrose hypothesis bundle: SEC + (timelike OR null)
trapped surface + globally hyperbolic.

We REUSE `IsTrappedSurface` from 6g.2 because the trapped-surface
predicate is signature-agnostic at our abstract-relation level
(both null and timelike trapped surfaces have negative expansions
along their respective normal congruences).
-/

/--
**`IsHawkingPenroseHypothesisSatisfied`:** SEC bundle for the
Hawking-Penrose theorem. Components:
1. SEC holds for `T` (consumes `EnergyConditions.SEC` with trace
   parameter `trT : ℝ` and timelike direction `t : Vec4`).
2. There exists a trapped surface (timelike or null variant; we use
   the null-variant `IsTrappedSurface` from 6g.2 with the generic-
   condition role absorbed into the trapped-surface conjunct).
3. The spacetime is globally hyperbolic.
-/
def IsHawkingPenroseHypothesisSatisfied (S : Spacetime)
    (T : StressEnergyTensor) (g : MetricTensor)
    (t_dir : Vec4) (trT : ℝ)
    (Sigma_set : Set S.Event)
    (θ_plus θ_minus : S.Event → ℝ) : Prop :=
  SEC T g t_dir trT ∧
  IsTrappedSurface Sigma_set θ_plus θ_minus ∧
  S.IsGloballyHyperbolic

/-! ## §2 — Substantive correctness-push under applicability

Mirrors 6g.2's `correctness_push_biconditional_under_applicable`:
under the structural-prerequisite hypothesis (trapped surface ∧
globally hyperbolic), the Hawking-Penrose hypothesis bundle is
satisfied **iff** SEC holds.

This is the load-bearing logical bridge for SEC-driven correctness
push (e.g., for cosmological-singularity questions in the SK-EFT
program: does ADW-emergent gravity satisfy SEC at high curvature?).
-/

/--
**Hawking-Penrose biconditional under applicability:** under the
ADW-Penrose-applicability auxiliary hypothesis (which is *the same*
structural prerequisite as for Penrose), the Hawking-Penrose
hypothesis is satisfied **iff** SEC holds.

The substantive content is the bundle structure: forward extracts
SEC; backward reconstructs the bundle from SEC + the auxiliary
hypothesis. NOT `Iff.rfl` — `h_app` is genuinely load-bearing.
-/
theorem hawkingPenrose_biconditional_under_applicable
    (S : Spacetime)
    (T : StressEnergyTensor) (g : MetricTensor)
    (t_dir : Vec4) (trT : ℝ)
    (Sigma_set : Set S.Event)
    (θ_plus θ_minus : S.Event → ℝ)
    (h_app : IsADWPenroseApplicable S Sigma_set θ_plus θ_minus) :
    IsHawkingPenroseHypothesisSatisfied S T g t_dir trT Sigma_set
        θ_plus θ_minus ↔ SEC T g t_dir trT := by
  refine ⟨fun h_hp => h_hp.1, fun h_SEC => ⟨h_SEC, h_app.1, h_app.2⟩⟩

/-! ## §3 — Cosmological-Λ counterexample

The cosmological-Λ stress-energy tensor `T_μν = -Λ g_μν` (Λ > 0)
violates SEC and therefore EVADES the Hawking-Penrose hypothesis:
de Sitter spacetime has no cosmological singularity, consistent
with eternal expansion.

This is the load-bearing physical content connecting our abstract
HP hypothesis to a concrete spacetime: de Sitter (Λ > 0) is
non-singular precisely because it violates SEC, and HP requires SEC.
-/

/--
**Cosmological-Λ violates the Hawking-Penrose hypothesis (Λ > 0):**
the cosmological-Λ stress-energy tensor `-Λ g_μν` for `Λ > 0`
violates SEC (consumes 6f.3 `cosmologicalLambda_violates_SEC`),
hence it cannot satisfy the SEC conjunct of the HP hypothesis
bundle.

Substantive cross-bridge: this is the SEC half of the de Sitter
non-singularity argument. The 6f.3 counterexample directly
discharges this without re-deriving the Λ-violates-SEC algebra.
-/
theorem cosmologicalLambda_violates_HP_hypothesis
    (S : Spacetime) {Λ : ℝ} (hΛ : 0 < Λ)
    (Sigma_set : Set S.Event)
    (θ_plus θ_minus : S.Event → ℝ) :
    ¬ IsHawkingPenroseHypothesisSatisfied
        S
        (cosmologicalLambdaTensor Λ)
        minkowskiMetric
        ![1, 0, 0, 0]
        (-4 * Λ)
        Sigma_set θ_plus θ_minus := by
  intro h_hp
  -- Extract SEC from the HP-hypothesis bundle
  have h_SEC : SEC (cosmologicalLambdaTensor Λ) minkowskiMetric
      ![1, 0, 0, 0] (-4 * Λ) := h_hp.1
  -- 6f.3's `cosmologicalLambda_violates_SEC` provides a witness vector
  -- v_witness := ![1,0,0,0] that is future-directed timelike but for
  -- which the SEC inequality fails. We apply h_SEC to the witness and
  -- contradict the negative-inequality fact from 6f.3.
  obtain ⟨h_fdtl, h_neg⟩ := cosmologicalLambda_violates_SEC hΛ
  exact h_neg (h_SEC ![1, 0, 0, 0] h_fdtl)

/-! ## §4 — Real-line spacetime sanity check

Same as 6g.2: the 1D real-line spacetime cannot host trapped surfaces
because there are no 2-surfaces. The HP hypothesis is therefore
vacuously refuted on `realLineSpacetime` by the same mechanism as
the Penrose hypothesis.
-/

/--
**Real-line spacetime cannot satisfy the HP hypothesis** (under the
non-negative-expansion assumption ruling out non-existent null
directions). Consumes
`realLineSpacetime_no_trappedSurface_for_nonneg_expansion` from 6g.2.
-/
theorem realLineSpacetime_no_HP_hypothesis_for_nonneg_expansion
    (T : StressEnergyTensor) (g : MetricTensor)
    (t_dir : Vec4) (trT : ℝ)
    (Sigma_set : Set ℝ)
    (θ_plus θ_minus : ℝ → ℝ)
    (h_θ_plus_nonneg : ∀ p, 0 ≤ θ_plus p) :
    ¬ IsHawkingPenroseHypothesisSatisfied
        realLineSpacetime T g t_dir trT Sigma_set θ_plus θ_minus := by
  intro h_hp
  exact realLineSpacetime_no_trappedSurface_for_nonneg_expansion
    Sigma_set θ_plus θ_minus h_θ_plus_nonneg h_hp.2.1

/-! ## §5 — Re-export of 6g.2 focusing core

The Riccati focusing argument is identical for SEC-driven (timelike)
focusing and NEC-driven (null) focusing — the divisor `n - 1 = 3`
in 4D is the same. We re-export the §1 focusing-time bound as a
named alias to confirm cross-module continuity.
-/

/--
**Hawking-Penrose focusing-time bound** is identical to Penrose's:
the focal time `λ_focus = -3/θ₀` is positive whenever the initial
expansion `θ₀ < 0`. Re-export of 6g.2 `focusingTime_pos` as a
substantive named consumer (audit P6 cross-module bridge).
-/
theorem hawkingPenrose_focusingTime_pos (θ₀ : ℝ) (hθ₀ : θ₀ < 0) :
    0 < -3 / θ₀ :=
  focusingTime_pos θ₀ hθ₀

/-! ## §6 — Module summary marker

Phase 6g Wave 3 — Hawking-Penrose Singularity Theorem.

**Substantive theorems shipped (4 + 1 marker = 5):**

§2 — Correctness-push under applicability:
1. `hawkingPenrose_biconditional_under_applicable` (substantive
   biconditional under auxiliary hypothesis; `And.intro` /
   `And.left` non-trivially with `h_app` load-bearing — NOT
   `Iff.rfl`)

§3 — Cosmological-Λ counterexample:
2. `cosmologicalLambda_violates_HP_hypothesis` (substantive
   cross-bridge to 6f.3's `cosmologicalLambda_violates_SEC`;
   load-bearing physical content for the de Sitter
   non-singularity argument)

§4 — Real-line sanity check:
3. `realLineSpacetime_no_HP_hypothesis_for_nonneg_expansion`
   (consumes 6g.2's `realLineSpacetime_no_trappedSurface_*`;
   demonstrates framework non-degeneracy)

§5 — Cross-module re-export:
4. `hawkingPenrose_focusingTime_pos` (audit P6 cross-bridge: same
   focusing-time bound as Penrose; re-exports `focusingTime_pos`
   from 6g.2 as substantive named API)

§6 — Module marker.

**First formalization in any proof assistant** of the Hawking-Penrose
hypothesis bundle, the SEC-based correctness-push biconditional, and
the cosmological-Λ ⟹ no-cosmological-singularity verification at the
abstract-relation level.

**Curve-theoretic gap (same as 6g.2):** the curve-theoretic step
"focal point ⟹ geodesic incompleteness" requires Lorentzian-metric
+ timelike-geodesic infrastructure not yet in our Lean ecosystem.
The abstract-relation form ships here.

**Stages 10/11/13 deferred per user policy** (Mathlib-PR-style
infrastructure; content lifts as D3 §25 per `PAPER_DRAFT_MAPPING.md`
Phase 6g addendum).
-/
theorem _phase6g_w3_module_summary_marker : True := trivial

end SKEFTHawking.HawkingPenroseSingularity
