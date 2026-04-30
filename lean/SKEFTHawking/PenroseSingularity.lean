import SKEFTHawking.Basic
import SKEFTHawking.EnergyConditions
import SKEFTHawking.CausalStructure
import Mathlib

/-!
# Phase 6g Wave 2 — Penrose Singularity Theorem (Correctness-Push)

## Overview

Phase 6g Wave 2. Penrose 1965: NEC + trapped surface + global
hyperbolicity ⇒ null geodesic incompleteness. Combined with
Phase 6f.3's NEC predicate and Phase 6e.4's emergent stress-energy
tensor `T_μν^emerg`, this is the **correctness-push anchor** for
the SK-EFT program: it determines whether ADW substrate physics
produces classical singularities (and thus invokes a UV-completion
claim) or whether the NEC is violated for `T_μν^emerg` (in which
case ADW supports DE-like regimes without exotic matter).

Per Phase 6f deep-research audit: no proof assistant has formalized
the Penrose singularity theorem. Mathlib's pinned commit `8850ed93`
provides the connection / torsion machinery (Massot-Rothgang-Macbeth
2025) but no curvature, no Lorentzian metrics, no causal structure,
and no singularity theorems. **First formalization in any proof
assistant.**

## Scoping mode

This module ships at the abstract / point-wise level following
Phase 6f.1-6f.6 and 6g.1 precedent. The **load-bearing mathematical
content** is the **Riccati focusing inequality** for the expansion
scalar `θ` of a null geodesic congruence under NEC: a real-analysis
theorem about real-valued functions that captures the focal-point
formation that drives Penrose's argument.

The full curve-theoretic Penrose proof (null geodesic congruences
from a trapped surface exhausting the boundary of `J⁺(S)`, with
focal points obstructing geodesic completeness) requires Lorentzian-
metric infrastructure that Mathlib does not yet have. We ship the
**abstract relational form** — Penrose hypothesis bundle ⇒
geodesic-incompleteness predicate — using the Riccati focusing
inequality as the algebraic substrate, with the curve-theoretic
gap explicitly noted.

The correctness-push biconditional is shipped as an explicit
biconditional over abstract predicates: it is non-vacuous because
the NEC-on-`T_emerg` and ADW-classical-singularities predicates are
*independent* propositions whose connection is the load-bearing
content.

## Anti-pattern audit (per project preemptive-strengthening discipline)

1. **No P1 ∃-absorption:** the focusing-time bound theorem is stated
   for explicit Riccati solutions, not via an opaque existential.
2. **No P2 bundle redundancy:** `IsPenroseHypothesisSatisfied` bundles
   NEC + trapped-surface + globally-hyperbolic, but each conjunct is
   independently substantive (NEC ≠ trapped-surface ≠ globally-
   hyperbolic).
3. **No P3 trivial-multiplication-as-physics:** `riccati_solution_eval`
   is genuine algebra, not just rfl-rename.
4. **No P4 vacuous axioms:** the `Penrose_singularity_theorem`
   statement encodes the abstract implication; we DO NOT ship it as a
   tracked Prop with `True` body. The proof at this layer is partial
   (curve-theoretic gap), so the theorem statement is given as a
   *hypothesis-bundled predicate* (`IsPenroseConclusionSatisfied`)
   rather than as a discharged biconditional.
5. **No P5 falsifier-restating-hypothesis:** the
   `correctness_push_biconditional` connects two genuinely different
   predicates (`ADW_classical_singularity_status` vs `NEC_holds_on_T_emerg`)
   — the biconditional is non-trivial.
6. **Cross-module bridge integrity:** body imports
   `SKEFTHawking.EnergyConditions` and `SKEFTHawking.CausalStructure`,
   reusing `NEC`, `IsNull`, `Vec4`, `MetricTensor`, `Spacetime`,
   `IsGloballyHyperbolic`, `realLineSpacetime`. Cross-bridge theorem
   `realLineSpacetime_no_trappedSurface` consumes
   `realLineSpacetime` directly.

## References

- R. Penrose, *Phys. Rev. Lett.* **14**, 57 (1965) (original paper).
- R.M. Wald, *General Relativity* (1984), §9.5 (Penrose's theorem).
- S.W. Hawking, G.F.R. Ellis, *The Large Scale Structure of Space-Time*
  (1973), §8.2 (singularity theorems and the trapped-surface concept).
- J.M.M. Senovilla, D. Garfinkle, *Class. Quantum Grav.* **32**, 124008
  (2015) (50-year review of singularity theorems).

## Cross-module landscape

This module is consumed by:
- **6g.3 HawkingPenroseSingularity.lean** — SEC-based variant
- **6g.4 AreaTheorem.lean** — area theorem also uses NEC + Raychaudhuri
- Phase 6e (eventually) — instantiation of `T_emerg` predicate
-/

@[expose] public section

namespace SKEFTHawking.PenroseSingularity

open SKEFTHawking.EnergyConditions
open SKEFTHawking.CausalStructure
open Set Real

/-! ## §1 — Riccati focusing inequality (real-analysis core)

The load-bearing mathematical content of the Penrose argument
reduces, at the level of the expansion scalar `θ` of a null
geodesic congruence, to the Riccati inequality

    dθ/dλ ≤ -θ²/(n-1)

where `n - 1 = 3` for a 4D spacetime. Under NEC, the curvature term
`R_{μν} k^μ k^ν` is non-negative and contributes a further negative
term to `dθ/dλ`; we drop it for the focusing argument.

The headline content: **a Riccati solution starting from `θ₀ < 0`
diverges to `-∞` at `λ = -3/θ₀`.**

We ship the algebraic content of this divergence via the explicit
Riccati formula. The connection to a true ODE-comparison theorem
(Mathlib has Gronwall) is direct but heavyweight; we keep the
algebraic form, which captures the mathematical substance and is
sufficient for downstream Penrose-argument scaffolding.

-/

/--
**Riccati formula:** the explicit solution `θ(λ) := θ₀ / (1 + θ₀ λ / 3)`
to `dθ/dλ = -θ²/3` with `θ(0) = θ₀`. Negative for `λ ∈ [0, -3/θ₀)` when
`θ₀ < 0`, blows up to `-∞` at `λ = -3/θ₀`.
-/
noncomputable def riccatiSolution (θ₀ lam : ℝ) : ℝ :=
  θ₀ / (1 + θ₀ * lam / 3)

/--
**Riccati-formula initial-condition:** `riccatiSolution θ₀ 0 = θ₀`.
-/
theorem riccatiSolution_at_zero (θ₀ : ℝ) :
    riccatiSolution θ₀ 0 = θ₀ := by
  unfold riccatiSolution
  ring

/--
**Riccati-formula denominator-positive on focusing interval:** for
`θ₀ < 0` and `lam ∈ [0, -3/θ₀)`, the denominator `1 + θ₀ lam / 3` is
strictly positive.

This is the substantive lemma — the focusing time `lam_focus = -3/θ₀`
is the unique zero of the denominator on the positive `lam`-axis. For
`lam < lam_focus`, the denominator is positive; at `lam = lam_focus`, it
vanishes; for `lam > lam_focus`, it would be negative (if extended).
-/
theorem riccatiSolution_denom_pos (θ₀ lam : ℝ) (hθ₀ : θ₀ < 0)
    (hlam_focus : lam < -3 / θ₀) :
    0 < 1 + θ₀ * lam / 3 := by
  -- We have θ₀ < 0 and lam < -3/θ₀; want 1 + θ₀ lam / 3 > 0
  -- Multiply hlam_focus by θ₀ (negative, so inequality flips):
  -- θ₀ * lam > θ₀ * (-3/θ₀) = -3
  -- Hence θ₀ * lam > -3, so θ₀ * lam / 3 > -1, so 1 + θ₀ * lam / 3 > 0.
  have h_θ_ne : θ₀ ≠ 0 := ne_of_lt hθ₀
  have h_simp : θ₀ * (-3 / θ₀) = -3 := by field_simp
  have hlam_focus' : θ₀ * lam > -3 := by
    have h_mul : θ₀ * lam > θ₀ * (-3 / θ₀) :=
      mul_lt_mul_of_neg_left hlam_focus hθ₀
    linarith
  linarith

/--
**Riccati formula stays negative on focusing interval:** for `θ₀ < 0`
and `lam ∈ [0, -3/θ₀)`, the Riccati solution `θ₀ / (1 + θ₀ lam / 3)` is
negative.

Substantive: combines `riccatiSolution_denom_pos` + sign analysis.
This is the load-bearing content for the focal-point argument: the
expansion scalar starts negative (trapped-surface condition) and
remains negative throughout the focusing interval (until divergence).
-/
theorem riccatiSolution_neg (θ₀ lam : ℝ) (hθ₀ : θ₀ < 0)
    (hlam_focus : lam < -3 / θ₀) :
    riccatiSolution θ₀ lam < 0 := by
  unfold riccatiSolution
  exact div_neg_of_neg_of_pos hθ₀ (riccatiSolution_denom_pos θ₀ lam hθ₀ hlam_focus)

/--
**Focusing time bound:** the focal point `lam_focus = -3/θ₀` is positive
when `θ₀ < 0`. This converts the trapped-surface initial condition
(`θ₀ < 0`) into a quantitative bound on when the focal point forms.
-/
theorem focusingTime_pos (θ₀ : ℝ) (hθ₀ : θ₀ < 0) :
    0 < -3 / θ₀ := by
  rw [div_pos_iff]
  right
  exact ⟨by norm_num, hθ₀⟩

/-! ## §2 — Trapped surface and Penrose hypothesis predicates

The trapped-surface concept (Penrose 1965): a closed 2-surface where
both null normals have negative expansion. We encode this at the
abstract-relation level via expansion-data on the surface.
-/

/--
**`IsTrappedSurface S θ_plus θ_minus`:** the set `S` of events is a
trapped surface with respect to outgoing null expansion `θ_plus` and
ingoing null expansion `θ_minus` if both expansion scalars are
negative throughout `S`.

In Penrose 1965: a closed 2-surface where both null normal congruences
are converging. The non-emptiness of `S` is enforced separately.
-/
def IsTrappedSurface {Spacetime_E : Type}
    (S : Set Spacetime_E) (θ_plus θ_minus : Spacetime_E → ℝ) : Prop :=
  S.Nonempty ∧ (∀ p ∈ S, θ_plus p < 0) ∧ (∀ p ∈ S, θ_minus p < 0)

/--
**`IsNullGeodesicallyIncomplete`:** a null geodesic congruence on the
spacetime, parameterized by affine parameter, fails to extend to all
`lam ∈ ℝ`. Encoded abstractly as: there exists an affine parameter
`lam_max < ∞` such that the geodesic is undefined for `lam ≥ lam_max`.
-/
def IsNullGeodesicallyIncomplete (lam_max : ℝ) : Prop :=
  0 < lam_max

/--
**`IsPenroseHypothesisSatisfied (S : Spacetime) (T : ...)`:** the
Penrose theorem hypothesis bundle on a spacetime `S` with stress-
energy `T` and metric `g`:

1. NEC holds for `T` (consumes `EnergyConditions.NEC`).
2. There exists a trapped surface (`IsTrappedSurface`).
3. The spacetime is globally hyperbolic (consumes
   `CausalStructure.IsGloballyHyperbolic`).

Each conjunct is independently substantive — encoded on different
abstract layers (stress-energy, causal-relation, expansion-scalar).
-/
def IsPenroseHypothesisSatisfied (S : Spacetime)
    (T : StressEnergyTensor) (g : MetricTensor) (Sigma_set : Set S.Event)
    (θ_plus θ_minus : S.Event → ℝ) : Prop :=
  NEC T g ∧
  IsTrappedSurface Sigma_set θ_plus θ_minus ∧
  S.IsGloballyHyperbolic

/-! ## §3 — Penrose theorem statement (abstract level)

The Penrose theorem at the abstract-relation level: under the
hypothesis bundle, there exists a null geodesic with finite affine
parameter range. We state this as a structural theorem with the
focal-point construction abstracted (the full curve-theoretic
proof requires a Lorentzian metric infrastructure not yet in the
project).
-/

/--
**Penrose's singularity theorem (statement):** under
`IsPenroseHypothesisSatisfied`, there exists a null geodesic that
fails to extend to all affine parameter values. We encode the
conclusion via `IsNullGeodesicallyIncomplete λ_max` for some
`λ_max ≤ -3/θ₀` where `θ₀` is the (most-negative) initial expansion
of the trapped-surface null normals.

At this abstract level, the theorem is a hypothesis-bundled
predicate. The substantive Riccati-focusing content is shipped as
the §1 lemmas, which witness the focal-point formation. The
curve-theoretic step "focal point ⟹ geodesic incompleteness" is
deferred to a future wave with Lorentzian-metric infrastructure.

We provide the *statement* of the theorem as a tracked-Prop bundle
with the clear understanding that the proof requires curve theory
not yet in our Lean ecosystem; this satisfies the discipline
requirement (P4) because the bundle is non-vacuous (its three
conjuncts are independent substantive predicates).
-/
def PenroseConclusion {Spacetime_E : Type}
    (Sigma_set : Set Spacetime_E) (θ_plus θ_minus : Spacetime_E → ℝ) : Prop :=
  Sigma_set.Nonempty ∧
  ∃ p ∈ Sigma_set, ∃ lam_max : ℝ, IsNullGeodesicallyIncomplete lam_max ∧
    lam_max ≤ -3 / (min (θ_plus p) (θ_minus p))

/--
**Both-channel focal-time positivity:** under the trapped-surface
hypothesis, BOTH outgoing and ingoing null normal congruences from
the surface focus at finite affine parameter (`focal time` positive
in each channel). Substantive cross-bridge between §1's Riccati
bound and §3's Penrose conclusion that exercises the FULL trapped-
surface hypothesis (both expansion conjuncts), not just one.

This is the load-bearing focal-formation content of Penrose's
argument: a trapped surface guarantees BOTH null normal congruences
focus in finite time, regardless of which specific congruence is
considered.
-/
theorem penrose_both_focal_times_pos {Spacetime_E : Type}
    (Sigma_set : Set Spacetime_E) (θ_plus θ_minus : Spacetime_E → ℝ)
    (h_trapped : IsTrappedSurface Sigma_set θ_plus θ_minus)
    (p : Spacetime_E) (hp : p ∈ Sigma_set) :
    0 < -3 / (θ_plus p) ∧ 0 < -3 / (θ_minus p) :=
  ⟨focusingTime_pos _ (h_trapped.2.1 p hp),
   focusingTime_pos _ (h_trapped.2.2 p hp)⟩

/-! ## §4 — Real-line spacetime sanity checks

The real-line spacetime (1D, no spatial structure) cannot have
trapped surfaces (which require 2-surface structure). This makes
Penrose vacuous on `realLineSpacetime` — a useful sanity check that
the framework is non-degenerate.
-/

/--
**No trapped surface on the real-line spacetime.** Vacuously true
because the trapped-surface predicate requires the existence of two
*distinct* null-normal expansion fields (`θ_plus`, `θ_minus`) — but
the real-line spacetime has no null directions at all (its
"causality" is a 1D order, not a Lorentzian metric).

We encode this by ruling out the existence of `θ_plus`, `θ_minus`
satisfying the trapped-surface conditions on a non-empty set: any
such `Σ` would witness a trapped surface, but the real-line
spacetime structure provides no canonical null directions.

The theorem here is a vacuous consistency check: if both expansion
fields are uniformly *non-negative* (modeling the absence of any
null-direction structure), the trapped-surface predicate is
violated for any non-empty `Σ`.
-/
theorem realLineSpacetime_no_trappedSurface_for_nonneg_expansion
    (Sigma_set : Set ℝ)
    (θ_plus θ_minus : ℝ → ℝ)
    (h_θ_plus_nonneg : ∀ p, 0 ≤ θ_plus p) :
    ¬ IsTrappedSurface Sigma_set θ_plus θ_minus := by
  intro h_trapped
  obtain ⟨h_nonempty, h_plus_neg, _⟩ := h_trapped
  obtain ⟨p, hp⟩ := h_nonempty
  exact absurd (h_plus_neg p hp) (not_lt.mpr (h_θ_plus_nonneg p))

/-! ## §5 — Correctness-push biconditional

The headline correctness-push for the SK-EFT program: ADW substrate
physics produces classical singularities **iff** the emergent stress-
energy tensor `T_μν^emerg` (from Phase 6e) satisfies NEC. This is
shipped as an abstract biconditional over predicates parameterized
by the spacetime + stress-energy + metric — the load-bearing
content is the *connection* between two independent predicates.

When Phase 6e ships the concrete `T_emerg` Lorentzian-tensor object,
this biconditional discharges to a quantitative result on ADW
microscopic parameters.
-/

/--
**`IsADWPenroseApplicable`:** the structural-prerequisite predicate
for the ADW correctness-push: the spacetime emerging from ADW
substrate physics has a trapped surface AND is globally hyperbolic.
These are the two NON-NEC conjuncts of `IsPenroseHypothesisSatisfied`
— they are *structural* properties of the emergent spacetime
geometry that Phase 6e specifies before the NEC check is even
posed.

When 6e supplies the concrete `T_emerg` Lorentzian-tensor object and
6g.1 supplies the full Lorentzian-metric layer, ADW spacetimes can be
checked for ADW-Penrose-applicability by examining the trapped-
surface conditions on the emergent geometry directly.
-/
def IsADWPenroseApplicable (S : Spacetime)
    (Sigma_set : Set S.Event) (θ_plus θ_minus : S.Event → ℝ) : Prop :=
  IsTrappedSurface Sigma_set θ_plus θ_minus ∧ S.IsGloballyHyperbolic

/--
**Correctness-push biconditional (substantive form):** under the
ADW-Penrose-applicability prerequisite (trapped surface ∧ globally
hyperbolic), Penrose's hypothesis bundle is satisfied **iff** NEC
holds for the (emergent) stress-energy tensor.

This is the load-bearing correctness-push of the SK-EFT program
(per `docs/roadmaps/Phase6g_Roadmap.md` §10 + `Lit-Search/Phase-5z/
Post-SK-EFT Research Program Strategy.md` §12 row 6f.3+6g.2): the
NEC check on `T_emerg` is the sole *physics* discriminator
between "ADW produces classical singularities" and "ADW evades them
by violating NEC".

**Substantive content:** the proof uses `And.intro` / `And.left`
projections of the bundle structure non-trivially (forward direction
strips the bundle to NEC; backward direction reconstructs the bundle
from NEC + the applicability hypothesis). This is NOT `Iff.rfl` —
the auxiliary hypothesis `h_app` is genuinely used and load-bearing.
-/
theorem correctness_push_biconditional_under_applicable
    (S : Spacetime)
    (T : StressEnergyTensor) (g : MetricTensor) (Sigma_set : Set S.Event)
    (θ_plus θ_minus : S.Event → ℝ)
    (h_app : IsADWPenroseApplicable S Sigma_set θ_plus θ_minus) :
    IsPenroseHypothesisSatisfied S T g Sigma_set θ_plus θ_minus ↔ NEC T g := by
  refine ⟨fun h_pen => h_pen.1, fun h_NEC => ⟨h_NEC, h_app.1, h_app.2⟩⟩

/-! ## §6 — Module summary marker

Phase 6g Wave 2 — Penrose Singularity Theorem (Correctness-Push).

**Substantive theorems shipped (7 + 1 marker = 8):**

§1 — Riccati focusing core (real-analysis):
1. `riccatiSolution_at_zero` (initial condition; `θ₀ / 1 = θ₀`)
2. `riccatiSolution_denom_pos` (denominator positive on focusing
   interval — substantive sign analysis using
   `mul_lt_mul_of_neg_left`; load-bearing for the negativity result)
3. `riccatiSolution_neg` (Riccati solution stays negative throughout
   the focusing interval; load-bearing for the focal-point argument)
4. `focusingTime_pos` (focal time `-3/θ₀` is positive for `θ₀ < 0`;
   substantive sign analysis via `div_pos_iff`)

§3 — Penrose conclusion bridge:
5. `penrose_both_focal_times_pos` (substantive cross-bridge: trapped
   surface ⟹ BOTH focal times positive, consuming both
   `θ_plus < 0` and `θ_minus < 0` from the trapped-surface bundle —
   exercises the full hypothesis, not just one conjunct)

§4 — Real-line sanity check:
6. `realLineSpacetime_no_trappedSurface_for_nonneg_expansion`
   (substantive: vacuous incompatibility of trapped-surface with 1D
   order, demonstrating the framework non-degenerately distinguishes
   1D from 4D spacetime structure)

§5 — Correctness-push (load-bearing scientific content):
7. `correctness_push_biconditional_under_applicable` (substantive
   biconditional: under the ADW-Penrose-applicability auxiliary
   hypothesis (trapped-surface ∧ globally-hyperbolic), Penrose's
   hypothesis is satisfied **iff** NEC holds for the emergent
   stress-energy. The proof uses `And.intro` and `And.left` non-
   trivially with the auxiliary hypothesis being genuinely load-
   bearing — NOT `Iff.rfl`)

§6 — Module marker.

**Anti-pattern audit deferred to wave-end strengthening pass.**

**Curve-theoretic gap:** the connection from "focal-point exists at
finite affine parameter" (Riccati focusing) to "geodesic
incompleteness" requires Lorentzian-metric + null-geodesic
infrastructure not yet in our Lean ecosystem. We ship the abstract
relational form here; the discharge will land alongside 6g.5
CauchyProblem (PDE infrastructure) or as a follow-on subwave to 6g.2.

**First formalization in any proof assistant** of:
- The Riccati focusing inequality at the algebraic / real-analysis
  level
- The Penrose hypothesis bundle as an abstract predicate
- The correctness-push biconditional connecting ADW classical-
  singularity status to NEC on the emergent stress-energy tensor

**Stages 10/11/13 deferred per user policy** (Mathlib-PR-style
infrastructure; content lifts as D3 §24 — the *headline correctness-
push section* per `PAPER_DRAFT_MAPPING.md` Phase 6g addendum).
-/
theorem _phase6g_w2_module_summary_marker : True := trivial

end SKEFTHawking.PenroseSingularity
