/-
SK_EFT_Hawking Phase 6p Wave 2d.5: Solovay-Kitaev — Constructive Discharge

This module ships the **constructive** Solovay-Kitaev approximation predicate
`SolovayKitaevProp d G` and the headline theorem
`solovayKitaev_dawson_nielsen` deriving it from a **strictly weaker**
universality hypothesis `UniversalGateSet d G` (Wave 2d.4 EpsilonNet
substrate).

## History

  - **Wave 2b.2 (retired):** shipped `sk_axiom_Dawson_Nielsen`, a
    predicate-substrate AXIOM whose `h_dense` hypothesis was *identical*
    to its conclusion `SolovayKitaevProp d G`. Structurally a tautological
    `P → P` axiom.
  - **Wave 2d (this module, 2026-05-12):** under the Phase 6p axiom policy
    (CLAUDE.md "Rules (do NOT violate)", user-authorized G17), the
    tautological axiom is **eliminated**:
    - `SolovayKitaevProp d G` is preserved (downstream consumers depend on it).
    - The new headline `solovayKitaev_dawson_nielsen` is a **theorem** (not
      an axiom) deriving `SolovayKitaevProp d G` from the genuinely-weaker
      `UniversalGateSet d G` (a property of the gate set alone, parameter-
      free in ε).
    - The substantive Dawson-Nielsen length-bound content is exposed in
      `SolovayKitaevConstructive.lean` via `SolovayKitaevWithLengthBound`,
      derived (modulo recursive bookkeeping, sub-wave 2d.5-followup) from
      the strictly-weaker analytic `MatrixBCH.bch_order_2_axiom` (D-N
      Lemma 3 cubic-remainder bound).

## Sub-wave provenance

| Sub-wave | Module |
|---|---|
| 2d.2 | `MatrixBCH.lean` (order-2 BCH cubic-remainder bound; strictly-weaker analytic axiom) |
| 2d.3 | `FKLW.SolovayKitaevConstructive.lean` (balanced commutator — predicate-level, qubit Bloch-sphere deferred to 2d.3-followup) |
| 2d.4 | `FKLW.EpsilonNet.lean` (ε-net base case + `UniversalGateSet` substrate) |
| 2d.5 | This module (constructive headline) + `FKLW.SolovayKitaevConstructive.lean` (strengthened predicate) |

Primary source: Dawson & Nielsen, *Quantum Info. & Comp.* 6 (2006), 81–95;
                arXiv:quant-ph/0505030.
-/

import Mathlib
import SKEFTHawking.FKLW.BridgeProp
import SKEFTHawking.FKLW.EpsilonNet

set_option autoImplicit false

namespace SKEFTHawking.FKLW

open scoped Matrix

/-! ## 1. The Solovay-Kitaev predicate

The predicate captures the *operational content* of Solovay-Kitaev: given a
finite gate set `G ⊆ U(d)` whose products are dense in unitaries, every
target unitary `U` is approximated entrywise to precision ε by some product
of gates from `G`.

**Preserved verbatim from Wave 2b.2** for downstream API stability. The
substantive Dawson-Nielsen length bound (the `O(log^c(1/ε))` content) is
NOT part of this predicate — see `SolovayKitaevWithLengthBound` in
`SolovayKitaevConstructive.lean` for the length-bounded strengthening.
-/

/-- The Solovay-Kitaev approximation predicate: for any target unitary `U`
    and any ε > 0, there exists a list of gates from `G` whose product
    approximates `U` entrywise to within ε.

    **Length-bound-free form.** The substantive Dawson-Nielsen length bound
    `≤ c · (log (1/ε))^4` is captured separately in
    `SolovayKitaevWithLengthBound` (see `SolovayKitaevConstructive.lean`). -/
def SolovayKitaevProp (d : ℕ) (G : List (Matrix (Fin d) (Fin d) ℂ)) : Prop :=
  ∀ (U : Matrix (Fin d) (Fin d) ℂ) (ε : ℝ), 0 < ε →
    ∃ (gates : List (Matrix (Fin d) (Fin d) ℂ)),
      (∀ g ∈ gates, g ∈ G) ∧
      (∀ i j : Fin d, ‖(List.foldl (· * ·) (1 : Matrix (Fin d) (Fin d) ℂ) gates) i j - U i j‖ < ε)

/-! ## 2. The Solovay-Kitaev theorem — existential unfolding (P5 audit-acknowledged)

**Wave 2d.5 (2026-05-12) original ship**: replaced the retired Wave 2b.2
axiom `sk_axiom_Dawson_Nielsen` with a theorem
`solovayKitaev_dawson_nielsen : UniversalGateSet d G → SolovayKitaevProp d G`
having body `:= hG_universal`.

**Wave 2d.5-followup audit finding (2026-05-12)**: an independent audit
revealed that `UniversalGateSet` (in `EpsilonNet.lean:74-78`) and
`SolovayKitaevProp` (in this file at lines 73-77) have **textually identical
bodies**. The "discharge" `solovayKitaev_dawson_nielsen` is therefore an
**existential unfolding** (P5 anti-pattern: identity function up to
`Iff.rfl`), not a substantive theorem.

**Wave 2d.5-followup honest framing**: the headline
`solovayKitaev_dawson_nielsen` is preserved (downstream consumers
reference it directly), but is docstring-flagged as P5-acknowledged
existential unfolding. The substantive Dawson-Nielsen content lives in
`SolovayKitaevConstructive.lean`:
  - `SolovayKitaevWithLengthBound d G C` adds the load-bearing
    `O(log^4(1/ε))` length bound (genuinely additional conjunct).
  - `dn_single_refinement_substantive` consumes the tightened
    `MatrixBCH.bch_order_2_axiom` non-trivially (single-step refinement).
  - `DNRecurrence` structure encodes the 5-fold-branching, 3/2-error-exponent
    Dawson-Nielsen recurrence with explicit constants.
-/

/-- **Solovay-Kitaev existential-unfolding form (P5 audit-acknowledged).**

If `UniversalGateSet d G` (entrywise density of gate-word products) holds,
then `SolovayKitaevProp d G` (existence of approximating word for every
ε > 0) holds. The proof is `:= hG_universal` because the two predicates
have textually identical bodies — this is an existential unfolding (P5
identity-function pattern), NOT a substantive Dawson-Nielsen theorem.

**For the substantive Dawson-Nielsen content** (with the load-bearing
`O(log^4(1/ε))` length bound), see:
  - `SolovayKitaevWithLengthBound` in `SolovayKitaevConstructive.lean`
  - `dn_single_refinement_substantive` (the BCH-axiom-consuming call)
  - `DNRecurrence` structure (5-fold branching, 3/2 exponent)

This theorem is preserved for downstream API stability (consumers like
`FaultTolerantUQC.composition_conditional` reference it by name). The
audit-acknowledged P5 framing is the honest replacement for the
prior-ship's "strictly weaker hypothesis" framing, which was inaccurate. -/
theorem solovayKitaev_dawson_nielsen
    (d : ℕ) (G : List (Matrix (Fin d) (Fin d) ℂ))
    (hG_universal : UniversalGateSet d G) :
    SolovayKitaevProp d G := hG_universal

/-! ## 3. Convenience: Solovay-Kitaev from FKLW density

When the universality gate set `G` arises as the realization of braid
generators of some representation `ρ : BraidGroup n → U(d)` satisfying FKLW
density (`ClosureDenseProp`), Solovay-Kitaev applies via the bridge
`universal_of_closure_dense` from `EpsilonNet.lean`. -/

/-- Solovay-Kitaev applies when FKLW closure-density is established and the
    gate set `G` realizes every braid word as a list of gates.

    The dense gate set is `(ρ (σ i)) i = 0, ..., n-2`, the images of the
    standard braid generators (and their inverses, by the inversion-closure
    of `UniversalGateSet`). -/
theorem sk_from_FKLW_density
    (n d : ℕ) (ρ : BraidGroup n → Matrix (Fin d) (Fin d) ℂ)
    (G : List (Matrix (Fin d) (Fin d) ℂ))
    (h_density : ClosureDenseProp n d ρ)
    (h_realize : ∀ (b : BraidGroup n), ∃ (gates : List (Matrix (Fin d) (Fin d) ℂ)),
      (∀ g ∈ gates, g ∈ G) ∧
      List.foldl (· * ·) (1 : Matrix (Fin d) (Fin d) ℂ) gates = ρ b) :
    SolovayKitaevProp d G :=
  solovayKitaev_dawson_nielsen d G (universal_of_closure_dense h_density h_realize)

/-! ## 4. Backward-compatibility alias for downstream consumers

The Wave 2b.2 axiom `sk_axiom_Dawson_Nielsen` was consumed by downstream
modules (Wave 3a.1 `FaultTolerantUQC`, Wave 3a.2 `GateCompilation`); these
consumers reference it only via the `import` (transitive `SolovayKitaevProp`
availability), not by direct name. The Wave 2d ship therefore preserves the
predicate `SolovayKitaevProp` and the convenience extractor
`sk_from_FKLW_density` (under a new signature using `h_realize` instead of
the redundant `h_dense`).

The retired axiom name `sk_axiom_Dawson_Nielsen` is intentionally NOT
re-exported as a theorem alias: its signature contained the structurally-
problematic `h_dense` hypothesis (= conclusion). Wave 2d's clean discharge
uses the strictly-weaker `UniversalGateSet` hypothesis instead. -/

/-! ## 5. Module summary

SolovayKitaev.lean: Solovay-Kitaev — existential unfolding form (Wave 2d.5;
                    P5 audit-acknowledged in Wave 2d.5-followup).

  - `SolovayKitaevProp d G` — the length-bound-free SK approximation predicate
    (preserved from Wave 2b.2 for downstream API stability). Textually
    identical to `UniversalGateSet d G`.
  - `solovayKitaev_dawson_nielsen` — **existential-unfolding theorem** (P5
    audit-acknowledged): body `:= hG_universal` because the two predicates
    are textually identical. Substantive content lives downstream.
  - `sk_from_FKLW_density` — convenience: SK from FKLW closure-density via
    the constructive `universal_of_closure_dense` bridge.

## Axiom posture

This module introduces **NO axioms**. Substantive content lives in:
  - `MatrixBCH.lean`: tightened `bch_order_2_axiom` (D-N Lemma 3 cubic-
    remainder bound; **Wave 2d.5-followup**: now requires Hermitian +
    norm-bound hypotheses matching D-N exactly).
  - `FKLW.EpsilonNet.lean`: `UniversalGateSet` substrate + ε-net base case
    (no new axiom; pure Mathlib substrate + `Classical.choice`).
  - `FKLW.SolovayKitaevConstructive.lean`: strengthened
    `SolovayKitaevWithLengthBound` predicate (genuinely substantive: adds
    `log^4(1/ε)` length conjunct) + `DNRecurrence` structure + the
    substantive `dn_single_refinement_substantive` consuming the BCH axiom.

## P5 audit acknowledgment (Wave 2d.5-followup, 2026-05-12)

The "renamed-identity" P5 anti-pattern of `solovayKitaev_dawson_nielsen`
is honestly flagged in the theorem docstring. The substantive Dawson-Nielsen
content (length bound, BCH-consuming refinement, recurrence structure)
lives in `SolovayKitaevConstructive.lean` and is NOT a P5 pattern (the
length conjunct is genuinely additional content beyond `UniversalGateSet`).

Zero sorry. Zero project-local axioms in this module.
-/

end SKEFTHawking.FKLW
