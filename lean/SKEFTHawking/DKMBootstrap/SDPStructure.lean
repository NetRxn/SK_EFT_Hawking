/-
# Phase 6q Wave 1c.1 — DKM Transport Bootstrap: SDP-bypass structural finding

The Phase 6o Wave 1c Obstruction (III) motivates the comparison. The Phase
6o NO-GO writeup (`temporary/working-docs/phase6o/wave_1c_NO-GO_writeup.md`
§2.3) identified the breakdown of SDP feasibility on the complex
Schwinger–Keldysh contour as the third structural obstruction. The DR
Wave 1a.1 §1 row (3) notes that CHHK 2509.18255 derives its
published transport bounds without solving an SDP. The derivation uses:
- Lehmann (spectral) representation;
- nonnegativity of `Im G^R` on nonnegative frequencies;
- the Abanin–De Roeck–Huveneers nested-commutator norm bound (CHHK v2 Eq. (31));
- the Stirling-type estimate (CHHK v2 Eq. (32));
- direct integration over the DKM Lorentzian spectral form (CHHK v2 Eq. (4));
- auxiliary estimates on the momentum integral.

CHHK §6 discusses dual S-matrix-bootstrap SDP-style optimisation as
a possible future strengthening. The Phase 6o obstruction motivates
recording the assumptions of the published analytic route.

The Lean interface aliases the legacy `IsDKMAxiomSet`, shows the
equivalence with the vertical bundle plus three supplied fields, and
reserves a universally true SDP scaffold for future work.

References:
- Phase 6o Wave 1c NO-GO §2.3: SDP feasibility breaks on complex contour
- DR Wave 1a.1 §1 row (3): CLEARED — CHHK has no SDP, purely analytic
- CHHK §§3–4: Lehmann representation + analytic spectral-weight bound
- CHHK §6: "future strengthening could use dual S-matrix-style optimization"
- Simmons-Duffin et al. SDPB arXiv:1502.02033 — the SDPB tool CHHK does
  NOT use (mentioned as the standard conformal-bootstrap SDP tool)
- Wave 2a.1 DR §5: SDP infrastructure deferred unless Wave 2b attempts
  strengthening beyond CHHK analytic bounds
-/
import SKEFTHawking.DKMBootstrap.NoCrossing

namespace SKEFTHawking.DKMBootstrap

/-! ## §1. The analytic-bootstrap predicate.

The source uses a microscopic thermal spectral bound, a DKM
description on an effective window and actual nested-commutator
estimates. The analytic-bootstrap name below labels the legacy Lean
bundle. The microscopic evidence must be supplied separately. -/

/-- Transparent alias for the legacy `IsDKMAxiomSet`. The name reflects
CHHK's analytic approach. The alias inherits the incompatible global
F1 and pointwise F2 fields, and the legacy real-value F5 predicate.
The source's Lehmann and spectral-bound arguments require separate
microscopic evidence. -/
abbrev IsAnalyticBootstrap
    (G : Correlator) (p : DKMParameters)
    (commutatorNorm : ℕ → ℝ) (n0Norm boundData : ℝ) : Prop :=
  IsDKMAxiomSet G p commutatorNorm n0Norm boundData

/-! ## §2. Analyticity composes with the Wave 1b.3 vertical-equivalence.

Post-strengthening 2026-05-25: the prior `analytic_bootstrap_bypasses_sdp`
identity wrapper `h := h` was removed (its content is now `rfl` via the
`abbrev` above). The substantive composition with verticality is kept. -/

/-- **Legacy bundle equivalence with verticality plus F4, F5 and F6.**
Combines the Wave 1b.3 vertical-bootstrap-iff-CHHK-axiom-set equivalence
with the Wave 1c.1 labelling identification. -/
theorem analytic_iff_vertical_plus_f4f5f6
    (G : Correlator) (p : DKMParameters)
    (commutatorNorm : ℕ → ℝ) (n0Norm boundData : ℝ) :
    IsAnalyticBootstrap G p commutatorNorm n0Norm boundData ↔
    (IsVerticalBootstrap G p commutatorNorm n0Norm boundData ∧
     IsImGRetardedNonneg G ∧
     IsUpperHalfPlaneAnalytic G ∧
     HasParityTimeReversal G) :=
  dkm_axiom_set_iff_vertical_plus_f4f5f6 G p commutatorNorm n0Norm boundData

/-! ## §3. Forward-deferred SDP predicate (research-frontier scaffold).

For the Phase 7+ research-frontier extension to dual S-matrix-style
optimisation (CHHK §6 discussion item), we ship a *predicate-substrate
scaffold* `IsDKMFeasibleSDPCandidate` with no substantive content
beyond the well-typed Prop shape. The substantive SDP-feasibility
content (linear-functional positivity, polynomial matrix inequalities,
SDPB-style numerical optimisation) is reserved for a future wave.

This is a *deferred scaffold*, not a load-bearing predicate — its only
role in Wave 1c.1 is to make explicit that the CHHK approach (the
project's Wave 1c.1 substrate) is **distinct from** any future SDP-based
strengthening. Downstream Wave 2 modules consume `IsAnalyticBootstrap`,
not `IsDKMFeasibleSDPCandidate`. -/

/-- **Forward-deferred SDP-candidate predicate (research-frontier
scaffold).** A linear functional `F : Correlator → ℝ` is an "SDP
feasibility candidate" on a DKM correlator if it satisfies a positivity
condition on a substantive convex-cone of test correlators. **At Wave
1c.1 this is a placeholder Prop with the universally-true shape;** the
substantive convex-cone-positivity content (Mathlib4 substrate:
`ProperCone.hyperplane_separation`, `PositiveLinearMap` on
C*-algebras) ships if and when the project attempts a future SDPB-
extension beyond CHHK analytic bounds.

**Strengthening-pass disposition (2026-05-25):** *KEEP as-is.* The
`Prop := True` shape is intentional research-frontier scaffolding, not
a vacuous predicate to be cut. Phase 7+ SDPB-extension wave will lift
this to substantive convex-cone-positivity content (consuming Mathlib4
`ProperCone.hyperplane_separation` + `PositiveLinearMap`). Removing the
predicate now would erase the architectural marker for the deferred
substantive lift; the placeholder explicitly *advertises* the future
work to downstream readers. -/
def IsDKMFeasibleSDPCandidate
    (_F : Correlator → ℝ) (_G : Correlator) : Prop :=
  True

/-- **Trivial SDP-candidate witness.** Confirms the deferred-scaffold
reduces to `True` for every functional and correlator. -/
theorem trivial_sdp_candidate (F : Correlator → ℝ) (G : Correlator) :
    IsDKMFeasibleSDPCandidate F G := trivial

/-! ## §4. Pairing with the deferred SDP scaffold.

The theorem pairs the supplied bundle witness `h` with a proof of
`True`. The proposed SDP-feasibility predicate remains future work. -/

/-- Pair the supplied legacy bundle with the universally true
SDP-candidate scaffold. Actual SDP feasibility remains deferred. -/
theorem analytic_independent_of_sdp_candidate
    {G : Correlator} {p : DKMParameters}
    {commutatorNorm : ℕ → ℝ} {n0Norm boundData : ℝ}
    (h : IsAnalyticBootstrap G p commutatorNorm n0Norm boundData)
    (F : Correlator → ℝ) :
    IsAnalyticBootstrap G p commutatorNorm n0Norm boundData ∧
    IsDKMFeasibleSDPCandidate F G :=
  ⟨h, trivial_sdp_candidate F G⟩

/-! ## §5. Closure summary — Wave 1c.1 SDP-bypass.

This module ships:
- **`IsAnalyticBootstrap`** — `abbrev` for `IsDKMAxiomSet` identifying
  CHHK's "no SDP, purely analytic" content (post-strengthening 2026-05-25
  the prior `def` plus identity-wrapper `analytic_bootstrap_bypasses_sdp`
  collapsed into a transparent `abbrev`; the labelling is preserved
  without a redundant wrapper theorem).
- **`analytic_iff_vertical_plus_f4f5f6`** — composition with the Wave
  1b.3 vertical equivalence.
- **`IsDKMFeasibleSDPCandidate`** — forward-deferred SDP scaffold for
  the Phase 7+ research-frontier extension.
- **`analytic_independent_of_sdp_candidate`** — pairs the supplied
  bundle witness with the `True` scaffold.

The declarations formalize relationships between the legacy
predicates. A populated physical bundle and its spectral bounds
remain separate obligations. -/

end SKEFTHawking.DKMBootstrap
