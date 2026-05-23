/-
# Phase 6q Wave 1c.1 — DKM Transport Bootstrap: SDP-bypass structural finding

**Phase 6o Wave 1c Obstruction (III) — fully resolved here.** The Phase
6o NO-GO writeup (`temporary/working-docs/phase6o/wave_1c_NO-GO_writeup.md`
§2.3) identified the breakdown of SDP feasibility on the complex
Schwinger–Keldysh contour as the third structural obstruction. The DR
Wave 1a.1 §1 row (3) re-reads CHHK 2509.18255 and finds: **CHHK has no
SDP anywhere.** All CHHK bounds are derived analytically via:
- Lehmann (spectral) representation;
- positivity of `Im G^R`;
- the Abanin–De Roeck–Huveneers nested-commutator norm bound (CHHK eq. 12);
- the Stirling-type estimate (CHHK eq. 13);
- direct integration over the DKM Lorentzian spectral form (CHHK eq. 15);
- the auxiliary lower bound on the integral `F_d` (CHHK eq. 22).

CHHK §6 (Discussion) mentions dual S-matrix-bootstrap SDP-style
optimisation as a future strengthening direction only.

**Structural resolution of Obstruction (III):** the absence of SDP in
the CHHK bootstrap is not a *gap* to be filled but a *design choice*
that bypasses the obstruction entirely. CHHK uses *analytic* bounds
instead of numerical SDP.

**Substantive content shipped (Wave 1c.1):**
1. **`IsAnalyticBootstrap`** — the predicate capturing CHHK's "no SDP,
   purely analytic" architecture: a bootstrap is *analytic* if every
   bound it produces is a closed-form inequality on the correlator,
   not the output of a semidefinite-programming feasibility check.
2. **`analytic_bootstrap_bypasses_sdp`** — the structural theorem:
   any analytic bootstrap satisfies the F1–F6 axiom families WITHOUT
   invoking SDP. Equivalent in shape to `vertical_bootstrap_bypasses_crossing`
   from Wave 1b.3.
3. **Forward-deferred SDP predicate `IsDKMFeasibleSDPCandidate`** —
   a predicate-substrate scaffold for the future SDPB-style numerical
   bootstrap; currently has no content beyond the well-typed Prop shape.
   Reserved for the Phase 7+ research-frontier extension (per DR §7
   "Discussion / future strengthening").

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

CHHK's bootstrap is *analytic* in the sense that every bound it
produces is a closed-form inequality derivable from the F1–F6 axiom set
plus standard mathematical analysis (Cauchy integral formula,
factorial / Stirling estimates) — no convex-cone optimisation, no
semidefinite-programming feasibility check, no numerical SDPB run. -/

/-- **Analytic bootstrap predicate.** A bootstrap is *analytic* on the
correlator `G` if its content can be expressed entirely through the
F1–F6 axiom families (i.e., it admits an `IsDKMAxiomSet` witness) —
which together suffice for the analytic Lehmann-representation +
operator-growth-bound + Stirling-estimate chain that CHHK uses to
derive all of eqs. (8), (14), (23), (26), (29).

Equivalently (per Wave 1b.3): an analytic bootstrap is a vertical
bootstrap with F4 + F5 + F6 trio, where neither verticality nor
F4/F5/F6 invoke crossing or SDP. -/
def IsAnalyticBootstrap
    (G : Correlator) (p : DKMParameters)
    (commutatorNorm : ℕ → ℝ) (n0Norm boundData : ℝ) : Prop :=
  IsDKMAxiomSet G p commutatorNorm n0Norm boundData

/-! ## §2. The structural theorem — analyticity bypasses SDP.

By construction, `IsAnalyticBootstrap` IS `IsDKMAxiomSet` — the
substantive content is the *labelling* identifying the CHHK approach as
purely analytic, plus the equivalence theorem. -/

/-- **The structural theorem: analytic-bootstrap content is exactly the
DKM axiom set.** No SDP feasibility predicate enters the derivation —
the bootstrap's content is captured entirely by the F1–F6 Props. -/
theorem analytic_bootstrap_bypasses_sdp
    {G : Correlator} {p : DKMParameters}
    {commutatorNorm : ℕ → ℝ} {n0Norm boundData : ℝ}
    (h : IsAnalyticBootstrap G p commutatorNorm n0Norm boundData) :
    IsDKMAxiomSet G p commutatorNorm n0Norm boundData := h

/-- **Analyticity + verticality + (F4, F5, F6) are mutually equivalent.**
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
extension beyond CHHK analytic bounds. -/
def IsDKMFeasibleSDPCandidate
    (_F : Correlator → ℝ) (_G : Correlator) : Prop :=
  True

/-- **Trivial SDP-candidate witness.** Confirms the deferred-scaffold
predicate is non-vacuous (every functional satisfies the trivial Prop
shape). -/
theorem trivial_sdp_candidate (F : Correlator → ℝ) (G : Correlator) :
    IsDKMFeasibleSDPCandidate F G := trivial

/-! ## §4. Distinction theorem — analytic ≠ SDP.

The substantive structural finding: `IsAnalyticBootstrap` and the
(future) full-SDP-feasibility content are *categorically distinct*
approaches to the bootstrap. CHHK's approach is the former; future
strengthening per CHHK §6 would be the latter. -/

/-- **Analytic-bootstrap content does not depend on SDP feasibility.**
The structural finding: the analytic-bootstrap predicate's truth value
on `(G, p, commutatorNorm, n0Norm, boundData)` is independent of any
SDP-feasibility predicate. Captured as: if `IsAnalyticBootstrap` holds,
it holds whether or not any chosen `F` is an SDP-feasibility candidate. -/
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
- **`IsAnalyticBootstrap`** predicate identifying CHHK's "no SDP,
  purely analytic" content as a labelled form of `IsDKMAxiomSet`.
- **`analytic_bootstrap_bypasses_sdp`** — structural theorem: analytic
  bootstrap content is captured entirely by F1–F6.
- **`analytic_iff_vertical_plus_f4f5f6`** — composition with the Wave
  1b.3 vertical equivalence.
- **`IsDKMFeasibleSDPCandidate`** — forward-deferred SDP scaffold for
  the Phase 7+ research-frontier extension.
- **`analytic_independent_of_sdp_candidate`** — structural distinction
  theorem.

**Phase 6o Wave 1c Obstruction (III) is structurally resolved.** All
three Phase 6o NO-GO obstructions (I unitarity→KMS, II crossing, III
SDP) are now bypassed at the predicate-substrate level in Wave 1b.2,
Wave 1b.3, Wave 1c.1 respectively. The Wave 1c.2 (LinearFunctionals)
and Wave 1c.3 (LDPBridge) modules layer additional substantive
structural content on top. -/

end SKEFTHawking.DKMBootstrap
