# Phase 6o′: Genuine-Substrate Completion of the Phase 6o 
# Emergent-IR / Topological-Invariant Families

## Technical Roadmap — July 2026 (follow-on to `Phase6o_Roadmap.md`)

*Prepared 2026-07-20, at the close of the Codex substrate-review R-01 remediation (main `af4e3c59`).
Sources: `temporary/sk_eft_hawking_substrate_review_2026-07-16/REVIEW_REPORT.md` (findings R-01–R-03) +
`REMEDIATION_PLAN.md`; the R-01 genuine builds merged 2026-07-20 (SoftTheorems/DissipativeNoGo,
NoiseFloorPrediction, EmergentGraviton, Carrollian — memory↔soft edge); the in-module "Documented GAP"
section of `lean/SKEFTHawking/SoftTheorems/Carrollian.lean`; `HYPOTHESIS_REGISTRY` entries
`carrollian_boundary_bms_vertex`, `he3a_moving_eta_nonzero`, `acyclic_factor_graph_has_rank_cert`
(`src/core/constants.py`); On-Shell Methods DR §3–§4.3, §8.2.*

**Relation to the original roadmap.** `Phase6o_Roadmap.md` shipped Waves 1a/1b/2a (among others) at a
predicate-scaffold level that the 2026-07-16 Codex substrate review found partially vacuous
(`:= True` predicates, lookup-table conclusions, identity wrappers). The 2026-07 remediation
(operator-corrected posture: **build the genuine substrate, or prove it can't be built — never walk
back claims**) replaced the vacuous content with genuine theorems wherever tractable in one block.
Phase 6o′ tracks the RESIDUE: the follow-on builds that are bounded-but-larger than one remediation
block, each registered in `HYPOTHESIS_REGISTRY` where short of proof. **Wave labels are primed
versions of the original wave that owns the substrate.**

**Trigger condition:** opened 2026-07-20 by operator authorization of the Carrollian-vertex build
(the Wave 1a′ centerpiece) at the R-01 close.

**Project rules (inherited from `Phase6o_Roadmap.md`, reaffirmed):** No PM / time / phase-cost
estimates anywhere in this roadmap — effort is expressed in **task-count reference classes only**
(e.g. "the cylinder cap-cross arc ≈ 10 worker tasks"). No manuscript drafting from this roadmap;
bundle absorption runs through `LATE_PHASE6_ABSORPTION_PROTOCOL.md` after math closes. No Mathlib
PR drafts; in-program builds use Mathlib naming/style conventions to ease future upstreaming when
authorized.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
>
> 1. **Mandatory project bootstrap** per `CLAUDE.md` Mandatory References list.
> 2. **Read `Phase6o_Roadmap.md` Waves 1a/1b/2a rows** + this roadmap end-to-end before claiming a wave.
> 3. **Critical predecessor modules — read source directly:**
>    - `lean/SKEFTHawking/SoftTheorems/*.lean` — the post-remediation genuine substrate (Boostless
>      soft factor; `memory_eq_softCharge` + `burst_satisfies_ward` FTC pattern; the damped-oscillator
>      retarded kernel + `dissipative_gapped_no_real_pole`; computed noise floor). The Carrollian
>      module's **"Documented GAP"** section is the Wave 1a′ specification.
>    - `lean/SKEFTHawking/Uqsl2Aff*.lean` / `Uqsl3*.lean` / `OnsagerAlgebra.lean` — the in-tree
>      precedent for building named infinite-dimensional algebras with explicit brackets (Wave 1a′ C2/C3).
>    - Mathlib `Mathlib.Algebra.Lie.Extension` (`LieAlgebra.Extension` — central-extension substrate
>      EXISTS; no named Witt/Virasoro/BMS — verified 2026-07-20 via leansearch).
>    - `Lit-Search/_Exploratory/On-Shell Methods, Soft Theorems, and Spinor-Helicity Amplitudes...md`
>      §3, §4.3, §8.2 — read DIRECTLY (never summarized-by-subagent) before Wave 1a′ design passes.
>    - The C0 scout return (filed under `Lit-Search/Phase-6o-prime/` when it lands) — MANDATORY read
>      before the C4 design pass.
> 4. **Apply the preemptive-strengthening checklist** (CLAUDE.md five questions) to every statement;
>    the whole point of Phase 6o′ is that the first pass shipped vacuous shapes. **C4 (phase-space +
>    charges) carries a mandatory Fable-style vacuity gate before any consumption.**
> 5. **Kernel-purity bar throughout:** axioms exactly `{propext, Classical.choice, Quot.sound}`; no
>    new `sorry`/`axiom`/`native_decide`/`maxHeartbeats`-in-proof; `#print axioms` via fresh
>    `lake env lean` is the authoritative check.
> 6. **SCOPE FENCE (binding — the one failure mode to police):** Wave 1a′ targets
>    **analog-appropriate fidelity ONLY** — acoustic horizon, BMS₃ or the Carrollian line, algebraic
>    boundary phase-space model. **Asymptotically-flat BMS₄ at null infinity (asymptotic expansions,
>    spinor-helicity, Lorentz group as a formal Lie group) is OUT OF SCOPE** — that is a
>    Mathlib-frontier program the paper claims do not need. Any drift toward it is a wave-stop +
>    operator escalation, not a stretch goal.
> 7. **No PM / time estimates** — task-count reference classes only.
> 8. **On completion of a wave, retire its `HYPOTHESIS_REGISTRY` entry** (delete the entry, note the
>    discharging theorems in the wave close) and regenerate `PERMANENT_TRACKED_HYPOTHESES.md`
>    (`scripts/render_tracked_hypotheses.py`); `validate.py --check tracked_hypotheses_fresh` gates it.

---

## Wave catalog

**Status legend (matches Phase 6o):** ✅ SHIPPED · 🟡 IN-PROGRESS · 📝 WORKING DOC · ⏳ NOT STARTED

| Wave | Codename | Registry entry | Status | Reference class |
|---|---|---|---|---|
| **Wave 1a′** | **Carrollian/BMS third vertex** (the Strominger-triangle completion for analog systems) | `carrollian_boundary_bms_vertex` | ⏳ **C0 scout DISPATCHED 2026-07-20**; C1–C6 awaiting C0 | ≈ the cylinder cap-cross arc (~10 worker tasks) |
| **Wave 1a″** | BP rank-certificate discharge (`IsAcyclicFactorGraph → Nonempty BPRankCert` — upgrades `bp_converges_on_ranked_acyclic` to cert-free form) | `acyclic_factor_graph_has_rank_cert` | ⏳ ready (routine graph-theory grind; leaf-strip well-founded construction) | ≈ 1–2 worker blocks |
| **Wave 1b′** | Double-copy genuine encoding (Kerr–Schild data + derived Petrov-D/single-copy classifications + structural BCJ no-go) | — (slot: register at harvest if short of proof) | 🟡 **IN-FLIGHT 2026-07-20** (R-02 worker, worktree-wt2) — this row absorbs its outcome: genuine builds close it, precise-gap writeups become registry entries + sub-waves here | TBD at harvest |
| **Wave 1c′** | Gauge-erasure / fracton derived conclusions (center-derived 1-form labels; real bootstrap recursion) | — (slot: register at harvest if short of proof) | 🟡 **IN-FLIGHT 2026-07-20** (R-03 worker, worktree-wt2, same block as 1b′) | TBD at harvest |
| **Wave 2a′** | ³He-A moving-operator η-invariant (the full spectral-asymmetry SYMBOL for the moving 3D domain-wall Dirac operator) | `he3a_moving_eta_nonzero` | ⏳ **PARKED as landmark** — `eliminability: very_hard` (needs Dirac-operator spectral theory + APS index infrastructure absent from Mathlib; a future Phase 6X wave or Mathlib contribution). NOT queued for spare capacity. | Mathlib-frontier (out of Phase 6o′ scope; tracked only) |

**Wave dependencies:** 1a′ C1/C2 are independent of each other; C3 needs C2; C4 needs C0 + C1 + C3
(+ its own lead design pass); C5 needs C4 + the banked `memory_eq_softCharge`/`softCharge` machinery;
C6 gates 1a′ close. 1a″, 1b′, 1c′ are mutually independent and independent of 1a′. 2a′ has no
in-scope dependencies (parked).

---

## Wave 1a′ — the Carrollian/BMS vertex arc (the centerpiece)

**Objective.** Discharge `carrollian_boundary_bms_vertex`: build the genuine third Strominger-triangle
vertex for the acoustic analog — a Carrollian structure on the sonic horizon carrying BMS-type
supertranslation charges whose conservation Ward identity IS the acoustic soft theorem — and rewire
`StromingerTriangleClosed` so all three vertices + both proven edges are real theorems on the same
concrete model. End state: the registry entry is RETIRED and the triangle claim is unconditionally
kernel-pure.

**Why bounded (the LOE finding, 2026-07-20):** none of the 16-conv machinery class is needed (no PD,
no Steenrod, no surgery, no bordism carriers). The deepest analytic content is FTC/integration-by-parts
class — already demonstrated by `memory_eq_softCharge`. The algebra layer has direct in-tree precedent
(Uqsl2Aff/Uqsl3/Onsager) and Mathlib's `LieAlgebra.Extension` supplies the central-extension substrate.

### Sub-waves

- **C0 — literature-anchoring scout** — ✅ **RETURNED + LEAD-VETTED + FILED 2026-07-20**:
  `Lit-Search/Phase-6o-prime/C0_horizon_BMS_charge_algebra_verdict_20260720.md` (MANDATORY read
  before C3/C4/C5). **Verdict:** (a) primary model = the 2+1 acoustic horizon with the
  Donnay-et-al./Penna **horizon** algebra `Vect(S¹) ⋉ C∞(S¹)_ab` — CENTERLESS at vector-field
  level (central extensions are charge-algebra properties to be DERIVED, never assumed;
  Barnich–Compère); the 1+1 Carrollian-line is the degenerate check. (b) The charge to encode =
  **Penna eq 3.3/3.13: `Q_f = ∫ f · κ/8π`** over the horizon cut — κ = the sonic-horizon surface
  gravity, ALREADY formalized in this project; conservation via the Damour–Navier–Stokes + energy
  equations. (c) The Ward identity to encode = Agrawal–Nguyen eqs 10/11/18 (charge difference
  across the correlator = zero-frequency mode insertion; spontaneously-broken-symmetry framing);
  spot-check those equation numbers at PDF fidelity before Lean encoding (HTML-extraction grade).
  The memory corner cites Strominger–Zhiboedov 1411.5745. **Dissipation subtlety DISSOLVES:
  Penna's membrane conservation holds WITH real viscosities — dissipation relocates charge into
  the membrane energy density ("energy conserved at every angle", §4.2).** Negative result
  confirmed: NO published acoustic-horizon BMS theorem exists — the build is a new composition.
  **⚠ Citation correction propagated:** arXiv:2504.10577 = Agrawal–Nguyen (NOT
  Have–Nguyen–Prohazka–Salzer, whose paper is 2402.05190) — fixed in Carrollian.lean, the
  registry entry, and here.
- **C1 — `CarrollianStructure` + the acoustic-horizon instance** *(~1 block)*. Structure class:
  carrier + degenerate symmetric bilinear form of corank 1 + nowhere-zero null field spanning the
  kernel; concrete instance on an explicit ℝⁿ model of the sonic line of a transonic background.
  Non-vacuity pins: the form is genuinely degenerate (a kernel witness) AND genuinely nonzero off
  the kernel (a falsifiable evaluation).
- **C2 — Witt/Virasoro in-tree** *(~1–2 blocks; independent of C1)*. ℤ-graded basis Lₙ as
  finitely-supported functions; explicit bracket; Jacobi; the standard 2-cocycle + central extension
  via `LieAlgebra.Extension`. Mathlib-style naming for future upstreaming.
- **C3 — BMS semidirect product + supertranslation subalgebra** *(~1 block; needs C2)*.
  Vect ⋉ functions with the action bracket; the abelian supertranslation ideal as a `LieIdeal`;
  the quotient statement.
- **C4 — boundary phase-space model + charge functionals** *(~1–2 blocks; needs C0+C1+C3; LEAD
  DESIGN PASS FIRST + mandatory vacuity gate)*. The C0-anchored model of horizon field data + the
  supertranslation charge as a functional; charges must act NON-TRIVIALLY (a moved-state witness) —
  this is where the first-pass vacuity failure would recur if unpoliced.
- **C5 — the charge Ward identity + triangle rewiring** *(~1–2 blocks; needs C4)*. Charge
  conservation ⟹ the acoustic soft theorem on the model (FTC/IBP class, the `memory_eq_softCharge`
  pattern); rewire `StromingerTriangleClosed` to conjoin three REAL vertices; retire the registry
  entry; update the Phase6o stakeholder-doc lines flagged at the R-01 close (accuracy sweep).
- **C6 — vacuity gate round** *(~1 block)*. Fable-style attack on the C1/C4/C5 statements (zero-
  geometric-input discharge attempts) before the wave closes; then the standard wave gate
  (`validate.py` full + fresh adversarial review at the next Stage-13-touching pass).

**Acceptance (wave close):** all C1–C5 headliners kernel-pure via fresh `#print axioms`; C6 gate
passed; `carrollian_boundary_bms_vertex` deleted from `HYPOTHESIS_REGISTRY` +
`PERMANENT_TRACKED_HYPOTHESES.md` regenerated + `tracked_hypotheses_fresh` green; no
`:= True`/lookup-table/identity-wrapper shapes anywhere in the new modules (proxy-body audit green);
the triangle's three vertices and two edges name real theorems in module docstrings.

---

## Bundle absorption

Inherits the original Wave 1a/1b/2a mappings (`D1` + `F` flagship cross-bridge content; `D2/D3/L3/E1`
for the 2a family) — **DEFERRED** to the standing absorption pass per `LATE_PHASE6_ABSORPTION_PROTOCOL.md`,
branch D.2, exactly as the parent roadmap records. The R-01-flagged stakeholder-doc accuracy lines
(`Phase6o_Roadmap.md:73,119-138`, `Phase6o_Implications.md`, `RESEARCH_STATUS_OVERVIEW.md`) are swept
in C5 (for the Carrollian rows) and at the 1b′/1c′ harvests (for theirs) — accuracy-only edits, no
claim walk-backs without operator sign-off.
