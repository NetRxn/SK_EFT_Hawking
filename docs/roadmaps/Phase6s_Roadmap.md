# Phase 6s: Twin Formalization-Line Phase — Phase 1c Bootstrap-as-Uniqueness (KMS-decorated OS Axioms) + Substantive I3 Mathlib4 Upstream

## Technical Roadmap — May 2026

*Prepared 2026-05-12 at Phase 6o close. Sources: planning conversation 2026-05-12 (4-phase scoping pass); user direction "find good fits for our pipeline & investigate directions that may lead to strengthening of the program and investigations that could plausibly make significant contributions to the physics/math/qc communities, and/or contribute meaningful no-gos"; I3 paper §upstream-coordination at `papers/I3/paper_draft.tex` §3 (the explicit upstream-PR coordination plan); Modular Bootstrap DR §3 Tier 2 (Phase 1c bootstrap-as-uniqueness route).*

**Trigger condition:** Phase 6s opens at Phase 6o close. The phase has two **parallel formalization tracks** both targeting **community alignment**:

- **Track 1 — Phase 1c bootstrap-as-uniqueness:** extend the Douglas-Hoback-Mei-Nissim Lean formalization of the Osterwalder-Schrader axioms (Euclidean QFT axiomatic) with a KMS-decorated Schwinger-Keldysh / OS variant. Aligned with PhysLean community direction. Opens a new formalization line that could become foundational for KMS-EFT going forward.
- **Track 2 — Substantive I3 Mathlib upstream:** lift each of the 12 I3 predicate-substrate Lean modules (Itô + LDP) to substantive Mathlib-quality classical content; open Mathlib4 PR cycle. Per `papers/I3/paper_draft.tex` §3: "each module is sized for exactly one upstream PR." The phase delivers 12-16 upstream PRs to Mathlib4.

**The two tracks are independent in substrate but coordinated in cadence** — both are community-alignment work, both involve external coordination cycles (PhysLean / Mathlib4 maintainers), both are designed to run in parallel without blocking the program's main research lanes (6p, 6q, 6r).

**Honesty caveat (carried forward from planning conversation):** Track 2 is **mostly beyond what helps the SK-EFT-Hawking project directly**. The substrate-interface design choice (predicate-substrate operationalization in I3) was deliberate; downstream papers use the substrate interface, not the full classical content. Track 2 is **community citizenship work** with ~20% marginal benefit to the program (stronger cross-bridge instances; downstream papers can derive rather than hypothesize for some specific cases). The framing of Phase 6s is "good citizenship investment that 20% strengthens our own program," not "necessary for our work."

**Status (2026-05-12, Phase 6s stub):** **Roadmap stub committed at Track / Wave level**. Two Tracks, ten Waves (3 Track 1 + 7 Track 2).

**Project rule (carried from Phase 6n/6o; user direction reaffirmed 2026-05-12):** **No PM / time / phase-cost estimates** anywhere in this roadmap. **No manuscript drafting at this phase** for Track 1 (Track 1 substrate work only). **Mathlib4 PR drafts ARE authorized in Phase 6s Track 2** — that is the substantive deliverable of Track 2; this is the **explicit reversal** of the Phase 6n/6o "no Mathlib PR drafts" rule, scoped to Track 2 only.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
>
> 1. **Mandatory project bootstrap** per `CLAUDE.md` Mandatory References list.
> 2. **Read `Phase6o_Roadmap.md` Wave 3b end-to-end** — Phase 6s Track 2 is the substantive-lift continuation of Phase 6o Wave 3b's predicate-substrate I3 work.
> 3. **Read this roadmap end-to-end** before claiming any wave assignment.
> 4. **Read the planning brief `memory/project_phase_6p6q6r6s_planning.md`** for entry-state context.
> 5. **Critical predecessor modules + literature — read source directly:**
>    - **Track 1 substrate — Douglas-Hoback-Mei-Nissim OS-axioms Lean paper:** verify at Wave 1a.1 substrate-scout that this paper exists and is publicly available (likely arXiv:2502.* or similar; verify via WebFetch); read end-to-end. **If the paper has not yet been published, Phase 6s Track 1 is on hold pending publication / community coordination.**
>    - **Track 1 substrate — PhysLean roadmap:** consult PhysLean roadmap / Zulip for current state of KMS-related work. Coordination dependency.
>    - **Track 2 substrate — I3 Lean modules (heaviest dependency):** `lean/SKEFTHawking/Itô/*.lean` (6 modules: StochasticIntegral, QuadraticVariation, Semimartingale, ItoIsometry, ItoLemma, Novikov), `lean/SKEFTHawking/LDP/*.lean` (6 modules: CramerIID, Sanov, Contraction, CramerLowerBound, Varadhan, LDPCompatibleSKEFT). Read each module fully. The I3 paper at `papers/I3/paper_draft.tex` §3 contains the explicit upstream-PR plan.
>    - **Track 2 substrate — Mathlib4 probability infrastructure:** `Mathlib/Probability/*` for the existing martingale + filtration + Markov-kernel substrate; `Mathlib/MeasureTheory/Integral/*` for the integration substrate; Degenne brownian-motion repository (separate from Mathlib mainline; consult repository state).
>    - **Track 2 substrate — Mathlib4 PR conventions:** read `mathlib4` repository CONTRIBUTING.md + Zulip-channel etiquette + recent PR examples for the probability namespace. Coordination dependency.
> 6. **`LATE_PHASE6_ABSORPTION_PROTOCOL.md` — load before any bundle-touching work.**
> 7. **Apply preemptive-strengthening checklist** + **primacy-claim discipline** per `memory/project_2026_05_12_first_claim_close.md`. **CRITICAL for Phase 6s:** the Mathlib upstream cycle is the kind of work that most invites "first Itô integral in Mathlib4" framing in PR descriptions. Resist this framing; write Mathlib PR descriptions in Mathlib's own factual style ("This PR adds the Itô integral against continuous semimartingales..." not "First formalization of...").
> 8. **Do not delegate Lean theorem proving to subagents.** MCP loop default; Aristotle is fallback. Explore-agent substrate scouts authorized.
> 9. **No PM / time estimates anywhere** — by user direction.
> 10. **Mathlib PR drafts ARE authorized in Phase 6s Track 2** (explicit reversal of Phase 6n/6o no-PR rule, scoped to Track 2 only).

---

## Wave catalog — Shape D (2 Tracks × 10 Waves: 3 Track 1 + 7 Track 2)

Ten waves across two Tracks.

**Track 1 (3 waves):** Phase 1c bootstrap-as-uniqueness via KMS-decorated OS axioms.
**Track 2 (7 waves):** Substantive I3 Mathlib upstream — substrate analysis + 6 PR cycles (Itô track: 3 PRs; LDP track: 3 PRs).

**Status legend:**
- ✅ **SHIPPED** — Lean / numerical / memo deliverables committed; PRs merged (Track 2) or substrate published (Track 1).
- 🟡 **IN-PROGRESS** — partial deliverables shipped; for Track 2, PR open and under review.
- 📝 **WORKING DOC** — Stage-1 substrate-analysis or audit draft exists; no Lean yet.
- ⏳ **NOT STARTED** — substrate ready; awaiting dispatch.

| Wave | Codename | Status | Bundle absorption | Branch | User-auth gate |
|---|---|---|---|---|---|
| **Track 1 — Phase 1c bootstrap-as-uniqueness via KMS-decorated OS axioms** | | | | | |
| **Wave 1a** | OS axioms substrate analysis + PhysLean coordination | ⏳ NOT STARTED | n/a (working doc + community coordination) | n/a | possibly **YES** (PhysLean Zulip coordination) |
| **Wave 1b** | KMS-decoration of OS axioms — Lean substrate | ⏳ NOT STARTED | New bundle candidate OR L2/D5 extension — DEFERRED | **D.4 candidate** | possibly **YES** (new-bundle creation) |
| **Wave 1c** | Bootstrap-as-uniqueness application: program's SK-EFT-Hawking substrate as OS-axiom instance | ⏳ NOT STARTED | F flagship (positioning) + new bundle — DEFERRED | **D.2** | none |
| **Track 2 — Substantive I3 Mathlib upstream (6 PR cycles)** | | | | | |
| **Wave 2a** | Substrate analysis + Mathlib4 PR-quality bar audit | ⏳ NOT STARTED | n/a (working doc + Mathlib coordination) | n/a | **YES** — Mathlib PR campaign authorization required |
| **Wave 2b** | I3 Itô PR 1 — `StochasticIntegral` substantive lift + Mathlib PR | ⏳ NOT STARTED | I3 refinement (substantive-content addendum) — DEFERRED | **D.2** | none after Wave 2a |
| **Wave 2c** | I3 Itô PR 2 — `QuadraticVariation` + `Semimartingale` substantive lift + Mathlib PR | ⏳ NOT STARTED | I3 refinement — DEFERRED | **D.2** | none |
| **Wave 2d** | I3 Itô PR 3 — `ItoIsometry` + `ItoLemma` + `Novikov` substantive lift + Mathlib PR | ⏳ NOT STARTED | I3 refinement — DEFERRED | **D.2** | none |
| **Wave 2e** | I3 LDP PR 1 — `CramerIID` substantive lift + Mathlib PR | ⏳ NOT STARTED | I3 refinement — DEFERRED | **D.2** | none |
| **Wave 2f** | I3 LDP PR 2 — `Sanov` + `Contraction` substantive lift + Mathlib PR | ⏳ NOT STARTED | I3 refinement — DEFERRED | **D.2** | none |
| **Wave 2g** | I3 LDP PR 3 — `CramerLowerBound` + `Varadhan` + `LDPCompatibleSKEFT` substantive lift + Mathlib PR | ⏳ NOT STARTED | I3 refinement — DEFERRED | **D.2** | none |

**Wave dependencies:**
- Track 1 waves run sequentially (1a → 1b → 1c).
- Track 2 waves run sequentially within Track 2 (2a → 2b → 2c → 2d → 2e → 2f → 2g), BUT can be parallelized after Wave 2a authorization (the 6 PR-cycle waves are mutually independent in substrate; only the Mathlib review-cycle cadence binds them).
- **Tracks 1 and 2 are independent of each other; can run in parallel.**

**Coherent sub-narrative.** Both tracks are **community-alignment work**. Track 1 contributes to PhysLean's KMS-EFT formalization line; opens new ground in the Lean QFT-axiomatic formalization landscape. Track 2 contributes to Mathlib4's probability infrastructure; turns I3's predicate-substrate operationalization into substantive classical content. Together they position the program as a contributor to the formal-methods-for-physics community — citizenship work that strengthens external recognition while marginally strengthening internal cross-bridge instances.

**Recommended next-up order:**

1. **Wave 2a** Mathlib4 PR-quality bar audit + user-authorization gate (the Mathlib campaign is the bigger deliverable; should be authorized first).
2. **Wave 1a** OS-axioms substrate analysis (in parallel with Wave 2a; depends on DR-style substrate research on PhysLean coordination state).
3. **Wave 2b-2g** Mathlib PR cycle (parallelizable after Wave 2a authorization; cadence bound by Mathlib review-cycle).
4. **Wave 1b** KMS-decoration Lean substrate (after Wave 1a substrate analysis).
5. **Wave 1c** Bootstrap-as-uniqueness application (after Wave 1b).

**Pre-Phase-7 bundle absorption gate:** Track 2 doesn't trigger bundle absorption events in the usual sense (Mathlib PRs change Mathlib4 mainline, not the program's bundle drafts); Track 2 closes when all 6 PRs are merged (or stalled at maintainer's discretion). Track 1 may trigger a new-bundle-creation user-authorization gate at Wave 1b close.

---

## Track 1 — Phase 1c bootstrap-as-uniqueness via KMS-decorated OS axioms

### Wave 1a — OS axioms substrate analysis + PhysLean coordination ⏳ NOT STARTED

**Sub-wave decomposition (proposed):**

- **Wave 1a.1 (Douglas-Hoback-Mei-Nissim paper substrate-scout):** WebFetch + verify the Douglas-Hoback-Mei-Nissim OS-axioms Lean paper. Verify publication state + paper content + GitHub repository (if any) + Lean module names. **If paper not published or repository not public, Phase 6s Track 1 is on hold pending availability.**
- **Wave 1a.2 (PhysLean coordination):** consult PhysLean roadmap / Zulip for current state of KMS-related work. Identify whether PhysLean has open work on KMS-EFT axiomatic — if yes, coordinate; if no, Phase 6s Track 1 is the program's PhysLean contribution. Working doc at `temporary/working-docs/phase6s/wave_1a_OS_axioms_PhysLean_coordination.md`.
- **Wave 1a.3 (KMS-decoration substrate sketch):** working doc at `temporary/working-docs/phase6s/wave_1a_KMS_decoration_substrate.md` identifying which OS axioms get KMS-decorated and how. The substantive entry-point: OS axioms are 5 (reflection positivity, Euclidean invariance, regularity, cluster decomposition, symmetry); KMS-decoration adds a sixth axiom encoding the dynamical-KMS Z₂ involution on the Schwinger-Keldysh contour. Substrate scout dispositive on which OS axioms remain intact under KMS-decoration and which need modification.

**Three-question template:**

- *Integrates with:* Douglas-Hoback-Mei-Nissim OS-axioms Lean paper (verify at Wave 1a.1); PhysLean SymTFT + QFT-axiomatic roadmap; Phase 6o Wave 1c NO-GO writeup (the trigger context — KMS-replaces-unitarity content); Phase 6n Wave 2a Glorioso-Liu monotonicity (the program's existing KMS-related substrate); arXiv:2511.08560 KMS bootstrap on QM (KMS-bootstrap-framework substrate).
- *New constraint adds:* a fresh substrate analysis identifying the KMS-decoration shape, with explicit PhysLean coordination.
- *Tension surfaces:* (i) Douglas-Hoback-Mei-Nissim paper availability dispositive — if not yet published, Phase 6s Track 1 is on hold; (ii) PhysLean roadmap coordination — Phase 6s Track 1 should not duplicate existing PhysLean work; (iii) the KMS-decoration shape — does it commute with the OS-Wick-rotation (Schwinger-Keldysh = real-time → Euclidean is the standard Wick rotation; KMS-decoration must respect this) — substantive structural question.

**Substrate.** Douglas-Hoback-Mei-Nissim OS-axioms Lean paper; PhysLean roadmap; Phase 6o Wave 1c NO-GO writeup; Phase 6n Wave 2a Glorioso-Liu monotonicity modules; arXiv:2511.08560 KMS bootstrap.

**Module decomposition (Lean):** None at Wave 1a (working doc + community coordination only).

**Bundle absorption.** n/a.

**Risk axes.**
- Douglas-Hoback-Mei-Nissim paper availability.
- PhysLean coordination dependency.
- KMS-decoration shape — substantive structural question.

### Wave 1b — KMS-decoration of OS axioms — Lean substrate ⏳ NOT STARTED

**Sub-wave decomposition (proposed; matures after Wave 1a):**

- **Wave 1b.1 (KMS-decorated OS axioms Lean encoding):** Lean modules implementing the KMS-decorated OS axioms (specific module names dispositive at Wave 1a.3 substrate-sketch outcome). Substrate-data level operationalization initially; substantive content depending on Mathlib4 measure-theory + complex-analysis substrate adequacy.
- **Wave 1b.2 (substrate-instance witness on a concrete dissipative EFT):** explicit instance theorem: a specific concrete dissipative EFT (e.g., diffusion equation; linear-response transport) satisfies the KMS-decorated OS axioms. Substantive content.
- **Wave 1b.3 (PhysLean PR draft if appropriate):** if PhysLean coordination at Wave 1a.2 confirmed PhysLean wants the contribution, draft a PhysLean PR adding the KMS-decoration substrate. **User-authorization gate** for new-bundle creation (if Phase 6s ships KMS-EFT axiomatic as a distinct bundle target) OR for L2/D5 extension.

**Three-question template:**

- *Integrates with:* Wave 1a substrate; Douglas-Hoback-Mei-Nissim baseline; PhysLean infrastructure; program's existing KMS-related Lean modules (Glorioso-Liu, Crooks-on-analog-Hawking).
- *New constraint adds:* Lean substrate for the KMS-decorated OS axioms; opens a new formalization line aligned with PhysLean.
- *Tension surfaces:* (i) Mathlib4 complex-analysis adequacy for the OS reflection-positivity axiom (Wick-rotation content); (ii) PhysLean PR readiness dispositive on coordination state.

**Substrate.** Wave 1a substrate; Mathlib4 complex-analysis + measure-theory infrastructure; PhysLean substrate.

**Bundle absorption.** D.4 candidate (new bundle) OR D.2 extension into L2/D5. User-authorization required for new-bundle decision.

**Risk axes.**
- Mathlib4 OS-axiom infrastructure adequacy.
- PhysLean coordination dependency.
- New-bundle vs. extension decision.

### Wave 1c — Bootstrap-as-uniqueness application ⏳ NOT STARTED

**Sub-wave decomposition (proposed):**

- **Wave 1c.1 (program's SK-EFT-Hawking substrate as KMS-decorated-OS-axiom instance):** substantive theorem identifying the SK-EFT-Hawking substrate as a concrete instance of the KMS-decorated OS axioms. Cross-bridge to all the program's existing SK-EFT-Hawking Lean modules.
- **Wave 1c.2 (uniqueness statement):** substantive theorem: under the KMS-decorated OS axioms + a specific finite axiom-replacement set (the set identified by Phase 6o Wave 1c as needed for a positive bootstrap result), the SK-EFT-Hawking substrate's transport coefficients are uniquely determined. This is the substantive **positive bootstrap-as-uniqueness result** — companion to the Wave 1c NO-GO writeup.
- **Wave 1c.3 (flagship-F positioning):** flagship F cross-bridge — short positioning paragraph identifying where the bootstrap-as-uniqueness result sits in the broader emergent-physics-from-substrate narrative.

**Three-question template:**

- *Integrates with:* Wave 1b substrate; Phase 6o Wave 1c NO-GO writeup; Phase 6q DKM transport bootstrap (parallel positive-result effort); program's existing SK-EFT-Hawking Lean modules; F flagship.
- *New constraint adds:* a substantive positive bootstrap-as-uniqueness result on the SK-EFT-Hawking substrate, via the KMS-decorated OS axioms.
- *Tension surfaces:* (i) the substantive uniqueness statement depends on the axiom-replacement set identified by Phase 6o Wave 1c — if the replacement set is too restrictive, the uniqueness statement is vacuous; if too permissive, the uniqueness statement is impossible; (ii) overlap / divergence with Phase 6q DKM transport bootstrap (both are positive-result responses to the Wave 1c NO-GO); productive cross-bridge structural finding.

**Substrate.** Wave 1b substrate; Phase 6o Wave 1c modules; Phase 6q DKM substrate (cross-bridge); program's existing SK-EFT-Hawking modules; F flagship.

**Bundle absorption.** D.2 into F flagship (positioning) + new bundle (the bootstrap-as-uniqueness paper).

**Risk axes.**
- Substantive uniqueness statement depends on axiom-replacement set; substrate scout dispositive.
- Cross-bridge with Phase 6q DKM transport bootstrap.

---

## Track 2 — Substantive I3 Mathlib upstream

### Wave 2a — Substrate analysis + Mathlib4 PR-quality bar audit ⏳ NOT STARTED

**This is the gating wave for Track 2. User-authorization required.**

**Sub-wave decomposition (proposed):**

- **Wave 2a.1 (Mathlib4 PR-quality bar audit):** read recent Mathlib4 PRs in the probability namespace; identify the canonical PR style (commit message format, theorem-naming conventions, docstring format, simp-lemma policy, deprecation policy); identify the active maintainers in the probability namespace. Working doc at `temporary/working-docs/phase6s/wave_2a_Mathlib_quality_bar.md`.
- **Wave 2a.2 (I3 module audit):** read each of the 12 I3 modules; identify the substantive content gap from predicate-substrate level to Mathlib-quality classical level. Per `papers/I3/paper_draft.tex` §3: "the substantive quantitative content (the bilinear $L^2$-isometry norm; the Doob-Meyer uniqueness; the C² change-of-variables identity; the Esscher-tilted Cramér lower bound) lives at the downstream-consumer interface and is the staged target of the upstream Mathlib4 PR cycle." This wave makes the gap explicit, per-module.
- **Wave 2a.3 (PR campaign authorization request):** working doc requesting **user authorization** for the 6-PR Mathlib campaign. The authorization scope: (a) PRs are opened against `leanprover-community/mathlib4` mainline; (b) PR descriptions follow Mathlib factual style (NOT primacy-claim style per `project_2026_05_12_first_claim_close.md`); (c) PR review cycles may take weeks-months in Mathlib's cadence (which per `feedback_loe_calibration.md` is "real Mathlib weeks-months," not "our pipeline weeks-months" — Mathlib coordination is genuinely external and the calibration does not apply). User-auth required before Wave 2b opens.

**Three-question template:**

- *Integrates with:* I3 Lean modules + I3 paper; Mathlib4 probability namespace; Mathlib4 PR conventions; Mathlib4 active maintainers.
- *New constraint adds:* explicit per-module substantive-content gap audit; PR-campaign authorization framework.
- *Tension surfaces:* (i) Mathlib4 PR campaign is **the** Track 2 deliverable; the per-module substantive content lift is the core work; (ii) Mathlib review cadence is genuinely external — the calibration does not apply (LOE calibration is about the pipeline's cadence, not external community's); (iii) authorization request scope is broad (6 PRs over potentially months); user may choose to authorize the full campaign or pilot with 1-2 PRs first.

**Substrate.** I3 Lean modules + I3 paper §3; Mathlib4 mainline; Mathlib4 maintainer list; recent Mathlib4 probability-namespace PRs.

**Module decomposition (Lean):** None at Wave 2a (audit + authorization only).

**Bundle absorption.** n/a.

**Risk axes.**
- Mathlib4 PR campaign authorization scope (full vs. pilot).
- Mathlib4 review cadence (external; weeks-to-months Mathlib cadence).
- Per-module substantive-content gap may be larger than expected for some modules; substrate-discovery yield.

### Wave 2b — I3 Itô PR 1: `StochasticIntegral` substantive lift + Mathlib PR ⏳ NOT STARTED

**Sub-wave decomposition (proposed):**

- **Wave 2b.1 (substantive content lift):** lift `lean/SKEFTHawking/Itô/StochasticIntegral.lean` predicate substrate (`IsStochasticIntegral H W I` Prop) to a substantive Mathlib-quality `StochasticIntegral` definition + theorem. Substantive content: integration of a predictable process H against a continuous semimartingale W; the substantive `∫₀^t H_s dW_s` definition; bilinear properties; cross-bridge to Mathlib4 measure-theory.
- **Wave 2b.2 (Mathlib-style polish):** apply Mathlib4 conventions (naming, docstring, simp policy) per Wave 2a.1 audit.
- **Wave 2b.3 (PR open + review cycle):** open PR against `leanprover-community/mathlib4` mainline. PR description follows Mathlib factual style. Review-cycle iteration with maintainers until merged or stalled.
- **Wave 2b.4 (I3 paper update):** after PR merge (or close), update `papers/I3/paper_draft.tex` §3 + per-module annotations reflecting the Mathlib-upstream-state.

**Three-question template:**

- *Integrates with:* Wave 2a audit + authorization; I3 `StochasticIntegral.lean`; Mathlib4 measure-theory + probability infrastructure.
- *New constraint adds:* Mathlib4 mainline-merged Itô stochastic integral against continuous semimartingales.
- *Tension surfaces:* (i) substantive content lift complexity (Wave 2a.2 dispositive); (ii) Mathlib review cadence; (iii) PR scope decisions (one big PR vs. several smaller PRs); substrate scout dispositive.

**Substrate.** Wave 2a; I3 `StochasticIntegral.lean`; Mathlib4 measure-theory + probability infrastructure.

**Module decomposition (Mathlib):**
```
Mathlib/Probability/Stochastic/Integral.lean (or equivalent — Mathlib decides namespace)
  -- Substantive content lifted from SKEFTHawking/Itô/StochasticIntegral.lean
```

**Bundle absorption.** D.2 into I3 paper (substantive-content addendum noting Mathlib upstream merge).

**Risk axes.**
- Substantive content lift complexity.
- Mathlib review cadence.
- PR-scope decisions.

### Waves 2c-2g — Remaining I3 module PRs ⏳ NOT STARTED

Same pattern as Wave 2b applied to each remaining I3 module group. Wave-by-wave skeleton:

- **Wave 2c:** `QuadraticVariation` + `Semimartingale` substantive lift + Mathlib PR.
- **Wave 2d:** `ItoIsometry` + `ItoLemma` + `Novikov` substantive lift + Mathlib PR. **Note:** ItoLemma may decompose into 2-3 Mathlib PRs per `papers/I3/paper_draft.tex` §3 "ItoLemma likely for two or three PRs given its larger surface area."
- **Wave 2e:** `CramerIID` substantive lift + Mathlib PR (LDP track entry).
- **Wave 2f:** `Sanov` + `Contraction` substantive lift + Mathlib PR.
- **Wave 2g:** `CramerLowerBound` + `Varadhan` + `LDPCompatibleSKEFT` substantive lift + Mathlib PR. **Note:** `LDPCompatibleSKEFT` is a typeclass cross-bridge to the SK-EFT-Hawking program; substrate scout at Wave 2g.1 dispositive on whether Mathlib wants it (likely yes as a generic LDP-compatibility class) or whether it stays project-local.

Each wave follows the Wave 2b sub-wave decomposition pattern (substantive content lift → Mathlib-style polish → PR open + review cycle → I3 paper update).

**Cumulative outcome:** if all 6-9 PRs merge, Mathlib4 gains Itô calculus + LDP infrastructure. If some stall at maintainer discretion, Phase 6s ships substantive lift in the SK-EFT-Hawking project repo with PR-state annotations.

---

## User authorization gates — consolidated

| Wave | Authorization point | Authorization required for | Status |
|---|---|---|---|
| **Wave 1a** PhysLean coordination | Engaging PhysLean Zulip / coordinating with community | YES — community engagement is a user-action | 🔒 **PENDING** |
| **Wave 1b** New-bundle creation | If KMS-EFT axiomatic ships as a distinct bundle | YES — new-bundle creation requires `PAPER_STRATEGY.md` update | 🔒 **PENDING** Wave 1b close |
| **Wave 2a** Mathlib PR campaign authorization | The 6-9 Mathlib PR campaign as a whole | **YES — Mathlib campaign authorization is the gating decision for Track 2** | 🔒 **PENDING** Wave 2a close |

---

## Phase 6s-internal further-deferred tracks

- **PhysLean SymTFT contribution** — could extend Phase 6r's SymTFT formalization upstream to PhysLean. Consider after Phase 6r 8 waves close.
- **Mathlib4 categorical infrastructure contribution** — could lift portions of Phase 5b-5p categorical chain (paper11 quantum group, paper14 MTC) to Mathlib4 mainline. Consider after Phase 6s Track 2 closes.

---

## Cross-references

- `docs/roadmaps/Phase6o_Roadmap.md` Wave 3b (I3 predicate-substrate work) — Phase 6s Track 2 is the substantive-lift continuation.
- `docs/roadmaps/Phase6o_Roadmap.md` Wave 1c (NO-GO writeup) — Phase 6s Track 1 is one positive-result response.
- `docs/roadmaps/Phase6p_Roadmap.md` — sibling phase (fault-tolerant QC).
- `docs/roadmaps/Phase6q_Roadmap.md` — sibling phase (DKM transport bootstrap; parallel positive-result effort).
- `docs/roadmaps/Phase6r_Roadmap.md` — sibling phase (SymTFT formalization).
- `memory/project_phase_6p6q6r6s_planning.md` — strategic entry-state brief; **explicit caveat that Track 2 is mostly community-citizenship work with marginal in-project benefit.**
- `memory/feedback_loe_calibration.md` — pipeline speed calibration; **explicit note that this does NOT apply to Mathlib review cycles**.
- `memory/project_2026_05_12_first_claim_close.md` — primacy-claim discipline; applies to Mathlib PR descriptions.
- `papers/I3/paper_draft.tex` §3 — explicit upstream-PR coordination plan.
- `lean/SKEFTHawking/Itô/*.lean` + `lean/SKEFTHawking/LDP/*.lean` — Track 2 substrate.
- Mathlib4 repository — Track 2 destination.

---

*Created 2026-05-12 at Phase 6o close. Per-wave decomposition + 3-question template + module decomposition + bundle absorption + risk axes. Updates atomically as waves close.*

---

## Sessions log

*Empty — Phase 6s has not yet been dispatched. **Note:** Track 2 is gated on Wave 2a Mathlib PR campaign user-authorization. Track 1 is gated on Douglas-Hoback-Mei-Nissim paper availability + PhysLean coordination state.*
