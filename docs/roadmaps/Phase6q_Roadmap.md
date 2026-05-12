# Phase 6q: Drude-Kadanoff-Martin Transport Bootstrap on SK-EFT-Hawking Horizon Transport

## Technical Roadmap — May 2026

*Prepared 2026-05-12 at Phase 6o close. Sources: planning conversation 2026-05-12 (4-phase scoping pass); user direction "find good fits for our pipeline & investigate directions that may lead to strengthening of the program and investigations that could plausibly make significant contributions to the physics/math/qc communities, and/or contribute meaningful no-gos"; Phase 6o Wave 1c NO-GO writeup at `temporary/working-docs/phase6o/wave_1c_NO-GO_writeup.md` (the trigger result); `Lit-Search/_Exploratory/Modular : Conformal Bootstrap as a Uniqueness Argument...md` §3 (the substrate); primary source Chowdhury-Hartnoll-Hebbar-Khondaker arXiv:2509.18255 (Drude-Kadanoff-Martin transport bootstrap).*

**Trigger condition:** Phase 6q opens at Phase 6o close. The trigger is Phase 6o Wave 1c's NO-GO finding: *"dissipative SK-EFT bootstrap can't produce uniqueness with current axioms."* Phase 6q is the **positive-result response** — apply the Chowdhury-Hartnoll-style transport bootstrap (arXiv:2509.18255) to SK-EFT-Hawking horizon transport, replacing some of the NO-GO'd axioms. Outcome is intentionally **bimodal**: a positive uniqueness result (the program produces a transport-bootstrap-as-uniqueness companion paper to Wave 1c's NO-GO) OR a sharpened second NO-GO (transport-bootstrap-with-DKM-axioms-also-fails) — both publishable.

**Status (2026-05-12, Phase 6q stub):** **Roadmap stub committed at Track / Wave level**. Two Tracks, five Waves.

**Project rule (carried from Phase 6n/6o; user direction reaffirmed 2026-05-12):** **No PM / time / phase-cost estimates** anywhere in this roadmap. **No manuscript drafting at this phase** — Phase 6q stays at math/physics/Lean-substrate / infrastructure level. **No Mathlib PR drafts at this phase.**

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
>
> 1. **Mandatory project bootstrap** per `CLAUDE.md` Mandatory References list.
> 2. **Read `Phase6n_Roadmap.md` Wave 2c + `Phase6o_Roadmap.md` Wave 1c end-to-end** — Phase 6q consumes both as substrate.
> 3. **Read this roadmap end-to-end** before claiming any wave assignment.
> 4. **Read the planning brief `memory/project_phase_6p6q6r6s_planning.md`** for entry-state context.
> 5. **Critical predecessor modules + literature — read source directly:**
>    - **Phase 6o Wave 1c NO-GO memo:** `temporary/working-docs/phase6o/wave_1c_NO-GO_writeup.md` — the trigger result. Identifies three structural obstructions (unitarity → KMS replacement breaks EFT-positivity; crossing has no doubled-contour analog; SDP feasibility breaks on complex contour). Identifies the axiom replacement set required for a positive result. **Phase 6q starts where Phase 6o Wave 1c ended.**
>    - **Primary source Chowdhury-Hartnoll-Hebbar-Khondaker arXiv:2509.18255** — the DKM transport bootstrap. The cleanest existing example of a bootstrap on a dissipative correlator.
>    - **Akyuz-Penco arXiv:2508.18346** — SK EFT charge transport (current state-of-the-art statement of dissipative axioms; the axioms Phase 6q replaces).
>    - **Crossley-Glorioso-Liu arXiv:1511.03646** — SK-EFT axioms (the foundational substrate).
>    - **arXiv:2511.08560** — Bootstrapping Euclidean Two-point Correlators (KMS bootstrap on QM, not 4D field theory; provides KMS-bootstrap framework).
>    - **Phase 6n Wave 2c Crooks-on-analog-Hawking trajectory measure:** `lean/SKEFTHawking/CrooksAnalogHawking/*.lean` — substrate for the SK-EFT-Hawking-specific specialization in Track 2.
>    - **Phase 6n Wave 2a Glorioso-Liu monotonicity:** `lean/SKEFTHawking/GloriosoLiu/*.lean` — substrate for the dissipative monotonicity axiom that any new bootstrap must respect.
>    - **`Lit-Search/_Exploratory/Modular : Conformal Bootstrap as a Uniqueness Argument...md` §3** — substrate for the bootstrap-substrate enumeration.
> 6. **`LATE_PHASE6_ABSORPTION_PROTOCOL.md` — load before any bundle-touching work.**
> 7. **Apply preemptive-strengthening checklist** + **primacy-claim discipline** per `memory/project_2026_05_12_first_claim_close.md`.
> 8. **Do not delegate Lean theorem proving to subagents.** MCP loop default; Aristotle is fallback. Explore-agent substrate scouts authorized.
> 9. **No PM / time estimates anywhere** — by user direction.
> 10. **No manuscript drafting at this phase.** Bundle absorption deferred per Phase 6n Session-5 convention.

---

## Wave catalog — Shape D (2 Tracks × 5 Waves)

Five waves across two Tracks. Track 1 = transport-bootstrap axiom replacement (the generic machinery applied to SK-EFT). Track 2 = SK-EFT-Hawking specialization + horizon transport application.

**Status legend:**
- ✅ **SHIPPED** — Lean / numerical / memo deliverables committed; bundle absorption deferred.
- 🟡 **IN-PROGRESS** — partial deliverables shipped.
- 📝 **WORKING DOC** — Stage-1 substrate-analysis or audit draft exists; no Lean yet.
- ⏳ **NOT STARTED** — substrate ready; awaiting dispatch.

| Wave | Codename | Status | Bundle absorption | Branch | User-auth gate |
|---|---|---|---|---|---|
| **Track 1 — DKM transport bootstrap axiom replacement** | | | | | |
| **Wave 1a** | DKM substrate analysis + axiom-replacement decision | ⏳ NOT STARTED | D1 or L2/D5 (TBD Wave 2c) — DEFERRED | **D.2** | none |
| **Wave 1b** | Lean substrate for DKM transport-bootstrap axioms | ⏳ NOT STARTED | D1 or L2/D5 — DEFERRED | **D.2** | none |
| **Wave 1c** | Semi-definite programming structure + linear-functional substrate | ⏳ NOT STARTED | D1 or L2/D5 — DEFERRED | **D.2** | none |
| **Track 2 — SK-EFT-Hawking specialization + horizon transport** | | | | | |
| **Wave 2a** | SK-EFT-Hawking-specific specialization of DKM bootstrap | ⏳ NOT STARTED | D1 (transport coefficients) — DEFERRED | **D.2** | none |
| **Wave 2b** | Horizon transport coefficient bootstrap (positive result OR second NO-GO) | ⏳ NOT STARTED | D1 + L2 or D5 (placement at Wave 2c) — DEFERRED | **D.2** | none |
| **Wave 2c** | Closing positioning + bundle-placement decision (L2 vs D5) + flagship-F integration | ⏳ NOT STARTED | L2 or D5 + F flagship — DEFERRED | **D.2** | none |

**Wave dependencies:**
- Wave 1a (DKM substrate) is independent; opens the phase.
- Wave 1b depends on Wave 1a.
- Wave 1c depends on Wave 1b.
- Wave 2a depends on Wave 1c (the SK-EFT specialization needs the full DKM bootstrap substrate in place).
- Wave 2b depends on Wave 2a.
- Wave 2c depends on Wave 2b (final placement decision needs the outcome).

**Coherent sub-narrative.** Track 1 (Waves 1a-1c) builds the **generic transport-bootstrap machinery** in Lean: axioms (replacing Wave 1c's NO-GO'd axiom set), SDP / linear-functional structure, and the bootstrap framework. Track 2 (Waves 2a-2c) specializes to SK-EFT-Hawking-horizon transport — the program's substrate. The outcome at Wave 2b is intentionally **bimodal**:

- **Positive case:** the DKM-axiom-set bootstrap produces a uniqueness statement on horizon transport coefficients (the analog of Drude weight, conductivity sum rules) for the SK-EFT-Hawking substrate. This is a substantial positive companion to the Phase 6o Wave 1c NO-GO writeup.
- **NO-GO case:** the DKM-axiom-set bootstrap also fails to produce uniqueness on the SK-EFT-Hawking substrate (despite succeeding on the CHHK textbook problem). This is a sharpened second NO-GO; identifies precisely which DKM axioms break for the SK-EFT-Hawking specialization.

Either outcome closes a substantial loop opened by Phase 6o Wave 1c.

**Recommended next-up order:**

1. **Wave 1a** DKM substrate analysis (substrate scout on CHHK paper's axiom set; predicate enumeration; SDP structure).
2. **Wave 1b** Lean substrate for DKM axioms.
3. **Wave 1c** SDP + linear-functional substrate.
4. **Wave 2a** SK-EFT-Hawking specialization.
5. **Wave 2b** Horizon transport bootstrap — bimodal outcome.
6. **Wave 2c** Closing positioning + bundle placement.

**Pre-Phase-7 bundle absorption gate:** all 5 Phase 6q Waves close → unified Phase 6q → Phase 7 absorption pass. L2 vs D5 placement decision at Wave 2c close (matches Phase 6o Wave 1c convention).

---

## Wave 1a — DKM substrate analysis + axiom-replacement decision ⏳ NOT STARTED

**Sub-wave decomposition (proposed):**

- **Wave 1a.1 (deep-research dispatch + substrate analysis):** read Chowdhury-Hartnoll-Hebbar-Khondaker arXiv:2509.18255 end-to-end. Extract the explicit axiom set: (a) Drude-Kadanoff-Martin transport-correlator structure (frequency-momentum dependence of $G_{JJ}$); (b) static-limit constraints (Drude weight sum rule); (c) high-frequency-limit constraints (operator-product-expansion constraints); (d) positivity constraints (real part non-negative); (e) Kramers-Kronig analytic structure; (f) symmetry constraints (parity, time-reversal). Compare with Phase 6o Wave 1c NO-GO axiom set; identify which CGL/Akyuz-Penco axioms map cleanly to DKM axioms and which need replacement. Working doc at `temporary/working-docs/phase6q/wave_1a_DKM_substrate.md`.
- **Wave 1a.2 (Lean predicate-substrate scaffolding):** `lean/SKEFTHawking/DKMBootstrap/Predicates.lean` — `IsDKMTransportCorrelator G` Prop bundling the 6 axiom families above; `DrudeWeight G` real-valued substrate field; `OPECoefficients G` substrate fields encoding the high-frequency operator-product expansion; substantive non-vacuity witness on a textbook example (free-fermion conductivity or Drude metal — both have known closed-form solutions in the CHHK paper).

**Three-question template:**

- *Integrates with:* Phase 6o Wave 1c NO-GO writeup (the trigger); Crossley-Glorioso-Liu SK-EFT axioms; Akyuz-Penco SK-EFT charge transport; Phase 6n Wave 2a Glorioso-Liu monotonicity; Mathlib4 complex-analysis infrastructure (Kramers-Kronig is essentially Cauchy integral formula).
- *New constraint adds:* an explicit Lean substrate for the DKM transport-bootstrap axioms, ready for specialization to the SK-EFT-Hawking horizon transport problem. Substrate-data level operationalization.
- *Tension surfaces:* (i) which of the 6 axiom families is the cleanest to encode in Lean — Kramers-Kronig and positivity have clean Mathlib analogs; OPE-coefficient axiom is more substantive; sum-rule constraints map cleanly to identity theorems on `∫ G(ω) dω`; (ii) whether the Mathlib4 complex-analysis substrate is adequate (Mathlib has the Cauchy integral formula for `ℂ → ℂ`; has the residue theorem; has Bochner-Lebesgue integration); (iii) the working doc's principal output is the explicit decision on whether the substantive content lives at predicate-substrate level (mirroring I3's choice for Itô/LDP) or at substantive theorem level — the planning conversation's calibration is "be aggressive on substantive content where Mathlib substrate exists; default to predicate substrate where Mathlib gap is real."

**Substrate.** Chowdhury-Hartnoll-Hebbar-Khondaker arXiv:2509.18255; Crossley-Glorioso-Liu arXiv:1511.03646; Akyuz-Penco arXiv:2508.18346; arXiv:2511.08560 KMS bootstrap; Mathlib4 complex-analysis infrastructure (Cauchy integral formula, residue theorem, Bochner-Lebesgue integration).

**Module decomposition (Lean):**
```
SKEFTHawking/DKMBootstrap/
  Predicates.lean       -- IsDKMTransportCorrelator predicate bundling 6 axiom families
  -- (Wave 1b will add:)
  -- AxiomSet.lean      -- Explicit Lean encodings of CHHK axioms
  -- KMSConsistency.lean -- KMS-replaces-unitarity content
```

**Bundle absorption.** D.2 candidate; final placement decision at Wave 2c.

**Risk axes.**
- Mathlib4 complex-analysis substrate adequacy (Cauchy integral formula present; Hilbert transform / Sokhotski-Plemelj less mature).
- DKM bootstrap's reliance on numerical SDP (the CHHK paper uses SDPB to compute bounds) — Lean cannot execute SDP solvers; substantive content goes through predicate-substrate level with the SDP-solving step deferred to Python tooling.
- Axiom-replacement decision is the substantive entry-point of the phase; should not be pre-judged.

---

## Wave 1b — Lean substrate for DKM transport-bootstrap axioms ⏳ NOT STARTED

**Sub-wave decomposition (proposed):**

- **Wave 1b.1 (axiom set Lean encoding):** `lean/SKEFTHawking/DKMBootstrap/AxiomSet.lean` — explicit Lean encodings of the 6 CHHK axioms (per Wave 1a.1 enumeration) as Props bundled in `IsDKMAxiomSet`.
- **Wave 1b.2 (KMS replaces unitarity):** `lean/SKEFTHawking/DKMBootstrap/KMSConsistency.lean` — substantive structural lemma: KMS condition + dynamical-KMS symmetry replaces Hermitian-Hamiltonian-unitarity for the bootstrap inequalities. Cross-bridge to Phase 6n Wave 2a Glorioso-Liu monotonicity.
- **Wave 1b.3 (no crossing analog):** `lean/SKEFTHawking/DKMBootstrap/NoCrossing.lean` — formal Lean statement that the bootstrap inequalities do not invoke crossing symmetry (the Wave 1c NO-GO writeup identified crossing's absence as one of three obstructions; DKM bootstrap bypasses by using sum rules + OPE instead of crossing).

**Three-question template:**

- *Integrates with:* Wave 1a substrate; Phase 6n Wave 2a Glorioso-Liu monotonicity; CGL SK-EFT axioms; Akyuz-Penco; arXiv:2511.08560 KMS bootstrap.
- *New constraint adds:* an explicit Lean encoding of the DKM bootstrap axiom set, ready for SK-EFT specialization in Track 2. The key substantive structural content is the KMS-replaces-unitarity lemma at Wave 1b.2 — this is the load-bearing axiom-replacement of the phase.
- *Tension surfaces:* (i) substantive vs. predicate-substrate level of the KMS-replaces-unitarity lemma (Wave 1a.2 dispositive); (ii) whether the "no crossing" obstruction admits a clean structural statement in Lean — possible YES at predicate level; (iii) which Phase 6n substrate gets cross-bridged (Glorioso-Liu monotonicity at minimum; possibly Phase 6n Wave 2c Crooks-on-analog-Hawking depending on Wave 2a specialization choice).

**Substrate.** Wave 1a substrate; Phase 6n Wave 2a + 2c Lean modules.

**Bundle absorption.** D.2 — final placement at Wave 2c.

**Risk axes.**
- KMS-replaces-unitarity content is structurally subtle — substrate scout at Wave 1a.1 dispositive on tractable formalization level.

---

## Wave 1c — Semi-definite programming structure + linear-functional substrate ⏳ NOT STARTED

**Sub-wave decomposition (proposed):**

- **Wave 1c.1 (SDP-feasibility-on-complex-contour Lean substrate):** `lean/SKEFTHawking/DKMBootstrap/SDPStructure.lean` — Lean substrate for the SDP-feasibility-on-complex-contour content (the Wave 1c NO-GO writeup identified complex-contour SDP as the third structural obstruction; DKM bootstrap bypasses by using real-frequency constraints + analytic continuation). `IsDKMFeasibleSDP F G` Prop on (F, G) pairs of linear functional and correlator. Predicate-substrate operationalization (the actual SDP solving is downstream Python).
- **Wave 1c.2 (linear-functional substrate):** `lean/SKEFTHawking/DKMBootstrap/LinearFunctionals.lean` — substantive lemma: the set of linear functionals satisfying the DKM axioms forms a convex cone (essential for the bootstrap structure). Substrate scout dispositive on whether to ship the substantive convex-cone lemma or predicate-substrate operationalization.
- **Wave 1c.3 (cross-bridge to Phase 6n Wave 2c IsLDPRateFunction):** `lean/SKEFTHawking/DKMBootstrap/LDPBridge.lean` — substantive cross-bridge: under appropriate conditions, the DKM bootstrap's positivity constraint reduces to an LDP-rate-function condition. Cross-bridge to Phase 6n Wave 2c.5c+ `IsLDPRateFunction` class.

**Three-question template:**

- *Integrates with:* Wave 1b substrate; Phase 6n Wave 2c LDP infrastructure; Mathlib4 convex analysis (cone structures, convex set theorems).
- *New constraint adds:* Lean substrate for SDP feasibility + linear-functional convex-cone structure, ready for SK-EFT specialization.
- *Tension surfaces:* (i) Mathlib4 convex analysis is mature enough for cone structures; (ii) substantive convex-cone lemma at Wave 1c.2 is substantively new content (DKM paper doesn't ship a Lean version of this); (iii) LDP cross-bridge at Wave 1c.3 is genuinely new content — connects the DKM transport bootstrap to the program's existing LDP substrate.

**Substrate.** Wave 1b substrate; Phase 6n Wave 2c LDP modules; Mathlib4 convex analysis.

**Bundle absorption.** D.2 — final placement at Wave 2c.

**Risk axes.**
- SDP-feasibility content is mathematically delicate (interior-point methods don't formalize naturally; the Lean substrate handles existence-of-SDP-solution rather than algorithmic solution).
- Cross-bridge to IsLDPRateFunction may surface non-trivial substantive content (could be the highest-leverage cross-bridge of the phase).

---

## Wave 2a — SK-EFT-Hawking-specific specialization of DKM bootstrap ⏳ NOT STARTED

**Sub-wave decomposition (proposed):**

- **Wave 2a.1 (substrate analysis + working doc):** identify which DKM axioms specialize cleanly to the SK-EFT-Hawking horizon transport problem and which need modification (e.g., the static-limit constraint becomes the Hawking-temperature constraint; the high-frequency constraint becomes the UV-cutoff constraint at the BEC Bogoliubov scale). Working doc at `temporary/working-docs/phase6q/wave_2a_SKEFT_specialization.md`.
- **Wave 2a.2 (Lean SK-EFT-Hawking specialization):** `lean/SKEFTHawking/DKMBootstrap/SKEFTSpecialization.lean` — explicit specialization of the Wave 1b-1c substrate to the SK-EFT-Hawking horizon transport problem. Cross-bridge to Phase 6n Wave 2c Crooks-on-analog-Hawking trajectory measure (substantive content: the transport correlator on the analog-Hawking horizon is a thermal-state correlator at the Hawking temperature; this connects the DKM bootstrap to the program's existing Crooks/FDT/KMS infrastructure).
- **Wave 2a.3 (cross-bridge to E1 polariton + E2 graphene):** `lean/SKEFTHawking/DKMBootstrap/E1E2CrossBridge.lean` — substrate-level cross-bridge connecting the Wave 2a.2 horizon transport bootstrap to E1 polariton-Hawking + E2 graphene-Dirac-fluid substrates. Substantive content: the DKM bootstrap specializes differently for the three platforms (BEC, polariton, graphene) — substantive structural finding either way.

**Three-question template:**

- *Integrates with:* Track 1 substrate; Phase 6n Wave 2c Crooks-on-analog-Hawking; existing analog-Hawking Lean modules (`AnalogHawking/*.lean`); paper1/paper2/paper3 (D1 bundle's SK-EFT-Hawking content); paper16_graphene (E2); E1 polariton.
- *New constraint adds:* the program's first specialization of the DKM transport bootstrap to its native SK-EFT-Hawking horizon transport problem. The specialization either succeeds (Wave 2b ships positive uniqueness result) or surfaces obstructions (Wave 2b ships sharpened NO-GO).
- *Tension surfaces:* (i) which of the three program substrates (BEC, polariton, graphene) admits the cleanest DKM specialization — substrate scout dispositive; (ii) whether the horizon temperature scale + UV cutoff scale + dissipation scale form a hierarchy that the DKM bootstrap can navigate; (iii) the analog-Hawking-specific KMS condition (Hawking-temperature thermal state) may or may not be the right KMS condition for the DKM-bootstrap-replaces-unitarity content — a substantive structural sub-question.

**Substrate.** Track 1 substrate; Phase 6n Wave 2c modules; analog-Hawking Lean infrastructure; D1/E1/E2 paper drafts.

**Bundle absorption.** D.2 additive into D1 (transport coefficients section) + E1/E2 cross-bridge.

**Risk axes.**
- Specialization may surface multiple non-trivial obstructions — substantive structural finding either direction.
- Three-platform specialization (BEC vs polariton vs graphene) — substrate scout picks one for initial wave; others as follow-up.
- Cross-bridge to existing analog-Hawking Lean substrate may surface alignment / misalignment with Wave 1c LDP bridge.

---

## Wave 2b — Horizon transport coefficient bootstrap ⏳ NOT STARTED

**This is the substantive theorem wave. Bimodal outcome.**

**Sub-wave decomposition (proposed):**

- **Wave 2b.1 (substantive bootstrap-as-uniqueness theorem at predicate-substrate level):** `lean/SKEFTHawking/DKMBootstrap/HorizonTransportBootstrap.lean` — the bootstrap-as-uniqueness statement for SK-EFT-Hawking horizon transport coefficients. Substantive content dispositive per Wave 2a.2 outcome — either a uniqueness theorem (positive result) or a sharpened NO-GO (the DKM bootstrap also fails on the SK-EFT-Hawking substrate for explicit substantively-identified obstructions).
- **Wave 2b.2 (concrete witness on a specific transport coefficient):** explicit theorem on a specific transport coefficient (e.g., horizon shear viscosity / entropy density ratio, or the dissipative bulk transport coefficient $\zeta$): bootstrap bounds the value to a specific interval (positive result) or fails to bound it (NO-GO). Substantive content depends on Wave 2b.1 outcome.
- **Wave 2b.3 (cross-bridge to D1 Hawking temperature analytic):** substantive cross-bridge connecting the Wave 2b.1-2 transport-bootstrap result to the program's existing D1 Hawking temperature analytic substrate. Substantive content: if positive, the bootstrap bounds + the Hawking-temperature analytic combine to constrain the SK-EFT Wilson coefficient ratios in D1; if NO-GO, the cross-bridge identifies the specific Wilson coefficient ratio that the DKM bootstrap fails to bound.

**Three-question template:**

- *Integrates with:* Track 1 substrate; Wave 2a SK-EFT specialization; D1 paper drafts (paper1, paper2, paper3 SK-EFT-Hawking content); Phase 6n Wave 2c Crooks-on-analog-Hawking trajectory measure.
- *New constraint adds:* a substantive uniqueness-or-NO-GO result on SK-EFT-Hawking horizon transport coefficients. **Bimodal outcome by design.**
- *Tension surfaces:* (i) the substantive vs. predicate-substrate level of the theorem statement is dispositive at Wave 2a.2; (ii) the bimodal outcome means the wave can ship in either direction — the Phase 6q success criterion is "publishable result, positive or negative" not "positive result" specifically; (iii) the bootstrap-numerics step (SDPB-style optimization) happens outside Lean — the Lean content is the structural framework + bounds-have-the-claimed-properties theorems; the numerical bound computation is Python tooling.

**Substrate.** All prior Phase 6q waves; D1 paper drafts; Phase 6n Wave 2c modules; SDPB-style Python tooling (if positive result requires numerical bounds).

**Bundle absorption.** D.2 additive into D1 (substantive new section) + L2 or D5 (positioning paper, similar to Phase 6o Wave 1c NO-GO companion).

**Risk axes.**
- **Bimodal outcome by design** — risk is not that the wave fails; risk is that the wave's outcome is ambiguous between positive and NO-GO (in which case Wave 2b.3 cross-bridge identifies the substantive sub-question that needs additional substrate work).
- SDPB-style numerical bounds happen outside Lean — the Lean content is structural framework only.
- Specific transport coefficient choice (Wave 2b.2) — substrate scout picks one; others as follow-up.

---

## Wave 2c — Closing positioning + bundle-placement decision + flagship-F integration ⏳ NOT STARTED

**Sub-wave decomposition (proposed):**

- **Wave 2c.1 (L2 vs D5 placement decision):** working doc identifying which bundle the Phase 6q positioning paper lives in. Same convention as Phase 6o Wave 1c (L2 vs D5; deferred to Wave 1c.3 close). Decision criteria: (a) is the Phase 6q result a positive uniqueness theorem (probably L2 — companion to L1 GW170817 paper) or a sharpened NO-GO (probably D5 — companion to dark-sector NO-GO landscape)?; (b) does it absorb cleanly into the existing structure of either bundle?
- **Wave 2c.2 (closing positioning section):** short paragraph in the chosen bundle identifying where Phase 6q sits in the broader "what is and is not in the substrate" narrative. Bound the writeup explicitly per Phase 6n Session-5 user direction on hedging discipline; flag the Wave 2b outcome (positive or NO-GO) and identify what follow-up work would close any remaining loops.
- **Wave 2c.3 (flagship-F integration):** flagship F cross-bridge — short paragraph in F's substrate-narrative section identifying the Phase 6q result. If positive: "the program's SK-EFT-Hawking substrate admits a transport-bootstrap-as-uniqueness statement." If NO-GO: "the program's SK-EFT-Hawking substrate is not fully constrained by the DKM transport bootstrap; the remaining obstructions are X, Y, Z."

**Three-question template:**

- *Integrates with:* L2 + D5 paper drafts; F flagship; bundle architecture; all prior Phase 6q waves.
- *New constraint adds:* bundle-placement decision + flagship-F positioning of the Phase 6q result.
- *Tension surfaces:* (i) the L2 vs D5 decision depends substantively on whether Wave 2b shipped positive or NO-GO; (ii) flagship-F positioning depends substantively on the Wave 2b outcome.

**Substrate.** All prior Phase 6q waves.

**Bundle absorption.** D.2 into L2 OR D5 + F flagship positioning.

**Risk axes.**
- L2 vs D5 decision should not be pre-judged; substantively driven by Wave 2b outcome.

---

## User authorization gates — consolidated

| Wave | Authorization point | Authorization required for | Status |
|---|---|---|---|
| **Wave 2c** L2 vs D5 placement | Final placement of Phase 6q closing-positioning paper | none (placement-decision; no architecture change) | n/a |

---

## Phase 6r+ preview (related deferred tracks)

The remaining 3 phases (6p, 6r, 6s) are independent of Phase 6q substrate; can run in parallel.

---

## Cross-references

- `docs/roadmaps/Phase6o_Roadmap.md` Wave 1c — the trigger NO-GO writeup that Phase 6q responds to.
- `docs/roadmaps/Phase6n_Roadmap.md` Wave 2a + Wave 2c — substrate dependencies.
- `docs/roadmaps/Phase6p_Roadmap.md` — sibling phase (fault-tolerant QC).
- `docs/roadmaps/Phase6r_Roadmap.md` — sibling phase (SymTFT formalization).
- `docs/roadmaps/Phase6s_Roadmap.md` — sibling phase (1c bootstrap + I3 substantive lift).
- `memory/project_phase_6p6q6r6s_planning.md` — strategic entry-state brief.
- `memory/feedback_loe_calibration.md` — pipeline speed calibration.
- `temporary/working-docs/phase6o/wave_1c_NO-GO_writeup.md` — the trigger result.
- `Lit-Search/_Exploratory/Modular : Conformal Bootstrap as a Uniqueness Argument...md` — substrate.
- arXiv:2509.18255 Chowdhury-Hartnoll-Hebbar-Khondaker — primary source.
- arXiv:2508.18346 Akyuz-Penco — SK EFT charge transport substrate.
- arXiv:2511.08560 KMS bootstrap on QM — KMS-bootstrap framework substrate.
- arXiv:1511.03646 Crossley-Glorioso-Liu — SK-EFT axiom substrate.

---

*Created 2026-05-12 at Phase 6o close. Per-wave decomposition + 3-question template + module decomposition + bundle absorption + risk axes. Updates atomically as waves close.*

---

## Sessions log

*Empty — Phase 6q has not yet been dispatched.*
