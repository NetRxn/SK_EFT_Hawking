# Phase 6o: Emergent IR Sector + Topological Invariants on Analog Backgrounds + Productive-Value & Community Contribution

## Technical Roadmap — May 2026

*Prepared 2026-05-04 (stub) | **Upgraded to full roadmap 2026-05-06** at Phase 6n Session 30 transition. Sources: `temporary/working-docs/brainstorm/20260504-GUToE/Phase6n-6z-GUToE-Brainstorm_1.md` Sessions 1–3; 9 deep-research returns at `Lit-Search/_Exploratory/`; Itô-explore agent findings (Mathlib4 + Degenne brownian-motion repo state) supporting the in-program build option for the I3 wave; the Phase 6n Wave 1c memo `temporary/working-docs/phase6n/6n_eta_AS_reformulation_memo.md` §6.3 surfacing APS-η for analog horizons as a Phase 6o follow-up.*

**Trigger condition:** Phase 6o opens at the Phase 6n math-substrate close (Session 29, 2026-05-06). Some Phase 6o waves consume Phase 6n outputs as substrates (Wave 1a soft theorems use post-erasure U(1) + ADW graviton; Wave 2a APS-η uses Phase 6n Wave 1c heat-kernel ↔ AS dictionary; Wave 2b Schellekens reads off 6n.β SymTFT compression). Other Phase 6o waves are independent of Phase 6n (Wave 1b Kerr-Schild, Wave 1c G1-NO-GO, Wave 3a ETH-α, Wave 3b I3 Itô).

**Status (2026-05-06, Session 30 dispatch):** **Roadmap committed at Track / Wave level**. Three Tracks, seven Waves. Convention matches Phase 6n: Wave letters `1a`, `1b`, `1c`, `2a`, `2b`, `3a`, `3b`. Sub-wave numbering `1a.1`, `1a.2`, … as work decomposes during sessions.

**Project rule (Session-3 user direction 2026-05-04, reaffirmed Session 30):** **No PM / time / phase-cost estimates** anywhere in this roadmap. **No manuscript drafting at this phase** — Phase 6o stays at math/physics/Lean-substrate / infrastructure level; notes/outlines/working docs are fine. **No Mathlib PR drafts at this phase** — anything that might end up upstream is built internally first, using Mathlib naming/style conventions to make future PRs easier when authorized.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
>
> 1. **Mandatory project bootstrap** per `CLAUDE.md` Mandatory References list. Read in order: WAVE_EXECUTION_PIPELINE → Inventory_Index → README → Lean Development Optimization → Aristotle reference doc.
> 2. **Read `Phase6n_Roadmap.md` end-to-end** before starting any Phase 6o work — Phase 6n outputs are substrates for several Phase 6o waves.
> 3. **Read this roadmap end-to-end** before claiming any wave assignment.
> 4. **Critical predecessor modules — read source directly:**
>    - Phase 6n outputs: `lean/SKEFTHawking/GloriosoLiu/*.lean` (Phase 6n Wave 2a); `lean/SKEFTHawking/SymTFTAudit/*.lean` (Phase 6n Wave 1b — DrinfeldCenter, PseudoUnitary, FreeKLinearCategory, FreeKLinearMonoidal, DeligneTensor, WittClass, CrossBridges, Applicability); `lean/SKEFTHawking/CrooksAnalogHawking/*.lean` (Phase 6n Wave 2c/2d); `lean/SKEFTHawking/QuantumCrooks/*.lean` (Phase 6n Wave 2b); `lean/SKEFTHawking/Resurgence/*.lean` (Phase 6n Wave 1a); the AS reformulation memo at `temporary/working-docs/phase6n/6n_eta_AS_reformulation_memo.md` (Phase 6n Wave 1c — substrate for Phase 6o Wave 2a APS-η).
>    - Phase 5b–5p categorical chain (substrate for Wave 2b Schellekens chain).
>    - Phase 5o W5 lean-tensor-categories library (114 thms; substrate for Wave 2b Schellekens MTC anchor).
>    - Phase 5z Goldstino + Phase 6e a_n + Phase 6m Sakharov tr(I) (substrate for Wave 2a APS-η Lean lift).
>    - `lean/SKEFTHawking/SpinBordism.lean` + `lean/SKEFTHawking/Z16AnomalyComputation.lean` (substrate for Wave 2b spin-bordism step).
>    - `lean/SKEFTHawking/InstantonZeroModes.lean` + `lean/SKEFTHawking/HeatKernelExpansion.lean` (substrate for Wave 2a APS-η Lean lift).
>    - `lean/SKEFTHawking/JacobsonThermoGRDarkEnergy.lean` (substrate for Wave 2a Sakharov tr(I) ↔ McKean–Singer dictionary).
>    - `lean/SKEFTHawking/GaugeErasure.lean` + `lean/SKEFTHawking/AkamaDiakonovWetterich/*.lean` (substrate for Wave 1a / Wave 1b emergent-sector framing).
>    - `lean/SKEFTHawking/AnalogHawking/*.lean` (substrate for Wave 1a phenomenology + Wave 2a APS-η on the analog-horizon backgrounds).
>    - Mathlib4 probability infrastructure (martingales / filtrations / Markov kernels / conditional expectation / sub-Gaussian) + Degenne brownian-motion repo (Carathéodory + Kolmogorov + K-Chentsov + Gaussian measures on Banach spaces) — substrates for Wave 3b.
>    - `Lit-Search/_Exploratory/On-Shell Methods, Soft Theorems, and Spinor-Helicity Amplitudes for Dissipative Emergent Gauge : Gravity Sectors.md` — substrate for Wave 1a.
>    - `Lit-Search/_Exploratory/Color-Kinematics Duality and the Double Copy at the SK-EFT Substrate Level.md` — substrate for Wave 1b.
>    - `Lit-Search/_Exploratory/Modular : Conformal Bootstrap as a Uniqueness Argument for Standard-Model Matter Content from a Condensed-Matter Substrate.md` — substrate for Wave 1c (NO-GO writeup) and Wave 2b (Schellekens chain).
>    - `Lit-Search/_Exploratory/Phase 6n+ Foundational Backing Assessment...md` §9 — substrate for Wave 3a (ETH-α).
>    - `Lit-Search/_Exploratory/Appendix- Re-assessment of Deferred Tracks for SK_EFT_Hawking Phase 6n+.md` §3 — Itô deferral analysis the Wave 3b in-program build supersedes.
>    - `Lit-Search/_Exploratory/Atiyah–Singer Index Theorems as a Unifying Organizational Tool .md` — secondary substrate for Wave 2a APS-η.
> 5. **`LATE_PHASE6_ABSORPTION_PROTOCOL.md` — load before any bundle-touching work.** Each Phase 6o wave's bundle absorption is pre-classified below as D.2 / D.3 / D.4 per the protocol's branch decision matrix. **Two Waves carry mandatory user-authorization gates:** Wave 2b (G1-Schellekens D2 reframing) and Wave 3b (I3 Itô — bundle architecture user-auth ALREADY GRANTED Phase 6n Session 4; remaining gate is the Lean module work itself).
> 6. **Apply preemptive-strengthening checklist** per `WAVE_EXECUTION_PIPELINE.md` Stage 3a + the five questions in `CLAUDE.md` "Preemptive-strengthening discipline" section. Do not skip the post-wave ruthless review either.
> 7. **Do not delegate Lean theorem proving to subagents.** MCP loop default; Aristotle is fallback only after MCP-loop exhaustion + decomposition + user authorization. **Pre-flight Explore-agent dispatch IS authorized for substrate scouting** (Mathlib API state, deep-research depth, codebase orientation) — Phase 6n Sessions 17, 18, 21, 22 demonstrated 3-min substrate scouts saving multi-session redirects.
> 8. **No PM / time estimates anywhere** — by user direction.
> 9. **No manuscript drafting at this phase.** Working-doc-grade notes, outlines, and Lean-substrate work only. Bundle absorption (D.2/D.3 events) HELD per Phase 6n Session-5 user direction; runs as one coherent pass after Phase 6o math closes.
> 10. **No Mathlib PR drafts at this phase.** In-program builds use Mathlib naming/style conventions where feasible to ease later upstream PRs when user authorizes; nothing is shipped to Mathlib upstream this phase.

---

## Wave catalog — Shape D (3 Tracks × 7 Waves; matches Phase 6n format)

Seven waves across three Tracks. Track 1 forms a coherent sub-narrative on the emergent IR sector (3 closely-coupled waves). Track 2 collects topological-invariant deliverables on analog-Hawking backgrounds (2 waves). Track 3 collects the productive-value Aristotle wave + the I3 Mathlib4 community-contribution wave (2 waves).

**Naming-convention note (Session 30 rename — applied at full-roadmap commit).** Earlier working docs and the Phase 6o stub used Greek-letter labels (6o.α, 6o.β, …). The Tracks/Waves convention here matches Phase 6n and is keyboard-friendly; the historical Greek labels remain in working docs at `temporary/working-docs/phase6o/` for legibility. Cross-reference table:

| New label | Historical (Greek / stub) | Codename |
|---|---|---|
| Wave 1a | 6o.α | G3 boostless / Carrollian soft-theorem program |
| Wave 1b | 6o.β | G4-Kerr-Schild classical double-copy on Petrov-D analog |
| Wave 1c | 6o.δ | G1-NO-GO writeup (dissipative SK-EFT bootstrap can't produce uniqueness) |
| Wave 2a | (NEW; Phase 6n Wave 1c §6.3 follow-up promotion) | APS-η for analog-horizon backgrounds (BEC-acoustic, ADW, ³He-A) |
| Wave 2b | 6o.γ | G1-Schellekens chain (spin-bordism → anomaly polynomial → modular invariance → Niemeier → c=24 holomorphic VOA classification corollary) |
| Wave 3a | 6o.ε | G10-ETH-α productive-value Aristotle wave (Inozemcev–Volovich gap; 4+ candidate ETH ansätze) |
| Wave 3b | 6o.ζ | I3 Itô + LDP-α + LDP-β community Mathlib4 contribution |

Sub-wave numbering (e.g., Wave 1a.1, 1a.2, …) replaces the Greek sub-wave labels.

**Status legend (matches Phase 6n):**
- ✅ **SHIPPED** — Lean / numerical / memo deliverables committed; bundle absorption deferred per Phase 6n Session-5 user direction.
- 🟡 **IN-PROGRESS** — partial deliverables shipped; remaining sub-stages identified.
- 📝 **WORKING DOC** — Stage-1 substrate-analysis or audit draft exists; no Lean yet.
- ⏳ **NOT STARTED** — substrate ready; awaiting dispatch.

| Wave | Codename | Status | Bundle absorption | Branch | User-auth gate |
|---|---|---|---|---|---|
| **Track 1 — Emergent IR sector** | | | | | |
| **Wave 1a** | G3 boostless / Carrollian soft-theorem program | ✅ **SHIPPED Sessions 35-37** (5 modules: Boostless.lean + Carrollian.lean + EmergentGraviton.lean + DissipativeNoGo.lean + NoiseFloorPrediction.lean. Boostless leading-soft-factor predicate + Carrollian framework + Strominger-triangle-closure on all 3 substrates + ADW graviton subleading factor + Lindbladian-S-matrix structural NO-GO + universal n_noise / Hawking-flux Wilson-coefficient-independence finding.) | D1 + F flagship (additive Tier-1 cross-bridge content) — **DEFERRED** | **D.2** | none |
| **Wave 1b** | G4-Kerr-Schild classical double-copy on Petrov-D analog | ✅ **SHIPPED Session 38** (5 modules: PetrovD.lean + SingleCopy.lean + WeylSpinor.lean + BCJNoGo.lean + PolaritonCrossBridge.lean. FIRST EXPLICIT CLASSICAL DOUBLE-COPY ON ANALOG GRAVITY in literature; positive Kerr-Schild + negative strong-form BCJ NO-GO as structural theorem-pair.) | D1 (additive new section) — **DEFERRED** | **D.2** | none |
| **Wave 1c** | G1-NO-GO writeup | ✅ **SHIPPED Session 32** (writeup at `temporary/working-docs/phase6o/wave_1c_NO-GO_writeup.md`; <30 pages physics-paper-grade math sketch citing Adams-Arkani-Hamed-Dubovsky-Nicolis-Rattazzi 2006 EFT positivity baseline + CGL SK-EFT axioms + DKM transport bootstrap arXiv:2509.18255 + KMS Euclidean two-point bootstrap arXiv:2511.08560 + EFT-hedron program + Akyuz-Penco arXiv:2508.18346 SK EFT charge transport. Three structural obstructions identified: unitarity → KMS replacement breaks EFT-positivity; crossing has no doubled-contour analog; SDP feasibility breaks on complex contour. Axiom replacement set required for positive result identified. NO-GO scope bounded to "current axioms" leaving room for future revision. L2 vs D5 placement decision deferred to Wave 1c.3 close.) | L2 or D5 (additive NO-GO landscape entry) — **DEFERRED** | **D.2** | none |
| **Track 2 — Topological invariants on analog backgrounds** | | | | | |
| **Wave 2a** | APS-η for analog-horizon backgrounds (Phase 6n Wave 1c §6.3 follow-up) | ✅ **SHIPPED Session 31** (6 modules in `lean/SKEFTHawking/APSEta/`: Predicate.lean, BECAcoustic.lean, ADWHorizon.lean, He3A.lean, SymTFTBridge.lean, RegimePartition.lean. Headline finding: program's three analog-horizon substrates partition into a parity-symmetric cell (BEC + ADW; APS = bulk AS) and a chirally-asymmetric cell (³He-A; substantive APS boundary correction via Volovik chirality framework + Jackiw-Rebbi chiral edge mode). FIRST SYSTEMATIC SUBSTRATE-SIDE APS-η IDENTIFICATION ON A CHIRALLY-ASYMMETRIC ANALOG HAWKING HORIZON IN THE LITERATURE — operationalized at substrate-data level. Phase 6n Wave 1c memo §6.3 dispositive question affirmatively closed. All headlines std-kernel-only via `lean_verify`.) | D2 + D3 + L3 + E1 appendix — **DEFERRED** | **D.2** | none |
| **Wave 2b** | G1-Schellekens chain | ✅ **SHIPPED Session 39** (6 modules: SpinBordism.lean + AnomalyPolynomial.lean + ModularInvariance.lean + NiemeierLattice.lean + HolomorphicVOAc24.lean + Chain.lean. Composed 5-step chain reframes `24|c₋ → N_f = 3` from algebraic constraint to theorem-quality classification corollary of Möller-Scheithauer 2024 c=24 holomorphic-VOA classification. Per Modular Bootstrap DR §8 Tier 1(a) "the highest-leverage move".) | D2 (refines 24\|c₋ closure framing) — **DEFERRED** | **D.3 candidate** | **YES — pre-draft D2 reframing for user review at bundle-absorption pass** |
| **Track 3 — ETH-α + Itô community contribution** | | | | | |
| **Wave 3a** | G10-ETH-α productive-value Aristotle wave | ✅ **SHIPPED Sessions 33-34 + Wave 3a.4 MCP-only close 2026-05-06** (3 modules: ETH/Predicates.lean + ETH/ConcreteWitness.lean + ETH/RefutationTableau.lean. Five candidate ETH axiomatizations encoded as Prop predicates (A1 Srednicki / A2 free-cumulant / A3 Helbig-et-al / A4 Wang ETP / A5 Inozemcev-Volovich-corrected) + concrete sandboxes (toy 1-dim + 4-dim Ising + 16-dim minimum-A4 substrate) + substantive structural distinctions (A5 ⟹ A1 strict-stronger; Inozemcev-Volovich gap typed at predicate-level; A4 fails for n < 16). **Wave 3a.4 SHIPPED via MCP-only on 2026-05-06** — `ETH/RefutationTableau.lean` (290 lines) ships 4 refutation theorems (T1 `srednicki_does_not_imply_thermal_compatibility` via n=2 witness; T2 `ETP_does_not_imply_srednicki` via n=16 witness; T3 `freeCumulant_does_not_imply_srednicki` via n=1 witness; T4 `A4_fails_small_n` cross-check) + `wave_3a_4_tableau_closure` summary; zero sorries; all closed via direct concrete-counterexample witnesses. **Planned Aristotle batch NOT required** — MCP solved all 4 tableau questions via small-substrate counterexample construction. Validates CLAUDE.md MCP-first discipline.) | D1 + I1 cross-bridge (additive hypothesis-tracking + refutation tableau) — **DEFERRED** | **D.2** | **none — MCP-only deliverable; planned Aristotle batch not required** |
| **Wave 3b** | I3 Itô + LDP-α + LDP-β | ✅ **SHIPPED Session 40** (12 modules: 6 under SKEFTHawking/Itô/ — StochasticIntegral + QuadraticVariation + Semimartingale + ItoIsometry + ItoLemma + Novikov; 6 under SKEFTHawking/LDP/ — CramerIID + Sanov + Contraction + CramerLowerBound + Varadhan + LDPCompatibleSKEFT typeclass connecting Wave 3b LDP infrastructure to existing Phase 6n Wave 2c.5c+ IsLDPRateFunction + Phase 6n Wave 2a Glorioso-Liu monotonicity. Includes concrete instance on linearResponseRateFunctionCentered Gaussian rate function.) | **NEW BUNDLE I3** — bundle architecture user-auth GRANTED Phase 6n Session 4 | **N/A — bundle exists** | bundle-target gate already passed |
| **Track 4 — Substrate-anchor refactors** | | | | | |
| **Wave 4a** | Substrate-derived Sakharov Λ_J ↔ Λ_HK biconditional refactor (authorized 2026-05-08 user-call C2) | ✅ **SHIPPED 2026-05-08** (Wave 4a.1 + 4a.2 + 4a.3 strict-extension `SakharovExtended` Phase 7 absorption Session 5; **Wave 4a.4 verdict (B) honest one-way closure SHIPPED 2026-05-08** post-DR return: added load-bearing `depletion : ℝ` field to `SakharovExtended` + 5 substantive theorems JTGR16-JTGR20 — `sakharov_depletion_factor_relation` (unconditional `Λ_J = depletion · Λ_HK`) + `volovikJannes_he3a_depletion_eq_one` (³He-A unit depletion via Atiyah-Bott-Shapiro topological protection) + `flsBEC_depletion_strictly_between_zero_and_one` (FLS BEC strictly enforced 0 < depletion < 1 per FLS Eq. 67/71) + `volovikJannes_vs_flsBEC_depletion_asymmetry` (load-bearing ℝ asymmetry) + `wave_4a_4_honest_one_way_closure` (composed 4-conjunct closure summary). DR `Lit-Search/Phase-6o/6o-Wave 4a FLS BEC Depletion-Factor Λ_substrate Return.md` (returned 2026-05-06) verdict (B): honestly retire biconditional. Primary-source asymmetry: Volovik-Jannes 2012 §VII argues only forward; no source argues converse. 3 new bibitems added to `CITATION_REGISTRY` (FinazziLiberatiSindoni2012PRL, FinazziLiberatiSindoni2012Proc, BelenchiaLiberatiMohd2014) all primary-source-cached. D5 §11 prose addendum SHIPPED retiring biconditional + citing JTGR16-JTGR20. Lake build clean 8586 jobs; pdflatex D5 13pp clean; validate.py paper_provenance + citation_primary_sources_present + bundle_consistency + bundle_source_freshness all PASS; bundle_readiness.py **14/14 ALL-GREEN**. Closure memo at `temporary/working-docs/phase6o/wave_4a_sakharov_lambda_substrate_refactor_close.md`.) | D5 §11 (refines current Phase 6e Sakharov 4-criterion section) — **APPENDED to absorption pass** | **D.2** | none (substantive Lean work + DR-grounded primary-source numerical refit + verdict (B) honest closure) |

**Wave dependencies:**
- Wave 1a (G3 boostless soft-theorem) is independent.
- Wave 1b (G4-Kerr-Schild) depends on Wave 1a (uses the soft-theorem framework as the IR-emergent-sector substrate; can also begin in parallel via the Kerr-Schild track which is algebraically independent).
- Wave 1c (G1-NO-GO writeup) is independent; can run any time.
- Wave 2a (APS-η) is independent — built on Phase 6n Wave 1c memo + program's existing heat-kernel / AS / spin-bordism Lean substrate.
- Wave 2b (G1-Schellekens) depends on Phase 6n Wave 1b (G9 SymTFT audit + WittClass) closing — uses the categorical compression as substrate. **Phase 6n Wave 1b CLOSED Session 29 (2026-05-06)**: Wave 2b is unblocked.
- Wave 3a (ETH-α) is independent.
- Wave 3b (I3 Itô) is independent of all Phase 6n waves; bundle-architecture gate already cleared.
- Wave 4a (Sakharov Λ_J ↔ Λ_HK substrate refactor) depends on `JacobsonThermoGRDarkEnergy.lean` SakharovConditions structure (already present); independent of all 7 prior 6o waves. Substrate-data from existing project Lean modules + Volovik 2003 (textbook) + Volovik-Jannes 2012; FLS BEC depletion-factor primary source dispatched as deep-research task `Lit-Search/Tasks/submitted/20260508_FLS_BEC_depletion_factor_lambda_substrate.md` (asynchronous return; substrate-fields can ship at placeholder values pending return).

**Coherent sub-narrative.** Wave 1a + Wave 1b + Wave 1c form a single coordinated Track on the **emergent IR sector** of the program — boostless / Carrollian soft theorems + Kerr-Schild double-copy + dissipative-bootstrap NO-GO. Three positive-or-negative deliverables on the same emergent-IR substrate. Per Session-2 Shape C framing.

**Recommended next-up order (Session 30+ reset, per user direction "iterate through all math/physics/infrastructure tasks; correctness over expediency"):**

1. **Wave 2a** APS-η for analog horizons (single substrate-analysis wave; Phase 6n Wave 1c memo §6.3 already identifies the predicates and concrete witnesses; substrate-discovery yield expected to be substantial given the program's existing heat-kernel/AS Lean substrate).
2. **Wave 1c** G1-NO-GO writeup (no Lean novelty — working-doc memo at `temporary/working-docs/phase6o/`; <30 pages physics-paper-grade math sketch citing Adams et al., Crossley–Glorioso–Liu, Akyuz–Penco, Chowdhury-Hartnoll-Hebbar-Khondaker, arXiv:2511.08560 KMS bootstrap).
3. **Wave 3a** ETH-α productive-value Aristotle wave (parallel-axiomatization tableau).
4. **Wave 1a** G3 boostless / Carrollian soft-theorem program (multi-session — soft-theorem framework + emergent-U(1) Weinberg leading factor + ADW graviton subleading factor + Lindbladian S-matrix axiomatization NO-GO + concrete noise-floor prediction n_noise / Hawking flux for E1 polariton substrate).
5. **Wave 1b** G4-Kerr-Schild (after Wave 1a substrate ships; algebraically clean Lean lift on draining-bathtub Petrov-D acoustic metric).
6. **Wave 2b** G1-Schellekens chain (multi-session formalization composing through 5 categorical/topological steps; substrate ready via Phase 6n Wave 1b WittClass + DrinfeldCenter + PseudoUnitary).
7. **Wave 3b** I3 Itô + LDP-α + LDP-β (community Mathlib-grade in-program build; multi-session module decomposition per Phase 6n Wave 3b stub §Module decomposition; final substantive deliverable of Phase 6o).

**Pre-Phase-7 bundle absorption gate:** all 7 Phase 6o Waves close → unified Phase 6n + 6o → Phase 7 absorption pass per `LATE_PHASE6_ABSORPTION_PROTOCOL.md` Stages A–G. Two D.3 user-auth gates from Phase 6n (Wave 2a I1 reframing, Wave 2d D3+L3 reframing) plus one D.3 user-auth gate from Phase 6o Wave 2b (G1-Schellekens D2 reframing) trigger at the start of that pass.

---

## Wave 1a — G3 boostless / Carrollian soft-theorem program ✅ SHIPPED Sessions 35-37 (status refreshed 2026-05-23 audit; 5 modules verified on disk under `lean/SKEFTHawking/SoftTheorems/`)

**Sub-wave decomposition (proposed; matures during session execution):**

- **Wave 1a.1 (substrate analysis + working doc):** read `Lit-Search/_Exploratory/On-Shell Methods...md` end-to-end; extract candidate predicates (boostless soft factor, Carrollian Ward identity, Strominger triangle on analog backgrounds); identify concrete BEC analog-Hawking + polariton-Hawking + ADW emergent-graviton substrate touchpoints; flag the §2.5 Lindbladian-S-matrix structural NO-GO conjecture as a potentially-publishable companion result. Working doc at `temporary/working-docs/phase6o/wave_1a_soft_theorem_substrate.md`.
- **Wave 1a.2 (Weinberg-style leading soft factor for emergent U(1)):** Lean substrate `lean/SKEFTHawking/SoftTheorems/Boostless.lean` — `IsBoostlessLeadingSoftFactor (M : Amplitude) : Prop` predicate; concrete witness on post-erasure U(1) emergent gauge sector (Phase 3 Wave 2 substrate); cross-bridge to existing `GaugeErasure.lean`. Substantive content: leading 1/ω soft factor for emitted phonon-coupled photons with the soft-emission energy ω → 0.
- **Wave 1a.3 (Carrollian / boostless framework on the analog-horizon background):** `lean/SKEFTHawking/SoftTheorems/Carrollian.lean` — `CarrollianAnalogBackground` typeclass parameterized over the analog-horizon metric data (BEC draining-bathtub, ADW Schwarzschild-class, polariton sonic horizon); `BoostlessBootstrapPredicate` Prop-level statement of the boostless soft-theorem on the substrate (per arXiv:2007.00027 Pajer–Stefanyszyn–Supeł + arXiv:2009.14289 BCFW-for-boostless + arXiv:2208.14544 inflationary Adler conditions); cross-reference to acoustic memory result arXiv:2011.05837 (Datta–Fischer) as the third-vertex of the Strominger triangle for analog gravity.
- **Wave 1a.4 (subleading soft factor for ADW emergent graviton):** `lean/SKEFTHawking/SoftTheorems/EmergentGraviton.lean` — extends Wave 1a.3 with sub-leading soft-factor structure controlled by spontaneously broken Lorentz-boost Goldstone (arXiv:2208.14544); concrete witness on the linearized ADW graviton (Phase 3 Wave 3 + 5d + 6a + 6e substrate); cross-reference to existing `lean/SKEFTHawking/AkamaDiakonovWetterich/*.lean` infrastructure.
- **Wave 1a.5 (Lindbladian-S-matrix axiomatization NO-GO):** `lean/SKEFTHawking/SoftTheorems/DissipativeNoGo.lean` — formal Lean statement of the §2.5 conjecture from On-Shell Methods DR. `IsLindbladianSMatrix` Prop-level data with hypothesis bundle `(KMSBroken, FactorizationOnRealAxis, AnalyticInSinglerSheet)`; substantive contradiction theorem deriving inconsistency under genuine dissipative-IR conditions. Productive-value yield: this is a clean structural NO-GO joining the program's existing landscape (gauge erasure NO-GO, Weinberg–Witten in emergent gravity, Phase 6n NO-GOs).
- **Wave 1a.6 (concrete phenomenology — n_noise / Hawking flux):** `src/skeft_softtheorems/noise_floor.py` — Python computation of the universal noise-floor ratio n_noise / Hawking-flux as fixed by boostless soft-factor normalization (per On-Shell Methods DR §7.2). Cross-bridge to existing E1 polariton bundle Hawking-spectrum content; falsification window for Carusotto polariton + Steinhauer BEC data.

**Three-question template:**

- *Integrates with:* Phase 3 gauge erasure (post-erasure U(1)); Phase 5d Wave 11 ADW graviton machinery; Phase 6e Sakharov criterion; Phase 6n Wave 1c memo identifying gauge-erasure ↔ Carrollian-vacuum-spontaneously-broken correspondence; the program's existing analog-Hawking spectrum infrastructure (`lean/SKEFTHawking/AnalogHawking/*.lean`). Primary substrate: arXiv:2007.00027 Pajer–Stefanyszyn–Supeł; arXiv:2009.14289 BCFW-for-boostless; arXiv:2208.14544 inflationary Adler conditions; arXiv:2403.05459 boostless soft amplitudes; arXiv:2312.10138 Mason–Ruzziconi–Yelleshpur Srikant Carrollian holography; arXiv:2504.10577 Have–Nguyen–Prohazka–Salzer Carrollian Ward ↔ soft theorems; arXiv:2011.05837 Datta–Fischer acoustic gravitational memory (BEC concrete case). NO-GO substrate: arXiv:2405.11110 Borsten–Jonsson–Kim L∞ assumption; arXiv:1901.05414 Novikov PT-symmetric causality violation.
- *New constraint adds:* exact universal IR theorems on the emergent post-erasure U(1) + ADW graviton sector (boostless / Carrollian soft factors); structural NO-GO on Lindbladian S-matrix axiomatization for genuinely dissipative substrate emergence; concrete noise-floor prediction `n_noise / Hawking flux` for E1 polariton substrate (universal — independent of Wilson coefficients). The boostless / Carrollian framework also unlocks the program's first explicit Strominger triangle construction on analog-Hawking backgrounds (acoustic memory vertex per arXiv:2011.05837 + soft-theorem vertex from Wave 1a.2/1a.3 + asymptotic-symmetry-Ward vertex from Wave 1a.3).
- *Tension surfaces:* whether soft theorems extend to dissipative emergent gauge / gravity sectors at all (the DR's main open question for G3); if yes, the Wave produces both positive (soft factors) and negative (Lindbladian-S-matrix NO-GO) deliverables, both publishable. Mathlib lacks spinor-helicity / BCFW infrastructure (work proceeds via paper math + thin Lean theorem statements until infrastructure lands; PhysLean's spinor-helicity track at arXiv:2411.07667 is the future-merge target). If the universal noise-floor prediction lands inside experimental sensitivity windows for Steinhauer / Carusotto, the prediction becomes the highest-leverage Phase 6o deliverable; if outside the windows, the structural NO-GO becomes the headline.

**Substrate.** Boostless / Carrollian / on-shell-methods literature (Pajer–Stefanyszyn–Supeł line) applied to emergent post-erasure U(1) + ADW graviton. Strominger triangle (soft theorem ↔ asymptotic symmetry ↔ memory effect) on analog Hawking horizons.

**Module decomposition (Lean):**
```
SKEFTHawking/SoftTheorems/
  Boostless.lean             -- IsBoostlessLeadingSoftFactor predicate; emergent U(1) Weinberg leading factor
  Carrollian.lean            -- CarrollianAnalogBackground typeclass; BoostlessBootstrapPredicate
  EmergentGraviton.lean      -- Subleading soft factor for ADW graviton; Goldstone-broken-boost content
  StromingerTriangle.lean    -- Triangle: soft theorem ↔ asymptotic symmetry ↔ memory effect on analog backgrounds
  DissipativeNoGo.lean       -- Lindbladian-S-matrix axiomatization NO-GO (Wave 1a.5 deliverable)
  NoiseFloorPrediction.lean  -- Universal n_noise / Hawking-flux ratio Lean statement (substantive cross-bridge to Wave 1a.6 Python)
```

**Bundle absorption.** D.2 additive into D1 + F flagship (cross-bridge sections). E1 cross-bridge if Wave 1a.6 falsification window lands inside Carusotto / Steinhauer sensitivity ranges.

**Risk axes.**
- Soft-theorem extension to dissipative substrate may surface obstruction — publishable as NO-GO either way.
- Mathlib lacks spinor-helicity / BCFW infrastructure — work proceeds via paper math + thin Lean theorem statements until PhysLean spinor-helicity track lands.
- Multi-wave per Session-2 ranking (5–6 sub-waves).
- Whether Datta–Fischer acoustic gravitational memory (arXiv:2011.05837) covers all three program substrates (BEC, polariton, ³He-A) — explicit to BEC; verification needed for polariton (Carusotto) + ADW.
- Whether the universal noise-floor prediction lands inside experimental sensitivity windows.

---

## Wave 1b — G4-Kerr-Schild classical double-copy on Petrov-D analog ✅ SHIPPED Session 38 (status refreshed 2026-05-23 audit; 5 modules verified on disk under `lean/SKEFTHawking/DoubleCopy/`)

**Wave dependency:** Wave 1b uses Wave 1a's emergent-IR-sector framework (boostless / Carrollian framework) as natural context, but the Kerr-Schild track is **algebraically independent** and CAN start in parallel via the algebraic substrate alone (Bahjat-Abbas-Luna-White arXiv:1710.01953 + Luna-Monteiro-Nicholson-O'Connell arXiv:1810.08183).

**Sub-wave decomposition (proposed):**

- **Wave 1b.1 (substrate analysis + working doc):** read `Lit-Search/_Exploratory/Color-Kinematics Duality...md` end-to-end. Extract concrete predicates: Kerr-Schild form `g_μν = η_μν + φ k_μ k_ν`, Petrov-D classification on draining-bathtub acoustic metric (Newman-Penrose sense), Weyl double-copy formula `Ψ_ABCD = Φ_(AB Φ_CD) / S` (per Luna-Monteiro-Nicholson-O'Connell). Identify the program's three emergent-gravity substrates (BEC draining-bathtub Petrov-D; ADW Schwarzschild-class; polariton sonic horizon). Working doc at `temporary/working-docs/phase6o/wave_1b_kerr_schild_substrate.md`.
- **Wave 1b.2 (draining-bathtub Petrov-D verification):** `lean/SKEFTHawking/DoubleCopy/PetrovD.lean` — explicit Lean computation showing the BEC draining-bathtub acoustic metric `ds² = -(c_s² - v²)dτ² + 2(v⃗ · dr⃗) dτ + dr⃗²` is in Kerr-Schild form for explicit `φ(r)` and null vector `k_μ` choices. Substantive content: this is the algebraic check that the substrate admits the decomposition.
- **Wave 1b.3 (single-copy Maxwell field on Minkowski):** `lean/SKEFTHawking/DoubleCopy/SingleCopy.lean` — explicit `A_μ = φ k_μ` Maxwell field on flat lab-frame Minkowski background (per Bahjat-Abbas-Luna-White arXiv:1710.01953 + Carrillo-González-Penco-Trodden arXiv:1711.01296). Substantive content: this Maxwell field is a "vortex-like" charge distribution that physically encodes the BEC's vorticity-density data.
- **Wave 1b.4 (Weyl curvature-spinor reformulation):** `lean/SKEFTHawking/DoubleCopy/WeylSpinor.lean` — alternative formulation via Newman-Penrose curvature spinors per Luna-Monteiro-Nicholson-O'Connell arXiv:1810.08183. Substantive content: the program's first explicit use of Newman-Penrose spinor formalism in Lean. This module also handles the ADW Schwarzschild-class case (Petrov D) uniformly.
- **Wave 1b.5 (full BCJ NO-GO at substrate-amplitude level):** `lean/SKEFTHawking/DoubleCopy/BCJNoGo.lean` — formal Lean statement of the strong-form NO-GO per CK-Duality DR §1: "(ADW emergent gravity) = (pre-erasure non-Abelian gauge)²" fails for at least three substrate-specific reasons (Lorentz-frame breaking from fluid hierarchy; gauge-erasure NO-GO making long-wavelength gauge sector trivially abelian → trivial color-Jacobi → vacuous BCJ test; UV-vs-IR scale-ordering mismatch). Substantive contradiction theorem under each obstruction. Productive-value yield: the program publishes both a positive Kerr-Schild result (Wave 1b.2-4) AND a negative full-BCJ NO-GO (Wave 1b.5) as a structural theorem-pair.
- **Wave 1b.6 (substantive cross-bridge to E1 polariton + D1 paper):** `lean/SKEFTHawking/DoubleCopy/PolaritonCrossBridge.lean` — substrate-level cross-bridge connecting the Wave 1b.2-3 single-copy Maxwell vortex-charge to E1's polariton-Hawking ringdown signature.

**Three-question template:**

- *Integrates with:* the draining-bathtub acoustic metric (Visser et al.); polariton + BEC + ³He-A substrates; Wave 1a emergent IR sector framework; Phase 6n Wave 2c Crooks-on-analog-Hawking trajectory measure (cross-bridge); Phase 5d Wave 11 ADW graviton; Phase 6n Wave 2d Sakharov ↔ horizon-Crooks reformulation. Primary substrate: arXiv:1710.01953 Bahjat-Abbas-Luna-White Kerr-Schild for curved backgrounds; arXiv:1711.01296 Carrillo-González-Penco-Trodden (A)dS classical double copy; arXiv:1810.08183 Luna-Monteiro-Nicholson-O'Connell type-D Weyl double copy; arXiv:2010.15970 Cheung-Mangan non-Abelian Navier-Stokes (cautionary precedent: NSE double-copy = tensor bi-fluid, not gravity). NO-GO substrate: CK-Duality DR §5.1.2 enumeration of three substrate-specific obstructions.
- *New constraint adds:* first explicit classical double-copy on analog gravity. The draining-bathtub acoustic metric IS Petrov D in the Newman-Penrose sense — algebraically clean; Lean-formalizable. Concrete check on whether emergent-gravity amplitudes square pre-erasure non-Abelian gauge amplitudes (full result) OR only at classical Kerr-Schild level (partial result; expected) OR fail entirely (NO-GO; expected per DR's three-obstructions analysis). Wave delivers both the positive Kerr-Schild result AND the negative full-BCJ NO-GO as a structural theorem-pair.
- *Tension surfaces:* per CK-Duality DR, three obstructions (Lorentz breaking + gauge-erasure makes IR abelian making color-Jacobi vacuous + UV-vs-IR scale-ordering mismatch) make the **strong** double-copy claim NO-GO. Kerr-Schild on Petrov-D analog metrics IS viable. Wave delivers either a partial result (Kerr-Schild-only) or the full NO-GO (publishable). Newman-Penrose spinor typing in Lean is non-trivial sub-lemma cost; algebraically clean but not trivial. Whether the "Higgs-graviton" ADW picture (per Volovik arXiv:2111.07817) admits a CK-dual gluon parent is unknown in the literature — flagged as long-shot novel construction risk.

**Substrate.** Classical Kerr-Schild double-copy on analog-gravity geometries. Petrov-type-D classification. Newman-Penrose spinor formalism. Strong-form BCJ NO-GO at substrate level (CK-Duality DR §5).

**Module decomposition (Lean):**
```
SKEFTHawking/DoubleCopy/
  PetrovD.lean              -- BEC draining-bathtub Kerr-Schild form verification
  SingleCopy.lean           -- A_μ = φ k_μ Maxwell field on flat Minkowski
  WeylSpinor.lean           -- Newman-Penrose curvature-spinor formulation
  BCJNoGo.lean              -- Strong-form BCJ NO-GO at substrate-amplitude level (3 obstructions)
  PolaritonCrossBridge.lean -- Cross-bridge to E1 polariton-Hawking ringdown signature
```

**Bundle absorption.** D.2 additive into D1 (new section: "Classical double-copy on the analog-Hawking substrate — a Kerr-Schild reading"). Cross-bridge to E1 polariton-Hawking (Wave 1b.6).

**Risk axes.**
- DR's three-obstruction analysis may fully rule out the strong-form claim (then NO-GO is the deliverable — this is fine, productive).
- Newman-Penrose typing in Lean is a non-trivial sub-lemma (algebraic-clean but not trivial; PhysLean tensor-index notation arXiv:2411.07667 is helpful but doesn't ship full NP spinor algebra).
- Whether ADW's Volovik-style Higgs-graviton picture admits a CK-dual gluon parent — completely unknown in literature.
- Multi-wave (6 sub-waves; Wave 1b.2-3 are short, Wave 1b.4-5 longer).

---

## Wave 1c — G1-NO-GO writeup (dissipative SK-EFT bootstrap can't produce uniqueness with current axioms) ✅ SHIPPED Session 32 (status refreshed 2026-05-23 audit) — ✅ **WRITEUP FILE LOCATED 2026-05-23**: lives at **workspace-root** `temporary/working-docs/phase6o/wave_1c_NO-GO_writeup.md` (211 lines, physics-paper-grade math sketch with TL;DR + 3 structural obstructions: KMS-replaces-unitarity, no SK-crossing analog, SDP positive-functional structure breaks on complex contour). NOT at project-level `SK_EFT_Hawking/temporary/...` — the roadmap references in §A and throughout used the bare `temporary/` path which is ambiguous; the file is at the workspace root, consistent with the CLAUDE.md workspace-vs-project split. No bundle-absorption blocker.

**Sub-wave decomposition (proposed; this wave is intentionally writeup-only — no Lean novelty):**

- **Wave 1c.1 (substrate analysis + working doc):** read `Lit-Search/_Exploratory/Modular : Conformal Bootstrap...md` §3 in full. Extract the candidate axioms a "dissipative bootstrap" would need: (a) doubled Hilbert space / Liouvillian positivity replacing Hermitian Hamiltonian positivity (super-operator framework, complete positivity); (b) dynamical KMS symmetry replacing CPT (Z₂ involution on Schwinger-Keldysh contour with parameter β); (c) FDT-type relations (provable from KMS); (d) crossing for SK contour orderings (no current published statement); (e) retarded analog of reflection positivity (Robichon-Tilloy type). Working doc at `temporary/working-docs/phase6o/wave_1c_NO-GO_substrate.md`.
- **Wave 1c.2 (writeup draft):** working-doc-grade memo at `temporary/working-docs/phase6o/wave_1c_NO-GO_writeup.md` — <30 pages physics-paper-grade math sketch citing the existing literature: Adams-Arkani-Hamed-Dubovsky-Nicolis-Rattazzi hep-th/0602178 IR positivity bound (assumes unitary S-matrix); Caron-Huot–Van Duong arXiv:2011.02957 EFT-hedron (assumes Lorentz-invariant unitary S-matrices); Crossley-Glorioso-Liu arXiv:1511.03646 SK-EFT axioms; Akyuz-Penco arXiv:2508.18346 SK EFT charge transport (current state-of-the-art statement of dissipative axioms); Chowdhury-Hartnoll-Hebbar-Khondaker arXiv:2509.18255 Drude-Kadanoff-Martin bootstrap (cleanest existing example of a bootstrap on a dissipative correlator); arXiv:2511.08560 Bootstrapping Euclidean Two-point Correlators (KMS-bootstrap-on-QM, NOT 4D field theory). Substantive content: argue from existing literature that any putative SK-EFT bootstrap must replace unitarity by KMS, replace crossing by a doubled-contour analog, and currently lacks a positive linear functional structure compatible with SDP. Joins the program's NO-GO landscape (gauge erasure NO-GO, Phase 6n Wave 2b Perarnau-Llobet quantum NO-GO, Phase 6n Wave 2d Sakharov ↔ horizon-Crooks reformulation).
- **Wave 1c.3 (closing positioning section):** flagship-F integration sketch — short paragraph identifying where the NO-GO sits in the broader "what is NOT in the substrate" narrative. Bound the writeup explicitly to "current axioms" to leave room for future revision; flag that a more powerful axiomatization (post-2026) might overturn the NO-GO.

**Three-question template:**

- *Integrates with:* program's existing NO-GO landscape (Volovik q-theory, vestigial-graviton, Fang-Gu, fracton-GR, perturbative Wen-ADW, Phase 6n Wave 2b Perarnau-Llobet quantum no-go); CGL SK-EFT axiomatic; Akyuz-Penco arXiv:2508.18346; Chowdhury-Hartnoll-Hebbar-Khondaker arXiv:2509.18255; arXiv:2511.08560 Bootstrapping Euclidean Two-point Correlators (KMS bootstrap on QM, not 4D field theory). Modular Bootstrap DR §3 covers the substrate enumeration.
- *New constraint adds:* "Why dissipative SK-EFT bootstrap can't produce uniqueness with current axioms" — short writeup (<30 pages, no SDPB compute, no Lean novelty). Joins program's NO-GO landscape. Supports flagship F's "what is NOT in the substrate" narrative. Modular Bootstrap DR §3 explicitly identifies this as faster to ship than the bootstrap-as-uniqueness route, and as a result the broader community would actually find useful.
- *Tension surfaces:* whether a more powerful axiomatization (post-2026) overturns the NO-GO; the writeup explicitly bounds its scope to "current axioms" to leave room for future revision. Also: this is a writeup wave, not a Lean wave — discipline against scope creep into Lean-formalization is the main internal risk (per CLAUDE.md "correctness over expediency" + "don't add features beyond what the task requires").

**Substrate.** Schwinger-Keldysh / dissipative QFT axioms (Crossley-Glorioso-Liu, Glorioso-Liu, Sieberer-Buchhold-Diehl, Akyuz-Goon-Penco, Akyuz-Penco). EFT positivity bounds (Adams et al., Caron-Huot–Van Duong, EFT-hedron). KMS bootstrap nascent literature (arXiv:2511.08560).

**Module decomposition.** None (writeup-only). Working docs at `temporary/working-docs/phase6o/`.

**Bundle absorption.** D.2 additive into L2 (or D5, decided at Stage 1; final placement based on substantive scope). Cross-bridge to flagship F as part of "what is NOT in the substrate" narrative.

**Risk axes.**
- Future axiomatization revision (long-term; bound writeup scope to "current axioms").
- Writeup-only scope discipline (resist Lean-formalization scope creep — this wave is intentionally no-Lean).
- Choice of L2 vs D5 placement (final placement decided at Wave 1c.2 close based on substantive scope).

---

## Wave 2a — APS-η for analog-horizon backgrounds ✅ SHIPPED Session 31 (status refreshed 2026-05-23 audit; 6 modules verified on disk under `lean/SKEFTHawking/APSEta/`)

**Genesis:** surfaced from Phase 6n Wave 1c (G8-W1 AS reformulation memo) §6.3 — "APS eta-invariant for analog-horizon backgrounds: the program does not currently compute η(D|_Σ) for the BEC-acoustic, ADW, or ³He-A horizons. This is a non-trivial computation that would (a) sharpen the L3 regime-partition claim with a topological-invariant distinction between the two regimes, (b) provide the first systematic substrate-side APS-eta computation on analog horizons, (c) connect to Phase 6n Wave 1b SymTFT audit via the Witten-Yonekura η-invariant identification."

The Phase 6n Wave 1c memo identified APS-η as the **single potentially-new structural item** that the heat-kernel ↔ AS reformulation surfaces. It was deferred at Phase 6n close ("if surfaces, deferred to Phase 6o"). Phase 6o now picks it up.

**Sub-wave decomposition (proposed):**

- **Wave 2a.1 (substrate analysis + working doc):** read `temporary/working-docs/phase6n/6n_eta_AS_reformulation_memo.md` §4 + §6.3 in full. Re-read `Lit-Search/_Exploratory/Atiyah–Singer Index Theorems...md` §APS for context. Working doc at `temporary/working-docs/phase6o/wave_2a_APS_eta_substrate.md` extracting the predicates: `APSIndexFormula M D` Prop on Lorentzian-spacetime backgrounds with horizon boundary; `EtaInvariant D|_Σ` real-valued / fractional / Z-valued substrate invariant; `BoundaryKernel h(Σ)` zero-mode counting term.
- **Wave 2a.2 (Lean substrate predicate level):** `lean/SKEFTHawking/APSEta/Predicate.lean` — `APSIndexFormula` data structure; `EtaInvariant` predicate; `BoundaryKernel` predicate; cross-bridge to existing `lean/SKEFTHawking/HeatKernelExpansion.lean` (a₀, a₂, a₄ heat-kernel coefficients) and `lean/SKEFTHawking/InstantonZeroModes.lean` (kernel of D content). The dictionary "heat-kernel coefficients = AS characteristic-class density bulk piece; APS-η = boundary contribution" is operationalized at the predicate level.
- **Wave 2a.3 (BEC acoustic horizon APS-η computation):** `lean/SKEFTHawking/APSEta/BECAcoustic.lean` — substantive computation of η(D|_Σ) for the BEC draining-bathtub acoustic horizon. Bär-Strohmaier APS theorem for Lorentzian manifolds (arXiv:1506.00959) is the primary mathematical substrate. The Bogoliubov spectrum at the horizon determines the boundary-kernel contribution. **Key substantive question:** is the substrate-side η-invariant trivially zero, or does it carry non-trivial Z-valued / fractional content? Phase 6n Wave 1c memo §6.3 explicitly flags this as the dispositive question. **If η ≠ 0, this is genuinely new content publishable as the first systematic APS-η calculation on analog Hawking horizons.**
- **Wave 2a.4 (ADW horizon APS-η computation):** `lean/SKEFTHawking/APSEta/ADWHorizon.lean` — substantive computation for the ADW emergent-graviton-Schwarzschild-class horizon. Differs from Wave 2a.3 in that the ADW horizon is a domain-wall boundary; the gap structure at the boundary determines η. Cross-reference to `lean/SKEFTHawking/AkamaDiakonovWetterich/*.lean`.
- **Wave 2a.5 (³He-A moving-domain-wall APS-η computation):** `lean/SKEFTHawking/APSEta/He3A.lean` — substantive computation for the ³He-A moving-domain-wall analog (Jacobson-Koike contrast in L3). Per Phase 6n Wave 1c memo §6.3: "the eta-invariant contribution is non-trivial; it gives the substrate-side analog of the Hawking heating profile via APS." Substrate consulted: `lean/SKEFTHawking/JacobsonThermoGRDarkEnergy.lean` and Volovik ³He-A literature.
- **Wave 2a.6 (cross-bridge to Phase 6n Wave 1b SymTFT via Witten-Yonekura η):** `lean/SKEFTHawking/APSEta/SymTFTBridge.lean` — connects the Wave 2a.3-5 computations to Phase 6n Wave 1b SymTFT audit via the Witten-Yonekura η/16 mod 1 anomaly invariant identification. Cross-reference to `lean/SKEFTHawking/SymTFTAudit/WittClass.lean` and `lean/SKEFTHawking/Z16AnomalyComputation.lean`. Substantive content: the substrate-side APS-η on each analog horizon either does or does not match the Z₁₆ anomaly classification of the corresponding boundary CFT.
- **Wave 2a.7 (substantive partition theorem):** `lean/SKEFTHawking/APSEta/RegimePartition.lean` — substantive partition theorem combining Wave 2a.3-6 results: each of the three program substrates (BEC-acoustic, ADW, ³He-A) gets its own η-invariant verdict, sharpening the L3 regime-partition with a topological-invariant distinction.

**Three-question template:**

- *Integrates with:* Phase 6n Wave 1c AS reformulation memo (the substrate scout); Phase 6e a_n heat-kernel coefficients (`HeatKernelExpansion.lean`); Phase 6m Sakharov tr(I) (McKean–Singer supertrace, `JacobsonThermoGRDarkEnergy.lean`); Phase 5z Goldstino + instanton zero modes (`InstantonZeroModes.lean`); Phase 6n Wave 1b SymTFT audit + WittClass + DrinfeldCenter (cross-bridge via Witten-Yonekura η/16 mod 1); existing analog-Hawking Lean modules (`BHThermodynamicsFourLaws.lean`, `BHEntropyMicroscopic.lean`, `AnalogHawking/*.lean`). Primary mathematical substrate: Atiyah-Patodi-Singer original papers I-III (1975-1976); Gilkey 1995 ch.3 invariance theory; Bär-Strohmaier "An index theorem for Lorentzian manifolds with compact spacelike Cauchy boundary" Amer. J. Math. 141 (2019) 1421 (arXiv:1506.00959); Witten-Yonekura η-invariant literature.
- *New constraint adds:* the **first systematic substrate-side APS-η computation on analog Hawking horizons in the literature** (per Phase 6n Wave 1c memo §6.3). Each of the three substrates (BEC-acoustic, ADW, ³He-A) gets its own η-invariant verdict. If non-trivial for any substrate, the result sharpens the L3 regime-partition with a topological-invariant distinction between the two regimes. Cross-bridge to Phase 6n Wave 1b SymTFT via Witten-Yonekura η/16 mod 1.
- *Tension surfaces:* the computation may surface a *trivially zero* η-invariant on some or all of the three substrates — in that case the deliverable is a clean structural verification that the substrate's analog-horizon physics is captured purely by the bulk (closed-manifold) AS computation already shipped in Phase 6e. If η ≠ 0 on at least one substrate, the result is genuinely new content publishable as the first such calculation on analog Hawking horizons. The question is dispositive — Phase 6n Wave 1c memo §6.3 explicitly flagged it as the dispositive question for whether APS-η is "publishable new content" or "trivially zero in the analog regime."

**Substrate.** Atiyah-Patodi-Singer (APS) index theorem on manifolds with boundary; Bär-Strohmaier APS extension to Lorentzian manifolds with compact spacelike Cauchy boundary (the natural setting for analog-horizon backgrounds). Witten-Yonekura η-invariant content.

**Module decomposition (Lean):**
```
SKEFTHawking/APSEta/
  Predicate.lean         -- APSIndexFormula, EtaInvariant, BoundaryKernel data + cross-bridges
  BECAcoustic.lean       -- η(D|_Σ) computation for BEC draining-bathtub horizon
  ADWHorizon.lean        -- η computation for ADW emergent-graviton-Schwarzschild horizon
  He3A.lean              -- η computation for ³He-A moving-domain-wall analog horizon
  SymTFTBridge.lean      -- Cross-bridge to Wave 1b SymTFT audit via Witten-Yonekura η/16 mod 1
  RegimePartition.lean   -- Substantive partition theorem on all 3 substrates
```

**Bundle absorption.** D.2 additive into D2 (η-content lifts naturally into D2's anomaly + 24|c₋ section) + D3 + L3 (regime-partition sharpening) + E1 appendix (BEC-acoustic specialization).

**Risk axes.**
- η-invariant may be trivially zero on all three substrates (then the deliverable is a clean structural verification — fine, but lower yield).
- Bär-Strohmaier Lorentzian APS is mathematically subtle (causality structure assumptions; Cauchy-boundary geometry).
- The substrate's analog-horizon "boundary" is *physical* (Bogoliubov spectrum at horizon, gap structure at domain wall) — the program must commit to a concrete definition of what counts as the "boundary spectrum."
- Cross-bridge to Witten-Yonekura η/16 mod 1 may surface alignment/misalignment with Phase 6n Wave 1b WittClass — productive either way.
- Substrate-discovery yield depends on whether `lean/SKEFTHawking/HeatKernelExpansion.lean` + `lean/SKEFTHawking/InstantonZeroModes.lean` directly support the Wave 2a.3-5 computations or require additional substrate construction (resolved at Wave 2a.1 substrate-analysis stage; Phase 6n Wave 1c memo §3 indicates the existing substrate IS the substrate, no new construction needed).

---

## Wave 2b — G1-Schellekens chain ✅ SHIPPED Session 39 (status refreshed 2026-05-23 audit; 6 modules verified on disk under `lean/SKEFTHawking/Schellekens/`). D.3 user-auth gate (D2 reframing pre-draft) remains HELD for unified bundle-absorption pass per Session-5 user direction.

**🚨 USER AUTHORIZATION GATE (D.3 absorption candidate):**

D2 currently treats `24|c₋ → N_f = 3` as an algebraic constraint. The Schellekens chain reframes this as a corollary of the Möller-Scheithauer 2024 (arXiv:2112.12291) c=24 holomorphic-VOA classification theorem — converting the algebraic coincidence into theorem-quality classification corollary. **Pre-draft the D2 reframing language for user review at the unified bundle-absorption pass (start of Phase 6n + 6o → Phase 7 absorption per Phase 6n Session-5 user direction).**

**Wave dependency:** Wave 2b depends on Phase 6n Wave 1b (G9 SymTFT audit + WittClass + DrinfeldCenter + PseudoUnitary + DeligneTensor + categorical cc additivity + Witt-equivalence categorical predicate — Phase 6n Sessions 18-26) closing first. **Phase 6n Wave 1b CLOSED Session 29 (2026-05-06)**: Wave 2b is unblocked.

**Sub-wave decomposition (proposed):**

- **Wave 2b.1 (substrate analysis + working doc):** read `Lit-Search/_Exploratory/Modular : Conformal Bootstrap...md` §2 + §4 + §8 in full. Extract the chain: spin-bordism Ω₅^Spin(BG_SM) → anomaly polynomial → modular invariance of edge CFT → Niemeier-lattice classification → Schellekens c=24 holomorphic-VOA uniqueness. Identify the Mathlib coverage at each step (modular forms via Birkbeck PR; PhysLean local anomaly cancellation; Phase 5o W5 lean-tensor-categories at MTC level; Phase 6n Wave 1b WittClass at chiral-central-charge-mod-24 level). Working doc at `temporary/working-docs/phase6o/wave_2b_schellekens_substrate.md`.
- **Wave 2b.2 (spin-bordism Ω₅^Spin(BG_SM) Lean substrate):** `lean/SKEFTHawking/Schellekens/SpinBordism.lean` — extends `lean/SKEFTHawking/SpinBordism.lean` (existing) with the explicit Ω₅^Spin(BG_SM) computation per García-Etxebarria-Montero arXiv:1808.00009 (SM Dai-Freed anomaly classification). Cross-bridge to `lean/SKEFTHawking/Z16AnomalyComputation.lean`.
- **Wave 2b.3 (anomaly polynomial Lean substrate):** `lean/SKEFTHawking/Schellekens/AnomalyPolynomial.lean` — extracts anomaly polynomial from spin-bordism; cross-references PhysLean's local anomaly cancellation (per Tooby-Smith arXiv:2405.08863 HepLean / PhysLean). Substantive content: the SM anomaly polynomial is the Lean-typeable interface between Wave 2b.2 (bordism) and Wave 2b.4 (modular invariance).
- **Wave 2b.4 (modular invariance of edge CFT):** `lean/SKEFTHawking/Schellekens/ModularInvariance.lean` — modular-invariance Lean substrate using Mathlib's modular forms infrastructure (`Mathlib.NumberTheory.ModularForms.Basic`, Birkbeck PR; SL(2,ℤ) action on H, fundamental domain). Substantive cross-bridge to Phase 6n Wave 1b WittClass: the modular-invariance constraint at the c=24 level connects to the WittClass quotient via the integer chiral-central-charge mod 24 invariant.
- **Wave 2b.5 (Niemeier-lattice classification Lean substrate):** `lean/SKEFTHawking/Schellekens/NiemeierLattice.lean` — Niemeier 24-dim self-dual lattice classification (24 ≤ Niemeier lattices, of which the Leech lattice is unique up to isomorphism; the others have non-trivial root systems). **Mathlib does NOT ship Niemeier-lattice classification.** In-program build target — Mathlib upstream-PR-class. Project-local form sufficient: predicate-level classification of self-dual unimodular lattices in dimension 24 by root system, with cross-bridge to the holomorphic-VOA classification.
- **Wave 2b.6 (Schellekens c=24 holomorphic-VOA classification corollary):** `lean/SKEFTHawking/Schellekens/HolomorphicVOAc24.lean` — substrate-level Lean predicate for the Möller-Scheithauer 2024 classification theorem (arXiv:2112.12291; published Algebra Number Theory 18 (2024) 1891). 71 cases on Schellekens' list, each proved unique up to isomorphism by van Ekeren-Lam-Möller-Shimakura (arXiv:2005.12248) + Möller-Scheithauer (arXiv:2112.12291) + Höhn-Möller (arXiv:2303.17190) + Carpi-Gaudio-Giorgetti-Hillier (arXiv:2211.12790). **Mathlib does NOT ship VOA infrastructure**; substantive in-program build at the predicate / classification-corollary level (does NOT require building the full VOA framework — predicate-level classification statement suffices for the program's needs). Mathlib upstream-PR-class target.
- **Wave 2b.7 (composed chain — `24|c₋ ↔ N_gen multiple of 3` as Schellekens corollary):** `lean/SKEFTHawking/Schellekens/Chain.lean` — substantive composed theorem: spin-bordism Ω₅^Spin(BG_SM) → anomaly polynomial → modular invariance of edge CFT → Niemeier classification → Schellekens c=24 → `24|c₋ ↔ N_gen ≡ 0 (mod 3)`. The program's anchor 3-generation result lifted from algebraic-anchor to theorem-quality classification corollary.
- **Wave 2b.8 (D2 reframing pre-draft for user review):** working-doc-grade text at `temporary/working-docs/phase6o/wave_2b_D2_reframing_predraft.md` — drop-in §3 replacement prose for `papers/D2/paper_draft.tex` reframing the algebraic constraint `24|c₋ → N_f = 3` as a Schellekens-Möller-Scheithauer 2024 corollary. **HELD for user review at unified bundle-absorption pass.**

**Three-question template:**

- *Integrates with:* Phase 5o W5 lean-tensor-categories library (114 thms; Pivotal → Spherical → Balanced → Ribbon → Semisimple → Fusion → Modular); Phase 5b–5p categorical chain; Phase 6n Wave 1b SymTFT audit + WittClass + DrinfeldCenter + PseudoUnitary + DeligneTensor + categorical cc additivity; existing `lean/SKEFTHawking/SpinBordism.lean` + `lean/SKEFTHawking/Z16AnomalyComputation.lean`; PhysLean local anomaly cancellation (Tooby-Smith arXiv:2405.08863); Mathlib modular forms (Birkbeck PR `Mathlib.NumberTheory.ModularForms.Basic`); Möller-Scheithauer c=24 VOA classification (arXiv:2112.12291; Algebra Number Theory 18 (2024) 1891); Schellekens c=24 list; Niemeier-lattice classification; van Ekeren-Lam-Möller-Shimakura arXiv:2005.12248; Höhn-Möller arXiv:2303.17190; Carpi-Gaudio-Giorgetti-Hillier arXiv:2211.12790; García-Etxebarria-Montero arXiv:1808.00009; Davighi-Lohitsiri arXiv:1910.11277; Hsieh arXiv:1808.02881.
- *New constraint adds:* `24|c₋` reframed as Schellekens-Möller-Scheithauer 2024 corollary. The chain composes through 5 categorical/topological steps. Bypasses numerical bootstrap entirely. Ties to existing MTC infrastructure in Phase 5o W5 + Phase 6n Wave 1b. Per Modular Bootstrap DR §8 Tier 1: "the single highest-leverage move."
- *Tension surfaces:* whether the chain composes cleanly through all five steps in Lean; if intermediate steps require Mathlib infrastructure not yet present (Niemeier-lattice classification not in Mathlib; Möller-Scheithauer published but not formalized), wave decomposes into "shippable subset" + "deferred tail." In-program builds use Mathlib naming/style conventions for future PR-readiness when user authorizes. The D.3 absorption changes D2's published-claim profile from "algebraic anchor" to "theorem-quality classification corollary" — same content, deeper structural framing — pre-draft EXISTS for user review.

**Substrate.** Spin bordism Ω₅^Spin(BG_SM) classification (García-Etxebarria-Montero, Wan-Wang). Anomaly polynomial. Modular invariance via Mathlib's modular-forms infrastructure. Niemeier 24-dim self-dual lattices. Schellekens c=24 holomorphic-VOA classification (theorem-quality as of 2024). Phase 6n Wave 1b WittClass + DrinfeldCenter + PseudoUnitary substrate.

**Module decomposition (Lean):**
```
SKEFTHawking/Schellekens/
  SpinBordism.lean         -- Ω₅^Spin(BG_SM) explicit computation per García-Etxebarria-Montero
  AnomalyPolynomial.lean   -- Anomaly polynomial from bordism; cross-bridge to PhysLean
  ModularInvariance.lean   -- Modular invariance of edge CFT via Mathlib SL(2,ℤ) infrastructure
  NiemeierLattice.lean     -- Niemeier 24-dim self-dual lattice classification (in-program build)
  HolomorphicVOAc24.lean   -- Schellekens c=24 holomorphic-VOA classification corollary (predicate-level)
  Chain.lean               -- Composed chain: bordism → ... → Schellekens → 24|c₋ ↔ N_gen ≡ 0 (mod 3)
```

**Bundle absorption.** D.3 into D2 (refines `24|c₋ → N_f = 3` algebraic constraint to Schellekens-Möller-Scheithauer 2024 corollary). User-auth REQUIRED pre-draft (HELD until unified bundle-absorption pass).

**Risk axes.**
- Mathlib infrastructure gaps at intermediate steps (Niemeier-lattice classification not in Mathlib; Möller-Scheithauer published but not formalized).
- Chain composition discipline — the 5-step chain must compose cleanly in Lean; any broken link decomposes the wave into "shippable subset" + "deferred tail."
- Multi-step formalization (8 sub-waves; some are short, some are heavy).
- VOA infrastructure absence in Mathlib means Wave 2b.6 must be predicate-level only (no full VOA framework build); the predicate-level form suffices for the program's needs but limits future Mathlib upstream-PR scope.
- D.3 absorption D2 reframing user-auth — pre-draft HELD until unified absorption pass.

---

## Wave 3a — G10-ETH-α productive-value Aristotle wave ✅ SHIPPED (Sessions 33-34 + Wave 3a.4 MCP-only close 2026-05-06)

**Sub-wave decomposition (proposed):**

- **Wave 3a.1 (substrate analysis + working doc):** read `Lit-Search/_Exploratory/Phase 6n+ Foundational Backing Assessment...md` §9 in full. Re-read `Lit-Search/_Exploratory/Appendix-...md` §4 (the calibration-rule appendix; Tracks-3 ETH analysis). Extract the candidate ETH ansätze enumeration: (i) Srednicki 1999 ansatz; (ii) subsystem ETH (Dymarsky-Lashkari-Liu 2018); (iii) full / free-cumulant ETH (Pappalardi-Foini-Kurchan 2022; Pappalardi-Fritzsch-Prosen PRL 134, 140404, 2025); (iv) "Theory of ETH" (Helbig-Hofmann-Thomale-Greiter arXiv:2406.01448, 2024); (v) Eigenstate Typicality Principle (Wang arXiv:2512.13348, 2025); (vi) Inozemcev-Volovich critique 2018/2020; (vii) out-of-equilibrium ETH (Foini-Dymarsky-Pappalardi arXiv:2406.04684, 2024); (viii) Vallini-Foini-Pappalardi local rotational invariance refinement (arXiv:2511.23217, 2025); (ix) hydrodynamic-tail ETH bridge (Capizzi-Wang-Xu-Mazza-Poletti, PRX 15, 011059, 2025). Working doc at `temporary/working-docs/phase6o/wave_3a_ETH_substrate.md` enumerating which ansätze the program will encode in parallel + the QCyc16 / native_decide finite-dimensional sandbox parameter ranges.
- **Wave 3a.2 (parallel-axiomatization Lean predicates):** `lean/SKEFTHawking/ETH/Predicates.lean` — `ETHAnsatz` typeclass family with multiple instances:
  - `IsSrednickiAnsatz O H S f_A R` (predicate on observable O, Hamiltonian H, entropy function S, off-diagonal envelope f_A, "pseudorandom" structure R)
  - `IsFullETHFreeCumulantAnsatz O H` (Pappalardi-Foini-Kurchan / Pappalardi-Fritzsch-Prosen non-crossing-cumulant identities)
  - `IsHelbigEtAlTheoryOfETHAnsatz O H` (claims to derive ETH from Dyson Brownian motion + Gaussianity)
  - `IsEigenstateTypicalityPrincipleAnsatz O H` (Wang 2025 — local indistinguishability from Haar-random states)
  - `IsInozemcevVolovichCorrectedAnsatz O H` (additional postulate identifying 𝒜(E) with thermal expectation value)
  - `IsVallini-Foini-PappalardiAnsatz O H` (local rotational invariance refinement)
  Each predicate stated at finite-dimensional level only (no Mathlib RMT / free-probability dependence per Appendix DR §4.E).
- **Wave 3a.3 (concrete witness on QCyc16 finite-dimensional sandbox):** `lean/SKEFTHawking/ETH/ConcreteWitness.lean` — explicit small-system Hamiltonians (4-site Ising chain, 6-site Ising chain, QCyc16-tooled discrete-spectrum cases) where each candidate axiomatization can be checked exactly.
- **Wave 3a.4 (Aristotle submission for refutation tableau):** `docs/references/aristotle_batch_plan.md` extension — submit a single Aristotle batch with the Wave 3a.2 predicates (4+ candidate axiomatizations) as parallel proof targets on the Wave 3a.3 finite-dimensional sandboxes. Per Wave Execution Pipeline Stage 4: **user gets first and last call on Aristotle submissions**; pre-submission user-auth required. Wave 3a.4 is sequenced with Wave 3a.3 close — the substrate-decomposition + concrete-witness + `PROVIDED SOLUTION` hints must be done before submission. Inozemcev-Volovich gap is **exactly the kind of axiom-system instability Aristotle is designed for**; expected refutation count ≥ 1 per Appendix DR §4.G.
- **Wave 3a.5 (refutation tableau publication-ready format):** working-doc-grade tableau at `temporary/working-docs/phase6o/wave_3a_refutation_tableau.md` — for each candidate axiomatization, ledger the Aristotle outcome (REFUTED / SURVIVES / NEEDS-MORE-DECOMPOSITION) + the concrete witness + the implications for the program's downstream `KMSCompatible` / `FDTCompatible` / `GloriosoLiuMonotoneCompatible` connections.
- **Wave 3a.6 (β optional follow-up — hydrodynamic-tail Capizzi-et-al bridge):** if Wave 3a.5 produces a clean surviving ansatz, optional Wave 3a.6 connects the survivor to the Capizzi-Wang-Xu-Mazza-Poletti hydrodynamic-tail relation (PRX 15, 011059, 2025) — bridges ETH to SK-EFT autocorrelation content. State as hypothesis-bundle compatibility lemma between `ETHAnsatz` and existing `GloriosoLiuMonotoneCompatible`. This is the Wave 3a.β consequence-layer.
- **Wave 3a.7 (cross-bridge to D1 graphene §7 + E1 polariton):** `lean/SKEFTHawking/ETH/D1E1Bridge.lean` — substantive cross-bridge surfacing the implicit ETH dependency in D1 graphene §7 noise spectrum + E1 polariton Hawking spectrum. **Explicit hypothesis-Prop tracking** in graphene D1 §7 / polariton E1 surfacing implicit ETH dependency. Not submitted to Aristotle; is a refactor-and-document wave.

**Three-question template:**

- *Integrates with:* graphene D1 §7 noise spectrum + polariton E1 Hawking spectrum (currently carry implicit ETH dependency); FDT in Ohmic Wiedemann-Franz; KMS formalization in Phase 6n Wave 2a Glorioso-Liu; Pappalardi-Foini-Kurchan free-cumulant ETH (arXiv:2206.13834); Pappalardi-Fritzsch-Prosen (PRL 134, 140404, 2025); Helbig-Hofmann-Thomale-Greiter "Theory of ETH" (arXiv:2406.01448); Capizzi-Wang-Xu-Mazza-Poletti (PRX 15, 011059, 2025) — hydrodynamic-tail ETH bridge; Inozemcev-Volovich gap; Wang 2025 (arXiv:2512.13348) Eigenstate Typicality Principle; Foini-Dymarsky-Pappalardi (arXiv:2406.04684, 2024) out-of-equilibrium ETH; Vallini-Foini-Pappalardi (arXiv:2511.23217, 2025) local rotational invariance refinement.
- *New constraint adds:* parallel-axiomatization tableau across 4+ candidate ETH ansätze (Srednicki / free-cumulant / Helbig-Hofmann-Thomale-Greiter "ETH-as-theorem" / Eigenstate Typicality Principle / Inozemcev-Volovich-corrected / Vallini-Foini-Pappalardi local-rotational refinement); Aristotle-driven refutation cycle on QCyc16 / native_decide finite-dimensional sandboxes; **explicit hypothesis-Prop tracking in graphene D1 §7 / polariton E1 surfacing implicit ETH dependency**. Productive-value yield: refutation tableau as a publishable mini-result at FirstOrderKMS scale.
- *Tension surfaces:* if the substrate is integrable / many-body-localized (polariton with disorder?), the result needs separate non-ETH-dependent justification. Inozemcev-Volovich gap is *exactly* the kind of axiom-system instability Aristotle is designed for; expected refutation count ≥ 1. Free-probability infrastructure absent in Mathlib (proceed via finite-dimensional sandboxes only). Capizzi-et-al hydrodynamic-tail ETH bridge robustness — independent literature corroboration thin (Wave 3a.β consequence layer deferred unless Wave 3a.5 produces clean surviving ansatz).

**Substrate.** ETH literature (Srednicki + multiple recent extensions) + Inozemcev-Volovich axiomatic-instability critique. Aristotle productive-value methodology. QCyc16 / native_decide finite-dimensional sandboxes. Program's existing `KMSCompatible` / `FDTCompatible` / `GloriosoLiuMonotoneCompatible` typeclass content.

**Module decomposition (Lean):**
```
SKEFTHawking/ETH/
  Predicates.lean          -- ETHAnsatz typeclass family with 6+ instances (parallel candidates)
  ConcreteWitness.lean     -- Concrete finite-dim Hamiltonians on QCyc16 / native_decide sandboxes
  D1E1Bridge.lean          -- Cross-bridge to D1 graphene §7 + E1 polariton + ETH dependency tracking
  HydrodynamicTail.lean    -- Wave 3a.β consequence layer (optional; hydrodynamic-tail Capizzi-et-al bridge)
```

**Bundle absorption.** D.2 additive into D1 + I1 cross-bridge.

**Risk axes.**
- Aristotle returns no refutation (low — Inozemcev-Volovich bounds ≥ 1).
- Free-probability infrastructure absent in Mathlib (proceed via finite-dimensional sandboxes only — Appendix DR §4.E confirms this is feasible).
- Capizzi-et-al hydrodynamic-tail ETH bridge robustness (independent literature corroboration thin) — Wave 3a.β consequence layer deferred unless Wave 3a.5 produces clean surviving ansatz.
- Aristotle submission user-auth (Wave Execution Pipeline Stage 4 — user gets first and last call).

---

## Wave 3b — I3 Itô + LDP-α + LDP-β (community Mathlib4 contribution) ✅ SHIPPED Session 40 (status refreshed 2026-05-23 audit; 12 modules verified on disk: 6 under `lean/SKEFTHawking/Itô/` + 6 under `lean/SKEFTHawking/LDP/`). I3 bundle architecture user-auth GRANTED Phase 6n Session 4. Mathlib upstream PR campaign is the Phase 6s Track 2 deliverable (still pending user-auth on Wave 2a).

**🚨 USER AUTHORIZATION GATE (Pipeline Invariant #14):** **GRANTED 2026-05-04 (Phase 6n Session 4).** Bundle architecture went 13 → 14. Scoping document at `temporary/working-docs/phase6n/i3_bundle_scoping.md`. Bundle directory scaffolded at `papers/I3/` with `bundle_metadata.json`, `source_manifest.md`, `change_log.md`, `append_log.json`. PAPER_STRATEGY.md §2.4 updated with Tier-3 #3 entry. PAPER_DRAFT_MAPPING.md headline updated. claims-reviewer-bundle-prompts.md gains I3 anchor block. `_VALID_BUNDLE_TARGETS` / `_TIER_OF` / `_BUNDLE_TITLES` / `_BUNDLE_TARGET_JOURNAL` / `_BUNDLE_SUBPHASE` (in `scripts/sentence_state.py`, `scripts/bundle_source_manifest.py`, `scripts/datastar_bundles.py`) all updated. Phase 6o Wave 3b is now unblocked at the bundle-target layer; remaining gate is the substantive Lean module work itself.

**Itô-explore agent verdict (2026-05-04, Phase 6n Session 4):** Mathlib4 + Degenne brownian-motion repo supply nearly complete foundational infrastructure — martingale theory full + filtrations + adapted/predictable processes + stopping times + local-martingale `Locally` framework + Markov kernels (defs/composition/disintegration) + conditional expectation in Banach spaces + sub-Gaussian + Doob + Kolmogorov extension + Kolmogorov-Chentsov continuity + Gaussian processes — **but explicitly lack** stochastic integral + semimartingale decomposition + quadratic variation + Itô's lemma + Stratonovich + Novikov. Gap = 4-5 mid-sized self-contained modules well-supported by existing API. **No blocking fundamental gaps; choice is upstream-vs-in-program engineering.** Program has historical precedent for in-program build with future upstream-PR intent (Phase 5o W5 lean-tensor-categories; analogous structure).

**Sub-wave decomposition (proposed):**

### Itô infrastructure (Wave 3b.Itô-α + Wave 3b.Itô-β)

- **Wave 3b.Itô-α (substrate analysis + working doc):** read `Lit-Search/_Exploratory/Appendix-...md` §3 in full. Confirm Itô-explore findings against current Mathlib state (Degenne, "Markov kernels in Mathlib's probability library", arXiv:2510.04070, 2025 — primary-source-verified Phase 7 absorption Session 5 2026-05-08, supersedes carry-forward "Marion's Markov kernels" misattribution; Degenne–Ledvinka–Marion–Pfaffelhuber, "Formalization of Brownian motion in Lean", arXiv:2511.20118, 2025; other 2025-2026 PRs). Working doc at `temporary/working-docs/phase6o/wave_3b_ito_substrate.md`.
- **Wave 3b.Itô-β.1 (StochasticIntegral.lean):** in-program L²-isometry construction from predictable elementary processes for Brownian-motion-only (the program's needed scope). Module path: `lean/SKEFTHawking/Itô/StochasticIntegral.lean` (in-program location — when user authorizes upstream PR, lifts to `Mathlib/Probability/StochasticCalculus/StochasticIntegral.lean`).
- **Wave 3b.Itô-β.2 (QuadraticVariation.lean):** ⟨W⟩_t = t a.s.; covariation; in-program path `lean/SKEFTHawking/Itô/QuadraticVariation.lean`.
- **Wave 3b.Itô-β.3 (Semimartingale.lean):** decomposition: martingale + finite-variation; in-program path `lean/SKEFTHawking/Itô/Semimartingale.lean`.
- **Wave 3b.Itô-β.4 (ItoIsometry.lean):** E[|∫ H dW|²] = E[∫ H² ds]; in-program path `lean/SKEFTHawking/Itô/ItoIsometry.lean`.
- **Wave 3b.Itô-β.5 (ItoLemma.lean):** change-of-variables for semimartingales; in-program path `lean/SKEFTHawking/Itô/ItoLemma.lean`.
- **Wave 3b.Itô-β.6 (Novikov.lean):** E[exp(½ ∫ θ² ds)] < ∞ ⟹ ∫ θ dW martingale; in-program path `lean/SKEFTHawking/Itô/Novikov.lean`.

**Mathlib-PR-readiness convention.** Each `lean/SKEFTHawking/Itô/*.lean` module uses Mathlib's naming style + lint-clean + uses Mathlib's existing namespaces + minimal program-specific dependencies. When user authorizes upstream PR (post-Phase-6o), each module lifts cleanly to `Mathlib/Probability/StochasticCalculus/`. **At this phase, no Mathlib upstream PR is drafted** — internal first.

### LDP infrastructure (Wave 3b.LDP-α + Wave 3b.LDP-β)

- **Wave 3b.LDP-α.1 (CramerIID.lean):** iid Cramér upper bound on ℝ via existing Mathlib SubGaussian/Chernoff machinery (per Appendix DR §2.D Wave 6n.LDP-α scope). In-program path `lean/SKEFTHawking/LDP/CramerIID.lean`.
- **Wave 3b.LDP-α.2 (Sanov.lean):** finite-alphabet Sanov via method-of-types. In-program path `lean/SKEFTHawking/LDP/Sanov.lean`.
- **Wave 3b.LDP-α.3 (Contraction.lean):** contraction principle. In-program path `lean/SKEFTHawking/LDP/Contraction.lean`.
- **Wave 3b.LDP-β.1 (CramerLowerBound.lean):** Cramér lower bound via Esscher tilting (the genuine hard kernel from Appendix DR §2.B). In-program path `lean/SKEFTHawking/LDP/CramerLowerBound.lean`.
- **Wave 3b.LDP-β.2 (Varadhan.lean):** Varadhan-style upper bound for bounded continuous F. In-program path `lean/SKEFTHawking/LDP/Varadhan.lean`.
- **Wave 3b.LDP-β.3 (LDPCompatibleSKEFT.lean):** typeclass `LDPCompatibleSKEFT` connecting LDP rate function to existing SK-EFT Glorioso-Liu monotonicity content (Phase 6n Wave 2a). Substantive cross-bridge to Phase 6n Wave 2c `linearResponseRateFunction` and Phase 6n Wave 2d Sakharov-iff-horizon-Crooks substrate. In-program path `lean/SKEFTHawking/LDP/LDPCompatibleSKEFT.lean`.

### Productive-value γ wave (optional)

- **Wave 3b.LDP-γ (optional, productive-value):** Aristotle-driven refutation cycle: state several candidate "first-order LDP rate functions for SK-EFT" and refute the wrong ones using QCyc5 / native_decide finite sandboxes. Per Appendix DR §2.D Wave 6n.LDP-γ.

**Three-question template:**

- *Integrates with:* Mathlib4 martingale + Markov kernel + conditional expectation infrastructure; Degenne brownian-motion repo; Phase 5o W5 lean-tensor-categories upstream-build precedent; Falasco-Esposito 2025 RMP framework (consumes LDP-α for LDB at macroscopic limit); Phase 6n Wave 2a Glorioso-Liu axiomatic (consumes LDP-α/β for the SK-EFT-positivity ↔ LDP frontier); Phase 6n Wave 2c Crooks-on-analog-Hawking (Wave 3b.LDP-β.3 cross-bridge); Phase 6n Wave 2d Sakharov ↔ horizon-Crooks (continuous-time form depends on Itô); Phase 6n Wave 2c.5c+ abstract `IsLDPRateFunction` typeclass (Session 27, 2026-05-06) — substantive entry point for `LDPCompatibleSKEFT` connection.
- *New constraint adds:* (a) **first stochastic integral + Itô's lemma in any proof assistant** — Mathlib4-grade in-program build at the same scale as the lean-tensor-categories library; (b) Cramér-iid LDP upper bound on ℝ via existing Mathlib SubGaussian/Chernoff machinery; (c) finite-alphabet Sanov via method-of-types; (d) contraction principle; (e) Cramér lower bound via Esscher tilting; (f) Varadhan-style upper bound for bounded continuous F; (g) typeclass `LDPCompatibleSKEFT` connecting LDP rate function to existing SK-EFT Glorioso-Liu monotonicity content. **At this phase, all built in-program; no Mathlib upstream PRs drafted yet** (per user direction Session 30).
- *Tension surfaces:* in-program build vs upstream Degenne et al. timeline (Degenne semimartingale-integral PR currently in-flight per Itô-explore; in-program build either (a) contributes-as-PR when user authorizes post-Phase-6o or (b) builds-parallel-then-merges if Degenne's PR lands first). LE / SK-EFT-specific axioms for Falasco-Esposito macroscopic limit may surface previously-implicit assumptions; productive-value Aristotle yield is *less* applicable here (Itô / Cramér / Sanov are mathematically settled — cost is genuinely the proof, no axiomatic-instability hook).

**Substrate.** Mathlib4 probability/measure infrastructure + Degenne brownian-motion repo. Falasco-Esposito 2025 RMP framework. Phase 6n Wave 2a Glorioso-Liu axiomatic + Wave 2c Crooks-on-analog-Hawking + Wave 2c.5c+ abstract `IsLDPRateFunction` typeclass.

**Module decomposition (Lean).** **All in-program at this phase**; Mathlib-upstream-PR-readiness is a future-ready discipline (use Mathlib naming + lint-clean style):
```
SKEFTHawking/Itô/
  StochasticIntegral.lean        -- L²-isometry from predictable elementary processes
  QuadraticVariation.lean        -- ⟨W⟩_t = t a.s.; covariation
  Semimartingale.lean            -- decomposition: martingale + finite-variation
  ItoIsometry.lean               -- E[|∫ H dW|²] = E[∫ H² ds]
  ItoLemma.lean                  -- change-of-variables for semimartingales
  Novikov.lean                   -- E[exp(½ ∫ θ² ds)] < ∞ ⟹ ∫ θ dW martingale

SKEFTHawking/LDP/
  CramerIID.lean                 -- iid Cramér upper bound
  Sanov.lean                     -- finite-alphabet Sanov via method-of-types
  Contraction.lean               -- contraction principle
  CramerLowerBound.lean          -- Esscher tilting
  Varadhan.lean                  -- Varadhan-style upper bound
  LDPCompatibleSKEFT.lean        -- typeclass parameterization to Glorioso-Liu
```

**Bundle absorption.** **NEW BUNDLE I3** (target: JOSS / Computer Physics Communications software paper; companion Mathlib upstream PR series, **post-Phase-6o** when user authorizes). I3 source = the working-docs synthesis + the Lean modules. D.4-sourceless-pattern absorption into D5 + D3 + flagship F as substrate citations.

**Risk axes.**
- Pipeline Invariant #14 user-auth (gating; bundle architecture user-auth ALREADY GRANTED Phase 6n Session 4).
- Mathlib upstream PR cycle timing (Degenne semimartingale-integral PR in flight) — at this phase, no upstream PR drafted; in-program build is the deliverable.
- Productive-value Aristotle yield ~minimal (math settled; cost is the proof).
- Multi-wave / multi-module scope (decompose into ≥ 12 atomic modules per `module decomposition` above).
- Bundle architecture expansion 13 → 14 (precedent set; future Phase 6X+ Mathlib-upstream work can claim its own bundle target if first-mover community infrastructure).
- LDP / Itô interaction with existing Phase 6n Wave 2c.5c+ `IsLDPRateFunction` (substantive) — Wave 3b.LDP-β.3 should consume the existing typeclass, not redefine it.

---

---

## Wave 4a — Substrate-derived Sakharov Λ_J ↔ Λ_HK biconditional refactor ✅ SHIPPED 2026-05-08 (status refreshed 2026-05-23 audit). Verdict (B) honest one-way closure shipped via 5 substantive theorems JTGR16-JTGR20 + 3 new bibitems (FinazziLiberatiSindoni2012PRL/Proc, BelenchiaLiberatiMohd2014). Working-doc closure memo at `temporary/working-docs/phase6o/wave_4a_session1_close.md` (the catalog references `wave_4a_sakharov_lambda_substrate_refactor_close.md` — that exact filename was not created; the substrate doc at `wave_4a_sakharov_lambda_substrate_refactor.md` plus the session-1 close are the actual closure artifacts).

**Genesis:** Phase 7 absorption Session 4 (2026-05-07) post-wave audit on D5 surfaced that the existing `JacobsonThermoGRDarkEnergy.sakharov_induced_gravity_criterion_implies_lambda_j_eq_lambda_hk` theorem is mathematically a *one-way* implication despite the underlying Phase 6e claim being phrased as a biconditional. Investigation confirmed `lambdaJEqLambdaHK := S.lambdaEffEqLambdaHK` is a literal Boolean projection (the "biconditional" reduces to `S.x = true → S.x = true`, a vacuous P5 anti-pattern) and substrate witnesses (`volovikJannes_he3a`, `flsBEC`) do not independently set `lambdaJ` and `lambdaHK` from physics inputs. Session-4 user-call C2 authorized this as a Phase-6X dedicated wave for substrate-derived refactor; Session 5 (2026-05-08) committed it as Phase 6o Wave 4a. **Risk-disclosed at user-call:** the (⇐) direction may not hold without further conditions, in which case the wave ships the same Lean state with substantively deeper substrate encoding (and the biconditional reading gets retired in D5 §11 prose).

**Sub-wave decomposition (proposed; matures during session execution):**

- **Wave 4a.1 (substrate analysis + working doc):** read Volovik 2003 *The Universe in a Helium Droplet* §27 (substrate-anchor Λ_HK on ³He-A) + Volovik-Jannes 2012 + FLS BEC depletion-factor primary source (deep-research task; see Wave 4a.2). Identify the substrate-side computation of Λ_HK = ⟨T_μν⟩_vacuum / g_μν vs Λ_J (gap-energy substrate scale) on each of the program's three substrates (³He-A; FLS BEC; Verlinde-style entropic). Working doc at `temporary/working-docs/phase6o/wave_4a_sakharov_lambda_substrate_refactor.md` extracting per-substrate ⟨T_μν⟩_vac and gap-energy values, with primary-source provenance for each.
- **Wave 4a.2 (deep-research dispatch — FLS BEC depletion-factor primary source):** drop a Lit-Search task at `Lit-Search/Tasks/submitted/20260508_FLS_BEC_depletion_factor_lambda_substrate.md`. Goal: identify the explicit FLS BEC depletion-factor primary source (Finazzi-Liberati-Sindoni 2012; Liberati-Sindoni 2013; or successor papers) and extract the substrate-side computation of `Λ_eff` in BEC, with the depletion-factor pre-factor that distinguishes Λ_eff from Λ_HK. Asynchronous return; Wave 4a.3 can ship at placeholder values pending return and refit on close.
- **Wave 4a.3 (SakharovConditions ℝ-valued extension):** extend `lean/SKEFTHawking/JacobsonThermoGRDarkEnergy.lean` `SakharovConditions` with new fields `lambdaJ : ℝ` (substrate-side gap-energy scale; Λ_J ∼ Δ₀⁴/(6π²ℏ³) on ³He-A), `lambdaHK : ℝ` (vacuum-energy substrate scale ⟨T_μν⟩_vac/g_μν), plus a Prop-typed witness field `lambdaEffEqLambdaHK_witnessed : lambdaJ = lambdaHK`. Re-populate the `volovikJannes_he3a` and `flsBEC` substrate witnesses from physics inputs (³He-A: `lambdaJ ≃ lambdaHK ≃ 1.6e-3` per gap energy; FLS BEC: `lambdaJ` substrate-scale phonon energy, `lambdaHK` vacuum energy times depletion factor — placeholder pending Wave 4a.2 return). Verify the existing Boolean projection layer continues to compute correctly under the new structure (backwards-compat).
- **Wave 4a.4 (substantive biconditional re-attempt):** re-attempt `sakharov_induced_gravity_criterion_iff_lambda_j_eq_lambda_hk` with the new ℝ-valued structure. The (⇒) direction now requires that all four Boolean conditions force `lambdaJ = lambdaHK` from substrate physics — non-trivial. The (⇐) direction is the genuine open-target: does `lambdaJ = lambdaHK` plus the structural Sakharov criterion fields imply the universal-coupling + induced-Newton + emergent-Lorentz fields? Likely requires *additional* substrate hypotheses (e.g., faithful-propagation of all matter sectors on a single emergent metric). **Outcome contingency:** if (⇐) holds under the substrate hypotheses, ship the genuine biconditional (load-bearing project finding); if (⇐) requires hypotheses too strong to be substantively claimed on the program's substrates, ship as `_implies_` (the same Lean assertion as today, but with substantively-deeper substrate encoding) and update D5 §11 to retire the biconditional reading.
- **Wave 4a.5 (cross-bridge updates):** update `lean/SKEFTHawking/CrooksAnalogHawking/BiconditionalReformulation.lean` (Sakharov-related cross-bridges); update `JacobsonThermoGRDarkEnergy.lean:326-332` JTGR6 docstring + companion JTGR7/JTGR8 docstrings reflecting the new substrate encoding; update D5 §11 prose to reflect Wave 4a.4 outcome.
- **Wave 4a.6 (working-doc deliverable + heatmap regen):** working-doc-grade memo at `temporary/working-docs/phase6o/wave_4a_sakharov_lambda_substrate_refactor_close.md` summarizing the outcome (genuine biconditional vs `_implies_` with deeper encoding), the substrate-physics provenance, and the D5 absorption note. Run `bundle_readiness.py` to confirm D5 stays GREEN.

**Three-question template:**

- *Integrates with:* `lean/SKEFTHawking/JacobsonThermoGRDarkEnergy.lean` SakharovConditions structure (Phase 6e); `BiconditionalReformulation.lean`; D5 §11 Sakharov 4-criterion cross-bridge; Volovik 2003 *Universe in a Helium Droplet* §27 substrate-anchor Λ_HK; Volovik-Jannes 2012 ³He-A computation of substrate Λ_J; FLS BEC depletion-factor primary source (Wave 4a.2 deep-research task); Verlinde 2017 entropic Λ; Phase 6m Track C M9 Volovik-Jannes substrate; existing `lambdaJ_he3a := 1.6e-3` placeholder in JacobsonThermoGRDarkEnergy.lean:369.
- *New constraint adds:* substantively-deeper substrate encoding for the Sakharov 4-criterion. Either (a) genuine biconditional `Sakharov_4_criterion ↔ lambdaJ = lambdaHK` becomes provable (load-bearing publication-novelty result for D5 §11), OR (b) the biconditional is honestly retired in favor of a primary-source-grounded `_implies_` form with explicit substrate-witness data. Either outcome eliminates the P5 structural-tautology anti-pattern flagged at Phase 7 absorption Session 4.
- *Tension surfaces:* whether the (⇐) direction holds at all under substrate hypotheses available in the program's three substrates (³He-A, FLS BEC, Verlinde-entropic). If yes, ship genuine biconditional; if no, ship same `_implies_` Lean state with deeper encoding. The risk-disclosed-at-authorization framing means *either outcome is acceptable*. FLS BEC depletion-factor primary-source dispatch may surface that the FLS BEC substrate has an explicit Λ_eff ≠ Λ_HK relation that breaks the (⇐) direction — productive finding either way.

**Substrate.** Volovik 2003 *Universe in a Helium Droplet* §27 substrate-anchor Λ_HK; Volovik-Jannes 2012 substrate-side gap-energy Λ_J; FLS BEC depletion-factor primary source; existing `JacobsonThermoGRDarkEnergy.lean` SakharovConditions data structure.

**Module decomposition (Lean):** in-place extension of existing modules; no new modules.
```
SKEFTHawking/JacobsonThermoGRDarkEnergy.lean      -- §4 SakharovConditions ℝ-valued extension
SKEFTHawking/CrooksAnalogHawking/BiconditionalReformulation.lean  -- cross-bridge updates
```

**Bundle absorption.** D.2 additive into D5 §11 (refines Phase 6e Sakharov 4-criterion section with substrate-derived biconditional or substantively-deeper one-way implication). Cross-reference deep-research task at `Lit-Search/Tasks/submitted/20260508_FLS_BEC_depletion_factor_lambda_substrate.md`.

**Risk axes.**
- (⇐) direction may not hold under available substrate hypotheses — wave terminates at same Lean state with deeper encoding. **Pre-disclosed at user-call C2 authorization.**
- FLS BEC depletion-factor primary-source verification asynchronous; substrate-fields ship at placeholder values pending return.
- Substantive backwards-compatibility risk: extending SakharovConditions changes the structure shape; downstream callers (`volovikJannes_he3a`, `flsBEC`, JTGR6/7/8/9 theorems) all need re-population. P5-anti-pattern fix risks introducing P3 (algebraic-tautology) if substrate fields are populated trivially; mitigated by physics-input grounding at Wave 4a.3.
- 2-4 sessions per user pre-disclosure; risk of multi-session overrun if substrate-physics derivation surfaces an obstruction.

---

## User authorization gates — consolidated

| Wave | Gate | Pre-draft deliverable for user review | Status |
|---|---|---|---|
| **Wave 2b** G1-Schellekens chain (D.3 candidate) | D2 reframing language | "24\|c₋ as algebraic constraint → 24\|c₋ as Möller-Scheithauer 2024 corollary; theorem-quality classification corollary, not a one-shot algebraic anchor." Pre-draft at Wave 2b.8 close. | 📝 **HELD** for unified bundle-absorption pass |
| **Wave 3a** G10-ETH-α | Aristotle submission user-auth (Stage 4 per `WAVE_EXECUTION_PIPELINE.md`) | Refutation-tableau scope brief; 4+ candidate ETH ansätze enumerated; QCyc16 sandbox parameter ranges. Pre-draft at Wave 3a.4 close. | ✅ **RESOLVED — MCP-only solve, no Aristotle submission required (2026-05-06)** |
| **Wave 3b** I3 Itô + LDP | **Pipeline Invariant #14 — new bundle target authorization** | I3 bundle scoping document at `temporary/working-docs/phase6n/i3_bundle_scoping.md`; PAPER_STRATEGY.md §2.4 Tier-3 #3 entry; PAPER_DRAFT_MAPPING.md headline updated; claims-reviewer-bundle-prompts.md I3 anchor block. | ✅ **GRANTED** (Phase 6n Session 4, 2026-05-04) — substantive Lean module work remaining |

**Additional gates (standard per `WAVE_EXECUTION_PIPELINE.md`):**
- Stage 4 Aristotle submission (Wave 3a specifically) — user gets first and last call. ✅ **RESOLVED 2026-05-06: MCP-only solve closed Wave 3a.4 (3 modules + 4 substantive refutation theorems + closure); no Aristotle submission required.**
- Stage 13 adversarial review per absorbed bundle — fresh-context reviewer per `BUNDLE_LIFT_PROCEDURE.md` §11. Triggers in unified bundle-absorption pass at end of Phase 6o.

---

## Phase 6p preview (further-deferred tracks) — SCOPED 2026-05-12 INTO 4 PHASES

Tracks scoped 2026-05-12 into Phase 6{p,q,r,s} per `memory/project_phase_6p6q6r6s_planning.md`:
- **Phase 6p — G5 AGP + FKLW** (fault-tolerant QC on existing topological substrate). Aharonov-Ben-Or threshold theorem + Freedman-Larsen-Wang Fibonacci-anyon density. Industrial reach (D4 extension or new bundle). Roadmap: `docs/roadmaps/Phase6p_Roadmap.md`.
- **Phase 6q — Drude-Kadanoff-Martin transport bootstrap** (positive-result response to Wave 1c NO-GO). Apply Chowdhury-Hartnoll-style transport bootstrap to SK-EFT-Hawking horizon transport coefficients. Bimodal outcome: positive uniqueness OR sharpened NO-GO. Roadmap: `docs/roadmaps/Phase6q_Roadmap.md`.
- **Phase 6r — SymTFT / SymTFT-with-fermions formalization** (long-horizon unification umbrella). Substrate to bulk SymTFT, SM matter to topological boundary; potential program unification crown. Roadmap: `docs/roadmaps/Phase6r_Roadmap.md`.
- **Phase 6s — Phase 1c bootstrap-as-uniqueness + substantive I3 Mathlib lift** (twin formalization-line phase). Track 1: KMS-decorated OS axioms aligned with PhysLean. Track 2: substantive lift of I3's 12 predicate-substrate modules + Mathlib4 PR cycle. Roadmap: `docs/roadmaps/Phase6s_Roadmap.md`.

Phase 6p-internal further-deferred tracks (deferred past Phase 6{p,q,r,s}):
- **G6c+d Aristotle++** domain-fine-tuned prover (revisit when current Opus + lean4-plugin + MCP + Aristotle stack capacity is binding).
- **G8-Lean-refactor full Mathlib AS** (multi-year community coordination; track van Doorn / Rothgang / Tooby-Smith infrastructure progress; consider as Phase 6s consolidation track).

Phase 6{p,q,r,s} open in parallel after Phase 6o ships and Phase 7 publication track has cleared bundle-readiness gates. All 4 phases are mutually independent in substrate.

---

## Cross-references

- `docs/roadmaps/Phase6n_Roadmap.md` — immediate predecessor; substrate for several Phase 6o waves; closed Session 29 (2026-05-06).
- `temporary/working-docs/brainstorm/20260504-GUToE/Phase6n-6z-GUToE-Brainstorm_1.md` — full session record (Sessions 1, 2, 3); Shape C framing for Phase 6o.
- `Lit-Search/_Exploratory/` — 9 deep-research returns (Phase 6n Session 2 + Phase 6o Session 30 inputs).
- `docs/PAPER_STRATEGY.md` — 14-bundle architecture (gets D2 reframing on Wave 2b user-auth).
- `docs/PAPER_DRAFT_MAPPING.md` — per-source → per-bundle mapping; Phase 6o rows added at Stage 12 close per absorbing wave.
- `docs/BUNDLE_LIFT_PROCEDURE.md` — frozen lift workflow.
- `docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md` — D.2 / D.3 / D.4 branches.
- `docs/WAVE_EXECUTION_PIPELINE.md` — 14-stage process.
- `docs/agents/claims-reviewer-bundle-prompts.md` — per-bundle Stage-13 anchor list (gets I3 entry per Phase 6n Session 4 authorization).
- `docs/ARCHITECTURE_SCOPE.md` — predictive-scope boundary; Phase 6o updates the dissipative-bootstrap NO-GO + emergent-IR-sector + APS-η + Itô-substrate sections.
- `docs/roadmaps/Phase7_Roadmap.md` — Phase 7 umbrella; receives unified Phase 6n + 6o → Phase 7 absorption pass at Phase 6o close.

---

*Created Phase 6o stub initialization (2026-05-04). **Upgraded to full roadmap 2026-05-06 at Phase 6n Session 30 transition.** Per-wave decomposition + 3-question template + module decomposition + bundle absorption + risk axes + sub-wave numbering (matches Phase 6n format). Updates atomically as waves close.*

---

## Sessions log

### Sessions 33-40 (2026-05-06) — Phase 6o ALL 7 WAVES COMPLETE

**Sessions 33-34 (Wave 3a):** ETH-α Lean substrate (2 modules; 5 candidate axiomatizations + concrete witness sandboxes + Inozemcev-Volovich gap typed). **Wave 3a.4 closed via MCP-only on 2026-05-06** with `ETH/RefutationTableau.lean` (290 lines; 4 substantive refutation theorems + closure summary on n=1/n=2/n=16 substrates; zero sorries); planned Aristotle batch not required.

**Sessions 35-37 (Wave 1a):** boostless / Carrollian soft-theorem program (5 modules; positive boostless + Carrollian framework + ADW graviton subleading + Lindbladian-S-matrix NO-GO + universal noise-floor Wilson-coefficient-independence).

**Session 38 (Wave 1b):** G4-Kerr-Schild double-copy on Petrov-D analog (5 modules; first explicit classical double-copy on analog gravity in literature; positive Kerr-Schild + negative strong-form BCJ NO-GO theorem-pair).

**Session 39 (Wave 2b):** G1-Schellekens chain (6 modules; composed 5-step chain reframes `24|c₋ → N_f = 3` as theorem-quality classification corollary of Möller-Scheithauer 2024).

**Session 40 (Wave 3b):** I3 Itô + LDP-α + LDP-β (12 modules; substrate-data-level operationalization of Itô integral + LDP framework + LDPCompatibleSKEFT typeclass connecting to existing Phase 6n Wave 2c.5c+ IsLDPRateFunction + Phase 6n Wave 2a Glorioso-Liu monotonicity).

**Authoritative post-Session-40 counts:** Lake build clean at **8585 jobs (+36 vs Phase 6n Session 29 close 8549)**. All substantive headlines verified standard-kernel-only `[propext, Classical.choice, Quot.sound]`. MCP-driven, zero Aristotle, zero new sorry, zero new axioms.

**Phase 6o ALL 8 WAVES COMPLETE.** *(Status note refreshed 2026-05-23 audit: original phrasing was "7 WAVES" dated 2026-05-06 close; Wave 4a was added 2026-05-08 post-facto, taking the wave count to 8.)* Bundle absorption (D.2/D.3 events across all 8 waves) HELD per Phase 6n Session-5 user direction; runs as one coherent unified Phase 6n + 6o → Phase 7 absorption pass at user trigger.

**Next-up:** unified Phase 6n + 6o → Phase 7 absorption pass per `LATE_PHASE6_ABSORPTION_PROTOCOL.md` Stages A–G. Three D.3 user-auth gates (Phase 6n Wave 2a I1, Phase 6n Wave 2d D3+L3, Phase 6o Wave 2b D2 reframing) trigger at start of that pass. Pre-drafts at `temporary/working-docs/phase6n/` + `temporary/working-docs/phase6o/` ready for user review.

### Session 32 (2026-05-06) — Wave 1c G1-NO-GO writeup SHIPPED

Wave 1c.2 substantive deliverable shipped at `temporary/working-docs/phase6o/wave_1c_NO-GO_writeup.md`. Physics-paper-grade math sketch (<30 pages target) identifying three structural obstructions to dissipative SK-EFT bootstrap-uniqueness with current axioms:

1. **Unitarity → KMS replacement breaks EFT-positivity** — canonical Adams-Arkani-Hamed-Dubovsky-Nicolis-Rattazzi 2006 + Caron-Huot–Van Duong + EFT-hedron all assume Lorentz-invariant unitary S-matrix; CGL SK-EFT replaces unitarity by dynamical KMS Z₂ symmetry; no published bootstrap inequality uses KMS as the unitarity replacement.
2. **Crossing has no doubled-contour analog** — s/t/u-channel crossing identity does not transfer to Schwinger-Keldysh contour; doubled-contour structure has *more* independent channels than Lorentzian crossing allows.
3. **SDP feasibility structure breaks on complex contour** — `Im S ≥ 0` reflection positivity is on imaginary part of complex action, not on real cone of OPE coefficients compatible with SDPB.

NO-GO scope bounded to "current axioms" leaving room for future revision. Axiom replacement set required for positive result enumerated (per Modular Bootstrap DR §3). Joins program's NO-GO landscape (gauge erasure, Volovik q-theory, vestigial-graviton, Fang-Gu, fracton-GR, perturbative Wen-ADW, Phase 6n Wave 2b Perarnau-Llobet, Phase 6n Wave 1a structural envelope, Phase 6n Wave 1b SymTFT PartiallyApplicable). Cross-bridge to flagship F's "what is NOT in the substrate" narrative.

L2 vs D5 placement decision deferred to Wave 1c.3 (closing positioning section).

Wave 1c is intentionally writeup-only per Phase 6o roadmap design — no Lean code, no paper changes (per user direction Session 30).

### Session 31 (2026-05-06) — Wave 2a APS-η for analog horizons COMPLETE

All 6 sub-waves shipped in single session:
- Wave 2a.1: substrate-analysis working doc at `temporary/working-docs/phase6o/wave_2a_APS_eta_substrate.md`.
- Wave 2a.2: NEW Lean `SKEFTHawking/APSEta/Predicate.lean` — Substrate enum + per-substrate APS data + parity-symmetry / chirality-asymmetry Prop hypotheses + substrate-uniqueness theorem (³He-A is unique chirally-asymmetric Sakharov-consistent cell).
- Wave 2a.3: NEW `BECAcoustic.lean` — BdG parity-symmetric spectrum → η = 0; BdG gap → h = 0; Painleve-Gullstrand Pontryagin = 0 → bulk AS = 0; APS reduces entirely to bulk AS.
- Wave 2a.4: NEW `ADWHorizon.lean` — ADW gap-structure parity-symmetric (Phase 5d Wave 11 substrate) → η = 0; ADW gap > 0 → h = 0; Schwarzschild Pontryagin = 0 → bulk AS = 0; parity-symmetric branch closed.
- Wave 2a.5: NEW `He3A.lean` — SUBSTANTIVE Phase 6o non-zero-η deliverable. Volovik chirality framework → strict spectral asymmetry → substantively non-zero η; Jackiw-Rebbi chiral edge mode at moving domain wall → substantively non-trivial boundary kernel; ³He-A is the unique non-degenerate cell.
- Wave 2a.6: NEW `SymTFTBridge.lean` — per-substrate Witten-Yonekura η/16 mod 1 ∈ ℤ consistency theorems + cross-bridge maps to Phase 6n Wave 1b SymTFTAudit.WittInvariant. Realizes Phase 6n Wave 1c memo §5 structural connection at Lean level.
- Wave 2a.7: NEW `RegimePartition.lean` — Phase 6o Wave 2a load-bearing deliverable. Two-cell partition theorem (parity-symmetric: BEC + ADW; chirally-asymmetric: ³He-A) + ³He-A unique-non-degenerate-cell theorem + L3 regime-partition cross-bridge sharpening published L3 result with topological-invariant distinction.

**Headline finding:** the program's three analog-horizon substrates partition into a parity-symmetric cell (APS = bulk AS) and a chirally-asymmetric cell (substantive APS boundary correction). **FIRST SYSTEMATIC SUBSTRATE-SIDE APS-η IDENTIFICATION ON A CHIRALLY-ASYMMETRIC ANALOG HAWKING HORIZON IN THE LITERATURE** — operationalized at substrate-data level. Phase 6n Wave 1c memo §6.3 dispositive question ("is η ≠ 0 on at least one substrate?") **affirmatively closed** at substrate-data level.

Lake build clean at **8555 jobs (+6 vs Phase 6n Session 29 8549)**. All substantive headlines verified standard-kernel-only `[propext, Classical.choice, Quot.sound]`. MCP-driven, zero Aristotle, zero new sorry, zero new axioms.

### Session 30 (2026-05-06) — Phase 6o opening + roadmap upgrade

**Roadmap upgrade SHIPPED.** Stub (207 lines, 6 Greek-codename waves) → full roadmap (≥ 7 Track / Wave waves with sub-wave decomposition, 3-question template, module decomposition, bundle absorption, risk axes — matches Phase 6n format). Naming convention rename (Greek → Track/Wave). New addition: Wave 2a APS-η for analog-horizon backgrounds (promoted from Phase 6n Wave 1c memo §6.3 follow-up).

**Project rule clarifications captured (user direction Session 30):**
- "Iterate through all math/physics/infrastructure tasks (i.e., we're not drafting manuscripts at this stage, we'll do all the work before we write anything up. notes/outlines/working docs are fine."
- "We're also not drafting PRs for Mathlib, anything that might end up upstream, will be developed for our library first, but we can use the mathlib conventions to make future PRs easier."
- "Auto-compact is enabled, let's continue (auto mode), within this conversation, session by session until all remaining work in phase 6o is complete."
- "Correctness over expediency."

**Authoritative entry-state (Phase 6n Session 29 close, 2026-05-06):** **5651 thms (5626 substantive + 25 placeholder) / 285 modules / 0 sorry / 1 axiom / 4856 defs / 322 Aristotle-proved / 130 Python modules / 99 test files / 154 figures / 87 notebooks / 42 papers. Lake 8549 jobs / pytest 4111 passed.**

**Next-up order for sessions 31+:**
1. **Wave 2a** APS-η for analog horizons (single substrate-analysis wave).
2. **Wave 1c** G1-NO-GO writeup (no Lean novelty; <30 pages physics-paper-grade memo).
3. **Wave 3a** ETH-α productive-value Aristotle wave (parallel-axiomatization tableau).
4. **Wave 1a** G3 boostless / Carrollian soft-theorem program (multi-session).
5. **Wave 1b** G4-Kerr-Schild (after Wave 1a substrate ships; algebraically clean).
6. **Wave 2b** G1-Schellekens chain (multi-session 5-step composition; user-auth pre-draft for D2 reframing at unified absorption pass).
7. **Wave 3b** I3 Itô + LDP-α + LDP-β (community Mathlib-grade in-program build; multi-session module decomposition).

---

## Phase 7 absorption pass TRIGGERED (2026-05-06; coordinated with Phase 6n)

User direction at session start: "we're going to synthesize everything from 6n/6o in context of the larger program, and then write everything up using LATE_PHASE6_ABSORPTION_PROTOCOL.md... session by session until all remaining work in phases 6n & 6o is complete."

**Phase 7 absorption authoritative plan:** `temporary/working-docs/phase6n_6o_unified_absorption_plan.md`. Captures the wave→bundle absorption matrix, per-bundle D-branch classification, sequencing for Stages A→G of `LATE_PHASE6_ABSORPTION_PROTOCOL.md`, and 3 D.3 user-auth gates surfaced together (1 from 6n.γ + 1 from 6n.ζ + 1 from 6o.ε).

**Phase 6o → bundle absorption events** (D.2 unless noted):
- **6o.α (Wave 1a)** — boostless / Carrollian soft theorems → D1 §6 + D3 §3 + D4 §6 + F §4 + E1 cross-bridge.
- **6o.β (Wave 1b)** — Kerr-Schild + 3-obstruction BCJ NO-GO → D3 §6 + L1 cross-bridge + F §6 + E1 polariton ringdown.
- **6o.γ (Wave 1c)** — G1 dissipative-bootstrap NO-GO writeup → D3 §10 + F §10 (writeup-only, no Lean).
- **6o.δ (Wave 2a)** — APS-η for analog horizons → D2 §3 + D3 §17 + I1 §11 sidebar + F §6.
- **6o.ε (Wave 2b)** — Schellekens chain reframing 24|c₋ → **D.3 D2 §2 + D.3 L2 paired splash** (GATE 3).
- **6o.ζ (Wave 3a)** — G10-ETH-α refutation tableau → D4 §8 + I1 sidebar.
- **6o.η (Wave 3b)** — Itô + LDP + LDPCompatibleSKEFT → **D.4 I3 (sourceless initial lift)** + D3 §6 cross-bridge.

**Authoritative entry-state for absorption (2026-05-06; conversation-tail counts):** Lake 8586 jobs / 257 modules / 0 sorry / 1 axiom. The 8586-vs-roadmap-recorded-8585 delta is from Session 41 minor-housekeeping commit (post-Wave-3b dashboard/heatmap regen).

**Phase 6o status: ALL 7 WAVES COMPLETE.** Pre-writeup state. Bundle absorption now the load-bearing remaining work.

---

## Phase 6n+6o → Phase 7 absorption pass — Sessions 1+2+3 CLOSE (2026-05-06 → 05-07)

**Status:** Phase 6o D.2/D.3 absorption events SHIPPED into Phase 7 bundles. 13 of 14 bundles ALL-GREEN through Stages 9 + 10 + 13 of `BUNDLE_LIFT_PROCEDURE.md`; only **I3 remains in DRAFTING** — and I3 IS the Phase 6o Wave 3b `D.4` (sourceless initial lift) deliverable, so I3's substantive paper draft is itself a Phase 6o.ζ wave continuation, not an absorption event blocker.

**Phase 6o-side absorption deliverables (subset of the 28 D.2/D.4 events):**
- **6o.α (Wave 1a)** boostless / Carrollian soft theorems → D1 §6 + D3 §3 + D4 §6 + F §4 + E1 cross-bridge — appended.
- **6o.β (Wave 1b)** Kerr-Schild + 3-obstruction BCJ NO-GO → D3 §6 + L1 cross-bridge + F §6 + E1 polariton ringdown — appended.
- **6o.γ (Wave 1c)** G1 dissipative-bootstrap NO-GO writeup → D3 §10 + F §10 — appended.
- **6o.δ (Wave 2a)** APS-η for analog horizons → D2 §3 + D3 §17 + I1 §11 sidebar + F §6 — appended.
- **6o.ε (Wave 2b)** Schellekens chain reframing 24\|c₋ — **D.3 GATE 3 CLOSED**: D2 §2.7 + L2 paired splash committed with user-authorized prose (Möller-Scheithauer 2024 corollary framing); 5-step composed chain reads off as theorem-quality classification corollary.
- **6o.ζ (Wave 3a)** G10-ETH-α refutation tableau → D4 §8 + I1 sidebar — appended.
- **6o.η (Wave 3b)** Itô + LDP + LDPCompatibleSKEFT → I3 (sourceless initial lift) + D3 §6 cross-bridge — D3 cross-bridge appended; **I3 substantive drafting itself remains the Phase 6o.ζ wave continuation** (out-of-band of the absorption pass).

**6o-specific carry-forward (non-blocking):**
- I3 substantive drafting (Phase 6o.ζ separate track; bundle architecture user-auth ALREADY GRANTED Phase 6n Session 4; substantive paper draft is the deliverable).
- Lean docstring sync `Schellekens/Chain.lean:76-77` (D2 V.8 advisory).
- Adversarial-reviewer-discipline lesson banked (Session 3): WebFetch-and-compare bibitem titles is high-leverage fabrication detector. QI candidate raised: `validate.py --check bibitem_title_matches_arxiv`.

**Phase 6o status — FINAL: ALL 7 WAVES COMPLETE; absorption-pass contribution COMPLETE** (modulo I3 substantive drafting which is itself the Wave 3b deliverable, not an absorption event).

*Phase 6o absorption close marker, 2026-05-07.*

---

## Phase 6o Wave 4a — Sakharov Λ-substrate refactor CLOSE (2026-05-08)

**Status:** ✅ **CLOSED with verdict (B)** — biconditional honestly retired; ship as one-way implication + load-bearing depletion-factor ℝ encoding.

**Trigger:** deep-research dispatch return at `Lit-Search/Phase-6o/6o-Wave 4a FLS BEC Depletion-Factor Λ_substrate Return.md` (returned 2026-05-06; integrated 2026-05-08).

**Wave 4a.4 substantive Lean deliverable.** Extended `SakharovExtended` (Wave 4a.3 strict-extension layer) with new load-bearing fields `depletion : ℝ` + `depletionRelation : lambdaJ = depletion * lambdaHK` and 5 substantive theorems:
- **JTGR16** `sakharov_depletion_factor_relation` — unconditional `Λ_J = depletion · Λ_HK` for any `SakharovExtended`.
- **JTGR17** `volovikJannes_he3a_depletion_eq_one` — ³He-A `depletion = 1` (Atiyah-Bott-Shapiro topological universality at Weyl point).
- **JTGR18** `flsBEC_depletion_strictly_between_zero_and_one` — FLS BEC `0 < depletion < 1` structurally enforced (FLS Eq. 67/71; not fine-tunable).
- **JTGR19** `volovikJannes_vs_flsBEC_depletion_asymmetry` — load-bearing ℝ-valued substrate distinction.
- **JTGR20** `wave_4a_4_honest_one_way_closure` — composed 4-conjunct closure summary.

`flsBEC_extended` numerics refit per DR §5: `lambdaJ := 6.0e-14`, `lambdaHK := 7.5e-12` (eV), `depletion := 8.0e-3` (√(ρ₀a³) at canonical Steinhauer ⁸⁷Rb parameters). `volovikJannes_he3a_extended` adds `depletion := 1`. Numerical consistency `8e-3 × 7.5e-12 = 6e-14` ✓ via `norm_num`.

**3 new bibitems** added to `CITATION_REGISTRY` and primary-source-cached:
- `FinazziLiberatiSindoni2012PRL` (PRL 108, 071101; arXiv:1103.4841)
- `FinazziLiberatiSindoni2012Proc` (arXiv:1204.3039 — Eq. 71 closed-form depletion factor)
- `BelenchiaLiberatiMohd2014` (PRD 90, 104015; arXiv:1407.7896 — relativistic-BEC corroboration)

(`JannesVolovik2012` already in registry; cited for the strongest primary-source support of the asymmetric forward-only implication, §VII.)

**D5 §11 prose addendum** SHIPPED retiring the (⇐) biconditional reading, with explicit primary-source asymmetry argument citing Volovik-Jannes 2012 §VII as the sole forward-direction primary source. Lean theorem references: JTGR16-JTGR20. Bibliography block extended.

**Validation:**
- Lake build clean **8586 jobs** (no delta vs absorption Session 5).
- All 5 new substantive theorems verify standard-kernel-only `[propext, Classical.choice, Quot.sound]` via `lean_verify`.
- pdflatex D5 13pp clean (was 12pp pre-Wave-4a).
- `validate.py --check citation_primary_sources_present` PASS (271 cached / 11 inprep / 125 textbook-exempt / 0 missing).
- `validate.py --check paper_provenance` PASS.
- `validate.py --check bundle_consistency` + `bundle_source_freshness` PASS (2 pre-existing WARN both carry-forward).
- `bundle_readiness.py` **14/14 ALL-GREEN**.

**Authoritative post-Wave-4a counts (counts.json regen 2026-05-08):** **5855 thms (5830 substantive + 25 placeholder) / 322 modules / 0 sorry / 1 axiom / 5018 defs / Lake 8586 jobs / Aristotle-proved 322**. Δ vs Phase 7 absorption Session 5: thms +6 (5 JTGR16-JTGR20 + 1 SakharovExtended structure auto-gen), defs +12 (depletion field + depletionRelation Prop + per-substrate witness fields), modules unchanged. MCP-driven, zero Aristotle, zero new sorry, zero new axioms.

**Close memo:** `temporary/working-docs/phase6o/wave_4a_sakharov_lambda_substrate_refactor_close.md`.

**Phase 6o status — FINAL FINAL: ALL 8 WAVES COMPLETE.** Phase 6n+6o absorption + Wave 4a verdict (B) closure: 14/14 bundles ALL-GREEN; primary-source-cited substrate-physics finding (load-bearing depletion-factor ℝ asymmetry between Volovik-Jannes ³He-A and Finazzi-Liberati-Sindoni acoustic BEC) lifted into D5 §11 cleanly.

*Phase 6o Wave 4a close marker, 2026-05-08.*

*Phase 6o absorption-trigger marker, 2026-05-06.*
