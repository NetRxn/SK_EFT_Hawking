# Phase 6r: SymTFT Formalization — Substrate-to-Bulk Unification Under the Symmetry Topological Field Theory Umbrella

## Technical Roadmap — May 2026

*Prepared 2026-05-12 at Phase 6o close. Sources: planning conversation 2026-05-12 (4-phase scoping pass); user direction "find good fits for our pipeline & investigate directions that may lead to strengthening of the program and investigations that could plausibly make significant contributions to the physics/math/qc communities, and/or contribute meaningful no-gos"; Phase 6n Wave 1b SymTFT audit (substrate); `Lit-Search/_Exploratory/Modular : Conformal Bootstrap as a Uniqueness Argument...md` §8 Tier 3 — SymTFT preview track.*

**Trigger condition:** Phase 6r opens at Phase 6o close. The Phase 6n Wave 1b SymTFT audit produced the in-program substrate (DrinfeldCenter + PseudoUnitary + WittClass + Applicability + CrossBridges). Phase 6r promotes that substrate-level audit to a substantive SymTFT formalization line — connecting the program's substrate physics to bulk SymTFT machinery, and placing Standard Model matter on a topological boundary condition. This is the program's potential **unification crown**: reframing emergent-physics-from-substrate under a single SymTFT lens.

**Status (2026-05-12, Phase 6r stub):** **Roadmap stub committed at Track / Wave level**. Three Tracks, eight Waves. **Long-horizon track** by all prior project conventions; per `memory/feedback_loe_calibration.md`, "long-horizon" with this pipeline is single-digit weeks of session time, not years.

**Project rule (carried from Phase 6n/6o; user direction reaffirmed 2026-05-12):** **No PM / time / phase-cost estimates** anywhere in this roadmap. **No manuscript drafting at this phase** — Phase 6r stays at math/physics/Lean-substrate / infrastructure level. **No Mathlib PR drafts at this phase.**

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
>
> 1. **Mandatory project bootstrap** per `CLAUDE.md` Mandatory References list.
> 2. **Read `Phase6n_Roadmap.md` Wave 1b end-to-end** — Phase 6r consumes the Phase 6n SymTFT audit as substrate.
> 3. **Read this roadmap end-to-end** before claiming any wave assignment.
> 4. **Read the planning brief `memory/project_phase_6p6q6r6s_planning.md`** for entry-state context.
> 5. **Critical predecessor modules + literature — read source directly:**
>    - **Phase 6n Wave 1b SymTFT audit substrate (heaviest dependency):** `lean/SKEFTHawking/SymTFTAudit/*.lean` (DrinfeldCenter, PseudoUnitary, FreeKLinearCategory, FreeKLinearMonoidal, DeligneTensor, WittClass, CrossBridges, Applicability). This is the existing in-program substrate.
>    - **Phase 5b-5p categorical chain:** paper11 quantum group + paper14 braided MTC + paper16_wrt_tqft WRT TQFT (the modular tensor category infrastructure that the SymTFT bulk needs).
>    - **Phase 6o Wave 2b G1-Schellekens chain** (shipped Session 39): `lean/SKEFTHawking/Schellekens/Chain.lean` — the 5-step categorical/topological chain from spin-bordism to c=24 holomorphic VOA classification. SymTFT-adjacent infrastructure.
>    - **Phase 6n Wave 1c heat-kernel ↔ AS reformulation memo:** `temporary/working-docs/phase6n/6n_eta_AS_reformulation_memo.md` — substrate for the SymTFT-via-AS-index identification.
>    - **Phase 6o Wave 2a APS-η for analog-horizon backgrounds:** `lean/SKEFTHawking/APSEta/*.lean` — SymTFT-via-Witten-Yonekura η/16 mod 1 identification was the substrate for the Wave 2a SymTFTBridge module.
>    - **Mathlib4 categorical infrastructure:** `Mathlib/CategoryTheory/*` — especially `Mathlib.CategoryTheory.Monoidal.Braided`, `Mathlib.CategoryTheory.Center`, `Mathlib.CategoryTheory.Bicategory` (substrate for SymTFT bulk-boundary correspondence).
>    - **Fresh DR substrate (REQUIRED before Wave 1a):** Phase 6r MUST start with a deep-research dispatch on SymTFT literature 2024-2026 — the field is moving fast and the formalization choices depend on which definitional framework the community converges on. **Wave 1a.1 cannot proceed without fresh DR return.**
> 6. **`LATE_PHASE6_ABSORPTION_PROTOCOL.md` — load before any bundle-touching work.**
> 7. **Apply preemptive-strengthening checklist** + **primacy-claim discipline** per `memory/project_2026_05_12_first_claim_close.md`. **CRITICAL for Phase 6r:** the SymTFT formalization is the kind of work that most invites "first SymTFT formalization in Lean" framing. Resist this framing per `project_2026_05_12_first_claim_close.md`; ship descriptive content-first prose.
> 8. **Do not delegate Lean theorem proving to subagents.** MCP loop default; Aristotle is fallback. **Pre-flight Explore-agent dispatch IS authorized for substrate scouting** — Phase 6r has the longest substrate-discovery surface of the 4 new phases, so substrate scouts are particularly valuable.
> 9. **No PM / time estimates anywhere** — by user direction.
> 10. **No manuscript drafting at this phase.** Bundle absorption deferred per Phase 6n Session-5 convention.

---

## Wave catalog — Shape D (3 Tracks × 8 Waves)

Eight waves across three Tracks. Track 1 = SymTFT axiomatization (the bulk-side substrate). Track 2 = SymTFT-with-fermions extension. Track 3 = SM-matter-on-topological-boundary application.

**Status legend:**
- ✅ **SHIPPED** — Lean / numerical / memo deliverables committed; bundle absorption deferred.
- 🟡 **IN-PROGRESS** — partial deliverables shipped.
- 📝 **WORKING DOC** — Stage-1 substrate-analysis or audit draft exists; no Lean yet.
- ⏳ **NOT STARTED** — substrate ready; awaiting dispatch.

| Wave | Codename | Status | Bundle absorption | Branch | User-auth gate |
|---|---|---|---|---|---|
| **Track 1 — SymTFT axiomatization (bulk-side substrate)** | | | | | |
| **Wave 1a** | SymTFT substrate analysis + fresh DR | ⏳ NOT STARTED | n/a (working doc) | n/a | **YES** — fresh DR dispatch required pre-Wave |
| **Wave 1b** | Bulk SymTFT data: 3D TQFT predicate + Z(C) Drinfeld-center reading | ⏳ NOT STARTED | D4 extension + new bundle candidate — DEFERRED | **D.4 candidate** | none |
| **Wave 1c** | Boundary condition substrate: gapped boundaries + Lagrangian-algebra characterization | ⏳ NOT STARTED | D4 extension — DEFERRED | **D.2** | none |
| **Wave 1d** | SymTFT bulk-boundary correspondence: Drinfeld-center ≃ Z(boundary-algebra-Lagrangian) | ⏳ NOT STARTED | D4 + D2 (anomaly) — DEFERRED | **D.2** | none |
| **Track 2 — SymTFT-with-fermions extension** | | | | | |
| **Wave 2a** | Spin-SymTFT axiomatization (fermionic extension) | ⏳ NOT STARTED | D2 (anomaly substrate) + D4 — DEFERRED | **D.2** | none |
| **Wave 2b** | Z₁₆ classification via Spin-SymTFT (Witten-Yonekura connection) | ⏳ NOT STARTED | D2 (refines Z₁₆ section) — DEFERRED | **D.3 candidate** | possibly **YES** (D2 reframing) |
| **Track 3 — SM matter on topological boundary** | | | | | |
| **Wave 3a** | SM matter content as topological-boundary-condition data | ⏳ NOT STARTED | D2 + L2 — DEFERRED | **D.2** | none |
| **Wave 3b** | Substrate-to-bulk-SymTFT identification + flagship-F unification chapter | ⏳ NOT STARTED | F flagship (substantive new chapter) + new bundle candidate — DEFERRED | **D.3 candidate** | possibly **YES** (F flagship reframing) |

**Wave dependencies:**
- Wave 1a is the substrate-analysis entry point; depends on fresh DR.
- Wave 1b depends on Wave 1a; produces the bulk SymTFT data predicate.
- Wave 1c depends on Wave 1a; produces the boundary-condition substrate. Can run in parallel with Wave 1b.
- Wave 1d depends on Waves 1b + 1c (combines bulk + boundary into the correspondence).
- Wave 2a depends on Waves 1b + 1c (fermionic extension of bulk + boundary substrates).
- Wave 2b depends on Wave 2a; produces the Z₁₆ classification via SymTFT (substantive new content connecting paper8/paper9 substrate to the SymTFT axiomatization).
- Wave 3a depends on Wave 1d (SM matter as topological-boundary data needs the bulk-boundary correspondence).
- Wave 3b depends on all prior waves (flagship-F unification needs the full substrate).

**Coherent sub-narrative.** The phase produces a single substantive sub-narrative: *"the program's emergent-physics-from-substrate substrate is the boundary condition of a SymTFT bulk."* Each component (categorical substrate, fermionic extension, SM matter as boundary data) builds toward the flagship-F unification chapter at Wave 3b. The flagship-F chapter is the **unification crown** — the substantive reframing that makes the program's various bundles cohere under a single conceptual umbrella.

**Recommended next-up order:**

1. **Wave 1a** SymTFT substrate analysis (REQUIRES fresh DR dispatch; this is the deepest substrate-discovery surface of the 4 new phases).
2. **Wave 1b** Bulk SymTFT data (in parallel with Wave 1c after Wave 1a closes).
3. **Wave 1c** Boundary condition substrate (in parallel with Wave 1b).
4. **Wave 1d** Bulk-boundary correspondence (after Waves 1b + 1c).
5. **Wave 2a** Spin-SymTFT axiomatization (after Wave 1d).
6. **Wave 2b** Z₁₆ classification via Spin-SymTFT (after Wave 2a).
7. **Wave 3a** SM matter on topological boundary (after Wave 1d; possibly in parallel with Waves 2a-2b).
8. **Wave 3b** Substrate-to-bulk identification + flagship-F unification (after all prior waves; the unification crown).

**Pre-Phase-7 bundle absorption gate:** all 8 Phase 6r Waves close → unified Phase 6r → Phase 7 absorption pass. **Two D.3 candidate gates:** Wave 2b (D2 Z₁₆ reframing via SymTFT) and Wave 3b (F flagship unification chapter) require user-authorization at bundle-absorption pass.

---

## Wave 1a — SymTFT substrate analysis + fresh DR ⏳ NOT STARTED

**Sub-wave decomposition (proposed):**

- **Wave 1a.1 (fresh DR dispatch — REQUIRED before Lean work):** DR task at `Lit-Search/Tasks/submitted/<date>_SymTFT_2024_2026_substrate.md` covering: (a) SymTFT definitional consolidation 2024-2026 — Kaidi-Ohmori-Zheng arXiv:2209.11062 + Apruzzi-Bonetti-Garcia-Etxebarria-Hosseini-Schäfer-Nameki arXiv:2112.02092 + recent 2024-2026 reformulations; (b) state of SymTFT-with-fermions literature — Aasen-Mong-Fendley arXiv:2008.08598 + recent 2024-2026 fermionic SymTFT papers; (c) any prior formalization in Lean / Coq / Isabelle / HOL Light / Mizar (likely zero per Phase 6o I3 cross-prover survey methodology); (d) PhysLean SymTFT roadmap or community direction (Tooby-Smith / Rothgang / van Doorn coordination); (e) which definitional framework (Kaidi-Ohmori-Zheng's 3D-anyon-theory definition vs. Schäfer-Nameki's higher-categorical definition vs. Lurie-style ∞-categorical definition) is most tractable for Lean formalization while still being community-canonical. **This DR is the substantive entry-point of the phase; substrate decisions made here determine the rest of the wave catalog.**
- **Wave 1a.2 (substrate analysis + working doc):** read DR return end-to-end; map the SymTFT axiomatization onto the program's existing SymTFT-audit substrate (`SymTFTAudit/*.lean`); identify where the existing audit substrate IS the SymTFT substrate (likely: DrinfeldCenter + WittClass are direct hits; FreeKLinearCategory + DeligneTensor are the categorical algebra; CrossBridges + Applicability provide cross-bridges). Working doc at `temporary/working-docs/phase6r/wave_1a_SymTFT_substrate.md`.
- **Wave 1a.3 (predicate substrate scaffolding):** `lean/SKEFTHawking/SymTFT/Predicate.lean` — `IsSymTFT B C` Prop on a (bulk B, boundary C) pair; substrate-data level operationalization. Predicates encode (a) bulk B is a 3D TQFT (Drinfeld-center-of-fusion-category-data); (b) boundary C is a fusion category; (c) the bulk-boundary correspondence Z(C) ≃ B at predicate level. Cross-bridge to existing `SymTFTAudit/WittClass.lean` + `SymTFTAudit/DrinfeldCenter.lean`.

**Three-question template:**

- *Integrates with:* Phase 6n Wave 1b SymTFT audit substrate (the heaviest dependency); paper11/paper14/paper16_wrt_tqft categorical chain; Mathlib4 categorical infrastructure; PhysLean SymTFT roadmap (if any); current SymTFT literature.
- *New constraint adds:* a fresh DR substrate-analysis identifying the canonical SymTFT axiomatization for Lean formalization, mapped onto the program's existing audit substrate.
- *Tension surfaces:* (i) SymTFT definitional consolidation is in flux — the DR may surface that the field has not yet converged on a single canonical axiomatization, in which case Phase 6r commits to one definitional framework (likely Kaidi-Ohmori-Zheng's 3D-anyon-theory definition for tractability) and documents the choice explicitly; (ii) the program's existing `SymTFTAudit` substrate uses categorical-Witt-class language; the SymTFT literature may use higher-categorical language — substrate scout dispositive on whether existing substrate suffices or requires extension; (iii) the DR dispatch is the load-bearing entry point; if the DR surfaces that the community-canonical definitional framework is incompatible with Mathlib4 categorical infrastructure (e.g., requires ∞-categories not present in Mathlib), Phase 6r decomposes into "substrate-level operationalization on tractable subset" + "Mathlib-substrate-gap memo for community coordination."

**Substrate.** Kaidi-Ohmori-Zheng arXiv:2209.11062; Apruzzi-Bonetti-Garcia-Etxebarria-Hosseini-Schäfer-Nameki arXiv:2112.02092; Aasen-Mong-Fendley arXiv:2008.08598; existing `SymTFTAudit/*.lean`; PhysLean roadmap (community coordination).

**Module decomposition (Lean):**
```
SKEFTHawking/SymTFT/
  Predicate.lean       -- IsSymTFT B C predicate; SymTFTData data structure
  -- (Wave 1b will add bulk content; Wave 1c will add boundary content)
```

**Bundle absorption.** n/a (working doc + predicate scaffolding only; no substantive content yet).

**Risk axes.**
- **SymTFT definitional flux** — community has not yet converged; risk mitigated by explicit definitional-framework commitment + documentation.
- **Mathlib4 categorical infrastructure adequacy** — Mathlib has fusion categories + Drinfeld center; less clear on the full SymTFT bulk-boundary correspondence; substrate scout dispositive.
- **PhysLean coordination dependency** — if PhysLean has begun SymTFT work, coordinate; if not, Phase 6r is the program's contribution.
- **The fresh DR dispatch is load-bearing**; cannot proceed without it.

---

## Wave 1b — Bulk SymTFT data: 3D TQFT predicate + Z(C) Drinfeld-center reading ⏳ NOT STARTED

**Sub-wave decomposition (proposed; matures after Wave 1a):**

- **Wave 1b.1 (3D TQFT predicate substrate):** `lean/SKEFTHawking/SymTFT/BulkTQFT.lean` — `Is3DTQFT B` Prop on bulk data B; specializes the more general Atiyah-style cobordism-category TQFT definition to the 3D case. Cross-bridge to paper16_wrt_tqft `WRTInvariant.lean` (the existing 3D quantum invariant from MTC data is a substantive instance of Wave 1b.1's predicate).
- **Wave 1b.2 (Z(C) Drinfeld-center reading):** `lean/SKEFTHawking/SymTFT/DrinfeldCenter.lean` — substantive lemma: the Drinfeld center Z(C) of a fusion category C is a 3D TQFT (canonical SymTFT bulk reading). Cross-bridge to existing `SymTFTAudit/DrinfeldCenter.lean`.
- **Wave 1b.3 (substantive instance on Ising / Fibonacci):** explicit instance theorems: Z(Ising-MTC) and Z(Fibonacci-MTC) as 3D TQFTs (substantive content reading from paper14's existing MTC substrate).

**Three-question template:**

- *Integrates with:* Wave 1a substrate; paper14 Ising + Fibonacci MTCs; paper16_wrt_tqft WRT invariant; existing `SymTFTAudit/DrinfeldCenter.lean`.
- *New constraint adds:* Lean substrate for the bulk SymTFT data (3D TQFT + Drinfeld-center reading) on the program's existing categorical substrate.
- *Tension surfaces:* (i) the 3D TQFT predicate substrate is fairly mature in the categorical literature; cleanest substantive deliverable of the phase; (ii) the existing `WRTInvariant.lean` is already a substantive instance — so Wave 1b.3 is "lift the WRTInvariant content to the SymTFT-bulk-language" rather than fresh content.

**Substrate.** Wave 1a substrate; paper14 + paper16_wrt_tqft categorical chain; existing `SymTFTAudit/DrinfeldCenter.lean`.

**Bundle absorption.** D.2 / D.4 candidate; final placement at Wave 3b close.

**Risk axes.**
- Atiyah-style cobordism-category TQFT predicate may pull in cobordism-category infrastructure not currently in Mathlib4 — substrate scout dispositive on whether to encode at predicate level or substantive level.

---

## Wave 1c — Boundary condition substrate: gapped boundaries + Lagrangian-algebra characterization ⏳ NOT STARTED

**Sub-wave decomposition (proposed):**

- **Wave 1c.1 (gapped-boundary predicate):** `lean/SKEFTHawking/SymTFT/GappedBoundary.lean` — `IsGappedBoundary C B` Prop on (boundary category C, bulk TQFT B); substantive structural property at predicate-substrate level.
- **Wave 1c.2 (Lagrangian-algebra characterization):** `lean/SKEFTHawking/SymTFT/LagrangianAlgebra.lean` — substantive lemma: gapped boundaries of a 3D TQFT are in bijection with Lagrangian algebras in the boundary fusion category. Cross-bridge to existing categorical infrastructure.
- **Wave 1c.3 (substantive instance on toric code / Vec_G):** explicit instance theorems on toric-code boundary (e and m boundary types correspond to two Lagrangian algebras in Z(Vec_Z₂)) and Vec_G general case.

**Three-question template:**

- *Integrates with:* Wave 1a substrate; paper9 Drinfeld center computations (`Z(Vec_Z/2) ≃ toric code`; `Z(Vec_S3)`); paper14 Müger center substrate; existing `SymTFTAudit/*.lean`.
- *New constraint adds:* Lean substrate for the boundary-side SymTFT data (gapped boundaries + Lagrangian-algebra characterization).
- *Tension surfaces:* (i) Lagrangian algebras in fusion categories are categorical-algebra content; Mathlib4 has algebras-in-monoidal-categories infrastructure (recent — Tooby-Smith / Rothgang work) — substrate scout dispositive on adequacy; (ii) toric code substantive instance is the natural concrete witness — paper9's existing Drinfeld-center computation supports this directly.

**Substrate.** Wave 1a substrate; paper9 Drinfeld center modules; Mathlib4 categorical algebra infrastructure.

**Bundle absorption.** D.2 additive into D4 extension.

**Risk axes.**
- Lagrangian-algebra-in-fusion-category infrastructure adequacy.
- Cross-bridge to paper9 + paper14 substrate — should be clean.

---

## Wave 1d — SymTFT bulk-boundary correspondence ⏳ NOT STARTED

**Sub-wave decomposition (proposed):**

- **Wave 1d.1 (correspondence statement):** `lean/SKEFTHawking/SymTFT/BulkBoundaryCorrespondence.lean` — substantive theorem: for any fusion category C with a Lagrangian algebra A, the boundary theory described by A on the Drinfeld-center bulk Z(C) recovers C. This is the core SymTFT correspondence.
- **Wave 1d.2 (anomaly classification reading):** substantive cross-bridge connecting the Wave 1d.1 correspondence to anomaly classification — the SymTFT bulk captures the anomaly content of the boundary theory; cross-bridge to paper9 anomaly substrate.
- **Wave 1d.3 (Witten-Yonekura η/16 reading):** substantive cross-bridge connecting the Wave 1d.1 correspondence to the Z₁₆-anomaly content. Cross-bridge to Phase 6o Wave 2a APS-η SymTFTBridge module.

**Three-question template:**

- *Integrates with:* Waves 1b + 1c; paper9 anomaly substrate; Phase 6o Wave 2a APS-η bridge.
- *New constraint adds:* the substantive bulk-boundary SymTFT correspondence + anomaly-classification reading.
- *Tension surfaces:* (i) the correspondence statement is the core SymTFT content; substrate scout dispositive on tractable formalization level; (ii) the anomaly-classification cross-bridge at Wave 1d.2 is genuinely new content connecting paper9's existing anomaly substrate to the SymTFT axiomatization; (iii) the Witten-Yonekura η/16 cross-bridge at Wave 1d.3 may surface alignment / misalignment with the Phase 6o Wave 2a result (productive either way).

**Substrate.** Waves 1b + 1c; paper9 anomaly modules; Phase 6o Wave 2a APS-η modules.

**Bundle absorption.** D.2 additive into D4 + D2 (anomaly section).

**Risk axes.**
- Substantive correspondence theorem is the load-bearing content of Track 1; substrate scout dispositive on formalization level.
- Anomaly cross-bridge may surface obstructions or new alignments.

---

## Wave 2a — Spin-SymTFT axiomatization (fermionic extension) ⏳ NOT STARTED

**Sub-wave decomposition (proposed):**

- **Wave 2a.1 (substrate analysis + working doc):** read DR return on fermionic SymTFT literature; identify the canonical spin-SymTFT axiomatization (likely Aasen-Mong-Fendley + recent 2024-2026 work). Working doc at `temporary/working-docs/phase6r/wave_2a_spin_SymTFT_substrate.md`.
- **Wave 2a.2 (spin-SymTFT predicate):** `lean/SKEFTHawking/SymTFT/SpinSymTFT.lean` — `IsSpinSymTFT B C` Prop extending Wave 1a's `IsSymTFT` with fermionic substrate-data; cross-bridge to paper8 Pin⁺ bordism substrate.
- **Wave 2a.3 (substantive instance on Z₁₆-classified SymTFT):** explicit instance theorem on the Z₁₆-classified spin-SymTFT corresponding to the SM with right-handed neutrinos. Cross-bridge to paper8 + paper9 substrate.

**Three-question template:**

- *Integrates with:* Wave 1d (bulk-boundary correspondence); paper8 Pin⁺ bordism + Z₁₆ classification substrate; paper9 SM anomaly content.
- *New constraint adds:* a Lean substrate for the spin-SymTFT (fermionic SymTFT) extension; substantive instance on the program's Z₁₆ anomaly content.
- *Tension surfaces:* (i) fermionic SymTFT literature is even less consolidated than the bosonic case; substrate scout dispositive on canonical axiomatization choice; (ii) the cross-bridge to paper8 Pin⁺ bordism is a substantive structural alignment question — productive either way.

**Substrate.** Wave 1d substrate; paper8 Pin⁺ bordism + Z₁₆ classification; paper9 SM anomaly modules.

**Bundle absorption.** D.2 additive into D2 (anomaly substrate) + D4 (categorical substrate).

**Risk axes.**
- Fermionic SymTFT literature consolidation.
- Cross-bridge alignment with paper8 Pin⁺ substrate.

---

## Wave 2b — Z₁₆ classification via Spin-SymTFT ⏳ NOT STARTED

**Sub-wave decomposition (proposed):**

- **Wave 2b.1 (Z₁₆-classification-via-SymTFT theorem):** `lean/SKEFTHawking/SymTFT/Z16ViaSpinSymTFT.lean` — substantive theorem: the Z₁₆ classification of SM anomalies is recovered as the spin-SymTFT classification of fermionic boundary conditions on the SymTFT bulk. Cross-bridge to paper9's existing Z₁₆ classification.
- **Wave 2b.2 (Witten-Yonekura η/16 connection):** substantive cross-bridge: the Spin-SymTFT classification at Wave 2b.1 is precisely the Witten-Yonekura η/16 mod 1 anomaly invariant. Cross-bridge to Phase 6o Wave 2a APS-η.
- **Wave 2b.3 (D2 reframing pre-draft for user review):** working-doc-grade text at `temporary/working-docs/phase6r/wave_2b_D2_reframing_predraft.md` — drop-in section replacement prose for `papers/D2/paper_draft.tex` reframing the Z₁₆ classification under the spin-SymTFT umbrella. **HELD for user review at unified bundle-absorption pass.**

**Three-question template:**

- *Integrates with:* Wave 2a substrate; paper8 + paper9 substrate; D2 bundle; Phase 6o Wave 2a APS-η bridge.
- *New constraint adds:* substantive theorem identifying the program's existing Z₁₆ classification as a spin-SymTFT classification result. **D.3 candidate** — refines D2's current Z₁₆ content from "anomaly-cancellation constraint" to "spin-SymTFT-boundary-classification corollary."
- *Tension surfaces:* (i) the substantive identification is mathematically subtle (spin-SymTFT formal framework + Z₁₆ explicit content); substrate scout dispositive; (ii) D2 reframing is a D.3 absorption event — same pattern as Phase 6o Wave 2b G1-Schellekens chain D2 reframing; (iii) cross-bridge to Witten-Yonekura η/16 may surface alignment / misalignment with Phase 6o Wave 2a result.

**Substrate.** Wave 2a substrate; paper8 + paper9 + Phase 6o Wave 2a modules; D2 paper draft.

**Bundle absorption.** D.3 candidate (D2 reframing). User-authorization gate at Wave 2b.3 close.

**Risk axes.**
- Substantive identification mathematical subtlety.
- D2 reframing D.3 user-auth gate.

---

## Wave 3a — SM matter on topological boundary ⏳ NOT STARTED

**Sub-wave decomposition (proposed):**

- **Wave 3a.1 (substrate analysis + working doc):** read DR return on "SM matter as topological-boundary-condition data" literature (Tachikawa-Yonekura + Schäfer-Nameki + recent 2024-2026 work). Working doc at `temporary/working-docs/phase6r/wave_3a_SM_matter_on_boundary_substrate.md`.
- **Wave 3a.2 (SM-matter-as-boundary-data predicate):** `lean/SKEFTHawking/SymTFT/SMMatterBoundary.lean` — `IsSMMatterTopologicalBoundary B C` Prop characterizing the SM matter content as boundary-condition data on a SymTFT bulk; cross-bridge to paper9 SM-anomaly substrate + paper10 modular-generation substrate.
- **Wave 3a.3 (substantive theorem on 3-generation constraint via SymTFT):** substantive theorem: the SM 3-generation constraint $N_f \equiv 0 \pmod 3$ (paper10's existing result) is recovered as a SymTFT-boundary-condition constraint. Cross-bridge to paper10's existing modular-invariance derivation.

**Three-question template:**

- *Integrates with:* Wave 1d (bulk-boundary correspondence); paper9 SM anomaly; paper10 modular generation; paper17 dark sector (SymTFT-extended-substrate as dark-sector substrate).
- *New constraint adds:* substantive Lean substrate identifying SM matter content as SymTFT-boundary-condition data; substantive theorem recovering the 3-generation constraint from the SymTFT framework.
- *Tension surfaces:* (i) the SM-matter-as-boundary-data framing is the natural reading of paper9 + paper10 results under the SymTFT umbrella; (ii) the substantive theorem at Wave 3a.3 is the highest-leverage substantive deliverable of the phase — it directly reframes the program's existing 3-generation constraint result under the SymTFT lens; (iii) cross-bridge to paper17 dark sector may surface new structural alignments (the dark-sector content as alternative SymTFT-boundary-condition data).

**Substrate.** Wave 1d substrate; paper9 + paper10 modules; paper17 dark sector substrate.

**Bundle absorption.** D.2 additive into D2 (substantive new section) + L2 (3-generation constraint substrate).

**Risk axes.**
- The substantive theorem at Wave 3a.3 depends on the spin-SymTFT framework (Wave 2a-2b output); could decompose into "shippable subset on bosonic-SymTFT-only formulation" + "fermionic-SymTFT-full formulation."

---

## Wave 3b — Substrate-to-bulk-SymTFT identification + flagship-F unification chapter ⏳ NOT STARTED

**This is the unification crown wave.**

**Sub-wave decomposition (proposed):**

- **Wave 3b.1 (substantive substrate-to-bulk identification):** `lean/SKEFTHawking/SymTFT/SubstrateToBulkIdentification.lean` — substantive theorem identifying the program's emergent-physics-from-substrate substrate (the SK-EFT-Hawking substrate) as a SymTFT-boundary-condition reading of a specific SymTFT bulk. Cross-bridge to all prior Phase 6r waves + the program's emergent-physics substrate.
- **Wave 3b.2 (flagship-F unification chapter — substantive draft):** flagship-F substantive new chapter at `papers/F/paper_draft.tex` reframing the program's narrative under the SymTFT umbrella: "What the SK-EFT-Hawking substrate is, in SymTFT language." Working-doc-grade text at `temporary/working-docs/phase6r/wave_3b_F_unification_chapter_predraft.md`. **HELD for user review at unified bundle-absorption pass.**
- **Wave 3b.3 (bundle architecture impact + new-bundle candidate):** working doc analyzing whether the Phase 6r content warrants creating a new bundle (e.g., "F2 — SymTFT-unified emergent-physics-from-substrate framework") or extends F flagship. Same pattern as Phase 6p Wave 3b. **User-authorization gate REQUIRED here** if new-bundle creation decided.

**Three-question template:**

- *Integrates with:* All prior Phase 6r waves; F flagship paper draft; bundle architecture; all the program's existing bundles (D1-D5, L1-L3, I1-I3, E1-E2).
- *New constraint adds:* the program's unification crown — the substantive reframing of the SK-EFT-Hawking substrate as a SymTFT boundary condition. **D.3 candidate** for the F flagship reframing.
- *Tension surfaces:* (i) the unification chapter is the most ambitious deliverable of the phase; substrate scout dispositive on tractable formalization level; (ii) bundle-architecture decision is strategic; user-authorization required if new-bundle creation; (iii) the unification reading may surface that not all bundles fit cleanly under the SymTFT umbrella — productive structural finding either way.

**Substrate.** All prior Phase 6r waves; F flagship; all existing bundles; bundle architecture (`PAPER_STRATEGY.md`).

**Bundle absorption.** D.3 candidate (F flagship reframing) + possible new bundle creation.

**Risk axes.**
- The unification chapter is the most ambitious substantive deliverable; substrate scout dispositive.
- Bundle-architecture decision (new bundle vs F extension) is strategic; user-authorization required.
- Some bundles may not fit cleanly under SymTFT — productive structural finding.

---

## User authorization gates — consolidated

| Wave | Authorization point | Authorization required for | Status |
|---|---|---|---|
| **Wave 1a** Fresh DR dispatch | DR task submission | YES — DR-task submission is user-action (per CLAUDE.md DR convention) | 🔒 **PENDING** Wave 1a.1 dispatch |
| **Wave 2b** D2 reframing pre-draft | D.3 absorption event for D2 Z₁₆ reframing | **YES — D.3 user-authorization required at bundle-absorption pass** | 🔒 **HELD** for unified bundle-absorption pass |
| **Wave 3b** F flagship unification chapter / new-bundle creation | D.3 absorption event for F flagship + potential new bundle creation | **YES — D.3 user-authorization + potential new-bundle creation requires `PAPER_STRATEGY.md` update** | 🔒 **HELD** for unified bundle-absorption pass |

---

## Phase 6r-internal further-deferred tracks

- **Higher-categorical SymTFT** (∞-categorical reformulation) — multi-year community coordination; track Lurie-style infrastructure progress; consider for Phase 6r+1.
- **SymTFT-with-supersymmetry** — extend the spin-SymTFT framework with supersymmetric content; substrate-discovery yield uncertain; consider after Phase 6r 8 waves close.

---

## Cross-references

- `docs/roadmaps/Phase6n_Roadmap.md` Wave 1b — SymTFT audit substrate (heaviest dependency).
- `docs/roadmaps/Phase6o_Roadmap.md` Wave 2a + Wave 2b — APS-η + Schellekens chain substrate.
- `docs/roadmaps/Phase6p_Roadmap.md` — sibling phase (fault-tolerant QC).
- `docs/roadmaps/Phase6q_Roadmap.md` — sibling phase (DKM transport bootstrap).
- `docs/roadmaps/Phase6s_Roadmap.md` — sibling phase (1c bootstrap + I3 substantive lift).
- `memory/project_phase_6p6q6r6s_planning.md` — strategic entry-state brief.
- `memory/feedback_loe_calibration.md` — pipeline speed calibration.
- `Lit-Search/_Exploratory/Modular : Conformal Bootstrap as a Uniqueness Argument...md` §8 Tier 3 — SymTFT preview substrate.
- arXiv:2209.11062 Kaidi-Ohmori-Zheng — SymTFT primary source.
- arXiv:2112.02092 Apruzzi-Bonetti-Garcia-Etxebarria-Hosseini-Schäfer-Nameki — SymTFT primary source.
- arXiv:2008.08598 Aasen-Mong-Fendley — fermionic SymTFT substrate.

---

*Created 2026-05-12 at Phase 6o close. Per-wave decomposition + 3-question template + module decomposition + bundle absorption + risk axes. Updates atomically as waves close.*

---

## Sessions log

*Empty — Phase 6r has not yet been dispatched. **Note:** Wave 1a fresh DR dispatch is required before Lean work can begin.*
