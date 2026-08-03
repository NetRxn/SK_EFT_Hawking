# Absorbability & Strategy Drift — Publication-Readiness Audit (process layer)

**Auditor:** CROSS-absorbability-and-strategy-drift   **Date:** 2026-08-01

**Scope:** the process layer only — whether the documented publication strategy matches
reality, and whether the machinery can absorb future work without redrafting. Manuscript
prose is the sibling auditors' scope and is not re-audited here; where manuscript-level
facts appear they are used only as *evidence about the process that produced them*.

**Artifacts examined:**
`docs/PAPER_STRATEGY.md`, `docs/PAPER_DRAFT_MAPPING.md`, `docs/BUNDLE_LIFT_PROCEDURE.md`,
`docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md`, `docs/6E_SERIES_ABSORPTION_HANDOFF.md`,
`docs/BUNDLE_DIRECTORY_SCHEMA.md`, `docs/PAPER_TABLES_STATUS.md`,
`docs/WAVE_EXECUTION_PIPELINE.md`, `docs/QI_REGISTER.md`, `docs/READINESS_GATES.md`,
`docs/BUNDLE_READINESS_HEATMAP.md`, `docs/RESEARCH_STATUS_OVERVIEW.md`,
`docs/ARXIV_DEPOSIT_PLAN.md`, all 119 files in `docs/roadmaps/`,
`scripts/bundle_readiness.py`, `scripts/readiness_gates.py`, `scripts/validate.py`,
`scripts/bundle_append.py`, `scripts/check_bundle_source_freshness.py`,
`scripts/compile_bundle_pdf.py`, all 21 `papers/<X>/bundle_metadata.json` +
`append_log.json` + `change_log.md`, and git history on both procedure documents.

Commands run:
```bash
uv run python scripts/validate.py --check bundle_source_freshness
uv run python scripts/validate.py --check paper_toolchain_pin_drift
uv run python scripts/validate.py --list
git log --oneline --follow -- docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md
git log --oneline --follow -- docs/BUNDLE_LIFT_PROCEDURE.md
git log --oneline -30 -- papers/D11 papers/D12
```

---

## Verdict summary

| Task | Verdict |
|---|---|
| 1. Strategy-vs-reality drift | **60 drift items** across 11 process documents + 7 roadmap headers. The 2026-05-07 §3 status note is the most visible, but the load-bearing one is Pipeline Invariant #14 naming an 18-target roster that cannot legally accept D10/D11/D12 work. |
| 2. Phase → bundle routing | See §2. **8 fully-executed phases have no bundle home and no lift**; **~340 kernel-verified Lean modules across 6 arcs appear in no bundle draft**; the 6A\* series is double-homed (D6 vs D9) across 7 roadmaps; D4 §9.8 is a phantom destination declared by 5 phases and holding none of them. |
| 3. Absorption-protocol fitness | Protocol **has** been exercised (~36 events). But its **trigger is structurally dead for every bundle authorized since D6** — a code defect, not a documentation one. It has **no branch for a defective target bundle**, which is now the normal case. |
| 4. Lift-procedure failure modes | The procedure is producing defective output by construction. **No step owns manuscript-level quality.** Root causes localised to §3a, §6, §7, §11, §12, §14. |
| 5. Gate coverage gap | **Confirmed.** Nothing in the entire gate machinery measures length, structure, figure adequacy, or voice. One gate (FirstClaimVerification) was never implemented; one (NarrativeGrounding) covers only the abstract. |
| 6. Pending work not in strategy | 5 live/authorized threads + ~34 pin-drift sites have no landing declaration. |

**Portfolio-level statement.** The strategy documents describe a 14–18 bundle portfolio that
shipped GREEN in May 2026. The repository contains a 21-bundle portfolio that is 15 RED, in
which 14 of 21 bundles carry a recorded `stage13_status: "green"` while holding open blockers,
and 9 of 21 ship zero figures. The documents are not merely stale; **several of them assert
the opposite of the artifact.**

---

## 1. Strategy-vs-reality drift ledger

Severity per the shared rubric. `file:line → assertion → correcting evidence`.

### 1.1 `docs/PAPER_STRATEGY.md`

| ID | Sev | Location | Assertion | Correcting evidence |
|---|---|---|---|---|
| S-01 | **P0** | `PAPER_STRATEGY.md:341` | "**All 14 bundles have shipped Stage 9 + Stage 10 + Stage 13 reviewer triples GREEN** per `BUNDLE_READINESS_HEATMAP.md` after Phase 7 absorption Sessions 1–5" | `BUNDLE_READINESS_HEATMAP.md:23-43` (regenerated 2026-08-01): **15 RED, 4 YELLOW, 1 GREEN, 1 YELLOW-P1-blocked, of 21**. Also the roster is 21, not 14. Both halves of the sentence are false. |
| S-02 | **P0** | `PAPER_STRATEGY.md:332` | "D5 depends on … Phase 6m Tracks A/B/C closure (in progress). **Blocked on Phase 6m.**" | `docs/roadmaps/Phase6m_Roadmap.md:3`: "**Phase 6m FULLY CLOSED** at the Lean-formalization scope" — dated **2026-04-30**, i.e. two days *before* this strategy document's §3 was written. The blocker has never existed in the document's own lifetime. |
| S-03 | **P0** | `PAPER_STRATEGY.md:318` | "**Month 5–8:** D5 (dark sector). Ships after Phase 6m Tracks A/B/C return verdicts (**estimated ~4–6 months from now**)." | Same as S-02. This estimate is the anchor for the entire back half of the sequencing plan and it was stale on arrival. |
| S-04 | **P1** | `PAPER_STRATEGY.md:328-331` | "D3 … **Ready.** D2 … **Ready.** D1 … **Ready.** D4 … **Ready.**" | Heatmap: D1 🔴 37 blockers; D2 🔴 19; D3 🔴 7; D4 🔴 1. |
| S-05 | **P1** | `PAPER_STRATEGY.md:326` | "L3 ships after Paper 27 Stage-13 closure (**already done**)" | Heatmap L3 🔴, 6 blockers. |
| S-06 | **P1** | `PAPER_STRATEGY.md:236` | "Paper 27 is **already submission-ready** (cleared a 4-pass Stage 13 adversarial review)" | Same. |
| S-07 | **P0** | `PAPER_STRATEGY.md:310-319` (§3 sequencing) | The Month 0–12 roll-out enumerates L1, L3, D3, L2, D2, D1, E1, E2, D4, I1, I2, D5, F — **13 targets**. | **8 of the 21 targets (38 %) have no calendar position anywhere in §3**: D6, D7, D8, D9, D10, D11, D12, I3. §6's table gives D6–D9 month ranges and D10–D12 the placeholder `(after phase exec)`; §3, the section that actually sequences, was never updated after the D6 authorization (2026-05-26). `6E_SERIES_ABSORPTION_HANDOFF.md:116-117` independently identifies this: "The §3 *Sequencing* section … predates D6–D12 and never included them — that is why nothing schedules D12." |
| S-08 | **P1** | `PAPER_STRATEGY.md:333` | "F depends on **D1–D5 + I1 + I2 + L1–L3** all shipped." | F's own manifest carries **63 sources** (heatmap:23) and the roster has 21 targets. The flagship's dependency statement omits D6–D12, I3, E1, E2 — 9 of the bundles it is supposed to index. |
| S-09 | P2 | `PAPER_STRATEGY.md:375` | "Citation hygiene infrastructure (**2026-05-07 status**) … 264 cached / 0 missing as of 2026-05-08" | ~12 weeks stale. `6E_SERIES_ABSORPTION_HANDOFF.md:125`: the `6E*` corpus leans on Le Cam/Bhattacharyya, Mills, Birnbaum–Feller, McCann, Irwin–Hilton — "**no `CITATION_REGISTRY` entries exist yet**". |
| S-10 | P2 | `PAPER_STRATEGY.md:369` | "Should D4 be split? … The decision is **deferred to the bundle's Stage 1 scoping**." | D4 was drafted (81 kB / 1,584 lines / 13 sections) and reviewed. The decision was taken by default and never recorded. An open question in a strategy document that the work has already silently answered is worse than no question. |
| S-11 | P2 | `PAPER_STRATEGY.md:70` vs `:386-397` vs rubric | §2.2 says Tier 1 is "**20–60 pages**"; §6's table says ~30/40/45/50pp per bundle; the audit rubric interprets the target as ~30–50 pp. | Three different length statements for the same tier in the same document plus its consumers. **There is no single machine-readable length target anywhere in the repo** (§5 below). |
| S-12 | P1 | `PAPER_STRATEGY.md:180`, `:182`, `:194` | Inline blocks: "**⚠️ Scope correction, 2026-07-30 (D11 first-lift substrate audit):** this block previously advertised *Berry curvature* …"; "**Corrected 2026-07-30:** this line previously read …"; "(NOT Hashin–Shtrikman … — **corrected 2026-07-31, D11 Stage-13**)". | These are correct *content*, wrongly *shaped*. The canonical strategy document has become a review-narration log — the same habit the sibling auditors are finding in the manuscripts. A strategy document should state the current position; the correction history belongs in git. This item is listed because **it is the doc-level instance of the manuscript defect**, and rewriting the strategy is the moment to break the habit. |
| S-13 | P3 | `PAPER_STRATEGY.md:27` and `:405` | The full 13→14→15→16→17→18→20→21 roster-change history is written out **twice**, at 12 lines each. | Duplicated changelog. Keep one, in a `## Roster history` section or in git. |
| S-14 | P2 | `PAPER_STRATEGY.md:27` | "This is roughly a **1.9:1 collapse from the thirty-two drafts**" | `PAPER_DRAFT_MAPPING.md:110`: "**41 existing draft directories** + 4 substrate-bundled rosters + 23 … synthetic handles". `papers/` contains 44 `paperN_*` directories. The 32-draft figure is the April-2026 baseline. |

### 1.2 `docs/WAVE_EXECUTION_PIPELINE.md` — the law

| ID | Sev | Location | Assertion | Correcting evidence |
|---|---|---|---|---|
| S-15 | **P0** | `WAVE_EXECUTION_PIPELINE.md:689` (**Pipeline Invariant #14**) | "Every new draft … identifies its target bundle (one of `F`, **`D1`–`D9`**, `L1`–`L3`, `I1`–`I3`, `E1`, `E2` — **18 targets** as of the 2026-06-10 D9 authorization)" | The roster is **21** (`PAPER_STRATEGY.md:405`). **This is the single most consequential drift item in the ledger**: Invariant #14 is the rule that makes routing mandatory at Stage 1, and it names an enum that cannot legally contain D10, D11 or D12. Every 6B\*/6C\*/6E\* phase that declared into D10/D11/D12 did so against an invariant that does not admit those targets. |
| S-16 | P1 | `WAVE_EXECUTION_PIPELINE.md:395` | Phase 7+ bundle drafts are "`papers/<bundle>/` for **I1–I3, D1–D9, L1–L3, F, E1, E2**" | Omits D10/D11/D12, all of which have `papers/<X>/paper_draft.tex` on disk. |
| S-17 | P1 | `WAVE_EXECUTION_PIPELINE.md:607` | Stage-13 bundle profile: "**Tier 1 (D1–D5):** intra-bundle consistency …" | Tier 1 is D1–D12. **Seven Tier-1 bundles have no defined Stage-13 review profile.** |
| S-18 | P1 | `WAVE_EXECUTION_PIPELINE.md:609` | "**Tier 3 (I1, I2):** software/methodology review" | Omits I3 — which is drafted (68 kB) and 🔴 with 16 blockers. |
| S-19 | P2 | `WAVE_EXECUTION_PIPELINE.md:614` | "Late-arriving Phase 6X waves are absorbed … (Stages A–G with branches **D.1/D.2/D.3**)" | Branch **D.4** has existed since the 7a.4 freeze (`LATE_PHASE6_ABSORPTION_PROTOCOL.md:141`) and is the branch **all** modern Lean-only phases use. |
| S-20 | P2 | `WAVE_EXECUTION_PIPELINE.md:584` vs `:577` | ":584 — the agent "works **8 finding-classes** in order (one per readiness gate)"" vs ":577 — "the canonical definition of the **11** readiness gates"" | Internally inconsistent seven lines apart. `READINESS_GATES.md:3` defines 11. |
| S-21 | P2 | `WAVE_EXECUTION_PIPELINE.md:730` | "`uv run python scripts/validate.py` # **All 16 checks**" | `validate.py --list` returns **62**. The repo now carries **five different check counts**: 16 (pipeline:730), 21 (workspace `CLAUDE.md`), 33 (`RESEARCH_STATUS_OVERVIEW.md:9`), 49 (`6E_SERIES_ABSORPTION_HANDOFF.md:22`), 106 (repo `CLAUDE.md`). |

### 1.3 `docs/BUNDLE_LIFT_PROCEDURE.md`

| ID | Sev | Location | Assertion | Correcting evidence |
|---|---|---|---|---|
| S-22 | P1 | `BUNDLE_LIFT_PROCEDURE.md:238` | "Tier 1 (**D1–D5**)" per-bundle Stage-13 profile | Same as S-17. |
| S-23 | P1 | `BUNDLE_LIFT_PROCEDURE.md:240` | "Tier 3 (**I1, I2**)" | Same as S-18. |
| S-24 | P1 | `BUNDLE_LIFT_PROCEDURE.md:313` | "Post-freeze validation footnote (2026-05-07). Phase 7 absorption Sessions 1–5 … have **validated the procedure across all 14 bundles'** D.2/D.3/D.4 absorption events **without procedural revision**." | 21 bundles. And the procedure *has* since needed revision — see S-31. The footnote reads as a closure certificate over a portfolio that has since grown by half. |
| S-25 | **P1** | `BUNDLE_LIFT_PROCEDURE.md:16`, `:26` | Pre-condition: "Source papers at 🟢/🟡 per-paper readiness (**verify in `docs/BUNDLE_READINESS_HEATMAP.md`**)"; §1 "Confirm 🟢/🟡 source-paper readiness". | D11 and D12 were first-lifted 2026-07-30 into a portfolio the heatmap already rendered mostly RED, and D12 took a further D.3 revision on 2026-08-01. **The pre-condition is documented and unenforced** — no script checks it, and the lift proceeded. |

### 1.4 `docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md`

| ID | Sev | Location | Assertion | Correcting evidence |
|---|---|---|---|---|
| S-26 | P2 | `LATE_PHASE6_ABSORPTION_PROTOCOL.md:31` | Stage table row D: "Branch by bundle state (**D.1 / D.2 / D.3**)" | The index table omits D.4, which the same document defines at `:141`. A reader following the stage table never learns the branch that applies to every modern phase. |
| S-27 | **P1** | `LATE_PHASE6_ABSORPTION_PROTOCOL.md:68` | "If the new content does not fit any of the **existing 13 bundles**, user authorization is required for a **14th+** bundle target" | 21. The Stage-B authorization gate — the one that protects the roster — is written against a roster eight targets out of date. |
| S-28 | P1 | `LATE_PHASE6_ABSORPTION_PROTOCOL.md:269` | "if Phase 6X output does not fit any of the **existing 13 bundle targets**" | Same, in the consolidated authorization-gate list. |
| S-29 | P2 | `LATE_PHASE6_ABSORPTION_PROTOCOL.md:281` | "`docs/PAPER_STRATEGY.md` — **17-bundle architecture**" | 21. |
| S-30 | P2 | `LATE_PHASE6_ABSORPTION_PROTOCOL.md:294` | "Stages A–G with branches **D.1/D.2/D.3**" | Same as S-19/S-26. |
| S-31 | P2 | `LATE_PHASE6_ABSORPTION_PROTOCOL.md:3`, `:294`, vs `:298` | ":3 — "Updated with **worked-example examples** on first real absorption event"" (present tense, and a duplicated word) vs ":298 — the protocol executed "across **16+** Phase 6n + 6o handles"" | The header still reads as though no absorption has happened; the footer records 16+. Git shows ~36 branch-tagged events. |

### 1.5 `docs/RESEARCH_STATUS_OVERVIEW.md` — dated 2026-06-10, ~7 weeks stale

| ID | Sev | Location | Assertion | Correcting evidence |
|---|---|---|---|---|
| S-32 | **P0** | `RESEARCH_STATUS_OVERVIEW.md:492-511` | "**The 17 publication targets:**" followed by a 17-row table. | D10, D11, D12 are absent entirely from the project's plain-language status document. A reader orienting from this document does not know four of the twelve Tier-1 bundles exist. |
| S-33 | **P0** | `RESEARCH_STATUS_OVERVIEW.md:514` | "**All 17 bundles are drafted** … Current verdicts: **14 of 17 GREEN; F, D2, and L2 are RED**" | Heatmap 2026-08-01: **15 of 21 RED, 1 GREEN**. |
| S-34 | P1 | `RESEARCH_STATUS_OVERVIEW.md:488` | "auto-generated gate × **17-bundle** Stage-13 readiness summary" | 21. |
| S-35 | P1 | `RESEARCH_STATUS_OVERVIEW.md:9` | "**936 Lean modules, 12,463 theorems** … `validate.py` now runs **33 checks**" | `validate.py --list` = 62 checks. Lean counts predate the v4.32.0 bump and the whole `6B*`/`6C*`/`6E*` corpus. |
| S-36 | P2 | `RESEARCH_STATUS_OVERVIEW.md:587` | "42 paper drafts, 0 submitted as of 2026-06-10 (external communication now routes through the **17-bundle** architecture)" | 21. |
| S-37 | P1 | `RESEARCH_STATUS_OVERVIEW.md:526` | "**Resolved 2026-06-10** — the Chain 13 corpus maps to the newly-authorized D9. The early quantum-network arc (**6AA–6AH**) was **lifted into D6 §6** … the corpus as a whole … now maps to … **D9**." | This is the *origin* of the routing contradiction in §2 below: 6AA–6AH content physically sits in D6 §6 while the strategy assigns the corpus to D9, and the roadmap headers still say D6. All three statements are individually defensible and collectively incoherent. |

### 1.6 Other documents

| ID | Sev | Location | Assertion | Correcting evidence |
|---|---|---|---|---|
| S-38 | **P1** | `ARXIV_DEPOSIT_PLAN.md:4` | "Records the deposit sequencing for the **17 publication bundles**" | 21. |
| S-39 | **P1** | `ARXIV_DEPOSIT_PLAN.md:196` | "Step 2 batch: **D1–D5, D8, L2, L3, I1–I3, E1, E2** (+D6/D7 iff lifts done)" | **D9, D10, D11 and D12 appear nowhere in the deposit plan.** Four of twelve Tier-1 bundles have no deposit path. |
| S-40 | P2 | `BUNDLE_DIRECTORY_SCHEMA.md:197` | "Validated against **14 bundles'** actual on-disk state through Phase 7 absorption Session 5" | 21. |
| S-41 | P2 | `PAPER_DRAFT_MAPPING.md:208` | "**D1–D5:** deep-paper bundle review. Each bundle has 30+ source-claim sentences …" | Omits D6–D12. (Note: `:5` and `:110` roster counts **have** been corrected to 21 — good.) |
| S-42 | P2 | `docs/agents/claims-reviewer-bundle-prompts.md:58` | F's anchor requires "Every **D1–D5** Tier 1 bundle's main result statement cited" | Tier 1 is D1–D12. F's Stage-13 anchor cannot detect a missing D6–D12 cross-reference. |
| S-43 | **P1** | `PAPER_TABLES_STATUS.md` (whole document) | The table-autogeneration retrofit status, "9 of 10 papers with tables fully retrofitted". | The document covers **only per-paper drafts paper1–paper16**. **Zero of the 21 bundles has a `tables.py`** (verified: `ls papers/*/tables.py` → none). The anti-drift table pipeline — the infrastructure that makes numerical drift "structurally impossible" — covers **none of the actual publication targets**. |
| S-44 | P2 | `docs/BUNDLE_READINESS_HEATMAP.md:49` vs `READINESS_GATES.md:3` | The heatmap's Gate × Bundle table has **10** gate columns, one named **`CountFreshness`**. | `READINESS_GATES.md` defines **11** gates. **`FirstClaimVerification` is absent from the heatmap entirely**, and `CountFreshness` is the pre-Phase-5v name that `READINESS_GATES.md:189` itself records as superseded by `NumericalFreshness`. |
| S-45 | P2 | `docs/README`-level: repo `CLAUDE.md` when-to-read table | "lifting draft content into a bundle → `docs/BUNDLE_LIFT_PROCEDURE.md`" — and the workspace `CLAUDE.md` reference names the bundle set "(I1–I3, **D1–D11**, L1–L3, F, E1, E2)" | Omits D12. |

### 1.7 `docs/6E_SERIES_ABSORPTION_HANDOFF.md` — a live handoff that is no longer live

This document was written 2026-07-30 "for pickup after compaction". Most of its checklist was
executed within 24 h; **the document was never updated and still reads as an open to-do list.**

| ID | Sev | Location | Handoff says | Actual state (2026-08-01) |
|---|---|---|---|---|
| S-46 | P1 | `:90` item 1 | "`PAPER_DRAFT_MAPPING.md` row per phase — **ABSENT** — zero rows for 6EA/6EB/6EC/6ED/6EE or D12" | **Partly done, and not in the prescribed form.** `PAPER_DRAFT_MAPPING.md:108-109` now carry consolidated `D11_initial_draft` / `D12_initial_draft` rows. But `grep -c "_phase6E" docs/PAPER_DRAFT_MAPPING.md` = **0**: the per-phase sourceless rows the handoff's next-action 3 specifies (`_phase6EA_lean_only`, …) were never written. Consequence in §3.3. |
| S-47 | **P1** | `:91` item 2 | "Substantive synthesis in `temporary/working-docs/` — **ABSENT** — content lives only in `docs/dev-loops/Phase6E*/` lab notebooks, which are **gitignored** (one `git clean -x` from loss)" | **STILL ABSENT.** No `temporary/working-docs/*6E*` exists; `docs/dev-loops/Phase6E{A,B,C,D,E}/` exist and are gitignored. **This is the one genuinely-open item and it is a data-loss risk on the substrate backing a 35 pp bundle.** |
| S-48 | P2 | `:92` item 3 | "`ARCHITECTURE_SCOPE.md` updated — **ABSENT** — zero `6E` mentions" | **DONE.** 5 `6E` mentions; file mtime 2026-07-30 18:21. |
| S-49 | P2 | `:94` item 5 / `:237` action 9 | "D12 appears in **NO** `Phase7*.md` roadmap — operator scheduling decision" / "stand up `papers/D12/` at first content-lift, **or record explicitly that it is deferred**" | **DONE.** `papers/D12/` first-lift 2026-07-30; D11 likewise. |
| S-50 | P2 | `:160` | "`_VALID_BUNDLE_TARGETS` (`scripts/sentence_state.py:203-212`) contains **neither D11 nor D12**" | **DONE.** `sentence_state.py:207` now re-exports from `scripts/bundle_registry.py` ("THE roster source of truth, consolidated 2026-07-30"). |
| S-51 | P2 | `:173` | "`docs/agents/claims-reviewer-bundle-prompts.md` has **no D11/D12 reviewer anchor** (stops at D10)" | **DONE.** Anchors present at `:626` (D11) and `:734` (D12). |
| S-52 | P2 | `:186-188` | "**Stale-count drift to fix:** `PAPER_DRAFT_MAPPING.md:5` still says '17 publication targets'" | **DONE.** `:5` and `:110` now read 21. |
| S-53 | P2 | `:246-258` §5 "Repo state at handoff" | "HEAD `d42333c4`. … `/goal` cleared" | Many commits since (D11/D12 14-round Stage-13 grind, 2026-07-31; D12 D.3 re-lift `3fa4b4c1`, 2026-08-01). |

**Verdict on the handoff (task 3, sub-question 3):** it *was* complete and actionable when
written — it is one of the better-constructed documents in this corpus, and the Explore
verdict in its §3 (no D9/D1/D7 collision, D12 owns the composite ceilings) is consistent with
what D12 actually contains. It is now **~80 % executed and 0 % updated**, which makes it a
trap: a fresh reader will redo five completed items and may miss the one that is still open
(S-47). **Recommendation: retire it. Fold S-47 into the D12 bundle's `change_log.md` as an
open item and delete the rest.** A handoff document that outlives its handoff becomes drift.

---

### 1.8 Roadmap-header drift (the routing documents' own staleness)

Recorded here because the strategy rewrite will read these headers as input.

| ID | Sev | Location | Header says | Body says |
|---|---|---|---|---|
| S-54 | P2 | `Phase6AA_Roadmap.md:3` | "**Status:** OPEN (seeded 2026-06-01)" | `:46` "🎯🎯 **PHASE 6AA DONE (2026-06-01)**" |
| S-55 | P2 | `Phase6AB:3`, `6AC:3`, `6AD:3`, `6AE:3`, `6AF:3`, `6AG:3` | all "**Status:** OPEN" | all six record completion in-body (`6AD:14` "PHASE 6AD DONE"; `6AG:29-30` "FULLY DONE") |
| S-56 | P2 | `Phase6AI_Roadmap.md:3` | "**Status:** PLANNED" | `:547` "✅ OUTCOME UPDATE 15 (2026-06-03) — **6AI COMPLETE**: `diamondDist_eq_choiSDP` PROVEN UNCONDITIONAL" |
| S-57 | P2 | `Phase6AL_Roadmap.md:3` | "**Status: PLANNED 2026-06-04**" | `:16-55` Waves 1–4 all "✅ SHIPPED" with commit hashes |
| S-58 | **P1** | `Phase6CA_Roadmap.md:3` | "🔄 IN PROGRESS … W1 substrate shipped" and (historically) advertised Berry curvature + bulk–boundary | `PAPER_STRATEGY.md:180` flags this file as **stale** and the advertised content as having "**zero occurrences project-wide**". The live ledger is `Phase6CA_prime_Roadmap.md`. **Two D11 scope corrections (2026-07-30, 07-31) were caused by a reader trusting this header.** Add a supersession banner to the file itself. |
| S-59 | P2 | `Phase6r_Roadmap.md`, `Phase6r_prime_Roadmap.md` | every wave "⏳ NOT STARTED" | ~54 of the modules those waves name **exist in `lean/`** (U-04). The roadmaps understate their own arc by an entire corpus. |
| S-60 | P2 | `Phase6EE_Roadmap.md:10-12` | "**Status: COMPLETE (2026-07-30)**" | same lines: "the **stricter operator bar — zero BLOCKER *and* zero MAJOR *and* zero IMPORTANT — was NOT reached**". Honest, but "COMPLETE" in the header is the field a reader indexes on. |

---

## 2. Phase → bundle routing coverage

Two exhaustive read-only passes were run over all 119 roadmaps (lowercase `Phase6`–`Phase6z`;
uppercase `6AA`–`6GA` plus the `5q` series and Phase 7). Method for the `lifted?` column: a
phase counts as **LIFTED** only if (i) a `_phase6X_*` handle appears in some
`papers/<Bx>/source_manifest.md` **or** (ii) the phase's distinctive Lean module basenames
appear (word-boundary grep) in some file under `papers/`. **UN-HOMED** = the `.lean` file
exists in `lean/` and its basename appears in **zero** files under `papers/`; grep-ambiguous
generic names (`Basic`, `Trace`, `Module`, `Sum`, `Spectrum`, …) are excluded from un-homed
claims.

### 2.0 Headline — un-homed executed work

**This is the finding the brief asks for most directly, and it is much larger than the
strategy documents suggest.**

| # | Arc | Status | Scale of un-homed Lean | Evidence |
|---|---|---|---|---|
| **U-01** | **Phase 5q.E / 5q.F / 5q.G / 5q.H — the whole Pin⁺ ℤ/16 bordism programme** | 5q.E "COMPLETE-CONDITIONAL"; 5q.F/G/H live | **162 `PinPlus*.lean` modules + ~88 `Smith*`/`Wu*`/`SingularManifold*` modules** | `grep -rl "PinPlus" papers/` → **0 files**. Also zero `papers/` hits for `CommonOrigin`, `Omega4PinPlusBordism`, `sixteen_convergence_common_origin`, `rokhlin_reads_kitaev`, `SmithInflow`, `PinPlusDischarge`, `DataBordismGrp`, `dataBordism_quotient_abk_equiv_zmod16`, `sixteen_convergence_genuine_carrier`, `abkGrade`, `smithDataHom`, `Omega5Finite`. D2/L2 contain only the **5q.B-generation** result (`D2/paper_draft.tex:319,347,412`; `L2:210-215,273-291`) and their `change_log.md` files both end 2026-06-10 — **before** 5q.E's capstone (06-14), 5q.F (06-15), 5q.G (06-24) and 5q.H (07-13). |
| **U-02** | **Phase 6x — quantum-compilation substrate** | COMPLETE/PARTIAL, MVP shipped 2026-05-30 | **51 modules** | All `KMM*` (`KMMCompute`, `KMMLemma3{,Bridge,Column}`, `KMMReduce{,Mu}`, `KMMReductionDischarge`), all `Gde*`/`ZOmega*`/`GridSynth`/`GridEnum`/`GridCompileCorrect`, **all four Mathlib-PR-eligible modules** (`CartanFinalStepSUdGenericMathlibPR`, `MatrixBCHCubicMathlibPR`, `MatrixExpLocalHomeomorphMathlibPR`, `SU2CompactnessMathlibPR`), `MukhopadhyayCCZ`, `TrappedIonAlphabet`, `ReadRezayiK5/K7BaseFinder` — zero `papers/` hits. |
| **U-03** | **Phase 6p** | PARTIAL-SHIPPED | **52 modules** | Incl. `AharonovAradBridge{,Iteration,Proof}`, `FaultTolerantUQC`, `FibonacciQuintetUniversality`, `FibonacciQutritUniversality`, `GateCompilation`, `JonesWenzl`, `TemperleyLieb`, `StabilizerCode`, `SteaneCode`, `SolovayKitaevConstructive`, `QCyc80{,Ext}`. Only the `_phase6p_W2cd_lean_only` handle is registered (D4/D8/F), covering Waves 2c/2d alone. |
| **U-04** | **Phase 6r + 6r′ — the SymTFT line** | Both roadmaps read **"⏳ NOT STARTED" on every wave** | **~54 modules that exist anyway** | `BulkTQFT`, `BulkBoundaryCorrespondence`, `DrinfeldCenterAsBulk`, `GappedBoundary`, `LagrangianAlgebra`, `FrobeniusAlgebra`, `SMMatterAsSymTFTBoundary`, `SpinSymTFT{,SchellekensAlignment}`, `Z16ViaSpinSymTFT`, `ToricCodeLagrangian{,Anyons}`, `PinBordism`, `PinPlusBordism4`, `RP4{,ChartedSpace,IsManifold,Smooth}`, `Center{,Biproducts,Functor,…}`, `AndersonDual{Functor,Substrate,TFT}`, `EtaInvariant`, `KirbyTaylor`, `FractonDarkMatter` … **The work was done off-roadmap and has no publication destination at all** — the roadmaps that would declare one still say the waves never started. |
| **U-05** | **Phase 6y — the SU(d) Solovay–Kitaev substrate** | "All three Phase 6y instances ship UNCONDITIONAL + kernel-only" (`Phase6y_Roadmap.md:235`) | **30 modules — the entire `GenericSUd*` family** | 29 `GenericSUd*` modules (`GenericSUdSkApproxC*`, `GenericSUdSkHeadlineCascade*`, `GenericSUdDnStepFG*`, `GenericSUdMatrixMercatorLog`, …) + `CartanFinalStepSUdMathlibPR`. `PAPER_STRATEGY.md:150` advertises this as D8's result (ii) — "the first kernel-verified quantitative Solovay-Kitaev at general d" — and **not one of its module names appears in D8's draft.** |
| **U-06** | **Phase 6x′** | "✅✅ COMPLETE — both phases shipped, kernel-pure" | **13 of its 14 modules** | `CCZ_SU`, `CliffordCCZSU8{CNOTConj,GenConjValues,LabelTransitivity,PauliConj,TangentSpan}`, `Mukhopadhyay{CCZConjugation,ChannelRep,CliffordConverse,Sde2,SignedPerm,ToffoliBound}`, `SdeMatrix`. Only `MukhopadhyayCliffordNotDense` reaches D8 — yet `PAPER_STRATEGY.md:150` result (v) is built on `channelSde2_le_toffoliCost` and `channelRep_interp_isRat`. |
| **U-07** | **`QuantumNetwork/` (6AE–6AL)** | 6AI/6AJ/6AK all COMPLETE | **20+ modules** | `DiamondNormWitness`, `DiamondSDPAttainment`, `DiamondSDPCone`, `FidelityAttainmentPSD`, `FidelityBlockForm`, `FidelityDataProcessing`, `FidelityForwardBound{,PSD}`, the six `Gaussian*` modules, `HermitianCarrier`, `KroneckerEntropy`, `KroneckerPower`, `OpNormHolder`, `PauliChoiNegativity`, `TraceNormCauchySchwarz`, `VectorMajorization`. Two of these are **named headline achievements**: the `Gaussian*` block is 6AG's constructive unitary-2-design ("the 2nd moment as a THEOREM, not an import", `Phase6AG_Roadmap.md:30`); `DiamondSDP*` is 6AI's `diamondDist_eq_choiSDP`, which `RESEARCH_STATUS_OVERVIEW.md:14` calls "the **first kernel-verified Watrous diamond-norm SDP strong duality**". Neither module name reaches any draft. |
| **U-08** | **Phases 6h, 6j, 6k, 6l, 6q** | 6h CLOSED-NEGATIVE; **6j, 6k, 6l, 6q all FULLY CLOSED with substantial Lean** | 6k "5 modules / 69 substantive theorems"; 6l "4 modules / 61"; 6q "5 waves / 10 modules"; 6j "4 modules / 60 substantive theorems" | **None appears in `docs/PAPER_DRAFT_MAPPING.md`** (`grep -ci 'phase ?6[hjklq]'` = 0 for each) **nor in any `source_manifest.md`.** Un-homed modules include 6h's `MajoranaRungSMG`, `BHLGaugeEmbedding`, `NeutrinoMixing`; 6k's `CKMApexSubstrateConstraint`, `CPPhaseSubstrate`, `QuarkRung{MajoranaChannel,ScalarChannel}`; 6q's own headline `BECBogoliubovBosonicGrowth`, plus `AnalogHawkingBiconditional`, `HorizonTransportBootstrap`, `KMSConsistency`, `LDPBridge`, `E1E2CrossBridge`; 6l's `SubstrateAxion`, `InstantonZeroModes`, `SubstrateInstantonSpectrum`. |
| **U-09** | **Phase 5q.T** | "COMPLETE 2026-06-03" | `A1ExtSubstantive.lean` | `Phase5qT_...:133-134` sets its own closing task: "Update the target **bundles** — **D2** … and the **L2** PRL splash — to cite the substantive theorems, **not the proxies**." `grep -rl "A1ExtSubstantive" papers/` → **0**. D2/L2 still cite the proxies. The phase closed with its publication obligation unexecuted. |
| **U-10** | **Phase 6n / 6o residuals** | Both closed; handles registered | 22 (6n) + 18 (6o) modules | e.g. 6n's `DynamicalKMS`, `EntropyCurrent`, `GallavottiCohen`, `LocalSecondLaw`, `OnsagerReciprocity`, `SKEFTHorizonBridge`; 6o's `EmergentGraviton`, `BCJNoGo`, `ModularInvariance`, `NoiseFloorPrediction`, `SymTFTBridge`, `RefutationTableau`. These phases *are* homed at handle level (8 + 6 handles across many bundles) — the modules simply were never named in the prose. Lower severity than U-01…U-08, but it is the same failure. |

**Aggregate: roughly 340 kernel-verified Lean modules across ten arcs are named in no bundle
draft.** Several are the project's own advertised firsts. This is work that was paid for,
proved, kernel-checked — and is currently invisible to every publication target.

> **Two distinct failure modes, and they need different fixes.** U-01, U-04 and U-08 are
> *genuinely un-homed*: no bundle claims the work and no mapping row exists. U-02, U-03,
> U-05, U-06, U-07, U-09, U-10 are *homed but unlifted*: the strategy's §2.2 Sources
> paragraph claims the content and the bundle's draft never names it. The second class is
> arguably worse, because the strategy reads as though the work has landed. §2.4 explains the
> mechanism.

### 2.1 The largest routing conflict: the entire `6A*` series is double-declared

**Seven roadmaps declare D6; the strategy assigns the corpus to D9; and both bundles' drafts
currently carry it.**

- Roadmap side: `Phase6AA_Roadmap.md:3` "Bundle-target: **D6**"; `Phase6AB:3`, `Phase6AC:3`,
  `Phase6AD:3`, `Phase6AE:3`, `Phase6AF:3`, `Phase6AG:3` all "Bundle-target **D6 §6**".
- Strategy side: `PAPER_STRATEGY.md:27` and `:164` — D9 consolidates "Phases **6AA–6AL** …
  plus the 6AM/6AN/6AP/6AQ envelope waves **that had no bundle home**".
- Origin: `RESEARCH_STATUS_OVERVIEW.md:526` records both as historically true — 6AA–6AH "was
  lifted into **D6 §6**" as it shipped, and the corpus "as a whole … now maps to … **D9**"
  (authorized 2026-06-10). **The re-homing was written into the strategy and never propagated
  back to the seven roadmap headers, nor reflected in D6's draft.**

**This is not cosmetic — the content is physically double-homed in two drafted bundles.**
`papers/D6/paper_draft.tex` still carries the corpus as running §6 body text: `:504`
("a verified network-fidelity envelope (Phase 6AA)"), `:542` (6AB), `:563` (6AC), `:589` (6AD),
`:617` (6AE), `:629` (6AF), `:718` (6AG), `:782` (6AI), `:793` (6AJ), `:824` (6AK) — and
`grep "D9" papers/D6/paper_draft.tex` returns **zero hits**, so there is no supersession note.
Meanwhile `papers/D9/paper_draft.tex:14-18` re-synthesizes the same phases from scratch.
**Either D6 §6 must be cut or D9 must be re-scoped; today both drafts claim the same work.**

Compounding it: **`papers/D9/source_manifest.md:13` lists exactly one contributing source** —
the synthetic `D9_initial_draft` — with Phase/Wave "(see mapping)" and mtime "**(missing)**".
The phase attribution survives only in a `%%` LaTeX comment block. CHECK 22 cannot function
on this manifest (see §3.2).

**Ten of the seventeen `6A*` phases (6AH, 6AI, 6AJ, 6AK, 6AL, 6AM, 6AO, 6AP, 6AQ, and 6AN
except its W5) declare no bundle in their own roadmap at all.** `Phase6AK_Roadmap.md:3` reads
"✅ COMPLETE (2026-06-03). All 6 waves shipped kernel-pure, Stage-13 GREEN" with no bundle line
anywhere in the file. This violates Pipeline Invariant #14 ten times over — and the `6B*`,
`6C*` and `6E*` roadmaps all comply correctly, so the discipline exists and the `6A*` series
simply skipped it.

**Seven `6A*` roadmap headers are additionally stale on their own status**: 6AA, 6AB, 6AC, 6AD,
6AE, 6AF, 6AG all say `Status: OPEN` at `:3` while their bodies record completion (e.g.
`Phase6AA_Roadmap.md:46` "🎯🎯 **PHASE 6AA DONE (2026-06-01)**"). `Phase6AI:3` says "PLANNED"
against `:547` "**6AI COMPLETE**"; `Phase6AL:3` says "PLANNED 2026-06-04" against `:16-55`
recording all four waves shipped.

**`6AO` is an orphan in the strategy.** `Phase6AO_Roadmap.md:42` "✅ **PHASE 6AO CLOSED
(2026-06-10)**", and it *is* a lifted D8 source (`papers/D8/source_manifest.md`) — but 6AO
appears **nowhere** in `PAPER_STRATEGY.md` (`:27`, `:160`, `:164` all skip it). Its closure
predates the D9 authorization by hours.

**`6AH` is genuinely incomplete and marked ACTIVE**: `Phase6AH_Roadmap.md:3` "ACTIVE (opened
2026-06-02)"; `:37` "✅ FOUNDATION SHIPPED (`RBCertificate.lean`, kernel-pure, **not
root-imported**"; `:102-104` phase-exit checklist unticked. A not-root-imported module is not
in the library build — D9 cites `RBCertificate` regardless.

### 2.2 `D4 §9.8` is a phantom destination — five phases declare it, none landed there

| Phase | Declares | Actually landed in |
|---|---|---|
| 6t | `Phase6t_Roadmap.md:170` "Wave 8 — Closeout + **D4** bundle absorption ✅ SHIPPED" | `_phase6t_lean_only` → **D6, D8, F** manifests. **Absent from `papers/D4/source_manifest.md`.** |
| 6u | `Phase6u_Roadmap.md:47` "\| **D4 §9.6** \|"; `:897` "Bundle D4 §9.6-§9.8 absorption ready" | `_phase6u_lean_only` → **D6, D8, F**. Absent from D4. |
| 6x | `Phase6x_Roadmap.md:132`, `:179`, `:221` "**Bundle absorption**: **D4 §9.8**" | `_phase6x_lean_only` → **D8, F**. Absent from D4. |
| 6y | `Phase6y_Roadmap.md:251` "**D4 §9.8** bundle absorption (**held for a separate user-authorized event**)" | `_phase6y_lean_only` → **D8, F**. Absent from D4. |
| 6z | `Phase6z_Roadmap.md:142` "**Bundle absorption:** HOLD any **D4 §9.8** … extension" | `_phase6z_lean_only` → **D8, F**. Absent from D4. |

The re-pointing is *documented* — `PAPER_STRATEGY.md:152` says the 6p/6t content "previously
routed to D4 §9.1–9.5 **is re-pointed to D8**". **The five roadmaps were never updated**, and
two of them (6y, 6z) explicitly record the D4 absorption as *held pending user
authorization* — an authorization that the D8 re-pointing silently made moot. Anyone reading
those roadmaps today will look for content in a section that does not exist.

### 2.3 Phases whose declared home does not resolve, or resolves twice

| Phase | Status | Declared home | Problem |
|---|---|---|---|
| **6DA** | `Phase6DA_Roadmap.md:3` "PLANNED (authorized 2026-07-02; reframed 07-04)"; `:145` waves unticked | `:52` "**Publication target: DEFERRED — none assigned**"; `:23` "operator's call" | A whole new `6D*` thematic series with an explicitly unassigned bundle. Legal only while unexecuted; the moment it ships, Invariant #14 has no target to satisfy. |
| **6FA** | `Phase6FA_Roadmap.md:3` "PLANNED (namespace authorized 2026-07-29)" | `:7` "It is a different *kind* of work … **no bundle target**, no Stage-13 claims review" | A deliberate exemption from Invariant #14 that the invariant does not provide for. If `6F*` is genuinely not paper-shaped, the strategy should say so explicitly; today it is silent. |
| **6GA** | `Phase6GA_Roadmap.md:3` "PLANNED (namespace authorized 2026-07-29)" | none (zero `bundle` hits) | New `6G*` series, no home, no exemption rationale. |
| **6CC** | `Phase6CC_Roadmap.md:3` "⏸ PARKED / HOLDING", gated on 5q.G | `:19` "**D2** … **or** D11; decided at Stage 1" | Honestly dual-declared and honestly parked. Acceptable *while parked*; couple the decision to P-01. |
| **6BD** | `Phase6BD_Roadmap.md:3` "PLANNED — **IN PLAY** (activated 2026-07-01)" | `:22` "**D8** … *not* D10" ✅ | One-directional: D8's own Sources list (`PAPER_STRATEGY.md:154`) omits 6BD. Zero `6BD` hits in `papers/`. |
| **6r′** | all waves "⏳ NOT STARTED" | `:1148` names **four** bundles — D2, D4, D5, L1 — plus F | A five-way declaration with no primary. Combined with U-04 (the modules exist anyway), this arc has both too many declared homes and no actual one. |
| **6j** | `Phase6j_Roadmap.md:9` "**FULLY CLOSED across all 4 waves**" | `:419` "Per `docs/PAPER_DRAFT_MAPPING.md`: Phase 6j content lifts into **D3 §13.5 + I1 sidebar**" | **The cited authority does not contain the citation.** `grep -ci 'phase ?6j' docs/PAPER_DRAFT_MAPPING.md` = **0**; no `_phase6j` handle in any manifest; "Phase 6j" text appears only in `papers/I2`, not D3 or I1. The sharpest declared-but-unfulfilled case in the corpus. |
| **6h** | `Phase6h_Roadmap.md:13` "**Gate Z.4 closed NEGATIVE** … shipped as a **second structural no-go**" | none | A *negative result the strategy explicitly prizes* (`PAPER_STRATEGY.md:32` "NO-GOs as first-class deliverables") with zero bundle home, zero mapping row, zero draft hits. Its `MajoranaRungSMG`, `BHLGaugeEmbedding`, `NeutrinoMixing` are un-homed. |
| **D7** | `Phase6w_Roadmap.md:49` "D7 bundle CREATED" | D7 | **`papers/D7/` is the only bundle with no `source_manifest.md`** and (per §3.1) no `append_log.json`. Its draft is 16 kB / 339 lines / 1 subsection against a ~40 pp target. The bundle exists as a directory and a stub. |

### 2.4 Where routing *works* — the template to copy

Not everything is broken, and the working cases are recent and consistent. **`6BA`, `6BB`,
`6BC` → D10; `6CA`, `6CA′`, `6CB`, `6CD`, `6CE`, `6ED` → D11; `6EA`, `6EB`, `6EC`, `6EE` →
D12** all declare their bundle in the roadmap header, match `PAPER_STRATEGY.md`, and have their
modules verifiably present in the target draft. Every `6B*`/`6C*`/`6E*` module resolved to its
declared bundle — **zero un-homed modules in those three series.**

`PAPER_STRATEGY.md:180-182`'s treatment of 6CA's deferred differential geometry is the model
for honest deferral: it names what is *not* in the tree, says *deferred not conditional*, gives
the cost (4k–15k+ LOC), and points at the live ledger. Every deferred thread should be
documented in exactly that shape.

The single caveat: the `6B*`/`6C*`/`6E*` phases are homed **collectively**, one mapping row per
bundle, not per phase (§3.3) — so the granularity regressed even where the direction is right.

### 2.5 The structural cause: registering ≠ lifting

**This is the mechanism behind the "homed but unlifted" class in §2.0** (U-02, U-03, U-05,
U-06, U-07, U-09, U-10).

`scripts/bundle_append.py` inserts "a `\section` **stub**" at a marker (`:205-261`) and the
script's own docstring (`:56`) says the "actual prose lift from source [is] **manual**; the
script appends a stub section only." So `bundle_append.py --lean-modules "A,B,C"` records A,
B and C in `append_log.json` and creates an empty heading — after which the bundle's manifest,
its `change_log.md`, its `last_lift` and the freshness check **all report the absorption as
done, while the draft contains a heading and nothing else.**

`papers/D4/append_log.json:130` records the failure mode in the project's own words:

> "Stage 10.E manual prose authoring (user-authorized 2026-05-23) … **replacing two
> post-bibliography D.4 sourceless skeletons** (lines 947-969)."

Two empty stub sections sat **after the bibliography** for ~2 weeks and no gate noticed. That
is the same state U-05's thirty `GenericSUd*` modules are in today: registered against D8,
present in `append_log.json`, absent from the prose.

**No check distinguishes "a source is registered" from "its content is in the manuscript."**
`prose_theorem_reference_coverage` (`validate.py:6927`) checks only the converse — that
`\texttt{}` tokens *in the draft* resolve in `lean_deps.json`. Nothing checks that a bundle's
declared Lean modules are *mentioned* in its draft. **That single missing check is the cheapest
fix for the entire "homed but unlifted" class** — see F-10.

### 2.6 Section architecture is a projection of the source roster

(Detailed in §4.2 — the same tool that fails to lift content succeeds at creating one section
per source, which is the origin of the stitched-lift structure.)

---

## 3. Absorption-protocol fitness

### 3.1 Has it been exercised end to end? — **Yes, ~36 times. This is not shelfware.**

Git and the per-bundle logs give an unambiguous answer:

- `docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md` created `463d699c` (2026-05-01), frozen
  `7779f143` (same day), 6 commits total.
- **36 branch-tagged absorption events across 12 bundles**, recorded in
  `papers/<X>/append_log.json` + `change_log.md`: **D.2 × 26** (D1×4, D2×2, D3×7, D4×3, D5×2,
  E1×2, I1×3, I2×1, L1×1, L3×1), **D.3 × 6** (I1 GATE 1; D3+L3 GATE 2; D2+L2 GATE 3; D12
  2026-08-01), **D.4 × 4** (D5, D8, I3, D4), plus 6 untagged "Late absorption" and ~14
  bookkeeping-only sweeps.
- The 2026-05-06 D.2 batch carries machine timestamps clustered `15:39:38Z → 15:43:01Z` across
  ten bundles — that is `bundle_append.py` in a loop, not hand-written JSON.
- The protocol has survived a **live correction forced by a reviewer catching an error in the
  protocol itself**: commit `8b9e2376` (2026-07-31), from D12 Stage-13 round-11 finding 8.6,
  rewrote `:184` after establishing that the documented `freshness_stale`-clearing rule was
  violated by `check_bundle_source_freshness.py:201` and `bundle_append.py:318` "on every run".
- Most recent execution: `3fa4b4c1` (2026-08-01) "D12 D.3 revision: re-lift from complete
  sources" — the only commit in the repo whose subject names a protocol branch.

**Gaps in the execution record:**

- **A-01 (P2).** The protocol's own headline worked example (`:228`, Phase 6o Wave 4a Track 4 →
  D5) **has no `append_log.json` entry**. The mapping row exists
  (`PAPER_DRAFT_MAPPING.md:85`), the prose landed (`papers/D5/paper_draft.tex:1063-1111`), and
  Stage F ran (`papers/AutomatedReviews/2026-05-08-bundle-stage13/D5.md`) — but the D.4 step
  the protocol says exists "for audit-trail purposes" was skipped. The document's most-cited
  proof of execution is the one event with no machine record.
- **A-02 (P3).** Six bookkeeping events in `papers/{D1,D2,D3,E1,F,I1}/append_log.json` cite
  "`LATE_PHASE6_ABSORPTION_PROTOCOL §3d`". There is no §3d in that document; §3d is
  `BUNDLE_LIFT_PROCEDURE.md:93`. Wrong document, six times identically.
- **A-03 (P2).** `papers/D7/` has **no `append_log.json` at all** — the only bundle missing one.
  Its `bundle_metadata.json` claims `last_lift: 2026-05-26` with no machine-readable record.
- **A-04 (P1).** The 2026-08-01 D12 D.3 is **entered but not completed**. Protocol D.3 step 4
  (`:134`) requires setting both `stage13_redo_required=true` *and* `freshness_stale=true`;
  D12 has the first and not the second, and `last_stage13_review: 2026-07-31` predates the
  revision, so Stage F has not run on the revised draft.

### 3.2 **The trigger is structurally dead for every bundle authorized since D6** — P0

This is the most serious finding in the report and it is a code defect, not a documentation one.

Protocol **Stage C** is the entry point: "`validate.py --check bundle_source_freshness` flags
affected bundles `freshness-stale=true`" (`:86`), and **Stage D branches on that flag**
(`:31`). If the flag cannot be set, the protocol cannot be entered.

`scripts/check_bundle_source_freshness.py`:

```python
def _latest_source_mtime(source: str) -> datetime | None:
    pdir = PAPERS_DIR / source
    if not pdir.exists():
        return None            # ← line 63
    ...

for src in sources:
    mt = _latest_source_mtime(src)
    if mt is not None and mt > last_lift:    # ← line 161: None is silently skipped
        stale_sources.append((src, mt))
```

A **sourceless** bundle's only registered source is a *synthetic key* —
`D9_initial_draft`, `D10_initial_draft`, `D11_initial_draft`, `D12_initial_draft`,
`_phase6AP_W3b_lean_only`, … — for which no `papers/<key>/` directory exists. `_latest_source_mtime`
returns `None`; line 161 skips it; the else-branch then emits:

> `✓ bundle:D12 — fresh: all 1 source paper(s) older than last_lift (2026-07-30)`

**That message is a false green.** No mtime was compared. The check as run today reports
D9, D10, D11, D12, D7, I2, I3 and E2 as *fresh* on the strength of a comparison it never made.

**Consequence.** The absorption trigger is keyed to `papers/<source>/` **file mtimes**. Every
bundle authorized since D6 (2026-05-26) is sourceless — its substrate is `lean/SKEFTHawking/*`.
**Nothing in the freshness check looks at Lean modules at all.** So:

> A future `6F*` / `6G*` / `6D*` / `6BD` wave can ship a hundred kernel-pure theorems into
> D8's or D9's or D12's scope, and `bundle_source_freshness` will keep printing *fresh*. Stage
> C never fires, Stage D never branches, Stage F never re-reviews. The bundle silently rots.

This is precisely the operator's second goal ("ensure that future work is able to be absorbed
cleanly") failing at the mechanism level. **Fix in §4.6, F-07.**

### 3.3 The per-phase mapping-row gap compounds it

Even where a phase *is* mapped, the 6E precedent shows the granularity is wrong. The handoff's
next-action 3 (`6E_SERIES_ABSORPTION_HANDOFF.md:224`) specified per-phase sourceless rows:

> `| _phase6EA_lean_only | <Title> | Phase 6EA W1–W3 | **D12 §N** | Synthesize |`

What was written instead is one consolidated `D12_initial_draft` row
(`PAPER_DRAFT_MAPPING.md:109`) covering all four phases. `grep -c "_phase6E"` = **0**. So
D12's `sources` list has length 1, and there is no handle by which 6EB (say) could later be
re-absorbed, re-reviewed, or detected as revised independently of the others. Same for D11/6ED.

Contrast the 6A\* series, which *did* get per-wave handles (`_phase6AP_W3b_lean_only`,
`_phase6AN_W5_lean_only`, …). The granular pattern is the correct one and it regressed.

### 3.4 Does the protocol work when the target bundle is itself defective? — **No, and there is no branch for it.**

The protocol's Stage-D branch table (`:219-224`) discriminates on exactly two axes:

| Condition | Branch |
|---|---|
| `paper_draft.tex` does not exist | D.1 |
| exists AND additive AND has per-paper draft | D.2 |
| exists AND overturns prior content | D.3 |
| exists AND additive AND Lean-only | D.4 |

**Nothing branches on the target's readiness.** The design assumption is stated at `:20`:
"Phase 7's bundles must absorb the new content **without redrafting**" — i.e. the target is a
drafted, sound bundle receiving an addition.

That assumption is now false for most of the portfolio:

- 15 of 21 bundles are 🔴 RED.
- 14 of 21 carry `stage13_status: "green"` **with `blockers_open > 0`** — D1 (37), F (23), D2
  (19), I2 (19), D5 (17), I1 (16), I3 (16), L2 (16), D7 (12), D3 (7), L3 (6), E1 (5), L1 (2),
  D4 (1). The protocol's Stage-F pass criterion is literally *zero BLOCKER* (`:180`).
- 9 of 21 ship **zero figures** (F, D1, D2, D3, D4, D6, D7, D10, I3).
- D6 is `stage9: not_started`, `stage10: skeleton`, `stage13: green` — a skeleton that renders
  🟡 better than every fully-drafted sibling because it has no findings.

**The gap, stated precisely.** Absorbing new content into a bundle with 37 open blockers does
three harmful things the protocol has no answer for:

1. **It buries the blockers.** Stage F re-invokes the reviewer triple, which returns the 37
   pre-existing findings alongside any new ones. The 6EE experience is the documented proof of
   this dynamic — six rounds where "each remediation added surface that the next round then
   reviewed" (`6E_SERIES_ABSORPTION_HANDOFF.md:51`), MAJOR/IMPORTANT counts flat while the
   artifact grew 99 → 191 declarations. **Appending to a defective bundle makes the review
   loop non-convergent.**
2. **It inflates the artifact past the point where remediation is affordable.** D3 is already
   139 kB / 2,885 lines / 37 sections / 114 subsections with **zero figures**. Absorbing a
   38th section does not make D3 more publishable.
3. **It licenses the false-green.** D.2's exit (`:120` "Then proceed to Stage F") plus the
   Stage-F exit gate (`stage13_redo_required`, `:184`) can both be satisfied while
   `blockers_open` stays at 37, because **no check compares `stage13_status` against
   `blockers_open`**.

**Recommended new branch — D.0 (target-unsound → remediate-before-absorb).** Definition in §4.6
(F-08).

### 3.5 `bundle_source_freshness` — what it currently flags

Run 2026-08-01: `0 FAIL / 11 WARN / 12 PASS`, overall **PASS** (the check is advisory).

| Flagged `freshness-stale` | Flagged `stage13_redo_required` | Reported fresh |
|---|---|---|
| D1 (4/12 sources), D2 (4/6), D3 (5/31), D4 (3/12), D5 (1/9), E1 (1/5), F (11/63), I1 (1/8), L2 (1/1) | D11, D12 | D6, D7, D8, D9, D10, E2, I2, I3, L1, L3, **and D11/D12's source rows** |

Read against §3.2: **every bundle in the "reported fresh" column whose only source is a
synthetic key was never actually checked.** The 9 genuinely-stale bundles are the *old*
sourced ones — the ones with real `papers/paperN_*/` directories whose files got touched.

---

## 4. The lift procedure's real-world failure modes

Read as a process engineer. The procedure is well-constructed *for what it is scoped to do* —
it is a claim-integrity and bookkeeping workflow with a reviewer-ordering discipline. **The
defect is scope: it has no manuscript-quality layer at all.** Below: what is missing, what is
unenforced, and precisely which steps produce which observed symptom.

### 4.1 Does any step own manuscript-level quality? — **No. Every step operates at sentence/claim/artifact level.**

Walking all 14 steps:

| § | What it owns | Level |
|---|---|---|
| §1 Pre-lift checks | source readiness, mapping rows exist | metadata |
| §2 Directory creation | six bookkeeping files | filesystem |
| §3 Initial lift / append | registers a source; inserts a `\section` **stub** | structural scaffold |
| §4 Sentence-state migration | per-sentence `bundle_destination` | sentence |
| §5 Citation merge | bibitem copy + collision resolution | citation |
| §6 Figure migration | **copies figures that already exist in sources** | artifact |
| §7 Paper-draft authoring | prose synthesis + 1 compile gate + 4 content gates | **sentence/claim** |
| §8 Stage 9 | figure rendering review | figure |
| §9 Stage 10 | claims review — numerical agreement, Lean-state match, DOI resolution | claim |
| §10 Stage 13 | adversarial review — citation, drift, placeholder, contradiction, overclaim | claim |
| §11 BLOCKER loop | per-finding fix + all-occurrence grep + ledger append | finding |
| §12 Iteration to GREEN | six boolean metadata fields | metadata |
| §13 Dashboard refresh | four script invocations | tooling |
| §14 Bundle close | panel populated, change-log entry, metadata snapshot | metadata |

**Not one row says "document".** There is no step that asks: *Is this the length its venue
requires? Does it have an argument a reader can follow start to finish? Are there figures a
referee would expect? Does it read as an article rather than as a response to a reviewer?*

§7 is the only step that could carry this and its four "substantive content gates" are: (1)
4-table cross-registry attribution audit, (2) hedging discipline on numerical claims, (3)
cross-program prior-art verifiability, (4) definition-before-broadening. **All four are
sentence-level correctness rules.** Its one structural gate is `pdflatex` exiting clean.

### 4.2 Which step produces the stitched-lift structure — **§3a**

`bundle_append.py` is invoked **once per contributing source**, each time with an
`--insertion-point '<§N>'`, and inserts a section skeleton there. The correlation is exact:

| Bundle | Sources (heatmap) | `\section{` in draft |
|---|---|---|
| D3 | **31** | **37** |
| D1 | 12 | 12 |
| D4 | 12 | 13 |
| F | 63 | 12 (+65 subsections) |
| D5 | 9 | 14 |
| I1 | 8 | 17 |

D1 is a one-to-one match; D3 is 31 sources → 37 sections. **The document's section
architecture is a projection of its source roster.** That is sedimentation, not architecture.

§3's framing paragraph (`:53`) is *aware* of the risk and states the right principle —
"Bundles are *synthesis-driven new compositions*, not stitched-together copies … the bundle's
narrative arc, section structure, and prose are **authored fresh**". But the principle is
prose; the tool ships one section per source; and **no later step ever revisits the section
architecture the tool created.** §7 authors *into* the skeleton (`:160` — "The `\section`
skeleton from §3 is just structural"), it never re-plans it. A stated principle with a
contradicting default and no enforcement point loses every time.

### 4.3 Which step lets referee-facing text into the manuscript — **§11, with §7 gate 2 as an accelerant**

§11 is a per-finding fix loop: reviewer emits BLOCKER → **author edits `paper_draft.tex`** →
grep for all occurrences → append to the supersession ledger → re-invoke the *same* reviewer.
Iterate. §12 repeats §8→§11 until the metadata booleans flip.

Three properties make this a scar-tissue generator:

1. **The manuscript is the fix surface.** The author's only lever on a finding is to edit the
   prose, so every finding leaves a textual deposit.
2. **The loop is adversarial and repeated.** D11/D12 ran **14 Stage-13 rounds in a single day**
   (git, 2026-07-31: `9a61e0b1` round 4 → `4b5a1b62` round 14). 6EE ran six rounds. Each round
   deposits more defensive text addressed at the previous round.
3. **§7 gate 2 ("hedging discipline") tells the author to add qualifications** rather than to
   find a formulation that needs none — it forbids *unfounded* hedges but is silent on the
   accumulation of founded ones.
4. **Nothing ever reads the result as a reader.** §12's exit is six booleans. §14's exit is a
   change-log line. There is no "does this still read as an article" pass anywhere.

Measured deposit (grep for `Stage 13|adversarial review|round-N|scope correction|corrected 20|previously read|an earlier draft|the audit found|Phase 6X|wave 6` in each `paper_draft.tex`):

| F | D4 | I1 | D3 | D6 | D1 | D2 | D5 | D8 | I3 | E1 | D7 | L3 | D11 | D12 | E2 | L1 | L2 | I2 | D9 | D10 |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| 37 | 35 | 29 | 27 | 13 | 10 | 9 | 9 | 9 | 9 | 9 | 8 | 6 | 5 | 3 | 3 | 2 | 2 | 1 | 0 | 0 |

(Raw hit counts, not adjudicated findings — I1's are largely legitimate subject matter per the
rubric's exception, and some hits in others are legitimate Lean-provenance references. The
*shape* is the signal: **the two bundles with zero hits, D9 and D10, are the two that took a
single-pass lift and were never put through a multi-round remediation loop.** D9 was created
and reviewed the same day (`4c17ece5`, 2026-06-10) and never touched again; D10 closed in ~24 h.
The correlation between round count and process-vocabulary density is the mechanism.)

The project's own documents exhibit the identical habit — `PAPER_STRATEGY.md:180` carries an
inline "⚠️ Scope correction, 2026-07-30 … this block previously advertised *Berry curvature*".
The behaviour is cultural, and the lift procedure institutionalises it by making
manuscript-editing the only response to a finding.

### 4.4 Which step produces zero-figure articles — **§6**

§6 is titled "Figure **migration**" and its first bullet is:

> "Copy each source's referenced figures from `papers/<source>/figures/` into `papers/<X>/figures/`."

It is a *transport* step. **There is no step anywhere in the procedure that plans what figures
the bundle needs.** If the contributing sources have no figures, the bundle has none, and
nothing objects. Result:

**9 of 21 bundles ship zero figures and zero `\begin{figure}`:** F (121 kB, 2,494 lines, the
80–150 pp flagship), D1 (58 kB), D2 (70 kB), D3 (139 kB), D4 (81 kB), D6, D7, D10, I3.
**Only 3 of 21 contain any `\begin{table}`.**

And Stage 9 (§8) **passes vacuously**: its criterion is "ALL figures PASS, no FAIL, no MINOR".
Over an empty set that is `True`. `papers/D10/bundle_metadata.json` records
`stage9_status: "green"` for a bundle with zero figures. Likewise `paper_provenance`
(`validate.py:2640-2660`) only validates that `\includegraphics` targets *exist on disk* — a
draft with no `\includegraphics` is trivially clean.

### 4.5 Steps that are documented but unenforced

| Step | Documented rule | Observed violation |
|---|---|---|
| §preamble + §10 | "**Reviewer-stage ordering is a hard gate.** Stage 13 may not be invoked until **both** Stage 9 AND Stage 10 are GREEN" | **5 bundles hold a recorded Stage-13 verdict with Stage 9 or 10 never run**: D6 (`s9: not_started`, `s10: skeleton`, `s13: green`), D7 (`s9: not_started`, `s13: green`), D8 (`s9: pending`, `s10: pending`, `s13: green`), D9 (`s10: pending`, `s13: green`, **and it is the portfolio's only 🟢**), I3 (`s9: pending`, `s13: green`). No script checks this. |
| §12 | "Repeat … until `bundle_metadata.json` shows `stage13_status == "green"` **and `blockers_open == 0`**" | **14 of 21 bundles have `stage13_status: green` with `blockers_open > 0`** (list in §3.4). No validate check compares the two fields. |
| §1 pre-conditions | "Source papers at 🟢/🟡 per-paper readiness" | D11/D12 lifted 2026-07-30 into a 15-RED portfolio. Not checked. |
| §7 | "**LaTeX compile gate (mandatory before §8)** … Stage 9 may not be invoked until LaTeX compiles cleanly." | `validate.py --check paper_latex_compiles` is **advisory and always returns `passed=True`** (`validate.py:6274-6276`) and is **skipped unless `--force-latex`**. |
| §13 | "All four must succeed before bundle close." | Advisory checks; nothing blocks. |

**The pattern:** every quality rule in the procedure is enforced by *the reader of the
procedure*, and every mechanical check is either advisory or measures bookkeeping.

### 4.6 Recommended changes — concrete

Numbered so they can be adopted individually. **F-01…F-06 are the manuscript-quality layer the
procedure lacks; F-07…F-09 fix the absorption machinery.**

---

**F-01 — Insert a new §0: *Bundle charter and page budget* (before §1).**
Before any lift, author `papers/<X>/CHARTER.md` (one page, committed) containing:
- target venue (single, named) and its **hard length limit or floor**, as a number;
- the **one-sentence contribution claim** the whole article delivers;
- the **planned section architecture** — a numbered outline of 6–12 sections written *before*
  any source is registered, with a one-line statement of what each section argues;
- the **figure plan**: for each planned figure, what it shows and which computed result it
  comes from — including figures that do not yet exist and must be authored;
- which phases/sources feed which planned section (many-to-one is the expected shape).

Rationale: this is the artifact whose absence causes §4.2 and §4.4. The section architecture
must exist *before* `bundle_append.py` can project one from the source roster. Make the
charter's outline the required `--insertion-point` vocabulary, so a source can only be
appended *into a section that the charter planned*.

**F-02 — Change §3a from "one section per source" to "map source → planned section".**
`bundle_append.py` gains `--charter-section <name>` validated against `CHARTER.md`, and drops
the stub-insertion default entirely when the target section already exists. Registering a
source must never create a section. This removes the mechanism, not just the symptom.

**F-03 — Promote §6 from "figure migration" to *"figure realisation"*, and make Stage 9
non-vacuous.**
- §6 acquires: "For every figure in the charter's figure plan, either the figure exists in
  `papers/<X>/figures/` or the section is marked `\figuredeferred{<id>}{<reason>}`."
- Stage 9's pass criterion changes from "all figures PASS" to "all **planned** figures PASS
  **and** the count of unexplained `\figuredeferred` is zero."
- A bundle with zero figures and no charter figure plan is a **charter defect**, caught at §0.

**F-04 — Add a new §7.5: *Whole-document read-through* (mandatory, before §8).**
A single reviewer pass — human or a purpose-built agent, explicitly **not** the
adversarial-reviewer — whose only brief is: *read this start to finish as a referee at the
named venue who has never seen the repository.* It answers five questions and blocks on any
`no`:
1. Does the abstract lead with the result?
2. Does each section advance a single argument that connects to the next?
3. Is every symbol defined before use?
4. Is there any sentence addressed to a reviewer, to the project's own process, or to a prior
   draft, rather than to a reader of the literature? (**deletion list, with line numbers**)
5. Is the compiled length within the charter's budget?

This is the step that does not exist. Its output is a **restructuring instruction**, not a
finding list — which is why it must not be the adversarial reviewer, whose output is
findings-only by design (`WAVE_EXECUTION_PIPELINE.md:602`).

**F-05 — Add a *scar-tissue prohibition* to §11 and a de-scarring pass to §12.**
- §11 step 2 gains: "A fix may not narrate itself. Corrections are made silently in the
  manuscript and recorded in `change_log.md` + the supersession ledger. Any sentence
  containing a date, a round number, a review verdict, a phase identifier, or the words
  *previously*, *earlier draft*, *corrected*, *scope correction* is a §11 violation."
- §12 gains a terminal **de-scarring pass**: after the last round converges, re-run F-04
  question 4 alone and delete. Empirically necessary — the 14-round D11/D12 day is exactly
  when this deposit accumulates.
- Apply the same rule to `PAPER_STRATEGY.md` when it is rewritten (S-12).

**F-06 — Make §12 and §14 assert on the document, not on booleans.**
§12's exit condition gains three document-level clauses, all machine-checkable (see §5):
`pages within charter budget`, `figures ≥ charter plan`, `blockers_open == 0 AND
stage13_status == green` (currently only the second half is written and neither is checked).
§14's close gains: the compiled PDF, its page count, and its figure/table counts are recorded
in `bundle_metadata.json` at close.

**F-07 — Fix the absorption trigger (P0 — this is a code fix, not a doc fix).**
`check_bundle_source_freshness.py` must:
1. **Not report "fresh" on a comparison it did not make.** When `_latest_source_mtime` returns
   `None` for every source, emit a distinct finding — `unmeasurable: N of N sources are
   synthetic keys with no on-disk directory` — at WARN, never at PASS.
2. **Track Lean substrate, which is what sourceless bundles are actually made of.** Add a
   `lean_modules` list to `bundle_metadata.json` (the data already exists — `bundle_append.py`
   takes `--lean-modules` and writes it to `append_log.json`) and compare the newest mtime
   under `lean/SKEFTHawking/<Module>.lean` against `last_lift`. This is the change that makes
   D6–D12 absorbable at all.
3. Promote the check from advisory to **FAIL at the submission gate** (the docstring already
   anticipates this: "promotable to FAIL at the Phase 8 submission gate via `--strict`").

**F-08 — Add branch D.0 to the absorption protocol: *target unsound → remediate before absorb*.**
Insert as the **first** row of the Stage-D decision table:

| Condition | Branch | Action |
|---|---|---|
| `paper_draft.tex` exists **AND** (`blockers_open > 0` **OR** `stage13_status != green` **OR** the bundle fails its charter's length/figure floor) | **D.0** | **Do not absorb.** Register the mapping row (Stage B) so the work is *homed*, set `absorption_queued: true` in `bundle_metadata.json`, and stop. The bundle is remediated to GREEN first; the queued absorptions are then applied as a single D.2/D.4 batch, followed by one Stage-F cycle. |

Rationale: appending to a bundle with 37 open blockers makes the review loop non-convergent
(§3.4) and inflates an artifact that already needs restructuring. D.0 decouples *homing* from
*absorbing* — the work never becomes un-homed, but the defective bundle stops growing. This is
the branch the protocol is missing, and it is the normal case today, not the exception.

**F-09 — Restore per-phase mapping granularity.**
Stage B's sourceless variant must produce **one row per phase**, not one per bundle
(`_phase6EA_lean_only`, `_phase6EB_lean_only`, …), as `6E_SERIES_ABSORPTION_HANDOFF.md:224`
specified and as the 6A\* series did correctly. Retrofit rows for 6EA/6EB/6EC/6ED/6EE and for
6CA/6CB/6CD/6CE. Without per-phase handles there is no unit of absorption smaller than the
whole bundle.

**F-10 — Add a `bundle_lean_module_coverage` check: declared modules must appear in the draft.**
The cheapest fix for the ~340 un-homed/unlifted modules of §2.0, and it needs no new data.
For each bundle, take the union of `--lean-modules` values recorded in
`papers/<X>/append_log.json` (already written by `bundle_append.py`) and assert each module
basename appears at least once in `papers/<X>/paper_draft.tex`. Report per module:
`CITED` / `REGISTERED-BUT-ABSENT`. FAIL at the submission gate on any
`REGISTERED-BUT-ABSENT`, WARN at draft stage. Exclude a curated grep-ambiguous list
(`Basic`, `Trace`, `Module`, `Sum`, `Spectrum`, `Chain`, `Concrete`, `Positive`, `Log`).
This converts §2.5's invisible failure into a hard signal, and it fires today on D8 (the whole
`GenericSUd*` and `KMM*` families), D9 (the `Gaussian*` and `DiamondSDP*` blocks), D4, D2 and
L2. Pair it with the inverse direction — a repo-wide sweep listing every `lean/SKEFTHawking/`
module cited in **no** bundle — surfaced on the dashboard as an **un-homed-substrate register**,
the publication-side analogue of the proof atlas's frontier.

---

## 5. Gate coverage gap

### 5.1 The claim-level hypothesis — **CONFIRMED**, with two refinements

**Refinement 1: some gates *do* read the manuscript.** Six of the eleven gates plus ~8
`validate.py` checks open `paper_draft.tex`. But every one extracts **claim-level tokens** —
`\bibitem{}` keys, `\texttt{}` identifiers, hypothesis-name substrings, unit-bearing numeric
literals, abstract sentences. **None derives a document-level property.**

**Refinement 2: the heatmap's "gates" are not gate evaluations.** The Gate × Bundle
distribution table (`BUNDLE_READINESS_HEATMAP.md:49-71`) is produced by
`qi_register.classify_finding(f)` (`bundle_readiness.py:135`), which is a **regex keyword match
against the reviewer's own free-text finding title/body** (`qi_register.py:89-125`). A finding
whose text happens to contain `\btest\b` is bucketed as `ComputationCorrectness`. Nothing is
evaluated. The table describes *what reviewers wrote about*, not *what is true of the bundle*.

**The verdict function, verbatim** (`bundle_readiness.py:347-368`):

```python
n_blockers = sum(sev_counter[s] for s in ("critical", "major"))
if n_blockers > 0:                 readiness = "RED"
elif not review_recorded:          readiness = "YELLOW (unreviewed)"
elif len(open_findings) > 5:       readiness = "YELLOW"
else:                              readiness = "GREEN"
```

**"0 blockers" means: zero ReviewFinding records that a past reviewer wrote down and nobody
later marked closed.** It is fully compatible with a 300-line stub. Since the 2026-06-10 S5
patch, GREEN additionally requires that *a dated review file exists* — not that it found
anything. **D6 is the living proof: `stage10_status: "skeleton"`, zero findings, 🟡 — better
than every fully-drafted sibling.** The verdict function rewards emptiness.

### 5.2 What is measured nowhere

| Property | Measured? | Evidence |
|---|---|---|
| Page count | **No** | `scripts/compile_bundle_pdf.py:105-112` **computes** it via `pdfinfo`, then at `:114` `ok = not errors and unresolved <= 0 and not unused_opts` — `pages` enters only the human-readable string at `:116`. The instrument exists and is deliberately unwired. |
| Word count | **No** | `texcount` does not appear in the repo. |
| Section count | **No** | `\section` appears in `scripts/*.py` exactly once, as a template literal in `bundle_append.py:184`. Never counted. |
| Figure count / adequacy | **No** | `paper_provenance` (`validate.py:2647-2660`) checks only that referenced `\includegraphics` targets exist. Zero references ⇒ trivially clean. `bundle_figure_integrity` (`:2086`) is real but covers **D11 and D12 only**, by a `d11_`/`d12_` filename filter at `:2140`. |
| Table count | **No** | — |
| Structural coherence | **No** | — |
| Reader-facing voice | **No** | The nearest gate, NarrativeGrounding, checks abstract-sentence→SUPPORTS-edge existence. |
| Length **target** | **Does not exist** | Grep for `page target|target length|word limit|page limit|target_pages` across `docs/*.md` + `scripts/*.py` returns one hit, a prose aside at `PAPER_DRAFT_MAPPING.md:80`. `PAPER_STRATEGY.md` §6 has per-bundle page figures in a markdown table cell that no script parses. |

### 5.3 Two gate defects worth fixing independently of the new gates

- **G-01 (P1) — Gate 10 `FirstClaimVerification` has never been implemented.**
  `READINESS_GATES.md:203`: "**Status:** The ledger node type is not yet implemented. Until it
  lands, this gate is `needs-recheck` for every paper with a first-claim — advisory only."
  It is also **absent from the bundle heatmap entirely** (S-44). This is the gate whose whole
  purpose is to catch unhedged novelty claims — and the 6EA priority claim *was* refuted by a
  live prior-art sweep (`PAPER_STRATEGY.md:194`). The one failure the gate exists to prevent
  happened while the gate was a stub.
- **G-02 (P2) — Gate 7 `NarrativeGrounding`'s doc and code disagree.**
  `READINESS_GATES.md:126` promises "abstract, **intro, conclusion**". `build_graph.py:1165-1180`
  extracts ProseClaims from `\begin{abstract}…\end{abstract}` **only** — "Broader paper prose
  (intro, conclusions, body sections) is deferred" — and `readiness_gates.py:468` consumes only
  those. The only gate nominally about reader-facing prose covers ~1 % of the manuscript.

### 5.4 Proposed new gates — implementable as specified

All five are cheap because the instruments already exist (`compile_bundle_pdf.py` computes
pages; `bundle_append.py` already writes `--lean-modules`; grep-counting `\section` /
`\includegraphics` is trivial). Each is specified as a `validate.py` check plus a
`bundle_readiness.py` gate column.

---

**Gate 12 — `ManuscriptLength`** (Priority 1)

*Intent:* the compiled article is within the length its named venue requires.

*New data required:* `papers/<X>/CHARTER.md` (F-01) or a `length_target` block in
`bundle_metadata.json`:
```json
"venue": "Physical Review D (long article)",
"length_target": {"unit": "pages", "floor": 25, "ceiling": 60}
```
For PRL-class targets use `{"unit": "word_equivalents", "ceiling": 3750}` per the rubric's
PRL rule (text + 300/figure + tables + captions + references).

*Implementation (`scripts/validate.py`, new check `bundle_manuscript_length`):*
1. `compile_bundle_pdf.py --bundle <X>` (already exists); parse `Pages:` from `pdfinfo`.
2. For word-equivalent targets, `pdftotext` the body (already a dependency of
   `compile_bundle_pdf.py`) + `300 × n_figures` + table/caption/reference allowances.
3. Persist `compiled_pages` and `compiled_word_equivalents` into `bundle_metadata.json` so
   the heatmap can render them without recompiling.

*Passes iff:* `floor ≤ compiled ≤ ceiling`.
*Blocks on:* below floor (a "deep paper" that is a letter) or above ceiling (a PRL that is not).
*Note:* this single gate would have flagged **D7 (16 kB / 339 lines / 1 subsection, target
~40 pp) and D10 (22 kB / 315 lines, target ~40 pp)** on the day they were closed GREEN.

---

**Gate 13 — `FigureAdequacy`** (Priority 1)

*Intent:* the article has the figures a referee at its venue expects, and each is planned
rather than inherited.

*Implementation (`bundle_figure_adequacy`):*
1. Count `\begin{figure}` + `\begin{table}` in `paper_draft.tex`.
2. Read the charter's `figure_plan` (list of `{id, shows, source}`); require each planned id
   to resolve to an `\includegraphics` in the draft **or** to a `\figuredeferred{id}{reason}`
   macro.
3. Apply a tier floor as a backstop where no charter exists yet:
   Tier 0 (F) ≥ 8; Tier 1 (D\*) ≥ 4; Tier 3 (I\*) ≥ 2; Tier 2/4 (L\*, E\*) ≥ 1.

*Passes iff:* every planned figure resolves **and** count ≥ tier floor.
*Blocks on:* zero figures in any Tier 0/1/3 bundle.
*Note:* fires immediately on **9 of 21 bundles**, including the flagship.

---

**Gate 14 — `StructuralCoherence`** (Priority 1)

*Intent:* the section architecture is authored, not sedimented from the source roster.

*Implementation (`bundle_structural_coherence`):*
1. `n_sections` = count of `\section{` + `\section*{`; `n_sources` = length of the bundle's
   mapping-derived source list.
2. **Sedimentation ratio** `r = n_sections / n_sources`. FAIL if `r > 0.8` **and**
   `n_sections > 12` — the signature of one-section-per-source. (D3: 37/31 = 1.19 with 37
   sections → FAIL. D1: 12/12 = 1.0 with 12 sections → borderline, WARN.)
3. FAIL if `n_sections > 20` for any Tier 1/2/4 bundle (D3's 37 sections + 114 subsections in
   a 30–50 pp target is not an architecture).
4. FAIL if a required-section set is missing: `abstract`, an introduction-class first section,
   a conclusion/discussion-class final section, and a bibliography with `\bibitem` count > 0.
   (**This alone catches D8 — 26 `\cite{}`, 0 `\bibitem` — and D10 — 13 `\cite{}`, 0
   `\bibitem`.**)
5. WARN if any `\section` body is under 400 words (an unfilled stub — the
   `papers/D4/append_log.json:130` post-bibliography-skeleton failure mode).

*Passes iff:* required sections present, bibliography non-empty, ratio and count within bounds.

---

**Gate 15 — `ReaderFacingVoice`** (Priority 1)

*Intent:* the manuscript addresses a reader of the literature, not a reviewer or the project's
own process.

*Implementation (`bundle_reader_facing_voice`) — deterministic, not an LLM:*
Scan `paper_draft.tex` outside `\begin{comment}` blocks and `%` comments for a denylist,
skipping bundles whose charter declares the pipeline as subject matter (I1, and I2/I3 for
library-name terms):

| Class | Patterns |
|---|---|
| review narration | `Stage[ -]13`, `Stage[ -](9\|10\|12\|14)`, `adversarial review`, `round[- ][0-9]+`, `the audit found`, `reviewer`, `BLOCKER` |
| revision narration | `previously read`, `an earlier draft`, `⚠`, `[Ss]cope correction`, `[Cc]orrected 20[0-9]{2}-`, `retracted`, `[Ww]as wrong and is` |
| internal process vocabulary | `Phase 6[A-Za-z]`, `Wave [0-9]`, `bundle`, `lift`, `kernel-pure`, `tracked Prop`, `sorry`, `roadmap`, `\bQI\b`, `supersession` |
| dates as narration | any `20[0-9]{2}-[0-9]{2}-[0-9]{2}` in body prose outside a citation or a version pin |

*Passes iff:* zero hits in classes 1–2, and class-3 hits only inside a `\providesscope{methodology}`
region a charter declares.
*Note:* fires on **19 of 21 bundles** at current counts; F (37) and D4 (35) worst.
Deliberately deterministic so it can run every commit and cannot drift.

---

**Gate 16 — `MetadataTruthfulness`** (Priority 1) — *the cheapest and highest-yield*

*Intent:* a bundle's recorded status matches its own findings and its own procedure.

*Implementation (`bundle_metadata_self_consistent`), four assertions:*
1. `stage13_status == "green"` ⟹ `blockers_open == 0`. **Fires on 14 of 21 bundles today.**
2. `stage13_status ∈ {green, pending}` with a non-null `last_stage13_review` ⟹
   `stage9_status == "green" AND stage10_status == "green"` (the `BUNDLE_LIFT_PROCEDURE.md`
   §10 hard gate). **Fires on 5 bundles: D6, D7, D8, D9, I3.**
3. `readiness == "GREEN"` ⟹ all of (1) and (2). **D9, the portfolio's only GREEN, fails (2).**
4. `stage13_redo_required == true` ⟹ `last_stage13_review` is **newer** than `last_lift`.
   **Fires on D12** (redo required, review 07-31, D.3 re-lift 08-01).

This gate requires no new data at all — every field already exists in
`bundle_metadata.json`. **It converts the lift procedure's §10 and §12 from prose into
enforcement**, which is the single change that would have prevented most of §4.5.

---

*Wiring, per `READINESS_GATES.md:221-231`:* update `READINESS_GATES.md` first (and bump its
title from 11 gates to 16); add evaluators to `scripts/readiness_gates.py`; add the checks to
`scripts/validate.py`; extend `scripts/templates/partials/readiness_tab.html`'s `GATES` array;
add the columns to `bundle_readiness.py`'s heatmap (replacing the `classify_finding` regex
buckets, which should be relabelled *"finding topics"* since they are not gates). Also close
S-44 by restoring `NumericalFreshness` and `FirstClaimVerification` to the bundle heatmap.

---

## 6. Pending work not yet in any strategy document

Each item below is live or authorized, and each needs a declared landing target before the
strategy is rewritten.

| # | Thread | Status | Where its output must land | Currently declared? |
|---|---|---|---|---|
| P-01 | **Phase 5q.E / 5q.F / 5q.G / 5q.H — the Pin⁺ ℤ/16 arc** (5q.H re-based 2026-07-13; continuation of 5q.G) | 5q.E COMPLETE-CONDITIONAL (2026-06-14); 5q.F/G **live `/goal` arc** | **D2** (owner of the 16-convergence) and **L2** (the splash). Note `SIXTEEN_CONVERGENCE_STATUS.md:12`'s standing rule: the load-bearing result is three generations and it does **not** depend on the convergence — so this arc strengthens D2's *bordism* section, not L2's headline, and the strategy should say so. | **No — and this is U-01, the largest un-homed block.** None of 5q.E/F/G/H/T declares a bundle. **162 `PinPlus*` modules + ~88 `Smith*`/`Wu*` modules have zero `papers/` hits.** D2/L2's change logs both end 2026-06-10, before 5q.E's capstone; both bundles are 🔴 carrying the same 6 unreconciled paper10 findings this arc is meant to discharge; and 5q.T's own closing task ("update D2 and L2 to cite the substantive theorems, not the proxies", `Phase5qT_...:133-134`) was never executed. |
| P-02 | **6E series → D12/D11 residual** | Substrate frozen; bundles lifted 2026-07-30; D12 took a D.3 re-lift 2026-08-01 | D12 (6EA/6EB/6EC/6EE), D11 (6ED) | **Partly.** The bundle-level rows exist; **per-phase rows do not** (F-09), the `temporary/working-docs/` synthesis is still absent and its content is gitignored (S-47), and D12's Stage-F is entered-not-completed (A-04). |
| P-03 | **Mathlib v4.32.0 pin drift** — `validate.py --check paper_toolchain_pin_drift` reports **29 pin-drift + 5 capability-claim sites** (34 total, of which **18 pin-drift sites are in bundles**: D10:105, D11:546, D12:129, D2:15, D9:1074, E1:449/453/454, E2:484/485/488/489, I1:1182/1196, I3:1197, L2:12/387/396; plus D6:327/787 capability-claims) | Advisory; the check **PASSES** with 35 warnings | Each affected bundle's Stage 13 | **No.** No strategy document mentions the bump or the deferred sites. `project-mathlib-v432-bump-complete` memory records "32 paper pin-drift sites (Stage-13 deferred)". <br>⚠️ *Calibration:* D11:546 and D12:129 flag `c4843367`, which repo `CLAUDE.md` records as the **correct live PhysLib pin** — those two are plausibly checker false-positives (it appears to compare every hash against the Mathlib pin). Verify before remediating. |
| P-04 | **New thematic series `6D*` / `6F*` / `6G*`** — `Phase6DA` (PLANNED, authorized 2026-07-02, reframed 07-04; dimensionless-constant determination-chain provenance), `Phase6FA` + `Phase6GA` (PLANNED, namespaces authorized 2026-07-29) | Authorized, not executed | **Undecided.** `Phase6DA:52` "**Publication target: DEFERRED — none assigned**". `Phase6FA:7` claims an exemption — "a different *kind* of work … **no bundle target**, no Stage-13 claims review". 6GA: silent. | **No.** Three authorized series with no landing target. Per Invariant #14 these cannot legally execute; per S-15 the invariant's enum cannot legally hold their answer either; and 6FA asserts an exemption the invariant does not provide for. **This is the highest-priority item for the strategy rewrite** — it is the operator's goal 2 in its purest form. If some series are genuinely infrastructure rather than paper-shaped, the strategy must define that category explicitly rather than letting individual roadmaps self-exempt. |
| P-04b | **Phase 6r / 6r′ — the SymTFT line** | Roadmaps say **every wave "⏳ NOT STARTED"**; ~54 modules exist in `lean/` regardless (U-04) | Undeclared beyond 6r′'s five-way "D2/D4/D5/L1/F" | **No.** Built off-roadmap, no destination, and the roadmaps that would assign one still describe the work as not begun. This is the clearest instance of substrate outrunning the publication plan and needs an explicit operator decision: home it, or record it as infrastructure. |
| P-05 | **Phase 6BD (Jordan–Wigner / Trotter fermionic simulation)** — "PLANNED — **IN PLAY** (authorized 2026-06-29; activated 2026-07-01) … to be picked up at **full strength in the near future**" | Activated, in play | Declared into **D8** by the roadmap ("*not* D10 — JW/Trotter resource content is a compilation-substrate feature") | **One-directional.** D8's own Sources list (`PAPER_STRATEGY.md:154`) does not include 6BD. Add it. |
| P-06 | **Phase 6CC (2D class-D SPT / Pin⁺ condensed-matter reframe)** — "⏸ PARKED / HOLDING, gated on 5q.G → L2" | Parked | **D2 or D11**, "decided at Stage 1" | Honestly dual-declared; must resolve when 5q.H/5q.G unblocks it. Couple this decision to P-01. |
| P-07 | **Phase 6CA differential-geometry remainder** — Berry curvature, bulk–boundary correspondence, continuum Chern `C = (1/2π)∫F` | DR-gated / route-C deferred (4k–15k+ LOC of absent Mathlib manifold infrastructure) | D11 §(i), if ever built | **Yes, and honestly** — `PAPER_STRATEGY.md:180-182` marks these DEFERRED, not conditional, and explicitly corrects a prior overstatement. **This is the reference case.** Every other deferred thread should be documented in this shape. |
| P-08 | **Mathlib upstreaming batch** — concrete-radius matrix logarithm (`matrixMercatorLog`), generic order-2 BCH cubic, SU(d) Cartan density-from-witness, matrix-exp local homeomorphism, lean-tensor-categories extraction (`Phase6_Deferred_Targets.md` items 1–4) | Open future work | **I2** (lean-tensor-categories) and **D8** §(vi) (which already claims the "Mathlib-upstream contribution portfolio") | Partly — D8 claims the portfolio; I2's upstream cycle is a stated risk at `PAPER_STRATEGY.md:365`. No target holds the four Mathlib-PR-eligible lemmas as a deliverable. |
| P-09 | **Vestigial-gravity RHMC at L ≥ 8** (`Phase6_Deferred_Targets.md` item 12; memory `project_mlx_rhmc_port`, `project_rhmc_vestigial_missing_item`) | Campaign staged, operator-launched; L=8 m=0.1 returned **no signal** | **D3 §10** per the memory note | Not in `PAPER_STRATEGY.md`. D3's §2.2 content list does not mention the MC campaign; `ProductionRunHealth` is the gate that will block on it if the paper claims MC evidence. |
| P-10 | **842 repo-wide docstring-drift advisories** outside the strict families (`6E_SERIES_ABSORPTION_HANDOFF.md:76`) | "a separate, unscheduled backlog worth a decision" | Not publication-facing directly, but `lean_docstring_refs_resolve` + `prose_theorem_reference_coverage` feed bundle Stage-13 | Unscheduled. |

---

## What I could not check

Stated explicitly, per the rubric — an unchecked item silently reported as clean is worse than a gap.

1. **The un-homed module counts in §2.0 are name-grep results, not semantic ones.** A module
   whose *content* is described in a draft under different wording, without its basename
   appearing, counts as un-homed by my method. That is the correct test for *verifiability by
   the reader* (rubric Axis 3: "a formally-verified result the reader cannot locate is not a
   result") but it overstates the case if the intent was only that the physics be present.
   Conversely, grep-ambiguous basenames were **excluded** from un-homed claims, so the counts
   also undercount. Treat ~340 as the right order of magnitude, not an exact figure.
2. **Whether an un-homed module is *supposed* to be publication-facing.** Some of the 340 are
   plausibly internal infrastructure (helper lemmas, bridge modules) that no paper should name.
   I did not triage them. **The triage is itself a deliverable the strategy rewrite needs** —
   F-10's un-homed-substrate register is the mechanism, and someone has to decide, per arc,
   what is a result and what is scaffolding.
3. **Manuscript prose quality.** Out of scope by assignment. The scar-tissue counts in §4.3 are
   raw grep hits used as *process evidence*, not adjudicated findings; the sibling per-bundle
   auditors own the adjudication and their counts will differ from mine.
4. **Compiled page counts.** I did not run `latexmk`/`pdflatex` on the 21 bundles — that is the
   per-bundle auditors' ground-truth step. §4 and §5 use byte size, line count and section
   count as proxies, which is sufficient to establish *that nothing measures length* but not to
   state any bundle's true page count.
5. **Whether the D11:546 / D12:129 PhysLib pin flags are genuine drift or checker
   false-positives** (P-03). Flagged with calibrated uncertainty rather than asserted.
6. **`RESEARCH_STATUS_OVERVIEW.md:628` "Technical blockers and outstanding work"** — I read the
   surrounding sections but did not enumerate that subsection against the live roadmap set. It
   is dated 2026-06-10 and almost certainly omits the `6B*`/`6C*`/`6E*`/`6F*`/`6G*` corpus, but
   I did not verify item by item.
7. **The claim in S-43 that no bundle has a `tables.py`** was verified by directory listing
   only; I did not check whether some other mechanism supplies autogenerated tables to bundles.
