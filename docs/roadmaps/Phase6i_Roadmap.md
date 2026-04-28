# Phase 6i: QI Register Closure & Process Hardening

## Hygiene-Wave Roadmap — April 2026

*Prepared 2026-04-28 | Derived from `docs/QI_REGISTER.md` (Stage 14 advisory output, regenerated 2026-04-28 with 373 ReviewFinding nodes consumed) + the new primary-sources cache pattern established as PoC during Phase 6e Wave 3 closure.*

**Entry state (2026-04-28 Inventory_Index snapshot):** 192 modules, 4466 theorems (4443 substantive + 23 placeholder), 0 sorry, 1 axiom, 36 papers, 78 notebooks, 132 figures, 80 test files. Phase 6e Waves 1–3 SHIPPED; Wave 4 (`NonlinearEFE.lean`) unblocked at full scope. Phase 6i runs in parallel with Phase 6e Wave 4 — it is a hygiene programme, not a structural-physics programme, and operates entirely on existing artifacts.

**Thesis.** The Stage 14 QI register currently has **8 open systemic items** spanning all 8 readiness gates, with an aggregate **373 ReviewFinding nodes** across the project history. None block any single paper individually, but together they represent ~3 PM of accumulated bookkeeping debt + 1 critical gap (citation hallucination) that the project's own internal pipeline cannot fully prevent. Phase 6i closes the open QI items via 6 dedicated hygiene waves, hardens the pipeline against recurrence by wiring new `validate.py` checks, and establishes the primary-sources cache pattern (PoC done in Wave 6e.3) as the project-wide convention for citation grounding.

**Open-ended structure.** Phase 6i is **append-only**: new waves are added if Stage 14 surfaces new patterns during the rollout. The wave list below is the planned scope as of 2026-04-28; if a wave's execution surfaces a new systemic finding category, a new wave is appended rather than retrofitted into an existing one. This keeps each wave's scope tight and the trend log honest.

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
>
> 1. Read CLAUDE.md, WAVE_EXECUTION_PIPELINE.md, SK_EFT_Hawking_Inventory_Index, `docs/QI_REGISTER.md`
> 2. Read this roadmap for wave assignments
> 3. Phase 6i is **hygiene work only** — no new physics, no new Lean modules unless explicitly required (e.g., a new `validate.py` Lean-source check). Each wave operates on existing artifacts.
> 4. Each wave still follows the WAVE_EXECUTION_PIPELINE.md 14-stage process — but expect Stages 3 (Lean), 6 (Python tests for new physics), and 8 (figures) to be no-ops or trivial in most waves. The substantive work is in Stages 1, 7, 10, 12, 13, 14 (cross-cutting registry + paper sweeps + reviewer re-invocations + counts/inventory sync).
> 5. **Mandatory Stage 13 re-invocation for any paper touched** — every paper modified in a Phase 6i wave must clear a fresh adversarial-reviewer pass before that wave is marked SHIPPED.
> 6. **Mandatory Stage 14 register regeneration after each wave** — confirms the wave actually closed the targeted QI item(s), or surfaces a residual that becomes a follow-up wave.
> 7. **User authorization required only at Wave 1 start** (Phase 6i opens with a project-wide convention change). Subsequent waves run autonomously following the same wave-execution pipeline, with the Stage 13 re-invocation per affected paper as the natural gate.

---

## Scope Lock & Out-of-Scope

**IN SCOPE for Phase 6i:**
- Citation integrity: per-phase `Lit-Search/Phase-X/primary-sources/` cache rollout for every external bibitem in `CITATION_REGISTRY`
- New `CITATION_REGISTRY` fields project-wide: `primary_source_path`, `inprep`
- New `validate.py --check citation_primary_sources_present` (mandatory at Stage 13)
- Extension of `scripts/citation_cache.py` to write per-phase per-bibkey files (one fetch, two destinations)
- Parameter provenance closure: human-verify all `human_verified_date: None` entries in `PARAMETER_PROVENANCE`
- Narrative-grounding sweep: re-ground all open NarrativeGrounding findings in primary sources or Lean theorems
- Cross-paper consistency sweep: walk all CrossPaperConsistency findings; reconcile contradictions
- Lean proof substance audit: verify each cited Lean theorem in every paper exists with cited name + discharges cited content
- Assumption disclosure: apply paper41's "derived vs tracked-Prop" distinction across all papers using H_*-named Props
- Computation correctness audit: spot-check open ComputationCorrectness findings
- Production run health audit: verify "production run" claims have backing data
- Pipeline doc updates: WAVE_EXECUTION_PIPELINE.md Stage 1 + Stage 13 amended for new conventions
- Final QI register sweep: confirm all 8 (or N) open items closed with `evidence_on_close`

**OUT OF SCOPE for Phase 6i:**
- New physics modules (Phase 6e Waves 4–6, Phase 6f, Phase 6g, etc. continue independently in their own roadmaps)
- New papers (Phase 6i edits existing papers only)
- New experimental predictions
- Aristotle resubmissions for closed sorries (Stage 4 is independent of Phase 6i)

---

## Track A: Citation Integrity Foundation (6i.1)

### Wave 1 — Primary-Sources Cache Rollout [Pipeline: Stages 1–13] — **TIER 0 — central**

**Goal.** Establish the per-phase primary-sources cache as the project-wide grounding artifact for every external bibitem. PoC completed during Phase 6e Wave 3 closure (`Lit-Search/Phase-6e/primary-sources/` with 4 entries). This wave back-fills all phases.

**Prerequisites:** PoC convention documented in `feedback_primary_sources_cache.md` memory + Phase-6e example. User authorization (project-wide convention change).

**Module structure (Python + Lean):** No new Lean. Python additions:
- `scripts/back_fill_primary_sources.py` — walks `CITATION_REGISTRY`, fetches Crossref + arXiv (or abstract fallback) per bibkey, writes to `Lit-Search/Phase-X/primary-sources/<bibkey>.{pdf,json,abstract.txt}` keyed off the registry's first `used_in` paper's phase number
- Extension to `scripts/citation_cache.py` to optionally write per-phase per-bibkey files alongside the existing `docs/citation_verifications.jsonl` cache (one fetch, two writes)
- New `validate.py --check citation_primary_sources_present` walking every cited bibitem in every `papers/*/paper_draft.tex`; FAIL on missing file (unless `inprep: True`)

**Per-bibkey acquisition tier hierarchy (per `feedback_primary_sources_cache.md`):**
1. **arXiv PDF** (preferred when DOI/arXiv ID available)
2. **arXiv .tex source** (when arXiv ID available; full content for grep)
3. **INSPIRE-HEP fulltext URL** or **OSTI / NASA ADS fulltext** (older HEP papers)
4. **Author/institutional preprint URL** (manual; documented in registry `notes` field)
5. **Crossref/ADS abstract** (`<bibkey>.abstract.txt`) — fallback when paywalled and no preprint
6. **Crossref metadata only** (`<bibkey>.json`) — true last resort (books, very old paywalled with no preprint)

**Field additions to `CITATION_REGISTRY`:**
- `primary_source_path: str | None` — relative path from project root to the cache file (or `None` for in-prep self-cites). Single canonical entry; for multi-file caches (PDF + JSON + abstract), this points at the "best available" tier.
- `inprep: bool` — discriminator field; `True` exempts the entry from the primary-source-cache requirement (replaces `doi_verified: True` semantic-overload for in-prep self-cites). Closes round-1 reviewer F3 finding from paper41.

**Bridges:**
- Closes Stage 14 `qi-citationintegrity` (45+ findings, 13 papers — the largest single QI item)
- Establishes the validation infrastructure consumed by all subsequent 6i waves

**Deliverables:**
- `scripts/back_fill_primary_sources.py` shipped; runs to completion across all phases
- `Lit-Search/Phase-{5d,5p,5w,5x,5y,5z,6a,6b,6c,6d,6e,6f}/primary-sources/` populated (~190+ bibkeys)
- `validate.py --check citation_primary_sources_present` shipped and passing
- `scripts/citation_cache.py` extended; documented
- `WAVE_EXECUTION_PIPELINE.md` Stage 1 + Stage 13 sections amended
- All `CITATION_REGISTRY` entries gain `primary_source_path` + `inprep` fields
- Inventory update: ~190+ files added under `Lit-Search/Phase-*/primary-sources/`; ~150-300 MB git-tracked storage

**Estimated LOE:** 4–8 person-months (mostly mechanical fetching + per-entry registry edits; the script + check is ~1 PM of code work, the rest is per-bibkey fetch + verification)

**Risk.** Medium-low. Primary risk: paywalled papers without arXiv preprints fall to abstract-only tier; documented as an honest limit, not a failure. Storage exceeding 1 GB triggers a git-lfs migration decision (gate).

**Decision Gate I.1:** at Wave 1 close, the citation-cache check is mandatory at every Stage 13. Any paper failing the check cannot ship a Stage 13 PASS verdict.

---

## Track B: Provenance & Submission Gates (6i.2)

### Wave 2 — Parameter Provenance Closure [Pipeline: Stages 1, 7, 12–14]

**Goal.** Walk `PARAMETER_PROVENANCE` (in `src/core/provenance.py`); identify all entries with `human_verified_date: None`; LLM-verify via primary source fetches (Wave 1 cache helps here); flip to verified or escalate to user-action queue. Particularly closes the **HC_BOUND_LIGO/SRG/PULSAR/CASSINI_C_SQ** parameters carried over from Phase 6e Wave 2 (paper40 submission blocker per Pipeline Invariant 8).

**Prerequisites:** Wave 1 substantially complete (primary-sources cache available for cross-reference).

**Module structure:** No new Lean / Python source. Updates to `src/core/provenance.py` (PARAMETER_PROVENANCE entries gain primary-source paths + `human_verified_date` flips).

**Bridges:**
- Closes Stage 14 `qi-parameterprovenance` (38 findings, 8 papers)
- Unblocks paper40 submission gate (Pipeline Invariant 8 / CHECK 15 strict mode)

**Deliverables:**
- All `human_verified_date: None` entries either flipped or queued with explicit action items
- `validate.py --check parameter_provenance --strict` passes for all submission-pending papers
- Provenance dashboard reflects new state
- Inventory update: registry counts unchanged; verification timestamps updated

**Estimated LOE:** 2–4 person-months

**Risk.** Low.

**Decision Gate I.2:** at Wave 2 close, all submission-pending papers' Pipeline Invariant 8 gate passes strict mode.

---

## Track C: Paper Hygiene Sweeps (6i.3, 6i.4, 6i.5)

### Wave 3 — Narrative Grounding & Cross-Paper Consistency [Pipeline: Stages 10, 12–14, per affected paper]

**Goal.** Re-ground all open NarrativeGrounding findings (30 findings, 10 papers) in primary sources (Wave 1 cache) or Lean theorems. Reconcile all open CrossPaperConsistency findings (34 findings, 10 papers) by walking the contradictions and updating the side that's stale.

**Prerequisites:** Wave 1 substantially complete.

**Most-affected papers:** paper6_vestigial, paper17_dark_sector, paper18_doublon_gate, paper20_scalar_rung, paper26_bh_entropy, paper32_strong_cp_de, paper35_qec_holography, paper37_chiral_ssb, paper38_cfl, paper7_chirality_formal.

**Bridges:**
- Closes Stage 14 `qi-narrativegrounding` + `qi-crosspaperconsistency`

**Deliverables:**
- Per-paper edits to remediate flagged narrative/cross-paper findings
- Mandatory Stage 13 re-invocation per touched paper; readiness gates flip back to passed

**Estimated LOE:** 3–5 person-months

**Risk.** Medium. Narrative grounding is judgement-heavy; ambiguous findings may persist as documented residuals rather than full closures.

### Wave 4 — Lean Proof Substance Audit [Pipeline: Stages 5, 12–14, per affected paper]

**Goal.** Verify each Lean theorem cited in every paper actually exists with the cited name and discharges the cited content (P6 cross-module bridge integrity sweep). The reviewer's protocol from Stage 13 done systematically across the project.

**Prerequisites:** Wave 1 substantially complete; helper script useful.

**Most-affected papers:** paper2_second_order, paper15_methodology, paper17_dark_sector, paper20_scalar_rung.

**Module structure:** Python helper `scripts/audit_paper_lean_refs.py` walks all `paper_draft.tex`, extracts every cited Lean theorem name (from `\texttt{}` blocks and prose), and confirms presence in `lean/SKEFTHawking/*.lean` via grep. Reports drift; author fixes.

**Bridges:**
- Closes Stage 14 `qi-leanproofsubstance` (26 findings, 5 papers)
- Codifies the existing `feedback_python_lean_refs_drift.md` memory pattern

**Deliverables:**
- `scripts/audit_paper_lean_refs.py` shipped; runs clean across all papers
- Per-paper edits to fix drift
- Mandatory Stage 13 re-invocation per touched paper

**Estimated LOE:** 3–5 person-months

**Risk.** Low. Mechanical auditing.

### Wave 5 — Assumption Disclosure: Derived vs Tracked-Prop [Pipeline: Stages 10, 12–14, per affected paper]

**Goal.** Apply paper41's "derived (witness shipped) vs tracked-hypothesis (consumer-side load-bearing)" distinction across all papers that use `H_*`-named Props. The round-1 paper41 reviewer's F7 finding generalizes — many papers loosely call derived theorems "tracked-Prop" which misleads readers.

**Prerequisites:** None beyond Wave 1 access for citation cross-reference.

**Most-affected papers (from QI register):** paper10_modular_generation, paper12_polariton, paper17_dark_sector, paper20_scalar_rung, paper22_ew_phase_transition, paper26_bh_entropy, paper27_bh_thermodynamics_four_laws, paper35_qec_holography, paper36_center_symmetry, paper39_heat_kernel_expansion, paper40_higher_curvature.

**Bridges:**
- Closes Stage 14 `qi-assumptiondisclosure` (31 findings, 12 papers)

**Deliverables:**
- Per-paper sweep of every `H_*` mention; classify as derived or tracked-hypothesis; update wording where mislabeled
- Lean module docstring updates where definitions are similarly mislabeled
- Mandatory Stage 13 re-invocation per touched paper

**Estimated LOE:** 2–4 person-months

**Risk.** Low. Wording-level edits.

---

## Track D: Closure & Process Wiring (6i.6)

### Wave 6 — Computation Correctness, Production Run Health, & Process Wiring Close [Pipeline: Stages 7, 12–14]

**Goal.** Three lower-volume QI items bundled with the final pipeline-doc + `validate.py` aggregation:
- Spot-check open ComputationCorrectness findings (5 findings, 2 papers); recompute and patch
- Audit "production run" claims for backing-data presence; ProductionRunHealth has small open count
- Aggregate all new `validate.py` checks added during Phase 6i (W1 citation cache, W4 paper-Lean-refs)
- Final pipeline doc updates: WAVE_EXECUTION_PIPELINE.md amendments accumulated through 6i merged into a clean final state
- Final QI register sweep: confirm all 8 items closed with explicit `evidence_on_close` entries

**Prerequisites:** Waves 1–5 substantially complete.

**Bridges:**
- Closes Stage 14 `qi-computationcorrectness` + `qi-productionrunhealth`
- Closes the Phase 6i programme

**Deliverables:**
- All open QI items in `docs/QI_REGISTER.md` flipped to closed with `evidence_on_close` field populated
- `validate.py --list` shows the new Phase-6i-added checks
- `WAVE_EXECUTION_PIPELINE.md` finalized with new conventions documented in Stage 1, Stage 10, Stage 13, and Pipeline Invariants sections
- Final Stage 14 register snapshot: 0 open items (or N << 8 with explicit deferral rationale per residual)
- Inventory update: closure block in Inventory_Index

**Estimated LOE:** 1–2 person-months

**Risk.** Low.

**Decision Gate I.6:** at Wave 6 close, Phase 6i is CLOSED. All 8 entry-state QI items closed (or explicitly deferred with documented rationale). Any new QI items surfaced during 6i runs become Wave 7+ in this same roadmap (open-ended structure).

---

## Decision Gates (summary)

**Gate I.0 — before Wave 1 begins:** User explicit authorization. Phase 6i opens with a project-wide convention change (CITATION_REGISTRY field additions); needs sign-off before mass edits.

**Gate I.1 — after Wave 1:** Citation cache rollout complete. `validate.py --check citation_primary_sources_present` becomes mandatory at every Stage 13.

**Gate I.2 — after Wave 2:** All submission-pending papers' Pipeline Invariant 8 gate passes strict mode. paper40 unblocked for submission.

**Gate I.6 — after Wave 6:** All 8 entry-state QI items closed; Phase 6i CLOSED.

---

## Dependencies

```
6i.1 (Citation cache)         — depends on user gate I.0
  ↓
  ↓ → 6i.2 (Parameter provenance) — independent of 6i.1, but uses cache for cross-ref
  ↓
  ↓ → 6i.3 (Narrative + cross-paper) — uses cache for re-grounding
  ↓
  ↓ → 6i.4 (Lean proof substance)   — independent
  ↓
  ↓ → 6i.5 (Assumption disclosure)  — independent
  ↓
6i.6 (Closure + process wiring) — depends on 6i.1–6i.5

Parallelism:
  6i.2, 6i.3, 6i.4, 6i.5 all run after 6i.1 and can overlap freely.
  6i.6 closes the programme.
```

---

## Timeline

| Wave | Scope | Lean PM | Python PM | Dependencies | Priority |
|------|-------|---------|-----------|--------------|----------|
| 6i.1 | Primary-sources cache rollout (~190+ bibkeys) + new validate.py check + scripts/citation_cache.py extension | 0 | 4–8 | User gate I.0 | **TIER 0 — central** |
| 6i.2 | Parameter provenance closure (HC_BOUND_* + others) | 0 | 2–4 | 6i.1 | **TIER 1** (paper40 submission gate) |
| 6i.3 | Narrative grounding + cross-paper consistency sweep (~10 papers) | 0 | 3–5 | 6i.1 | **TIER 1** |
| 6i.4 | Lean proof substance audit (~5 papers + scripts/audit_paper_lean_refs.py) | 0 | 3–5 | 6i.1 | **TIER 1** |
| 6i.5 | Assumption disclosure (derived vs tracked-Prop, ~12 papers) | 0 | 2–4 | None | **TIER 2** |
| 6i.6 | Computation/production health + closure + process wiring | 0 | 1–2 | 6i.1–6i.5 | **TIER 1** (closes phase) |

**Total Phase 6i LOE:** 15–28 person-months Python (no new Lean physics). Serial-with-parallel: 6i.1 first (~1–2 wks wall-clock); then 6i.2/3/4/5 in parallel (~2–3 wks); then 6i.6 (~3–5 days). Estimated wall-clock 4–6 weeks if pursued continuously, longer if interleaved with Phase 6e Wave 4+.

**Deliverables cumulative:**
- 0 new Lean modules
- 2 new Python helpers (`back_fill_primary_sources.py`, `audit_paper_lean_refs.py`)
- 2+ new `validate.py` checks
- 1 extended script (`scripts/citation_cache.py`)
- ~190+ files added under `Lit-Search/Phase-*/primary-sources/`
- Pipeline doc updates (WAVE_EXECUTION_PIPELINE.md Stages 1 + 10 + 13)
- All 8 entry-state QI items closed
- 0 new sorry (no new Lean), 0 new axioms

---

## Open Questions

**O.1** — git-lfs migration decision. If primary-sources cache exceeds ~1 GB total, switch to git-lfs. Decide before Wave 1 starts the bulk-fetch. Estimated likely size: 200–400 MB; threshold should not trigger.

**O.2** — provenance dashboard column. Should the localhost:8050 dashboard gain a `primary_source_path` column showing the cache state per parameter? Likely yes; small UI change in Wave 2.

**O.3** — Wave 3 narrative findings: who arbitrates when a "qualitative claim" is genuinely defensible without a Lean theorem? Default: User decides; agent flags candidates only.

**O.4** — Wave 5 retroactive H_*-Prop renames: do we rename Lean definitions whose name implies "tracked" but which are derived? Default: NO — Lean names are stable, paper text is updated to clarify. Memory `feedback_python_lean_refs_drift.md` reinforces stability of Lean names.

**O.5** — Append-only structure: when Stage 14 surfaces a new pattern during 6i execution, do we always open a new wave or sometimes amend an existing wave's scope? Default: always new wave; preserves trend log honesty per CLAUDE.md preemptive-strengthening discipline metric.

---

## What Success Looks Like

**Per wave:**
- 6i.1: every external bibitem in the project has a primary-source cache file; `validate.py --check citation_primary_sources_present` passes project-wide; hallucinated-citation failure mode structurally prevented at Stage 13
- 6i.2: every parameter has `human_verified_date != None`; paper40 submission gate clears
- 6i.3: narrative grounding + cross-paper consistency findings either fixed or documented as residual; Stage 13 re-invocations clean
- 6i.4: every cited Lean theorem in every paper resolves; `audit_paper_lean_refs.py` runs clean
- 6i.5: every `H_*`-Prop reference correctly classified as derived or tracked-hypothesis in paper text
- 6i.6: 0 open QI items (or N << 8 with explicit deferral rationale)

**Cumulative:**
- Pipeline hardened against the 8 systemic failure classes Stage 14 surfaced
- Citation hallucination structurally prevented
- All paper-submission gates clear (Pipeline Invariant 8 strict)
- 4 new validate.py checks codifying the hygiene
- **Program-level value:** the project's own internal pipeline now catches what Stage 13 catches, raising the floor on what makes it past Stage 12. Future waves spend less time in Stage 13 remediation.

---

## Cross-References

**Source documents:**
- `docs/QI_REGISTER.md` (auto-regenerated 2026-04-28; entry-state input to this roadmap)
- `~/.claude/projects/.../memory/feedback_primary_sources_cache.md` (PoC pattern from Phase 6e Wave 3 closure)
- `~/.claude/projects/.../memory/feedback_hallucinated_citation_paper40.md` (incident root cause)
- `~/.claude/projects/.../memory/feedback_python_lean_refs_drift.md` (Wave 4 audit precedent)
- `~/.claude/projects/.../memory/feedback_post_wave_strengthening_audit.md` (Wave 5 audit precedent)
- `papers/AutomatedReviews/2026-04-28-0727-internal-adversarial/paper41_diff_invariance.md` (round-1 reviewer findings; F3 motivates the `inprep` discriminator)
- `papers/AutomatedReviews/2026-04-28-0750-internal-adversarial-reinvocation/paper41_diff_invariance.md` (re-invocation; suggests `inprep` field)

**Phases this hardens (all):**
- Phase 5d–5z, Phase 6a–6f bibliographies — every paper benefits from Wave 1 + Wave 4 + Wave 5
- Phase 6e specifically: paper40 submission gate via Wave 2

**Append-only follow-ups (anticipated future waves):**
- 6i.7+ — TBD if Stage 14 surfaces new patterns during 6i execution. Not pre-scoped.

---

*Phase 6i roadmap. Prepared 2026-04-28 from `docs/QI_REGISTER.md` Stage 14 advisory output + Phase 6e Wave 3 PoC. Six waves, hygiene programme, hardens pipeline against citation hallucination + 7 other QI patterns. Append-only structure: new waves added if new patterns surface. Total PM: 15–28 Python (no new Lean). Wall-clock 4–6 weeks if continuous. All waves follow [Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md). User authorization required before Wave 1 only.*
