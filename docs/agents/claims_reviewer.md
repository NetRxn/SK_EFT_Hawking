# claims-reviewer Agent — Reference + Change Log

**Agent file:** `.claude/plugins/physics-qa/agents/claims-reviewer.md` (repo root)
**Companion docs:**
- Design spec: `SK_EFT_Hawking/temporary/working-docs/claims_reviewer_v2_design.md`
- KG schema delta: `SK_EFT_Hawking/temporary/working-docs/sentence_kg_schema_delta.md`
- Roadmap: `SK_EFT_Hawking/docs/roadmaps/Phase5v_Roadmap.md` Wave 10
- Sibling agents: `figure-reviewer.md`, `adversarial-reviewer.md` (same plugin)

**Role in the pipeline.** claims-reviewer is the Stage-10 internal content-accuracy checker (before Stage 11 notebooks, Stage 12 doc-sync, Stage 13 adversarial). It is NOT a fresh-context external reviewer (that's `adversarial-reviewer`); it IS the structural prose-versus-pipeline checker. Its output (`claims_review.json` per paper) drives the Paper Provenance dashboard tab and feeds the `ReviewFinding` graph extractor.

---

## 1. Version history

| Version | Date | Scope | Status |
|---|---|---|---|
| v1 | original (pre-2026-04) | ~30–60 curated high-priority claims per paper, grouped into 7 typed sections | Superseded by v2 as of 2026-04-26 |
| v2 | 2026-04-26 | Sentence-level full-paper walk with five finding classes, decoupled verdicts, reconciliation protocol, content-hash IDs | **Current** |

---

## 2. v1 scope + limitations (why v2 exists)

### What v1 did

`claims-reviewer` v1 walked a paper looking for ~30–60 "important" claims and grouped them into seven typed sections in a per-paper `claims_review.json`:

1. `numerical_claims[]` — numeric values to recompute against `formulas.py`
2. `theorem_refs[]` — Lean theorem names to check against source files
3. `parameter_provenance[]` — parameter llm_verified/human_verified status
4. `citation_integrity[]` — `\bibitem` / `\cite` presence in `CITATION_REGISTRY`
5. `qualitative_claims[]` — feasibility / detectability / reach statements
6. `axiom_risk[]` — project axioms the paper's claims depend on
7. `hypothesis_risk[]` — HYPOTHESIS_REGISTRY + structure-field constraints

Each claim got PASS/WARN/FAIL + free-text `notes`. Output: `papers/<paper>/claims_review.json`.

### Limitations that drove v2

A 2026-04-24 rigor audit on three random papers (5, 10, 16) surfaced three systemic problems:

**(L1) Coverage partial-by-design.** v1 picked "important" claims; ~80% of paper prose went silently unreviewed. Paper 5's audit found 8 internal contradictions, several of which weren't in any structured artifact. Paper 16 (zero prior claims_review) had 30% of prose `UNGROUNDED` — previously invisible because no agents had run.

**(L2) Findings go stale without a watchdog.** Paper 10's `claims_review.json` (April 3) had entries like "ModularInvarianceConstraint has 4 sorry" — true then, but the module is now zero-sorry. Dashboard kept surfacing the finding as an open issue indefinitely. v1 had no reconciliation mechanism. 8 of 23 prior adversarial findings on Paper 10 were STALE by 2026-04-24.

**(L3) Three (now five) finding classes systematically missed by v1 AND adversarial-reviewer alike:**
- Internal arithmetic drift (Class IA — e.g., Paper 5: abstract "20 thms zero sorry" vs body "20 thms 1 sorry")
- Toolchain pin drift (Class TP — e.g., Papers 5/10: "Lean v4.28.0" vs project v4.29.0)
- Stealth pipeline-vs-prose drift (Class SD — Paper 5: "five obstacles" vs `formulas.py::structural_obstacles` returning 4)
- Theorem-name reference drift (Class TN — **added 2026-04-26 from paper20 Stage-13 QI candidate**)
- Hypothesis disclosure gap (Class HD — **added 2026-04-26 from qi-assumptiondisclosure cluster**)

---

## 3. v2 design decisions + reasoning

Five major design calls, each with an explicit rationale anchored in the feedback round (2026-04-26):

### 3.1 Sentence-level walk, not claim-selection

**Decision.** Walk every sentence top-to-bottom; emit one record per sentence regardless of whether it's a "claim."

**Reasoning.**
- v1's claim-selection is a forcing function for under-coverage (L1). Sentence-level walk makes silent gaps structurally visible as `UNGROUNDED` counts.
- Full coverage also enables cross-sentence contradiction detection (Class IA needs both `X thms 0 sorry` and `X thms 1 sorry` to fire).
- Implementation cost is bounded — typical paper has ~250 sentences; sub-unit splitting is lazy (only when verdicts diverge).

**Not chosen.** Selective re-walk: couldn't address L1 without losing the coverage-visibility signal.

### 3.2 Decoupled agent verdict from human review state

**Decision.** Agent verdict is purely about chain resolution + recomputation agreement. Never influenced by `human_verified_date` or `human_state`.

**Reasoning (user feedback 2026-04-26).**
- v1's verdict vocabulary was muddled: "WARN if parameter not human-verified" meant virtually every freshly-run agent report emitted WARN for every parameter (human verification takes weeks+). This buried real WARN signals.
- Agent and human ratification are orthogonal axes. The agent answers "does the chain resolve?"; the human answers "do I accept this?" Conflating them hides both.
- Per-link `link_state` flag (`llm_verified_only`, `human_verified`, `stale`) is derived at graph-build time from the link target's metadata — not set by the agent. Dashboard uses it for coloring + freshness change-bus.

**Not chosen.** Keep v1's human-verification-aware WARN: would perpetuate the buried-signal problem.

### 3.3 Reconciliation protocol, not silent supersession

**Decision.** Prior findings that don't reproduce in a new run go to `non_reproducing_prior_findings[]`. LLM-judgment findings become `candidate_for_supersession` (human ratifies via dashboard). Deterministic structural rechecks (sorry count grep, dict lookup, file read) auto-close with `status: superseded, auto_closed: true`.

**Reasoning (user feedback 2026-04-26).**
- Original v2 draft proposed: "every prior finding that doesn't reproduce gets `status: superseded` appended."
- User correctly identified this as dangerous. LLM runs aren't deterministic; a second run may miss what the first caught. One sentence can map to multiple findings; agent traversal order may shift the anchor. Asymmetry of risk: silently closing a true issue is much worse than a stale finding remaining visible.
- Two-tier protocol separates safe auto-close (a deterministic recheck produced a different value, trivially reproducible) from unsafe auto-close (LLM judgment, non-reproducible). Mechanical staleness clears automatically; narrative judgments require human confirm.

**Eligible for auto-close.** Sorry count per module, module count, theorem count, axiom count, Class TN registry lookup, Class TP file read, citation-in-registry dict lookup, bibkey arXiv cache lookup.

**Never eligible.** Narrative overclaim judgments, figure / caption qualitative assessment, cross-paper semantic match, interpretive-vs-verifiable boundary calls.

### 3.4 Content-hash sentence IDs

**Decision.** `sentence:<paper>:<section_slug>:<sha8(normalized_quote)>`. Normalization: lowercase, whitespace-collapse, strip TeX markup (keep args for `\texttt`/`\emph`/etc., drop args for `\cite`/`\label`), unicode-normalize quotes and dashes, strip trailing bibliographic brackets.

**Reasoning (user feedback 2026-04-26).**
- Original v2 draft used `paper:section:ordinal`. User flagged: "what about situations where one sentence maps to many things? [...] how does the metadata around each sentence remain updated [under edits]?"
- Ordinal-based IDs shift every downstream sentence's ID when a sentence inserts or deletes at the top of a section — all prior verification records orphaned. Catastrophic for a verification-backlog workflow.
- Content-hash survives: section reorder (section_slug is title-derived, not position-derived); sentence insert/delete (other sentences' hashes unchanged); benign edits (punctuation, citation insertion, whitespace adjustment, TeX-markup refactor — all normalize to same hash).
- Substantive edits = new ID + old ID tombstoned. Near-match Levenshtein heuristic over normalized quotes surfaces "is this a rewrite of `<old_id>`?" prompt for one-click verification rollover.

**Not chosen.** Ordinal IDs (shift bug); raw-quote IDs (benign edits break stability).

### 3.5 `scripts/sentence_state.py` CLI as the only writer

**Decision.** Human ratification, supersession, audit-log writes ALL go through `scripts/sentence_state.py` CLI subcommands. LLMs, dashboard backend, and ad-hoc scripts all call the CLI. No free-form JSON edits.

**Reasoning (user feedback 2026-04-26).**
- User flagged: "LLMs won't read the full JSON File and are likely to edit in unsafe ways without full context. Either type of write should happen deterministically with either a customized tool, crud, or script."
- JSON direct-edit is unsafe: LLMs can corrupt schema, omit required fields, lose prior state. The CLI enforces schema validation + atomic writes + audit logging.
- Matches Wave 9f architecture (PG+AGE read-only mirror; JSON canonical at rest). The CLI is the single mutation chokepoint.
- Subcommands: `mark`, `ingest_agent_run`, `reconcile`, `supersede`, `tombstone-sweep`, `validate`, `normalize-quote`.

**Not chosen.** Let agents write JSON directly (unsafe). Move prose_state to PG as source-of-truth (conflicts with Wave 9f's JSON-canonical architecture).

---

## 4. Finding class catalog

| Class | Detects | Data sources | Gate | Origin |
|---|---|---|---|---|
| **IA** (Internal Arithmetic drift) | Numbers differing between two places in paper; pipeline counts differing from live pipeline | paper TeX + `lake build`/`pytest`/`grep` output + `formulas.py`/`constants.py` cardinality | Gate 9 NumericalFreshness | Rigor audit 2026-04-24, Paper 5 (8 contradictions) |
| **TP** (Toolchain Pin drift) | Literal Lean/Mathlib version in paper ≠ project pin | `lean-toolchain`, `lakefile.toml` | Gate 9 | Rigor audit 2026-04-24, Papers 5/10 |
| **SD** (Stealth pipeline-vs-prose Drift) | Prose adjective/numeral describing codified cardinality ≠ actual | `formulas.py` / `constants.py` integer-returns + fixed-list `len(...)` | Gate 9 + relevant downstream gate | Rigor audit 2026-04-24, Paper 5 "five obstacles" |
| **TN** (Theorem-Name reference drift) | `\texttt{<Module>.<name>}` in paper ≠ live Lean registry | `lean_deps.json` (no `EXTRACT_NAME_DEPS` needed) | Gate 5 LeanProofSubstance + Gate 9 | Paper20 Stage-13 QI candidate 2026-04-25 (ScalarRungInterpretation rename) |
| **HD** (Hypothesis Disclosure gap) | Paper cites theorem T as "verified" but T's tracked hypothesis is undisclosed in paper prose | `HYPOTHESIS_REGISTRY.dependent_theorems[]` (Wave 1c) + paper TeX grep | Gate 6 AssumptionDisclosure | qi-assumptiondisclosure cluster 2026-04-26 (4 papers) |

All five classes are **structural checks**, not LLM judgments. A `validate.py --check paper_lean_refs` + `--check paper_hypothesis_disclosure` (Wave 10g) mirrors Classes TN and HD at zero-agent-cost for per-save CI-like invocation.

---

## 5. Schema diff v1 → v2

### Top-level structure

| Element | v1 | v2 |
|---|---|---|
| Root keys | paper, review_date, overall_status, 7 typed sections, summary, blocking_issues | paper, review_date, **reviewer_version, reviewer_model, reviewer_run_id**, **sentences[]** (primary), **non_reproducing_prior_findings[]**, summary, blocking_issues, non_blocking_followups |
| Typed sections | `numerical_claims[]` + 6 others (first-class) | **Dropped.** `sentences[]` is the only primary store. No derived-typed-section views (hard cutover; no backward compat). |
| Claim count per paper | ~30–60 curated | ~250 per paper (full prose walk) |
| Stability across edits | Location-keyed (line numbers); fragile | Content-hash IDs; stable under benign edits + section reorder |

### Per-claim → per-sentence record

| Field | v1 per-claim | v2 per-sentence |
|---|---|---|
| id | (implicit — section + field offset) | **`sentence:<paper>:<section_slug>:<sha8>`** — content-hash, stable |
| type | (one of 7 typed sections) | `numeric \| theorem-ref \| citation \| parameter \| formal-claim \| qualitative \| methodology \| transition \| metaclaim` |
| verdict | PASS/WARN/FAIL | **`PASS \| FAIL \| WARN \| INFO \| UNGROUNDED \| TRANSITION`** (decoupled from human state) |
| chain | implicit (typed section indicates chain kind) | `chain_proposed: { links[], completeness }` — explicit per-link kind + target |
| per-link state | (none) | `link_state: resolved \| llm_verified_only \| human_verified \| stale \| missing_target` — DERIVED at build, not agent-set |
| finding_classes | (none) | `finding_classes: [IA \| TP \| SD \| TN \| HD]` subset |
| rewrite_of | (none) | `rewrite_of: <prior_sentence_id> \| null` — Levenshtein near-match for tombstoned rewrites |
| tombstone | (none) | `tombstone: bool` — true iff sentence_id was in prior run but not current |
| agent_run_id | (none) | Every sentence carries `agent_run_id` for audit-log correlation |

### Human ratification (out of band from agent)

v2 cleanly separates what the agent owns from what the dashboard/CLI own:

- **Agent owns:** `claims_review.json` — sentences, verdicts, chains, finding classes, non-reproducing prior findings.
- **Dashboard + CLI own:** `prose_state.json` — per-sentence human_state, human_notes, human_ratified_at. `audit_log.jsonl` — append-only event stream.
- **Never in v2:** per-link human ratification (dropped; sentence-level is the axis, per-link verify is UX affordance over derived `link_state`). `human_verified_ungrounded` (dropped; no semantics distinct from INTERPRETIVE).

---

## 6. Migration + rollout

### 6.1 Feature flag (during migration)

`CLAIMS_REVIEWER_V2=1` (default from Wave 10a ship date) — agent emits v2 schema. `=0` — emits v1 for rollback.

### 6.2 Hard cutover (no backward compat)

No derived-typed-section views. Downstream consumers (`_pp_build_data` in `provenance_dashboard.py`, graph extractor `extract_review_finding_nodes`) rewritten against v2 schema in Wave 10b + 10d. No long-term burden of emitting both schemas.

Rationale: user explicitly accepted re-working every paper from scratch (no external downstream consumers require compatibility). Hard cutover simpler than maintaining dual-path.

### 6.3 Retrofit (Wave 10h)

After Wave 10a + 10b land + Wave 10d UI ships, run claims-reviewer v2 on all 18 extant papers in a batch (~2h wallclock + agent budget). Initial state: every sentence `agent_proposed`. Coverage ribbon reads ~0% human-verified across all papers — the verification backlog.

Bulk-verify-unchanged UX (Wave 10d) + ClaimCluster cross-paper propagation (Wave 10f) are the critical UX for clearing the backlog.

### 6.4 Steady state

Per dev cycle:
- Edit a paper → run claims-reviewer → sentences with unchanged content keep their IDs + verification states.
- Substantive prose edits → new IDs + tombstones → `rewrite_of` heuristic prompts one-click rollover.
- Lean / formula / parameter change → dependent sentences auto-flip to `needs_recheck` via Wave 10c change-bus.
- Only `needs_recheck` sentences require human re-action.

---

## 7. Smoke test protocol

After Wave 10a + 10b land, before Wave 10h retrofit:

1. **Run** claims-reviewer v2 on paper 12 (reference paper — fullest QA coverage already):
   ```
   Use the claims-reviewer agent to review paper 12 polariton.
   ```

2. **Validate schema**:
   ```bash
   python3 -c "import json; json.load(open('SK_EFT_Hawking/papers/paper12_polariton/claims_review.json'))"
   ```
   (Future: `scripts/sentence_state.py validate ...` once Wave 10b CLI lands.)

3. **Diff against v1 output**:
   - Pull v1 `claims_review.json` from git history (pre-v2-landing).
   - Compare: every v1 typed-section entry should be represented in v2 `sentences[]` (semantically). v2 will have more entries (full walk), fewer missing (L1 coverage fix).

4. **Finding class calibration**:
   - Paper 12 should produce Class TP and Class TN findings if they exist (check for Lean version mentions + theorem-name refs).
   - Paper 5 should produce Class IA findings (the known 8 contradictions).
   - Paper 10 should produce multiple Class TP findings (Lean v4.28 vs v4.29) + Class IA (stale counts).
   - Paper 20 should produce Class TN findings for the renamed ScalarRungInterpretation theorems.
   - Papers with tracked-hypothesis theorems (paper8, paper17, papers using FermiHubbardDimer Z16 hidden sector) should produce Class HD findings.

5. **Reconciliation smoke test**:
   - Run claims-reviewer v2 on paper 10 twice in a row.
   - First run: populates `claims_review.json`.
   - Second run: should produce `non_reproducing_prior_findings[]` with `auto_closed: true` for mechanical re-checks (sorry counts, module counts) and `candidate_for_supersession` for narrative judgments.

---

## 8. Integration with other agents

| Agent | Relationship |
|---|---|
| `figure-reviewer` | Unchanged. Emits `figure_review_report.json` per paper — orthogonal concern (figure rendering quality). No schema interaction. |
| `adversarial-reviewer` | Unchanged in scope; Wave 10e extends its output to cite `sentence_id` from current `claims_review.json` when a finding targets a specific sentence. Enables Paper Provenance inspector to overlay adversarial findings onto the relevant sentence. |
| `claims-reviewer-cross-paper` | **New in Wave 10f.** Consumes all `claims_review.json` files post-retrofit; emits `ClaimCluster` nodes + `MEMBER_OF` edges for cross-paper claim equivalence. Does not write `claims_review.json` itself. |

---

## 9. Known limitations + Phase-6 considerations

- **Class HD v1 uses HYPOTHESIS_REGISTRY's `dependent_theorems[]` only** (direct ASSUMES edges). Transitive proof-dep walks (catching hypotheses depended on through proof chains) require `EXTRACT_NAME_DEPS=1` extraction (+3-5min Lean cost). Deferred to a follow-up once Wave 9c-followup-cache ships the sidecar file that makes opt-in proof-dep extraction cheap to toggle.
- **Class SD scope is bounded** to integer-returning functions with `count`/`total`/`n_` prefix + fixed-list `len(...)`. More complex cardinality drift (e.g., "the 23 transport coefficients" where the count depends on a runtime computation) requires opt-in registration in `STEALTH_DRIFT_REGISTRY` (not yet populated).
- **Sentence boundary detection is heuristic.** Edge cases in physics papers (equations mid-sentence, displayed `\begin{equation}...\end{equation}` blocks, abbreviations like `e.g.` / `Eq.` / `Fig.`) will occasionally split incorrectly. Manual review on smoke-test paper flags these; can be refined iteratively.
- **No footnote walk** in v1. Physics papers use footnotes sparingly; extension trivial when needed.
- **No bibliography walk** in v1. Bibkey integrity is checked via `\cite{...}` references in body prose; unused bibitems aren't flagged (separate concern).

---

## 10. Change log

### 2026-04-26 — v2 smoke-test follow-ups (10 prompt tightenings)

After 2026-04-26 release, ran v2 prompt against `paper12_polariton` as smoke test (background agent, sentence-walker mode, full pipeline). Output validated clean; 56 sentences emitted (4 finding-class hits: 3 IA + 1 SD, 0 TP/TN/HD); reconciliation correctly auto-closed 4 prior findings + flagged 8 candidates for human supersession; non-blocking. Prompt produced coherent output overall.

10 anomalies surfaced and addressed:

| # | Issue | Fix |
|---|-------|-----|
| 1 | `\textit{et al.}` boundary handled correctly | (no fix needed; documenting as confirmed-OK) |
| 2 | Multi-claim itemized lists — splitting policy underspecified | Prompt §A.1 expanded with split-eagerly/split-lazily case list |
| 3 | Long table captions mixing distinct claims — sub-unit splitting underused | Prompt §A.1 split-eagerly list now explicitly includes table captions |
| 4 | `quote_normalized` step-6 trailing-bracket regex only caught `[0-9, ]+` | `sentence_state.py::_TRAILING_BRACKETS` widened to author-year `[Author 2024]` |
| 5 | Schema validator only checked top-level required + sentences-is-list; per-sentence schema loose | `sentence_state.py validate` now enforces required fields, id shape, line ordering, type/verdict/finding_class/link_kind/completeness enums, tombstone bool, AND flags unknown fields as likely typos |
| 6 | `reviewer_model` canonical format unspecified | Validator now requires hyphenated lowercase (`claude-opus-4-7-1m` form); prompt clarifies |
| 7 | `link_state` placement unclear (chain proposal vs derived metadata) | Prompt §F clarifies: agent-side hint, graph extractor re-derives at build time |
| 8 | `tex_line_start` precision unclear | Prompt §F: start = first line, end = last line; equation environments span their full range |
| 9 | Pre-`\maketitle` blocks unspecified | Prompt §A.1 explicitly excludes `\title`/`\author`/`\date`/`\affiliation`; start at first content past `\maketitle` |
| 10 | Bibliography-orphan handling correct but unobvious | (no fix needed — confirmed structural validate.py concern, addresses by Wave 1d's `paper_lean_refs` + `citation_live_resolution`) |

**Sentence-count observation:** paper12 produced 56 sentences vs the design-doc estimate ~250. Likely explanations: paper12 is shorter than average (5 pages); aggressive boundary detection around equations + tables collapsing potentially-distinct items; lazy sub-unit splitting keeping multi-claim sentences as single records. Will calibrate against paper16 (worst-coverage paper, 30% UNGROUNDED in v1 audit) at retrofit time.

**Validator backward-compat:** the smoke-test output validates clean against the strengthened schema — no false-negative changes from the strictening pass. Stricter rules align with what the agent already does naturally.

### 2026-04-26 — v2 release

- **Author:** Claude Opus 4.7 session, user: @johnroehm.
- **Context:** Phase 5v Wave 10a. Follows 2026-04-24 v2 design doc + 2026-04-26 feedback-round revisions.
- **Agent prompt file:** rewritten end-to-end. New length ~450 lines (was ~215).
- **Net schema change:** v1 7-typed-section output → v2 sentence-keyed output with 5 finding classes, decoupled verdicts, reconciliation, content-hash IDs, tombstone state, per-sentence `finding_classes[]`.
- **Behavior change for existing reviews:** all pre-2026-04-26 `claims_review.json` files are v1 schema. On next claims-reviewer invocation against any paper, v2 runs and:
  - Emits new sentence-keyed output (overwrites the v1 file).
  - Loads v1 findings from the old file (via the reconciliation protocol — both `blocking_issues` and typed-section entries).
  - For each v1 finding, attempts to match against current run. Deterministic re-checks auto-close; LLM-judgment findings become `candidate_for_supersession`.
- **Downstream blockers.**
  - `_pp_build_data` in `provenance_dashboard.py` assumes v1 schema keys (`numerical_claims[]`, etc.). MUST be rewritten against `sentences[]` before any v2 agent run targets a paper whose dossier is live-viewed. This is Wave 10b/10d work.
  - `extract_review_finding_nodes` in `build_graph.py` currently consumes v1 via `blocking_issues[]`. Partial compat: `blocking_issues[]` stays in v2; `non_blocking_followups[]` is new. Wave 10b updates extractor to consume sentence-level findings + `finding_classes`.
- **Sentinel:** `reviewer_version: "claims-reviewer-v2"` in every v2 output file; downstream consumers can check this field and fall back if needed during migration.

### Prior versions

v1 was originally authored (date undocumented in file; probably Phase 5u vintage around late March 2026). Captured 7 typed sections: numerical/theorem-refs/parameter_provenance/citation_integrity/qualitative/axiom_risk/hypothesis_risk.

---

## 11. References

- v2 agent file: `.claude/plugins/physics-qa/agents/claims-reviewer.md`
- v2 design spec (full detail): `SK_EFT_Hawking/temporary/working-docs/claims_reviewer_v2_design.md`
- KG schema delta: `SK_EFT_Hawking/temporary/working-docs/sentence_kg_schema_delta.md`
- Roadmap Wave 10: `SK_EFT_Hawking/docs/roadmaps/Phase5v_Roadmap.md`
- Paper20 QI candidate (Class TN seed): `SK_EFT_Hawking/papers/AutomatedReviews/2026-04-25-0135-internal-adversarial/paper20_scalar_rung.md` §QI Candidate
- qi-assumptiondisclosure cluster (Class HD seed): `SK_EFT_Hawking/docs/QI_REGISTER.md`
- Rigor audit data (v2 justification): `/tmp/paper{5,10,16}_rigor_audit.md`
- Sibling plugin agents: `.claude/plugins/physics-qa/agents/{figure-reviewer.md, adversarial-reviewer.md}`
- Wave 9f PG architecture: `SK_EFT_Hawking/scripts/sync_graph_to_pg.py` + roadmap Wave 9f
