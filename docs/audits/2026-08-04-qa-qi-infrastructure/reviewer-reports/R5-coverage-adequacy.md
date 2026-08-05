<!-- Recovered verbatim 2026-08-05 from the subagent transcript
     agent-a21ed46ccf1d78255.jsonl. This is the reviewer's own final report,
     unedited. See ../FINDINGS_REGISTER.md for the consolidated list. -->

I have enough evidence. Writing up.

## What IS well covered

**Lean substrate integrity is the strongest layer in the system.** ADR-004's R1–R5 all have named, live, hard-failing checks: `formula_grounding` (`lean_statements.py:287`, ~390 refs, hard-fails on placeholder-grounded), `proxy_body_audit` (`lean_substrate.py:354`), `tracked_hypothesis_ledger` (`lean_substrate.py:468`), `placeholder_not_cited` (`lean_substrate.py:151`), `native_decide_regression` (`lean_toolchain.py:87`, ratcheted at `NATIVE_DECIDE_DECL_CLOSURE_CEILING = 546`, `constants.py:2415`). `axiom_closure_allowlist` (`lean_toolchain.py:424`) closes the compiler-trust surface. `vacuous_statement_audit` and `nogo_substrate_integrity` cover the tautology and negative-frontier classes. This is genuinely more than most formalization projects have.

**Zero-sorry is the one invariant with a real automatic gate.** `.git/hooks/pre-commit` → `scripts/pre-commit-sync.sh:68-71` parses the actual `lake build` log for `declaration uses 'sorry'` and hard-blocks on `main`. Correctly built to avoid source-grep false positives.

**Meta-QA (ADR-009 D5) is excellent and unusual.** `tests/test_d5_mutation_obligation.py` requires every registered check to declare `MUTATION_VERIFIED` or `AWAITING_MUTATION_TEST`, with the backlog ceiling at 0 — a new check without a both-directions test fails on arrival. The ADR is also honest about its own retraction (`ADR-009:881`). Very few QA systems test whether their tests can fail.

**Review-recordedness is not fakeable.** `BUNDLE_READINESS_HEATMAP.md` distinguishes 🟡 YELLOW (unreviewed) from 🟢 GREEN — "no findings recorded ≠ reviewed and passed" — and `bundle_source_freshness` flags a bundle whose sources moved after its last lift. `review_docs_mint_findings` prevents a review document that finds nothing from counting.

**Citation cache existence, count freshness, table freshness** are structurally prevented rather than checked: `render_paper_tables.py` + `tables_fresh` + `counts.tex` macros mean tabular and count claims cannot drift.

## COVERAGE GAPS

### Critical gaps (a wrong artifact can ship)

**C1. Nothing runs the 59 checks automatically. There is no CI.**
- Obligation: Stages 1–13 each have a gate; Invariant #16 (AI-defect layer) requires Tier 1+2 green before Tier 3.
- What catches it today: `.git/hooks/pre-commit` runs exactly **3** of 59 checks (`pre-commit-sync.sh:96` — `formula_grounding`, `placeholder_not_cited`, `native_decide_regression`), **fail-open** by design (`:36`, `:100`), **hard-blocks only on `main`** (`:59`, `:70`, `:99`), and is skipped entirely in worktrees (`:23-26`). No `.github/workflows`, no Makefile, no CI of any kind. The hook itself is installed by a script in the *private* repo, so a fresh clone has zero enforcement.
- Likelihood: certain — it is the current state. Blast radius: total. Every other gap below is downstream of this one: the system is a *library* of checks, not a gate.
- Cheapest fix: a GitHub Actions workflow running `uv run python scripts/validate.py --no-archive && uv run python -m pytest tests/ -m ''` on push. One file.

**C2. Figure content correctness is unverified for ~130 of 137 figures — and Stage 9 has no gate at all.**
- Obligation: Stage 9 gate — "All figures PASS LLM review. No FAIL, no MINOR remaining."
- What catches it today: **nothing mechanical.** `FigureSpec.physics_checks` (`review_figures.py:61`) has **no runner anywhere in the repo** — it is only serialized into the manifest (`:2818`) for the LLM. And **118 of 137 specs have `physics_checks=[]`**, so for those the LLM gets no assertions either. `bundle_figure_integrity` (the legibility + source-drift check) is scoped to `d11_`/`d12_` prefixes only (`bundles_readiness.py:117`) — 7 figures; D5(7), D8(3), D9(4), I1(6), I2(5), E1(2), E2(4), L1–L3 and ~48 legacy paper dirs are unguarded. No validate check consumes `figures/figure_review_report.json` (only `provenance_dashboard.py:2493` displays it); the global report is dated **2026-04-27**, covers **1 figure**, and reads `"overall_status": "issues_found"`.
- Likelihood: high. Blast radius: high — a figure that plots the wrong quantity under a confident caption is exactly the arXiv-moderation failure mode, and the project already documented this end-to-end (`freshness.py:412-419`: a reviewer demonstrated a notebook plotting `ε = 1 + 3f` instead of Maxwell–Garnett under a "(certified)" annotation).
- Cheapest fix: (a) generalize `bundle_figure_integrity` to iterate `FIGURE_REGISTRY` unfiltered (delete the `d11_/d12_` filter — ~3 lines); (b) implement a `physics_checks` runner and ratchet the empty-list count downward.

**C3. No mechanism recomputes a paper-quoted number against the formula that produces it.**
- Obligation: Invariant #6 / Stage 10 FAIL criterion (">0.5% disagreement"). QI item `qi-numericalverification` proposed `validate.py --check threshold_arithmetic` on 2026-05-04.
- What catches it today: **nothing.** `threshold_arithmetic` returns **0 files** repo-wide. `paper_provenance` is on the known-inert list. `numerical_literals` is a ratchet, and it is *at* its ceiling: **116 inline unit-bearing literals across the corpus, ceiling 116** (`constants.py:2444`) — 116 grandfathered untraced numbers, against only 15 `\input{tables/}` references in 64 drafts.
- Likelihood: high, with a worked precedent. `QI_REGISTER.md:96` records a paper claiming `G > 0.01` where the correct value was `0.5` (factor 50), with a companion photon count wrong by 25× — the drift propagated across 4 sites and survived a full per-paper Stage-13 review. Target date was 2026-05-04; today is 2026-08-04, owner "unassigned". Blast radius: high — this is the defect class that damages a journal submission.
- Cheapest fix: ship `threshold_arithmetic` as specified in `AI-DEFECT-DEFENSE-LAYER.md:82`. Estimated 4–6 hr there.

**C4. Nothing checks that a cited theorem's *statement* supports the claim the prose makes about it.**
- Obligation: Stage 10 FAIL — "'formally verified' claim but theorem not in Lean"; Invariant #9's spirit.
- What catches it today: name resolution only. `prose_theorem_reference_coverage` (`prose_lean_refs.py:391`) resolves `\texttt{Module.symbol}` against `lean_deps.json`. The planned semantic check `theorem_quoted_bound_matches_lean_literal` returns **0 files** repo-wide; both QI items it was to close (`qi-leantheoremname`, `qi-prose_lean_numerical_bound_gap`) are **still open**, targeted "before D3 Stage 10", 3 months ago.
- Likelihood: high — this is precisely the LLM failure mode of proving something *adjacent* to the claim. Documented instance at `QI_REGISTER.md:108`: prose said "formally bounded at ≤1.8%"; the Lean theorem is a generic algebraic envelope and the 1.8% lives in a **docstring**. Blast radius: severe — it converts a formal-verification claim into an unsupported one, which is the project's headline differentiator.
- Cheapest fix: ship `theorem_quoted_bound_matches_lean_literal` (`AI-DEFECT-DEFENSE-LAYER.md:84`); it also lets claims-reviewer Class TN sunset.

**C5. Citation *content* verification is a single inert check; the two planned replacements never shipped.**
- Obligation: Invariant #11 + Stage 13 "citation findings are BLOCKER, no exceptions."
- What catches it today: `citation_primary_sources_present` (`citations.py:269`) verifies a cache **file exists** on disk — existence, not correspondence. The one check that compares content, `bibitem_title_primary_source`, is on the known-inert list. `bibitem_registry_character_match` and `citation_bibkey_form_matches_metadata` return **0 files** repo-wide; `qi-bibitem_registry_drift` and `qi-citation_authoryear_metadata_match` are both **open**, the former recording **4 instances in one bundle** where bibitem text and registry entry described *different real papers*.
- Likelihood: high — fabricated/mis-targeted citations are the single most-documented LLM authoring defect, and the project already had the paper40 incident (a hallucinated arXiv ID pointing at a graph-NN paper). Blast radius: severe; this is a one-strike arXiv trigger.
- Cheapest fix: `citation_bibkey_form_matches_metadata` first (parse `<LastName><Year>` from the bibkey, assert against `authors`/`year`) — the spec estimates 1–2 hr and it catches the two named real cases (`KaulMajumdar1998`, `SextyWetterich2009`).

### Important gaps

**I1. Pipeline Invariant #10 has no enforcement and 22 live violations.**
`set_option maxHeartbeats N in` immediately precedes `theorem`/`private theorem` declarations at 22 sites across `QuantumGroupAntipode.lean` (2), `QuantumGroupCoproduct.lean` (2), `Uqsl3Hopf.lean` (8), `Uqsl2AffineHopf.lean` (10) — e.g. `QuantumGroupAntipode.lean:353-355`, `Uqsl2AffineHopf.lean:3291-3292`. `elaboration_knob_watchlist` deliberately **excludes** `maxHeartbeats` on a false premise stated in its own docstring (`lean_toolchain.py:564`: "forbidden outright by Invariant #10") — nothing forbids it. The Tier-1 hook that would have caught it (`AI-DEFECT-DEFENSE-LAYER.md:32`) was never installed. Likelihood: realized. Blast radius: moderate (proof-architecture debt and Mathlib-CI portability, not soundness) — but an invariant stated in three documents with 22 live violations erodes trust in every other stated invariant. Cheapest fix: extend the `elaboration_knob_watchlist` regex (`lean_toolchain.py:578`) to include `maxHeartbeats`, ratchet at the current 22, and exempt `ExtractDeps.lean`.

**I2. Notebook stored-output correctness covers 2 of 91 notebooks.**
`notebook_stored_outputs_current` (`freshness.py:340`) globs `D1[12]_*.ipynb` — literally the two notebooks where the defect was found. `notebook_exec` proves a notebook *runs* and never writes back (`freshness.py:346`), so every other shipped notebook's stored outputs can display arbitrary stale content. The check's own docstring states the scope limit and the reason (execution cost), which is honest — but the D11 incident (a shipped notebook rendering claims the paper explicitly retracts) is not specific to D11. Cheapest fix: widen the glob to all notebooks referenced by a `bundle_metadata.json`, and run it in the slow suite.

**I3. The LaTeX compile gate is opt-in, and at least one bundle currently fails it.**
`paper_latex_compiles` (`papers_prose.py:400`) returns early unless `--force-latex` (`:429`), so a normal `validate.py` run — including `gate_precheck.py s13`, the Stage-13 prerequisite — never compiles anything. Its own repair note records "**D3 fails with 2 fatal errors**" (`:507`). It is also one non-stop pass with no BibTeX, so `Citation '...' undefined` is not detected; the planned `bundle_latex_compile_clean_citations` returns 0 files repo-wide and `qi-bundle_skeleton_inline_bibliography` is still open. Cheapest fix: add `paper_latex_compiles` to `gate_precheck.STAGE_CHECKS["s13"]` (`gate_precheck.py:28`) and grep the log for undefined-citation warnings.

**I4. No mechanism scans TeX for LLM artifacts or placeholder strings.**
Grep for `as an AI` / `Certainly!` / `language model` across `scripts/` returns nothing. `[REFERENCE]`, `[CITATION]`, `TODO`, `(citation needed)` are likewise unscanned. This is the cheapest check in the entire spec (`AI-DEFECT-DEFENSE-LAYER.md:39-40`) and the one Dietterich's arXiv actions treat as one-strike. Blast radius: reputational and immediate. Cheapest fix: ~15 lines appended to `pre-commit-sync.sh`, or a `validate.py` check over `_H.all_paper_drafts()`.

**I5. Headline certainty-calibration has no mechanism.**
`qi-headline-certainty-overclaim-vs-body` (`QI_REGISTER.md:114`, opened 2026-06-30, owner unassigned): a D10 abstract asserted essential self-adjointness as *unconditional* when the kernel proves only a Kato–Rellich reduction with two undischarged Props, and understated the global disclosure count. The QI entry states the mechanism precisely — "the Stage-10 claims review checks *presence*, not *certainty-calibration*." `disclosure_consistency` and `axiom_count_prose_consistency` are the nearest checks and neither compares an abstract's certainty words to the named theorem's actual hypotheses. Likelihood: high for LLM-drafted abstracts. Blast radius: high — the abstract is the most-read surface.

**I6. Invariants #1/#2/#3 (canonicality of `formulas.py` / `constants.py` / `visualizations.py`) are enforced for notebooks only.**
`notebooks` and `viz_consistency` (`notebooks.py:59,100`) check that *notebooks* import rather than reimplement. Nothing scans the **177 `src/` modules** for a reimplemented formula, a hardcoded physical constant outside `constants.py`, or a figure function outside `visualizations.py`. The δ_diss incident recorded at Invariant #4 (a 7–9-order dimensional error hiding behind a nominally-present theorem) is the same shape. Cheapest fix: an AST scan for unit-bearing float literals in `src/**` outside `constants.py`, ratcheted.

### Minor gaps

- **M0. Invariant #5 is enforced over 3 platforms.** `physical_bounds` (`physics.py:500`) checks 5 assertions each for `steinhauer`/`heidelberg`/`trento`. "Every computed quantity has bounds" across a Phase-1→6 codebase rests on the 164 pytest files, with no coverage requirement tying a new `src/` module to a bounds test.
- **M1.** `scripts/lint_native_decide_comments.py` is deliberately unregistered (`:22-24`) and relies on someone running it after a `native_decide`-touching edit. Honest, but a human-memory dependency.
- **M2.** The figure manifest carries `spec.caption` (the registry caption authored in `review_figures.py`), not the paper's `\caption{}`. So "does the figure match its caption" is checked against the *wrong* caption; drift between registry and paper caption is invisible even to the LLM.
- **M3.** The AI-defect layer's Invariant #16 was never appended to `WAVE_EXECUTION_PIPELINE.md` (grep for "three-tier" returns nothing), and its number **collides** with the existing Invariant #16 (tracked hypotheses). The prep brief that Invariant #16 depends on (`review_runner.py:84`) emits tier/sources/anchors and carries **no `tier_2_status` field**; neither reviewer agent has the "halt if Tier 2 failed" step zero. So the discipline "Tier 3 is residue-only" is unimplemented in both directions.
- **M4.** Invariant #12's `provenance_doi_in_registry` is advisory unless `--strict`, which is not in the default suite; Invariant #17's "encode-on-settle" clause is an advisory audit only.

## WAVE_EXECUTION_PIPELINE Invariants → enforcing mechanism → verdict

| # | Invariant | Enforcing mechanism | Verdict |
|---|---|---|---|
| 1 | `formulas.py` canonical | `notebooks` (notebooks only); nothing for 177 `src/` modules | **partial** |
| 2 | `constants.py` canonical | `numerical` (fixed param set); no scan for hardcoded constants in `src/` | **partial** |
| 3 | `visualizations.py` canonical | `viz_consistency` (notebooks only) | **partial** |
| 4 | Formula content-grounded on real non-placeholder theorem; zero sorry | `formula_grounding`, `formulas`, `lean_build`, pre-commit sorry guard | **enforced** |
| 5 | Every computed quantity has bounds | `physical_bounds` — 3 platforms × 5 assertions | **partial** |
| 6 | Every paper claim traces to computation ≤0.5% | `paper_provenance` (inert); `numerical_literals` ratchet with 116 grandfathered; `tables_fresh` for 15 opted-in tables | **prose-only in effect** |
| 7 | Narrative derives from data | Gate 7 `NarrativeGrounding` over LLM-derived `ProseClaim`/`SUPPORTS` edges | **partial (agent-derived)** |
| 8 | Parameter provenance verified | `parameter_provenance` (LLM tier); `--strict` human tier not in default suite | **enforced / partial at submission** |
| 9 | Placeholder theorems non-load-bearing | `placeholder_not_cited`, `formula_grounding`, graph exclusion | **enforced** |
| 10 | No heartbeat overrides in proof bodies | **none** — `elaboration_knob_watchlist` explicitly excludes `maxHeartbeats`; 22 live violations | **prose-only (violated)** |
| 11 | Every external bibitem has a primary-source cache file | `citation_primary_sources_present` (existence only); content match inert | **enforced (existence) / gap (content)** |
| 12 | Provenance DOIs resolve to registry | `provenance_doi_in_registry` — advisory unless `--strict` | **partial** |
| 13 | QI register auto-regen, never wiped | `scripts/qi_register.py` closed-block preservation | **enforced (by tool)** |
| 14 | Every paper-shaped output lifts into a bundle | `bundle_registry_consistency`, `bundle_consistency`, `bundle_source_freshness`; nothing asserts all 64 drafts carry a mapping entry | **partial** |
| 15 | New axiom requires user sign-off + `AXIOM_METADATA` | `axiom_closure_allowlist` (registration); sign-off unenforceable; pre-commit `^axiom` guard never installed | **partial** |
| 16 | Consumed tracked-hypothesis Props registered | `tracked_hypothesis_ledger` + `tracked_hypotheses_fresh`; struct-field assumptions not auto-enumerated (documented debt) | **partial (self-scoped)** |
| 17 | Provably-false no-gos have kernel-pure backing theorems | `nogo_substrate_integrity` (hard-fail); encode-on-settle advisory | **enforced / partial** |
| 16′ | AI-defect three-tier layer (per `AI-DEFECT-DEFENSE-LAYER.md`) | never appended to the pipeline doc; Tier 1 not installed; 6 of 9 Tier 2 checks absent; prep brief carries no Tier-2 status | **prose-only** |

**Stage gates:** mechanically gated on commit — **Stage 3b/5 only** (lake build + sorry). Mechanical *when run* — Stages 1, 2, 4, 7, 8, 11, 12, 13-precheck. Rely on an agent or human remembering — **Stages 6, 9, 10, 13, 14**. Stage 9 has no gate consuming its output at all.

## Assessment

**Is the infrastructure adequate to the stated policy?** **Partially.**

Where the artifact is a *Lean proof*, the answer is close to yes: the substrate gates, axiom closure, no-go ledger, and D5 mutation obligation genuinely mean a defective proof struggles to reach a human. Where the artifact is a *paper, figure, or notebook*, the answer is no — the deterministic layer verifies **presence and freshness** (does the reference resolve, is the count current, does the file exist) and almost never **correspondence** (does the number equal what the formula gives, does the theorem say what the prose says, does the cited paper contain the claim, does the figure show its caption). Correspondence is delegated wholesale to three LLM reviewer agents that (a) nothing forces to run, (b) receive no deterministic prep brief despite Invariant #16, and (c) are the *same class of system* whose defects the policy exists to catch. The project knows this: nine QI items are open, six of them naming a specific unshipped check, all with owner "unassigned" and target dates ~3 months past.

The most telling single fact is that the whole apparatus has no automatic trigger. 56 of 59 checks, all 11 readiness gates, and all 3 reviewer agents run only when someone remembers.

**The 3 highest-value additions, in order:**

1. **Make the system run itself.** A CI workflow executing `validate.py` (with `--force-latex`) plus the full pytest suite on every push, and moving the pre-commit hook's canonical source into *this* repo so a fresh clone is protected. Nothing else on this list matters until the checks execute without a human deciding to run them. Cost: hours.

2. **Ship `threshold_arithmetic` and `theorem_quoted_bound_matches_lean_literal`** — the two correspondence checks that close C3 and C4, four open QI items, and the two failure classes with documented worked instances (a factor-50 threshold error and a docstring bound quoted as a theorem). These convert "the prose asserts X" into "X is recomputed from the pipeline." Cost: ~10 hr combined, per the project's own estimates.

3. **Generalize the artifact-integrity checks off their incident-specific scopes**: `bundle_figure_integrity` from `d11_/d12_` to all of `FIGURE_REGISTRY`, `notebook_stored_outputs_current` from `D1[12]_*` to every bundle companion notebook, plus a `physics_checks` runner with a ratcheted empty-list count. Each was written to close exactly the figure or notebook where a human reviewer found the bug, and each leaves the other ~130 figures and ~89 notebooks in the state that produced the bug. Cost: low — these are scope widenings of working code, not new checks.
