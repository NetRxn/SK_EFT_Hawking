# R5 — coverage adequacy (PR review, pass 2)

**Branch:** `infra/adr-009-validation-modularization` · **Base:** `main` @ `c2b597e1`
**Lens:** not "is what exists correct" but **"what is missing entirely?"** — a wrong artifact
that could ship today with every gate green.
**Reviewer id prefix:** `R5` (pass-2 findings are numbered fresh; pass-1 ids are cited as
`R5-C2`, `R5-I1`, … when I am re-filing them).

Every finding below carries a command I ran and its output. Where I re-file a pass-1 finding I
say so explicitly with its id, per BRIEF §6.

---

## 0. Executive summary

| | |
|---|---|
| **Verdict** | **YES WITH FIXES** — safe to merge; one new merge-blocker-class finding (`R5-C1`) is latent and cheap to fix or to demote by deleting the mode. |
| New CRITICAL | 1 (`R5-C1` — the `--ci` coverage floor cannot fire on the condition it documents) |
| Re-filed CRITICAL, still open | 4 (`R5-C2`…`R5-C5` = pass 1's `R5-C2`…`R5-C5`) — all **submission** blockers, ADR-010 |
| New MAJOR | 2 (`R5-MAJ1` human-verification write path; `R5-MAJ2` Stage 9's gate cannot fail) |
| Re-filed MAJOR | 1 (`R5-MAJ3` = pass 1's `R5-I1`, Invariant #10 — **22 violations re-measured and confirmed**, escalated because a *test* now pins the false premise) |
| IMPORTANT | 7 · **MINOR** 5 |
| On the C1 re-diagnosis | **Partially accept.** The performance argument is sound and well-evidenced. It answers "is a runner the cheapest way to get speed" and does **not** answer "what fires without a human deciding to." See `R5-I1`. |

The single sentence that has not changed since pass 1: **where the artifact is a Lean proof the
substrate is genuinely strong; where the artifact is a paper, figure or notebook the
deterministic layer verifies presence and freshness and almost never correspondence.**

---

## 1. Project invariant → enforcing mechanism → verdict

Sourced from `docs/WAVE_EXECUTION_PIPELINE.md` §Pipeline Invariants (#1–#17) and
`SK_EFT_Hawking/CLAUDE.md` §Architecture. Verdicts: `ENFORCED` · `PARTIAL` · `PROSE-ONLY` ·
`PROSE-ONLY AND VIOLATED`. Registry size at review time: **59 checks** (`validate.py --list |
grep -c '^  [a-z]'` → `59`).

| # | Invariant | Enforcing mechanism (verified) | Verdict |
|---|---|---|---|
| 1 | `formulas.py` canonical | `notebooks` (`checks/notebooks.py`) — **notebooks only**. No scanner over `src/`. | **PARTIAL** |
| 2 | `constants.py` canonical | `numerical` (fixed param set) + `parameter_provenance`; nothing scans `src/**` for hardcoded physical constants. | **PARTIAL** |
| 3 | `visualizations.py` canonical | `viz_consistency` (`checks/notebooks.py:100`) — notebooks only, **and returns `passed=True` unconditionally at `:199`**. | **PARTIAL** (advisory) |
| 4 | Formula content-grounded on a real non-placeholder theorem; zero sorry | `formula_grounding` (~390 refs, hard-fail on placeholder-grounded), `formulas`, `lean_build`, pre-commit `declaration uses 'sorry'` parse | **ENFORCED** |
| 5 | Every computed quantity has bounds | `physical_bounds` (`checks/physics.py:685-703`) — 3 platforms (`steinhauer`/`heidelberg`/`trento`) × ~5 assertions. No coverage rule tying a new `src/` module to a bounds test. | **PARTIAL** |
| 6 | Every paper claim traces to computation (≤0.5 %) | `paper_provenance` (figure/bib existence only — its theorem-ref leg was **removed** 2026-08-05, QI-32, `papers_prose.py:107`); `numerical_literals` is a ratchet **at** its ceiling (`NUMERICAL_LITERAL_CEILING = 116`, `constants.py:2495`); `tables_fresh` for opted-in tables. **Nothing recomputes a quoted number.** | **PROSE-ONLY in effect** (see `R5-C3`) |
| 7 | Narrative derives from data | Readiness gate `NarrativeGrounding` over LLM-derived `ProseClaim`/`SUPPORTS` graph edges — agent-derived, not deterministic | **PARTIAL (agent-derived)** |
| 8 | Every experimental parameter has verified provenance | `parameter_provenance` legs 1–2 hard-fail (LLM tier, 206/206 green); leg 3 (human tier) hard-fails only under `--strict`, called by `gate_precheck submission`. **But the only sanctioned way to satisfy leg 3 does not write to disk** — `R5-MAJ1`. | **PARTIAL / broken at the submission tier** |
| 9 | Placeholder theorems non-load-bearing | `placeholder_not_cited`, `formula_grounding`, `build_graph` placeholder exclusion | **ENFORCED** |
| 10 | **No heartbeat overrides in proof bodies** | **none.** `elaboration_knob_watchlist` regex (`lean_toolchain.py:604`) covers `maxRecDepth\|synthInstance.maxSize\|synthInstance.maxHeartbeats` and deliberately excludes bare `maxHeartbeats` on the docstring premise that it is *"enforced elsewhere"* (`:590-592`). There is no elsewhere. **22 live violations.** | **PROSE-ONLY AND VIOLATED** (`R5-MAJ3`) |
| 11 | Every external bibitem has a primary-source cache file | `citation_primary_sources_present` — file **existence** only. The one content check (`bibitem_title_primary_source`) is ratcheted at `BIBITEM_TITLE_DRIFT_CEILING = 7` and `--strict`-only. | **ENFORCED (existence) / GAP (content)** — `R5-C5` |
| 12 | Provenance DOIs resolve to registry | `provenance_doi_in_registry` — advisory unless `--strict`; `--strict` now has a caller (`gate_precheck submission`, `2577fdbc`) | **PARTIAL → improved this branch** |
| 13 | QI register auto-regen, never wiped | `scripts/qi_register.py` closed-block preservation | **ENFORCED (by tool)** |
| 14 | Every paper-shaped output lifts into a bundle | `bundle_registry_consistency`, `bundle_consistency`, `bundle_source_freshness`. Nothing asserts every draft under `papers/` carries a `PAPER_DRAFT_MAPPING` entry. | **PARTIAL** |
| 15 | New axiom requires user sign-off + `AXIOM_METADATA` | `axiom_closure_allowlist` enforces **registration** (10 `AXIOM_METADATA` entries vs the live `axiom` decls); the *sign-off* clause is unenforceable by construction and no pre-commit `^axiom` guard is installed | **PARTIAL** (registration only — honest limit) |
| 16 | Consumed tracked-hypothesis Props registered | `tracked_hypothesis_ledger` (hard-fail) + `tracked_hypotheses_fresh`; 48 registry entries. Struct-field Prop assumptions not auto-enumerated (documented debt). | **PARTIAL (self-scoped, disclosed)** |
| 17 | Provably-false no-gos have kernel-pure backing theorems | `nogo_substrate_integrity` hard-fail over `KERNEL_NOGO_REGISTRY` (45 entries); the **encode-on-settle** clause is an advisory audit only | **ENFORCED (registered) / PARTIAL (encode-on-settle)** |
| 16′ | AI-defect three-tier layer (`docs/AI-DEFECT-DEFENSE-LAYER.md`) | Tier-1 hooks never installed; of the layer's named Tier-2 checks, `threshold_arithmetic`, `theorem_quoted_bound_matches_lean_literal`, `bibitem_registry_character_match`, `citation_bibkey_form_matches_metadata`, `bundle_latex_compile_clean_citations` return **0 non-doc files** repo-wide (below). Number also collides with the real Invariant #16. | **PROSE-ONLY** |

**Stage gates.** Mechanically gated *on commit*: Stage 3b/5 only (incremental `lake build` +
sorry parse), and only on `main` (`pre-commit-sync.sh:59,70,99`). Mechanical *when someone runs
them*: 1, 2, 4, 7, 8, 11, 12, 13-precheck, and now `submission`. Depend on an agent or human
remembering: 6, 9, 10, 13, 14. **Stage 9's gate exists and cannot fail** — `R5-MAJ2`.

---

## 2. CRITICAL

### R5-C1 — `validate.py --ci`'s coverage floor cannot fire on the condition it was built for. **NEW.**

**Severity:** `CRITICAL`. **This is the only finding in my report that meets the brief's
merge-blocker definition** ("ships a guard that cannot fire"). It is *latent* — no caller exists
— which is why my overall verdict is still YES WITH FIXES rather than NO.

- **file:line** — `scripts/validate.py:659-676` (the floor), `scripts/validate.py:227-239`
  (`run_checks`), `scripts/validation/_config.py:105-119` (`CI_MIN_CHECKS_RUN = 55`),
  `tests/test_ci_mode.py:TestCoverageFloor`.
- **What it claims.** `_config.py:108-113`, verbatim: *"Dropping the Lean toolchain from a
  runner makes the suite ~200 s faster and stops 7 checks that read `lean_deps.json` plus 3 that
  shell to `lake` from measuring anything — while the run still reports green… So `--ci` FAILS
  when fewer checks execute than this. **A missing toolchain becomes a red build reading '48 of
  55 ran'**."* `CI_DEFAULTS_ASSESSMENT.md:284-287` repeats the claim as the justification for
  retaining the mode.
- **What it actually does.** `n_ran = len(results)`. `run_checks` populates
  `results[spec.name]` for **every** registered spec — the check's own result, or a synthesized
  `CheckResult(passed=False, error=…)` if it raised. Nothing in the environment can remove an
  entry. So `n_ran == len(_CHECKS) − len(CI_SKIP)` **identically**, = 59 − 4 = **55** = the
  floor. The branch `if n_ran < _cfg.CI_MIN_CHECKS_RUN` is unreachable except by editing the
  registry, and `tests/test_ci_mode.py::test_the_LIVE_floor_has_ZERO_headroom` *asserts* the
  constant tracks the registry size — which closes the only remaining route to failure. **The
  floor is a registry-size bookkeeping assertion wearing the name of a coverage floor.**
- **How I verified.**

  ```
  $ LEAN_PROJECT_DIR=/nonexistent/lean uv run --no-sync python scripts/validate.py \
        --check axiom_closure_allowlist --no-memo
    ✓ PASS  axiom_closure_allowlist: …
    ✓ axiom_audit_src  —  SKIPPED — /nonexistent/lean/SKEFTHawking/AxiomAudit.lean not found
    Overall: 1/1 checks passed
  ```

  The check most cited in the floor's own rationale returns **PASS with a SKIPPED detail** when
  the Lean tree is absent — and a PASS is an entry in `results`, so it counts toward `n_ran`.
  Population of the same shape:

  ```
  $ rg -n "CheckResult\(passed=True" -A3 scripts/validation/checks/*.py | rg -ci skip
  19
  # by file: lean_toolchain 8 · papers_prose 5 · bundles_readiness 2 · freshness 2 · reviews 1
  ```

  **19 early-return-PASS-on-missing-artifact paths, none of which the floor can see.**
- **The test does not close it either.** `test_a_shrunken_suite_FAILS_even_though_every_check_passed`
  monkeypatches `validate._CHECKS` down to 6 specs and sets the floor to 9. That seeds
  *registry shrinkage*, not *toolchain absence* — while its own docstring says *"on a runner
  without `lake`, the suite gets ~200 s faster and 10 checks quieter, and without this it exits
  0."* By **QI-30's criterion** (seed the defect in the production artifact) this is a
  fixture-shaped mutation test asserting the guard against a condition the mode does not
  document. The production-artifact seed is the `LEAN_PROJECT_DIR` run above, and it stays
  green.
- **Blast radius.** Latent today (no `.github/`, no workflow — `ls .github` → *No such file*).
  The moment anyone wires `--ci` into a runner, the single guard that makes the mode
  safe-to-trust is inert, and the mode's documented purpose is *"a green tick over 48 of 59 is
  worse than no CI."* That is the audit's own defect class, in the artifact built to close it.
- **Fix (either is fine, ~20 lines / ~1 line).** (a) Count *measurement*, not registration:
  have `Detail` carry a `skipped: bool` (or classify on a `SKIPPED` prefix, which every one of
  the 19 sites already emits) and define `n_ran` as checks with ≥1 non-skipped detail; then
  re-derive the floor empirically and ratchet it. (b) Or delete `--ci` and its floor until a
  runner exists, and say in the assessment that fresh-clone coverage is unsolved.

### R5-C2 — figure *content* is unverified. **RE-FILE of pass-1 `R5-C2`; still open, and the measurement is worse than filed.**

- **Confirmed as filed.** `physics_checks=` appears **137** times in
  `scripts/review_figures.py`; **118** are `physics_checks=[]`. The field has exactly **two**
  occurrences outside the registry literals — its declaration (`:61`) and its serialization into
  the manifest (`:2818`). **There is no runner.** Only `scripts/provenance_dashboard.py` reads
  `figures/figure_review_report.json` (`rg -ln figure_review_report scripts/ src/ tests/` → one
  file). `bundle_figure_integrity` is still filtered to `d11_`/`d12_`
  (`checks/bundles_readiness.py:117`, with the same filter hardcoded in the `except` fallback at
  `:124-133`).
- **New measurement pass 1 did not take — the *shipped* population, not the registry.**

  ```
  FIGURE_REGISTRY specs: 137        empty physics_checks: 118
  shipped PNGs under papers/*/figures/: 124   across 49 paper/bundle dirs
  shipped PNGs with NO FIGURE_REGISTRY spec: 29
    e.g. papers/D8/figures/d8_fig1_alphabet_dimension_map.png,
         d8_fig2_su8_density_duality.png, d8_fig3_sk_recursion.png,
         papers/E1/figures/fig_stimulated_hawking_spectrum.png,
         papers/D5/figures/fig_bbn_conformance_matrix.png
  PNGs matching bundle_figure_integrity's d11_/d12_ filter: 7   (7 of 124 = 5.6 %)
  ```

  **This corrects pass 1's proposed cheap fix.** Deleting the `d11_/d12_` filter so the check
  iterates `FIGURE_REGISTRY` unfiltered would take coverage from 7 to 95 of 124 — it would still
  leave **29 shipped figures (23 %), including all three of D8's main figures, invisible to every
  mechanism in the repo**, because they have no registry spec to iterate. The filter deletion
  must be paired with a registry-completeness check (`every papers/*/figures/*.png has a
  FIGURE_REGISTRY spec`, ratcheted at 29).
- **Blast radius / routing.** Pre-existing absence, not a regression → **submission blocker,
  ADR-010.** Pass-1 severity rationale stands: *"a figure that plots the wrong quantity under a
  confident caption is exactly the arXiv-moderation failure mode, and the project already
  documented this end-to-end."*

### R5-C3 — nothing recomputes a paper-quoted number from its formula. **RE-FILE of pass-1 `R5-C3`; still open.**

```
$ rg -l "threshold_arithmetic" . | grep -v docs/audits
./docs/QI_REGISTER.md
./docs/AI-DEFECT-DEFENSE-LAYER.md
```

**Zero implementation files. Not registered** (absent from `validate.py --list`). Invariant #6's
only live mechanisms are `numerical_literals` (a ratchet sitting *at* `NUMERICAL_LITERAL_CEILING
= 116`, i.e. 116 grandfathered untraced inline literals) and `paper_provenance`, whose
theorem-reference leg was **removed** on 2026-08-05 as inert (QI-32, `papers_prose.py:107-115`).
Worked precedent unchanged (`QI_REGISTER.md:96`): a `G > 0.01` claim where the correct value was
`0.5`, with a companion photon count wrong 25×, propagated across 4 sites and survived a full
per-paper Stage-13 review. **Submission blocker, ADR-010.**

### R5-C4 — nothing checks a cited theorem's STATEMENT supports the prose. **RE-FILE of pass-1 `R5-C4`; still open.**

```
$ rg -l "theorem_quoted_bound_matches_lean_literal" .
./docs/AI-DEFECT-DEFENSE-LAYER.md
+ 3 files under docs/audits/ (the pass-1 reports themselves)
```

Zero implementation files, not registered. `prose_theorem_reference_coverage` resolves
`\texttt{Module.symbol}` against `lean_deps.json` — **name resolution only**. The documented
instance (`QI_REGISTER.md:108`) stands: prose said *"formally bounded at ≤1.8 %"*; the Lean
theorem is a generic algebraic envelope and the 1.8 % lives in a **docstring**. This is the
project's headline differentiator converting to an unsupported claim. **Submission blocker,
ADR-010.**

### R5-C5 — citation *content* verification is inert. **RE-FILE of pass-1 `R5-C5`; still open.**

```
$ rg -l "bibitem_registry_character_match" .        → docs only (AI-DEFECT + QI_REGISTER + audits)
$ rg -l "citation_bibkey_form_matches_metadata" .   → docs only
$ rg -l "bundle_latex_compile_clean_citations" .    → docs only + one AutomatedReviews md
```

Zero implementation files for all three; none registered. What ships is
`citation_primary_sources_present` — file **existence** — plus `bibitem_title_primary_source`,
which is `--strict`-only and ratcheted at `BIBITEM_TITLE_DRIFT_CEILING = 7`. Pass 1's cheapest
cut (`citation_bibkey_form_matches_metadata`, 1–2 h, catches `KaulMajumdar1998` and
`SextyWetterich2009`) is still unbuilt. **Submission blocker, ADR-010.** One-strike arXiv
trigger; the paper40 hallucinated-arXiv-ID incident is on the record.

---

## 3. MAJOR

### R5-MAJ1 — Invariant #8's human-verification tier has a hard gate and **no working way to satisfy it**. **NEW (pass 1 listed this unattributed in the register as "highest value remaining"; it was never measured).**

- **file:line** — `scripts/provenance_dashboard.py:5449-5452` (the `--write` CLI),
  `:1272-1284` (the HTTP confirm route), `scripts/validation/checks/citations.py:119-146`
  (the gate), `scripts/readiness_gates.py:235-262` (the readiness gate).
- **What it claims.** Invariant #8: *"Paper submission requires human verification via the
  provenance dashboard."* The CLI advertises `--write` as *"Write current verification state to
  provenance.py and exit"*. The HTTP route returns a green `HUMAN VERIFIED` badge with today's
  date.
- **What it actually does.**

  ```python
  if args.write:
      print("Write mode: updating provenance.py with verification state...")
      # TODO: implement file rewriting
      return
  ```

  It prints a progress message and returns. **Absence of a write rendered as a write** — the
  branch's target defect class, verbatim. The HTTP route mutates the imported dict in
  process memory (`entry['human_verified_date'] = now`) and never persists; the badge is
  returned regardless.
- **How I verified.**

  ```
  $ rg -n "human_verified_date" scripts/ src/ tests/ --glob '!provenance_dashboard.py'
  # every hit is a READER (citations.py, readiness_gates.py, build_graph.py, last_modified.py)
  # or a literal in src/core/provenance.py. NO WRITER ANYWHERE.

  $ ls docs/verification_log.jsonl
  ls: docs/verification_log.jsonl: No such file or directory     # the event log has never been written

  $ python -c "from src.core.provenance import PARAMETER_PROVENANCE as P; ..."
  total 206  human_verified 128  llm_verified 206
  ```

  The 128 populated entries were hand-edited into `src/core/provenance.py`; the
  `verification_state.record_event` fallback is wrapped in a bare `try/except … logger.warning`
  (`:1289-1301`) and its log file does not exist, so even the audit trail is empty.
- **Blast radius.** 78 parameters lack `human_verified_date`. `parameter_provenance` leg 3
  hard-fails under `--strict`, and `gate_precheck submission` — new on this branch — is now its
  caller. So the Paper Submission Gate is **hard-blocked on a field whose only sanctioned
  producer is a stub**, and the workaround (hand-editing `provenance.py`) has no audit trail and
  no distinction from an LLM writing the same date. A reviewer looking at the dashboard sees
  `HUMAN VERIFIED`; nothing on disk changed.
- **Fix.** Implement the `--write` rewrite (or make the route append to
  `docs/verification_log.jsonl` and have `parameter_provenance` read the log as the source of
  truth). Until then the `--write` flag should raise `NotImplementedError`, not print a success
  message — that one-line change removes the false signal immediately.
- **Routing.** Not a regression on this branch → **submission blocker**, but the
  `NotImplementedError` one-liner is worth taking pre-merge.

### R5-MAJ2 — Stage 9's gate is a single check that returns `passed=True` unconditionally. **NEW.**

- **file:line** — `scripts/gate_precheck.py:30` (`"s9": ["viz_consistency"]`),
  `scripts/validation/checks/notebooks.py:199` (`return CheckResult(passed=True, details=details)`
  with the preceding comment `# Always passes — these are advisory warnings`).
- **What it claims.** `WAVE_EXECUTION_PIPELINE.md` Stage 9 gate: *"All figures PASS LLM review.
  No FAIL, no MINOR remaining."* `gate_precheck s9` is the sanctioned pre-dispatch gate.
- **What it actually does.** Runs exactly one check whose return is a hardcoded `True`,
  regardless of what it found.
- **How I verified.**

  ```
  $ uv run --no-sync python scripts/gate_precheck.py s9 ; echo rc=$?
    Overall: 1/1 checks passed (24 warnings)
    ALL CHECKS PASSED
    gate_precheck s9: PASS
  rc=0
  ```

  **24 warnings, discarded; rc=0 by construction.** `gate_precheck s9` cannot return non-zero.
- **Blast radius.** The gate immediately preceding the figure-reviewer dispatch — the one place
  the pipeline says figures are gated — is structurally incapable of blocking, and it does not
  run `bundle_figure_integrity` either (that only reaches figures at `s13`'s `__full__`). This
  is the *mechanism* half of `R5-C2`: pass 1 said "Stage 9 has no gate consuming its output";
  the sharper truth is that a gate exists, emits 24 warnings, and passes.
- **Provenance.** Pre-existing (`ee51bfa5`, 2026-06-17), not introduced here → **submission
  blocker**, ADR-010. Cheap partial fix: add `bundle_figure_integrity` to `STAGE_CHECKS["s9"]`
  (1 line) so at least something in that stage can fail.

### R5-MAJ3 — Invariant #10 is unenforced with **22 live violations**, and a test now pins the false premise. **RE-FILE of pass-1 `R5-I1`, escalated `IMPORTANT` → `MAJOR`.**

- **Re-measured, count CONFIRMED exactly** (the brief requires this; pass 1 said 22 across 4
  files, all `theorem`):

  ```
  $ rg -c "set_option (maxHeartbeats|synthInstance\.maxHeartbeats)" lean/SKEFTHawking --glob '*.lean'
  # 12 files match; 8 of them are docstring/comment mentions of the RULE.
  # Real `set_option maxHeartbeats N in` immediately preceding a decl:
  QuantumGroupCoproduct.lean   2   (:784, :1120  → private theorem)
  Uqsl3Hopf.lean               8   (:1104 :1387 :1663 :1951 :2561 :2945 :3290 :3629)
  Uqsl2AffineHopf.lean        10   (:2063 :2332 :3291 :4157 :4964 :5098 :5215 :5327 :5642 :5720)
  QuantumGroupAntipode.lean    2   (:353, :541   → public theorem)
  ────────────────────────────────
  TOTAL                       22   in 4 files
  ```

  (`Uqsl2AffineHopf.lean:1520` and 7 hits in `FibonacciSextetTrueRep`, `Mat13K5Ext`,
  `PinPlus…SeamDetect`, `CenterFunctorZ2Equiv`, `FKLW/{FibRepInfiniteOrder,
  SpecialUnitaryPathConnected, SpecialUnitaryTopology}` are prose asserting the rule is
  respected. `ExtractDeps.lean:497,502` sets `maxHeartbeats` via `Options`/`Core.Context`, which
  is the invariant's explicit metaprogram exception — correctly excluded.)
- **The false premise is confirmed and now load-bearing on a test.**
  `lean_toolchain.py:590-592`: *"NB `maxHeartbeats` in proof bodies is forbidden outright by
  Invariant #10 (architecture discipline) and **is enforced elsewhere**; it is intentionally not
  in this advisory list."* There is no elsewhere:

  ```
  $ rg -n "maxHeartbeats" scripts/ tests/ .claude/ .git/hooks/   # excluding worktrees + agent prose
  scripts/validation/checks/lean_toolchain.py:604   # the regex that omits it
  scripts/validation/checks/lean_toolchain.py:726   # an unrelated identifier-exemption set
  tests/test_d5_lean_toolchain.py:397               # ← see below
  ```

- **New since pass 1 — a test that asserts the gap.** `tests/test_d5_lean_toolchain.py:397-405`,
  `test_maxHeartbeats_is_deliberately_not_watched_here`, feeds `set_option maxHeartbeats 400000`
  to the watchlist and asserts the report says `"0 proof-body"`. Its docstring repeats the false
  premise (*"is enforced elsewhere"*). Introduced on **this branch** (`15edc340`, 2026-08-04).
  So the branch converted an unenforced invariant into a **test-pinned** unenforced invariant:
  anyone who later extends the regex to close the gap now breaks a passing test whose docstring
  tells them the gap is correct. That is *"a document describing a broken guard as fine"* —
  BRIEF §4's seventh face — promoted to executable form.
- **Blast radius.** Not soundness (the kernel re-checks; these stay kernel-pure). It is
  proof-architecture debt and Mathlib-CI portability — *and* an invariant restated in
  `WAVE_EXECUTION_PIPELINE.md`, both `CLAUDE.md`s, the `lean-worker` agent, the `goal-dev`
  skill, and 8 Lean file docstrings, with 22 live violations. An invariant that agents are told
  five times is inviolable and that 22 shipped theorems violate erodes the credibility of the
  other sixteen.
- **Fix (cheap, and it belongs pre-merge because the test is new here).** Either (a) delete or
  invert `test_maxHeartbeats_is_deliberately_not_watched_here` and fix the docstring at
  `:590-592` so the gap is *documented as a gap*; or (b) extend the `:604` regex to include bare
  `maxHeartbeats`, exempt `ExtractDeps.lean`, and ratchet at 22 in the house idiom
  (`MAXHEARTBEATS_PROOF_BODY_CEILING = 22`) so it can only decrease. (b) is ~5 lines and is the
  form every other debt in this repo takes.

---

## 4. IMPORTANT

### R5-I1 — the C1 re-diagnosis: I accept the performance half, and **reject it as a retraction**. Two of C1's four mechanism claims are unanswered.

`CI_DEFAULTS_ASSESSMENT.md` is a good document and its central move is right: the suite cost
332 s because it was the only unscoped stage, the memo work is real (`171.6 s → 0.1 s`,
production-seeded invalidation probe in the real tree), the LaTeX slow-gate deletion is a
genuine strengthening, and "no nightly, no per-push suite" is a defensible operator call I do
not contest.

**But it answers a different question than C1 asked.** C1's claim was *"the system is a library
of checks, not a gate — nothing runs without a human deciding to."* The assessment's rebuttal is
*"the harness's own stages carry the load at a cost proportional to the diff."* Those stages are:

| stage | who triggers it |
|---|---|
| `pre-commit-sync.sh` / `pre-commit-notebooks.sh` | git — **the only automatic trigger in the system** |
| `validate.py` full | a human or an agent typing it |
| `gate_precheck s9/s10/s13/submission` | a human or an agent typing it |
| `wave-close` | a human or an agent typing it |

Change-scoping made the *manual* stages cheap. It did not make any of them fire. Two of C1's
four mechanism claims about the one automatic trigger are re-verified and **unaddressed by the
re-diagnosis**:

```
$ git ls-files | grep -i hooks/pre-commit      → (empty: the hook is untracked; installed by a
                                                  script in the PRIVATE repo)
$ ls .github                                   → No such file or directory
scripts/pre-commit-sync.sh:36   command -v uv … || { echo "…skipping"; exit 0; }   # FAIL-OPEN
scripts/pre-commit-sync.sh:24   worktree commit → exit 0                            # SKIPPED
scripts/pre-commit-sync.sh:59,70,99  [ "$BRANCH" = "main" ] && exit 1 || "(off-main: warn only)"
```

So: **a fresh clone of this public repo has zero enforcement** (the hook is not in it), and
**every one of this branch's 99 commits was made under warn-only enforcement** because the
branch is not `main`. The assessment's §4 concedes the fresh-clone half exists and defers it
("that remains the operator's call") — which is a legitimate product decision — but the register
records the finding as `🔁 RE-DIAGNOSED`, and a reader will take that as *closed*. It is not.

**What I would change:** re-label the register row `🔧 PARTIAL` and add a one-line residual —
*"the pre-commit hook's canonical source is not in this repo; a fresh clone has no gate."*
Moving `pre-commit-sync.sh`'s installer into this repo is a few lines and closes the half of C1
that the memo work does not touch. `UNVERIFIED` sub-claim I could not settle: whether the
operator considers a public-repo hook installer an outward-facing change requiring the same
sign-off as a workflow file. That would settle it.

### R5-I2 — `paper_latex_compiles` still runs no BibTeX; undefined citations remain undetected. **RE-FILE of pass-1 `R5-I3` (BibTeX half; the `--force-latex` half was fixed by `2577fdbc`).**

`scripts/validation/checks/papers_prose.py:61-64`, verbatim: *"Undefined-reference /
undefined-citation / overfull-box warnings are NOT fatal and are ignored."* No `bibtex`/`biber`
invocation anywhere in the file (`rg -n "bibtex|biber" checks/papers_prose.py` → nothing). The
planned `bundle_latex_compile_clean_citations` has 0 implementation files (see `R5-C5`). So a
draft citing a bibkey that does not exist compiles "clean". Verified live — the check is
currently red for a *different* reason:

```
$ uv run --no-sync python scripts/validate.py --check paper_latex_compiles
  ✗ summary  —  20/21 bundle drafts clean (20 from cache, 0 freshly compiled) — 1 with fatal errors
  ✗ compile:D3  —  D3: 2 fatal — first: ! Undefined control sequence.
```

D3's failure is a **pre-existing corpus defect newly surfaced**, exactly as the assessment says
— not a merge blocker. The BibTeX gap is a **submission blocker**. Fix: one `bibtex` pass plus a
grep of the `.log` for `Citation '.*' undefined`, ~10 lines.

### R5-I3 — no scan for LLM artifacts or placeholder strings in TeX. **RE-FILE of pass-1 `R5-I4`; still open.**

`rg -ni "as an AI|Certainly!|language model|\[REFERENCE\]|\[CITATION\]|citation needed|lorem
ipsum" scripts/validation/checks/*.py` returns nothing but unrelated `TODO` comments. The
nearest live mechanism is `lean_substrate.py:155`'s `_TODO|not yet (proven|formal|verif)|conjectur`
regex, which scans **Lean docstrings**, not paper `.tex`. Cheapest check in the entire spec
(`AI-DEFECT-DEFENSE-LAYER.md:39-40`), one-strike reputational blast radius. **Submission
blocker.**

### R5-I4 — Invariants #1/#2/#3 are enforced for notebooks only; `src/` is unscanned. **RE-FILE of pass-1 `R5-I6`; still open.**

`notebooks` and `viz_consistency` (`checks/notebooks.py:59,100`) check that *notebooks* import
rather than reimplement. Nothing scans `src/**` for a reimplemented formula, a hardcoded
physical constant outside `constants.py`, or a figure function outside `visualizations.py`. Note
the interaction with `CI_DEFAULTS_ASSESSMENT.md`'s own measurement: editing `src/core/formulas.py`
invalidates 91/91 notebooks and a *non-core* edit still invalidates 82/91 — the assessment
correctly calls that structural, *"which Pipeline Invariants #1–#3 make structural, not
incidental."* The invariants that make it structural are the ones with no `src/`-side mechanism.

### R5-I5 — notebook stored-output correctness covers 2 of 91. **RE-FILE of pass-1 `R5-I2`; routed to ADR-010 by the operator.**

`notebook_stored_outputs_current` globs `D1[12]_*.ipynb` — literally the two notebooks where the
defect was found. `notebook_exec` proves a notebook *runs* and never writes back. Confirmed
still scoped as filed. **Submission blocker.**

### R5-I6 — headline certainty-calibration has no mechanism. **RE-FILE of pass-1 `R5-I5`; still open.**

`qi-headline-certainty-overclaim-vs-body` remains in `docs/QI_REGISTER.md` §Open Items (23 `###
qi-*` blocks total in the file). No check compares an abstract's certainty words against the
named theorem's actual hypotheses; `disclosure_consistency` and `axiom_count_prose_consistency`
are the nearest and neither does this. **Submission blocker.**

### R5-I7 — `--ci` does not imply `--no-memo`. **NEW.**

`validate.py:576` sets `_cfg.NO_MEMO = args.no_memo`; `--strict` implies it, `--ci` does not
(`tests/test_ci_mode.py::test_ci_does_not_imply_strict` deliberately confirms `--ci` ≠
`--strict`, and no test covers the memo interaction). On a genuinely fresh clone the memo cache
is gitignored (`.gitignore:77 docs/validation/.check_memo.json`) so it misses and this is
harmless — which is the intended use. But `--ci` run on a warm workstation (the only place it
*can* be run today) reuses cached PASSes, and those cached PASSes count toward the floor that
`R5-C1` shows cannot fire. The two defects compose: `validate.py --ci` on this machine can
report `55 ran` with both expensive Lean checks having measured nothing. One line: `_cfg.NO_MEMO
= args.no_memo or args.ci`. **Merge-adjacent** (same new surface as `R5-C1`), cheap.

---

## 5. MINOR

- **R5-MIN1.** The figure manifest carries `spec.caption` (the registry caption authored in
  `review_figures.py`), not the paper's `\caption{}`. "Does the figure match its caption" is
  therefore checked against the *wrong* caption even by the LLM; registry↔paper caption drift is
  invisible. (Re-file of pass-1 `R5-M2`.)
- **R5-MIN2.** Invariant #5 is enforced over 3 platforms × ~5 assertions
  (`checks/physics.py:685-703`). No rule ties a new `src/` module to a bounds test.
- **R5-MIN3.** `scripts/lint_native_decide_comments.py` is deliberately unregistered and depends
  on someone remembering to run it. Honest, but a human-memory dependency.
- **R5-MIN4.** Invariant #17's *encode-on-settle* clause is advisory-only
  (`nogo_substrate_integrity` hard-fails on a missing/tainted backing theorem for a *registered*
  fork, but only advises on a refutable-but-unencoded one). 45 registry entries.
- **R5-MIN5.** `AI-DEFECT-DEFENSE-LAYER.md`'s "Invariant #16" was never appended to
  `WAVE_EXECUTION_PIPELINE.md` and its number **collides** with the real Invariant #16 (tracked
  hypotheses). Its Tier-1 hooks are uninstalled and 5 of its named Tier-2 checks have 0
  implementation files (C3/C4/C5 above). (Re-file of pass-1 `R5-M3`.)

---

## 6. What is genuinely well covered (unchanged from pass 1, re-verified)

- **Lean substrate integrity** — `formula_grounding`, `proxy_body_audit`,
  `tracked_hypothesis_ledger`, `placeholder_not_cited`, `native_decide_regression`,
  `axiom_closure_allowlist`, `vacuous_statement_audit`, `nogo_substrate_integrity`. Registries
  are live and non-trivial: 10 `AXIOM_METADATA`, 45 `KERNEL_NOGO_REGISTRY`, 48
  `HYPOTHESIS_REGISTRY`.
- **Zero-sorry** is the one invariant with a real automatic gate, and it parses the `lake build`
  log rather than grepping source — correctly built.
- **The D5 mutation obligation** (`tests/test_d5_mutation_obligation.py`) still forces every
  registered check to declare `MUTATION_VERIFIED` or `AWAITING_MUTATION_TEST`. Very few QA
  systems test whether their tests can fail.
- **New this branch and good:** `gate_precheck submission` gives Invariant #12's `--strict` an
  actual caller for the first time; the memo's four guards (body-source in every key,
  production-seeded key tests, PASS-only caching with FAIL eviction, visible skip line) are the
  right four; and `CI_DEFAULTS_ASSESSMENT.md` records its own two wrong measurements rather than
  quietly fixing them — which is the behaviour this audit is trying to install.

---

## 7. Verdict

# YES WITH FIXES

**Safe to merge.** Nothing on this branch removes coverage that previously existed. The two
things that *look* like regressions are not: `paper_latex_compiles` going red on D3 is a
pre-existing corpus defect the branch made visible for the first time, and the memo's PASS-
without-running is guarded four ways with a production-seeded invalidation probe.

**Findings that decide it:**

**Merge-blocker class (by BRIEF §7's "ships a guard that cannot fire") — both new, both cheap:**

1. **`R5-C1`** — `--ci`'s coverage floor cannot fire on toolchain absence, the condition its own
   docstring names; `n_ran` is registry size, invariant at 55, and 19 checks return PASS with a
   `SKIPPED` detail without reducing it. Latent (no caller). **Fix, demote, or delete the mode
   before merge.**
2. **`R5-MAJ3`** — the branch added `test_maxHeartbeats_is_deliberately_not_watched_here`, which
   test-pins a false premise about an invariant with **22 re-confirmed live violations**. Fixing
   the docstring and inverting or deleting that test is a few lines and should land here,
   because the test is new here.

Two more I would take pre-merge as one-liners: `R5-I7` (`--ci` should imply `--no-memo`) and the
`NotImplementedError` half of `R5-MAJ1` (stop `--write` printing a success message for work it
does not do).

**Submission blockers — not merge blockers, route to ADR-010:** `R5-C2` (figure content;
**and note the corrected remedy — 29 of 124 shipped PNGs have no registry spec, so deleting the
`d11_/d12_` filter is necessary but not sufficient**), `R5-C3`, `R5-C4`, `R5-C5`, `R5-MAJ1`
(the real write path), `R5-MAJ2` (Stage 9's gate cannot fail), `R5-I2` (BibTeX), `R5-I3`,
`R5-I4`, `R5-I5`, `R5-I6`.

**On C1's re-diagnosis:** accepted on performance, **rejected as a retraction**. The register
row should read `🔧 PARTIAL`, not `🔁 RE-DIAGNOSED`. Change-scoping made the manual stages
cheap; it did not make any of them fire, the hook is still not in this repo, and all 99 commits
of this branch were made under warn-only enforcement because the branch is not `main`.
