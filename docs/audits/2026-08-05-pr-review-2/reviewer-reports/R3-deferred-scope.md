# R3 — deferred scope, ratchets and claim honesty

**Branch:** `infra/adr-009-validation-modularization` @ `19ddba6d` · **Base:** `main` @ `c2b597e1`
**Reviewer:** R3 · **Date:** 2026-08-05
**Lens:** what did this branch promise, defer, or claim that is not true?

> ⚠️ **Tree conditions during review.** Other reviewers were seeding mutations into the
> **production** tree concurrently. `git status` transitioned through
> `scripts/validation/checks/citations.py` (a `return CheckResult(passed=True)` short-circuit),
> `src/core/constants.py`, `papers/paper11_quantum_group/paper_draft.tex` and
> `scripts/validation/checks/lean_substrate.py` while I worked. **Every ratchet measurement
> below was taken while `git status --short` showed only `M lean/lean_deps.json.hash`** (see
> R3-I5 — that one file is dirty for a reason of its own). I re-checked status before and after
> each measurement block.

---

## 0. Verdict up front

**YES WITH FIXES.** Decided by **R3-MAJ1** and **R3-MAJ5** (two guards that report success
without measuring — the exact class this branch exists to close, reintroduced by the surface it
landed on 2026-08-05) and by **R3-MAJ2/3/4** (three canonical documents asserting, at HEAD,
things a later commit on this same branch made false).

None of the five is a *regression in what the default suite catches*. All five are cheap. But
this branch's entire thesis is that "a document describing a repaired guard as broken, or a
broken guard as fine" is a defect of the same class as a check that cannot fail — and it is
shipping five of them, three of which it wrote itself. Detail in §6.

---

## 1. Ratchets and ceilings — every one measured against live data

House rule: **the ceiling must equal the current measured population; slack is a ratchet that
cannot fire.** I measured all ten.

| ratchet | value | measured live | headroom | zero-headroom test? |
|---|---|---|---|---|
| `NATIVE_DECIDE_DECL_CLOSURE_CEILING` | 546 | **546** | 0 | ❌ none |
| `COUNT_LITERAL_CEILING` | 107 | **107** | 0 | ❌ none |
| `NUMERICAL_LITERAL_CEILING` | 116 | **116** | 0 | ❌ none |
| `ARISTOTLE_REGISTRY_UNRESOLVED_CEILING` | 14 | **14** | 0 | ❌ none |
| `LEGACY_DRAFT_UNRESOLVED_REF_CEILING` | 81 | **81** | 0 | ✅ `test_d5_prose_lean_refs.py:188` |
| `BIBITEM_TITLE_DRIFT_CEILING` | 7 | **7** DROP-WORD | 0 | ✅ `test_d5_citations.py:327` |
| `VACUOUS_STATEMENT_BASELINE` | 48 names | 30 (`vacuous_statement_audit`) + 23 (`proxy_body_audit`), **union 48, 0 dead** | 0 | ❌ none |
| `FIXTURE_ONLY_CEILING` | 55 | **55** (59 registered − 4 `PRODUCTION_SEEDED`) | 0 | ✅ `test_d5_mutation_obligation.py:692` |
| `AWAITING_CEILING` | 0 | **0** | 0 | ✅ `test_d5_mutation_obligation.py:637` |
| `CI_MIN_CHECKS_RUN` | 55 | 59 registered − 4 `CI_SKIP` = **55** | 0 arithmetically | ✅ `test_ci_mode.py:157` — **but it measures the wrong thing, see R3-MAJ1** |

**How verified.** `uv run --no-sync python scripts/validate.py --check <name>` for
`theorems` (`14 registry entries resolve to no Lean declaration … ceiling 14`),
`native_decide_regression` (`546 <= ceiling 546 (measured from lean_deps.json)`),
`count_literals` (`107 count-literal matches across 64 papers (ceiling 107)`),
`numerical_literals` (`116 inline literals … (ceiling 116)`),
`prose_theorem_reference_coverage` (`43 legacy drafts / 774 candidates — 81 unresolved, at or
under the frozen ceiling 81`), `bibitem_title_primary_source` (`7 DROP-WORD drift flag(s) / 58
NOT-FOUND advisory`), `vacuous_statement_audit` (`30 grandfathered`), `proxy_body_audit`
(`23 grandfathered`). `VACUOUS_STATEMENT_BASELINE`'s dead-entry count came from a script that
re-runs both legs' matching predicates and subtracts
(`scratchpad/measure_baseline.py`: `BASELINE size: 48 / matched by vacuous_statement_audit: 30 /
matched by proxy_body_audit: 23 / union matched: 48 / DEAD (match nothing): 0`).
`CI_SKIP`/floor arithmetic from a direct import of `validate._CHECKS` and `_config`.

**Result: no ratchet on this branch currently carries slack.** That is a genuinely good
outcome and I want it on the record before the findings. `CI_SKIP` names four real registered
checks and nothing else (`CI_SKIP not registered: []`). The two findings below are about
*durability* and about one ratchet that counts the wrong population.

---

## 2. MAJOR findings

### R3-MAJ1 — `--ci`'s coverage floor counts the registry, not what measured. The scenario its own docstring says it exists to catch is empirically green.

- **file:line** — `scripts/validation/_config.py:108-119`; `scripts/validate.py:227-239`, `:658-676`
- **What it claims** (`_config.py:110-118, verbatim`): *"Dropping the Lean toolchain from a runner
  makes the suite ~200 s faster and stops 7 checks that read `lean_deps.json` plus 3 that shell to
  `lake` from measuring anything — while the run still reports green. … So `--ci` FAILS when fewer
  checks execute than this. **A missing toolchain becomes a red build reading '48 of 55 ran'**, not
  a green tick."* Repeated at `validate.py:658-665` (*"A green tick over 48 of 59 is worse than no
  CI"*).
- **What it actually does.** `n_ran = len(results)`, and `run_checks` (`validate.py:231-239`)
  assigns `results[spec.name]` on **every** iteration — including the `except` path. `len(results)`
  is therefore the registry cardinality minus the `--check` filter minus `CI_SKIP`, and is
  **invariant under anything a missing toolchain does.** The floor can only fire if a check is
  *deleted from the registry*, which `test_check_count_is_frozen` already catches.
- **How verified** — three measurements:
  1. Monkeypatched every registered check to raise, then called `run_checks()`:
     `registered specs: 59 / len(results) with EVERY check raising: 59 / passed count: 0`.
     No toolchain failure can reduce the count.
  2. `lean/lean_deps.json` is **git-tracked** (`git ls-files lean/lean_deps.json` → present).
     So on a fresh clone with no `lake`, all eight `lean_deps.json` readers read the committed
     snapshot and *do* measure. The docstring's "stops 7 checks from measuring anything" is
     false on its face.
  3. Ran with the toolchain genuinely unreachable
     (`HOME=<scratch> PATH=<uv-dir>:/usr/bin:/bin`):
     - `--check lean_build` → **`✓ PASS … SKIPPED — lake not found`**
     - `--check axiom_closure_allowlist` → **`✓ PASS`** (see R3-MAJ5)
- **Blast radius.** A `--ci` run on a toolchain-less runner reports **"55 of 55 ran"**, all
  green, and the floor is silent — precisely the "absence of measurement rendered as success"
  the mode was built to prevent. Currently *unreachable*: `19ddba6d` retracted the workflow, so
  nothing invokes `--ci` (verified: no `.github/workflows`, no `--ci` in `scripts/*.sh` or
  `gate_precheck.py`). It becomes live the moment a runner is wired — which the assessment
  explicitly leaves as the operator's next step.
- **Settles it.** Count checks that *measured*: have `CheckResult` carry a "measured" flag, or
  have the floor assert on the set of checks that did not take a cannot-measure early return.
  Failing that, delete the two paragraphs of docstring that claim a capability the code lacks.

### R3-MAJ5 — the memo returns an affirmative PASS, with replayed measurement detail lines, when the Lean toolchain is gone. The key does not include the toolchain's existence.

- **file:line** — `scripts/validation/_memo.py`; key at
  `scripts/validation/checks/lean_toolchain.py:426-437`
- **Key composition** (verbatim): `lean_source_fingerprint()` + `toolchain_pin_fingerprint()` +
  `files_fingerprint([constants.py, update_counts.py])`, plus (`_memo.py:239`) the body's own
  source. **What is missing: whether `lake` / the `AxiomAudit` executable is reachable at all.**
- **How verified.** With `lake` unreachable (`HOME=<scratch> PATH=<uv-dir>:/usr/bin:/bin`),
  `--check axiom_closure_allowlist` printed:
  ```
  ✓ PASS  axiom_closure_allowlist: …
    ✓ memo — SKIPPED (cached) — Lean sources, toolchain pins, AXIOM_METADATA unchanged since the last PASS
    ✓ allowlist_size — 13 allow-listed axioms (3 core + 10 AXIOM_METADATA)
    ✓ allowlist — no declaration carries a non-allow-listed, non-native_decide axiom (Invariant #15 backstop clean)
  ```
  The last line asserts a live measurement of the axiom closure. **No `AxiomAudit` run
  occurred; `lake` did not exist.**
- **Fairness.** The memo *does* print a visible `SKIPPED (cached)` line, and the cached PASS was
  a real measurement when it was taken; the pre-memo behaviour on this path was also PASS
  (one of the five documented `axiom_closure_allowlist` cannot-measure PASS returns, ADR-009
  §Deferred item 4). So this is not a *new* false green.
- **What is new, and why it is MAJOR.** (a) The memo makes the honest "no lake" skip line
  **unreachable** — the output now positively asserts the check is clean rather than admitting it
  could not look. (b) It removes the last signal `--ci`'s floor could have keyed on. Together
  with R3-MAJ1, a toolchain-less CI run is green *and* claims Invariant #15 is verified.
- **Blast radius.** Every `validate.py` run on a machine without the Lean toolchain, including
  the "on-demand fresh-clone check" the branch says is the one thing a runner adds.
- **Settles it.** Add toolchain reachability (`shutil.which("lake")` presence, or the
  `AxiomAudit` binary's mtime/hash) to the key — a one-line addition to the existing
  `files_fingerprint` call. Or: evict/bypass the memo whenever the check would take a
  cannot-measure branch.

### R3-MAJ2 — `QA_QI_INFRASTRUCTURE_MAP.md` still asserts the retracted "all 59 checks are mutation-verified", in two places. The retraction commit touched this file and did not touch either.

- **file:line** — `docs/architecture/QA_QI_INFRASTRUCTURE_MAP.md:349` (table cell
  *"Checks with a test that would fail on a seeded defect | 5 of 59 | 10 of 59 | ✅ **59 of 59**"*)
  and `:395` (*"✅ **It has since been performed** (audit 2026-08-04, workstream W-D): all 59
  checks are mutation-verified…"*).
- **What is true.** `9a2a757f` — titled *"docs(qa-qi): RETRACT 'all 59 mutation-verified' — 4
  checks cannot fail (QI-31..34)"* — states in its body: *"RETRACTED across the audit tracker,
  RESUME_STATE and ADR-009."* The map is not in that list. The branch's own ratchet says
  `PRODUCTION_SEEDED` = **4 of 59** (`tests/test_d5_mutation_obligation.py:561-574, 584`).
- **How verified.**
  ```
  git log --oneline -1 -- docs/architecture/QA_QI_INFRASTRUCTURE_MAP.md  → 9a2a757f
  git show 9a2a757f -- docs/architecture/QA_QI_INFRASTRUCTURE_MAP.md     → ONE changed line,
      about the "eight always-pass checks" being a syntactic lower bound. Lines 349/395 untouched.
  rg -ni "retract|QI-3[1-4]|PRODUCTION_SEEDED" QA_QI_INFRASTRUCTURE_MAP.md → 1 hit, and it is
      the word "production artifact" in the Status header.
  ```
- **Blast radius.** The map is `Status: production artifact` and is on the mandatory-read list
  in this review's own BRIEF §6. A reviewer or a future session reading it for the D5 coverage
  ground truth gets **59 of 59** where the code says 4. This is the same defect the branch
  spent `9a2a757f` correcting elsewhere.

### R3-MAJ3 — the audit README contradicts its own retraction six lines later, and re-uses the "~17 Important" figure it opens by declaring wrong by 3×.

- **file:line** — `docs/audits/2026-08-04-qa-qi-infrastructure/README.md`
- **Contradiction 1.** `:20-25` — *"⚠️ **RETRACTED: 'all 59 checks are mutation-verified in both
  directions.'** … The stronger reading was mine and it was wrong."* → `:31-33` — *"**The headline
  result: `AWAITING_MUTATION_TEST` is EMPTY.** All **59 registered checks are mutation-verified**
  in both directions…"*. Same file, six lines apart, in the entry-point document.
- **Contradiction 2.** `:4-6` — *"⚠️ The *'~17 Important'* figure that stood in this file was
  never derived from the artifact and is wrong by ~3×."* → `:15` — *"~17 Important findings from
  the same review are filed, not fixed"*. The register itself says **53**.
- **How verified.** Direct read of `:1-40`; cross-checked against
  `FINDINGS_REGISTER.md:1` (*"all 53 actionable non-Critical"*) and the BRIEF's own account of
  the 17-vs-53 gap.
- **Blast radius.** `README.md` line 3 says **"START HERE"**. The two numbers a reader takes away
  from the first screen are both ones the same screen has already retracted.

### R3-MAJ4 — "57 of 59" is now 56 of 59, and `RESUME_STATE`'s QI-29 correction says the opposite of what the code does.

- **What changed.** `19ddba6d` **deleted the slow gate** on `paper_latex_compiles`
  (`papers_prose.py:598` — *"the slow-gate skip, which is gone as of 2026-08-05"*). The check now
  runs, and compiles, on a plain `validate.py`.
- **Measured, no flags, default mode:**
  - `--check paper_latex_compiles` → **`✗ FAIL … 20/21 bundle drafts clean … ✗ compile:D3 — D3: 2 fatal`**
  - `--check readiness_submission_gate` → **`✗ FAIL … 0 green / 3 yellow / 61 red across 64 papers`**
  - `--check bundle_metadata_matches_graph` → **`✗ FAIL … 21 blobs compared … 14 with drift`**
  → **three default reds ⇒ 56 of 59**, not 57.
- **Sites still asserting 57 of 59** (5, all at HEAD):
  `docs/architecture/.working-docs/RESUME_STATE.md:101`,
  `docs/architecture/QA_QI_INFRASTRUCTURE_MAP.md:328`,
  `docs/audits/2026-08-04-qa-qi-infrastructure/PR_REVIEW_2026-08-05.md:12` and `:26`,
  `docs/audits/2026-08-04-qa-qi-infrastructure/README.md:38`. Each also names the failing
  set as a **pair**.
- **The sharpest one** — `RESUME_STATE.md:276`, verbatim: *"⚠️ **It is NOT one of `validate.py`'s
  two reds in a default run** (audit QI-29). It sits behind the slow gate and reports *'SKIPPED
  (slow) — pass `--force-latex`'*, so a default run counts it as a PASS."* Both sentences are
  now false. This paragraph **is** QI-29's correction — the finding whose whole content was
  "the documented red checks were the wrong pair" — falsified by a later commit on the same
  branch. That is QI-29 recurring against its own fix.
- **Blast radius.** Every downstream consumer of "the branch is 57/59, two reds, both owned by
  the publication workstream" — which is the merge-readiness sentence in `PR_REVIEW_2026-08-05.md`
  §0. The third red is D3's LaTeX, and it is *also* publication-owned, so the conclusion survives;
  the measurement does not.

---

## 3. IMPORTANT findings

### R3-I1 — "`--strict` is passed by NO automated caller" is false in five live sites, two of them production module docstrings.

`2577fdbc` added `gate_precheck.py`'s `submission` stage (`scripts/gate_precheck.py:51`
`"submission": ["__strict__"]`, `:86` → `validate.py --strict --force-latex`). The register
records this as **✅ R4-I11 fixed**. Five sites were not updated:

| file:line | text |
|---|---|
| `docs/adrs/ADR-009-…md:752` | *"nothing automated passes the flag, and there is no CI at all (verified: no `.github/workflows`, **no submission-gate runner in `scripts/`**)"* |
| `docs/adrs/ADR-009-…md:765` | *"because nothing automated passes `--strict`, those five are exercised only if a human runs the flag"* |
| `docs/architecture/.working-docs/validation-module-migration-notes.md:359` | *"**`--strict` is passed by nothing automated** — not the commit hook, not `gate_precheck.py`"* |
| `scripts/validation/checks/citations.py:20-22` | *"⚠️ `--strict` is passed by NO automated caller (ADR-009 §Deferred item 6), so those strict paths are unreachable in practice today"* |
| `scripts/validation/checks/bundles_readiness.py:548` | *"(`--strict` remains unreachable in practice anyway — no automated caller passes it; §Deferred item 6.)"* |

- **How verified.** `rg -n "strict" scripts/gate_precheck.py` (lines 36-51, 86); `rg -n
  "§Deferred item 6"` across `scripts/`, `tests/`, `docs/`; read each site.
- **Why it matters beyond tidiness.** `src/core/constants.py:1418-1424`
  (`BIBITEM_TITLE_DRIFT_CEILING`) says the **opposite**, correctly: *"`gate_precheck.py
  submission` is now that caller, **which made the check's strict semantics load-bearing for the
  first time**."* The repo contradicts itself about whether a submission gate is enforced, and
  `citations.py` — the module that owns the check whose strict semantics became load-bearing —
  is on the wrong side of the contradiction, 900 lines above the ceiling that says so.
- **Also**: ADR §Deferred item 6's **DECLINE rests on this premise**. Its residue ("five strict
  legs are exercised only if a human runs the flag") is stale; three of the five now run in
  `gate_precheck submission`.

### R3-I2 — `papers_prose.py`'s module header says `paper_latex_compiles` "is still slow-gated"; the same file's function docstring says the gate was deleted.

- **file:line** — `scripts/validation/checks/papers_prose.py:21-23`, verbatim: *"It is still
  slow-gated behind `_cfg.FORCE_LATEX`, so a default full run **skips it** — skipped is not the
  same as advisory."* vs `:465-472` in the same file: *"**Always on, change-scoped.** ⚠️ CHANGED
  2026-08-05. This was *slow-gated*…"* and `:598` *"the slow-gate skip, which is gone as of
  2026-08-05."*
- **How verified.** Read both; confirmed empirically — a default `--check paper_latex_compiles`
  compiled and FAILED (§R3-MAJ4).
- **Why this one stings.** That header block ends with *"⚠️ This header said both 'return
  `passed=True` even after a real compile failure' until 2026-08-04 (audit finding QI-13), which
  was false."* The header was corrected once for describing this exact check wrongly, and has
  rotted again within a day, in the opposite direction.
- **Same class, one more site:** `scripts/validation/_config.py:9` — the flag table opener still
  reads *"`FORCE_LATEX` runs the slow-gated pdflatex check"*, contradicted by `:60-66` of the
  same file.

### R3-I3 — ADR §Deferred item 0 is marked ✅ but its sub-clause (d) — a named part of the fix — was never done. Re-confirms pass-1 **R1-I6** as still open.

- **What the ADR promises** (`ADR-009…md:558-564`, item 0(d)): *"`tests/test_validate_registry_
  contract.py::test_regenerators_precede_their_consumers` asserts only `counts_fresh` against
  `_COUNTS_CONSUMERS` … It has no knowledge of `lean_deps.json` consumers … `tables_fresh` and
  `claim_clusters_fresh` are declared in `_REGENERATORS` but are never asserted against any
  consumer. **Widening this property is part of item 0's fix, and it will fail on the current
  ordering — which is the point.**"*
- **What the code has.** `tests/test_validate_registry_contract.py:77-78` still reads
  `_REGENERATORS = ('counts_fresh','tables_fresh','claim_clusters_fresh')` /
  `_COUNTS_CONSUMERS = ('axiom_count_prose_consistency','inventory_index_autogen_fresh')`, and
  `:102-111` still asserts only `counts_fresh` against those two.
- **How verified.** `rg -n "_COUNTS_CONSUMERS|_REGENERATORS|def test_regenerators"
  tests/test_validate_registry_contract.py` + full read of `:70-112`.
- **Assessment.** The *substantive* half of item 0 (one `lean_deps` snapshot per full run) is
  genuinely done — `validate.py:594-611` calls `ensure_lean_deps_fresh()` on full runs only, and
  `tests/test_validate_lean_deps_snapshot.py` guards it. The ordering property may even be moot
  now for `lean_deps`. But the ADR names the widening as part of the fix and marks the item ✅
  anyway, and `tables_fresh`/`claim_clusters_fresh` still have zero asserted consumers.
- **Re-confirms pass-1 `R1-I6`** (*"`test_regenerators_precede_their_consumers` never widened;
  `_REGENERATORS` names two members it never asserts"*) — status ⬜ open in
  `FINDINGS_REGISTER.md:155`. **Still open at HEAD.**

### R3-I4 — 5 of the 10 ratchets have no zero-headroom test. The house rule is mechanized for half of the population it governs.

- **Without a "ceiling == measured population" assertion:** `COUNT_LITERAL_CEILING`,
  `NUMERICAL_LITERAL_CEILING`, `NATIVE_DECIDE_DECL_CLOSURE_CEILING`,
  `ARISTOTLE_REGISTRY_UNRESOLVED_CEILING`, `VACUOUS_STATEMENT_BASELINE`.
- **With one:** `LEGACY_DRAFT_UNRESOLVED_REF_CEILING`, `BIBITEM_TITLE_DRIFT_CEILING`,
  `FIXTURE_ONLY_CEILING`, `AWAITING_CEILING`, `CI_MIN_CHECKS_RUN`.
- **How verified.** `rg -ln "<CEILING>" tests/` for each, then read each hit;
  `rg -n "ZERO.headroom|tracks_the" tests/*.py` → 5 assertions, listed in §1's table.
- **Blast radius / calibration.** **No slack exists today** (§1) — this is a durability finding,
  not a live hole. But the five unguarded ones are exactly the ones the ADR and `constants.py`
  repeatedly cite as *"the house idiom"*, and `test_d5_mutation_obligation.py:692-700` states the
  precedent in its own docstring: *"`ledger_ids_resolve` sat at 67 against a population of 66 and
  so admitted one new dangling record silently."* A repair that removes one literal without
  lowering `COUNT_LITERAL_CEILING` reintroduces that shape and nothing notices.
- **Cost.** Each is 4 lines, modelled on `test_d5_citations.py:327`.

### R3-I5 — the committed `lean/lean_deps.json.hash` does not match the committed `.lean` sources, so item 0's new up-front refresh fires a full ExtractDeps on every fresh clone — and rewrites a **tracked** file on every full run.

- **Measured:**
  ```
  extract_lean_deps.compute_lean_hash()          → 5c500bf3cc4b9d92
  git show HEAD:lean/lean_deps.json.hash         → 2ea566be12c9ffa5
  worktree lean/lean_deps.json.hash              → 5c500bf3cc4b9d92   (M in git status)
  git ls-files lean/lean_deps.json{,.hash}       → BOTH TRACKED
  ```
- **Consequence.** `extract_lean_deps._needs_refresh()` (`:81-88`) compares stored vs computed
  and returns **True** on a clean checkout. `validate.main()` (`:608-611`) now calls
  `ensure_lean_deps_fresh()` unconditionally on every full run, so a clean checkout runs
  `_run_extraction()` — the 30-minute ExtractDeps, requiring `lake`. If `lake` is absent it is
  swallowed (`validate_helpers.py:158-161`, *"NEVER fail the run here"*) and every reader
  proceeds on the stale committed artifact, silently.
- **Attribution, measured.** The stale hash is **inherited**: the last commit touching
  `lean/SKEFTHawking/*.lean` is `c362a633`, and `git merge-base --is-ancestor c362a633 main`
  → true. `ensure_lean_deps_fresh` is **branch-introduced** (`be5ad87d` / `a8349c93`). So the
  branch converts an inherited, dormant inconsistency into a per-run cost and a dirty tracked
  file. The `M lean/lean_deps.json.hash` in my working tree at session start is that side effect.
- **Blast radius.** Contradicts item 0's own cost claim (*"the hash guard is 46 ms"* /
  *"Cost is zero on a run with no Lean change"*) and `_config.CI_MODE`'s fresh-clone analysis,
  which does not mention it. Any future runner pays a 30-minute extraction or silently reads a
  stale substrate on its first run.
- **Fix.** Regenerate and commit `lean/lean_deps.json.hash` (and `lean_deps.json` if it moves)
  in the merge commit, or stop tracking the hash file.

### R3-I6 — `VACUOUS_STATEMENT_BASELINE` grandfathers by **short name across the whole tree**, and nothing asserts the set has no dead entries.

- **file:line** — `scripts/validation/checks/lean_statements.py:483, 491` (`short =
  name.split(".")[-1]` … `elif short in BASELINE`) and
  `scripts/validation/checks/lean_substrate.py:431` (`if thm_name in BASELINE`).
- **Two consequences.** (a) A **new** thin theorem in **any** module whose last name component
  matches one of the 48 entries is silently grandfathered — the set is not module-pinned, and 48
  is a lot of short names (`chirality_obstruction`, `circuit_depth_two`, `bag_weight_real`…).
  (b) The constant's own docstring says *"The set may only SHRINK"*, but nothing enforces that a
  removed theorem takes its baseline entry with it; a dead entry is exactly the loophole in (a).
- **How verified.** Read both matching sites; ran the union/dead-entry script (§1) —
  **0 dead entries today**, so this is latent, not live. `rg -ln VACUOUS_STATEMENT_BASELINE
  tests/` → `test_substrate_integrity_gates.py`, `test_d5_lean_statements.py`; neither asserts
  set-size-vs-population.
- **Fix.** A `test_the_baseline_has_no_dead_entries` asserting `set(BASELINE) == matched_union`,
  4 lines, using the same predicates the two checks use.

### R3-I7 — a wrong §Deferred ordinal is live in `src/core/constants.py`. Re-confirms pass-1 **R3-I1** as still open.

- **file:line** — `src/core/constants.py:2469`: *"# PAPER-LITERAL RATCHETS (**ADR-009 Phase 3
  item 2**, 2026-08-03)"*. The paper-literal ratchets are §Deferred **item 3** (the always-pass
  dispositions — see the item-3 table, `ADR-009…md:596-600`); item 2 is
  `readiness_submission_gate`. The check bodies that implement these ratchets cite it correctly
  (`papers_prose.py:272, 373` — *"RATCHET (ADR-009 §Deferred item 3)"*), so `constants.py` is the
  outlier.
- **How verified.** `rg -n "ADR-009 (§Deferred |Phase 3 )?item [0-9]|§Deferred item [0-9]"` over
  `scripts/ tests/ src/ docs/` (excluding `docs/audits/`, `papers/`), then adjudicated each of the
  ~40 hits against the ADR's canonical 0–7 list. `constants.py:2469` is the only mismatch I
  found in code.
- **Re-confirms pass-1 `R3-I1`** (*"QI-16 marked FIXED; 4 wrong §Deferred ordinals remain outside
  `scripts/validation/`"*) — ⬜ open at `FINDINGS_REGISTER.md:172`. **Still open**, though my
  sweep found **one**, not four — the count is a claim and I am re-measuring it as one. The
  ADR's own §Deferred preamble is explicit that *"every cross-reference must carry the §Deferred
  ordinal"*, and the collision it warns about is live in the canonical constants file.

---

## 4. MINOR findings

- **R3-MIN1 — mandatory-read docs carry check counts off by 2×–3×.**
  `README.md:410` — *"`uv run python scripts/validate.py` **# ~28 cross-layer validation
  checks**"*; `SK_EFT_Hawking_Inventory_Index.md:609` — *"full validation suite (**21 checks**)"*;
  `:87` — *"`validate.py` **33/33 ALL CHECKS PASSED**"*. Live count is **59**
  (`--list | grep -c '^  '` → 59). Inherited, not branch-introduced — but the branch touched
  `SK_EFT_Hawking_Inventory_Index.md` in **6 commits** (`19ddba6d`, `4a16826e`, `76bbf599`,
  `6c89beaa`, `7d2fbc4f`, `c09e5532`) without correcting the number, and `Inventory_Index` is on
  the mandatory-read list. `README.md` was not touched by the branch at all.

- **R3-MIN2 — a test docstring asserts, in the present tense, the behaviour its own branch deleted.**
  `tests/test_gate_precheck.py:117-118`: *"⚠️ Without `--force-latex`, `paper_latex_compiles`
  **returns** PASS with 'SKIPPED (slow)'"*. The assertion it justifies (s13 passes
  `--force-latex`) is still correct; the stated reason is not. Same class as R3-I2.

- **R3-MIN3 — `BIBITEM_TITLE_DRIFT_CEILING`'s docstring quotes a NOT-FOUND population of 62; live is 58.**
  `src/core/constants.py:1432` — *"they promoted the NOT-FOUND class (**62 live entries** …)"*.
  Measured: `--check bibitem_title_primary_source` → *"7 DROP-WORD drift flag(s) / **58**
  NOT-FOUND advisory flag(s)"*. The **ratcheted** number (7) is exact; the incidental one drifted.

---

## 5. ADR-009 §Deferred items 0–7 — verified against code

The brief says *"the tracker claims 4 of 8."* **That figure is stale.** Both trackers at HEAD
claim **8 of 8**: `ADR-009…md:445-448` (*"Status, verified 2026-08-04: ALL 8 DISPOSITIONED"*)
and `RESUME_STATE.md:250` (*"COMPLETE — 8 of 8 dispositioned"*). The "4 of 8 (1,2,3,7 done;
0,4,5,6 open)" reading reflects the state before `be5ad87d`. My verdict, from code:

| item | claim | verified against code | R3 verdict |
|---|---|---|---|
| **0** | 1st half FIXED (one `lean_deps` snapshot/run), 2nd half DECLINED | `validate.py:594-611` calls `_H.ensure_lean_deps_fresh()`, full runs only; `validate_helpers.py:108-161`; `tests/test_validate_lean_deps_snapshot.py` present | ✅ **substantively done** — ⚠️ sub-clause (d) never done (**R3-I3**); operational cost claim false (**R3-I5**) |
| **1** | native_decide ratchet measures live substrate | `lean_toolchain.py:114-160` — computes from `native_decide_decls(_H.load_lean_deps())`; `counts.json` used only as a `counts_drift` warning; absent `lean_deps` → **FAIL**, not pass | ✅ **done, and correctly hardened** |
| **2** | `readiness_submission_gate` hard-fails | ran it: **`✗ FAIL — 0 green / 3 yellow / 61 red across 64 papers`** | ✅ **done** |
| **3** | 8 always-pass checks dispositioned individually | `paper_latex_compiles` **FAILs** on D3 (measured); `count_literals` 107/107 and `numerical_literals` 116/116 are live ratchets (measured); 4 advisories kept with reasons | ✅ **done** — ⚠️ its documentation has since rotted (**R3-MAJ4**, **R3-I2**) |
| **4** | type change DECLINED, generator CLOSED with a ratchet | `tests/test_cannot_measure_baseline.py` present and green; ratchets **both** directions (`:192` new-PASS fails, `:206` stale-baseline fails) + a scanner-seam guard (`:177`, `len(sites) >= 30`) | ✅ **done — the best-built ratchet on the branch** |
| **5** | DECLINE the merge; premise measured false | premise re-verified: `count_literals` *is* a ratchet now (`papers_prose.py:373-396`), and `axiom_count_prose_consistency` is a value comparison, not a density count | ✅ **honest decline** |
| **6** | DECLINE the filed remedy; residue "unenforced" | `gate_precheck.py:51,86` now passes `--strict`. The item's stated premise and residue are **false at HEAD** | ⚠️ **disposition stands, prose does not** (**R3-I1**) |
| **7** | VERIFIES resolver guarded, both halves | `build_graph.py:3839-3880` — the guarded Lean branch is present with both rules (module-alias roots; no tail-resolution of dotted refs) and the corrected 144-of-536 measurement inline | ✅ **done** |

**Net: 8 of 8 dispositioned is accurate.** Two carry defects in what they *say* (0, 6); none is
falsely marked done on the substance.

---

## 6. Pass-1 findings I re-confirm as still OPEN

Named by id, per BRIEF §6, so reconciliation is not guesswork:

| pass-1 id | register status | R3 re-confirmation |
|---|---|---|
| **R1-I6** | ⬜ open (`:155`) | ✅ **re-confirmed open** — see R3-I3. `_COUNTS_CONSUMERS` unchanged; `tables_fresh`/`claim_clusters_fresh` still assert against nothing. |
| **R3-I1** (pass 1) | ⬜ open (`:172`) | ✅ **re-confirmed open**, with a **re-measured count: 1, not 4**, in code — `src/core/constants.py:2469`. See R3-I7. |
| **R3-C2** (pass 1) | 🔧 PARTIAL (`:35`) | ✅ **re-confirmed PARTIAL** — `PRODUCTION_SEEDED` = 4, `FIXTURE_ONLY_CEILING` = 55, both measured, zero headroom. The ratchet is real; the sweep is 4 of 59. |
| **R3-I9** (pass 1) | ⬜ open (`:180`) | ✅ **re-confirmed open** — the map's "eight always-pass" annotation still ends *"A semantic-reachability re-measurement has not been run."* Nobody has run it. |
| **R5-C1** | 🔁 re-diagnosed (`:37`) | ⚠️ **the re-diagnosis's remedy has its own hole** — R3-MAJ1 + R3-MAJ5. The mode built to make CI safe cannot detect the exact scenario it was built for. |

I did **not** re-measure R5-C2…C5, R4-I6, R4-I8, or the R6/R2 test-quality items — outside this
lens; other reviewers have them.

---

## 7. Verdict

# YES WITH FIXES

**Merge blockers** (cheap, and all five are the branch's own signature defect turned inward):

1. **R3-MAJ1** — fix the `--ci` coverage floor to count checks that *measured*, or delete the two
   docstring paragraphs claiming a capability the code does not have. Shipping a guard whose
   documentation describes a scenario it demonstrably cannot catch is the thing this branch
   exists to stop.
2. **R3-MAJ5** — add toolchain reachability to the memo key (one line), or bypass the memo when
   the check would take a cannot-measure branch.
3. **R3-MAJ2** — retract the two "59 of 59 mutation-verified" assertions in
   `QA_QI_INFRASTRUCTURE_MAP.md:349, :395`, the file `9a2a757f` meant to include and did not.
4. **R3-MAJ3** — reconcile `docs/audits/2026-08-04-qa-qi-infrastructure/README.md` with itself
   (`:31` vs `:20`; `:15` vs `:4`).
5. **R3-MAJ4** — re-state 57 of 59 as **56 of 59** at all five sites, and rewrite
   `RESUME_STATE.md:276`, which now asserts the opposite of what the code does.

**Should also land with the merge** (each ≤ 15 minutes): R3-I1 (five `--strict` sites,
two of them shipped module docstrings), R3-I2 (`papers_prose.py:21-23` +
`_config.py:9`), R3-I5 (commit a matching `lean_deps.json.hash`), R3-I7 (one ordinal).

**Not merge blockers, route to ADR-010:** R3-I4 and R3-I6 (durability of ratchets that carry no
slack today), R3-MIN1…3, and the item-6 residue's substance — whether the five uncovered
`--strict` legs get ReadinessGates.

**What this branch got right, and it is the larger half.** Ten ratchets, **zero slack in any of
them**, measured independently against live data. `test_cannot_measure_baseline.py` and
`test_d5_mutation_obligation.py` are ratchets that bite in *both* directions and guard their own
scanner seam — the best-built enforcement I found. All eight §Deferred items are genuinely
dispositioned, and the two DECLINEs carry real measurements rather than assertions. The
substance is sound; what is failing is the layer that describes it, and it is failing fastest at
the documents this repo makes mandatory reading.
