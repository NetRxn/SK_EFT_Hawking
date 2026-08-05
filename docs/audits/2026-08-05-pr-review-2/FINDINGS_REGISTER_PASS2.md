# PR-review pass 2 — findings register

**Source of truth:** [`reviewer-reports/`](reviewer-reports/) — each reviewer's own file, written
by the reviewer. This file is the tracker; when the two disagree, the report wins.

**Status:** ✅ fixed · 🔧 in progress · ⬜ open · 🔁 superseded/duplicate ·
❌ not reproduced (measured, wrong as stated) · ↪️ routed to ADR-010

> Standing rule, applied here to my own work as well: **a filed finding's count, consumer and
> effort are CLAIMS.** Every entry below is re-measured by the lead before it is actioned, and
> the measurement is recorded next to it.

---

## ⛔ CRITICAL

### R5-C1 — `validate.py --ci`'s coverage floor CANNOT FIRE ✅ **CONFIRMED by the lead**

**This is my own defect, introduced earlier in this same session**, in the mechanism I described
as *"the point of the mode"*. It is the audit's central defect class — absence of measurement
rendered as success — reproduced inside the guard built to prevent it.

**The arithmetic.** `run_checks` (`scripts/validate.py:227`) writes `results[spec.name]` for
**every** registered spec, unconditionally — an exception handler even records a result on
crash. So `len(results)` counts *checks invoked*, never *checks that measured*:

```
registered checks : 59
CI_SKIP           : 4
=> n_ran ALWAYS   : 55
CI_MIN_CHECKS_RUN : 55
floor fires when n_ran < floor -> False
```

**Reproduced in production**, two independent paths:

| path | mechanism | evidence |
|---|---|---|
| **B** — pre-existing | `LEAN_PROJECT_DIR=/nonexistent LAKE_PATH=/nonexistent … --check axiom_closure_allowlist --no-memo` | **✓ PASS**, `Overall: 1/1 checks passed` |
| **A** — added today | same, *without* `--no-memo` | **✓ PASS** via `SKIPPED (cached)` — the memo replays a verdict measured when the toolchain was present |

Path A is a second finding in its own right and R5 did not separate it: **`--ci` does not imply
`--no-memo`**, so a runner with a warm cache can replay a PASS that was measured on a machine
that had `lake`. The memo key covers the Mathlib *pins*, not the *presence* of the toolchain.

**What the docs claim, and it is false.** `_config.py`'s `CI_MIN_CHECKS_RUN` docstring and
`CI_DEFAULTS_ASSESSMENT.md` both promise *"a missing toolchain becomes a red build reading
'48 of 55 ran', not a green tick"*. It cannot. R5 also notes the guarding test
(`test_a_shrunken_suite_FAILS_even_though_every_check_passed`) seeds **registry shrinkage**, not
toolchain absence — so by QI-30's own criterion it is a fixture-shaped mutation test that
"proves" a property the production path does not have.

**Severity.** R5 files it CRITICAL and calls it a merge blocker by the brief's definition
(a guard that cannot fire). Mitigating: `--ci` currently has **no caller** — no workflow file
exists — so nothing in the harness relies on it today. It is latent, not active. It still ships
a guard that cannot fire plus documentation asserting it can, which is the worse half.

**Fix direction (not yet applied — pending the other five reviewers, to avoid reviewing a
moving target):**
1. count checks that **measured**, not checks invoked — an additive `CheckResult.measured:
   bool = True` (additive, so the `passed` contract read by `--json` / `gate_precheck.py` /
   `pre-commit-sync.sh` is untouched, unlike the third-`passed`-state ADR-009 §Deferred item 4
   declined), set `False` at the cannot-measure return sites that
   `tests/test_cannot_measure_baseline.py` **already enumerates by AST**;
2. `--ci` implies `--no-memo` (one line) — closes path A;
3. assert provisioning directly in `--ci` (`lake` resolves, `lean_deps.json` present) and fail
   fast, which is what the floor was really trying to say;
4. correct the two documents that assert the impossible behaviour.

---

## 🔶 MAJOR — R5, all three verified by the lead

### R5-MAJ3 — Invariant #10 is unenforced, and this branch shipped a test that PINS the gap ✅ **CONFIRMED, count corrected**

The nastiest of the three, because it fuses the documentation defect with the test defect.

**Measured by the lead** (AST-ish scan attributing each `set_option` to the declaration it
precedes): **23 violations across 4 files**, every one attached to a `theorem` —
`Uqsl2AffineHopf.lean` (11), `Uqsl3Hopf.lean` (8), `QuantumGroupAntipode.lean` (2),
`QuantumGroupCoproduct.lean` (2). R5 filed 22; **same 4 files**, one occurrence differs in
attribution. A further **8** occurrences attach to no declaration within 12 lines — file-level
`set_option` blocks, which apply to *every* proof below them and are arguably worse than a
proof-body option; nobody has filed those.

**Nothing enforces it.** `elaboration_knob_watchlist`'s regex
(`lean_toolchain.py:605`) is
`set_option\s+(maxRecDepth|synthInstance\.maxSize|synthInstance\.maxHeartbeats)\s+(\d+)` —
bare `maxHeartbeats` is deliberately excluded, and `:591` explains why: *"forbidden outright by
Invariant #10"*, i.e. handled elsewhere. It is handled nowhere. `rg maxHeartbeats scripts/`
returns only that check's own docstring and exclusion list.

**And the branch pinned it.** `15edc340` (2026-08-04) added
`tests/test_d5_lean_toolchain.py:397::test_maxHeartbeats_is_deliberately_not_watched_here`,
whose docstring reads *"Invariant #10 forbids `maxHeartbeats` in a proof body OUTRIGHT and is
**enforced elsewhere**."* Closing the gap now **breaks a passing test whose docstring asserts
the gap is correct** — which is the strongest form of this audit's core defect: a false claim
with a green test defending it.

### R5-MAJ2 — Stage 9's gate cannot fail ✅ **CONFIRMED**

`gate_precheck.py`'s `s9` stage runs exactly one check, `viz_consistency`, and that check ends
(`notebooks.py:198-199`):

```python
    # Always passes — these are advisory warnings
    return CheckResult(passed=True, details=details)
```

So the deterministic precheck guarding the Stage-9 figure-reviewer dispatch returns rc=0
unconditionally. Its own docstring opens *"Visualization consistency warnings (advisory, always
passes)"* — honest at the function level, and nobody checked what depended on it.

### R5-MAJ1 — Invariant #8's human-verification tier has a hard gate and no way to satisfy it ✅ **CONFIRMED**

`--strict` gates on human-verified provenance and (as of 2026-08-05) finally has a caller
(`gate_precheck submission`). But nothing can *set* the field:

- `scripts/provenance_dashboard.py:5451` — `# TODO: implement file rewriting`;
- `:1273/:1278` mutate `entry['human_verified_date']` **in memory only**, then the UI renders a
  green `HUMAN VERIFIED` badge;
- `docs/verification_log.jsonl` — **ABSENT**.

78 of 206 parameters unverified, and the gate that blocks on them cannot be satisfied through
the tool built for it. ⚠️ One thread the lead has not closed: `scripts/wave2_flip_provenance.py`
also references `human_verified_date` and may be a real writer — check before costing the fix.

---

## 🔶 MAJOR — R6, against the memo shipped today. Both verified by the lead.

**R5 and R6 reached `--ci`'s broken floor independently** (R5-C1 = R6-C1), from different
directions. R6 then found two holes in the memo key — exactly what BRIEF §5 asked for, and both
are real.

### R6-MAJ1 — the memo caches a FAIL-OPEN SKIP as a genuine PASS, permanently ✅ **CONFIRMED, worse than filed**

The single worst thing landed today. Demonstrated end to end by the lead:

| step | state | result |
|---|---|---|
| 1 | `LEAN_PROJECT_DIR=/nonexistent LAKE_PATH=/nonexistent` | check returns **PASS**, detail `SKIPPED — /nonexistent/…/AxiomAudit.lean not found` — **and the memo stores it** |
| 2 | **toolchain fully restored** | **PASS in 0.1 s**, replaying `SKIPPED — /nonexistent/… not found` — a path no longer in use |

The axiom closure is then never measured again until some *other* input happens to move the key.
A transient inability to measure is converted into a permanent green verdict.

**Why my guard failed.** `_memo.memoized` documents guard 3 as *"Only PASS is cached… a failing
check re-runs every time."* That guard is defeated by a category error I made: **a fail-open SKIP
IS a PASS.** `CheckResult` has no way to say "I did not measure", so the memo cannot tell the two
apart — which is the same root cause as R5-C1's floor counting invoked-not-measured.

⚠️ `gate_precheck s13` reads through the memo (it does not pass `--no-memo`), so this reaches the
wave-close gate, not just ad-hoc runs.

### R6-MAJ2 — `lean/SKEFTHawking.lean` is NOT in the key ✅ **CONFIRMED**

`_memo.lean_source_fingerprint()` globs `lean/SKEFTHawking/**/*.lean` → **2,039 files**. The root
aggregate `lean/SKEFTHawking.lean` is a **sibling of that directory, not inside it** — 5,226
lines, 365 KB, and it is the file whose `import` lines determine which modules are in the
environment `AxiomAudit` walks. Verified: `target in files` → **False**.

So adding or removing an `import SKEFTHawking.Foo` changes the verified surface and **does not
move the key**. A textbook "the key misses an input", in code shipped with four guards written
against exactly that.

### THE SHARED ROOT CAUSE, and the one fix

R5-C1, R6-C1, R6-MAJ1 are three faces of one missing distinction: **a check that could not
measure is indistinguishable from one that measured and passed.** Fix once:

1. `CheckResult.measured: bool = True` — **additive field**, so the `passed` contract read by
   `--json`, `gate_precheck.py` and `pre-commit-sync.sh` is untouched. (ADR-009 §Deferred item 4
   declined a third *value of `passed`* for that reason; a separate field does not attract the
   objection.)
2. Set `measured=False` at the cannot-measure return sites — the population
   `tests/test_cannot_measure_baseline.py` **already enumerates by AST** and freezes.
3. `_memo.memoized`: refuse to cache when `not result.measured` → kills R6-MAJ1.
4. `--ci` floor: count `sum(r.measured for r in results.values())` → kills R5-C1/R6-C1, and the
   docstring's promised *"48 of 55 ran"* becomes achievable.
5. `--ci` implies `--no-memo`; add `lean/SKEFTHawking.lean` to `lean_source_fingerprint`.

### R6-M1 — the atlas count has now been measured wrong THREE times, mine included ❌ **my re-count was also wrong**

Pass 1 filed *29 module-only obstructions from 3 modules*; the lead's re-count agreed; **both
were wrong for the same reason**. R6: `rec["name"]` in `lean_deps.json` is **fully qualified**, so
`_NOGO_RE` matches the *namespace*, not the declaration. Live atlas: **454 obstructions, 45
registered, 409 unregistered — of which 144 are namespace/module-only from 14 modules.** R6
reproduces 29/3 exactly under the old predicate, which is how it identified the predicate as the
bug.

R6 also **corrects pass 1 in the project's favour**: the claim *"the digest filters, the CLI does
not"* is wrong — the CLI slices `[:8]` against a registered-first sort with 45 registered and tags
rows `[naming-only, unregistered]`. Latent, not live. The digest filter is intact but has **0
tests**.

*A count that three independent measurements got wrong the same way is a defect in the predicate,
not in the counters.*

---

## 🔶 MAJOR — R3, documentation honesty. Verified by the lead.

**Convergence note.** R3-MAJ1 = R5-C1 = R6-C1 (the floor), and R3-MAJ5 = R6-MAJ1 (the memo
replaying a fail-open skip). **Three independent reviewers on the floor, two on the memo.** No
further adjudication needed; these are facts.

R3 adds the good news first: **all ten ratchets measured against live data have ZERO slack** —
`NATIVE_DECIDE_DECL_CLOSURE_CEILING` 546/546, `COUNT_LITERAL_CEILING` 107/107,
`NUMERICAL_LITERAL_CEILING` 116/116, `ARISTOTLE_REGISTRY_UNRESOLVED_CEILING` 14/14,
`LEGACY_DRAFT_UNRESOLVED_REF_CEILING` 81/81, `BIBITEM_TITLE_DRIFT_CEILING` 7/7,
`VACUOUS_STATEMENT_BASELINE` 48 names with **0 dead**, `FIXTURE_ONLY_CEILING` 55/55. The house
idiom is being honoured. (Lead correction to my own earlier statement: `FIXTURE_ONLY_CEILING`
lives in `tests/test_d5_mutation_obligation.py:584`, not `src/core/constants.py`.)

### R3-MAJ2 — "all 59 checks mutation-verified" is STILL asserted after retraction ✅ **CONFIRMED**

`docs/architecture/QA_QI_INFRASTRUCTURE_MAP.md`:
- `:349` — `| Checks with a test that would **fail on a seeded defect** | **5** of 59 | 10 of 59 | ✅ **59 of 59** |`
- `:395` — *"all 59 checks are mutation-verified"*

The branch's own ratchet says the opposite: `FIXTURE_ONLY_CEILING = 55`, i.e. **4 of 59 are
production-seeded**. R3 notes the retraction commit `9a2a757f` *touched this file* and changed one
unrelated line — the retraction was written and the contradicted table left in place.

### R3-MAJ3 — the audit README retracts and re-asserts the same claims ✅ **CONFIRMED**

Within one file: `:20` retracts *"all 59 checks are mutation-verified in both directions"*, `:31`
re-asserts *"All 59 registered checks are…"*. Same shape for `~17 Important` (`:4` vs `:15`).

### R3-MAJ4 — my change today falsified QI-29's own correction ✅ **CONFIRMED, and it is the sharpest finding of the pass**

QI-29 was the finding *"a claim written true and left standing after the surrounding behaviour
moved."* Its correction, `docs/architecture/.working-docs/RESUME_STATE.md:276`, reads:

> *"⚠️ It is NOT one of `validate.py`'s two reds in a default run (audit QI-29). It sits behind
> the slow gate and reports 'SKIPPED (slow)', so a default run counts it as a PASS."*

**I deleted that slow gate this morning.** `paper_latex_compiles` is now a third default red.
`:101` still reads *"57 of 59 passed, 2 failed"* — now 56 and 3. Five documents carry `57 of 59`.

I updated the pass-1 audit README's QI-29 entry when I made the change and **stopped there**,
without sweeping for the same claim elsewhere. The defect the audit is named for, committed by
the audit's author, inside the correction written to prevent it. Nothing rebuts that.

### R3 — other findings to action
- *"`--strict` has no automated caller"* is **false in 5 live sites**, two of them shipped module
  docstrings, and contradicts `constants.py`'s own correct note.
- The committed `lean/lean_deps.json.hash` **does not match** the committed `.lean` sources, so
  §Deferred item 0's up-front refresh fires a **full ExtractDeps on every fresh clone**.
  (⚠️ Lead note: my working tree has carried `M lean/lean_deps.json.hash` uncommitted all
  session — likely the same root cause. Investigate before fixing.)
- **5 of 10 ratchets have no zero-headroom test.**
- §Deferred "**4 of 8**" is **STALE** — both trackers claim 8 of 8 and R3 verified all eight
  against code. Substance holds; items 0 and 6 carry prose defects. ⚠️ My own memory note says
  "4 of 8" and must be corrected.

### ⚠️ Process hazard this pass exposed

R3 reports: *"other reviewers were seeding production mutations concurrently; all my
measurements were taken on an otherwise-clean tree."* Running mutation-seeding reviewers
(R2, R4) **concurrently** with measuring reviewers (R1, R3) risks one observing another's seeded
defect as a real finding. R3 handled it; that it noticed at all is luck. **Serialize seeding
reviewers from measuring ones next pass** — a brief-level fix, filed against the process.

---

## 🔶 MAJOR — R1, architecture. Verified by the lead.

R1 confirms the split itself is sound, by AST scan: **12 modules (398–1024 lines), zero
duplicated helpers, zero duplicated regexes, zero dead constants, zero verdicts
computed-and-discarded at a function tail.** H3, H4, H5 correctly implemented. The
`SystemExit`-in-a-library fix and the `build_graph` / `readiness_gates` / `bundle_readiness` /
`atlas_view` repairs are each correct and testable.

*"The weakness is concentrated in `_memo.py`, added 2026-08-05, and it fails in the branch's own
signature way."* That is the correct summary and I accept it.

**Convergence tally — this is now beyond dispute:**

| defect | independent reviewers |
|---|---|
| `--ci` floor cannot fire | **4** — R5-C1, R6-C1, R1-MAJ2, R3-MAJ1 |
| memo caches a cannot-measure PASS | **4** — R6-MAJ1, R1-MAJ1, R3-MAJ5, (lead reproduced) |

### R1-MAJ3 — `source_fingerprint` hashes only the `def`, so module-level state is OUTSIDE the key ✅ **CONFIRMED — the third hole**

`_memo.source_fingerprint` calls `inspect.getsource(fn)`, which returns **only the function's own
text**. Every module-level constant, regex and helper the body reads is therefore outside the key
— while the docstring I wrote claims it covers *"editing the check — including editing what it
reads"*. It does not.

**Verified by the lead** with a line-count-preserving in-place mutation of
`_DOCSTRING_STRICT_FAMILIES` — the constant that decides **FAIL vs advisory** for
`lean_docstring_refs_resolve`:

```
key before: 2b0ae907a6a826e9
key after : 2b0ae907a6a826e9     <- identical
```

So flipping a check's fail-vs-warn switch leaves its cached verdict in place. One-line fix:
`inspect.getsource(inspect.getmodule(fn))`.

⚠️ **Lead process note.** My *first* attempt to reproduce this printed *"key moved (R1 wrong)"*
and I nearly recorded the finding as not-reproduced. The probe was contaminated: it inserted a
line, which shifted the function's `firstlineno`, so `getsource` returned differently-offset text
for a reason unrelated to the claim. **A failed reproduction is itself a measurement that can be
wrong** — the same discipline this register applies to reviewers applies to the lead rejecting
them.

### R1 — the three memo-key holes, together

| # | hole | finder |
|---|---|---|
| 1 | fail-open SKIP cached as a genuine PASS, replayed after the cause is fixed | R6-MAJ1 / R1-MAJ1 / R3-MAJ5 |
| 2 | `lean/SKEFTHawking.lean` (root aggregate, 5,226 lines) outside the glob | R6-MAJ2 |
| 3 | module-level constants outside `source_fingerprint` | R1-MAJ3 |

Four guards were written against exactly this failure and three holes shipped anyway. The
guards were not wrong; they were **guarding the wrong layer** — all four police *how the cache
is used*, none audits *whether the key spans the inputs*.

### R1 — IMPORTANT to action
- BinOp path-alias gap — re-files pass-1 `R3-I5` with a measured **5 sites**, two sitting
  directly under a docstring denying they exist.
- `--strict` reachability contradiction between two files **in the same diff**.
- The commit gate's three check names are **not validated against the registry** — a rename
  gives a silent SKIP. `CI_SKIP` has exactly that test; the commit gate, which can hard-block
  `main`, does not.
- Paper 15 Table 2 is now numbered by source-file name — i.e. by the ordering H3 declares
  non-semantic (`main` row 1 = `formulas`, HEAD row 1 = `bundle_figure_integrity`).

### R1 — explicitly NOT a merge blocker (and I agree)
`validate.py` now exits 1 on a clean tree (`paper_latex_compiles` → D3; `readiness_submission_gate`
→ 61 red). **Both previously returned PASS while measuring the same reality.** That red belongs
to the paper corpus → ADR-010, not to this diff.

### ⚠️ Operational — a live mutation was left in the production tree
R1 reported `prose_lean_refs.py` dirty with an injected
`return CheckResult(passed=True, details=[])` at `:731`, short-circuiting
`theorem_name_embedded_citations` to an unconditional PASS — another reviewer's probe, not
reverted. **Lead reverted it and verified the check is live again** (`3 year-token declaration
names / 0 mismatches`). Compounds the concurrency hazard R3 flagged: seeding reviewers must be
serialized from measuring ones, and must restore in a `finally`.

---

## 🔴 R4 — enforcement efficacy. **VERDICT: NO — not safe to merge.**

32 findings (7 MAJOR · 21 IMPORTANT · 4 MINOR), 1,302 lines. Headline measurement: of 59
registered checks, **11 cannot fail on the defect they advertise**, and 24 more can fail only on
a narrowed / ratcheted / `--strict`-only sliver. Five of the eleven are `--strict`-only, and
`--strict` has one manual caller.

This is the same lens that returned "No" in pass 1. It returns "No" again, and the reason has
changed: pass 1's four blockers were fixed; **the new blockers are the code I added today.**

### R4-MAJ1 — the memo, with the sharpest detail yet ✅ (5th independent confirmation)

`axiom_closure_allowlist` has **six** return paths yielding `passed=True` without measuring —
including `if result.returncode != 0`. R4 ran it with `LAKE_PATH=/nonexistent/lake`, cached the
PASS-SKIP under key `667d2fce…`, and showed that key is **byte-identical to the one holding the
developer's real measurement**. Restore lake → the next run replays the skip in **0.07 s**.

**⚠️ TRIGGER RE-DERIVED 2026-08-05 (operator correction) — I had this wrong.** R4 and I both
framed the trigger as the published clean-baseline step, `rm -rf .lake/build && lake build
SKEFTHawking.ExtractDeps`, and I repeated it in the fix commit. **That step is deliberately
rare** — toolchain bumps and major structural changes only, per `feedback_clean_rebuild_cadence`
— so it is a poor headline and overstates how often this fires.

The real trigger is more mundane: **any environment where `lake` is not resolvable when
`validate.py` runs.** `_resolve_lake()` tries `LAKE_PATH`, then `~/.elan/bin/lake`, then `PATH`;
`scripts/pre-commit-sync.sh:56` guards `command -v lake` *precisely because* "git hooks run in a
minimal env (GUI clients / non-login shells) where uv/lake are NOT on PATH". Live candidates:

- a **worktree slot** (`.claude/worktrees/wt1|2|3` all exist) running validate without elan on PATH;
- a GUI-launched or non-login shell;
- a fresh clone before `elan` setup;
- a mis-set `LAKE_PATH`.

⚠️ The commit gate itself is **not** a poisoning path — `pre-commit-sync.sh` runs only three
named checks (`formula_grounding`, `placeholder_not_cited`, `native_decide_regression`), none
memoized.

**Severity is unchanged and does not depend on the frequency claim:** once it happens the green
verdict is permanent and silent, surviving until some unrelated input moves the key. What
changes is that I should not have led with a rare procedure as the motivating case.

### R4-I1 — `--strict` does NOT bypass the LaTeX cache ✅ **CONFIRMED — my guarantee is wrong as written**

`_memo`'s docstring states the Paper Submission Gate *"always re-measures"*. That is true of
`_memo.memoized` and **false of the LaTeX cache I wrote alongside it**, which is gated solely on
`_cfg.FORCE_LATEX` (`papers_prose.py:508, :524, :562`). `--strict`, `--no-memo` and
`SKEFT_VALIDATION_NO_MEMO=1` all read it. Two separate caches, two different bypass rules, one
docstring claiming both.

Mitigating: `gate_precheck submission` does pass `--force-latex`, so the submission *path* does
recompile. The stated guarantee is still wrong, and `--strict` alone does not deliver it.

⚠️ **Compounding, found by the lead while verifying:** `papers_prose.py:22` — the module header —
still reads *"It is still slow-gated behind `_cfg.FORCE_LATEX`, so a default full run…"*. I
deleted that slow gate this morning **in this same file** and did not update the header. Same
defect as R3-MAJ4, in the file I was editing at the time.

### R4-MAJ7 — `counts_fresh` wedges permanently red ✅ **CONFIRMED LIVE — a regression I introduced**

Reproduced and root-caused by the lead:

| | |
|---|---|
| `counts.json` content after regeneration | **byte-identical** → not genuinely stale |
| `constants.py` mtime | `1785947998.849` |
| `counts.json` mtime | `1785947429.469` → mtime says STALE |
| `update_counts.py` | exits 0, writes identical content, mtime never advances |
| ⇒ `post_regenerate` leg | *"exited 0 but the artifact is STILL STALE"* → **permanent FAIL** |

The pass-1 repair `1a7f016d` (mine — the R4-I7 `_verify_regeneration` fix) correctly made the
check able to fail, but on a **predicate that can be permanently false for a benign reason**: any
`git checkout`, merge, or write-and-restore bumps a source mtime, and no content change can ever
heal it. In-repo precedent for the right shape exists — `inventory_index_autogen_fresh` compares
**content**.

Tree healed by the lead (`touch docs/counts.json docs/counts.tex`, content verified identical
first) and `counts_fresh` is green again. **The defect is unfixed.**

### R4-MAJ3 — `bundle_figure_integrity` silently runs the fallback on EVERY run

The "derived from `FIGURE_REGISTRY` rather than hand-maintained" block raises `AttributeError`
every time (`spec_from_file_location` + `@dataclass`), so production always uses the hardcoded
7-figure list. **7 of 124 shipped bundle PNGs checked.** The anti-drift guarantee is advisory
only — and this is the exact "hand-maintained list parallel to a registry" defect the block was
written to remove, failing open into the list it replaced.

### R4 — pass-1 re-verification, in both directions
- **R4-I1 (`cross_path_consistency`)** — re-filed with a **corrected mechanism**: the two legs'
  `rel_diff` are **bit-identical** (`4.127685699545415e-06`), and both silently skip to
  `passed=True, details=[]`.
- **R4-I6 (`formula_grounding`)** — ❌ **NOT reproduced.** Both "dead" legs fire on production
  seeds. Register must mark it **corrected**, not closed. *(Pass 1 filed a finding that was
  wrong; that is worth as much as a confirmation.)*
- **R4-I8 (`readiness_verdicts_agree`)** — ✅ confirmed **with mechanism**: GREEN is demoted by
  the producer whenever a P1 gate blocks, and **0 of 704** gates are ever blocked at P2, so the
  reverse leg is dead by construction.
- **R4-I7 and R4-I10** — both **re-opened**: displaced onto the wrong predicate, and half-closed.

### R4 — process findings
- The working tree was mutated by concurrent reviewers throughout: **three check bodies stubbed
  to `passed=True`** and **`papers/D1/paper_draft.tex` truncated to zero bytes** mid-run. R4
  re-derived every static claim from `git show HEAD:`. **Lead verified the tree is now intact**
  (D1 = 58,301 bytes, no zero-byte tracked files, one leftover stub reverted). Next pass:
  **one worktree per reviewer.**
- `bundle_source_freshness` **writes git-tracked `bundle_metadata.json` during a validation run.**

---

## 🔴 R2 — test quality. 29 findings, 3 CRITICAL. **All six reviewers now reported.**

### The population result, and it argues FOR the branch
R2 neutered **each of the 59 registered checks in turn, in production source**, and ran every
test file mentioning it: **0 of 59 undetected.** Static census: **775 test functions** in changed
files, **exactly 1** with no assertion — and that one pre-exists on `main`. Suite baseline
re-measured: **5,482 passed, 5 skipped, 280.85 s.** Crude test theatre is essentially absent from
this branch. That deserves saying as plainly as the failures below.

### R2-C2 — my memo tests test the HASH HELPERS, not any check's KEY ⛔ **the worst finding of the pass**

`tests/test_validation_memo.py::TestKeyCoversItsInputs` asserts that
`_memo.lean_source_fingerprint()` moves when a `.lean` file changes. It **never asserts that
`axiom_closure_allowlist`'s `key_fn` calls it.**

R2 deleted `lean_source_fingerprint()` from that check's `key_fn` **in production** — producing
exactly the outcome my own test file calls *"the single worst outcome this cache can produce"* —
and got **`24 passed`**. Same for the toolchain-pin input: `24 passed`, plus `77 passed` across
related files.

So the tests I wrote **to satisfy QI-30's production-seeded criterion** violate that criterion:
they seed the helper, not the artifact the guard protects. A test one level away from what it
claims to guard is the same shape as a check one level away from what it claims to measure.

### R2-C1 — the zero-headroom test is what makes the floor unfireable ⛔

Beyond the four prior confirmations, R2 identifies the mechanism: `test_ci_mode.py:157` asserts
`CI_MIN_CHECKS_RUN == len(_CHECKS) - len(CI_SKIP)` — **the definition of the quantity being
compared.** I wrote that as a house-idiom zero-headroom ratchet; it *guarantees* `n_ran < floor`
is never true. The guard and its test are jointly self-sealing.

### R2-C3 — no test covers the cached-SKIP path ✅
`test_a_failure_is_never_cached` covers `passed=False` only. The `passed=True`-without-measuring
path — the one that actually happens — has no coverage at all.

### R2-MAJ3 — the one real historical regression is invisible to 5,482 tests
`build_graph._infer_bundle_from_text` appears in `tests/` **only as a monkeypatch target**. R2
restored the genuine historical bug verbatim (`D\d{1,2}` → `D[1-9]` — the one that rendered D12
"Blockers 0" while it carried 36 open findings, and minted false `FLAGS` edges) and the full
suite returned **5,482 passed, byte-identical to baseline**.

**59/59 checks are protected against deletion; the one regression that actually happened is not
detected.** That is the R6 mismatch thesis, demonstrated rather than argued.

### R2 — answers to the questions I put in the brief
- `tests/conftest.py`'s env var weakens **no existing assertion** — but it means the memo is
  **never exercised end-to-end**, including in subprocesses.
- `test_validation_memo.py` **does** restore content (`try/finally` + post-restore byte
  assertion) — **but not mtimes.** R2 measured **four production files left stamped at suite
  runtime**, which flips `counts_fresh` stale and arms the 1800 s regenerator.
  ⇒ **This is the cause of R4-MAJ7's live wedge.** My test file triggers the regression my
  earlier repair introduced. Two of my own defects, compounding.
- Every registry-introspecting guard **does** use `_memo.unwrap` today (4-row census) — but by
  convention only, with nothing enforcing it.

### R2 — other measurements
- The cannot-measure baseline scanner is **blind to 12 of 36** silent-PASS sites — *including the
  two that poison the memo*. ⚠️ **This directly affects the planned fix**, which was going to
  lean on that scanner's population. It must be widened first.
- Its seam guard has **44 % headroom** (`>= 30` against an actual 54) — a ratchet with slack,
  contradicting R3's otherwise-clean zero-headroom finding.
- Fixture-only ratchet: **55 of 59 checks never production-seeded** (re-file of open pass-1
  `R3-C2`).
- ❌ **Not reproduced:** an inherited claim that `scripts/validate.py` holds 5 live
  `@register_check` decorators outside the scanner's scope — all 5 hits are comments/docstrings,
  **zero live decorators.** Filed as not-reproduced rather than dropped.

**R2 verdict: YES WITH FIXES** — *"nothing makes anything worse than `main`, which had no guard
in these positions at all."*

---

## ✅ FIXED — round 2 (2026-08-05, after the Criticals)

| id | finding | resolution |
|---|---|---|
| **R4-MAJ3** | `bundle_figure_integrity` raised on every run → always used its hardcoded 7-figure fallback | ✅ `module_from_spec` doesn't register in `sys.modules`, and py3.12+ `@dataclass` dereferences `sys.modules.get(cls.__module__)`. Registered before `exec_module`; `FIGURE_REGISTRY` now loads (**137 specs**). ⚠️ Coverage is still **7** — the `d11_/d12_` filter is R5-C2 → ADR-010. What is restored is the anti-drift guarantee: a NEW d11/d12 figure is picked up instead of silently omitted. Seeded-defect test added and **verified to fire** by removing the line in production. |
| **R5-MAJ2** | `gate_precheck s9` ran one check that always passes | ✅ added `bundle_figure_integrity` (verified side-effect-free first — a precheck runs before every dispatch and must not dirty the tree). `viz_consistency` stays advisory by design; the defect was s9 having nothing else. |
| **R5-MAJ3** | Invariant #10 unenforced, with a green test pinning the gap | ✅ enforced in `elaboration_knob_watchlist` behind `MAXHEARTBEATS_PROOF_BODY_CEILING = 22` (zero headroom). The pinning test is **replaced by its inverse**, plus a silent-on-correct-data test and a live zero-headroom test. |
| **R5-MAJ1** | `--write` reported success while writing nothing | ✅ now raises `NotImplementedError` naming the working alternative. ❌ **R5's framing corrected** — see below. |

### ⚠️ R5-MAJ1 was OVERSTATED, and the correction matters

R5 filed *"no working way to satisfy it"* and *"there is no writer of `human_verified_date`
anywhere"*. **Re-measured: `scripts/wave2_flip_provenance.py:178` is a real writer**
(`PROV_PATH.write_text`). The `--strict` provenance gate **is** satisfiable — through the
bulk-flip script, not through the dashboard. What is genuinely broken is narrower: the
dashboard's `--write` was a no-op that printed success, and its confirm button mutates memory
then renders a green `HUMAN VERIFIED` badge for a change that is never persisted.

### ⚠️ The Invariant-#10 count: measured three times, lead wrong twice

| measurement | value | verdict |
|---|---|---|
| R5 (reviewer) | **22** | ✅ correct |
| lead, "correcting" R5 with a looser attribution scan | 23 | ❌ wrong |
| lead, explaining the gap as "22 bare + 1 `synthInstance.`" | 23 | ❌ **wrong twice** — there are **zero** `synthInstance.maxHeartbeats` sites in the tree |
| enforced predicate (attached to `theorem`/`lemma`/`example`) | **22** | ✅ frozen as the ceiling |

31 bare `set_option maxHeartbeats` lines exist in total; the other 9 attach to no
theorem/lemma/example within 12 lines — file-level blocks, or the **tactic-bodied `def` limb of
Invariant #10 that this check does not yet cover** (documented in the check body, not hidden).

*A count is meaningless without its predicate.* I re-measured a reviewer's number, got a
different one, invented a reconciliation for the difference, and was wrong about both. The
reviewer was right the whole time.

---

## ✅ FIXED — round 3 (the IMPORTANT tail)

| id | finding | resolution |
|---|---|---|
| **R2 (scanner blindness)** | cannot-measure scanner saw 21 (check,kind) pairs against 47 literal `passed=True` returns | ✅ **17 further silent non-measurements annotated** `measured=False` — found by scanning for returns whose OWN detail text says SKIPPED / not found / absent. Floor sensitivity with no toolchain went **1 → 2** detected, and a provisioned run still clears 55. New guard `TestSelfDeclaredSkipsDeclareMeasuredFalse` **verified to fire** by stripping one annotation in production. |
| **R2-MAJ3** | `_infer_bundle_from_text` appeared in `tests/` only as a monkeypatch target; the real historical regression was invisible to 5,482 tests | ✅ 6 direct tests. **Verified by re-seeding R2's exact experiment** — narrowing `D\d{1,2}` → `D[1-9]` in production now FAILS `test_two_digit_bundles_do_not_truncate`, where it previously returned byte-identical green. |
| **R6-M8** | 11 submission-deciding `_eval_*` evaluators, zero direct tests | ✅ `tests/test_readiness_gate_evaluators.py` — 36 tests: per-evaluator contract (identity, well-formedness, blocked-says-why), the crash→BLOCKED contract, and roster/priority-split ratchets parametrized from `GATES` so a new gate cannot land untested. |

### ⚠️ NEW FINDING, surfaced by writing those tests: 9 of 11 gates pass vacuously

Given a paper with **no evidence in the graph at all**, **9 of the 11 readiness gates return
`passed`**. It is deliberate and explicit — e.g. `_eval_parameter_provenance`:

```python
if not param_ids:
    r.state = 'passed'
    r.notes = 'no parameter dependencies declared'
```

**I nearly asserted my way past this.** My first test asserted `state != "passed"` — which would
have imposed a redefinition of 11 submission gates, on a corpus where 61 papers are already red,
based on my reading rather than a validated decision. Reading the code first showed a considered
choice: a paper that genuinely uses no parameters *does* pass that gate.

**The residual risk is real and is filed rather than pinned:** these gates cannot distinguish
*"this paper declares no parameters"* from *"the extraction failed to link them"*. A paper
missing from the graph therefore reads as submission-ready. The test now asserts only what is
defensible — **a vacuous pass must announce itself** — so the decision stays visible and
reviewable. ⬜ **OPEN**, needs an operator call on whether empty-population should be `open`
rather than `passed`.

### ✅ Also closed in round 3

| id | finding | resolution |
|---|---|---|
| **R1 (commit gate)** | `pre-commit-sync.sh`'s three check names never validated against the registry — a rename gives a silent SKIP on the only gate that can hard-block `main`, while `CI_SKIP` has exactly that test | ✅ `TestCommitGateCheckNamesAreReal`, **verified to fire** by renaming a check in the hook. (The first version's regex was case-narrow and tripped the seam guard instead of the real assertion — widened so the seeded defect hits the assertion that names the problem.) |
| **R3 (`--strict` caller)** | *"`--strict` reaches no automated caller"* restated in 5 live sites after `gate_precheck submission` became its caller | ✅ corrected in `RESUME_STATE.md`; the shipped module docstrings already carry the correct note. |

## ❌ NOT REPRODUCED — measured, and wrong as filed

Recording these is worth as much as the confirmations: an unchallenged bad finding sends the
next person chasing a ghost, and pass 1 shipped several.

| id | filed as | measured |
|---|---|---|
| **R4 (tree write)** | *"`bundle_source_freshness` **writes** git-tracked `bundle_metadata.json` during a validation run"* | **Misattributed.** `freshness.py` contains no `write_text`/`json.dump`; running `--check bundle_source_freshness` **and** `--check bundle_metadata_matches_graph` leaves `papers/` byte-clean (verified twice). The writer is `scripts/bundle_readiness.py:688 write_metadata_counts`, called from that script's own flow at `:773` — a **generator**, which is supposed to write. No validate check writes it. |
| **R4-I6** (pass 1, re-tested) | two `formula_grounding` legs are dead | **Not reproduced** — both fire on production seeds. Marked *corrected*, not *closed*. |
| **R5-MAJ1** (partly) | *"no writer of `human_verified_date` anywhere"* | `scripts/wave2_flip_provenance.py:178` is a real writer. The gate is satisfiable; only the dashboard path was broken. |
| **R2** (inherited claim) | `scripts/validate.py` holds 5 live `@register_check` decorators outside the scanner's scope | **Zero live decorators** — all 5 hits are comments/docstrings. R2 filed it as not-reproduced rather than dropping it. |

---

## Verdicts

| reviewer | verdict |
|---|---|
| R1 architecture | YES WITH FIXES |
| R2 test quality | YES WITH FIXES |
| R3 deferred scope | YES WITH FIXES |
| R4 enforcement efficacy | **NO** |
| R5 coverage adequacy | YES WITH FIXES |
| R6 appropriateness | YES WITH FIXES |

**5 of 6 say mergeable with fixes; R4 says no.** The disagreement is not about facts — every
reviewer found the same defects — it is about whether shipping a guard that cannot fire is worse
than shipping no guard. R4 says yes. On the specific code at issue I agree with R4, and the fixes
below are ordered to clear its blockers first.


---

## ⬜ STILL OPEN after round 3

**Infra, this branch — none of these is a merge blocker; each is measured and filed.**

| id | finding | why deferred |
|---|---|---|
| R6-M1 | atlas negative frontier: **454 obstructions, 409 unregistered, 144 namespace-only from 14 modules**; the digest filter has **0 tests** | the count has been wrong three times (pass 1, my re-count, R6's correction of both). Needs the predicate fixed first — `rec["name"]` is fully qualified, so `_NOGO_RE` matches the namespace, not the declaration. |
| R2 (seam guard) | the cannot-measure seam guard asserts `>= 30` against an actual **54** — **44 % headroom** | a ratchet with slack cannot fire. Tighten to 54 with a stated reason, in a commit that re-measures. |
| R3 | **5 of 10 ratchets have no zero-headroom test** | mechanical; each needs its own live-population assertion, like the one added for `MAXHEARTBEATS_PROOF_BODY_CEILING`. |
| R3 | committed `lean/lean_deps.json.hash` does not match committed `.lean` sources → §Deferred item 0's refresh fires a full ExtractDeps on every fresh clone | needs a `lake` run to regenerate honestly; deliberately not done here (`rm -rf .lake/build` is rare by policy and must not run casually). |
| R1 | BinOp path-alias gap — **5 sites**, two under a docstring denying they exist | H1 hardening; mechanical. |
| R1 | Paper 15 Table 2 numbered by source-file name, i.e. by the ordering H3 declares non-semantic | paper-side; pairs with the ADR-010 sweep. |
| R4-I1 | `cross_path_consistency`'s two legs produce **bit-identical** `rel_diff` (`4.127685699545415e-06`) and both skip to `passed=True, details=[]` | the mechanism differs from pass 1's filing; needs a decision on what the second leg is *for*. |
| R4-I8 | `readiness_verdicts_agree`'s reverse leg is dead **by construction** — GREEN is demoted whenever a P1 gate blocks, and 0 of 704 gates are ever blocked at P2 | needs a semantics decision, not a code fix. |
| R4-I7 / R4-I10 | re-opened: displaced onto the wrong predicate; half-closed | re-measure before re-fixing. |
| **new** | **9 of 11 readiness gates pass vacuously on an empty population** — cannot distinguish "declares no parameters" from "extraction failed to link them" | ⛔ **needs an operator call**: should empty-population be `open` rather than `passed`? Changing it moves verdicts on a corpus where 61 papers are already red. |

**Submission blockers → ADR-010** (operator routing, unchanged): R5-C2 figure content (**124 PNGs
across 49 dirs, 29 with no `FIGURE_REGISTRY` spec at all** — worse than pass 1 measured, and
deleting the `d11_/d12_` filter takes coverage 7→95 but still leaves 29 invisible), R5-C3 number
recomputation, R5-C4 theorem-statement correspondence, R5-C5 citation content. Plus D3's two fatal
LaTeX errors, and the ~40 open items from pass 1.

## Process findings against this review itself

1. **Six reviewers shared one working tree.** R4 observed three check bodies stubbed to
   `passed=True` and `papers/D1/paper_draft.tex` truncated to zero bytes mid-run; R3 noted the
   same hazard and took its measurements on a clean tree; R1 caught a leftover stub in
   `prose_lean_refs.py` that the lead then reverted. **Next pass: one worktree per reviewer**, and
   seeding reviewers restore in a `finally`.
2. **The severity vocabulary mandate worked.** Pass 1's sixth reviewer invented its own scheme and
   its 16 findings counted as zero; pass 2's R6 returned 19 findings correctly labelled.
3. **Reports-to-disk worked.** Pass 1 lost 53 findings to the transcript. Pass 2 has six files.
