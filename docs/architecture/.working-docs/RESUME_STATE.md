# Resume state — infrastructure + publication remediation

**Last updated:** 2026-08-04. Written so any session (or a post-compaction continuation) can pick this up
without re-deriving it. Read this first, then the linked documents.

> ## ✅ ADR-009 IS DELIVERED — ⚠️ AND **NOT MERGED** (2026-08-04)
> Phases 0–3 complete, **all 8 §Deferred items dispositioned**, ADR-009 **ACCEPTED**. The branch is
> **`infra/adr-009-validation-modularization`, 69 ahead of `main` and 0 behind — NOT merged.**
> ⚠️ *This block claimed "merged to `main`" until 2026-08-04. That was false and is corrected here;
> verify with `git merge-base --is-ancestor HEAD main` before repeating any merge claim.*
> Verified on the branch HEAD: **59 checks** in **12** modules under `scripts/validation/checks/`,
> `validate.py` registers **0**; `--list` 59; unknown `--check` exits 2; `BUNDLE_CODES` 21; largest
> module 965 lines; fast suite **5398 passed / 5 skipped / 0 failed**; `validate.py` **57/59 with
> 2 intentional reds**. Characterization **HELD** at every structural boundary.
> ⚠️ These figures move as remediation lands — re-measure, do not quote.
>
> **Both red checks belong to the publication workstream.** The two readiness-layer cannot-measure
> sites (`evaluate_all_gates`, `_blocked_p1_gates_by_paper`) were **CLOSED by `5228ed6d`**, after the
> documents below were written — several still record them as open (audit finding QI-21/QI-22).
>
> ## 🔴 THE QA/QI INFRASTRUCTURE AUDIT IS **REOPENED** — 31 closed, 4 OPEN Criticals
> **➡️ Read [`docs/audits/2026-08-04-qa-qi-infrastructure/PR_REVIEW_2026-08-05.md`](../../audits/2026-08-04-qa-qi-infrastructure/PR_REVIEW_2026-08-05.md) FIRST** — six-reviewer PR
> review, verdict **DO NOT MERGE**, measured state and the ordered resume point.
> A full direct read of the entire QA/QI surface (~17,700 lines, including `build_graph.py`, which
> this file had recorded as never read) was completed 2026-08-04. It found **31 findings** across
> four workstreams — one live enforcement hole, duplicated predicates, dead code, documentation
> contradicting the code it describes, and D5's missing mechanical enforcement — and **all are now
> closed**.
>
> ⚠️ **RETRACTED: "every one of the 59 checks is mutation-verified in both directions."**
> PR review 2026-08-05 found FOUR checks that carry a MUTATION_VERIFIED entry, a passing
> both-directions test, and **no ability to fail in production** (QI-31…QI-34). What the
> registry certifies is that a decision was recorded and the named test references the check
> in code — not that the check can fail. Read the tracker before quoting any coverage number.
>
> ⚠️ **The four are FIXED (2026-08-05)** — `17bbe234`, `2dc856ec`, `865db716`, `637d1184` — each
> re-verified by seeding the defect in the **production artifact**, not a fixture. **The retraction
> above still stands for the other 55.** Not one of the four was fixed by widening a constant: two
> were reading the wrong artifact, one the wrong FIELD of the right one, and one promoted the class
> its own docstring calls advisory. The prescribed "recalibrate the threshold" for `recurrence`
> would have been its fourth mis-tuning.
> `AWAITING_MUTATION_TEST` is empty and its ceiling is **0**, so a new check that ships without a
> both-directions test **fails on arrival**. That discharges ADR-009 D5, the obligation its own
> §Context calls *"the one that caused the damage"* — it had shipped as prose, and 32 of 59 checks
> had no test at all.
>
> ⚠️ **Roughly a third of the ~150 mutations came back MISSED on first run, and every one was a real
> finding** — an inert guard, a vacuous test, or a line that should not be counted as verified.
> Do not read the final green as the result; the ratio is the result.
>
> **➡️ [`docs/audits/2026-08-04-qa-qi-infrastructure/README.md`](../../audits/2026-08-04-qa-qi-infrastructure/README.md)
> is the tracker and stays authoritative. Read it before touching the validation suite** — in
> particular its §4 residuals (recorded, deliberately NOT scheduled) and its §4b harness lessons,
> which will cost time again otherwise.

> **Every figure in this file is either (a) re-verified on the date shown, (b) marked as a historical
> measurement, or (c) marked as INHERITED from a document and not independently checked.** That third
> class is the one that bites: on 2026-08-04 three claims were written in a declarative voice while
> actually being inherited — most seriously "main has no infra code", which is false (see below). A
> number in prose is a cache with no invalidation protocol; where an authoritative definition exists,
> this file points at it instead of restating its size.
>
> **The failure mode to watch for is not "unverified" — it is "verified adjacent".** Running a check
> whose result is merely CONSISTENT with a claim, and reporting that as confirmation. Every verification
> must be able to distinguish the claim from its neighbours, or it is not a verification.

---

## The measured baseline — what "the suite was green" actually meant

**This is the evidence the whole workstream rests on. It is a committed artifact, not a characterization.**

`docs/validation/reports/validation_20260801T055521Z.json` — the last full `validate.py` run, 2026-08-01,
**before this branch existed**, so main-equivalent:

> **58 of 59 checks passed. One failed.**

Run concurrently with the publication-readiness audit, which found **no bundle submittable, best grade C−,
80 P0 findings.** Same tree, same day. What the individual checks reported in that run:

| check | verdict | its own summary line |
|---|---|---|
| `readiness_submission_gate` | **PASS** | *"0 green / 3 yellow / **61 red** across 64 papers"* |
| `paper_latex_compiles` | **PASS** | *"SKIPPED (slow)"* — never compiled anything |
| `count_literals` | **PASS** | *"107 count-literal matches … WARN-level during retrofit"* |
| `numerical_literals` | **PASS** | *"116 inline literals … WARN-level during retrofit"* |
| `bundle_source_freshness` | **PASS** | *"0 FAIL / 11 WARN / 12 PASS"* |
| `bundle_metadata_matches_graph` | FAIL | the one real failure |

**Read the first row twice.** The check computed the RED verdict, printed it, and returned `True`. That is
the defect this workstream exists to fix, preserved in an artifact rather than argued from.

**So: never describe the pre-refactor suite as "working".** It *ran* — all 59 checks executed and produced
output. It did not *measure*: a substantial subset was structurally incapable of returning a failing
verdict, so green carried no information. The accurate framing is **"reports success while measuring
nothing"**, and it is the audit's central finding (`SYNTHESIS.md` §2).

### The current failing set — MEASURED 2026-08-04 (AC6)

`docs/validation/reports/validation_20260804T184002Z.json`, run on the final HEAD, 334 s:
**57 of 59 passed, 2 failed, 1,053 warnings** *(as of 2026-08-04; since 2026-08-05 a default run is **56 of 59, 3 failed** — `paper_latex_compiles` joined the reds when its slow gate was deleted)* — identical failing set to the 17:41 run, re-verified after
the item-0 fix and the `lean_statements` split. Both failures are intentional and neither is clearable by
infrastructure work:

| check | why it is red | who clears it |
|---|---|---|
| `readiness_submission_gate` | *"0 green / 3 yellow / **61 red** across 64 papers"* — the same measurement it used to report while returning PASS. Now it fails, per §Deferred item 2. | the publication workstream, per paper |
| `bundle_metadata_matches_graph` | **14 of 21 bundles** carry `stage13_status: "green"` with open blockers (D1 37, F 23, D2/I2 19, D5 17, I1/I3/L2 16, D7 12, D3 7, L3 6, E1 5, L1 2, D4 1). | the publication workstream — ⚠️ **NOT fixable by re-running `bundle_readiness.py`**: `write_metadata_counts` owns `blockers_open`/`advisories_open`/`readiness`, and deliberately does **not** write `stage13_status`. That field is hand-asserted; only `bundle_append.py`'s green→pending demotion touches it. |

The 1,053 warnings are advisory by design (pin drift, count/numerical literals under their ceilings,
orphan nodes, uncited bibitems).

⚠️ A full run **mutates the working tree**: `counts_fresh`, `tables_fresh` and `claim_clusters_fresh`
regenerate tracked artifacts mid-run. Check `git status` afterwards and stage deliberately.

---

## Working rules for this workstream

Read these before the state below; they govern how every increment is built.

**1. Read before you write.** Do not modify a file you have not read in full, directly, in your current
context — a compaction resets that. Scope the read to what you are changing plus its blast radius, traced
through consumers (imports, the frozen external surface, `_ROSTER_CONSUMERS`, the pre-commit gate), not
by a fixed file list. Core infra here: `scripts/validate.py`, `scripts/validation/**`,
`scripts/validate_helpers.py`, `scripts/build_graph.py`.

**2. Judge a check by its body.** A check's `--list` description and its docstring state intent, not
behaviour. Where the two differ, the body wins — several checks in this suite carry docstrings that
describe a stricter guard than the code implements.

**3. Measure before you fix, and label the evidence.** Every claim is *measured this session*,
*historical*, or *inherited from a document*. A filed finding's count, named consumer and effort estimate
are claims; take the measurement yourself and record it alongside the original. A measurement is scoped
by a predicate — when the thing that predicate keyed on changes, the measurement is void.

**4. Make verifications discriminating.** Before accepting a check as confirmation, ask what it would
look like if the claim were false. If the answer is "the same", it confirms nothing.

**5. Separate mechanical from semantic.** A structural move edits no check body, unifies no policy,
retunes no threshold, flips no verdict. Semantic changes ship one at a time, each independently reviewed.

**6. Both directions, or it is not a test.** Every new or modified check ships a mutation test that fires
on a seeded defect and stays silent on correct data. Scope each mutation to the target function's AST
span, and distinguish "the assertion fired" from "the mutation broke the import".

**7. Guards are never weakened to make the suite green.** A red gate where remediation has not landed is
the instrument working. Where a claim is unsupported, build the substrate that makes it true or prove it
cannot be.

**8. Attribute every characterization delta** to a named cause. "Probably the new tests" is not an
attribution.

---

## Git layout (verified 2026-08-04)

**`main`** — `c2b597e1 docs(audit): publication-readiness assessment of all 21 bundles`.

⚠️ **This entry read "No infra code" until 2026-08-04. That was MATERIALLY WRONG and is corrected here.**
**`main` carries the ENTIRE working validation infrastructure** — `scripts/validate.py` at **7,765 lines
with all 59 checks registered**, 105 files under `scripts/`, 140 under `tests/`. Verified 2026-08-04.
**ADR-009 is a REFACTOR of working code, not a greenfield build**, and every plan must be read that way.

What `main` does NOT have is this branch's work: no `scripts/validation/` package (the Phase-2 split), and
no `stage13_status` guard (zero hits). The checks themselves all exist there and run today — three of them
simply **cannot fail** on `main`, which is the defect this branch repairs.

*(How the error happened, because the shape matters: the false line was inherited from an earlier revision
of this file, then "confirmed" by a narrow check — no `validation/` package, no `stage13_status` — whose
result was merely CONSISTENT with it. A verification that cannot distinguish the claim from its neighbours
launders the claim instead of testing it.)*

**`infra/adr-009-validation-modularization`** — ALL infrastructure work, off main until every phase is done
(operator ruling 2026-08-03). **76 commits ahead of main, 0 behind** — re-count with `git rev-list --count main..HEAD` rather than trusting this number; it was "35" and stale by 20 within a day (audit finding QI-24).
Recent:

```
d1c39ad3  docs(resume): re-shape Phase-3 items 5 and 6 from a full read of all 11 check modules
1c02544c  docs(validate): correct two stale in-file figures found by reading it in full
75b1016d  docs(adr-009): re-ground the tracker — 5 stale figures + the numbering collision
cc797605  fix(graph): stop fabricating 144 Lean VERIFIES edges — §Deferred item 7 (complete)
9532ba76  fix(validate): native_decide ratchet measures live substrate — §Deferred item 1
cb9e1dcd  fix(graph): stop silently dropping 66 test nodes — §Deferred item 7 (first half)
c3456a23  fix(validate): disposition the always-pass checks — §Deferred item 3
fd470314  fix(validate): readiness_submission_gate can finally fail — §Deferred item 2
2ced308d  refactor(validate): extract citations, reviews, bundles_readiness — Phase 2 complete
```

Working tree carries two pre-existing, deliberately untouched entries — leave both alone:
`M lean/lean_deps.json.hash`, and `?? docs/dev-loops/proposals/prose-bridged-claims-gate.md` (an
operator-filed DRAFT awaiting their own go/no-go; not this workstream's to land).

**`stash@{0}`** — paper-remediation WIP from the 07-31/08-01 sessions (132 regenerated figures,
`counts.json`/`.tex`, `provenance.py`, `citation_cache.py`, `lean_deps.json.hash`). Separated by mtime;
boundary verified. **Restoring it changes `counts.json`, which several checks read — take a fresh
characterization baseline after any unstash.**

### Live measurements — all re-verified 2026-08-04

| Quantity | Value | Authoritative source (prefer this over the number) |
|---|---|---|
| registered checks | **59** | `validate.py --list` |
| `validate.py` | **720** lines, **zero** registered checks | its 5 `@register_check` hits are all comments/docstrings |
| `_apply_canonical_order()` | `:618`, below the import block (`:484-494`) ✅ | `test_validate_registry_contract.py` asserts the position from the AST |
| frozen external surface | **54** | `EXPECTED_SURFACE` in `tests/test_validate_public_surface.py` |
| characterization quarantine | **10** → 59 − 10 = **49** characterized | `QUARANTINE` in `tests/validate_characterization.py` |
| bundle roster | **21** | `scripts/bundle_registry.py` → `BUNDLE_CODES` |
| fast suite | **5398 passed, 5 skipped, 0 failed** in ~197 s | `uv run python -m pytest tests/ -q` — 5039 → 5055 → 5080 → 5398 as guards and the D5 suites landed; re-run, do not quote |

⚠️ **Two git gotchas learned here.**
1. The pre-commit hook runs `sync.py --fast` and **restages** `SK_EFT_Hawking_Inventory_Index.md`,
   `lean/atlas_view.json`, `docs/ATLAS_HEATMAP.md` and `papers/*/tables/*.tex` into whatever you commit.
   Stage explicit paths only; check `git show --stat HEAD` afterwards.
2. **mtime is not provenance.** `harness_web_egress_guard.py` reported an 08-01 mtime for a change made
   on 08-03. Verify authorship by diff content, not timestamp.
3. **A background shell reverts to the workspace parent.** Run everything from `$REPO`; a piped `tail`
   will report exit 0 for a command that never ran. (Caught twice.)

---

## Where we are

Two workstreams, sequenced by operator ruling: **infrastructure remediation first (ADR-009), then the
portfolio re-assessment (ADR-010). ADR-008 onboarding third, deferred by decision.**

| Workstream | Deliverable | State |
|---|---|---|
| **W1 — ADR-009** | validation-suite modularization + the mutation-test obligation | ✅ **DELIVERED.** Phases 0–3 complete, all 8 §Deferred dispositioned. ⚠️ Post-delivery audit found 31 findings, ALL CLOSED — see the tracker |
| **W2 — ADR-010** | portfolio purpose / distribution / late-phase absorption — **a DOCUMENT** | **CHARTER AUTHORED 2026-08-04**, analysis pending W1 |
| W3 — ADR-008 | Claude-Code onboarding | DEFERRED. `tangential-items.md` T2 |

⚠️ **W2 was RE-SCOPED by the operator on 2026-08-04.** It is no longer "execute the paper remediation".
It is **author [ADR-010](../../adrs/ADR-010-publication-portfolio-reassessment.md)** — a researched,
densely-linked strategy document — and the *execution* it specifies is a later goal. The charter, the
operator's verbatim framing, the verified constraints and the open questions are all in that ADR; **read
it rather than re-deriving them here.** No manuscript edits and no `PAPER_STRATEGY.md` edits in W2.

---

## Workstream 1 — ADR-009 (ACTIVE)

Governed by [ADR-009](../../adrs/ADR-009-validation-suite-modularization.md) (status: **ACCEPTED** 2026-08-04; this line said PROPOSED — audit finding QI-24).

| Phase | State |
|---|---|
| **0 — characterization harness** | ✅ COMPLETE. 3 guards + the harness, all mutation-verified |
| **1 — anchors + helpers, file stays put** | ✅ COMPLETE. `CHARACTERIZATION HELD — 49 checks identical` |
| **2 — package split** | ✅ COMPLETE 2026-08-03. 11 modules, 0 checks left in `validate.py`. 48/49 byte-identical vs the pre-Phase-2 baseline |
| **3 — semantic fixes** | ✅ **COMPLETE — 8 of 8 dispositioned.** Fixed: **1, 2, 4, 7**; **0** fixed (1st half) + DECLINED (2nd half); **3** dispositioned per-check; **5, 6** DECLINED with measurements |

### ⚠️ Numbering: cite ADR-009 §Deferred's own 0–7, always

The same eight items are numbered three ways across the documents — ADR §Deferred **0–7** (canonical),
`validation-module-migration-notes.md` §7 as **1–7** (+ a referenced item 0), and the cost-ordered list
that used to live here. The collision already produced two live mis-citations. **This file now uses the
§Deferred numbering exclusively.**

### Phase 3 — the eight items

**✅ Item 1 — `native_decide_regression` read a possibly-stale `counts.json`** (`9532ba76`).
Now measures `lean_deps.json` directly. Reordering could not have fixed it: the commit gate invokes the
check in ISOLATION, so `counts_fresh` never runs there at all. 15 tests, 5 mutations.

**✅ Item 2 — `readiness_submission_gate` was INVERTED** (`fd470314`).
It failed only when zero gate nodes existed and passed when it measured RED. **61 of 64 papers RED,
verdict `True`.** Four defects fixed (verdict, per-paper details, summary, fail-open ImportError); two
pure cores extracted; 11 tests, 5 mutations, clean negative control. **The suite is RED on this check by
design.** ⚠️ Harness lesson: **scope every mutation to the target function's AST span** — two mutations
read as MISSED because `str.replace(…, 1)` hit the first textual match, inside a *different* function.

**✅ Item 3 — the eight always-pass checks, dispositioned individually** (`c3456a23`).
Four were defects (fixed: `readiness_submission_gate`, `paper_latex_compiles`, plus ratchets for
`count_literals` / `numerical_literals`); four are honestly advisory with recorded reasons.
**`paper_latex_compiles` fails on D3 under `--force-latex` — 2 fatal LaTeX errors**, a real publication blocker owned by W2.
⚠️ **SUPERSEDED 2026-08-05 — and this line is now the exhibit.** It read: *"It is NOT one of `validate.py`'s two reds in a default run (audit QI-29). It sits behind the slow gate and reports 'SKIPPED (slow)', so a default run counts it as a PASS."* **The slow gate was deleted on 2026-08-05** and `paper_latex_compiles` is now a **third default red** on D3's two fatal errors. QI-29 was the finding *"a claim written true and left standing after the surrounding behaviour moved"* — and its own correction suffered exactly that, because the author of the change updated one file's entry and did not sweep. Reviewer R3 found it. Measured on a full run 2026-08-04: the two reds are **`bundle_metadata_matches_graph`** (14 of 21 bundle blobs assert `stage13_status: green` with blockers open) and **`readiness_submission_gate`** (0 green / 3 yellow / 61 red across 64 papers). Three documents named the wrong pair — the D3 claim was written true and left standing after the flag context moved.

**✅ Item 7 — `build_graph`'s coverage picture was wrong in BOTH directions** (`cb9e1dcd` + `cc797605`).
*Dropped nodes:* the node id omitted the class, so same-named methods in different classes collided —
**4,416 `def test_*` → 4,350 nodes; 66 lost.** Fixed; id now mirrors pytest's nodeid.
*Fabricated edges:* **144 of 536** Lean-targeted VERIFIES edges were phantom (the ADR recorded 10). Two
independent rules, each mutation-verified as load-bearing — a ref rooted at a **module alias** is a Python
module, never a Lean declaration (kills bare `v`, `m`, `time`, and every `np.*`); a **dotted** ref may
resolve only as a full Lean name, never by its tail. Formula/param edges bit-identical (1,390 → 1,390), so
no `ComputationCorrectness` verdict can move. 16 tests, 6 mutations, clean negative control.
⚠️ **The filed finding was wrong in FOUR ways** — count, consumer, function name, effort. Standing lesson
now in the map's §9: *re-measure a finding's scope before fixing it, even your own.*
**Live consequence, for the record:** 135 PythonTest nodes and 16 Lean declarations lost their last edge
and are now orphans — their only graph coverage was fabricated. That is the honest picture arriving.

---

**✅ Item 0 — DISPOSITIONED 2026-08-04. First half FIXED, second half DECLINED.**
*It was never a caching question.* Measured: `counts_fresh` at position **29**, with **five** lean_deps
readers before it (4, 6, 7, 8, 9) and **three** after (54, 55, 57), and nothing refreshing the artifact in
between. On a wave close the two groups validated different extractions inside one run — including the
`native_decide_regression` ratchet, which exists to notice trust surface the *current* wave added.
- **FIXED:** `validate.main()` calls `validate_helpers.ensure_lean_deps_fresh()` once before any check.
  ⚠️ **Full runs only** — refreshing inside `load_lean_deps()` would fire the 30-min ExtractDeps inside
  the commit gate, which `pre-commit-sync.sh:72-74` forbids. `test_check_run_does_not_refresh` guards it.
  Guard cost 46 ms vs 150 ms for one parse. 8 tests, 4 mutations run and caught.
- **DECLINED (shared graph handle):** measured **5 invocations / 45.4 s** at ~9.4 s each — a ~36 s saving
  on a 447 s run (**8%**), not the ~27% the ADR's "≈8 passes × 15 s" implied. Ordering already permits
  caching (no builder precedes a regenerator), but memoizing *inside* `build_graph_json` is
  documented-wrong: it mutates module-scoped `_LEAN_SHORT_INDEX` / `_TEST_MODULE_ALIASES` /
  `_LEAN_AMBIGUITY_SEEN`, which is why `provenance_dashboard.py` caches at the CALLER with a fingerprint
  and a lock. A correct validate-side handle needs signature changes across `bundle_readiness` and
  `readiness_gates`. Residue: adopt the dashboard's pattern if runtime ever matters.
  ✅ `build_graph.py` HAS been read in full (2026-08-04, QA/QI audit) — that precondition is
  discharged. The DECLINE itself is unchanged: the read confirmed the module-scoped state it
  rests on and found no cheaper seam.

**✅ Item 4 — DISPOSITIONED 2026-08-04. Type change DECLINED, generator CLOSED.**
*Measured:* **60 cannot-measure return sites across the 59 checks — 35 FAIL (58% converted), 25 PASS**,
collapsing to **22 (check, kind) pairs**. The filed "~20 sites" was close; it is now computed.
- **DECLINED — an `UNEVALUATED` state.** `CheckResult.passed` is D2 contract item 5 (`--json`,
  `gate_precheck.py`, `pre-commit-sync.sh` all read it). A third state is a contract break.
- **DECLINED — converting the 22 wholesale.** 5 are optional-toolchain-absent, 3 advisory by design
  (item 3), 8 the H4 `lean_deps` divergence kept visible, 2 the annotated H1-silent sites. Unifying them
  in one commit is the "semantic change wearing a mechanical disguise" H4 forbids.
- **✅ FIXED — `tests/test_cannot_measure_baseline.py`** freezes the 22 and fails on growth (house ratchet
  idiom). Fires both ways: a new silent PASS fails until added deliberately; a site converted to FAIL
  fails until removed, so the ratchet tightens. A third test guards the scanner seam. 3 mutations caught.
- ✅ **CLOSED by `5228ed6d` (2026-08-04) — the "by scope" disposition was WRONG.**
  `evaluate_all_gates` (exception → `open` → YELLOW not RED) and `_blocked_p1_gates_by_paper`
  (exception → `{}` → P1 downgrade dropped) are code defects in the readiness layer with no
  dependency on any roster or paper decision. Neither returns a `CheckResult`, so
  `test_cannot_measure_baseline.py` still cannot see them — `tests/test_readiness_cannot_measure.py`
  is their guard. Audit finding QI-21.
  ⚠️ This bullet read *"Out of the ratchet's reach, by scope … → publication workstream"* until
  2026-08-05 — **290 lines below the banner that had already corrected it.** The identical
  "survived 40 lines below its own correction" shape QI-24 fixed once in this same file, and the
  audit's §2 table named this document for this exact row while asserting all six rows were
  corrected. Only the banner had been.

**⛔ Item 5 — `count_literals` ⊂ `axiom_count_prose_consistency`: THE PREMISE IS FALSE.** Both read
2026-08-04; neither half survives. (a) `count_literals` is no longer "incapable of failing" — item 3 made
it a ratchet against `COUNT_LITERAL_CEILING`. (b) They are **not the same predicate**: `count_literals`
ratchets the *density* of literal counts ("N theorems", "N modules", "N sorry") and compares them to
nothing, while `axiom_count_prose_consistency` performs a **value comparison against computed truth**
(`docs/counts.json` → `lean.axioms`) with a ±120-char historical-attribution window and a negation guard,
hard-failing only when prose asserts a live axiom while the count is 0. **Merging would destroy the
comparison-to-truth.** Disposition: **DECLINE the merge** with this measurement. The inverse is the real
finding and is worth shipping separately — *`axiom_count_prose_consistency` is the model `count_literals`
should be raised to*: compare each literal against its `counts.tex` macro value, not merely count them.

**✅ Item 6 — DECLINED 2026-08-04, after reading `readiness_gates.py` (781) and `bundle_readiness.py`
(783) in full.** Filed as "`--strict` reaches no automated caller, making two gates unreachable in
practice". Premise true; **count wrong (six, not two) and inference wrong.**
- **`--strict` is the documented Paper Submission Gate**, not dead code — `WAVE_EXECUTION_PIPELINE.md:72`
  (*"checked before arXiv/journal submission, not at Stage 1"*), Invariant #12 at `:685` calls it
  mandatory there. No automated caller passes it **by design**: it gates a submission decision.
- **The automated submission gate already exists** — the eleven ReadinessGates in `readiness_gates.py`
  (`GATES` table + `evaluate_all_gates`), surfaced by `readiness_submission_gate`, which item 2 repaired
  to hard-fail. ⚠️ *I spent a cycle looking for a missing runner that has existed since Phase 5v Wave 4.
  Map the subsystem before concluding it is absent.*
- **Per-consumer coverage, mapped against the evaluators:** 1 of 6 covered
  (`_eval_parameter_provenance` blocks on exactly the `human_verified_date` predicate that
  `parameter_provenance --strict` promotes); 5 not covered — provenance DOIs→registry,
  bibitem-title-vs-PDF, author+year in decl names, axiom closures, bundle lift freshness.
  *"Redundant" is too strong even for the covered row:* the gate is per-paper `DEPENDS_ON`, the check is
  whole-registry minus `PROJECTED`.
- **Residue, recorded and NOT built** (`REMEDIATION_PLAN.md` §6a): those five strict legs are exercised
  only if a human passes the flag. Whether to add gates, mechanize a submission runner, or accept them
  as human-run is an **operator decision belonging to the publication workstream.**

⚠️ **Re-measure every open item's scope before fixing it.** Item 7's filing was wrong four independent
ways; item 6's "two" is six; item 5's premise is false outright. A partition inherited from prose is not a
partition.

### The full read — DONE 2026-08-04, and what it covers

> ⛔ **OPERATING MANDATE (operator, 2026-08-04): you are UNAUTHORIZED to work on a file you have not read
> in full, and the authorization RESETS AT EVERY COMPACTION.** This is not advisory. It exists because the
> alternative is a long tail of re-discovering the same facts. Budget the read; do not start without it.

**Read in full on this branch, 2026-08-04:**
`scripts/validate.py` + all **12** `scripts/validation/checks/*.py`, plus `readiness_gates.py`,
`bundle_readiness.py`, `gate_precheck.py` and `tests/test_validate_public_surface.py`.

✅ **THE "NOT yet read" LIST IS NOW EMPTY** (2026-08-04, audit finding QI-24). The QA/QI infrastructure
audit read the remainder in full — **`scripts/build_graph.py` (4,207)**, `validate_helpers.py`,
`graph_integrity.py` and `tests/validate_characterization.py` — ~17,700 lines across the whole surface.
`build_graph.py` was the one ADR-009 §Deferred item 0 named as a precondition for the shared-graph-handle
work; that precondition is discharged, and reading it immediately surfaced QI-01 and QI-03, neither of
which caller analysis had found.

Per-module sizes drift on every commit — read them with `wc -l scripts/validation/checks/*.py` rather
than from this file. ✅ The `lean_substrate` split this section demanded was DONE (`b896cd6d`): the
type-thinness classifier and its three consumers moved to `lean_statements`, and `citations` is now the
largest module. (This paragraph still listed `lean_substrate` at 1,079 with a ⚠️ to split it — audit
finding QI-24.)

⚠️ **Do not assert what a check does from its `--list` description or its docstring.** That error was made
once in this workstream and caught by the operator: a claim that "no check can validate a hand-typed
count" was refuted by `axiom_count_prose_consistency`, which does exactly that and hard-fails.

### Phase 2 — what was built, and the four scaffolding repairs

Eleven modules under `scripts/validation/checks/`; `validate.py` is framework only. Shared layers:
`_registry` (result types + registry), `_config` (flags), `_tex` (LaTeX), `validate_helpers` (paths).
End-to-end, **48 of 49 characterized checks byte-identical** to the pre-Phase-2 baseline, the one
difference being `graph_integrity`'s node count moving by exactly the 13 guard tests added.

**Three modules split beyond the §4 plan**, each measured first, each on a seam where the halves share no
helpers: `lean_substrate`/`lean_toolchain` · `papers_prose`/`prose_lean_refs` · `bundles_readiness`/`reviews`.
§4's table is a plan; D1's *readable in one pass* is the requirement. The two checks the table never
assigned — `theorems` and `paper_toolchain_pin_drift` — are in `lean_toolchain` and `papers_prose`.

**The guards that made it safe**, all mutation-verified both directions, in
`tests/test_validate_{registry_contract,public_surface,flag_propagation}.py`: registry count + order ·
every check has a declared execution position · the sort runs after the last registration · flags reach
their checks and no module shadows one · no module derives a path from `__file__` · no module aliases a
path by value · no module references a name left behind in `validate.py` · one module identity for
`validate.py` · the frozen external surface.

**Four for four, the scaffolding was defective on first write — and each defect was of the same class the
scaffolding exists to prevent. Three were found by re-reading or by attempting the next step, not by any
test.**

1. **`_CANONICAL_ORDER` + `_apply_canonical_order()`** (H3) — shipped with the call **mid-file**, so 14 of
   59 checks were never sorted and its `raise` could not fire for anything below that line, *including the
   end of the file where a new check naturally goes*. Invisible because the tail was coincidentally
   already in canonical order. Now structural: the call sits below the check-module import block.
2. **`validation/_config.py`** (H5) — one owner for the three runtime flags, reached by attribute so the
   value resolves at call time. ⚠️ **Guard 2 had a hole**, found by attempting the work it protects:
   `co_names` records `LOAD_ATTR` as well as `LOAD_GLOBAL`, so `from validate import STRICT_MODE` still
   showed `STRICT_MODE` in `co_names`. Closed structurally — every consuming check must show `_cfg`, and
   `TestNoCheckModuleShadowsAFlag` asserts no suite module binds a flag in its own namespace at all.
3. **`validation/__init__.py`** — named `validation`, **not** `validate`: a package shadows a same-named
   module on the same `sys.path` entry (verified empirically), so ADR-009 D1's original
   `scripts/validate/` + shim pairing was unbuildable. Corrected in the ADR.
4. **`validation/_registry.py`** — re-exported from `validate` **by binding**; `_CHECKS` must stay the
   SAME list, since registration appends and the canonical sort mutates in place. ⚠️ Extracting it
   surfaced a pre-existing defect: `test_substrate_integrity_gates.py` used `from scripts.validate import`
   while everything else uses `import validate`, loading the file under **two module identities**.
   Survivable while state was per-module (two registries of 59 look like one); fatal once `_CHECKS` became
   a singleton. Never harmless — `isinstance` across the two `CheckResult` classes was silently False.
   `test_validate_is_loaded_exactly_once` guards it via `sys.modules`.

### Standing lessons from this refactor

- **Assume the next piece of scaffolding is defective, and attack it before trusting it.**
- **A failing test is NOT evidence that a guard fired.** Twice a mutation run reported "caught" when the
  test had failed to *collect* — a stray docstring quote (SyntaxError), and a mutation using a name the
  target module does not import (NameError). Every mutation harness must distinguish **"the assertion
  fired"** from **"the mutation broke the import"**, and the mutation must be something a person would
  plausibly write. The `notebooks` extraction's harness does both; copy it.
- **Guard scope must grow with the code it guards.** The H1 test scanned only `validate.py` and would have
  gone blind the moment the first check module landed; it now walks `validation/**/*.py`.
- **Run the WHOLE fast suite.** Removing `validate.STRICT_MODE` broke the one pre-existing strict-mode
  test; targeted runs stayed green and the full suite caught it immediately.
- **A stranded module-level constant is invisible to the test suite.** `_COUNT_LITERAL_PATTERNS`,
  `_NUMERICAL_LITERAL_RE`, `_LATEX_FATAL_RE` passed all 4,986 tests and were caught only by the
  characterization harness, because only it invokes every check.

### Phase 1 delivered (all verified behaviour-preserving)

- `scripts/validate_helpers.py` — the single path anchor + artifact loaders.
- **8 `lean_deps.json` loaders** → one helper; each call site KEEPS its own missing-file verdict, marked
  `TODO(semantic-review, ADR-009 Phase 3)`. **Current measured spread (2026-08-04, post-item-1):
  4 silent PASS** (`tracked_hypothesis_ledger`, `formula_grounding`, `vacuous_statement_audit`,
  `nogo_substrate_integrity`) · **1 PASS-with-warning** (`lean_docstring_refs_resolve`) · **3 FAIL**
  (`prose_theorem_reference_coverage`, `theorem_name_embedded_citations`, and `native_decide_regression`
  since item 1 converted it). ADR-009 H4's "five PASS / two FAIL / one unguarded" is the **pre-fix**
  tally — historical. This divergence is item 4's core population.
- **7 draft-scoping sites** → `all_paper_drafts()`; equivalence proven empirically (all three idioms
  return the identical 64 files).
- **7 module-level path anchors** → aliases of `validate_helpers` (H1).
  ⚠️ **This was INCOMPLETE and the original claim overstated it.** Five `Path(__file__)` derivations
  remained *inside check bodies* — `formulas`, `graph_integrity`, `accepted_findings_carry_rationale`,
  `citation_primary_sources_present`, `quantum_network` — which is exactly where a module move relocates
  them. Measured before fixing: three would have failed loudly, **two would have passed SILENTLY**. All
  five now derive from `validate_helpers`. `test_no_check_derives_a_path_from___file__` makes "H1 is
  closed" checkable, and is the guard to run before EACH module move, not once.
  *(The line citations that accompanied this entry pointed into the 7,778-line file and no longer
  resolve — locate the checks by name.)*
- **14 redundant `sys.path.insert`** + 3 dead `import sys as _sys` + 2 orphaned guards removed.

**Deliberately NOT converted** (pattern-matched but semantically different): the `iterdir` scanning for
`claims_review.json` (different artifact; its `name.startswith('paper')` filter excludes every bundle);
and the three `for code in BUNDLE_CODES` loops (each carries per-site missing-draft reporting that
`bundle_drafts()` would silently drop).

### Phase 0 progress

- ✅ **Guard 1 — registry contract** (`test_validate_registry_contract.py`, 6 tests). Freezes check COUNT
  and registration ORDER + a property test that regenerators precede consumers. Mutation-tested three ways.
- ✅ **Guard 2 — flag propagation** (`test_validate_flag_propagation.py`, 14 tests). Behavioural +
  end-to-end CLI + structural `co_names` legs. Stated coverage limit: no behavioural leg for
  `FORCE_NOTEBOOK_REEXEC` or the `True` direction of `FORCE_LATEX` (too slow) — structural only.
- ✅ **Guard 3 — de-nested the recurrence matcher.** `_RECURRENCE_MIN_TITLE`, `_RECURRENCE_MIN_OVERLAP`,
  `_recurrence_norm` now live at module scope (in `checks/reviews.py` after Phase 2), so
  `tests/test_bundle_formulas_d11_d12.py` binds the REAL matcher instead of re-implementing it. Before
  this, the production matcher could have been deleted or inverted with that test still green.
- ⬜ **Golden per-check `--json` snapshots.** Normalize `elapsed_seconds`, sort details, `PYTHONHASHSEED=0`.
  **Ten quarantined** (planned as nine; `bundle_source_freshness` added at build time) — authoritative set
  is `QUARANTINE` in `tests/validate_characterization.py`.

### Verification loop for any Phase-3 change

```
uv run python tests/validate_characterization.py --record /tmp/before.json   # ~6 min, 49 checks
...make the change...
uv run python tests/validate_characterization.py --record /tmp/after.json
uv run python tests/validate_characterization.py --compare /tmp/before.json /tmp/after.json
```
Run from the repo root. Any `graph_integrity` delta must be **attributed to named test functions**, never
dismissed.

---

## Workstream 2 — ADR-010 (CHARTER AUTHORED, ANALYSIS PENDING — **A SEPARATE GOAL**)

⛔ **NOT part of the ADR-009 goal.** Operator ruling 2026-08-04: the infrastructure goal stays laser-focused
on W1, and ADR-010's analysis is armed as its own goal afterwards. Do not begin it inside the W1 loop, and
do not treat W1's closure as authorization to start it.

**Read [ADR-010](../../adrs/ADR-010-publication-portfolio-reassessment.md) first — it holds the operator's
verbatim framing, the verified constraints, and the open questions.** Summary only, here:

- **Deliverable = the ADR itself**, researched and densely linked. Execution is a LATER goal. No
  manuscript edits, no `PAPER_STRATEGY.md` / `PAPER_DRAFT_MAPPING.md` / `bundle_registry.py` edits.
- **⛔ The roster number is OPEN. Do NOT assume one, and do NOT carry "21 → 14"** — nothing on disk
  supports 14, and it is itself a stale count the audit files as **P0 defect X-11**. The audit's own
  recommendation is **21 → 16** (`SYNTHESIS.md` §5 D-1; `CROSS-portfolio-coherence.md` §6.4, with a full
  per-target table). Treat 16 as *input to evaluate*, not a conclusion. Live registry = **21**.
- **The roster is machine-gated in three legs** (`bundle_registry_consistency`) — leg A ties
  `PAPER_STRATEGY.md` **§6 Summary table** to the registry on codes AND tiers, leg B requires all **7**
  `_ROSTER_CONSUMERS` modules to match exactly, leg C is an AST scan failing any literal with **≥6**
  bundle codes outside `bundle_registry.py`. **A roster recommendation is a change-set, not a number.**
- **Known process-doc drift to fold into that change-set:** Pipeline Invariant #14
  (`WAVE_EXECUTION_PIPELINE.md:689`) enumerates 18 targets (`F, D1–D9, L1–L3, I1–I3, E1, E2`) and
  **cannot legally hold D10–D12**; `PAPER_STRATEGY.md:341` still says "All 14 bundles" (2026-05-07).

**Source audit:** `docs/audits/2026-08-01-publication-readiness/` — `SYNTHESIS.md` (verdict, **80 P0s**,
the systemic finding), `REMEDIATION_PLAN.md` (**BUILD B1–B8 / CORRECT-TO-SUBSTRATE / FACTUAL** triage),
**10 bundle reports** in `bundles/` + **3 `CROSS-*.md`** — 13 auditors, 13 documents, ten of them
per-bundle.

⚠️ **The two lead documents use DIFFERENT vocabularies and are not interchangeable.** "P0" is a severity
label in `SYNTHESIS.md` §1 and the per-finding tables (`X-11`, `X-14`, …). **`REMEDIATION_PLAN.md` contains
the string "P0" zero times** — its §0 explains that `SYNTHESIS.md` §6 Phase 1 was *mis-posed*, pricing the
walk-back as the fix, and re-triages instead. So "remediate every P0 in REMEDIATION_PLAN.md" names a set
that document does not define.

**Governing posture:** [[feedback-remediation-build-dont-walkback]] — fix with substance, not prose. The
publication schedule is the flexible variable; claim strength is not.

---

## Live state / gotchas

- **The suite is RED on the BRANCH, by design — not on `main`.** ⚠️ The reason given here was "`main`
  carries no infra code at all", which is **FALSE** and is corrected in the Git-layout section above:
  `main` carries the entire working validation suite with all 59 checks. What `main` lacks is the
  `scripts/validation/` package and the `stage13_status` guard (zero occurrences there). The checks
  themselves run on `main` today — three of them simply cannot fail there, which is the defect this
  branch repairs. (Audit finding QI-24: the false line survived here after being corrected 40 lines up.) On `infra/adr-009-…`, `readiness_submission_gate` (item 2)
  and the `stage13_status` guard inside `bundle_metadata_matches_graph` both fail; `paper_latex_compiles`
  fails on D3's 2 fatal LaTeX errors. The operator has confirmed they **expect** gates and bundles to go
  red as remediation applies. Suppressing any of them is forbidden.
- **ADR-009's `validate.py:NNNN` citations are HISTORICAL and do not resolve.** They are anchored to the
  7,778-line file; the check bodies now live in `validation/checks/*.py`. Read them as *names* and locate
  by name. The note in ADR-009 that promised Phase 1 would "re-anchor them mechanically" was never acted
  on and is now moot — that is recorded in the ADR itself.
- **Egress guard extended** 2026-08-03 with `isa-afp.org` and a path-scoped `_PATH_WHITELIST` for named
  prover repos; verified 12/12 on an allow/deny matrix including traversal and suffix-confusable hosts.
  This unblocks D12's two prior-art gates, previously mis-recorded as "structurally undischargeable".
- **Do not re-derive the Codex question.** Verified zero coupling to the validation suite; parked in
  `tangential-items.md` T1.
- **`check_theorem_count` hardcodes `expected = 322`** and asserts `TOTAL_THEOREMS ==
  len(ARISTOTLE_THEOREMS) == 322`. Deliberate as a freeze, but it is a hand-typed count inside the
  validation suite — noted so a future session does not mistake it for drift.

---

## Reading order for a cold start

1. **This file.**
1b. **[`docs/audits/2026-08-04-qa-qi-infrastructure/README.md`](../../audits/2026-08-04-qa-qi-infrastructure/README.md)
   — the QA/QI remediation tracker (31 findings, W-A…W-E, all CLOSED). Read it before any validation-suite
   work; several figures in the documents below are superseded by it and are flagged there by
   finding id.**
2. `docs/adrs/ADR-009-validation-suite-modularization.md` — the decision, H1–H5, D2's 8 contract items,
   §Deferred 0–7 (the canonical numbering).
3. `docs/architecture/QA_QI_INFRASTRUCTURE_MAP.md` — the whole quality layer; **§6 (enforcement reality)
   and §7 (the systemic pattern) first**, §9 for the standing measurement lesson.
4. `docs/adrs/ADR-010-publication-portfolio-reassessment.md` — if picking up W2.
5. `docs/audits/2026-08-01-publication-readiness/SYNTHESIS.md` — the evidence base for W2.
6. `.working-docs/validation-module-migration-notes.md` — layout + per-check module assignment.
7. `.working-docs/qa-qi-map-verification-log.md` — only if you need to know how a claim was established.
