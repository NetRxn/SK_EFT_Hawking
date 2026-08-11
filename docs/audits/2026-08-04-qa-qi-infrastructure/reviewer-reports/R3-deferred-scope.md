<!-- Recovered verbatim 2026-08-05 from the subagent transcript
     agent-a5c9590d21c1d550d.jsonl. This is the reviewer's own final report,
     unedited. See ../FINDINGS_REGISTER.md for the consolidated list. -->

I have enough to write this up. Working tree was left untouched (the modifications present are pre-existing session work, not mine).

## Strengths (specific, file:line)

- **`tests/test_cannot_measure_baseline.py:181-204`** — the best ratchet on the branch. It fires in *both* directions (a new silent PASS fails; a site converted to FAIL and left in the baseline also fails, so the ratchet tightens rather than leaving headroom), and `test_scanner_finds_the_population` (`:167-179`) guards the seam so the AST scan cannot go vacuous. This is a ratchet built to be dismantled, not to be lived in.
- **`tests/test_readiness_cannot_measure.py`** — not a ratchet at all, an actual fix. `evaluate_all_gates` exception → `state='blocked'` (was `'open'` → YELLOW), and `_blocked_p1_gates_by_paper` → `None` (was `{}` → licenses GREEN). Both mutation-verified, and `test_green_withheld_when_unverified:105-120` asserts the false-GREEN specifically. The decision to *reverse* the earlier "this belongs to the publication workstream" disposition (ADR-009 §Deferred item 4, `5228ed6d`) is the single best scope call on the branch.
- **`scripts/validation/checks/lean_toolchain.py:224-235`** — `theorems` adopts **FAIL** on missing `lean_deps.json` and says why ("I could not find the Lean is not evidence that the registry is clean"), explicitly declining to widen the H4 divergence. New readers taking the strict policy is the right ratchet direction.
- **`tests/test_lean_scan_coverage.py:20-28`** — ships a *structural* scan, not only a count, with the reasoning recorded; it immediately earned itself by catching a sixth site (`physics.py`, receiver `qn_dir`) the manual sweep missed.
- **QI-30 (`38b496a4`)** — a §4 "cosmetic residual" was re-read on challenge and turned out to be a check whose three legs were all vacuous. The commit message records that its *own earlier mutations were misleading* (caught only against monkeypatched constants). Self-incriminating and correct.
- **Verified independently:** fast suite **5401 passed / 5 skipped / 0 failed** (196.8 s); `_CHECKS` = 59; `MUTATION_VERIFIED` = 59, `AWAITING_MUTATION_TEST` = 0, `AWAITING_CEILING` = 0; branch is 75 ahead of `main`, 0 behind, **not merged**.

---

## Issues

### Critical (Must Fix)

**C1 — "All 59 checks are mutation-verified in both directions" is false at HEAD, and the seam guard built to prevent exactly that claim was defeatable by prose.**
`docs/audits/.../README.md:9-12`, `:75-76`, `:288-299`; `RESUME_STATE.md:26-31`; `ADR-009:840-846`.

I measured HEAD's `MUTATION_VERIFIED` against a docstring-stripped source scan: **`axiom_count_prose_consistency` never references its registered check in code at all** — `git show 38b496a4:tests/test_d5_papers_prose.py` exercises only the pure core `_axiom_prose_findings` (`:144-187`). The seam guard `test_verified_entries_name_a_real_test` (HEAD, `test_d5_mutation_obligation.py:574-588`) matched **raw file text**, and these files describe in prose every check they cover — so a prose mention satisfied it. The file's own §3 states the guard's purpose: *"promoting a name out of the backlog cannot be free."* At HEAD it was free.

The uncommitted working tree already contains the fix (`_code_only()` + resolve the function name from the live registry) and its docstring records "**3 of 59 entries were satisfied by prose alone**". The same uncommitted diff rewrites `TestBundleFigureIntegrity` (`test_d5_bundles_readiness.py`) because at HEAD it *"patched `bundle_figure_typeset_pt` and then pointed `PAPERS_DIR` at an empty tmp tree — so every PNG was absent, the check took its `missing_png` branch and `continue`d, and the patched function was never called. It asserted `passed is False` and passed, for a reason unrelated to its name, while `if pt < FLOOR_PT:` had no coverage at all."*

So at HEAD there are at least three confirmed-hollow entries inside the 59, plus `theorems` (QI-30's own admission that its mutations bypassed the import assert). All four were found by *challenge or review*, none by the mechanism. **Fix:** land the working-tree seam-guard fix and the two test rewrites, then re-run the seam guard over all 59 and restate the headline as what the registry actually proves ("every check has a declared, code-reachable test; N re-verified under the strengthened predicate"). Do not merge with the current headline standing.

**C2 — QI-30's new invalidating criterion was applied to one check and never swept.**
`README.md:266-269`.
QI-30 introduces: *"A mutation caught against a patched fixture does not establish that the check can fail in production."* It is recorded as "residue worth carrying forward" and nothing else happens. That is the audit's own most-repeated failure shape (QI-01: *"This class was already fixed once in `freshness.py` and not swept"*). C1 shows the sweep would have found more. `constants.py` has exactly one import-time assert (`:1372`), so the *narrow* mechanism is unique — but the general criterion (test bypasses a guard the check cannot bypass in production) is not. **Fix:** re-read the 59 `MUTATION_VERIFIED` entries against the criterion before declaring the audit closed, or state explicitly that the criterion is un-swept and reopen QI-30 as partially closed.

### Important (Should Fix)

**I1 — QI-16 is marked FIXED but the stated remedy is not implemented.**
`README.md:214` claims *"4 wrong §Deferred ordinals corrected."* The §Deferred preamble (`ADR-009:412-419`) declares the 0–7 numbering canonical and says *"every cross-reference must carry the §Deferred ordinal."* The sweep covered `scripts/validation/checks/*` only. Still wrong at HEAD:
- `tests/test_always_pass_dispositions.py:1` and `:127` — "ADR-009 Phase 3 item 2" for §Deferred item **3**; `:4` says `readiness_submission_gate` "was item 1", it is item **2**.
- `tests/test_native_decide_ratchet.py:1` — "Phase 3 item 3" for §Deferred item **1** (and `:118` in the same file correctly says item 1 — self-contradictory).
- `tests/test_readiness_submission_gate.py:111` — "§Deferred item 1" for item **2**.
- `scripts/update_counts.py:96` — "ADR-009 Phase 3 item 3" for item **1**.

**Fix:** sweep `tests/` and `scripts/` (not just `scripts/validation/`), or downgrade QI-16 to partially closed.

**I2 — `RESUME_STATE.md` still carries three claims the audit says it corrected. This is the document a cold session reads first — QI-23 called that "the highest-cost item in the whole audit."**
- `:296` — *"⚠️ `build_graph.py` NOT read in full — implementing this later requires that read first."* QI-21 (`README.md:219`) and `ADR-009:522-526` both say the read is discharged. Direct contradiction.
- `:309-311` — item 4's readiness sites recorded as *"Out of the ratchet's reach, by scope … Readiness-layer work → publication workstream."* QI-21 says that disposition was **wrong** and both were closed by `5228ed6d`. The audit's §2 table (`README.md:91`) names RESUME_STATE for this exact row and asserts *"All six rows are now corrected."* Only the top banner (`:17-19`) was corrected; the body 290 lines down was not — the *identical* "survived 40 lines below its own correction" pattern QI-24 fixed once already.
- `:216` — *"Post-delivery audit found 27 further items"* (now 31).

`3730f4ed`'s message shows why: its RESUME_STATE scope was banner + suite figure + ahead-count, not a sweep. **Fix:** sweep the whole file; the ahead-count (`:162`, "56") is now 75.

**I3 — §Deferred item 6's headline verdict overstates its own measurement.**
`ADR-009:721-730` concludes *"**Disposition: DECLINE.** There is no defect to fix here."* Its own next paragraph says *"**five strict legs enforce concerns that no ReadinessGate covers**, and because nothing automated passes `--strict`, those five are exercised only if a human runs the flag."* I confirmed there is **no `.github/workflows` directory at all** and no submission-gate runner in `scripts/`; `WAVE_EXECUTION_PIPELINE.md:685` calls `--strict` *"mandatory at the Paper Submission Gate"* and `scripts/check_bundle_source_freshness.py:23` says it is enforced *"via `validate.py --strict`."* An invariant declared mandatory with nothing that runs it is a defect in enforcement even if the decision about *what to do* is the operator's. **Fix:** restate as "DECLINE the filed remedy; five strict legs remain unenforced — operator decision pending," so the residue is not hidden behind "no defect."

**I4 — QI-15 converted a live inconsistency from tracked debt into declared intent, on the strength of a decline that was about something else.**
`README.md:213`; markers at `lean_substrate.py:480-492`, `lean_statements.py:297-309`, `:463`, `:546`, `prose_lean_refs.py:432-443`, `:666`, `lean_toolchain.py:642-652`.
H4 (`ADR-009:270-279`) shipped each `lean_deps` loader with a per-site policy *"each marked `TODO(semantic-review)`"*, and §Alternatives 1 (`:391-394`) uses the divergence as a **live defect** justifying the whole ADR: *"five checks currently pass on a missing `lean_deps.json` while two fail, and no reader of any single check can see that."* Item 4 declined converting the 22 **wholesale**, and explicitly kept these eight *"marked `TODO(semantic-review)` so it stays visible."* QI-15 then removed the TODOs and relabelled them *"H4 DIVERGENCE, deliberately preserved."* No per-site decision was ever recorded for why `formula_grounding` passes on a missing artifact while `prose_theorem_reference_coverage` fails. **Fix:** either make the eight per-site decisions (the honest form of item 4), or restore a tracking marker; "deliberate" should not be inherited from a decline of a different remedy.

**I5 — §4 residual "path-alias guard's BinOp gap" understates what the guard concedes.**
`README.md:378-382`; `tests/test_validate_public_surface.py:339-341` — the guard's own message says the BinOp form *"freezes the same way if the base is patched."* That is the H1/H5 hazard verbatim, and QI-11 (`README.md:198-209`) fixed five sites of the same shape *as a defect* on the grounds that *"a test monkeypatching the anchor reached some sites and not others."* Four of the five remaining sites are mitigated by explicit pinning tests (`test_d5_freshness.py:534-543`, `test_d5_notebooks.py:295-306`); **`prose_lean_refs._PHYSLIB_DIR:290` has none.** Inconsistent disposition. **Fix:** extend the guard to `BinOp` with an allow-list of pinned sites, and pin `_PHYSLIB_DIR`.

**I6 — QI-01's fix is Lean-only; the same class is live one directory over and the guard is structurally blind to it.**
`scripts/build_graph.py:1465` — `extract_python_test_nodes` uses `tests_dir.glob("test_*.py")`, non-recursive. Measured: **162 top-level files / 4,795 `def test_*` vs 174 / 4,825 recursive — 12 files and 30 test functions in `tests/e2e/` mint no `PythonTest` node**, so any VERIFIES coverage they carry is invisible to Gate 4. `TestGraphTestNodeCoverage` (`test_validate_public_surface.py:421-439`) counts with the *same* non-recursive glob, so its count assertion agrees vacuously — precisely the failure §4b names (*"a count assertion … only protects sites that already exist"*). `tests/test_lean_scan_coverage.py`'s structural leg matches only `\.glob\(["']\*\.lean["']\)`. Latent (e2e are dashboard smoke tests), same posture as QI-01 — which *was* filed. **Fix:** `rglob`, and generalise the structural leg beyond `*.lean`.

**I7 — Map §3's five documented silent-drop points are neither findings nor §4 residuals.**
`QA_QI_INFRASTRUCTURE_MAP.md:216-220`. Drop point **#2** — `_emit` is a no-op when the FLAGS target is absent from `node_ids`, *"no log. This produced the D11 false-green"* — is confirmed live at `build_graph.py:3664-3667`. Drop point **#4** — `papers/AutomatedReviews/*/*.md` is a one-level glob (`build_graph.py:1731`); I confirmed no review sits deeper today, so it is latent *exactly as QI-01 was*, and QI-01 was filed. An audit that closes 31 findings while leaving a documented, already-damaging silent drop untriaged in a companion document has an incomplete §4. **Fix:** triage §3's five points into findings or §4 residuals with the same measured posture used for QI-01.

**I8 — `provenance_dashboard.py`'s exclusion from the QI-01 guard is asserted, not measured.**
`tests/test_lean_scan_coverage.py:54-56`: *"the provenance dashboard is deliberately EXCLUDED — it is a read-only human surface, not an enforcement path, and holds its own non-recursive globs by choice."* Nothing in `provenance_dashboard.py` says "by choice"; there is no such comment at any of its four sites (`:231`, `:426`, `:509`, `:882`). And `:231` is a **cache fingerprint** — a subdirectory-only Lean edit does not invalidate the dashboard cache, which is functionally identical to `compute_source_hash`, the QI-01 site that *was* fixed. The dashboard is also where Invariant #8 human parameter verification happens, and that verification is a gate input. In an audit whose standing rule is "measure, don't inherit," this exclusion is inherited. **Fix:** measure the four sites' consumers, then either fix or record the measurement.

**I9 — The "eight always-pass checks" population (item 3) was wrong and nothing re-measured it.**
QI-30 established `theorems` "had been green since it was written" because it could not fail — a ninth. The AST-shaped scan that produced "eight" saw `theorems` return `passed=False` syntactically and stopped there. `QA_QI_INFRASTRUCTURE_MAP.md:311-313` still says *"Eight checks were structurally incapable of returning `passed=False`. Four remain."* **Fix:** re-run the population measurement with a semantic-reachability criterion, or state that "eight" is a syntactic lower bound.

### Minor

- **M1 — audit README §4c is stale in three ways.** `:443` says *"All four workstreams complete — 29 of 29 findings closed"*; there are **five** workstreams (W-A…W-E, per `:3`) and **31** findings (per `:3-6`, which explicitly warns "re-count the boxes"). `:444` and `:15` say *"5398 passed"*; measured 5401 (and `38b496a4`'s own message says "5398 → 5401"). The commit that added QI-30 updated the header count and not §4c.
- **M2 — `ADR-009:820-821`** still says the audit *"records **29 findings** … (QI-01…QI-28 plus the QI-26b sub-finding)"*, and `:830` *"one live enforcement hole"*. QI-29/QI-30 landed after and the governing ADR was not updated.
- **M3 — QI-30's latent-exposure measurement is missing.** QI-01 and QI-28 both state "measured verdict movement: **0**". QI-30 does not. I measured it: none of the 14 unresolved `ARISTOTLE_THEOREMS` keys appears in `src/core/formulas.py`, so nothing is currently laundered. Worth recording so the ratchet's frozen debt is known-inert.
- **M4 — `_iter_test_functions` residual (`README.md:391-394`) misdescribes the failure.** `build_graph.py:1428-1432` walks the outer class *and* the inner class, so a nested test class yields the same function twice under different qualifiers → **two** nodes for one `def`. `TestGraphTestNodeCoverage` would then fail with *"N silently dropped"* and a **negative** count, while `test_node_ids_are_unique` passes. That is not "the correct behaviour"; it is a misleading failure on legitimate code.
- **M5 — commit messages consistently use the RESUME_STATE cost ordering** (`fd470314` "Phase 3 item 1", `c3456a23` "item 2", `9532ba76` "item 3") against the §Deferred canonical 0–7. History is immutable; noting it because the code comments in I1 inherited it.
- **M6 — my 5401-test run was against the dirty tree**, which carries the C1 remediation. A clean-HEAD count will be lower.

---

## Table: every ratchet on this branch

| Ratchet | Frozen | Live (measured 2026-08-04) | Path to reduction? | Verdict |
|---|---|---|---|---|
| `COUNT_LITERAL_CEILING` (**new**, `constants.py:2443`) | 107 | **107** — zero headroom | ✅ emits *"lower the ceiling"* when below; remedy named (`counts.tex` macros) | **Legitimate.** Replaces a promise whose trigger receded (15→64 papers) with one binding today. |
| `NUMERICAL_LITERAL_CEILING` (**new**, `:2444`) | 116 | **116** — zero headroom | ✅ same | **Legitimate.** |
| `ARISTOTLE_REGISTRY_UNRESOLVED_CEILING` (**new**, `:1389`) | 14 | **14** — zero headroom | ✅ dedicated `ratchet` detail asks to lower it | **Legitimate**, and it replaced a vacuous check with a real one. See M3. |
| `CANNOT_MEASURE_PASS_BASELINE` (**new**, `test_cannot_measure_baseline.py:82`) | 22 pairs | 22 — zero headroom, **bidirectional**, seam-guarded | ⚠️ partial — 5 optional-toolchain and 3 advisory are justified; **8 H4 sites have no stated path** (see I4) | **Mechanism excellent; framing of 8 of 22 questionable.** |
| `AWAITING_CEILING` (**new**, `test_d5_mutation_obligation.py:503`) | 0 | **0**; companion test asserts ceiling *equals* backlog | ✅ at floor by construction | **Legitimate mechanism.** But what it ratchets (registry membership) is weaker than the claim built on it — C1. |
| `NATIVE_DECIDE_DECL_CLOSURE_CEILING` (pre-existing; **measurement changed** by item 1) | 546 | **546** — zero headroom | ✅ ADR-002 owns elimination policy | **Legitimate; strengthened** (now reads `lean_deps.json` content-hash, not `counts.json` mtime). |
| `_LEDGER_DANGLING_BASELINE` (pre-existing, **relocated** to `graph_atlas.py:182`) | 66 | **66** — zero headroom | ⚠️ none stated; annotated debt | **Legitimate**; the 67→66 headroom removal is documented in-place. |
| `VACUOUS_STATEMENT_BASELINE` (pre-existing, identity-pinned frozenset) | frozen set | unchanged by branch | ✅ named "Vacuous Statement Sweep" tracker | Out of scope for this branch. |
| `EXPECTED_SURFACE` 54 / `EXPECTED_CHECKS` / `QUARANTINE` 10 (**new** contract freezes) | 54 / 59 / 10 | verified 54 / 59 / 10 | n/a — contracts, not debt | **Legitimate.** Independently frozen from production, correctly. |

**No ratchet on this branch carries headroom.** That is genuinely unusual and to the branch's credit — the one that did (`ledger_ids_resolve`, 67 vs 66) was tightened. The ratchets are not being used to dodge work; the *dispositions around two of them* (I4, C1) are where scope leaked.

---

## Table: every DECLINED / deferred item

| id | Stated reason | Justified? |
|---|---|---|
| **§D-0, 2nd half** — shared graph handle | Measured 5 invocations / 45.4 s = **8%** of a 447 s run (not the ADR's own ~27%); correct pattern is caller-side fingerprint + lock (dashboard); a validate-side handle is a 3-module signature change | **YES.** Measurement replaced the ADR's own estimate downward and the decline followed. The `build_graph.py`-read precondition was discharged. §4 records the cheaper sub-finding (3×/2× redundant extractors) rather than acting — acceptable. |
| **§D-3** — 4 checks kept advisory | Per-check reasoning: `elaboration_knob_watchlist` (kernel re-checks the term; knobs add nothing to the axiom closure), `paper_toolchain_pin_drift` (auto-fail pushes authors to find-and-replace), `viz_consistency` (shipped artifacts gated by `bundle_figure_integrity`), `inventory_index_autogen_fresh` (`sync.py --fast` regenerates every commit) | **YES for all four.** Each argument is about what the check *measures*, not about cost. The other four were converted, which is the tell that the line was drawn honestly. |
| **§D-4** — add `UNEVALUATED` state | `CheckResult.passed` is D2 contract item 5; `--json`, `gate_precheck.py`, `pre-commit-sync.sh` all read it | **YES.** Contract break, correctly identified. |
| **§D-4** — convert the 22 wholesale | Heterogeneous: 5 optional-toolchain, 3 advisory-by-design, 8 H4 divergence, 2 H1-silent; H4 forbids unify-by-refactor | **PARTIALLY.** Declining the *wholesale* sweep is right. But item 4 kept the 8 as visible TODOs and QI-15 then declared them intentional — the per-site decisions H4 demanded were never made (I4). |
| **§D-5** — merge `count_literals` into `axiom_count_prose_consistency` | Both bodies read; premise false twice over — `count_literals` is no longer always-pass, and the two are different predicates (density vs value-comparison-to-truth) | **YES**, and exemplary: the decline names the inverse as the real finding (*raise `count_literals` to compare against `counts.tex` macro values*). That residue is recorded, unscheduled. |
| **§D-6** — `--strict` unreachable | Count corrected 2→6; `--strict` is the documented Paper Submission Gate; ReadinessGates mechanize submission readiness | **PARTIALLY — headline overstated.** The measurement is solid and the correction of the filing is right, but *"There is no defect to fix here"* is contradicted by the same item's residue: 5 of 6 strict legs are covered by no gate, no CI exists, and nothing passes the flag. See I3. |
| **§4 residual** — path-alias BinOp gap | *"a known, deliberate limit"* documented in the guard's own message | **NO — should be a defect.** Same shape as QI-11, which was fixed as one. `_PHYSLIB_DIR` unpinned. See I5. |
| **§4 residual** — `check_theorem_count` hardcodes 322 | *(struck)* promoted to QI-30 | **Correctly promoted.** The precedent the owner cited. |
| **§4 residual** — graph build cost (3×/2× extractors) | Substance behind the declined §D-0 handle | **YES** — genuinely an optimisation. |
| **§4 residual** — `sys.path` growth (4 sites, unbounded in the dashboard process) | recorded | **YES, minor.** |
| **§4 residual** — `_iter_test_functions` nested-class double-count | *"latent-but-guarded … which is the correct behaviour"* | **NO — misdescribed.** It double-*mints*, and the guard's failure message would misdiagnose it as a drop with a negative count. See M4. |
| **Map §3 drops #1–#5** | documented in the map, never triaged | **NO — should be findings or §4 residuals.** #2 already produced the D11 false-green and is still unlogged; #4 is a latent non-recursive glob, the exact posture that got QI-01 filed. See I7. |

---

## Assessment

**Ready to merge?** **No** — with fixes.

**Reasoning:** The engineering is strong and the ratchets are honest (every one sits at zero headroom with a stated reduction path — they are staging debt, not hiding it), but the branch's headline deliverable is overstated: at HEAD, the D5 seam guard could be satisfied by a docstring mention, `axiom_count_prose_consistency`'s "mutation-verified" test never invokes its check, and `bundle_figure_integrity`'s test passed for a reason unrelated to its name — so "all 59 mutation-verified in both directions" is not true as written, and the tree already carries the un-committed fix that proves it. Land C1/C2, sweep the four documents that still contradict the code (I1, I2), and re-word the item-6 decline (I3); the remaining items are genuine but can follow.
