# QA/QI Infrastructure Audit — 2026-08-04

**Status:** 🟡 **W-A / W-B / W-C COMPLETE — W-D remains.** 26 of 27 findings closed; the one open
item is QI-27 (D5: mutation tests for 43 checks + a mechanical gate). This is the live tracker —
update the checkboxes in §3 as work lands and keep the measurement column honest.

**Verified at the last increment:** fast suite **5080 passed / 5 skipped / 0 failed**;
characterization **HELD — 49 checks identical** across W-B and W-C; the two W-A behaviour changes
each attributed in full. Branch **56 commits ahead of `main`, 0 behind — NOT merged.**

**Scope.** The complete QA/QI enforcement surface on `infra/adr-009-validation-modularization`:
`scripts/validate.py`, all 12 `scripts/validation/**`, `scripts/validate_helpers.py`,
`scripts/readiness_gates.py`, `scripts/bundle_readiness.py`, `scripts/build_graph.py`,
`scripts/graph_integrity.py`, `scripts/gate_precheck.py`, `tests/validate_characterization.py`,
and the governing documents (ADR-009, `QA_QI_INFRASTRUCTURE_MAP.md`, `RESUME_STATE.md`,
`.working-docs/*`).

**Method.** Every file above read **in full, directly**, per the operator's standing read mandate —
including `scripts/build_graph.py` (4,207 lines), which `RESUME_STATE.md` had recorded as
never read and which ADR-009 §Deferred item 0 names as a precondition for the shared-graph-handle
work. ~17,700 lines total. Every load-bearing figure below is **measured on 2026-08-04**, not
inherited; where a claim rests on something else it is marked.

**Relationship to the 2026-08-01 publication-readiness audit.** That audit's §2 systemic finding —
*"the project's quality instrumentation reports absence-of-measurement as success"* — is why ADR-009
exists. ADR-009 Phases 0–3 fixed the instrumentation defects that audit could see **from the
outside**, by reading check verdicts. This audit is the inside view: it reads the enforcement code
itself and finds the residue. See
[`../2026-08-01-publication-readiness/SYNTHESIS.md`](../2026-08-01-publication-readiness/SYNTHESIS.md).

---

## 1. Verdict

**ADR-009's delivery is real and holds under inspection.** Independently re-verified on HEAD:
59 checks across 12 modules, `validate.py` registers 0, `--list` 59, unknown `--check` exits 2,
`BUNDLE_CODES` 21, `EXPECTED_SURFACE` 54, `QUARANTINE` 10, fast suite **5055 passed / 5 skipped /
0 failed**, `validate.py` 57/59 with 2 intentional reds. The shared-helper layer is genuine and its
policy line (*"this module owns where things are, not what their absence means"*) is held in code.

**What was not done is the layer underneath the check verdicts.** Four kinds, all now closed except
the last:

1. ✅ **One live enforcement hole** — a third of the Lean substrate unscanned by **six** glob sites
   (QI-01). Measured verdict movement: **zero**, so it closed a latent hole rather than surfacing
   live debt.
2. ✅ **Duplicated predicates** across subsystems a check requires to agree (QI-02, QI-03).
3. ✅ **Dead and doubled code** in the enforcement path (QI-05 … QI-11).
4. ✅ **Documentation contradicting the code it describes** — including three in-code headers telling
   a reader a repaired check was still broken (QI-12 … QI-26b).

⬜ **Remaining: the standing obligation ADR-009 itself calls the disease** — **D5 has no mechanical
enforcement, and 32 of 59 checks have no test at all** (QI-27).

---

## 2. The shape of what is left

The 2026-08-01 audit found *checks that reported success while measuring nothing*. Phase 3 fixed
those. What this read finds is the same shape one layer down:

| | reports | actually |
|---|---|---|
| `extract_placeholder_marker_nodes` | "these are the placeholders" | scans 1,373 of 2,039 Lean files — **112 placeholder theorems mint no node**, and P1 Gate 5 reads those nodes |
| `compute_source_hash` | the graph's staleness key | hashes 67% of the Lean tree; a subdirectory-only change is invisible to it |
| `bundles_readiness.py` header | *"readiness_submission_gate IS INVERTED AND CANNOT BLOCK … do not fix it"* | it was fixed on 2026-08-03 and hard-fails |
| `paper_latex_compiles` `--list` text + docstring | "advisory; always passes" | hard-fails since 2026-08-03 |
| ADR-009 §Deferred, map §4/§7, RESUME_STATE | two readiness sites "remain open BY SCOPE" | both closed by `5228ed6d` |
| RESUME_STATE headline | "the branch merged to `main`" | not merged — a cold session reads this first |

**All six rows are now corrected.** They are kept as the record of what the documents said, because
the pattern matters more than any individual line: every one of them was written true and became
false when a later commit landed without returning to it.

**A document that describes a repaired guard as broken is the same defect class as a guard that
cannot fire** — both make the reader's model of the system wrong in the direction of false
confidence. That is why the documentation items below are tracked as findings, not as tidying.

---

## 3. Status board

Legend: ⬜ open · 🔄 in progress · ✅ done (with the verifying evidence named).

### W-A — enforcement holes

- [x] **QI-01** ✅ **FIXED 2026-08-04.** Non-recursive Lean globs: **6** sites saw 1,373 of 2,039
      files (+666). Worst was `build_graph.extract_placeholder_marker_nodes` → unminted
      `PlaceholderMarker` nodes feeding P1 Gate 5. Measured verdict movement on the current tree:
      **0** (no paper cites any of them by `\texttt` name; exactly one is formula-reachable,
      `readoutDecayProb_eq_cohGamma`, and no paper's `key_claims` ground on its formula
      `teleport_avg_fidelity`) — so this closed a latent hole rather than surfacing live debt, the
      same posture as `5228ed6d`.
      ⚠️ This class was already fixed once in `freshness.py:74` (ADR-004 W7 finding M2) and not swept.
      **Sites:** `build_graph` ×2 (`compute_source_hash`, `extract_placeholder_marker_nodes`),
      `lean_toolchain.check_lean_source`, `papers_prose.check_paper_provenance`,
      `lean_substrate.check_formulas_to_theorems`, `physics.check_quantum_network`.
      **Result:** PlaceholderMarker 593 → **707** (+114), 0 id collisions, every `lean_file` resolves.
      Node ids now carry the module PATH (`APSEta.Predicate`), because a bare stem would have
      collided across packages — the §Deferred-item-7 key defect, re-reachable the moment recursion
      landed.
      **Guard:** `tests/test_lean_scan_coverage.py` — 6 tests, mutation-verified both directions,
      with a scanner-seam test so the structural leg cannot go vacuous.
      ⚠️ **The structural leg earned itself immediately:** it caught a **sixth** site
      (`physics.py`, receiver named `qn_dir`) that the manual grep sweep missed. A count assertion
      would not have — it only protects sites that already exist. That is the leg that would have
      caught the original defect, since `freshness.py` was correct while its siblings were not.
- [x] **QI-02** ✅ **FIXED 2026-08-04.** Unit-literal predicate duplicated:
      `papers_prose._NUMERICAL_LITERAL_RE` and an inline `lit_re` in
      `readiness_gates._eval_numerical_freshness` — feeding `numerical_literals` and **P2 Gate 9**,
      the two verdicts `readiness_verdicts_agree` exists to keep consistent. A divergence between
      them would have been introduced inside that check's own blind spot.
      **Proved identical first** (pattern string, flags, *and* the surrounding two-step
      `\input{tables/}` + `\caption{}` strip), so the merge is behaviour-preserving. Now one owner:
      `validation/_tex.find_inline_numerical_literals`, imported by both. `_tex` imports nothing from
      the suite, so `readiness_gates` importing it cannot close a cycle with
      `bundles_readiness → readiness_gates`. Verified: D1 yields 13 literals before and after.
- [x] **QI-03** ✅ **FIXED 2026-08-04, after the filing was refuted by measurement.** See the
      re-scoping note below — it is kept verbatim because the correction is the point.
      **What landed:** `_clean_lean_ref` is the single owner; it now strips a leading dot and keeps
      Lean prime names while staying `\w`-based so Unicode identifiers survive.
      `extract_verified_by_edges` no longer carries its own parser.
      **Measured:** refs 509 → **514** (+5, every one resolves; 0 newly rejected; dangling unchanged
      at 4, so no `formula_grounding` movement). VERIFIED_BY **529 → 533**. Characterization:
      +8 nodes (the guard file's 8 tests), +4 edges, **broken_chains 40 → 36** — four formulas gained
      their first verification link. No check verdict moved.
      **Guard:** `tests/test_lean_ref_normalizer.py`, 19 tests, 4 AST-scoped mutations caught.
      ⚠️ **A fifth mutation was NOT caught, and that is recorded on purpose.** My first draft carried
      a separate `any(c in tok for c in "{}*/\\")` rejection; mutating it to `if False:` failed no
      test, because the `\w` fullmatch below already rejects those characters. It was **deleted** —
      shipping a guard that cannot fire, inside the audit that exists to delete them, would have been
      the same defect one layer down.
      ⬜ **Residue, not fixed:** `_parse_formula_lean_refs` (the `formula_grounding` gate) still
      disagrees with the graph label on **55 names**, though `_clean_lean_ref`'s docstring claims it
      mirrors that function. The gate is currently clean (0 dangling), so reconciling it carries
      verdict risk with no demonstrated defect behind it yet. Needs its own measured increment.

  <details><summary>Original filing, kept as the record of what was wrong</summary>

  ⚠️ **RE-SCOPED 2026-08-04 — my own filing was wrong; do NOT unify these blindly.**
      Filed as "three implementations, unify behind one owner". **Measured, that fix is a
      regression.** The three are `build_graph._clean_lean_ref` (509 refs),
      `build_graph.extract_verified_by_edges`'s inline `split('(')[0].split(' ')[0]` (538), and
      `lean_statements._parse_formula_lean_refs` (522).
      - The inline parser accepts **33 junk tokens** the others reject — `'N/A'`, `'K0E0'`, `'2'`,
        `'16}_num'` — and feeds them to `_resolve_lean_short`. That is the §Deferred-item-7 hazard
        (unfiltered tokens into a short-name resolver).
      - **But `_clean_lean_ref` is also wrong**: switching the inline site to it **loses 5 genuine
        VERIFIED_BY edges and gains 4**. Its `[A-Za-z_][\w.]*` guard rejects a **leading-dot** ref
        (`.dean_adiabatic` → `QuasiOneDReduction.dean_adiabatic`) and every **Lean prime name**
        (`haldaneD_diracK'`). Those are real theorems and real coverage.
      - `_clean_lean_ref`'s docstring claims it "mirrors `_parse_formula_lean_refs` so the graph
        label agrees with the `formula_grounding` gate". Measured: the two disagree on **55 names**.
      **Disposition: needs ONE correct parser** (leading dots, prime names, em-dash descriptions,
      parentheticals, junk rejection) written as its own reviewed increment with a mutation test and
      an attributed edge delta — not folded into a mechanical pass. Mixing them is what the ADR
      forbids. **Scope figures above are measured; the original filing's was not.**

  </details>
- [x] **QI-04** ✅ **FIXED 2026-08-04.** `bundle_readiness._blocked_p1_gates_by_paper` was annotated
      `-> dict[str, list[str]]` while returning `None` on its exception path — a type lie in the
      function whose `None`-vs-`{}` distinction is the entire point of `5228ed6d`. Now
      `-> dict[str, list[str]] | None`, with the summary line saying so.

### W-B — dead / doubled code

- [x] **QI-05** ✅ **FIXED 2026-08-04.** `readiness_gates._eval_citation_integrity` — `paper_key`
      computed from `meta.topic`/`name`, then overwritten on the next line by the `paper['id']` form
      every other evaluator uses. Dead assignment removed.
- [x] **QI-06** ✅ **FIXED 2026-08-04.** `build_graph.extract_cites_theorem_edges` — `for node_id in node_ids: pass`, a dead loop over ~46,700 ids.
- [x] **QI-07** ✅ **FIXED 2026-08-04.** `reviews.check_recurrence_reopens_closures` — vestigial `if True:`.
- [x] **QI-08** ✅ **FIXED 2026-08-04.** `citations.check_bibitem_title_primary_source` — `summary_passed` computed then overwritten by a no-op `if`; its comment ALSO claimed DROP-WORD flags fail in default mode, which the body contradicts. Both corrected.
- [x] **QI-09** ✅ **FIXED 2026-08-04.** `reviews._carries_findings` — the same `any()` computed twice (`findall` then `finditer`); `_SEVERITY_HEADING` has only non-capturing groups so the two legs were identical. Proved equivalent over all **273** review documents before collapsing.
- [x] **QI-10** ✅ **FIXED 2026-08-04.** Dead imports: `numpy` in `citations._lookup_provenance_value`, `importlib` in `notebooks.check_viz_consistency`.
- [x] **QI-11** ✅ **FIXED 2026-08-04.** Import and path hygiene, AST-verified rather than grepped.
      Module-level `json` (citations), `re` and `BUNDLE_CODES` (bundles_readiness) never referenced —
      the four `re.` grep hits in the latter are all PROSE ("re-exported", "elsewhere."), which is why
      this was settled by AST. **7 function-local imports** shadowing a module-level one removed across
      `citations` / `bundles_readiness` / `lean_toolchain` / `readiness_gates`; **zero remain
      suite-wide**. `_H.LEAN_DIR` was re-derived as `_H.PROJECT_ROOT / "lean" / "SKEFTHawking"` at
      **5 sites** — same value, second definition, so a test monkeypatching the anchor reached some
      sites and not others (the by-value hazard H1/H5 exist to prevent, one level down); verified
      identical before collapsing. Incidentally this made `lean_toolchain`'s module header true again.
      ⬜ **Not done:** the lake-resolution block duplicated verbatim between `check_lean_build` and
      `check_axiom_closure_allowlist` — a genuine 6-line copy, but extracting it touches two checks'
      early-return behaviour and belongs with their mutation tests in W-D.
- [x] **QI-12** ✅ **FIXED 2026-08-04.** `bundles_readiness.py` header declared `readiness_submission_gate` inverted and told the reader not to fix it. Rewritten; it hard-fails.
- [x] **QI-13** ✅ **FIXED 2026-08-04.** `paper_latex_compiles` — `--list` description, docstring opener, Posture bullet and module header all said "advisory / always passes". All four corrected; it hard-fails.
- [x] **QI-14** ✅ **FIXED 2026-08-04.** `count_literals` / `numerical_literals` docstrings still promised a future escalation ("once all 15 papers use macros") that the 64-paper corpus had made unreachable. Both now describe the ratchet.
- [x] **QI-15** ✅ **FIXED 2026-08-04.** 7 `TODO(semantic-review, ADR-009 Phase 3)` markers re-labelled as the deliberate H4 divergence they are — the phase is complete and item 4 DECLINED the sweep.
- [x] **QI-16** ✅ **FIXED 2026-08-04.** 4 wrong §Deferred ordinals corrected (`papers_prose` ×3 said "Phase 3 item 2" for item 3; `bundles_readiness` said item 1 for item 2). `lean_toolchain`'s "item 1" was already correct and was left.
- [x] **QI-17** ✅ **FIXED 2026-08-04.** `_registry.py` "33 names" → point at `EXPECTED_SURFACE` (54); "~20 sites" → the measured 60 sites / 25 PASS / 22 pairs, with item 4's DECLINE recorded.
- [x] **QI-18** ✅ **FIXED 2026-08-04.** `validate_helpers.py`'s NO-MEMOIZATION section described the pre-item-0 reader divergence as current, contradicting `ensure_lean_deps_fresh` sixty lines below in the same file.
- [x] **QI-19** ✅ **FIXED 2026-08-04.** `validate_characterization.py` — "RED on `main`" (main has zero `stage13_status`), "Nine checks" (QUARANTINE has 10), "item 7 filed, not fixed" (fixed 2026-08-03).
- [x] **QI-20** ✅ **FIXED 2026-08-04.** `test_cannot_measure_baseline.py` docstring described both readiness sites as live defects; both closed by `5228ed6d`.
- [x] **QI-21** ✅ **FIXED 2026-08-04.** ADR-009 §Deferred status block and item 4 recorded the two readiness sites as open/out-of-scope. Also discharged item 0's "`build_graph.py` has NOT been read" precondition.
- [x] **QI-22** ✅ **FIXED 2026-08-04.** QA/QI map §4, §7 (both rows + "four of eight" → six), §1 mermaid (11 → 12 modules), the re-basis note's build_graph caveat, and the superseded banner.
- [x] **QI-23** ✅ **FIXED 2026-08-04.** `RESUME_STATE.md`'s headline claimed the branch was **merged
      to `main`**. It is not — currently **56 ahead, 0 behind**. A cold session reads that block
      first, so the false claim was the highest-cost item in the whole audit. Corrected, with
      `git merge-base --is-ancestor HEAD main` inline so the claim is re-checkable rather than
      re-inherited. The companion line at the foot of the file ("`main` carries no infra code at all")
      — which had survived 40 lines below its own correction — is fixed under QI-24.
- [x] **QI-24** ✅ **FIXED 2026-08-04.** RESUME_STATE internal drift: W1 status, ADR status PROPOSED, commit count, suite count, module sizes, the NOT-yet-read list, and the "main carries no infra code" line that survived 40 lines below its own correction.
- [x] **QI-25** ✅ **FIXED 2026-08-04.** `validation-module-migration-notes.md` §7 "items 0,4,5,6 open" → all eight dispositioned; §4 "eight domain modules" → twelve as built.
- [x] **QI-26** ✅ **FIXED 2026-08-04.** `qa-qi-map-verification-log.md` promised a Phase-1 citation re-anchor that never happened and is now moot.
- [x] **QI-26b** ✅ **FIXED 2026-08-04.** `validate.py` extraction scars: 5 orphaned `CHECK NN`/`CLI` headers removed, the `Shared helpers` header relabelled to what actually sits under it, blank-line runs collapsed (743 → 635 lines). The stranded `NOT SHIPPED: ledger_evidence_names_its_finding` design note was REHOMED to `reviews.py` beside its nearest kin rather than deleted.

### W-D — the standing obligation (D5)

- [ ] **QI-27** D5 — *"every new or modified check ships a mutation test proving both directions"* —
      is **prose with no mechanical enforcement**. No registered check and no test asserts it.
      Coverage (inherited from `QA_QI_INFRASTRUCTURE_MAP.md` §6, not re-measured here):
      **10 of 59** checks have a test that would fail on a seeded defect; **11** are green-only;
      **32 have no test at all**. Operator ruling 2026-08-04: **all checks need tests.**
      Sequenced after W-A/B/C so tests are written against corrected code.

---

## 4. Recorded, not scheduled

Known residuals — reported so they are not re-discovered, deliberately **not** filed as defects:

- **The path-alias guard's `BinOp` gap.** `test_no_check_module_aliases_a_path` catches
  `X = _H.NAME` but not `X = _H.NAME / "y"`. Five modules use the latter form
  (`freshness._COUNTS_SOURCES`, `_TABLES_SOURCES`, `CLAIM_CLUSTERS_PATH`;
  `prose_lean_refs._PHYSLIB_DIR`; `notebooks.NOTEBOOK_EXEC_CACHE`). **The guard documents this in its
  own assertion message** — a known, deliberate limit, not an oversight.
- **`check_theorem_count` hardcodes `322` in three places** (the registered description and two dict
  entries) — a hand-typed count inside the validation suite. Already noted in `RESUME_STATE.md`.
- **Graph build cost.** `extract_formula_nodes` runs 3× and `extract_lean_declaration_nodes` 2× per
  build, plus `extract_python_test_nodes` 2×. This is the substance behind ADR-009 §Deferred item 0's
  **declined** shared-graph-handle (measured there: 5 invocations / 45.4 s / 8% of a run).
- **`sys.path` growth.** `build_graph_json` inserts into `sys.path` on every call (4 sites); in a
  long-lived dashboard process this grows unboundedly.
- **`_iter_test_functions` double-counts nested test classes.** A `def test_*` inside a class nested
  in another class yields twice under different qualifiers. No such class exists today —
  `TestGraphTestNodeCoverage` (count equality) would fail the day one is added, which is the
  correct behaviour, so this is a latent-but-guarded shape rather than a defect.

---

## 4b. Harness lessons from this remediation

Recorded in the same spirit as ADR-009 §Deferred item 2's *"scope every mutation to the target
function's AST span"* — these cost time here and will cost it again otherwise.

- **⚠️ NEVER revert a mutation with `git checkout <file>` while that file carries uncommitted work.**
  Done once on 2026-08-04: the mutation was correctly scoped to the target function's AST span, but
  the *restore* was file-wide, so it silently discarded the QI-01 edits in the same file and
  invalidated a 6-minute characterization run that was reading the file concurrently. Restore a
  mutation by writing back the exact bytes you saved, never by reverting the file. The AST-span rule
  covers applying a mutation; it says nothing about undoing one, and that is where this went wrong.
- **A structural leg is worth more than a count leg, and they are not substitutes.** The count
  assertion for QI-01 protects the six sites that exist. The structural scan found a **seventh
  receiver name** the manual sweep missed and is what would have caught the defect originally —
  `freshness.py` was already correct while five siblings were not, so no count over the broken sites
  could have flagged it. Where a finding is "N places do X wrong", ship the scan, not just the count.
- **Do not run the characterization harness concurrently with edits to the code it is reading.** It
  executes checks in-process against the live tree; an edit mid-run silently corrupts the snapshot.

## 4c. Resume point

**W-A, W-B and W-C are complete** — 27 of 28 findings closed across six commits on
`infra/adr-009-validation-modularization`. Fast suite **5080 passed / 5 skipped / 0 failed**.
Characterization **HELD (49 identical)** across both mechanical passes; the two W-A behaviour changes
were each attributed in full (+114 PlaceholderMarker nodes, +4 VERIFIED_BY edges closing 4 broken
provenance chains) and **no check verdict moved by any of it**.

**Next and last: W-D — QI-27.** Mutation tests for the 43 checks that lack one (32 untested +
11 green-only), plus a registered gate so D5 stops being prose. Operator ruling 2026-08-04: all
checks need tests before this branch is ready for PR review.

**Read these first** — they are the only part of the QA/QI surface this audit did NOT read in full,
and they define the house patterns to mirror: the 15 unread test files (~3,170 lines), starting with
`test_validate_public_surface.py`, `test_readiness_submission_gate.py` and
`test_native_decide_ratchet.py` (the three Phase-3 repairs shipped both-directions tests worth
copying).

**Carry into W-D:** the lake-resolution duplication noted under QI-11 — extracting it changes two
checks' early-return behaviour, so it belongs with their mutation tests rather than in a
mechanical pass.

**Standing rules for anyone continuing this** (all learned the hard way in §4b): scope every mutation
to the target function's AST span; restore it by writing back saved bytes, never `git checkout`;
never run the characterization harness while editing the code it reads; and when a mutation is *not*
caught, that is a finding about the guard, not a formality to wave through — it deleted a redundant
guard from my own QI-03 fix.

## 5. Companion documents

- [ADR-009](../../adrs/ADR-009-validation-suite-modularization.md) — the decision this audit checks.
- [QA_QI_INFRASTRUCTURE_MAP.md](../../architecture/QA_QI_INFRASTRUCTURE_MAP.md) — the map this audit corrects.
- [RESUME_STATE.md](../../architecture/.working-docs/RESUME_STATE.md) — the handoff state.
- [2026-08-01 publication-readiness audit](../2026-08-01-publication-readiness/README.md) — the ancestor.
