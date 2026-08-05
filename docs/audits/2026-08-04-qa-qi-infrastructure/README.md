# QA/QI Infrastructure Audit — 2026-08-04

**➡️ START HERE: [`FINDINGS_REGISTER.md`](FINDINGS_REGISTER.md)** — all **53** actionable
non-Critical findings with status, and [`reviewer-reports/`](reviewer-reports/) — the six
reviewers' own words, recovered verbatim 2026-08-05. ⚠️ The *"~17 Important"* figure that
stood in this file was never derived from the artifact and is wrong by ~3×.

**Then: [`PR_REVIEW_2026-08-05.md`](PR_REVIEW_2026-08-05.md)** — the six-reviewer PR review,
its verdict (DO NOT MERGE), the measured state, and the ordered resume point.

**Status:** 🟠 **MERGE BLOCKERS CLEARED 2026-08-05; the review's Important findings remain open.**
35 findings closed — **QI-31…QI-34, the four Criticals that blocked merge, are FIXED** (see §W-F),
each verified by a probe seeded in the PRODUCTION artifact rather than a fixture. All four were
checks that **could not fail** — the exact class this audit was convened to find, missed by it, and
then "mutation-verified" by W-D's own tests. ~17 Important findings from the same review are filed,
not fixed; the reviewer-6 findings (the human-verification write path, a RED test hidden behind the
`slow` marker, silent severity downgrades, the 11 untested gate evaluators) are recorded in the
review file and are **not** merge blockers.

⚠️ **RETRACTED: "all 59 checks are mutation-verified in both directions."** That headline stood in
this file, `RESUME_STATE.md` and ADR-009. What the D5 registry actually certifies is *"a decision was
recorded for every check, and the named test references it in code"* — which is what
`test_d5_mutation_obligation.py`'s own docstring says at §"THIS FILE DOES NOT PROVE A TEST IS GOOD."
The stronger reading was mine and it was wrong. Four checks carry a `MUTATION_VERIFIED` entry, a
passing both-directions test, **and no ability to fail in production.**
*(31 = QI-01…QI-30 plus the QI-26b sub-finding. Counted as CHECKBOX ENTRIES in §3, not as the
highest ordinal — the original filing said "27", which was the highest number at the time while
the board already carried 28 entries. Re-count the boxes; do not read the last id.)* This remains the
tracker; keep the measurement column honest if anything reopens.

**The headline result: `AWAITING_MUTATION_TEST` is EMPTY.** All **59 registered checks are
mutation-verified** in both directions, and `AWAITING_CEILING` is **0** — so the next check added
without a both-directions test fails on arrival rather than being absorbed into a backlog. ADR-009
D5, the obligation its own §Context calls *"the one that caused the damage"*, is discharged.

**Verified at close:** fast suite **5398 passed / 5 skipped / 0 failed** (5055 at audit open,
5086 at W-C close); **`CHARACTERIZATION HELD — 49 checks identical`**; `validate.py` **57 of 59** in
317.8 s, both reds owned by the publication workstream and **both re-identified by name** (QI-29 —
the documented pair was wrong). Branch **NOT merged** — verify
with `git merge-base --is-ancestor HEAD main` rather than inheriting this line.

⚠️ **How that characterization was taken matters, and the first attempt was wrong.** The natural
move — record the "before" snapshot in a `git worktree` at the pre-session commit — is invalid here:
a fresh worktree lacks the gitignored artifacts (`lean/lean_deps.json`, the notebook skip-cache), so
every Lean check takes its absent branch and the diff is noise dressed as signal. It was discarded
unrun. The valid form reverts **only the two source files this session changed** in place, on the
same tree with every artifact present, snapshots, then writes the saved bytes back and clears the
bytecode. Reporting the worktree diff as "HELD" would have been the *verified-adjacent* failure
`RESUME_STATE` warns about: running a check whose result is merely CONSISTENT with the claim.

**Scale of W-D:** ~330 new tests across 11 files, **~150 AST-scoped mutations**. Roughly a third
came back **MISSED on first run**, and *in every case the finding was real* — either the guard was
inert or the test was. That ratio, not the final green, is the argument for D5.

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
0 failed** *(at audit open; 5398 at close)*, `validate.py` 57/59 with 2 intentional reds. The
shared-helper layer is genuine and its policy line (*"this module owns where things are, not what
their absence means"*) is held in code.

**What was not done is the layer underneath the check verdicts.** Five kinds, **all now closed**:

1. ✅ **One live enforcement hole** — a third of the Lean substrate unscanned by **six** glob sites
   (QI-01). Measured verdict movement: **zero**, so it closed a latent hole rather than surfacing
   live debt.
2. ✅ **Duplicated predicates** across subsystems a check requires to agree (QI-02, QI-03).
3. ✅ **Dead and doubled code** in the enforcement path (QI-05 … QI-11).
4. ✅ **Documentation contradicting the code it describes** — including three in-code headers telling
   a reader a repaired check was still broken (QI-12 … QI-26b).

5. ✅ **The standing obligation ADR-009 itself calls the disease** — D5 had no mechanical
   enforcement and 32 of 59 checks had no test at all. Both closed (QI-27): the obligation is a
   registered gate, and the untested population is **zero**.

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

### W-E — found at close

- [x] **QI-29** ✅ **FIXED 2026-08-04 — the documented red checks were the wrong pair.**
      Three documents (and every status report in this session) named `validate.py`'s two failures as
      `paper_latex_compiles` *"on D3's 2 fatal LaTeX errors"* and `readiness_submission_gate`.
      **Measured on a full run at close (317.8 s):** the failures are
      **`bundle_metadata_matches_graph`** (14 of 21 bundle blobs assert `stage13_status: green` while
      blockers are open — ADR-009 §Consequences predicted exactly "fires on 14 of 21") and
      **`readiness_submission_gate`** (0 green / 3 yellow / **61 red** across 64 papers).
      **`paper_latex_compiles` PASSES**, and correctly: it sits behind the slow gate and reports
      *"SKIPPED (slow) — pass `--force-latex`"* unless forced. Its D3 failure is real but reachable
      only under `--force-latex`, which no default run passes.
      **Why this is a finding and not a typo:** it is the §2 pattern exactly — a claim written true
      (D3 *was* the live failure when item 3 landed, under the flag that was set at the time) and
      left standing after the surrounding behaviour moved. A reader planning remediation would have
      gone to D3's LaTeX and never touched the 14 bundle blobs that are actually red.
      ⚠️ **I inherited it rather than measuring it, and repeated it in four status reports before the
      closing `validate.py` run contradicted me.** The audit spent workstream W-C on this class and I
      reproduced it in the same session — which is the strongest available argument for its own rule:
      *a number in prose is a cache with no invalidation protocol.*
      **Corrected in:** this tracker (§4c + the close banner) and `RESUME_STATE.md`.
      🔁 **SUPERSEDED 2026-08-05 — and by its own rule.** The sentence above,
      *"`paper_latex_compiles` PASSES, and correctly: it sits behind the slow gate"*, is now
      false: the slow gate is **gone** (the compile is always on, change-scoped by a per-draft
      content-hash cache), so a default `validate.py` is red on D3's two fatal errors. Reading
      it back a day later: calling the skip *correct* was the weakest line in this entry. It was
      a check declining to measure, which is the defect class the whole audit is about — the
      measurement was right and the adjective was wrong. Left standing above rather than edited,
      with this note, because that is what this entry is for.

- [x] **QI-30** ✅ **FIXED 2026-08-04 — `theorems` was vacuous in ALL THREE legs.**
      §4 recorded this as a cosmetic residual (*"hardcodes 322 in three places"*). Reading it
      properly on challenge showed the duplication was the least of it. The check asserted:

      | leg | verdict |
      |---|---|
      | `TOTAL_THEOREMS == 322` | **unreachable** — `constants.py:1372` asserts the count at IMPORT, so a wrong value raises `AssertionError` before the body runs (demonstrated) |
      | `len(ARISTOTLE_THEOREMS) == 322` | same assertion, same unreachability, written twice |
      | `TOTAL_THEOREMS == len(ARISTOTLE_THEOREMS)` | **a tautology** — `TOTAL_THEOREMS = ARISTOTLE_PROVED_COUNT = len(ARISTOTLE_THEOREMS)` |

      So a check registered as *"has 322 entries and is self-consistent"* asserted nothing, and had
      been green since it was written for exactly that reason. It is one of the 59.
      ⚠️ **And my W-D mutations on it were misleading.** They were CAUGHT — but only because the
      tests monkeypatched the constants, bypassing the import assert. *A mutation caught against a
      patched fixture does not establish that the check can fail in production.* That distinction is
      new to this audit's vocabulary and is the residue worth carrying forward.

      **The count invariant is KEPT and not duplicated:** `constants.py` owns it and enforces it
      harder than a check can (an unimportable module). The check now does the thing nothing did —
      **resolve every `ARISTOTLE_THEOREMS` key against the Lean substrate.** That matters because
      `check_formulas_to_theorems` unions those KEYS into its valid-Lean-name set, so a stale key
      launders a nonexistent theorem into it and a formula grounded on that theorem reads as verified.
      **Measured: 14 of 322 keys resolve to nothing** in `lean_deps.json` *or* the Lean source (the
      `DG_inst*` family, `DG_basis_mul`, `fock_space_finite_dim` — an Aristotle batch whose Lean was
      later restructured).
      **Shipped as a RATCHET** (`ARISTOTLE_REGISTRY_UNRESOLVED_CEILING = 14`), not a hard fail: the
      house idiom, and it closes the generator without turning a registry cleanup into a red build.
      `validate.py --check theorems` still PASSES, now with the debt visible.
      ✅ **THE CRITERION HAS NOW BEEN SWEPT (2026-08-05, PR review C2).** QI-30 introduced
      *"a mutation caught against a patched fixture does not establish that the check can fail in
      production"* and then recorded it as residue without applying it — the audit's own most-repeated
      failure shape (cf. QI-01: *"already fixed once in `freshness.py` and not swept"*). Swept:
      **module-level `assert`s across `src/` and `scripts/` = 10, of which exactly ONE governs a
      check's inputs** (`constants.py:1372`, pinning `ARISTOTLE_PROVED_COUNT`). Two registered checks
      read the names it pins — `theorems` (this finding) and `formulas`. `formulas` is **not** the
      same shape: its failure path is a mapped theorem missing from the Lean name set, which the
      assert does not gate, so it can fail in production. The other nine asserts are in `phase6p_*`
      compiler scripts and gate no check.
      **Result: the mechanism is unique and QI-30 was its only instance.** The criterion still
      generalises — *a test that patches something invariant in production proves nothing about
      production* — and is worth applying to any future check whose only failure path runs through
      a compile-time-pinned constant.

      **Guard:** 7 tests / 4 mutations, plus a structural leg forbidding any comparison against an
      integer literal in the check body — which is why the display cap is a named `_SAMPLE` rather
      than an inline `8`.

### W-F — ✅ CLOSED 2026-08-05: the four merge blockers found by PR review

All four are fixed, and each was verified by the criterion that found them —
**seed the defect in the PRODUCTION artifact, not in a monkeypatched fixture** (QI-30).
Every one now has a probe that turns the live check red:

| finding | production probe | result |
|---|---|---|
| QI-31 | a drifted cell / a rules-only table / a deleted row in the shipped `table1_experimental_params.tex` | rc=1 (×3) |
| QI-32 | a new unresolved `\texttt{}` reference added to `papers/paper12_polariton/paper_draft.tex` | 82 vs ceiling 81 → rc=1 |
| QI-33 | a real single-word title drift added to `CITATION_REGISTRY` | 8 vs ceiling 7 → rc=1 under `--strict` |
| QI-34 | a real recurrence written into `papers/AutomatedReviews/` | 1 contradicted → rc=1 |

**Not one of the four was fixed by widening a constant.** QI-31 and QI-32 were reading the
wrong artifact; QI-34 was reading the wrong FIELD of the right one; QI-33's strict branch was
promoting the class its own docstring calls advisory. Where inherited debt could not be repaired
on this branch, it is frozen at a **zero-headroom ratchet** with a test asserting the live corpus
sits exactly at the ceiling — `LEGACY_DRAFT_UNRESOLVED_REF_CEILING = 81`,
`BIBITEM_TITLE_DRIFT_CEILING = 7` — so raising one to buy a green run fails.

⚠️ **Two fixture defects surfaced while fixing these, and both are the same shape as the
findings.** `test_d5_reviews._finding` modelled a ReviewFinding node carrying `label` and no
`name`, so no test in that file could have shown the check reading the truncated field; and its
marginal-band pair scored 0.4444, which the new threshold excludes outright, so both of that
test's legs would have passed with the tie-breaker never exercised. A band-anchored fixture goes
vacuous the moment the band moves.

#### Original filing (2026-08-05)

⚠️ **PROVENANCE, measured 2026-08-05 — NONE of these is a branch regression.** The question
"did this used to work?" was asked and answered against git history, because the disposition
differs entirely: a regression means the refactor broke it, an inherited defect means the guard
was decoration from the start and the audit convened to find that missed it.

| finding | on `main` too? | first broken | verdict |
|---|---|---|---|
| QI-31 `paper_table` | **yes, identical** | never worked — 12 sampled commits to 2026-05-01 show zero `read_text` in its body | **inherited** |
| QI-32 `paper_provenance` | **yes, identical regex** | `b0461531`, **2026-03-26** — dead ~4.5 months | **inherited** |
| QI-33 `bibitem_title` | **yes, and more explicit** — `main` carried a literal `summary_passed = True  # Always pass in default mode` | since the check existed | **inherited** |
| QI-34 `recurrence` threshold | branch-era constant, but the *class* is documented 3× before this branch | 4th mis-calibration | **inherited class** |
| `paper_latex_compiles` | **`main` was WORSE** — computed `all_pass` and returned `passed=True` unconditionally | — | **branch IMPROVED it** (item 3); the remaining slow-gate skip is inherited |

**Checks registered: 59 on `main`, 59 on the branch. None dropped, none added** (verified by AST on
both sides — a raw decorator-text count reads 61 on `main` because two appear in prose).

⚠️ **This makes the finding worse, not better.** The refactor did not break these; it inherited them,
and **this audit was convened specifically to find guards that cannot fire and did not find them.**
`paper_provenance` is the sharper case: QI-01 "fixed" its Lean scan, and the measured
verdict-movement of **zero** — which I reported as evidence the exposure was latent — was in fact
evidence the leg had been dead since March.



⚠️ **All four are the QI-30 shape, and all four were "verified" by W-D.** The lesson QI-30 recorded
and I did not apply as a sweep — *seed the defect in the PRODUCTION artifact, not in a monkeypatched
fixture* — is what would have caught every one.

- [x] **QI-31** 🔴 **`paper_table` never reads the paper.** `physics.py` resolves
      `papers/paper1_first_order/paper_draft.tex` and uses it **only for `.exists()`**; the "paper"
      side of the comparison is a hardcoded dict in the check body. Editing Paper 1's Table 1 to any
      wrong value cannot fail the one check registered to catch exactly that.
      **Measured: 11 of its 12 cells are byte-identical to `numerical`'s table**, compared against the
      same `get_all_experiments()` source — the QI-30 "same comparison written twice" shape verbatim.
      Only `Steinhauer.T_H` differs (5.78e-12 vs 6.0e-12), inside the 5% tolerance.
      ⚠️ My D5 test seeded the defect on the **solver** side and wrote a fixture `.tex` containing the
      literal string `"draft"` — no table at all — while its docstring claimed *"the published table
      and the code disagree, which is the entire purpose of the check."*
      **Fix:** parse the cells from the `.tex` as `d1_hierarchy_table` already does, and delete the
      duplicated dict.
      ✅ **CLOSED `17bbe234`** — now parses the shipped `tables/table1_experimental_params.tex` in three legs (the draft `\input`s it; every cell against the canonical evaluator at ONE unit in the cell's last printed place; every declared row present). 15 real cell comparisons replace 12 tautologies. The duplicated dict is deleted.

- [x] **QI-32** 🔴 **`paper_provenance`'s theorem-reference leg examines 0 of 1,963 candidates.**
      `re.findall(r'\\texttt\{([a-z_][a-zA-Z0-9_]*)\}')` cannot cross a backslash, and LaTeX writes
      underscores inside `\texttt{}` as `\_`. **Measured across all 64 drafts: 480 raw matches, 0
      containing `_`, against 1,963 `\texttt{}` blocks that contain an escaped underscore** — i.e.
      every real Lean theorem name. The 2,039-file `rglob` building a 19,108-name set is consumed by
      nothing.
      ⚠️ **This is the leg QI-01 "fixed."** The `glob`→`rglob` repair was applied to a leg that cannot
      fire, and my QI-01 verdict-movement measurement of "zero" was true for that reason.
      ⚠️ My D5 fixtures used raw `\texttt{real_theorem}` — the one input shape the check can parse and
      the shape no real draft uses.
      `paper_provenance` is one of four checks `gate_precheck.py s10` runs.
      ✅ **CLOSED `2dc856ec`** — the leg is REMOVED, not revived: resolving a Lean name cited in prose is `prose_lean_refs`'s question and that check owns a real extractor and resolver. Its scope grew instead, from 21 bundles to all 64 drafts: the 43 legacy drafts are now measured (774 candidates, 81 unresolved across 23 drafts) under a zero-headroom ratchet. Repairing the 81 is ADR-010.

- [x] **QI-33** 🔴 **`bibitem_title_primary_source` cannot fail, and is suppressing 9 live flags.**
      `summary_passed = not _cfg.STRICT_MODE or (...)` reduces to the literal `True` in every
      automated run, and no caller passes `--strict`. Run live: **PASS with 9 DROP-WORD flags** — the
      BLOCKER class it exists to detect. Confirmed samples include `Berti2025` and `DESI2024`
      (registry titles carrying words absent from the cached PDF page 1), and `Turyshev2026DESI`,
      which reads as a citation pointing at a different paper.
      It is **not** in ADR-009 §Deferred item 3's disposition table, so it was never consciously
      ruled advisory.
      ✅ **CLOSED `637d1184`** — `--strict` gained a caller in `2577fdbc`, which made the strict branch load-bearing and exposed that it promoted NOT-FOUND (58 live, advisory by design) alongside DROP-WORD (7). Strict now promotes DROP-WORD only; 2 of the 9 flags were `pdfminer` whitespace artifacts and are repaired; the remaining 7 are ratcheted.

- [x] **QI-34** 🔴 **`recurrence_reopens_closures`' threshold is above its live maximum — the FOURTH
      mis-calibration.** `_RECURRENCE_MIN_OVERLAP = 0.40`. **Measured on the live corpus: 7,489
      candidate pairs, max Jaccard 0.3750.** Zero pairs can clear it; the `+0.10` section-number
      tie-breaker tightens it further. Live output `213 compared / 0 contradicted` is the only
      reachable result.
      The in-body comment still cites a justifying 0.429 pair that no longer exists in the corpus —
      the check's own documented failure mode (*"a constant set just under the live maximum by the
      same commit that repaired the pair producing that maximum"*), for the fourth time.
      ⚠️ My replacement test used synthetic fixtures scoring **Jaccard 1.0**, which is as disconnected
      from the live distribution as the re-implemented matcher it replaced.
      **Fix:** calibrate against the measured distribution (p99 0.200 / max 0.375) **and** add a test
      asserting the live corpus max stays below the threshold by a stated margin, or the next corpus
      shift silently re-deadens it.
      ✅ **CLOSED `865db716`** — NOT a fourth tuning. The node already carried `name: heading[:200]` next to `label: heading[:50]` and the check read the truncated one; open findings whose heading is a RESOLUTION NOTICE (the corpus's top three scores, every one a closure matched against its own “**RESOLVED**” restatement) are now excluded. Corpus max 0.375 → 0.267, a true restatement 0.500 → 0.900, separation 1.33× → **3.37×**. 0.45 chosen inside the resulting empty band, not from the live maximum. The frozen fixture pairs are still not separated and the guard is still weak — it is now weak with a margin.

⬜ **Also open, filed not fixed:** ~17 Important findings from the same review — including
`cross_path_consistency`'s two legs routing through the same function, `paper_latex_compiles`
unreachable from every automated caller (18s when forced, so the "slow gate" rationale is stale),
the three freshness regenerators that regenerate-then-pass and can never fail on staleness,
`atlas_view.py`'s `SystemExit` aborting the remaining ~24 checks, and `notebook_exec`'s unsigned
skip-cache. See the review record.

### W-D — the standing obligation (D5)

- [x] **QI-27** ✅ **CLOSED 2026-08-04 — the backlog is EMPTY.** D5 — *"every new or modified check
      ships a mutation test proving both directions"* — shipped as **prose with no enforcement**.
      ADR-009 §Context names it as the one of its three problems that *"caused the damage"*.

      ✅ **The obligation is now MECHANICAL:** `tests/test_d5_mutation_obligation.py`. Every registered
      check must appear in exactly one of `MUTATION_VERIFIED` (naming the test, with the mutation
      recorded) or `AWAITING_MUTATION_TEST`; a new check declaring neither **fails on arrival**. The
      backlog is ratcheted at `AWAITING_CEILING`, and a companion test asserts the ceiling EQUALS the
      backlog so there is no headroom — the exact defect found in `ledger_ids_resolve`, which sat at 67
      against a population of 66 and so admitted one new dangling record silently. A seam guard rejects
      a `MUTATION_VERIFIED` entry whose named test does not mention the check, so promoting a name out
      of the backlog cannot be free. 6 tests, 3 mutations caught, clean negative control.

      ⚠️ **Why a registry and not a scanner — measured, not assumed.** Of the test files covering the
      five Phase-3 repairs, **none** carries a mutation marker in its source: the mutation runs are
      recorded in commit messages and in ADR-009, because a mutation is an act performed against the
      tree, not an artifact left in it. A scanner would have to infer "both directions" from test
      structure — the kind of proxy that produced `recurrence_reopens_closures`' three mis-calibrations
      and the eight inert guards. A registry that must be edited deliberately is honest.

      ✅ **THE BACKLOG IS EMPTY.** Seeded at **54** awaiting (only the 5 the ADR documents were
      admitted as verified; the map's §6 figures do not sum — 10 + 11 + 32 = 53, not 59 — and were
      deliberately **not** used). Worked down module by module, lowering `AWAITING_CEILING` in the
      same commit as each batch:

      | ceiling | module | tests | mutations |
      |---:|---|---:|---:|
      | 54 → 50 | `reviews.py` | 22 | 8 |
      | 50 → 44 | `lean_substrate.py` | 34 | 12 |
      | 44 → 35 | `physics.py` (+ d1/f reinforcement) | 27 (+4) | 14 |
      | 35 → 29 | `lean_statements.py` + `notebooks.py` | 43 | 16 |
      | 29 → 23 | `freshness.py` | 37 | 13 |
      | 23 → 17 | `lean_toolchain.py` | 34 | 14 |
      | 17 → 14 | `graph_atlas.py` | 26 | 11 |
      | 14 → 11 | `papers_prose.py` | 20 | 12 |
      | 11 → 9 | `prose_lean_refs.py` | 12 | 8 |
      | 9 → 5 | `citations.py` | 25 | 12 |
      | **5 → 0** | `bundles_readiness.py` | 28 | 14 |

      ⚠️ **ROUGHLY A THIRD OF ALL MUTATIONS CAME BACK MISSED ON FIRST RUN — and every one was a
      real finding.** That is the durable result, more than the final green. The pattern split
      three ways, and all three recur:
      1. **The GUARD was inert** — QI-28 (six dead hedge alternatives).
      2. **The TEST was vacuous** — a `1e-16` float "jitter" that is bit-identical to the original;
         a placeholder fixture typed `True` so an INDEPENDENT rule caught it and the branch under
         test never fired; a marginal-band pair measured at 0.36 when the threshold is 0.40.
      3. **The mutated line was genuinely redundant** — the `notebook_exec` cache-load conjunct, and
         the `bundle_metadata` missing-blob branch. Both LEFT IN PLACE and explicitly **not counted
         as verified**, because an unverifiable line must not be recorded as verified in either
         direction.

      ⚠️ **Three checks the ADR credits as already covered were weaker than claimed** —
      `d1_hierarchy_table` and `f_hierarchy_claims` (verdict-propagation mutations MISSED: their
      stale fixtures are wrong four ways at once, so no single ground carried the verdict) and the
      prose pair (pure cores well tested, but the CHECKS reached only through a live-tree smoke
      test, leaving the core→verdict step untested). Verified, not inherited.

- [x] **QI-28** ✅ **FIXED 2026-08-04 — found BY the D5 work, not by reading.**
      `lean_substrate._LEDGER_HEDGE_RE` listed nine honest-framing alternatives for a bookkeeping
      theorem. Six of them (`tabulat`, `aggregat`, `enumerat`, `bookkeep`, `summari[sz]`, and the
      `tall`-stem) were written as **stems but closed with `\b`**, so they could match only the bare
      stem — a form nobody writes. Measured: `tabulated`, `tabulates`, `aggregates`, `enumerates`,
      `bookkeeping`, `summarizes` all failed to match. Only `record(s|ed)?`, `tallies` and
      `classification ledger` worked.
      **Direction matters:** a hedge SUPPRESSES a flag, so the dead alternatives meant correct
      bookkeeping prose would be flagged as an Invariant-#9-style overclaim — a guard firing on
      correct data, which this project holds to be *worse than no guard* (the standing rule recorded
      in `reviews.py`'s own not-shipped `ledger_evidence_names_its_finding` note).
      **Measured verdict movement: 0.** 21 disclosed definitional/vacuous_proxy theorems across the
      64-draft corpus produce **0 overclaim-verb windows** today, so 0 flags before and 0 after —
      latent, closed rather than surfaced (same posture as QI-01 and `5228ed6d`).
      **How it was found:** the mutation dropping the `_LEDGER_HEDGE_RE` conjunct was **MISSED**.
      The hedge test used *"records the closure"*, which carries no overclaim verb, so the FIRST
      conjunct short-circuited and the hedge was never reached. Strengthening the test to put both
      in one window exposed the dead alternatives.
      **Guard:** `test_a_ledger_hedge_beside_an_overclaim_verb_suppresses` (behavioural) plus
      `test_every_hedge_alternative_can_match_an_inflected_form` (structural — protects the next
      alternative someone adds, not just the ones there now, per the §4b lesson).

      ⚠️ **This is the first defect the D5 obligation FOUND rather than documented**, and it makes
      the case for the obligation better than the ADR does: the check was green, its test was green,
      and a sixth of its logic could not execute. It is also the second time in this audit that a
      *missed* mutation was the informative result — the first deleted dead code from the QI-03 fix.

---

## 4. Recorded, not scheduled

Known residuals — reported so they are not re-discovered, deliberately **not** filed as defects:

- **The path-alias guard's `BinOp` gap.** `test_no_check_module_aliases_a_path` catches
  `X = _H.NAME` but not `X = _H.NAME / "y"`. Five modules use the latter form
  (`freshness._COUNTS_SOURCES`, `_TABLES_SOURCES`, `CLAIM_CLUSTERS_PATH`;
  `prose_lean_refs._PHYSLIB_DIR`; `notebooks.NOTEBOOK_EXEC_CACHE`). **The guard documents this in its
  own assertion message** — a known, deliberate limit, not an oversight.
- ~~**`check_theorem_count` hardcodes `322` in three places**~~ — **PROMOTED to a defect and FIXED:
  see QI-30.** Recording it as a cosmetic residual was itself the error; reading it properly showed
  all three of the check's legs were vacuous, not merely duplicated.
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
- **⚠️ RESTORING THE SOURCE DOES NOT UNDO A MUTATION — THE `.pyc` OUTLIVES IT.** The most
  dangerous harness defect found in this audit, because it corrupts results *silently and in
  either direction*. CPython decides a cached bytecode file is current from the source's
  **(mtime-in-seconds, size)**. A mutation that preserves LENGTH — `"if not m:"` → `"if False:"`,
  both 9 characters — and is restored **within the same second** (a fast pytest run takes 0.07 s)
  leaves a `__pycache__` entry that still looks valid. Every subsequent process then imports
  **mutated bytecode from a clean-looking, `git status`-clean tree.**
  Observed 2026-08-04: it produced an `AttributeError` in `test_f_hierarchy_claims` whose
  traceback was *impossible* against the source on disk — `m` was `None` immediately after
  `if not m: continue` — and it reproduced on a stashed tree, so it read convincingly as a
  pre-existing repo defect rather than as contamination from a mutation run minutes earlier.
  It would just as easily have produced a **false CAUGHT** (a test failing against poisoned
  bytecode, credited to the mutation under test) or a **false MISSED**.
  **Rule: a mutation harness must delete the target's cached bytecode after restoring it, and
  bump the source mtime.** Every mutation verdict recorded in this audit before the fix was
  re-run from a cleared cache; all 19 held, so nothing recorded here rests on a poisoned run.
  ⚠️ The same trap applies to *any* tooling that writes a source file, runs it, and writes it
  back — not just this harness.
- **⚠️ A `git worktree` is the WRONG place to take a "before" characterization.** A fresh worktree
  has no gitignored artifacts — `lean/lean_deps.json`, the notebook skip-cache — so every Lean check
  takes its artifact-absent branch and the comparison reports a large diff that says nothing about
  the code change. Revert only the changed SOURCE files in place instead, on the tree that has the
  artifacts, then write the saved bytes back and clear the bytecode. Caught before the run here, but
  it would have produced a confident, wrong "HELD".
- **A structural leg is worth more than a count leg, and they are not substitutes.** The count
  assertion for QI-01 protects the six sites that exist. The structural scan found a **seventh
  receiver name** the manual sweep missed and is what would have caught the defect originally —
  `freshness.py` was already correct while five siblings were not, so no count over the broken sites
  could have flagged it. Where a finding is "N places do X wrong", ship the scan, not just the count.
- **Do not run the characterization harness concurrently with edits to the code it is reading.** It
  executes checks in-process against the live tree; an edit mid-run silently corrupts the snapshot.

## 4c. State at close

**All four workstreams complete — 29 of 29 findings closed** on
`infra/adr-009-validation-modularization`. Fast suite **5398 passed / 5 skipped / 0 failed**
(5055 at audit open). Every mechanical pass verified **CHARACTERIZATION HELD — 49 checks identical**;
the behaviour changes were each attributed in full (+114 `PlaceholderMarker` nodes, +4 `VERIFIED_BY`
edges closing 4 broken provenance chains) and **no check verdict moved by any of it**.

**Two deferred items were closed where they belonged, not where they were found:**
- the **QI-11 lake-resolution duplication** landed with `lean_toolchain`'s mutation tests, because
  extracting it changes two checks' early-return path (ADR-009 D4 forbids mixing that into a
  mechanical pass). Only the resolution is shared; each caller keeps its own SKIP message, and a
  test asserts the two stayed different.
- **QI-28** was found BY the D5 work and fixed in the same commit as the tests that caught it.

**What is genuinely still open, and is NOT this audit's to close:**
- The branch is **not merged**. Re-check with `git merge-base --is-ancestor HEAD main`.
- `validate.py` is **57 of 59**. The two reds are **`bundle_metadata_matches_graph`** (14 of 21
  bundles assert `stage13_status: green` with blockers open) and **`readiness_submission_gate`**
  (61 of 64 papers RED). Both are the dial working as designed and belong to the publication
  workstream. ⚠️ *Not* `paper_latex_compiles` — see QI-29.
- The §4 residuals below are **recorded, not scheduled** — read them before assuming they are
  oversights.

**Standing rules for anyone extending this** (all learned the hard way; see §4b): scope every
mutation to the target function's AST span; restore it by writing back saved bytes, **never**
`git checkout`, and **delete the cached bytecode afterwards**; never run the characterization
harness while editing the code it reads; and when a mutation is *not* caught, that is a finding —
about the guard, or about the test, or about a line that should not be counted as verified. It was
never once a formality here.

## 5. Companion documents

- [ADR-009](../../adrs/ADR-009-validation-suite-modularization.md) — the decision this audit checks.
- [QA_QI_INFRASTRUCTURE_MAP.md](../../architecture/QA_QI_INFRASTRUCTURE_MAP.md) — the map this audit corrects.
- [RESUME_STATE.md](../../architecture/.working-docs/RESUME_STATE.md) — the handoff state.
- [2026-08-01 publication-readiness audit](../2026-08-01-publication-readiness/README.md) — the ancestor.
