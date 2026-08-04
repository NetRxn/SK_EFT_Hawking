# ADR-009 — Validation-suite modularization and the mutation-test obligation

- **Status:** **PROPOSED (2026-08-03).** Direction authorized in principle by the project owner on
  2026-08-03 ("as long as you take it that direction, it's authorized"), explicitly **contingent on this
  architecture document being reviewed first**, on operator visibility during execution, and on the standing
  rule that no core-infrastructure file may be modified by an agent that has not read it in full directly.
  No implementation may begin before acceptance and Phase-0 completion.
- **Decider:** John Roehm (project owner) — raised the concern that `scripts/validate.py` "has exploded in
  terms of ad-hoc edits", is "too big to read directly in one go", and that "agents were just adding to it
  without reading what already exists"; directed that the validation layer become "a legit module rather
  than a single file".
- **Investigation and draft:** Claude (Opus 5), from a complete direct read of all 7,778 lines of
  `scripts/validate.py` on 2026-08-03. Reconnaissance agents mapped adjacent subsystems; **every
  load-bearing claim in this ADR is verified against the source by the author**, not inherited from a
  subagent report. Two subagent claims were checked and corrected (§Alternatives, note 3).
- **Scope:** `scripts/validate.py` and the package that replaces it; the shared-helper layer it grows; and
  the process obligation attached to every check in the suite. **Out of scope:** the semantics of any
  individual check (§Deferred), the readiness/graph subsystems it consumes, and the publication-bundle
  remediation that surfaced this work.
- **Related:** [ADR-002](ADR-002-native-decide-policy.md) (the `native_decide` ratchet, enforced by a check
  this ADR moves); [ADR-004](ADR-004-substrate-integrity-gates.md) (R1–R5 gates, five of the checks in
  scope; and the single-writer/generated-artifact posture this ADR must not disturb);
  [ADR-005](ADR-005-derived-proof-atlas.md) and [ADR-007](ADR-007-kernel-nogo-ledger-and-negative-frontier.md)
  (atlas and no-go gates, likewise in scope);
  `docs/architecture/.working-docs/` (migration working notes).

> **Line-citation baseline — ⚠️ THE CITATIONS BELOW NO LONGER RESOLVE. Read them as names, not lines.**
> Every `validate.py:NNNN` citation in this document is anchored to the file **as read on 2026-08-03 at
> 7,778 lines** (7,813 after the `stage13_status` guard inserted 35 lines at `:4355`). **Phase 2 has since
> moved all 59 check bodies out**, and `scripts/validate.py` is now **720 lines** of framework, so every
> citation to a CHECK BODY is dangling: locate the check **by name** in its `scripts/validation/checks/*.py`
> module instead. Citations to the framework itself (`Detail`/`CheckResult`, the registry, `run_checks`,
> reporting, the CLI, `main`) still resolve in `validate.py`, at new line numbers.
>
> This note originally read *"Phase 1 should re-anchor them once, mechanically, and delete this note."*
> **That did not happen through Phases 1 and 2, and re-anchoring is now moot** — the citations' target file
> no longer contains the code. Deliberately not hand-rewritten: silently renumbering ~25 citations across a
> module boundary is a larger correctness risk than stating plainly that they are historical. **The
> behaviour each citation describes is unchanged** — every phase boundary verified `CHARACTERIZATION HELD`.
> `QA_QI_INFRASTRUCTURE_MAP.md` §9 carries the same warning for the map's own citations.

---

## Context

`scripts/validate.py` is the project's cross-layer gate: 59 registered checks spanning Python ↔ Lean ↔
notebooks ↔ papers, invoked at Stage 7 and Stage 12 of the wave pipeline, by `scripts/gate_precheck.py`, and
by the pre-commit hook.

It has grown 1,158 → **7,778** lines since 2026-03-26, with ~2,550 lines added in the five weeks to 07-31
and ~1,650 on 07-31 alone.

**The registration architecture is sound and is not the problem.** `@register_check(name, description)`
(`validate.py:151-156`) is a clean contract documented at `:34-43`; all seven checks added on 07-31 followed
it, introduced no duplication, and are among the best-written in the file — three carry explicit
*"FAIL, not pass, because unverified ≠ agreement"* reasoning (`:4302-4310`, `:4317-4322`, `:4330-4336`).

Three distinct problems are conflated under "the file is too big":

1. **No shared-helper layer.** Eight independent `lean_deps.json` load sites with *incompatible*
   missing-file policies; three mutually inconsistent paper-draft scoping idioms; 13 redundant
   `sys.path.insert` calls; 59 scattered `re.compile` sites with no shared TeX-parsing layer.
2. **The file exceeds a single readable unit**, so a new check is written without sight of the existing
   ones. This is the mechanism behind (1).
3. **No mutation-test discipline.** This is the one that caused the damage. The repository's own commit log
   records at least eight shipped guards that could not fire: `edd9878d` *"the drift guard was dead code"*,
   `221cb6c9` *"my closure guard was inert and my mutation test hid it"*, `b6830c7d` *"the readiness gate was
   blind in three stacked layers"*, `5073276a` *"an eighth guard that could not fire"*. Each was found only
   by adversarial review, never by the test suite.

A concurrent publication-readiness audit established the consequence: **the project's quality
instrumentation reports absence-of-measurement as success.** Eight checks are structurally incapable of
returning `passed=False`; some can fail only under `--strict`, which no automated caller passes; and
roughly twenty sites encode "could not measure" as PASS. `CheckResult.passed` is a bare `bool` with no
third state, though the concept exists in comments and in three hand-patched sites.
*(This paragraph originally said "two more" for the `--strict` set. Re-measured 2026-08-04: **six**
registered checks read `_cfg.STRICT_MODE`, of which three are fully strict-gated and three merely promote
an advisory — see §Deferred item 6. The "eight always-pass" and "roughly twenty" figures are the
2026-08-03 measurements and are addressed by §Deferred items 3 and 4 respectively.)*

**Splitting the file addresses (1) and (2). It does not address (3), and (3) is the disease.** A refactor
that lands without the mutation-test obligation would relieve the symptom while leaving the generator
intact — and would itself be executed against ~80% untested surface.

### Test protection is thinner than it looks

Measured across the 11 test files that import `validate`: **16 checks TESTED, 6 PARTIAL (pure cores only),
37 UNTESTED.** Of the 16, **eleven assert only `result.passed` on the live tree** — so a check rewritten to
`return CheckResult(passed=True, details=[])` would pass every one of them. **Exactly five checks have a
test that would fail on a seeded defect**: `formula_grounding`, `d1_hierarchy_table`, `f_hierarchy_claims`,
and weakly the three prose checks via their pure cores.

The sharpest case is a test that *reads* as protection and is not. `recurrence_reopens_closures` calibrates
its Jaccard threshold against `tests/fixtures/recurrence_pairs.json`, whose own `_why` field states the
principle: *"A threshold on a self-remediating corpus must be calibrated against FROZEN labelled pairs, not
a live sweep."* But the matcher `_norm` is a **nested closure** (`:3958`) and `_MIN_OVERLAP` a function-local
(`:3927`), so neither is importable — and `tests/test_bundle_formulas_d11_d12.py:691` **re-implements `norm`
as a local function** and re-hardcodes `SHIPPED = 0.40` at `:747`. Verified: that file never imports
`validate`. **The production matcher could be deleted or inverted and both fixture tests would still pass.**
The check's own source comment cites the fixture as its calibration basis, so the file reads as covered.

Two further measurements bearing on the migration contract: **no test asserts the check count or the
registration order** (two assert membership only), and the fast suite takes **152 s**, not the "~2s"
`CLAUDE.md` claims — a 75× doc drift that matters because Phase 0's snapshot loop runs against it.

### One architectural payoff worth naming

`build_graph_json()` is invoked four times per validate run (`:3316` and, inside
`graph_integrity.run_integrity_checks()`, an independent extraction; then `:4660`, `:4768` — pre-shift
numbering). Verified at `build_graph.py:2544-2601`, each build additionally re-runs **16 node extractors plus
a full edge pass** inside `extract_readiness_gate_nodes` to break gate/graph recursion. Net: **≈8 full
extraction passes and ≈20 parses of a 70 MB `lean_deps.json` per run**, ~15 s per build measured by the
dashboard. A shared graph handle is a natural consequence of the framework/`helpers` split and is the one
performance item large enough to justify naming here — but it is a **Phase 3 semantic change**, since
sharing a graph across checks alters what each check observes when the `*_fresh` checks regenerate artifacts
mid-run.

---

## Decision

### D1 — the checks move to `scripts/validation/`; `scripts/validate.py` stays the module

**⚠️ CORRECTED 2026-08-03, during Phase 2 planning.** This clause originally specified a
`scripts/validate/` **package** plus a thin `scripts/validate.py` **shim**. Those cannot coexist:
verified empirically that a package **shadows** a same-named module on the same `sys.path` entry, so
`import validate` would resolve to `validate/__init__.py` and the shim would be unreachable by import —
dead code that looks load-bearing. Worse, it would silently satisfy H2 (`import validate` works,
`BUNDLE_CODES` present) via a file nobody realised was the live one.

The corrected layout:

- **`scripts/validate.py` remains a module** — the framework core (~400 lines: `Detail` / `CheckResult` /
  `CheckSpec`, the `_CHECKS` registry and `register_check`, `run_checks`, reporting, `archive_results`, the
  CLI, and the `BUNDLE_CODES` re-export H2 requires). It imports the check modules for their registration
  side-effect, from an **explicit ordered list** (H3).
- **`scripts/validation/checks/*.py`** — the 59 checks, split by domain, each file readable in one pass.
- **`scripts/validate_helpers.py`** — already shipped in Phase 1; stays put so its path anchor keeps
  resolving from `scripts/` (H1).

This preserves `python scripts/validate.py`, `import validate`, `--check`, `--list`, `--json` and every
hook / skill / documentation invocation, with no name collision anywhere.

Layout, rationale and per-check module assignment: `docs/architecture/.working-docs/`.

### D2 — The migration contract is asserted mechanically, not asserted in prose

The following are invariant across every phase, verified by the Phase-0 harness at each boundary:

1. `--list` output byte-identical — 59 names, **same order**, same descriptions.
2. Per-check `passed` values identical on the live tree.
3. Exit codes identical — `0` all-pass, `1` any-fail, **`2`** unknown `--check` (`:7732-7735`; the inline
   comment records that `all([]) == True` would otherwise silently disable the gate).
4. `import validate` resolves **and** exposes `BUNDLE_CODES` (see H2).
5. `--json` payload schema unchanged — `gate_precheck.py` and `pre-commit-sync.sh` parse it.
6. `--check <name>` behaves as today for all 59, including the `FORCE_LATEX` side-effect at `:7719`.
7. No new import-time side effects; registration remains the only one.
8. **The 54-name external surface of `validate` stays reachable as `validate.<name>`.** Added 2026-08-03,
   measured by AST across `tests/` and `scripts/` — and it is the constraint most likely to break the
   extraction, because items 1–7 are all satisfied by a split that nonetheless makes every one of these
   `ImportError`:

   > **⚠️ CORRECTED 2026-08-04 — this item was filed as "33-name" and the real surface is 54.** The
   > enumeration below (16 + 17 + `BUNDLE_CODES`) is the FIRST measurement and is kept verbatim as the
   > record of what was missed. That AST scan filtered on `node.module == "validate"`, but
   > `tests/test_substrate_integrity_gates.py` still spelled its imports `from scripts.validate import …`
   > at the time — so the whole file, and every name it reaches, was invisible. **20 names were missed**,
   > fifteen of them internals of the then-unextracted `lean_substrate` module (`_STRUCTURAL_NAME_RE`,
   > `_TRIVIAL_BODY_RES`, `_thin_type_label`, `_is_vacuous_identity_wrapper` and friends) — i.e. the
   > omission would have bitten precisely on the largest remaining extraction. The spelling was then
   > fixed (it was loading `validate.py` under a second module identity — see
   > `test_validate_is_loaded_exactly_once`) and **the scan was not re-run**, so the frozen list sat at
   > 34 while the real surface was 54.
   >
   > **The authoritative list is `EXPECTED_SURFACE` in `tests/test_validate_public_surface.py`** —
   > 21 check functions + 32 private helpers + `BUNDLE_CODES` = **54**, verified 2026-08-04. That file,
   > not this clause, is what the extraction is held to.
   >
   > The generalisable lesson, and the reason this is a correction rather than a silent renumber:
   > **a measurement is scoped by a predicate, and fixing the thing the predicate keyed on invalidates
   > the measurement.** Re-run the scan whenever an import spelling changes. Same class as §Deferred
   > item 7's four-way miscount.

   - **16 check functions imported by name** — `check_formulas_to_theorems`, `check_numerical_consistency`,
     `check_theorem_count`, `check_lean_source`, `check_notebook_isolation`, `check_formula_identities`,
     `check_paper_table_consistency`, `check_d1_hierarchy_table`, `check_f_hierarchy_claims`,
     `check_bundle_consistency`, `check_citation_primary_sources_present`,
     `check_axiom_count_prose_consistency`, `check_prose_theorem_reference_coverage`,
     `check_theorem_name_embedded_citations`, `check_inventory_index_autogen_fresh`,
     `check_paper_toolchain_pin_drift`. Nine test files call these DIRECTLY rather than through `_CHECKS`.
   - **17 private helpers and pure cores** — including the four deliberately extracted to be testable
     (`_tp_scan_lines`, `_axiom_prose_findings`, `_extract_prose_lean_candidates`,
     `_prose_occurrence_disclaimed`), the Guard-3 recurrence matcher (`_recurrence_norm`,
     `_RECURRENCE_MIN_OVERLAP`), and `_CHECKS` / `_CANONICAL_ORDER`.
   - ⚠️ **Two are consumed by a production script, not a test:** `scripts/sync_manifest.py` imports
     `_counts_is_stale` and `_tables_is_stale`. So this is not merely a test-ergonomics concern — the
     pre-commit sync path depends on `validate`'s private surface.
   - `BUNDLE_CODES` is additionally reached dynamically via `_ROSTER_CONSUMERS` (H2) and so does not appear
     in a static import scan. It is contract item 4 and is easy to lose precisely because no `import`
     statement names it.

   **Therefore `scripts/validate.py` re-exports every moved name.** Not "most"; a partial re-export fails
   loudly at import, which is the good case, but only for whichever consumer happens to run first.
   `tests/test_validate_public_surface.py` freezes the list independently so the extraction cannot quietly
   shrink it.

### D3 — Five identified hazards are handled explicitly, not discovered during execution

Each was found by direct reading and would break a mechanical refactor silently.

**H1 — `PROJECT_ROOT` retargets on a package move.** `SCRIPT_DIR = Path(__file__).resolve().parent`
(`:79`); `PROJECT_ROOT = SCRIPT_DIR.parent` (`:80`). Under `scripts/validate/__init__.py` this yields
`PROJECT_ROOT = scripts/`. Nothing raises: every check takes its artifact-absent branch and the suite goes
**green while measuring nothing** — the exact failure mode this ADR exists to end, reintroduced across all
59 at once. Four further sites derive paths identically (`:3381`, `:4239`, `:5066`, and
`Path(__file__).parent` at `:179`, `:452`, `:619`, `:6009`).
*Mitigation:* path anchoring is centralized in `_paths.py` **in Phase 1, while the file stays put**, so the
snapshot proves path-neutrality before anything moves.

**H2 — the roster gate asserts on a module named exactly `validate`.** `_ROSTER_CONSUMERS` (`:6059-6068`)
contains `("validate", ("BUNDLE_CODES",))`; leg B does `importlib.import_module` + `getattr` and requires
key-set equality (`:6175-6189`). *Mitigation:* `__init__.py` re-exports `BUNDLE_CODES` deliberately, and the
harness asserts it. Removing the `_ROSTER_CONSUMERS` entry is prohibited — it would drop `validate` from the
single-source-of-truth gate that exists because the roster was once hardcoded in seven places.

**H3 — registration order is semantically load-bearing.** `counts_fresh` (`:2894`), `tables_fresh`
(`:3011`) and `claim_clusters_fresh` (`:3093`) shell out and **regenerate artifacts that later checks read**;
`run_checks` (`:4874-4886`) iterates in registration order.

*Mitigation, REVISED 2026-08-03 during Phase-2 planning.* The original "preserve order via an explicit
ordered import list" **cannot work**: the current order interleaves domains (#10 Lean, #11 physics, #13
papers, #16 Lean), so no ordering of domain modules reproduces it. Import order and execution order are
genuinely different concerns and must be decoupled.

The suite therefore gains a frozen `_CANONICAL_ORDER` — the 59 names in execution order — and sorts
`_CHECKS` against it once, after all check modules are imported. Module organisation becomes free; execution
order becomes explicit data rather than an emergent property of import statements. A check missing from
`_CANONICAL_ORDER` raises on sort, which is the correct loud failure for a registration that nobody declared
an execution position for.

This is introduced **before** any module moves and verified to be a no-op against the current file (the
registry already happens to be in canonical order), so the ordering mechanism is proven inert before it is
relied upon. `tests/test_validate_registry_contract.py` keeps its OWN independently-frozen list — it must not
import `_CANONICAL_ORDER`, or it would assert only that production agrees with itself.

> **⚠️ The sort must run after the LAST registration, and that is not a detail — it is the mechanism.**
> Recorded because the first implementation (2026-08-03) got it wrong and nothing caught it. The
> `_apply_canonical_order()` call was placed next to its definition, mid-file, which left **14 of the 59
> checks registered below it** — appended in import order, never sorted — and made the clause's own
> `raise` unreachable for anything declared after that point, *including the end of the file, where a new
> check naturally goes*. Verified by mutation: an undeclared check registered at `:7441` ran, listed, and
> exited 0.
>
> Both failures were invisible because the tail happened to already be in canonical sequence, so every
> behavioural test stayed green — the guard written to make ordering explicit was itself order-dependent.
> This is the ADR's own §Context item 3 (no mutation-test discipline) reproduced inside the fix for H3.
>
> Two consequences for the phases that follow. **Phase 2 must place the sort after the check-module import
> block**, at which point "after all registrations" becomes structural rather than positional and this
> hazard retires. Until then the position *is* the contract, and
> `TestCanonicalOrderMechanism::test_the_sort_runs_after_the_last_registration` asserts it from the AST —
> deliberately a source-structure test, because while the tail is coincidentally ordered no behavioural
> test can tell an early sort from a correct one. Its sibling leg asserts the property the `raise` was
> supposed to guarantee (every registered check has a declared position), since a `raise` reachable for
> only part of the registry is evidence of nothing.

**H4 — the eight `lean_deps.json` loaders disagree on missing-file policy** — five PASS (`:571`, `:892`,
`:1047`, `:1130`, `:7413` with a warning), two FAIL (`:6968`, `:7191`), one unguarded (`:6729`).
*(That tally is the **2026-08-03 pre-fix** state. Measured 2026-08-04, after item 1 converted
`native_decide_regression` to FAIL: **4 silent PASS · 1 PASS-with-warning · 3 FAIL**. This divergence is
§Deferred item 4's core population.)* A single
extracted loader silently unifies eight checks' behaviour. *Mitigation:* the helper takes an explicit
`on_missing` policy per call site reproducing today's behaviour exactly, each marked
`TODO(semantic-review)`. The same applies to draft scoping: `bundle_drafts()` (21 drafts) and
`all_paper_drafts()` (64) ship as two named functions, **never one function with a flag** — the difference is
documented and load-bearing (`:6939-6942`).

**H5 — runtime flags are module globals set by `main()`.** `STRICT_MODE` (`:136`), `FORCE_LATEX` (`:148`),
`FORCE_NOTEBOOK_REEXEC` (`:142`), assigned at `:7716-7719`, read across seven checks. A `from validate import
STRICT_MODE` in a split module binds a copy at import time and the flag silently stops working. *Mitigation:*
one config object accessed by attribute; never imported by value.

### D4 — Phased, independently revertible, stoppable after Phase 1

- **Phase 0 — characterization harness. Do this or do nothing:** at the documented eight-inert-guards base
  rate, refactoring this file without it is a coin flip. Scope, set by the measured coverage in §"Test
  protection is thinner than it looks":
  - **Three cheap guards first**, each closing a hazard no current test covers. (i) `assert len(_CHECKS) == 59`
    plus a frozen **ordered** name list (H3) — note `main()` returns 0 for silently-dropped checks because
    `all([])` is `True`; `:7732-7735` guards this for `--check` but **nothing guards the full run**.
    (ii) One propagation test per runtime global (H5): `STRICT_MODE` is read at 12 sites with only 1 tested;
    `FORCE_LATEX` and `FORCE_NOTEBOOK_REEXEC` are untested entirely, and a silently-stuck `False` makes
    `paper_latex_compiles` skip forever and `notebook_exec` return a cache verdict without executing anything.
    (iii) Promote `recurrence_reopens_closures`'s nested `_norm` / `_MIN_OVERLAP` to module scope so its
    fixture test imports them instead of re-implementing them.
  - **Golden `--json` snapshot per check**, not one whole-suite run — a single run lets the
    artifact-regenerating checks contaminate later ones. Measured: two runs of
    `--json --check formula_grounding` diff in exactly one line (`elapsed_seconds`). Normalize by dropping
    that key, sorting `details` by name, scrubbing subprocess job counts, and pinning `PYTHONHASHSEED=0`
    (13 unsorted `glob`/`iterdir` sites plus set-derived comprehensions can otherwise permute detail order).
  - **Ten checks are structurally non-snapshottable and must be quarantined, not forced:** `lean_build`,
    `notebook_exec`, `notebook_stored_outputs_current`, `paper_latex_compiles`, `counts_fresh`,
    `tables_fresh`, `claim_clusters_fresh`, `tracked_hypotheses_fresh`, `bundle_figure_integrity`, and
    `bundle_source_freshness`. They shell out, execute notebooks, or rewrite tracked artifacts, so run
    *N+1* legitimately differs from run *N*. **59 − 10 = 49 characterized checks**, which is what every
    `CHARACTERIZATION HELD — 49 checks identical` line in the working notes refers to; the quarantine set
    is authoritative in `QUARANTINE` in `tests/validate_characterization.py`, verified 2026-08-04.
    *(Filed here as nine; `bundle_source_freshness` was added when the harness was built, and this clause
    was not updated.)* Snapshotting the remaining 49 covers 37 currently-untested checks against
    mechanical damage.
  - **A snapshot detects change, not inertness.** It must ship with D5, or the refactor is validated by the
    same "it still passes" reasoning that produced eight inert guards.
- **Phase 1 — anchors and helpers, file stays put.** `_paths.py` + `helpers/` introduced in place; the 8
  loaders and 10 glob sites rewritten to call them at identical semantics; the 13 redundant `sys.path`
  mutations deleted. H1 cannot bite. Snapshot must be byte-identical. **Most of the value is banked here.**
- **Phase 2 — package split.** Code moves; shim added; `_config` wired; order and re-exports preserved.
  Snapshot must be byte-identical.
- **Phase 3 — semantic fixes,** separately reviewed (§Deferred). **Never** mixed with Phases 1–2.

### D5 — Every check ships with a mutation test (standing obligation, independent of the refactor)

**A new or modified check MUST ship with a test demonstrating both directions: it FAILS on a seeded defect,
and it stays SILENT on correct data.** Where a check has a pure core, the test targets that core; where it
does not, the seeded defect is applied to a fixture or to live state and reverted.

Both halves are mandatory. The file already teaches the second at `:3848-3866`, where a proposed guard
measured to flag **40 correct records** was deliberately **not shipped**, the reasoning recorded in a comment
instead: *"a guard that flags 40 correct records is worse than no guard."*

Precedent exists: `_tp_scan_lines` (`:7573`) was extracted as a pure core specifically to be testable, and
`papers/AutomatedReviews/2026-08-01-0009-internal-adversarial/D11.md:179` records a real mutation test. The
`stage13_status` guard added 2026-08-03 (§Consequences) shipped with one.

---

## Overlap reconciliation with prior ADRs (keep the ADR set one system)

- **ADR-002** owns the `native_decide` policy and its ratchet metric; **ADR-009 owns only the code location**
  of `native_decide_regression`. The ratchet's ceiling, clusters and elimination policy are untouched.
  *One defect is surfaced, not fixed here:* that check reads `docs/counts.json` at registration position ~10,
  **before** `counts_fresh` regenerates it at ~30, so the ratchet can compare against a stale count. It is one
  of only three checks in the commit gate. Deferred to Phase 3 (§Deferred, item 1) — it is a semantic
  ordering fix, and mixing it into a mechanical move is precisely what this ADR forbids.
- **ADR-004** defines the R1–R5 substrate-integrity gates and the *single-writer* posture for generated
  artifacts. Five of its enforcing checks move modules; none changes behaviour. The single-writer rule is
  strengthened, not weakened: H4's explicit per-site policies prevent an extracted helper from becoming a
  second writer of policy.
- **ADR-005 / ADR-007** own the atlas and kernel-no-go ledgers; their enforcing checks (`atlas_integrity`,
  `atlas_hypothesis_discipline`, `nogo_substrate_integrity`) move into `checks/graph_atlas.py` and
  `checks/lean_substrate.py` unchanged.
- **ADR-008** established that shared infrastructure must be compatible before any client activates. This ADR
  adopts the same separation: Phases 0–2 change no behaviour, so no consumer needs to activate anything.

---

## Consequences

**Accepted costs.**
- ~4 days of work on infrastructure that produces no new physics, of which ~1.5 (Phases 0–1) captures most
  of the value.
- The suite gains a package boundary, so a check can no longer reach a sibling's private helper by accident —
  deliberate, and it will surface hidden coupling as import errors during Phase 2.
- `--list` and `--json` become contract surfaces with tests, so changing them costs more than it does today.
  Intended.

**Already realized.** The `stage13_status` guard was added to `check_bundle_metadata_matches_graph`
on 2026-08-03 under separate operator approval, making `stage13_status: "green"` illegal while blockers are
open. It fires on 14 of 21 bundles, passes 7 live negative controls, and reproduces the mutation recorded as
missed at `2026-08-01-0009-internal-adversarial/D11.md:179`.

⚠️ **CORRECTED 2026-08-04.** This clause read *"`validate.py` is consequently RED on `main`"*. **It is not.**
The guard lives on `infra/adr-009-validation-modularization`; `main`'s `validate.py` contains **zero**
`stage13_status` occurrences (verified 2026-08-04). `main` runs all 59 checks and is unaffected by this
guard until the branch merges. The suite is red **on the branch** — which is the dial working as intended,
one merge earlier than this clause implied.

**Risk if not done.** The next check is written against a file no agent can read, on ~80% untested surface,
at a documented base rate of roughly one inert guard per two rounds of adversarial review. The instrumentation
continues to be trusted in proportion to how little it measures.

**Risk if done badly.** H1 alone converts every check into a silent pass. This is why Phase 0 precedes
everything and Phase 1 moves no files.

---

## Alternatives considered

1. **Leave it as one file; add only the mutation-test rule.** Rejected as insufficient, but *closer to
   correct than it appears* — the rule is the load-bearing half. Rejected because the shared-helper defects
   (H4) are live today: five checks currently pass on a missing `lean_deps.json` while two fail, and no
   reader of any single check can see that.
2. **Rewrite the checks while splitting.** Rejected outright. Mixing mechanical and semantic change is the
   documented mechanism by which the inert guards shipped. Phases 1–2 must be provably behaviour-preserving.
3. **Trust the reconnaissance and skip the full read.** Rejected by the operator, and vindicated: the five
   hazards in D3 were all found by reading and none appeared in any reconnaissance report. Two subagent
   claims also required correction — `readiness_submission_gate` was initially reported as a working gate
   (it is effectively always-pass, `:4830`, `:4836`), and `atlas_hypothesis_discipline` was reported as
   contradicting its own "never a gate" description when its `passed=False` at `:3717` is in the
   **exception handler** — a fail-on-cannot-measure, which is the correct pattern.
4. **Split by size rather than domain.** Rejected: arbitrary boundaries would cut the shared-helper clusters
   the refactor exists to consolidate.

---

## Deferred — semantic fixes, each requiring separate review

Identified during the read; explicitly **not** part of Phases 0–2.

> **⚠️ THIS NUMBERING (0–7) IS CANONICAL. Cite Phase-3 work as "§Deferred item N" using it.**
> Added 2026-08-04 because three documents were numbering the same eight items three different ways —
> this list 0–7, `validation-module-migration-notes.md` §7 as 1–7 (+ a referenced "item 0"), and
> `RESUME_STATE.md` as 1–8 in *cost order*, which is a different permutation again. The collision already
> produced two live defects: item 3's table cross-referenced the `readiness_submission_gate` fix as
> "item 1" when item 1 is the `native_decide` fix, and `QA_QI_INFRASTRUCTURE_MAP.md` §6 calls the same fix
> "ADR-009 Phase 3 item 1". Working trackers may order by cost — that is useful — but every cross-reference
> must carry the §Deferred ordinal.
>
> **Status, verified 2026-08-04: 4 of 8 done** — items **1, 2, 3, 7**. Open: **0, 4, 5, 6**.
>
> **Every open item's scope figure is UNVERIFIED and must be re-measured before it is fixed** (item 7's
> filing was wrong four independent ways; item 6's "two gates" is already measured at six — see below).
> That is the §9 standing lesson in the map, and it applies to this list first.

0. **Memoizing `load_lean_deps()` is a behaviour change, not an optimisation** — discovered while
   writing the Phase-1 helper. The eight sites re-read and re-parse the 70 MB file on every call, and that
   is load-bearing: `counts_fresh` (position ~30) shells out to `update_counts.py`, which can **regenerate
   `lean/lean_deps.json` mid-run**. Readers at ~5/7/8/9 observe the pre-regeneration file; readers at
   ~55/56/58 observe the regenerated one. A cache would freeze whichever was read first and silently change
   what the later checks validate against. Note also that these sites read the file **directly**, never
   through `extract_lean_deps.load_lean_deps()`, so they never trigger its hash-guarded refresh. Any caching
   must be reviewed together with the shared-graph-handle item (both change what a check observes).
1. ✅ **DONE 2026-08-03.** `native_decide_regression` read a possibly-stale `counts.json`. **Reordering
   could not have fixed it:** in a full run the check sits at ~9 and `counts_fresh` rewrites the file at
   ~29, but in the **commit gate** it is one of only three checks invoked, in ISOLATION, so `counts_fresh`
   never runs at all — and that is the one moment the ratchet can hard-block `main`. Fixed at the source
   instead: the metric is a pure function of `lean_deps.json`, which `update_counts.py` merely records, so
   the check now computes it directly. `lean_deps.json` is also the stronger input — content-hash staleness
   vs `counts.json`'s mtime. `counts.json` is still compared, as a **staleness signal** rather than as the
   measurement. Measured at the fix: `counts.json` was already stale, and the two values happened to agree
   at 546 — which is why the defect had never produced a wrong verdict, and why it survived.
   Also deduplicated the `native_decide` axiom predicate, which existed in two places and was about to be
   written a third time; one definition now lives in `update_counts` (the ADR-002 metric's owner).
   15 tests, 5 mutations, clean negative control.
2. ✅ **DONE 2026-08-03** (`fd470314`). `readiness_submission_gate` was **inverted**: it failed only when
   zero `ReadinessGate` nodes existed and **passed when it measured RED**, marked only by an inline
   `# WARN not FAIL during rollout`. Its docstring promised a `--strict` path that was **never built** —
   `STRICT_MODE` was not referenced anywhere in the function. Measured at repair: **61 of 64 papers RED,
   verdict `True`** — which is why 14 bundles sat at `stage13_status: green` with open blockers.
   Four distinct defects fixed (the verdict, the per-paper details, the summary line, and a fail-OPEN
   `ImportError` handler); two pure cores extracted to be testable; 11 tests, 5 mutations, clean negative
   control. **`validate.py` is RED on this check by design** until the bundles are remediated.
   ⚠️ Harness lesson from it, now standing: **scope every mutation to the target function's AST span.**
   Two mutations read as MISSED because `str.replace(…, 1)` hit the first textual match in the file —
   inside a *different* function.
3. ✅ **DISPOSITIONED 2026-08-03.** The eight always-pass checks, decided individually. Four were
   defects and are fixed; four are honestly advisory and stay that way. The distinction is not
   "does it fail" — it is **whether the check's own reasoning survives contact with what it measures.**

   | check | disposition | why |
   |---|---|---|
   | `readiness_submission_gate` | **FIXED** (item **2**) | Inverted. 61 of 64 papers RED, verdict `True`. |
   | `paper_latex_compiles` | **FIXED** — hard-fails | Computed `all_pass` and discarded it. Its stated reason (transient toolchain gaps) is already handled by two earlier returns — missing `pdflatex`, and the slow-gate skip. What reaches the verdict is a draft a working `pdflatex` could not compile. **Measured: D3 fails with 2 fatal `! Undefined control sequence`.** |
   | `count_literals` | **FIXED** — ratchet | "WARN-level until all 15 papers use macros." The corpus is 64 papers; the target receded faster than it was approached. Frozen at `COUNT_LITERAL_CEILING = 107`; new literals fail. |
   | `numerical_literals` | **FIXED** — ratchet | Same shape. `NUMERICAL_LITERAL_CEILING = 116`. |
   | `elaboration_knob_watchlist` | **advisory — keep** | The best-reasoned advisory in the suite. `maxRecDepth` / `synthInstance` are *elaboration-time* knobs; the kernel re-checks the final term and never reads them, so they add nothing to the axiom closure. Mathlib uses them routinely. The only real cost — a `decide` heavy enough to need a knob is a slow kernel reduction — is an upstreaming consideration, not a soundness one. 46 sites, all kernel-pure. |
   | `paper_toolchain_pin_drift` | **advisory — keep** | A stale pin in a DRAFT is a publication decision, not a defect: does this paper re-verify under the new pin (update the literal), or does it record the pin it was actually verified under (keep it, and say so)? A gate that auto-failed would push authors toward find-and-replace, silently asserting the former for every draft. It reports; Stage 13 decides. |
   | `viz_consistency` | **advisory — keep** | Notebook figure-tracking hygiene — untagged `.show()`, hardcoded `COLORS` hex. Real signal, but it grades authoring style in exploratory notebooks, and the artifacts that ship are gated by `bundle_figure_integrity` (legibility floor + render drift), which *can* fail. |
   | `inventory_index_autogen_fresh` | **advisory — keep** | A stale doc index is documentation hygiene, and the generator is one command away. It also *cannot* silently rot: `sync.py --fast` regenerates it on every commit, so staleness is transient by construction. Currently clean. |

   **A ratchet, not a walk-back.** `count_literals` and `numerical_literals` both promised escalation in
   their own docstrings, so declaring them permanently advisory would be exactly the prose walk-back this
   project forbids. Freezing the debt and failing on growth makes the promise real *today* without
   requiring the retrofit to finish first — and it is the house idiom already
   (`NATIVE_DECIDE_DECL_CLOSURE_CEILING`, `VACUOUS_STATEMENT_BASELINE`).

   **Live consequence:** `paper_latex_compiles` now fails on D3. That is a genuine publication blocker
   for that bundle and belongs to the paper-remediation workstream, not to this ADR.
4. **No `UNEVALUATED` result state.** ⚠️ **RE-SHAPED 2026-08-04 by a full read of all eleven check
   modules.** The "roughly twenty sites" figure in §Context is in the right ballpark — ~11 return
   `passed=True` from an `except` handler, and the missing-artifact class adds roughly as many again —
   **but the framing was wrong. Do not add a third `CheckResult` state.** `passed` is consumed by
   `print_results`, `archive_results`, the `--json` payload (**D2 contract item 5**), `gate_precheck.py`
   and `pre-commit-sync.sh`; a third state is a contract break.

   More importantly, the project has **already hand-converted a substantial share of the population** to
   FAIL-on-cannot-measure, each with the reasoning written in-body: `bundle_metadata_matches_graph`,
   `readiness_verdicts_agree`, `readiness_submission_gate`, `review_docs_mint_findings`,
   `recurrence_reopens_closures`, `native_decide_regression`, `notebook_stored_outputs_current` (empty
   glob → FAIL) and both of `graph_integrity`'s inner guards. **Treat this item as finishing that per-site
   sweep, with the readiness/graph family as the template — or decline the type change with the
   measurement.** *(Counting both populations exactly is step 1; an intermediate note claimed "~60 %",
   which was never computed and is withdrawn.)*

   Remaining PASS-on-cannot-measure sites concentrate in `axiom_closure_allowlist` (**five** separate PASS
   returns — no lake, no source file, timeout, non-zero rc, unparseable JSON), `paper_latex_compiles` (2),
   `paper_toolchain_pin_drift` (2), `inventory_index_autogen_fresh` (2), plus the import guards in
   `notebooks`, `bundle_figure_integrity`, `tracked_hypotheses_fresh` and `bibitem_title_primary_source`.
   Two are annotated in-body as the **H1-silent** sites: `accepted_findings_carry_rationale` (missing
   ledger → PASS) and `citation_primary_sources_present`'s duplicate-key guard (exception → advisory).
5. ⛔ **`count_literals` ⊂ `axiom_count_prose_consistency` — THE PREMISE IS FALSE.** Both bodies read
   2026-08-04; neither half of this filing survives.
   - `count_literals` is **no longer "incapable of failing"** — item 3 converted it to a ratchet against
     `COUNT_LITERAL_CEILING`, in this same ADR.
   - They are **not the same predicate.** `count_literals` ratchets the *density* of literal counts
     ("N theorems", "N modules", "N sorry") and compares them to nothing.
     `axiom_count_prose_consistency` performs a **value comparison against computed truth**
     (`docs/counts.json` → `lean.axioms`) with a ±120-char historical-attribution window and a
     preceding-negation guard, hard-failing only when prose asserts a live axiom while the count is 0.
     **Merging them would destroy the comparison-to-truth.**

   **Disposition: DECLINE the merge**, on the measurement above. The inverse is the real finding and is
   worth shipping separately: *`axiom_count_prose_consistency` is the model `count_literals` should be
   raised to* — compare each literal against its `counts.tex` macro value rather than merely counting
   literals. That is new work, not a merge, and needs its own review.
6. `--strict` is passed by no automated caller — not the commit hook, not `gate_precheck.py` — so every
   strict-only leg in the suite is dead code in practice.
   ⚠️ **Filed as "two gates" (`axiom_closure_allowlist`, `bundle_source_freshness`). Re-measured
   2026-08-04 by AST: SIX registered checks read `_cfg.STRICT_MODE`** — those two plus
   `parameter_provenance`, `provenance_doi_in_registry`, `bibitem_title_primary_source` and
   `theorem_name_embedded_citations`. The fix must still partition them: a check whose *only* failure
   path is strict-only is unreachable, whereas one that merely *promotes an advisory* under `--strict`
   still fails on its own terms by default. That partition is the first step of this item, not an
   assumption to inherit — the filed "two" conflated the two categories.
7. ✅ **DONE 2026-08-03 — both halves.** **`build_graph`'s Lean-side VERIFIES resolver manufactured
   coverage from library aliases.** Found while attributing a characterization diff.
   `extract_verifies_edges` (`build_graph.py:3634`; earlier revisions of this ADR called it
   `extract_test_verifies_edges`, a name that has never existed) resolves each of a test's
   `referenced_names` against Formula, Parameter, then **Lean short names**. The *formula* branch is
   deliberately guarded — `_FORMULA_MODULE_ALIASES` restricts dotted tails to
   `{F, formulas, src.core.formulas}`, with a comment stating that a blanket tail fallback
   "would let `np.sum` or `math.exp` match a formula named `sum` or `exp`, manufacturing coverage that does
   not exist". **The Lean branch had no equivalent guard**, so exactly that happened.

   **⚠️ Two claims in the original filing were wrong, and both were corrected by measuring rather than
   by re-reading the note.**

   - **The count was understated 14-fold.** This item recorded "10 of the 534". The real figure is
     **144 of 536** — the original was a sample of five example names, not a sum. Measured by
     partitioning every ref that reaches the Lean branch: `np.all` (58) → `FaultTolerance.Pauli.all`,
     `v` (21, the conventional `import validate as v`) → `EWMassMatrixInputs.v`, `np.diag` (11) →
     `IsCharQ.diag`, `np.dot` (10) → `KMM.Col.dot`, `mx.eval` (8) → `IntFundamentalClass.eval`,
     `CITATION_REGISTRY.get` / `PARAMETER_PROVENANCE.get` (8) → `NeutrinoMixing.get`, and 18 more.
   - **`ComputationCorrectness` was named as the consumer and is not one.** That gate iterates
     `formula_ids` and reads `idx.incoming(fid, 'VERIFIES')` for `formula:` targets only
     (`readiness_gates.py:283-294`) — it never sees a Lean-targeted edge. The real consumers are
     `last_modified.py`'s `PROPAGATION_EDGE_TYPES` (VERIFIES propagates a test file's mtime onto the Lean
     node, feeding the Wave-10c change-bus and sentence-freshness check) and any human or dashboard
     reading the graph's Lean coverage picture. So the defect was *staleness pollution plus fabricated
     evidence in the graph*, not a wrong gate verdict — a smaller blast radius than filed, and worth
     recording as such rather than leaving the stronger claim standing.

   The protection that did exist was accidental: collisions are spared only by AMBIGUITY — the resolver
   skips names with ≥2 candidates, and the run log shows `np.sum`, `np.conj`, `math.e`, `re.compile`,
   `sp.I` all being *attempted*. A name that happens to be unique gets through, so the guard weakened as
   the Lean library grew more unique short names.

   **The fix was not one line.** The filing proposed "an alias allow-list, or require the ref to be
   undotted". Neither alone suffices: `v` is undotted, and there is no Python alias that means "Lean", so
   an allow-list has nothing to list. The measurement showed the two failure modes are independent and
   need one rule each:
   - a ref rooted at a **module alias** (`import X [as y]`) denotes a Python module and can never be a
     Lean declaration — this is what kills bare `v`, `m`, `time`, `ext` *and* every `np.*`/`mx.*`/`sp.*`;
   - a **dotted** ref is a Python attribute access, so it may resolve only as a full Lean name, never by
     its tail — this is what kills `PARAMETER_PROVENANCE.get` and the five distinct
     `CANDIDATE_*.basic_viability` refs that all collapsed onto one Lean field.

   Both mutation-verified as load-bearing: dropping either rule alone is CAUGHT. Module aliases are
   recorded during test-node extraction into `_TEST_MODULE_ALIASES` (the `_LEAN_SHORT_INDEX` pattern —
   a property of the file, so not stored on all 4,400 test nodes). `from M import a` is deliberately NOT
   recorded: those symbols are the Python↔Lean naming correspondence the branch exists to follow, and
   `from src.core import formulas as F` is a from-import, so the formula branch's `F.` path is untouched.

   **Why it was safe to land mid-remediation:** the Lean branch runs only after the Formula and Parameter
   indexes have both missed, so it can neither add nor remove a formula- or param-targeted edge. Verified
   empirically — **1,390 non-Lean edges before and after, bit-identical** — which is what makes "no
   `ComputationCorrectness` verdict can move" a measurement rather than an argument.

   Characterization: one check moved, fully attributed. `graph_integrity` **+16 nodes** (the 16 tests in
   the new guard file), **−144 edges** (the fabricated set exactly; zero added), **+167 orphans** = 135
   PythonTests that lost their last edge + 16 Lean declarations that lost their last edge + the 16 new
   test nodes, with **0 nodes leaving** the orphan set. That 135 is the honest picture arriving: those
   tests' only graph coverage was fabricated. All 17 Lean declarations that lost an edge lost *every*
   edge they had — none had genuine coverage mixed in, which is the strongest evidence the partition is
   the right one. 16 tests, 6 mutations all caught, clean negative control.

   **⚠️ The same subsystem also DROPPED real coverage**, found while attributing a Phase-3
   characterization delta. `extract_python_test_nodes` minted its node id as
   `test:<module>::<function>` — **the class is not in the key** — and deduped on it. So two tests with the
   same method name in different classes of one file collided, and every one after the first was silently
   discarded. Measured corpus-wide: **4,416 `def test_*` in `tests/` produced 4,350 PythonTest nodes — 66
   tests missing.** It surfaced because a new 9-test file minted 7 nodes.

   So the graph's coverage picture was wrong in *both* directions at once — inflated by alias-resolved
   phantom edges, deflated by dropped nodes. Unlike the fabricated edges, the dropped nodes *did* reach
   `ComputationCorrectness`: a dropped node takes its formula-targeted edges with it.

   ✅ **The dropped-node half was fixed first (2026-08-03).** The id now mirrors pytest's own nodeid shape,
   `test:<module>::<Class>::<method>`, and a genuine duplicate logs a warning instead of vanishing.
   **4,416 defs → 4,416 nodes, 66 recovered.** Safe to change: the id is constructed in exactly one place,
   consumed only within the same build, and persisted nowhere (`write_graph_to_pg` is delete-and-rewrite;
   neither the supersession ledger nor bundle metadata references a `test:` id).
   `TestGraphTestNodeCoverage` asserts node count == `def test_*` count, mutation-verified.

---

## References

- `scripts/validate.py` — read in full 2026-08-03; all line citations above verified against that read.
- `docs/architecture/.working-docs/` — migration working notes, module layout, per-check assignment.
- `docs/audits/2026-08-01-publication-readiness/` — the audit that surfaced this work; `SYNTHESIS.md` §2
  documents the absence-of-measurement finding across five independent mechanisms.
- `papers/AutomatedReviews/2026-07-31-1652-internal-adversarial/D11.md:227` — the `stage13_status` remedy,
  authored by this project's own reviewer.
- `papers/AutomatedReviews/2026-08-01-0009-internal-adversarial/D11.md:179` — the committed mutation test
  that recorded the hole as `PASS <-- missed`.
- Commits `edd9878d`, `221cb6c9`, `ad844e42`, `b6830c7d`, `5073276a`, `055083ad`, `bcbeee6b` — the
  inert-guard history motivating D5.
