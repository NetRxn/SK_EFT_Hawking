# `validate.py` → `scripts/validate/` — migration working notes

> **⚠️ WORKING DOCUMENT — not the decision record.**
> The decision, its hazards, the migration contract and the mutation-test obligation live in
> **[ADR-009](../../adrs/ADR-009-validation-suite-modularization.md)**, which is authoritative.
> This file holds the execution detail the ADR summarizes: the package layout, the per-check module
> assignment, and the working evidence behind each hazard. Where the two differ, ADR-009 wins.

**Status:** working notes. No implementation until ADR-009 is accepted and Phase 0 lands.
**Author's basis:** the entire 7,778-line `scripts/validate.py` read directly, line 1 to line 7,779, on
2026-08-03. Every claim below is verified against the source, not against a subagent report.

**Operator constraints (2026-08-03):**
> "I think that, when the python file is too large to read directly in one go, it creates a risk to re-create
> these same issues. Was thinking of turning the validation piece into a legit module rather than a single
> file… since it's critical & core infra, would want to go through the full architecture / planning piece
> first… you can only modify core infra systems you're fully aware of… all files you modify must be read
> directly — err on the side of over-read until the remediation plan is set in stone."

---

## 1. Why this file grew, and what actually went wrong

Growth: 1,158 lines (2026-03-26) → **7,778** (2026-08-03). ~2,550 of those landed in the five weeks to
07-31; ~1,650 on 07-31 alone.

**The architecture is not the problem.** `@register_check(name, description)` (`validate.py:151-156`) is a
clean contract, documented at `:34-43`, and every check added on 07-31 followed it. Those additions are also
the **best-written** checks in the file — three of them carry explicit *"FAIL, not pass, because unverified ≠
agreement"* reasoning (`:4302-4310`, `:4317-4322`, `:4330-4336`).

**Three things did go wrong, and only one of them is fixed by splitting files:**

| Problem | Fixed by a module split? |
|---|---|
| No shared helper layer → 8 divergent `lean_deps.json` loaders, 3 incompatible draft-scoping idioms | **Yes** — this is the real payoff |
| File exceeds what an agent can read in one pass → new checks written without seeing the old ones | **Yes** — indirectly |
| **No mutation-test discipline** → 8 shipped guards that could not fire | **No.** This is a process rule, and it is the one that caused the damage |

The file's own commit log is the evidence for the third: `edd9878d` *"the drift guard was dead code"*,
`221cb6c9` *"my closure guard was inert and my mutation test hid it"*, `b6830c7d` *"the readiness gate was
blind in three stacked layers"*, `5073276a` *"an eighth guard that could not fire"*. **A refactor that does
not also land the mutation-test rule fixes the symptom and not the disease.**

---

## 2. Hazards that would break a naive refactor

All five found by reading the source; none surfaced in reconnaissance. Each is a hard constraint on the
migration, not a nice-to-have.

### H1 — `PROJECT_ROOT` is derived from `__file__` and silently shifts on a package move

```python
SCRIPT_DIR   = Path(__file__).resolve().parent   # validate.py:79  → scripts/
PROJECT_ROOT = SCRIPT_DIR.parent                 # validate.py:80  → repo root
```

Moving to `scripts/validate/__init__.py` makes `SCRIPT_DIR` = `scripts/validate/` and **`PROJECT_ROOT` =
`scripts/`**. Every path in the file — `LEAN_DIR`, `PAPERS_DIR`, `NOTEBOOKS_DIR`, `SRC_DIR`, `REPORTS_DIR`,
`COUNTS_JSON_PATH` — silently retargets into a directory that does not exist. Checks would not crash loudly;
they would take their *"artifact absent → PASS"* branches (§H4) and the suite would go **green while
measuring nothing**. That is precisely the failure mode this whole engagement exists to eliminate, and a
mechanical refactor is the most likely way to reintroduce it at full scale.

Three more sites derive paths the same way and must move together: `:3381`, `:4239`, `:5066` (each
`Path(__file__).resolve().parent.parent / "docs" / …`), plus `Path(__file__).parent` at `:179`, `:452`,
`:619`, `:6009`.

**Constraint:** path anchoring must become explicit and single-sourced *before* any file moves, and the
golden snapshot (§5, Phase 0) must be taken with the anchors already centralized so the move is provably
path-neutral.

### H2 — `check_bundle_registry_consistency` asserts on a module named exactly `validate`

`_ROSTER_CONSUMERS` (`:6059-6068`) contains `("validate", ("BUNDLE_CODES",))`, and leg B does
`importlib.import_module(mod_name)` then `getattr(mod, attr)` (`:6175-6189`), requiring the key set to equal
the registry's exactly.

So the refactor must preserve **both** `import validate` resolving **and** `validate.BUNDLE_CODES` existing
at top level. A package `scripts/validate/__init__.py` that re-exports it satisfies this — but only if the
re-export is deliberate. Miss it and the roster gate fails, or worse, `_ROSTER_CONSUMERS` gets "fixed" by
deleting the entry, silently removing `validate` from the single-source-of-truth gate.

Note the irony: this is the gate that exists because the roster was hardcoded in seven places. Breaking it
during a refactor would re-open exactly what it was built to close.

### H3 — Registration order is semantically load-bearing, not cosmetic

Three checks **mutate artifacts that later checks read**:

- `counts_fresh` (`:2894`) shells out to `update_counts.py`, regenerating `docs/counts.json` + `counts.tex`
- `tables_fresh` (`:3011`) regenerates `papers/*/tables/*.tex`
- `claim_clusters_fresh` (`:3093`) regenerates `papers/claim_clusters.json`

`run_checks` (`:4874-4886`) iterates `_CHECKS` in registration order. So a package split that changes import
order changes *what data later checks see*. `axiom_count_prose_consistency` (`:6489`) reads `counts.json`
and is registered **after** `counts_fresh` — correctly.

**And this ordering already contains a live defect.** `native_decide_regression` (`:1203`) reads
`docs/counts.json` for the ADR-002 ratchet, and is registered at position ~10 — **before** `counts_fresh`
regenerates it at ~30. So the ratchet can compare `native_decide_decl_closure` against a **stale**
`counts.json`. This check is one of only three wired into the commit gate (`pre-commit-sync.sh:96`), where it
can hard-block on `main`. Filed as a §7 semantic fix; **not** to be repaired during the mechanical move.

**Constraint:** registration order must be byte-preserved across the migration, and the golden snapshot must
assert the ordered check-name list, not just the set.

> **⚠️ MITIGATION REVISED 2026-08-03.** "Preserve order via an explicit ordered import list" **cannot
> work**: the live order interleaves domains (#10 Lean, #11 physics, #13 papers, #16 Lean), so no ordering
> of domain modules reproduces it. Import order and execution order are different concerns and are now
> decoupled — `validate._CANONICAL_ORDER` declares the 59 names as data and `_apply_canonical_order()`
> sorts `_CHECKS` once. Module organisation becomes free; order becomes explicit.
>
> **The sort must run after the LAST registration.** The first implementation put the call next to its
> definition, mid-file, leaving 14 of 59 checks unsorted below it and making its "undeclared check" `raise`
> unreachable for anything registered after that point — including the end of the file. Both were invisible
> because the tail was coincidentally in canonical order. In Phase 2 the call goes **after the
> `validation.checks.*` import block**, which makes "after all registrations" structural; until then
> `TestCanonicalOrderMechanism` asserts the position from the AST.

### H4 — Divergent "artifact absent" policies, which a shared loader would silently unify

Eight independent `lean_deps.json` load sites, with **incompatible** missing-file semantics:

| Site | Policy on absent |
|---|---|
| `:571-573` (`tracked_hypothesis_ledger`) | `passed=True` |
| `:892-893` (`formula_grounding`) | `passed=True` |
| `:1047-1049` (`vacuous_statement_audit`) | `passed=True` |
| `:1130-1132` (`nogo_substrate_integrity`) | `passed=True` |
| `:6968-6974` (`prose_theorem_reference_coverage`) | **`passed=False`** |
| `:7191-7197` (`theorem_name_embedded_citations`) | **`passed=False`** |
| `:7413-7416` (`lean_docstring_refs_resolve`) | `passed=True` + warning |
| `:6729-6730` (`_load_lean_name_index`) | **unguarded** — raises |

Extracting one `load_lean_deps()` **forces a decision** about which policy is correct, for eight checks at
once. That is a semantic change wearing a mechanical disguise, and it is exactly how a "cleanup" turns five
gates into no-ops.

**Constraint:** the extracted helper takes an explicit `on_missing` policy per call site, reproducing each
site's current behaviour **exactly**, with a `# TODO(semantic-review)` marker. Unifying the policy is a §7
item requiring its own review.

The same applies to draft scoping — three incompatible idioms live today:
`PAPERS_DIR.iterdir()` + `paper_draft.tex` (`:286`, `:360`, `:2609`); `PAPERS_DIR.glob("*/paper_draft.tex")`
(`:3198`, `:3781`, `:5097`, `:6535`, `:7634`); and `BUNDLE_CODES`-scoped (`:6984`, `:7235`). The first two
cover **64** drafts, the third covers **21**. That difference is load-bearing and documented
(`:6939-6942`), and must survive as `bundle_drafts()` vs `all_paper_drafts()` — two explicitly named
functions, never one with a flag.

### H5 — Module-global mutable state read across check boundaries

| Global | Line | Read by |
|---|---|---|
| `STRICT_MODE` | 136 | `axiom_closure_allowlist:2006`, `parameter_provenance:2782`, `provenance_doi_in_registry:5426`, `bundle_source_freshness:5630`, `bibitem_title_primary_source:5858-5882`, `theorem_name_embedded_citations:7281-7291` |
| `FORCE_LATEX` | 148 | `paper_latex_compiles:6283` — set at `:7719` from `--force-latex` **or** `--check paper_latex_compiles` |
| `FORCE_NOTEBOOK_REEXEC` | 142 | `notebook_exec:2392-2415` |
| `_LEAN_NAME_INDEX_CACHE` | 6712 | `_load_lean_name_index` |
| `_LEAN_SOURCE_CACHE` | 6792 | `_lean_source_declares` |
| `_PHYSLIB_SOURCE_CACHE` | 6825 | `_physlib_declares` |
| `_CHECKS` | 131 | registration + `run_checks` + `print_results` + `--list` + the unknown-check guard `:7732` |

`main()` sets the first three via `global` at `:7716-7719`. Split across modules, a `from validate import
STRICT_MODE` binds a **copy at import time** and the flag stops working — silently, since the affected
checks simply take their non-strict branch.

> **⚠️ CORRECTION 2026-08-03 — the three caches are NOT shared across checks.** This section claimed they
> "are shared across checks within a run". Measured: all three are populated and consumed inside the call
> tree of **one** check, `prose_theorem_reference_coverage`, via `_load_lean_name_index()` and
> `_resolve_prose_ref()`. No other check reaches them. So they move together with that check and carry no
> cross-module sharing obligation — but if the resolver helpers are ever split from the cache globals, the
> H5 rule below applies to them unchanged. (The same wrong claim was also in
> `tests/validate_characterization.py`'s rationale and is corrected there.)

**Constraint:** runtime flags move into a single explicit config object passed to checks, or stay in one
module accessed by attribute (`cfg.STRICT_MODE`), never imported by value.

✅ **SHIPPED** as `scripts/validation/_config.py`. `validate.STRICT_MODE` and siblings **no longer exist** —
one owner, reached as `_cfg.<FLAG>`.

> **⚠️ The `co_names` guard written for this hazard did not cover it.** `co_names` records names used for
> `LOAD_ATTR` as well as `LOAD_GLOBAL`, so `from validate import STRICT_MODE` still puts `STRICT_MODE` in
> the function's `co_names` — a global lookup resolving against the *wrong* namespace. The value freezes at
> import time, `--strict` becomes a no-op, and the guard stays green. Closed structurally: consuming checks
> must show `_cfg` in `co_names`, and `TestNoCheckModuleShadowsAFlag` asserts that **no suite module binds a
> flag in its own namespace at all**, which holds however the body reads it. Mutation-verified both ways.

---

## 3. What must not change (the migration contract)

Asserted by the golden snapshot at every phase boundary:

1. **`--list` output byte-identical** — 59 names, same order, same descriptions.
2. **Per-check `passed` values identical** on the live tree.
3. **Exit codes identical** — 0 all-pass, 1 any-fail, **2** unknown `--check` (`:7732-7735`; the inline
   comment explains that `all([]) == True` would otherwise silently disable the gate).
4. **`import validate` works and exposes `BUNDLE_CODES`** (H2).
5. **`--json` payload schema unchanged** — `gate_precheck.py` and `pre-commit-sync.sh` parse it.
6. **`--check <name>` for all 59 names** behaves as today, including the `FORCE_LATEX` side-effect at `:7719`.
7. **No new import-time side effects.** Registration must stay the only one.

---

## 4. Target architecture

> **⚠️ CORRECTED 2026-08-03 — the layout below is NOT the one this section originally described.**
> It specified a `scripts/validate/` **package** plus a thin `scripts/validate.py` **shim**. Those cannot
> coexist: a package **shadows** a same-named module on the same `sys.path` entry (verified empirically),
> so `import validate` would resolve to `validate/__init__.py` and the shim would be unreachable — dead
> code that looks load-bearing, while silently satisfying H2 through a file nobody realised was live.
> ADR-009 D1 carries the correction. The package is **`scripts/validation/`**; `scripts/validate.py`
> **stays a module** and remains the framework core.

```
scripts/validate.py              # STAYS A MODULE — the framework core (~400 lines):
                                 #   Detail / CheckResult / CheckSpec, the _CHECKS registry +
                                 #   register_check, _CANONICAL_ORDER + _apply_canonical_order,
                                 #   run_checks, print_results, archive_results, main, and the
                                 #   BUNDLE_CODES re-export H2 requires. Imports validation.checks.*
                                 #   for their registration side-effect, THEN sorts (H3).
scripts/validate_helpers.py      # THE path anchor + artifact loaders (H1, H4). Shipped in Phase 1;
                                 #   stays at scripts/ so its anchor keeps resolving.
scripts/validation/
  __init__.py                    # package docstring only — no re-exports, no import side effects.
                                 #   ⚠️ Execution order does NOT live here (see H3 below).
  _config.py                     # STRICT_MODE / FORCE_LATEX / FORCE_NOTEBOOK_REEXEC (H5).  ✅ SHIPPED
                                 #   Reached as `_cfg.<FLAG>`; never imported by value.
  helpers/                       # (not yet created — validate_helpers.py covers Phase 1's needs)
    tex.py                       # _strip_tex_comments, _line_of, shared regexes
  checks/
    lean_substrate.py            # SUBSTANCE gates (R1-R3): formulas, placeholder_not_cited,
                                 #   disclosure_consistency, proxy_body_audit, tracked_hypothesis_ledger,
                                 #   tracked_hypotheses_fresh, formula_grounding, vacuous_statement_audit,
                                 #   nogo_substrate_integrity  + the type-thinness classifier they share
    lean_toolchain.py            # BUILD + TRUST SURFACE: native_decide_regression, theorems, lean_source,
                                 #   lean_build, axiom_closure_allowlist, elaboration_knob_watchlist,
                                 #   lean_docstring_refs_resolve
                                 # ⚠️ SPLIT FROM lean_substrate 2026-08-03. As one module the assignment
                                 #   above measured ~1,580 lines, which fails the criterion the whole split
                                 #   exists to satisfy — every file readable in one pass (D1). The two halves
                                 #   share NO helpers, which is the seam confirming itself: one asks "does
                                 #   this theorem prove anything", the other "does it build and what does it
                                 #   trust". `theorems` lands in lean_toolchain; the table never assigned it.
    physics.py                   # numerical, identities, physical_bounds, cross_path_consistency, cgl_fdr,
                                 #   quantum_network, paper_table, d1_hierarchy_table, f_hierarchy_claims
    papers_prose.py              # count_literals, numerical_literals, axiom_count_prose_consistency,
                                 #   prose_theorem_reference_coverage, theorem_name_embedded_citations,
                                 #   paper_provenance, paper_latex_compiles
    citations.py                 # citation_primary_sources_present, bibitem_title_primary_source,
                                 #   provenance_doi_in_registry, parameter_provenance
    bundles_readiness.py         # bundle_consistency, bundle_registry_consistency, bundle_metadata_matches_graph,
                                 #   readiness_verdicts_agree, readiness_submission_gate, bundle_figure_integrity,
                                 #   review_* , recurrence_reopens_closures, accepted_findings_carry_rationale
    graph_atlas.py               # graph_integrity, atlas_integrity, atlas_hypothesis_discipline
    freshness.py                 # counts_fresh, tables_fresh, claim_clusters_fresh, bundle_source_freshness,
                                 #   inventory_index_autogen_fresh, notebook_stored_outputs_current
    notebooks.py                 # notebooks, notebook_exec, viz_consistency
```

Roughly 250 lines of framework + eight domain modules averaging ~900. Every module fits in one read.

**Deliberately NOT changed in the move:** no check body is edited, no policy unified, no always-pass flipped,
no threshold touched. The diff should be almost entirely moves plus import rewrites.

---

## 5. Migration sequence

Each phase is independently revertible and gated on the snapshot. Stoppable after Phase 1 with most of the
value banked.

**Phase 0 — characterization harness (~0.5 day). Do this or do nothing.**
Golden `validate.py --json --no-archive` snapshot, normalized for nondeterminism (elapsed time, absolute
paths, timestamps, set-iteration order — the fourth exploration is enumerating these), plus a test asserting
the ordered 59-name `--list` output and the three exit codes. Without it, a refactor of this file is a coin
flip at the documented eight-inert-guards base rate.

**Phase 1 — anchors + helpers, file stays put (~1 day). Highest value-to-risk.**
Introduce `_paths.py` and the `helpers/` layer *in place*; rewrite the 8 loaders and 10 glob sites to call
them, each preserving its exact current policy (H4). Delete the 13 redundant `sys.path.insert` calls. **No
files move**, so H1 cannot bite yet. Snapshot must be byte-identical.

**Phase 2 — package split (~1–2 days).** Move code into `checks/*`, add the `validate.py` shim, wire
`_config` (H5), preserve registration order via an explicit ordered import list (H3), re-export
`BUNDLE_CODES` (H2). Still no behaviour change; snapshot must be byte-identical.

**Phase 3 — semantic fixes, separately reviewed (§7).** Never mixed with 1 or 2. Mixing mechanical and
semantic change is how the inert guards shipped.

---

## 6. Standing rule (independent of the refactor)

**Every new or modified check ships with a mutation test proving it FAILS on a seeded defect.**

Precedent exists: `_tp_scan_lines` (`:7573`) was split out as a pure core specifically to be testable, and
`2026-08-01-0009-internal-adversarial/D11.md:179` records a real mutation test. The `stage13_status` guard
added 2026-08-03 shipped with one (seed D11 `pending→green` → drift 14→15; reverted).

Corollary the file teaches at `:3848-3866` — a guard measured to flag 40 correct records was **not shipped**,
with the reasoning recorded instead. *A guard that flags correct data is worse than no guard.* The mutation
test must demonstrate both directions: fires on the defect, silent on correct data.

---

## 7. Semantic fixes held back for separate review

Identified while reading; **not** part of the mechanical work.

> ⚠️ **These 1–7 match ADR-009 §Deferred's canonical 1–7** (its item **0**, memoizing `load_lean_deps()` +
> the shared graph handle, is referenced in §8 below but was never given a numbered slot here — that is
> the eighth item). **Cite Phase-3 work by the §Deferred ordinal, never by `RESUME_STATE.md`'s list**,
> which is the same eight in *cost order* — a different permutation that has already produced two
> mis-citations. Status 2026-08-04: **items 1, 2, 3, 7 DONE; 0, 4, 5, 6 open.**

1. **`native_decide_regression` reads a possibly-stale `counts.json`** (H3). Ratchet ordering defect, in a
   commit-gate check.
2. **`readiness_submission_gate` is inverted** (`:4770-4836`): fails only when zero `ReadinessGate` nodes
   exist, passes when it measures RED (`:4830` `# WARN not FAIL during rollout`). Its docstring promises a
   `--strict` path (`:4756`) that **was never built** — `STRICT_MODE` is not referenced in the function.
   This is why 14 RED bundles never fired it.
3. **The 8 always-pass checks** — decide per check whether always-pass is intended: `paper_latex_compiles`
   (`:6347`), `paper_toolchain_pin_drift` (`:7675`), `count_literals` (`:3841`), `numerical_literals`
   (`:3252`), `viz_consistency` (`:2325`), `elaboration_knob_watchlist` (`:2077`),
   `inventory_index_autogen_fresh` (`:7358`), `readiness_submission_gate` (`:4836`).
   Three are honestly advisory by design; `paper_latex_compiles` and `readiness_submission_gate` are not.
4. **No `UNEVALUATED` result state** (`:105-119`): `passed` is a bare `bool`; `warning` is documented as
   *"passed but with advisory"*. ~20 sites encode "couldn't measure" as PASS. The concept already exists in
   comments and three hand-patched sites (`:4302`, `:4317`, `:4330`) — it does not exist in the type system.
5. **`count_literals` ⊂ `axiom_count_prose_consistency`** — same predicate shape, split by subject; one
   hard-fails, one cannot fail. Candidates to merge into one parameterized check.
6. **`--strict` is passed by nothing automated** — not the commit hook, not `gate_precheck.py`, so every
   strict-only leg is dead code in practice. ⚠️ **Filed as "two gates"
   (`axiom_closure_allowlist`, `bundle_source_freshness`); re-measured 2026-08-04 by AST at SIX**
   registered checks reading `_cfg.STRICT_MODE` — those two plus `parameter_provenance`,
   `provenance_doi_in_registry`, `bibitem_title_primary_source`, `theorem_name_embedded_citations`.
   Partition "unreachable without `--strict`" from "merely promotes an advisory" first; the filed
   figure conflated them.
7. ✅ **DONE 2026-08-03 — fabricated VERIFIES edges from library aliases** (`extract_verifies_edges`,
   `build_graph.py:3634`). The Lean short-name branch of the test-coverage resolver had no alias guard,
   though the formula branch beside it has one with a comment explaining exactly this risk. **144 of 536**
   Lean-targeted edges were false — `np.all` → `FaultTolerance.Pauli.all`, `v` → `EWMassMatrixInputs.v`.
   Two rules now gate it (module-alias roots, and no tail-resolution of dotted refs); both mutation-verified
   as load-bearing.
   ⚠️ **Three things in this entry as originally filed were wrong**, and each was caught by measuring
   instead of re-reading: the count (10, a sample of five names, understated 14×), the consumer
   (ComputationCorrectness reads `formula:` targets only — the real consumer is `last_modified.py`'s
   VERIFIES propagation), and the function name (`extract_test_verifies_edges` has never existed).
   "One-line fix" was also wrong — the two failure modes are independent and neither rule catches the
   other's cases. Full detail: ADR-009 §Deferred item 7.

**Correction to an earlier claim of mine:** I reported `atlas_hypothesis_discipline` as contradicting its own
"NEVER a gate" description. Reading it, the `passed=False` at `:3717` is in the **exception handler** — it
fails only when it cannot build the atlas, and passes unconditionally on content. That is the *correct*
pattern, not a defect. Withdrawn.

---

## 8. Reconnaissance — CLOSED 2026-08-03

The four read-only explorations landed and their load-bearing claims were verified directly. Outcomes:

- **Test coverage** — 16 TESTED / 6 PARTIAL / 37 UNTESTED, and **eleven of the sixteen assert only
  `result.passed`**, so a check rewritten to `return CheckResult(passed=True, details=[])` passes them.
  Exactly five would fail on a seeded defect. `--json` proved deterministic enough once `elapsed_seconds`
  is dropped, details are sorted and `PYTHONHASHSEED` is pinned — but **ten checks are structurally
  non-snapshottable and are quarantined** rather than forced (see `tests/validate_characterization.py`).
- **Artifact-generation stack** — confirmed: `build_graph_json()` runs ≈8 full extraction passes and ≈20
  parses of a 70 MB `lean_deps.json` per suite run, ~15 s per build. A shared graph handle is the obvious
  consequence and is deliberately **Phase 3**, because sharing changes what each check observes once the
  `*_fresh` checks regenerate artifacts mid-run. Same reasoning forbids memoizing `load_lean_deps()`
  (§7 item 0 / ADR-009 §Deferred item 0).
- **Agent/hook layer** — external callers enumerated (pre-commit hook, `gate_precheck.py`,
  `pre-commit-sync.sh`, the skills/plugins, the dashboard). All go through `python scripts/validate.py`,
  `import validate`, or the `--json` payload — which is why the migration contract in §3 pins exactly those
  three surfaces. **The Codex control plane was checked separately and has zero coupling to the validation
  suite** (verified across its 7 commits); parked in `tangential-items.md` T1 — do not re-derive it.

The plan is final in the sense that reconnaissance no longer gates it. It is **not** final in the sense of
being correct on first write: three pieces of Phase-0/2 scaffolding shipped defective and were caught by
re-reading and mutation, not by tests. See RESUME_STATE.md's standing lesson.
