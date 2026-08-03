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
checks simply take their non-strict branch. The three caches are correctness-relevant too: they are shared
across checks within a run, and duplicating them per-module changes cost, not behaviour — but only if the
split is done by reference, not by value.

**Constraint:** runtime flags move into a single explicit config object passed to checks, or stay in one
module accessed by attribute (`cfg.STRICT_MODE`), never imported by value.

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

```
scripts/validate.py              # thin shim: `from validate import main; sys.exit(main())`
                                 #   — keeps `python scripts/validate.py` and every doc/hook invocation working
scripts/validate/
  __init__.py                    # public surface: main, run_checks, register_check, CheckResult, Detail,
                                 #   BUNDLE_CODES (H2). Imports checks/* for registration side-effect,
                                 #   in an EXPLICIT ordered list (H3).
  _paths.py                      # THE path anchor. PROJECT_ROOT resolved once, explicitly (H1).
  _config.py                     # STRICT_MODE / FORCE_LATEX / FORCE_NOTEBOOK_REEXEC as one object (H5)
  _result.py                     # Detail, CheckResult, CheckSpec, registry, run_checks
  _report.py                     # print_results, archive_results, --json payload
  helpers/
    lean_deps.py                 # load_lean_deps(on_missing=...) + the three source caches (H4, H5)
    papers.py                    # bundle_drafts() / all_paper_drafts() — two names, never a flag (H4)
    counts.py                    # load_counts()
    tex.py                       # _strip_tex_comments, _line_of, shared regexes
  checks/
    lean_substrate.py            # formulas, placeholder_not_cited, disclosure_consistency, proxy_body_audit,
                                 #   tracked_hypothesis_*, formula_grounding, vacuous_statement_audit,
                                 #   nogo_substrate_integrity, native_decide_regression, lean_source, lean_build,
                                 #   axiom_closure_allowlist, elaboration_knob_watchlist, lean_docstring_refs_resolve
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
6. **`--strict` is passed by nothing automated** — not the commit hook, not `gate_precheck.py`. Two gates
   (`axiom_closure_allowlist`, `bundle_source_freshness`) are therefore unreachable in practice.

**Correction to an earlier claim of mine:** I reported `atlas_hypothesis_discipline` as contradicting its own
"NEVER a gate" description. Reading it, the `passed=False` at `:3717` is in the **exception handler** — it
fails only when it cannot build the atlas, and passes unconditionally on content. That is the *correct*
pattern, not a defect. Withdrawn.

---

## 8. Open — pending reconnaissance

Four read-only explorations are in flight (artifact-generation stack; readiness/bundle stack; agent/hook/
register layer; test coverage). Three answers could change this plan:

- **Test coverage** — which of the 59 could break silently under a mechanical move, and whether
  `--json` is deterministic enough for Phase 0.
- **Artifact-generation stack** — whether `build_graph_json()` is invoked multiple times per run (several
  checks call it; if uncached, that is a large duplicated cost and a possible consistency hazard when
  artifacts are regenerated mid-run by the `*_fresh` checks).
- **Agent/hook layer** — every external caller of `validate.py` that must keep working (hooks,
  `gate_precheck`, skills, the dashboard).

This plan is not final until those land and I have verified their load-bearing claims myself.
