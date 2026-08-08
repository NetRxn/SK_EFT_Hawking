"""ADR-009 Phase 0 — the registry contract that makes a package split safe.

WHY THIS FILE EXISTS
--------------------
`validate.py` is being split into `scripts/validate/` (ADR-009). Two properties
of the registry are load-bearing and, before this file, asserted by nothing:

1. **The check COUNT.** `run_checks` iterates `_CHECKS`; `main()` returns
   ``0 if all(r.passed ...)``. Python's ``all([])`` is ``True``, so a check that
   silently fails to register — a missed import in a future package
   ``__init__`` — makes the suite *quieter*, not louder. `validate.py:7732-7735`
   already guards this failure mode for ``--check`` (unknown name -> rc2) with
   an inline comment explaining exactly this reasoning; there was no equivalent
   guard for the full run.

2. **The registration ORDER.** Three checks (`counts_fresh`, `tables_fresh`,
   `claim_clusters_fresh`) shell out and REGENERATE artifacts that later checks
   read — `axiom_count_prose_consistency` and `inventory_index_autogen_fresh`
   both consume `docs/counts.json`. Order is therefore semantics, not cosmetics,
   and an import-order change during the split would alter what later checks
   observe while every existing test still passed.

Two prior tests assert *membership* of a single name
(`test_validate_toolchain_pin_drift.py`, `test_bundle_consistency.py`). Neither
asserts count or order.

MAINTENANCE
-----------
`EXPECTED_CHECKS` is a frozen ordered list, deliberately verbose rather than
computed: a test that derives its expectation from the thing under test asserts
nothing. Adding a check is a real event — append it here in its registration
position, in the same commit. If this test fails after an intentional change,
update the list and say why in the commit message.
"""
from __future__ import annotations

import subprocess
import sys
from pathlib import Path

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))

import validate as v  # noqa: E402


# Frozen 2026-08-03 against `validate.py --list`, in registration order.
EXPECTED_CHECKS = [
    'counts_fresh',
    'formulas', 'lean_zero_sorry', 'placeholder_not_cited', 'disclosure_consistency',
    'proxy_body_audit', 'tracked_hypothesis_ledger', 'tracked_hypotheses_fresh',
    'formula_grounding', 'vacuous_statement_audit', 'nogo_substrate_integrity',
    'native_decide_regression', 'numerical', 'identities',
    'paper_table', 'd1_hierarchy_table', 'f_hierarchy_claims',
    'theorems', 'notebooks', 'lean_source',
    'cgl_fdr', 'lean_modules_in_build_graph', 'lean_build', 'axiom_closure_allowlist',
    'elaboration_knob_watchlist', 'bundle_figure_integrity', 'viz_consistency',
    'notebook_exec', 'physical_bounds', 'cross_path_consistency',
    'paper_provenance', 'parameter_provenance',
    'tables_fresh', 'claim_clusters_fresh', 'numerical_literals', 'bundle_tables_use_pipeline',
    'graph_integrity', 'gate_edge_types_are_emitted', 'atlas_integrity',
    'atlas_hypothesis_discipline',
    'count_literals', 'recurrence_reopens_closures', 'review_severity_declared',
    'review_docs_mint_findings', 'accepted_findings_carry_rationale',
    'chain_backing_targets_resolve',
    'bundle_metadata_matches_graph', 'bundle_stage13_claim_consistent',
    'bundle_manuscript_length', 'notebook_stored_outputs_current',
    'readiness_verdicts_agree', 'readiness_submission_gate',
    'citation_primary_sources_present', 'provenance_doi_in_registry',
    'bundle_consistency', 'bundle_source_freshness',
    'bibitem_title_primary_source', 'quantum_network',
    'bundle_registry_consistency', 'bundle_apex_resolves', 'paper_latex_compiles',
    'axiom_count_prose_consistency', 'prose_theorem_reference_coverage',
    'theorem_name_embedded_citations', 'inventory_index_autogen_fresh',
    'architecture_inventory_fresh',
    'lean_docstring_refs_resolve', 'paper_toolchain_pin_drift',
]

# Checks that regenerate an on-disk artifact a LATER check reads. Their relative
# order against their consumers is the part of the ordering that is semantic
# rather than incidental.
_REGENERATORS = ('counts_fresh', 'tables_fresh', 'claim_clusters_fresh')
def _counts_consumers() -> set[str]:
    """Registered checks whose body reads `docs/counts.json`, DERIVED by AST.

    ⚠️ This was a hand-written tuple naming two checks. Measured 2026-08-07, the real
    population was larger, and THREE of the undeclared readers ran BEFORE the
    regenerator — including `lean_zero_sorry`, the Invariant #4 gate. The tuple was
    the failure mode `CHECK_AUTHORING_GUIDE.md` §6 lists as *"a hand-maintained list
    parallel to a registry"*, sitting inside the test that enforces ADR-009 hazard H3.

    Deriving it means a check that starts reading counts.json is covered on arrival,
    with no edit here. A body that reaches counts.json through a helper rather than
    naming it is still invisible — an accepted limit, and the reason the production
    comment in `_CANONICAL_ORDER` states the ordering intent in prose too.
    """
    import ast
    consumers: set[str] = set()
    checks_dir = SK_ROOT / "scripts" / "validation" / "checks"
    for path in sorted(checks_dir.glob("*.py")):
        src = path.read_text()
        for node in ast.walk(ast.parse(src)):
            if not isinstance(node, ast.FunctionDef):
                continue
            names = [d for d in node.decorator_list
                     if isinstance(d, ast.Call)
                     and getattr(d.func, "id", None) == "register_check"]
            if not names:
                continue
            body = ast.get_source_segment(src, node) or ""
            if "COUNTS_JSON_PATH" in body or "counts.json" in body:
                consumers.add(names[0].args[0].value)
    return consumers


class TestRegistryContract:
    def test_check_count_is_frozen(self):
        actual = [s.name for s in v._CHECKS]
        assert len(actual) == len(EXPECTED_CHECKS), (
            f"check count changed: {len(actual)} registered, "
            f"{len(EXPECTED_CHECKS)} expected.\n"
            f"  added:   {sorted(set(actual) - set(EXPECTED_CHECKS))}\n"
            f"  missing: {sorted(set(EXPECTED_CHECKS) - set(actual))}\n"
            "A DROPPED check does not fail the suite — `all([])` is True — so "
            "this assertion is the only thing that notices."
        )

    def test_registration_order_is_frozen(self):
        actual = [s.name for s in v._CHECKS]
        assert actual == EXPECTED_CHECKS, (
            "registration ORDER changed. This is semantic, not cosmetic: "
            f"{_REGENERATORS} regenerate artifacts that later checks read. "
            "First divergence at index "
            f"{next((i for i, (a, e) in enumerate(zip(actual, EXPECTED_CHECKS)) if a != e), 'n/a')}."
        )

    def test_regenerators_precede_their_consumers(self):
        """The ordering invariant stated as a property, so it survives a
        deliberate reordering that updates EXPECTED_CHECKS without noticing
        this consequence."""
        order = {s.name: i for i, s in enumerate(v._CHECKS)}
        consumers = _counts_consumers() - {'counts_fresh'}
        assert consumers, (
            "AST scan found no counts.json consumers — the scan has silently "
            "narrowed, and a scan that matches nothing passes vacuously.")
        for consumer in sorted(consumers):
            assert order['counts_fresh'] < order[consumer], (
                f"`counts_fresh` (idx {order['counts_fresh']}) must run before "
                f"`{consumer}` (idx {order[consumer]}), which reads the "
                "docs/counts.json it regenerates."
            )

    def test_every_check_has_a_description(self):
        for spec in v._CHECKS:
            assert spec.description and spec.description.strip(), spec.name

    def test_names_are_unique(self):
        names = [s.name for s in v._CHECKS]
        assert len(names) == len(set(names)), (
            "duplicate check name — `--check` resolves by name and would run "
            "only the first, silently disabling the second."
        )


class TestCanonicalOrderMechanism:
    """`_CANONICAL_ORDER` + `_apply_canonical_order()` are what decouple EXECUTION
    order from IMPORT order (ADR-009 H3), so the Phase-2 domain split can organise
    modules for reading. Both legs below exist because the mechanism shipped
    BROKEN on 2026-08-03 and every other test in this file stayed green:

    the call sat mid-file, so it sorted the 45 checks registered above it and left
    the 14 below appended in import order — and its `raise` for an undeclared check
    could not fire for anything registered below, including the end of the file,
    which is where a new check naturally goes. Nothing caught it because the tail
    was coincidentally already in canonical sequence.
    """

    def test_every_registered_check_has_a_declared_position(self):
        """The property `_apply_canonical_order`'s `raise` promises to enforce.

        Asserted here as well as in production because the raise is reachable only
        for checks registered before the call — so on its own it is evidence of
        nothing.
        """
        declared = set(v._CANONICAL_ORDER)
        undeclared = [s.name for s in v._CHECKS if s.name not in declared]
        assert not undeclared, (
            f"check(s) registered with no declared execution position: {undeclared}. "
            "Position is semantic (the *_fresh checks regenerate artifacts later "
            "checks read), so it must be chosen, not inherited from import order."
        )

    def test_the_sort_runs_after_the_last_registration(self):
        """Structural, and it has to be: while the tail is coincidentally in the
        right order, NO behavioural test can distinguish a sort that ran too early
        from one that ran at the right time. That coincidence is exactly the state
        this file was in when the defect shipped.

        AST-based, so the `@register_check` example in the module docstring and any
        mention in a comment are not counted — only real decorators.
        """
        import ast
        src = (SK_ROOT / "scripts" / "validate.py").read_text()
        tree = ast.parse(src)

        # Registration happens two ways, and the sort must follow BOTH:
        #   (a) `@register_check` decorators still in validate.py, and
        #   (b) `from validation.checks import <mod>` — importing a check module
        #       runs its decorators.
        # (a) shrinks to ZERO as Phase 2 completes, at which point (b) is the
        # whole story. Keying only on (a) — which this test did until 2026-08-03 —
        # would have made it assert nothing on an empty max(), and it would have
        # missed an import placed *below* the sort, which is the live hazard now
        # that check modules exist.
        in_file = [
            node.lineno for node in ast.walk(tree)
            if isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef))
            for d in node.decorator_list
            if isinstance(d, ast.Call) and getattr(d.func, "id", "") == "register_check"
        ]
        module_imports = [
            node.lineno for node in ast.walk(tree)
            if isinstance(node, ast.ImportFrom)
            and (node.module or "").startswith("validation.checks")
        ]
        registrations = in_file + module_imports
        assert registrations, (
            "found neither an in-file @register_check nor a `from validation.checks "
            "import ...` — nothing registers, so this test would assert nothing."
        )
        last_registration = max(registrations)

        call_lines = [
            node.lineno for node in tree.body
            if isinstance(node, ast.Expr) and isinstance(node.value, ast.Call)
            and getattr(node.value.func, "id", "") == "_apply_canonical_order"
        ]
        assert len(call_lines) == 1, (
            f"expected exactly one module-level `_apply_canonical_order()` call, "
            f"found {len(call_lines)} at lines {call_lines}. Two calls would make "
            f"the first one dead and hide which registrations it covered."
        )
        assert call_lines[0] > last_registration, (
            f"`_apply_canonical_order()` is called at line {call_lines[0]} but the "
            f"last `@register_check` is at line {last_registration}. Every check "
            f"registered after the call is appended UNSORTED, and the call's "
            f"`raise` cannot fire for any of them — so both halves of the ordering "
            f"mechanism are silently inert for the tail of the file."
        )


class TestListOutputMatchesRegistry:
    """`--list` is a contract surface: `ADR-009` requires it byte-identical
    across the migration, and other tooling reads it."""

    def test_list_names_match_registry_in_order(self):
        r = subprocess.run(
            [sys.executable, "scripts/validate.py", "--list"],
            cwd=SK_ROOT, capture_output=True, text=True,
        )
        assert r.returncode == 0, r.stderr
        listed = [
            ln.strip().split()[0]
            for ln in r.stdout.splitlines()
            if ln.startswith("  ") and ln.strip()
        ]
        assert listed == EXPECTED_CHECKS, (
            "`--list` disagrees with the frozen registry order."
        )
