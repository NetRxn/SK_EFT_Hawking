"""Lean VERIFIES edges require an eligible reference to the exact target.

Formula/Parameter selection precedes alias exclusion; only allowed undotted names
use short lookup. Deduplicated edges need existential genuine support. ADR-009
item 7 owns the rule; the exact-alias finding owns incident measurements.
"""
from __future__ import annotations

import ast
import copy
import hashlib
import inspect
import json
import subprocess
from collections import Counter
from contextlib import contextmanager
from dataclasses import asdict
import sys
from pathlib import Path

import pytest

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT))
sys.path.insert(0, str(SK_ROOT / "scripts"))

import build_graph as bg  # noqa: E402


# ── synthetic harness ────────────────────────────────────────────────────────

def _test_node(module: str, name: str, refs: list[str], kind: str = "golden") -> dict:
    return {
        "id": f"test:{module}::{name}", "type": "PythonTest", "label": name,
        "name": name, "verification": "verified", "detail": "",
        "meta": {"module": module, "file": f"tests/{module}.py", "line": 1,
                 "test_kind": kind, "referenced_names": refs},
    }


def _formula_node(name: str) -> dict:
    return {"id": f"formula:{name}", "type": "Formula", "label": name, "name": name,
            "verification": "verified", "detail": "", "meta": {}}


def _param_node(name: str) -> dict:
    return {"id": f"param:{name}", "type": "Parameter", "label": name, "name": name,
            "verification": "verified", "detail": "", "meta": {}}


def _run(monkeypatch, *, tests, lean_full=(), formulas=(), params=(), aliases=None):
    """Drive the REAL extract_verifies_edges against a stub graph."""
    lean_nodes = [{"id": f"lean:{fn}", "name": fn.rsplit(".", 1)[-1]} for fn in lean_full]
    f_nodes = [_formula_node(n) for n in formulas]
    p_nodes = [_param_node(n) for n in params]

    monkeypatch.setattr(bg, "extract_python_test_nodes", lambda: list(tests))
    monkeypatch.setattr(bg, "extract_formula_nodes", lambda: f_nodes)
    monkeypatch.setattr(bg, "extract_parameter_nodes", lambda: p_nodes)

    short_index: dict[str, list[str]] = {}
    for fn in lean_full:
        short_index.setdefault(fn.rsplit(".", 1)[-1], []).append(f"lean:{fn}")
    monkeypatch.setattr(bg, "_LEAN_SHORT_INDEX", short_index)
    monkeypatch.setattr(bg, "_TEST_MODULE_ALIASES", dict(aliases or {}))

    node_ids = {n["id"] for n in tests} | {n["id"] for n in lean_nodes} \
        | {n["id"] for n in f_nodes} | {n["id"] for n in p_nodes}
    return bg.extract_verifies_edges(node_ids)


# ── the module-alias half ────────────────────────────────────────────────────

class TestModuleAliasExtraction:
    """`import X` binds a module; `from M import a` binds a symbol. The VERIFIES
    resolver has to tell them apart, so the extractor must not conflate them."""

    def test_import_forms_are_recorded(self):
        tree = ast.parse("import numpy as np\nimport time\nimport mlx.core as mx\n")
        assert bg._extract_module_aliases(tree) == {"np", "time", "mx"}

    def test_from_imports_are_NOT_recorded(self):
        """THE LOAD-BEARING HALF. `from src.core import formulas as F` and
        `from src.adw import critical_coupling` must stay resolvable — they are
        the project's Python<->Lean naming correspondence, not library aliases."""
        tree = ast.parse(
            "from src.core import formulas as F\n"
            "from src.adw.gap_equation import critical_coupling\n"
        )
        assert bg._extract_module_aliases(tree) == set()

    def test_a_dotted_import_records_only_its_root(self):
        assert bg._extract_module_aliases(ast.parse("import a.b.c\n")) == {"a"}

    def test_function_scoped_imports_count_too(self):
        """`import validation.checks.bundles_readiness as m` inside a test body
        is how `m` reached the resolver on the live tree."""
        tree = ast.parse("def f():\n    import validation.checks.x as m\n")
        assert bg._extract_module_aliases(tree) == {"m"}

    def test_the_real_extractor_populates_the_index(self):
        """Guards the seam: the synthetic legs above stub `_TEST_MODULE_ALIASES`,
        so without this they would all still pass if the production extractor
        stopped filling it in."""
        bg._TEST_MODULE_ALIASES.clear()
        bg.extract_python_test_nodes()
        assert bg._TEST_MODULE_ALIASES, "extract_python_test_nodes filled nothing in"
        mine = bg._TEST_MODULE_ALIASES.get("test_validate_public_surface", set())
        assert "v" in mine, (
            "`import validate as v` must be recognised as a module alias")


class TestModuleAliasRefsDoNotResolve:
    LEAN = ("SKEFTHawking.Curvature.kron",
            "SKEFTHawking.ScalarRungInterpretation.EWMassMatrixInputs.v")

    def test_a_dotted_library_call_manufactures_no_edge(self, monkeypatch):
        """FIRES ON THE SEEDED DEFECT — remove the guard and `np.kron` resolves
        to `Curvature.kron` again."""
        edges = _run(monkeypatch,
                     tests=[_test_node("test_gauge", "test_kramers", ["np.kron", "np"])],
                     lean_full=self.LEAN, aliases={"test_gauge": {"np"}})
        assert edges == [], (
            f"`np.kron` produced {edges} — the Lean branch is tail-resolving a "
            f"NumPy attribute access again (ADR-009 §Deferred item 7)")

    def test_a_bare_module_alias_manufactures_no_edge(self, monkeypatch):
        """An undotted module alias is excluded as well as an attribute access."""
        edges = _run(monkeypatch,
                     tests=[_test_node("test_d1_hierarchy_table", "test_x", ["v"])],
                     lean_full=self.LEAN,
                     aliases={"test_d1_hierarchy_table": {"v"}})
        assert edges == [], f"bare module alias `v` produced {edges}"

    def test_the_same_name_resolves_when_it_is_NOT_a_module_alias(self, monkeypatch):
        """SILENT ON CORRECT DATA, and the sharpest control in the file: the ref
        is identical, only its origin differs. A test that imported a project
        symbol named `v` should still get its edge."""
        edges = _run(monkeypatch,
                     tests=[_test_node("test_scalar_rung", "test_x", ["v"])],
                     lean_full=self.LEAN, aliases={"test_scalar_rung": set()})
        assert [e["target"] for e in edges] == [
            "lean:SKEFTHawking.ScalarRungInterpretation.EWMassMatrixInputs.v"]


class TestDottedRefsDoNotTailResolve:
    LEAN = ("SKEFTHawking.NeutrinoMixing.get",
            "SKEFTHawking.DarkSectorSynthesis.DarkSectorCandidate.basic_viability")

    def test_an_attribute_on_a_project_constant_does_not_tail_resolve(self, monkeypatch):
        """`PARAMETER_PROVENANCE` is a from-imported project symbol, so the
        module-alias rule does not catch it — but `.get` is a dict access, and
        five different `CANDIDATE_*.basic_viability` refs all collapsed onto one
        Lean field. Tail-matching is not reference resolution."""
        edges = _run(monkeypatch,
                     tests=[_test_node("test_p", "test_x",
                                       ["PARAMETER_PROVENANCE.get",
                                        "CANDIDATE_T0.basic_viability"])],
                     lean_full=self.LEAN, aliases={"test_p": set()})
        assert edges == [], f"a dotted ref tail-resolved to Lean: {edges}"

    def test_a_full_lean_name_still_resolves(self, monkeypatch):
        """SILENT ON CORRECT DATA. The dotted rule refuses TAIL resolution, not
        dotted names as such — a genuine `SKEFTHawking.Foo.bar` reference is
        still an edge."""
        edges = _run(monkeypatch,
                     tests=[_test_node("test_p", "test_x",
                                       ["SKEFTHawking.NeutrinoMixing.get"])],
                     lean_full=self.LEAN, aliases={"test_p": set()})
        assert [e["target"] for e in edges] == ["lean:SKEFTHawking.NeutrinoMixing.get"]


class TestLegitimateCoverageSurvives:
    def test_a_from_imported_project_symbol_resolves(self, monkeypatch):
        """A Python symbol may mirror its Lean formalization's short name."""
        edges = _run(monkeypatch,
                     tests=[_test_node("test_adw", "test_c", ["critical_coupling"])],
                     lean_full=("SKEFTHawking.ADWMechanism.critical_coupling",),
                     aliases={"test_adw": {"pytest"}})
        assert [(e["target"], e["test_kind"]) for e in edges] == [
            ("lean:SKEFTHawking.ADWMechanism.critical_coupling", "golden")]

    def test_ambiguous_short_names_are_still_skipped(self, monkeypatch):
        """The pre-existing ambiguity rule is untouched by the guard."""
        edges = _run(monkeypatch,
                     tests=[_test_node("test_x", "test_y", ["gs_conditions"])],
                     lean_full=("SKEFTHawking.ChiralityWall.gs_conditions",
                                "SKEFTHawking.ChiralityWallStatus.gs_conditions"),
                     aliases={"test_x": set()})
        assert edges == []


class TestFormulaAndParamBranchesAreUntouched:
    """Formula and Parameter priority is upstream of the Lean alias guard."""

    def test_a_module_alias_still_reaches_a_formula(self, monkeypatch):
        """`F.hawking_temperature` comes from `from src.core import formulas as
        F` — a from-import, so it is not a module alias and the formula branch's
        own allow-list keeps working. But even a true module alias must still
        reach the formula index, because the guard is downstream of it."""
        edges = _run(monkeypatch,
                     tests=[_test_node("test_f", "test_x", ["F.hawking_temperature"])],
                     formulas=("hawking_temperature",),
                     aliases={"test_f": {"F"}})
        assert [e["target"] for e in edges] == ["formula:hawking_temperature"]

    def test_a_module_alias_still_reaches_a_parameter(self, monkeypatch):
        edges = _run(monkeypatch,
                     tests=[_test_node("test_p", "test_x", ["omega_perp"])],
                     params=("Steinhauer.omega_perp",),
                     aliases={"test_p": {"omega_perp"}})
        assert [e["target"] for e in edges] == ["param:Steinhauer.omega_perp"]

    def test_formula_wins_over_a_same_named_lean_declaration(self, monkeypatch):
        edges = _run(monkeypatch,
                     tests=[_test_node("test_f", "test_x", ["critical_coupling"])],
                     formulas=("critical_coupling",),
                     lean_full=("SKEFTHawking.ADWMechanism.critical_coupling",),
                     aliases={"test_f": set()})
        assert [e["target"] for e in edges] == ["formula:critical_coupling"]


@pytest.mark.slow
class TestLiveGraphHasNoFabricatedEdges:
    """Every deduplicated Lean edge requires at least one valid supporting ref.

    Module alias references cannot support it; a separate eligible ref may.
    """

    def test_no_lean_edge_is_alias_rooted_or_tail_resolved(self):
        nodes = (bg.extract_parameter_nodes() + bg.extract_formula_nodes()
                 + bg.extract_lean_declaration_nodes() + bg.extract_python_test_nodes())
        node_ids = {n["id"] for n in nodes}
        edges = bg.extract_verifies_edges(node_ids)
        _assert_supported_edges(edges, nodes, bg._TEST_MODULE_ALIASES, bg._LEAN_SHORT_INDEX)


class TestExactAliasRegression:
    @pytest.mark.parametrize("raw", ["pi", "bad.foo"])
    def test_exact_alias_is_rejected(self, monkeypatch, raw):
        edges = _run(monkeypatch,
                     tests=[_test_node("test_exact", "test_x", [raw])],
                     lean_full=(raw,), aliases={"test_exact": {raw.split(".")[0]}})
        assert edges == [], f"exact module alias manufactured edge: {edges}"

    def test_mixed_genuine_reference_supports_deduplicated_edge(self, monkeypatch):
        test = _test_node("test_mixed", "test_x", ["bad.foo", "foo"])
        lean = {"id": "lean:Good.foo", "name": "foo", "type": "LeanTheorem"}
        monkeypatch.setattr(bg, "extract_python_test_nodes", lambda: [test])
        monkeypatch.setattr(bg, "extract_parameter_nodes", lambda: [])
        monkeypatch.setattr(bg, "extract_formula_nodes", lambda: [])
        monkeypatch.setattr(bg, "extract_lean_declaration_nodes", lambda: [lean])
        monkeypatch.setattr(bg, "_TEST_MODULE_ALIASES", {"test_mixed": {"bad"}})
        monkeypatch.setattr(bg, "_LEAN_SHORT_INDEX", {"foo": [lean["id"]]})
        TestLiveGraphHasNoFabricatedEdges().test_no_lean_edge_is_alias_rooted_or_tail_resolved()


def _support_context(nodes, graph_ids=None):
    ids = {n['id'] for n in nodes} if graph_ids is None else graph_ids
    formula = {n['name']: n['id'] for n in nodes if n.get('type') == 'Formula'}
    parameter = {}
    for n in nodes:
        if n.get('type') == 'Parameter':
            parameter[n['name']] = n['id']
            parameter.setdefault(n['name'].rsplit('.', 1)[-1], n['id'])
    return ids, formula, parameter


def _reference_evidence(raw, aliases, nodes, short_index, *, graph_ids=None, context=None):
    """Independent support predicate: selected earlier indexes block Lean support.

    This test-local evidence never calls the production resolver or short helper.
    Ordered dictionaries below model index selection, including absent targets.
    """
    ids, formula, parameter = context or _support_context(nodes, graph_ids)
    selected = formula.get(raw)
    if selected is None and '.' in raw:
        prefix, tail = raw.rsplit('.', 1)
        if prefix in {'F', 'formulas', 'src.core.formulas'}:
            selected = formula.get(tail)
    branch = 'formula'
    if selected is None:
        selected = parameter.get(raw)
        branch = 'parameter'
    root_alias = raw.split('.', 1)[0] in aliases
    candidates = [c for c in short_index.get(raw, []) if c in ids]
    if selected is not None:
        reason = branch if selected in ids else f'{branch}-selected-missing'
        support = None
    elif root_alias:
        reason, support = 'module-alias', None
    elif f'lean:{raw}' in ids:
        reason, support = 'exact', f'lean:{raw}'
    elif '.' in raw:
        reason, support = 'dotted-without-exact', None
    elif len(candidates) == 1:
        reason, support = 'unique-in-graph-short', candidates[0]
    else:
        reason = 'ambiguous-short' if candidates else 'missing-short'
        support = None
    return dict(raw=raw, selected_earlier=selected, root_alias=root_alias,
                dotted='.' in raw, exact_in_graph=f'lean:{raw}' in ids,
                in_graph_short_sequence=candidates, reason=reason, support=support)


def _unsupported_edges(edges, nodes, aliases, short_index, *, graph_ids=None):
    """An emitted Lean edge is valid iff one eligible raw ref supports its target."""
    tests = {n['id']: n for n in nodes if n.get('type') == 'PythonTest'}
    offenders = []
    context = _support_context(nodes, graph_ids)
    for edge in edges:
        if not edge['target'].startswith('lean:'):
            continue
        test = tests[edge['source']]
        refs = test['meta']['referenced_names']
        evidence = [_reference_evidence(raw, aliases.get(test['meta']['module'], set()),
                                      nodes, short_index, context=context) for raw in refs]
        if not any(row['support'] == edge['target'] for row in evidence):
            offenders.append(dict(edge=copy.deepcopy(edge), references=evidence))
    return offenders



def _assert_supported_edges(edges, nodes, aliases, short_index):
    offenders = _unsupported_edges(edges, nodes, aliases, short_index)
    assert not offenders, f"unsupported Lean VERIFIES edges: {offenders[:10]}"


@pytest.mark.parametrize('case,raw,aliases,formula_names,param_names,lean_names,index,excluded,want', [
    ('formula-bare', 'foo', set(), ['foo'], [], ['A.foo'], {'foo': ['lean:A.foo']}, set(), None),
    ('formula-qualified', 'F.foo', set(), ['foo'], [], ['F.foo'], {}, set(), None),
    ('parameter', 'foo', set(), [], ['A.foo'], ['B.foo'], {'foo': ['lean:B.foo']}, set(), None),
    ('missing-formula', 'foo', set(), ['foo'], [], ['A.foo'], {'foo': ['lean:A.foo']}, {'formula:foo'}, None),
    ('missing-param', 'foo', set(), [], ['P.foo'], ['A.foo'], {'foo': ['lean:A.foo']}, {'param:P.foo'}, None),
    ('filtered-ambiguity', 'foo', set(), [], [], ['A.foo'], {'foo': ['lean:A.foo', 'lean:B.foo']}, set(), 'lean:A.foo'),
    ('exact-before-ambiguity', 'foo', set(), [], [], ['foo', 'A.foo'], {'foo': ['lean:foo', 'lean:A.foo']}, set(), 'lean:foo'),
    ('duplicate-sequence', 'foo', set(), [], [], ['A.foo'], {'foo': ['lean:A.foo', 'lean:A.foo']}, set(), None),
    ('qualified-exact', 'Good.foo', set(), [], [], ['Good.foo'], {}, set(), 'lean:Good.foo'),
    ('dotted-tail', 'bad.foo', set(), [], [], ['Good.foo'], {'foo': ['lean:Good.foo']}, set(), None),
    ('exact-bare-alias', 'foo', {'foo'}, [], [], ['foo'], {}, set(), None),
    ('exact-root-alias', 'bad.foo', {'bad'}, [], [], ['bad.foo'], {}, set(), None),
    ('param-order', 'foo', set(), [], ['P.foo', 'Q.foo'], ['A.foo'], {}, set(), None),
])
def test_independent_support_priority_table(case, raw, aliases, formula_names,
                                            param_names, lean_names, index,
                                            excluded, want):
    nodes = ([_formula_node(n) for n in formula_names]
             + [_param_node(n) for n in param_names]
             + [dict(id=f'lean:{n}', name=n.rsplit('.', 1)[-1], type='LeanDef')
                for n in lean_names])
    ids = {n['id'] for n in nodes} - excluded
    assert _reference_evidence(raw, aliases, nodes, index, graph_ids=ids)['support'] == want, case


@pytest.mark.parametrize('earlier', ['formula', 'parameter', 'missing-formula', 'missing-parameter'])
def test_invalid_alias_cannot_be_laundered_by_earlier_index(earlier):
    test = _test_node('test_bad', 'test_x', ['bad.foo', 'foo'])
    earlier_node = (_formula_node('foo') if 'formula' in earlier else _param_node('foo'))
    nodes = [test, earlier_node, dict(id='lean:bad.foo', type='LeanDef', name='foo')]
    ids = {n['id'] for n in nodes}
    if earlier.startswith('missing'):
        ids.remove(earlier_node['id'])
    edge = dict(source=test['id'], target='lean:bad.foo', type='VERIFIES', test_kind='golden')
    assert _unsupported_edges([edge], nodes, {'test_bad': {'bad'}},
                              {'foo': ['lean:bad.foo']}, graph_ids=ids) == [
        dict(edge=edge, references=[_reference_evidence(raw, {'bad'}, nodes,
             {'foo': ['lean:bad.foo']}, graph_ids=ids) for raw in ['bad.foo', 'foo']])]


def test_support_requires_target_identity_and_accepts_mixed_genuine_support():
    test = _test_node('test_mixed', 'test_x', ['bad.foo', 'Good.foo'])
    nodes = [test] + [dict(id=f'lean:{n}', name='foo', type='LeanDef')
                      for n in ['Good.foo', 'Wrong.foo']]
    edges = [dict(source=test['id'], target=f'lean:{n}', type='VERIFIES', test_kind='golden')
             for n in ['Good.foo', 'Wrong.foo']]
    offenders = _unsupported_edges(edges, nodes, {'test_mixed': {'bad'}}, {})
    assert [o['edge']['target'] for o in offenders] == ['lean:Wrong.foo']
    test['meta']['referenced_names'] = ['bad.foo', 'absent.foo']
    assert len(_unsupported_edges(edges, nodes, {'test_mixed': {'bad'}}, {})) == 2


def test_real_from_import_classification_and_exact_precedence(monkeypatch):
    tree = ast.parse('from json import loads as pi\ndef test_x():\n    assert pi("{}") == {}\n')
    _, refs = bg._classify_test_function(tree.body[1], bg._extract_imports(tree))
    aliases = bg._extract_module_aliases(tree)
    assert refs == ['pi'] and aliases == set()
    edges = _run(monkeypatch, tests=[_test_node('test_from', 'test_x', refs)],
                 lean_full=('pi', 'Other.pi'), aliases={'test_from': aliases})
    assert [e['target'] for e in edges] == ['lean:pi']


@pytest.fixture(scope='session')
def _frozen_catalogue():
    from scripts import extract_lean_deps as ld
    raw = ld.JSON_PATH.read_bytes()
    pins = dict(canonical_sha256=hashlib.sha256(raw).hexdigest(),
                source_hash=ld.compute_lean_hash(),
                stored_hash=ld.HASH_PATH.read_text().strip(),
                metadata_sha256={str(p.relative_to(SK_ROOT)): hashlib.sha256(p.read_bytes()).hexdigest()
                    for p in [SK_ROOT / x for x in ['lean/lean_deps.json', 'lean/lean_deps.json.hash',
                        'lean/atlas_view.json', 'docs/counts.json', 'docs/counts.tex', 'docs/ATLAS_HEATMAP.md']]})
    assert pins['source_hash'] == pins['stored_hash'] and not ld._needs_refresh()
    # Read-only injection at the actual production loader boundary, not cache validation.
    return pins, json.loads(raw)


def _check_catalogue_pins(pins):
    from scripts import extract_lean_deps as ld
    assert hashlib.sha256(ld.JSON_PATH.read_bytes()).hexdigest() == pins['canonical_sha256']
    assert ld.compute_lean_hash() == ld.HASH_PATH.read_text().strip() == pins['source_hash']
    assert not ld._needs_refresh(), 'refuse extraction fallback'
    for name, digest in pins['metadata_sha256'].items():
        assert hashlib.sha256((SK_ROOT / name).read_bytes()).hexdigest() == digest, name
    return dict(pins, needs_refresh=False)


@pytest.fixture(autouse=True)
def _read_only_catalogue_and_restored_state(monkeypatch, _frozen_catalogue, request, tmp_path):
    from scripts import extract_lean_deps as ld
    pins, catalogue = _frozen_catalogue
    originals = {name: getattr(bg, name) for name in ['_TEST_MODULE_ALIASES',
        '_LEAN_SHORT_INDEX', '_LEAN_AMBIGUITY_SEEN', 'extract_verifies_edges']}
    before = _runtime_state_record()
    _check_catalogue_pins(pins)
    def frozen_load():
        _check_catalogue_pins(pins)
        return copy.deepcopy(catalogue)
    def refuse_extraction():
        pytest.fail('Lean extraction/build is forbidden in this focused guard')
    monkeypatch.setattr(ld, 'load_lean_deps', frozen_load)
    monkeypatch.setattr(ld, '_run_extraction', refuse_extraction)
    # The original objects and memo presence are restored even when a test raises.
    monkeypatch.setattr(bg, '_TEST_MODULE_ALIASES', copy.deepcopy(bg._TEST_MODULE_ALIASES))
    monkeypatch.setattr(bg, '_LEAN_SHORT_INDEX', copy.deepcopy(bg._LEAN_SHORT_INDEX))
    monkeypatch.setattr(bg, '_LEAN_AMBIGUITY_SEEN', set(bg._LEAN_AMBIGUITY_SEEN))
    sentinel = object()
    old_memo = getattr(bg._BUILD_MEMO_TLS, 'memo', sentinel)
    bg._BUILD_MEMO_TLS.memo = None
    try:
        yield
    finally:
        if old_memo is sentinel:
            del bg._BUILD_MEMO_TLS.memo
        else:
            bg._BUILD_MEMO_TLS.memo = old_memo
        monkeypatch.undo()
        assert all(getattr(bg, k) is v for k, v in originals.items())
        assert _runtime_state_record() == before
        _check_catalogue_pins(pins)
        if request.node.name.split('[', 1)[0] == 'test_frozen_corpus_production_seed_mutant_and_consumers':
            _write_record(tmp_path, 'teardown-restoration.json', dict(
                before=before, after=_runtime_state_record(),
                source_comparison_mode=request.node.callspec.params['source_comparison_mode'],
                object_identity_restored=True,
                memo_presence_and_identity_restored=True,
                canonical_pins=_check_catalogue_pins(pins)))


def _runtime_state_record():
    return dict(aliases={k: sorted(v) for k, v in bg._TEST_MODULE_ALIASES.items()},
                short_index=copy.deepcopy(bg._LEAN_SHORT_INDEX),
                ambiguity=sorted(bg._LEAN_AMBIGUITY_SEEN),
                memo_present=hasattr(bg._BUILD_MEMO_TLS, 'memo'),
                memo_id=id(getattr(bg._BUILD_MEMO_TLS, 'memo', None)),
                resolver_id=id(bg.extract_verifies_edges))


def _write_record(tmp_path, name, value):
    path = tmp_path / name
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + '\n')
    digest = hashlib.sha256(path.read_bytes()).hexdigest()
    print(f'VERIFIES_EVIDENCE {path} sha256={digest}')
    return dict(path=str(path), sha256=digest)


def _digest(value):
    return hashlib.sha256(json.dumps(value, sort_keys=True).encode()).hexdigest()


def _python_inputs():
    # Every Python source read by these producers, plus their implementation roster.
    paths = sorted({p for home in ['tests', 'src', 'scripts']
                    for p in (SK_ROOT / home).rglob('*.py')})
    return {str(p.relative_to(SK_ROOT)): p.read_text() for p in paths}


def _actual_inputs(pins):
    _check_catalogue_pins(pins)
    assert bg.PROJECT_ROOT.resolve() == SK_ROOT.resolve()
    bg._BUILD_MEMO_TLS.memo = None
    bg._LEAN_AMBIGUITY_SEEN = set()
    python_before = _python_inputs()
    lean = bg.extract_lean_declaration_nodes()
    tests = bg.extract_python_test_nodes()
    formula = bg.extract_formula_nodes()
    parameter = bg.extract_parameter_nodes()
    papers = bg.extract_paper_nodes()
    claims = bg.extract_paper_claim_nodes()
    readiness_ids = {n['id'] for n in formula + papers + claims}
    readiness_links = bg.extract_claims_edges(readiness_ids) + bg.extract_grounded_in_edges(readiness_ids)
    paper_bytes = {str(p.relative_to(SK_ROOT)): p.read_text()
                   for p in bg.discover_paper_draft_paths(SK_ROOT / 'papers')}
    assert _python_inputs() == python_before
    state = dict(python_bytes=python_before, tests=tests, formulas=formula,
                 parameters=parameter, lean_ids=[n['id'] for n in lean],
                 short_index=copy.deepcopy(bg._LEAN_SHORT_INDEX),
                 aliases={k: sorted(v) for k, v in bg._TEST_MODULE_ALIASES.items()},
                 ambiguity=sorted(bg._LEAN_AMBIGUITY_SEEN), papers=papers,
                 paper_claims=claims, readiness_links=readiness_links, paper_bytes=paper_bytes,
                 catalogue_pins=_check_catalogue_pins(pins),
                 runtime=dict(python=sys.version, executable=sys.executable,
                              producer_module=bg.__file__,
                              project_root=str(bg.PROJECT_ROOT.resolve()),
                              uv_lock_sha256=hashlib.sha256((SK_ROOT / 'uv.lock').read_bytes()).hexdigest(),
                              pyproject_sha256=hashlib.sha256((SK_ROOT / 'pyproject.toml').read_bytes()).hexdigest()))
    return state, lean


def _actual_edges(state, pins):
    _check_catalogue_pins(pins)
    assert _python_inputs() == state['python_bytes']
    nodes = state['parameters'] + state['formulas'] + state['tests']
    ids = {n['id'] for n in nodes} | set(state['lean_ids'])
    # Frozen memo replay uses actual production-produced values and actual resolver.
    # It prevents the resolver's redundant producer calls from changing its inputs.
    bg._BUILD_MEMO_TLS.memo = dict(extract_python_test_nodes=copy.deepcopy(state['tests']),
                                  extract_formula_nodes=copy.deepcopy(state['formulas']),
                                  extract_parameter_nodes=copy.deepcopy(state['parameters']))
    bg._TEST_MODULE_ALIASES = {k: set(v) for k, v in state['aliases'].items()}
    bg._LEAN_SHORT_INDEX = copy.deepcopy(state['short_index'])
    bg._LEAN_AMBIGUITY_SEEN = set(state['ambiguity'])
    before = dict(memo=_digest(bg._BUILD_MEMO_TLS.memo), aliases=_digest(state['aliases']),
                  short_index=_digest(bg._LEAN_SHORT_INDEX), ambiguity=sorted(bg._LEAN_AMBIGUITY_SEEN))
    try:
        edges = bg.extract_verifies_edges(ids)
        after = dict(memo=_digest(bg._BUILD_MEMO_TLS.memo), aliases=_digest(
            {k: sorted(v) for k, v in bg._TEST_MODULE_ALIASES.items()}),
            short_index=_digest(bg._LEAN_SHORT_INDEX), ambiguity=sorted(bg._LEAN_AMBIGUITY_SEEN))
        assert before['memo'] == after['memo'] and before['short_index'] == after['short_index']
        return edges, dict(before=before, after=after)
    finally:
        bg._BUILD_MEMO_TLS.memo = None


@contextmanager
def _production_order_mutant(state, pins, tmp_path):
    """Journal and execute the actual production function with only ordering regressed."""
    import seed_journal as sj
    path = SK_ROOT / 'scripts/build_graph.py'
    assert bg.PROJECT_ROOT.resolve() == sj.PROJECT_ROOT.resolve() == SK_ROOT.resolve()
    assert sj.JOURNAL_DIR.resolve().parent == SK_ROOT.resolve()
    assert path.resolve().is_relative_to(SK_ROOT.resolve())
    function = bg.extract_verifies_edges
    original = inspect.getsource(function)
    removed = "                if raw.split('.', 1)[0] in module_aliases:\n                    continue\n"
    assert original.count(removed) == 1
    mutant = original.replace(removed, '').replace(
        "elif '.' not in raw:\n", "elif '.' not in raw and raw.split('.', 1)[0] not in module_aliases:\n")
    source = path.read_text()
    assert source.count(original) == 1
    journal_before = sj.outstanding(include_live=True)
    _check_catalogue_pins(pins)
    try:
        with sj.seeded_mutation(path, source.replace(original, mutant),
                                reason='exact-first production function ordering mutant'):
            exec(compile(mutant, str(path), 'exec'), bg.__dict__)
            record = dict(path=str(path), original_function=original, mutant_function=mutant,
                          original_file_sha256=hashlib.sha256(source.encode()).hexdigest(),
                          mutant_file_sha256=hashlib.sha256(path.read_bytes()).hexdigest(),
                          journal_during=sj.outstanding(include_live=True),
                          changed_span='alias exclusion moved after exact membership')
            # The source roster differs only by this declared production function mutation.
            mutant_state = copy.deepcopy(state)
            mutant_state['python_bytes']['scripts/build_graph.py'] = path.read_text()
            yield mutant_state, record
    finally:
        bg.extract_verifies_edges = function
        assert path.read_text() == source
        assert sj.outstanding(include_live=True) == journal_before
        assert bg.extract_verifies_edges is function
        _check_catalogue_pins(pins)


def _reference_rows(state, lean):
    nodes = state['parameters'] + state['formulas'] + state['tests'] + lean
    result = []
    context = _support_context(nodes)
    for test in state['tests']:
        aliases = set(state['aliases'].get(test['meta']['module'], []))
        for raw in test['meta']['referenced_names']:
            result.append(dict(test=test['id'], **_reference_evidence(
                raw, aliases, nodes, state['short_index'], context=context)))
    return result


def _edge_multiset(edges):
    return Counter(json.dumps(e, sort_keys=True) for e in edges)


def _paired_production(state, lean, pins, tmp_path, label):
    """Only the actual production function's alias-order span changes in this pair."""
    nodes = state['parameters'] + state['formulas'] + state['tests'] + lean
    repaired, repaired_run = _actual_edges(state, pins)
    assert not _unsupported_edges(repaired, nodes, state['aliases'], state['short_index'])
    with _production_order_mutant(state, pins, tmp_path) as (mutant_state, mutation):
        mutant, mutant_run = _actual_edges(mutant_state, pins)
        # All resolver inputs are identical, including memo replay and ordered index.
        common_keys = ['tests', 'formulas', 'parameters', 'lean_ids', 'short_index',
                       'aliases', 'ambiguity', 'papers', 'paper_claims', 'readiness_links',
                       'paper_bytes', 'catalogue_pins', 'runtime']
        assert all(mutant_state[k] == state[k] for k in common_keys)
        assert {k: v for k, v in mutant_state['python_bytes'].items()
                if k != 'scripts/build_graph.py'} == {
                    k: v for k, v in state['python_bytes'].items() if k != 'scripts/build_graph.py'}
    assert _python_inputs() == state['python_bytes']
    old_nonlean = [e for e in mutant if not e['target'].startswith('lean:')]
    new_nonlean = [e for e in repaired if not e['target'].startswith('lean:')]
    assert _edge_multiset(old_nonlean) == _edge_multiset(new_nonlean)
    removed = list((_edge_multiset(mutant) - _edge_multiset(repaired)).elements())
    added = list((_edge_multiset(repaired) - _edge_multiset(mutant)).elements())
    assert not added
    rows = _reference_rows(state, lean)
    for row in rows:
        bypass = (row['reason'] == 'module-alias' and row['exact_in_graph'])
        row['repaired_disposition'] = row['reason']
        row['mutant_disposition'] = ('exact-before-alias' if bypass else
            'dotted-without-exact' if row['reason'] == 'module-alias' and row['dotted']
            else row['reason'])
        row['mutant_support'] = f"lean:{row['raw']}" if bypass else row['support']
    by_test = {}
    for row in rows:
        by_test.setdefault(row['test'], []).append(row)
    deltas = []
    for encoded in removed:
        edge = json.loads(encoded)
        evidence = by_test[edge['source']]
        assert any(row['root_alias'] and row['exact_in_graph']
                   and f"lean:{row['raw']}" == edge['target']
                   and row['selected_earlier'] is None for row in evidence)
        deltas.append(dict(edge=edge, disposition='removed-exact-module-alias', references=evidence))
    record = dict(label=label, loader='READ-ONLY frozen catalogue injection at scripts.extract_lean_deps.load_lean_deps; not cache-refresh validation',
                  inputs=state, input_fingerprints={k: _digest(v) for k, v in state.items()},
                  mutant_run=mutant_run, repaired_run=repaired_run, mutation=mutation,
                  mutant_edges=mutant, repaired_edges=repaired,
                  mutant_lean_edges=[e for e in mutant if e['target'].startswith('lean:')],
                  repaired_lean_edges=[e for e in repaired if e['target'].startswith('lean:')],
                  per_reference_dispositions=rows, deltas=deltas, added_edges=added,
                  nonlean_multiset=dict(_edge_multiset(new_nonlean)),
                  nonlean_multisets_equal=True,
                  mutant_unsupported=_unsupported_edges(mutant, nodes, state['aliases'], state['short_index']))
    return record


def _causal_consumers(record, state, lean):
    import last_modified as lm
    import readiness_gates as rg
    older = '2020-01-01T00:00:00Z'
    newer = '2021-01-01T00:00:00Z'
    all_nodes = state['parameters'] + state['formulas'] + state['tests'] + lean + state['papers']
    by_id = {n['id']: n for n in all_nodes}
    seed_id = 'test:test_verifies_exact_alias_seed_round44::test_exact_alias_seed'
    bad = [e for e in record['mutant_edges'] if e['source'] == seed_id and e['target'] == 'lean:pi']
    assert len(bad) == 1
    actual = bad[0]
    assert actual not in record['repaired_edges']
    positive = next(e for e in record['repaired_lean_edges']
                    if e['source'] != seed_id and e['target'] != 'lean:pi')
    results = {}
    for name, edges, selected in [('mutant', [actual], actual),
                                  ('repaired', [], actual),
                                  ('genuine-positive', [positive], positive)]:
        nodes = copy.deepcopy([by_id[selected['source']], by_id[selected['target']]])
        assert nodes[0]['type'] == 'PythonTest' and nodes[1]['id'].startswith('lean:')
        for n in nodes:
            n.setdefault('meta', {})['last_modified_explicit'] = older
        nodes[0]['meta']['last_modified_explicit'] = newer
        assert nodes[0]['meta']['last_modified_explicit'] > nodes[1]['meta']['last_modified_explicit']
        graph = dict(nodes=nodes, links=copy.deepcopy(edges))
        before = copy.deepcopy(graph)
        lm.annotate_last_modified(graph)
        expected = older if name == 'repaired' else newer
        assert graph['nodes'][1]['meta']['last_modified'] == expected
        results[name] = dict(input=before, output=graph, expected_target=expected)
    # Full actual Formula and paper inputs are retained, including papers with real formulas.
    assert state['formulas'] and state['papers']
    papers = state['papers']
    assert any(p.get('meta', {}).get('formulas') for p in papers)
    assert state['paper_claims'] and state['readiness_links']
    assert papers and any(e['target'].startswith('formula:') for e in record['repaired_edges'])
    readiness = {}
    for variant in ['mutant', 'repaired']:
        edges = record[f'{variant}_edges'] + state['readiness_links']
        nodes = copy.deepcopy(state['formulas'] + state['tests'] + state['papers'] + state['paper_claims'])
        graph = dict(nodes=nodes, links=copy.deepcopy(edges))
        idx = rg.GraphIndex(graph)
        readiness[variant] = [asdict(rg._eval_computation_correctness(copy.deepcopy(p), idx))
                              for p in papers]
    assert readiness['mutant'] == readiness['repaired']
    return dict(boundary='Isolated causal slices of actual production nodes and links; other incoming graph paths deliberately omitted. This does not measure whole-production freshness.',
                timestamp_order=dict(target_and_other_inputs=older, test=newer),
                freshness=results, readiness=readiness,
                complete_formula_nodes=state['formulas'], complete_paper_nodes=state['papers'],
                complete_claim_nodes=state['paper_claims'], complete_paper_bytes=state['paper_bytes'],
                complete_claims_and_grounding_edges=state['readiness_links'],
                complete_formula_edges=[e for e in record['repaired_edges'] if e['target'].startswith('formula:')],
                actual_nonempty_formula_papers=[p['id'] for p in papers if p.get('meta', {}).get('formulas')])


@pytest.mark.slow
@pytest.mark.parametrize('source_comparison_mode', ['current-head', 'controlled-committed-source'])
def test_frozen_corpus_production_seed_mutant_and_consumers(tmp_path, _frozen_catalogue,
                                                          source_comparison_mode):
    """Recompute every causal leg; saved manifests never substitute for execution."""
    import seed_journal as sj
    pins, _ = _frozen_catalogue
    assert bg.PROJECT_ROOT.resolve() == sj.PROJECT_ROOT.resolve() == SK_ROOT.resolve()
    assert sj.JOURNAL_DIR.resolve().parent == SK_ROOT.resolve()
    assert (SK_ROOT / 'tests').resolve().is_relative_to(SK_ROOT.resolve())
    assert not sj.outstanding(include_live=True), 'candidate has another live or orphaned seed'
    before_journal = sj.outstanding(include_live=True)
    seed = SK_ROOT / 'tests/test_verifies_exact_alias_seed_round44.py'
    assert not seed.exists(), 'seed collision: ROOT must revise the assigned path'
    state, lean = _actual_inputs(pins)
    corpus = _paired_production(state, lean, pins, tmp_path, f'{source_comparison_mode}:unseeded-corpus')
    corpus_file = _write_record(tmp_path, 'paired-corpus.json', corpus)
    # Current-HEAD source attribution is independent of resolver-only A/B.
    test_path = Path(__file__)
    head = subprocess.run(['git', 'rev-parse', '--verify', 'HEAD'], cwd=SK_ROOT,
                          text=True, capture_output=True, check=True)
    resolved_head = head.stdout.strip()
    actual_head_source = subprocess.run(
        ['git', 'show', f'{resolved_head}:{test_path.relative_to(SK_ROOT)}'],
        cwd=SK_ROOT, capture_output=True, check=True)
    working_bytes = test_path.read_bytes()
    comparison_bytes = (actual_head_source.stdout if source_comparison_mode == 'current-head'
                        else working_bytes)
    identical = comparison_bytes == working_bytes
    comparison = dict(mode=source_comparison_mode,
        label=('current-HEAD-vs-working-source' if source_comparison_mode == 'current-head'
               else 'CONTROLLED committed-source-equivalent; baseline is exact working bytes'),
        resolved_actual_head_commit=resolved_head,
        actual_head_source_sha256=hashlib.sha256(actual_head_source.stdout).hexdigest(),
        working_source_sha256=hashlib.sha256(working_bytes).hexdigest(),
        selected_comparison_source_sha256=hashlib.sha256(comparison_bytes).hexdigest(),
        comparison_bytes_equal_working=identical,
        actual_postcommit_execution_claim=False,
        read_only_git_commands=[dict(command=head.args, stdout=head.stdout,
            stderr=head.stderr, returncode=head.returncode),
            dict(command=actual_head_source.args, stdout=actual_head_source.stdout.decode('utf-8'),
                 stderr=actual_head_source.stderr.decode('utf-8'), returncode=actual_head_source.returncode)])
    attribution_journal_before = sj.outstanding(include_live=True)
    replay_journal = []
    if identical:
        # A no-op is not a mutation: exercise real producers without opening a journal.
        base_state, base_lean = _actual_inputs(pins)
        base_edges, base_run = _actual_edges(base_state, pins)
        assert base_state == state and base_lean == lean
        assert base_edges == corpus['repaired_edges']
        assert sj.outstanding(include_live=True) == attribution_journal_before
    else:
        with sj.seeded_mutation(test_path, comparison_bytes,
                                reason='current-HEAD Python producer attribution, separate from resolver pair'):
            replay_journal = sj.outstanding(include_live=True)
            assert len(replay_journal) == len(attribution_journal_before) + 1
            assert any(e['path'] == str(test_path) and e['sha256'] == comparison['working_source_sha256']
                       for e in replay_journal)
            base_state, base_lean = _actual_inputs(pins)
            base_edges, base_run = _actual_edges(base_state, pins)
    assert test_path.read_bytes() == working_bytes
    assert base_state['python_bytes'][str(test_path.relative_to(SK_ROOT))].encode('utf-8') == comparison_bytes
    assert sj.outstanding(include_live=True) == attribution_journal_before
    base_record = dict(comparison=comparison, input=base_state, edges=base_edges, run=base_run,
                       journal_replay_performed=not identical,
                       journal_before=attribution_journal_before, journal_during=replay_journal,
                       journal_after=sj.outstanding(include_live=True))
    final_by_id = {n['id']: n for n in state['tests']}
    base_by_id = {n['id']: n for n in base_state['tests']}
    changed_ids = sorted(k for k in final_by_id.keys() | base_by_id.keys()
                         if final_by_id.get(k) != base_by_id.get(k))
    new_ids = sorted(final_by_id.keys() - base_by_id.keys())
    removed_ids = sorted(base_by_id.keys() - final_by_id.keys())
    # Line/detail changes are source changes, not resolver deltas.
    final_edges = _edge_multiset(corpus['repaired_edges'])
    base_edges_set = _edge_multiset(base_edges)
    added = [json.loads(e) for e in (final_edges - base_edges_set).elements()]
    removed = [json.loads(e) for e in (base_edges_set - final_edges).elements()]
    if identical:
        assert changed_ids == new_ids == removed_ids == added == removed == []
        assert base_state == state and base_edges == corpus['repaired_edges']
    else:
        assert changed_ids and all(k.startswith('test:test_verifies_alias_guard::') for k in changed_ids)
        assert all(e['source'] in changed_ids for e in added + removed)
    assert base_state['lean_ids'] == state['lean_ids']
    assert base_state['formulas'] == state['formulas'] and base_state['parameters'] == state['parameters']
    attribution = dict(base=base_record, changed_test_ids=changed_ids,
                       new_test_ids=new_ids, removed_test_ids=removed_ids,
                       source_change_added_edges=added, source_change_removed_edges=removed,
                       complete_inputs_equal=base_state == state,
                       complete_edge_lists_equal=base_edges == corpus['repaired_edges'],
                       separated_from_resolver_deltas=True)
    attribution_file = _write_record(tmp_path, 'source-attribution.json', attribution)
    seeded_payload = "import json as pi\n\ndef test_exact_alias_seed():\n    assert pi.loads('{}') == {}\n"
    seeded_id = 'test:test_verifies_exact_alias_seed_round44::test_exact_alias_seed'
    with sj.seeded_artifact(seed, seeded_payload, reason='unique actual Python producer exact pi alias witness'):
        journal_during = sj.outstanding(include_live=True)
        assert len(journal_during) == 1 and journal_during[0]['path'] == str(seed)
        seeded_state, seeded_lean = _actual_inputs(pins)
        row = [n for n in seeded_state['tests'] if n['id'] == seeded_id]
        assert len(row) == 1
        assert 'pi' in row[0]['meta']['referenced_names']
        assert 'pi.loads' in row[0]['meta']['referenced_names']
        assert 'pi' in seeded_state['aliases'][seed.stem]
        canonical_pi = [n for n in seeded_lean if n['id'] == 'lean:pi']
        assert len(canonical_pi) == 1 and canonical_pi[0]['type'] == 'LeanDef'
        pair = _paired_production(seeded_state, seeded_lean, pins, tmp_path, f'{source_comparison_mode}:seeded-corpus')
        seeded_offenders = [o for o in pair['mutant_unsupported'] if o['edge']['source'] == seeded_id
                            and o['edge']['target'] == 'lean:pi']
        assert len(seeded_offenders) == 1, 'global corpus red cannot substitute for seeded offender'
        assert any(e['source'] == seeded_id and e['target'] == 'lean:pi' for e in pair['mutant_edges'])
        assert not any(e['source'] == seeded_id and e['target'] == 'lean:pi' for e in pair['repaired_edges'])
        seeded_nodes = seeded_state['parameters'] + seeded_state['formulas'] + seeded_state['tests'] + seeded_lean
        mutant_seed_edges = [e for e in pair['mutant_edges'] if e['source'] == seeded_id]
        repaired_seed_edges = [e for e in pair['repaired_edges'] if e['source'] == seeded_id]
        with pytest.raises(AssertionError) as guard_red:
            _assert_supported_edges(mutant_seed_edges, seeded_nodes,
                                    seeded_state['aliases'], seeded_state['short_index'])
        assert seeded_id in str(guard_red.value) and 'lean:pi' in str(guard_red.value)
        _assert_supported_edges(repaired_seed_edges, seeded_nodes,
                                seeded_state['aliases'], seeded_state['short_index'])
        pair['seed_guard'] = dict(mutant_assertion_error=str(guard_red.value),
                                  repaired_assertion='passed',
                                  mutant_actual_edges=mutant_seed_edges,
                                  repaired_actual_edges=repaired_seed_edges)
        pair['seed'] = dict(path=str(seed), bytes=seeded_payload, row=row[0],
                            canonical_pi=canonical_pi[0], journal_during=journal_during,
                            unique_mutant_offender=seeded_offenders[0],
                            added_python_file_only=str(seed.relative_to(SK_ROOT)))
        seed_file = _write_record(tmp_path, 'paired-seed.json', pair)
        consumers = _causal_consumers(pair, seeded_state, seeded_lean)
        consumer_file = _write_record(tmp_path, 'consumers.json', consumers)
    assert not seed.exists()
    assert sj.outstanding(include_live=True) == before_journal
    restored_state, restored_lean = _actual_inputs(pins)
    assert restored_state == state
    assert [n['id'] for n in restored_lean] == [n['id'] for n in lean]
    _write_record(tmp_path, 'restoration.json', dict(journal_before=before_journal,
                  journal_after=sj.outstanding(include_live=True), seed_absent=not seed.exists(),
                  all_producer_inputs_restored=True, source_sha256=hashlib.sha256(
                      (SK_ROOT / 'scripts/build_graph.py').read_bytes()).hexdigest(),
                  source_comparison_mode=source_comparison_mode,
                  source_attribution_comparison=comparison,
                  records=[corpus_file, attribution_file, seed_file, consumer_file],
                  pins=_check_catalogue_pins(pins)))


@pytest.mark.parametrize('raw', ['pi', 'bad.foo'])
def test_identical_exact_reference_without_module_alias_is_allowed(monkeypatch, raw):
    test = _test_node('test_exact_positive', 'test_x', [raw])
    edges = _run(monkeypatch, tests=[test], lean_full=(raw,),
                 aliases={'test_exact_positive': set()})
    assert edges == [dict(source=test['id'], target=f'lean:{raw}',
                          type='VERIFIES', test_kind='golden')]


def test_distinct_valid_refs_deduplicate_with_test_kind_intact(monkeypatch):
    test = _test_node('test_dedup', 'test_x', ['foo', 'Good.foo'], kind='roundtrip')
    edges = _run(monkeypatch, tests=[test], lean_full=('Good.foo',))
    assert edges == [dict(source=test['id'], target='lean:Good.foo',
                          type='VERIFIES', test_kind='roundtrip')]


def test_parameter_full_key_and_first_tail_selection_are_ordered():
    lean = dict(id='lean:Good.foo', name='foo', type='LeanDef')
    nodes = [_param_node('P.foo'), _param_node('Q.foo'), lean]
    first = _reference_evidence('foo', set(), nodes, {'foo': [lean['id']]})
    assert first['selected_earlier'] == 'param:P.foo' and first['support'] is None
    nodes.insert(2, _param_node('foo'))
    full = _reference_evidence('foo', set(), nodes, {'foo': [lean['id']]})
    assert full['selected_earlier'] == 'param:foo' and full['support'] is None
