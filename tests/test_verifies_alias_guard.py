"""ADR-009 §Deferred item 7 (second half) — the Lean VERIFIES branch stops
manufacturing coverage from Python library aliases.

`extract_verifies_edges` resolves each of a test's `referenced_names` against
Formula, then Parameter, then Lean short names. The formula index has carried an
alias allow-list since D12 round-9, with a comment stating the hazard outright:
a blanket tail fallback "would let `np.sum` or `math.exp` match a formula named
`sum` or `exp`, manufacturing coverage that does not exist". The Lean branch had
no equivalent guard, and `_resolve_lean_short` falls back to matching the TAIL of
a dotted name — so exactly that happened.

**Measured on the live graph at the fix: 144 of 536 Lean-targeted VERIFIES edges
were fabricated.** `np.all` (58) -> `FaultTolerance.Pauli.all`; `v` (21, from the
conventional `import validate as v`) -> `EWMassMatrixInputs.v`; `np.diag` (11) ->
`IsCharQ.diag`; `np.dot` -> `KMM.Col.dot`; `mx.eval` -> `IntFundamentalClass.eval`;
`PARAMETER_PROVENANCE.get` -> `NeutrinoMixing.get`. All 17 Lean declarations that
lost an edge lost EVERY edge they had — none had genuine coverage mixed in, which
is what makes the partition credible.

(ADR-009 originally recorded 10. That figure came from five example names and
understated the count 14-fold; corrected here from a direct measurement.)

Two rules, one principle — a VERIFIES edge must rest on a name the test actually
wrote, not on a suffix of one:

* a ref rooted at a MODULE ALIAS (`import X [as y]`) is a Python module
  reference and can never denote a Lean declaration;
* a DOTTED ref is a Python attribute access, so it may resolve only as a full
  Lean name, never by its tail.

D5: every test below runs both directions — it FIRES if the guard is removed and
stays SILENT on the legitimate name-correspondence the branch exists to follow.
The synthetic legs drive the real extractor with stub node sets, so remediation
that legitimately changes the corpus cannot break them.
"""
from __future__ import annotations

import ast
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
            "`import validate as v` is the alias that produced 21 fabricated "
            "edges; it must be recognised as a module alias")


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
        """`v` is undotted, so a dotted-only guard would miss it. It was the
        single largest fabricated cluster after `np.all`: 21 edges."""
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
        still an edge. (No ref on disk takes this path today; the leg keeps the
        guard from being written as a blanket ban on dots.)"""
        edges = _run(monkeypatch,
                     tests=[_test_node("test_p", "test_x",
                                       ["SKEFTHawking.NeutrinoMixing.get"])],
                     lean_full=self.LEAN, aliases={"test_p": set()})
        assert [e["target"] for e in edges] == ["lean:SKEFTHawking.NeutrinoMixing.get"]


class TestLegitimateCoverageSurvives:
    def test_a_from_imported_project_symbol_resolves(self, monkeypatch):
        """SILENT ON CORRECT DATA — this is the 392-edge majority the branch
        exists for: a Python implementation whose name mirrors its Lean
        formalization."""
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
    """The safety property that makes this landable mid-remediation: the Lean
    branch runs only when the Formula and Parameter indexes have both missed, so
    it can neither add nor remove a formula- or param-targeted edge. Measured on
    the live graph: 1,390 non-Lean edges before and after, bit-identical — which
    is why no `ReadinessGate: ComputationCorrectness` verdict can move.

    (That gate reads only `formula:` targets — verified at
    `readiness_gates.py:283-294`. ADR-009 item 7 named it as the consumer of the
    fabricated LEAN edges, which was wrong; the real consumers are
    `last_modified.py`'s VERIFIES propagation and any reader of the graph's Lean
    coverage picture.)"""

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
    """Structural, corpus-independent: no Lean-targeted VERIFIES edge on the live
    graph may be rooted at one of its own test module's aliases, or be dotted
    without being a full Lean name. Marked slow — needs the Lean declaration
    nodes, hence `load_lean_deps()`."""

    def test_no_lean_edge_is_alias_rooted_or_tail_resolved(self):
        nodes = (bg.extract_parameter_nodes() + bg.extract_formula_nodes()
                 + bg.extract_lean_declaration_nodes() + bg.extract_python_test_nodes())
        node_ids = {n["id"] for n in nodes}
        refs_by_test = {n["id"]: n["meta"].get("referenced_names", [])
                        for n in nodes if n["type"] == "PythonTest"}
        mods = {n["id"]: n["meta"].get("module", "")
                for n in nodes if n["type"] == "PythonTest"}

        offenders = []
        for e in bg.extract_verifies_edges(node_ids):
            if not e["target"].startswith("lean:"):
                continue
            aliases = bg._TEST_MODULE_ALIASES.get(mods.get(e["source"], ""), set())
            short = e["target"][len("lean:"):].rsplit(".", 1)[-1]
            for raw in refs_by_test.get(e["source"], []):
                if raw.rsplit(".", 1)[-1] != short:
                    continue
                if raw.split(".", 1)[0] in aliases:
                    offenders.append((e["source"], raw, e["target"], "module-alias"))
                elif "." in raw and f"lean:{raw}" not in node_ids:
                    offenders.append((e["source"], raw, e["target"], "tail-resolved"))
        assert not offenders, (
            f"{len(offenders)} fabricated Lean VERIFIES edge(s) back on the live "
            f"graph: {offenders[:10]}")
