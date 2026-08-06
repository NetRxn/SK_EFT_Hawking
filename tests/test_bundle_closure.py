"""Tests for the bundle substrate closure — the derived half of publication intake.

Each test states which direction it guards. A test that only asserts the happy path is
how a check that cannot fail gets shipped, which is the defect class this whole branch
exists to remove.
"""
from __future__ import annotations

import json
import sys
from pathlib import Path

import pytest

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT))
sys.path.insert(0, str(SK_ROOT / "scripts"))

import bundle_closure  # noqa: E402


def rec(name, kind="theorem", module="SKEFTHawking.Foo", deps=(), autogen=False):
    return {"name": name, "kind": kind, "module": module,
            "name_deps_project": list(deps), "autogen": autogen}


APEX = "SKEFTHawking.Foo.headline"


def corpus():
    """A small corpus with every shape the walk has to handle."""
    return [
        rec(APEX, deps=[
            "SKEFTHawking.Foo.mid",
            "SKEFTHawking.Bar.Shape.casesOn",       # generated: walked through, not counted
            "_private.SKEFTHawking.Foo.0.hidden",   # private: walk STOPS, counted as truncation
        ]),
        rec("SKEFTHawking.Foo.mid", deps=["SKEFTHawking.Bar.deep"]),
        rec("SKEFTHawking.Bar.deep", module="SKEFTHawking.Bar"),
        rec("SKEFTHawking.Bar.Shape.casesOn", kind="def", module="SKEFTHawking.Bar",
            autogen=True, deps=["SKEFTHawking.Bar.reached_only_via_generated"]),
        rec("SKEFTHawking.Bar.reached_only_via_generated", module="SKEFTHawking.Bar"),
        rec("SKEFTHawking.Unrelated.orphan", module="SKEFTHawking.Unrelated"),
    ]


class TestClosureWalk:
    def _closure(self):
        by_name, autogen = bundle_closure._index(corpus())
        return bundle_closure.compute_closure([APEX], by_name, autogen)

    def test_it_is_transitive_not_just_direct(self):
        """SILENT ON CORRECT DATA — a one-hop walk would miss `Bar.deep`, and the whole
        design rests on the closure reaching further than a citation does."""
        closure, _d, _p, _o = self._closure()
        assert "SKEFTHawking.Bar.deep" in closure

    def test_generated_declarations_are_WALKED_THROUGH_but_not_counted(self):
        """FIRES ON THE SEEDED DEFECT, both directions.

        Skipping generated declarations at the EDGE severs real dependencies that route
        through a structure's eliminator; counting them inflates every closure size by
        the compiler's output.
        """
        closure, _d, _p, _o = self._closure()
        assert "SKEFTHawking.Bar.Shape.casesOn" not in closure, "generated decl counted"
        assert "SKEFTHawking.Bar.reached_only_via_generated" in closure, (
            "a real declaration reachable only through a generated one was severed")

    def test_a_private_dependency_is_counted_as_a_TRUNCATION(self):
        """ExtractDeps omits private declarations, so the walk stops there and loses
        whatever is beneath. Reporting a size without this is an absence rendered as
        success."""
        _c, _d, private, _other = self._closure()
        assert private == 1

    def test_depth_is_the_longest_chain(self):
        _c, depth, _p, _o = self._closure()
        assert depth == 2  # headline -> mid -> deep

    def test_an_unreachable_declaration_stays_out(self):
        closure, _d, _p, _o = self._closure()
        assert "SKEFTHawking.Unrelated.orphan" not in closure


class TestDeclarationLoading:
    def _write(self, root: Path, bundle: str, payload: dict):
        d = root / bundle
        d.mkdir(parents=True)
        (d / "bundle_metadata.json").write_text(json.dumps(payload))

    def test_a_bundle_without_the_key_is_UNDECLARED_not_absent(self, tmp_path):
        """FIRES ON THE SEEDED DEFECT: skip undeclared bundles here and the population
        silently shrinks to the ones that already comply — which is how 'no bundle has a
        problem' gets manufactured."""
        self._write(tmp_path, "D1", {"bundle_target": "D1"})
        got = bundle_closure.load_apex_declarations(tmp_path)
        assert "D1" in got
        assert got["D1"]["declared"] is False

    def test_an_unreadable_metadata_file_is_undeclared_not_skipped(self, tmp_path):
        d = tmp_path / "D2"
        d.mkdir(parents=True)
        (d / "bundle_metadata.json").write_text("{ not json")
        got = bundle_closure.load_apex_declarations(tmp_path)
        assert got["D2"]["declared"] is False and got["D2"]["unreadable"] is True

    def test_both_the_string_and_the_object_form_are_read(self, tmp_path):
        self._write(tmp_path, "L1", {"apex_theorems": ["A.b"]})
        self._write(tmp_path, "L2", {"apex_theorems": [{"name": "C.d", "claims": "§2"}]})
        got = bundle_closure.load_apex_declarations(tmp_path)
        assert got["L1"]["apexes"] == ["A.b"] and got["L2"]["apexes"] == ["C.d"]


class TestMeasurability:
    def test_an_undeclared_bundle_is_NOT_measurable(self):
        """⚠️ THE LOAD-BEARING ASSERTION. A closure over zero apexes is empty and every
        universal over it holds; `measurable` is what stops that reading as clean."""
        closures = bundle_closure.build_closures(
            corpus(), {"D1": {"declared": False, "apexes": []}})
        assert closures["D1"].measurable is False

    def test_a_bundle_declaring_an_EMPTY_list_is_also_not_measurable(self):
        closures = bundle_closure.build_closures(
            corpus(), {"D1": {"declared": True, "apexes": []}})
        assert closures["D1"].measurable is False

    def test_a_declared_bundle_is_measurable(self):
        closures = bundle_closure.build_closures(
            corpus(), {"D1": {"declared": True, "apexes": [APEX]}})
        assert closures["D1"].measurable is True


class TestApexValidity:
    def test_an_apex_naming_nothing_is_reported_unresolved(self):
        closures = bundle_closure.build_closures(
            corpus(), {"D1": {"declared": True, "apexes": ["SKEFTHawking.Foo.renamed"]}})
        assert closures["D1"].unresolved_apexes == ["SKEFTHawking.Foo.renamed"]

    def test_an_apex_that_is_a_def_is_reported(self):
        """A bundle claims results; a `def` is machinery the results are stated over."""
        recs = corpus() + [rec("SKEFTHawking.Foo.someDef", kind="def")]
        closures = bundle_closure.build_closures(
            recs, {"D1": {"declared": True, "apexes": ["SKEFTHawking.Foo.someDef"]}})
        assert closures["D1"].non_theorem_apexes == ["SKEFTHawking.Foo.someDef"]


class TestHoming:
    def test_two_bundles_sharing_substrate_both_appear(self):
        recs = corpus() + [rec("SKEFTHawking.Foo.other", deps=["SKEFTHawking.Bar.deep"])]
        closures = bundle_closure.build_closures(recs, {
            "D1": {"declared": True, "apexes": [APEX]},
            "D2": {"declared": True, "apexes": ["SKEFTHawking.Foo.other"]}})
        homed = bundle_closure.homing_index(closures)
        assert homed["SKEFTHawking.Bar.deep"] == ["D1", "D2"]

    def test_the_un_homed_denominator_is_DERIVED_from_the_records(self):
        """The denominator must come from the record set, never a module list — an
        enumerated denominator is the defect this design replaces."""
        project = bundle_closure.project_declarations(corpus())
        assert "SKEFTHawking.Unrelated.orphan" in project
        assert "SKEFTHawking.Bar.Shape.casesOn" not in project  # generated

    def test_a_declaration_outside_the_project_namespace_is_not_in_the_denominator(self):
        recs = corpus() + [rec("Mathlib.Thing.lemma", module="Mathlib.Thing")]
        assert "Mathlib.Thing.lemma" not in bundle_closure.project_declarations(recs)


class TestTheCheck:
    """`bundle_apex_resolves` — the gate on the one hand-maintained input."""

    @pytest.fixture
    def check(self):
        import validate
        return validate.check_bundle_apex_resolves

    def _papers(self, monkeypatch, tmp_path, bundles: dict):
        for bundle, payload in bundles.items():
            d = tmp_path / "papers" / bundle
            d.mkdir(parents=True)
            (d / "bundle_metadata.json").write_text(json.dumps(payload))
        import validate_helpers
        monkeypatch.setattr(validate_helpers, "PROJECT_ROOT", tmp_path)

    def test_nothing_declared_says_UNMEASURABLE_rather_than_passing_vacuously(
            self, check, monkeypatch, tmp_path):
        """The substantive predicate is a universal over a bundle-supplied set, so with
        nothing declared it holds of nothing. The check must SAY that, not report a
        resolution it never performed."""
        self._papers(monkeypatch, tmp_path, {"D1": {"bundle_target": "D1"}})
        res = check()
        resolve = next(d for d in res.details if d.name == "apexes_resolve")
        assert "UNMEASURABLE" in resolve.message and resolve.warning is True
        # Pin the fixture, not the live tree: `1 of 21` here would mean the check read
        # the real papers/ and the test proved nothing about the seeded state.
        ratchet = next(d for d in res.details if d.name == "undeclared_does_not_rise")
        assert "1 of 1 bundle(s)" in ratchet.message, ratchet.message

    def test_the_undeclared_count_RISING_is_a_hard_failure(
            self, check, monkeypatch, tmp_path):
        """⚠️ FIRES ON THE SEEDED DEFECT, and this is the assertion that gives the check
        teeth on day one. Without the ratchet, a portfolio where NOBODY has said what any
        bundle claims reports a clean pass — absence rendered as success (H1)."""
        import validation.checks.bundles_readiness as mod
        monkeypatch.setattr(mod, "UNDECLARED_APEX_CEILING", 1)
        self._papers(monkeypatch, tmp_path,
                     {"D1": {"bundle_target": "D1"}, "D2": {"bundle_target": "D2"}})
        res = check()
        assert res.passed is False
        assert "rose to 2" in " ".join(d.message for d in res.details)

    def test_the_ratchet_is_silent_AT_the_ceiling(self, check, monkeypatch, tmp_path):
        """SILENT ON CORRECT DATA — a ratchet that fires at its own baseline is a
        permanently red check nobody reads."""
        import validation.checks.bundles_readiness as mod
        monkeypatch.setattr(mod, "UNDECLARED_APEX_CEILING", 2)
        self._papers(monkeypatch, tmp_path,
                     {"D1": {"bundle_target": "D1"}, "D2": {"bundle_target": "D2"}})
        assert check().passed is True

    def test_absent_bundle_metadata_is_the_one_CANNOT_MEASURE_branch(
            self, check, monkeypatch, tmp_path):
        """No metadata at all is an ABSENT input — distinct from present-but-undeclared,
        which is a measurement with a definite result."""
        (tmp_path / "papers").mkdir()
        import validate_helpers
        monkeypatch.setattr(validate_helpers, "PROJECT_ROOT", tmp_path)
        res = check()
        assert res.measured is False and res.passed is True

    def test_a_declared_apex_naming_nothing_FAILS(self, check, monkeypatch, tmp_path):
        self._papers(monkeypatch, tmp_path,
                     {"D1": {"apex_theorems": ["SKEFTHawking.Nope.gone"]}})
        monkeypatch.setattr(bundle_closure, "load_records", corpus)
        res = check()
        assert res.passed is False and res.measured is True

    def test_a_live_apex_PASSES_and_counts_as_evidence(self, check, monkeypatch, tmp_path):
        """SILENT ON CORRECT DATA — the guard must not be unconditionally red either."""
        self._papers(monkeypatch, tmp_path, {"D1": {"apex_theorems": [APEX]}})
        monkeypatch.setattr(bundle_closure, "load_records", corpus)
        res = check()
        assert res.passed is True and res.measured is True

    def test_the_closure_detail_carries_its_truncation(self, check, monkeypatch, tmp_path):
        """A closure size reported alone is an absence rendered as success."""
        self._papers(monkeypatch, tmp_path, {"D1": {"apex_theorems": [APEX]}})
        monkeypatch.setattr(bundle_closure, "load_records", corpus)
        res = check()
        detail = next(d for d in res.details if d.name == "closure_D1")
        assert "private" in detail.message


class TestGraphOverlay:
    """§6's hard constraint: closures reach the graph, so human review is not a second
    conversation. As an OVERLAY on existing nodes — the `_overlay_atlas` precedent —
    because materialising closure membership would add ~10 k links to a 14 040-edge graph.
    """

    def _nodes(self):
        return [
            {"id": f"lean:{APEX}", "type": "LeanTheorem", "meta": {}},
            {"id": "lean:SKEFTHawking.Bar.deep", "type": "LeanTheorem", "meta": {}},
            {"id": "lean:SKEFTHawking.Unrelated.orphan", "type": "LeanTheorem", "meta": {}},
            {"id": "module:SKEFTHawking.Bar", "type": "LeanModule", "meta": {}},
            {"id": "paper:D1", "type": "Paper", "meta": {}},
        ]

    def _overlay(self, monkeypatch, declared):
        import build_graph
        monkeypatch.setattr(bundle_closure, "load_records", corpus)
        monkeypatch.setattr(bundle_closure, "load_apex_declarations",
                            lambda _root: {"D1": declared})
        nodes = self._nodes()
        build_graph._overlay_closure(nodes)
        return {n["id"]: n["meta"] for n in nodes}

    def test_a_claimed_declaration_carries_its_bundle(self, monkeypatch):
        meta = self._overlay(monkeypatch, {"declared": True, "apexes": [APEX]})
        assert meta["lean:SKEFTHawking.Bar.deep"]["homed_by"] == ["D1"]
        assert meta["module:SKEFTHawking.Bar"]["homed_by"] == ["D1"]

    def test_an_unclaimed_declaration_is_left_UN_HOMED(self, monkeypatch):
        """SILENT ON CORRECT DATA — un-homed is the state the dashboard filters on, so a
        default of `[]` written everywhere would be indistinguishable from claimed-by-none
        only if it were also written for claimed nodes. It must stay absent."""
        meta = self._overlay(monkeypatch, {"declared": True, "apexes": [APEX]})
        assert not meta["lean:SKEFTHawking.Unrelated.orphan"].get("homed_by")

    def test_an_undeclared_bundle_publishes_NO_closure_size(self, monkeypatch):
        """⚠️ FIRES ON THE SEEDED DEFECT: emit `closure_size: 0` unconditionally and a
        bundle nobody has described reads on the dashboard as resting on nothing."""
        meta = self._overlay(monkeypatch, {"declared": False, "apexes": []})
        assert meta["paper:D1"]["closure_measurable"] is False
        assert "closure_size" not in meta["paper:D1"]

    def test_a_declared_bundle_publishes_its_shape_WITH_truncation(self, monkeypatch):
        meta = self._overlay(monkeypatch, {"declared": True, "apexes": [APEX]})
        p = meta["paper:D1"]
        # apex + mid + deep + the one reachable only through a generated declaration.
        assert p["closure_measurable"] is True and p["closure_size"] == 4
        assert p["closure_truncated_private"] == 1, (
            "a closure size published without its truncation reads as complete")

    def test_apex_edges_are_emitted_for_live_declarations_only(self, monkeypatch):
        import build_graph
        monkeypatch.setattr(bundle_closure, "load_apex_declarations",
                            lambda _root: {"D1": {"declared": True,
                                                  "apexes": [APEX, "SKEFTHawking.Nope"]}})
        edges = build_graph.extract_claims_apex_edges(
            {"paper:D1", f"lean:{APEX}"})
        assert edges == [{"source": "paper:D1", "target": f"lean:{APEX}",
                          "type": "CLAIMS_APEX"}], (
            "a dangling apex must surface as a broken declaration, not as a graph edge")
