"""Per-finding orientation — ADR-012 D17.

Orientation is GENERATED, not gathered. Re-deriving it per finding from cold context is the
expensive way, and it is what the operator's step 1 was reacting to.
"""
from __future__ import annotations

import sys
from pathlib import Path

import pytest

PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT))
sys.path.insert(0, str(PROJECT_ROOT / "scripts"))

import review_runner as rr  # noqa: E402


def _a_finding_with_a_RESOLVABLE_target():
    """⚠️ Requires the target to resolve on disk, not merely to exist as a string.

    The first version asked only for a `target`, and the corpus is walked in sorted order,
    so which finding it returned changed whenever a review was filed or closed. It picked a
    finding whose `papers/`-relative target the brief could not resolve, and the whole class
    read as a test failure rather than as the production bug it was.
    """
    import review_runner as _rr
    from build_graph import extract_review_finding_nodes
    for n in extract_review_finding_nodes():
        t = (n["meta"].get("target") or "").strip("`")
        if t and n["meta"].get("status") == "open" and _rr._resolve_target(t)[0]:
            return n
    return None


def _a_finding_with_an_UNRESOLVABLE_target():
    import review_runner as _rr
    from build_graph import extract_review_finding_nodes
    for n in extract_review_finding_nodes():
        t = (n["meta"].get("target") or "").strip("`")
        if t and not _rr._resolve_target(t)[0]:
            return n
    return None


def _a_finding_with_a_target():
    n = _a_finding_with_a_RESOLVABLE_target()
    assert n is not None, "no open finding carries a resolvable target — the seam is empty"
    return n


class TestPerFindingBrief:
    def test_the_brief_names_the_target_and_its_provenance(self):
        node = _a_finding_with_a_target()
        assert node is not None, (
            "no open finding carries a target — the seam is empty, not clean")
        out = rr.emit_finding_brief(node["id"])
        assert node["meta"]["target"].strip("`") in out
        for heading in ("## TARGET", "## GIT HISTORY", "## ROADMAP",
                        "## SUBSTRATE DELTA"):
            assert heading in out, f"{heading} missing from the brief"

    def test_it_carries_the_routing_fields_a_worker_needs(self):
        node = _a_finding_with_a_target()
        out = rr.emit_finding_brief(node["id"])
        for label in ("LANE:", "BLOCKS:", "VERIFY:", "BLOCKED-BY:", "DISPATCHABLE:",
                      "NEEDS-OPERATOR:"):
            assert label in out


class TestTargetResolution:
    """⚠️ Review `Location:` values are written **`papers/`-relative**. Resolving them only
    from the repo root made most of them miss, and the brief then told the worker the
    finding was STALE — a false staleness claim on a live file."""

    def test_a_papers_relative_target_resolves(self):
        from build_graph import extract_review_finding_nodes
        n = next(x for x in extract_review_finding_nodes()
                 if (x["meta"].get("target") or "").strip("`").startswith("paper"))
        t = n["meta"]["target"].strip("`")
        path, tried = rr._resolve_target(t)
        assert path is not None, f"{t} resolved against none of {tried}"
        assert path.is_file()

    def test_the_repo_root_is_still_tried_first(self, tmp_path, monkeypatch):
        """A repo-relative target must not start resolving against `papers/` instead."""
        path, tried = rr._resolve_target("scripts/review_runner.py")
        assert path is not None and path.name == "review_runner.py"
        assert tried[0] == "scripts/review_runner.py"

    def test_an_unresolvable_target_NAMES_WHAT_IT_TRIED(self):
        """'Does not resolve' plus the paths tried is a measurement. Alone it is a verdict
        the reader cannot check."""
        path, tried = rr._resolve_target("no/such/file.tex:12")
        assert path is None
        assert tried == ["no/such/file.tex", "papers/no/such/file.tex"]

    def test_the_unresolved_branch_of_the_brief_is_reachable_and_honest(self):
        node = _a_finding_with_an_UNRESOLVABLE_target()
        if node is None:
            pytest.skip("every filed target currently resolves")
        out = rr.emit_finding_brief(node["id"])
        assert "does not resolve to a file on disk" in out
        assert "Tried:" in out

    def test_an_unknown_finding_id_RAISES_rather_than_emitting_an_empty_brief(self):
        """⚠️ An empty brief reads as 'nothing to orient on' when the truth is 'not
        found' — absence rendered as success, in the one artifact a worker trusts."""
        with pytest.raises(KeyError, match="names no minted finding"):
            rr.emit_finding_brief("review:no-such-date:NOPE:1.1")

    def test_the_substrate_delta_prompt_is_always_present(self):
        """The operator's step 1 asks explicitly whether anything moved. A brief that
        omits the question lets a worker skip it silently."""
        node = _a_finding_with_a_target()
        out = rr.emit_finding_brief(node["id"])
        assert "including 'no'" in out


class TestTheCLI:
    def test_finding_is_handled_before_the_bundle_gate(self, capsys):
        """⚠️ `main()` returns 1 on anything without `--bundle`, so a `--finding` handled
        after that gate would exit 1 while printing nothing."""
        node = _a_finding_with_a_target()
        rc = rr.main(["--finding", node["id"]])
        assert rc == 0
        assert "# Orientation —" in capsys.readouterr().out

    def test_an_unknown_id_exits_1_with_a_message_on_stderr(self, capsys):
        rc = rr.main(["--finding", "review:no-such-date:NOPE:1.1"])
        assert rc == 1
        assert "names no minted finding" in capsys.readouterr().err

    def test_main_accepts_argv_so_it_is_testable_in_process(self):
        import inspect
        assert "argv" in inspect.signature(rr.main).parameters
