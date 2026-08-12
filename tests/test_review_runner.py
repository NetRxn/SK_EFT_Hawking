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

    def test_a_WORKSPACE_level_target_resolves(self):
        """⚠️ `temporary/working-docs/...` lives in the workspace that HOLDS this repo, not
        inside it. Resolving only from the repo root reported those files as stale — the
        same false-staleness defect the `papers/` root was added to fix, one directory
        further out. Found because an adjudicator cited content from a file the repo-root
        resolver said did not exist, and the file was real."""
        ws = rr._workspace_root()
        if ws is None or ws == rr.PROJECT_ROOT:
            pytest.skip("not running inside a multi-repo workspace")
        probe = "temporary/working-docs/phase6q/wave_2c_positioning.md"
        if not (ws / probe).is_file():
            pytest.skip(f"{probe} is not present in this workspace")
        path, tried = rr._resolve_target(probe + ":29")
        assert path is not None, f"resolved against none of {tried}"
        assert path.is_file()

    def test_the_workspace_root_comes_from_find_workspace(self):
        """Never a hardcoded parent-walk — that is the repo convention, and a parent-walk
        breaks in a worktree.

        ⚠️ ASSERTS THE CALL VIA `ast`, NOT A SUBSTRING. `CHECK_AUTHORING_GUIDE.md` §2.5: "a
        guard that asserts a helper is called by searching the source finds the name in a
        COMMENT and passes over a seeded regression." This test's first draft did exactly
        that — and this docstring, which names `find_workspace`, would itself have satisfied
        it.
        """
        import ast
        tree = ast.parse(Path(rr.__file__).read_text(encoding="utf-8"))
        fn = next(n for n in ast.walk(tree)
                  if isinstance(n, ast.FunctionDef) and n.name == "_workspace_root")
        called = {
            (c.func.id if isinstance(c.func, ast.Name) else
             c.func.attr if isinstance(c.func, ast.Attribute) else None)
            for c in ast.walk(fn) if isinstance(c, ast.Call)
        }
        assert "find_workspace" in called, (
            f"_workspace_root does not CALL find_workspace; it calls {sorted(x for x in called if x)}")

    def test_an_unresolvable_target_NAMES_WHAT_IT_TRIED(self):
        """'Does not resolve' plus the paths tried is a measurement. Alone it is a verdict
        the reader cannot check."""
        path, tried = rr._resolve_target("no/such/file.tex:12")
        assert path is None
        # Repo root, then `papers/`, then the workspace root when there is one. The
        # workspace candidate is shown ABSOLUTE because it lies outside the repo.
        assert tried[:2] == ["no/such/file.tex", "papers/no/such/file.tex"]
        ws = rr._workspace_root()
        if ws is not None and ws != rr.PROJECT_ROOT:
            assert tried[2] == str(ws / "no/such/file.tex")
        else:
            assert len(tried) == 2

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
