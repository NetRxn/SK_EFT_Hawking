"""Tests for the canonical workspace-root resolver (``src.core.workspace``).

Network-free and fast. Guards the single source of truth that replaced three
divergent ``LIT_SEARCH = ...`` derivations across scripts. The synthetic
``tmp_path`` cases exercise the resolution logic independent of the
environment; the real-workspace assertions skip gracefully in a standalone
clone (where there is no surrounding workspace).
"""
from __future__ import annotations

from pathlib import Path

import pytest

from src.core.workspace import find_workspace, lit_search_dir


def test_find_workspace_returns_existing_dir():
    ws = find_workspace()
    assert ws.is_dir()


def test_find_workspace_is_cwd_independent():
    """Default resolution keys off the module location, not the caller's cwd."""
    assert find_workspace() == find_workspace(start=Path(__file__))


def test_lit_search_dir_is_under_workspace():
    lit = lit_search_dir()
    assert lit == find_workspace() / "Lit-Search"
    assert lit.name == "Lit-Search"


def test_real_workspace_markers_when_present():
    """When run inside the dev workspace, the resolved root carries the markers."""
    ws = find_workspace()
    if not (ws / ".mcp.json").is_file():
        pytest.skip("not running inside the dev workspace (standalone clone)")
    assert (ws / "SK_EFT_Hawking").is_dir()
    assert not (ws / ".git").exists()


def test_sentinel_takes_precedence(tmp_path: Path):
    """An explicit ``.workspace-root`` sentinel pins the root unambiguously."""
    (tmp_path / ".workspace-root").write_text("")
    deep = tmp_path / "a" / "b" / "c"
    deep.mkdir(parents=True)
    assert find_workspace(start=deep) == tmp_path


def test_structural_detection_without_sentinel(tmp_path: Path):
    """Falls back to structural markers: .mcp.json + SK_EFT_Hawking/ + no .git."""
    ws = tmp_path / "ws"
    (ws / "SK_EFT_Hawking" / "src").mkdir(parents=True)
    (ws / ".mcp.json").write_text("{}")
    assert find_workspace(start=ws / "SK_EFT_Hawking" / "src") == ws


def test_git_dir_excludes_candidate(tmp_path: Path):
    """A candidate carrying ``.git`` is rejected; resolution climbs past it."""
    outer = tmp_path / "outer"
    inner = outer / "proj"
    (inner / "SK_EFT_Hawking").mkdir(parents=True)
    (inner / ".mcp.json").write_text("{}")
    (inner / ".git").mkdir()  # inner is itself a git repo -> not the workspace
    (outer / "SK_EFT_Hawking").mkdir(parents=True)
    (outer / ".mcp.json").write_text("{}")
    assert find_workspace(start=inner / "SK_EFT_Hawking") == outer


def test_worktree_layout_resolves_to_outer_workspace(tmp_path: Path):
    """Regression (B-01 worktree-path bug): resolution from inside a git
    worktree — nested at ``SK_EFT_Hawking/.claude/worktrees/wtN/`` — must
    reach the OUTER workspace, not the intermediate ``.claude/worktrees``.

    A naive ``__file__.parent × 3`` walk from ``wtN/tests`` lands on
    ``.claude/worktrees`` (which has no ``Lit-Search/``); ``find_workspace``
    must instead climb past the nesting to the real workspace root.
    """
    ws = tmp_path / "ws"
    repo = ws / "SK_EFT_Hawking"
    worktree = repo / ".claude" / "worktrees" / "wt3"
    (worktree / "src" / "core").mkdir(parents=True)
    (worktree / "tests").mkdir(parents=True)
    # Realistic git markers: the main repo carries a .git DIR; a worktree
    # carries a .git FILE. Neither must be mistaken for the workspace.
    (repo / ".git").mkdir()
    (worktree / ".git").write_text("gitdir: ../../..\n")
    # Only the true workspace carries the shared .mcp.json + repo child.
    (ws / ".mcp.json").write_text("{}")
    # Resolution from both a src module and a test file inside the worktree.
    assert find_workspace(start=worktree / "src" / "core") == ws
    assert find_workspace(start=worktree / "tests" / "test_x.py") == ws
    assert lit_search_dir(start=worktree / "tests") == ws / "Lit-Search"


def test_main_and_worktree_layouts_agree(tmp_path: Path):
    """The resolver returns the SAME workspace whether called from the main
    checkout or a worktree nested under it — behaviour is layout-independent
    (the acceptance requirement for the B-01 test-hygiene fix)."""
    ws = tmp_path / "ws"
    repo = ws / "SK_EFT_Hawking"
    (repo / "src" / "core").mkdir(parents=True)
    (repo / ".git").mkdir()
    worktree = repo / ".claude" / "worktrees" / "wt3"
    (worktree / "src" / "core").mkdir(parents=True)
    (worktree / ".git").write_text("gitdir: ../../..\n")
    (ws / ".mcp.json").write_text("{}")
    from_main = find_workspace(start=repo / "src" / "core")
    from_worktree = find_workspace(start=worktree / "src" / "core")
    assert from_main == from_worktree == ws
