"""Regression guards for the skill/command/agent shell-invocation defects (incident 2026-06-17).

WHY THIS FILE EXISTS
====================
Four defects shipped in the initial harness build and broke it from the **workspace-root
launch** — which is a CORE requirement, not an edge case (spec §11 / §A.2 / §A.3 / §A.6), and is
also how a standalone/public user launches from inside the repo. Each defect was invisible to the
original tests because the tests exercised a *different* invocation than what shipped. These
deterministic content-scans of THIS plugin's markdown fail if any defect class regresses — no model
judgment, so they run in the fast suite / CI.

The four guarded defect classes:

  1. test_no_placeholder_shell_injection  —  the ``!`cmd`` `` bug.
     Claude Code's slash preprocessor executes ``!`<x>` `` injections BEFORE the skill is sent.
     A meta-reference like ``!`cmd` `` (a placeholder, not a real command) ran `cmd` →
     `command not found: cmd` → the whole skill aborted before its body was sent. GUARD: every
     ``!`…` `` injection in a skill/command must invoke a known command verb.

  2. test_repo_resolution_uses_repo_root_not_bare_git  —  the workspace-root UNRESOLVED bug.
     A skill/agent that resolved the repo via a bare `git rev-parse --show-toplevel` returns empty
     at the non-git workspace root → no marker armed → durability dead. GUARD: any file using
     `rev-parse --show-toplevel` must ALSO use the harness `repo_root()` resolver
     (`harness_common_cli.py repo-root`); git rev-parse is only ever a fallback.

  3. test_harness_scripts_run_under_uv_python_not_bare_python3  —  the wrong-interpreter bug.
     Bare `python3` here is the system 3.9.x; the project is uv-managed 3.14. Harness scripts must
     be invoked with `uv run --no-sync python` (yields 3.14 from ANY cwd, incl. the workspace root).
     GUARD: no `python3 "$CLI"` and no `python3 "${CLAUDE_PLUGIN_ROOT}/scripts/…` in skill/agent prose.

  4. test_project_scripts_cd_into_repo_before_uv_run  —  the uv-run-from-workspace-root bug.
     `uv run python <repo>/scripts/X` for a project-DEPENDENCY script runs an ephemeral interpreter
     WITHOUT the repo's deps (`src.core` etc. fail to import) from a non-repo cwd. GUARD: project
     scripts must be `cd "<repo>" && uv run …`; the bare `uv run python <repo>` form must not appear.

This file scans `Path(__file__).resolve().parent.parent` (i.e. THIS plugin), so the identical file
is dropped into both this QA plugin and its private sibling and guards each in place.

Run: uv run python -m pytest <plugin>/tests/test_skill_safety.py -v
"""
import re
from pathlib import Path

PLUGIN = Path(__file__).resolve().parent.parent
SKILLS_CMDS = sorted((PLUGIN / "skills").rglob("*.md")) + sorted((PLUGIN / "commands").glob("*.md"))
ALL_MD = SKILLS_CMDS + sorted((PLUGIN / "agents").glob("*.md"))

# Real command verbs a `!`…` ` pre-send injection may invoke. A placeholder like `cmd`
# (the 2026-06-17 bug) is intentionally NOT here, so it gets flagged.
KNOWN_CMDS = {"git", "ls", "test", "date", "echo", "uv", "head", "cd", "grep", "jq",
              "cat", "python", "python3", "true", "printf"}


def _injections(text):
    """CC pre-send shell injections: a `!` immediately followed by a backtick-delimited body."""
    return re.findall(r"!`([^`]+)`", text)


def test_files_present():
    """Sanity: the scan actually found skill/command files (a path typo would silently pass)."""
    assert SKILLS_CMDS, f"no skill/command markdown found under {PLUGIN}"


def test_no_placeholder_shell_injection():
    """Defect 1 — every pre-send `!`…`` injection must invoke a real command verb (catches `!`cmd``)."""
    offenders = []
    for md in SKILLS_CMDS:
        for inj in _injections(md.read_text()):
            words = set(re.findall(r"[a-z][a-z0-9_]*", inj.lower()))
            if not (words & KNOWN_CMDS):
                offenders.append(f"{md.relative_to(PLUGIN)}: !`{inj[:50]}`")
    assert not offenders, (
        "placeholder/meta-reference `!`…`` injection — it would execute as a shell command "
        "(the `!`cmd`` bug):\n  " + "\n  ".join(offenders))


def test_repo_resolution_uses_repo_root_not_bare_git():
    """Defect 2 — files resolving a repo via `rev-parse` must also use repo_root() (works at the workspace root)."""
    offenders = []
    for md in ALL_MD:
        t = md.read_text()
        if "rev-parse --show-toplevel" in t and 'harness_common_cli.py" repo-root' not in t:
            offenders.append(str(md.relative_to(PLUGIN)))
    assert not offenders, (
        "repo resolved via bare git rev-parse (empty at the non-git workspace root) without the "
        "harness repo_root() resolver:\n  " + "\n  ".join(offenders))


def test_harness_scripts_run_under_uv_python_not_bare_python3():
    """Defect 3 — harness scripts must run via `uv run --no-sync python` (3.14), not bare python3 (system 3.9.x)."""
    bad = ['python3 "$CLI"', 'python3 "${CLAUDE_PLUGIN_ROOT}/scripts/']
    offenders = []
    for md in ALL_MD:
        t = md.read_text()
        for b in bad:
            if b in t:
                offenders.append(f"{md.relative_to(PLUGIN)}: {b}")
    assert not offenders, (
        "harness script invoked with bare `python3` (system 3.9.x) instead of "
        "`uv run --no-sync python` (the project's 3.14):\n  " + "\n  ".join(offenders))


def test_project_scripts_cd_into_repo_before_uv_run():
    """Defect 4 — project-dep scripts must `cd \"<repo>\" && uv run`, not bare `uv run python <repo>`."""
    offenders = []
    for md in ALL_MD:
        if "uv run python <repo" in md.read_text():
            offenders.append(str(md.relative_to(PLUGIN)))
    assert not offenders, (
        "project-dependency script run via bare `uv run python <repo>` (no `cd` into the repo -> "
        "ephemeral env missing the repo's deps):\n  " + "\n  ".join(offenders))
