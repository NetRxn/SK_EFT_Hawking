"""Surface-vs-README synchronization guards (ADR-011 Phase 8).

WHY THIS FILE EXISTS
====================
The README is this plugin's map: it is what an operator (and a fresh agent) reads to learn what
ships. Every component here is auto-discovered by Claude Code from the filesystem, so a new agent,
command, hook, or skill goes LIVE the moment its file lands -- with nothing forcing the README to
follow. The result measured at ADR-011 Phase 8: the README documented 4 of 9 agents, 4 of 6
commands, and 4 of 5 hooks, and asserted a safety posture ("all default-inert + fail-open") that was
false for the one hook it had never been updated to mention -- the fail-CLOSED web-egress guard.

A one-time sync does not fix that; it re-rots on the next component. These scans make the drift a
test failure at the moment it is introduced. No model judgment, so they run in the fast suite.

The guarded defect classes:

  1. test_every_agent_is_documented        -- an agent ships undocumented.
  2. test_every_command_is_documented      -- a command ships undocumented.
  3. test_every_skill_is_documented        -- a skill ships undocumented.
  4. test_every_hook_script_is_documented  -- a hook ships undocumented.
  5. test_readme_hook_count_matches        -- the README's spelled-out hook count goes stale.
  6. test_plugin_root_paths_resolve        -- a `${CLAUDE_PLUGIN_ROOT}/...` reference rots.
  7. test_bare_script_paths_are_unambiguous-- `scripts/<name>.py` prose that resolves under neither root
     from the cwd a reader would use (the plugin has a scripts/ dir AND so does the repo).
  8. test_agents_declare_an_explicit_model -- an agent omits `model:` and silently inherits.
  9. test_model_invocable_skills_use_third_person -- a model-invocable skill's description lacks the
     third-person trigger form, which is what the model matches on to decide to load it.

This file scans `Path(__file__).resolve().parent.parent` (i.e. THIS plugin), so the identical file
guards the private sibling plugin in place.

RELATION TO `tests/test_plugin_prompt_code_refs.py` (repo-side) -- NOT a duplicate. That test
accepts a bare `scripts/<name>.py` resolving under EITHER root, which is deliberately permissive.
Defect 7 here is stricter for prose files: a plugin-only script written bare satisfies that test
and still gives a reader standing at the repo root a file-not-found. Keep both; the repo-side one
is the broader net, this one is the sharper rule on the prose surface an agent follows literally.
(That test also enforces that any `scripts/...`-shaped string in a plugin file must resolve, which
is why placeholders in this file are written `scripts/<name>.py` rather than a real-looking path.)

Run: uv run python -m pytest <plugin>/tests/test_plugin_surface.py -v
"""
import json
import re
from pathlib import Path

PLUGIN = Path(__file__).resolve().parent.parent
# .claude/plugins/<name>/ -> repo root is three levels up.
REPO = PLUGIN.parents[2]
README = (PLUGIN / "README.md").read_text()
HOOKS = json.loads((PLUGIN / "hooks/hooks.json").read_text())

# Markdown that a human/agent reads for instructions (prose surface), excluding the README itself.
PROSE_MD = (sorted((PLUGIN / "skills").rglob("*.md"))
            + sorted((PLUGIN / "commands").glob("*.md"))
            + sorted((PLUGIN / "agents").glob("*.md")))

NUM_WORDS = {1: "one", 2: "two", 3: "three", 4: "four", 5: "five", 6: "six",
             7: "seven", 8: "eight", 9: "nine", 10: "ten"}


def _frontmatter(md: Path) -> str:
    t = md.read_text()
    if not t.startswith("---"):
        return ""
    return t[3:t.index("\n---", 3)]


def _hook_scripts():
    """Every plugin script a hook actually invokes."""
    return sorted(set(re.findall(r"\$\{CLAUDE_PLUGIN_ROOT\}/scripts/([A-Za-z0-9._-]+\.(?:py|sh))",
                                 json.dumps(HOOKS))))


# ---------------------------------------------------------------- seam guards

def test_populations_are_non_empty():
    """Guard the seam: a path typo here would make every scan below pass vacuously."""
    assert sorted((PLUGIN / "agents").glob("*.md")), f"no agents found under {PLUGIN}"
    assert sorted((PLUGIN / "commands").glob("*.md")), f"no commands found under {PLUGIN}"
    assert [d for d in (PLUGIN / "skills").iterdir() if d.is_dir()], f"no skills under {PLUGIN}"
    assert _hook_scripts(), "no hook scripts parsed out of hooks.json"
    assert README.strip(), "README.md is empty"
    assert (REPO / "scripts").is_dir(), (
        f"repo root misresolved: {REPO} has no scripts/ dir "
        "(test_bare_script_paths_are_unambiguous would pass vacuously)")


# ---------------------------------------------------- surface-vs-README sync

def test_every_agent_is_documented():
    """Defect 1 -- an agent that ships undocumented is one no operator knows to invoke."""
    missing = [a.stem for a in sorted((PLUGIN / "agents").glob("*.md")) if a.stem not in README]
    assert not missing, (
        "agent ships but is absent from README.md:\n  " + "\n  ".join(missing))


def test_every_command_is_documented():
    """Defect 2 -- same, for slash commands."""
    missing = [c.stem for c in sorted((PLUGIN / "commands").glob("*.md")) if c.stem not in README]
    assert not missing, (
        "command ships but is absent from README.md:\n  " + "\n  ".join(missing))


def test_every_skill_is_documented():
    """Defect 3 -- same, for skills."""
    missing = [d.name for d in sorted((PLUGIN / "skills").iterdir())
               if d.is_dir() and (d / "SKILL.md").exists() and d.name not in README]
    assert not missing, (
        "skill ships but is absent from README.md:\n  " + "\n  ".join(missing))


def test_every_hook_script_is_documented():
    """Defect 4 -- the measured case: the fail-CLOSED egress guard shipped undocumented, under a
    README sentence asserting every hook was fail-OPEN."""
    missing = [s for s in _hook_scripts() if s not in README]
    assert not missing, (
        "hook script is wired in hooks.json but absent from README.md -- the README's description "
        "of the hook surface (including its fail-open/fail-closed posture) cannot be trusted while "
        "a hook is missing from it:\n  " + "\n  ".join(missing))


def test_readme_hook_count_matches():
    """Defect 5 -- a spelled-out count in the README goes stale the moment a hook is added."""
    actual = sum(len(e.get("hooks", [])) for entries in HOOKS.get("hooks", {}).values()
                 for e in entries)
    # The dash before the count may be an em-dash or ASCII hyphens; accept either.
    m = re.search(r"###\s*Hooks\b[^\n]*?(?:--+|—)\s*([a-z]+)\b", README)
    assert m, ("README has no '### Hooks ... -- <count>' heading to check; if the heading was "
               "reworded, update this guard rather than deleting it")
    claimed = m.group(1)
    assert claimed == NUM_WORDS.get(actual), (
        f"README's Hooks heading claims '{claimed}' hooks; hooks.json wires {actual} "
        f"('{NUM_WORDS.get(actual)}')")


# ------------------------------------------------------------- path integrity

def test_plugin_root_paths_resolve():
    """Defect 6 -- a `${CLAUDE_PLUGIN_ROOT}/...` reference that no longer resolves."""
    offenders = []
    for md in PROSE_MD + [PLUGIN / "README.md", PLUGIN / "hooks/hooks.json"]:
        for ref in re.findall(r"\$\{CLAUDE_PLUGIN_ROOT\}/([A-Za-z0-9._/-]+)", md.read_text()):
            if not (PLUGIN / ref).exists():
                offenders.append(f"{md.relative_to(PLUGIN)}: {ref}")
    assert not offenders, (
        "`${CLAUDE_PLUGIN_ROOT}` path does not resolve:\n  " + "\n  ".join(offenders))


def test_bare_script_paths_are_unambiguous():
    """Defect 7 -- BOTH the plugin and the repo have a `scripts/` dir, so a bare `scripts/<name>.py` in
    prose is ambiguous. It must resolve under the repo (the cwd a reader is in); a plugin script
    must be written `${CLAUDE_PLUGIN_ROOT}/scripts/<name>.py` or `<plugin>/scripts/<name>.py` so the reader
    does not get file-not-found running it from the repo root."""
    offenders = []
    for md in PROSE_MD:
        for m in re.finditer(r"(?<![\w/${.-])scripts/([A-Za-z0-9._-]+\.(?:py|sh))", md.read_text()):
            rel = f"scripts/{m.group(1)}"
            if (REPO / rel).exists():
                continue
            hint = (" -- exists only under the PLUGIN; write it as "
                    "`${CLAUDE_PLUGIN_ROOT}/scripts/...`") if (PLUGIN / rel).exists() else ""
            offenders.append(f"{md.relative_to(PLUGIN)}: {rel}{hint}")
    assert not offenders, (
        "bare `scripts/...` reference does not resolve from the repo root:\n  "
        + "\n  ".join(offenders))


# ---------------------------------------------------------- frontmatter rules

def test_agents_declare_an_explicit_model():
    """Defect 8 -- an agent with no `model:` silently inherits whatever the caller happens to be
    running, so its cost/capability is set by accident. `inherit` is a valid explicit choice;
    omission is not."""
    missing = [a.stem for a in sorted((PLUGIN / "agents").glob("*.md"))
               if not re.search(r"^model:", _frontmatter(a), re.M)]
    assert not missing, (
        "agent frontmatter omits `model:` (state it explicitly -- `inherit` is a valid value):\n  "
        + "\n  ".join(missing))


def test_model_invocable_skills_use_third_person():
    """Defect 9 -- a model-invocable skill's description is what the model matches on to decide
    whether to load it. The third-person trigger form ('This skill should be used when ...') is what
    the plugin-dev skill-development criteria require. Skills carrying
    `disable-model-invocation: true` are exempt: their description is never matched, it is a
    human-facing label.

    Whitespace is normalized first: a folded-YAML (`description: >`) block wraps the description
    across lines, so a raw substring match splits the very phrase it is looking for."""
    offenders = []
    for s in sorted((PLUGIN / "skills").glob("*/SKILL.md")):
        head = _frontmatter(s)
        if "disable-model-invocation: true" in head:
            continue
        flat = " ".join(head.lower().split())
        if "this skill should be used" not in flat:
            offenders.append(s.parent.name)
    assert not offenders, (
        "model-invocable skill description lacks the third-person trigger form "
        "('This skill should be used when the user asks to \"...\"'):\n  " + "\n  ".join(offenders))
