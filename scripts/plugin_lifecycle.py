#!/usr/bin/env python3
"""The `skeft-qa` plugin's bind/refresh lifecycle — status, sync, and the mid-flight delta.

A Claude Code session resolves `--plugin-dir` ONCE, at process start, from
`installed_plugins.json`. Editing `.claude/plugins/skeft-qa/` changes the SOURCE; the bound copy
is a cache keyed by the committed HEAD SHA. So a long-running session executes whatever the
plugin was when it started, however far the repo has moved since.

**A RESTART ALONE DOES NOT REFRESH.** The install record still points at the old SHA, so a restart
re-binds the same stale cache. Only `sync` moves the record; the restart then binds what it points
at. That ordering is the whole operational content of this module.

This lives in `scripts/` and NOT in the plugin, deliberately: a detector shipped inside the plugin
inherits the staleness it exists to detect, and would be as stale as the thing it is reporting on.

Three failure modes this exists to prevent, each measured here:

  * **Refreshing one install record.** The plugin has one record PER LAUNCH POINT — the workspace
    root and the repo. `claude plugin update` touches only the record for the current cwd, so a
    one-directory refresh leaves the other launch point stale. Records are discovered from
    `installed_plugins.json` rather than assumed, so this is correct for a single-repo install too.
  * **Editing the cache instead of the source.** Reverted by the next refresh, and divergent
    meanwhile.
  * **Syncing with the source uncommitted.** The cache is keyed by the COMMITTED HEAD, so an
    uncommitted edit is silently skipped by a refresh that reports success.

⚠️ `sync` asserts the DECIDER — is any plugin source uncommitted? — over the whole
`.claude/plugins/skeft-qa/` tree. Keying that check on one file (as the egress-scoped predecessor
did) is wrong for every edit outside it: a modified agent definition or skill reference passes the
guard and is then skipped by the refresh it was supposed to block.

Usage:
    uv run python scripts/plugin_lifecycle.py status   # bound vs committed, per install record
    uv run python scripts/plugin_lifecycle.py sync     # refresh every record from HEAD
    uv run python scripts/plugin_lifecycle.py delta    # what the RUNNING session cannot see

`delta` is the mid-flight half. A long `/goal` run cannot restart, so plugin improvements authored
during it are inert until it ends. `delta` renders the current text of every changed agent, skill
and reference to a stable path a dispatch brief can cite by absolute path, letting a lead hand a
subagent the guidance its own definition lacks. It emits nothing when the SHAs agree, so a brief
carries the pointer only when there is something to point at.

⚠️ Hooks bind at start and execute outside any prompt. A stale guard stays stale until restart, and
no amendment document can reach it — `delta` says so rather than implying full coverage.
"""
from __future__ import annotations

import argparse
import json
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
PLUGIN_SRC = REPO / ".claude" / "plugins" / "skeft-qa"
INSTALLED = Path.home() / ".claude" / "plugins" / "installed_plugins.json"
PLUGIN = "skeft-qa@skeft-local"

#: Where `delta` writes. Absolute, inside the main checkout, so an agent in a worktree can read it.
DELTA_DOC = REPO / "docs" / "dev-loops" / "PLUGIN_DELTA.md"

#: Component trees whose content is delivered to an agent through a PROMPT, and can therefore be
#: amended mid-flight by citing the rendered delta. Everything else (hooks, scripts) binds at
#: process start and cannot.
_PROMPT_DELIVERED = ("agents/", "skills/", "commands/")


def _run(cmd: list[str], cwd: Path) -> tuple[int, str]:
    p = subprocess.run(cmd, cwd=str(cwd), capture_output=True, text=True)
    return p.returncode, (p.stdout + p.stderr).strip()


def _install_records() -> list[Path]:
    """Every project path with an install record for this plugin. Discovered, never assumed."""
    if not INSTALLED.is_file():
        return []
    data = json.loads(INSTALLED.read_text())
    return [Path(r["projectPath"]) for r in data.get("plugins", {}).get(PLUGIN, [])
            if Path(r["projectPath"]).is_dir()]


def _bound_shas() -> dict[str, str]:
    """projectPath -> the cache SHA that path's record currently points at."""
    if not INSTALLED.is_file():
        return {}
    data = json.loads(INSTALLED.read_text())
    return {r["projectPath"]: Path(r["installPath"]).name
            for r in data.get("plugins", {}).get(PLUGIN, [])}


def _plugin_head() -> str:
    """The last commit touching plugin SOURCE — what a refresh would bind."""
    return _run(["git", "log", "-1", "--format=%H", "--", str(PLUGIN_SRC.relative_to(REPO))], REPO)[1]


def _plugin_dirty() -> str:
    """⚠️ THE DECIDER: is any plugin source uncommitted? Not: is one chosen file uncommitted."""
    return _run(["git", "status", "--porcelain", str(PLUGIN_SRC.relative_to(REPO))], REPO)[1]


def _is_current(bound: str, head: str) -> bool:
    """Cache dirs are SHA-prefixed; compare on the shorter of the two prefixes."""
    if not bound or not head:
        return False
    n = min(len(bound), len(head))
    return bound[:n] == head[:n]


def cmd_status(_args) -> int:
    head = _plugin_head()
    dirty = _plugin_dirty()
    print(f"plugin source   : {'MODIFIED, uncommitted' if dirty else 'clean'}")
    print(f"plugin HEAD     : {head[:12]}")
    stale = False
    print("install records :")
    for proj, bound in _bound_shas().items():
        current = _is_current(bound, head)
        stale = stale or not current
        print(f"  {'current' if current else 'STALE  '}  {bound}  {proj}")
    if dirty:
        print("\nCommit the plugin source first — the cache is keyed by the committed HEAD,\n"
              "so an uncommitted edit is skipped by a refresh that still reports success.")
    elif stale:
        print("\nRun `plugin_lifecycle.py sync`, then RESTART. A restart alone re-binds the same\n"
              "stale cache; only sync moves the record.")
    return 1 if (dirty or stale) else 0


def cmd_sync(_args) -> int:
    dirty = _plugin_dirty()
    if dirty:
        print("REFUSING: plugin source has uncommitted changes. The cache is keyed by the "
              "committed HEAD SHA,\nso those edits would be silently skipped by this refresh.\n"
              "Commit them, then re-run sync.\n")
        print(dirty)
        return 1
    records = _install_records()
    if not records:
        print(f"No install records for {PLUGIN}. Nothing to refresh.")
        return 0
    rc, out = _run(["claude", "plugin", "marketplace", "update"], records[0])
    print(f"marketplace update: {out.splitlines()[-1] if out else rc}")
    failed = []
    for proj in records:
        rc, out = _run(["claude", "plugin", "update", PLUGIN, "--scope", "local"], proj)
        print(f"  [{proj.name}] {out.splitlines()[-1] if out else f'rc={rc}'}")
        if rc != 0:
            failed.append(proj)
    if failed:
        print(f"\nFAILED for: {', '.join(p.name for p in failed)}")
        return 1
    print("\nAll install records refreshed. RESTART Claude Code to apply — a refresh alone does "
          "not\nreload the running session's agents, skills or hooks.")
    return 0


def _changed_since(bound_sha: str) -> list[str]:
    """Plugin files changed between the bound cache SHA and HEAD, repo-relative."""
    rc, out = _run(["git", "diff", "--name-only", f"{bound_sha}..HEAD", "--",
                    str(PLUGIN_SRC.relative_to(REPO))], REPO)
    return [ln for ln in out.splitlines() if ln.strip()] if rc == 0 else []


def cmd_delta(args) -> int:
    head = _plugin_head()
    bound = sorted({s for s in _bound_shas().values()})
    if not bound:
        print("No install record — nothing bound, so no delta.")
        return 0
    # Records may disagree (one launch point refreshed, the other not). Render against the most
    # stale of them, so the delta covers every session regardless of which record it bound.
    oldest = sorted(bound)[0]
    if all(_is_current(b, head) for b in bound):
        if DELTA_DOC.exists():
            DELTA_DOC.unlink()
        print(f"No delta: every install record is at plugin HEAD {head[:12]}.")
        return 0

    changed = _changed_since(oldest)
    if not changed:
        print(f"Records report {oldest}, but no plugin file differs from HEAD. Nothing to render.")
        return 0

    amendable = [f for f in changed if any(k in f for k in _PROMPT_DELIVERED)]
    bind_only = [f for f in changed if f not in amendable]

    lines = [
        "# Plugin delta — guidance the RUNNING session is not executing",
        "",
        "**Derived; do not edit.** Regenerate with `uv run python scripts/plugin_lifecycle.py delta`.",
        "It is emptied automatically once the bound cache reaches plugin HEAD.",
        "",
        f"Bound cache `{oldest}` · plugin HEAD `{head[:12]}`",
        "",
        "A session binds its plugin at process start. The files below changed afterwards, so the "
        "agents and skills this session dispatches do not carry them.",
        "",
        "## How a lead uses this",
        "",
        "Cite this file to a subagent **by absolute path** and instruct it to treat the section for "
        "its own definition as an amendment that supersedes its loaded instructions. A subagent's "
        "system prompt cannot be changed mid-flight; its prompt can.",
        "",
    ]
    if bind_only:
        lines += [
            "## ⚠️ Not amendable — these bind at process start",
            "",
            "Hooks and scripts execute outside any prompt, so no citation reaches them. They stay "
            "stale until a sync + restart:",
            "",
        ] + [f"- `{f}`" for f in bind_only] + [""]
    if amendable:
        lines += ["## Current text of each changed component", ""]
        for f in amendable:
            p = REPO / f
            lines += [f"### `{f}`", ""]
            if p.is_file():
                lines += ["```markdown", p.read_text(encoding="utf-8", errors="replace").rstrip(), "```", ""]
            else:
                lines += ["*(deleted at HEAD — the loaded copy should no longer be relied on)*", ""]

    DELTA_DOC.parent.mkdir(parents=True, exist_ok=True)
    DELTA_DOC.write_text("\n".join(lines) + "\n")
    print(f"Delta rendered: {DELTA_DOC.relative_to(REPO)}")
    print(f"  {len(amendable)} prompt-delivered component(s) amendable by citation")
    print(f"  {len(bind_only)} bind-at-start file(s) that a citation CANNOT reach")
    return 1


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    sub.add_parser("status", help="bound vs committed, per install record").set_defaults(func=cmd_status)
    sub.add_parser("sync", help="refresh every install record from HEAD").set_defaults(func=cmd_sync)
    sub.add_parser("delta", help="render guidance the running session cannot see").set_defaults(func=cmd_delta)
    args = ap.parse_args()
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
