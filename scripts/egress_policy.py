#!/usr/bin/env python3
"""Add a domain to the web-egress whitelist, and push it to every running install.

WHY A COMMAND. Widening egress is a five-step ritual — edit the plugin SOURCE, verify,
commit, refresh EVERY install record, restart — and every step has a silent failure mode
we have already hit:

  * Editing the cache instead of the source: reverted by the next refresh, diverges meanwhile.
  * Forgetting a step: measured 2026-08-15, six committed domains sat un-refreshed while the
    session served a cache three commits old. A RESTART DOES NOT REFRESH — the cache is keyed
    by the committed HEAD SHA and only `claude plugin update` moves it.
  * Refreshing one install record: this plugin has one record PER LAUNCH POINT (the workspace
    root, for Lit-Search work, and the repo itself). `claude plugin update` only touches the
    record for the current cwd, so a one-directory refresh leaves the other launch point stale.
    This script discovers the records from `installed_plugins.json` rather than assuming two,
    so it is correct for a single-repo install as well as this workspace layout.
  * Granting in the wrong file: `permissions.allow` cannot confer egress. Only `_WHITELIST`
    can. `data-star.dev` sat granted-and-unreachable for months exactly that way.

Usage:
    uv run python scripts/egress_policy.py add <domain> --for "<what needs it>" [--path /prefix]
    uv run python scripts/egress_policy.py sync           # refresh every install from HEAD
    uv run python scripts/egress_policy.py status         # what is live vs committed vs source

`add` refuses a domain that is already covered (including by a parent entry, since matching is
subdomain-aware), refuses anything that is not a bare registrable host, and — for code-hosting
hosts, which serve arbitrary user content — refuses a bare host entry outright and directs you
to `--path`. It verifies by IMPORTING the edited guard and asserting the domain resolves, so a
malformed edit fails here rather than at the next fetch.
"""
from __future__ import annotations

import argparse
import importlib.util
import json
import os
import re
import subprocess
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
GUARD = REPO / ".claude" / "plugins" / "skeft-qa" / "scripts" / "harness_web_egress_guard.py"
INSTALLED = Path.home() / ".claude" / "plugins" / "installed_plugins.json"
PLUGIN = "skeft-qa@skeft-local"

#: Hosts that serve arbitrary user-controlled content. A bare entry for one of these is a far
#: broader grant than any lookup needs, so they are path-scoped or not at all.
_CODE_HOSTS = {"github.com", "raw.githubusercontent.com", "gitlab.com", "bitbucket.org",
               "gist.github.com", "codeberg.org", "sourceforge.net", "hub.docker.com"}

_HOST_RE = re.compile(r"^(?!-)[a-z0-9-]+(\.[a-z0-9-]+)+$")


def _load_guard(path: Path = GUARD):
    spec = importlib.util.spec_from_file_location("_egress_guard_probe", path)
    mod = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(mod)
    return mod


def _covered(host: str, whitelist) -> str | None:
    """The entry already covering `host`, if any — matching the guard's own subdomain rule."""
    for entry in whitelist:
        if host == entry or host.endswith("." + entry):
            return entry
    return None


def _install_records() -> list[Path]:
    if not INSTALLED.is_file():
        return []
    data = json.loads(INSTALLED.read_text())
    return [Path(r["projectPath"]) for r in data.get("plugins", {}).get(PLUGIN, [])
            if Path(r["projectPath"]).is_dir()]


def _live_sha() -> dict[str, str]:
    if not INSTALLED.is_file():
        return {}
    data = json.loads(INSTALLED.read_text())
    return {r["projectPath"]: Path(r["installPath"]).name
            for r in data.get("plugins", {}).get(PLUGIN, [])}


def _run(cmd: list[str], cwd: Path) -> tuple[int, str]:
    p = subprocess.run(cmd, cwd=str(cwd), capture_output=True, text=True)
    return p.returncode, (p.stdout + p.stderr).strip()


def cmd_status(_args) -> int:
    head, _ = _run(["git", "rev-parse", "HEAD"], REPO)
    head = _run(["git", "rev-parse", "HEAD"], REPO)[1][:12]
    dirty = _run(["git", "status", "--porcelain", str(GUARD.relative_to(REPO))], REPO)[1]
    print(f"guard source        : {'MODIFIED, uncommitted' if dirty else 'clean'}")
    print(f"repo HEAD           : {head}")
    print(f"whitelist entries   : {len(_load_guard()._WHITELIST)} (source)")
    print("install records:")
    stale = False
    for proj, sha in _live_sha().items():
        mark = "current" if sha.startswith(head[:8]) or head.startswith(sha[:8]) else "STALE"
        if mark == "STALE":
            stale = True
        print(f"  {mark:8} {sha}  {proj}")
    if dirty or stale:
        print("\nRun `egress_policy.py sync` (commit first if the source is modified).")
    return 1 if (dirty or stale) else 0


def cmd_sync(args) -> int:
    dirty = _run(["git", "status", "--porcelain", str(GUARD.relative_to(REPO))], REPO)[1]
    if dirty:
        print("REFUSING: the guard source has uncommitted changes. The plugin cache is keyed "
              "by the committed HEAD SHA, so an unsynced edit would be silently skipped.\n"
              "Commit it, then re-run sync.")
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
        last = out.splitlines()[-1] if out else f"rc={rc}"
        print(f"  [{proj.name}] {last}")
        if rc != 0:
            failed.append(proj)
    if failed:
        print(f"\nFAILED for: {', '.join(p.name for p in failed)}")
        return 1
    print("\nAll install records refreshed. RESTART Claude Code to apply "
          "(a refresh alone does not reload the running hooks).")
    return 0


def cmd_add(args) -> int:
    host = args.domain.strip().lower().removeprefix("https://").removeprefix("http://").rstrip("/")
    if not _HOST_RE.match(host):
        print(f"REFUSING: {host!r} is not a bare registrable host (no scheme, no path, no port).")
        return 1
    if host in _CODE_HOSTS and not args.path:
        print(f"REFUSING: {host} serves arbitrary user-controlled content. A bare host entry is "
              f"a far broader grant than a lookup needs.\nUse --path /owner/repo to scope it.")
        return 1

    mod = _load_guard()
    existing = _covered(host, mod._WHITELIST)
    if existing and not args.path:
        print(f"ALREADY COVERED: {host} matches whitelist entry {existing!r} "
              f"(matching is subdomain-aware). No change needed.")
        return 0

    text = GUARD.read_text()
    if args.path:
        anchor = "_PATH_WHITELIST = ("
        entry = (f'    ("{host}", "{args.path}"),'
                 f'  # {args.reason} (added {args.date})\n')
        idx = text.index(anchor) + len(anchor) + 1
        text = text[:idx] + entry + text[idx:]
    else:
        anchor = "\n)\n\n# Path-scoped destinations:"
        entry = (f'    # {args.reason} (added {args.date})\n    "{host}",')
        text = text.replace(anchor, f"\n{entry}{anchor}", 1)
    GUARD.write_text(text)

    # READ BACK: import the edited guard and assert the grant actually resolves. A regex edit
    # that lands in a comment or a neighbouring literal would otherwise pass silently.
    try:
        fresh = _load_guard()
    except Exception as exc:
        print(f"EDIT BROKE THE GUARD ({type(exc).__name__}: {exc}). Reverting.")
        _run(["git", "checkout", "--", str(GUARD.relative_to(REPO))], REPO)
        return 1
    ok = (_covered(host, fresh._WHITELIST) if not args.path
          else any(h == host and p == args.path for h, p in fresh._PATH_WHITELIST))
    if not ok:
        print("EDIT DID NOT TAKE — the domain is not resolvable after the write. Reverting.")
        _run(["git", "checkout", "--", str(GUARD.relative_to(REPO))], REPO)
        return 1

    rc, out = _run([sys.executable, "-m", "pytest", "-q", "-k", "egress or whitelist"], REPO)
    print(out.splitlines()[-1] if out else "")
    if rc != 0:
        print("EGRESS TESTS FAILED. Reverting.")
        _run(["git", "checkout", "--", str(GUARD.relative_to(REPO))], REPO)
        return 1

    print(f"\nAdded {host}{' ' + args.path if args.path else ''} to the "
          f"{'path ' if args.path else ''}whitelist.")
    print("Next: commit the guard, then `egress_policy.py sync`, then restart.")
    return 0


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = ap.add_subparsers(dest="cmd", required=True)
    a = sub.add_parser("add", help="add a domain to the whitelist")
    a.add_argument("domain")
    a.add_argument("--for", dest="reason", required=True,
                   help="what needs it — name the TARGET, so the grant can be retired later")
    a.add_argument("--path", help="scope to a path prefix (required for code hosts)")
    a.add_argument("--date", default=os.environ.get("EGRESS_DATE", ""),
                   help="authorizing date (YYYY-MM-DD); grants must be datable to be audited")
    a.set_defaults(func=cmd_add)
    sub.add_parser("sync", help="refresh every install record from HEAD").set_defaults(func=cmd_sync)
    sub.add_parser("status", help="what is live vs committed vs source").set_defaults(func=cmd_status)
    args = ap.parse_args()
    if args.cmd == "add" and not args.date:
        print("REFUSING: --date is required (or set EGRESS_DATE). An undated grant cannot be audited.")
        return 1
    return args.func(args)


if __name__ == "__main__":
    raise SystemExit(main())
