#!/usr/bin/env python3
"""Show what `uv lock --upgrade` WOULD do, classified by risk. Writes nothing.

Dependency upgrades are how security fixes arrive. Skipping them is not free: this repo went
until 28 Dependabot alerts had piled up across 6 packages before anyone looked. But a blanket
`uv lock --upgrade` also moves everything at once -- pytest, scipy, and a package removal in
the same breath -- which is why it feels unsafe to run and therefore does not get run.

This makes the decision legible: removals and major bumps are the two classes that break
things, so they are separated from the routine ones and counted.

Removals are safe for anything we IMPORT -- tests/test_dependency_declaration.py enforces that
every imported module is declared, and the resolver cannot drop a declared package silently.
A removal here is therefore a package nothing in this repo imports. That is usually fine and
occasionally not: a pytest PLUGIN is activated by installation rather than import, so no
import scan sees it. Read the removal list with that one exception in mind.

    uv run python scripts/dep_upgrade_preview.py            # report, always exit 0
    uv run python scripts/dep_upgrade_preview.py --check    # exit 1 if anything is removed
"""
from __future__ import annotations

import argparse
import re
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent

UPDATE = re.compile(r"^Update (\S+) v(\S+) -> v(\S+)$")
REMOVE = re.compile(r"^Remove (\S+) v(\S+)$")
ADD = re.compile(r"^Add (\S+) v(\S+)$")


def _major(v: str) -> str:
    return v.split(".")[0]


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--check", action="store_true",
                    help="exit 1 if the upgrade would REMOVE a package")
    args = ap.parse_args()

    proc = subprocess.run(
        ["uv", "lock", "--upgrade", "--dry-run"],
        cwd=ROOT, capture_output=True, text=True,
    )
    if proc.returncode != 0:
        sys.stderr.write(proc.stderr or "uv lock --upgrade --dry-run failed\n")
        return proc.returncode

    removed: list[tuple[str, str]] = []
    added: list[tuple[str, str]] = []
    major: list[tuple[str, str, str]] = []
    minor: list[tuple[str, str, str]] = []

    for line in (proc.stdout + proc.stderr).splitlines():
        line = line.strip()
        if m := UPDATE.match(line):
            name, old, new = m.groups()
            (major if _major(old) != _major(new) else minor).append((name, old, new))
        elif m := REMOVE.match(line):
            removed.append(m.groups())
        elif m := ADD.match(line):
            added.append(m.groups())

    total = len(removed) + len(added) + len(major) + len(minor)
    if total == 0:
        print("uv lock --upgrade would change nothing — the lock is current.")
        return 0

    print(f"`uv lock --upgrade` would change {total} package(s). Nothing has been written.\n")

    if removed:
        print(f"REMOVED ({len(removed)}) — read these; the rest is routine")
        for name, ver in sorted(removed):
            print(f"    - {name} v{ver}")
        print("    Anything this repo imports is declared and cannot be dropped "
              "(tests/test_dependency_declaration.py).")
        print("    The gap that check cannot see is a pytest PLUGIN: activated by install, "
              "never imported.\n")

    if major:
        print(f"MAJOR version bump ({len(major)}) — API breakage lives here")
        for name, old, new in sorted(major):
            print(f"    ~ {name}  {old} -> {new}")
        print()

    if added:
        print(f"ADDED ({len(added)})")
        for name, ver in sorted(added):
            print(f"    + {name} v{ver}")
        print()

    print(f"minor/patch ({len(minor)}) — not listed; run "
          "`uv lock --upgrade --dry-run` for the full diff")
    print("\nTo apply:      uv lock --upgrade && uv sync --extra mlx")
    print("Then verify:   uv run python scripts/verify_scope.py")

    if args.check and removed:
        print(f"\n--check: {len(removed)} removal(s) — review before upgrading", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
