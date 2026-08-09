#!/usr/bin/env python3
"""
check_bundle_source_freshness.py — Phase 7a sub-wave 7a.1.4 deliverable
=======================================================================

Implementation of `validate.py --check bundle_source_freshness` (CHECK 22).

For every bundle directory under `papers/<bundle>/`:

  - Read `bundle_metadata.json` to find `last_lift` timestamp.
  - For each source paper mapped to the bundle (per PAPER_DRAFT_MAPPING.md),
    compute the latest mtime under `papers/<source>/` (excluding
    bookkeeping caches).
  - If any source mtime is newer than the bundle's `last_lift`,
    the bundle is `freshness-stale` — flag at WARN level.

Also detects:
  - bundles with `bundle_metadata.json.stage13_redo_required = true`
    (set by `bundle_append.py`; cleared by Stage-13 reviewer agent
    after re-review).

Default: advisory; promotable to FAIL at the Phase 8 submission gate
via `validate.py --strict`.

Schema reference: `docs/BUNDLE_DIRECTORY_SCHEMA.md`.

This module exposes a single public function `check()` that returns a
list of per-bundle finding dicts. `validate.py` consumes it via
`@register_check("bundle_source_freshness", ...)`.
"""
from __future__ import annotations

import json
import sys
from datetime import datetime, timezone
from pathlib import Path

PROJECT_ROOT = Path(__file__).resolve().parent.parent
PAPERS_DIR = PROJECT_ROOT / "papers"
MAPPING_DOC = PROJECT_ROOT / "docs" / "PAPER_DRAFT_MAPPING.md"

sys.path.insert(0, str(PROJECT_ROOT / "scripts"))


def _parse_iso(s: str | None) -> datetime | None:
    if not s:
        return None
    try:
        # Accept both "2026-04-30T12:00:00Z" and "...+00:00"
        if s.endswith("Z"):
            return datetime.strptime(s, "%Y-%m-%dT%H:%M:%SZ").replace(
                tzinfo=timezone.utc
            )
        return datetime.fromisoformat(s)
    except (ValueError, TypeError):
        return None


# ═══════════════════════════════════════════════════════════════════════
# The Lean-module trigger (ADR-011 F-07 part 2, TODO-D27)
# ═══════════════════════════════════════════════════════════════════════
#
# Nine bundles — D6, D7, D8, D9, D10, D11, D12, I2, I3 — declare only synthetic
# source tokens (`_phase6t_lean_only`, `D10_initial_draft`) that name no
# directory, so the source-mtime trigger reports UNMEASURABLE for every one of
# them and the Stage-C absorption trigger cannot fire. Their substrate is Lean,
# and they say so: `append_log.json`'s `lean_modules_referenced`.
#
# ⚠️ THE FIELD NAME IS THE TRAP. Probing `lean_modules` returns 0 of 21 and
# reads as "no data exists" (ACCURACY_LEDGER V56 atom 1). Measured on the live
# corpus: **18 of 21 bundles declare 384 distinct module names**, of which 357
# resolve to a file and 27 name none.
#
# ⚠️ NOT MTIME — COMMIT TIME. The audit proposed Lean-module *mtimes*, and
# ADR-010 D6 required the proposal be evaluated rather than assumed. It does not
# survive evaluation: a `git checkout`, a worktree creation or a fresh clone
# rewrites every mtime in the tree, which would mark all nine bundles stale at
# once for a reason that has nothing to do with content. The last commit that
# touched a file is checkout-stable and monotone, so that is the signal, with a
# fall back to mtime for a file git does not know about (untracked, or dirty in
# the working tree — both of which mean "changed and not yet history").

_LEAN_ROOT = PROJECT_ROOT / "lean" / "SKEFTHawking"


def _lean_module_index() -> dict[str, Path]:
    """Dotted module name → file, for every `.lean` under `SKEFTHawking/`.

    Both the dotted path (`ETH.Predicates`) and the bare stem (`Predicates`) are
    keys; the dotted form wins, which is what disambiguates the four names whose
    stem is shared by up to five files (`Basic` alone appears five times).
    """
    idx: dict[str, Path] = {}
    if not _LEAN_ROOT.is_dir():
        return idx
    files = sorted(_LEAN_ROOT.rglob("*.lean"))
    stems: dict[str, list[Path]] = {}
    for p in files:
        dotted = ".".join(p.relative_to(_LEAN_ROOT).with_suffix("").parts)
        idx[dotted] = p
        stems.setdefault(p.stem, []).append(p)
    for stem, hits in stems.items():
        if len(hits) == 1:
            idx.setdefault(stem, hits[0])
    return idx


def _resolve_lean_module(name: str, idx: dict[str, Path]) -> Path | None:
    """The file a declared module name refers to, or None.

    Declared names arrive in three shapes — dotted, slash-separated, and
    `SKEFTHawking.`-prefixed — because they were typed by hand at lift time.
    Normalising all three is what takes resolution from 328 to 357 of 384.
    """
    key = name.replace("/", ".").removeprefix("SKEFTHawking.")
    return idx.get(key) or idx.get(key.split(".")[-1])


def _git_last_commit_times() -> dict[str, datetime]:
    """Repo-relative path → last commit time, for the whole Lean tree.

    One `git log` pass rather than one per module: the per-file form would be
    ~357 subprocesses inside a check that runs in every validate invocation.
    """
    import subprocess
    try:
        out = subprocess.run(
            ["git", "log", "--format=%ct", "--name-only", "--",
             "lean/SKEFTHawking"],
            cwd=str(PROJECT_ROOT), capture_output=True, text=True, check=True,
        ).stdout
    except (OSError, subprocess.CalledProcessError):
        return {}
    latest: dict[str, datetime] = {}
    ts: int | None = None
    for line in out.splitlines():
        if not line.strip():
            continue
        if line.isdigit():
            ts = int(line)
        elif ts is not None:
            # `git log` walks newest-first, so the first sighting wins.
            latest.setdefault(line, datetime.fromtimestamp(ts, timezone.utc))
    return latest


def _dirty_lean_paths() -> set[str]:
    """Repo-relative Lean paths with uncommitted changes (incl. untracked).

    A file edited but not committed has no commit time reflecting the edit, so
    without this the trigger would call a just-rewritten module fresh.
    """
    import subprocess
    try:
        out = subprocess.run(
            ["git", "status", "--porcelain", "--", "lean/SKEFTHawking"],
            cwd=str(PROJECT_ROOT), capture_output=True, text=True, check=True,
        ).stdout
    except (OSError, subprocess.CalledProcessError):
        return set()
    return {line[3:].strip().strip('"') for line in out.splitlines() if line[3:].strip()}


def _registered_lean_modules(bundle: str) -> list[str]:
    """Module names this bundle's append log declares, de-duplicated.

    Hand-typed at lift time, so this is the weaker of the two populations — but
    not a subset of the derived one: a module can be registered as contributing
    without any apex's closure reaching it.
    """
    log = PAPERS_DIR / bundle / "append_log.json"
    if not log.exists():
        return []
    try:
        data = json.loads(log.read_text())
    except (json.JSONDecodeError, OSError):
        return []
    seen: dict[str, None] = {}
    for e in data.get("events", []):
        for m in e.get("lean_modules_referenced") or []:
            seen.setdefault(str(m), None)
    return sorted(seen)


def _derived_lean_modules() -> dict[str, set[str]]:
    """`{bundle: modules}` from each bundle's declared-apex closure.

    ⚠️ **This is the population that made the trigger universal.** Registration
    alone covers 18 of 21 bundles, and the two that most needed a trigger — D6
    and D7, both sourceless — register **zero** modules, so a registration-only
    trigger would have left them UNMEASURABLE, which is the state F-07 exists to
    end. The closure is derived from `apex_theorems` over `name_deps_project`
    and is declared for all 21, D6 at 13 modules and D7 at 8. Nothing about it
    is hand-maintained, so nothing about it can drift.
    """
    try:
        import bundle_closure
        records = bundle_closure.load_records()
        decls = bundle_closure.load_apex_declarations(PAPERS_DIR)
        return {b: set(c.modules)
                for b, c in bundle_closure.build_closures(records, decls).items()}
    except Exception:
        # The closure needs `lean_deps.json`; its absence must not take the
        # source-mtime half of the check down with it.
        return {}


def _lean_module_change_times(
    bundle: str, idx: dict[str, Path],
    commits: dict[str, datetime], dirty: set[str],
    derived: set[str] | None = None,
) -> tuple[dict[str, datetime], list[str]]:
    """`({module: last-change time}, unresolved_names)` for one bundle.

    The population is the UNION of the derived closure and the registered names.
    Neither contains the other: the closure reaches only what an apex depends on,
    and registration records what a lift said it drew from.

    ⚠️ **Keyed by resolved PATH, not by name.** The two sources spell the same
    module differently — the closure emits `SKEFTHawking.EffectiveMediumBounds`,
    registration emits `EffectiveMediumBounds` — so a name-keyed union counts one
    file twice and prints it twice in the sample. The shorter spelling is kept as
    the label because that is what a reader looking for it will type.
    """
    seen: dict[str, str] = {}          # repo-relative path -> label
    unresolved: list[str] = []
    for name in sorted(set(_registered_lean_modules(bundle)) | set(derived or ())):
        path = _resolve_lean_module(name, idx)
        if path is None:
            unresolved.append(name)
            continue
        rel = str(path.relative_to(PROJECT_ROOT))
        prev = seen.get(rel)
        if prev is None or len(name) < len(prev):
            seen[rel] = name

    times: dict[str, datetime] = {}
    for rel, label in seen.items():
        if rel in dirty or rel not in commits:
            times[label] = datetime.fromtimestamp(
                (PROJECT_ROOT / rel).stat().st_mtime, timezone.utc)
        else:
            times[label] = commits[rel]
    return times, unresolved


def _latest_source_mtime(source: str) -> datetime | None:
    """Return the latest mtime of any meaningful file under
    papers/<source>/, or None if the directory is missing/empty."""
    pdir = PAPERS_DIR / source
    if not pdir.exists():
        return None
    latest = 0.0
    for p in pdir.rglob("*"):
        if not p.is_file():
            continue
        if any(part.startswith(".") or part == "__pycache__" for part in p.parts):
            continue
        # Skip bundle-bookkeeping files when source happens to be a
        # bundle (it shouldn't, but be defensive).
        if p.name in {"bundle_metadata.json", "append_log.json"}:
            continue
        latest = max(latest, p.stat().st_mtime)
    if latest == 0.0:
        return None
    return datetime.fromtimestamp(latest, timezone.utc)


def check(write_metadata: bool = False) -> list[dict]:
    """Run the freshness check across all bundle directories.

    ⚠️ **PURE BY DEFAULT.** `write_metadata=False` means this never touches the tree.
    A CHECK MUST NOT MUTATE THE ARTIFACT IT CHECKS: `bundle_metadata.json` is what the
    dashboard and `LATE_PHASE6_ABSORPTION_PROTOCOL` read as the absorption trigger, so
    a validate.py run (or a pytest run, which imports this) writing its own verdict
    into it makes the instrument its own upstream. Verified 2026-08-05: forcing D1's
    `freshness_stale` to a wrong value and calling `check()` silently rewrote the
    tracked file. PR-review pass 3, R4.

    `scripts/check_bundle_source_freshness.py` invoked as a CLI passes True, so the
    dashboard-refresh capability is preserved and is now an explicit, named action.

    Returns a list of finding dicts, each:
      {
        "bundle": str,
        "passed": bool,
        "warning": bool,    # advisory only
        "message": str,
      }

    Empty list means: no bundle directories found yet (acceptable
    pre-Phase-7-execution state).
    """
    from bundle_migration import parse_mapping
    from sentence_state import _VALID_BUNDLE_TARGETS

    if not MAPPING_DOC.exists():
        return [{
            "bundle": "_meta",
            "passed": False,
            "warning": False,
            "message": f"PAPER_DRAFT_MAPPING.md not found at {MAPPING_DOC}",
        }]

    assignments = parse_mapping(MAPPING_DOC.read_text())

    # Lean trigger inputs, computed once for the whole run (F-07 part 2).
    lean_idx = _lean_module_index()
    lean_commits = _git_last_commit_times()
    lean_dirty = _dirty_lean_paths()
    lean_derived = _derived_lean_modules()

    findings: list[dict] = []
    for bundle in sorted(_VALID_BUNDLE_TARGETS):
        bdir = PAPERS_DIR / bundle
        md_path = bdir / "bundle_metadata.json"
        if not md_path.exists():
            # No bookkeeping yet → bundle hasn't been initialized.
            # This is acceptable pre-Phase-7-execution; not a finding.
            continue

        try:
            md = json.loads(md_path.read_text())
        except (json.JSONDecodeError, OSError) as exc:
            findings.append({
                "bundle": bundle,
                "passed": False,
                "warning": False,
                "message": f"failed to read bundle_metadata.json: {exc}",
            })
            continue

        last_lift = _parse_iso(md.get("last_lift"))

        # Sub-finding A: stage13_redo_required flag
        if md.get("stage13_redo_required") is True:
            findings.append({
                "bundle": bundle,
                "passed": True,
                "warning": True,
                "message": (
                    "stage13_redo_required=true (set by bundle_append.py); "
                    "Stage-13 reviewer agent must re-clear before bundle close"
                ),
            })

        # Sub-finding B: source-paper mtime newer than last_lift
        if last_lift is None:
            # Bundle initialized but never appended → freshness check
            # is not applicable (no lifts to compare against).
            findings.append({
                "bundle": bundle,
                "passed": True,
                "warning": False,
                "message": "bundle initialized; no lifts yet (skip)",
            })
            continue

        sources = sorted([
            p for p, a in assignments.items()
            if bundle in a["bundle_destinations"]
        ])
        # A source naming a directory that does not exist is UNMEASURABLE, not fresh.
        # `_latest_source_mtime` returns None for a missing directory and the staleness
        # loop skips every None, so absent sources must be split out BEFORE the verdict —
        # otherwise a bundle whose sources are all absent reports freshness over an empty
        # population. Phase-sourced bundles (D6-D12, I2, I3) declare synthetic tokens
        # like `_phase6t_lean_only` that name no directory, so this is the normal case
        # for them, not an edge case.
        #
        # House rule (ADR-009): absence of measurement must never render as success.
        # See docs/architecture/CHECK_AUTHORING_GUIDE.md §2.1.
        absent_sources = [s for s in sources if not (PAPERS_DIR / s).is_dir()]
        measurable = [s for s in sources if s not in set(absent_sources)]

        stale_sources: list[tuple[str, datetime]] = []
        for src in measurable:
            mt = _latest_source_mtime(src)
            if mt is not None and mt > last_lift:
                stale_sources.append((src, mt))

        # Sub-finding C: the Lean-module trigger (F-07 part 2). Computed for
        # EVERY bundle, not only the nine sourceless ones — a bundle can be
        # source-fresh and Lean-stale, and scoping the trigger to the bundles
        # that happen to have no sources would make it a special case rather
        # than a measurement.
        lean_times, lean_unresolved = _lean_module_change_times(
            bundle, lean_idx, lean_commits, lean_dirty,
            lean_derived.get(bundle))
        stale_lean = sorted(
            ((m, t) for m, t in lean_times.items() if t > last_lift),
            key=lambda mt: mt[1], reverse=True)
        if lean_unresolved:
            sample = ", ".join(lean_unresolved[:3])
            extra = (f" ... and {len(lean_unresolved) - 3} more"
                     if len(lean_unresolved) > 3 else "")
            findings.append({
                "bundle": bundle,
                "passed": True,
                "warning": True,
                "message": (
                    f"{len(lean_unresolved)} of "
                    f"{len(lean_unresolved) + len(lean_times)} declared Lean "
                    f"module(s) resolve to no file ({sample}{extra}); they are "
                    f"NOT measured by the freshness trigger — a renamed or "
                    f"deleted module silently drops out of the population it "
                    f"was registered into"
                ),
            })
        if stale_lean:
            sample = ", ".join(f"{m}({t.strftime('%Y-%m-%d')})"
                               for m, t in stale_lean[:3])
            extra = (f" ... and {len(stale_lean) - 3} more"
                     if len(stale_lean) > 3 else "")
            findings.append({
                "bundle": bundle,
                "passed": True,
                "warning": True,
                "message": (
                    f"lean-stale: {len(stale_lean)} of {len(lean_times)} declared "
                    f"Lean module(s) last changed after last_lift "
                    f"({last_lift.strftime('%Y-%m-%d')}); sample: {sample}{extra}"
                ),
            })

        if sources and not measurable and not lean_times:
            sample = ", ".join(sources[:3])
            extra = f" ... and {len(sources) - 3} more" if len(sources) > 3 else ""
            findings.append({
                "bundle": bundle,
                "passed": True,
                "warning": True,
                "message": (
                    f"UNMEASURABLE: all {len(sources)} declared source(s) name a "
                    f"directory absent from papers/ ({sample}{extra}) AND the "
                    f"bundle declares no resolvable Lean module; freshness is "
                    f"NOT established — the Stage-C absorption trigger cannot "
                    f"fire on either population."
                ),
            })
            continue

        if sources and not measurable:
            # Sourceless, but the Lean trigger measured it — which is the whole
            # point of F-07 part 2. Verdict comes from `stale_lean` above.
            findings.append({
                "bundle": bundle,
                "passed": True,
                "warning": bool(stale_lean),
                "message": (
                    f"source-UNMEASURABLE, Lean-measured: all {len(sources)} "
                    f"declared source(s) name an absent directory, but "
                    f"{len(lean_times)} declared Lean module(s) resolve and "
                    + ("carry the staleness reported above"
                       if stale_lean else
                       f"all predate last_lift ({last_lift.strftime('%Y-%m-%d')})")
                ),
            })
            continue

        if stale_sources:
            sample = ", ".join(
                f"{s}({mt.strftime('%Y-%m-%d')})"
                for s, mt in stale_sources[:3]
            )
            extra = (
                f" ... and {len(stale_sources) - 3} more"
                if len(stale_sources) > 3 else ""
            )
            findings.append({
                "bundle": bundle,
                "passed": True,
                "warning": True,
                "message": (
                    f"freshness-stale: {len(stale_sources)} of {len(measurable)} "
                    f"measurable source paper(s) modified after last_lift "
                    f"({last_lift.strftime('%Y-%m-%d')}); "
                    f"sample: {sample}{extra}"
                ),
            })
            # Set freshness_stale=true in metadata so dashboard reflects it
            if write_metadata:
                try:
                    md["freshness_stale"] = True
                    md_path.write_text(json.dumps(md, indent=2) + "\n")
                except OSError:
                    pass
        else:
            findings.append({
                "bundle": bundle,
                "passed": True,
                "warning": False,
                "message": (
                    f"fresh: all {len(measurable)} measurable source paper(s) "
                    f"older than last_lift ({last_lift.strftime('%Y-%m-%d')})"
                    + (f"; {len(absent_sources)} further declared source(s) name "
                       f"an absent directory and were NOT measured"
                       if absent_sources else "")
                ),
            })
            # Clear stale flag if previously set
            if write_metadata and md.get("freshness_stale"):
                md["freshness_stale"] = False
                try:
                    md_path.write_text(json.dumps(md, indent=2) + "\n")
                except OSError:
                    pass

    return findings


def main() -> int:
    """Standalone CLI: run the check, print findings, exit 0 always
    (advisory). Return non-zero only on hard errors."""
    findings = check(write_metadata=True)
    if not findings:
        print("CHECK 22 (bundle_source_freshness): no bundle directories "
              "found; pre-Phase-7-execution state — skip.")
        return 0

    print(f"CHECK 22 (bundle_source_freshness): {len(findings)} sub-finding(s)")
    for f in findings:
        if not f["passed"]:
            tag = "FAIL"
        elif f["warning"]:
            tag = "WARN"
        else:
            tag = "PASS"
        print(f"  [{tag}] {f['bundle']}: {f['message']}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
