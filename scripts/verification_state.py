#!/usr/bin/env python3
"""
verification_state.py — cross-tab change-bus event log (Phase 5v Wave 10c)
==========================================================================

Append-only JSONL of human verification actions across artifact types.
Powers the Wave 10c "verification ripple" — when a Parameter, Citation, or
LeanAxiom-eliminability is confirmed/rejected/flagged on any dashboard tab,
this module records the event and bumps the corresponding KG node's
``meta.last_modified_explicit``. Downstream ``last_modified.annotate_last_modified``
propagates that timestamp along dependency edges (USED_BY, VERIFIED_BY,
DEPENDS_ON_AXIOM, etc.) into dependent Sentence / ProseClaim nodes, which
then surface as "stale" in Paper Provenance.

Invariants
----------
- This module is the **sole writer** to ``docs/verification_log.jsonl``
  (mirrors the sentence_state.py pattern).
- Events are append-only; nothing in this file is ever rewritten.
- Each event line is one JSON object; event order = file order.
- Dashboard backends call ``record_event`` directly (in-process); ad-hoc
  scripts and external agents go through the CLI.

Event schema
------------
::

    {
      "artifact_type": "Parameter" | "Citation" | "LeanAxiom" | "LeanTheorem" | ...,
      "artifact_id":   "<source-of-truth key>",       # e.g. "EW.gauge_g1"
      "node_id":       "<KG node id>",                # e.g. "param:EW.gauge_g1"
      "action":        "confirm" | "reject" | "flag" | "reset",
      "actor":         "user:<id>" | "agent:<name>:<ISO-timestamp>",
      "timestamp":     "<ISO-8601 UTC>",
      "notes":         "<free-form>"
    }

CLI subcommands
---------------
- ``record``   — append a single event (atomic, locked write)
- ``list``     — dump events (optionally filtered by --artifact-id/--type)
- ``apply``    — read a graph.json from stdin / path, stamp
                 ``meta.last_modified_explicit`` on matching nodes, then
                 (optionally) call ``annotate_last_modified``; writes the
                 mutated graph to stdout / --out path

Library API
-----------
- ``record_event(...)``           — append-only writer
- ``read_events(path=...)``       — generator over events (oldest first)
- ``latest_per_node(events=None)``— dict {node_id: latest event}
- ``apply_to_graph(graph)``       — mutates graph in-place; returns count of
                                    nodes touched
- ``node_id_for(artifact_type, artifact_id)`` — best-effort id heuristic
"""

from __future__ import annotations

import argparse
import errno
import fcntl
import json
import os
import sys
import tempfile
from datetime import datetime, timedelta, timezone
from pathlib import Path
from typing import Any, Iterable, Iterator

# ── Paths ──────────────────────────────────────────────────────────────────

SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_ROOT = SCRIPT_DIR.parent
LOG_PATH = PROJECT_ROOT / 'docs' / 'verification_log.jsonl'
LOCK_PATH = PROJECT_ROOT / 'docs' / 'verification_log.jsonl.lock'

# ── Validation ─────────────────────────────────────────────────────────────

VALID_ACTIONS = {'confirm', 'reject', 'flag', 'reset'}
# Artifact_type values match KG node types we know how to map. Unknown
# values are accepted but a warning is emitted; the event lands on
# verification_log but apply_to_graph won't touch a node.
KNOWN_ARTIFACT_TYPES = {
    'Parameter', 'Citation', 'PrimarySource',
    'LeanAxiom', 'LeanTheorem', 'LeanDef',
    'Formula', 'PaperClaim', 'ProseClaim', 'Sentence',
    # Wave 10c strengthening: v2 chain_link.kind values that agents may
    # cite — without these, change-bus events get silently dropped at
    # node_id_for time and apply_to_graph never propagates the timestamp.
    'Hypothesis', 'AristotleRun', 'ProductionRun',
}

REQUIRED_FIELDS = ('artifact_type', 'artifact_id', 'action', 'actor', 'timestamp')


def _parse_iso(ts: str | None) -> str:
    """Normalize an ISO-8601 to a Zulu-suffixed sortable string."""
    if not ts:
        return ''
    t = str(ts)
    if t.endswith('+00:00'):
        t = t[:-6] + 'Z'
    return t


def _now_iso() -> str:
    return datetime.now(timezone.utc).strftime('%Y-%m-%dT%H:%M:%SZ')


def _validate_event(event: dict) -> list[str]:
    errs: list[str] = []
    for f in REQUIRED_FIELDS:
        if not event.get(f):
            errs.append(f"missing required field: {f}")
    action = event.get('action')
    if action and action not in VALID_ACTIONS:
        errs.append(
            f"action {action!r} not in {sorted(VALID_ACTIONS)}"
        )
    actor = event.get('actor', '')
    if actor and not (actor.startswith('user:') or actor.startswith('agent:')):
        errs.append(
            f"actor {actor!r} must start with 'user:<id>' or 'agent:<name>:<ts>'"
        )
    ts = event.get('timestamp', '')
    if ts and not (ts.endswith('Z') or '+00:00' in ts):
        errs.append(f"timestamp {ts!r} must be ISO-8601 UTC (ending in 'Z')")
    return errs


# ── Node ID heuristic ──────────────────────────────────────────────────────

def node_id_for(artifact_type: str, artifact_id: str) -> str | None:
    """Best-effort mapping from (artifact_type, artifact_id) to KG node id.

    Mirrors the prefix conventions in build_graph.py:
        Parameter      → param:<key>
        Citation       → source:<bibkey>     (alias for PrimarySource)
        PrimarySource  → source:<bibkey>
        LeanAxiom      → lean:<full_name>
        LeanTheorem    → lean:<full_name>
        LeanDef        → lean:<full_name>
        Formula        → formula:<func_name>
        ProseClaim     → claim:<id>          (already includes paper prefix)
        Sentence       → sentence:<id>       (already a sentence: id)

    Callers may also pass a fully qualified node_id directly via the
    ``node_id`` event field, which overrides this heuristic.
    """
    if not artifact_type or not artifact_id:
        return None
    if artifact_type == 'Parameter':
        return f'param:{artifact_id}'
    if artifact_type in ('Citation', 'PrimarySource'):
        return f'source:{artifact_id}'
    if artifact_type in ('LeanAxiom', 'LeanTheorem', 'LeanDef'):
        # Already-qualified passthroughs (callers occasionally pass the
        # full lean: prefix in artifact_id).
        if artifact_id.startswith('lean:'):
            return artifact_id
        return f'lean:{artifact_id}'
    if artifact_type == 'Formula':
        if artifact_id.startswith('formula:'):
            return artifact_id
        return f'formula:{artifact_id}'
    if artifact_type == 'ProseClaim':
        if artifact_id.startswith('claim:'):
            return artifact_id
        return f'claim:{artifact_id}'
    if artifact_type == 'Sentence':
        if artifact_id.startswith('sentence:'):
            return artifact_id
        return f'sentence:{artifact_id}'
    if artifact_type == 'Hypothesis':
        if artifact_id.startswith('hyp:'):
            return artifact_id
        return f'hyp:{artifact_id}'
    if artifact_type == 'AristotleRun':
        if artifact_id.startswith('aristotle:'):
            return artifact_id
        return f'aristotle:{artifact_id}'
    if artifact_type == 'ProductionRun':
        if artifact_id.startswith('production:'):
            return artifact_id
        return f'production:{artifact_id}'
    return None


# ── Append-only writer (sole writer pattern) ───────────────────────────────

def record_event(
    *,
    artifact_type: str,
    artifact_id: str,
    action: str,
    actor: str,
    timestamp: str | None = None,
    notes: str | None = None,
    node_id: str | None = None,
    triggered_by: str | None = None,
    extra: dict[str, Any] | None = None,
    log_path: Path | None = None,
) -> dict:
    """Append a single verification event to the log.

    Atomic-append: takes an exclusive ``flock`` on the lock file, writes
    one line, releases. Concurrent writers serialize at the OS level —
    no readers ever see a partial line.

    ``triggered_by`` (Wave 10 strengthening): when the event was fired
    from a per-link verify UI inside a sentence inspector, this carries
    the ``sentence:<paper>:<slug>:<hash>`` id of the source sentence so
    the audit trail surfaces cross-tab provenance. Null for events that
    originated from the Parameters tab, an ad-hoc CLI, or a script.

    Returns the event dict that was written (with normalized timestamp +
    auto-derived ``node_id`` if not supplied).
    """
    log_path = log_path or LOG_PATH
    log_path.parent.mkdir(parents=True, exist_ok=True)

    event: dict[str, Any] = {
        'artifact_type': artifact_type,
        'artifact_id': artifact_id,
        'action': action,
        'actor': actor,
        'timestamp': _parse_iso(timestamp) or _now_iso(),
    }
    if notes:
        event['notes'] = notes
    if triggered_by:
        event['triggered_by'] = triggered_by
    if node_id is None:
        node_id = node_id_for(artifact_type, artifact_id)
    if node_id:
        event['node_id'] = node_id
    if extra:
        for k, v in extra.items():
            if k not in event:
                event[k] = v

    errs = _validate_event(event)
    if errs:
        raise ValueError(f"verification event invalid: {'; '.join(errs)}")
    if artifact_type not in KNOWN_ARTIFACT_TYPES:
        # Soft-warn; we still record. apply_to_graph may not touch a node.
        sys.stderr.write(
            f"[verification_state] WARN unknown artifact_type={artifact_type!r}; "
            f"event recorded but no graph node will be bumped\n"
        )

    line = json.dumps(event, sort_keys=True, ensure_ascii=False)

    # Lock-and-append. fcntl.flock on an open file descriptor.
    with open(LOCK_PATH, 'a+') as lock_f:
        try:
            fcntl.flock(lock_f.fileno(), fcntl.LOCK_EX)
            with open(log_path, 'a', encoding='utf-8') as out:
                out.write(line + '\n')
        finally:
            try:
                fcntl.flock(lock_f.fileno(), fcntl.LOCK_UN)
            except OSError:
                pass

    return event


# ── Reader ─────────────────────────────────────────────────────────────────

_LOG_SIZE_WARN_BYTES = 1_048_576  # 1 MB
_LOG_SIZE_WARN_EMITTED: set[str] = set()


def _maybe_warn_log_size(log_path: Path) -> None:
    """One-shot WARN to stderr when the log file crosses 1MB.

    Triggers `prune --keep-days 90` as the standard remediation but
    never auto-prunes — log loss should be a deliberate human act.
    De-duplicates the warning per process so heavy readers don't spam.
    """
    key = str(log_path)
    if key in _LOG_SIZE_WARN_EMITTED:
        return
    try:
        size = log_path.stat().st_size
    except OSError:
        return
    if size > _LOG_SIZE_WARN_BYTES:
        sys.stderr.write(
            f"[verification_state] WARN: {log_path.name} is "
            f"{size/1_048_576:.1f}MB. Consider "
            f"`scripts/verification_state.py prune --keep-days 90` "
            f"to retain recent events only.\n"
        )
        _LOG_SIZE_WARN_EMITTED.add(key)


def read_events(log_path: Path | None = None) -> Iterator[dict]:
    """Yield events from the log in file order (oldest first).

    Skips malformed lines with a warning to stderr. Returns an empty
    iterator if the log doesn't exist yet. Warns once per process
    when the log exceeds 1 MB.
    """
    log_path = log_path or LOG_PATH
    if not log_path.exists():
        return iter(())
    _maybe_warn_log_size(log_path)

    def _gen() -> Iterator[dict]:
        with open(log_path, 'r', encoding='utf-8') as f:
            for lineno, raw in enumerate(f, 1):
                line = raw.rstrip('\n')
                if not line.strip():
                    continue
                try:
                    yield json.loads(line)
                except json.JSONDecodeError as exc:
                    sys.stderr.write(
                        f"[verification_state] WARN line {lineno}: "
                        f"malformed JSON; skipping ({exc})\n"
                    )
    return _gen()


# ── Prune (retention) ─────────────────────────────────────────────────────

def prune_log(
    *,
    keep_days: int | None = None,
    keep_records: int | None = None,
    before: str | None = None,
    log_path: Path | None = None,
    archive_to: Path | None = None,
    dry_run: bool = False,
) -> dict:
    """Rewrite the verification log keeping only events that satisfy the
    retention criteria. At least one of ``keep_days`` / ``keep_records`` /
    ``before`` must be supplied.

    Atomic: serializes through the same lock file as ``record_event``,
    builds a new file at ``log_path.tmp``, then ``os.replace`` swaps it
    in. Pruned events are optionally appended to ``archive_to`` so the
    discarded events stay recoverable on disk.

    Returns ``{kept, removed, total, oldest_kept, newest_kept}``.
    Refuses to run if no criterion is supplied (don't accidentally wipe).
    """
    # Refuse to operate without a retention criterion REGARDLESS of log
    # state — protects against an accidental wipe even when the log
    # doesn't yet exist (a future record_event call would be discarded).
    if keep_days is None and keep_records is None and before is None:
        raise ValueError(
            "prune_log requires at least one of "
            "keep_days / keep_records / before — refusing to truncate "
            "without a retention criterion"
        )

    log_path = log_path or LOG_PATH
    if not log_path.exists():
        return {'kept': 0, 'removed': 0, 'total': 0,
                'oldest_kept': None, 'newest_kept': None}

    cutoff_iso: str | None = None
    if before:
        cutoff_iso = _parse_iso(before)
    elif keep_days is not None:
        cutoff_dt = datetime.now(timezone.utc) - timedelta(days=int(keep_days))
        cutoff_iso = cutoff_dt.strftime('%Y-%m-%dT%H:%M:%SZ')

    # Load all events
    all_events: list[dict] = list(read_events(log_path))
    total = len(all_events)

    # Apply criteria. Both can apply jointly — keep events that satisfy
    # the timestamp criterion AND fall within the most-recent N count.
    surviving = list(all_events)
    if cutoff_iso is not None:
        surviving = [
            e for e in surviving
            if _parse_iso(e.get('timestamp', '')) >= cutoff_iso
        ]
    if keep_records is not None:
        # Most-recent N by timestamp
        surviving.sort(key=lambda e: e.get('timestamp', ''))
        if len(surviving) > int(keep_records):
            surviving = surviving[-int(keep_records):]

    # Recover insertion order: file order = timestamp order normally, so
    # sort surviving by timestamp.
    surviving.sort(key=lambda e: e.get('timestamp', ''))

    pruned = [
        e for e in all_events
        if e not in surviving  # NB: O(N²); acceptable for any realistic log
    ]

    result = {
        'kept': len(surviving),
        'removed': len(pruned),
        'total': total,
        'oldest_kept': surviving[0].get('timestamp') if surviving else None,
        'newest_kept': surviving[-1].get('timestamp') if surviving else None,
    }
    if dry_run:
        return result

    # Atomic rewrite
    log_path.parent.mkdir(parents=True, exist_ok=True)
    tmp = log_path.with_suffix('.jsonl.tmp')
    with open(LOCK_PATH, 'a+') as lock_f:
        try:
            fcntl.flock(lock_f.fileno(), fcntl.LOCK_EX)
            with open(tmp, 'w', encoding='utf-8') as out:
                for ev in surviving:
                    out.write(json.dumps(ev, sort_keys=True, ensure_ascii=False))
                    out.write('\n')
            os.replace(tmp, log_path)
            # Optionally archive pruned events to a sidecar for recovery
            if archive_to and pruned:
                archive_to.parent.mkdir(parents=True, exist_ok=True)
                with open(archive_to, 'a', encoding='utf-8') as ar:
                    for ev in pruned:
                        ar.write(json.dumps(ev, sort_keys=True, ensure_ascii=False))
                        ar.write('\n')
        finally:
            try:
                fcntl.flock(lock_f.fileno(), fcntl.LOCK_UN)
            except OSError:
                pass

    return result


def latest_per_node(events: Iterable[dict] | None = None) -> dict[str, dict]:
    """Return {node_id: latest_event} keyed by event timestamp.

    Multiple events for the same node — the newest one wins for the
    "latest verification" view; the full history remains in the log.
    """
    if events is None:
        events = read_events()
    by_node: dict[str, dict] = {}
    for ev in events:
        nid = ev.get('node_id')
        if not nid:
            continue
        prev = by_node.get(nid)
        if prev is None or ev.get('timestamp', '') > prev.get('timestamp', ''):
            by_node[nid] = ev
    return by_node


# ── Graph integration ──────────────────────────────────────────────────────

def apply_to_graph(graph: dict, events: Iterable[dict] | None = None) -> int:
    """Stamp ``meta.last_modified_explicit`` on every node that has a
    matching verification event. Returns the count of nodes touched.

    Designed to run BEFORE ``last_modified.annotate_last_modified``: the
    explicit field takes priority in ``_direct_last_modified`` so the
    verification timestamp wins over file mtime + previously-stored values.

    Idempotent — running twice with the same event log produces the same
    output. Older events never overwrite newer ones.
    """
    nodes: list[dict] = graph.get('nodes', [])
    id_to_node = {n.get('id'): n for n in nodes if n.get('id')}

    touched = 0
    for nid, ev in latest_per_node(events).items():
        node = id_to_node.get(nid)
        if node is None:
            continue
        meta = node.setdefault('meta', {})
        ts = _parse_iso(ev.get('timestamp', ''))
        if not ts:
            continue
        existing = _parse_iso(meta.get('last_modified_explicit', ''))
        if ts > existing:
            meta['last_modified_explicit'] = ts
            # Also surface the action so the dashboard can render verbatim:
            meta['last_verification_action'] = ev.get('action')
            meta['last_verification_actor'] = ev.get('actor')
            meta['last_verification_notes'] = ev.get('notes')
            # Wave 10 strengthening: cross-tab provenance — when the
            # event originated from a sentence's per-link verify UI,
            # carry the source sentence id forward so dashboard panes
            # can render "verified from <sentence>".
            meta['last_verification_triggered_by'] = ev.get('triggered_by')
            touched += 1
    return touched


# ── CLI ────────────────────────────────────────────────────────────────────

def _cmd_record(args: argparse.Namespace) -> int:
    ev = record_event(
        artifact_type=args.artifact_type,
        artifact_id=args.artifact_id,
        action=args.action,
        actor=args.actor,
        timestamp=args.timestamp,
        notes=args.notes,
        node_id=args.node_id,
        triggered_by=getattr(args, 'triggered_by', None),
    )
    print(json.dumps(ev, sort_keys=True))
    return 0


def _cmd_list(args: argparse.Namespace) -> int:
    n = 0
    for ev in read_events():
        if args.artifact_id and ev.get('artifact_id') != args.artifact_id:
            continue
        if args.type and ev.get('artifact_type') != args.type:
            continue
        if args.actor and ev.get('actor') != args.actor:
            continue
        if args.latest_only:
            continue  # handled below
        print(json.dumps(ev, sort_keys=True))
        n += 1
    if args.latest_only:
        for nid, ev in sorted(latest_per_node().items()):
            if args.artifact_id and ev.get('artifact_id') != args.artifact_id:
                continue
            if args.type and ev.get('artifact_type') != args.type:
                continue
            print(json.dumps(ev, sort_keys=True))
            n += 1
    sys.stderr.write(f"# {n} events\n")
    return 0


def _cmd_apply(args: argparse.Namespace) -> int:
    if args.graph == '-':
        graph = json.load(sys.stdin)
    else:
        with open(args.graph, 'r', encoding='utf-8') as f:
            graph = json.load(f)

    touched = apply_to_graph(graph)
    sys.stderr.write(f"# verification_state: {touched} nodes touched\n")

    if args.annotate:
        try:
            sys.path.insert(0, str(SCRIPT_DIR))
            from last_modified import annotate_last_modified
            annotate_last_modified(graph)
        except ImportError as exc:
            sys.stderr.write(f"# annotate skipped: {exc}\n")

    if args.out:
        with open(args.out, 'w', encoding='utf-8') as f:
            json.dump(graph, f, indent=2, sort_keys=True)
        sys.stderr.write(f"# wrote {args.out}\n")
    else:
        json.dump(graph, sys.stdout, indent=2, sort_keys=True)
    return 0


def _build_parser() -> argparse.ArgumentParser:
    p = argparse.ArgumentParser(
        prog='verification_state.py',
        description='Append-only cross-tab verification event log + graph stamper',
    )
    sub = p.add_subparsers(dest='cmd', required=True)

    rec = sub.add_parser('record', help='Append a verification event')
    rec.add_argument('--artifact-type', required=True,
                     help=f"one of {sorted(KNOWN_ARTIFACT_TYPES)}")
    rec.add_argument('--artifact-id', required=True,
                     help='source-of-truth key (e.g. EW.gauge_g1, Falque2025)')
    rec.add_argument('--action', required=True,
                     choices=sorted(VALID_ACTIONS))
    rec.add_argument('--actor', required=True,
                     help="user:<id> | agent:<name>:<ISO-timestamp>")
    rec.add_argument('--timestamp', default=None,
                     help='Override timestamp (default: now-UTC)')
    rec.add_argument('--notes', default=None)
    rec.add_argument('--node-id', default=None,
                     help='Override the auto-derived KG node id')
    rec.add_argument('--triggered-by', default=None,
                     help='Source sentence_id (Wave 10 cross-tab provenance)')
    rec.set_defaults(func=_cmd_record)

    lst = sub.add_parser('list', help='Dump events from the log')
    lst.add_argument('--artifact-id', default=None)
    lst.add_argument('--type', dest='type', default=None,
                     help='Filter by artifact_type')
    lst.add_argument('--actor', default=None)
    lst.add_argument('--latest-only', action='store_true',
                     help='Show only the most recent event per node')
    lst.set_defaults(func=_cmd_list)

    app = sub.add_parser('apply', help="Stamp meta.last_modified_explicit on graph nodes")
    app.add_argument('graph', help='Path to graph.json or - for stdin')
    app.add_argument('--annotate', action='store_true',
                     help='Also call last_modified.annotate_last_modified')
    app.add_argument('--out', default=None,
                     help='Write annotated graph here (default: stdout)')
    app.set_defaults(func=_cmd_apply)

    pr = sub.add_parser(
        'prune',
        help='Rewrite the log keeping only events matching retention criteria',
    )
    pr.add_argument('--keep-days', type=int, default=None,
                    help='Keep events newer than N days')
    pr.add_argument('--keep-records', type=int, default=None,
                    help='Keep at most N most-recent events')
    pr.add_argument('--before', default=None,
                    help='Drop events older than ISO-8601 timestamp')
    pr.add_argument('--archive-to', default=None,
                    help='Append pruned events to this jsonl file (recovery)')
    pr.add_argument('--dry-run', action='store_true',
                    help='Report what would be removed; do not write')
    pr.set_defaults(func=_cmd_prune)

    return p


def _cmd_prune(args: argparse.Namespace) -> int:
    if (args.keep_days is None and args.keep_records is None
            and args.before is None):
        sys.stderr.write(
            "verification_state prune: refusing to wipe — supply at "
            "least one of --keep-days / --keep-records / --before\n"
        )
        return 2
    archive = Path(args.archive_to).resolve() if args.archive_to else None
    try:
        result = prune_log(
            keep_days=args.keep_days,
            keep_records=args.keep_records,
            before=args.before,
            archive_to=archive,
            dry_run=args.dry_run,
        )
    except ValueError as exc:
        sys.stderr.write(f"verification_state prune: {exc}\n")
        return 2
    print(json.dumps(result, sort_keys=True, indent=2))
    return 0


def main(argv: list[str] | None = None) -> int:
    args = _build_parser().parse_args(argv)
    return args.func(args)


if __name__ == '__main__':
    sys.exit(main())
