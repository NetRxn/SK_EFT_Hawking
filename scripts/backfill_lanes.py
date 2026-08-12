#!/usr/bin/env python3
"""Declare a `Lane:` on findings that predate the emission contract (ADR-012 D1/D2).

Why this exists
---------------
`lane` is **forward-only**: `_parse_lane` reads an absent lane as `unclassified`, which is the
right default because it cannot be mistaken for a routed finding. The cost is that the entire
historical backlog — the findings actually blocking the bundles — routes nowhere. Fan-out by
lane works for findings that do not exist yet and not for the ones in front of the operator.

This writes the missing declaration into the review documents themselves, so the lane lives
where every other finding field lives and the extractor reads it by the normal path. Nothing
about the parser, the schema or the gates changes.

⚠️ **IT REFUSES TO GUESS, AND THAT IS THE WHOLE DESIGN.**
Two of the six lanes are *semantic*, not path-derivable:

* `substrate` means **the theorem and the implementation disagree** — a defect needing a
  Lean-side statement, a Python-side repair, and a regression test asserting the two agree.
  A `.lean` target is equally consistent with a plain `lean` proof obligation.
* `research` means **a question the corpus cannot answer**. No path implies it.

So a path rule that mapped `*.lean -> lean` would silently reclassify every substrate defect as
a proof obligation and route it to a worker who cannot fix it. A WRONG lane is worse than an
absent one: absent reads `unclassified` and stops, wrong reads routed and sends work to the
wrong agent profile. Everything this module cannot establish from evidence is emitted for
adjudication instead of being assigned.

Usage
-----
    python scripts/backfill_lanes.py --propose            # measure; writes nothing
    python scripts/backfill_lanes.py --propose --json out.json
    python scripts/backfill_lanes.py --apply              # write the CONFIDENT ones only
    python scripts/backfill_lanes.py --apply --from adjudicated.json
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import Counter
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_ROOT = SCRIPT_DIR.parent
sys.path.insert(0, str(SCRIPT_DIR))

import build_graph as _bg  # noqa: E402

#: Only these mappings are asserted from a target path alone. Each is a shape whose lane is
#: unambiguous under the D2 table; anything a path cannot decide is left for adjudication.
_CONFIDENT: tuple[tuple[str, str, str], ...] = (
    # (predicate name, lane, why)
    ('paper_tex', 'prose',
     'a manuscript, figure or citation target — the `prose` lane by definition'),
    ('scripts', 'infra',
     'the machine itself: a validation check, generator or harness script'),
    ('architecture_doc', 'infra',
     'an architecture document, the wave pipeline, or the plugin surface'),
)

_FIELD_LINE = re.compile(r'^\s*[-*]\s*\*\*[A-Za-z][\w -]*:?\*\*', re.M)


def _target_head(meta: dict) -> str:
    """The path part of a `Location:`, stripped of line ranges and list-item noise."""
    t = (meta.get('target') or '').strip()
    t = t.lstrip('-*').strip().strip('`').strip()
    return t.split(':')[0].strip()


def propose(meta: dict) -> tuple[str | None, str]:
    """`(lane, why)` — or `(None, reason it needs a human)`."""
    head = _target_head(meta)
    if not head:
        return None, 'no Location: line, so there is no evidence to route on'

    low = head.lower()
    if low.endswith('.lean'):
        return None, ('a .lean target is `lean` OR `substrate` — "the theorem and the '
                      'implementation disagree" is a semantic property no path implies')
    if low.startswith('src/') or low.startswith('rust/') or low.startswith('notebooks/'):
        return None, ('physics code is `pyrust` unless it disagrees with a theorem, which '
                      'makes it `substrate` — read the finding')
    if low.startswith('tests/'):
        return None, 'a test target follows the lane of the code it covers — read the finding'
    if (low.endswith('.tex') or low.startswith('papers/') or low.startswith('figures/')
            or 'paper_draft' in low):
        return 'prose', _CONFIDENT[0][2]
    if low.startswith('scripts/') or low.startswith('.claude/'):
        return 'infra', _CONFIDENT[1][2]
    if low.startswith('docs/architecture/') or low in (
            'docs/wave_execution_pipeline.md', 'docs/readiness_gates.md',
            'docs/knowledge_graph.md', 'docs/check_authoring_guide.md'):
        return 'infra', _CONFIDENT[2][2]
    if low.startswith('docs/roadmaps/') or low.startswith('temporary/'):
        return None, ('a roadmap or working doc can carry any lane — it names scope, not '
                      'a work kind')
    if low.startswith('docs/'):
        return None, 'a docs/ target is `infra` or `prose` depending on the reader it serves'
    return None, f'no rule covers {head!r}'


def _sections(text: str) -> list[tuple[int, int]]:
    """`(body_start, body_end)` for each finding, matching the extractor's own split."""
    marks = [m for m in _bg._REVIEW_SECTION_RE.finditer(text)]
    out = []
    for i, m in enumerate(marks):
        end = marks[i + 1].start() if i + 1 < len(marks) else len(text)
        out.append((m.end(), end))
    return out


def _insert_lane(text: str, body_span: tuple[int, int], lane: str) -> str:
    """Put `- **Lane:** \\`x\\`` after the finding's last field line, or at the body's end.

    Placement matters only for readability — `_parse_finding_field` searches the whole body —
    but a field belongs with the other fields, not stranded after the prose.
    """
    start, end = body_span
    body = text[start:end]
    line = f'- **Lane:** `{lane}`\n'
    fields = list(_FIELD_LINE.finditer(body))
    if fields:
        at = body.index('\n', fields[-1].start()) + 1
    else:
        at = len(body.rstrip()) + 1 if body.strip() else 0
        line = '\n' + line
    return text[:start] + body[:at] + line + body[at:] + text[end:]


def collect(blocking_only: bool = True) -> list[dict]:
    """Every open finding that declares no lane, with a proposal attached."""
    from readiness_gates import BLOCKING_SEVERITIES
    out = []
    for n in _bg.extract_review_finding_nodes():
        m = n['meta']
        if m.get('status') != 'open' or m.get('lane') != 'unclassified':
            continue
        if blocking_only and m.get('severity') not in BLOCKING_SEVERITIES:
            continue
        lane, why = propose(m)
        out.append({'id': n['id'], 'review_file': m.get('review_file'),
                    'severity': m.get('severity'), 'target': m.get('target'),
                    'bundle': m.get('inferred_bundle'), 'paper': m.get('inferred_paper'),
                    'lane': lane, 'why': why,
                    'heading': (n.get('name') or '')[:120]})
    return out


def apply(items: list[dict], dry_run: bool = False) -> tuple[int, list[str]]:
    """Write each item's lane into its review document. Returns `(written, skipped)`."""
    by_file: dict[str, list[dict]] = {}
    for it in items:
        if it.get('lane'):
            by_file.setdefault(it['review_file'], []).append(it)

    written, skipped = 0, []
    for rel, group in sorted(by_file.items()):
        path = PROJECT_ROOT / rel
        if not path.is_file():
            skipped.append(f'{rel}: not on disk')
            continue
        text = path.read_text(encoding='utf-8')
        # Late-to-early, so an earlier insertion cannot shift a later span.
        spans = _sections(text)
        marks = [m for m in _bg._REVIEW_SECTION_RE.finditer(text)]
        wanted = {it['id']: it['lane'] for it in group}
        plan = []
        date_dir, review_name = Path(rel).parent.name, Path(rel).stem
        for (mk, span) in zip(marks, spans):
            # group(1) is the section number, group(2) the heading — the same positional
            # contract `extract_review_finding_nodes` uses. Reading them by any other route
            # is a second parser, and this file's whole point is that there is one.
            fid = _bg.mint_finding_id(date_dir, review_name, mk.group(1))
            if fid in wanted:
                plan.append((span, wanted[fid], fid))
        found = {f for _, _, f in plan}
        for fid in wanted:
            if fid not in found:
                skipped.append(f'{fid}: no section matched in {rel}')
        for span, lane, _fid in sorted(plan, key=lambda p: -p[0][0]):
            text = _insert_lane(text, span, lane)
            written += 1
        if not dry_run:
            path.write_text(text, encoding='utf-8')
    return written, skipped


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split('\n')[0])
    ap.add_argument('--propose', action='store_true', help='measure and report; write nothing')
    ap.add_argument('--apply', action='store_true', help='write the confident lanes')
    ap.add_argument('--from', dest='src', help='apply an adjudicated JSON instead')
    ap.add_argument('--json', help='write the proposal set here')
    ap.add_argument('--all-severities', action='store_true',
                    help='not just the blocking population')
    ap.add_argument('--dry-run', action='store_true')
    a = ap.parse_args(argv)

    items = (json.loads(Path(a.src).read_text(encoding='utf-8')) if a.src
             else collect(blocking_only=not a.all_severities))

    confident = [i for i in items if i.get('lane')]
    needs = [i for i in items if not i.get('lane')]
    print(f'{len(items)} open finding(s) with no declared lane')
    print(f'  {len(confident)} routable from evidence: '
          f'{dict(Counter(i["lane"] for i in confident))}')
    print(f'  {len(needs)} need adjudication:')
    for why, k in Counter(i['why'] for i in needs).most_common():
        print(f'     {k:4}  {why}')

    if a.json:
        Path(a.json).write_text(json.dumps(items, indent=2) + '\n', encoding='utf-8')
        print(f'  wrote {a.json}')

    if a.apply:
        written, skipped = apply(items, dry_run=a.dry_run)
        verb = 'would write' if a.dry_run else 'wrote'
        print(f'{verb} {written} lane declaration(s)')
        for s in skipped:
            print(f'  ⚠ skipped {s}')
    return 0


if __name__ == '__main__':
    raise SystemExit(main())
