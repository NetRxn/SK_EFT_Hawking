#!/usr/bin/env python3
"""Citation verification cache helpers (Phase 5v Wave 6).

Read/append/lookup helpers for docs/citation_verifications.jsonl. Used
by the adversarial-reviewer agent to avoid re-fetching arXiv / DOI
metadata for bibitems whose content hasn't changed since the last
verification.

Usage:
    # Hash a bibitem's content (normalized)
    h = bibitem_hash("A. Author, B. Writer, \"Title,\" Journal 1, 2 (2025).")

    # Look up most recent verification for (bibkey, hash)
    rec = lookup_latest("Author2025", h)
    if rec and rec['verdict'] == 'match' and not is_stale(rec):
        # skip re-fetch — still good
        ...

    # After fetching, append a new record
    append_record({
        "bibkey": "Author2025",
        "paper": "paper1_first_order",
        "bibitem_hash": h,
        "arxiv_id": "2408.17292",
        "fetched_title": "…",
        "fetched_authors": "Author, B., et al.",
        "verdict": "match",
        "detail": "arXiv abstract title matches bibitem title",
        "verified_date": datetime.now(timezone.utc).isoformat(timespec='seconds'),
        "reviewer": "adversarial-reviewer",
    })
"""
from __future__ import annotations

import hashlib
import json
import re
import sys
from datetime import datetime, timezone, timedelta
from pathlib import Path
from typing import Optional

PROJECT_ROOT = Path(__file__).resolve().parent.parent
CACHE_PATH = PROJECT_ROOT / "docs" / "citation_verifications.jsonl"
STALENESS_DAYS = 90


def bibitem_hash(bibitem_text: str) -> str:
    """Normalize bibitem text and return sha256.

    Normalization: lowercase, collapse whitespace, strip LaTeX formatting
    commands (\\emph, \\textbf, \\textit, etc.), strip surrounding braces.
    This means minor formatting edits don't invalidate the cache; content
    changes do.
    """
    t = bibitem_text
    t = re.sub(r'\\[a-zA-Z]+\{([^}]*)\}', r'\1', t)   # \emph{x} -> x
    t = re.sub(r'\\[a-zA-Z]+\*?', ' ', t)              # stray commands -> space
    t = re.sub(r'[{}]', '', t)                         # strip braces
    t = re.sub(r'\s+', ' ', t).strip().lower()
    return hashlib.sha256(t.encode('utf-8')).hexdigest()


def _iter_records():
    """Yield every record line, skipping schema headers."""
    if not CACHE_PATH.exists():
        return
    with open(CACHE_PATH) as f:
        for line in f:
            line = line.strip()
            if not line:
                continue
            try:
                rec = json.loads(line)
            except json.JSONDecodeError:
                continue
            # Schema header lines carry _schema_version etc. — skip
            if rec.get('_schema_version') is not None:
                continue
            yield rec


def lookup_latest(bibkey: str, h: str) -> Optional[dict]:
    """Return the most-recent record for (bibkey, bibitem_hash), or None."""
    best = None
    best_date = None
    for rec in _iter_records():
        if rec.get('bibkey') != bibkey or rec.get('bibitem_hash') != h:
            continue
        d = rec.get('verified_date', '')
        if best_date is None or d > best_date:
            best = rec
            best_date = d
    return best


def is_stale(record: dict, days: int = STALENESS_DAYS) -> bool:
    """A record is stale if older than `days`."""
    try:
        verified = datetime.fromisoformat(record['verified_date'].replace('Z', '+00:00'))
    except (KeyError, ValueError):
        return True
    now = datetime.now(timezone.utc)
    return (now - verified) > timedelta(days=days)


def append_record(record: dict) -> None:
    """Append a verification record. Caller must populate verdict +
    verified_date. No deduplication — most-recent-wins is enforced at
    lookup time."""
    required = {'bibkey', 'bibitem_hash', 'verdict', 'verified_date'}
    missing = required - set(record.keys())
    if missing:
        raise ValueError(f"citation cache record missing required fields: {sorted(missing)}")
    CACHE_PATH.parent.mkdir(parents=True, exist_ok=True)
    with open(CACHE_PATH, 'a') as f:
        f.write(json.dumps(record, separators=(',', ':')) + '\n')


def stats() -> dict:
    """Return summary of the cache for the dashboard / CLI."""
    from collections import Counter
    verdicts = Counter()
    by_reviewer = Counter()
    stale_count = 0
    total = 0
    for rec in _iter_records():
        total += 1
        verdicts[rec.get('verdict', '?')] += 1
        by_reviewer[rec.get('reviewer', '?')] += 1
        if is_stale(rec):
            stale_count += 1
    return {
        'total_records': total,
        'verdicts': dict(verdicts),
        'by_reviewer': dict(by_reviewer),
        'stale_records': stale_count,
        'staleness_days': STALENESS_DAYS,
    }


def main():
    import argparse
    ap = argparse.ArgumentParser(description="Citation verification cache helper")
    ap.add_argument('--stats', action='store_true', help='Print cache summary')
    ap.add_argument('--lookup', metavar='BIBKEY', help='Look up latest verification for bibkey')
    args = ap.parse_args()
    if args.stats:
        print(json.dumps(stats(), indent=2))
    elif args.lookup:
        for rec in _iter_records():
            if rec.get('bibkey') == args.lookup:
                print(json.dumps(rec, indent=2))
    else:
        ap.print_help()


if __name__ == '__main__':
    main()
