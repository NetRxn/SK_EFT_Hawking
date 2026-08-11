"""The single serializer for per-bundle JSON blobs (TODO-D25).

WHY THIS EXISTS
---------------
`papers/<X>/bundle_metadata.json` and `papers/<X>/append_log.json` were written
by eleven call sites across five scripts, and they disagreed on `ensure_ascii`.
Whichever tool touched a blob last decided its encoding, so the corpus
oscillated and a one-field edit could rewrite hundreds of lines: seeding
`length_target` through a default-`ensure_ascii` writer produced **98
insertions / 91 deletions on `papers/D3/bundle_metadata.json` for a 9-line
change**.

Measured 2026-08-09, and the defect was TWICE the scope TODO-D25 recorded:

    bundle_metadata.json   21 files   20 raw-unicode    1 escaped
    append_log.json        20 files    2 raw-unicode   19 escaped

TODO-D25 scoped itself to `bundle_metadata.json` and named four writers. Both
file types carry the same defect, in opposite majority directions, across more
writers than the entry listed. Normalising only one of them would have left the
other free to keep oscillating.

THE DECISION, STATED
--------------------
`ensure_ascii=False` for both. The blobs carry `§` and `—` in their apex
`claims` strings, and the on-disk form a reviewer must read those claims through
should be the readable one. `\\u00a7` is not review-legible. This is also what
the most frequent writer (`write_metadata_counts`) already produced, so it is
the majority form for metadata and the direction the corpus was already drifting.

⚠️ Do NOT "fix" a diff by re-escaping. Route every write through here instead.
"""
from __future__ import annotations

import json
from pathlib import Path
from typing import Any


def dump_bundle_json(obj: Any) -> str:
    """Canonical text for a per-bundle JSON blob, trailing newline included.

    `ensure_ascii=False` is REQUIRED, not cosmetic — see the module docstring.
    `indent=2` and key order are preserved as-authored so a semantic diff stays
    a semantic diff; this function normalises encoding only.
    """
    return json.dumps(obj, indent=2, ensure_ascii=False) + "\n"


def write_bundle_json(path: str | Path, obj: Any) -> bool:
    """Write `obj` to `path` in canonical form. Returns True if bytes changed.

    A byte-identical write is skipped so the file's mtime is not disturbed —
    the same discipline as the `cluster_detect` writer (TODO-D29): other
    freshness checks key on mtime, and rewriting identical content would make
    a no-op look like a change.
    """
    p = Path(path)
    payload = dump_bundle_json(obj)
    try:
        if p.read_text(encoding="utf-8") == payload:
            return False
    except OSError:
        pass
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(payload, encoding="utf-8")
    return True
