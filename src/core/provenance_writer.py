"""The single per-entry writer for `PARAMETER_PROVENANCE` human-verification fields.

WHY THIS MODULE EXISTS
----------------------
`ParameterProvenance` is a **P1 readiness gate** that blocks on `human_verified_date`, and
until now there was **no supported way to set that field for one parameter**. The two
halves of the job were disjoint and neither did it:

* `provenance_dashboard.verify_param` (`/verify`) mutated the imported
  `PARAMETER_PROVENANCE` dict **in memory** and wrote only a change-bus event. The green
  **HUMAN VERIFIED** badge it rendered is byte-identical to a persisted one and reverts on
  the next page load — Pipeline Invariant #8, and ADR-012 D15's *"a control surface whose
  approve button does not persist cannot be the sign-off tool"*.
* `scripts/wave2_flip_provenance.py` wrote the file, but as a bulk regex sweep stamping a
  **frozen** `VERIFY_DATE`, matching only entries whose value is literally `None`. It
  therefore cannot record today's confirmation, and cannot revise an existing one at all.

⚠️ **`force` is not defensive scaffolding.** The bulk sweep's `HUMAN_NULL_RE` requires the
literal pair `'human_verified_date': None,` / `'human_verified_notes': None,`, so *revising*
a verified entry was impossible by any supported route. Overwriting a human's recorded
verification is a real decision, so it is available and explicit rather than silent.

THE WRITE IS ATOMIC, AND THAT IS NOT DECORATION
-----------------------------------------------
Temp-and-replace, the same shape as `close_finding._atomic_write`. A crash midway through
rewriting `provenance.py` produces a syntactically broken module that every importer in the
repo fails on — the graph builder, the dashboard, the readiness gates and `validate.py`
together. See ADR-004's single-writer posture, which this extends rather than weakens.

⚠️ **This module edits SOURCE TEXT, not a data file**, because `provenance.py` is a Python
module carrying prose, structure and comments a round-trip would destroy. The edit is
therefore anchored per entry and per key, and it **verifies the result parses and still
carries the same number of entries** before replacing the original. A rewrite that silently
dropped an entry would read to `ParameterProvenance` as a parameter that never needed
verifying.
"""
from __future__ import annotations

import ast
import os
import re
import tempfile
from datetime import date as _date
from pathlib import Path

#: The module this writer owns. Resolved from THIS file's location, never from cwd —
#: `harness_common_cli.py` resolving a repo from cwd and failing open is a recorded defect.
PROVENANCE_PATH = Path(__file__).resolve().parent / "provenance.py"

#: `YYYY-MM-DD`. Rejected rather than coerced: a malformed date in this field reaches the
#: readiness gate as a *present* value, so a typo would read as verified.
_DATE_RE = re.compile(r"^\d{4}-\d{2}-\d{2}$")


def _entry_span(src: str, key: str) -> tuple[int, int] | None:
    """`(start, end)` character offsets of one top-level entry's body, or `None`.

    Top-level entries are indented exactly four spaces and terminated by `    },` — the
    same anchor `wave2_flip_provenance.ENTRY_RE` uses, kept identical on purpose so the two
    routes cannot disagree about where an entry begins and ends.
    """
    m = re.search(rf"(?m)^    {re.escape(repr(key))}: \{{", src)
    if not m:
        m = re.search(rf"(?m)^    '{re.escape(key)}': \{{", src)
    if not m:
        return None
    end = src.find("\n    },", m.end())
    return (m.end(), end) if end != -1 else None


def _py_str(value: str) -> str:
    """A single-quoted Python literal. `repr` handles the escaping; this asserts the
    quoting style the file uses so a written entry is indistinguishable from a hand one."""
    r = repr(value)
    return r if r.startswith("'") else "'" + r[1:-1].replace("'", "\\'") + "'"


def _replace_key(body: str, key: str, literal: str) -> tuple[str, int]:
    """Replace one `'key': <value>,` inside an entry body. Returns `(body, n_replaced)`.

    ⚠️ The value may span lines (the notes strings are long and wrapped), so the pattern
    consumes up to the next key or the entry's end rather than to the next newline.
    """
    pat = re.compile(
        rf"(?ms)^(        '{re.escape(key)}': ).*?(?=\n        '[a-z_]+': |\Z)")
    return pat.subn(rf"\g<1>{literal.replace(chr(92), chr(92) * 2)},", body, count=1)


def set_human_verified(
    key: str,
    date: str | None = None,
    notes: str = "",
    actor: str | None = None,
    dry_run: bool = False,
    force: bool = False,
) -> tuple[bool, str]:
    """Record a human verification for exactly one parameter. `(ok, message)`.

    Refuses — never partially writes — when the key is unknown, the date is malformed, or
    the entry already carries a non-null `human_verified_date` and `force` is not set.

    `date` defaults to **today**, which is the point: `wave2_flip_provenance.VERIFY_DATE` is
    frozen at a date months in the past, and a writer that stamps today's confirmation with
    it is worse than one that refuses.
    """
    stamp = date or _date.today().isoformat()
    if not _DATE_RE.match(stamp):
        return False, (f"date {stamp!r} is not YYYY-MM-DD — refusing, because a malformed "
                       f"date still reads as PRESENT to the ParameterProvenance gate")

    src = PROVENANCE_PATH.read_text(encoding="utf-8")
    span = _entry_span(src, key)
    if span is None:
        return False, f"unknown parameter key {key!r} — nothing written"

    start, end = span
    body = src[start:end]
    current = re.search(r"^        'human_verified_date': (.+?),\s*$", body, re.M)
    if current and current.group(1).strip() != "None" and not force:
        return False, (f"{key} is already human-verified at {current.group(1)} — pass "
                       f"force=True to overwrite. Silently replacing a recorded human "
                       f"verification is not a thing this writer does")

    note = notes.strip() or "Confirmed via the provenance dashboard"
    if actor:
        note = f"{note} [{actor}]"
    new_body, n_date = _replace_key(body, "human_verified_date", _py_str(stamp))
    new_body, n_note = _replace_key(new_body, "human_verified_notes", _py_str(note))
    if not (n_date and n_note):
        return False, (f"{key} does not carry both human_verified_date and "
                       f"human_verified_notes — refusing rather than inventing them")

    new_src = src[:start] + new_body + src[end:]

    # ⚠️ VERIFY BEFORE REPLACING. A regex edit to source text can produce a module that
    # imports but has lost an entry, and a lost entry reads to the readiness gate as a
    # parameter that never needed verifying — absence rendered as success, in the registry
    # the gate is built on.
    try:
        tree = ast.parse(new_src)
    except SyntaxError as exc:
        return False, f"the edit would not parse ({exc}) — nothing written"
    before, after = _count_entries(src), _count_entries(new_src)
    if before != after:
        return False, (f"the edit changed the entry count {before} -> {after} — nothing "
                       f"written")
    del tree

    if dry_run:
        return True, f"{key}: would set human_verified_date={stamp} (dry run)"

    _atomic_write(PROVENANCE_PATH, new_src)
    return True, f"{key}: human_verified_date={stamp}"


def _count_entries(src: str) -> int:
    """Top-level keys of `PARAMETER_PROVENANCE`, by AST — never by counting braces."""
    for node in ast.walk(ast.parse(src)):
        if (isinstance(node, ast.Assign)
                and any(getattr(t, "id", None) == "PARAMETER_PROVENANCE"
                        for t in node.targets)
                and isinstance(node.value, ast.Dict)):
            return len(node.value.keys)
    return -1


def _atomic_write(path: Path, text: str) -> None:
    """Temp-and-replace in the target's own directory, so `os.replace` is atomic."""
    fd, tmp = tempfile.mkstemp(dir=str(path.parent), prefix=path.name, suffix=".tmp")
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as fh:
            fh.write(text)
        os.replace(tmp, path)
    except BaseException:
        Path(tmp).unlink(missing_ok=True)
        raise
