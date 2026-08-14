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
    consumes up to the next sibling key or the entry's end rather than to the next newline.

    ⚠️ **THE LOOKAHEAD IS THE WHOLE CORRECTNESS ARGUMENT, AND THE FIRST VERSION WAS WRONG.**
    It read `'[a-z_]+':` — lowercase and underscore only — so a sibling key containing a digit
    or a capital did not terminate the match and `.*?` ran straight through it. Confirmed by
    probe: with `'iso_2019_ref'` sitting between `human_verified_notes` and `notes`, replacing
    the notes field **deleted the `iso_2019_ref` pair entirely**, and both guards below passed
    it (the file still parsed; the top-level entry count was unchanged). Same for an
    `8-space` comment line, which is how a `# value disputed, do not mark verified` caveat
    would vanish on a routine dashboard click.

    It now stops at any sibling key OR a comment line. `_assert_only_changed` is the real
    backstop; this pattern is the first line of defence, not the only one.
    """
    pat = re.compile(
        rf"(?ms)^(        '{re.escape(key)}': ).*?"
        rf"(?=\n        (?:'[A-Za-z0-9_]+':|#)|\Z)")
    return pat.subn(rf"\g<1>{literal.replace(chr(92), chr(92) * 2)},", body, count=1)


def _entry_keys(src: str, key: str) -> list[str] | None:
    """The key list of one `PARAMETER_PROVENANCE` entry, by AST. `None` if not found."""
    for node in ast.walk(ast.parse(src)):
        if not (isinstance(node, ast.Assign)
                and any(getattr(t, "id", None) == "PARAMETER_PROVENANCE"
                        for t in node.targets)
                and isinstance(node.value, ast.Dict)):
            continue
        for k, v in zip(node.value.keys, node.value.values):
            if isinstance(k, ast.Constant) and k.value == key and isinstance(v, ast.Dict):
                return [kk.value for kk in v.keys if isinstance(kk, ast.Constant)]
    return None


def _current_verified_date(src: str, key: str) -> tuple[str | None, bool]:
    """`(value, resolved)` for one entry's `human_verified_date`, by AST.

    `resolved` is False when the entry or the field cannot be found, or when the value is not
    a literal — every one of which is a reason to REFUSE rather than to proceed as though the
    field were unset. Comments, line wrapping and quoting style are all irrelevant to the
    AST, which is the entire reason it replaced a line-anchored regex here.
    """
    for node in ast.walk(ast.parse(src)):
        if not (isinstance(node, ast.Assign)
                and any(getattr(t, "id", None) == "PARAMETER_PROVENANCE"
                        for t in node.targets)
                and isinstance(node.value, ast.Dict)):
            continue
        for k, v in zip(node.value.keys, node.value.values):
            if not (isinstance(k, ast.Constant) and k.value == key
                    and isinstance(v, ast.Dict)):
                continue
            for kk, vv in zip(v.keys, v.values):
                if isinstance(kk, ast.Constant) and kk.value == "human_verified_date":
                    if isinstance(vv, ast.Constant):
                        return (vv.value, True)
                    return (None, False)      # present but not a literal — cannot judge
            return (None, False)              # entry found, field absent
    return (None, False)                      # entry not found


def _assert_only_changed(before: str, after: str, key: str,
                         allowed: set[str]) -> str | None:
    """`None` if the edit touched only `allowed` fields of `key`; else the reason it did not.

    ⚠️ **THIS IS THE GUARD THAT ACTUALLY WORKS.** Parsing and counting top-level entries —
    the original pair — is blind to everything *inside* the entry being edited, which is
    exactly where a regex edit does its damage. A swallowed sibling key leaves the file
    parseable and the entry count unchanged, so both original guards passed the mutation
    that deleted `iso_2019_ref`.
    """
    kb, ka = _entry_keys(before, key), _entry_keys(after, key)
    if kb is None or ka is None:
        return f"entry {key!r} could not be located after the edit"
    if kb != ka:
        lost, gained = sorted(set(kb) - set(ka)), sorted(set(ka) - set(kb))
        return (f"the edit changed {key}'s field list — lost {lost}, gained {gained}. "
                f"A regex edit that swallows a neighbouring field leaves the module "
                f"parseable and the entry count unchanged, which is why neither of those "
                f"checks catches it")
    return None


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
    # ⚠️ THE CURRENT VALUE COMES FROM THE AST, AND THE LINE REGEX IT REPLACES WAS A BYPASS.
    # It required the value to end the line at a comma (`': (.+?),\s*$'`), so a perfectly
    # ordinary trailing comment —
    #     'human_verified_date': '2020-01-01',  # signed off by the operator
    # — made the match fail, `current` read None, and the "already verified" refusal was
    # SKIPPED ENTIRELY. A recorded human verification would have been silently overwritten
    # by a routine confirm, on the registry backing a P1 gate. Constructed and confirmed.
    #
    # ⚠️ AND IT FAILS CLOSED. If the key is present but its value cannot be resolved, that is
    # a refusal, not a licence: "I could not read the current value" must never behave like
    # "there isn't one".
    current, resolved = _current_verified_date(src, key)
    if not resolved:
        return False, (f"{key}'s `human_verified_date` could not be resolved from the "
                       f"module — refusing rather than assuming it is unset")
    if current is not None and not force:
        return False, (f"{key} is already human-verified at {current!r} — pass force=True "
                       f"to overwrite. Silently replacing a recorded human verification is "
                       f"not a thing this writer does")

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
    # ⚠️ ORDER MATTERS AND I GOT IT WRONG FIRST. This guard parses `new_src`, so running it
    # before the SyntaxError check above turns a clean refusal ("would not parse") into an
    # uncaught exception out of the writer.
    reason = _assert_only_changed(src, new_src, key,
                                  {"human_verified_date", "human_verified_notes"})
    if reason:
        return False, f"{reason} — nothing written"

    if dry_run:
        return True, f"{key}: would set human_verified_date={stamp} (dry run)"

    _atomic_write(PROVENANCE_PATH, new_src)
    return True, f"{key}: human_verified_date={stamp}"


def withdraw_human_verified(key: str, notes: str, actor: str | None = None,
                            dry_run: bool = False) -> tuple[bool, str]:
    """Clear `human_verified_date` and record why. `(ok, message)`.

    ⚠️ **THE ASYMMETRY THIS EXISTS TO CLOSE WAS WORSE THAN THE ORIGINAL DEFECT.** When only
    `confirm` persisted, the dashboard's **Reject** button set `human_verified_date = None`
    in memory, rendered a red `REJECTED` badge, and changed nothing on disk — so a
    verification the operator had just retracted stayed on disk, kept the P1
    `ParameterProvenance` gate green, and **had no UI route to withdraw it**. Sign-off stuck;
    retraction evaporated. Before the writer existed, both were equally ephemeral and the
    surface was at least uniformly honest.

    **No `force` here, deliberately.** Withdrawing REDUCES what the tree claims; the guard on
    `set_human_verified` exists to stop a claim being overwritten silently, and refusing a
    retraction would keep an unwanted green in place — the opposite of what that guard is for.
    """
    note = (notes or "").strip() or "Withdrawn via the provenance dashboard"
    return _write_fields(key, {"human_verified_date": None,
                               "human_verified_notes": f"REJECTED: {note}"},
                         actor=actor, dry_run=dry_run,
                         what=f"withdrew human verification for {key}")


def annotate_human_verified(key: str, notes: str, actor: str | None = None,
                            dry_run: bool = False) -> tuple[bool, str]:
    """Record a concern WITHOUT touching the verification date. `(ok, message)`.

    The dashboard's **Flag** action. It deliberately leaves `human_verified_date` alone —
    flagging raises a question, it does not answer one — but it must still PERSIST, or the
    flag is a badge that vanishes on reload.
    """
    note = (notes or "").strip() or "Flagged via the provenance dashboard"
    return _write_fields(key, {"human_verified_notes": f"FLAGGED: {note}"},
                         actor=actor, dry_run=dry_run, what=f"flagged {key}")


def _write_fields(key: str, updates: dict[str, str | None], actor: str | None,
                  dry_run: bool, what: str) -> tuple[bool, str]:
    """Apply one entry's field updates atomically, with every guard `set_human_verified` uses.

    Shared so the three public operations cannot drift in their safety properties — the same
    reason `close_finding` imports the extractor's id minter instead of reimplementing it.
    """
    src = PROVENANCE_PATH.read_text(encoding="utf-8")
    span = _entry_span(src, key)
    if span is None:
        return False, f"unknown parameter key {key!r} — nothing written"
    start, end = span
    body = src[start:end]

    for field_name, value in updates.items():
        literal = "None" if value is None else _py_str(
            f"{value} [{actor}]" if actor else value)
        body, n = _replace_key(body, field_name, literal)
        if not n:
            return False, (f"{key} does not carry `{field_name}` — refusing rather than "
                           f"inventing it")

    new_src = src[:start] + body + src[end:]
    try:
        ast.parse(new_src)
    except SyntaxError as exc:
        return False, f"the edit would not parse ({exc}) — nothing written"
    if _count_entries(src) != _count_entries(new_src):
        return False, "the edit changed the entry count — nothing written"
    reason = _assert_only_changed(src, new_src, key, set(updates))
    if reason:
        return False, f"{reason} — nothing written"

    if dry_run:
        return True, f"{what} (dry run)"
    _atomic_write(PROVENANCE_PATH, new_src)
    return True, what


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
