"""One writer for `human_verified_date` — ADR-012 P9a Tasks 5 and 6.

WHY THIS FILE EXISTS
--------------------
`ParameterProvenance` is a P1 gate that blocks on `human_verified_date`, and there was **no
supported way to set it for one parameter**. Two half-writers existed and neither did the
job: the dashboard's confirm mutated an in-memory dict and wrote only an audit event, and
`wave2_flip_provenance.py` wrote the file with a **frozen** date, matching only entries
literally holding `None`.

The badge and the persisted badge are the same markup, so the only way to tell them apart
is to reload — which is why the browser case for this lives in `tests/e2e/`, and why this
file cannot be the whole gate.
"""
from __future__ import annotations

import ast
import inspect
import sys
from pathlib import Path

import pytest

ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(ROOT))
sys.path.insert(0, str(ROOT / "scripts"))

from src.core import provenance_writer as pw  # noqa: E402


@pytest.fixture
def sandbox(tmp_path, monkeypatch):
    """A COPY of the real registry. Every test writes to the copy, so a failure cannot
    leave `src/core/provenance.py` mutated — this module's whole job is editing that file
    in place, and a test that damages it breaks every importer in the repo."""
    dst = tmp_path / "provenance.py"
    dst.write_text(pw.PROVENANCE_PATH.read_text(encoding="utf-8"), encoding="utf-8")
    monkeypatch.setattr(pw, "PROVENANCE_PATH", dst)
    return dst


def _first_unverified(path: Path) -> str:
    src = path.read_text(encoding="utf-8")
    for m in __import__("re").finditer(r"(?m)^    '([A-Za-z0-9_.+-]+)': \{", src):
        span = pw._entry_span(src, m.group(1))
        if span and "'human_verified_date': None," in src[span[0]:span[1]]:
            return m.group(1)
    raise AssertionError("no unverified entry in the registry — fixture is vacuous")


# ── The contract ──────────────────────────────────────────────────────────────────────

def test_one_entry_is_written_to_the_source_file(sandbox):
    key = _first_unverified(sandbox)
    ok, msg = pw.set_human_verified(key, date="2026-08-12", notes="confirmed against CODATA")
    assert ok, msg
    body = sandbox.read_text(encoding="utf-8")
    span = pw._entry_span(body, key)
    entry = body[span[0]:span[1]]
    assert "'human_verified_date': '2026-08-12'," in entry
    assert "confirmed against CODATA" in entry


def test_the_date_is_a_PARAMETER_not_a_module_constant():
    """⚠️ `wave2_flip_provenance.VERIFY_DATE` is frozen at 2026-04-28. A writer that stamps
    today's confirmation with a date from months ago is worse than one that refuses."""
    assert "date" in inspect.signature(pw.set_human_verified).parameters


def test_it_defaults_to_TODAY_rather_than_a_frozen_constant(sandbox):
    from datetime import date as _d
    key = _first_unverified(sandbox)
    ok, msg = pw.set_human_verified(key)
    assert ok and _d.today().isoformat() in msg


def test_an_unknown_key_is_refused_and_writes_nothing(sandbox):
    before = sandbox.read_text(encoding="utf-8")
    ok, msg = pw.set_human_verified("NOT_A_REAL_PARAMETER", date="2026-08-12")
    assert not ok and "unknown parameter key" in msg
    assert sandbox.read_text(encoding="utf-8") == before


def test_a_malformed_date_is_refused(sandbox):
    """A bad date still reads as PRESENT to the gate, so coercing it would manufacture a
    verification. Refuse."""
    before = sandbox.read_text(encoding="utf-8")
    ok, msg = pw.set_human_verified(_first_unverified(sandbox), date="2026-8-1")
    assert not ok and "YYYY-MM-DD" in msg
    assert sandbox.read_text(encoding="utf-8") == before


def test_an_existing_verification_is_not_silently_overwritten(sandbox):
    key = _first_unverified(sandbox)
    assert pw.set_human_verified(key, date="2026-08-12")[0]
    ok, msg = pw.set_human_verified(key, date="2026-08-13")
    assert not ok and "already human-verified" in msg
    assert pw.set_human_verified(key, date="2026-08-13", force=True)[0]


def test_dry_run_reports_what_it_would_do_and_writes_nothing(sandbox):
    before = sandbox.read_text(encoding="utf-8")
    ok, msg = pw.set_human_verified(_first_unverified(sandbox), date="2026-08-12",
                                   dry_run=True)
    assert ok and "dry run" in msg
    assert sandbox.read_text(encoding="utf-8") == before


def test_the_edit_preserves_every_other_entry(sandbox):
    """⚠️ THE FAILURE THAT WOULD BE INVISIBLE. This edits SOURCE TEXT, and a regex that
    swallowed a neighbour would produce a module that still imports — with a parameter
    silently gone. `ParameterProvenance` reads a missing parameter as one that never
    needed verifying, which is absence rendered as success inside the registry the gate
    is built on."""
    before_src = sandbox.read_text(encoding="utf-8")
    key = _first_unverified(sandbox)
    assert pw.set_human_verified(key, date="2026-08-12")[0]
    after_src = sandbox.read_text(encoding="utf-8")
    assert pw._count_entries(before_src) == pw._count_entries(after_src) > 100
    ast.parse(after_src)


def test_a_sibling_field_with_a_DIGIT_in_its_name_is_not_swallowed(sandbox):
    """⚠️ CONSTRUCTED AND CONFIRMED BY REVIEW, NOT IMAGINED. `_replace_key`'s lookahead was
    `'[a-z_]+':` — no digits, no capitals — so `.*?` ran straight through a sibling like
    `iso_2019_ref` and deleted the whole pair. The file still parsed and the top-level entry
    count was unchanged, **so both of the original guards passed it.**

    That is why `_assert_only_changed` exists: parsing and counting entries are blind to
    everything INSIDE the entry being edited, which is precisely where a regex edit does its
    damage."""
    src = sandbox.read_text(encoding="utf-8")
    key = _first_unverified(sandbox)
    span = pw._entry_span(src, key)
    injected = src[:span[0]] + src[span[0]:span[1]].replace(
        "        'human_verified_notes': None,\n",
        "        'human_verified_notes': None,\n"
        "        'iso_2019_ref': 'ISO 80000-1:2022',\n", 1) + src[span[1]:]
    sandbox.write_text(injected, encoding="utf-8")

    ok, msg = pw.set_human_verified(key, date="2026-08-12", notes="probe")
    after = sandbox.read_text(encoding="utf-8")
    assert "iso_2019_ref" in after, (
        f"the sibling field was deleted by a routine verification write (ok={ok}, {msg})")
    assert ok, msg


def test_an_adjacent_CAVEAT_COMMENT_is_not_swallowed(sandbox):
    """The same defect in its most dangerous form: `# do not mark verified, value disputed`
    sitting beside the field, deleted by the click it was written to prevent."""
    src = sandbox.read_text(encoding="utf-8")
    key = _first_unverified(sandbox)
    span = pw._entry_span(src, key)
    caveat = "        # DO NOT MARK VERIFIED: value disputed, see audit 2026-08-01\n"
    injected = src[:span[0]] + src[span[0]:span[1]].replace(
        "        'human_verified_notes': None,\n",
        caveat + "        'human_verified_notes': None,\n", 1) + src[span[1]:]
    sandbox.write_text(injected, encoding="utf-8")

    pw.set_human_verified(key, date="2026-08-12", notes="probe")
    assert "DO NOT MARK VERIFIED" in sandbox.read_text(encoding="utf-8"), (
        "the caveat comment was deleted by the write it warned against")


# ── Withdraw and annotate — the two buttons that used to lie ──────────────────────────

def test_reject_WITHDRAWS_the_verification_on_disk(sandbox):
    """⚠️ THE ASYMMETRY THAT WAS WORSE THAN THE ORIGINAL DEFECT. With only `confirm`
    persisting, Reject cleared the date in memory, rendered a red badge, and left the
    verification on disk — still green to the P1 gate, with no route to withdraw it."""
    key = _first_unverified(sandbox)
    assert pw.set_human_verified(key, date="2026-08-12")[0]
    ok, msg = pw.withdraw_human_verified(key, "source is wrong", actor="user:test")
    assert ok, msg
    entry = _entry_text(sandbox, key)
    assert "'human_verified_date': None," in entry
    assert "REJECTED: source is wrong" in entry


def test_withdrawing_needs_no_FORCE(sandbox):
    """Withdrawing REDUCES what the tree claims. The force guard exists to stop a claim
    being overwritten silently; refusing a retraction would keep an unwanted green in
    place — the opposite of what that guard is for."""
    key = _first_unverified(sandbox)
    assert pw.set_human_verified(key, date="2026-08-12")[0]
    assert pw.withdraw_human_verified(key, "retract")[0]


def test_flag_persists_and_leaves_the_DATE_alone(sandbox):
    """Flagging raises a question rather than answering one — but a flag that vanishes on
    reload is a badge, not a record."""
    key = _first_unverified(sandbox)
    assert pw.set_human_verified(key, date="2026-08-12")[0]
    assert pw.annotate_human_verified(key, "check the units")[0]
    entry = _entry_text(sandbox, key)
    assert "'human_verified_date': '2026-08-12'," in entry
    assert "FLAGGED: check the units" in entry


def test_every_write_path_refuses_an_unknown_key(sandbox):
    before = sandbox.read_text(encoding="utf-8")
    for fn in (pw.withdraw_human_verified, pw.annotate_human_verified):
        ok, msg = fn("NOT_A_REAL_PARAMETER", "x")
        assert not ok and "unknown parameter key" in msg
    assert sandbox.read_text(encoding="utf-8") == before


def _entry_text(path: Path, key: str) -> str:
    src = path.read_text(encoding="utf-8")
    span = pw._entry_span(src, key)
    return src[span[0]:span[1]]


def test_a_write_that_would_not_parse_is_refused(sandbox, monkeypatch):
    """SEEDED: force the replacement to emit a broken literal and confirm nothing lands."""
    before = sandbox.read_text(encoding="utf-8")
    monkeypatch.setattr(pw, "_py_str", lambda v: "'unterminated")
    ok, msg = pw.set_human_verified(_first_unverified(sandbox), date="2026-08-12")
    assert not ok and "would not parse" in msg
    assert sandbox.read_text(encoding="utf-8") == before


# ── The single-writer property ────────────────────────────────────────────────────────

def _calls(relpath: str) -> set[str]:
    tree = ast.parse((ROOT / relpath).read_text(encoding="utf-8"))
    out = set()
    for c in ast.walk(tree):
        if isinstance(c, ast.Call):
            f = c.func
            out.add(getattr(f, "id", None) or getattr(f, "attr", None))
    return out - {None}


def test_the_bulk_script_CALLS_the_writer_rather_than_reimplementing_it():
    """Two implementations of one write is how they drift — and these two already HAD.

    ⚠️ VIA `ast`, ASSERTING THE CALL. `CHECK_AUTHORING_GUIDE.md` §2.5: a substring scan for
    the helper's name finds it in the comment that explains why it is used. The comment
    above the call says `set_human_verified` in prose.
    """
    called = _calls("scripts/wave2_flip_provenance.py")
    assert "set_human_verified" in called, "the bulk script does not call the shared writer"
    assert "write_text" not in called, (
        "the bulk script still writes provenance.py itself — a second implementation of "
        "the one write this module exists to own")


def test_the_dashboard_confirm_path_CALLS_the_writer():
    """The badge must follow the write. Asserting the call, not the import: importing and
    not calling is exactly the shape that would render green over nothing."""
    assert "set_human_verified" in _calls("scripts/provenance_dashboard.py")


def _func_calls(relpath: str, func: str) -> set[str]:
    """Call names inside ONE function — not the whole module."""
    tree = ast.parse((ROOT / relpath).read_text(encoding="utf-8"))
    fn = next((n for n in ast.walk(tree)
               if isinstance(n, ast.FunctionDef) and n.name == func), None)
    assert fn is not None, f"{func} not found in {relpath}"
    out = set()
    for c in ast.walk(fn):
        if isinstance(c, ast.Call):
            out.add(getattr(c.func, "id", None) or getattr(c.func, "attr", None))
    return out - {None}


def test_the_write_is_atomic():
    """A crash midway through rewriting `provenance.py` breaks every importer in the repo
    at once — the graph builder, the dashboard, the gates and `validate.py` together.

    ⚠️ **THE FIRST VERSION OF THIS TEST COULD NOT FAIL.** It asserted `"replace" in
    _calls(module)` — a MODULE-WIDE call set that already contains `str.replace`, from
    `literal.replace(chr(92), …)` in `_replace_key`. Confirmed by mutation: swapping
    `os.replace(tmp, path)` for a plain `path.write_text(...)` left all thirteen tests
    green. The single test naming atomicity was satisfied by an unrelated string method.
    Scope the assertion to the function that must be atomic.
    """
    inner = _func_calls("src/core/provenance_writer.py", "_atomic_write")
    assert "mkstemp" in inner and "replace" in inner, (
        f"`_atomic_write` no longer does temp-and-replace (calls: {sorted(inner)})")
    assert "write_text" not in _func_calls(
        "src/core/provenance_writer.py", "set_human_verified"), (
        "the writer bypasses `_atomic_write` and writes the registry directly")


def test_the_dashboard_calls_the_writer_FROM_THE_VERIFY_ROUTE():
    """Scoped to the route. A module-wide assertion stays green if the call is moved into
    dead code, which is the shape that would render a badge over nothing."""
    for fn in ("verify_param",):
        calls = _func_calls("scripts/provenance_dashboard.py", fn)
        assert {"set_human_verified", "withdraw_human_verified",
                "annotate_human_verified"} <= calls, (
            f"{fn} does not route all three actions through the writer (calls: "
            f"{sorted(c for c in calls if 'verified' in c)})")


def test_the_write_flag_message_no_longer_names_the_bulk_sweep_as_the_route():
    """⚠️ NEVER LEAVE A MESSAGE THAT DESCRIBES A DEFECT THAT HAS BEEN FIXED. `--write`
    used to route the user to `wave2_flip_provenance.py` as "a real writer"; that was true
    and is now misleading, because the sweep stamps a frozen date and cannot revise an
    entry at all."""
    src = (ROOT / "scripts" / "provenance_dashboard.py").read_text(encoding="utf-8")
    i = src.index("if args.write:")
    block = src[i:i + 1800]
    assert "provenance_writer" in block, "the refusal does not name the supported route"
    assert "wave2_flip_provenance.py`, which does persist" not in block, (
        "the refusal still advertises the bulk sweep as the way to persist a verification")
