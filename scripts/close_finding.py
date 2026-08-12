#!/usr/bin/env python3
"""Write a closure into the supersession ledger — the writer the ledger never had.

Why this exists
---------------
`docs/review_finding_supersessions.json` is the ONLY channel that can close a blocking
`ReviewFinding` (`build_graph.py`, the closure bar). It had **no writer**. All 870 records
were hand-typed into a 645 KB JSON file, and 66 of the `review:`-scheme ones carry a
`finding_id` that matches no minted node — inert, while the findings they meant to close
still read `open`.

This is the same shape of gap `scripts/record_review.py` was written to close for bundle
status, where "every green in the corpus was therefore a hand edit". **Nobody skips a
script. People skip a hand-edit** — and when they do not skip it, a hand-typed key is
wrong often enough to have produced that 66.

Load-bearing decisions
----------------------
* **`mint_finding_id` is IMPORTED from `build_graph`, never reimplemented.** A second
  minter reproduces the orphan class by construction. Precedent: `_recurrence_norm` moved
  to module scope after a period in which the production matcher could have been deleted
  or inverted with its test still green.
* **Writes are atomic** (temp-and-replace). A crash midway through rewriting the only
  closure channel leaves exactly the malformed-ledger state every reader is told to fail
  closed on.
* **A conflicting existing record is a REFUSAL, not an exception.** `_load_supersession_
  ledger` is last-wins and does not say so, so appending a second record with a different
  status means one of the pair silently does nothing — the defect this script exists to
  remove, reintroduced by its own writer.

⚠️ `--verify` runs `shell=True` against the repo root. It executes whatever the caller
supplies, so it is for operator-authored commands, never untrusted input.
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
import tempfile
from datetime import date as _date
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_ROOT = SCRIPT_DIR.parent
sys.path.insert(0, str(SCRIPT_DIR))

import build_graph as _bg  # noqa: E402  — after sys.path setup

LEDGER = PROJECT_ROOT / "docs" / "review_finding_supersessions.json"
VALID_STATUSES = ("fixed", "accepted", "reopened")
CLOSING_STATUSES = ("fixed", "accepted")
MIN_EVIDENCE = 40


def _live_ids() -> set[str]:
    return {n["id"] for n in _bg.extract_review_finding_nodes()}


def ids_for_doc(doc: str) -> list[str]:
    """Every minted id belonging to one review document — for the refusal message.

    Printing these is the difference between a tool that PREVENTS a broken key and one
    that merely complains about it: the caller sees the real section numbers instead of
    guessing at them.
    """
    prefix = _bg.mint_finding_id(Path(doc).parent.name, Path(doc).stem, "")
    return sorted(i for i in _live_ids() if i.startswith(prefix))


def close(doc: str, sections: list[str], status: str, evidence: str,
          commit: str | None = None, date: str | None = None,
          verify: str | None = None, superseded_by: str | None = None,
          dry_run: bool = False) -> tuple[bool, str]:
    """Close one or more findings from a single review document.

    Multiple sections write one record EACH, sharing the evidence string — meeting the
    need that produced hand-written keys like `…:D5:5.1+5.2+5.3` without breaking the
    one-id-per-record invariant the reader depends on.
    """
    if status not in VALID_STATUSES:
        return False, f"status={status!r} is not one of {VALID_STATUSES}"

    date_dir, review_name = Path(doc).parent.name, Path(doc).stem
    live = _live_ids()
    minted = [_bg.mint_finding_id(date_dir, review_name, s) for s in sections]

    missing = [m for m in minted if m not in live]
    if missing:
        have = ids_for_doc(doc)
        return False, (f"no such finding: {', '.join(missing)}. This document mints: "
                       f"{', '.join(have) if have else '(none)'}")

    if status in CLOSING_STATUSES and len(evidence.strip()) < MIN_EVIDENCE:
        return False, (f"evidence is {len(evidence.strip())} chars; the bar is "
                       f"{MIN_EVIDENCE}. A closure has to say what changed and where.")

    if not (commit or date):
        return False, "no anchor: pass --commit or --date"

    verified_by = None
    if verify:
        proc = subprocess.run(verify, shell=True, cwd=str(PROJECT_ROOT),
                              capture_output=True, text=True)
        if proc.returncode != 0:
            return False, (f"verify command failed (exit {proc.returncode}): {verify}\n"
                           f"{proc.stdout}{proc.stderr}")
        verified_by = {"command": verify, "exit_code": 0,
                       "run_at": _date.today().isoformat()}

    if not dry_run:
        try:
            _append(minted, status, evidence, commit, date, verified_by, superseded_by)
        except ValueError as exc:       # a conflicting pre-existing record
            return False, str(exc)

    verb = "would write" if dry_run else "wrote"
    return True, f"{verb} {len(minted)} record(s): {', '.join(minted)}"


def _append(minted, status, evidence, commit, date, verified_by, superseded_by) -> None:
    # Re-read immediately before writing, so a concurrent append is not clobbered.
    data = json.loads(LEDGER.read_text(encoding="utf-8"))
    existing = {e["finding_id"]: e for e in data["supersessions"]}   # last-wins, as the reader
    to_add = []
    for fid in minted:
        prior = existing.get(fid)
        if prior is not None and prior.get("status") == status:
            continue                                                # idempotent
        if prior is not None:
            raise ValueError(
                f"{fid} already carries status={prior.get('status')!r}; refusing to append "
                f"a conflicting {status!r}. The reader is last-wins and does not say so, "
                f"which is how a closure silently does nothing. Amend the existing record "
                f"deliberately instead.")
        rec = {"finding_id": fid, "status": status, "evidence": evidence,
               "superseded_by": superseded_by,
               "date": date or _date.today().isoformat()}
        if commit:
            rec["commit"] = commit
        if verified_by:
            rec["verified_by"] = verified_by
        to_add.append(rec)
    if not to_add:
        return
    data["supersessions"].extend(to_add)
    _atomic_write(data)


def _atomic_write(data: dict) -> None:
    """⚠️ Temp-and-replace. `LEDGER.write_text(json.dumps(...))` on a 645 KB file leaves a
    truncated ledger if the process dies mid-write — and every reader is told to fail
    closed on a malformed one, so a crash here would block every closure until repaired."""
    fd, tmp = tempfile.mkstemp(dir=str(LEDGER.parent), suffix=".tmp")
    try:
        with os.fdopen(fd, "w", encoding="utf-8") as fh:
            json.dump(data, fh, indent=2, ensure_ascii=False)
            fh.write("\n")
        os.replace(tmp, str(LEDGER))
    except BaseException:
        Path(tmp).unlink(missing_ok=True)
        raise


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(
        description="Record a ReviewFinding closure in the supersession ledger.")
    ap.add_argument("--doc", required=True,
                    help="review document containing the finding")
    ap.add_argument("--section", required=True, nargs="+",
                    help="one or more section numbers, e.g. 5.5 5.6")
    ap.add_argument("--status", required=True, choices=VALID_STATUSES)
    ap.add_argument("--evidence", required=True,
                    help=f"what changed and where (>= {MIN_EVIDENCE} chars to close)")
    ap.add_argument("--commit", help="commit anchoring the fix")
    ap.add_argument("--date", help="ISO date (either this or --commit is required)")
    ap.add_argument("--verify", help="command proving the fix; RUN before writing")
    ap.add_argument("--superseded-by", dest="superseded_by",
                    help="the re-review that confirmed it")
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args(argv)
    ok, msg = close(a.doc, a.section, a.status, a.evidence, a.commit, a.date,
                    a.verify, a.superseded_by, a.dry_run)
    print(("✓ " if ok else "✗ REFUSED — ") + msg)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
