#!/usr/bin/env python3
"""Write a closure into the supersession ledger — the writer the ledger never had.

Why this exists
---------------
`docs/review_finding_supersessions.json` is the ONLY channel that can close a
`ReviewFinding` (`build_graph.py`, the closure bar — which applies at every severity since
2026-08-12). It had **no writer**: every record was hand-typed into a large JSON file, and a
substantial minority of the `review:`-scheme ones carry a `finding_id` that matches no
minted node — inert, while the findings they meant to close still read `open`.
`ledger_ids_resolve` owns that population and its ratchet; **read the live number there**,
never from a docstring that ages.

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
* **A matching existing record is only idempotent if it MEETS THE BAR.** A prior
  `{"finding_id": X, "status": "fixed"}` with no evidence closes nothing; skipping the write
  because the status already matches would report success over a finding that stays `open`.
* **The finding's declared `Verify:` command is what runs.** `verified_by` is the strongest
  evidence in the ledger, so it may not be satisfied by an unrelated command that happens to
  exit 0.

⚠️ Verification runs `shell=True` against the repo root — the declared command from the
review document, or `--verify` when the finding declares none. Both are authored inside this
repo; neither is untrusted input, and neither is taken from a network source.
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


def _norm_cmd(cmd: str) -> str:
    """Whitespace-insensitive comparison. `a  b` and `a b` are the same command."""
    return " ".join((cmd or "").strip().strip("`").split())


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
    nodes = {n["id"]: n for n in _bg.extract_review_finding_nodes()}
    minted = [_bg.mint_finding_id(date_dir, review_name, s) for s in sections]

    missing = [m for m in minted if m not in nodes]
    if missing:
        have = ids_for_doc(doc)
        return False, (f"no such finding: {', '.join(missing)}. This document mints: "
                       f"{', '.join(have) if have else '(none)'}")

    if status in CLOSING_STATUSES and len(evidence.strip()) < MIN_EVIDENCE:
        return False, (f"evidence is {len(evidence.strip())} chars; the bar is "
                       f"{MIN_EVIDENCE}. A closure has to say what changed and where.")

    if not (commit or date):
        return False, "no anchor: pass --commit or --date"

    ok, verified_by, msg = _run_verifications(minted, nodes, verify, status)
    if not ok:
        return False, msg

    try:
        to_add, already = _plan(minted, nodes, status, evidence, commit, date,
                               verified_by, superseded_by)
    except ValueError as exc:           # a conflicting or sub-bar pre-existing record
        return False, str(exc)

    if not dry_run and to_add:
        _write(to_add)

    verb = "would write" if dry_run else "wrote"
    body = ", ".join(r["finding_id"] for r in to_add) or "(nothing)"
    # ⚠️ Name BOTH populations. "wrote 2 record(s)" over a batch where one was already
    # recorded is a false count in the tool's own success line.
    tail = (f"; {len(already)} already recorded: {', '.join(already)}"
            if already else "")
    return True, f"{verb} {len(to_add)} record(s): {body}{tail}"


def _run_verifications(minted, nodes, verify, status: str = "fixed") -> tuple[bool, dict, str]:
    """Run each finding's verification command and record what actually ran.

    ⚠️ **The finding's OWN `Verify:` line is authoritative.** `verified_by` is the strongest
    evidence in the ledger — it is what makes the bar's Verify leg non-vacuous — and a
    record carrying `exit_code: 0` reads to every consumer as *the declared check passed*.
    Accepting any command the closer happened to pass would let `--verify true` stand in for
    the real check, which is absence of measurement rendered as success, in the field
    designed to prevent exactly that.

    So: when the finding declares a command, it is RUN. Passing a different one is a
    refusal, not an override — and passing none is not a way around it.

    ⚠️ **`accepted` RECORDS the verify, it does not ENFORCE it** — and the distinction is
    what makes the status reachable at all. `accepted` means *a decision not to fix*, so
    its verify normally encodes the very state the decision declines to change and will
    exit non-zero by construction. Gating on it made `accepted` unreachable exactly when
    it was needed: found 2026-08-14 on `review:2026-08-14-l1-stage13:L1:3.2`, whose verify
    asserts a Lean dependency the module must NOT have. The outcome is still recorded in
    `verified_by` — a non-zero exit at acceptance is the useful forensic datum, not a
    reason to refuse the write. `fixed` is unchanged and still fails closed.
    """
    enforce = status != "accepted"
    verified_by: dict[str, dict] = {}
    for fid in minted:
        declared = ((nodes[fid].get("meta") or {}).get("verify") or "").strip().strip("`")
        if verify and declared and _norm_cmd(verify) != _norm_cmd(declared):
            return False, {}, (
                f"{fid} declares a verification command and --verify is a different one.\n"
                f"  declared: {declared}\n  passed:   {verify}\n"
                f"Closing on an unrelated command records exit_code=0 against a check that "
                f"never ran. Run the declared command, or amend the finding's Verify: line.")
        cmd = (verify or declared or "").strip()
        if not cmd:
            continue
        proc = subprocess.run(cmd, shell=True, cwd=str(PROJECT_ROOT),
                              capture_output=True, text=True)
        if proc.returncode != 0 and enforce:
            return False, {}, (f"verify command failed (exit {proc.returncode}): {cmd}\n"
                               f"{proc.stdout}{proc.stderr}")
        verified_by[fid] = {"command": cmd, "declared": declared or None,
                            "exit_code": proc.returncode,
                            "enforced": enforce,
                            "run_at": _date.today().isoformat()}
    return True, verified_by, ""


def _plan(minted, nodes, status, evidence, commit, date, verified_by, superseded_by):
    """`(to_add, already)` — or raise. Shared by the real write AND `--dry-run`.

    ⚠️ Planning is separate from writing so that `--dry-run` previews the REFUSALS. When
    the conflict scan lived inside the writer, a dry run reported `would write 2 record(s)`
    for a batch the real invocation refused — a preview that cannot show the thing it is
    previewing.
    """
    data = _read_ledger()
    existing = {e.get("finding_id"): e for e in data["supersessions"]}  # last-wins, as the reader
    to_add, already = [], []
    for fid in minted:
        prior = existing.get(fid)
        if prior is not None:
            _guard_prior(fid, prior, status, nodes, already)
            if fid in already:
                continue
        rec = {"finding_id": fid, "status": status, "evidence": evidence,
               "superseded_by": superseded_by,
               "date": date or _date.today().isoformat()}
        if commit:
            rec["commit"] = commit
        if verified_by.get(fid):
            rec["verified_by"] = verified_by[fid]
        to_add.append(rec)
    return to_add, already


def _guard_prior(fid, prior, status, nodes, already) -> None:
    """Decide what an existing record means for this write. Appends to `already` or raises.

    ⚠️ **Same status is NOT automatically idempotent.** A prior record carrying
    `{"finding_id": X, "status": "fixed"}` and nothing else does not meet the closure bar,
    so the finding still reads `open` — and skipping the write "because it is already fixed"
    reports success while the finding stays blocked. That is this branch's founding defect
    regenerated inside the writer built to remove it.
    """
    prior_status = prior.get("status")
    if prior_status == status:
        has_verify = bool((nodes[fid].get("meta") or {}).get("verify"))
        if status in CLOSING_STATUSES and not _bg._closure_record_meets_bar(
                prior, has_verify):
            raise ValueError(
                f"{fid} already carries status={status!r}, but that record does NOT meet "
                f"the closure bar, so the finding still reads `open` and this call would "
                f"report success while changing nothing. Amend the existing record — it "
                f"needs an explicit closing status, >=40 chars of rationale, a commit or "
                f"date anchor"
                + (", and a passing verified_by for its declared Verify: command."
                   if has_verify else "."))
        already.append(fid)
        return
    # A lifecycle transition through the append-only ledger, which the reader resolves
    # last-wins: closing → reopened, and reopened → closing, are both legitimate.
    if status == "reopened" and prior_status in CLOSING_STATUSES:
        return
    if prior_status == "reopened" and status in CLOSING_STATUSES:
        return
    raise ValueError(
        f"{fid} already carries status={prior_status!r}; refusing to append a conflicting "
        f"{status!r}. The reader is last-wins and does not say so, which is how a closure "
        f"silently does nothing. Amend the existing record deliberately instead.")


def _read_ledger() -> dict:
    data = json.loads(LEDGER.read_text(encoding="utf-8"))
    data.setdefault("supersessions", [])
    return data


def _write(to_add: list[dict]) -> None:
    # Re-read immediately before writing, so a concurrent append is not clobbered.
    data = _read_ledger()
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
