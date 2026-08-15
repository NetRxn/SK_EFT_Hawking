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
import contextlib
import fcntl
import json
import os
import re
import subprocess
import sys
import tempfile
import time as _time
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


# ── Out-of-repo artifact anchors (D11 Stage-13 finding 2026-08-01-0009:D11:N3) ──
# `Lit-Search/` is a workspace SIBLING of this repository, and Pipeline Invariant #11
# makes a primary-source cache mandatory at every Stage 13 — so for any finding whose
# artifact lives there, a commit reference is STRUCTURALLY IMPOSSIBLE: no commit in this
# repo can contain the change. The schema offered only `commit` or `date`, which forced
# either a fabricated SHA or no closure at all, and a record shipped citing the very
# commit the finding says did NOT fix it. A provenance record whose commit cannot
# contain the change is worse than no record, because it reads as an audit trail.
#
# `--artifact` is the anchor for that case: it hashes the file as it stands at closure
# time and records `artifact_sha256` + `artifact_path`, which a later reviewer can
# re-derive with one command. It counts as an anchor in its own right.
_PATH_IN_TARGET = re.compile(r"`([^`\s]+/[^`\s]+\.[A-Za-z0-9]+)`")


def _resolve_case_insensitively(base: Path, rel: str) -> Path | None:
    """Resolve `rel` under `base`, falling back to a case-insensitive segment match.

    Filesystem-independent by construction: it never relies on APFS folding the case
    for it, so a path typed `Phase-6C` against a `Phase-6c` directory resolves the same
    way on Linux CI as it does here, and the CALLER gets the on-disk spelling back.
    """
    cur = base
    for seg in Path(rel).parts:
        if not cur.is_dir():
            return None
        # ⚠️ Read the DIRECTORY LISTING rather than testing `(cur / seg).exists()`.
        # On a case-insensitive filesystem `exists()` is true for the TYPED spelling, so
        # a probe-based walk happily returns `Phase-6C` and the recorded path is one that
        # exists nowhere else. The listing carries the real name.
        names = {c.name: c for c in cur.iterdir()}
        match = names.get(seg) or next(
            (c for n, c in names.items() if n.lower() == seg.lower()), None)
        if match is None:
            return None
        cur = match
    return cur if cur.is_file() else None


def _artifact_anchor(rel_paths: list[str]) -> tuple[dict | None, str]:
    """`({artifact_path, artifact_sha256, artifact_anchors}, "")` or `(None, reason)`."""
    import hashlib

    from src.core.workspace import find_workspace
    ws = find_workspace()
    recs = []
    for rel in rel_paths:
        f = _resolve_case_insensitively(ws, rel)
        if f is None:
            return None, (f"--artifact {rel!r} does not resolve under the workspace "
                          f"({ws}). An anchor that names nothing is the defect this "
                          f"option exists to replace.")
        # Record the RESOLVED spelling, not the typed one: review documents quote
        # `Phase-6C` where the directory is `Phase-6c`, and a record carrying a path
        # that only resolves on a case-insensitive filesystem is not provenance
        # anywhere else (D11 Stage-13 round-4 finding 1.2).
        recs.append({"path": f.relative_to(ws).as_posix(),
                     "sha256": hashlib.sha256(f.read_bytes()).hexdigest()})
    if not recs:
        return None, "--artifact was given no path"
    return ({"artifact_path": recs[0]["path"],
             "artifact_sha256": recs[0]["sha256"],
             "artifact_anchors": recs}, "")


def _targets_are_all_out_of_repo(node) -> list[str]:
    """Workspace-relative paths a finding names that this git repo does not track.

    Returns `[]` unless EVERY path-shaped token in the finding's Location is untracked
    here — a finding with an in-repo half still has something a commit can legitimately
    anchor, and must not be blocked.
    """
    target = (node.get("meta") or {}).get("target") or ""
    cands = _PATH_IN_TARGET.findall(target)
    if not cands:
        return []
    outside = []
    for c in cands:
        r = subprocess.run(["git", "ls-files", "--error-unmatch", c],
                           cwd=str(_bg.PROJECT_ROOT),
                           capture_output=True, text=True)
        if r.returncode == 0:
            return []                      # at least one tracked path: commit is fine
        outside.append(c)
    return outside


def close(doc: str, sections: list[str], status: str, evidence: str,  # noqa: PLR0913
          commit: str | None = None, date: str | None = None,
          verify: str | None = None, superseded_by: str | None = None,
          dry_run: bool = False,
          artifact: list[str] | None = None,
          amend: str | None = None) -> tuple[bool, str]:
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

    art_rec = None
    if artifact:
        art_rec, why = _artifact_anchor(artifact)
        if art_rec is None:
            return False, why

    if not (commit or date or art_rec):
        return False, "no anchor: pass --commit, --date or --artifact"

    # ⚠️ REFUSE a commit anchor this repository cannot possibly carry. Narrow on
    # purpose: it fires only when EVERY path the finding's Location names is untracked
    # here, so an in-repo finding is never blocked by it.
    if commit and not art_rec:
        for fid in minted:
            outside = _targets_are_all_out_of_repo(nodes[fid])
            if outside:
                return False, (
                    f"{fid} names only artifacts this repository does not track "
                    f"({', '.join(outside)}), so NO commit here can contain the change "
                    f"and --commit {commit} would read as an audit trail while proving "
                    f"nothing. Anchor it with `--artifact {outside[0]}`, which records "
                    f"the file's sha256 at closure time; --date may accompany it.")

    ok, verified_by, msg = _run_verifications(minted, nodes, verify, status)
    if not ok:
        return False, msg

    try:
        to_add, already = _plan(minted, nodes, status, evidence, commit, date,
                               verified_by, superseded_by, art_rec, amend=amend)
    except ValueError as exc:           # a conflicting or sub-bar pre-existing record
        return False, str(exc)

    if not dry_run and to_add:
        try:
            _write(to_add)
        except (RuntimeError, TimeoutError) as exc:
            # A lost or blocked write is a REFUSAL, not a crash. Every caller of this
            # function — the CLI, the batch scripts, the tests — reads the `(ok, msg)`
            # pair; a traceback escaping here would be reported by a batch runner as
            # "one entry errored" and skipped past, which is how a lost write became
            # invisible in the first place.
            return False, str(exc)

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


def _plan(minted, nodes, status, evidence, commit, date, verified_by, superseded_by,
          art_rec=None, amend=None):
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
            _guard_prior(fid, prior, status, nodes, already, amend=amend)
            if fid in already:
                continue
        rec = {"finding_id": fid, "status": status, "evidence": evidence,
               "superseded_by": superseded_by,
               "date": date or _date.today().isoformat()}
        if prior is not None and (
                prior.get("status") == "open"
                or (prior.get("status") in CLOSING_STATUSES
                    and not _bg._closure_record_meets_bar(
                        prior, bool((nodes[fid].get("meta") or {}).get("verify"))))):
            # Keep the history legible: this closure walks over an inert `open` record
            # rather than a genuine prior decision. Without the marker the ledger reads as
            # if nothing preceded it, and the next reader cannot tell the two apart.
            rec["supersedes_inert_open"] = True
        if commit:
            rec["commit"] = commit
        if art_rec:
            rec.update(art_rec)
        if amend:
            # A DELIBERATE supersession of a record that already met the bar. The reason
            # travels with it, because the ledger is append-only and last-wins: without
            # it, a later reader sees two valid-looking closures and no account of why the
            # second exists.
            rec["amends_prior"] = {"reason": amend,
                                   "superseded_record": {k: prior.get(k) for k in
                                                         ("status", "commit", "date")}}
        if verified_by.get(fid):
            rec["verified_by"] = verified_by[fid]
        to_add.append(rec)
    return to_add, already


def _guard_prior(fid, prior, status, nodes, already, amend=None) -> None:
    """Decide what an existing record means for this write. Appends to `already` or raises.

    ⚠️ **Same status is NOT automatically idempotent.** A prior record carrying
    `{"finding_id": X, "status": "fixed"}` and nothing else does not meet the closure bar,
    so the finding still reads `open` — and skipping the write "because it is already fixed"
    reports success while the finding stays blocked. That is this branch's founding defect
    regenerated inside the writer built to remove it.
    """
    prior_status = prior.get("status")
    # ⚠️ `--amend` is the operation THREE refusal messages in this file have been advising
    # since ADR-012 ("amend the existing record deliberately instead") while it did not
    # exist. Its absence is not cosmetic: a record that MEETS the bar but is WRONG — the
    # measured case is `…1951…:D11:1.1`, anchored to a commit that cannot contain the fix
    # because the finding's only Location is untracked in this repo — was uncorrectable
    # except by hand-editing the ledger, which is what this writer exists to eliminate.
    #
    # Deliberately loud rather than permissive: it requires an explicit reason, and the
    # new record carries `amends_prior` naming what it supersedes, so the append-only
    # history stays readable instead of showing two valid-looking closures.
    if amend:
        return
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
    # An `open` prior is INERT. `build_graph.py` births every finding `open`
    # (BIRTH-STATUS INVARIANT), so a record restating it asserts nothing, closes nothing,
    # and changes no reader's answer — it is bookkeeping. Refusing on it made the *presence
    # of a record that does nothing* permanently unclosable through the sole writer, and the
    # refusal below advises "amend the existing record", an operation this tool does not
    # offer; the only route left was hand-editing the ledger, which is what this writer
    # exists to eliminate. Measured 2026-08-15: 10 findings carried an inert `open` record,
    # 5 of them open BLOCKING findings on the 21 submission bundles, at least two already
    # independently verified as remediated and held open by nothing but this guard.
    #
    # ⚠️ Deliberately narrow. The `fixed`↔`accepted` refusal and the below-the-bar-`fixed`
    # refusal above are each load-bearing and were each written to close a real defect —
    # widening this guard generally would reopen both.
    if prior_status == "open":
        return
    # A prior closure that does NOT MEET THE BAR is inert for the same reason: the reader
    # leaves the finding `open`, so the record changes no reader's answer either. Refusing
    # on it strands the finding — and the refusal's advice, "amend the existing record",
    # still names an operation this tool does not offer.
    #
    # Measured 2026-08-15, and the stranding mechanism is worth stating because it is not
    # obvious: `review:2026-08-14-l1-stage13:L1:3.2` carried a substantive `accepted`
    # record that could never meet the bar, because the finding DECLARED a Verify
    # asserting one branch of a two-branch Expected while the decision took the other. The
    # declared command could not pass under the decision actually made, so no record could
    # carry a passing `verified_by`, so the bar was unreachable and the finding read `open`
    # permanently. The Verify was the defect; this guard turned it into a life sentence.
    #
    # ⚠️ STILL NARROW. A prior that DOES meet the bar continues to refuse a conflicting
    # status — that is the `fixed`↔`accepted` guard, and it is load-bearing. Only a record
    # that closes nothing is walked over, and only by one that closes something: `_plan`
    # applies the bar to the new record independently.
    if prior_status in CLOSING_STATUSES and not _bg._closure_record_meets_bar(
            prior, bool((nodes[fid].get("meta") or {}).get("verify"))):
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


def _lock_path() -> Path:
    """Sidecar advisory lock beside whatever `LEDGER` currently points at.

    ⚠️ Derived at CALL time, not bound at import. Every test in
    `tests/test_close_finding.py` repoints `LEDGER` into `tmp_path`; a module-level
    constant would have kept locking the real `docs/` file, so the suite would serialise
    against live closures and leave a lockfile in the tree.

    NOT the ledger itself: `_atomic_write` replaces the ledger's inode, so a lock held on
    that fd would guard a file no longer at the path.
    """
    return LEDGER.parent / (LEDGER.name + ".lock")


@contextlib.contextmanager
def _ledger_lock(timeout: float = 60.0):
    """Exclusive advisory lock over the read-modify-write window.

    ⚠️ **A re-read before writing is not enough, and this is measured.** `_write` already
    re-read the ledger immediately before serialising it, on the reasoning that the window
    was too small to matter. On 2026-08-15, during a five-worker parallel run, a closure
    for `…:2026-07-31-1823…:D12:8.6` printed `✓ wrote 1 record(s)`, exited 0, and the
    record was **not in the file** afterwards while an earlier one was. `json.dump` of a
    645 KB structure is not instantaneous; "too small to matter" was a guess, and the
    guess was wrong.

    Scoped to the file operations ONLY. `_run_verifications` shells out to a `--verify`
    command that can run for minutes and must never hold this lock.
    """
    lock = _lock_path()
    lock.touch(exist_ok=True)
    with open(lock, "r+", encoding="utf-8") as fh:
        deadline = _time.monotonic() + timeout
        while True:
            try:
                fcntl.flock(fh.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                break
            except OSError:
                if _time.monotonic() >= deadline:
                    raise TimeoutError(
                        f"another process has held {lock.name} for {timeout:.0f}s. The "
                        f"ledger is read-modify-write, so proceeding without the lock "
                        f"risks silently discarding that process's records.")
                _time.sleep(0.05)
        try:
            yield
        finally:
            fcntl.flock(fh.fileno(), fcntl.LOCK_UN)


def _write(to_add: list[dict]) -> None:
    with _ledger_lock():
        # Re-read UNDER THE LOCK, so a concurrent append is not clobbered.
        data = _read_ledger()
        data["supersessions"].extend(to_add)
        _atomic_write(data)
        # ⚠️ READ BACK. The success line is printed from the in-memory plan, so without
        # this it asserts what the tool INTENDED, not what the file holds — the one thing
        # a closure writer must never get wrong. The 8.6 loss above was caught by a
        # coincidence of workflow (`git commit` reporting "no changes"), not by any guard.
        landed = {e.get("finding_id") for e in _read_ledger()["supersessions"]}
        lost = sorted({r["finding_id"] for r in to_add} - landed)
        if lost:
            raise RuntimeError(
                f"WRITE LOST: {len(lost)} record(s) reported written are absent from the "
                f"ledger on read-back: {lost}. Another process replaced the file inside "
                f"the locked window, which should be impossible — do not re-run blindly, "
                f"inspect {LEDGER.name} first.")


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
    ap.add_argument("--date", help="ISO date (this, --commit or --artifact is required)")
    ap.add_argument("--artifact", action="append", metavar="WORKSPACE_REL_PATH",
                    help="anchor the closure to a file's sha256 instead of a commit. "
                         "REQUIRED when the finding's artifact lives outside this git "
                         "repo (e.g. Lit-Search/), where no commit can contain the "
                         "change. Repeatable.")
    ap.add_argument("--verify", help="command proving the fix; RUN before writing")
    ap.add_argument("--superseded-by", dest="superseded_by",
                    help="the re-review that confirmed it")
    ap.add_argument("--amend", metavar="REASON",
                    help="deliberately supersede a record that ALREADY meets the bar but "
                         "is wrong (e.g. anchored to a commit that cannot contain the "
                         "fix). Requires a reason, which is recorded in `amends_prior` "
                         "beside what it supersedes. Not a way to re-close a finding: an "
                         "ordinary duplicate closure is still reported as already recorded.")
    ap.add_argument("--dry-run", action="store_true")
    a = ap.parse_args(argv)
    ok, msg = close(a.doc, a.section, a.status, a.evidence, a.commit, a.date,
                    a.verify, a.superseded_by, a.dry_run, a.artifact, a.amend)
    print(("✓ " if ok else "✗ REFUSED — ") + msg)
    return 0 if ok else 1


if __name__ == "__main__":
    raise SystemExit(main())
