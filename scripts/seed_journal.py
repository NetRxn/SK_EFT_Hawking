"""Crash-safe production-seeded mutation — the journal that survives a killed run.

WHY THIS EXISTS
---------------
`CHECK_AUTHORING_GUIDE` §2.4 requires a check to be proved against a defect written
into the **real artifact the check reads**. The house pattern for that was::

    original = path.read_text()
    try:
        path.write_text(seeded)
        ...assert red...
    finally:
        path.write_text(original)

`finally` runs on a normal exit, on an exception, and on a `KeyboardInterrupt`. It does
**not** run on `SIGKILL`, on a `SIGTERM` whose handler never completes, on a harness
timeout that kills the process group, or on a dead runner. When it does not run, the
seed stays in the working tree.

That is not hypothetical. Measured 2026-08-15: a killed run of
`tests/test_d5_bundles_readiness.py::test_A_REAL_NEW_BLOCKING_FINDING_TURNS_THE_LEG_RED`
left six seeded lines in
`papers/AutomatedReviews/2026-08-12-0200-citation-integrity/D10.md`. For the review
corpus the seed **is a finding**: it minted a node, emitted a `FLAGS` edge, counted
against the D10 ratchet and moved `readiness_submission_gate`. Nothing marked it
synthetic, and it was three days from being frozen into a ratchet ceiling as an
accepted blocker. Filed as
`papers/AutomatedReviews/2026-08-15-seeded-mutation-survives-a-killed-run/infra.md`.

WHAT THIS MODULE CHANGES
------------------------
The restore stops depending on the seeding process staying alive. **Before** the
production file is touched, a durable record — the original bytes, their digest, the
original mtime, the owning pid — is `fsync`'ed to `.seed-journal/`. The mutation
happens second. Restoration is then possible from a *different, later* process, which
is precisely the capability `finally` lacks.

Three consumers close the loop, and they are deliberately independent:

1. **The context managers here** restore on any normal or exceptional exit and drop
   the journal entry. This is the fast path and covers everything except death.
2. **A session-scoped autouse fixture** (`tests/conftest.py`) repairs orphaned entries
   at the start of every pytest run and says so loudly.
3. **`validate.py --check seed_residue_absent`** FAILS while residue is present. It
   asserts the *outcome* — no seeded content in the corpus — not that (1) or (2) ran.

⚠️ **PID LIVENESS IS LOAD-BEARING.** Concurrent agents share this repo and its worktrees,
so a journal entry whose owner is still running is an *in-flight seed*, not residue.
Repair and the residue check both skip live owners. Without that, one session's repair
would restore a file out from under another session's running test — turning a crash-
safety mechanism into a corruption mechanism.

⚠️ **THE MARKER IS MANDATORY IN THE REVIEW CORPUS.** A seed under
`papers/AutomatedReviews/` must contain `SEED_MARKER`, and `seeded_mutation` refuses the
seed otherwise. That is what makes residue *detectable by reading the corpus*, which is
what lets the guard check assert an outcome instead of trusting this module.

⚠️ **THE MARKER DOES NOT MAKE RESIDUE HARMLESS — the extractor still mints it.** An earlier
version of this docstring claimed the graph extractor refuses to mint a marker-bearing
finding, so that un-repaired residue could not become a blocking finding. **That is false,
and it was false in the reassuring direction.** `scripts/build_graph.py` documents at
length that exactly this containment was considered and REJECTED: skipping marker-bearing
sections would make the finding-minting path impossible to production-seed, and two
entries depend on minting a seeded section (`bundle_stage13_claim_consistent`'s
ratchet-breach leg and `review_severity_declared`'s dangling-`Blocked-by` leg), so both
would fall back to fixtures and raise `FIXTURE_ONLY_CEILING` — a ceiling the project only
lets shrink. Residue in the corpus **does** mint a node, emit a `FLAGS` edge and count
against a bundle ratchet. The marker buys DETECTABILITY, not immunity, and the containment
is the three independent consumers below — not a blind spot in the extractor.

(Corrected 2026-08-15. The wrong claim was found while re-measuring a filed finding before
acting on it: the docstring said the race could not mint a fabricated CRITICAL, `build_graph`
said it could, and the code agreed with `build_graph`. Judging substrate strength from a
docstring rather than the code nearly retracted a correct finding.)

USAGE
-----
Mutating an existing production artifact::

    from seed_journal import seeded_mutation, SEED_MARKER

    with seeded_mutation(doc, lambda t: t + f"\\n<!-- {SEED_MARKER} -->\\n...",
                         reason="prove the ratchet fires on a new blocker"):
        assert check().passed is False

Creating a production artifact that did not exist::

    with seeded_artifact(review_dir / "infra.md", body, reason="...") as p:
        ...

Repairing by hand after a kill::

    uv run python scripts/seed_journal.py status
    uv run python scripts/seed_journal.py repair
"""
from __future__ import annotations

import hashlib
import json
import os
import shutil
import sys
import time
import uuid
from contextlib import contextmanager
from datetime import datetime, timezone
from pathlib import Path
from typing import Callable, Iterator

PROJECT_ROOT = Path(__file__).resolve().parent.parent

#: Untracked, gitignored. Deliberately at the repo root and NOT under `/tmp`: a journal
#: in a system temp directory is reaped by the OS, and the whole point is to outlive the
#: process. Deliberately not inside `.git/` either — a worktree has its own gitdir, and
#: residue is a property of the working tree.
JOURNAL_DIR = PROJECT_ROOT / ".seed-journal"

#: The sentinel a seed writes into the review corpus. Any occurrence of this string in a
#: tracked review document means a test seed outlived its test.
#:
#: ⚠️ Written as a concatenation so that THIS FILE, and the check that greps for it, do
#: not themselves count as corpus residue when the string is quoted in prose elsewhere.
SEED_MARKER = "SKEFT-SEEDED" + "-BY-TEST-SUITE"

#: Corpus whose documents are read as DATA by the graph builder, where a surviving seed
#: is not merely a dirty file but a fabricated finding.
REVIEW_CORPUS = PROJECT_ROOT / "papers" / "AutomatedReviews"


# ────────────────────────────────────────────────────────────────────────────────
# journal primitives
# ────────────────────────────────────────────────────────────────────────────────

def _fsync_path(p: Path) -> None:
    """Force `p` to stable storage. A journal that is only in the page cache when the
    machine dies is not a journal."""
    fd = os.open(str(p), os.O_RDONLY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def _fsync_dir(p: Path) -> None:
    fd = os.open(str(p), os.O_RDONLY)
    try:
        os.fsync(fd)
    finally:
        os.close(fd)


def _pid_alive(pid: int) -> bool:
    """True if `pid` is a live process. Signal 0 performs the permission/existence
    check without delivering anything."""
    if pid <= 0:
        return False
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        return False
    except PermissionError:
        return True   # exists, owned by someone else
    return True


def _entry_path(entry_id: str) -> Path:
    return JOURNAL_DIR / f"{entry_id}.json"


def _lock_path(path: Path) -> Path:
    """The lockfile serialising seeders of ONE production path.

    Keyed on the resolved path's digest, not on its name: two worktrees seeding
    same-named files are different transactions and must not contend, while two
    processes seeding the same file must.
    """
    digest = hashlib.sha256(str(Path(path).resolve()).encode()).hexdigest()[:16]
    return JOURNAL_DIR / f"{digest}.lock"


@contextmanager
def _path_lock(path: Path, *, timeout: float = 120.0) -> Iterator[None]:
    """Hold an exclusive lock for the WHOLE read -> seed -> assert -> restore window.

    ⚠️ THE WINDOW MUST INCLUDE THE ASSERTION, and that is the whole point. The journal
    made a seed survive a KILLED run; it does nothing about two LIVE seeders of the same
    file. Both read the original, both write their seed, both restore — and whichever
    restores first writes back a copy that already contains the other's seed. The journal
    reports clean, because each transaction completed correctly on its own terms. The
    invariant broken is PAIRWISE, so no single transaction can observe it.

    Measured 2026-08-15: the D10 stanza reappeared in the corpus while two suites ran
    concurrently and the journal reported 0 in flight. Residue there is not inert — the
    graph extractor mints a marker-bearing section as an open finding at its declared
    severity (see the module docstring), so a race can manufacture a blocking CRITICAL
    that is indistinguishable downstream from a real one.

    Narrowing the lock to just the write would not fix it: the corruption is that the
    SECOND reader captures the first's seed AS the original, and that read happens before
    either write.

    Fails with a timeout naming the holder rather than blocking forever, following
    `scripts/close_finding.py`'s ledger lock. A same-path re-seed from inside the
    assertion window would deadlock and is a genuine bug in the calling test — the
    timeout surfaces it as one instead of hanging the suite.
    """
    import fcntl

    JOURNAL_DIR.mkdir(parents=True, exist_ok=True)
    lock = _lock_path(path)
    with open(lock, "a+") as fh:
        deadline = time.monotonic() + timeout
        while True:
            try:
                fcntl.flock(fh.fileno(), fcntl.LOCK_EX | fcntl.LOCK_NB)
                break
            except OSError:
                if time.monotonic() >= deadline:
                    try:
                        fh.seek(0)
                        holder = fh.read(200).strip() or "unknown"
                    except OSError:
                        holder = "unknown"
                    raise TimeoutError(
                        f"another process has been seeding {path} for {timeout:.0f}s "
                        f"(holder: {holder}). Proceeding without the lock would let the "
                        f"two read-seed-restore windows interleave, and the loser's seed "
                        f"survives as corpus residue that mints a finding.")
                time.sleep(0.05)
        try:
            fh.seek(0)
            fh.truncate()
            fh.write(f"pid={os.getpid()} test={_current_test()}")
            fh.flush()
            yield
        finally:
            fcntl.flock(fh.fileno(), fcntl.LOCK_UN)


def _current_test() -> str:
    """Best-effort nodeid of the running test, for the human reading `status`."""
    return os.environ.get("PYTEST_CURRENT_TEST", "").split(" (")[0] or "<not under pytest>"


def _write_entry(entry: dict) -> Path:
    """Durably record `entry` BEFORE the production file is touched.

    tmp-write → fsync → rename → fsync(dir) is the standard atomic-publish sequence.
    A half-written entry must never be visible to a repairing process, because repair
    acts on what it reads.
    """
    JOURNAL_DIR.mkdir(parents=True, exist_ok=True)
    final = _entry_path(entry["id"])
    tmp = final.with_suffix(".json.tmp")
    tmp.write_text(json.dumps(entry, indent=2, sort_keys=True) + "\n", encoding="utf-8")
    _fsync_path(tmp)
    tmp.replace(final)
    _fsync_dir(JOURNAL_DIR)
    return final


def _drop_entry(entry: dict) -> None:
    """Remove a satisfied entry and its backup. Called only after the restore has been
    verified byte-identical, so an entry that survives always means unrepaired residue."""
    backup = entry.get("backup")
    if backup:
        Path(backup).unlink(missing_ok=True)
    _entry_path(entry["id"]).unlink(missing_ok=True)


def outstanding(*, include_live: bool = False) -> list[dict]:
    """Every journal entry not yet satisfied, oldest first.

    `include_live=False` (the default) hides entries whose owning process is still
    running: those are seeds currently in flight in a concurrent session, not residue.
    """
    if not JOURNAL_DIR.is_dir():
        return []
    entries: list[dict] = []
    for p in sorted(JOURNAL_DIR.glob("*.json")):
        try:
            e = json.loads(p.read_text(encoding="utf-8"))
        except (OSError, json.JSONDecodeError):
            # A corrupt entry is itself unrepaired state — surface it rather than skip.
            entries.append({"id": p.stem, "kind": "corrupt", "path": str(p),
                            "pid": 0, "reason": "unreadable journal entry",
                            "started": "", "test": "", "backup": ""})
            continue
        e["live"] = _pid_alive(int(e.get("pid", 0)))
        if e["live"] and not include_live:
            continue
        entries.append(e)
    return sorted(entries, key=lambda e: e.get("started", ""))


# ────────────────────────────────────────────────────────────────────────────────
# seeding
# ────────────────────────────────────────────────────────────────────────────────

def _require_marker(path: Path, seeded: bytes) -> None:
    """A seed into the review corpus must be self-identifying.

    The corpus is consumed as DATA, so an unmarked seed is indistinguishable from a real
    finding to every consumer — the exact property that made the 2026-08-12 residue
    dangerous. Refusing the seed at write time is the only place this can be enforced
    cheaply; afterwards the seed is already in the tree.
    """
    try:
        path.relative_to(REVIEW_CORPUS)
    except ValueError:
        return
    if SEED_MARKER.encode() not in seeded:
        raise ValueError(
            f"a seed into the review corpus must contain {SEED_MARKER!r} so that "
            f"residue is detectable by reading the corpus (and so the extractor "
            f"refuses to mint it as a finding): {path}")


@contextmanager
def journalled(
    path: Path,
    *,
    reason: str,
    preserve_mtime: bool = True,
    allow_absent: bool = False,
) -> Iterator[bytes]:
    """Durably record `path`'s current bytes, then hand control back and restore on exit.

    The general primitive: it writes NOTHING itself, so the caller is free to mutate the
    file however it likes — in stages, via a subprocess, or through a browser clicking a
    button that persists to a tracked registry. `seeded_mutation` is this plus a
    one-shot write.

    Use it when the seed cannot be expressed as a single up-front content substitution:

    * `tests/test_d5_freshness.py` must stamp `docs/counts.json` with a future mtime,
      assert the isolation holds, and only THEN write the wrong count — three phases,
      where a content-only API would have to record the mtime after the stamp.
    * `tests/e2e/*` never writes at all; a Playwright click reaches `/verify`, which
      persists a `human_verified_date` into tracked `src/core/provenance.py`.

    ⚠️ REFUSES THE REVIEW CORPUS, deliberately. A corpus seed must carry `SEED_MARKER`,
    and that can only be enforced where the content is known — which is `seeded_mutation`
    and `seeded_artifact`, not here. Without the refusal this function would be the hole
    in the invariant that `seed_residue_absent` depends on.
    """
    path = Path(path)
    try:
        path.relative_to(REVIEW_CORPUS)
    except ValueError:
        pass
    else:
        raise ValueError(
            f"journalled() cannot take a review-corpus path ({path}): a seed there must "
            f"carry {SEED_MARKER!r} so residue is readable from the corpus, and only "
            f"seeded_mutation()/seeded_artifact() can enforce that. Use one of those.")
    if not path.is_file():
        if not allow_absent:
            raise FileNotFoundError(
                f"journalled() targets an existing file; {path} is not one. Pass "
                f"allow_absent=True if the caller may CREATE it (a runtime artifact such "
                f"as `docs/verification_log.jsonl`, absent in a clean checkout), and the "
                f"restore then means DELETE.")
        # Absent now → the caller may create it → the restore is a removal. Recorded as a
        # `creation` entry, which is the same shape `seeded_artifact` writes, so `_restore`
        # needs no special case and repair-after-a-kill is one code path.
        created_dirs: list[str] = []
        probe = path.parent
        while not probe.exists():
            created_dirs.append(str(probe))
            probe = probe.parent
        entry = {
            "id": uuid.uuid4().hex, "kind": "creation", "path": str(path), "backup": "",
            "sha256": "", "mtime_ns": 0, "atime_ns": 0, "preserve_mtime": False,
            "created_dirs": created_dirs, "reason": reason, "test": _current_test(),
            "pid": os.getpid(), "started": datetime.now(timezone.utc).isoformat(),
        }
        _write_entry(entry)
        try:
            yield b""
        finally:
            _restore(entry)
        return

    entry = _open_entry(path, reason=reason, preserve_mtime=preserve_mtime)
    try:
        yield bytes(Path(entry["backup"]).read_bytes())
    finally:
        _restore(entry)


def _open_entry(path: Path, *, reason: str, preserve_mtime: bool) -> dict:
    """Back up `path` and publish its journal entry. Returns the entry.

    Shared by `journalled` and `seeded_mutation` so there is exactly one ordering of
    backup → fsync → entry → fsync, and the production file is never touched before both
    are on stable storage.
    """
    original = path.read_bytes()
    st = path.stat()
    entry_id = uuid.uuid4().hex
    JOURNAL_DIR.mkdir(parents=True, exist_ok=True)
    backup = JOURNAL_DIR / f"{entry_id}.bak"
    backup.write_bytes(original)
    _fsync_path(backup)
    entry = {
        "id": entry_id,
        "kind": "mutation",
        "path": str(path),
        "backup": str(backup),
        "sha256": hashlib.sha256(original).hexdigest(),
        "mtime_ns": st.st_mtime_ns,
        "atime_ns": st.st_atime_ns,
        "preserve_mtime": preserve_mtime,
        "created_dirs": [],
        "reason": reason,
        "test": _current_test(),
        "pid": os.getpid(),
        "started": datetime.now(timezone.utc).isoformat(),
    }
    _write_entry(entry)
    return entry


@contextmanager
def seeded_mutation(
    path: Path,
    mutate: "str | bytes | Callable[[str], str]",
    *,
    reason: str,
    preserve_mtime: bool = True,
) -> Iterator[bytes]:
    """Seed a defect into an EXISTING production artifact, crash-safely.

    Yields the original bytes. `mutate` is either the replacement content (str/bytes) or
    a callable applied to the decoded original.

    On exit the original bytes — and, by default, the original mtime — are restored and
    asserted byte-identical. If the process dies before that, `.seed-journal/` holds
    everything a later `repair()` needs.

    ⚠️ `preserve_mtime=True` is the default because several checks in this repo compare
    mtimes (`counts_fresh`, `bundle_manuscript_length`). A byte-perfect restore with a
    fresh mtime silently took a bundle UNMEASURED once already; see the note in
    `tests/test_unscannable_input_guard.py`.
    """
    path = Path(path)
    if not path.is_file():
        raise FileNotFoundError(
            f"seeded_mutation targets an existing production artifact; {path} is not a "
            f"file. Use seeded_artifact() to create one.")

    # ⚠️ The lock opens BEFORE the read. The race this closes is that a second seeder
    # captures the first's seed AS its original, so locking only the write leaves the
    # defect intact.
    with _path_lock(path):
        original = path.read_bytes()
        entry = _open_entry(path, reason=reason, preserve_mtime=preserve_mtime)

        try:
            if callable(mutate):
                seeded = mutate(original.decode("utf-8")).encode("utf-8")
            elif isinstance(mutate, bytes):
                seeded = mutate
            else:
                seeded = mutate.encode("utf-8")
            _require_marker(path, seeded)
            if seeded == original:
                raise ValueError(
                    f"the seed did not change {path} — a mutation that fails to apply is a "
                    f"test that proves nothing (guide §2.4)")
            path.write_bytes(seeded)
            yield original
        finally:
            _restore(entry)


@contextmanager
def seeded_artifact(
    path: Path,
    content: "str | bytes",
    *,
    reason: str,
) -> Iterator[Path]:
    """Seed a production artifact that does NOT exist yet, crash-safely.

    Yields the path. On exit the file is deleted, along with any parent directories this
    call created (never one that already existed). A killed run leaves a journal entry
    that `repair()` acts on identically.
    """
    path = Path(path)
    # ⚠️ The lock spans the exists-check too. Without it two creators both see the path
    # absent, both create it, and the first to finish DELETES the file the second is
    # still asserting against — the same pairwise invariant seeded_mutation breaks, in
    # the other direction.
    with _path_lock(path):
        if path.exists():
            raise FileExistsError(
                f"{path} already exists — seeded_artifact creates; use seeded_mutation to "
                f"modify. (If this is residue from a killed run, run "
                f"`uv run python scripts/seed_journal.py repair`.)")

        created_dirs: list[str] = []
        probe = path.parent
        while not probe.exists():
            created_dirs.append(str(probe))
            probe = probe.parent

        payload = content.encode("utf-8") if isinstance(content, str) else content
        _require_marker(path, payload)

        entry_id = uuid.uuid4().hex
        entry = {
            "id": entry_id,
            "kind": "creation",
            "path": str(path),
            "backup": "",
            "sha256": "",
            "mtime_ns": 0,
            "atime_ns": 0,
            "preserve_mtime": False,
            # deepest-first on the way in; repair removes them in that same order
            "created_dirs": created_dirs,
            "reason": reason,
            "test": _current_test(),
            "pid": os.getpid(),
            "started": datetime.now(timezone.utc).isoformat(),
        }
        _write_entry(entry)

        try:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_bytes(payload)
            yield path
        finally:
            _restore(entry)


@contextmanager
def seeded_directory(path: Path, *, reason: str) -> Iterator[Path]:
    """Seed an empty production DIRECTORY, crash-safely.

    Narrow but real: `tests/test_dashboard_graph_cache.py` proves that a new dated review
    directory moves the dashboard's graph key, and the subject of that test is the
    directory itself — putting a file in it would conflate "a new directory" with "a new
    document" and stop testing the thing it names.

    An empty directory mints no finding, so the residue it leaves after a kill is benign
    compared with a document; it is journalled anyway, because "benign residue nobody
    repairs" is how a tree accumulates state nobody can explain.
    """
    path = Path(path)
    if path.exists():
        raise FileExistsError(f"{path} already exists — seeded_directory creates")

    created_dirs: list[str] = []
    probe = path.parent
    while not probe.exists():
        created_dirs.append(str(probe))
        probe = probe.parent

    entry = {
        "id": uuid.uuid4().hex, "kind": "creation", "path": str(path), "backup": "",
        "sha256": "", "mtime_ns": 0, "atime_ns": 0, "preserve_mtime": False,
        "created_dirs": created_dirs, "reason": reason, "test": _current_test(),
        "pid": os.getpid(), "started": datetime.now(timezone.utc).isoformat(),
    }
    _write_entry(entry)
    try:
        path.mkdir(parents=True)
        yield path
    finally:
        _restore(entry)


# ────────────────────────────────────────────────────────────────────────────────
# repair
# ────────────────────────────────────────────────────────────────────────────────

def _restore(entry: dict) -> str:
    """Put the tree back the way `entry` says it was, then drop the entry.

    Shared by the context managers' `finally` and by `repair()`, deliberately: a repair
    performed three days later must be byte-for-byte the same operation as the one the
    test would have performed, or the two can disagree.
    """
    path = Path(entry["path"])
    if entry["kind"] == "corrupt":
        Path(entry["path"]).unlink(missing_ok=True)
        return f"discarded corrupt journal entry {entry['id']}"

    if entry["kind"] == "mutation":
        backup = Path(entry["backup"])
        if not backup.is_file():
            raise RuntimeError(
                f"journal entry {entry['id']} has no backup at {backup}; "
                f"{path} must be restored by hand (`git checkout -- {path}`)")
        original = backup.read_bytes()
        if hashlib.sha256(original).hexdigest() != entry["sha256"]:
            raise RuntimeError(
                f"backup for {path} does not match its recorded digest — refusing to "
                f"restore from a corrupt backup")
        if path.read_bytes() != original:
            path.write_bytes(original)
        if entry.get("preserve_mtime"):
            os.utime(path, ns=(entry["atime_ns"], entry["mtime_ns"]))
        if path.read_bytes() != original:
            raise RuntimeError(f"failed to restore {path}")
        _drop_entry(entry)
        return f"restored {path}"

    # creation — of a file, or (seeded_directory) of the directory itself
    if path.is_dir():
        try:
            path.rmdir()
        except OSError:
            pass          # something else lives there now; leave it rather than destroy it
    else:
        path.unlink(missing_ok=True)
    for d in entry.get("created_dirs", []):
        try:
            Path(d).rmdir()
        except OSError:
            break   # not empty — something else lives there now; leave it
    _drop_entry(entry)
    return f"removed seeded artifact {path}"


def repair(*, dry_run: bool = False) -> list[str]:
    """Restore every orphaned seed. Returns one human line per action taken.

    Skips entries whose owning process is alive — those are in flight, not residue.
    """
    actions: list[str] = []
    for entry in outstanding():
        if dry_run:
            actions.append(f"WOULD restore {entry.get('path')} "
                           f"(seeded by {entry.get('test')}, pid {entry.get('pid')})")
            continue
        actions.append(_restore(entry))
    return actions


# ────────────────────────────────────────────────────────────────────────────────
# CLI
# ────────────────────────────────────────────────────────────────────────────────

def main(argv: "list[str] | None" = None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    cmd = argv[0] if argv else "status"
    if cmd not in {"status", "repair"}:
        print(f"usage: {Path(__file__).name} [status|repair]", file=sys.stderr)
        return 2

    entries = outstanding(include_live=True)
    orphans = [e for e in entries if not e.get("live")]

    if cmd == "status":
        if not entries:
            print("seed journal clean — no outstanding seeded mutations")
            return 0
        for e in entries:
            state = "IN FLIGHT" if e.get("live") else "ORPHANED"
            print(f"[{state}] {e.get('path')}\n"
                  f"          kind={e.get('kind')} pid={e.get('pid')} "
                  f"started={e.get('started')}\n"
                  f"          test={e.get('test')}\n"
                  f"          reason={e.get('reason')}")
        print(f"\n{len(orphans)} orphaned, {len(entries) - len(orphans)} in flight. "
              f"`repair` acts on the orphans only.")
        return 1 if orphans else 0

    if not orphans:
        print("nothing to repair")
        return 0
    for line in repair():
        print(line)
    return 0


if __name__ == "__main__":
    start = time.time()
    code = main()
    if code == 0 and time.time() - start > 5:
        print(f"({time.time() - start:.1f}s)")
    raise SystemExit(code)
