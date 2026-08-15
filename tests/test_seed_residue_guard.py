"""The crash-safe seeded-mutation mechanism, and the guard that backstops it.

WHAT FAILED
-----------
`CHECK_AUTHORING_GUIDE` §2.4 requires a check to be proved by writing the defect into the
REAL artifact it reads. The house pattern restored in a `finally`, which does not run
under `SIGKILL`, a harness timeout, or a dead runner. On 2026-08-12 a killed run of
`test_d5_bundles_readiness.py::test_A_REAL_NEW_BLOCKING_FINDING_TURNS_THE_LEG_RED` left
six seeded lines in `papers/AutomatedReviews/2026-08-12-0200-citation-integrity/D10.md`.
The corpus is read as DATA, so the seed became a live open CRITICAL on bundle D10 — a
node, a FLAGS edge, a ratchet consumer, a moved `readiness_submission_gate` — for three
days, and was nearly frozen into a ratchet ceiling as an accepted blocker.

WHAT THIS FILE COVERS
---------------------
1. `scripts/seed_journal.py` — the ONE mechanism every production-seeding test now uses.
   The journal is written and `fsync`ed BEFORE the production file is touched, so the
   restore can be completed by a different, later process.
2. `validate.py --check seed_residue_absent` — the independent guard, which asserts the
   OUTCOME (nothing seeded is in the corpus) rather than the MECHANISM (the fixture ran).

⚠️ THE TWO ARE DELIBERATELY NOT THE SAME TEST. A guard whose only evidence is that its own
fixture executed is the proxy failure §4.5 names: a fixture that executes and does nothing
satisfies it. Every assertion here about the check reads the corpus or the journal.

⚠️ THE KILL IS SIMULATED WITH A REAL `SIGKILL`, not by monkeypatching the restore away.
A test that patches `_restore` to a no-op proves that a patched function does nothing.
`test_a_SIGKILLED_seeder_leaves_repairable_residue` forks a real subprocess, kills it with
signal 9 while it holds a seed open, and repairs the tree from the journal afterwards —
which is the exact sequence that lost three days.
"""
from __future__ import annotations

import json
import os
import signal
import subprocess
import sys
import time
from pathlib import Path

import pytest

SK_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(SK_ROOT / "scripts"))
sys.path.insert(0, str(SK_ROOT))

import seed_journal as sj                                          # noqa: E402
import validation.checks.reviews as rv                             # noqa: E402
import validate_helpers as _H                                      # noqa: E402

REVIEWS = _H.PAPERS_DIR / "AutomatedReviews"

#: A review directory this file OWNS. Dated far enough out that it cannot collide with a
#: real wave's directory, and named for what it is so a human who finds it knows.
_PROBE_DIR = "2099-01-01-seed-residue-guard-probe"


def _probe_doc(name: str = "infra.md") -> Path:
    return REVIEWS / _PROBE_DIR / name


def _run() -> "rv.CheckResult":
    return rv.check_seed_residue_absent()


def _leg(res, name):
    return next(d for d in res.details if d.name == name)


# ══════════════════════════════════════════════════════════════════════════════════
# The check — PRODUCTION-SEEDED (guide §2.4), dogfooding the mechanism it backstops
# ══════════════════════════════════════════════════════════════════════════════════

class TestTheCheckFiresOnRealResidue:

    def test_the_live_corpus_is_clean(self):
        """The SILENT direction. If this is red, either a killed run left residue — run
        `uv run python scripts/seed_journal.py repair` — or a real review document has
        quoted the marker, which it must not."""
        res = _run()
        assert res.passed is True, [(d.name, d.message) for d in res.details if not d.passed]
        assert res.details, "a verdict with no details measured nothing"

    def test_PRODUCTION_SEEDED_a_marked_document_in_the_REAL_corpus_turns_it_red(self):
        """⚠️ THE NON-VACUITY BAR, and it is seeded through the very mechanism this check
        exists to backstop. That is deliberate: a residue guard built on a crash-safe
        seeder that could not itself be seeded crash-safely would be assuming its own
        premise. If `seeded_artifact` ever stops restoring, THIS test leaves residue and
        the next run of `test_the_live_corpus_is_clean` says so.

        A fixture tree cannot reach this leg — the check resolves `papers/AutomatedReviews`
        from the repo root, so the only way to observe it fail is to put a document in the
        real corpus.
        """
        doc = _probe_doc()
        assert _run().passed is True, "the corpus was already dirty before seeding"
        with sj.seeded_artifact(
                doc,
                f"# Seed-residue guard probe\n\n"
                f"### 1 — probe\n\n- **Severity:** minor\n- **Lane:** infra\n"
                f"- **Observed:** written by tests/test_seed_residue_guard.py.\n"
                f"### 9.9 — 🔴 CRITICAL — seeded probe\n\n- **Severity:** critical\n\n"
                f"Seeded by the test suite. <!-- {sj.SEED_MARKER} -->\n",
                reason="a marker-bearing document in the real corpus must turn "
                       "seed_residue_absent red"):
            res = _run()
            assert res.passed is False, (
                "a review document carrying the seed marker reported PASS — the check "
                "cannot fire in production, which is the state D10 was in on 2026-08-12")
            leg = _leg(res, "corpus")
            assert leg.passed is False
            assert _PROBE_DIR in (leg.message or ""), leg.message
            assert leg.measured is not False, (
                "the corpus leg reported UNVERIFIED rather than a violation — the "
                "population floor fired instead of the residue scan")
        # …and the corpus is clean again, with the probe directory gone.
        assert not doc.exists() and not doc.parent.exists()
        assert _run().passed is True

    def test_an_ORPHANED_JOURNAL_ENTRY_alone_turns_it_red(self, tmp_path):
        """The second leg, covering residue the marker cannot reach.

        A seed into `docs/counts.json` or `src/core/provenance.py` cannot carry a sentinel
        without changing what the seed means, so the corpus scan is blind to it. The
        journal is not. Seeded with a DEAD pid, which is what an orphan is.
        """
        victim = tmp_path / "not_really_production.txt"
        victim.write_text("original\n")
        entry = sj._open_entry(victim, reason="unit probe", preserve_mtime=True)
        entry["pid"] = _a_dead_pid()
        sj._write_entry(entry)
        try:
            res = _run()
            assert res.passed is False, (
                "an unrestored seed whose owner is gone reported PASS")
            leg = _leg(res, "journal")
            assert leg.passed is False and str(victim) in (leg.message or "")
        finally:
            sj._drop_entry(entry)
        assert _run().passed is True

    def test_a_LIVE_owner_is_not_residue(self, tmp_path):
        """⚠️ THE FALSE-RED THIS CHECK MUST NOT PRODUCE. Concurrent agents share this
        repo, so a seed held open by a RUNNING pytest is in flight, not residue. Without
        this exemption `validate.py` in one session goes red on another session's healthy
        test — and the first response to a false red is to weaken the check.

        Uses THIS process's pid, which is by construction alive.
        """
        victim = tmp_path / "held_open.txt"
        victim.write_text("original\n")
        entry = sj._open_entry(victim, reason="unit probe", preserve_mtime=True)
        assert entry["pid"] == os.getpid()
        try:
            res = _run()
            assert res.passed is True, (
                "a seed held open by a LIVE process was reported as residue: "
                f"{[(d.name, d.message) for d in res.details if not d.passed]}")
        finally:
            sj._drop_entry(entry)

    def test_the_live_owner_exemption_STOPS_at_the_corpus_leg(self):
        """⚠️ THE ASYMMETRY, ASSERTED — because making it symmetric is the obvious
        "improvement" and it silently disarms the check.

        The first draft exempted live owners on both legs. The corpus leg then could not
        be seeded at all: putting a marked document in the real corpus requires a live
        process, so every possible production-seeded mutation was exempted, and the leg
        passed over its own seed. It reported PASS while a marker sat in the tracked tree
        — §1's defect reached by way of a convenience.

        So: a marker in the corpus is red whoever holds it, and the message says which."""
        doc = _probe_doc("inflight.md")
        with sj.seeded_artifact(
                doc, f"### 9.9 — 🔴 CRITICAL — seeded probe\n\n- **Severity:** critical\n\n"
                f"Seeded by the test suite. <!-- {sj.SEED_MARKER} -->\n",
                reason="in-flight reporting probe"):
            res = _run()
            assert res.passed is False, (
                "a marker in the tracked corpus was exempted because a live process held "
                "it — that exemption makes this leg impossible to seed")
            msg = _leg(res, "corpus").message or ""
            assert "IN FLIGHT" in msg, msg
            # …while the JOURNAL leg does exempt it, which is the half that prevents a
            # concurrent session's healthy test from reading as unrepaired state.
            assert _leg(res, "journal").passed is True, _leg(res, "journal").message

    def test_the_population_floor_has_zero_headroom_and_is_not_vacuous(self):
        """Guide §2.5. A grep guard whose glob narrows reports 'no residue' over nothing;
        the floor is what makes that UNVERIFIED rather than a pass."""
        from src.core.constants import REVIEW_CORPUS_DOC_FLOOR
        live = len(list(REVIEWS.glob("*/*.md")))
        assert REVIEW_CORPUS_DOC_FLOOR > 0, "a floor of zero cannot fire"
        assert live >= REVIEW_CORPUS_DOC_FLOOR, (
            f"the corpus holds {live} documents, below the frozen floor of "
            f"{REVIEW_CORPUS_DOC_FLOOR}. Review documents are append-only, so this means "
            f"documents were DELETED or the glob narrowed — not that the corpus shrank.")
        res = _run()
        assert f"{live}" in (_leg(res, "corpus").message or ""), (
            "the check does not report how many documents it scanned, so a narrowed "
            "glob would be invisible in its output")

    def test_A_NARROWED_GLOB_IS_UNVERIFIED_NOT_A_PASS(self, monkeypatch):
        """FIRES ON THE SEEDED DEFECT: raise the floor above the live population and the
        check must report `measured=False`, never PASS. This is the direction §2.5 says
        an emptiness guard alone does not cover."""
        import src.core.constants as _c
        live = len(list(REVIEWS.glob("*/*.md")))
        monkeypatch.setattr(_c, "REVIEW_CORPUS_DOC_FLOOR", live + 1)
        res = _run()
        assert res.passed is False
        leg = _leg(res, "corpus")
        assert leg.measured is False, (
            "a scan that lost its population reported a measurement; that is a clean "
            "bill issued over nothing")


# ══════════════════════════════════════════════════════════════════════════════════
# The mechanism — including a REAL kill
# ══════════════════════════════════════════════════════════════════════════════════

def _a_dead_pid() -> int:
    """A pid that is certainly not running: spawn `true`, reap it, reuse its number.

    Not a made-up large integer — pid namespaces differ and a guessed number can be live,
    which would silently turn every assertion about orphans into an assertion about
    in-flight seeds.
    """
    p = subprocess.Popen([sys.executable, "-c", "pass"])
    p.wait()
    return p.pid


class TestTheJournalSurvivesAKill:

    def test_a_SIGKILLED_seeder_leaves_repairable_residue(self, tmp_path):
        """⚠️ THE WHOLE POINT, PROVEN WITH SIGNAL 9 rather than with a patched restore.

        A child process seeds a file and then blocks forever. We `SIGKILL` it — so no
        `finally`, no atexit, no signal handler runs, exactly as when a harness timeout
        killed the D10 run. The file is then observably still seeded, the journal still
        holds the original bytes, and `repair()` from THIS process puts it back.

        Restoring from a different process is the capability `try/finally` does not have,
        and it is the only claim this file is really making.
        """
        victim = tmp_path / "victim.txt"
        victim.write_text("ORIGINAL CONTENT\n")
        flag = tmp_path / "seeded.flag"

        child = subprocess.Popen(
            [sys.executable, "-c",
             "import sys, time, pathlib\n"
             f"sys.path.insert(0, {str(SK_ROOT / 'scripts')!r})\n"
             "import seed_journal as sj\n"
             f"with sj.journalled(pathlib.Path({str(victim)!r}), reason='kill probe'):\n"
             f"    pathlib.Path({str(victim)!r}).write_text('SEEDED\\n')\n"
             f"    pathlib.Path({str(flag)!r}).write_text('x')\n"
             "    time.sleep(600)\n"],
            cwd=str(SK_ROOT))
        try:
            deadline = time.time() + 60
            while not flag.exists() and time.time() < deadline:
                if child.poll() is not None:
                    pytest.fail(f"the seeding child exited early (rc={child.returncode})")
                time.sleep(0.05)
            assert flag.exists(), "the child never got as far as seeding"
            assert victim.read_text() == "SEEDED\n"

            child.send_signal(signal.SIGKILL)
            child.wait(timeout=30)
            assert child.returncode in (-signal.SIGKILL, -9), child.returncode
        finally:
            if child.poll() is None:                       # pragma: no cover - cleanup
                child.kill()
                child.wait(timeout=30)

        # THE STATE THAT COST THREE DAYS: the seed is still there and nothing knows.
        assert victim.read_text() == "SEEDED\n", (
            "the child's write did not survive the kill — this test is not reproducing "
            "the failure it exists for")

        orphans = [e for e in sj.outstanding() if e["path"] == str(victim)]
        assert len(orphans) == 1, (
            f"the journal does not hold the killed seed; nothing could repair it. "
            f"Outstanding: {[e['path'] for e in sj.outstanding()]}")
        assert not orphans[0]["live"], "the killed child is reported as still running"

        # …and a LATER process puts it back, which is the capability `finally` lacks.
        actions = sj.repair()
        assert any(str(victim) in a for a in actions), actions
        assert victim.read_text() == "ORIGINAL CONTENT\n"
        assert not [e for e in sj.outstanding() if e["path"] == str(victim)]

    def test_repair_does_not_touch_a_seed_a_live_process_holds(self, tmp_path):
        """⚠️ THE CORRUPTION THIS MECHANISM MUST NOT CAUSE. Concurrent sessions share this
        repo. If `repair()` restored an in-flight seed, one session's session-start fixture
        would yank a file out from under another session's running test — turning crash
        safety into a data race. The pid check is what prevents it, so it is asserted."""
        victim = tmp_path / "held.txt"
        victim.write_text("ORIGINAL\n")
        with sj.journalled(victim, reason="live-holder probe"):
            victim.write_text("SEEDED\n")
            actions = sj.repair()
            assert not any(str(victim) in a for a in actions), (
                f"repair() restored a seed still held by a live process: {actions}")
            assert victim.read_text() == "SEEDED\n"
        assert victim.read_text() == "ORIGINAL\n"

    def test_the_journal_is_durable_BEFORE_the_file_is_touched(self, tmp_path):
        """Ordering, not merely presence. If the entry were written after the mutation
        there would be a window in which a kill loses the original bytes entirely — the
        failure this module exists to remove, made smaller rather than removed."""
        victim = tmp_path / "ordering.txt"
        victim.write_text("ORIGINAL\n")
        seen: list[str] = []
        real_write_entry = sj._write_entry

        def spy(entry):
            seen.append(victim.read_text())
            return real_write_entry(entry)

        sj._write_entry = spy
        try:
            with sj.journalled(victim, reason="ordering probe"):
                victim.write_text("SEEDED\n")
        finally:
            sj._write_entry = real_write_entry
        assert seen == ["ORIGINAL\n"], (
            f"the journal entry was published when the file already read {seen!r} — the "
            f"backup does not precede the mutation")

    def test_the_backup_holds_the_original_bytes_on_disk(self, tmp_path):
        """The entry is only useful if the bytes are actually there. Read them from the
        filesystem while the seed is open, the way a repairing process would."""
        victim = tmp_path / "bytes.txt"
        victim.write_text("ORIGINAL\n")
        with sj.journalled(victim, reason="backup probe"):
            victim.write_text("SEEDED\n")
            [entry] = [e for e in sj.outstanding(include_live=True)
                       if e["path"] == str(victim)]
            assert Path(entry["backup"]).read_bytes() == b"ORIGINAL\n"
            assert json.loads(sj._entry_path(entry["id"]).read_text())["sha256"]

    def test_mtime_is_restored_not_merely_bytes(self, tmp_path):
        """⚠️ MEASURED CONSEQUENCE, not tidiness. `bundle_manuscript_length` refuses to
        size a PDF older than its draft's `\\input` closure, so a byte-perfect restore
        with a fresh mtime silently took D1 UNMEASURED and shrank a gate's population
        while it kept passing."""
        victim = tmp_path / "mtime.txt"
        victim.write_text("ORIGINAL\n")
        os.utime(victim, ns=(1_000_000_000_000_000_000, 1_000_000_000_000_000_000))
        before = victim.stat().st_mtime_ns
        with sj.journalled(victim, reason="mtime probe"):
            victim.write_text("SEEDED\n")
        assert victim.stat().st_mtime_ns == before

    def test_a_seed_that_does_not_apply_is_an_ERROR(self, tmp_path):
        """A mutation that silently fails to change the file is a test that proves
        nothing while reporting success — the exact shape of the four checks QI-31…34
        found satisfying every fixture test and unable to fail in production."""
        victim = tmp_path / "noop.txt"
        victim.write_text("ORIGINAL\n")
        with pytest.raises(ValueError, match="did not change"):
            with sj.seeded_mutation(victim, "ORIGINAL\n", reason="noop probe"):
                pass                                        # pragma: no cover
        assert victim.read_text() == "ORIGINAL\n"
        assert not [e for e in sj.outstanding() if e["path"] == str(victim)]

    def test_a_corpus_seed_without_the_marker_is_REFUSED(self):
        """The invariant the guard check depends on. If an unmarked seed could reach the
        corpus, `seed_residue_absent`'s corpus leg would be measuring a population the
        seeders can leave. Enforced at write time because afterwards it is too late."""
        with pytest.raises(ValueError, match="SEEDED"):
            with sj.seeded_artifact(_probe_doc("unmarked.md"), "# no marker here\n",
                                    reason="marker enforcement probe"):
                pass                                        # pragma: no cover
        assert not _probe_doc("unmarked.md").exists()

    def test_journalled_REFUSES_the_review_corpus(self):
        """`journalled` cannot enforce the marker — it never sees the content — so it must
        not accept a corpus path at all. Otherwise it is the hole in the invariant."""
        target = REVIEWS / "2026-08-12-0200-citation-integrity" / "D10.md"
        assert target.is_file(), "re-point this assertion; the document moved"
        with pytest.raises(ValueError, match="seeded_mutation"):
            with sj.journalled(target, reason="should never open"):
                pass                                        # pragma: no cover


# ══════════════════════════════════════════════════════════════════════════════════
# The suite-wide repair fixture
# ══════════════════════════════════════════════════════════════════════════════════

class TestTheSessionFixtureRepairs:

    def test_conftest_registers_an_autouse_session_repair(self):
        """⚠️ ASSERTED AGAINST THE AST, not against a passing run. The fixture's effect is
        invisible from inside a session it already repaired, so "the suite is green" is
        not evidence that it exists. Deleting it must break something."""
        import ast
        tree = ast.parse((SK_ROOT / "tests" / "conftest.py").read_text())
        fns = [n for n in tree.body if isinstance(n, ast.FunctionDef)]
        target = [f for f in fns if "repair" in f.name]
        assert target, "tests/conftest.py has no repair fixture"
        fn = target[0]
        deco = [d for d in fn.decorator_list if isinstance(d, ast.Call)]
        kwargs = {k.arg: getattr(k.value, "value", None) for d in deco for k in d.keywords}
        assert kwargs.get("scope") == "session", kwargs
        assert kwargs.get("autouse") is True, kwargs
        called = {ast.unparse(n.func) for n in ast.walk(fn) if isinstance(n, ast.Call)}
        assert "seed_journal.repair" in called, (
            f"the fixture does not call the repair function; it is a no-op that reads as "
            f"a guarantee. Calls found: {sorted(called)}")

    def test_the_cli_reports_orphans_with_a_nonzero_exit(self, tmp_path):
        """`status` is what a human runs after a kill. It must SAY something is wrong,
        and it must say it in the exit code — the half a script can act on."""
        victim = tmp_path / "cli.txt"
        victim.write_text("ORIGINAL\n")
        entry = sj._open_entry(victim, reason="cli probe", preserve_mtime=True)
        entry["pid"] = _a_dead_pid()
        sj._write_entry(entry)
        try:
            proc = subprocess.run(
                [sys.executable, str(SK_ROOT / "scripts" / "seed_journal.py"), "status"],
                capture_output=True, text=True, cwd=str(SK_ROOT))
            assert proc.returncode == 1, proc.stdout + proc.stderr
            assert "ORPHANED" in proc.stdout and str(victim) in proc.stdout
        finally:
            sj._drop_entry(entry)


# ══════════════════════════════════════════════════════════════════════════════════
# ONE MECHANISM — the inventory, ratcheted
# ══════════════════════════════════════════════════════════════════════════════════
#
# ⚠️ WITHOUT THIS THE VERIFY HAS A HOLE. Everything above proves the mechanism works and
# the guard fires. None of it proves the SEEDING TESTS USE the mechanism — a test could
# still restore a production artifact in a bare `finally` and be exactly as fragile as the
# one that cost three days. This scan is what turns "a crash-safe seeder exists" into "the
# seeders are crash-safe".
#
# ⚠️ IT IS A SCAN WITH A FROZEN ALLOW-LIST, NOT A JUDGEMENT. The predicate is purely
# syntactic — a `try` whose `finally` writes to a path — so it cannot drift into opinion.
# What it CANNOT know is whether the path is production or a `tmp_path`, so every match is
# held against a named, dated list. `test_d5_mutation_obligation.py` makes the same choice
# for the same reason, and says why at length.

#: `<file>:<function>` sites that restore a file in a `finally` and are NOT required to
#: journal it, each with the reason. **MAY ONLY SHRINK.** Adding an entry is a decision.
_UNJOURNALLED_RESTORES: dict[str, str] = {
    "tests/e2e/test_parameter_signoff_persists.py:"
    "test_a_confirmed_parameter_is_still_confirmed_after_reload":
        "covered by the AUTOUSE journal in tests/e2e/conftest.py, which opens its entry "
        "on src/core/provenance.py before this test starts. The local finally is the "
        "in-process fast path, not the only copy of the restore information.",
    "tests/test_build_graph_memo.py:tmp_probe":
        "creates and sweeps a review DIRECTORY, and sweeps it again unconditionally at "
        "SETUP (`rmtree(..., ignore_errors=True)` before `mkdir`), so a killed run is "
        "repaired by the next run of this fixture rather than by the journal. The "
        "document written inside it IS journalled (`seeded_artifact`).",
}

_SCAN_ROOTS = ("tests",)


def _finally_restore_sites() -> dict[str, str]:
    """`<relpath>:<enclosing def>` → the unparsed `finally` body, for every `try` whose
    `finally` writes, unlinks, renames or removes a filesystem path."""
    import ast
    _WRITERS = ("write_text", "write_bytes", "unlink", "rmdir", "rmtree", "replace",
                "rename")
    found: dict[str, str] = {}
    for root in _SCAN_ROOTS:
        for path in sorted((SK_ROOT / root).rglob("*.py")):
            tree = ast.parse(path.read_text(encoding="utf-8"))
            # map each node to its nearest enclosing function, so a match is nameable
            owner: dict[int, str] = {}
            for fn in (n for n in ast.walk(tree) if isinstance(n, ast.FunctionDef)):
                for sub in ast.walk(fn):
                    owner.setdefault(id(sub), fn.name)
            for node in ast.walk(tree):
                if not (isinstance(node, ast.Try) and node.finalbody):
                    continue
                body = "\n".join(ast.unparse(s) for s in node.finalbody)
                if not any(w in body for w in _WRITERS):
                    continue
                key = (f"{path.relative_to(SK_ROOT)}:"
                       f"{owner.get(id(node), '<module>')}")
                found[key] = body
    return found


class TestEverySeederUsesTheOneMechanism:

    def test_the_scan_reaches_a_plausible_population(self):
        """Guide §2.5 — the seam. This scan's whole value is in what it finds; if the AST
        walk silently matched nothing, the ratchet below would pass vacuously and read as
        proof that every seeder is journalled.

        ⚠️ THE FLOOR IS ON FILES PARSED, NOT ON `try` STATEMENTS FOUND — and the first
        draft got that wrong in a way worth recording. A floor on `try` count fires when a
        seeder is MIGRATED, because migrating removes a `try`: the ratchet would have
        punished exactly the work it exists to encourage, and the only way to keep it
        green would have been to lower it after every fix. Files parsed measures what the
        seam is actually about — whether the walk reached the tree — and moves the right
        way when the tree grows.
        """
        import ast
        parsed = 0
        for root in _SCAN_ROOTS:
            for p in (SK_ROOT / root).rglob("*.py"):
                ast.parse(p.read_text(encoding="utf-8"))   # unswallowed: a parse failure
                parsed += 1                                # must break this test, loudly
        # Measured live 2026-08-15: 199 test files. Lower only with a stated reason.
        assert parsed >= 199, (
            f"the AST walk parsed only {parsed} files under {_SCAN_ROOTS}; it is not "
            f"seeing the test tree, so the ratchet below is measuring nothing")

    def test_no_unjournalled_restore_outside_the_frozen_list(self):
        """FIRES ON THE SEEDED DEFECT: revert any migrated seeder to a bare
        `try/finally` and this names it.

        ⚠️ The remedy is `scripts/seed_journal.py`, never an entry in the allow-list. An
        allow-list that grows to accommodate each new seeder is the backlog
        `test_d5_mutation_obligation` was written to stop growing, one file over."""
        sites = _finally_restore_sites()
        new = sorted(set(sites) - set(_UNJOURNALLED_RESTORES))
        assert not new, (
            f"{len(new)} test site(s) restore a file in a bare `finally`, which does not "
            f"run under SIGKILL:\n" +
            "\n".join(f"  {k}\n      finally: {sites[k].splitlines()[0]}" for k in new) +
            "\n\nUse `seed_journal.seeded_mutation` / `seeded_artifact` / `journalled` so "
            "the restore survives a killed process. If this site genuinely cannot (it "
            "writes only under tmp_path, or another journal already covers it), add it to "
            "_UNJOURNALLED_RESTORES with the reason.")

    def test_the_allow_list_only_shrinks(self):
        """Every exemption must still be REAL. A stale entry is an exemption granted to
        code that no longer exists, and the next matching site inherits it silently."""
        sites = _finally_restore_sites()
        stale = sorted(set(_UNJOURNALLED_RESTORES) - set(sites))
        assert not stale, (
            f"{len(stale)} exemption(s) name a site that no longer restores anything in a "
            f"`finally`: {stale}. Delete them — an exemption outliving its subject is a "
            f"hole waiting for the next site with the same key.")
        assert len(_UNJOURNALLED_RESTORES) <= 2, (
            f"the unjournalled-restore allow-list has grown to "
            f"{len(_UNJOURNALLED_RESTORES)}. It may only shrink.")


def test_the_guard_is_REGISTERED_not_merely_importable():
    """⚠️ WITHOUT THIS THE VERIFY HAS ITS LAST HOLE. Every assertion above reaches the
    check by importing `validation.checks.reviews` directly, so the whole file stays green
    with the check dropped from `_CANONICAL_ORDER` — a guard nobody runs, which is the
    same nothing as a guard that cannot fire.

    `close_finding` executes this file's Verify verbatim and nothing else, so the
    registration has to be provable from inside it.
    """
    import validate
    assert "seed_residue_absent" in validate._CANONICAL_ORDER, (
        "the check is not in the canonical order — validate.py will never run it")
    assert validate.check_seed_residue_absent is rv.check_seed_residue_absent, (
        "validate.py's re-export does not point at the live check")
    from validation._registry import _CHECKS
    spec = [s for s in _CHECKS if s.name == "seed_residue_absent"]
    assert spec, f"not in the registry: {sorted(s.name for s in _CHECKS)[:5]}…"
    from validation._config import CI_SKIP
    assert "seed_residue_absent" not in CI_SKIP, (
        "the check is CI_SKIPped, so --ci never measures it")


class TestTheMarkerMustMintAFindingNotMerelyAppear:
    """ADR-014-adjacent, 2026-08-15 — the guard shipped keying on the STRING.

    Within hours a finding documenting the seeder-vs-seeder race quoted the marker in its
    own prose, and the guard flagged THAT DOCUMENT as residue — with remediation text
    telling the reader to `git checkout --` it, which would have deleted the finding. A
    guard whose repair instruction destroys correct work is worse than the defect.

    The harm residue does is that it MINTS A FINDING; prose about the marker mints nothing.
    So the predicate is the finding-shaped stanza the extractor keys on.
    """

    M = "SKEFT-SEEDED-BY-TEST-SUITE"

    def _f(self):
        from validation.checks.reviews import _marker_mints_a_finding
        return _marker_mints_a_finding

    def test_a_seeded_STANZA_fires(self):
        assert self._f()(
            f"### 1.1 — 🔴 CRITICAL — seeded mutation\n\n- **Severity:** critical\n\n"
            f"Seeded by the test suite. <!-- {self.M} -->\n", self.M) is True

    def test_a_PROSE_mention_does_not_fire(self):
        assert self._f()(f"The marker `{self.M}` is written by the seeder.\n", self.M) is False

    def test_a_real_finding_plus_a_prose_mention_ELSEWHERE_does_not_fire(self):
        """⚠️ THE SEAM, and the leg that caught a real bug in the first fix. Under
        `re.DOTALL` a greedy `.*$` on the heading line swallows the whole document, so the
        body pattern never stops at the next heading and a prose mention three sections
        later matched. Both a `##` and a `###` boundary are pinned: stopping only at `###`
        let a stanza swallow a following `## Notes`."""
        for boundary in ("## Notes", "### Appendix"):
            doc = (f"### 2.1 — 🔴 MAJOR — real\n\n- **Severity:** major\n\nBody.\n\n"
                   f"{boundary}\n\nThe marker `{self.M}` in prose.\n")
            assert self._f()(doc, self.M) is False, f"leaked across {boundary!r}"

    def test_the_live_race_FINDING_DOCUMENT_does_not_trip_the_guard(self):
        """Production-anchored: the document that exposed this must stay clean, or the
        next person to document the mechanism cannot write it down."""
        import validate_helpers as _H
        doc = (_H.PROJECT_ROOT / "papers/AutomatedReviews"
               / "2026-08-15-seeded-mutation-seeder-vs-seeder-race/infra.md")
        if not doc.is_file():
            import pytest
            pytest.skip("race finding not present")
        assert self.M in doc.read_text(), "the pin is vacuous unless the doc quotes the marker"
        assert self._f()(doc.read_text(), self.M) is False


class TestConcurrentSeedersAreSerialised:
    """Two LIVE seeders of the same production path must not interleave.

    The journal made a seed survive a KILLED run. It does nothing about the other
    concurrency axis, and that gap was not hypothetical: on 2026-08-15 the D10 stanza
    reappeared in the corpus while two suites ran concurrently, with the journal
    reporting 0 in flight. Filed as
    `papers/AutomatedReviews/2026-08-15-seeded-mutation-seeder-vs-seeder-race/infra.md`.

    Why interleaving corrupts: A reads the original, B reads and captures A's SEED as its
    own "original", both restore, and the file ends carrying a seed. Each transaction
    completed correctly on its own terms, so neither can detect it — the invariant is
    PAIRWISE. Residue is not inert either: the graph extractor mints a marker-bearing
    section as an OPEN finding at its declared severity, which is how a race manufactures
    a blocking CRITICAL indistinguishable downstream from a real one.

    ⚠️ These tests assert MUTUAL EXCLUSION, not a hoped-for interleaving. A test that
    races two threads and checks the file afterwards passes by luck on a fixed lock and
    passes by luck on a broken one — the window is microseconds. So the first leg holds
    the lock open and proves the second acquirer is refused, which is deterministic.
    """

    def test_a_second_seeder_of_the_same_path_is_excluded(self, tmp_path):
        """FIRES ON THE SEEDED DEFECT: with no lock, the second acquire succeeds."""
        import threading
        import seed_journal as sj

        target = tmp_path / "victim.txt"
        target.write_text("original\n")

        entered = threading.Event()
        release = threading.Event()
        failure: list[BaseException] = []

        def hold():
            try:
                with sj._path_lock(target):
                    entered.set()
                    release.wait(timeout=10)
            except BaseException as exc:      # noqa: BLE001 - reported, not swallowed
                failure.append(exc)
                entered.set()

        t = threading.Thread(target=hold, daemon=True)
        t.start()
        assert entered.wait(timeout=10), "the holding thread never acquired the lock"
        assert not failure, f"the holding thread failed: {failure!r}"

        try:
            with pytest.raises(TimeoutError) as caught:
                with sj._path_lock(target, timeout=0.5):
                    pass
            assert "seeding" in str(caught.value), (
                "the exclusion fired but its message does not explain what is held or "
                "why proceeding is unsafe, so a maintainer meeting it mid-suite cannot "
                "act on it")
        finally:
            release.set()
            t.join(timeout=10)

    def test_a_different_path_is_not_excluded(self, tmp_path):
        """The negative control. A lock that blocks EVERYTHING would also pass the test
        above while serialising the entire suite — so prove the exclusion is keyed to the
        path, not global."""
        import threading
        import seed_journal as sj

        a = tmp_path / "one.txt"
        b = tmp_path / "two.txt"
        a.write_text("a\n")
        b.write_text("b\n")

        entered = threading.Event()
        release = threading.Event()

        def hold():
            with sj._path_lock(a):
                entered.set()
                release.wait(timeout=10)

        t = threading.Thread(target=hold, daemon=True)
        t.start()
        assert entered.wait(timeout=10)
        try:
            with sj._path_lock(b, timeout=2.0):
                pass       # must NOT raise: different path, different transaction
        finally:
            release.set()
            t.join(timeout=10)

    def test_the_lock_key_distinguishes_same_named_files_in_different_trees(self, tmp_path):
        """Two worktrees seeding same-named files are different transactions.

        Keying the lock on the file's NAME would serialise every worktree against every
        other, turning a correctness fix into a throughput bug during a multi-agent
        campaign — which is exactly when concurrent suites run."""
        import seed_journal as sj

        one = tmp_path / "wt1" / "papers" / "D10.md"
        two = tmp_path / "wt2" / "papers" / "D10.md"
        for p in (one, two):
            p.parent.mkdir(parents=True)
            p.write_text("x\n")

        assert sj._lock_path(one) != sj._lock_path(two), (
            "same-named files in different trees share a lockfile, so unrelated "
            "worktrees would block each other")
        assert sj._lock_path(one) == sj._lock_path(one), "the lock key is not stable"
