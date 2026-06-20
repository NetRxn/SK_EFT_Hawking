"""Unit tests for the harvest reaper — the qualifies-for-reap predicate + reap() with injected
ps/kill (so tests NEVER inspect or kill a real process). Run: uv run python -m pytest ... -q"""
import sys
from pathlib import Path

SCRIPTS = Path(__file__).resolve().parent.parent / "scripts"
sys.path.insert(0, str(SCRIPTS))
import harvest_reaper as rp  # noqa: E402


def _rec(pid, stat="S", cpu=0.1, etimes=14400, cmd="/x/claude --input-format stream-json"):
    return {"pid": pid, "ppid": 1, "stat": stat, "cpu": cpu, "etimes": etimes, "cmd": cmd}


# ---- qualifies_for_reap (pure) ---------------------------------------------

def test_reaps_a_leaked_idle_firing():
    assert rp.qualifies_for_reap(_rec(999), current_pid=111) is True


def test_spares_current_firing():
    assert rp.qualifies_for_reap(_rec(111), current_pid=111) is False


def test_spares_running_process():
    assert rp.qualifies_for_reap(_rec(999, stat="R+"), current_pid=111) is False


def test_spares_cpu_active():
    assert rp.qualifies_for_reap(_rec(999, cpu=42.0), current_pid=111) is False


def test_spares_young_process():
    assert rp.qualifies_for_reap(_rec(999, etimes=60), current_pid=111) is False


def test_spares_pid_reuse_non_claude():
    # OS recycled the PID into a different process -> cmdline no longer 'claude'
    assert rp.qualifies_for_reap(_rec(999, cmd="node /srv/app.js"), current_pid=111) is False


def test_spares_dead_pid():
    assert rp.qualifies_for_reap(None, current_pid=111) is False


# ---- reap() with injected ps/kill ------------------------------------------

def test_reap_kills_only_qualifying_and_rewrites_log(tmp_path):
    # log holds: a leaked firing (200), a still-working firing (201, CPU-active),
    # a dead pid (202), and the current pid (300 — must never be reaped).
    (tmp_path / "harvest_pids.log").write_text("200\n201\n202\n300\n")
    table = {200: _rec(200), 201: _rec(201, cpu=30.0), 202: None}
    killed = []
    r = rp.reap(tmp_path, _proc_fn=lambda p: table.get(p),
                _kill_fn=lambda pid, sig: killed.append(pid), _current=300)
    assert killed == [200]                       # only the leaked idle one
    assert r["reaped"] == [200]
    assert 201 in r["survivors"]                 # alive-but-working -> kept tracking
    # log rewritten to survivors + current (dead 202 + reaped 200 dropped)
    keep = set(int(x) for x in (tmp_path / "harvest_pids.log").read_text().split())
    assert keep == {201, 300}


def test_reap_never_kills_a_pid_not_in_the_log(tmp_path):
    # a live goal/interactive session (999) is NOT self-logged -> never even inspected for kill
    (tmp_path / "harvest_pids.log").write_text("200\n300\n")
    table = {200: _rec(200), 999: _rec(999)}     # 999 looks reapable but is NOT logged
    killed = []
    rp.reap(tmp_path, _proc_fn=lambda p: table.get(p),
            _kill_fn=lambda pid, sig: killed.append(pid), _current=300)
    assert 999 not in killed                      # self-logged gate: launcher/goal untouchable
    assert killed == [200]


def test_reap_dry_run_kills_nothing_and_leaves_log(tmp_path):
    (tmp_path / "harvest_pids.log").write_text("200\n300\n")
    before = (tmp_path / "harvest_pids.log").read_text()
    killed = []
    r = rp.reap(tmp_path, dry_run=True, _proc_fn=lambda p: _rec(p),
                _kill_fn=lambda pid, sig: killed.append(pid), _current=300)
    assert killed == []                           # dry-run never kills
    assert r["reaped"] == [200] and r["dry_run"] is True   # but reports what it WOULD
    assert (tmp_path / "harvest_pids.log").read_text() == before  # log untouched


def test_reap_first_run_no_log(tmp_path):
    # no prior log -> nothing reaped, current logged for the next firing to reap
    r = rp.reap(tmp_path, _proc_fn=lambda p: None,
                _kill_fn=lambda pid, sig: None, _current=300)
    assert r["reaped"] == []
    assert (tmp_path / "harvest_pids.log").read_text().split() == ["300"]
