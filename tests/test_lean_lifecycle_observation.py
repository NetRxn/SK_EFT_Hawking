"""Production lifecycle controls with exclusively external, isolated OS seams.

The host is independently populated, not a mocked admission verdict. No controller
or supervisor guard is patched. Real Git commands are limited to pytest tmp repos.
"""
from __future__ import annotations

import errno
import json
import os
import signal
import subprocess
from contextlib import nullcontext
from pathlib import Path
from types import SimpleNamespace

import pytest

from scripts.lean_slots import state, supervisor as lifecycle, cli
from scripts.lean_slots.controller import Controller
from scripts.lean_slots.state import Inventory, SlotError, atomic_json, read_json
from scripts.lean_slots.supervisor import Supervisor
from tests.test_lean_slots import slot_repo, downstream_repo, run


class Host:
    """External ps/socket/Popen/kill/clock model with recorded observable attempts."""
    def __init__(self, patch):
        self.rows = {1: (0, "isolated init", "Sun Oct 11 00:00:00 2026 isolated init"),
                     os.getpid(): (1, "pytest isolated observer", "Sun Oct 11 00:00:00 2026 pytest isolated observer")}
        self.ports = {}
        self.denied_pids = set()
        self.denied_ports = set()
        self.census_denied = False
        self.after_census = None
        self.signals = []
        self.launches = []
        self.handles = []
        self.clock = 0.0
        self.next_pid = 810000
        self.launch_failure = None
        self.no_open = False
        self.retain_on_terminate = False
        self.after_signal = None
        self.after_poll = None
        self.selected_results = {}
        self.census_result = None
        self.port_errors = {}
        self.launch_reservations = []
        self.ps_calls = []
        self.command_calls = []
        self.real_run = subprocess.run
        patch.setattr(subprocess, "run", self.run)
        patch.setattr(lifecycle.socket, "create_connection", self.connection)
        patch.setattr(subprocess, "Popen", self.popen)
        patch.setattr(os, "kill", self.kill)
        patch.setattr(lifecycle.time, "monotonic", lambda: self.clock)
        patch.setattr(lifecycle.time, "sleep", self.sleep)

    def add(self, pid, command, *, ppid=None, port=None, signature=None):
        signature = signature or f"Sun Oct 11 00:00:00 2026 {command}"
        self.rows[pid] = (os.getpid() if ppid is None else ppid, command, signature)
        if port:
            self.ports[port] = pid
        return signature

    def run(self, argv, **kwargs):
        if argv[0] != "ps":
            self.command_calls.append(list(argv))
            # Only disposable fixture Git/build commands are allowed to execute.
            if argv[0] not in {"git", "/usr/bin/true", "cp"}:
                raise AssertionError(f"unexpected external subprocess: {argv}")
            # Real subprocess.run uses Popen; temporarily restore its OS implementation.
            saved = subprocess.Popen
            subprocess.Popen = self.real_popen
            try:
                return self.real_run(argv, **kwargs)
            finally:
                subprocess.Popen = saved
        self.ps_calls.append(list(argv))
        if "-axo" in argv:
            if self.census_denied:
                raise PermissionError(errno.EPERM, "census denied")
            if self.census_result is not None:
                if isinstance(self.census_result, BaseException):
                    raise self.census_result
                return self.census_result
            output = "".join(f"{pid} {row[0]} {row[2]}\n" for pid, row in self.rows.items())
            if self.after_census:
                self.after_census()
            return SimpleNamespace(returncode=0, stdout=output, stderr="")
        pid = int(argv[2])
        if pid in self.selected_results:
            result = self.selected_results[pid]
            if isinstance(result, BaseException):
                raise result
            return result
        if pid in self.denied_pids:
            raise PermissionError(errno.EPERM, "selected ps denied")
        return SimpleNamespace(returncode=0 if pid in self.rows else 1,
                               stdout=self.rows[pid][2] if pid in self.rows else "", stderr="")

    def connection(self, address, **kwargs):
        port = address[1]
        if port in self.port_errors:
            raise self.port_errors[port]
        if port in self.denied_ports:
            raise PermissionError(errno.EPERM, "socket denied")
        if port not in self.ports:
            raise ConnectionRefusedError(errno.ECONNREFUSED, "refused")
        return nullcontext()

    def sleep(self, seconds):
        self.clock += seconds

    def remove(self, pid):
        self.rows.pop(pid, None)
        for port, owner in list(self.ports.items()):
            if owner == pid:
                self.ports.pop(port)

    def kill(self, pid, sig):
        assert sig == signal.SIGTERM, "automatic SIGKILL forbidden"
        self.signals.append((pid, sig))
        self.remove(pid)
        if self.after_signal:
            self.after_signal(pid)

    def popen(self, argv, **kwargs):
        self.launches.append(list(argv))
        if self.launch_failure:
            raise self.launch_failure
        pid = self.next_pid
        self.next_pid += 1
        if "--port" in argv:
            port = int(argv[argv.index("--port") + 1])
        else:
            inv = Inventory.load(Path(argv[argv.index("--inventory") + 1]))
            port = int(inv.slot(int(argv[-1]))["proxy_port"])
        records = []
        for path in (Path(os.environ["LEAN_SLOT_STATE_DIR"]) / "processes").glob("*.json"):
            record = json.loads(path.read_text())
            if record.get("port") == port:
                records.append(record)
        self.launch_reservations.append(records)
        self.add(pid, " ".join(argv), port=None if self.no_open else port)
        host = self
        class Handle:
            def __init__(self):
                self.pid = pid
                self.terminations = 0
                self.waits = []
                self.returncode = None
            def poll(self):
                if self.returncode is not None:
                    return self.returncode
                if host.after_poll:
                    host.after_poll(self)
                if self.returncode is None and self.pid not in host.rows:
                    self.returncode = 0
                return self.returncode
            def terminate(self):
                self.terminations += 1
                if not host.retain_on_terminate:
                    host.remove(self.pid)
            def wait(self, timeout=None):
                self.waits.append(timeout)
                if self.returncode is None and self.pid in host.rows:
                    raise subprocess.TimeoutExpired(argv, timeout)
                self.returncode = 0
                return self.returncode
        result = Handle()
        self.handles.append(result)
        return result


@pytest.fixture
def host(monkeypatch):
    original = subprocess.Popen
    value = Host(monkeypatch)
    value.real_popen = original
    return value


@pytest.fixture
def rig(host, slot_repo, monkeypatch):
    ctl, repo, worktrees = slot_repo
    monkeypatch.delenv("LEAN_SLOT_SKIP_SUPERVISOR", raising=False)
    return ctl, Supervisor(ctl.inventory), host


def owned(sup, host, kind, number, pid, *, stale=False):
    port = int(sup.inventory.slot(number)[f"{kind}_port"])
    command = sup.backend_command(number) if kind == "backend" else sup.proxy_command(number)
    signature = host.add(pid, " ".join(command), port=port)
    record = dict(schema_version=1, process_schema_version=2, phase="running", repo_role=sup.inventory.repo_role,
                  kind=kind, slot=number, pid=pid, signature=signature,
                  runtime_fingerprint="old" if stale else sup._runtime_fingerprint(kind, number))
    atomic_json(sup.inventory.process_path(kind, number), record)
    return sup.inventory.process_path(kind, number)


def test_control_01_observation_and_absence(rig):
    _, sup, host = rig
    path = owned(sup, host, "backend", 1, 810101)
    original = path.read_bytes()
    host.denied_pids.add(810101)
    host.denied_ports.add(29101)
    with pytest.raises(SlotError):
        sup.stop_backend(1)
    assert path.read_bytes() == original and not host.signals
    assert sup.process_state("backend", 1) == "unavailable"
    assert state.observe_process(810101).state == "unavailable"
    assert lifecycle._port_observation("127.0.0.1", 29101).state == "unavailable"
    host.denied_pids.clear(); host.denied_ports.clear()
    for failure in (SimpleNamespace(returncode=2, stdout="", stderr="denied"), subprocess.TimeoutExpired(["ps"], 2)):
        host.selected_results[810101] = failure
        with pytest.raises(SlotError):
            sup.stop_backend(1)
        assert path.read_bytes() == original and not host.signals
        assert state.observe_process(810101).state == "unavailable"
    host.selected_results.clear(); host.port_errors[29101] = TimeoutError("connect timeout")
    assert lifecycle._port_observation("127.0.0.1", 29101).state == "unavailable"
    host.port_errors.clear(); host.remove(810101)
    sup.stop_backend(1)
    assert not path.exists() and sup.process_state("backend", 1) == "down"


def test_control_02_pid_mismatch_and_owned_tree(rig):
    _, sup, host = rig
    path = owned(sup, host, "backend", 1, 810102)
    original = path.read_bytes()
    host.rows[810102] = (os.getpid(), "unrelated replacement", "Sun Oct 11 01:00:00 2026 unrelated replacement")
    with pytest.raises(SlotError, match="mismatch"):
        sup.stop_backend(1)
    assert path.read_bytes() == original and not host.signals
    host.add(810102, " ".join(sup.backend_command(1)), port=29101, signature=read_json(path)["signature"])
    host.add(810202, "lean --worker", ppid=810102)
    def root_reuse():
        host.after_census = None
        host.add(810102, "unrelated replacement", signature="Sun Oct 11 01:00:00 2026 unrelated replacement")
    host.after_census = root_reuse
    with pytest.raises(SlotError, match="identity unavailable/mismatch"):
        sup.stop_backend(1)
    assert path.read_bytes() == original and not host.signals
    host.add(810102, " ".join(sup.backend_command(1)), port=29101, signature=read_json(path)["signature"])
    census_steps = []
    def child_reuse():
        census_steps.append(1)
        if len(census_steps) == 1:
            return  # Selected root coherence census precedes the ownership snapshot.
        host.after_census = None
        host.add(810202, "unrelated child replacement", signature="Sun Oct 11 01:00:00 2026 unrelated child replacement")
    host.after_census = child_reuse
    with pytest.raises(SlotError, match="identity unavailable/mismatch"):
        sup.stop_backend(1)
    assert path.read_bytes() == original and not host.signals
    host.add(810202, "lean --worker", ppid=810102)
    sup.stop_backend(1)
    assert {pid for pid, _ in host.signals} == {810102, 810202} and not path.exists()


def test_control_03_post_signal_unavailable(rig):
    _, sup, host = rig
    path = owned(sup, host, "backend", 1, 810103)
    host.after_signal = lambda pid: host.denied_pids.add(pid)
    with pytest.raises(SlotError, match="post-SIGTERM"):
        sup.stop_backend(1)
    assert path.exists() and read_json(path)["descendants"] and host.signals == [(810103, signal.SIGTERM)]
    host.after_signal = None; host.denied_pids.clear()
    sup.stop_backend(1)
    assert not path.exists()


def test_control_04_prepare_quiescence(rig, monkeypatch):
    ctl, sup, host = rig
    ctl.build(); ctl.acquire(1, client="codex", base_ref="main")
    owned(sup, host, "proxy", 1, 810104)
    host.add(810204, " ".join(sup.backend_command(1)))  # Lost registry, endpoint absent.
    cache = ctl.inventory.worktree(1) / "lean" / ".lake"
    marker = cache / "preserve"
    marker.parent.mkdir(parents=True, exist_ok=True); marker.write_text("preserve")
    reset_count = len([a for a in host.command_calls if "reset" in a])
    with pytest.raises(SlotError):
        ctl.prepare(1)
    assert marker.read_text() == "preserve" and not host.launches
    assert ctl.inventory.lease(1)["state"] == "QUARANTINED"
    assert len([a for a in host.command_calls if "reset" in a]) == reset_count
    host.remove(810204)
    ctl.release(1); ctl.acquire(1, client="codex", base_ref="main"); ctl.prepare(1)
    assert ctl.inventory.lease(1)["state"] == "ACTIVE" and not marker.exists()
    assert sup.process_state("backend", 1) == "running"


def test_control_05_paired_switch_restore(host, downstream_repo, monkeypatch):
    down, public, _, _ = downstream_repo
    monkeypatch.delenv("LEAN_SLOT_SKIP_SUPERVISOR", raising=False)
    target, previous = Supervisor(down.inventory), Supervisor(public.inventory)
    owned(previous, host, "proxy", 1, 810105)
    owned(previous, host, "backend", 1, 810205)
    bodies = []
    with target.activating_from(1, previous):
        bodies.append("cache")
        assert target.capacity_census()["reserved_physical_slots"] == []
    assert bodies == ["cache"] and target.process_state("backend", 1) == "running"
    target.restore_counterpart(1, previous)
    assert previous.process_state("backend", 1) == "running" and target.process_state("backend", 1) == "down"
    assert previous.capacity_census()["complete"]
    with pytest.raises(RuntimeError, match="body failure"):
        with target.activating_from(1, previous):
            raise RuntimeError("body failure")
    assert previous.process_state("backend", 1) == "running"
    host.denied_ports.add(int(target.inventory.slot(1)["proxy_port"]))
    with pytest.raises(SlotError, match="endpoint unavailable"):
        with target.activating_from(1, previous):
            bodies.append("forbidden proxy")
    assert bodies == ["cache"]
    host.denied_ports.clear()
    host.denied_ports.add(int(target.inventory.slot(1)["backend_port"]))
    with pytest.raises(SlotError):
        with target.activating_from(1, previous):
            bodies.append("forbidden")
    assert bodies == ["cache"]
    host.denied_ports.clear(); host.denied_pids.add(read_json(previous.inventory.process_path("backend", 1))["pid"])
    with pytest.raises(SlotError):
        with target.activating_from(1, previous):
            bodies.append("forbidden counterpart")
    assert bodies == ["cache"]
    host.denied_pids.clear()
    with pytest.raises(SlotError, match="body failure.*restoration failed.*restoration launch denied"):
        with target.activating_from(1, previous):
            host.launch_failure = PermissionError("restoration launch denied")
            raise RuntimeError("body failure")
    assert read_json(previous.inventory.process_path("backend", 1))["phase"] == "uncertain_residual"


def test_control_06_prelaunch_durability(rig, monkeypatch):
    _, sup, host = rig
    real_replace = state.os.replace
    def fail_reservation(source, dest):
        if str(dest).endswith("public-wt1-backend.json"):
            raise PermissionError("reservation denied")
        return real_replace(source, dest)
    with monkeypatch.context() as patch:
        patch.setattr(state.os, "replace", fail_reservation)
        with pytest.raises(PermissionError, match="reservation denied"):
            sup.start_backend(1)
    assert not host.launches
    sup.start_backend(1)
    assert len(host.launches) == 1 and read_json(sup.inventory.process_path("backend", 1))["phase"] == "running"
    assert len(host.launch_reservations[0]) == 1
    assert host.launch_reservations[0][0]["phase"] == "launch_pending"
    assert "pid" not in host.launch_reservations[0][0]


def test_control_07_postlaunch_failure_owned_rollback(rig, monkeypatch):
    _, sup, host = rig
    real_replace = state.os.replace
    writes = []
    def fail_final(source, dest):
        if str(dest).endswith("public-wt1-backend.json"):
            value = json.loads(Path(source).read_text())
            writes.append(value["phase"])
            if value["phase"] == "running":
                raise PermissionError("final registration denied")
        return real_replace(source, dest)
    with monkeypatch.context() as patch:
        patch.setattr(state.os, "replace", fail_final)
        with pytest.raises(PermissionError, match="final registration denied"):
            sup.start_backend(1)
    assert writes[:3] == ["launch_pending", "launch_pending", "running"]
    assert host.handles[0].terminations == 1 and host.handles[0].waits == [5]
    assert not sup.inventory.process_path("backend", 1).exists() and not host.signals
    sup.start_backend(1)
    assert sup.process_state("backend", 1) == "running"
    # Persistent disk failure after Popen must not disable exact-owned cleanup.
    attempts = []
    def fail_after_first(source, dest):
        if str(dest).endswith("public-wt2-backend.json"):
            attempts.append(json.loads(Path(source).read_text())["phase"])
            if len(attempts) >= 2:
                raise PermissionError("persistent registration failure")
        return real_replace(source, dest)
    with monkeypatch.context() as patch:
        patch.setattr(state.os, "replace", fail_after_first)
        with pytest.raises(PermissionError, match="persistent registration failure"):
            sup.start_backend(2)
    assert host.handles[-1].terminations == 1 and host.handles[-1].waits == [5]
    assert not sup.inventory.process_path("backend", 2).exists()
    assert len(attempts) >= 3
    # An unavailable census still allows valid exact wrapper cleanup, but cannot
    # certify its descendants absent or clear the durable reservation.
    census_writes = []
    def fail_census_registration(source, dest):
        if str(dest).endswith("public-wt3-backend.json"):
            census_writes.append(json.loads(Path(source).read_text())["phase"])
            if len(census_writes) >= 2:
                host.census_denied = True  # Coherent creation capture precedes this post-Popen write.
                raise PermissionError("persistent census-case write failure")
        return real_replace(source, dest)
    with monkeypatch.context() as patch:
        patch.setattr(state.os, "replace", fail_census_registration)
        with pytest.raises(SlotError, match="persistent census-case write failure.*residual retained.*census unavailable"):
            sup.start_backend(3)
    assert host.handles[-1].terminations == 1 and host.handles[-1].waits == [5]
    assert sup.inventory.process_path("backend", 3).exists()
    before = len(host.launches)
    with pytest.raises(SlotError):
        sup.start_backend(3)
    assert len(host.launches) == before and not host.signals
    host.census_denied = False; sup.stop_backend(3)
    # Identity unavailable cannot authorize even a guessed replacement PID.
    host.denied_pids.add(host.next_pid)
    with pytest.raises(SlotError, match="identity unavailable.*residual retained"):
        sup.start_backend(2)
    assert host.handles[-1].terminations == 0 and host.handles[-1].waits == []
    assert read_json(sup.inventory.process_path("backend", 2))["phase"] == "uncertain_residual"
    host.denied_pids.clear(); host.remove(host.handles[-1].pid); sup.stop_backend(2)
    # A reaped creation handle cannot establish ownership of a reused PID.
    def reap_and_reuse(handle):
        host.after_poll = None
        host.remove(handle.pid); handle.returncode = 0
        host.add(handle.pid, "unrelated replacement after reap", signature="Sun Oct 11 01:00:00 2026 unrelated replacement after reap")
    host.after_poll = reap_and_reuse
    before_signals = list(host.signals)
    with pytest.raises(SlotError, match="identity unavailable.*residual retained.*identity unavailable/mismatch"):
        sup.start_backend(2)
    handle = host.handles[-1]
    assert handle.terminations == 0 and handle.waits == [] and host.signals == before_signals
    assert host.rows[handle.pid][1] == "unrelated replacement after reap"
    assert sup.inventory.process_path("backend", 2).exists()


def test_control_08_pending_timeout_retains_capacity(rig):
    _, sup, host = rig
    host.no_open = True; host.retain_on_terminate = True
    with pytest.raises(SlotError, match="residual retained"):
        sup.start_backend(1)
    path = sup.inventory.process_path("backend", 1)
    assert read_json(path)["phase"] == "uncertain_residual"
    count = len(host.launches); host.clock += 1000000
    with pytest.raises(SlotError):
        sup.start_backend(1)
    assert len(host.launches) == count and 1 in sup.capacity_census()["reserved_physical_slots"]
    host.remove(host.handles[0].pid); sup.stop_backend(1)
    host.no_open = False; host.retain_on_terminate = False
    sup.start_backend(1)
    assert sup.process_state("backend", 1) == "running"
    # Interrupted pre-Popen reservation has no fabricated PID and no age-based escape.
    interrupted = sup.inventory.process_path("backend", 2)
    atomic_json(interrupted, dict(schema_version=1, process_schema_version=2, phase="launch_pending",
                                 repo_role="public", slot=2, kind="backend", started_at="1900-01-01T00:00:00Z"))
    count = len(host.launches)
    with pytest.raises(SlotError):
        sup.start_backend(2)
    assert len(host.launches) == count and 2 in sup.capacity_census()["reserved_physical_slots"]
    sup.stop_backend(2)
    assert not interrupted.exists()
    proxy_pending = sup.inventory.process_path("proxy", 2)
    atomic_json(proxy_pending, dict(schema_version=1, process_schema_version=2, phase="launch_pending",
                                   repo_role="public", slot=2, kind="proxy"))
    host.add(813208, " ".join(sup.proxy_command(2)))
    original = proxy_pending.read_bytes(); before_signals = list(host.signals)
    with pytest.raises(SlotError, match="fixed-inventory wrapper remains"):
        sup.stop_proxy(2)
    assert proxy_pending.read_bytes() == original and host.signals == before_signals
    host.remove(813208); sup.stop_proxy(2)
    assert not proxy_pending.exists()


def test_control_09_populated_capacity_conflict_and_third(host, downstream_repo, monkeypatch):
    down, public, _, _ = downstream_repo
    monkeypatch.delenv("LEAN_SLOT_SKIP_SUPERVISOR", raising=False)
    # An existing-family override changes only dependency ref/input location.
    # Both defaults and overrides describe the same populated physical domain.
    override = down.inventory.repo_root / "config" / "lean-slots.override.json"
    raw = json.loads(down.inventory.source.read_text())
    raw["paired_dependency"]["base_ref"] = "an-independent-dependency-input"
    override.write_text(json.dumps(raw))
    a, b = Supervisor(public.inventory), Supervisor(Inventory.load(override))
    family, errors = b._role_inventories(retain_aliases=True)
    assert not errors and {str(inv.source) for inv in family if inv.repo_role == "downstream"} == {str(override), str(down.inventory.source)}
    original_proxy = Supervisor(down.inventory)
    wrapper = original_proxy.proxy_command(3)
    host.add(819309, " ".join(wrapper))  # Older input filename, no PID record or listener.
    with pytest.raises(SlotError, match="fixed-inventory wrapper remains"):
        b.stop_proxy(3)
    assert 819309 in host.rows and not host.signals and not host.launches
    host.remove(819309); b.stop_proxy(3)
    assert not b.inventory.process_path("proxy", 3).exists()
    host.add(810109, " ".join(a.backend_command(1)), port=int(a.inventory.slot(1)["backend_port"]))
    owned(b, host, "backend", 2, 810209)
    census = a.capacity_census()
    assert census["complete"] and census["reserved_physical_slots"] == [1, 2]
    assert census["owners"] == {1: ["public"], 2: ["downstream"], 3: []}
    assert census["confirmed_services"] == 1
    assert b.capacity_census()["owners"] == census["owners"]
    before = (list(host.launches), list(host.signals))
    for mutation in ("server", "project", "endpoint"):
        conflicting = json.loads(override.read_text())
        if mutation == "server":
            conflicting["server"]["command"] = ["conflicting-server-mapping"]
        elif mutation == "project":
            conflicting["slots"]["2"]["worktree"] = "../different-physical-project"
        else:
            conflicting["slots"]["2"]["backend_port"] += 1000
        override.write_text(json.dumps(conflicting))
        conflict = a.capacity_census()
        assert not conflict["complete"] and "conflicting inventory domains" in " ".join(conflict["errors"])
        with pytest.raises(SlotError):
            a.start_backend(3)
        assert (host.launches, host.signals) == before
        override.write_text(json.dumps(raw))
    a.start_backend(3)
    assert a.capacity_census()["reserved_physical_slots"] == [1, 2, 3] and len(host.launches) == 1
    with pytest.raises(SlotError):
        b.start_backend(1)
    assert len(host.launches) == 1
    host.add(810309, " ".join(b.backend_command(1)), port=int(b.inventory.slot(1)["backend_port"]))
    assert a.capacity_census()["conflicts"] == [1]


def test_control_10_incomplete_census_blocks(rig):
    _, sup, host = rig
    host.add(810110, "lean-lsp-mcp --lean-project-path /unresolved/foreign/lean")
    census = sup.capacity_census()
    assert not census["complete"] and "unmapped" in " ".join(census["errors"])
    with pytest.raises(SlotError):
        sup.start_backend(3)
    assert not host.launches
    host.remove(810110); host.census_denied = True
    assert sup.capacity_census()["reserved_physical_slots"] == [1, 2, 3]
    with pytest.raises(SlotError):
        sup.start_backend(3)
    assert not host.launches
    host.census_denied = False; sup.start_backend(3)
    assert sup.process_state("backend", 3) == "running"


def test_control_11_tool_borrow_and_cache_hit(host, downstream_repo, monkeypatch):
    down, public, _, _ = downstream_repo
    monkeypatch.delenv("LEAN_SLOT_SKIP_SUPERVISOR", raising=False)
    sup, counterpart = Supervisor(public.inventory), Supervisor(down.inventory)
    owned(sup, host, "proxy", 1, 810111)
    requests = []
    class HTTP:
        def __init__(self, *args, **kwargs):
            self.payload = None
        def request(self, method, path, body=None, headers=None):
            self.payload = json.loads(body)
            requests.append(self.payload["method"])
        def getresponse(self):
            payload = {"result": {"tools": [{"name": "lean_diagnostic_messages"}]}} if self.payload["method"] == "tools/list" else {"result": {}}
            return SimpleNamespace(status=200, read=lambda: json.dumps(payload).encode(), getheaders=lambda: [("Mcp-Session-Id", "isolated-session")])
        def close(self):
            pass
    monkeypatch.setattr(lifecycle.http.client, "HTTPConnection", HTTP)
    assert sup._harvest_tool_list_unlocked() is True
    assert requests == ["initialize", "notifications/initialized", "tools/list"]
    assert sup.process_state("backend", 1) == "down" and len(host.launches) == 1
    launches = len(host.launches); signals = list(host.signals)
    assert sup._harvest_tool_list_unlocked() is False
    assert len(host.launches) == launches and host.signals == signals
    state.tool_cache_path(sup.inventory.state_root).unlink()
    # Populated other-role occupancy prevents bypassing admission during a borrow.
    for number in (1, 2, 3):
        owned(counterpart, host, "backend", number, 812110 + number)
    with pytest.raises(SlotError, match="cannot borrow"):
        sup._harvest_tool_list_unlocked()
    assert len(host.launches) == launches and not state.tool_cache_path(sup.inventory.state_root).exists()
    for number in (1, 2, 3):
        counterpart.stop_backend(number)
    host.denied_ports.add(29101)
    with pytest.raises(SlotError, match="cannot borrow"):
        sup._harvest_tool_list_unlocked()
    assert len(host.launches) == launches and not state.tool_cache_path(sup.inventory.state_root).exists()
    host.denied_ports.clear()
    class FailCleanupHTTP(HTTP):
        def getresponse(self):
            response = super().getresponse()
            if self.payload["method"] == "tools/list":
                host.denied_pids.add(host.handles[-1].pid)
            return response
    monkeypatch.setattr(lifecycle.http.client, "HTTPConnection", FailCleanupHTTP)
    with pytest.raises(SlotError, match="registration retained"):
        sup._harvest_tool_list_unlocked()
    assert sup.inventory.process_path("backend", 1).exists()
    assert 1 in sup.capacity_census()["reserved_physical_slots"]
    assert not state.tool_cache_path(sup.inventory.state_root).exists()


def test_control_12_global_start_rollback(rig, monkeypatch):
    _, sup, host = rig
    sup.inventory.raw["server"]["backend_policy"] = "leased"
    sup._write_tool_cache([{"name": "lean_diagnostic_messages"}])
    real_popen = host.popen
    def fail_second(argv, **kwargs):
        if argv[-1] == "2":
            raise PermissionError("second front door launch denied")
        return real_popen(argv, **kwargs)
    monkeypatch.setattr(subprocess, "Popen", fail_second)
    with pytest.raises(SlotError, match="second front door launch denied"):
        sup.start()
    assert not sup.inventory.process_path("proxy", 1).exists()
    assert read_json(sup.inventory.process_path("proxy", 2))["phase"] == "uncertain_residual"
    assert host.signals == [(host.handles[0].pid, signal.SIGTERM)]
    monkeypatch.setattr(subprocess, "Popen", host.popen)
    sup.stop_proxy(2)
    result = sup.start()
    assert all(item["proxy_state"] == "running" for item in result["slots"])
    sup.stop()
    monkeypatch.setattr(subprocess, "Popen", fail_second)
    host.after_signal = lambda pid: host.denied_pids.add(pid)
    with pytest.raises(SlotError, match="global startup failed.*second front door launch denied.*rollback residuals"):
        sup.start()
    assert sup.inventory.process_path("proxy", 1).exists()
    assert sup.inventory.process_path("proxy", 2).exists()


def test_control_13_owner_capture_reclaim_and_session(rig, monkeypatch):
    ctl, _, host = rig
    pid = os.getpid(); host.denied_pids.add(pid)
    with pytest.raises(SlotError, match="identity unavailable"):
        ctl.acquire(1, client="codex", base_ref="main")
    assert ctl.inventory.lease(1, required=False) is None
    host.denied_pids.clear(); ctl.acquire(1, client="codex", base_ref="main")
    lease = ctl.inventory.lease(1); lease.update(owner_pid=810113, owner_signature="old")
    ctl.inventory.save_lease(1, lease); original = ctl.inventory.lease_path(1).read_bytes()
    host.denied_pids.add(810113)
    with pytest.raises(SlotError, match="not confirmed absent"):
        ctl.reclaim(1)
    assert ctl.inventory.lease_path(1).read_bytes() == original
    host.denied_pids.clear(); ctl.reclaim(1)
    assert ctl.inventory.lease(1, required=False) is None
    # Process owner evidence also gates real dispatch; a false read cannot authorize it.
    from scripts.lean_slots.proxy import LeaseGate
    ctl.build(); ctl.acquire(2, client="codex", base_ref="main")
    live = Supervisor(ctl.inventory); owned(live, host, "proxy", 2, 812213)
    ctl.prepare(2)
    body = json.dumps({"jsonrpc": "2.0", "id": 1, "method": "tools/call", "params": {"name": "lean_goal", "arguments": {}}}).encode()
    gate = LeaseGate(ctl.inventory, 2); gate.authorize("codex", None, body)
    before = ctl.inventory.lease_path(2).read_bytes(); host.denied_pids.add(pid)
    with pytest.raises(SlotError, match="owner"):
        gate.authorize("codex", None, body)
    assert ctl.inventory.lease_path(2).read_bytes() == before
    host.denied_pids.clear(); ctl.release(2)
    monkeypatch.delenv("LEAN_SLOT_OWNER_PID"); monkeypatch.setenv("LEAN_SLOT_OWNER_SESSION", "retained-session")
    ctl.acquire(1, client="codex", base_ref="main")
    with pytest.raises(SlotError, match="confirm-owner-gone"):
        ctl.reclaim(1)
    ctl.reclaim(1, confirm_owner_gone=True)
    assert ctl.inventory.lease(1, required=False) is None


def test_control_14_free_lease_residual_resources(rig, monkeypatch, capsys):
    ctl, sup, host = rig
    ctl.inventory.raw["server"]["backend_policy"] = "leased"
    ctl.acquire(1, client="codex", base_ref="main")
    path = owned(sup, host, "backend", 1, 810114)
    host.denied_pids.add(810114)
    original = path.read_bytes()
    ctl.release(1)
    assert ctl.inventory.lease(1, required=False) is None and path.read_bytes() == original
    status = sup.status()
    assert status["slots"][0]["lease_state"] == "FREE" and status["slots"][0]["backend_state"] == "unavailable"
    assert 1 in status["reserved_physical_slots"]
    ctl_status = ctl.status()
    assert ctl_status["slots"][0]["lease"] is None and ctl_status["slots"][0]["resource_reserved"]
    assert ctl_status["slots"][0]["resources"]["backend"]["process_observation"] == "unavailable"
    cli._status_human(ctl_status)
    captured = capsys.readouterr()
    human = captured.out
    assert "reserved" in captured.err
    assert "wt1: FREE" in human and "backend=unavailable reserved=True" in human
    with pytest.raises(SlotError):
        sup.start_backend(1)
    assert not host.launches
    host.denied_pids.clear(); sup.stop_backend(1)
    sup.start_backend(1)
    assert sup.process_state("backend", 1) == "running"


def test_control_15_cli_rejects_ignored_slots_before_constructor(rig, capsys):
    ctl, _, host = rig
    # Invalid inventory makes ordering independently observable: slot error must win.
    for action in ("start", "stop", "status"):
        assert cli.main(["--inventory", "/nonexistent/isolated.json", "supervisor", action, "--slot", "2"]) == 2
        assert "are global" in capsys.readouterr().err
    assert cli.main(["--inventory", "/nonexistent/isolated.json", "supervisor", "probe"]) == 2
    assert "probe requires --slot" in capsys.readouterr().err
    assert not host.launches and not host.signals
    assert cli.main(["--inventory", str(ctl.inventory.source), "supervisor", "status", "--json"]) == 0
    result = json.loads(capsys.readouterr().out)
    assert len(result["slots"]) == 3 and result["capacity_complete"]
    assert cli.main(["--inventory", str(ctl.inventory.source), "supervisor", "probe", "--slot", "2"]) == 2
    assert "wt2" in capsys.readouterr().err  # Accepted targeted verb reached actual health check.


def test_control_16_literal_sha_vs_branch_absorb(rig, monkeypatch):
    ctl, sup, host = rig
    ctl.build()
    owned(sup, host, "proxy", 1, 810116)
    literal = run(ctl.repo, "git", "rev-parse", "main")
    ctl.acquire(1, client="codex", base_ref=literal); ctl.prepare(1)
    first = ctl.inventory.worktree(1)
    (first / "literal-change.txt").write_text("preserved literal task\n")
    run(first, "git", "add", "literal-change.txt"); run(first, "git", "commit", "-m", "literal task")
    ctl.ready(1)
    with pytest.raises(SlotError, match="primary checkout is on"):
        ctl.absorb(1)
    assert ctl.inventory.lease(1)["state"] == "READY_TO_ABSORB"
    assert ctl.inventory.lease(1)["base_ref"] == literal and (first / "literal-change.txt").exists()
    # A separate no-change literal task supports ordinary release without retargeting.
    ctl.acquire(2, client="codex", base_ref=literal); ctl.release(2)
    assert ctl.inventory.lease(2, required=False) is None
    owned(sup, host, "proxy", 3, 810316)
    ctl.acquire(3, client="codex", base_ref="main"); ctl.prepare(3)
    third = ctl.inventory.worktree(3)
    (third / "branch-change.txt").write_text("accepted branch task\n")
    run(third, "git", "add", "branch-change.txt"); run(third, "git", "commit", "-m", "branch task")
    ctl.ready(3); ctl.absorb(3)
    assert ctl.inventory.lease(3, required=False) is None and sup.process_state("backend", 3) == "running"
    assert (ctl.repo / "branch-change.txt").exists()


def test_control_17_truthful_status_doctor_and_health(rig, monkeypatch, capsys):
    ctl, sup, host = rig
    ctl.build(); ctl.render_config(scope="both", force=True)
    for n in (1, 2, 3):
        owned(sup, host, "proxy", n, 810117 + n)
        owned(sup, host, "backend", n, 810217 + n)
    status = sup.status()
    assert status["capacity_complete"] and status["global_running_backends"] == 3
    resource = status["slots"][0]["resources"]["backend"]
    assert resource["record_phase"] == "running" and resource["identity_authority"] == "managed"
    assert resource["process_observation"] == resource["endpoint_observation"] == "present"
    assert resource["errors"] == []
    record = sup.inventory.process_path("backend", 1); original = record.read_bytes()
    record.write_text("{")
    malformed = sup.status()["slots"][0]["resources"]["backend"]
    assert malformed["state"] == malformed["record_phase"] == malformed["identity_authority"] == "unavailable"
    assert malformed["errors"] and record.read_text() == "{"
    record.write_bytes(original)
    initial_launches, initial_signals = list(host.launches), list(host.signals)
    # Native stat/open denial and malformed PID reach actual status/doctor,
    # JSON and human CLI consumers without replacing their internal verdicts.
    for failure in ("exists-denied", "read-denied", "invalid-string-pid", "invalid-object-pid"):
        malformed_record = json.loads(original)
        if failure.startswith("invalid"):
            malformed_record["pid"] = "not-a-pid" if failure == "invalid-string-pid" else {"untrusted": 810218}
            record.write_text(json.dumps(malformed_record))
        with monkeypatch.context() as patch:
            if failure == "exists-denied":
                actual_stat = os.stat
                def denied_stat(path, *args, **kwargs):
                    if Path(path) == record:
                        raise PermissionError(errno.EPERM, "process record stat denied")
                    return actual_stat(path, *args, **kwargs)
                patch.setattr(os, "stat", denied_stat)
            elif failure == "read-denied":
                actual_open = Path.open
                def denied_open(path, *args, **kwargs):
                    if path == record:
                        raise PermissionError(errno.EPERM, "process record read denied")
                    return actual_open(path, *args, **kwargs)
                patch.setattr(Path, "open", denied_open)
            assert sup.process_state("backend", 1) == "unavailable"
            status = ctl.status()
            resource = status["slots"][0]["resources"]["backend"]
            assert resource["state"] == resource["identity_authority"] == "unavailable"
            assert resource["process_observation"] == "unavailable" and resource["errors"]
            assert status["slots"][0]["resource_reserved"] and not status["capacity_complete"]
            assert 1 in status["reserved_physical_slots"]
            if failure.startswith("invalid"):
                assert resource["recorded_pid"] == malformed_record["pid"]
            else:
                assert resource["record_phase"] == "unavailable"
            checks = {item["name"]: item for item in ctl.doctor()["checks"]}
            assert not checks["heavy_backend_limit"]["ok"] and not checks["wt1.endpoint"]["ok"]
            capsys.readouterr()
            assert cli.main(["--inventory", str(ctl.inventory.source), "status", "--json"]) == 0
            actual_json = json.loads(capsys.readouterr().out)
            assert actual_json["slots"][0]["resources"]["backend"]["state"] == "unavailable"
            assert cli.main(["--inventory", str(ctl.inventory.source), "status"]) == 0
            human = capsys.readouterr().out
            assert "FREE" in human and "backend=unavailable reserved=True" in human and "identity=unavailable" in human
            assert host.launches == initial_launches and host.signals == initial_signals
        if failure.startswith("invalid"):
            assert json.loads(record.read_text()) == malformed_record
        else:
            assert record.read_bytes() == original
        record.write_bytes(original)
    checks = {item["name"]: item for item in ctl.doctor()["checks"]}
    assert checks["heavy_backend_limit"]["ok"] and all(checks[f"wt{n}.endpoint"]["ok"] for n in (1, 2, 3))
    host.denied_ports.add(29101); host.denied_pids.add(810218)
    status = sup.status()
    assert status["slots"][0]["backend_state"] == "unavailable" and not status["capacity_complete"]
    resource = status["slots"][0]["resources"]["backend"]
    assert resource["record_phase"] == "running" and resource["identity_authority"] == "managed"
    assert resource["process_observation"] == resource["endpoint_observation"] == "unavailable"
    assert "denied" in " ".join(resource["errors"])
    checks = {item["name"]: item for item in ctl.doctor()["checks"]}
    assert not checks["heavy_backend_limit"]["ok"] and not checks["wt1.endpoint"]["ok"]
    with pytest.raises(SlotError, match="diagnose ownership"):
        sup.assert_healthy(1)


def captured(call):
    """Make unexpected native exceptions explicit data for independent assertions."""
    try:
        return call(), None
    except Exception as exc:
        return None, exc


def forbidden_counts(host):
    return (len(host.launches), len(host.signals),
            len([args for args in host.command_calls if "reset" in args]))


def require_witnesses(values):
    """Independent consumer contract, with explicit unknown/null witnesses."""
    import datetime
    assert values
    mandatory = {"state", "target", "operation", "observed_at", "returncode",
                 "error_class", "errno", "observed_identity", "diagnostic_text"}
    for value in values:
        assert mandatory <= value.keys()
        assert value["target"] and value["operation"]
        assert datetime.datetime.fromisoformat(value["observed_at"].replace("Z", "+00:00")).utcoffset() == datetime.timedelta(0)
        assert value["returncode"] is None or type(value["returncode"]) is int
        assert value["error_class"] is None or isinstance(value["error_class"], str)
        assert value["errno"] is None or type(value["errno"]) is int
        assert len(value["diagnostic_text"]) <= 2048


@pytest.mark.parametrize("exit_name", ["release", "reclaim", "absorb"])
@pytest.mark.parametrize("corruption", ["string-pid", "object-pid", "utf8", "descendant", "stat-denied", "read-denied", "healthy"])
def test_six_r1_actual_completed_exit_retains_corrupt_resources(rig, monkeypatch, capsys, exit_name, corruption):
    ctl, _, host = rig
    config = json.loads(ctl.inventory.source.read_text())
    config["server"]["backend_policy"] = "leased"
    ctl.inventory.source.write_text(json.dumps(config))
    run(ctl.repo, "git", "add", "config/lean-slots.public.json")
    run(ctl.repo, "git", "commit", "-m", "leased policy fixture")
    ctl = Controller(Inventory.load(ctl.inventory.source)); sup = Supervisor(ctl.inventory)
    ctl.build()
    if exit_name == "reclaim":
        host.add(820101, "synthetic stale lease owner")
        monkeypatch.setenv("LEAN_SLOT_OWNER_PID", "820101")
    ctl.acquire(1, client="codex", base_ref="main")
    if exit_name == "reclaim":
        host.remove(820101)
    if exit_name == "absorb":
        owned(sup, host, "proxy", 1, 820201)
        ctl.prepare(1)
        worktree = ctl.inventory.worktree(1)
        (worktree / "completed-exit.txt").write_text("integrated before resource diagnosis\n")
        run(worktree, "git", "add", "completed-exit.txt")
        run(worktree, "git", "commit", "-m", "completed exit fixture")
        ctl.ready(1)
    else:
        owned(sup, host, "backend", 1, 820301)
    record = ctl.inventory.process_path("backend", 1); lease_path = ctl.inventory.lease_path(1)
    real_unlink, real_stat, real_open = Path.unlink, os.stat, Path.open
    injected = {"done": False}
    def unlink(path, *args, **kwargs):
        result = real_unlink(path, *args, **kwargs)
        if path == lease_path:
            data = json.loads(record.read_text())
            if corruption == "string-pid": data["pid"] = "not-a-pid"
            if corruption == "object-pid": data["pid"] = {"unknown": 17}
            if corruption == "descendant": data["descendants"] = [{"pid": 820401}]
            record.write_bytes(b"\xff\xfe" if corruption == "utf8" else json.dumps(data).encode())
            injected.update(done=True, bytes=record.read_bytes(), before=forbidden_counts(host), pid=data.get("pid"))
        return result
    def stat_seam(path, *args, **kwargs):
        if injected["done"] and corruption == "stat-denied" and isinstance(path, (str, bytes, os.PathLike)) and Path(path) == record:
            raise PermissionError(errno.EPERM, "completed resource record stat denied")
        return real_stat(path, *args, **kwargs)
    def open_seam(path, *args, **kwargs):
        if injected["done"] and corruption == "read-denied" and path == record:
            raise PermissionError(errno.EACCES, "completed resource record read denied")
        return real_open(path, *args, **kwargs)
    with monkeypatch.context() as patch:
        patch.setattr(Path, "unlink", unlink); patch.setattr(os, "stat", stat_seam); patch.setattr(Path, "open", open_seam)
        capsys.readouterr()
        result, error = captured(lambda: getattr(ctl, exit_name)(1))
        warning = capsys.readouterr().err
        assert error is None, repr(error)
        assert injected["done"] and not lease_path.exists()
        if corruption == "healthy":
            assert not warning
        else:
            assert "released" in warning and "resource remains reserved" in warning and "observations=" in warning
            witness = json.loads(warning.split("observations=", 1)[1].strip())
            require_witnesses(witness)
        status, error = captured(ctl.status)
        assert error is None, repr(error)
        assert status["slots"][0]["lease"] is None
        if corruption == "healthy":
            assert status["slots"][0]["resources"]["backend"]["state"] == "down"
            assert 1 not in status["reserved_physical_slots"] and status["capacity_complete"]
            assert len(host.launches) == injected["before"][0]
            assert len(host.signals) == injected["before"][1] + 1
            assert host.signals[-1] == (injected["pid"], signal.SIGTERM)
            assert forbidden_counts(host)[2] == injected["before"][2]
        else:
            assert status["slots"][0]["resources"]["backend"]["state"] == "unavailable"
            assert 1 in status["reserved_physical_slots"] and not status["capacity_complete"]
            assert forbidden_counts(host) == injected["before"]
        if exit_name == "absorb":
            assert result["integrated_head"] == run(ctl.repo, "git", "rev-parse", "HEAD")
            assert result["epoch"] and (ctl.repo / "completed-exit.txt").read_text() == "integrated before resource diagnosis\n"
    if corruption == "healthy":
        assert not record.exists()
    else:
        assert record.read_bytes() == injected["bytes"]


BAD_DESCENDANTS = [
    [{}], [{"pid": 820202}], [{"pid": "not-a-pid", "signature": "untrusted"}],
    [{"pid": {"bad": 1}, "signature": "untrusted"}],
    [{"pid": 820202, "signature": 17}], [{"pid": 820202, "signature": ""}],
    {"pid": 820202, "signature": "untrusted"},
]


@pytest.mark.parametrize("bad", BAD_DESCENDANTS)
@pytest.mark.parametrize("root_present", [True, False])
def test_six_r2_corrupt_descendants_all_consumers(rig, monkeypatch, capsys, bad, root_present):
    ctl, sup, host = rig; ctl.build(); ctl.render_config(scope="both", force=True)
    for n in (1, 2, 3):
        owned(sup, host, "proxy", n, 821100+n); owned(sup, host, "backend", n, 821200+n)
    record = sup.inventory.process_path("backend", 1)
    healthy = record.read_bytes(); value = json.loads(healthy); value["descendants"] = bad
    record.write_text(json.dumps(value)); corrupt = record.read_bytes()
    if not root_present: host.remove(821201)
    before = forbidden_counts(host)
    for call in (sup.status, ctl.status, ctl.doctor):
        result, error = captured(call); assert error is None, repr(error)
        if "checks" in result:
            checks = {x["name"]: x for x in result["checks"]}
            assert not checks["heavy_backend_limit"]["ok"] and not checks["wt1.endpoint"]["ok"]
        else:
            resource = result["slots"][0]["resources"]["backend"]
            assert resource["state"] == resource["record_phase"] == resource["identity_authority"] == "unavailable"
            assert not result["capacity_complete"] and 1 in result["reserved_physical_slots"]
            require_witnesses(resource["observations"])
    for args in (["status", "--json"], ["status"]):
        capsys.readouterr(); result, error = captured(lambda: cli.main(["--inventory", str(ctl.inventory.source)] + args))
        output = capsys.readouterr(); assert error is None and result == 0
        if "--json" in args: assert json.loads(output.out)["slots"][0]["resources"]["backend"]["state"] == "unavailable"
        else: assert "backend=unavailable reserved=True" in output.out and "identity=unavailable" in output.out
    _, error = captured(lambda: sup.stop_backend(1)); assert isinstance(error, SlotError)
    ctl.acquire(1, client="codex", base_ref="main")
    cache = ctl.inventory.worktree(1) / "lean/.lake/preserve-r2"
    cache.parent.mkdir(parents=True, exist_ok=True); cache.write_text("untouched")
    _, error = captured(lambda: ctl.prepare(1)); assert isinstance(error, SlotError)
    assert cache.exists() and cache.read_text() == "untouched"
    assert forbidden_counts(host) == before and record.read_bytes() == corrupt
    record.write_bytes(healthy)
    assert sup.process_state("backend", 1) == ("running" if root_present else "down")
    if not root_present: sup.stop_backend(1); assert not record.exists()


@pytest.mark.parametrize("bad", [BAD_DESCENDANTS[0], BAD_DESCENDANTS[4], BAD_DESCENDANTS[6]])
def test_six_r2_paired_corruption_refuses_before_yield(host, downstream_repo, monkeypatch, bad):
    down, public, _, _ = downstream_repo; monkeypatch.delenv("LEAN_SLOT_SKIP_SUPERVISOR", raising=False)
    target, prior = Supervisor(down.inventory), Supervisor(public.inventory)
    owned(target, host, "proxy", 1, 822101)
    record = owned(prior, host, "backend", 1, 822201); value = json.loads(record.read_text())
    value["descendants"] = bad; record.write_text(json.dumps(value)); original = record.read_bytes()
    before = forbidden_counts(host); effects = []
    def transition():
        with target.activating_from(1, prior): effects.append("unsafe-yield")
    _, error = captured(transition)
    assert isinstance(error, SlotError) and not effects
    assert forbidden_counts(host) == before and record.read_bytes() == original


def test_six_r2_valid_legacy_and_pending_record_shapes(rig):
    _, sup, host = rig
    path = owned(sup, host, "backend", 1, 823101); data = json.loads(path.read_text())
    data.pop("phase"); data.pop("process_schema_version"); path.write_text(json.dumps(data))
    assert sup.process_state("backend", 1) == "running"
    sup.stop_backend(1); assert not path.exists()
    pending = dict(schema_version=1, process_schema_version=2, phase="launch_pending",
                   repo_role="public", kind="backend", slot=1)
    atomic_json(path, pending)
    assert sup.process_state("backend", 1) == "uncertain_residual" and 1 in sup.capacity_census()["reserved_physical_slots"]
    sup.stop_backend(1); assert not path.exists()


@pytest.mark.parametrize("child_state", ["present", "denied", "timeout", "mismatch"])
def test_six_r3_reparented_generic_child_reserves_original_number(host, downstream_repo, monkeypatch, child_state):
    down, public, _, _ = downstream_repo; monkeypatch.delenv("LEAN_SLOT_SKIP_SUPERVISOR", raising=False)
    sup, other = Supervisor(public.inventory), Supervisor(down.inventory)
    record = owned(sup, host, "backend", 1, 824101)
    signature = host.add(824201, "generic auxiliary child", ppid=os.getpid())
    data = json.loads(record.read_text()); data["descendants"] = [{"pid": 824201, "signature": signature}]
    record.write_text(json.dumps(data)); original = record.read_bytes(); host.remove(824101)
    owned(other, host, "backend", 2, 824302); owned(other, host, "backend", 3, 824303)
    if child_state == "denied": host.denied_pids.add(824201)
    if child_state == "timeout": host.selected_results[824201] = subprocess.TimeoutExpired(["ps"], 2)
    if child_state == "mismatch": host.add(824201, "unrelated replacement", signature="Sun Oct 11 01:00:00 2026 unrelated replacement")
    before = forbidden_counts(host)
    # A supported equivalent dependency-input alias must not double count the role.
    alias = down.inventory.repo_root / "config/lean-slots.equivalent.json"
    alias_value = json.loads(down.inventory.source.read_text()); alias_value["paired_dependency"]["base_ref"] = "alternate-dependency-input"
    alias.write_text(json.dumps(alias_value))
    census = sup.capacity_census()
    assert census["reserved_physical_slots"] == [1, 2, 3] and census["owners"][1] == ["public"]
    assert census["owners"][2] == census["owners"][3] == ["downstream"]
    assert census["complete"] == (child_state == "present")
    status = public.status()
    assert status["slots"][0]["resource_reserved"]
    require_witnesses(status["capacity_observations"])
    for call in (lambda: sup.start_backend(2), lambda: sup.stop_backend(1)):
        _, error = captured(call); assert isinstance(error, SlotError)
    assert record.read_bytes() == original and forbidden_counts(host) == before
    checks = {x["name"]: x for x in public.doctor()["checks"]}
    assert checks["heavy_backend_limit"]["ok"] == (child_state == "present")
    assert not checks["wt1.endpoint"]["ok"]
    if child_state == "present":
        owned(other, host, "backend", 1, 824304)
        assert sup.capacity_census()["conflicts"] == [1]
        _, error = captured(lambda: sup.start_backend(1)); assert isinstance(error, SlotError)
        assert forbidden_counts(host) == before
        other.stop_backend(1)  # Positive cleanup of explicitly owned injected conflict only.
    host.denied_pids.clear(); host.selected_results.clear(); host.remove(824201)
    sup.stop_backend(1); assert not record.exists()
    census = sup.capacity_census()
    assert census["complete"] and census["reserved_physical_slots"] == [2, 3]
    sup.start_backend(1)
    assert len(host.launches) == before[0]+1 and sup.process_state("backend", 1) == "running"


def test_six_r4_actual_consumer_witnesses_and_bounded_diagnostics(rig, monkeypatch, capsys):
    ctl, sup, host = rig
    owned(sup, host, "backend", 1, 825101)
    positive = sup.status()["slots"][0]["resources"]["backend"]
    require_witnesses(positive["observations"])
    witness = next(x for x in positive["observations"] if x["operation"] == "ps-selected")
    assert witness["returncode"] == 0 and witness["observed_identity"] == host.rows[825101][2]
    assert witness["error_class"] is None and witness["errno"] is None
    original = host.rows[825101]
    host.add(825101, "known unrelated replacement", signature="Sun Oct 11 01:00:00 2026 known unrelated replacement")
    changed = sup.status()["slots"][0]["resources"]["backend"]
    require_witnesses(changed["observations"])
    witness = next(x for x in changed["observations"] if x["operation"] == "ps-selected")
    assert witness["state"] == "mismatch" and witness["observed_identity"] == host.rows[825101][2]
    host.rows[825101] = original
    scenarios = [
        ("permission", PermissionError(errno.EPERM, "x"*10000), "PermissionError", errno.EPERM, None),
        ("stderr", SimpleNamespace(returncode=2, stdout="", stderr="y"*10000), None, None, 2),
        ("timeout", subprocess.TimeoutExpired(["ps"], 2, stderr="z"*10000), "TimeoutExpired", None, None),
        ("garbage", SimpleNamespace(returncode=0, stdout="garbage", stderr=""), None, None, 0),
    ]
    for _, failure, kind, number, returncode in scenarios:
        host.selected_results[825101] = failure
        status = ctl.status(); resource = status["slots"][0]["resources"]["backend"]
        assert resource["state"] == "unavailable"
        require_witnesses(resource["observations"])
        witness = next(x for x in resource["observations"] if x["operation"] == "ps-selected")
        assert witness["target"] == "PID 825101" and witness["error_class"] == kind
        assert witness["errno"] == number and witness["returncode"] == returncode
        capsys.readouterr(); assert cli.main(["--inventory", str(ctl.inventory.source), "status"]) == 0
        human = capsys.readouterr().out
        assert "observed_at" in human and "diagnostic_text" in human and "PID 825101" in human
        for line in human.splitlines():
            if "observation=" in line: require_witnesses([json.loads(line.split("observation=", 1)[1])])
    host.selected_results.clear()
    host.port_errors[29101] = PermissionError(errno.EACCES, "p"*10000)
    status = sup.status(); require_witnesses(status["slots"][0]["resources"]["backend"]["observations"])
    socket_witness = next(x for x in status["slots"][0]["resources"]["backend"]["observations"] if x["operation"] == "connect")
    assert socket_witness["error_class"] == "PermissionError" and socket_witness["errno"] == errno.EACCES and socket_witness["returncode"] is None
    host.port_errors.clear(); host.census_result = PermissionError(errno.EPERM, "c"*10000)
    census = sup.capacity_census()
    require_witnesses(census["observations"])
    witness = next(x for x in census["observations"] if x["operation"] == "ps-census")
    assert witness["error_class"] == "PermissionError" and witness["errno"] == errno.EPERM and witness["returncode"] is None
    host.census_result = None; host.remove(825101)
    status = sup.status(); require_witnesses(status["slots"][0]["resources"]["backend"]["observations"])
    assert status["slots"][0]["backend_state"] == "down"


@pytest.mark.parametrize("bad", ["garbage", "Sun Oct 11 00:00:00 2026", "Sun Oct 11 00:00:00 2026 partial\nSun Oct 11 00:00:00 2026 another"])
def test_six_r5_garbage_success_cannot_acquire_or_dispatch(rig, monkeypatch, bad):
    ctl, sup, host = rig; pid = os.getpid()
    host.selected_results[pid] = SimpleNamespace(returncode=0, stdout=bad, stderr="")
    before = forbidden_counts(host)
    _, error = captured(lambda: ctl.acquire(1, client="codex", base_ref="main"))
    assert isinstance(error, SlotError) and ctl.inventory.lease(1, required=False) is None
    assert forbidden_counts(host) == before
    host.selected_results.clear(); ctl.build(); ctl.acquire(1, client="codex", base_ref="main")
    owned(sup, host, "proxy", 1, 826101); ctl.prepare(1)
    from scripts.lean_slots.proxy import LeaseGate
    body = json.dumps({"jsonrpc":"2.0","id":1,"method":"tools/call","params":{"name":"lean_goal","arguments":{}}}).encode()
    gate = LeaseGate(ctl.inventory, 1); gate.authorize("codex", None, body)
    host.selected_results[pid] = SimpleNamespace(returncode=0, stdout=bad, stderr="")
    before = forbidden_counts(host); lease = ctl.inventory.lease_path(1).read_bytes()
    _, error = captured(lambda: gate.authorize("codex", None, body))
    assert isinstance(error, SlotError) and ctl.inventory.lease_path(1).read_bytes() == lease
    assert forbidden_counts(host) == before


def test_six_r5_inconsistent_census_and_launch_success_refused(rig, monkeypatch):
    ctl, sup, host = rig
    original = host.rows[os.getpid()]
    host.selected_results[os.getpid()] = SimpleNamespace(returncode=0, stdout="Sun Oct 11 01:00:00 2026 contradictory owner", stderr="")
    _, error = captured(lambda: ctl.acquire(1, client="codex", base_ref="main"))
    assert isinstance(error, SlotError) and ctl.inventory.lease(1, required=False) is None
    host.selected_results.clear()
    actual = host.popen
    def malformed_launch(argv, **kwargs):
        result = actual(argv, **kwargs)
        host.selected_results[result.pid] = SimpleNamespace(returncode=0, stdout="garbage", stderr="")
        return result
    monkeypatch.setattr(subprocess, "Popen", malformed_launch)
    _, error = captured(lambda: sup.start_backend(1))
    assert isinstance(error, SlotError)
    record = read_json(sup.inventory.process_path("backend", 1))
    assert record["phase"] == "uncertain_residual"
    assert not host.signals and host.handles[-1].terminations == 0
    assert sup.process_state("backend", 1) != "running"
    assert 1 in sup.capacity_census()["reserved_physical_slots"]


@pytest.mark.parametrize("failure_errno", [errno.EPERM, errno.EACCES, errno.EIO])
@pytest.mark.parametrize("target_kind", ["record-stat", "registry-stat", "registry-scan", "config-scan", "workspace-scan", "repository-stat"])
def test_six_r6_native_fs_denial_never_false_absence(rig, monkeypatch, capsys, failure_errno, target_kind):
    ctl, sup, host = rig; ctl.build(); ctl.render_config(scope="both", force=True)
    record = owned(sup, host, "backend", 1, 827101)
    original = record.read_bytes()
    # Root no longer has a listener; only explicit record/native family evidence remains.
    host.remove(827101)
    owned(sup, host, "proxy", 1, 827201)
    for n in (2, 3): owned(sup, host, "backend", n, 827100+n)
    target = {"record-stat":record, "registry-stat":record.parent, "registry-scan":record.parent,
              "config-scan":ctl.inventory.source.parent, "workspace-scan":ctl.inventory.workspace_root,
              "repository-stat":ctl.inventory.repo_root}[target_kind]
    real_stat, real_scan = os.stat, os.scandir
    def stat_seam(path, *args, **kwargs):
        if target_kind.endswith("stat") and isinstance(path,(str,bytes,os.PathLike)) and Path(path) == target:
            raise OSError(failure_errno, "native stat denied")
        return real_stat(path,*args,**kwargs)
    def scan_seam(path):
        if target_kind.endswith("scan") and Path(path) == target:
            raise OSError(failure_errno, "native scandir denied")
        return real_scan(path)
    before = forbidden_counts(host)
    with monkeypatch.context() as patch:
        patch.setattr(os,"stat",stat_seam); patch.setattr(os,"scandir",scan_seam)
        status,error = captured(ctl.status)
        assert error is None, repr(error)
        assert not status["capacity_complete"] and 1 in status["reserved_physical_slots"]
        require_witnesses(status["capacity_observations"])
        assert any(x["state"]=="unavailable" and x["errno"]==failure_errno and x["target"]==str(target)
                   for x in status["capacity_observations"])
        doctor,error = captured(ctl.doctor); assert error is None,repr(error)
        assert not next(x for x in doctor["checks"] if x["name"]=="heavy_backend_limit")["ok"]
        _,error = captured(lambda:sup.start_backend(1)); assert isinstance(error,SlotError)
        _,error = captured(lambda:sup.stop_backend(1)); assert isinstance(error,SlotError)
        ctl.acquire(1,client="codex",base_ref="main")
        marker=ctl.inventory.worktree(1)/"lean/.lake/preserve-r6";marker.parent.mkdir(parents=True,exist_ok=True);marker.write_text("untouched")
        _,error=captured(lambda:ctl.prepare(1));assert isinstance(error,SlotError)
        assert marker.exists() and marker.read_text()=="untouched"
        assert forbidden_counts(host)==before
        capsys.readouterr();code,error=captured(lambda:cli.main(["--inventory",str(ctl.inventory.source),"status","--json"]))
        assert error is None and code==0
        assert not json.loads(capsys.readouterr().out)["capacity_complete"]
        capsys.readouterr();code,error=captured(lambda:cli.main(["--inventory",str(ctl.inventory.source),"status"]))
        assert error is None and code==0
        human=capsys.readouterr().out
        assert "capacity_complete=False" in human and "observation=" in human
    assert record.read_bytes()==original
    sup.stop_backend(1);assert not record.exists()
    sup.start_backend(1);assert sup.process_state("backend",1)=="running"


@pytest.mark.parametrize("census_mode", ["denied", "malformed", "duplicate", "no-observer"])
def test_six_r5_census_cannot_mint_creation_or_lease_identity(rig, monkeypatch, census_mode):
    ctl, sup, host = rig
    if census_mode == "denied":
        failure = PermissionError(errno.EPERM, "census unavailable")
    elif census_mode == "malformed":
        failure = SimpleNamespace(returncode=0, stdout="garbage\n", stderr="")
    elif census_mode == "duplicate":
        row = f"{os.getpid()} {os.getppid()} {host.rows[os.getpid()][2]}\n"
        failure = SimpleNamespace(returncode=0, stdout=row+row, stderr="")
    else:
        failure = SimpleNamespace(returncode=0, stdout="", stderr="")
    host.census_result = failure
    _, error = captured(lambda: ctl.acquire(1, client="codex", base_ref="main"))
    assert isinstance(error, SlotError) and ctl.inventory.lease(1, required=False) is None
    assert not host.launches and not host.signals
    host.census_result = None
    actual = host.popen
    def fail_after_popen(argv, **kwargs):
        process = actual(argv, **kwargs)
        host.census_result = failure
        return process
    monkeypatch.setattr(subprocess, "Popen", fail_after_popen)
    _, error = captured(lambda: sup.start_backend(1))
    assert isinstance(error, SlotError)
    assert host.handles[-1].terminations == 0 and host.handles[-1].waits == []
    assert read_json(sup.inventory.process_path("backend", 1))["phase"] == "uncertain_residual"
    assert not host.signals
    assert sup.capacity_census()["reserved_physical_slots"] == [1, 2, 3]


@pytest.mark.parametrize("target_kind", ["record-stat", "registry-scan", "config-scan"])
@pytest.mark.parametrize("failure_errno", [errno.EPERM, errno.EIO])
def test_six_r6_native_paired_denial_prevents_effect(host, downstream_repo, monkeypatch, target_kind, failure_errno):
    down, public, _, _ = downstream_repo
    monkeypatch.delenv("LEAN_SLOT_SKIP_SUPERVISOR", raising=False)
    target, prior = Supervisor(down.inventory), Supervisor(public.inventory)
    owned(target, host, "proxy", 1, 828101)
    record = owned(prior, host, "backend", 1, 828201); original = record.read_bytes(); host.remove(828201)
    for n in (2, 3): owned(prior, host, "backend", n, 828200+n)
    denied = {"record-stat":record, "registry-scan":record.parent, "config-scan":public.inventory.source.parent}[target_kind]
    actual_stat, actual_scan = os.stat, os.scandir
    def stat_seam(path,*args,**kwargs):
        if target_kind=="record-stat" and isinstance(path,(str,bytes,os.PathLike)) and Path(path)==denied:
            raise OSError(failure_errno,"paired native stat denied")
        return actual_stat(path,*args,**kwargs)
    def scan_seam(path):
        if target_kind.endswith("scan") and Path(path)==denied:
            raise OSError(failure_errno,"paired native scandir denied")
        return actual_scan(path)
    effects=[];before=forbidden_counts(host)
    def transition():
        with target.activating_from(1,prior):
            effects.append("forbidden cache/body effect")
    with monkeypatch.context() as patch:
        patch.setattr(os,"stat",stat_seam);patch.setattr(os,"scandir",scan_seam)
        _,error=captured(transition)
        assert isinstance(error,SlotError) and not effects
        assert forbidden_counts(host)==before
        assert not prior.capacity_census()["complete"]
    assert record.read_bytes()==original
    prior.stop_backend(1)
    with target.activating_from(1,prior):effects.append("safe body")
    assert effects==["safe body"] and target.process_state("backend",1)=="running"


def test_six_r6_lease_stat_denial_cannot_report_free(rig, monkeypatch):
    ctl, _, host = rig
    ctl.acquire(1,client="codex",base_ref="main"); path=ctl.inventory.lease_path(1); original=path.read_bytes()
    real=os.stat;before=forbidden_counts(host)
    def denied(path_arg,*args,**kwargs):
        if isinstance(path_arg,(str,bytes,os.PathLike)) and Path(path_arg)==path:
            raise PermissionError(errno.EPERM,"lease stat denied")
        return real(path_arg,*args,**kwargs)
    with monkeypatch.context() as patch:
        patch.setattr(os,"stat",denied)
        value,error=captured(lambda:ctl.inventory.lease(1,required=False))
        assert value is None and isinstance(error,SlotError)
        assert error.observations[0].errno==errno.EPERM
        _,error=captured(lambda:ctl.release(1));assert isinstance(error,SlotError)
        assert forbidden_counts(host)==before
    assert path.read_bytes()==original


@pytest.mark.parametrize("shape", ["server-list", "missing-server", "host-list", "slots-list", "slot-list",
                                   "missing-worktree", "missing-port", "port-object", "role-object"])
def test_six_r6_malformed_populated_family_mapping_is_unavailable(rig, capsys, shape):
    ctl, sup, host = rig
    for number in (1, 2, 3):
        owned(sup, host, "backend", number, 831100+number)
    host.remove(831101)
    ctl.inventory.process_path("backend", 1).unlink()
    alias = ctl.inventory.source.parent / "lean-slots.equivalent.json"
    valid = json.loads(ctl.inventory.source.read_text())
    value = json.loads(json.dumps(valid))
    if shape == "server-list": value["server"] = []
    elif shape == "missing-server": value.pop("server")
    elif shape == "host-list": value["server"]["host"] = []
    elif shape == "slots-list": value["slots"] = ["1", "2", "3"]
    elif shape == "slot-list": value["slots"]["2"] = []
    elif shape == "missing-worktree": value["slots"]["2"].pop("worktree")
    elif shape == "missing-port": value["slots"]["2"].pop("backend_port")
    elif shape == "port-object": value["slots"]["2"]["backend_port"] = {}
    else: value["repo_role"] = {}
    alias.write_text(json.dumps(value)); original = alias.read_bytes()
    before = forbidden_counts(host)
    status, error = captured(ctl.status)
    assert error is None, repr(error)
    assert not status["capacity_complete"] and status["reserved_physical_slots"] == [1, 2, 3]
    require_witnesses(status["capacity_observations"])
    assert any(x["state"] == "unavailable" and x["operation"] == "validate-inventory"
               and x["target"] == str(alias) and x["error_class"] == "ValueError"
               for x in status["capacity_observations"])
    doctor, error = captured(ctl.doctor)
    assert error is None, repr(error)
    assert not next(x for x in doctor["checks"] if x["name"] == "heavy_backend_limit")["ok"]
    capsys.readouterr()
    code, error = captured(lambda: cli.main(["--inventory", str(ctl.inventory.source), "status", "--json"]))
    assert error is None and code == 0
    assert not json.loads(capsys.readouterr().out)["capacity_complete"]
    _, error = captured(lambda: sup.start_backend(1))
    assert isinstance(error, SlotError)
    assert forbidden_counts(host) == before and alias.read_bytes() == original
    alias.write_text(json.dumps(valid))
    restored = ctl.status()
    assert restored["capacity_complete"] and restored["reserved_physical_slots"] == [2, 3]
    assert sup.capacity_census()["confirmed_services"] == 2
    sup.start_backend(1)
    assert len(host.launches) == before[0]+1 and not host.signals
    assert sup.capacity_census()["confirmed_services"] == 3


@pytest.mark.parametrize("field,value", [
    ("pid",-1), ("pid",True), ("signature",None), ("signature",17), ("signature",""),
    ("phase",[]), ("phase","unsupported"), ("process_schema_version",{}),
    ("process_schema_version",True), ("schema_version",True), ("missing-pid",None),
])
def test_six_r2_root_phase_shape_cannot_be_managed(rig, capsys, field, value):
    ctl,sup,host=rig
    record=owned(sup,host,"backend",1,830101); data=json.loads(record.read_text())
    if field=="missing-pid":data.pop("pid")
    else:data[field]=value
    record.write_text(json.dumps(data));original=record.read_bytes();before=forbidden_counts(host)
    status,error=captured(ctl.status)
    assert error is None,repr(error)
    resource=status["slots"][0]["resources"]["backend"]
    assert resource["state"]==resource["record_phase"]==resource["identity_authority"]=="unavailable"
    assert 1 in status["reserved_physical_slots"] and not status["capacity_complete"]
    require_witnesses(resource["observations"])
    doctor,error=captured(ctl.doctor);assert error is None,repr(error)
    assert not next(x for x in doctor["checks"] if x["name"]=="heavy_backend_limit")["ok"]
    capsys.readouterr();code,error=captured(lambda:cli.main(["--inventory",str(ctl.inventory.source),"status","--json"]))
    assert error is None and code==0
    assert json.loads(capsys.readouterr().out)["slots"][0]["resources"]["backend"]["identity_authority"]=="unavailable"
    _,error=captured(lambda:sup.stop_backend(1));assert isinstance(error,SlotError)
    assert forbidden_counts(host)==before and record.read_bytes()==original


def native_linked_copy(ctl, name="native-secondary"):
    copy = ctl.inventory.workspace_root / name
    run(ctl.repo, "git", "worktree", "add", "-b", name, str(copy), "main")
    return copy


def test_native_control_01_proven_linked_copy_keeps_free_capacity(rig):
    ctl, sup, host = rig
    copy = native_linked_copy(ctl)
    for n in (1, 2): owned(sup, host, "backend", n, 841100+n)
    before = forbidden_counts(host)
    family, errors = sup._role_inventories(retain_aliases=True)
    assert not errors and {inv.repo_root for inv in family} == {ctl.repo}
    assert copy not in {inv.repo_root for inv in family}
    census = sup.capacity_census()
    assert census["complete"] and census["reserved_physical_slots"] == [1, 2]
    assert census["confirmed_services"] == 2 and not census["conflicts"]
    assert ctl.status()["capacity_complete"]
    assert forbidden_counts(host) == before
    sup.start_backend(3)
    assert len(host.launches) == before[0]+1 and sup.process_state("backend", 3) == "running"


def test_native_control_02_conflicting_primary_and_supported_aliases(rig):
    ctl, sup, host = rig; ctl.build(); ctl.acquire(1, client="codex", base_ref="main")
    owned(sup, host, "proxy", 1, 841201); owned(sup, host, "backend", 2, 841202)
    copy = native_linked_copy(ctl, "alias-location")
    alias = copy / "config/lean-slots.public.json"
    value = json.loads(alias.read_text()); value["repo_root"] = os.path.relpath(ctl.repo, alias.parent)
    value["build"]["dependency_ref"] = "independent-input-ref"
    alias.write_text(json.dumps(value))
    own_alias = ctl.inventory.source.parent / "lean-slots.override.json"
    own_value = json.loads(ctl.inventory.source.read_text()); own_value["build"]["dependency_ref"] = "alternate-input-ref"
    own_alias.write_text(json.dumps(own_value))
    family, errors = sup._role_inventories(retain_aliases=True)
    assert not errors and {inv.source for inv in family} == {ctl.inventory.source, alias, own_alias}
    assert sup.capacity_census()["complete"] and sup.capacity_census()["confirmed_services"] == 1
    other = ctl.inventory.workspace_root / "independent-primary"; other.mkdir()
    run(other, "git", "init", "-b", "main")
    (other / "config").mkdir()
    conflicting = json.loads(ctl.inventory.source.read_text()); conflicting["slots"]["3"]["backend_port"] += 100
    conflict_path = other / "config/lean-slots.public.json"; conflict_path.write_text(json.dumps(conflicting))
    marker = ctl.inventory.worktree(1) / "lean/.lake/preserve-native"; marker.parent.mkdir(parents=True, exist_ok=True); marker.write_text("retained")
    before = forbidden_counts(host)
    census = sup.capacity_census()
    assert not census["complete"] and any("conflicting inventory domains" in x for x in census["errors"])
    for call in (lambda: sup.start_backend(3), lambda: ctl.prepare(1)):
        _, error = captured(call); assert isinstance(error, SlotError)
    assert marker.read_text() == "retained" and forbidden_counts(host) == before
    conflict_path.unlink()
    assert sup.capacity_census()["complete"]
    # A real secondary copy with a substantive server difference is never silently dropped.
    second = native_linked_copy(ctl, "conflicting-secondary")
    second_path = second / "config/lean-slots.public.json"
    second_value = json.loads(second_path.read_text()); second_value["server"]["instructions"] = "different-server-contract"
    second_path.write_text(json.dumps(second_value))
    assert not sup.capacity_census()["complete"]
    assert any("secondary checkout has a conflicting" in x for x in sup.capacity_census()["errors"])
    assert forbidden_counts(host) == before


@pytest.mark.parametrize("failure", ["permission", "timeout", "nonzero", "truncated", "extra", "empty", "mismatched-top", "outside-common", "non-git", "canonical-unavailable", "stderr", "oversized", "nul"])
def test_native_control_03_git_observer_unavailable_is_not_capacity(rig, monkeypatch, capsys, failure):
    ctl, sup, host = rig
    for n in (2, 3): owned(sup, host, "backend", n, 841300+n)
    if failure == "canonical-unavailable": native_linked_copy(ctl, "needs-canonical")
    actual_run = subprocess.run
    def external_git(argv, **kwargs):
        if argv[:2] != ["git", "rev-parse"] or "--git-common-dir" not in argv or Path(kwargs["cwd"]) != ctl.repo:
            return actual_run(argv, **kwargs)
        if failure in ("permission", "canonical-unavailable"): raise PermissionError(errno.EPERM, "Git identity denied")
        if failure == "timeout": raise subprocess.TimeoutExpired(argv, 2)
        complete = actual_run(argv, **kwargs)
        lines = complete.stdout.splitlines()
        result = SimpleNamespace(returncode=0, stdout=complete.stdout, stderr="")
        if failure in ("nonzero", "non-git"): result.returncode=128; result.stderr="fatal: not a git repository"
        elif failure == "truncated": result.stdout="\n".join(lines[:2])+"\n"
        elif failure == "extra": result.stdout += "extra-field\n"
        elif failure == "empty": result.stdout = lines[0]+"\n\n"+lines[2]+"\n"
        elif failure == "mismatched-top": result.stdout = str(ctl.repo.parent)+"\n"+"\n".join(lines[1:])+"\n"
        elif failure == "outside-common": result.stdout = lines[0]+"\n/outside-unresolved-common\n/outside-unresolved-common/worktrees/secondary\n"
        elif failure == "stderr": result.stderr="diagnostic means incomplete observation"
        elif failure == "oversized": result.stdout="x"*17000
        elif failure == "nul": result.stdout=complete.stdout.replace(lines[1],"ambiguous\x00field")
        return result
    before = forbidden_counts(host)
    with monkeypatch.context() as patch:
        patch.setattr(subprocess, "run", external_git)
        status, error = captured(ctl.status); assert error is None, repr(error)
        assert not status["capacity_complete"] and status["reserved_physical_slots"] == [1,2,3]
        require_witnesses(status["capacity_observations"])
        assert any(x["operation"] == "git-checkout-identity" and x["state"] == "unavailable" and x["target"] == str(ctl.repo) for x in status["capacity_observations"])
        doctor, error = captured(ctl.doctor); assert error is None, repr(error)
        assert not next(x for x in doctor["checks"] if x["name"] == "heavy_backend_limit")["ok"]
        capsys.readouterr(); assert cli.main(["--inventory",str(ctl.inventory.source),"status","--json"]) == 0
        assert not json.loads(capsys.readouterr().out)["capacity_complete"]
        _, error = captured(lambda: sup.start_backend(1)); assert isinstance(error, SlotError)
        assert forbidden_counts(host) == before
    assert sup.capacity_census()["complete"] and sup.capacity_census()["reserved_physical_slots"] == [2,3]
    sup.start_backend(1)
    assert len(host.launches) == before[0]+1 and sup.process_state("backend",1) == "running"


def native_project_tree(ctl, sup, host, *, second=False):
    host.add(842001, "nonproject manager")
    owned(sup, host, "backend", 1, 842101); row=host.rows[842101]; host.rows[842101]=(842001,row[1],row[2])
    project = str(ctl.inventory.lean_root(1))
    host.add(842201, "generic Lake intermediary", ppid=842101)
    host.add(842301, "lean --worker "+project, ppid=842201)
    host.add(842401, "generic Lean intermediary", ppid=842301)
    host.add(842501, "project worker "+project, ppid=842401)
    if second:
        host.add(842601, "independent project service "+project, ppid=842001)
        host.add(842701, "generic independent intermediary", ppid=842601)
        host.add(842801, "independent project worker "+project, ppid=842701)
    owned(sup, host, "backend", 2, 842102)
    return project


def test_native_control_04_generic_intermediates_preserve_one_tree(rig):
    ctl, sup, host = rig; project=native_project_tree(ctl,sup,host)
    paths=[ctl.inventory.process_path("backend",n) for n in (1,2)]; before_bytes=[p.read_bytes() for p in paths]
    before=forbidden_counts(host); census=sup.capacity_census()
    assert census["complete"] and census["reserved_physical_slots"] == [1,2] and census["confirmed_services"] == 2
    witness=next(x for x in census["observations"] if x["operation"] == "process-ancestry" and x["target"] == project)
    assert witness["observed_identity"] == {"project_pids":[842101,842301,842501],"roots":[842101]}
    require_witnesses(census["observations"])
    assert ctl.status()["capacity_complete"] and forbidden_counts(host) == before
    assert [p.read_bytes() for p in paths] == before_bytes
    sup.start_backend(3)
    assert len(host.launches) == before[0]+1 and not host.signals


def test_native_control_05_common_nonproject_ancestor_keeps_two_services(rig):
    ctl,sup,host=rig;project=native_project_tree(ctl,sup,host,second=True)
    before=forbidden_counts(host);record=ctl.inventory.process_path("backend",1);original=record.read_bytes()
    census=sup.capacity_census()
    assert not census["complete"] and census["reserved_physical_slots"] == [1,2]
    witness=next(x for x in census["observations"] if x["operation"] == "process-ancestry" and x["target"] == project)
    assert witness["observed_identity"]["roots"] == [842101,842601]
    assert any("multiple service roots" in error for error in census["errors"])
    _,error=captured(lambda:sup.start_backend(3));assert isinstance(error,SlotError)
    assert record.read_bytes()==original and forbidden_counts(host)==before


@pytest.mark.parametrize("failure", ["cycle", "self-parent", "missing-middle", "missing-above-root", "duplicate", "denied", "partial", "retained"])
def test_native_control_06_unavailable_ancestry_and_retained_pins(rig, failure):
    ctl,sup,host=rig;project=native_project_tree(ctl,sup,host)
    record=ctl.inventory.process_path("backend",1)
    if failure=="cycle":
        row=host.rows[842201];host.rows[842201]=(842301,row[1],row[2])
    elif failure=="self-parent":
        row=host.rows[842301];host.rows[842301]=(842301,row[1],row[2])
    elif failure=="missing-middle":host.remove(842201)
    elif failure=="missing-above-root":host.remove(842001)
    elif failure=="duplicate":
        data="".join(f"{pid} {row[0]} {row[2]}\n" for pid,row in host.rows.items())
        host.census_result=SimpleNamespace(returncode=0,stdout=data+f"842101 {host.rows[842101][0]} {host.rows[842101][2]}\n",stderr="")
    elif failure=="denied":host.census_denied=True
    elif failure=="partial":
        data="".join(f"{pid} {row[0]} {row[2]}\n" for pid,row in host.rows.items() if pid in (1,os.getpid()))
        host.census_result=SimpleNamespace(returncode=0,stdout=data,stderr="")
    else:
        signature=host.add(842901,"generic reparented survivor")
        value=json.loads(record.read_text());value["descendants"]=[{"pid":842901,"signature":signature}];record.write_text(json.dumps(value))
        for pid in (842101,842201,842301,842401,842501):host.remove(pid)
    original=record.read_bytes();before=forbidden_counts(host);census=sup.capacity_census()
    if failure=="retained":
        assert census["complete"] and census["owners"][1]==["public"] and census["reserved_physical_slots"]==[1,2]
    else:
        assert not census["complete"]
        assert any(x["state"]=="unavailable" and x["operation"] in ("process-ancestry","ps-census","ps-selected") for x in census["observations"])
        _,error=captured(lambda:sup.start_backend(3));assert isinstance(error,SlotError)
    require_witnesses(census["observations"])
    assert record.read_bytes()==original and forbidden_counts(host)==before
