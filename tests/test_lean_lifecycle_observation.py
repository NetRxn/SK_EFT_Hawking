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
        self.ps_cost = 0.0  # Synthetic per-command elapsed time, never a native guarantee.
        self.command_calls = []
        self.real_run = subprocess.run
        self.native_states = {}
        self.tcp_extra = []
        self.tcp_denied = False
        self.before_signal = None
        self.after_sleep = None
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
        if argv[0] == "lsof":
            if self.tcp_denied:
                raise PermissionError(errno.EPERM, "TCP observation denied")
            if "cwd" in argv:
                return SimpleNamespace(returncode=0, stdout=f"p{os.getpid()}\nn/isolated-observer\n", stderr="")
            sockets = [{"pid": pid, "fd": str(port), "type": "IPv4", "name": f"127.0.0.1:{port}", "state": "LISTEN"}
                       for port, pid in self.ports.items()] + self.tcp_extra
            output = "".join(f"p{x['pid']}\nf{x['fd']}\nt{x['type']}\nn{x['name']}\nTST={x['state']}\n" for x in sockets)
            return SimpleNamespace(returncode=0 if output else 1, stdout=output, stderr="")
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
        remaining = kwargs.get("timeout", 2.0)
        self.clock += min(self.ps_cost, remaining)
        if self.ps_cost > remaining:
            raise subprocess.TimeoutExpired(argv, remaining)
        native = "stat=" in " ".join(argv)
        def native_row(pid, row):
            return f"{pid} {row[0]} {' '.join(row[2].split()[:5])} {self.native_states.get(pid, 'S')} {row[1]}\n"
        if "-axo" in argv:
            if self.census_denied:
                raise PermissionError(errno.EPERM, "census denied")
            if self.census_result is not None:
                if isinstance(self.census_result, BaseException):
                    raise self.census_result
                return self.census_result
            output = "".join(native_row(pid, row) if native else f"{pid} {row[0]} {row[2]}\n" for pid, row in self.rows.items())
            if self.after_census and not native:
                self.after_census()
            return SimpleNamespace(returncode=0, stdout=output, stderr="")
        requested = [int(pid) for pid in argv[2].split(",")]
        for pid in requested:
            if pid in self.selected_results:
                result = self.selected_results[pid]
                if isinstance(result, BaseException):
                    raise result
                return result
            if pid in self.denied_pids:
                raise PermissionError(errno.EPERM, "selected ps denied")
        with_pid = "pid=" in " ".join(argv)
        output = "".join(native_row(pid, self.rows[pid]) if native else
                         f"{pid} {self.rows[pid][0]} {self.rows[pid][2]}\n" if with_pid else self.rows[pid][2]
                         for pid in requested if pid in self.rows)
        return SimpleNamespace(returncode=0 if output else 1, stdout=output, stderr="")

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
        if self.after_sleep:
            self.after_sleep()

    def remove(self, pid):
        self.rows.pop(pid, None)
        for port, owner in list(self.ports.items()):
            if owner == pid:
                self.ports.pop(port)

    def kill(self, pid, sig):
        assert sig == signal.SIGTERM, "automatic SIGKILL forbidden"
        if self.before_signal:
            self.before_signal(pid)
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
    with pytest.raises(SlotError, match="post-SIGTERM") as failure:
        sup.stop_backend(1)
    assert failure.value.observations and all(row.state == "unavailable" for row in failure.value.observations)
    assert host.clock <= 10.00001
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
    publication_faults = []
    def fail_after_first(source, dest):
        if str(dest).endswith("public-wt2-backend.json"):
            attempts.append(json.loads(Path(source).read_text())["phase"])
            if len(attempts) >= 2:
                fault = PermissionError("persistent registration failure")
                publication_faults.append(fault)
                raise fault
        return real_replace(source, dest)
    with monkeypatch.context() as patch:
        patch.setattr(state.os, "replace", fail_after_first)
        with pytest.raises(SlotError, match="persistent registration failure.*diagnostic publication failed.*owned cleanup completed") as persistent:
            sup.start_backend(2)
    assert host.handles[-1].terminations == 1 and host.handles[-1].waits == [5]
    assert not sup.inventory.process_path("backend", 2).exists()
    assert len(attempts) >= 3
    assert len(publication_faults) == 2
    assert persistent.value.__cause__ is publication_faults[0]
    assert isinstance(persistent.value.__cause__, PermissionError)
    observations = persistent.value.observations
    assert [item.operation for item in observations] == ["startup-signature_write", "rollback-diagnostic-write"]
    assert [item.error_class for item in observations] == ["PermissionError", "PermissionError"]
    assert [item.errno for item in observations] == [fault.errno for fault in publication_faults]
    assert [item.detail for item in observations] == [str(fault) for fault in publication_faults]
    assert 2 not in sup.capacity_census()["reserved_physical_slots"]
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
    ctl.acquire(1,client="codex",base_ref="main")  # Acquire before deliberately denying provenance.
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


# RR controls use production owners, real temporary records and only external OS seams.
def rr_session(monkeypatch):
    monkeypatch.delenv("LEAN_SLOT_OWNER_PID", raising=False)
    monkeypatch.setenv("LEAN_SLOT_OWNER_SESSION", "rr-driving-session")


def rr_authorization(ctl, number=1, owner=None):
    sup = Supervisor(ctl.inventory)
    lease = ctl.inventory.lease(number, required=False)
    binding = None
    if lease:
        owner = owner or ctl
        binding = {"inventory_source": str(owner.inventory.source), "repo_role": owner.inventory.repo_role,
                   "inventory_domain": sup._inventory_domain(owner.inventory),
                   "worktree": str(owner.inventory.worktree(number)), "state_root": str(owner.inventory.state_root),
                   "slot": number, "public_dependency_sha": lease.get("public_dependency_sha"),
                   "lease_sha256": state.sha256_bytes(owner.inventory.lease_path(number).read_bytes())}
    return {"approval_ref": "isolated operator approval RR", "drain_receipt": "isolated requests completed",
            "dispatch_frozen": True, "requests_drained": True,
            "owner_session_hash": ctl._owner()["owner_session_hash"],
            "backend_target": sup.recovery_target(number), "lease_owner": binding}


def rr_orphan(ctl, host, *, owner=None, number=1):
    sup = Supervisor(ctl.inventory)
    if owner is not None:
        lease = owner.acquire(number, client="codex", base_ref="main")
        owner._quarantine(number, lease, "isolated recovery case")
    root = 910030 + number
    signature = host.add(root, " ".join(sup.backend_command(number)), ppid=1,
                         port=int(ctl.inventory.slot(number)["backend_port"]))
    child = root - 10
    child_signature = host.add(child, "generic backend child", ppid=root)
    family = [{"pid": root, "ppid": 1, "signature": signature},
              {"pid": child, "ppid": root, "signature": child_signature}]
    return {"expected_root": {"pid": root, "signature": signature}, "expected_family": family,
            "authorization": rr_authorization(ctl, number, owner)}


def rr_managed_zombie(sup, host, *, legacy=False):
    root, parent, child = 920030, 920010, 920020
    path = owned(sup, host, "backend", 1, root)
    parent_sig = host.add(parent, "generic live backend", ppid=root)
    child_sig = host.add(child, "lake serve -- fixture", ppid=parent)
    data = read_json(path)
    data["descendants"] = [{"pid": root, "signature": data["signature"]},
                           {"pid": parent, "signature": parent_sig},
                           {"pid": child, "signature": child_sig}]
    if legacy:
        data.pop("phase"); data.pop("process_schema_version")
    atomic_json(path, data)
    host.rows[child] = (parent, "<defunct>", "Sun Oct 11 00:00:00 2026 <defunct>")
    host.native_states[child] = "Z"
    return path, root, parent, child, data


def test_rr1_generic_identity_unchanged(rig):
    _, sup, host = rig
    path, root, parent, child, data = rr_managed_zombie(sup, host)
    assert state.observe_process(root, data["signature"]).state == "present"
    assert state.observe_process(child, data["descendants"][-1]["signature"]).state == "mismatch"
    terminal = state.observe_shutdown_process(child)
    assert terminal.state == "present" and terminal.identity["native_state"] == "Z", "RR native zombie remains present"
    assert state.observe_process(99999999).state == "absent"
    host.denied_pids.add(child)
    assert state.observe_process(child).state == state.observe_shutdown_process(child).state == "unavailable"
    assert path.exists() and not host.signals


@pytest.mark.parametrize("legacy", [False, True], ids=["current", "legacy"])
def test_rr1_retained_zombie_parent_progress(rig, legacy):
    _, sup, host = rig
    path, root, parent, child, original = rr_managed_zombie(sup, host, legacy=legacy)
    def before(pid):
        assert pid != child, "native zombie must never receive a signal"
        assert read_json(path)["descendants"] == sorted(original["descendants"], key=lambda row: row["pid"]), "original signatures must survive exit"
        assert child in host.rows, "terminal child is present until the actual parent reaps it"
    host.before_signal = lambda pid: before(pid) if pid == parent else None
    host.after_signal = lambda pid: host.remove(child) if pid == parent else None
    _, error = captured(lambda: sup.stop_backend(1))
    assert error is None, repr(error)
    assert [pid for pid, _ in host.signals] == [parent, root], "independently live parents must make progress"
    assert not path.exists() and not ({root, parent, child} & host.rows.keys())


@pytest.mark.parametrize("failure", ["fake-defunct", "bad-state", "birth", "unretained", "root-absent", "reparented", "cycle", "denied"], ids=str)
def test_rr1_terminal_evidence_refusal(rig, failure):
    _, sup, host = rig
    path, root, parent, child, data = rr_managed_zombie(sup, host)
    if failure == "fake-defunct": host.native_states[child] = "S"
    elif failure == "bad-state": host.native_states[child] = "?"
    elif failure == "birth": host.rows[child] = (parent, "<defunct>", "Sun Oct 11 01:00:00 2026 <defunct>")
    elif failure == "unretained":
        data["descendants"] = data["descendants"][:-1]; atomic_json(path, data)
    elif failure == "root-absent": host.remove(root)
    elif failure == "reparented": host.rows[child] = (1, *host.rows[child][1:])
    elif failure == "cycle": host.rows[child] = (child, *host.rows[child][1:])
    elif failure == "denied": host.denied_pids.add(child)
    before = path.read_bytes()
    _, error = captured(lambda: sup.stop_backend(1))
    assert isinstance(error, SlotError), repr(error)
    assert not host.signals, "invalid terminal witness must not authorize parent signals"
    assert path.read_bytes() == before


def test_rr1_ancestry_order(rig):
    _, sup, host = rig
    path = owned(sup, host, "backend", 1, 930090)
    host.add(930010, "generic intermediate", ppid=930090)
    host.add(930050, "generic leaf", ppid=930010)
    host.add(930030, "generic deepest leaf", ppid=930050)
    _, error = captured(lambda: sup.stop_backend(1))
    assert [x[0] for x in host.signals] == [930030, 930050, 930010, 930090], "topology must determine signal order"
    assert error is None, repr(error)
    assert not path.exists()


@pytest.mark.parametrize("outcome", ["reaped", "persistent", "slow-observation"], ids=str)
def test_rr1_exit_wait(rig, outcome):
    _, sup, host = rig
    path, root, parent, child, data = rr_managed_zombie(sup, host)
    def after_signal(pid):
        if pid == parent:
            host.rows[parent] = (root, "<defunct>", "Sun Oct 11 00:00:00 2026 <defunct>")
            host.native_states[parent] = "Z"
            host.rows[child] = (1, *host.rows[child][1:])
    host.after_signal = after_signal
    if outcome == "reaped":
        def reap():
            for pid in (root, parent, child): host.remove(pid)
        host.after_sleep = reap
    if outcome == "slow-observation": host.after_census = lambda: setattr(host, "clock", host.clock + 1)
    _, error = captured(lambda: sup.stop_backend(1))
    if outcome == "reaped":
        assert error is None and not path.exists()
        assert [x[0] for x in host.signals] == [parent], "exit transitions permit passive wait only"
    else:
        assert isinstance(error, SlotError) and path.exists()
        assert host.clock <= 10.00001, "all stop observation consumes one fixed deadline"
        assert child not in [x[0] for x in host.signals]


@pytest.mark.parametrize("residual", [False, True], ids=["absent", "foreign-listener"])
def test_rr1_absent_root_and_quiescence(rig, residual):
    _, sup, host = rig
    path = owned(sup, host, "backend", 1, 940010)
    if residual:
        host.after_signal = lambda pid: host.ports.update({29101: 999999})
    _, error = captured(lambda: sup.stop_backend(1))
    if residual:
        assert path.exists(), "endpoint/project quiescence must precede unregister"
        assert isinstance(error, SlotError)
    else:
        assert error is None and not path.exists()


@pytest.mark.parametrize("leased,deep", [(False, False), (True, False), (True, True)], ids=["free", "same-role-quarantine", "deep-family"])
def test_rr2_unique_family_stop_only(rig, monkeypatch, leased, deep):
    ctl, sup, host = rig; rr_session(monkeypatch)
    request = rr_orphan(ctl, host, owner=ctl if leased else None)
    if deep:
        parent = request["expected_family"][-1]["pid"]
        for pid in (909050, 909010, 909070, 909030):
            signature = host.add(pid, "generic deep intermediary", ppid=parent)
            request["expected_family"].append({"pid": pid, "ppid": parent, "signature": signature})
            parent = pid
    lease_path = ctl.inventory.lease_path(1)
    lease_before = lease_path.read_bytes() if leased else None
    record_path = ctl.inventory.process_path("backend", 1)
    records = []
    def before(pid):
        assert record_path.exists(), "no signal before exclusive durable reservation"
        data = read_json(record_path); records.append(data)
        assert data["record_origin"] == "operator_stop_only" and data["phase"] == "uncertain_residual"
        assert "runtime_fingerprint" not in data and "launch_token" not in data
    host.before_signal = before
    _, error = captured(lambda: ctl.recover_orphan_backend_stop(1, **request))
    assert error is None, repr(error)
    assert records and not record_path.exists() and not host.launches
    assert set(x[0] for x in host.signals) == {x["pid"] for x in request["expected_family"]}
    if deep:
        assert [x[0] for x in host.signals] == [row["pid"] for row in reversed(request["expected_family"])]
    assert (lease_path.read_bytes() if leased else None) == lease_before


@pytest.mark.parametrize("failure", ["approval", "wrong-owner", "active", "acquired", "preparing", "ready_to_absorb", "dirty", "unabsorbed", "drain", "scope"], ids=str)
def test_rr2_authority_and_work_refusal(rig, monkeypatch, failure):
    ctl, sup, host = rig; rr_session(monkeypatch)
    request = rr_orphan(ctl, host, owner=ctl)
    if failure == "approval": request["authorization"]["approval_ref"] = ""
    elif failure == "wrong-owner":
        lease = ctl.inventory.lease(1); lease["owner_session_hash"] = "0" * 64
        atomic_json(ctl.inventory.lease_path(1), lease)
        request["authorization"] = rr_authorization(ctl)
    elif failure in {"active", "acquired", "preparing", "ready_to_absorb"}:
        lease = ctl.inventory.lease(1); lease["state"] = failure.upper()
        atomic_json(ctl.inventory.lease_path(1), lease)
        request["authorization"] = rr_authorization(ctl)
    elif failure == "dirty": (ctl.inventory.worktree(1) / "unabsorbed.txt").write_text("preserve")
    elif failure == "unabsorbed":
        tree = ctl.inventory.worktree(1); (tree / "unabsorbed.txt").write_text("preserve")
        run(tree, "git", "add", "unabsorbed.txt"); run(tree, "git", "commit", "-m", "isolated unabsorbed work")
    elif failure == "drain": request["authorization"]["requests_drained"] = False
    elif failure == "scope": request["authorization"]["backend_target"]["slot"] = 2
    _, error = captured(lambda: ctl.recover_orphan_backend_stop(1, **request))
    assert not host.signals, "authority/work refusal must precede all native signals"
    assert isinstance(error, SlotError)
    assert not ctl.inventory.process_path("backend", 1).exists()


@pytest.mark.parametrize("failure", ["stale", "stale-child", "omitted-child", "extra-member", "second-root", "wrong-project", "wrong-port", "wrong-host", "foreign-listener", "duplicate-listener", "tcp", "denied", "census-denied", "registry-present"], ids=str)
def test_rr2_family_and_listener_refusal(rig, monkeypatch, failure):
    ctl, sup, host = rig; rr_session(monkeypatch)
    request = rr_orphan(ctl, host)
    root = request["expected_root"]["pid"]
    if failure == "stale": request["expected_root"]["signature"] = "Sun Oct 11 01:00:00 2026 stale"
    elif failure == "stale-child": request["expected_family"][-1]["signature"] = "Sun Oct 11 01:00:00 2026 stale child"
    elif failure == "extra-member": request["expected_family"].append({"pid": 950099, "ppid": root, "signature": "Sun Oct 11 00:00:00 2026 missing child"})
    elif failure == "omitted-child": request["expected_family"] = request["expected_family"][:1]
    elif failure in {"wrong-project", "wrong-port", "wrong-host"}:
        args = sup.backend_command(1)
        flag = {"wrong-project": "--lean-project-path", "wrong-port": "--port", "wrong-host": "--host"}[failure]
        args[args.index(flag)+1] = {"wrong-project": "/other/project", "wrong-port": "29999", "wrong-host": "0.0.0.0"}[failure]
        signature = host.add(root, " ".join(args), ppid=1)
        request["expected_root"]["signature"] = request["expected_family"][0]["signature"] = signature
    elif failure == "second-root": host.add(950001, " ".join(sup.backend_command(1)), ppid=1)
    elif failure == "foreign-listener": host.ports[29101] = 999999
    elif failure == "duplicate-listener": host.tcp_extra.append({"pid": root, "fd": "dup", "type": "IPv4", "name": "127.0.0.1:29101", "state": "LISTEN"})
    elif failure == "tcp": host.tcp_extra.append({"pid": root, "fd": "active", "type": "IPv4", "name": "127.0.0.1:29101->127.0.0.1:40000", "state": "ESTABLISHED"})
    elif failure == "denied": host.tcp_denied = True
    elif failure == "census-denied": host.census_denied = True
    elif failure == "registry-present": owned(sup, host, "backend", 1, root)
    _, error = captured(lambda: ctl.recover_orphan_backend_stop(1, **request))
    assert not host.signals, "ambiguous family/listener must never authorize signals"
    assert isinstance(error, SlotError)
    assert ctl.inventory.process_path("backend", 1).exists() == (failure == "registry-present")


@pytest.mark.parametrize("failure", ["none", "collision", "file-fsync", "directory-fsync", "link"], ids=str)
def test_rr2_exclusive_durable_reservation(tmp_path, monkeypatch, failure):
    path = tmp_path / "process.json"; data = {"phase": "uncertain_residual", "complete": [1, 2, 3]}
    real_fsync, real_link = os.fsync, os.link
    synchronizations = []
    def sync(fd):
        is_directory = state.stat.S_ISDIR(os.fstat(fd).st_mode)
        synchronizations.append("directory" if is_directory else "file")
        if failure == ("directory-fsync" if is_directory else "file-fsync"):
            raise OSError("isolated sync refusal")
        real_fsync(fd)
    def link(source, target):
        assert json.loads(Path(source).read_text()) == data
        assert "file" in synchronizations
        if failure == "link": raise OSError("isolated link refusal")
        real_link(source, target)
    monkeypatch.setattr(os, "fsync", sync); monkeypatch.setattr(os, "link", link)
    if failure == "collision": path.write_text("competitor")
    _, error = captured(lambda: state.exclusive_durable_json(path, data))
    if failure == "none":
        assert error is None and read_json(path) == data
        assert synchronizations == ["file", "directory"], "publication requires file and directory durability"
    elif failure == "collision":
        assert isinstance(error, SlotError) and path.read_text() == "competitor"
    elif failure == "directory-fsync":
        assert isinstance(error, SlotError) and read_json(path) == data
    else:
        assert isinstance(error, SlotError) and not path.exists()


def rr_retained_recovery(ctl, host, request):
    # Publication succeeds, then a genuine external signal failure leaves a real residual.
    host.before_signal = lambda pid: (_ for _ in ()).throw(PermissionError("isolated signal refusal"))
    _, error = captured(lambda: ctl.recover_orphan_backend_stop(1, **request))
    assert isinstance(error, SlotError)
    host.before_signal = None
    path = ctl.inventory.process_path("backend", 1)
    assert path.exists() and not host.signals
    assert read_json(path)["recovery"]["admission_observations"]
    assert read_json(path)["recovery"]["error_observations"]
    return path


def test_rr2_record_consumers(rig, monkeypatch):
    ctl, sup, host = rig; rr_session(monkeypatch)
    request = rr_orphan(ctl, host, owner=ctl)
    path = rr_retained_recovery(ctl, host, request)
    original = path.read_bytes()
    lease_original = ctl.inventory.lease_path(1).read_bytes()
    resource = sup._resource_status("backend", 1)
    assert resource["state"] == "uncertain_residual", "recovery provenance cannot become healthy managed service"
    assert resource["identity_authority"] == "stop_only_recovery"
    assert 1 in sup.capacity_census()["reserved_physical_slots"]
    assert ctl.status()["slots"][0]["resources"]["backend"]["state"] == "uncertain_residual"
    assert ctl.doctor()["checks"]
    # A healthy proxy makes these checks reach the backend recovery guard.
    owned(sup, host, "proxy", 1, 961001)
    effects = []
    def paused_transition():
        with sup.paused_backend(1):
            effects.append("forbidden cache transition")
    for operation in (lambda: sup.stop_backend(1), lambda: sup.start_backend(1), lambda: sup.assert_healthy(1)):
        _, error = captured(operation)
        assert not host.signals, "ordinary lifecycle cannot resume stop-only recovery"
        assert isinstance(error, SlotError) and path.read_bytes() == original
    for operation in (sup.start, paused_transition):
        _, error = captured(operation)
        assert isinstance(error, SlotError) and not effects and not host.launches and not host.signals
        assert path.read_bytes() == original
    data = read_json(path)
    for key, value in (("phase", "running"), ("phase", "launch_pending"), ("runtime_fingerprint", "invented"), ("launch_token", "invented"), ("record_origin", "unknown")):
        corrupt = dict(data); corrupt[key] = value; atomic_json(path, corrupt)
        assert sup._resource_status("backend", 1)["state"] == "unavailable"
        assert 1 in sup.capacity_census()["reserved_physical_slots"]
        _, error = captured(lambda: sup.stop_backend(1)); assert isinstance(error, SlotError)
        assert not host.signals
    path.write_bytes(original)
    marker = ctl.inventory.lean_root(1) / ".lake/preserved-recovery"
    marker.parent.mkdir(parents=True, exist_ok=True); marker.write_text("retained cache")
    for operation in (lambda: ctl.prepare(1), lambda: ctl.release(1)):
        _, error = captured(operation)
        assert isinstance(error, SlotError) and not host.signals and not host.launches
        assert marker.read_text() == "retained cache" and path.read_bytes() == original
        assert ctl.inventory.lease_path(1).read_bytes() == lease_original, "RR original quarantine lease bytes preserved"
    ctl.recover_orphan_backend_stop(1, **request, expected_residual_sha256=state.sha256_bytes(original))
    assert not path.exists()
    ctl.release(1)
    assert not ctl.inventory.lease_path(1).exists()


@pytest.mark.parametrize("failure", ["none", "partial-absent", "all-absent", "hash", "owner", "target", "signature", "domain"], ids=str)
def test_rr2_exact_residual_retry(rig, monkeypatch, failure):
    ctl, sup, host = rig; rr_session(monkeypatch)
    request = rr_orphan(ctl, host)
    path = rr_retained_recovery(ctl, host, request)
    original = path.read_bytes(); digest = state.sha256_bytes(original)
    if failure == "partial-absent": host.remove(request["expected_family"][-1]["pid"])
    elif failure == "all-absent":
        for row in request["expected_family"]: host.remove(row["pid"])
    elif failure == "hash": digest = "0" * 64
    elif failure == "owner": request["authorization"]["owner_session_hash"] = "0" * 64
    elif failure == "target": request["authorization"]["backend_target"]["slot"] = 2
    elif failure == "signature": request["expected_family"][-1]["signature"] = "Sun Oct 11 01:00:00 2026 other"
    elif failure == "domain":
        value = read_json(ctl.inventory.source); value["server"]["instructions"] = "changed same-path domain"
        atomic_json(ctl.inventory.source, value)
    _, error = captured(lambda: ctl.recover_orphan_backend_stop(1, **request, expected_residual_sha256=digest))
    if failure in {"none", "partial-absent", "all-absent"}:
        assert error is None, repr(error)
        assert not path.exists()
        assert bool(host.signals) == (failure != "all-absent")
    else:
        assert not host.signals, "retry must not signal under changed original authority/hash"
        assert isinstance(error, SlotError) and path.read_bytes() == original


@pytest.mark.parametrize("failure", ["none", "unpaired", "wrong-owner", "pin", "opposing-backend", "state-root", "number", "active", "dirty", "worktree", "retry-authority", "owner-domain"], ids=str)
def test_rr2_paired_lease_authority(host, downstream_repo, monkeypatch, failure):
    owner, target, _, _ = downstream_repo; rr_session(monkeypatch)
    request = rr_orphan(target, host, owner=owner)
    lease_path = owner.inventory.lease_path(1)
    residual = None
    if failure in {"retry-authority", "owner-domain"}:
        residual = rr_retained_recovery(target, host, request)
        if failure == "retry-authority":
            request["authorization"]["lease_owner"]["inventory_source"] += "-other"
        else:
            value = read_json(owner.inventory.source); value["server"]["instructions"] = "changed owner domain"
            atomic_json(owner.inventory.source, value)
    if failure == "unpaired":
        value = json.loads(owner.inventory.source.read_text()); value.pop("paired_dependency")
        owner.inventory.source.write_text(json.dumps(value))
    elif failure == "wrong-owner":
        value = read_json(lease_path); value["owner_session_hash"] = "0" * 64; atomic_json(lease_path, value)
        request["authorization"] = rr_authorization(target, owner=owner)
    elif failure == "pin":
        value = read_json(lease_path); value["public_dependency_sha"] = "0" * 40; atomic_json(lease_path, value)
        request["authorization"] = rr_authorization(target, owner=owner)
    elif failure == "opposing-backend":
        host.add(960001, " ".join(Supervisor(owner.inventory).backend_command(1)), ppid=1, port=29301)
    elif failure == "state-root": request["authorization"]["lease_owner"]["state_root"] += "-other"
    elif failure == "number": request["authorization"]["lease_owner"]["slot"] = 2
    elif failure == "active":
        value = read_json(lease_path); value["state"] = "ACTIVE"; atomic_json(lease_path, value)
        request["authorization"] = rr_authorization(target, owner=owner)
    elif failure == "dirty": (owner.inventory.worktree(1) / "preserve.txt").write_text("unabsorbed")
    elif failure == "worktree":
        value = read_json(lease_path); value["worktree"] += "-other"; atomic_json(lease_path, value)
        request["authorization"] = rr_authorization(target, owner=owner)
    before = lease_path.read_bytes()
    retry = {"expected_residual_sha256": state.sha256_bytes(residual.read_bytes())} if residual else {}
    _, error = captured(lambda: target.recover_orphan_backend_stop(1, **request, **retry))
    if failure == "none":
        assert error is None, repr(error)
        assert host.signals and not target.inventory.process_path("backend", 1).exists()
        assert not owner.inventory.process_path("backend", 1).exists()
    else:
        assert not host.signals, "foreign/unpaired/invalid owner cannot authorize target signals"
        assert isinstance(error, SlotError)
    assert lease_path.read_bytes() == before, "recovery must preserve the actual owner's lease"
    assert not host.launches


def test_rr2_lock_and_no_lifecycle_expansion(rig, monkeypatch, capsys):
    ctl, sup, host = rig; rr_session(monkeypatch)
    request = rr_orphan(ctl, host)
    locks = ctl.inventory.state_root / "locks"
    def before(pid):
        assert (locks / "wt1.lock").is_dir() and (locks / "supervisor.lock").is_dir()
        assert len(list(locks.iterdir())) == 2, "one physical slot lock then one lifecycle lock"
    host.before_signal = before
    _, error = captured(lambda: ctl.recover_orphan_backend_stop(1, **request))
    assert error is None, repr(error)
    assert not host.launches and not list(locks.iterdir())
    assert not ctl.inventory.lease_path(1).exists()
    effects = forbidden_counts(host)
    for verb in ("start", "stop", "status"):
        code, error = captured(lambda verb=verb: cli.main(["supervisor", verb, "--slot", "1"]))
        assert error is None and code == 2
        assert "are global; --slot is only valid for probe" in capsys.readouterr().err
        assert forbidden_counts(host) == effects


@pytest.mark.parametrize("shape", ["live-child", "terminal-parent"], ids=str)
def test_rr1_final_observed_parent_guard(rig, monkeypatch, shape):
    _, sup, host = rig
    if shape == "terminal-parent":
        path, root, target, child, _ = rr_managed_zombie(sup, host)
    else:
        root, target = 970030, 970010
        path = owned(sup, host, "backend", 1, root)
        host.add(target, "generic exact child", ppid=root)
    real_sync, real_run = os.fsync, subprocess.run
    directory_writes = 0
    native_reads = 0
    drifted = False
    def sync(fd):
        nonlocal directory_writes
        if state.stat.S_ISDIR(os.fstat(fd).st_mode):
            directory_writes += 1
        real_sync(fd)
    def observe(argv, **kwargs):
        nonlocal native_reads, drifted
        if (directory_writes >= 2 and argv[:3] == ["ps", "-p", str(target)] and
                "stat=" in " ".join(argv)):
            native_reads += 1
            if native_reads == 1:
                # Batched classification has a multi-PID selection; this individual
                # native read is the final target seam after post-write classification.
                host.rows[target] = (1, *host.rows[target][1:]); drifted = True
        return real_run(argv, **kwargs)
    monkeypatch.setattr(os, "fsync", sync); monkeypatch.setattr(subprocess, "run", observe)
    _, error = captured(lambda: sup.stop_backend(1))
    assert drifted, "RR final parent control reached the intended native seam"
    assert not host.signals, "RR final observed parent drift forbids every signal"
    assert isinstance(error, SlotError) and path.exists()
    assert sup._metadata("backend", 1)["pid"] == root


@pytest.mark.parametrize("shape", ["at-bound", "retained-plus-root", "discovered-with-absent"], ids=str)
def test_rr1_combined_family_bound(rig, shape):
    _, sup, host = rig
    root = 971001
    path = owned(sup, host, "backend", 1, root)
    data = read_json(path)
    count = 4096 if shape == "retained-plus-root" else 4095
    data["descendants"] = [{"pid": 1100000 + n, "signature": "Sun Oct 11 00:00:00 2026 retained absent worker"}
                           for n in range(count)]
    atomic_json(path, data)
    if shape == "discovered-with-absent": host.add(971002, "new owned child", ppid=root)
    original = path.read_bytes()
    def before(pid):
        persisted = sup._metadata("backend", 1)
        assert len(persisted["descendants"]) <= 4096, "RR combined retained identity bound before native effect"
        retained = {(row["pid"], row["signature"]) for row in data["descendants"]}
        assert retained <= {(row["pid"], row["signature"]) for row in persisted["descendants"]}
    host.before_signal = before
    _, error = captured(lambda: sup.stop_backend(1))
    if shape == "at-bound":
        assert error is None, repr(error)
        assert host.signals == [(root, signal.SIGTERM)] and not path.exists()
    else:
        assert not host.signals and path.read_bytes() == original, "RR over-bound family preserves original record without effects"
        assert isinstance(error, SlotError)


@pytest.mark.parametrize("mode", ["free", "same-role", "paired"], ids=str)
def test_rr2_pending_lease_authority(host, downstream_repo, monkeypatch, mode):
    down, target, _, _ = downstream_repo; rr_session(monkeypatch)
    owner = down if mode == "paired" else target if mode == "same-role" else None
    request = rr_orphan(target, host, owner=owner)
    record = rr_retained_recovery(target, host, request)
    original = record.read_bytes(); lease_path = target.inventory.lease_path(1)
    lease_before = lease_path.read_bytes() if lease_path.exists() else None
    before = forbidden_counts(host)
    if mode == "free":
        operation = lambda: target.acquire(1, client="codex", base_ref="main")
    else:
        operation = lambda: owner.release(1)
    _, error = captured(operation)
    after = lease_path.read_bytes() if lease_path.exists() else None
    assert after == lease_before, "RR pending recovery preserves exact original lease presence and bytes"
    assert record.read_bytes() == original and forbidden_counts(host) == before
    assert isinstance(error, SlotError)
    target.recover_orphan_backend_stop(1, **request, expected_residual_sha256=state.sha256_bytes(original))
    assert not record.exists() and (lease_path.read_bytes() if lease_path.exists() else None) == lease_before
    if mode == "free":
        target.acquire(1, client="codex", base_ref="main")
        assert lease_path.exists()
    elif mode == "same-role":
        owner.release(1)
        assert not lease_path.exists()


@pytest.mark.parametrize("lock", ["wt1.lock", "supervisor.lock"], ids=str)
def test_rr2_real_lock_contention(rig, monkeypatch, lock):
    ctl, _, host = rig; rr_session(monkeypatch)
    request = rr_orphan(ctl, host)
    path = ctl.inventory.state_root / "locks" / lock
    with state.directory_lock(path, purpose="independent held lock"):
        witness = {str(p): p.read_bytes() for p in path.iterdir() if p.is_file()}
        _, error = captured(lambda: ctl.recover_orphan_backend_stop(1, **request))
        assert isinstance(error, SlotError) and not host.signals and not host.launches
        assert path.is_dir() and {str(p): p.read_bytes() for p in path.iterdir() if p.is_file()} == witness
        assert not ctl.inventory.process_path("backend", 1).exists()
    ctl.recover_orphan_backend_stop(1, **request)
    assert host.signals and not ctl.inventory.process_path("backend", 1).exists()


@pytest.mark.parametrize("failure", ["write", "flush", "interruption"], ids=str)
def test_rr2_publication_io_failure(rig, monkeypatch, failure):
    ctl, _, host = rig; rr_session(monkeypatch)
    request = rr_orphan(ctl, host)
    real_open = os.fdopen
    class Stream:
        def __init__(self, stream): self.stream = stream
        def __enter__(self): self.stream.__enter__(); return self
        def __exit__(self, *args): return self.stream.__exit__(*args)
        def write(self, value):
            if failure == "write": raise OSError("isolated recovery write failure")
            return self.stream.write(value)
        def flush(self):
            if failure == "flush": raise OSError("isolated recovery flush failure")
            if failure == "interruption": raise KeyboardInterrupt("isolated publication interruption")
            return self.stream.flush()
        def fileno(self): return self.stream.fileno()
    def fdopen(fd, mode, *args, **kwargs):
        stream = real_open(fd, mode, *args, **kwargs)
        return Stream(stream) if mode == "wb" else stream
    with monkeypatch.context() as patch:
        patch.setattr(os, "fdopen", fdopen)
        error = None
        try:
            ctl.recover_orphan_backend_stop(1, **request)
        except BaseException as exc:
            error = exc
    assert isinstance(error, KeyboardInterrupt if failure == "interruption" else SlotError)
    assert not host.signals and not host.launches, "RR publication failure has no native effects"
    assert not ctl.inventory.process_path("backend", 1).exists()
    assert not list((ctl.inventory.state_root / "processes").glob(".*.json.*"))
    ctl.recover_orphan_backend_stop(1, **request)
    assert host.signals


def test_rr2_legacy_release_warning(rig, monkeypatch, capsys):
    ctl, sup, host = rig; rr_session(monkeypatch)
    config = read_json(ctl.inventory.source); config["server"]["backend_policy"] = "leased"
    atomic_json(ctl.inventory.source, config)
    ctl = Controller(Inventory.load(ctl.inventory.source)); sup = Supervisor(ctl.inventory)
    ctl.acquire(1, client="codex", base_ref="main")
    path = owned(sup, host, "backend", 1, 972001)
    original = path.read_bytes(); host.denied_pids.add(972001)
    ctl.release(1)
    assert not ctl.inventory.lease_path(1).exists()
    assert path.read_bytes() == original and not host.signals
    assert "resource remains reserved" in capsys.readouterr().err
    assert 1 in sup.capacity_census()["reserved_physical_slots"]
    host.denied_pids.clear(); sup.stop_backend(1)
    assert not path.exists() and host.signals == [(972001, signal.SIGTERM)]


@pytest.mark.parametrize("origin", [None, True, False, "", "unknown", "operator_stop_only"],
                         ids=["null", "true", "false", "blank", "unknown", "incomplete-stop-only"])
def test_rr2_optional_origin_is_not_legacy(rig, monkeypatch, origin):
    ctl, sup, host = rig; rr_session(monkeypatch)
    path = owned(sup, host, "backend", 1, 973001)
    legacy = read_json(path); corrupt = dict(legacy); corrupt["record_origin"] = origin
    atomic_json(path, corrupt); original = path.read_bytes()
    assert sup.process_state("backend", 1) == "unavailable", "RR explicit malformed origin is never legacy"
    assert 1 in sup.capacity_census()["reserved_physical_slots"]
    for operation in (lambda: ctl.acquire(1, client="codex", base_ref="main"), lambda: sup.stop_backend(1)):
        _, error = captured(operation)
        assert isinstance(error, SlotError) and not host.signals and not host.launches
        assert path.read_bytes() == original and not ctl.inventory.lease_path(1).exists()
    atomic_json(path, legacy)
    ctl.acquire(1, client="codex", base_ref="main")
    assert ctl.inventory.lease_path(1).exists()
    sup.stop_backend(1)
    assert host.signals == [(973001, signal.SIGTERM)] and not path.exists()


def test_rr2_reverse_paired_physical_reservation(host, downstream_repo, monkeypatch):
    target, public, _, _ = downstream_repo; rr_session(monkeypatch)
    request = rr_orphan(target, host)
    record = rr_retained_recovery(target, host, request); original = record.read_bytes()
    _, error = captured(lambda: public.acquire(1, client="codex", base_ref="main"))
    assert not public.inventory.lease_path(1).exists(), "RR reverse paired reservation preserves original FREE authority"
    assert isinstance(error, SlotError) and record.read_bytes() == original
    assert not host.signals and not host.launches
    target.recover_orphan_backend_stop(1, **request, expected_residual_sha256=state.sha256_bytes(original))
    assert not record.exists()
    public.acquire(1, client="codex", base_ref="main")
    assert public.inventory.lease_path(1).exists()


# R4: production shutdown with asynchronous external OS observations and real JSON.
def rr4_live_family(sup, host, count=5):
    pids = [980050, 980010, 980060, 980020, 980040, 980030][:count]
    path = owned(sup, host, "backend", 1, pids[0])
    for parent, pid in zip(pids, pids[1:]):
        host.add(pid, f"generic owned child {pid}", ppid=parent)
    return path, pids, {pid: host.rows[pid] for pid in pids}


@pytest.mark.parametrize("count", [5, 6], ids=["five", "six"])
def test_rr4_transient_exit_progress_and_cost(rig, count):
    _, sup, host = rig
    path, pids, originals = rr4_live_family(sup, host, count)
    host.ps_cost = 0.035  # Pilot-informed synthetic schedule; not a native guarantee.
    start_calls = len(host.ps_calls)
    def after(pid):
        if pid == pids[-1]:
            host.rows[pid] = originals[pid]
            def disappear():
                host.remove(pid); host.after_census = None
            host.after_census = disappear
    host.after_signal = after
    def before(pid):
        data = read_json(path)
        assert {row["pid"]: row["signature"] for row in data["descendants"]} == {
            key: value[2] for key, value in originals.items()}, "RR4 original identities survive every exit"
        assert host.native_states.get(pid, "S") != "Z", "RR4 no zombie signal"
    host.before_signal = before
    _, error = captured(lambda: sup.stop_backend(1))
    assert error is None, "RR4 transient exit resumes exact live parents: " + repr(error)
    assert [pid for pid, _ in host.signals] == list(reversed(pids)), "RR4 transient exit resumes exact live parents"
    assert not path.exists() and not (set(pids) & host.rows.keys()), "RR4 actual whole-family absence precedes unregister"
    assert host.clock <= 10.00001 and len(host.ps_calls) - start_calls < 180, "RR4 populated stop respects synthetic cost and fixed deadline"


def test_rr4_nested_terminal_progress(rig):
    _, sup, host = rig
    path, pids, originals = rr4_live_family(sup, host, 4)
    root, parent, intermediate, leaf = pids
    def zombie(pid):
        host.rows[pid] = (originals[pid][0], "<defunct>", "Sun Oct 11 00:00:00 2026 <defunct>")
        host.native_states[pid] = "Z"
    def after(pid):
        if pid == leaf:
            zombie(leaf); zombie(intermediate)
        elif pid == parent:
            host.remove(intermediate)
    host.after_signal = after
    slept = []
    def reap():
        slept.append(True)
        assert [pid for pid, _ in host.signals] == [leaf], "RR4 unqualified nested terminal blocks every parent signal"
        host.remove(leaf); host.after_sleep = None
    host.after_sleep = reap
    host.before_signal = lambda pid: (host.native_states.get(pid) != "Z") or pytest.fail("RR4 no zombie signal")
    _, error = captured(lambda: sup.stop_backend(1))
    assert error is None, repr(error)
    assert slept and [pid for pid, _ in host.signals] == [leaf, parent, root], "RR4 terminal ancestry becomes eligible only after deeper absence"
    assert not path.exists()


@pytest.mark.parametrize("failure", ["reparented", "mismatch", "denied", "root-absent", "nested-terminal"], ids=str)
def test_rr4_persistent_exit_refusal(rig, failure):
    _, sup, host = rig
    path, pids, originals = rr4_live_family(sup, host, 4)
    root, parent, intermediate, leaf = pids
    def after(pid):
        assert pid == leaf, "RR4 persistent unqualified family forbids additional signals"
        if failure == "root-absent": host.remove(root)
        elif failure == "denied": host.denied_pids.add(leaf)
        elif failure == "mismatch": host.add(leaf, "unrelated replacement", ppid=intermediate)
        else:
            host.rows[leaf] = (1 if failure == "reparented" else intermediate, "<defunct>", "Sun Oct 11 00:00:00 2026 <defunct>")
            host.native_states[leaf] = "Z"
            if failure == "nested-terminal":
                host.rows[intermediate] = (parent, "<defunct>", "Sun Oct 11 00:00:00 2026 <defunct>")
                host.native_states[intermediate] = "Z"
    host.after_signal = after
    _, error = captured(lambda: sup.stop_backend(1))
    assert [pid for pid, _ in host.signals] == [leaf], "RR4 persistent unqualified family forbids additional signals"
    assert isinstance(error, SlotError) and "post-SIGTERM" in str(error) and path.exists()
    assert host.clock <= 10.00001 and error.observations
    assert {row["pid"]: row["signature"] for row in read_json(path)["descendants"]} == {
        key: value[2] for key, value in originals.items()}


@pytest.mark.parametrize("boundary", ["persistence", "signal"], ids=str)
def test_rr4_batch_not_reused_across_effects(rig, monkeypatch, boundary):
    _, sup, host = rig
    path, pids, _ = rr4_live_family(sup, host, 3)
    root, parent, leaf = pids
    changed = []
    if boundary == "signal":
        def after(pid):
            host.rows[parent] = (1, *host.rows[parent][1:]); changed.append(True)
        host.after_signal = after
    else:
        real_sync = os.fsync
        writes = 0
        def sync(fd):
            nonlocal writes
            real_sync(fd)
            if state.stat.S_ISDIR(os.fstat(fd).st_mode):
                writes += 1
                if writes == 2:
                    host.rows[parent] = (1, *host.rows[parent][1:]); changed.append(True)
        monkeypatch.setattr(os, "fsync", sync)
    _, error = captured(lambda: sup.stop_backend(1))
    assert changed and isinstance(error, SlotError) and path.exists()
    expected = [leaf] if boundary == "signal" else []
    assert [pid for pid, _ in host.signals] == expected, "RR4 fresh family evidence after every effect forbids drifted ancestry"


@pytest.mark.parametrize("failure", ["malformed", "denied", "missing-observer", "partial-selected", "extra-selected", "duplicate", "output-bound", "row-bound", "cross-format", "selected-census", "returncode", "stderr"], ids=str)
def test_rr4_batch_refusal(rig, monkeypatch, failure):
    _, sup, host = rig
    path, pids, originals = rr4_live_family(sup, host, 3)
    real_run = subprocess.run
    injected = []
    def observe(argv, **kwargs):
        batch = argv[0] == "ps" and "-p" in argv and "," in argv[2]
        native_census = argv[:2] == ["ps", "-axo"] and "stat=" in argv[-1]
        target = native_census if failure in {"missing-observer", "cross-format"} else batch
        result = real_run(argv, **kwargs)
        if not target or injected:
            return result
        injected.append(True)
        if failure == "denied": raise PermissionError(errno.EPERM, "batch denied")
        lines = result.stdout.splitlines()
        if failure == "malformed": result.stdout = "bad row\n"
        elif failure == "missing-observer": result.stdout = "\n".join(line for line in lines if int(line.split()[0]) != os.getpid()) + "\n"
        elif failure == "partial-selected": result.stdout = "\n".join(lines[:-1]) + "\n"
        elif failure == "extra-selected": result.stdout += f"999991 1 Sun Oct 11 00:00:00 2026 foreign selected\n"
        elif failure == "duplicate": result.stdout += lines[0] + "\n"
        elif failure == "output-bound": result.stdout = "x" * (state.MAX_OBSERVER_OUTPUT + 1)
        elif failure == "row-bound": result.stdout = "".join(f"{1200000+i} 1 Sun Oct 11 00:00:00 2026 bound row\n" for i in range(state.MAX_CENSUS_ROWS+1))
        elif failure == "cross-format": result.stdout = result.stdout.replace(f"{pids[-1]} {pids[-2]} ", f"{pids[-1]} 1 ")
        elif failure == "selected-census": result.stdout = result.stdout.replace("generic owned child", "changed child")
        elif failure == "returncode": result.returncode = 1
        elif failure == "stderr": result.stderr = "partial output warning"
        return result
    # Initial discovery also uses native censuses; inject only the batch pass.
    started = False
    def gated(argv, **kwargs):
        nonlocal started
        if argv[0] == "ps" and "-p" in argv and "," in argv[2]: started = True
        return observe(argv, **kwargs) if started else real_run(argv, **kwargs)
    monkeypatch.setattr(subprocess, "run", gated)
    before = path.read_bytes()
    _, error = captured(lambda: sup.stop_backend(1))
    assert injected, "RR4 batch refusal reached intended external seam"
    assert not host.signals and path.read_bytes() == before, "RR4 incomplete batch cannot authorize any effect"
    assert isinstance(error, SlotError)


@pytest.mark.parametrize("mode", ["mixed-absence", "all-absent", "zombie", "at-bound", "over-bound", "request-bytes", "selection-bytes"], ids=str)
def test_rr4_batch_identity_and_bounds(rig, mode):
    _, sup, host = rig
    _, pids, originals = rr4_live_family(sup, host, 3)
    identities = {pid: row[2] for pid, row in originals.items()}
    if mode == "mixed-absence": host.remove(pids[-1])
    elif mode == "all-absent":
        for pid in pids: host.remove(pid)
    elif mode == "zombie":
        host.rows[pids[-1]] = (pids[-2], "<defunct>", "Sun Oct 11 00:00:00 2026 <defunct>")
        host.native_states[pids[-1]] = "Z"
    elif mode in {"at-bound", "over-bound"}:
        for pid in range(1200000, 1200000 + (4096 if mode == "at-bound" else 4097) - len(identities)):
            identities[pid] = "Sun Oct 11 00:00:00 2026 absent original"
    elif mode == "request-bytes": identities[pids[0]] = "Sun Oct 11 00:00:00 2026 " + "x" * state.MAX_OBSERVER_OUTPUT
    elif mode == "selection-bytes":
        identities.update({10**100 + i: "Sun Oct 11 00:00:00 2026 absent original" for i in range(1000)})
    before = len(host.ps_calls)
    snapshot, generic, native = state.observe_shutdown_family(identities, pids[0])
    if mode in {"over-bound", "request-bytes", "selection-bytes"}:
        assert snapshot.state == "unavailable" and len(host.ps_calls) == before, "RR4 oversized batch refused before observations"
    else:
        assert snapshot.state == "present" and len(host.ps_calls) - before == 4, "RR4 one classification has exactly four fresh commands"
        assert set(generic) == set(native) == set(identities)
        if mode == "zombie":
            assert generic[pids[-1]].state == "mismatch" and native[pids[-1]].state == "present", "RR4 batch native Z is present not absence"
        else:
            assert all(generic[pid].state == native[pid].state == ("present" if pid in host.rows else "absent") for pid in identities), "RR4 absence requires capable agreement for every retained PID"
        assert all(generic[pid].signature == host.rows[pid][2] for pid in identities if pid in host.rows), "RR4 generic full signatures remain exact"


def test_rr4_first_refusal_survives_deadline(rig, monkeypatch):
    _, sup, host = rig
    path, pids, _ = rr4_live_family(sup, host, 3)
    root, parent, leaf = pids
    real_sync = os.fsync
    writes = 0
    def sync(fd):
        nonlocal writes
        real_sync(fd)
        if state.stat.S_ISDIR(os.fstat(fd).st_mode):
            writes += 1
            if writes == 4:
                # After leaf delivery: pending parent was live before persistence.
                # It now becomes terminal beneath exact live root. Whole-state
                # comparison must refuse this signal and record its precise cause.
                host.rows[parent] = (root, "<defunct>", "Sun Oct 11 00:00:00 2026 <defunct>")
                host.native_states[parent] = "Z"
    monkeypatch.setattr(os, "fsync", sync)
    # Keep the terminal child unresolved after resampling by reparenting it on wait.
    host.after_sleep = lambda: host.rows.update({parent: (1, *host.rows[parent][1:])})
    _, error = captured(lambda: sup.stop_backend(1))
    assert [pid for pid, _ in host.signals] == [leaf], "RR4 first refusal never authorizes another signal"
    assert isinstance(error, SlotError) and path.exists() and host.clock <= 10.00001
    assert "first refusal: post-write classification" in str(error) and "shutdown rooted ancestry changed after durable write" in str(error), "RR4 first transition cause survives the passive deadline"
    assert error.observations and any(row.state == "present" for row in error.observations), "RR4 first typed observations survive final unavailable evidence"


# LA-C1–C12: actual production methods, external Host/OS/clock/IO seams only.
# SOURCE-ONLY author delivery: these controls have NOT been run by the author.
def _la_drift(host, *, once=True):
    pid = host.next_pid
    old = 'Sun Oct 11 00:00:00 2026 isolated earlier creation command'
    host.selected_results[pid] = SimpleNamespace(returncode=0, stdout=old, stderr='')
    if once:
        def after():
            if pid in host.rows:
                host.selected_results.pop(pid, None)
        host.after_census = after
    return pid, old


def _la_record(sup, number=1):
    return read_json(sup.inventory.process_path('backend', number))


def test_la_c1_exact_creation_pair_stabilizes_once(rig):
    _, sup, host = rig
    pid, old = _la_drift(host)
    sup.start_backend(1)
    record = _la_record(sup); v = record['startup_evidence']
    assert len(host.launches) == 1 and record['pid'] == pid
    assert record['signature'] == host.rows[pid][2] != old
    assert v['stage'] == 'complete' and v['creation_attempts'] == 2
    assert v['creation_succeeded'] and v['failure_count'] == 1
    assert v['first_failure_ref'] == v['last_failure_ref'] == 1
    pair = v['failures'][0]['diagnostics']
    assert pair['selected']['operand']['prefix'] == old
    assert pair['census']['operand']['prefix'] == record['signature']
    assert pair['selected']['capable'] and pair['census']['capable']
    assert pair['expected_signature_supplied'] is False
    assert host.launch_reservations[0][0]['phase'] == 'launch_pending'
    assert 'pid' not in host.launch_reservations[0][0]
    assert 'signature' not in host.launch_reservations[0][0]
    state.validate_startup_evidence(record)


def test_la_c2_persistent_drift_consumes_one_bound(rig, monkeypatch):
    _, sup, host = rig
    sup.inventory.raw['server']['startup_timeout_seconds'] = 0.25
    host.ps_cost = 0.02
    pid, _ = _la_drift(host, once=False)
    process_path = sup.inventory.process_path('backend', 1)
    popen, external_run, replace = subprocess.Popen, subprocess.run, state.os.replace
    launches, failed_writes, watchdog = [], [], []
    watching = [True]
    def launch(*args, **kwargs):
        launches.append(host.clock)
        return popen(*args, **kwargs)
    def finite_watchdog():
        # Independent of every emitted deadline. Two rollback ps commands may
        # consume .04 after admission, but resetting admission must still stop.
        if watching[0] and launches and host.clock > launches[0] + 0.25 + 0.04 + 1e-9:
            watchdog.append(host.clock)
            raise AssertionError('external finite startup watchdog exceeded')
    def command(argv, **kwargs):
        finite_watchdog()
        return external_run(argv, **kwargs)
    def write(source, destination):
        if Path(destination) == process_path:
            value = json.loads(Path(source).read_text())
            if value.get('startup_evidence', {}).get('stage') == 'failed':
                failed_writes.append(host.clock)
        return replace(source, destination)
    monkeypatch.setattr(subprocess, 'Popen', launch)
    monkeypatch.setattr(subprocess, 'run', command)
    monkeypatch.setattr(state.os, 'replace', write)
    host.after_sleep = finite_watchdog
    with pytest.raises(SlotError, match='residual retained') as failure:
        sup.start_backend(1)
    watching[0] = False
    v = _la_record(sup)['startup_evidence']
    assert v['stage'] == 'failed' and not v['creation_succeeded']
    assert v['failure_count'] == v['creation_attempts'] >= 2
    assert v['failures'][0]['id'] == 1
    assert v['failures'][-1]['id'] == v['failure_count']
    assert v['updated']['mono'] >= v['effective_deadline']
    assert len(launches) == 1 and v['started']['mono'] == launches[0]
    assert v['configured_seconds'] == 0.25
    assert v['local_deadline'] == launches[0] + 0.25
    assert v['enclosing_deadline'] is None and v['effective_deadline'] == launches[0] + 0.25
    assert launches[0] + 0.25 <= v['terminal']['at']['mono'] <= launches[0] + 0.25 + 1e-9
    assert failed_writes and max(failed_writes) <= launches[0] + 0.25 + 0.04 + 1e-9
    assert not watchdog, 'a reset/enlarged production bound must trip this independent finite oracle'
    assert v['terminal']['error']['error_class'] == 'TimeoutError'
    assert len(failure.value.observations) == 4
    assert failure.value.observations[0].reason == 'selected_census_signature_drift'
    assert failure.value.observations[-2].error_class == 'TimeoutError'
    assert len(host.launches) == 1 and not host.signals
    assert host.handles[0].terminations == 0 and pid in host.rows
    assert 1 in sup.capacity_census()['reserved_physical_slots']


@pytest.mark.parametrize('case', ['selected_denied', 'selected_timeout', 'stderr', 'nonzero',
                                  'malformed', 'missing_target', 'absent', 'duplicate',
                                  'oversized', 'no_observer', 'census_denied'])
def test_la_c3_ineligible_views_never_retry(rig, monkeypatch, case):
    _, sup, host = rig
    pid = host.next_pid; real = host.run
    def external(argv, **kw):
        if argv[0] != 'ps' or pid not in host.rows:
            return real(argv, **kw)
        selected = '-p' in argv and argv[2] == str(pid)
        if selected:
            if case == 'selected_denied': raise PermissionError(errno.EPERM, 'selected denied')
            if case == 'selected_timeout': raise subprocess.TimeoutExpired(argv, kw['timeout'])
            if case == 'stderr': return SimpleNamespace(returncode=0, stdout=host.rows[pid][2], stderr='warning')
            if case == 'nonzero': return SimpleNamespace(returncode=3, stdout='', stderr='')
            if case == 'malformed': return SimpleNamespace(returncode=0, stdout='partial identity', stderr='')
            if case == 'absent':
                host.remove(pid)
                return SimpleNamespace(returncode=1, stdout='', stderr='')
        if '-axo' in argv:
            if case == 'census_denied': raise PermissionError(errno.EPERM, 'census denied')
            value = real(argv, **kw)
            rows = value.stdout.splitlines(keepends=True)
            if case == 'missing_target': rows = [z for z in rows if not z.startswith(str(pid) + ' ')]
            if case == 'no_observer': rows = [z for z in rows if not z.startswith(str(os.getpid()) + ' ')]
            if case == 'duplicate': rows += [z for z in rows if z.startswith(str(pid) + ' ')]
            if case == 'oversized': return SimpleNamespace(returncode=0, stdout='x' * (state.MAX_OBSERVER_OUTPUT + 1), stderr='')
            return SimpleNamespace(returncode=value.returncode, stdout=''.join(rows), stderr=value.stderr)
        return real(argv, **kw)
    monkeypatch.setattr(subprocess, 'run', external)
    with pytest.raises(SlotError): sup.start_backend(1)
    record = _la_record(sup)
    assert record['phase'] != 'running' and len(host.launches) == 1
    assert not host.signals and host.handles[0].terminations == 0
    if 'startup_evidence' in record:
        assert record['startup_evidence']['creation_attempts'] == 1
        assert record['startup_evidence']['failure_count'] <= 1


@pytest.mark.parametrize('during_pair', [False, True])
def test_la_c4_reaped_handle_cannot_adopt_replacement(rig, during_pair):
    _, sup, host = rig
    pid = host.next_pid
    def replace():
        if host.handles and pid in host.rows:
            host.handles[-1].returncode = 0
            host.rows[pid] = (1, 'unrelated replacement', 'Sun Oct 11 00:00:01 2026 unrelated replacement')
    if during_pair:
        host.after_census = replace
    else:
        host.after_poll = lambda handle: replace()
    with pytest.raises(SlotError) as error: sup.start_backend(1)
    record = _la_record(sup)
    assert record['phase'] != 'running' and 'signature' not in record
    assert not host.signals and host.handles[0].terminations == 0
    assert len(host.launches) == 1 and host.rows[pid][1] == 'unrelated replacement'
    assert error.value.__cause__ is not None


@pytest.mark.parametrize('write_stage', ['creation', 'readiness', 'complete'])
def test_la_c5_late_write_only_uses_actual_outer_bound(rig, monkeypatch, write_stage):
    import sys
    _, sup, host = rig
    sup.inventory.raw['server']['startup_timeout_seconds'] = 45
    if write_stage == 'creation': _la_drift(host, once=False)
    path = sup.inventory.process_path('backend', 1)
    replace = state.os.replace; late = []; returned_guards = []
    start = host.clock
    def delayed(source, destination):
        value = json.loads(Path(source).read_text()) if Path(destination) == path else {}
        result = replace(source, destination)
        if not late and value.get('startup_evidence', {}).get('stage') == write_stage:
            # Only this external returned write consumes the remaining bound.
            host.clock = start + 1.1
            late.append(value)
        return result
    def trace(frame, event, arg):
        if event == 'call' and late and frame.f_code.co_name == '_startup_deadline':
            returned_guards.append((frame.f_locals['deadline'], frame.f_back.f_code.co_name))
    monkeypatch.setattr(state.os, 'replace', delayed)
    old_trace = sys.getprofile(); sys.setprofile(trace)
    try:
        with state.observation_budget(1) as outer:
            with pytest.raises(SlotError) as error: sup.start_backend(1)
            assert state._OBSERVATION_DEADLINE.get() == outer
    finally:
        sys.setprofile(old_trace)
    assert state._OBSERVATION_DEADLINE.get() is None
    assert len(late) == 1 and returned_guards[0] == (start + 1, 'publish')
    record = _la_record(sup); v = record['startup_evidence']
    assert v['stage'] == 'failed' and record['phase'] == 'uncertain_residual'
    assert v['terminal']['phase'] == {'creation': 'diagnostic_write', 'readiness': 'signature_write', 'complete': 'running_write'}[write_stage]
    assert v['terminal']['error']['error_class'] == 'TimeoutError'
    assert 'startup admission deadline expired' in str(error.value)
    assert not host.signals and host.handles[0].terminations == 0
    assert len(host.launches) == 1 and 'ACTIVE' not in str(record)


def test_la_c6_same_call_unicode_full_hash_and_supplied_suffix(rig):
    import copy
    import hashlib
    _, _, host = rig
    pid = 899106
    full = 'Sun Oct 11 00:00:00 2026 ' + 'α🙂' * 1500
    other = 'Sun Oct 11 00:00:00 2026 ' + 'β🙂' * 1500
    host.add(pid, other.split('2026 ', 1)[1], signature=other)
    host.selected_results[pid] = SimpleNamespace(returncode=0, stdout=full, stderr='')
    before = len(host.ps_calls); obs = state.observe_process(pid)
    assert len(host.ps_calls) - before == 2
    assert obs.state == 'unavailable' and obs.reason == 'selected_census_signature_drift'
    pair = obs.diagnostics
    assert len((json.dumps(pair, sort_keys=True, indent=2, ensure_ascii=True, allow_nan=False) + '\n').encode()) <= 65536
    for key, original in [('selected', full), ('census', other)]:
        text = pair[key]['operand']
        assert text['utf8_bytes'] == len(original.encode('utf-8'))
        assert text['sha256'] == hashlib.sha256(original.encode('utf-8')).hexdigest()
        assert text['truncated'] and text['hash_scope'] == 'full_unretained'
        assert len(text['prefix'].encode('utf-8')) <= 2048 and original.startswith(text['prefix'])
    supplied = copy.deepcopy(pair)
    supplied['selected']['operand']['sha256'] = '0' * 64
    # Reader cannot verify an unretained suffix; structure is not identity.
    state.validate_process_pair(supplied, obs.reason, obs.state, obs.observed_at)
    assert obs.signature is None and obs.identity is None
    assert 'diagnostics' not in state.Observation('unavailable').as_dict()
    with pytest.raises(ValueError): state.Observation('unavailable', reason='selected_failure')


@pytest.mark.parametrize('failure_stage', ['prelaunch', 'creation', 'readiness', 'complete', 'residual', 'interrupt'])
def test_la_c7_actual_publication_fault_preserves_reservation_or_owned_cleanup(rig, monkeypatch, failure_stage):
    _, sup, host = rig
    if failure_stage in {'creation', 'residual'}:
        _la_drift(host, once=False)
        sup.inventory.raw['server']['startup_timeout_seconds'] = 0.12
    path = sup.inventory.process_path('backend', 1); replace = state.os.replace; failed = []
    def fail(source, destination):
        value = json.loads(Path(source).read_text()) if Path(destination) == path else {}
        stage = value.get('startup_evidence', {}).get('stage')
        match = ((failure_stage == 'prelaunch' and value and stage is None) or
                 failure_stage == stage or
                 (failure_stage == 'residual' and stage == 'failed') or
                 (failure_stage == 'interrupt' and stage == 'readiness'))
        if match:
            failed.append(value)
            if failure_stage == 'interrupt': raise KeyboardInterrupt('isolated write interruption')
            raise PermissionError(errno.EACCES, 'isolated publication fault')
        return replace(source, destination)
    monkeypatch.setattr(state.os, 'replace', fail)
    with pytest.raises((SlotError, PermissionError, KeyboardInterrupt)):
        sup.start_backend(1)
    assert failed and not host.signals
    if failure_stage == 'prelaunch':
        assert not host.launches and not path.exists()
    elif failure_stage in {'creation', 'residual'}:
        assert path.exists() and _la_record(sup)['phase'] != 'running'
        record = _la_record(sup)
        assert 'signature' not in record and host.handles[0].terminations == 0
        state.validate_startup_evidence(record)
        if failure_stage == 'creation':
            v = record['startup_evidence']
            assert v['first_failure_ref'] == 1 and v['terminal']['phase'] == 'diagnostic_write'
            assert v['terminal']['error']['error_class'] == 'PermissionError'
            assert v['terminal']['error']['errno'] == errno.EACCES
            assert v['rollback'] is not None
    else:
        assert len(host.launches) == 1 and host.handles[0].terminations == 1
        assert host.handles[0].waits == [5] and not path.exists()


@pytest.mark.parametrize('seam', ['replace', 'fsync'])
@pytest.mark.parametrize('outcome', ['cleanup', 'residual', 'two-reporting-faults'])
def test_la_c7_each_actual_publication_cause_survives_guarded_cleanup(rig, monkeypatch, seam, outcome):
    _, sup, host = rig
    path = sup.inventory.process_path('backend', 1)
    original = PermissionError(errno.EIO, 'original coherent-write fault')
    first_report = PermissionError(errno.EACCES, 'first reporting fault')
    last_report = OSError(errno.ENOSPC, 'later reporting fault')
    if outcome == 'residual':
        _la_drift(host, once=False)
        sup.inventory.raw['server']['startup_timeout_seconds'] = 0.12
    if outcome == 'two-reporting-faults':
        host.retain_on_terminate = True
    replace, fsync, mkstemp = state.os.replace, state.os.fsync, state.tempfile.mkstemp
    temporary = {}; raised = []; durable = []
    def inspect(source):
        value = json.loads(Path(source).read_text())
        stage = value.get('startup_evidence', {}).get('stage')
        if outcome != 'residual' and stage == 'readiness':
            raised.append(original); durable.append(path.read_bytes()); raise original
        if stage == 'failed':
            fault = last_report if first_report in raised else first_report
            raised.append(fault); durable.append(path.read_bytes()); raise fault
    def allocate(*args, **kwargs):
        fd, name = mkstemp(*args, **kwargs)
        if Path(name).parent == path.parent:
            temporary[fd] = Path(name)
        return fd, name
    def replace_file(source, destination):
        if Path(destination) == path:
            inspect(source)
        return replace(source, destination)
    def sync(fd):
        source = temporary.get(fd)
        if source is not None and source.exists():
            inspect(source)
        return fsync(fd)
    if seam == 'replace':
        monkeypatch.setattr(state.os, 'replace', replace_file)
    else:
        monkeypatch.setattr(state.tempfile, 'mkstemp', allocate)
        monkeypatch.setattr(state.os, 'fsync', sync)
    with pytest.raises(SlotError) as failed:
        sup.start_backend(1)
    error = failed.value; observations = error.observations
    assert not host.signals and len(host.launches) == 1
    if outcome == 'residual':
        assert isinstance(error.__cause__, TimeoutError)
        assert raised == [first_report]
        assert [x.operation for x in observations[-3:]] == ['startup-diagnostic_write', 'rollback_identity', 'residual_write']
        assert observations[-1].error_class == 'PermissionError' and observations[-1].errno == errno.EACCES
        assert observations[-1].detail == str(first_report)
        assert host.handles[0].terminations == 0 and not host.handles[0].waits
    else:
        assert error.__cause__ is original, 'the exact original startup exception remains the cause'
        assert observations[0].error_class == 'PermissionError' and observations[0].errno == errno.EIO
        assert observations[0].detail == str(original) and observations[0].operation == 'startup-signature_write'
        assert observations[1].operation == 'rollback-diagnostic-write'
        assert observations[1].error_class == 'PermissionError' and observations[1].errno == errno.EACCES
        assert observations[1].detail == str(first_report)
        assert host.handles[0].terminations == 1 and host.handles[0].waits == [5]
        if outcome == 'cleanup':
            assert raised == [original, first_report] and len(observations) == 2
            assert not path.exists() and host.handles[0].pid not in host.rows
        else:
            assert raised == [original, first_report, last_report]
            assert len(observations) == 4
            assert observations[2].operation == 'rollback_wait' and observations[2].error_class == 'TimeoutExpired'
            assert observations[3].operation == 'residual_write'
            assert observations[3].error_class == 'OSError' and observations[3].errno == errno.ENOSPC
            assert observations[3].detail == str(last_report)
            assert host.handles[0].pid in host.rows
    if outcome != 'cleanup':
        assert path.read_bytes() == durable[0] == durable[-1], 'failed writes preserve the earlier durable reservation'
        assert _la_record(sup)['phase'] != 'running'
        assert 1 in sup.capacity_census()['reserved_physical_slots']


@pytest.mark.parametrize('seam', ['replace', 'fsync'])
@pytest.mark.parametrize('wait_failure', [False, True])
@pytest.mark.parametrize('reporting', [None, 'interrupt', 'exit'])
def test_la_c7_census_cause_precedes_wait_and_reporting_causes(rig, monkeypatch, seam, wait_failure, reporting):
    _, sup, host = rig
    path = sup.inventory.process_path('backend', 1)
    original = PermissionError(errno.EIO, 'original readiness publication')
    census = PermissionError(errno.EPERM, 'actual rollback census denial')
    early = KeyboardInterrupt('early reporting interruption') if reporting == 'interrupt' else SystemExit('early reporting exit')
    late = SystemExit('late reporting exit') if reporting == 'interrupt' else KeyboardInterrupt('late reporting interruption')
    replace, fsync, mkstemp = state.os.replace, state.os.fsync, state.tempfile.mkstemp
    temporary, attempts, durable = {}, [], []
    host.retain_on_terminate = wait_failure
    def inspect(source):
        value = json.loads(Path(source).read_text())
        stage = value.get('startup_evidence', {}).get('stage')
        if stage == 'readiness':
            durable.append(path.read_bytes())
            host.census_result = census
            raise original
        if stage == 'failed':
            attempts.append(value)
            if reporting:
                raise early if len(attempts) == 1 else late
    def allocate(*args, **kwargs):
        fd, name = mkstemp(*args, **kwargs)
        if Path(name).parent == path.parent:
            temporary[fd] = Path(name)
        return fd, name
    def replace_file(source, destination):
        if Path(destination) == path:
            inspect(source)
        return replace(source, destination)
    def sync(fd):
        source = temporary.get(fd)
        if source is not None and source.exists():
            inspect(source)
        return fsync(fd)
    if seam == 'replace':
        monkeypatch.setattr(state.os, 'replace', replace_file)
    else:
        monkeypatch.setattr(state.tempfile, 'mkstemp', allocate)
        monkeypatch.setattr(state.os, 'fsync', sync)
    with pytest.raises(SlotError, match='residual retained') as failed:
        sup.start_backend(1)
    observations = failed.value.observations
    assert failed.value.__cause__ is original
    assert observations[0].operation == 'startup-signature_write'
    assert observations[0].error_class == 'PermissionError' and observations[0].errno == errno.EIO
    assert observations[0].detail == str(original)
    assert observations[1].operation == 'rollback_census'
    assert observations[1].error_class == 'PermissionError' and observations[1].errno == errno.EPERM
    assert observations[1].detail == str(census)
    expected = ['startup-signature_write', 'rollback_census']
    if reporting:
        expected.append('rollback-diagnostic-write')
        assert observations[2].error_class == type(early).__name__ and observations[2].detail == str(early)
    if wait_failure:
        expected.append('rollback_wait')
        wait = next(x for x in observations if x.operation == 'rollback_wait')
        assert wait.error_class == 'TimeoutExpired' and wait.errno is None
        assert 'timed out after 5 seconds' in wait.detail
    if reporting:
        expected.append('residual_write')
        assert observations[-1].error_class == type(late).__name__ and observations[-1].detail == str(late)
    assert [x.operation for x in observations] == expected, 'no deferred re-raise duplicate or lost later cause'
    assert len(attempts) == 2 and len(durable) == 1
    for value in attempts:
        rollback = value['startup_evidence']['rollback']
        assert rollback['phase'] == 'rollback_census'
        assert rollback['error']['error_class'] == 'PermissionError' and rollback['error']['errno'] == errno.EPERM
        assert rollback['error']['message']['prefix'] == str(census)
        state.validate_startup_evidence(value)
    assert not host.signals and len(host.launches) == 1
    assert host.handles[0].terminations == 1 and host.handles[0].waits == [5]
    assert (host.handles[0].pid in host.rows) is wait_failure
    if reporting:
        assert path.read_bytes() == durable[0], 'both reporting failures retain the actual earlier reservation'
    else:
        assert _la_record(sup)['phase'] == 'uncertain_residual'
        assert _la_record(sup)['startup_evidence']['rollback']['phase'] == 'rollback_census'
    assert 1 in sup.capacity_census()['reserved_physical_slots']


@pytest.mark.parametrize('seam', ['replace', 'fsync'])
@pytest.mark.parametrize('reporting_failure', [False, True])
@pytest.mark.parametrize('mode', ['identity', 'later-identity', 'child-exit', 'child-remains', 'quiescence'])
def test_la_c7_every_rollback_native_witness_survives(rig, monkeypatch, seam, reporting_failure, mode):
    _, sup, host = rig
    path = sup.inventory.process_path('backend', 1)
    original = PermissionError(errno.EIO, 'original coherent publication')
    native = PermissionError(errno.EPERM, 'actual rollback native refusal')
    later = PermissionError(errno.EBUSY, 'later wrapper selected refusal')
    first_report = PermissionError(errno.EACCES, 'early diagnostic publication refusal')
    last_report = OSError(errno.ENOSPC, 'residual publication refusal')
    pid, child = host.next_pid, host.next_pid + 100
    replace, fsync, mkstemp = state.os.replace, state.os.fsync, state.tempfile.mkstemp
    popen, kill = subprocess.Popen, os.kill
    temporary, writes, durable = {}, [], []
    def after_census():
        if pid not in host.rows:
            host.census_result = native
    def inspect(source):
        value = json.loads(Path(source).read_text())
        stage = value.get('startup_evidence', {}).get('stage')
        if stage == 'readiness':
            durable.append(path.read_bytes())
            if mode == 'identity':
                host.selected_results[pid] = native
            elif mode == 'later-identity':
                host.census_result = native
            elif mode in {'child-exit', 'child-remains'}:
                host.add(child, 'independently populated owned child', ppid=pid)
            else:
                host.after_census = after_census
            raise original
        if stage == 'failed':
            writes.append(value)
            if mode == 'later-identity' and len(writes) == 1:
                host.selected_results[pid] = later
            if reporting_failure:
                raise last_report if value.get('phase') == 'uncertain_residual' else first_report
    def launch(*args, **kwargs):
        handle = popen(*args, **kwargs)
        wait = handle.wait
        def waited(timeout=None):
            result = wait(timeout=timeout)
            if mode == 'child-exit':
                host.selected_results[child] = native
            return result
        handle.wait = waited
        return handle
    def signal_child(target, sig):
        if target == child:
            assert sig == signal.SIGTERM
            host.signals.append((target, sig))  # Real external host retains this owned child.
            return
        return kill(target, sig)
    def allocate(*args, **kwargs):
        fd, name = mkstemp(*args, **kwargs)
        if Path(name).parent == path.parent:
            temporary[fd] = Path(name)
        return fd, name
    def replace_file(source, destination):
        if Path(destination) == path:
            inspect(source)
        return replace(source, destination)
    def sync(fd):
        source = temporary.get(fd)
        if source is not None and source.exists():
            inspect(source)
        return fsync(fd)
    monkeypatch.setattr(subprocess, 'Popen', launch)
    monkeypatch.setattr(os, 'kill', signal_child)
    if seam == 'replace':
        monkeypatch.setattr(state.os, 'replace', replace_file)
    else:
        monkeypatch.setattr(state.tempfile, 'mkstemp', allocate)
        monkeypatch.setattr(state.os, 'fsync', sync)
    with pytest.raises(SlotError, match='residual retained') as failed:
        sup.start_backend(1)
    error = failed.value; observations = error.observations
    assert error.__cause__ is original
    assert observations[0].operation == 'startup-signature_write'
    assert observations[0].error_class == 'PermissionError' and observations[0].errno == errno.EIO
    assert observations[0].detail == str(original)
    expected_phase = {'identity': 'rollback_identity', 'later-identity': 'rollback_census',
                      'child-exit': 'rollback_wait', 'child-remains': 'rollback_wait',
                      'quiescence': 'rollback_quiescence'}[mode]
    if mode == 'child-remains':
        actual = [x for x in observations if x.operation == 'rollback_wait']
        assert any(x.state == 'present' and x.signature == host.rows[child][2] for x in actual)
        assert actual and all(x.error_class is None and x.errno is None for x in actual)
        assert 'rollback descendants remain after bounded wait' in str(error)
    else:
        actual = [x for x in observations if x.operation == expected_phase and x.error_class == 'PermissionError']
        assert len(actual) == 1 and actual[0].errno == errno.EPERM and actual[0].detail == str(native)
        assert actual[0].target and actual[0].observed_at
    if mode == 'later-identity':
        subsequent = [x for x in observations if x.operation == 'rollback_signal']
        assert len(subsequent) == 1 and subsequent[0].error_class == 'PermissionError'
        assert subsequent[0].errno == errno.EBUSY and subsequent[0].detail == str(later)
        assert observations.index(actual[0]) < observations.index(subsequent[0])
        assert 'rollback wrapper identity changed/unavailable' in str(error)
    assert 'rollback contexts:' in str(error), 'native operation and real wrapper context remain independently visible'
    assert 'ps-' in str(error)
    residual = writes[-1]
    assert residual['phase'] == 'uncertain_residual'
    rollback = residual['startup_evidence']['rollback']
    assert rollback['phase'] == expected_phase
    assert rollback['error']['error_class'] == ('SlotError' if mode == 'child-remains' else 'PermissionError')
    assert rollback['error']['errno'] == (None if mode == 'child-remains' else errno.EPERM)
    if mode != 'child-remains':
        assert rollback['error']['message']['prefix'] == str(native)
    state.validate_startup_evidence(residual)
    if reporting_failure:
        assert observations[-1].operation == 'residual_write'
        assert observations[-1].error_class == 'OSError' and observations[-1].errno == errno.ENOSPC
        assert observations[-1].detail == str(last_report)
        assert path.read_bytes() == durable[0], 'all failed reports preserve the actual prior reservation'
    else:
        assert _la_record(sup)['startup_evidence']['rollback'] == rollback
    assert len(host.launches) == 1
    if mode in {'identity', 'later-identity'}:
        assert not host.signals and host.handles[0].terminations == 0 and not host.handles[0].waits
    else:
        assert host.handles[0].terminations == 1 and host.handles[0].waits == [5]
        assert host.signals == ([(child, signal.SIGTERM)] if mode.startswith('child-') else [])
        assert pid not in host.rows
    assert 1 in sup.capacity_census()['reserved_physical_slots']


_LA_BAD_STARTUP = [
    ('null_envelope', ('startup_evidence',), None),
    ('extra_key', ('startup_evidence', 'unexpected'), True),
    ('null_version', ('startup_evidence', 'version'), None),
    ('bool_version', ('startup_evidence', 'version'), True),
    ('future_version', ('startup_evidence', 'version'), 2),
    ('bool_allowance', ('startup_evidence', 'configured_seconds'), True),
    ('nan_allowance', ('startup_evidence', 'configured_seconds'), float('nan')),
    ('inf_deadline', ('startup_evidence', 'effective_deadline'), float('inf')),
    ('wrong_effective', ('startup_evidence', 'effective_deadline'), 999),
    ('wrong_local', ('startup_evidence', 'local_deadline'), 999),
    ('bool_attempt', ('startup_evidence', 'creation_attempts'), True),
    ('negative_count', ('startup_evidence', 'failure_count'), -1),
    ('wrong_count', ('startup_evidence', 'failure_count'), 5),
    ('wrong_stage', ('startup_evidence', 'stage'), 'unknown'),
    ('false_success', ('startup_evidence', 'creation_succeeded'), False),
    ('bool_reference', ('startup_evidence', 'first_failure_ref'), True),
    ('dangling_reference', ('startup_evidence', 'last_failure_ref'), 9),
    ('wrong_token', ('startup_evidence', 'launch_token'), '0' * 32),
    ('null_origin', ('record_origin',), None),
    ('null_recovery', ('recovery',), None),
    ('false_origin', ('record_origin',), 'managed'),
    ('bad_utc', ('startup_evidence', 'started', 'utc'), '2026-02-30T00:00:00Z'),
    ('nonascii_utc', ('startup_evidence', 'started', 'utc'), '２０２６-10-20T00:00:00Z'),
    ('bad_mono', ('startup_evidence', 'updated', 'mono'), -1),
    ('wrong_regression', ('startup_evidence', 'utc_regressed'), True),
    ('pair_extra', ('startup_evidence', 'failures', 0, 'diagnostics', 'unexpected'), 0),
    ('pair_version_bool', ('startup_evidence', 'failures', 0, 'diagnostics', 'version'), True),
    ('pair_pid_bool', ('startup_evidence', 'failures', 0, 'diagnostics', 'pid'), True),
    ('pair_expected', ('startup_evidence', 'failures', 0, 'diagnostics', 'expected_signature_supplied'), True),
    ('bad_reason', ('startup_evidence', 'failures', 0, 'reason'), 'unknown'),
    ('bad_state', ('startup_evidence', 'failures', 0, 'state'), 'present'),
    ('null_selected', ('startup_evidence', 'failures', 0, 'diagnostics', 'selected'), None),
    ('false_capability', ('startup_evidence', 'failures', 0, 'diagnostics', 'selected', 'capable'), False),
    ('bool_rc', ('startup_evidence', 'failures', 0, 'diagnostics', 'selected', 'returncode'), False),
    ('fake_errno', ('startup_evidence', 'failures', 0, 'diagnostics', 'selected', 'errno'), 13),
    ('fake_error', ('startup_evidence', 'failures', 0, 'diagnostics', 'selected', 'error_class'), 'ToolFailure'),
    ('bool_ppid', ('startup_evidence', 'failures', 0, 'diagnostics', 'census', 'target_ppid'), False),
    ('hash', ('startup_evidence', 'failures', 0, 'diagnostics', 'selected', 'operand', 'sha256'), '0' * 64),
    ('scope', ('startup_evidence', 'failures', 0, 'diagnostics', 'selected', 'operand', 'hash_scope'), 'full_unretained'),
    ('surrogate', ('startup_evidence', 'failures', 0, 'diagnostics', 'selected', 'operand', 'prefix'), '\ud800'),
]


def _la_set(value, keys, replacement):
    for key in keys[:-1]: value = value[key]
    value[keys[-1]] = replacement


def _la_bad_record_through_consumers(sup, host, value, name):
    """Independent current-file/effect oracle, not a replacement reader verdict."""
    import copy
    import hashlib
    from seed_journal import seeded_mutation
    path = sup.inventory.process_path('backend', 1)
    original, original_stat = path.read_bytes(), path.stat()
    roots = [sup.inventory.state_root] + [sup.inventory.worktree(n) for n in (1, 2, 3)]
    def disk():
        result = {}
        for root in roots:
            for item in root.rglob('*'):
                if item == path:
                    continue
                st = item.lstat()
                if item.is_symlink():
                    result[str(item)] = ('link', st.st_mode, os.readlink(item))
                elif item.is_file():
                    result[str(item)] = ('file', st.st_mode, st.st_mtime_ns,
                                         hashlib.sha256(item.read_bytes()).hexdigest())
        return result
    before_disk = disk()
    before_effects = (forbidden_counts(host), copy.deepcopy(host.rows), dict(host.ports),
                      [(h.pid, h.returncode, h.terminations, list(h.waits)) for h in host.handles])
    with seeded_mutation(
            path, value if isinstance(value, bytes) else json.dumps(value).encode(),
            reason='LA-C8 invalid record through actual consumers: ' + name) as journal_original:
        assert journal_original == original
        assert path.stat().st_mode == original_stat.st_mode
        bad_bytes = path.read_bytes()
        if not isinstance(value, bytes):
            with pytest.raises(SlotError, match='invalid process record'):
                sup._validate_record(value, 'backend', 1)
        with pytest.raises(SlotError):
            sup._read_metadata('backend', 1)
        status = sup.status()
        assert status['slots'][0]['resources']['backend']['state'] == 'unavailable', name
        assert not status['capacity_complete'] and 1 in status['reserved_physical_slots'], name
        capacity = sup.capacity_census()
        assert not capacity['complete'] and 1 in capacity['reserved_physical_slots'], name
        with pytest.raises(SlotError):
            sup.stop_backend(1)
        assert path.read_bytes() == bad_bytes, name
        assert disk() == before_disk, (name, 'lease/cache/other-file mutation')
        assert (forbidden_counts(host), host.rows, host.ports,
                [(h.pid, h.returncode, h.terminations, list(h.waits)) for h in host.handles]) == before_effects, name
    assert path.read_bytes() == original and path.stat().st_mtime_ns == original_stat.st_mtime_ns
    assert path.stat().st_mode == original_stat.st_mode


def test_la_c8_independent_grammar_reaches_actual_consumers(rig):
    import copy
    from seed_journal import seeded_mutation
    _, sup, host = rig
    _la_drift(host); sup.start_backend(1)
    path = sup.inventory.process_path('backend', 1)
    valid = _la_record(sup); original = path.read_bytes(); original_stat = path.stat()
    state.validate_startup_evidence(valid)
    before = forbidden_counts(host)
    for name, keys, replacement in _LA_BAD_STARTUP:
        value = copy.deepcopy(valid); _la_set(value, keys, replacement)
        with seeded_mutation(
                path, json.dumps(value).encode(),
                reason='LA-C8 independent grammar through actual consumers: ' + name) as journal_original:
            assert journal_original == original
            assert path.stat().st_mode == original_stat.st_mode
            bad_bytes = path.read_bytes()
            with pytest.raises(SlotError, match='invalid process record'):
                sup._validate_record(value, 'backend', 1)
            status = sup.status()
            assert status['slots'][0]['resources']['backend']['state'] == 'unavailable', name
            assert not status['capacity_complete'] and 1 in status['reserved_physical_slots'], name
            with pytest.raises(SlotError): sup.stop_backend(1)
            assert path.read_bytes() == bad_bytes and forbidden_counts(host) == before, name
        assert path.read_bytes() == original and path.stat().st_mtime_ns == original_stat.st_mtime_ns
        assert path.stat().st_mode == original_stat.st_mode
    assert sup.process_state('backend', 1) == 'running'
    # Genuine legacy absence, not null or invalid-field normalization.
    legacy = copy.deepcopy(valid); legacy.pop('startup_evidence')
    assert sup._validate_record(legacy, 'backend', 1) == legacy
    legacy['startup_evidence'] = None
    with pytest.raises(SlotError): sup._validate_record(legacy, 'backend', 1)
    class ObjectSubclass(dict): pass
    v = copy.deepcopy(valid); v['startup_evidence'] = ObjectSubclass(v['startup_evidence'])
    with pytest.raises(ValueError): state.validate_startup_evidence(v)


def test_la_c8_semantic_pairs_refs_and_typed_faults(rig):
    import copy
    import hashlib
    _, sup, host = rig
    _la_drift(host, once=False)
    sup.inventory.raw['server']['startup_timeout_seconds'] = 0.12
    with pytest.raises(SlotError): sup.start_backend(1)
    valid = _la_record(sup); state.validate_startup_evidence(valid)
    cases = []
    for field, bad in [('error_class', ''), ('error_class', 'not a class'), ('errno', True), ('errno', 2**60)]:
        v = copy.deepcopy(valid); v['startup_evidence']['terminal']['error'][field] = bad; cases.append(v)
    for field, bad in [('observation_ref', 99), ('phase', 'rollback_signal'), ('at', {'utc': 'bad', 'mono': 0})]:
        v = copy.deepcopy(valid); v['startup_evidence']['terminal'][field] = bad; cases.append(v)
    v = copy.deepcopy(valid); v['startup_evidence']['failures'].append(copy.deepcopy(v['startup_evidence']['failures'][0])); cases.append(v)
    v = copy.deepcopy(valid); v['startup_evidence']['failures'].reverse(); cases.append(v)
    v = copy.deepcopy(valid); del v['startup_evidence']['rollback']; cases.append(v)
    v = copy.deepcopy(valid); v['startup_evidence']['failures'][0]['diagnostics']['census']['observer_witness'] += 1; cases.append(v)
    # Correct hashes/lengths isolate the full operand strip/parse/equality guards.
    for text in [' Sun Oct 11 00:00:00 2026 leading whitespace', 'not a process signature']:
        v = copy.deepcopy(valid); operand = v['startup_evidence']['failures'][0]['diagnostics']['selected']['operand']
        operand.update(prefix=text, utf8_bytes=len(text.encode()), sha256=hashlib.sha256(text.encode()).hexdigest(), truncated=False, hash_scope='full_retained'); cases.append(v)
    v = copy.deepcopy(valid)
    pair = v['startup_evidence']['failures'][0]['diagnostics']; pair['selected']['operand'] = copy.deepcopy(pair['census']['operand']); cases.append(v)
    for value in cases:
        with pytest.raises(ValueError): state.validate_startup_evidence(value)
        _la_bad_record_through_consumers(sup, host, value, 'existing-semantic-case')
    # Complete actual first and last refusals remain in the original valid object.
    assert valid['startup_evidence']['failures'][0]['id'] == 1
    assert valid['startup_evidence']['terminal']['error']['error_class'] == 'TimeoutError'


def test_la_c8_required_keys_bindings_phases_and_times_reach_actual_consumers(rig):
    import copy
    from seed_journal import journalled
    _, sup, host = rig
    _la_drift(host, once=False)
    sup.inventory.raw['server']['startup_timeout_seconds'] = 0.45
    host.ps_cost = 0.02
    with pytest.raises(SlotError): sup.start_backend(1)
    valid = _la_record(sup)
    state.validate_startup_evidence(valid)
    cases = []
    # Explicit normative key lists; never import private validator key constants.
    required = [
        ((), ['launch_token', 'initiator_pid', 'process_schema_version']),
        (('startup_evidence',), ['version', 'launch_token', 'observer_pid', 'configured_seconds',
         'started', 'local_deadline', 'enclosing_deadline', 'effective_deadline', 'stage',
         'creation_attempts', 'creation_succeeded', 'failure_count', 'failures',
         'first_failure_ref', 'last_failure_ref', 'terminal', 'rollback', 'updated', 'utc_regressed']),
        (('startup_evidence', 'failures', 0), ['id', 'stage', 'attempt', 'state', 'reason', 'observed_at', 'diagnostics']),
        (('startup_evidence', 'failures', 0, 'diagnostics'), ['version', 'pid', 'expected_signature_supplied', 'span', 'selected', 'census']),
    ]
    for probe in ('selected', 'census'):
        keys = ('startup_evidence', 'failures', 0, 'diagnostics', probe)
        required.append((keys, ['operation', 'span', 'state', 'capable', 'returncode', 'error_class',
                               'errno', 'diagnostic', 'operand', 'target_ppid', 'observer_witness']))
        for text in ('operand', 'diagnostic'):
            required.append((keys + (text,), ['prefix', 'utf8_bytes', 'sha256', 'truncated', 'hash_scope']))
        required.append((keys + ('span',), ['start', 'end', 'utc_regressed']))
        for stamp in ('start', 'end'):
            required.append((keys + ('span', stamp), ['utc', 'mono']))
    for fault in ('terminal', 'rollback'):
        required.append((('startup_evidence', fault), ['phase', 'at', 'error', 'observation_ref']))
        required.append((('startup_evidence', fault, 'at'), ['utc', 'mono']))
        required.append((('startup_evidence', fault, 'error'), ['error_class', 'errno', 'message']))
        required.append((('startup_evidence', fault, 'error', 'message'), ['prefix', 'utf8_bytes', 'sha256', 'truncated', 'hash_scope']))
    for stamp in ('started', 'updated'):
        required.append((('startup_evidence', stamp), ['utc', 'mono']))
    required.append((('startup_evidence', 'failures', 0, 'diagnostics', 'span'), ['start', 'end', 'utc_regressed']))
    for stamp in ('start', 'end'):
        required.append((('startup_evidence', 'failures', 0, 'diagnostics', 'span', stamp), ['utc', 'mono']))
    for keys, fields in required:
        for field in fields:
            value = copy.deepcopy(valid); target = value
            for key in keys: target = target[key]
            del target[field]
            cases.append(('missing-' + repr(keys + (field,)), value))
    mutations = [
        ('parent-legacy-version-with-StartupV1', ('process_schema_version',), 1),
        ('initiator-binding', ('initiator_pid',), valid['initiator_pid'] + 1),
        ('observer-binding', ('startup_evidence', 'observer_pid'), valid['initiator_pid'] + 1),
        ('initiator-bool', ('initiator_pid',), True),
        ('observer-bool', ('startup_evidence', 'observer_pid'), True),
        ('count-versus-attempt', ('startup_evidence', 'creation_attempts'), 0),
        ('creation-attempt', ('startup_evidence', 'failures', 0, 'attempt'), 2),
        ('creation-id', ('startup_evidence', 'failures', 0, 'id'), 2),
        ('unknown-failure-stage', ('startup_evidence', 'failures', 0, 'stage'), 'readiness'),
        ('final-without-success', ('startup_evidence', 'failures', -1, 'stage'), 'final'),
        ('false-complete', ('startup_evidence', 'stage'), 'complete'),
        ('false-readiness', ('startup_evidence', 'stage'), 'readiness'),
        ('wrong-parent-phase', ('phase',), 'running'),
        ('negative-enclosing', ('startup_evidence', 'enclosing_deadline'), -1),
        ('bool-enclosing', ('startup_evidence', 'enclosing_deadline'), True),
        ('updated-before-start', ('startup_evidence', 'updated', 'mono'), valid['startup_evidence']['started']['mono'] / 2),
        ('terminal-before-refusal', ('startup_evidence', 'terminal', 'at', 'mono'), valid['startup_evidence']['started']['mono']),
        ('rollback-before-terminal', ('startup_evidence', 'rollback', 'at', 'mono'), valid['startup_evidence']['started']['mono']),
        ('first-pair-outside-start', ('startup_evidence', 'failures', 0, 'diagnostics', 'span', 'start', 'mono'), -1),
        ('last-pair-outside-updated', ('startup_evidence', 'failures', -1, 'diagnostics', 'span', 'end', 'mono'), 1e6),
        ('selected-after-census', ('startup_evidence', 'failures', 0, 'diagnostics', 'selected', 'span', 'end', 'mono'), valid['startup_evidence']['failures'][0]['diagnostics']['census']['span']['start']['mono'] + 0.001),
        ('wrong-observation-utc', ('startup_evidence', 'failures', 0, 'observed_at'), '2026-10-01T00:00:00Z'),
        ('parent-pid-binding', ('pid',), host.handles[0].pid + 1),
        ('last-pid-binding', ('startup_evidence', 'failures', -1, 'diagnostics', 'pid'), host.handles[0].pid + 1),
        ('fault-reference-bool', ('startup_evidence', 'rollback', 'observation_ref'), True),
        ('fault-reference-dropped', ('startup_evidence', 'terminal', 'observation_ref'), 2),
    ]
    for name, keys, replacement in mutations:
        value = copy.deepcopy(valid); _la_set(value, keys, replacement); cases.append((name, value))
    assert valid['startup_evidence']['failure_count'] > 2, 'dropped-middle reference has an actual missing id2'
    for name, value in cases:
        with pytest.raises(ValueError): state.validate_startup_evidence(value)
        _la_bad_record_through_consumers(sup, host, value, name)
    _la_bad_record_through_consumers(sup, host, b'{"startup_evidence":"\xff"}', 'invalid-UTF8-file')
    assert sup._read_metadata('backend', 1)[0] == valid
    truncated = copy.deepcopy(valid)
    operand = truncated['startup_evidence']['failures'][0]['diagnostics']['selected']['operand']
    operand.update(prefix=operand['prefix'][:1], truncated=True, hash_scope='full_unretained', sha256='0' * 64)
    path = sup.inventory.process_path('backend', 1); original = path.read_bytes(); original_stat = path.stat()
    with journalled(path, reason='LA-C8 truncated then legacy actual record readers') as journal_original:
        assert journal_original == original
        path.write_text(json.dumps(truncated))
        assert path.stat().st_mode == original_stat.st_mode
        assert sup._read_metadata('backend', 1)[0] == truncated, 'unretained suffix hash is supplied, not verified'
        legacy = copy.deepcopy(valid); legacy.pop('startup_evidence')
        path.write_text(json.dumps(legacy))
        assert path.stat().st_mode == original_stat.st_mode
        assert sup._read_metadata('backend', 1)[0] == legacy, 'absent legacy field remains accepted'
    assert path.read_bytes() == original and path.stat().st_mtime_ns == original_stat.st_mtime_ns
    assert path.stat().st_mode == original_stat.st_mode


@pytest.mark.parametrize('prior_capture', [False, True])
def test_la_c9_only_prior_capture_enables_narrow_wrapper_cleanup(rig, monkeypatch, prior_capture):
    _, sup, host = rig
    path = sup.inventory.process_path('backend', 1)
    if prior_capture:
        replace = state.os.replace
        def lose_census(source, destination):
            value = json.loads(Path(source).read_text()) if Path(destination) == path else {}
            result = replace(source, destination)
            if value.get('startup_evidence', {}).get('stage') == 'readiness':
                host.census_denied = True
            return result
        monkeypatch.setattr(state.os, 'replace', lose_census)
    else:
        host.after_poll = lambda handle: setattr(host, 'census_denied', True)
    with pytest.raises(SlotError, match='residual retained'): sup.start_backend(1)
    record = _la_record(sup); v = record['startup_evidence']
    assert record['phase'] == 'uncertain_residual'
    assert v['creation_succeeded'] is prior_capture
    assert host.handles[0].terminations == int(prior_capture)
    assert host.handles[0].waits == ([5] if prior_capture else [])
    assert not host.signals and len(host.launches) == 1
    assert 1 in sup.capacity_census()['reserved_physical_slots']
    if prior_capture:
        assert v['terminal']['phase'] == 'final_observation'
        assert v['failures'][-1]['stage'] == 'final'
        assert v['failures'][-1]['diagnostics']['census']['error_class'] == 'PermissionError'
    else:
        assert 'signature' not in record
        assert v['terminal']['phase'] == 'creation'


def test_la_c10_ordinary_owner_reclaim_proxy_and_stop_stay_strict(rig):
    from scripts.lean_slots.proxy import LeaseGate
    ctl, sup, host = rig
    pid = os.getpid()
    old = 'Sun Oct 11 00:00:00 2026 differing owner command'
    host.selected_results[pid] = SimpleNamespace(returncode=0, stdout=old, stderr='')
    calls = len(host.ps_calls); result = state.observe_process(pid)
    assert len(host.ps_calls) - calls == 2 and result.state == 'unavailable'
    assert result.reason == 'selected_census_signature_drift' and result.signature is None
    with pytest.raises(SlotError, match='identity unavailable'): ctl.acquire(1, client='codex', base_ref='main')
    assert ctl.inventory.lease(1, required=False) is None and not host.launches
    host.selected_results.pop(pid)
    ctl.build(); ctl.acquire(1, client='codex', base_ref='main')
    lease = ctl.inventory.lease(1); lease['heartbeat_at'] = '2000-01-01T00:00:00Z'
    ctl.inventory.save_lease(1, lease, touch_heartbeat=False); frozen = ctl.inventory.lease_path(1).read_bytes()
    host.selected_results[pid] = SimpleNamespace(returncode=0, stdout=old, stderr='')
    calls = len(host.ps_calls)
    with pytest.raises(SlotError, match='not confirmed absent'): ctl.reclaim(1)
    assert len(host.ps_calls) - calls == 2 and ctl.inventory.lease_path(1).read_bytes() == frozen
    host.selected_results.pop(pid)
    owned(sup, host, 'proxy', 1, 899110)
    ctl.prepare(1)
    body = json.dumps({'jsonrpc': '2.0', 'id': 1, 'method': 'tools/call', 'params': {'name': 'lean_goal', 'arguments': {}}}).encode()
    gate = LeaseGate(ctl.inventory, 1); gate.authorize('codex', None, body)
    frozen = ctl.inventory.lease_path(1).read_bytes()
    host.selected_results[pid] = SimpleNamespace(returncode=0, stdout=old, stderr='')
    with pytest.raises(SlotError, match='owner'): gate.authorize('codex', None, body)
    assert ctl.inventory.lease_path(1).read_bytes() == frozen
    record = _la_record(sup); record_path = sup.inventory.process_path('backend', 1)
    unchanged = record_path.read_bytes(); before = forbidden_counts(host)
    host.selected_results[record['pid']] = SimpleNamespace(returncode=0, stdout=old, stderr='')
    with pytest.raises(SlotError): sup.stop_backend(1)
    assert record_path.read_bytes() == unchanged and forbidden_counts(host) == before
    assert sup.process_state('backend', 1) == 'unavailable'


def test_la_c11_completed_history_survives_real_stop_park_prepare_release(rig, monkeypatch):
    import copy
    ctl, sup, host = rig
    ctl.build(); ctl.acquire(1, client='codex', base_ref='main')
    owned(sup, host, 'proxy', 1, 899111)
    sup.start_backend(1)
    path = sup.inventory.process_path('backend', 1)
    original = copy.deepcopy(_la_record(sup)['startup_evidence'])
    replace = state.os.replace; ordinary_stop_records = []
    def observe_write(source, destination):
        value = json.loads(Path(source).read_text()) if Path(destination) == path else {}
        if 'shutdown' in value:
            ordinary_stop_records.append(value)
        return replace(source, destination)
    monkeypatch.setattr(state.os, 'replace', observe_write)
    with sup.paused_backend(1):
        assert sup.process_state('backend', 1) == 'down'
    assert ordinary_stop_records
    assert all(row['phase'] == 'running' and row['startup_evidence'] == original for row in ordinary_stop_records)
    # Original stop changes descendants/shutdown, not startup history or phase.
    assert _la_record(sup)['startup_evidence']['stage'] == 'complete'
    ctl.prepare(1)
    assert ctl.inventory.lease(1)['state'] == 'ACTIVE'
    ctl.release(1)
    assert ctl.inventory.lease(1, required=False) is None


def test_la_c11_paired_restore_with_new_startup_records(host, downstream_repo, monkeypatch):
    down, public, _, _ = downstream_repo
    monkeypatch.delenv('LEAN_SLOT_SKIP_SUPERVISOR', raising=False)
    target, previous = Supervisor(down.inventory), Supervisor(public.inventory)
    previous.start_proxy(1); previous.start_backend(1)
    before = read_json(previous.inventory.process_path('backend', 1))
    assert before['startup_evidence']['stage'] == 'complete'
    entered = []
    with target.activating_from(1, previous):
        entered.append('cache work after both roles quiescent')
    assert entered and target.process_state('backend', 1) == 'running'
    target.restore_counterpart(1, previous)
    assert previous.process_state('backend', 1) == 'running'
    assert target.process_state('backend', 1) == 'down'
    assert previous.capacity_census()['complete']
    assert read_json(previous.inventory.process_path('backend', 1))['launch_token'] != before['launch_token']


@pytest.mark.parametrize('bad', [True, False, 0, -1, float('nan'), float('inf'), None, '1'])
def test_la_c12_invalid_allowance_refuses_before_reservation(rig, bad):
    _, sup, host = rig
    sup.inventory.raw['server']['startup_timeout_seconds'] = bad
    calls = len(host.ps_calls)
    with pytest.raises(ValueError): sup.start_backend(1)
    assert not host.launches and not sup.inventory.process_path('backend', 1).exists()
    # Capacity checks can precede _spawn; none may turn invalid T into a launch.
    assert len(host.ps_calls) >= calls


def test_la_c12_default_and_nested_deadline_restore_exactly(rig):
    _, sup, host = rig
    sup.inventory.raw['server'].pop('startup_timeout_seconds')
    sup.start_backend(1)
    v = _la_record(sup)['startup_evidence']
    assert v['configured_seconds'] == 45
    assert v['local_deadline'] == v['started']['mono'] + 45
    assert v['effective_deadline'] == v['local_deadline']
    assert state._OBSERVATION_DEADLINE.get() is None
    start = host.clock
    with state.observation_budget(1) as outer:
        with state.observation_budget(deadline=start + 45) as effective:
            assert effective == outer == start + 1
        assert state._OBSERVATION_DEADLINE.get() == outer
        host.clock = outer + 0.1
        launches = len(host.launches)
        with pytest.raises((SlotError, TimeoutError)):
            sup.start_backend(2)
        assert len(host.launches) == launches
        assert state._OBSERVATION_DEADLINE.get() == outer
    assert state._OBSERVATION_DEADLINE.get() is None


def test_la_c5_controller_cannot_activate_after_late_final_write(rig, monkeypatch):
    ctl, sup, host = rig
    ctl.build(); ctl.acquire(1, client='codex', base_ref='main')
    owned(sup, host, 'proxy', 1, 899115)
    path = sup.inventory.process_path('backend', 1)
    replace = state.os.replace; late = []
    start = host.clock
    def delayed(source, destination):
        value = json.loads(Path(source).read_text()) if Path(destination) == path else {}
        result = replace(source, destination)
        if not late and value.get('startup_evidence', {}).get('stage') == 'complete':
            host.clock = start + 1.1
            late.append(value)
        return result
    monkeypatch.setattr(state.os, 'replace', delayed)
    with state.observation_budget(1) as outer:
        with pytest.raises(SlotError, match='startup admission deadline expired'):
            ctl.prepare(1)
        assert state._OBSERVATION_DEADLINE.get() == outer
    assert len(late) == 1
    assert ctl.inventory.lease(1)['state'] == 'QUARANTINED'
    assert _la_record(sup)['phase'] == 'uncertain_residual'
    assert _la_record(sup)['startup_evidence']['terminal']['phase'] == 'running_write'
    assert not host.signals and host.handles[-1].terminations == 0
