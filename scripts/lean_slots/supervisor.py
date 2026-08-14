"""Deterministic local process lifecycle for fixed-root Lean MCP endpoints."""

from __future__ import annotations

import json
import http.client
import os
import signal
import socket
import subprocess
import sys
import time
from contextlib import contextmanager
from typing import Any, Iterator

from .state import (
    SCHEMA_VERSION,
    Inventory,
    SlotError,
    atomic_json,
    canonical_digest,
    directory_lock,
    now_iso,
    process_matches,
    process_start_signature,
    read_json,
    sha256_bytes,
)


def _port_open(host: str, port: int, timeout: float = 0.15) -> bool:
    try:
        with socket.create_connection((host, port), timeout=timeout):
            return True
    except OSError:
        return False


class Supervisor:
    def __init__(self, inventory: Inventory | None = None):
        self.inventory = inventory or Inventory.load()

    def _metadata(self, kind: str, number: int) -> dict[str, Any] | None:
        path = self.inventory.process_path(kind, number)
        if not path.exists():
            return None
        try:
            return read_json(path)
        except SlotError:
            return None

    def _running(self, kind: str, number: int) -> bool:
        metadata = self._metadata(kind, number)
        return bool(
            metadata
            and process_matches(int(metadata.get("pid", 0)), metadata.get("signature"))
            and metadata.get("runtime_fingerprint")
            == self._runtime_fingerprint(kind, number)
        )

    def _runtime_fingerprint(
        self, kind: str, number: int, command: list[str] | None = None
    ) -> str:
        """Identify the code/config a managed process actually loaded.

        The proxy command line names an inventory file but does not encode the
        selected client-auth mode. Recording the loaded inputs prevents a plain
        ``supervisor start`` from silently reusing a front door that still runs
        an earlier authentication policy or implementation.
        """

        if command is None:
            command = (
                self.proxy_command(number)
                if kind == "proxy"
                else self.backend_command(number)
            )
        sources: dict[str, str] = {}
        if kind == "proxy":
            candidates = [self.inventory.repo_root / "scripts" / "slotctl.py"]
            candidates.extend(
                sorted(
                    (self.inventory.repo_root / "scripts" / "lean_slots").glob("*.py")
                )
            )
            for path in candidates:
                if path.is_file():
                    sources[str(path.relative_to(self.inventory.repo_root))] = (
                        sha256_bytes(path.read_bytes())
                    )
        return canonical_digest(
            {
                "kind": kind,
                "repo_role": self.inventory.repo_role,
                "command": command,
                "server": self.inventory.raw.get("server", {}),
                "slot": self.inventory.slot(number),
                "sources": sources,
            }
        )

    def global_backend_count(self) -> int:
        count = 0
        process_root = self.inventory.state_root / "processes"
        for path in (
            process_root.glob("*-backend.json") if process_root.exists() else []
        ):
            try:
                metadata = read_json(path)
            except SlotError:
                continue
            if metadata.get("kind") == "backend" and process_matches(
                int(metadata.get("pid", 0)), metadata.get("signature")
            ):
                count += 1
        return count

    def global_backend_owners(self, number: int) -> list[str]:
        owners: list[str] = []
        process_root = self.inventory.state_root / "processes"
        for path in (
            process_root.glob("*-backend.json") if process_root.exists() else []
        ):
            try:
                metadata = read_json(path)
            except SlotError:
                continue
            if (
                metadata.get("kind") == "backend"
                and metadata.get("slot") == number
                and process_matches(
                    int(metadata.get("pid", 0)), metadata.get("signature")
                )
            ):
                owners.append(str(metadata.get("repo_role", "unknown")))
        return sorted(owners)

    def _wait_port(self, host: str, port: int, *, open_: bool) -> None:
        timeout = float(self.inventory.raw["server"].get("startup_timeout_seconds", 45))
        deadline = time.monotonic() + timeout
        while time.monotonic() < deadline:
            if _port_open(host, port) is open_:
                return
            time.sleep(0.1)
        expected = "open" if open_ else "close"
        raise SlotError(f"timed out waiting for {host}:{port} to {expected}")

    def _spawn(self, kind: str, number: int, command: list[str], port: int) -> None:
        expected_fingerprint = self._runtime_fingerprint(kind, number, command)
        metadata = self._metadata(kind, number)
        if metadata and process_matches(
            int(metadata.get("pid", 0)), metadata.get("signature")
        ):
            if metadata.get("runtime_fingerprint") != expected_fingerprint:
                raise SlotError(
                    f"managed {kind} wt{number} is running stale code/configuration; "
                    "run supervisor stop, then supervisor start"
                )
            return
        host = str(self.inventory.raw["server"]["host"])
        if _port_open(host, port):
            raise SlotError(
                f"refusing to start {kind} for wt{number}: {host}:{port} is owned by an unknown process"
            )
        log_path = self.inventory.log_path(kind, number)
        log_path.parent.mkdir(parents=True, exist_ok=True)
        environment = os.environ.copy()
        if kind == "backend":
            environment["LEAN_LSP_MCP_TOKEN"] = self.inventory.backend_token(number)
        with log_path.open("ab", buffering=0) as log:
            process = subprocess.Popen(
                command,
                cwd=self.inventory.repo_root,
                env=environment,
                stdin=subprocess.DEVNULL,
                stdout=log,
                stderr=subprocess.STDOUT,
                start_new_session=True,
            )
        deadline = time.monotonic() + float(
            self.inventory.raw["server"].get("startup_timeout_seconds", 45)
        )
        while time.monotonic() < deadline:
            if process.poll() is not None:
                raise SlotError(
                    f"{kind} for wt{number} exited during startup; inspect {log_path}"
                )
            if _port_open(host, port):
                break
            time.sleep(0.1)
        else:
            process.terminate()
            try:
                process.wait(timeout=5)
            except subprocess.TimeoutExpired:
                pass
            raise SlotError(
                f"timed out starting {kind} for wt{number}; inspect {log_path}"
            )
        # uvx may exec the resolved application during startup. Capture identity
        # only after the listening socket is live so later comparisons are stable.
        time.sleep(0.1)
        signature = process_start_signature(process.pid)
        if process.poll() is not None or not signature:
            raise SlotError(
                f"could not establish process identity for {kind} wt{number}"
            )
        atomic_json(
            self.inventory.process_path(kind, number),
            {
                "schema_version": SCHEMA_VERSION,
                "repo_role": self.inventory.repo_role,
                "slot": number,
                "kind": kind,
                "pid": process.pid,
                "signature": signature,
                "command": command,
                "runtime_fingerprint": expected_fingerprint,
                "port": port,
                "started_at": now_iso(),
            },
        )

    def _stop(self, kind: str, number: int, port: int) -> None:
        path = self.inventory.process_path(kind, number)
        metadata = self._metadata(kind, number)
        if metadata is None:
            if _port_open(str(self.inventory.raw["server"]["host"]), port):
                raise SlotError(
                    f"cannot stop unknown process using {kind} port {port} for wt{number}"
                )
            path.unlink(missing_ok=True)
            return
        pid = int(metadata.get("pid", 0))
        if not process_matches(pid, metadata.get("signature")):
            if _port_open(str(self.inventory.raw["server"]["host"]), port):
                raise SlotError(
                    f"PID identity mismatch for {kind} wt{number}; refusing to signal process {pid}"
                )
            path.unlink(missing_ok=True)
            return
        os.kill(pid, signal.SIGTERM)
        deadline = time.monotonic() + 10
        while time.monotonic() < deadline and process_matches(
            pid, metadata.get("signature")
        ):
            time.sleep(0.1)
        if process_matches(pid, metadata.get("signature")):
            raise SlotError(
                f"{kind} wt{number} did not stop after SIGTERM; refusing automatic SIGKILL"
            )
        path.unlink(missing_ok=True)
        self._wait_port(str(self.inventory.raw["server"]["host"]), port, open_=False)

    def backend_command(self, number: int) -> list[str]:
        slot = self.inventory.slot(number)
        server = self.inventory.raw["server"]
        disabled = ",".join(str(item) for item in server["disabled_tools"])
        return [
            *(str(item) for item in server["command"]),
            "--transport",
            "streamable-http",
            "--host",
            str(server["host"]),
            "--port",
            str(slot["backend_port"]),
            "--lean-project-path",
            str(self.inventory.lean_root(number)),
            "--disable-tools",
            disabled,
            "--instructions",
            str(server["instructions"]),
        ]

    def proxy_command(self, number: int) -> list[str]:
        wrapper = self.inventory.repo_root / "scripts" / "slotctl.py"
        return [
            sys.executable,
            str(wrapper),
            "--inventory",
            str(self.inventory.source),
            "_proxy",
            "--slot",
            str(number),
        ]

    def _start_backend_unlocked(self, number: int) -> None:
        slot = self.inventory.slot(number)
        if self._running("backend", number):
            return
        limit = int(self.inventory.raw["max_active_slots"])
        running = self.global_backend_count()
        if running >= limit:
            raise SlotError(
                f"global heavy-backend limit reached ({running}/{limit}); "
                "stop the numbered counterpart before switching repository roles"
            )
        owners = self.global_backend_owners(number)
        if owners:
            raise SlotError(
                f"physical wt{number} already has a heavy backend owned by {owners}"
            )
        # Materialize the private backend credential before exposing the port.
        self.inventory.backend_token(number)
        self._spawn(
            "backend", number, self.backend_command(number), int(slot["backend_port"])
        )

    def _stop_backend_unlocked(self, number: int) -> None:
        self._stop("backend", number, int(self.inventory.slot(number)["backend_port"]))

    def _assert_backend_owned_or_stopped(self, number: int) -> None:
        if self._running("backend", number):
            return
        host = str(self.inventory.raw["server"]["host"])
        port = int(self.inventory.slot(number)["backend_port"])
        if _port_open(host, port):
            raise SlotError(
                f"backend port for {self.inventory.repo_role} wt{number} is owned by "
                "an unknown process"
            )

    def _start_proxy_unlocked(self, number: int) -> None:
        slot = self.inventory.slot(number)
        self._spawn(
            "proxy", number, self.proxy_command(number), int(slot["proxy_port"])
        )

    def _stop_proxy_unlocked(self, number: int) -> None:
        self._stop("proxy", number, int(self.inventory.slot(number)["proxy_port"]))

    @contextmanager
    def lifecycle(self) -> Iterator[None]:
        with directory_lock(
            self.inventory.state_root / "locks" / "supervisor.lock",
            purpose="shared Lean endpoint lifecycle",
        ):
            yield

    def start_backend(self, number: int) -> None:
        with self.lifecycle():
            self._start_backend_unlocked(number)

    def stop_backend(self, number: int) -> None:
        with self.lifecycle():
            self._stop_backend_unlocked(number)

    def start_proxy(self, number: int) -> None:
        with self.lifecycle():
            self._start_proxy_unlocked(number)

    def stop_proxy(self, number: int) -> None:
        with self.lifecycle():
            self._stop_proxy_unlocked(number)

    @contextmanager
    def paused_backend(self, number: int) -> Iterator[None]:
        """Keep one backend stopped across an atomic cache/branch transition.

        Entry requires a healthy PROXY but tolerates a stopped backend: under
        `backend_policy: "leased"` a slot that has only just been acquired legitimately has
        no backend yet, and requiring one here would make `prepare` unreachable — the
        endpoint gate, not a running backend, is what protects the cache swap.

        Exit always leaves a healthy backend, because the caller is about to mark the slot
        ACTIVE and hand it to a worker.
        """
        with self.lifecycle():
            self.assert_proxy_healthy(number)
            if self._running("backend", number):
                self._stop_backend_unlocked(number)
            try:
                yield
            finally:
                if not self._running("backend", number):
                    self._start_backend_unlocked(number)
                self.assert_healthy(number)

    @contextmanager
    def activating_from(self, number: int, counterpart: "Supervisor") -> Iterator[None]:
        """Park a paired backend, mutate the target cache, then activate target.

        The shared lifecycle lock makes the handoff atomic with respect to all
        controller-managed endpoints.  On any failure the previous backend is
        restored before the exception escapes.
        """
        if counterpart.inventory.state_root != self.inventory.state_root:
            raise SlotError(
                "counterpart supervisors must share one runtime state directory"
            )
        with self.lifecycle():
            self._start_proxy_unlocked(number)
            self._assert_backend_owned_or_stopped(number)
            counterpart._assert_backend_owned_or_stopped(number)
            if self._running("backend", number):
                raise SlotError(
                    f"target backend for {self.inventory.repo_role} wt{number} is already running"
                )
            counterpart_was_running = counterpart._running("backend", number)
            if counterpart_was_running:
                counterpart._stop_backend_unlocked(number)
            try:
                yield
                self._start_backend_unlocked(number)
                self.assert_healthy(number)
            except Exception:
                if self._running("backend", number):
                    self._stop_backend_unlocked(number)
                if counterpart_was_running and not counterpart._running(
                    "backend", number
                ):
                    counterpart._start_backend_unlocked(number)
                raise

    def restore_counterpart(self, number: int, counterpart: "Supervisor") -> None:
        """Return one leased slot to its default paired backend without overlap."""
        if counterpart.inventory.state_root != self.inventory.state_root:
            raise SlotError(
                "counterpart supervisors must share one runtime state directory"
            )
        with self.lifecycle():
            target_was_running = self._running("backend", number)
            if target_was_running:
                self._stop_backend_unlocked(number)
            try:
                if not counterpart._running("backend", number):
                    counterpart._start_backend_unlocked(number)
            except Exception:
                if target_was_running and not self._running("backend", number):
                    self._start_backend_unlocked(number)
                raise

    def start(self) -> dict[str, Any]:
        started: list[tuple[str, int]] = []
        with self.lifecycle():
            try:
                for number in (1, 2, 3):
                    if not self._running("proxy", number):
                        self._start_proxy_unlocked(number)
                        started.append(("proxy", number))
                    expected_backend = self.inventory.backend_expected(number)
                    if expected_backend and not self._running("backend", number):
                        self._start_backend_unlocked(number)
                        started.append(("backend", number))
                    elif not expected_backend and self._running("backend", number):
                        self._stop_backend_unlocked(number)
            except Exception:
                for kind, number in reversed(started):
                    slot = self.inventory.slot(number)
                    port = int(slot[f"{kind}_port"])
                    try:
                        self._stop(kind, number, port)
                    except SlotError:
                        pass
                raise
        return self.status()

    def stop(self) -> dict[str, Any]:
        with self.lifecycle():
            for number in (1, 2, 3):
                self._stop_proxy_unlocked(number)
            for number in (1, 2, 3):
                self._stop_backend_unlocked(number)
        return self.status()

    def assert_proxy_healthy(self, number: int) -> None:
        """The front door must be up and running current code; the backend may be down."""
        slot = self.inventory.slot(number)
        host = str(self.inventory.raw["server"]["host"])
        if not self._running("proxy", number) or not _port_open(
            host, int(slot["proxy_port"])
        ):
            raise SlotError(
                f"proxy for wt{number} is not healthy; run slotctl supervisor start"
            )

    def assert_healthy(self, number: int) -> None:
        slot = self.inventory.slot(number)
        host = str(self.inventory.raw["server"]["host"])
        self.assert_proxy_healthy(number)
        if not self._running("backend", number) or not _port_open(
            host, int(slot["backend_port"])
        ):
            raise SlotError(
                f"backend for wt{number} is not healthy; run slotctl supervisor start"
            )

    @staticmethod
    def _sse_json(body: bytes) -> dict[str, Any]:
        for line in body.decode("utf-8").splitlines():
            if line.startswith("data: "):
                value = json.loads(line.removeprefix("data: "))
                if isinstance(value, dict):
                    return value
        value = json.loads(body)
        if not isinstance(value, dict):
            raise SlotError("MCP probe response was not a JSON object")
        return value

    def probe(self, number: int, *, client: str = "codex") -> dict[str, Any]:
        """Exercise initialization, lease gating, and the no-build tool list."""
        self.assert_healthy(number)
        slot = self.inventory.slot(number)
        host = str(self.inventory.raw["server"]["host"])
        headers = {
            "Accept": "application/json, text/event-stream",
            "Content-Type": "application/json",
        }
        if self.inventory.client_auth_mode == "bearer":
            headers["Authorization"] = f"Bearer {self.inventory.token(client)}"

        def request(payload: dict[str, Any], session_id: str | None = None):
            connection = http.client.HTTPConnection(
                host, int(slot["proxy_port"]), timeout=120
            )
            current = dict(headers)
            if session_id:
                current["Mcp-Session-Id"] = session_id
            connection.request(
                "POST",
                f"/mcp?client={client}",
                body=json.dumps(payload),
                headers=current,
            )
            response = connection.getresponse()
            body = response.read()
            response_headers = dict(response.getheaders())
            connection.close()
            if response.status not in {200, 202}:
                raise SlotError(
                    f"MCP probe failed for wt{number} ({response.status}): "
                    f"{body.decode('utf-8', errors='replace')}"
                )
            return (self._sse_json(body) if body else {}), response_headers

        initialized, response_headers = request(
            {
                "jsonrpc": "2.0",
                "id": 1,
                "method": "initialize",
                "params": {
                    "protocolVersion": "2025-06-18",
                    "capabilities": {},
                    "clientInfo": {"name": "slotctl-probe", "version": "1"},
                },
            }
        )
        session_id = next(
            (
                value
                for key, value in response_headers.items()
                if key.lower() == "mcp-session-id"
            ),
            None,
        )
        if not session_id or "result" not in initialized:
            raise SlotError(
                f"MCP initialize response for wt{number} lacked a session/result"
            )
        request(
            {"jsonrpc": "2.0", "method": "notifications/initialized", "params": {}},
            session_id,
        )
        listed, _ = request(
            {"jsonrpc": "2.0", "id": 2, "method": "tools/list", "params": {}},
            session_id,
        )
        tools = [
            str(item.get("name"))
            for item in ((listed.get("result") or {}).get("tools") or [])
            if isinstance(item, dict)
        ]
        if "lean_build" in tools:
            raise SlotError(
                f"MCP worker endpoint wt{number} exposed forbidden lean_build"
            )
        if not any(name.startswith("lean_") for name in tools):
            raise SlotError(f"MCP worker endpoint wt{number} exposed no Lean tools")
        active_dispatch: bool | str = False
        lease = self.inventory.lease(number, required=False)
        if lease and lease.get("state") == "ACTIVE" and lease.get("client") == client:
            diagnostics, _ = request(
                {
                    "jsonrpc": "2.0",
                    "id": 3,
                    "method": "tools/call",
                    "params": {
                        "name": "lean_diagnostic_messages",
                        "arguments": {
                            "file_path": self.inventory.raw["server"]["probe_file"]
                        },
                    },
                },
                session_id,
            )
            if diagnostics.get("error") or "result" not in diagnostics:
                raise SlotError(
                    f"active MCP dispatch failed for wt{number}: {diagnostics}"
                )
            active_dispatch = True
        elif lease:
            active_dispatch = "skipped-nonmatching-lease"
        connection = http.client.HTTPConnection(
            host, int(slot["proxy_port"]), timeout=10
        )
        cleanup_headers = {"Mcp-Session-Id": session_id}
        if self.inventory.client_auth_mode == "bearer":
            cleanup_headers["Authorization"] = headers["Authorization"]
        connection.request("DELETE", f"/mcp?client={client}", headers=cleanup_headers)
        cleanup = connection.getresponse()
        cleanup.read()
        connection.close()
        return {
            "slot": number,
            "repo_role": self.inventory.repo_role,
            "server": initialized["result"].get("serverInfo"),
            "tool_count": len(tools),
            "lean_build_exposed": False,
            "active_dispatch": active_dispatch,
            "cleanup_status": cleanup.status,
        }

    def status(self) -> dict[str, Any]:
        host = str(self.inventory.raw["server"]["host"])
        slots = []
        for number in (1, 2, 3):
            slot = self.inventory.slot(number)
            slots.append(
                {
                    "slot": number,
                    "repo_role": self.inventory.repo_role,
                    "proxy_port": int(slot["proxy_port"]),
                    "backend_port": int(slot["backend_port"]),
                    "proxy_running": self._running("proxy", number)
                    and _port_open(host, int(slot["proxy_port"])),
                    "backend_running": self._running("backend", number)
                    and _port_open(host, int(slot["backend_port"])),
                }
            )
        return {
            "schema_version": SCHEMA_VERSION,
            "global_running_backends": self.global_backend_count(),
            "slots": slots,
        }
