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
from pathlib import Path
from typing import Any

from .state import (
    SCHEMA_VERSION,
    Inventory,
    SlotError,
    atomic_json,
    now_iso,
    process_matches,
    process_start_signature,
    read_json,
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
        )

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
        if self._running(kind, number):
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
            raise SlotError(f"timed out starting {kind} for wt{number}; inspect {log_path}")
        # uvx may exec the resolved application during startup. Capture identity
        # only after the listening socket is live so later comparisons are stable.
        time.sleep(0.1)
        signature = process_start_signature(process.pid)
        if process.poll() is not None or not signature:
            raise SlotError(f"could not establish process identity for {kind} wt{number}")
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
        while time.monotonic() < deadline and process_matches(pid, metadata.get("signature")):
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

    def start_backend(self, number: int) -> None:
        slot = self.inventory.slot(number)
        # Materialize the private backend credential before exposing the port.
        self.inventory.backend_token(number)
        self._spawn("backend", number, self.backend_command(number), int(slot["backend_port"]))

    def stop_backend(self, number: int) -> None:
        self._stop("backend", number, int(self.inventory.slot(number)["backend_port"]))

    def start_proxy(self, number: int) -> None:
        slot = self.inventory.slot(number)
        self._spawn("proxy", number, self.proxy_command(number), int(slot["proxy_port"]))

    def stop_proxy(self, number: int) -> None:
        self._stop("proxy", number, int(self.inventory.slot(number)["proxy_port"]))

    def start(self) -> dict[str, Any]:
        started: list[tuple[str, int]] = []
        try:
            for number in (1, 2, 3):
                if not self._running("backend", number):
                    self.start_backend(number)
                    started.append(("backend", number))
                if not self._running("proxy", number):
                    self.start_proxy(number)
                    started.append(("proxy", number))
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
        for number in (1, 2, 3):
            self.stop_proxy(number)
        for number in (1, 2, 3):
            self.stop_backend(number)
        return self.status()

    def assert_healthy(self, number: int) -> None:
        slot = self.inventory.slot(number)
        host = str(self.inventory.raw["server"]["host"])
        if not self._running("proxy", number) or not _port_open(host, int(slot["proxy_port"])):
            raise SlotError(f"proxy for wt{number} is not healthy; run slotctl supervisor start")
        if not self._running("backend", number) or not _port_open(host, int(slot["backend_port"])):
            raise SlotError(f"backend for wt{number} is not healthy; run slotctl supervisor start")

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
        """Exercise auth, initialization, and the server-side no-build tool list."""
        self.assert_healthy(number)
        slot = self.inventory.slot(number)
        host = str(self.inventory.raw["server"]["host"])
        token = self.inventory.token(client)
        headers = {
            "Authorization": f"Bearer {token}",
            "Accept": "application/json, text/event-stream",
            "Content-Type": "application/json",
        }

        def request(payload: dict[str, Any], session_id: str | None = None):
            connection = http.client.HTTPConnection(host, int(slot["proxy_port"]), timeout=30)
            current = dict(headers)
            if session_id:
                current["Mcp-Session-Id"] = session_id
            connection.request("POST", "/mcp", body=json.dumps(payload), headers=current)
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
            (value for key, value in response_headers.items() if key.lower() == "mcp-session-id"),
            None,
        )
        if not session_id or "result" not in initialized:
            raise SlotError(f"MCP initialize response for wt{number} lacked a session/result")
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
            raise SlotError(f"MCP worker endpoint wt{number} exposed forbidden lean_build")
        if not any(name.startswith("lean_") for name in tools):
            raise SlotError(f"MCP worker endpoint wt{number} exposed no Lean tools")
        connection = http.client.HTTPConnection(host, int(slot["proxy_port"]), timeout=10)
        cleanup_headers = {"Authorization": f"Bearer {token}", "Mcp-Session-Id": session_id}
        connection.request("DELETE", "/mcp", headers=cleanup_headers)
        cleanup = connection.getresponse()
        cleanup.read()
        connection.close()
        return {
            "slot": number,
            "repo_role": self.inventory.repo_role,
            "server": initialized["result"].get("serverInfo"),
            "tool_count": len(tools),
            "lean_build_exposed": False,
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
        return {"schema_version": SCHEMA_VERSION, "slots": slots}
