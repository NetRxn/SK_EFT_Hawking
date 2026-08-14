"""Lease-gated reverse proxy for one fixed, loopback-only Lean endpoint."""

from __future__ import annotations

import hmac
import http.client
import json
import subprocess
from http.server import BaseHTTPRequestHandler, ThreadingHTTPServer
from typing import Any
from urllib.parse import parse_qs, urlsplit

from .state import Inventory, SlotError, token_hash


_DISCOVERY_METHODS = {
    "initialize",
    "notifications/initialized",
    "ping",
    "tools/list",
}
_HOP_HEADERS = {
    "connection",
    "keep-alive",
    "proxy-authenticate",
    "proxy-authorization",
    "te",
    "trailers",
    "transfer-encoding",
    "upgrade",
}


def _messages(body: bytes) -> list[dict[str, Any]]:
    if not body:
        return []
    try:
        value = json.loads(body)
    except (UnicodeDecodeError, json.JSONDecodeError) as exc:
        raise SlotError(f"request body is not valid JSON-RPC: {exc}") from exc
    if isinstance(value, dict):
        return [value]
    if isinstance(value, list) and all(isinstance(item, dict) for item in value):
        return value
    raise SlotError("request body is not a JSON-RPC object or batch")


class LeaseGate:
    def __init__(self, inventory: Inventory, number: int):
        self.inventory = inventory
        self.number = number

    def identify(
        self, authorization: str | None, client_hint: str | None = None
    ) -> tuple[str | None, str | None]:
        if self.inventory.client_auth_mode == "trusted-local":
            if client_hint is None:
                return None, None
            if client_hint not in {"codex", "claude"}:
                raise SlotError(f"unknown local client identity: {client_hint!r}")
            return client_hint, None
        if not authorization or not authorization.startswith("Bearer "):
            raise SlotError("missing bearer credential")
        supplied = authorization.removeprefix("Bearer ").strip()
        clients = self.inventory.state_root / "clients"
        for path in sorted(clients.glob("*.token")) if clients.exists() else []:
            expected = path.read_text(encoding="utf-8").strip()
            if expected and hmac.compare_digest(supplied, expected):
                if client_hint is not None and client_hint != path.stem:
                    raise SlotError("client identity does not match bearer credential")
                return path.stem, token_hash(supplied)
        raise SlotError("unknown or expired bearer credential")

    def authorize(
        self,
        client: str | None,
        supplied_hash: str | None,
        body: bytes,
        *,
        http_method: str = "POST",
    ) -> None:
        messages = _messages(body)
        requires_lease = http_method == "GET"
        for message in messages:
            method = str(message.get("method", ""))
            if method == "tools/call":
                name = str((message.get("params") or {}).get("name", ""))
                if name == "lean_build":
                    raise SlotError("lean_build is disabled for slot workers")
            if method and method not in _DISCOVERY_METHODS:
                requires_lease = True
        if not requires_lease:
            return
        lease = self.inventory.lease(self.number, required=False)
        slot = self.inventory.slot(self.number)
        expected_worktree = str(self.inventory.worktree(self.number))
        if lease is None:
            raise SlotError(f"wt{self.number} has no active lease")
        if lease.get("state") != "ACTIVE":
            raise SlotError(f"wt{self.number} is not active ({lease.get('state')})")
        if client is None or lease.get("client") != client:
            raise SlotError(f"wt{self.number} is leased by another client/session")
        if self.inventory.client_auth_mode == "bearer":
            if supplied_hash is None or not hmac.compare_digest(
                str(lease.get("token_hash", "")), supplied_hash
            ):
                raise SlotError(f"wt{self.number} is leased by another client/session")
        if lease.get("repo_role") != self.inventory.repo_role:
            raise SlotError(f"wt{self.number} repository-role mismatch")
        if lease.get("worktree") != expected_worktree:
            raise SlotError(f"wt{self.number} project-root mismatch")
        if lease.get("endpoint") != slot["endpoint_name"]:
            raise SlotError(f"wt{self.number} endpoint-identity mismatch")
        self._authorize_paired_dependency(lease)

    def _authorize_paired_dependency(self, lease: dict[str, Any]) -> None:
        paired = self.inventory.paired_inventory()
        if paired is None:
            return
        expected_sha = str(lease.get("public_dependency_sha", ""))
        if not expected_sha:
            raise SlotError(
                f"wt{self.number} downstream lease lacks a public dependency SHA"
            )
        expected_root = paired.lean_root(self.number).resolve()
        actual_root = self.inventory.paired_dependency_lean_root(self.number)
        if actual_root != expected_root:
            raise SlotError(f"wt{self.number} paired dependency root changed")
        worktree = paired.worktree(self.number)
        try:
            head = subprocess.run(
                ["git", "rev-parse", "HEAD"],
                cwd=worktree,
                check=False,
                capture_output=True,
                text=True,
            )
            status = subprocess.run(
                ["git", "status", "--porcelain=v1"],
                cwd=worktree,
                check=False,
                capture_output=True,
                text=True,
            )
        except OSError as exc:
            raise SlotError(
                f"wt{self.number} could not audit paired dependency: {exc}"
            ) from exc
        if head.returncode or head.stdout.strip() != expected_sha:
            raise SlotError(f"wt{self.number} paired dependency SHA changed")
        if status.returncode or status.stdout.strip():
            raise SlotError(f"wt{self.number} paired dependency became dirty")


#: Protocol version answered when we reply on the backend's behalf.
_OFFLINE_PROTOCOL_VERSION = "2025-06-18"


def offline_handshake(messages: list[dict[str, Any]]) -> dict[str, Any] | None:
    """A local reply for MCP handshake traffic when the slot has no backend, else None.

    A client opens every endpoint in its configuration at startup, long before any slot is
    leased. Answering 503 to `initialize` is therefore wrong on principle — the backend is a
    DISPATCH-time resource, and refusing the CONNECT-time handshake for its absence breaks
    clients that treat a transport failure as fatal. Measured with codex-cli 0.145.0 (rmcp):
    one 503 endpoint killed the whole session and produced no answer, `required = false`
    notwithstanding. Claude Code tolerates it, so this is not symmetric across clients.

    Nothing here weakens the gate. The tool list is empty, so no tool can be named, and
    `LeaseGate.authorize` still refuses every `tools/call` without a matching active lease.
    """
    if not messages:
        return None
    message = messages[0]
    method = message.get("method")
    if method == "initialize":
        params = message.get("params") or {}
        requested = params.get("protocolVersion") or _OFFLINE_PROTOCOL_VERSION
        return {
            "jsonrpc": "2.0",
            "id": message.get("id"),
            "result": {
                "protocolVersion": requested,
                "capabilities": {"tools": {"listChanged": False}},
                "serverInfo": {"name": "lean-slot proxy (backend idle)", "version": "1"},
                "instructions": (
                    "This slot holds no active lease, so its Lean backend is not running and "
                    "it exposes no tools. Acquire and prepare the slot with slotctl first."
                ),
            },
        }
    if method == "tools/list":
        return {"jsonrpc": "2.0", "id": message.get("id"), "result": {"tools": []}}
    if method == "ping":
        return {"jsonrpc": "2.0", "id": message.get("id"), "result": {}}
    return None


def is_notification_only(messages: list[dict[str, Any]]) -> bool:
    """True when every message is a notification, which takes 202 and no body."""
    return bool(messages) and all(
        "id" not in m and str(m.get("method", "")).startswith("notifications/")
        for m in messages
    )


def make_handler(inventory: Inventory, number: int):
    slot = inventory.slot(number)
    backend_host = str(inventory.raw["server"]["host"])
    backend_port = int(slot["backend_port"])
    backend_token = inventory.backend_token(number)
    gate = LeaseGate(inventory, number)

    class Handler(BaseHTTPRequestHandler):
        server_version = "LeanSlotGate/1"

        def log_message(self, format_: str, *args: object) -> None:
            super().log_message(format_, *args)

        def _deny(self, status: int, detail: str, request_id: object = None) -> None:
            body = json.dumps(
                {
                    "jsonrpc": "2.0",
                    "id": request_id,
                    "error": {
                        "code": -32001,
                        "message": f"ADR-008 lease gate: {detail}",
                    },
                }
            ).encode()
            self.send_response(status)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(body)

        def _respond_json(self, payload: dict[str, Any]) -> None:
            body = json.dumps(payload).encode()
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(body)))
            self.send_header("Cache-Control", "no-store")
            self.end_headers()
            self.wfile.write(body)

        def _handle(self) -> None:
            length = int(self.headers.get("Content-Length", "0") or 0)
            if length > 16 * 1024 * 1024:
                self._deny(413, "request body exceeds 16 MiB")
                return
            body = self.rfile.read(length) if length else b""
            request_id: object = None
            try:
                parsed = _messages(body)
                if parsed:
                    request_id = parsed[0].get("id")
                request_url = urlsplit(self.path)
                client_hint = parse_qs(request_url.query).get("client", [None])[0]
                client, supplied_hash = gate.identify(
                    self.headers.get("Authorization"), client_hint
                )
                gate.authorize(client, supplied_hash, body, http_method=self.command)
            except SlotError as exc:
                status = 401 if "credential" in str(exc) else 403
                self._deny(status, str(exc), request_id)
                return
            headers = {
                key: value
                for key, value in self.headers.items()
                if key.lower() not in _HOP_HEADERS
                and key.lower() not in {"host", "authorization", "content-length"}
            }
            headers["Authorization"] = f"Bearer {backend_token}"
            if body:
                headers["Content-Length"] = str(len(body))
            connection = http.client.HTTPConnection(
                backend_host, backend_port, timeout=180
            )
            try:
                connection.request(
                    self.command, request_url.path, body=body or None, headers=headers
                )
                response = connection.getresponse()
                self.send_response(response.status, response.reason)
                for key, value in response.getheaders():
                    lowered = key.lower()
                    if lowered not in _HOP_HEADERS and lowered not in {
                        "content-length",
                        "server",
                        "date",
                    }:
                        self.send_header(key, value)
                self.send_header("Connection", "close")
                self.end_headers()
                while True:
                    chunk = response.read(64 * 1024)
                    if not chunk:
                        break
                    self.wfile.write(chunk)
                    self.wfile.flush()
            except (OSError, http.client.HTTPException) as exc:
                if not self.wfile.closed:
                    try:
                        # The backend is a dispatch-time resource; do not fail the
                        # connect-time handshake for its absence (see offline_handshake).
                        if is_notification_only(parsed):
                            self.send_response(202)
                            self.send_header("Content-Length", "0")
                            self.end_headers()
                        elif (local := offline_handshake(parsed)) is not None:
                            self._respond_json(local)
                        else:
                            self._deny(503, f"backend unavailable: {exc}", request_id)
                    except (BrokenPipeError, OSError):
                        pass
            finally:
                connection.close()

        def do_HEAD(self) -> None:
            try:
                request_url = urlsplit(self.path)
                client_hint = parse_qs(request_url.query).get("client", [None])[0]
                gate.identify(self.headers.get("Authorization"), client_hint)
            except SlotError:
                self.send_response(401)
                self.send_header("Cache-Control", "no-store")
                self.end_headers()
                return
            self.send_response(204)
            self.send_header("Cache-Control", "no-store")
            self.end_headers()

        do_GET = _handle
        do_POST = _handle
        do_DELETE = _handle

    return Handler


def serve(inventory: Inventory, number: int) -> None:
    slot = inventory.slot(number)
    host = str(inventory.raw["server"]["host"])
    server = ThreadingHTTPServer(
        (host, int(slot["proxy_port"])), make_handler(inventory, number)
    )
    try:
        server.serve_forever(poll_interval=0.2)
    finally:
        server.server_close()
