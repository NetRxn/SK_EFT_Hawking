"""Configuration and durable-state primitives for the Lean slot controller."""

from __future__ import annotations

import hashlib
import math
import copy
import datetime
import stat
import re
import subprocess
import json
import os
import secrets
import tempfile
import time
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any, Iterator


SCHEMA_VERSION = 1
SLOT_STATES = {
    "ACQUIRED",
    "PREPARING",
    "ACTIVE",
    "READY_TO_ABSORB",
    "INTEGRATING",
    "REBUILDING",
    "REWARMING",
    "QUARANTINED",
}


class SlotError(RuntimeError):
    """An invariant failed, with optional bounded external observation witnesses."""

    def __init__(self, *args: object, observations: tuple["Observation", ...] = ()):
        super().__init__(*args)
        self.observations = observations
        self.recorded_pid = None  # Diagnostic raw input only, never identity authority.


def now_iso() -> str:
    return time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime())


def sha256_bytes(value: bytes) -> str:
    return hashlib.sha256(value).hexdigest()


def token_hash(token: str) -> str:
    return sha256_bytes(token.encode("utf-8"))


def canonical_digest(value: Any) -> str:
    return sha256_bytes(
        json.dumps(value, sort_keys=True, separators=(",", ":")).encode("utf-8")
    )


def read_json(path: Path) -> dict[str, Any]:
    try:
        with path.open("rb") as handle:
            content = handle.read(MAX_JSON_BYTES + 1)
        if len(content) > MAX_JSON_BYTES:
            raise ValueError("JSON artifact exceeds bounded read limit")
        value = json.loads(content.decode("utf-8"))
        if not isinstance(value, dict):
            raise ValueError("state file must contain a JSON object")
    except (OSError, UnicodeError, ValueError) as exc:
        evidence = Observation("absent" if isinstance(exc, FileNotFoundError) else "unavailable",
                               detail=str(exc), errno=getattr(exc, "errno", None),
                               target=str(path), operation="read-json", error_class=type(exc).__name__)
        label = "missing state file" if isinstance(exc, FileNotFoundError) else "invalid state file"
        raise SlotError(f"{label} {path}: {evidence.detail}", observations=(evidence,)) from exc
    return value


def atomic_write(path: Path, content: str, mode: int = 0o600) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, temporary = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    temporary_path = Path(temporary)
    try:
        os.fchmod(fd, mode)
        with os.fdopen(fd, "w", encoding="utf-8") as handle:
            handle.write(content)
            handle.flush()
            os.fsync(handle.fileno())
        os.replace(temporary_path, path)
    finally:
        temporary_path.unlink(missing_ok=True)


def atomic_json(path: Path, value: dict[str, Any], mode: int = 0o600) -> None:
    atomic_write(path, json.dumps(value, indent=2, sort_keys=True) + "\n", mode)


def exclusive_json(path: Path, value: dict[str, Any]) -> None:
    """Create *path* exactly once using an atomic filesystem primitive."""
    path.parent.mkdir(parents=True, exist_ok=True)
    try:
        fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, 0o600)
    except FileExistsError as exc:
        raise SlotError(f"slot already has a lease: {path}") from exc
    try:
        payload = (json.dumps(value, indent=2, sort_keys=True) + "\n").encode()
        with os.fdopen(fd, "wb", closefd=False) as handle:
            handle.write(payload)
            handle.flush()
            os.fsync(handle.fileno())
    finally:
        os.close(fd)


def exclusive_durable_json(path: Path, value: dict[str, Any]) -> None:
    """Publish complete process recovery provenance without replacing any record."""
    path.parent.mkdir(parents=True, exist_ok=True)
    fd, name = tempfile.mkstemp(prefix=f".{path.name}.", dir=path.parent)
    temporary = Path(name)
    try:
        with os.fdopen(fd, "wb") as stream:
            stream.write((json.dumps(value, indent=2, sort_keys=True) + "\n").encode())
            stream.flush()
            os.fsync(stream.fileno())
        os.link(temporary, path)  # RR durable reservation: exclusive complete publication.
        directory = os.open(path.parent, os.O_RDONLY)
        try:
            os.fsync(directory)
        finally:
            os.close(directory)
    except OSError as exc:
        raise SlotError(f"recovery reservation publication failed: {exc}") from exc
    finally:
        temporary.unlink(missing_ok=True)


_OBSERVATION_DEADLINE = ContextVar("lean_slot_observation_deadline", default=None)


def observation_timeout(limit: float = 2.0) -> float:
    deadline = _OBSERVATION_DEADLINE.get()
    remaining = limit if deadline is None else min(limit, deadline - time.monotonic())
    if remaining <= 0:
        raise TimeoutError("whole stop observation deadline expired")
    return remaining


@contextmanager
def observation_budget(seconds: float | None = None, *, deadline: float | None = None) -> Iterator[float]:
    """Install/yield one effective bound; reset only this context on exit."""
    current = _OBSERVATION_DEADLINE.get()
    if current is not None:
        _wire_number(current, minimum=0)
    if deadline is None:
        if seconds is None:
            raise ValueError("observation budget requires an allowance or deadline")
        _wire_number(seconds)
        deadline = time.monotonic() + seconds
    else:
        if seconds is not None:
            raise ValueError("observation budget accepts one bound")
    _wire_number(deadline, minimum=0)
    effective = min(current, deadline) if current is not None else deadline
    token = _OBSERVATION_DEADLINE.set(effective)
    try:
        yield effective
    finally:
        _OBSERVATION_DEADLINE.reset(token)


@contextmanager
def directory_lock(path: Path, *, purpose: str) -> Iterator[None]:
    """Portable fail-closed lock implemented by atomic directory creation."""
    path.parent.mkdir(parents=True, exist_ok=True)
    try:
        path.mkdir(mode=0o700)
    except FileExistsError as exc:
        owner = path / "owner.json"
        detail = (
            owner.read_text(encoding="utf-8").strip() if owner.exists() else "unknown"
        )
        raise SlotError(f"{purpose} is already locked ({detail})") from exc
    try:
        atomic_json(
            path / "owner.json",
            {"pid": os.getpid(), "purpose": purpose, "created_at": now_iso()},
        )
        yield
    finally:
        (path / "owner.json").unlink(missing_ok=True)
        try:
            path.rmdir()
        except OSError as exc:
            raise SlotError(f"could not remove {purpose} lock {path}: {exc}") from exc


@dataclass(frozen=True)
class Inventory:
    source: Path
    raw: dict[str, Any]
    repo_root: Path
    workspace_root: Path
    state_root: Path

    @classmethod
    def load(cls, source: Path | str | None = None) -> "Inventory":
        if source is None:
            env_path = os.environ.get("LEAN_SLOT_CONFIG")
            source = (
                env_path
                or Path(__file__).resolve().parents[2]
                / "config"
                / "lean-slots.public.json"
            )
        source_path = Path(source).expanduser().resolve()
        raw = read_json(source_path)
        def invalid(message: str) -> None:
            evidence = Observation("unavailable", detail=message, target=str(source_path),
                                   operation="validate-inventory", error_class="ValueError")
            raise SlotError(message, observations=(evidence,))
        if type(raw.get("schema_version")) is not int or raw["schema_version"] != SCHEMA_VERSION:
            invalid(f"unsupported inventory schema: {raw.get('schema_version')!r}")
        slots = raw.get("slots")
        if type(raw.get("max_active_slots")) is not int or raw["max_active_slots"] != 3 or not isinstance(slots, dict) or set(slots) != {"1", "2", "3"}:
            invalid("inventory must define exactly the global slots 1, 2, and 3")
        if not isinstance(raw.get("repo_role"), str) or not raw["repo_role"].strip():
            invalid("inventory repo_role must be a nonempty string")
        if not isinstance(raw.get("repo_root", ".."), str) or not raw.get("repo_root", "..").strip():
            invalid("inventory repo_root must be a nonempty string")
        server = raw.get("server")
        if not isinstance(server, dict) or not isinstance(server.get("host"), str) or not server["host"].strip():
            invalid("inventory server must map a nonempty host string")
        for number, slot in slots.items():
            if not isinstance(slot, dict):
                invalid(f"inventory slot {number} must be an object")
            for key in ("worktree", "branch", "endpoint_name"):
                if not isinstance(slot.get(key), str) or not slot[key].strip():
                    invalid(f"inventory slot {number}.{key} must be a nonempty string")
            for key in ("proxy_port", "backend_port"):
                value = slot.get(key)
                if type(value) not in (int, str):
                    invalid(f"inventory slot {number}.{key} must be a valid port")
                try:
                    port = int(value)
                except ValueError:
                    invalid(f"inventory slot {number}.{key} must be a valid port")
                if not 1 <= port <= 65535:
                    invalid(f"inventory slot {number}.{key} must be a valid port")
        repo_root = (source_path.parent / str(raw.get("repo_root", ".."))).resolve()
        workspace_root = repo_root.parent
        state_root = (
            Path(
                os.environ.get(
                    "LEAN_SLOT_STATE_DIR", str(workspace_root / ".lean-slots")
                )
            )
            .expanduser()
            .resolve()
        )
        inventory = cls(source_path, raw, repo_root, workspace_root, state_root)
        try:
            _ = inventory.client_auth_mode
        except SlotError as exc:
            invalid(str(exc))
        return inventory

    @property
    def repo_role(self) -> str:
        return str(self.raw["repo_role"])

    @property
    def client_auth_mode(self) -> str:
        """Client-to-proxy authentication mode.

        ``trusted-local`` is the single-user workstation default: the proxy is
        loopback-only and the lease remains the dispatch authority, but Codex
        does not need a bearer credential merely to start. ``bearer`` retains
        the stronger client/session binding for a future shared-user host.
        """

        server = self.raw.get("server", {})
        mode = str(server.get("client_auth", "trusted-local"))
        if mode not in {"trusted-local", "bearer"}:
            raise SlotError(
                f"server.client_auth must be 'trusted-local' or 'bearer', got {mode!r}"
            )
        host = str(server.get("host", ""))
        if mode == "trusted-local" and host not in {"127.0.0.1", "::1", "localhost"}:
            raise SlotError(
                "trusted-local client auth requires a loopback server.host, "
                f"got {host!r}"
            )
        return mode

    def slot(self, number: int) -> dict[str, Any]:
        if number not in {1, 2, 3}:
            raise SlotError(f"slot must be one of 1, 2, 3, got {number}")
        return dict(self.raw["slots"][str(number)])

    def worktree(self, number: int) -> Path:
        return (self.repo_root / self.slot(number)["worktree"]).resolve()

    def lean_root(self, number: int) -> Path:
        return self.worktree(number) / "lean"

    def lease_path(self, number: int) -> Path:
        return self.state_root / "leases" / f"wt{number}.json"

    def epoch_path(self) -> Path:
        return self.state_root / "epochs" / f"{self.repo_role}.json"

    def process_path(self, kind: str, number: int) -> Path:
        return (
            self.state_root / "processes" / f"{self.repo_role}-wt{number}-{kind}.json"
        )

    def log_path(self, kind: str, number: int) -> Path:
        return self.state_root / "logs" / f"{self.repo_role}-wt{number}-{kind}.log"

    def client_token_path(self, client: str) -> Path:
        return self.state_root / "clients" / f"{client}.token"

    def backend_token_path(self, number: int) -> Path:
        return self.state_root / "backends" / f"{self.repo_role}-wt{number}.token"

    def token(self, client: str, *, create: bool = True, rotate: bool = False) -> str:
        if not client.replace("-", "").replace("_", "").isalnum():
            raise SlotError(f"invalid client name: {client!r}")
        path = self.client_token_path(client)
        if rotate or not path.exists():
            if not create:
                raise SlotError(f"missing token for client {client}")
            value = secrets.token_urlsafe(48)
            atomic_write(path, value + "\n")
            return value
        value = path.read_text(encoding="utf-8").strip()
        if not value:
            raise SlotError(f"empty token file: {path}")
        if path.stat().st_mode & 0o077:
            raise SlotError(f"token permissions are too broad; expected 0600: {path}")
        return value

    def backend_token(self, number: int) -> str:
        path = self.backend_token_path(number)
        if not path.exists():
            atomic_write(path, secrets.token_urlsafe(48) + "\n")
        return path.read_text(encoding="utf-8").strip()

    def paired_inventory(self) -> "Inventory | None":
        """Return the optional downstream dependency inventory.

        The public control plane deliberately knows only this product-neutral
        schema.  Repository names and paths live in the downstream inventory.
        """
        paired = self.raw.get("paired_dependency")
        if paired is None:
            return None
        if not isinstance(paired, dict) or not paired.get("inventory"):
            raise SlotError(
                "paired_dependency.inventory must name an inventory JSON file"
            )
        source = Path(str(paired["inventory"]))
        if source.is_absolute():
            raise SlotError("paired dependency inventory paths must be relative")
        inventory = Inventory.load(self.source.parent / source)
        if inventory.state_root != self.state_root:
            raise SlotError("paired inventories must share one runtime state directory")
        if inventory.repo_role == self.repo_role:
            raise SlotError("paired inventories must use distinct repository roles")
        return inventory

    def paired_dependency_lean_root(self, number: int) -> Path | None:
        paired = self.raw.get("paired_dependency")
        if paired is None:
            return None
        relative = Path(str(paired.get("path_from_slot_lean", "")))
        if not str(relative) or relative.is_absolute():
            raise SlotError("paired_dependency.path_from_slot_lean must be relative")
        return (self.lean_root(number) / relative).resolve()

    def primary_dependency_lean_root(self) -> Path | None:
        paired = self.raw.get("paired_dependency")
        if paired is None:
            return None
        relative = Path(str(paired.get("path_from_primary_lean", "")))
        if not str(relative) or relative.is_absolute():
            raise SlotError("paired_dependency.path_from_primary_lean must be relative")
        return (self.repo_root / "lean" / relative).resolve()

    def backend_expected(self, number: int) -> bool:
        """Whether this inventory should own the heavy backend right now."""
        policy = str(self.raw.get("server", {}).get("backend_policy", "default"))
        if policy not in {"default", "leased"}:
            raise SlotError(f"unsupported backend policy: {policy!r}")
        lease = self.lease(number, required=False)
        if lease is not None:
            if lease.get("repo_role") != self.repo_role:
                return False
            if lease.get("state") in {
                "ACTIVE",
                "READY_TO_ABSORB",
                "INTEGRATING",
                "REBUILDING",
                "REWARMING",
            }:
                return True
            return policy == "default"
        return policy == "default"

    def lease(self, number: int, *, required: bool = True) -> dict[str, Any] | None:
        path = self.lease_path(number)
        observed = observe_path(path)
        if observed.state == "unavailable":
            raise SlotError(f"lease observation unavailable for wt{number}", observations=(observed,))
        if observed.state == "absent":
            if required:
                raise SlotError(f"slot wt{number} is not leased", observations=(observed,))
            return None
        lease = read_json(path)
        if lease.get("schema_version") != SCHEMA_VERSION:
            raise SlotError(f"unsupported lease schema for wt{number}")
        if lease.get("slot") != number or lease.get("state") not in SLOT_STATES:
            raise SlotError(f"invalid lease identity/state for wt{number}")
        return lease

    def save_lease(
        self, number: int, lease: dict[str, Any], *, touch_heartbeat: bool = True
    ) -> None:
        """Persist a lease record.

        `heartbeat_at` means **the owner is alive**, and `reclaim` gates on it. A
        controller-side write the owner did not initiate is therefore not a heartbeat:
        pass `touch_heartbeat=False` for those. Refreshing it on a failed reclaim's
        quarantine write makes a genuinely stale lease unreclaimable **by retry**, because
        every attempt resets the clock the next attempt reads.
        """
        if touch_heartbeat:
            lease["heartbeat_at"] = now_iso()
        atomic_json(self.lease_path(number), lease)


def tool_cache_path(state_root: Path) -> Path:
    """Where the advertised tool list is cached, shared by the supervisor and the proxy."""
    return state_root / "generated" / "tool-list.json"


def tool_list_key(server: dict[str, Any]) -> str:
    """What the advertised tool list actually depends on.

    The server binary, the disabled set, and whether a REPL is enabled — deliberately NOT
    the per-slot runtime fingerprint, which folds in the project path and port. Those
    change which PROJECT a backend serves, never which TOOLS exist, so keying on them
    would invalidate a perfectly good cache per slot and defeat the point.
    """
    return canonical_digest(
        {
            "command": [str(item) for item in server.get("command", [])],
            "disabled_tools": sorted(str(t) for t in server.get("disabled_tools", [])),
            "repl": bool(server.get("repl", False)),
        }
    )


# Bounds protect diagnostics and complete observations; overflow is unavailable,
# never a truncated census from which absence or capacity can be inferred.
DIAGNOSTIC_LIMIT = 2048
MAX_JSON_BYTES = 4 * 1024 * 1024
MAX_OBSERVER_OUTPUT = 8 * 1024 * 1024
MAX_CENSUS_ROWS = 16384
MAX_DIRECTORY_ENTRIES = 4096


@dataclass(frozen=True)
class Observation:
    """Evidence, never an absence inferred from failed observation."""

    state: str
    signature: str | None = None
    detail: str = ""
    errno: int | None = None
    target: str = ""
    operation: str = ""
    observed_at: str = field(default_factory=now_iso)
    returncode: int | None = None
    error_class: str | None = None
    identity: Any = None
    reason: str | None = None
    diagnostics: dict | None = None

    def __post_init__(self) -> None:
        object.__setattr__(self, "detail", str(self.detail)[:DIAGNOSTIC_LIMIT])
        if self.reason is not None or self.diagnostics is not None:
            validate_process_pair(self.diagnostics, self.reason, self.state, self.observed_at)

    def as_dict(self) -> dict[str, Any]:
        value = {"state": self.state, "target": self.target, "operation": self.operation,
                "observed_at": self.observed_at, "returncode": self.returncode,
                "error_class": self.error_class, "errno": self.errno,
                "observed_identity": self.identity if self.identity is not None else self.signature,
                "diagnostic_text": self.detail}
        if self.reason is not None:
            value.update(reason=self.reason, diagnostics=self.diagnostics)
        return value


def observe_path(path: Path) -> Observation:
    """Native stat: only FileNotFoundError establishes absence."""
    try:
        value = os.stat(path)
    except (OSError, ValueError) as exc:
        return Observation("absent" if isinstance(exc, FileNotFoundError) else "unavailable",
                           detail=str(exc), errno=getattr(exc, "errno", None),
                           target=str(path), operation="stat", error_class=type(exc).__name__)
    return Observation("present", target=str(path), operation="stat",
                       identity={"mode": stat.S_IFMT(value.st_mode), "inode": value.st_ino,
                                 "device": value.st_dev})


def observe_directory(path: Path) -> tuple[tuple[Path, ...], Observation]:
    """Bounded, complete native scandir; never use suppressed glob/is_dir errors."""
    before = observe_path(path)
    if before.state != "present":
        return (), Observation(before.state, detail=before.detail, errno=before.errno,
                               target=str(path), operation="scandir", error_class=before.error_class)
    if before.identity["mode"] != stat.S_IFDIR:
        return (), Observation("unavailable", detail="directory observer target is not a directory",
                               target=str(path), operation="scandir")
    entries = []
    try:
        with os.scandir(path) as iterator:
            for entry in iterator:
                entries.append(path / entry.name)
                if len(entries) > MAX_DIRECTORY_ENTRIES:
                    return (), Observation("unavailable", detail="directory exceeds complete enumeration bound",
                                           target=str(path), operation="scandir")
    except (OSError, ValueError) as exc:
        return (), Observation("absent" if isinstance(exc, FileNotFoundError) else "unavailable",
                               detail=str(exc), errno=getattr(exc, "errno", None),
                               target=str(path), operation="scandir", error_class=type(exc).__name__)
    return tuple(sorted(entries)), Observation("present", target=str(path), operation="scandir",
                                               identity={"entry_count": len(entries)})


@dataclass(frozen=True)
class ProcessRow:
    pid: int
    ppid: int
    command: str
    signature: str


@dataclass(frozen=True)
class ProcessSnapshot:
    state: str
    rows: tuple[ProcessRow, ...] = ()
    detail: str = ""
    target: str = "all-processes"
    operation: str = "ps-census"
    observed_at: str = field(default_factory=now_iso)
    returncode: int | None = None
    error_class: str | None = None
    errno: int | None = None

    def __post_init__(self) -> None:
        object.__setattr__(self, "detail", str(self.detail)[:DIAGNOSTIC_LIMIT])

    def as_dict(self) -> dict[str, Any]:
        witness = next((row for row in self.rows if row.pid == os.getpid()), None)
        return {"state": self.state, "target": self.target, "operation": self.operation,
                "observed_at": self.observed_at, "returncode": self.returncode,
                "error_class": self.error_class, "errno": self.errno,
                "observed_identity": {"pid": witness.pid, "signature": witness.signature} if witness else None,
                "diagnostic_text": self.detail}

    def as_observation(self) -> Observation:
        value = self.as_dict()
        return Observation(self.state, detail=self.detail, errno=self.errno,
                           target=self.target, operation=self.operation, observed_at=self.observed_at,
                           returncode=self.returncode, error_class=self.error_class,
                           identity=value["observed_identity"])

    def descendants(self, pid: int) -> set[int]:
        found = {pid}
        while True:
            expanded = found | {row.pid for row in self.rows if row.ppid in found}
            if expanded == found:
                return found
            found = expanded


def _signature_command(value: str) -> str | None:
    if not isinstance(value, str) or "\x00" in value or "\n" in value or "\r" in value:
        return None
    match = re.fullmatch(r"(Mon|Tue|Wed|Thu|Fri|Sat|Sun)\s+(Jan|Feb|Mar|Apr|May|Jun|Jul|Aug|Sep|Oct|Nov|Dec)\s+(\d{1,2})\s+(\d{2}:\d{2}:\d{2})\s+(\d{4})\s+(\S.*)", value.strip())
    if not match:
        return None
    try:
        moment = datetime.datetime.strptime(" ".join(match.groups()[:5]), "%a %b %d %H:%M:%S %Y")
    except ValueError:
        return None
    return match[6] if moment.strftime("%a") == match[1] else None


def process_snapshot() -> ProcessSnapshot:
    """A complete ps observation, with a known-present witness, or unavailable."""
    try:
        result = subprocess.run(["ps", "-axo", "pid=,ppid=,lstart=,command="],
                                check=False, capture_output=True, text=True, timeout=observation_timeout())
    except (OSError, subprocess.TimeoutExpired, UnicodeError, ValueError) as exc:
        return ProcessSnapshot("unavailable", detail=str(exc), error_class=type(exc).__name__,
                               errno=getattr(exc, "errno", None))
    if result.returncode or result.stderr.strip():
        return ProcessSnapshot("unavailable", detail=f"ps exit {result.returncode}: {result.stderr.strip()}",
                               returncode=result.returncode)
    if len(result.stdout) > MAX_OBSERVER_OUTPUT:
        return ProcessSnapshot("unavailable", detail="process census exceeds complete output bound", returncode=result.returncode)
    rows = []
    seen = set()
    for line in result.stdout.splitlines():
        match = re.fullmatch(r"\s*(\d+)\s+(\d+)\s+(.+)", line)
        if not match or len(rows) >= MAX_CENSUS_ROWS:
            return ProcessSnapshot("unavailable", detail="malformed/oversized process census", returncode=result.returncode)
        pid, ppid, signature = int(match[1]), int(match[2]), match[3].strip()
        command = _signature_command(signature)
        if pid <= 0 or pid in seen or command is None:
            return ProcessSnapshot("unavailable", detail="malformed/ambiguous process census identity", returncode=result.returncode)
        seen.add(pid); rows.append(ProcessRow(pid, ppid, command, signature))
    if not any(row.pid == os.getpid() for row in rows):
        return ProcessSnapshot("unavailable", detail="process census lacks known-present observer", returncode=result.returncode)
    return ProcessSnapshot("present", tuple(rows), returncode=result.returncode)


def observe_process(pid: int, signature: str | None = None) -> Observation:
    """Strict generic identity; same-call diagnostics never relax this verdict."""
    target = f"PID {pid}"
    started = diagnostic_stamp()
    selected = census_probe = None
    def observed(state, value=None, detail="", *, result=None, exc=None, reason=None):
        end = diagnostic_stamp()
        args = dict(target=target, operation="ps-selected", observed_at=end["utc"],
                    returncode=result.returncode if result is not None else None,
                    error_class=type(exc).__name__ if exc is not None else None)
        if state == "present":
            return Observation(state, value, detail, getattr(exc, "errno", None), **args)
        pair = {"version": 1, "pid": pid if type(pid) is int and pid > 0 else None,
                "expected_signature_supplied": signature is not None,
                "span": diagnostic_span(started, end), "selected": selected, "census": census_probe}
        try:
            pair = bound_diagnostics(pair, 65536)
            return Observation(state, value, detail, getattr(exc, "errno", None),
                               reason=reason, diagnostics=pair, **args)
        except (ValueError, UnicodeError, OverflowError) as failure:
            # A nonrepresentable diagnostic cannot authorize creation retry. Retain
            # the actual ordinary state and visible failure, never fake a pair.
            return Observation(state, value, f"{detail}; diagnostic unavailable: {failure}",
                               getattr(exc, "errno", None), **args)
    if type(pid) is not int or pid <= 0:
        return observed("unavailable", detail="no authoritative positive integer PID", reason="invalid_target")
    before = diagnostic_stamp()
    def selected_view(state, detail="", *, result=None, exc=None, operand=None):
        return diagnostic_probe("ps-selected", before, diagnostic_stamp(), state,
                                detail=detail, result=result, exc=exc, operand=operand)
    try:
        result = subprocess.run(["ps", "-p", str(pid), "-o", "lstart=", "-o", "command="],
                                check=False, capture_output=True, text=True, timeout=observation_timeout())
    except (OSError, subprocess.TimeoutExpired, UnicodeError, ValueError) as exc:
        selected = selected_view("unavailable", str(exc), exc=exc)
        return observed("unavailable", detail=str(exc), exc=exc, reason="selected_failure")
    value = result.stdout.strip()
    detail = None
    if len(result.stdout) > MAX_OBSERVER_OUTPUT:
        detail = "selected process output exceeds bound"
    elif result.stderr.strip() or result.returncode not in {0, 1}:
        detail = f"ps exit {result.returncode}: {result.stderr.strip()}"
    elif value and (result.returncode != 0 or _signature_command(value) is None):
        detail = "malformed/partial/ambiguous selected process identity"
    if detail is not None:
        selected = selected_view("unavailable", detail, result=result, operand=value)
        return observed("unavailable", detail=detail, result=result, reason="selected_failure")
    selected = selected_view("present" if value else "absent", result=result, operand=value)
    before = diagnostic_stamp()
    census = process_snapshot()
    row = next((item for item in census.rows if item.pid == pid), None) if census.state == "present" else None
    census_probe = diagnostic_probe("ps-census", before, diagnostic_stamp(),
                                    "unavailable" if census.state != "present" else "present" if row else "absent",
                                    detail=census.detail, result=census,
                                    operand=row.signature if row else None,
                                    ppid=row.ppid if row else None,
                                    witness=os.getpid() if census.state == "present" else None)
    if census.state != "present":
        return observed("unavailable", detail=f"coherent process census unavailable: {census.detail}",
                        result=result, reason="census_failure")
    if not value and row is None:
        return observed("absent", detail="confirmed absent in capable process census", result=result, reason="confirmed_absent")
    if not value or row is None or row.signature != value:
        reason = "selected_census_signature_drift" if value and row else "selected_census_presence_drift"
        return observed("unavailable", detail="selected/census target identity inconsistent", result=result, reason=reason)
    return observed("mismatch" if signature and value != signature else "present", value,
                    result=result, reason="signature_mismatch" if signature and value != signature else None)


def signature_birth(signature: str) -> str | None:
    """The genuine legacy lstart precision, never a fabricated generation token."""
    return " ".join(signature.split()[:5]) if _signature_command(signature) is not None else None


def observe_shutdown_process(pid: int) -> Observation:
    """Coherent native state for shutdown only; Z remains present, never absent."""
    target = f"PID {pid}"
    def refusal(detail, exc=None):
        return Observation("unavailable", detail=detail, target=target,
                           operation="ps-shutdown-state", error_class=type(exc).__name__ if exc else None)
    if type(pid) is not int or pid <= 0:
        return refusal("invalid shutdown PID")
    def rows(output):
        if len(output) > MAX_OBSERVER_OUTPUT:
            raise ValueError("shutdown observation exceeds bound")
        result = {}
        for line in output.splitlines():
            fields = line.split(None, 8)
            if len(fields) != 9 or len(result) >= MAX_CENSUS_ROWS:
                raise ValueError("incomplete shutdown row")
            number, parent = int(fields[0]), int(fields[1])
            birth, native, command = " ".join(fields[2:7]), fields[7], fields[8]
            if (number <= 0 or parent < 0 or number in result or
                    _signature_command(birth + " " + command) is None or
                    re.fullmatch(r"[DIRSTtUWXZ][+<>NnsLlEXV]*", native) is None):
                raise ValueError("malformed/ambiguous shutdown row")
            result[number] = {"pid": number, "ppid": parent, "birth": birth,
                              "native_state": native, "command": command}
        return result
    try:
        selected = subprocess.run(["ps", "-p", str(pid), "-o", "pid=,ppid=,lstart=,stat=,command="],
                                  check=False, capture_output=True, text=True, timeout=observation_timeout())
        census = subprocess.run(["ps", "-axo", "pid=,ppid=,lstart=,stat=,command="],
                                check=False, capture_output=True, text=True, timeout=observation_timeout())
        if selected.returncode not in (0, 1) or selected.stderr.strip() or census.returncode or census.stderr.strip():
            raise ValueError("native state observation failed")
        chosen, complete = rows(selected.stdout), rows(census.stdout)
        if os.getpid() not in complete or set(chosen) - {pid}:
            raise ValueError("native state census lacks witness or selected PID differs")
        if bool(chosen) != (selected.returncode == 0) or chosen.get(pid) != complete.get(pid):
            raise ValueError("native state selected/census drift")
        observation_timeout()
        return Observation("present" if pid in complete else "absent", target=target,
                           operation="ps-shutdown-state", identity=complete.get(pid))
    except (OSError, subprocess.TimeoutExpired, UnicodeError, ValueError) as exc:
        return refusal(str(exc), exc)



def observe_shutdown_family(identities: dict[int, str], root: int, *,
                            max_identities: int = 4096) -> tuple[ProcessSnapshot, dict[int, Observation], dict[int, Observation]]:
    """One bounded shutdown-only pass; never retain its witnesses across effects.

    Generic signatures remain byte-exact. Native state is additional evidence,
    never a replacement identity or proof that a zombie is absent. Unrelated
    processes may change between censuses; every selected PID and the complete
    rooted family must agree across the four capable views.
    """
    try:
        if (not identities or len(identities) > max_identities or type(root) is not int or root not in identities or
                any(type(pid) is not int or pid <= 0 or not isinstance(sig, str) or
                    _signature_command(sig) is None for pid, sig in identities.items())):
            raise ValueError("invalid/oversized shutdown family request")
        selection = ",".join(str(pid) for pid in sorted(identities))
        if len(selection.encode()) > 65536 or sum(len(sig.encode()) for sig in identities.values()) > MAX_OBSERVER_OUTPUT:
            raise ValueError("shutdown family request exceeds byte bound")

        def read(native, selected):
            fields = "pid=,ppid=,lstart=,stat=,command=" if native else "pid=,ppid=,lstart=,command="
            argv = ["ps", "-p", selection, "-o", fields] if selected else ["ps", "-axo", fields]
            value = subprocess.run(argv, check=False, capture_output=True, text=True,
                                   timeout=observation_timeout())
            if (value.returncode not in ((0, 1) if selected else (0,)) or value.stderr.strip() or
                    len(value.stdout) > MAX_OBSERVER_OUTPUT):
                raise ValueError("shutdown family command failed/exceeded output bound")
            rows = {}
            for line in value.stdout.splitlines():
                if len(rows) >= MAX_CENSUS_ROWS:
                    raise ValueError("shutdown family census exceeds row bound")
                if native:
                    fields = line.split(None, 8)
                    if len(fields) != 9:
                        raise ValueError("incomplete shutdown family native row")
                    pid, ppid = int(fields[0]), int(fields[1])
                    birth, stat_value, command = " ".join(fields[2:7]), fields[7], fields[8]
                    if (_signature_command(birth + " " + command) is None or
                            re.fullmatch(r"[DIRSTtUWXZ][+<>NnsLlEXV]*", stat_value) is None):
                        raise ValueError("malformed shutdown family native identity")
                    row = {"pid": pid, "ppid": ppid, "birth": birth,
                           "native_state": stat_value, "command": command}
                else:
                    match = re.fullmatch(r"\s*(\d+)\s+(\d+)\s+(.+)", line)
                    if match is None:
                        raise ValueError("incomplete shutdown family generic row")
                    pid, ppid, signature = int(match[1]), int(match[2]), match[3].strip()
                    command = _signature_command(signature)
                    if command is None:
                        raise ValueError("malformed shutdown family generic identity")
                    row = ProcessRow(pid, ppid, command, signature)
                if pid <= 0 or ppid < 0 or pid in rows:
                    raise ValueError("duplicate/invalid shutdown family PID")
                rows[pid] = row
            if selected:
                if set(rows) - set(identities) or bool(rows) != (value.returncode == 0):
                    raise ValueError("shutdown family selected extra PID/returncode")
            elif os.getpid() not in rows:
                raise ValueError("shutdown family census lacks known-present observer")
            return rows

        selected = read(False, True)
        complete = read(False, False)
        native_selected = read(True, True)
        native_complete = read(True, False)
        snapshot = ProcessSnapshot("present", tuple(complete.values()), operation="ps-shutdown-family")
        native_snapshot = ProcessSnapshot("present", tuple(
            ProcessRow(pid, row["ppid"], row["command"], row["birth"] + " " + row["command"])
            for pid, row in native_complete.items()))
        if snapshot.descendants(root) != native_snapshot.descendants(root):
            raise ValueError("shutdown family cross-format rooted census drift")
        generic, native = {}, {}
        for pid, signature in identities.items():
            row, terminal = complete.get(pid), native_complete.get(pid)
            if selected.get(pid) != row or native_selected.get(pid) != terminal:
                raise ValueError("shutdown family selected/census drift")
            if ((row is None) != (terminal is None) or
                    row is not None and (row.ppid != terminal["ppid"] or
                                         signature_birth(row.signature) != terminal["birth"] or
                                         row.command != terminal["command"])):
                raise ValueError("shutdown family cross-format identity drift")
            generic[pid] = Observation("absent" if row is None else "present" if row.signature == signature else "mismatch",
                                       row.signature if row else None, target=f"PID {pid}", operation="ps-shutdown-family-generic")
            native[pid] = Observation("present" if terminal is not None else "absent", target=f"PID {pid}",
                                      operation="ps-shutdown-family-native", identity=terminal)
        observation_timeout()
        return snapshot, generic, native
    except (OSError, subprocess.TimeoutExpired, UnicodeError, ValueError) as exc:
        snapshot = ProcessSnapshot("unavailable", detail=str(exc), operation="ps-shutdown-family",
                                   error_class=type(exc).__name__, errno=getattr(exc, "errno", None))
        return snapshot, {}, {}


def observe_tcp_sockets() -> tuple[list[dict[str, Any]], Observation]:
    """Bounded machine-readable TCP census with a known-present lsof witness."""
    try:
        witness = subprocess.run(["lsof", "-nP", "-a", "-p", str(os.getpid()), "-d", "cwd", "-Fpn"],
                                 capture_output=True, text=True, check=False, timeout=observation_timeout())
        if witness.returncode or witness.stderr.strip() or len(witness.stdout) > MAX_OBSERVER_OUTPUT:
            raise ValueError("lsof capability witness unavailable")
        if f"p{os.getpid()}" not in witness.stdout.splitlines() or not any(x.startswith("n/") for x in witness.stdout.splitlines()):
            raise ValueError("lsof lacks known-present observer cwd")
        result = subprocess.run(["lsof", "-nP", "-iTCP", "-FpftnT"],
                                capture_output=True, text=True, check=False, timeout=observation_timeout())
        if result.returncode not in (0, 1) or result.stderr.strip() or len(result.stdout) > MAX_OBSERVER_OUTPUT:
            raise ValueError("TCP census unavailable")
        sockets, pid, current = [], None, None
        def finish():
            if current is not None:
                if (set(current) != {"pid", "fd", "type", "name", "state"} or
                        current["type"] not in {"IPv4", "IPv6"} or not current["state"]):
                    raise ValueError("incomplete TCP socket record")
                sockets.append(current.copy())
        for line in result.stdout.splitlines():
            if not line or len(sockets) >= MAX_CENSUS_ROWS:
                raise ValueError("malformed/oversized TCP census")
            field, value = line[0], line[1:]
            if field == "p":
                finish(); current = None; pid = int(value)
                if pid <= 0:
                    raise ValueError("invalid TCP owner")
            elif field == "f":
                finish()
                if pid is None or not value:
                    raise ValueError("TCP descriptor lacks owner")
                current = {"pid": pid, "fd": value}
            elif current is None:
                raise ValueError("TCP field lacks descriptor")
            elif field in {"t", "n"}:
                key = {"t": "type", "n": "name"}[field]
                if key in current or not value:
                    raise ValueError("ambiguous TCP field")
                current[key] = value
            elif field == "T" and value.startswith("ST="):
                if "state" in current:
                    raise ValueError("duplicate TCP state")
                current["state"] = value[3:]
            elif field != "T":
                raise ValueError("unsupported TCP field")
        finish()
        if (result.returncode == 1) != (not sockets):
            raise ValueError("TCP result disagrees with census")
        return sockets, Observation("present", target="all-TCP-sockets", operation="lsof-census",
                                    identity={"count": len(sockets)})
    except (OSError, subprocess.TimeoutExpired, UnicodeError, ValueError) as exc:
        return [], Observation("unavailable", detail=str(exc), target="all-TCP-sockets",
                               operation="lsof-census", error_class=type(exc).__name__)


def _observe_created_handle(process: Any, signature: str) -> Observation:
    """Only the exact unreaped handle and a previously coherent identity may use this.

    Generic identity consumers use observe_process with a complete census. This
    narrower rollback witness permits bounded wrapper reap when a later census
    fails; it cannot discharge unknown descendants or the capacity reservation.
    """
    pid = process.pid
    target = f"PID {pid}"
    if getattr(process, "returncode", None) is not None or _signature_command(signature) is None:
        return Observation("unavailable", detail="created handle lacks unreaped coherent identity",
                           target=target, operation="ps-created-handle")
    try:
        result = subprocess.run(["ps", "-p", str(pid), "-o", "lstart=", "-o", "command="],
                                check=False, capture_output=True, text=True, timeout=observation_timeout())
        observation_timeout()
    except (OSError, subprocess.TimeoutExpired, UnicodeError, ValueError) as exc:
        return Observation("unavailable", detail=str(exc), errno=getattr(exc, "errno", None),
                           target=target, operation="ps-created-handle", error_class=type(exc).__name__)
    value = result.stdout.strip()
    if result.returncode != 0 or result.stderr.strip() or len(value) > MAX_OBSERVER_OUTPUT or _signature_command(value) is None:
        return Observation("unavailable", detail=f"created handle selected identity invalid: {result.stderr.strip()}",
                           target=target, operation="ps-created-handle", returncode=result.returncode)
    return Observation("present" if value == signature else "mismatch", value,
                       detail="exact unreaped creation handle checked against prior coherent identity",
                       target=target, operation="ps-created-handle", returncode=result.returncode)


def process_start_signature(pid: int) -> str | None:
    """Read-only compatibility helper; destructive consumers inspect Observation."""
    observed = observe_process(pid)
    return observed.signature if observed.state == "present" else None


def require_process_signature(pid: int) -> str:
    observed = observe_process(pid)
    if observed.state != "present" or not observed.signature:
        raise SlotError(f"process identity unavailable for PID {pid}: {observed.detail}", observations=(observed,))
    return observed.signature


def process_matches(pid: int, signature: str | None) -> bool:
    """Observed match only, never authority to delete or reclaim when false."""
    return bool(signature and observe_process(pid, signature).state == "present")


# LO-3a diagnostic grammar. These are existing-state payload helpers, never a
# second process observer, ownership registry, or a persisted retry capability.
_WIRE_INT = 2**53 - 1
_PAIR_KEYS = {'version', 'pid', 'expected_signature_supplied', 'span', 'selected', 'census'}
_REASONS = {'invalid_target', 'selected_failure', 'census_failure',
            'selected_census_presence_drift', 'selected_census_signature_drift',
            'confirmed_absent', 'signature_mismatch'}
_TERMINAL_PHASES = {'spawn', 'handle', 'creation', 'diagnostic_write', 'signature_write',
                    'readiness', 'final_observation', 'running_write', 'deadline'}
_ROLLBACK_PHASES = {'rollback_identity', 'rollback_census', 'rollback_signal',
                    'rollback_wait', 'rollback_quiescence', 'residual_write'}
_STARTUP_KEYS = {'version', 'launch_token', 'observer_pid', 'configured_seconds', 'started',
                 'local_deadline', 'enclosing_deadline', 'effective_deadline', 'stage',
                 'creation_attempts', 'creation_succeeded', 'failure_count', 'failures',
                 'first_failure_ref', 'last_failure_ref', 'terminal', 'rollback', 'updated',
                 'utc_regressed'}


def _wire_require(ok: bool, detail: str = 'invalid startup diagnostic structure') -> None:
    if not ok:
        raise ValueError(detail)


def _wire_object(value, keys) -> None:
    _wire_require(type(value) is dict and set(value) == set(keys), 'diagnostic keys/type')


def _wire_int(value, minimum=-_WIRE_INT) -> None:
    _wire_require(type(value) is int and minimum <= value <= _WIRE_INT, 'diagnostic integer')


def _wire_number(value, minimum=None, positive=False) -> None:
    _wire_require(type(value) in (int, float), 'diagnostic numeric type')
    try:
        finite = math.isfinite(value)
    except OverflowError:
        finite = False
    _wire_require(finite and (minimum is None or value >= minimum) and
                  (not positive or value > 0), 'diagnostic finite numeric domain')


def _wire_utc(value):
    _wire_require(type(value) is str and re.fullmatch(r'[0-9]{4}-[0-9]{2}-[0-9]{2}T[0-9]{2}:[0-9]{2}:[0-9]{2}Z', value) is not None,
                  'diagnostic UTC')
    return datetime.datetime.strptime(value, '%Y-%m-%dT%H:%M:%SZ')


def _wire_stamp(value) -> None:
    _wire_object(value, {'utc', 'mono'})
    _wire_utc(value['utc']); _wire_number(value['mono'], minimum=0)


def _wire_span(value) -> None:
    _wire_object(value, {'start', 'end', 'utc_regressed'})
    _wire_stamp(value['start']); _wire_stamp(value['end'])
    _wire_require(value['start']['mono'] <= value['end']['mono'] and
                  type(value['utc_regressed']) is bool and
                  value['utc_regressed'] == (_wire_utc(value['end']['utc']) < _wire_utc(value['start']['utc'])),
                  'diagnostic span order')


def _wire_within(inner, outer) -> None:
    _wire_require(outer['start']['mono'] <= inner['start']['mono'] <= inner['end']['mono'] <= outer['end']['mono'],
                  'diagnostic nested span')


def diagnostic_stamp() -> dict:
    value = {'utc': now_iso(), 'mono': time.monotonic()}
    _wire_stamp(value)
    return value


def diagnostic_span(start, end) -> dict:
    value = {'start': start, 'end': end, 'utc_regressed': _wire_utc(end['utc']) < _wire_utc(start['utc'])}
    _wire_span(value)
    return value


def diagnostic_text(value: str) -> dict:
    _wire_require(type(value) is str, 'diagnostic text type')
    data = value.encode('utf-8', errors='strict')
    prefix = data[:2048].decode('utf-8', errors='ignore')
    truncated = len(prefix.encode('utf-8')) != len(data)
    return {'prefix': prefix, 'utf8_bytes': len(data), 'sha256': sha256_bytes(data),
            'truncated': truncated, 'hash_scope': 'full_unretained' if truncated else 'full_retained'}


def _wire_text(value, *, operand=False) -> str | None:
    _wire_object(value, {'prefix', 'utf8_bytes', 'sha256', 'truncated', 'hash_scope'})
    _wire_require(type(value['prefix']) is str, 'diagnostic prefix type')
    data = value['prefix'].encode('utf-8', errors='strict')
    _wire_int(value['utf8_bytes'], minimum=0)
    _wire_require(type(value['hash_scope']) is str and len(data) <= 2048 and type(value['truncated']) is bool and
                  type(value['sha256']) is str and re.fullmatch(r'[0-9a-f]{64}', value['sha256']) is not None,
                  'diagnostic text/hash bound')
    if value['truncated']:
        _wire_require(value['hash_scope'] == 'full_unretained' and value['utf8_bytes'] > len(data),
                      'diagnostic supplied truncation')
        return None  # Its missing suffix/full hash is NOT verified by the reader.
    _wire_require(value['hash_scope'] == 'full_retained' and value['utf8_bytes'] == len(data) and
                  value['sha256'] == sha256_bytes(data), 'diagnostic retained hash')
    if operand:
        _wire_require(value['prefix'] == value['prefix'].strip(), 'diagnostic stripped operand')
    return value['prefix']


def diagnostic_encoding(value) -> bytes:
    return (json.dumps(value, sort_keys=True, indent=2, ensure_ascii=True, allow_nan=False) + '\n').encode('utf-8')


def bound_diagnostics(value: dict, limit: int) -> dict:
    """Deterministic scalar-prefix reduction; full lengths/hashes never change."""
    result = copy.deepcopy(value)
    texts = []
    def visit(node, path=()):
        if type(node) is dict:
            if set(node) == {'prefix', 'utf8_bytes', 'sha256', 'truncated', 'hash_scope'}:
                _wire_text(node); texts.append((path, node))
            else:
                for key in sorted(node): visit(node[key], path + (str(key),))
        elif type(node) is list:
            for index, row in enumerate(node): visit(row, path + (str(index),))
    visit(result)
    while len(diagnostic_encoding(result)) > limit:
        available = [(path, text) for path, text in texts if text['prefix']]
        _wire_require(bool(available), 'diagnostic fixed metadata exceeds encoded bound')
        path, text = min(available, key=lambda item: (-len(item[1]['prefix'].encode('utf-8')), item[0]))
        text['prefix'] = text['prefix'][:-1]
        text['truncated'] = True; text['hash_scope'] = 'full_unretained'
    return result


def diagnostic_probe(operation, start, end, state, *, detail='', result=None, exc=None,
                     operand=None, ppid=None, witness=None) -> dict:
    # ProcessSnapshot already carries the actual caught Python class/errno. Never
    # invent a ToolFailure type for a completed nonzero native return code.
    error_class = type(exc).__name__ if exc is not None else getattr(result, 'error_class', None)
    error_errno = getattr(exc, 'errno', None) if exc is not None else getattr(result, 'errno', None)
    return {'operation': operation, 'span': diagnostic_span(start, end), 'state': state,
            'capable': state != 'unavailable', 'returncode': None if error_class else getattr(result, 'returncode', None),
            'error_class': error_class, 'errno': error_errno,
            'diagnostic': diagnostic_text(str(detail)[:DIAGNOSTIC_LIMIT]),
            'operand': diagnostic_text(operand) if operand is not None else None,
            'target_ppid': ppid, 'observer_witness': witness}


def _wire_probe(value, operation, span, observer_pid=None) -> str | None:
    _wire_object(value, {'operation', 'span', 'state', 'capable', 'returncode', 'error_class',
                         'errno', 'diagnostic', 'operand', 'target_ppid', 'observer_witness'})
    _wire_require(type(value['operation']) is str and value['operation'] == operation and
                  type(value['capable']) is bool and type(value['state']) is str and value['state'] in {'present', 'absent', 'unavailable'}, 'diagnostic probe classification')
    _wire_span(value['span']); _wire_within(value['span'], span)
    for key in ('returncode', 'errno'):
        if value[key] is not None: _wire_int(value[key])
    if value['error_class'] is not None:
        _wire_require(type(value['error_class']) is str and
                      re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]{0,127}', value['error_class']) is not None and
                      value['returncode'] is None, 'diagnostic caught error')
    else:
        _wire_require(value['errno'] is None and value['returncode'] is not None, 'diagnostic actual result')
    diagnostic = _wire_text(value['diagnostic'])
    operand = _wire_text(value['operand'], operand=True) if value['operand'] is not None else None
    if value['capable']:
        _wire_require(value['state'] in {'present', 'absent'} and value['error_class'] is None and
                      diagnostic == '', 'diagnostic capable probe')
        if value['state'] == 'present':
            _wire_require(value['returncode'] == 0 and value['operand'] is not None, 'diagnostic present operand')
            if operand is not None: _wire_require(_signature_command(operand) is not None, 'diagnostic full signature')
        elif operation == 'ps-selected':
            _wire_require(value['returncode'] in (0, 1) and operand == '', 'diagnostic selected absence')
        else:
            _wire_require(value['returncode'] == 0 and value['operand'] is None and value['target_ppid'] is None,
                          'diagnostic census absence')
    else:
        _wire_require(value['state'] == 'unavailable', 'diagnostic incapable probe')
    if operation == 'ps-selected':
        _wire_require(value['target_ppid'] is None and value['observer_witness'] is None, 'diagnostic selected fields')
    elif value['capable']:
        _wire_int(value['observer_witness'], minimum=1)
        if observer_pid is not None: _wire_require(value['observer_witness'] == observer_pid, 'diagnostic observer binding')
        if value['state'] == 'present': _wire_int(value['target_ppid'], minimum=0)
    else:
        _wire_require(value['operand'] is None and value['target_ppid'] is None and value['observer_witness'] is None,
                      'diagnostic unavailable census fields')
    return operand


def _validate_process_pair(pair, reason, state, observed_at, observer_pid=None) -> None:
    _wire_object(pair, _PAIR_KEYS)
    _wire_require(type(pair['version']) is int and pair['version'] == 1 and
                  type(pair['expected_signature_supplied']) is bool and type(reason) is str and reason in _REASONS,
                  'diagnostic pair version/reason')
    _wire_require(type(state) is str, 'diagnostic state type')
    _wire_utc(observed_at)
    _wire_span(pair['span']); _wire_require(observed_at == pair['span']['end']['utc'], 'diagnostic observation time')
    selected, census = pair['selected'], pair['census']
    if reason == 'invalid_target':
        _wire_require(state == 'unavailable' and pair['pid'] is None and selected is None and census is None,
                      'diagnostic invalid target')
    else:
        _wire_int(pair['pid'], minimum=1)
        so = _wire_probe(selected, 'ps-selected', pair['span'], observer_pid)
        co = None
        if census is not None:
            _wire_require(selected['capable'], 'diagnostic census before selected capability')
            co = _wire_probe(census, 'ps-census', pair['span'], observer_pid)
            _wire_require(selected['span']['end']['mono'] <= census['span']['start']['mono'], 'diagnostic probe order')
        if reason == 'selected_failure':
            _wire_require(state == 'unavailable' and not selected['capable'] and census is None)
        elif reason == 'census_failure':
            _wire_require(state == 'unavailable' and selected['capable'] and census is not None and not census['capable'])
        else:
            _wire_require(census is not None and selected['capable'] and census['capable'])
            statuses = (selected['state'], census['state'])
            if reason == 'selected_census_presence_drift':
                _wire_require(state == 'unavailable' and set(statuses) == {'present', 'absent'})
            elif reason == 'confirmed_absent':
                _wire_require(state == 'absent' and statuses == ('absent', 'absent'))
            else:
                _wire_require(statuses == ('present', 'present'))
                if reason == 'selected_census_signature_drift':
                    _wire_require(state == 'unavailable' and (so is None or co is None or so != co))
                else:
                    _wire_require(state == 'mismatch' and pair['expected_signature_supplied'] and
                                  (so is None or co is None or so == co))
    _wire_require(len(diagnostic_encoding(pair)) <= 65536, 'diagnostic encoded pair bound')


def diagnostic_error(exc: BaseException) -> dict:
    return {'error_class': type(exc).__name__, 'errno': getattr(exc, 'errno', None),
            'message': diagnostic_text(str(exc))}


def _wire_fault(value, phases, retained, span):
    _wire_object(value, {'phase', 'at', 'error', 'observation_ref'})
    _wire_require(type(value['phase']) is str and value['phase'] in phases, 'diagnostic fault phase')
    _wire_stamp(value['at']); _wire_require(span['start']['mono'] <= value['at']['mono'] <= span['end']['mono'])
    _wire_object(value['error'], {'error_class', 'errno', 'message'})
    error = value['error']
    _wire_require(type(error['error_class']) is str and re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]{0,127}', error['error_class']) is not None)
    if error['errno'] is not None: _wire_int(error['errno'])
    _wire_text(error['message'])
    ref = value['observation_ref']
    if ref is not None:
        _wire_int(ref, minimum=1); _wire_require(ref in retained, 'diagnostic dangling fault reference')


def _validate_startup_evidence(parent: dict) -> None:
    """Validate optional evidence in the existing process reader; never authority."""
    if 'startup_evidence' not in parent:
        return
    v = parent['startup_evidence']
    _wire_object(v, _STARTUP_KEYS)
    _wire_require(type(parent.get('schema_version')) is int and parent['schema_version'] == 1 and
                  type(parent.get('process_schema_version')) is int and parent['process_schema_version'] == 2 and
                  'record_origin' not in parent and 'recovery' not in parent, 'startup parent origin/version')
    for token in (parent.get('launch_token'), v['launch_token']):
        _wire_require(type(token) is str and re.fullmatch(r'[0-9a-f]{32}', token) is not None, 'startup token')
    _wire_int(parent.get('initiator_pid'), minimum=1); _wire_int(v['observer_pid'], minimum=1)
    _wire_require(v['launch_token'] == parent['launch_token'] and v['observer_pid'] == parent['initiator_pid'])
    _wire_require(type(v['version']) is int and v['version'] == 1 and type(v['creation_succeeded']) is bool)
    _wire_number(v['configured_seconds'], positive=True); _wire_stamp(v['started']); _wire_stamp(v['updated'])
    span = diagnostic_span(v['started'], v['updated'])
    _wire_require(type(v['utc_regressed']) is bool and v['utc_regressed'] == span['utc_regressed'])
    for key in ('local_deadline', 'effective_deadline'): _wire_number(v[key], minimum=0)
    if v['enclosing_deadline'] is not None: _wire_number(v['enclosing_deadline'], minimum=0)
    _wire_require(v['local_deadline'] == v['started']['mono'] + v['configured_seconds'] and
                  v['effective_deadline'] == (v['local_deadline'] if v['enclosing_deadline'] is None else
                                              min(v['local_deadline'], v['enclosing_deadline'])), 'startup effective bound')
    _wire_int(v['creation_attempts'], minimum=0); _wire_int(v['failure_count'], minimum=0)
    _wire_require(type(v['failures']) is list and len(v['failures']) <= 2)
    c = v['creation_attempts'] - int(v['creation_succeeded'])
    q = int(bool(v['failures']) and v['failures'][-1].get('stage') == 'final') if all(type(z) is dict for z in v['failures']) else -1
    _wire_require(c >= 0 and q in (0, 1) and v['failure_count'] == c + q and (not q or v['creation_succeeded']), 'startup attempts/count')
    expected = [] if not v['failure_count'] else [1] if v['failure_count'] == 1 else [1, v['failure_count']]
    actual = []
    last_end = None
    pids = set()
    for failure in v['failures']:
        _wire_object(failure, {'id', 'stage', 'attempt', 'state', 'reason', 'observed_at', 'diagnostics'})
        _wire_int(failure['id'], minimum=1); _wire_int(failure['attempt'], minimum=1)
        _wire_require(type(failure['stage']) is str and type(failure['state']) is str and
                      failure['stage'] in {'creation', 'final'} and failure['state'] in {'unavailable', 'absent', 'mismatch'})
        if failure['stage'] == 'creation':
            _wire_require(failure['id'] == failure['attempt'] <= c and not failure['diagnostics']['expected_signature_supplied'] and
                          failure['reason'] != 'signature_mismatch', 'startup creation failure')
        else: _wire_require(failure['id'] == c + 1 and failure['attempt'] == 1)
        validate_process_pair(failure['diagnostics'], failure['reason'], failure['state'], failure['observed_at'], v['observer_pid'])
        fs = failure['diagnostics']['span']; _wire_within(fs, span)
        if last_end is not None: _wire_require(last_end <= fs['start']['mono'], 'startup failure order')
        last_end = fs['end']['mono']; actual.append(failure['id'])
        if failure['diagnostics']['pid'] is not None: pids.add(failure['diagnostics']['pid'])
    _wire_require(actual == expected and v['first_failure_ref'] == (expected[0] if expected else None) and
                  v['last_failure_ref'] == (expected[-1] if expected else None), 'startup retained failure references')
    for ref in (v['first_failure_ref'], v['last_failure_ref']):
        if ref is not None: _wire_int(ref, minimum=1)
    _wire_require(len(pids) <= 1 and ('pid' not in parent or not pids or pids == {parent['pid']}), 'startup diagnostic target binding')
    if v['creation_succeeded']:
        _wire_int(parent.get('pid'), minimum=1)
        _wire_require(type(parent.get('signature')) is str and _signature_command(parent['signature']) is not None, 'startup coherent parent identity')
    else: _wire_require('signature' not in parent, 'startup unverified signature')
    if v['terminal'] is not None:
        _wire_fault(v['terminal'], _TERMINAL_PHASES, expected, span)
        if last_end is not None: _wire_require(v['terminal']['at']['mono'] >= last_end, 'startup terminal before refusal')
    if v['rollback'] is not None:
        _wire_require(v['terminal'] is not None)
        _wire_fault(v['rollback'], _ROLLBACK_PHASES, expected, span)
        _wire_require(v['rollback']['at']['mono'] >= v['terminal']['at']['mono'], 'startup rollback order')
    if q:
        _wire_require(v['terminal'] is not None and v['terminal']['phase'] == 'final_observation' and
                      v['terminal']['observation_ref'] == expected[-1])
    _wire_require(type(v['stage']) is str and v['stage'] in {'creation', 'readiness', 'final', 'complete', 'failed'})
    if v['stage'] == 'failed':
        _wire_require(v['terminal'] is not None and parent.get('phase') in {'launch_pending', 'uncertain_residual'})
    else:
        _wire_require(v['terminal'] is None and v['rollback'] is None and not q and v['updated']['mono'] <= v['effective_deadline'])
        if v['stage'] == 'creation':
            _wire_require(not v['creation_succeeded'] and parent.get('phase') == 'launch_pending' and 'pid' not in parent and 'signature' not in parent)
        else:
            _wire_require(v['creation_succeeded'] and parent.get('phase') == ('running' if v['stage'] == 'complete' else 'launch_pending'))
    _wire_require(len(diagnostic_encoding(v)) <= 196608, 'startup encoded envelope bound')


def validate_process_pair(pair, reason, state, observed_at, observer_pid=None) -> None:
    try:
        _validate_process_pair(pair, reason, state, observed_at, observer_pid)
    except (KeyError, TypeError, AttributeError, OverflowError, UnicodeError) as exc:
        raise ValueError("malformed process diagnostic payload") from exc


def validate_startup_evidence(parent: dict) -> None:
    try:
        _validate_startup_evidence(parent)
    except (KeyError, TypeError, AttributeError, OverflowError, UnicodeError) as exc:
        raise ValueError("malformed startup diagnostic payload") from exc
