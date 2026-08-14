"""Configuration and durable-state primitives for the Lean slot controller."""

from __future__ import annotations

import hashlib
import json
import os
import secrets
import tempfile
import time
from contextlib import contextmanager
from dataclasses import dataclass
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
    """An invariant failed and the requested slot operation was refused."""


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
        value = json.loads(path.read_text(encoding="utf-8"))
    except FileNotFoundError as exc:
        raise SlotError(f"missing state file: {path}") from exc
    except (OSError, json.JSONDecodeError) as exc:
        raise SlotError(f"invalid state file {path}: {exc}") from exc
    if not isinstance(value, dict):
        raise SlotError(f"state file must contain a JSON object: {path}")
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
        if raw.get("schema_version") != SCHEMA_VERSION:
            raise SlotError(
                f"unsupported inventory schema: {raw.get('schema_version')!r}"
            )
        if raw.get("max_active_slots") != 3 or set(raw.get("slots", {})) != {
            "1",
            "2",
            "3",
        }:
            raise SlotError(
                "inventory must define exactly the global slots 1, 2, and 3"
            )
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
        _ = inventory.client_auth_mode
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
        if not path.exists():
            if required:
                raise SlotError(f"slot wt{number} is not leased")
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


def process_start_signature(pid: int) -> str | None:
    """Return a stable-enough host signature to defend against PID reuse."""
    if pid <= 0:
        return None
    try:
        import subprocess

        result = subprocess.run(
            ["ps", "-p", str(pid), "-o", "lstart=", "-o", "command="],
            check=False,
            capture_output=True,
            text=True,
        )
    except OSError:
        return None
    value = result.stdout.strip()
    return value or None


def process_matches(pid: int, signature: str | None) -> bool:
    return bool(signature and process_start_signature(pid) == signature)
