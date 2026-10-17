"""Configuration and durable-state primitives for the Lean slot controller."""

from __future__ import annotations

import hashlib
import datetime
import ctypes
try:
    import fcntl
except ImportError:  # Ordinary legacy callers retain their portable protocol.
    fcntl = None
import stat
import re
import subprocess
import json
import os
import secrets
import tempfile
import time
import threading
import sys
from contextlib import contextmanager
from contextvars import ContextVar
from dataclasses import dataclass, field, replace
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


def fsync_directory(path: Path) -> None:
    """Make a directory-entry boundary durable or refuse the transaction."""
    try:
        fd = os.open(path, os.O_RDONLY)
        try:
            os.fsync(fd)
        finally:
            os.close(fd)
    except OSError as exc:
        raise SlotError(f"directory durability unavailable: {path}: {exc}") from exc


def durable_json(path: Path, value: dict[str, Any]) -> None:
    """Atomic complete bytes plus directory durability for transaction journals."""
    atomic_json(path, value)
    fsync_directory(path.parent)


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
def observation_budget(seconds: float) -> Iterator[None]:
    current = _OBSERVATION_DEADLINE.get()
    deadline = time.monotonic() + seconds
    token = _OBSERVATION_DEADLINE.set(min(current, deadline) if current is not None else deadline)
    try:
        yield
    finally:
        _OBSERVATION_DEADLINE.reset(token)


@contextmanager
def directory_lock(path: Path, *, purpose: str,
                   checkpoint: CheckpointLockContext | None = None) -> Iterator[None]:
    """Portable fail-closed lock implemented by atomic directory creation."""
    if checkpoint is not None:
        if type(checkpoint) is not CheckpointLockContext:
            raise SlotError("invalid internal checkpoint lock context")
        try:
            with checkpoint.hold(path, purpose=purpose):
                yield
        except OSError as exc:
            raise SlotError(f"checkpoint lock filesystem observation/effect refused: {exc}") from exc
        return
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


_CP_PROTOCOL = "lean-checkpoint-lock/flock-v1"
_CP_HELD: dict[tuple[int, int], int] = {}
_CP_THREADS = threading.Lock()


def _checkpoint_after_fork() -> None:
    # Closing a copied description does not unlock a surviving parent's/flock
    # mutator's description. An arbitrary fork cannot continue the transaction.
    global _CP_THREADS
    for fd in tuple(_CP_HELD.values()):
        try:
            os.close(fd)
        except OSError:
            pass
    _CP_HELD.clear()
    _CP_THREADS = threading.Lock()


if hasattr(os, "register_at_fork"):
    os.register_at_fork(after_in_child=_checkpoint_after_fork)


def _checkpoint_rename(parent: int, source: str, destination: str) -> None:
    """The measured native no-replace operation; deliberately no fallback."""
    symbol, flag = ("renameatx_np", 4) if sys.platform == "darwin" else ("renameat2", 1)
    if sys.platform not in {"darwin", "linux"}:
        raise SlotError("checkpoint no-replace filesystem API is unsupported")
    try:
        function = getattr(ctypes.CDLL(None, use_errno=True), symbol)
    except AttributeError as exc:
        raise SlotError("checkpoint native no-replace API is unavailable") from exc
    function.argtypes = [ctypes.c_int, ctypes.c_char_p, ctypes.c_int, ctypes.c_char_p, ctypes.c_uint]
    function.restype = ctypes.c_int
    if function(parent, os.fsencode(source), parent, os.fsencode(destination), flag):
        number = ctypes.get_errno()
        raise SlotError(f"checkpoint native no-replace {source} -> {destination}: {os.strerror(number)}")


def _checkpoint_identity(value: os.stat_result) -> list[int]:
    return [value.st_dev, value.st_ino]


def _checkpoint_file(fd: int, *, directory: bool = False) -> os.stat_result:
    value = os.fstat(fd)
    valid_type = stat.S_ISDIR(value.st_mode) if directory else stat.S_ISREG(value.st_mode)
    if (not valid_type or value.st_uid != os.getuid() or stat.S_IMODE(value.st_mode) != (0o700 if directory else 0o600)
            or (not directory and value.st_nlink != 1)):
        raise SlotError("checkpoint lock member type/owner/mode/link count is unsafe")
    return value


def _checkpoint_read_at(parent: int, name: str) -> tuple[bytes, list[int]]:
    fd = os.open(name, os.O_RDONLY | os.O_NOFOLLOW | os.O_CLOEXEC, dir_fd=parent)
    try:
        before = _checkpoint_file(fd)
        if before.st_size > MAX_JSON_BYTES:
            raise SlotError("checkpoint lock metadata exceeds bound")
        data = os.read(fd, MAX_JSON_BYTES + 1)
        after = os.fstat(fd)
        entry = os.stat(name, dir_fd=parent, follow_symlinks=False)
        stamp = lambda value: (value.st_dev, value.st_ino, value.st_mode, value.st_size, value.st_mtime_ns, value.st_ctime_ns)
        if stamp(before) != stamp(after) or _checkpoint_identity(entry) != _checkpoint_identity(before) or len(data) != before.st_size:
            raise SlotError("checkpoint lock metadata changed while reading")
        return data, _checkpoint_identity(before)
    finally:
        os.close(fd)


class CheckpointLockRetired(SlotError):
    """Exact abandoned scope preserved; retry starts a new acquisition interval."""


@dataclass
class CheckpointLockContext:
    """Internal CP admission, never inferred from a purpose or ambient setting.

    Construction is effect-free. The transaction supplies exact validated domain,
    request and lease transitions, and the native mutation reconciliation reader.
    The context is a lock capability only; all transaction authority is rechecked.
    """
    state_root: Path
    binding: dict[str, Any]
    transaction: str
    operation: str
    generations: tuple[str, ...]
    lease_hashes: tuple[str, ...]
    request_digest: str
    quiescent: Any = field(repr=False)
    pid: int = field(default_factory=os.getpid, init=False)
    held: list[dict[str, Any]] = field(default_factory=list, init=False, repr=False)
    _admitted: tuple = field(init=False, repr=False)
    _root_identity: tuple = field(init=False, repr=False)

    def __post_init__(self) -> None:
        if (self.state_root != self.state_root.resolve(strict=True) or
                self.binding.get("state_root") != str(self.state_root) or
                self.operation not in {"preserve", "recover", "observe-release", "resume", "recover-resume"} or
                re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._-]{0,79}", self.transaction) is None or
                not self.generations or not self.lease_hashes or
                any(re.fullmatch(r"[0-9a-f]{64}", value) is None for value in (*self.generations, *self.lease_hashes, self.request_digest)) or
                not callable(self.quiescent)):
            raise SlotError("invalid validated internal checkpoint context")
        root = os.stat(self.state_root, follow_symlinks=False)
        if not stat.S_ISDIR(root.st_mode) or root.st_uid != os.getuid() or stat.S_IMODE(root.st_mode) & 0o022:
            raise SlotError("checkpoint state root is not privately owned")
        self.binding = json.loads(json.dumps(self.binding))
        self._root_identity = tuple(_checkpoint_identity(root))
        self._admitted = self._admission_identity()

    def _admission_identity(self) -> tuple:
        return (str(self.state_root), canonical_digest(self.binding), self.transaction, self.operation,
                self.generations, self.lease_hashes, self.request_digest, self.pid, id(self.quiescent))

    def _validate_admission(self) -> None:
        if self._admission_identity() != self._admitted:
            raise SlotError("checkpoint internal context changed after validation")
        root = os.stat(self.state_root, follow_symlinks=False)
        if (not stat.S_ISDIR(root.st_mode) or root.st_uid != os.getuid() or
                stat.S_IMODE(root.st_mode) & 0o022 or tuple(_checkpoint_identity(root)) != self._root_identity):
            raise SlotError("checkpoint trusted state root identity/permissions changed")

    def _domain(self) -> str:
        return canonical_digest({key: value for key, value in self.binding.items() if key != "selected_slot"})

    @staticmethod
    def _guard_domain(binding: dict) -> str:
        # The permanent inode belongs to the physical shared lock universe,
        # rather than one role/slot/checkpoint or mutable implementation bytes.
        if (not isinstance(binding.get("state_root"), str) or not isinstance(binding.get("domains", []), list) or
                any(not isinstance(row, dict) or not isinstance(row.get("inventory"), dict) or
                    not isinstance(row["inventory"].get("path"), str) or
                    not isinstance(row.get("repo"), str) or not isinstance(row.get("state_root"), str)
                    for row in binding.get("domains", []))):
            raise SlotError("checkpoint lock physical domain metadata is malformed")
        return canonical_digest({"state_root": binding["state_root"], "roots": sorted(
            ({"inventory": row["inventory"]["path"], "repo": row["repo"], "state_root": row["state_root"]}
             for row in binding.get("domains", [])), key=lambda row: row["inventory"])})

    def check(self) -> None:
        self._validate_admission()
        if os.getpid() != self.pid:
            raise SlotError("fork child cannot continue a checkpoint transaction")
        for held in self.held:
            parent = os.fstat(held["parent"])
            current = os.stat(held["path"].parent, follow_symlinks=False)
            if _checkpoint_identity(parent) != _checkpoint_identity(current):
                raise SlotError("checkpoint trusted lock parent was substituted")
            guard = _checkpoint_file(held["fd"])
            entry = os.stat(held["guard_name"], dir_fd=held["parent"], follow_symlinks=False)
            if _checkpoint_identity(guard) != _checkpoint_identity(entry):
                raise SlotError("checkpoint permanent guard inode was substituted")
            self._facade(held["parent"], held["path"].name, held["owner"], held["guard"])

    def descriptors(self) -> tuple[int, ...]:
        self.check()
        if len(self.held) != 2:
            raise SlotError("checkpoint mutation requires target-slot and lifecycle guards")
        return tuple(value["fd"] for value in self.held)

    def boundary(self, phase: str) -> None:
        """Native crash seam; no runtime/environment selector."""

    def _parent(self, path: Path) -> int:
        if path.parent != self.state_root / "locks" or path.name not in {"supervisor.lock", "wt1.lock", "wt2.lock", "wt3.lock"}:
            raise SlotError("checkpoint context cannot select another lock domain")
        fd = os.open("/", os.O_RDONLY | os.O_DIRECTORY | os.O_CLOEXEC)
        try:
            for component in path.parent.parts[1:]:
                try:
                    child = os.open(component, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC, dir_fd=fd)
                except FileNotFoundError:
                    # Only the existing state owner's locks child may be created.
                    if component != "locks" or _checkpoint_identity(os.fstat(fd)) != _checkpoint_identity(os.stat(self.state_root)):
                        raise SlotError("checkpoint trusted parent is missing")
                    os.mkdir(component, 0o700, dir_fd=fd)
                    os.fsync(fd)
                    child = os.open(component, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC, dir_fd=fd)
                os.close(fd)
                fd = child
            value = os.fstat(fd)
            if value.st_uid != os.getuid() or stat.S_IMODE(value.st_mode) & 0o022:
                raise SlotError("checkpoint lock parent is not privately owned")
            return fd
        except BaseException:
            os.close(fd)
            raise

    def _facade(self, parent: int, name: str, expected: dict | None, guard: list[int], *, history: str | None = None) -> dict:
        fd = os.open(name, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC, dir_fd=parent)
        try:
            identity = _checkpoint_identity(_checkpoint_file(fd, directory=True))
            if os.listdir(fd) != ["owner.json"]:
                raise SlotError("checkpoint facade has unknown or missing members")
            data, member = _checkpoint_read_at(fd, "owner.json")
            try:
                record = json.loads(data)
            except (ValueError, UnicodeError) as exc:
                raise SlotError("checkpoint facade metadata is unrecognized") from exc
            keys = {"protocol", "nonce", "pid", "signature", "birth", "purpose", "domain", "domain_binding", "transaction", "operation", "generation", "lease_sha256", "request_digest", "guard", "directory", "member", "publication", "retirement"}
            if (not isinstance(record, dict) or set(record) != keys or record.get("protocol") != _CP_PROTOCOL or
                    record.get("directory") != identity or record.get("member") != member or
                    record.get("guard") != guard or not isinstance(record.get("domain_binding"), dict) or
                    record.get("domain") != canonical_digest(record["domain_binding"]) or
                    self._guard_domain(record["domain_binding"]) != self._guard_domain(self.binding) or
                    (history is None and record.get("domain") != self._domain()) or
                    (history is None and (record.get("transaction") != self.transaction or record.get("generation") not in self.generations or
                    record.get("lease_sha256") not in self.lease_hashes or record.get("request_digest") != self.request_digest)) or
                    any(re.fullmatch(r"[0-9a-f]{64}", str(record.get(key))) is None for key in ("generation", "lease_sha256", "request_digest")) or
                    re.fullmatch(r"[A-Za-z0-9][A-Za-z0-9._-]{0,79}", str(record.get("transaction"))) is None or
                    record.get("operation") not in {"preserve", "recover", "observe-release", "resume", "recover-resume"} or
                    not record.get("signature") or signature_birth(record["signature"]) != record.get("birth") or
                    record.get("publication") != (history or name) or
                    record.get("retirement") != f".{history or name}.cp-history-{record.get('nonce')}" or
                    (history is not None and name not in {record["retirement"], f".{history}.cp-stage-{record.get('nonce')}"}) or
                    re.fullmatch(r"[0-9a-f]{48}", str(record.get("nonce"))) is None or
                    type(record.get("pid")) is not int or record["pid"] <= 0 or
                    (expected is not None and record != expected)):
                raise SlotError("checkpoint facade protocol/domain/generation/inode mismatch")
            return record
        finally:
            os.close(fd)

    def _retire(self, parent: int, name: str, record: dict, guard: list[int]) -> None:
        self._facade(parent, name, record, guard)
        self.quiescent()
        self.boundary("lock-retire-intent")
        self._facade(parent, name, record, guard)
        self.quiescent()
        _checkpoint_rename(parent, name, record["retirement"])
        # Only namespace durability remains; no protected work or legacy-path
        # access is permitted after the retirement linearization point.
        os.fsync(parent)
        self.boundary("lock-retired")

    @contextmanager
    def hold(self, path: Path, *, purpose: str) -> Iterator[None]:
        self._validate_admission()
        if os.getpid() != self.pid:
            raise SlotError("fork child cannot acquire a parent's checkpoint context")
        if fcntl is None or sys.platform not in {"darwin", "linux"}:
            raise SlotError("checkpoint selected native flock protocol is unsupported")
        if (not self.held and path.name != f"wt{self.binding.get('selected_slot')}.lock") or (self.held and (len(self.held) != 1 or path.name != "supervisor.lock")):
            raise SlotError("checkpoint lock order requires target slot then lifecycle")
        parent = self._parent(path)
        guard_name = path.name + ".cp-guard"
        fd = None
        registered = False
        published = False
        held = None
        try:
            encoded = (json.dumps({"protocol": _CP_PROTOCOL, "domain": self._guard_domain(self.binding), "path": str(path)}, sort_keys=True) + "\n").encode()
            try:
                fd = os.open(guard_name, os.O_RDWR | os.O_CREAT | os.O_EXCL | os.O_NOFOLLOW | os.O_CLOEXEC, 0o600, dir_fd=parent)
                if os.write(fd, encoded) != len(encoded):
                    raise SlotError("checkpoint permanent sidecar initialization incomplete")
                os.fsync(fd)
                os.fsync(parent)
            except FileExistsError:
                fd = os.open(guard_name, os.O_RDWR | os.O_NOFOLLOW | os.O_CLOEXEC, dir_fd=parent)
            guard = _checkpoint_identity(_checkpoint_file(fd))
            raw, identity = _checkpoint_read_at(parent, guard_name)
            if raw != encoded or identity != guard or os.get_inheritable(fd):
                raise SlotError("checkpoint permanent sidecar protocol/inode mismatch")
            with _CP_THREADS:
                key = tuple(guard)
                if key in _CP_HELD:
                    raise SlotError("checkpoint guard already held in this process/thread")
                _CP_HELD[key] = fd
                registered = True
            try:
                fcntl.flock(fd, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except OSError as exc:
                raise SlotError(f"checkpoint native guard unavailable/contended: {exc}") from exc
            self.boundary("lock-guard-held")
            self.quiescent()
            current_guard = os.stat(guard_name, dir_fd=parent, follow_symlinks=False)
            if _checkpoint_identity(current_guard) != guard:
                raise SlotError("checkpoint guard changed after native acquisition")
            for entry in os.listdir(parent):
                if entry.startswith(f".{path.name}.cp-"):
                    self._facade(parent, entry, None, guard, history=path.name)
            try:
                record = self._facade(parent, path.name, None, guard)
            except FileNotFoundError:
                record = None
            if record is not None:
                observation = observe_process(record["pid"], record["signature"])
                if observation.state not in {"absent", "mismatch"}:
                    raise SlotError("checkpoint abandoned facade native holder is not proven gone", observations=(observation,))
                self._retire(parent, path.name, record, guard)
                raise CheckpointLockRetired("checkpoint abandoned facade preserved in history; retry a fresh acquisition")
            nonce = secrets.token_hex(24)
            stage = f".{path.name}.cp-stage-{nonce}"
            os.mkdir(stage, 0o700, dir_fd=parent)
            stage_fd = os.open(stage, os.O_RDONLY | os.O_DIRECTORY | os.O_NOFOLLOW | os.O_CLOEXEC, dir_fd=parent)
            try:
                member = os.open("owner.json", os.O_WRONLY | os.O_CREAT | os.O_EXCL | os.O_CLOEXEC, 0o600, dir_fd=stage_fd)
                try:
                    self.boundary("lock-member-created")
                    observation = observe_process(os.getpid())
                    signature = observation.signature
                    if observation.state != "present" or not signature or not signature_birth(signature):
                        raise SlotError("checkpoint holder native birth unavailable", observations=(observation,))
                    record = {"protocol": _CP_PROTOCOL, "nonce": nonce, "pid": os.getpid(), "signature": signature,
                              "birth": signature_birth(signature), "purpose": purpose, "domain": self._domain(),
                              "domain_binding": {key: value for key, value in self.binding.items() if key != "selected_slot"},
                              "transaction": self.transaction, "operation": self.operation, "generation": self.generations[0],
                              "lease_sha256": self.lease_hashes[0], "request_digest": self.request_digest, "guard": guard,
                              "directory": _checkpoint_identity(os.fstat(stage_fd)), "member": _checkpoint_identity(os.fstat(member)),
                              "publication": path.name, "retirement": f".{path.name}.cp-history-{nonce}"}
                    data = (json.dumps(record, sort_keys=True) + "\n").encode()
                    if os.write(member, data) != len(data):
                        raise SlotError("checkpoint incomplete holder write")
                    os.fsync(member)
                    self.boundary("lock-member-flushed")
                finally:
                    os.close(member)
                os.fsync(stage_fd)
                self.boundary("lock-directory-flushed")
            finally:
                os.close(stage_fd)
            os.fsync(parent)
            self.boundary("lock-staged")
            _checkpoint_rename(parent, stage, path.name)
            published = True
            self.boundary("lock-publication-effect")
            os.fsync(parent)
            held = {"fd": fd, "parent": parent, "path": path, "guard_name": guard_name, "guard": guard, "owner": record}
            self.held.append(held)
            self.boundary("lock-published")
            self.check()
            yield
        finally:
            try:
                if published and held is not None:
                    self.check()
                    self.quiescent()
                    self._retire(parent, path.name, held["owner"], held["guard"])
            finally:
                if held in self.held:
                    self.held.remove(held)
                if registered:
                    with _CP_THREADS:
                        _CP_HELD.pop(key, None)
                # Never LOCK_UN: a bounded admitted exec may retain this same
                # open description after parent exception/death/timeout.
                if fd is not None:
                    os.close(fd)
                os.close(parent)


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
        if self.lease_path(number).exists():
            previous = read_json(self.lease_path(number))
            if previous.get("resume_admission") is not None and lease.get("resume_admission") != previous["resume_admission"]:
                raise SlotError("ordinary lease writer cannot erase or change checkpoint readiness")
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

    def __post_init__(self) -> None:
        object.__setattr__(self, "detail", str(self.detail)[:DIAGNOSTIC_LIMIT])

    def as_dict(self) -> dict[str, Any]:
        return {"state": self.state, "target": self.target, "operation": self.operation,
                "observed_at": self.observed_at, "returncode": self.returncode,
                "error_class": self.error_class, "errno": self.errno,
                "observed_identity": self.identity if self.identity is not None else self.signature,
                "diagnostic_text": self.detail}


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
    target = f"PID {pid}"
    def observed(state: str, value: str | None = None, detail: str = "", *, result=None, exc=None):
        return Observation(state, value, detail, getattr(exc, "errno", None), target=target,
                           operation="ps-selected", returncode=result.returncode if result else None,
                           error_class=type(exc).__name__ if exc else None)
    if type(pid) is not int or pid <= 0:
        return observed("unavailable", detail="no authoritative positive integer PID")
    try:
        result = subprocess.run(["ps", "-p", str(pid), "-o", "lstart=", "-o", "command="],
                                check=False, capture_output=True, text=True, timeout=observation_timeout())
    except (OSError, subprocess.TimeoutExpired, UnicodeError, ValueError) as exc:
        return observed("unavailable", detail=str(exc), exc=exc)
    if len(result.stdout) > MAX_OBSERVER_OUTPUT:
        return observed("unavailable", detail="selected process output exceeds bound", result=result)
    value = result.stdout.strip()
    if result.stderr.strip() or result.returncode not in {0, 1}:
        return observed("unavailable", detail=f"ps exit {result.returncode}: {result.stderr.strip()}", result=result)
    if value and (result.returncode != 0 or _signature_command(value) is None):
        return observed("unavailable", detail="malformed/partial/ambiguous selected process identity", result=result)
    census = process_snapshot()
    if census.state != "present":
        return observed("unavailable", detail=f"coherent process census unavailable: {census.detail}", result=result)
    row = next((item for item in census.rows if item.pid == pid), None)
    if not value and row is None:
        return observed("absent", detail="confirmed absent in capable process census", result=result)
    if not value or row is None or row.signature != value:
        return observed("unavailable", detail="selected/census target identity inconsistent", result=result)
    return observed("mismatch" if signature and value != signature else "present", value, result=result)


def signature_birth(signature: str) -> str | None:
    """The genuine legacy lstart precision, never a fabricated generation token."""
    return " ".join(signature.split()[:5]) if _signature_command(signature) is not None else None


class ShutdownSchedulerDiscrepancy(ValueError):
    """A fully checked pass differs only in same-suffix R versus S state."""

    def __init__(self, differences: list[tuple[int, str, str]]):
        self.context = repr(differences[:4])[:256]
        super().__init__("inconclusive R/S-only shutdown observation " + self.context)


def _shutdown_rs_only(selected: dict | None, complete: dict | None) -> bool:
    if selected is None or complete is None:
        return False
    left, right = selected["native_state"], complete["native_state"]
    return ({left[:1], right[:1]} == {"R", "S"} and left[1:] == right[1:] and
            {key: value for key, value in selected.items() if key != "native_state"} ==
            {key: value for key, value in complete.items() if key != "native_state"})


def _shutdown_refusal_detail(detail: str, first: str | None, last: str, attempt: int) -> str:
    # Diagnostic context is bounded and never reused as usable process evidence.
    width = max(32, (DIAGNOSTIC_LIMIT - 72) // 3)
    return (f"{detail[:width]}; first={str(first)[:width]}; "
            f"last=attempt={attempt} {last[:width]}")


def observe_shutdown_process(pid: int) -> Observation:
    """At most three fresh native passes inside one absolute shutdown budget."""
    first = None
    progress = {"last": "entry"}
    attempt = 0
    with observation_budget(10.0):
        try:
            for attempt in range(1, 4):
                observation_timeout()
                try:
                    result = _observe_shutdown_process_once(pid, progress)
                except ShutdownSchedulerDiscrepancy as exc:
                    first = exc.context if first is None else first
                    if attempt == 3:
                        raise
                    continue
                if result.state == "unavailable":
                    return replace(result, detail=_shutdown_refusal_detail(result.detail, first, progress["last"], attempt))
                observation_timeout()
                return result
        except (OSError, subprocess.TimeoutExpired, UnicodeError, ValueError) as exc:
            return Observation("unavailable", detail=_shutdown_refusal_detail(str(exc), first, progress["last"], attempt),
                               target=f"PID {pid}", operation="ps-shutdown-state", error_class=type(exc).__name__)


def _observe_shutdown_process_once(pid: int, progress: dict) -> Observation:
    """Coherent native state for shutdown only; Z remains present, never absent."""
    target = f"PID {pid}"
    def refusal(detail, exc=None):
        return Observation("unavailable", detail=detail, target=target,
                           operation="ps-shutdown-state", error_class=type(exc).__name__ if exc else None)
    if type(pid) is not int or pid <= 0:
        return refusal("invalid shutdown PID")
    def rows(output):
        observation_timeout()
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
        progress["last"] = "before native selected"
        selected = subprocess.run(["ps", "-p", str(pid), "-o", "pid=,ppid=,lstart=,stat=,command="],
                                  check=False, capture_output=True, text=True, timeout=observation_timeout())
        progress["last"] = f"native selected rc={selected.returncode} bytes={len(selected.stdout)}"
        observation_timeout()
        census = subprocess.run(["ps", "-axo", "pid=,ppid=,lstart=,stat=,command="],
                                check=False, capture_output=True, text=True, timeout=observation_timeout())
        progress["last"] = f"native census rc={census.returncode} bytes={len(census.stdout)}"
        observation_timeout()
        if selected.returncode not in (0, 1) or selected.stderr.strip() or census.returncode or census.stderr.strip():
            raise ValueError("native state observation failed")
        chosen, complete = rows(selected.stdout), rows(census.stdout)
        if os.getpid() not in complete or set(chosen) - {pid}:
            raise ValueError("native state census lacks witness or selected PID differs")
        if bool(chosen) != (selected.returncode == 0):
            raise ValueError("native state selected/census drift")
        if chosen.get(pid) != complete.get(pid):
            if _shutdown_rs_only(chosen.get(pid), complete.get(pid)):
                raise ShutdownSchedulerDiscrepancy([(pid, chosen[pid]["native_state"], complete[pid]["native_state"])])
            raise ValueError("native state selected/census drift")
        observation_timeout()
        return Observation("present" if pid in complete else "absent", target=target,
                           operation="ps-shutdown-state", identity=complete.get(pid))
    except ShutdownSchedulerDiscrepancy:
        raise
    except (OSError, subprocess.TimeoutExpired, UnicodeError, ValueError) as exc:
        return refusal(str(exc), exc)



def observe_shutdown_family(identities: dict[int, str], root: int, *,
                            max_identities: int = 4096) -> tuple[ProcessSnapshot, dict[int, Observation], dict[int, Observation]]:
    """At most three complete fresh batches; only R/S-only passes are discarded."""
    first = None
    progress = {"last": "entry"}
    attempt = 0
    with observation_budget(10.0):
        try:
            for attempt in range(1, 4):
                observation_timeout()
                try:
                    snapshot, generic, native = _observe_shutdown_family_once(identities, root, max_identities=max_identities, progress=progress)
                except ShutdownSchedulerDiscrepancy as exc:
                    first = exc.context if first is None else first
                    if attempt == 3:
                        raise
                    continue
                if snapshot.state == "unavailable":
                    return replace(snapshot, detail=_shutdown_refusal_detail(snapshot.detail, first, progress["last"], attempt)), {}, {}
                observation_timeout()
                return snapshot, generic, native
        except (OSError, subprocess.TimeoutExpired, UnicodeError, ValueError) as exc:
            return ProcessSnapshot("unavailable", detail=_shutdown_refusal_detail(str(exc), first, progress["last"], attempt),
                                   operation="ps-shutdown-family", error_class=type(exc).__name__, errno=getattr(exc, "errno", None)), {}, {}


def _observe_shutdown_family_once(identities: dict[int, str], root: int, *,
                                 max_identities: int, progress: dict) -> tuple[ProcessSnapshot, dict[int, Observation], dict[int, Observation]]:
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
            observation_timeout()
            fields = "pid=,ppid=,lstart=,stat=,command=" if native else "pid=,ppid=,lstart=,command="
            argv = ["ps", "-p", selection, "-o", fields] if selected else ["ps", "-axo", fields]
            label = ("native" if native else "generic") + (" selected" if selected else " census")
            progress["last"] = "before " + label
            value = subprocess.run(argv, check=False, capture_output=True, text=True,
                                   timeout=observation_timeout())
            progress["last"] = f"{label} rc={value.returncode} bytes={len(value.stdout)}"
            observation_timeout()
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
        generic, native, differences = {}, {}, []
        for pid, signature in identities.items():
            row, terminal = complete.get(pid), native_complete.get(pid)
            if selected.get(pid) != row:
                raise ValueError("shutdown family selected/census drift")
            if native_selected.get(pid) != terminal:
                if _shutdown_rs_only(native_selected.get(pid), terminal):
                    differences.append((pid, native_selected[pid]["native_state"], terminal["native_state"]))
                else:
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
        if differences:
            # A scheduling discrepancy cannot mask another retained-family defect.
            rooted = snapshot.descendants(root)
            if rooted - set(identities):
                raise ValueError("shutdown family has unretained descendant during scheduling discrepancy")
            if any(item.state == "mismatch" for item in generic.values()):
                raise ValueError("shutdown family retained identity mismatch during scheduling discrepancy")
            if (any(item.state == "present" for item in generic.values()) and
                    (root not in complete or native_complete[root]["native_state"].startswith("Z"))):
                raise ValueError("shutdown family root is not live during scheduling discrepancy")
            for pid, item in generic.items():
                if item.state == "absent":
                    continue
                ancestor, seen = pid, set()
                while ancestor != root:
                    if ancestor in seen or ancestor not in complete:
                        raise ValueError("shutdown family incomplete/cyclic during scheduling discrepancy")
                    seen.add(ancestor); ancestor = complete[ancestor].ppid
                    if ancestor not in identities:
                        raise ValueError("shutdown family reparented during scheduling discrepancy")
                    if (ancestor not in complete or ancestor not in native_complete or
                            generic[ancestor].state != "present" or
                            native_complete[ancestor]["native_state"].startswith("Z")):
                        raise ValueError("shutdown family ancestor is not independently present/exact/live during scheduling discrepancy")
            if root in complete and complete[root].ppid in rooted:
                raise ValueError("shutdown family root cycle during scheduling discrepancy")
            raise ShutdownSchedulerDiscrepancy(differences)
        observation_timeout()
        return snapshot, generic, native
    except ShutdownSchedulerDiscrepancy:
        raise
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
                                check=False, capture_output=True, text=True, timeout=2)
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
