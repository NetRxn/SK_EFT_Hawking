"""Durable nonaccepting source transactions inside the ADR-008 controller.

The journal records effects against an existing lease; it grants neither capacity
nor acceptance. Candidate entry validation runs before constructing a Controller.
"""
from __future__ import annotations

import copy
import datetime
import hashlib
import hmac
import json
import os
import re
import secrets
import shutil
import stat
import subprocess
import sys
import time
from dataclasses import dataclass, field
from pathlib import Path
from typing import Any

from .state import (Inventory, SlotError, CheckpointLockContext, MAX_JSON_BYTES, canonical_digest, durable_json,
                    exclusive_durable_json, fsync_directory, now_iso, read_json,
                    sha256_bytes, observe_process, observe_shutdown_process, process_snapshot, signature_birth)

SCHEMA = "lean-checkpoint/v1"
IDENTIFIER = re.compile(r"[a-zA-Z0-9][a-zA-Z0-9_-]{0,79}\Z")
OWNER_KEYS = ("owner_kind", "owner_pid", "owner_signature", "owner_session_hash")


class JournalSizeError(SlotError):
    """An oversized retained journal denies dispatch even when unrelated."""


def _git_executable() -> Path:
    reject_overrides()
    selected = shutil.which("git")
    if not selected:
        raise SlotError("checkpoint native Git prerequisite is missing")
    path = Path(selected).resolve(strict=True)
    fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
    try:
        before = os.fstat(fd)
        magic = os.read(fd, 4)
        after = os.fstat(fd)
        if (not stat.S_ISREG(before.st_mode) or stat.S_IMODE(before.st_mode) & 0o022 or
                (before.st_dev, before.st_ino, before.st_size, before.st_mtime_ns, before.st_ctime_ns) !=
                (after.st_dev, after.st_ino, after.st_size, after.st_mtime_ns, after.st_ctime_ns) or
                magic not in {b"\x7fELF", b"\xfe\xed\xfa\xcf", b"\xcf\xfa\xed\xfe", b"\xfe\xed\xfa\xce", b"\xce\xfa\xed\xfe",
                              b"\xca\xfe\xba\xbe", b"\xbe\xba\xfe\xca", b"\xca\xfe\xba\xbf", b"\xbf\xba\xfe\xca"}):
            raise SlotError("checkpoint refuses unproved Git script/helper executable")
    finally:
        os.close(fd)
    return path


def git(root: Path, *args: str, check: bool = True, input_data: bytes | None = None) -> bytes:
    # Read operations must not refresh the index or follow ambient Git redirects.
    env = dict(os.environ, GIT_OPTIONAL_LOCKS="0", GIT_NO_LAZY_FETCH="1")
    result = subprocess.run([str(_git_executable()), *args], cwd=root, env=env, capture_output=True, input=input_data)
    if check and (result.returncode or result.stderr):
        raise SlotError(f"checkpoint Git {args[0]} refused: {result.stderr.decode(errors='replace')}")
    return result.stdout


def text_git(root: Path, *args: str) -> str:
    return git(root, *args).decode().strip()


def regular_bytes(path: Path, *, maximum: int | None = None) -> bytes:
    """Observe the same readable regular inode before and after the actual read."""
    try:
        if path.resolve(strict=True) != path:
            raise SlotError(f"checkpoint input traverses a symlink: {path}")
        before = path.lstat()
        if not stat.S_ISREG(before.st_mode) or not before.st_mode & 0o444:
            raise SlotError(f"checkpoint input is not a readable regular file: {path}")
        if maximum is not None and before.st_size > maximum:
            raise JournalSizeError(f"checkpoint journal exceeds byte bound: {path}")
        with path.open("rb") as stream:
            opened = os.fstat(stream.fileno())
            if maximum is not None and opened.st_size > maximum:
                raise JournalSizeError(f"checkpoint journal exceeds byte bound: {path}")
            data = stream.read(maximum + 1) if maximum is not None else stream.read()
            final = os.fstat(stream.fileno())
        after = path.lstat()
        if maximum is not None and len(data) > maximum:
            raise JournalSizeError(f"checkpoint journal exceeds byte bound: {path}")
        identity = lambda s: (s.st_dev, s.st_ino, s.st_mode, s.st_size, s.st_mtime_ns, s.st_ctime_ns)
        if len({identity(s) for s in (before, opened, final, after)}) != 1:
            raise SlotError(f"checkpoint input changed during read: {path}")
        return data
    except OSError as exc:
        raise SlotError(f"checkpoint input unavailable: {path}: {exc}") from exc


def file_binding(path: Path) -> dict[str, Any]:
    data = regular_bytes(path)
    return {"path": str(path), "sha256": sha256_bytes(data)}


def journal_checked(path: Path, identifier: str) -> dict[str, Any]:
    value = json.loads(regular_bytes(path, maximum=MAX_JSON_BYTES))
    if (not isinstance(value, dict) or value.get("schema") != SCHEMA or value.get("id") != identifier or
            value.get("sourceReady") is not False):
        raise SlotError("checkpoint journal version/identity/nonacceptance mismatch")
    return value


def flush_directories(root: Path, leaves) -> None:
    directories = {root}
    for leaf in leaves:
        if not leaf.is_relative_to(root):
            raise SlotError("checkpoint durability directory escaped owning root")
        directory = leaf
        while directory != root:
            directories.add(directory)
            directory = directory.parent
    for directory in sorted(directories, key=lambda path: len(path.parts), reverse=True):
        if directory.resolve(strict=True) != directory:
            raise SlotError("checkpoint durability directory traverses a symlink")
        fsync_directory(directory)


def implementation_binding(root: Path, *, loaded: bool = False) -> dict[str, Any]:
    root = root.resolve(strict=True)
    package = root / "scripts" / "lean_slots"
    files = sorted(package.glob("*.py")) + [root / "scripts" / "slotctl.py"]
    if not files or not package.is_dir():
        raise SlotError("checkpoint implementation package unavailable")
    manifest = {str(path.relative_to(root)): sha256_bytes(regular_bytes(path)) for path in files}
    commit = text_git(root, "rev-parse", "HEAD")
    for name, digest in manifest.items():
        if sha256_bytes(git(root, "show", f"{commit}:{name}")) != digest:
            raise SlotError(f"checkpoint implementation is not exact committed source: {name}")
    if loaded:
        for name, module in tuple(sys.modules.items()):
            if name == __package__ or name.startswith(__package__ + "."):
                filename = getattr(module, "__file__", None)
                declared = getattr(getattr(module, "__spec__", None), "origin", None)
                if (not filename or not declared or Path(filename).resolve().parent != package or
                        Path(filename).resolve() != Path(declared).resolve() or Path(filename).is_symlink()):
                    raise SlotError("checkpoint imported implementation escaped the reviewed package")
        if Path(__file__).resolve().parent != package:
            raise SlotError("checkpoint loaded source is not the reviewed candidate")
    return {"root": str(root), "commit": commit, "files": manifest}


def inventory_binding(inv: Inventory) -> dict[str, Any]:
    from .supervisor import Supervisor
    common = Path(text_git(inv.repo_root, "rev-parse", "--git-common-dir"))
    common = (inv.repo_root / common).resolve()
    gitdir = Path(text_git(inv.repo_root, "rev-parse", "--absolute-git-dir")).resolve()
    if gitdir != common:
        raise SlotError("checkpoint inventory must name the canonical primary checkout")
    family, errors = Supervisor(inv)._role_inventories()
    if errors:
        raise SlotError("checkpoint canonical domain unavailable: " + "; ".join(errors))
    domains = []
    for item in family:
        domains.append({"inventory": file_binding(item.source), "repo": str(item.repo_root),
                        "domain": Supervisor._inventory_domain(item), "state_root": str(item.state_root)})
    return {"inventory": file_binding(inv.source), "launcher": file_binding(inv.repo_root / "scripts" / "slotctl.py"), "repo": str(inv.repo_root),
            "common_git": str(common), "state_root": str(inv.state_root),
            "domains": sorted(domains, key=lambda row: row["inventory"]["path"])}


def canonical_source_binding(inv: Inventory, root: Path, *, loaded: bool = False) -> dict[str, Any]:
    """Reuse SF's supported transparent-launcher observer without process health."""
    from .supervisor import Supervisor, _RuntimeSourcePass
    root = root.resolve(strict=True)
    common = Path(text_git(root, "rev-parse", "--git-common-dir"))
    if Path(text_git(root, "rev-parse", "--absolute-git-dir")).resolve() != (root / common).resolve():
        raise SlotError("checkpoint requires normally integrated canonical code, not a source worktree")
    implementation = implementation_binding(root, loaded=loaded)
    launcher = inv.repo_root / "scripts" / "slotctl.py"
    content = regular_bytes(launcher)
    if git(inv.repo_root, "show", "HEAD:scripts/slotctl.py") != content:
        raise SlotError("checkpoint canonical owning launcher is not exact committed source")
    routes = []
    for _ in range(2):
        sup = Supervisor(inv)
        observed = _RuntimeSourcePass(sup, "proxy", 1, sup.proxy_command(1), dict(os.environ))
        observed.launcher = launcher
        current, _ = observed.read(launcher)
        if current != content:
            raise SlotError("checkpoint canonical launcher bytes changed")
        route = observed.route(content, root / "scripts" / "lean_slots")
        if any(selector["present"] for selector in route["selectors"]):
            raise SlotError("checkpoint source-selector environment overrides refused")
        routes.append(route)
    if routes[0] != routes[1]:
        raise SlotError("checkpoint canonical source route drift")
    return {"implementation": implementation, "launcher": file_binding(launcher), "route": routes[0]}


def owner(lease: dict[str, Any]) -> dict[str, Any]:
    return {key: lease[key] for key in OWNER_KEYS if key in lease}


def native_binding(inv: Inventory, number: int) -> list[dict[str, Any]]:
    """Pin existing registry bytes and independently capable exact identities."""
    from .supervisor import Supervisor
    from .state import observe_process
    family, errors = Supervisor(inv)._role_inventories()
    if errors:
        raise SlotError("checkpoint native domain unavailable")
    result = []
    for item in family:
        path = item.process_path("backend", number)
        record = Supervisor(item)._metadata("backend", number)
        if record and record.get("record_origin") == "operator_stop_only":
            raise SlotError("checkpoint cannot alter an existing stop-only recovery reservation")
        identities = []
        if record:
            targets = {row["pid"]: row["signature"] for row in record.get("descendants", [])}
            if record.get("pid") and record.get("signature"):
                targets[record["pid"]] = record["signature"]
            for pid, signature in sorted(targets.items()):
                observation = observe_process(pid, signature)
                if observation.state not in {"present", "absent"}:
                    raise SlotError("checkpoint native identity unavailable/mismatched")
                identities.append({"pid": pid, "signature": signature, "state": observation.state})
        result.append({"inventory": str(item.source), "record": file_binding(path) if record else None, "identities": identities})
    return sorted(result, key=lambda row: row["inventory"])


def generation(lease: dict[str, Any]) -> str:
    # Includes acquire time, source/dependency pins, session credential and prepared
    # epoch. Readiness is an explicitly journaled mutable byte transition and
    # cannot recursively define this immutable acquisition identity.
    mutable = {"state", "heartbeat_at", "quarantine_reason", "quarantined_at", "checkpoint", "resume_admission"}
    return canonical_digest({key: value for key, value in lease.items() if key not in mutable})


def heartbeat_transition(record: dict[str, Any], lease: dict[str, Any], actual: str) -> dict[str, Any] | None:
    """An exact ordinary heartbeat transition, never a broad byte-drift waiver.

    Reconstruct only the existing writer's timestamp/canonical serialization from
    a journaled complete lease preimage. Every other field, including acquisition
    nonce, context, credentials, source/pins/epoch and owner, stays byte-equivalent.
    Observation is journaled under renewed CP locks before any transaction effect.
    Ordinary heartbeats do not grow a second ledger or rewrite completed evidence.
    """
    transition = record.get("lease_transition") or {}
    prior_observation = record.get("lease_observation") or {}
    candidates = [(transition.get("after"), transition.get("after_sha256")),
                  (prior_observation.get("after"), prior_observation.get("after_sha256"))]
    candidates += [(item.get("after"), item.get("after_sha256")) for item in record.get("lease_transitions", [])]
    if record.get("original_lease_bytes"):
        original = bytes.fromhex(record["original_lease_bytes"])
        candidates.append((record.get("original_lease"), sha256_bytes(original)))
    allowed = {record.get("lease_sha256"), transition.get("after_sha256")}
    for before, digest in candidates:
        if not isinstance(before, dict) or digest not in allowed or not digest:
            continue
        if {key: value for key, value in before.items() if key != "heartbeat_at"} != {key: value for key, value in lease.items() if key != "heartbeat_at"}:
            continue
        try:
            datetime.datetime.strptime(lease["heartbeat_at"], "%Y-%m-%dT%H:%M:%SZ")
        except (KeyError, ValueError, TypeError):
            continue
        encoded = (json.dumps(lease, indent=2, sort_keys=True) + "\n").encode()
        if sha256_bytes(encoded) == actual:
            return {"reason": "ordinary-heartbeat", "before_sha256": digest, "after_sha256": actual,
                    "generation_after": generation(lease), "after": copy.deepcopy(lease)}
    return None


SMOKE_HEADER = "X-Lean-Checkpoint-Smoke"
READINESS_SCHEMA = "lean-checkpoint-readiness/v1"


def smoke_payload(filename: str) -> dict[str, Any]:
    return {"jsonrpc": "2.0", "id": 3, "method": "tools/call", "params": {
        "name": "lean_diagnostic_messages", "arguments": {"file_path": filename}}}


@dataclass(frozen=True)
class CheckpointSmokeContext:
    """Internal live attempt only; capability is never a CLI/env/session value."""
    admission: dict[str, Any]
    capability: str = field(repr=False)

    def validate(self, filename: str, *, local: bool = True) -> None:
        context = self.admission
        attempt = context.get("attempt", {})
        if (context.get("schema") != READINESS_SCHEMA or context.get("state") != "pending" or
                (local and attempt.get("pid") != os.getpid()) or context.get("smoke", {}).get("file_path") != filename or
                not re.fullmatch(r"[0-9a-f]{64}", self.capability) or
                not hmac.compare_digest(sha256_bytes(self.capability.encode()), str(context.get("capability_sha256", "")))):
            raise SlotError("invalid internal checkpoint smoke context")
        observed = observe_process(attempt["pid"], attempt.get("signature"))
        if observed.state != "present" or signature_birth(observed.signature or "") != attempt.get("birth"):
            raise SlotError("checkpoint smoke attempt native identity unavailable", observations=(observed,))
        if not isinstance(attempt.get("deadline_unix"), (int, float)) or not 0 < attempt["deadline_unix"] - time.time() <= 181:
            raise SlotError("checkpoint smoke attempt expired")


def validate_smoke_rpc(request: bytes, response: bytes) -> None:
    """Reobserve actual terminal wire bytes, never a tools/list/boolean receipt."""
    from .supervisor import Supervisor
    try:
        sent = json.loads(request)
        received = Supervisor._sse_json(response)
        result = received["result"]
        structured = result.get("structuredContent")
        if structured is None:
            content = result.get("content", [])
            if len(content) == 1 and content[0].get("type") == "text":
                structured = json.loads(content[0]["text"])
        valid = (sent.get("jsonrpc") == "2.0" and sent.get("id") == 3 and
                 received.get("jsonrpc") == "2.0" and received.get("id") == sent["id"] and
                 "error" not in received and not received.get("isError") and not result.get("isError") and
                 isinstance(structured, dict) and structured.get("success") is True and
                 structured.get("timed_out") is False and structured.get("items") == [] and
                 structured.get("failed_dependencies") == [])
    except (KeyError, TypeError, ValueError, UnicodeError, AttributeError):
        valid = False
    if not valid:
        raise SlotError("checkpoint matching proof smoke lacks a clean positive terminal RPC")


def readiness_journal(inv: Inventory, number: int, lease: dict[str, Any]) -> dict[str, Any] | None:
    """Read durable resume provenance even if the lease context was erased.

    Preflight/checkpoint anchors and the unique acquired nonce select this same
    journal. No index, readiness ledger or new reservation is written.
    """
    root = inv.state_root / "checkpoints"
    admission = lease.get("resume_admission")
    preflight = lease.get("checkpoint_preflight") or {}
    if not isinstance(preflight, dict):
        raise SlotError("checkpoint preflight provenance is malformed")
    anchors = [lease.get("checkpoint"), preflight.get("id")]
    if isinstance(admission, dict):
        anchors.append(admission.get("checkpoint"))
    anchors = {value for value in anchors if isinstance(value, str) and IDENTIFIER.fullmatch(value)}
    if not root.exists():
        if anchors or admission is not None:
            raise SlotError("checkpoint readiness journal is missing")
        return None
    if root.resolve(strict=True) != root or not root.is_dir():
        raise SlotError("checkpoint readiness journal root escaped")
    paths = []
    # Path.iterdir itself materializes scandir on supported Python versions.
    # Admit each native entry before retaining it in this bounded collection.
    with os.scandir(root) as entries:
        for entry in entries:
            if len(paths) == 4096:
                raise SlotError("checkpoint readiness provenance exceeds bound")
            paths.append(root / entry.name)
    matched = []
    observed = set()
    for path in sorted(paths):
        if path.suffix != ".json" or not IDENTIFIER.fullmatch(path.stem):
            continue
        try:
            journal = journal_checked(path, path.stem)
        except JournalSizeError:
            # Size admission is a global reader-work bound, before selection by
            # nonce/anchor. An unrelated oversized file cannot be ignored.
            raise
        except (OSError, SlotError, ValueError):
            if path.stem in anchors:
                raise SlotError("checkpoint readiness journal is unreadable or invalid")
            continue
        observed.add(path.stem)
        transaction = journal.get("transaction_lease") or {}
        nonce_matches = bool(lease.get("lease_generation")) and transaction.get("lease_generation") == lease["lease_generation"]
        if journal.get("resume") and (nonce_matches or (path.stem in anchors and journal["resume"].get("generation") == generation(lease))):
            matched.append(journal)
    if anchors - observed:
        raise SlotError("checkpoint readiness anchored journal is missing")
    if len(matched) > 1:
        raise SlotError("checkpoint readiness acquisition has ambiguous journals")
    if not matched:
        if admission is not None or lease.get("checkpoint"):
            raise SlotError("checkpoint readiness has no matching durable resume")
        return None
    return matched[0]


def authorize_readiness(inv: Inventory, number: int, lease: dict[str, Any], body: bytes,
                        *, http_method: str, capability: str | None) -> None:
    """LeaseGate's fail-closed CP completion predicate; no lifecycle effects."""
    journal = readiness_journal(inv, number, lease)
    if journal is None:
        if capability is not None:
            raise SlotError("unexpected internal checkpoint capability")
        return
    context = lease.get("resume_admission")
    readiness = journal.get("readiness") or {}
    if not isinstance(context, dict) or not isinstance(readiness, dict):
        raise SlotError("checkpoint resume admission context missing or malformed")
    pending = {key: value for key, value in context.items() if key != "completion_sha256"}
    pending["state"] = "pending"
    required = {"schema", "checkpoint", "journal", "binding_digest", "generation", "acquired_generation", "owner", "source_digest", "smoke", "epoch", "dependency", "attempt", "capability_sha256", "state"}
    if (set(pending) != required or pending != readiness.get("context") or
            pending.get("schema") != READINESS_SCHEMA or pending.get("checkpoint") != journal["id"] or
            pending.get("journal") != str(inv.state_root / "checkpoints" / f"{journal['id']}.json") or
            pending.get("binding_digest") != canonical_digest(inventory_binding(inv)) or
            journal.get("binding") != inventory_binding(inv) or
            pending.get("generation") != generation(lease) or journal["resume"].get("generation") != generation(lease) or
            pending.get("acquired_generation") != lease.get("lease_generation") or
            pending.get("owner") != owner(lease) or owner(journal.get("transaction_lease", {})) != owner(lease) or
            pending.get("epoch") != lease.get("prepared_epoch") or read_json(inv.epoch_path()).get("epoch_id") != pending.get("epoch") or
            pending.get("dependency") != lease.get("public_dependency_sha") or
            pending.get("source_digest") != canonical_digest(journal.get("resulting_source"))):
        raise SlotError("checkpoint resume admission identity/generation/domain/current input mismatch")
    attempt = pending.get("attempt")
    if (not isinstance(attempt, dict) or set(attempt) != {"pid", "signature", "birth", "nonce", "deadline_unix"} or
            type(attempt.get("pid")) is not int or attempt["pid"] <= 0 or
            not signature_birth(attempt.get("signature")) or signature_birth(attempt["signature"]) != attempt.get("birth") or
            re.fullmatch(r"[0-9a-f]{48}", str(attempt.get("nonce"))) is None or
            any(re.fullmatch(r"[0-9a-f]{64}", str(pending.get(key))) is None for key in ("generation", "source_digest", "epoch", "capability_sha256")) or
            re.fullmatch(r"[0-9a-f]{48}", str(pending.get("acquired_generation"))) is None or
            set(context) != required | ({"completion_sha256"} if context.get("state") == "completed" else set())):
        raise SlotError("checkpoint readiness native/typed context is malformed")
    smoke = pending.get("smoke", {})
    try:
        filename = _relative(smoke["file_path"])
        name = (inv.lean_root(number) / filename).relative_to(inv.worktree(number)).as_posix()
        if journal["resulting_source"]["entries"][name]["sha256"] != smoke["sha256"]:
            raise ValueError("matching file binding drift")
    except (KeyError, TypeError, ValueError):
        raise SlotError("checkpoint matching smoke source binding invalid")
    if context.get("state") == "completed":
        receipt = readiness.get("receipt")
        if (capability is not None or readiness.get("status") != "completed" or not isinstance(receipt, dict) or
                receipt.get("schema") != READINESS_SCHEMA or context.get("completion_sha256") != canonical_digest(receipt) or
                receipt.get("context_sha256") != canonical_digest(pending) or
                receipt.get("admission_sha256") != canonical_digest(journal.get("admission")) or
                journal.get("phase") not in {"resumed", "lease-intent", "lease-complete"}):
            raise SlotError("checkpoint completed readiness receipt missing or mismatched")
        if journal["phase"] == "lease-intent":
            transition = journal.get("lease_transition") or {}
            after = transition.get("after") or {}
            if (after.get("state") != "ACTIVE" or after.get("resume_admission") != context or
                    sha256_bytes(regular_bytes(inv.lease_path(number))) != transition.get("after_sha256")):
                raise SlotError("checkpoint completed admission changed under another transition")
        try:
            rpc = receipt["rpc"]
            request, response = bytes.fromhex(rpc["request_hex"]), bytes.fromhex(rpc["response_hex"])
            if (sha256_bytes(request) != rpc["request_sha256"] or sha256_bytes(response) != rpc["response_sha256"] or
                    request != json.dumps(smoke_payload(filename)).encode()):
                raise ValueError("wire hash mismatch")
            validate_smoke_rpc(request, response)
        except (KeyError, TypeError, ValueError):
            raise SlotError("checkpoint completed readiness RPC receipt invalid")
        return
    if context.get("state") != "pending" or capability is None:
        raise SlotError("checkpoint resume readiness is pending; ordinary dispatch denied")
    if (http_method != "POST" or body != json.dumps(smoke_payload(filename)).encode() or
            not re.fullmatch(r"[0-9a-f]{64}", capability) or
            not hmac.compare_digest(sha256_bytes(capability.encode()), str(pending.get("capability_sha256", "")))):
        raise SlotError("invalid internal checkpoint matching smoke request")
    CheckpointSmokeContext(pending, capability).validate(filename, local=False)
    if sha256_bytes(regular_bytes(inv.lean_root(number) / filename)) != smoke["sha256"]:
        raise SlotError("checkpoint pending smoke file changed")
    from .supervisor import Supervisor
    Supervisor(inv).assert_healthy(number)


def contract_checked(value: Any) -> dict[str, Any]:
    if not isinstance(value, dict) or value.get("sourceReady") is not False:
        raise SlotError("checkpoint original contract must explicitly retain sourceReady=false")
    for key in ("objective", "obligations", "acceptance", "failures", "evidence", "clients"):
        if key not in value:
            raise SlotError(f"checkpoint original full contract lacks {key}")
    if not value["objective"] or not value["obligations"] or not value["acceptance"] or not value["clients"]:
        raise SlotError("checkpoint original full contract is incomplete")
    if not isinstance(value["evidence"], list) or any(
            not isinstance(reference, dict) or not isinstance(reference.get("path"), str) or
            not isinstance(reference.get("sha256"), str) or not re.fullmatch(r"[0-9a-f]{64}", reference["sha256"])
            for reference in value["evidence"]):
        raise SlotError("checkpoint original evidence requires explicit path/hash references")
    return copy.deepcopy(value)


def reject_overrides(*, bootstrap: bool = False) -> None:
    prefixes = ("GIT_", "LEAN_SLOT_", "LD_", "DYLD_") if bootstrap else ("GIT_", "LD_", "DYLD_")
    allowed = {"GIT_OPTIONAL_LOCKS", "GIT_PAGER", "GIT_TERMINAL_PROMPT", "LEAN_SLOT_OWNER_PID", "LEAN_SLOT_OWNER_SESSION"}
    unexpected = sorted(key for key in os.environ if key.startswith(prefixes) and key not in allowed)
    if unexpected:
        raise SlotError("checkpoint ambient overrides refused: " + ", ".join(unexpected))


def bootstrap_os_domain() -> str:
    """Observed domain identity; directories/ports alone never assert isolation."""
    native = {"platform": sys.platform, "hostname": os.uname().nodename, "namespaces": {}}
    directory = Path("/proc/self/ns")
    if directory.is_dir():
        native["namespaces"] = {name: os.readlink(directory / name) for name in ("pid", "net", "mnt", "user")}
    return canonical_digest(native)


def _authority_file(reference: Any) -> dict[str, Any]:
    if (not isinstance(reference, dict) or set(reference) != {"path", "sha256"} or
            not isinstance(reference["path"], str) or
            re.fullmatch(r"[0-9a-f]{64}", str(reference["sha256"])) is None):
        raise SlotError("checkpoint bootstrap requires an exact ROOT authority file binding")
    path = Path(reference["path"])
    if not path.is_absolute() or file_binding(path) != reference:
        raise SlotError("checkpoint bootstrap authority file bytes drift")
    data = regular_bytes(path)
    if len(data) > 65536:
        raise SlotError("checkpoint bootstrap authority document exceeds bounded control receipt size")
    value = json.loads(data)
    if not isinstance(value, dict):
        raise SlotError("checkpoint bootstrap authority document is not an object")
    return value


def bootstrap_authority(inv: Inventory, request: dict[str, Any]) -> None:
    """One explicit ROOT request, backed by accepted prior-phase receipt bytes.

    This is a source-route admission inside the existing request/journal, not a
    capacity/readiness ledger. ROOT alone issues these narrow control receipts
    after independent intake; their raw evidence/review hashes remain separate
    from scientific acceptance. The authorization's request hash excludes only
    its own file binding, avoiding a cyclic authorization/request hash.
    """
    bootstrap = request.get("bootstrap")
    if not isinstance(bootstrap, dict) or bootstrap.get("phase") not in {"isolated-native-bridge", "live-preservation"}:
        raise SlotError("checkpoint bootstrap requires an explicit admitted phase; prior-pilot booleans confer no authority")
    approval = _authority_file(bootstrap.get("authorization"))
    unsigned = copy.deepcopy(request)
    unsigned["bootstrap"].pop("authorization", None)
    candidate = canonical_digest(bootstrap.get("candidate"))
    canonical = canonical_digest(bootstrap.get("canonical"))
    domain = {"os_domain_sha256": bootstrap_os_domain(), "inventory_sha256": canonical_digest(inventory_binding(inv))}
    required = {"schema", "sourceReady", "phase", "root_owner", "domain", "request_sha256",
                "candidate_sha256", "canonical_sha256", "independent_review_sha256", "prior"}
    if (set(approval) != required or approval.get("schema") != "lean-checkpoint-bootstrap-authorization/v1" or
            approval.get("sourceReady") is not False or approval.get("phase") != bootstrap["phase"] or
            approval.get("root_owner") != bootstrap.get("root_owner") or approval.get("domain") != domain or
            approval.get("request_sha256") != canonical_digest(unsigned) or
            approval.get("candidate_sha256") != candidate or approval.get("canonical_sha256") != canonical or
            re.fullmatch(r"[0-9a-f]{64}", str(approval.get("independent_review_sha256"))) is None):
        raise SlotError("checkpoint bootstrap ROOT phase/request/domain/source authority mismatch")
    prior = approval.get("prior")
    stages = {"A"} if bootstrap["phase"] == "isolated-native-bridge" else {"A", "B"}
    if not isinstance(prior, dict) or set(prior) != stages:
        raise SlotError("checkpoint bootstrap lacks independently accepted prior native phases")
    domains = {domain["os_domain_sha256"]}
    for phase in sorted(stages):
        receipt = _authority_file(prior[phase])
        fields = {"schema", "sourceReady", "phase", "status", "accepted_by", "candidate_sha256",
                  "os_domain_sha256", "native_receipt_sha256", "independent_review_sha256"}
        if phase == "B":
            fields.add("canonical_sha256")
        if (set(receipt) != fields or receipt.get("schema") != "lean-checkpoint-native-admission/v1" or
                receipt.get("sourceReady") is not False or receipt.get("phase") != phase or
                receipt.get("status") != "accepted" or receipt.get("accepted_by") != "ROOT" or
                receipt.get("candidate_sha256") != candidate or
                phase == "B" and receipt.get("canonical_sha256") != canonical or
                any(re.fullmatch(r"[0-9a-f]{64}", str(receipt.get(key))) is None
                    for key in ("os_domain_sha256", "native_receipt_sha256", "independent_review_sha256")) or
                receipt.get("os_domain_sha256") in domains):
            raise SlotError("checkpoint bootstrap prior native phase/source/review/domain receipt invalid")
        domains.add(receipt["os_domain_sha256"])


def validate_bootstrap(source: Path | None, request: dict[str, Any], *, recover: bool = False,
                       observe_release: bool = False) -> Inventory:
    """Read-only admission before constructor/mkdir, never a general source loader."""
    reject_overrides(bootstrap=True)
    if source is None or str(source) != str(source.resolve()):
        raise SlotError("checkpoint bootstrap requires an explicit canonical inventory realpath")
    bootstrap = request.get("bootstrap")
    if not isinstance(bootstrap, dict):
        raise SlotError("checkpoint bootstrap lacks explicit ROOT source-route authority")
    contract_checked(request.get("contract"))
    inv = Inventory.load(source)
    expected = request.get("binding")
    if expected != inventory_binding(inv):
        raise SlotError("checkpoint bootstrap canonical inventory/domain binding mismatch")
    if Path.cwd().resolve() != inv.repo_root:
        raise SlotError("checkpoint bootstrap must be invoked by the canonical-primary ROOT orchestrator")
    loaded_root = Path(__file__).resolve().parents[2]
    if loaded_root == inv.repo_root:
        raise SlotError("checkpoint bootstrap requires the named ordinary candidate checkout")
    if bootstrap.get("candidate") != implementation_binding(loaded_root, loaded=True):
        raise SlotError("checkpoint bootstrap candidate/import source drift")
    canonical_root = Path(bootstrap.get("canonical", {}).get("root", ""))
    canonical_source_binding(inv, canonical_root)
    if bootstrap.get("canonical") != implementation_binding(canonical_root):
        raise SlotError("checkpoint bootstrap unchanged canonical source drift")
    # No Controller construction: _owner is read-only and uses the ordinary identity.
    from .controller import Controller
    current_owner = Controller._owner(None)
    lease = inv.lease(int(request["slot"]), required=not observe_release)
    if observe_release:
        identifier = request.get("id", "")
        if not IDENTIFIER.fullmatch(identifier):
            raise SlotError("checkpoint bootstrap release observation ID invalid")
        journal = journal_checked(inv.state_root / "checkpoints" / f"{identifier}.json", identifier)
        if lease is not None or journal.get("request") != request or not journal.get("reset_source"):
            raise SlotError("checkpoint bootstrap canonical release not observed or later lease present")
        lease = journal["original_lease"]
    if owner(lease) != current_owner or bootstrap.get("root_owner") != current_owner:
        raise SlotError("checkpoint bootstrap ROOT/original owner mismatch")
    bootstrap_authority(inv, request)
    if observe_release:
        if (journal.get("binding") != expected or
                sha256_bytes(bytes.fromhex(journal["original_lease_bytes"])) != request.get("lease_sha256")):
            raise SlotError("checkpoint bootstrap original release binding drift")
        return inv
    actual = sha256_bytes(regular_bytes(inv.lease_path(int(request["slot"]))))
    if recover:
        identifier = request.get("id", "")
        if not IDENTIFIER.fullmatch(identifier):
            raise SlotError("checkpoint bootstrap recovery ID invalid")
        journal = journal_checked(inv.state_root / "checkpoints" / f"{identifier}.json", identifier)
        transition = journal.get("lease_transition") or {}
        if (journal.get("request") != request or journal.get("binding") != expected or
                sha256_bytes(bytes.fromhex(journal["original_lease_bytes"])) != request.get("lease_sha256") or
                (actual not in {journal["lease_sha256"], transition.get("after_sha256")} and
                 heartbeat_transition(journal, lease, actual) is None)):
            raise SlotError("checkpoint bootstrap journal-bound lease recovery drift")
    elif actual != request.get("lease_sha256"):
        raise SlotError("checkpoint bootstrap original lease bytes drift")
    if not recover and native_binding(inv, int(request["slot"])) != request.get("native_bindings"):
        raise SlotError("checkpoint bootstrap original native binding drift")
    return inv


def _relative(value: str) -> str:
    path = Path(value)
    if not value or path.is_absolute() or ".." in path.parts or value != path.as_posix() or value == ".git" or ".git" in path.parts:
        raise SlotError(f"checkpoint path escapes source: {value}")
    return value


def source_manifest(root: Path, classifications: dict[str, Any]) -> dict[str, Any]:
    tracked = {os.fsdecode(name) for name in git(root, "ls-files", "-z").split(b"\0") if name}
    if git(root, "diff", "--no-ext-diff", "--no-textconv", "--binary", "HEAD"):
        raise SlotError("checkpoint requires a clean tracked source/index WIP commit")
    entries = {}
    classified_names = set()
    def classify(name):
        classification = classifications.get(name)
        if not isinstance(classification, dict) or classification.get("kind") not in {"source", "evidence", "cache"}:
            raise SlotError(f"checkpoint unclassified ignored/nontracked entry: {name}")
        kind = classification["kind"]
        if kind == "cache" and (not (name == "lean/.lake" or name.startswith("lean/.lake/")) or classification.get("owner") != "Controller._replace_lake"):
            raise SlotError(f"checkpoint cache lacks existing owner: {name}")
        if kind == "cache":
            common = Path(text_git(root, "rev-parse", "--git-common-dir"))
            common = (root / common).resolve()
            authoritative = common.parent / name
            current = root / name
            if current.is_dir():
                expected = {"path": str(authoritative), "type": "directory"}
                if authoritative.is_symlink() or not authoritative.is_dir():
                    raise SlotError(f"checkpoint cache owner directory unavailable: {name}")
            else:
                expected = file_binding(authoritative)
                if expected["sha256"] != sha256_bytes(regular_bytes(current)):
                    raise SlotError(f"checkpoint cache bytes do not belong to authoritative cache owner: {name}")
            if classification.get("owner_source") != expected:
                raise SlotError(f"checkpoint cache owner bytes are not explicitly bound: {name}")
        classified_names.add(name)
        return kind
    def walk(directory: Path) -> None:
        try:
            children = sorted(directory.iterdir())
        except OSError as exc:
            raise SlotError(f"checkpoint enumeration unavailable: {directory}: {exc}") from exc
        for path in children:
            name = path.relative_to(root).as_posix()
            if name == ".git":
                continue
            mode = path.lstat().st_mode
            if stat.S_ISDIR(mode):
                kind = "tracked" if any(value.startswith(name + "/") for value in tracked) else classify(name)
                entries[name] = {"type": "directory", "mode": stat.S_IMODE(mode), "kind": kind}
                walk(path)
                continue
            if not stat.S_ISREG(mode):
                raise SlotError(f"checkpoint unsupported source entry: {name}")
            data = regular_bytes(path)
            kind = "tracked" if name in tracked else None
            if kind is None:
                kind = classify(name)
            entries[name] = {"type": "file", "mode": stat.S_IMODE(mode), "sha256": sha256_bytes(data), "kind": kind}
    walk(root)
    if tracked - entries.keys():
        raise SlotError("checkpoint tracked source entries are missing")
    if set(classifications) != classified_names:
        raise SlotError("checkpoint classification contains absent or tracked inputs")
    index_path = Path(text_git(root, "rev-parse", "--git-path", "index"))
    index_path = index_path if index_path.is_absolute() else root / index_path
    return {"head": text_git(root, "rev-parse", "HEAD"), "tree": text_git(root, "rev-parse", "HEAD^{tree}"),
            "index_sha256": sha256_bytes(regular_bytes(index_path)), "entries": entries}


def collision_preflight(root: Path, commits: list[str], copied: list[str] = ()) -> None:
    """Refuse Git's overwrite/removal of every retained nontracked obstruction."""
    tracked = {os.fsdecode(name) for name in git(root, "ls-files", "-z").split(b"\0") if name}
    targets = set(copied)
    for commit in commits:
        targets.update(os.fsdecode(name) for name in git(root, "ls-tree", "-r", "--name-only", "-z", commit).split(b"\0") if name)
    for name in sorted(targets):
        _relative(name)
        path = root / name
        if path.exists() or path.is_symlink():
            if name not in tracked or not path.is_file() or path.is_symlink():
                raise SlotError(f"checkpoint destination collision: {name}")
        parent = path.parent
        while parent != root:
            if parent.is_symlink() or (parent.exists() and not parent.is_dir()):
                raise SlotError(f"checkpoint destination directory collision: {parent.relative_to(root)}")
            relative_parent = parent.relative_to(root).as_posix()
            if commits and parent.exists() and not any(value.startswith(relative_parent + "/") for value in tracked):
                raise SlotError(f"checkpoint destination directory collision: {relative_parent}")
            parent = parent.parent


def _copy_exclusive(path: Path, data: bytes, mode: int = 0o600) -> None:
    if path.resolve(strict=False) != path:
        raise SlotError(f"checkpoint payload path escaped through a symlink: {path}")
    path.parent.mkdir(parents=True, exist_ok=True)
    if path.resolve(strict=False) != path:
        raise SlotError(f"checkpoint payload parent changed: {path}")
    try:
        fd = os.open(path, os.O_WRONLY | os.O_CREAT | os.O_EXCL, mode)
    except FileExistsError:
        if regular_bytes(path) != data:
            raise SlotError(f"checkpoint partial copy changed: {path}")
        fd = os.open(path, os.O_RDONLY)
    try:
        if os.fstat(fd).st_size == 0 and data:
            with os.fdopen(os.dup(fd), "wb") as stream:
                stream.write(data)
                stream.flush()
        os.fchmod(fd, mode)
        os.fsync(fd)
    finally:
        os.close(fd)
    if regular_bytes(path) != data:
        raise SlotError(f"checkpoint source payload copy mismatch: {path}")
    fsync_directory(path.parent)


class CheckpointTransaction:
    """One journal and existing locks; every effect is preceded by durable intent."""
    def __init__(self, controller, request: dict[str, Any], *, bootstrap: bool = False):
        reject_overrides(bootstrap=bootstrap)
        self.controller, self.inv = controller, controller.inventory
        self.request = copy.deepcopy(request)
        self.number = int(request["slot"])
        self.identifier = request.get("id", "")
        if not isinstance(self.identifier, str) or not IDENTIFIER.fullmatch(self.identifier):
            raise SlotError("checkpoint ID is invalid")
        self.contract = contract_checked(request.get("contract"))
        self.bootstrap = bootstrap
        self.canonical_root = Path(request["bootstrap"]["canonical"]["root"]) if bootstrap else Path(__file__).resolve().parents[2]
        self.path = self.inv.state_root / "checkpoints" / f"{self.identifier}.json"
        self.binding = inventory_binding(self.inv)
        if self.binding != request.get("binding"):
            raise SlotError("checkpoint canonical binding drift")
        self.common = Path(self.binding["common_git"])
        self.store = self.common / "lean-checkpoint-data" / self.identifier
        if self.path.resolve(strict=False) != self.path or self.store.resolve(strict=False) != self.store:
            raise SlotError("checkpoint transaction storage escapes canonical owning roots")
        self.ref = f"refs/lean-checkpoints/{self.identifier}/source"
        self.journal = None
        self.context = None
        self._journal_sha256 = None

    def _lock_context(self, operation: str) -> CheckpointLockContext:
        """Effect-free original-owner/expected-transition admission before locks."""
        record = journal_checked(self.path, self.identifier) if self.path.exists() else None
        if record is not None:
            expected = sha256_bytes((json.dumps(record, indent=2, sort_keys=True) + "\n").encode())
            if sha256_bytes(regular_bytes(self.path)) != expected:
                raise SlotError("checkpoint journal bytes changed before lock admission")
            self._journal_sha256 = expected
        current = self.inv.lease(self.number, required=False)
        if record is not None and (record.get("binding") != self.binding or record.get("contract") != self.contract):
            raise SlotError("checkpoint lock original contract/domain drift")
        if record is not None and record.get("resume") and operation not in {"resume", "recover-resume"}:
            raise SlotError("checkpoint preservation was superseded by a new resume transaction; stale route refused")
        current_owner = self.controller._owner()
        original = (record.get("transaction_lease", record["original_lease"]) if record else current)
        if original is None or owner(original) != current_owner or (current and owner(current) != current_owner):
            raise SlotError("checkpoint lock original ROOT owner mismatch")
        generations = []
        hashes = []
        if current:
            actual = sha256_bytes(regular_bytes(self.inv.lease_path(self.number)))
            if operation in {"preserve", "resume"}:
                if actual != self.request.get("lease_sha256"):
                    raise SlotError("checkpoint original lease bytes drift before lock effects")
            elif record:
                transition = record.get("lease_transition") or {}
                if (actual not in {record["lease_sha256"], transition.get("after_sha256")} or
                        generation(current) not in {record["generation"], transition.get("generation_after")}):
                    if heartbeat_transition(record, current, actual) is None:
                        raise SlotError("checkpoint later lease generation/byte transition before lock effects")
            generations.append(generation(current))
            hashes.append(actual)
        elif operation != "observe-release" or record is None:
            raise SlotError("checkpoint released lease cannot be recreated")
        self._lock_base = original["base_sha"]
        if record:
            generations.extend([generation(record["original_lease"]), record["generation"]])
            hashes.extend([sha256_bytes(bytes.fromhex(record["original_lease_bytes"])), record["lease_sha256"]])
            transition = record.get("lease_transition") or {}
            if transition:
                generations.append(transition["generation_after"])
                hashes.append(transition["after_sha256"])
            for prior in record.get("lease_transitions", []):
                generations.append(prior["generation_after"])
                hashes.extend([prior["before_sha256"], prior["after_sha256"]])
            if record.get("resume"):
                hashes.append(record["resume"]["lease_sha256"])
            if record.get("lease_observation"):
                hashes.extend([record["lease_observation"]["before_sha256"], record["lease_observation"]["after_sha256"]])
        context = CheckpointLockContext(self.inv.state_root,
                    {**self.binding, "selected_slot": self.number}, self.identifier, operation,
                    tuple(dict.fromkeys(generations)), tuple(dict.fromkeys(hashes)),
                    canonical_digest(record["request"] if record else self.request), self._mutators_quiescent)
        context.boundary = self.boundary
        self.context = context
        return context

    def _mutators_quiescent(self) -> None:
        """A released guard/parent PID alone is never mutation completion."""
        self._journal_bytes()
        record = journal_checked(self.path, self.identifier) if self.path.exists() else None
        mutation = (record or {}).get("mutation")
        if not mutation or mutation.get("completed"):
            return
        if mutation.get("closure") != "checkpoint-builtin-git/no-hooks-helpers/v1":
            raise SlotError("checkpoint mutation family closure is unknown; scope reserved")
        identity = mutation.get("native")
        if not identity:
            # A wrapper cannot pass its start barrier before native binding is
            # durable. Missing binding therefore admits no first write, but its
            # still-live child is not presumed complete.
            raise SlotError("checkpoint mutation launch binding incomplete; scope reserved")
        observation = observe_shutdown_process(identity["pid"])
        census = process_snapshot()
        if observation.state not in {"absent", "present"} or census.state != "present":
            raise SlotError("checkpoint native mutation completion unavailable", observations=(observation,))
        if observation.state == "present" and (observation.identity or {}).get("birth") == identity["birth"]:
            raise SlotError("checkpoint admitted mutator still present; facade retained", observations=(observation,))
        if any(row.ppid == identity["pid"] for row in census.rows):
            raise SlotError("checkpoint retained mutation descendants remain; facade retained")

    def _mutation_policy(self, root: Path, target: str) -> dict[str, Any]:
        # Git's bounded built-in update-ref/reset/ort operations need no hook,
        # filter, signing agent, submodule or background maintenance helper.
        # Configured helper families are refused, never silently disabled.
        configuration = git(root, "config", "--null", "--list")
        attribute_paths = [os.fsdecode(name) for commit in ("HEAD", target)
                           for name in git(root, "ls-tree", "-r", "--name-only", "-z", commit).split(b"\0") if name]
        attributes = any(Path(name).name == ".gitattributes" for name in attribute_paths)
        forbidden = re.compile(r"^(?:core\.(?:hookspath|fsmonitor|worktree)$|checkout\.workers$|submodule\.|commit\.gpgsign$|merge\.verifysignatures$)", re.I)
        for entry in configuration.split(b"\0"):
            key = entry.split(b"\n", 1)[0].decode(errors="strict")
            if entry and (forbidden.search(key) or attributes and (key.startswith("filter.") or key.startswith("merge.") and key.endswith(".driver"))):
                raise SlotError("checkpoint refuses unbounded configured Git hook/helper family")
        if attributes or (self.common / "info" / "attributes").exists():
            raise SlotError("checkpoint unproved attributes/merge-driver/filter family")
        names = b"\0".join(os.fsencode(name) for name in sorted(set(attribute_paths))) + b"\0"
        # Include effective system/global and untracked worktree attributes.
        # check-attr only reads attributes; it does not run the configured filter.
        for source in ((), ("--source=HEAD",), (f"--source={target}",)):
            if git(root, "check-attr", *source, "--all", "--stdin", "-z", input_data=names):
                raise SlotError("checkpoint effective attributes/filter family is unproved")
        hooks = self.common / "hooks"
        if hooks.exists():
            if hooks.is_symlink() or not hooks.is_dir():
                raise SlotError("checkpoint Git hooks directory is unsafe")
            for path in hooks.iterdir():
                if path.is_symlink() or not path.is_file() or not path.name.endswith(".sample"):
                    raise SlotError("checkpoint refuses unproved Git hooks/helpers before mutation")
        if any(line.startswith(b"160000 ") for line in git(root, "ls-files", "--stage", "-z").split(b"\0")):
            raise SlotError("checkpoint mutation does not admit Git submodules")
        executable = _git_executable()
        return {"executable": file_binding(executable), "configuration_sha256": sha256_bytes(configuration),
                "version": git(root, "--version").decode().strip()}

    def _mutate_git(self, root: Path, *args: str, check: bool = True) -> subprocess.CompletedProcess:
        """Only CP's three built-in Git writes, with a prewrite native barrier."""
        if not args or args[0] not in {"update-ref", "reset", "merge"} or self.context is None:
            raise SlotError("checkpoint Git mutation lacks explicit admitted context")
        guards = self.context.descriptors()
        self._mutators_quiescent()
        expected_source = self.journal.get("resume", {}).get("destination", self.journal["source"])
        if self._source() != expected_source:
            raise SlotError("checkpoint Git prewrite source differs from its admitted preimage")
        target = args[-2] if args[0] == "update-ref" else args[-1]
        policy = self._mutation_policy(root, target)
        argv = [policy["executable"]["path"], "-c", "gc.auto=0", "-c", "maintenance.auto=false", *args]
        prior = [*self.journal.get("mutation_history", [])]
        if self.journal.get("mutation"):
            prior.append(copy.deepcopy(self.journal["mutation"]))
        self.write("mutation-intent", mutation_history=prior, mutation={"argv": argv, "cwd": str(root), "policy": policy,
            "source_preimage_sha256": canonical_digest(expected_source),
            "closure": "checkpoint-builtin-git/no-hooks-helpers/v1", "completed": False, "native": None})
        barrier_read, barrier_write = os.pipe()
        # No first write exists before reading exactly one start byte. EOF (the
        # parent's death at any pre-binding point) exits without exec/mutation.
        wrapper = "import os,sys; fd=int(sys.argv[1]); start=os.read(fd,1); os.close(fd); (os.execv(sys.argv[2],sys.argv[2:]) if start==b'G' else sys.exit(74)) # lean-checkpoint-start-barrier/v1"
        process = None
        started = False
        try:
            process = subprocess.Popen([sys.executable, "-I", "-S", "-B", "-c", wrapper, str(barrier_read), *argv], cwd=root,
                env={**os.environ, "GIT_OPTIONAL_LOCKS": "0", "GIT_NO_LAZY_FETCH": "1"},
                pass_fds=(*guards, barrier_read), stdin=subprocess.DEVNULL, stdout=subprocess.PIPE, stderr=subprocess.PIPE)
            os.close(barrier_read)
            barrier_read = -1
            self.boundary("mutation-launched-blocked")
            observation = observe_process(process.pid)
            if observation.state != "present" or not signature_birth(observation.signature or ""):
                raise SlotError("checkpoint prewrite child native identity unavailable", observations=(observation,))
            mutation = copy.deepcopy(self.journal["mutation"])
            mutation["native"] = {"pid": process.pid, "birth": signature_birth(observation.signature), "barrier_signature": observation.signature}
            mutation["guards"] = [{"device": os.fstat(fd).st_dev, "inode": os.fstat(fd).st_ino} for fd in guards]
            self.write("mutation-bound", mutation=mutation)
            self.context.check()
            if self._mutation_policy(root, target) != policy:
                raise SlotError("checkpoint Git configuration/executable changed at barrier")
            self._bindings()
            self._lease()
            if args[0] != "update-ref":
                self._protection()
                self._drain()
                from .supervisor import Supervisor
                self._observe_absence(Supervisor(self.inv))
            # Reobserve after the last durable/native launch boundary. No Git
            # write can erase an edit made while the bounded child was staged.
            self._journal_bytes()
            if self._source() != expected_source:
                raise SlotError("checkpoint source changed at the actual prewrite barrier")
            if os.write(barrier_write, b"G") != 1:
                raise SlotError("checkpoint incomplete start-barrier write")
            started = True
            os.close(barrier_write)
            barrier_write = -1
            self.boundary("mutation-started")
            stdout, stderr = process.communicate(timeout=30)
            self._mutators_quiescent()
            mutation.update(completed=True, returncode=process.returncode, stdout=stdout.hex(), stderr=stderr.hex())
            self.write("mutation-complete", mutation=mutation)
            result = subprocess.CompletedProcess(argv, process.returncode, stdout, stderr)
            if check and result.returncode:
                raise SlotError(f"checkpoint Git mutation failed: {stderr.decode(errors='replace')}")
            return result
        finally:
            for fd in (barrier_read, barrier_write):
                if fd != -1:
                    os.close(fd)
            if process is not None and not started:
                try:
                    stdout, stderr = process.communicate(timeout=5)
                except subprocess.TimeoutExpired:
                    pass  # Unknown completion keeps inherited guards/facades.
                else:
                    if process.returncode == 74:
                        cancelled = copy.deepcopy(self.journal["mutation"])
                        cancelled.update(completed=True, start_not_authorized=True,
                                         wait_pid=process.pid, returncode=74,
                                         stdout=stdout.hex(), stderr=stderr.hex())
                        self.write("mutation-cancelled-before-start", mutation=cancelled)
            # Never kill a possibly writing family, unlock its shared guards or
            # retire its facade on timeout/exception. Recovery proves completion.

    def boundary(self, phase: str) -> None:
        """Fault-injection seam after an actual durable production boundary."""

    def write(self, phase: str, **fields) -> None:
        if self.context is not None and self.context.held:
            self.context.check()
        self._journal_bytes()
        self.journal.update(fields)
        self.journal["phase"] = phase
        self.journal.setdefault("events", []).append({"phase": phase, "at": now_iso()})
        durable_json(self.path, self.journal)
        self._journal_sha256 = sha256_bytes((json.dumps(self.journal, indent=2, sort_keys=True) + "\n").encode())
        fsync_directory(self.inv.state_root)
        self.boundary(phase)

    def _journal_bytes(self) -> None:
        """Live-attempt drift cannot manufacture mutation completion or intent."""
        if self.path.exists():
            if (self._journal_sha256 is None or
                    sha256_bytes(regular_bytes(self.path)) != self._journal_sha256):
                raise SlotError("checkpoint journal byte drift; transaction remains reserved")
        elif self._journal_sha256 is not None:
            raise SlotError("checkpoint journal disappeared; transaction remains reserved")

    def _canonical(self) -> None:
        reject_overrides()
        canonical_source_binding(self.inv, Path(__file__).resolve().parents[2], loaded=True)

    def _bindings(self) -> None:
        if inventory_binding(self.inv) != self.binding:
            raise SlotError("checkpoint inventory/domain drift")
        if self.bootstrap:
            bootstrap_authority(self.inv, self.request)
        current = self.journal.get("resume", {}) if self.journal else {}
        source = current.get("implementation", self.journal.get("implementation")) if self.journal else None
        if source and implementation_binding(Path(source["root"]), loaded=True) != source:
            raise SlotError("checkpoint implementation/import drift")
        canonical = current.get("implementation", self.journal.get("canonical_implementation")) if self.journal else None
        if canonical and implementation_binding(Path(canonical["root"])) != canonical:
            raise SlotError("checkpoint canonical implementation drift")
        if self.journal and self.journal.get("canonical_source") and not current:
            if canonical_source_binding(self.inv, Path(canonical["root"])) != self.journal["canonical_source"]:
                raise SlotError("checkpoint canonical launcher/source binding drift")

    def _lease(self) -> dict[str, Any]:
        lease = self.controller._lease_for_command(self.number)
        record = self.journal
        actual = sha256_bytes(regular_bytes(self.inv.lease_path(self.number)))
        expected = record["lease_sha256"]
        transition = record.get("lease_transition")
        if transition and actual == transition["after_sha256"] and generation(lease) == transition["generation_after"]:
            self.write(record["phase"], lease_sha256=actual, generation=transition["generation_after"], lease_transition=None)
        elif actual != expected and (observed := heartbeat_transition(record, lease, actual)) is not None:
            self.write(record["phase"], lease_sha256=actual, generation=observed["generation_after"],
                       lease_transition=None, lease_observation=observed)
        elif generation(lease) != record["generation"]:
            raise SlotError("checkpoint later lease generation; original ownership preserved")
        elif actual != expected:
            raise SlotError("checkpoint unexpected lease byte/heartbeat transition")
        return lease

    def _transition_lease(self, lease: dict[str, Any], **changes) -> None:
        self._lease()
        updated = copy.deepcopy(lease)
        updated.update(changes)
        encoded = (json.dumps(updated, indent=2, sort_keys=True) + "\n").encode()
        transition = {"before_sha256": self.journal["lease_sha256"], "after_sha256": sha256_bytes(encoded), "after": updated,
                      "generation_after": generation(updated)}
        self.write("lease-intent", lease_transition=transition,
                   lease_transitions=[*self.journal.get("lease_transitions", []), copy.deepcopy(transition)])
        if changes.get("state") == "ACTIVE":
            self._verify_resume_activation(updated)
        if sha256_bytes(regular_bytes(self.inv.lease_path(self.number))) != transition["before_sha256"]:
            raise SlotError("checkpoint lease changed after durable transition intent; no overwrite")
        durable_json(self.inv.lease_path(self.number), updated)
        self.boundary("lease-write")
        self.write("lease-complete", lease_sha256=transition["after_sha256"], generation=transition["generation_after"], lease_transition=None)

    def _verify_resume_activation(self, lease: dict[str, Any]) -> None:
        if not self.journal.get("resume") or not self.journal.get("admission"):
            raise SlotError("checkpoint ACTIVE transition requires canonical resume admission")
        self._bindings()
        self._protection()
        self._drain()
        self.controller._assert_paired_dependency(self.number, lease.get("public_dependency_sha"))
        epoch = self.controller._matching_epoch(lease["base_sha"], public_dependency_sha=lease.get("public_dependency_sha"))
        if epoch["epoch_id"] != lease.get("prepared_epoch"):
            raise SlotError("checkpoint resume prepared epoch changed before ACTIVE")
        if self._source() != self.journal["resulting_source"]:
            raise SlotError("checkpoint resulting source changed before ACTIVE")
        context = lease.get("resume_admission")
        readiness = self.journal.get("readiness") or {}
        if not isinstance(context, dict):
            raise SlotError("checkpoint ACTIVE requires atomic pending/completed admission")
        pending = {key: value for key, value in context.items() if key != "completion_sha256"}
        pending["state"] = "pending"
        if (pending != readiness.get("context") or pending.get("generation") != generation(lease) or
                pending.get("owner") != owner(lease)):
            raise SlotError("checkpoint ACTIVE admission generation/context drift")
        attempt = pending.get("attempt", {})
        observed = observe_process(attempt.get("pid", 0), attempt.get("signature"))
        if observed.state != "present" or attempt.get("pid") != os.getpid():
            raise SlotError("checkpoint ACTIVE admission requires this live native attempt", observations=(observed,))
        if context.get("state") == "completed":
            receipt = readiness.get("receipt")
            if (readiness.get("status") != "completed" or not isinstance(receipt, dict) or
                    context.get("completion_sha256") != canonical_digest(receipt) or
                    receipt.get("context_sha256") != canonical_digest(pending)):
                raise SlotError("checkpoint completed lease requires durable clean journal first")
            rpc = receipt.get("rpc") or {}
            validate_smoke_rpc(bytes.fromhex(rpc.get("request_hex", "")), bytes.fromhex(rpc.get("response_hex", "")))
        elif context.get("state") != "pending":
            raise SlotError("checkpoint ACTIVE admission status invalid")

    def _activate_resume(self, supervisor, lease, resulting, smoke_file) -> dict[str, Any]:
        self._bindings()
        self._lease()
        self._drain()
        self.controller._assert_paired_dependency(self.number, lease.get("public_dependency_sha"))
        self.controller._matching_epoch(lease["base_sha"], public_dependency_sha=lease.get("public_dependency_sha"))
        self.write("resume-restore-intent")
        supervisor._start_backend_unlocked(self.number)
        supervisor.assert_healthy(self.number)
        admission = supervisor.probe(self.number, client=lease["client"])
        if admission.get("lean_build_exposed") is not False or admission.get("active_dispatch") not in {False, "skipped-nonmatching-lease"}:
            raise SlotError("checkpoint resume pre-dispatch session/tool-policy admission failed")
        if self._source() != resulting:
            raise SlotError("checkpoint resulting source drift before activation")
        lease = self._lease()
        observed = observe_process(os.getpid())
        if observed.state != "present" or not signature_birth(observed.signature or ""):
            raise SlotError("checkpoint resume attempt native identity unavailable", observations=(observed,))
        capability = secrets.token_hex(32)
        filename = _relative(smoke_file)
        context = {"schema": READINESS_SCHEMA, "checkpoint": self.identifier, "journal": str(self.path),
                   "binding_digest": canonical_digest(self.binding), "generation": generation(lease),
                   "acquired_generation": lease.get("lease_generation"), "owner": owner(lease),
                   "source_digest": canonical_digest(resulting),
                   "smoke": {"file_path": filename, "sha256": sha256_bytes(regular_bytes(self.inv.lean_root(self.number) / filename))},
                   "epoch": lease["prepared_epoch"], "dependency": lease.get("public_dependency_sha"),
                   "attempt": {"pid": os.getpid(), "signature": observed.signature, "birth": signature_birth(observed.signature),
                               "nonce": secrets.token_hex(24), "deadline_unix": time.time() + 180},
                   "capability_sha256": sha256_bytes(capability.encode()), "state": "pending"}
        prior = [*self.journal.get("readiness_history", [])]
        if self.journal.get("readiness"):
            prior.append(copy.deepcopy(self.journal["readiness"]))
        self.write("resume-reactivate-intent", admission=admission, readiness_history=prior,
                   readiness={"context": context, "status": "pending"})
        # No ACTIVE-without-context interval exists, even under os._exit.
        self._transition_lease(lease, state="ACTIVE", resume_admission=context)
        self.write("resume-active")
        smoke = supervisor.probe(self.number, client=lease["client"], proof_smoke_file=filename,
                                 checkpoint_smoke=CheckpointSmokeContext(context, capability))
        if smoke.get("active_dispatch") is not True or not isinstance(smoke.get("proof_rpc"), dict):
            raise SlotError("checkpoint matching fresh proof smoke failed")
        self.boundary("resume-smoke-complete")
        receipt = {"schema": READINESS_SCHEMA, "context_sha256": canonical_digest(context),
                   "admission_sha256": canonical_digest(admission), "rpc": smoke["proof_rpc"]}
        validate_smoke_rpc(bytes.fromhex(receipt["rpc"]["request_hex"]), bytes.fromhex(receipt["rpc"]["response_hex"]))
        readiness = {"context": context, "status": "completed", "receipt": receipt}
        self.write("resumed", smoke=smoke, readiness=readiness, sourceReady=False)
        self.boundary("resume-journal-completed")
        completed = {**context, "state": "completed", "completion_sha256": canonical_digest(receipt)}
        self._transition_lease(self._lease(), state="ACTIVE", resume_admission=completed)
        self.boundary("resume-admission-completed")
        self.write("resumed")
        return copy.deepcopy(self.journal)

    def _legacy_generation(self) -> None:
        lease = self._lease()
        if lease.get("lease_generation"):
            return
        self._bindings()
        self._drain()
        if self._source() != self.journal["source"] or native_binding(self.inv, self.number) != self.request.get("native_bindings"):
            raise SlotError("checkpoint legacy generation source/native binding drift")
        self.write("legacy-generation-intent")
        self._transition_lease(lease, lease_generation=secrets.token_hex(24))
        self.write("legacy-generation-complete")

    def _deny(self) -> None:
        lease = self._lease()
        if lease.get("state") != "QUARANTINED" or lease.get("checkpoint") != self.identifier:
            self._transition_lease(lease, state="QUARANTINED", checkpoint=self.identifier,
                                   quarantine_reason=f"checkpoint {self.identifier}: dispatch denied", quarantined_at=now_iso())
        self.write("quarantined")

    def _fail(self, exc: BaseException) -> None:
        # Never recreate a released lease, overwrite a changed heartbeat/owner or
        # restart a backend while recording failure.
        if self.journal is not None:
            try:
                self._mutators_quiescent()
                self._deny()
                self.write("failed", failure=f"{type(exc).__name__}: {exc}")
            except BaseException:
                pass

    def _source(self) -> dict[str, Any]:
        if self.context is not None and self.context.held:
            self.context.check()
            self._journal_bytes()
            self._mutation_policy(self.inv.worktree(self.number), self._lock_base)
        return source_manifest(self.inv.worktree(self.number), getattr(self, "restored_classifications", self.request.get("classifications", {})))

    def _evidence(self) -> dict[str, dict[str, Any]]:
        roots = [Path(value).resolve(strict=True) for value in self.request.get("evidence_roots", [])]
        if not roots:
            raise SlotError("checkpoint evidence roots must be explicit")
        references = {}
        def walk(value):
            if isinstance(value, dict):
                if "path" in value and "sha256" in value:
                    path = Path(value["path"])
                    real = path.resolve(strict=True)
                    if path != real or not any(real.is_relative_to(root) for root in roots):
                        raise SlotError("checkpoint evidence escaped declared owning roots")
                    binding = file_binding(path)
                    if binding["sha256"] != value["sha256"]:
                        raise SlotError("checkpoint evidence original changed")
                    if str(real) in references:
                        return
                    references[str(real)] = binding
                    # Close machine-readable evidence references by their actual
                    # JSON content, independently of the caller's file roster.
                    try:
                        nested_document = json.loads(regular_bytes(path))
                    except (ValueError, UnicodeError):
                        nested_document = None
                    if nested_document is not None:
                        walk(nested_document)
                for nested in value.values():
                    walk(nested)
            elif isinstance(value, list):
                for nested in value:
                    walk(nested)
        walk(self.contract)
        walk(self.request.get("drain_receipts", []))
        if self.bootstrap:
            walk(self.request.get("bootstrap", {}).get("authorization"))
        for name, item in self._source()["entries"].items():
            if item["type"] == "file" and item.get("kind") == "evidence" and str(self.inv.worktree(self.number) / name) not in references:
                raise SlotError("checkpoint classified evidence omitted from full evidence closure")
            if item.get("kind") == "cache" and str(self.inv.worktree(self.number) / name) in references:
                raise SlotError("checkpoint proof evidence cannot be classified as cache")
        return references

    def _drain(self) -> None:
        receipts = self.request.get("drain_receipts", [])
        if len(receipts) != len(self.contract["clients"]):
            raise SlotError("checkpoint missing independent completed-client drain receipts")
        completed = []
        for reference in receipts:
            path = Path(reference["path"])
            if file_binding(path) != reference:
                raise SlotError("checkpoint drain receipt changed")
            receipt = read_json(path)
            if (receipt.get("schema") != "lean-client-drain/v1" or receipt.get("producer") != "client" or
                    receipt.get("lease_generation") != self.journal.get("drain_generation", self.journal["generation"]) or
                    receipt.get("endpoint") != self.inv.slot(self.number)["endpoint_name"] or
                    receipt.get("owner") != owner(self.journal.get("transaction_lease", self.journal["original_lease"])) or
                    receipt.get("outstanding") != [] or not receipt.get("drained_at") or
                    not receipt.get("completed_requests")):
                raise SlotError("checkpoint independent actual request drain is incomplete")
            for response in receipt["completed_requests"]:
                if not all(response.get(key) for key in ("id", "request_sha256", "response_sha256", "completed_at")):
                    raise SlotError("checkpoint completed request lacks actual completion evidence")
                self._completed_request(response)
            completed.append(receipt.get("client"))
        if sorted(completed, key=canonical_digest) != sorted(self.contract["clients"], key=canonical_digest):
            raise SlotError("checkpoint drain does not cover original clients")

    def _completed_request(self, completion: dict[str, Any]) -> None:
        documents = {}
        for kind in ("request", "response"):
            reference = completion.get(kind)
            if (not isinstance(reference, dict) or not isinstance(reference.get("path"), str) or
                    reference.get("sha256") != completion.get(f"{kind}_sha256")):
                raise SlotError("checkpoint completed request requires actual request/response bytes")
            path = Path(reference["path"])
            if file_binding(path) != reference:
                raise SlotError("checkpoint completed request/response artifact changed")
            try:
                documents[kind] = json.loads(regular_bytes(path))
            except (ValueError, UnicodeError) as exc:
                raise SlotError("checkpoint completed RPC artifact is not JSON") from exc
        request, response = documents["request"], documents["response"]
        if (not isinstance(request, dict) or not isinstance(response, dict) or
                request.get("jsonrpc") != "2.0" or response.get("jsonrpc") != "2.0" or
                not request.get("method") or request.get("id") != completion["id"] or
                response.get("id") != request["id"] or (("result" in response) == ("error" in response))):
            raise SlotError("checkpoint completed RPC bytes do not prove a matching terminal response")

    def _protect_ref(self) -> None:
        head = self.journal["source"]["head"]
        self._objects(head)
        if (self.common / self.ref).resolve(strict=False) != self.common / self.ref:
            raise SlotError("checkpoint preservation ref traverses a symlink")
        existing = git(self.inv.repo_root, "rev-parse", "--verify", self.ref, check=False).decode().strip()
        if existing and existing != head:
            raise SlotError("checkpoint preservation ref collision/drift")
        if existing and self.journal["phase"] == "created":
            raise SlotError("checkpoint preservation ref already exists")
        self.write("ref-intent")
        if not existing:
            self._mutate_git(self.inv.repo_root, "update-ref", "--create-reflog", self.ref, head, "0" * 40)
        self.boundary("ref-created")
        # Verify every reachable object, then flush actual object/pack/ref bytes.
        paths = list((self.common / "objects").rglob("*"))
        if any(path.is_symlink() for path in paths):
            raise SlotError("checkpoint object storage symlinks are unsupported")
        paths += [self.common / self.ref, self.common / "logs" / self.ref]
        for path in paths:
            if path.is_file() and not path.is_symlink():
                fd = os.open(path, os.O_RDONLY)
                try:
                    os.fsync(fd)
                finally:
                    os.close(fd)
        flush_directories(self.common, [self.common / "objects", *(path.parent for path in paths if path.exists())])
        self.write("ref-complete")

    def _objects(self, head: str) -> None:
        objects = self.common / "objects"
        if objects.resolve(strict=True) != objects or any(path.is_symlink() or not (path.is_file() or path.is_dir()) for path in objects.rglob("*")):
            raise SlotError("checkpoint Git object storage is not locally regular")
        if ((self.common / "objects/info/alternates").exists() or
                text_git(self.inv.repo_root, "rev-parse", "--is-shallow-repository") != "false" or
                any((objects / "pack").glob("*.promisor")) or
                git(self.inv.repo_root, "config", "--get", "extensions.partialClone", check=False) or
                git(self.inv.repo_root, "config", "--get-regexp", r"remote\..*\.promisor", check=False)):
            raise SlotError("checkpoint requires complete locally owned Git objects")
        git(self.inv.repo_root, "fsck", "--strict", "--no-reflogs", "--no-dangling", head)

    def _copy(self) -> None:
        self.write("copy-intent")
        if self.store.resolve(strict=False) != self.store:
            raise SlotError("checkpoint staging storage changed outside owning root")
        self.store.mkdir(parents=True, exist_ok=True)
        flush_directories(self.common, [self.store])
        payloads = {}
        root = self.inv.worktree(self.number)
        for name, entry in self.journal["source"]["entries"].items():
            if entry["type"] == "directory" and entry["kind"] != "cache":
                directory = self.store / "source" / name
                directory.mkdir(parents=True, exist_ok=True)
                fsync_directory(directory.parent)
            if entry["type"] == "file" and entry["kind"] != "cache":
                payloads[f"source/{name}"] = root / name
        index = Path(text_git(root, "rev-parse", "--git-path", "index"))
        payloads["index"] = index if index.is_absolute() else root / index
        for path in self.journal["evidence"]:
            payloads[f"evidence/{sha256_bytes(path.encode())}"] = Path(path)
        copies = {}
        for destination, original in payloads.items():
            data = regular_bytes(original)
            _copy_exclusive(self.store / destination, data)
            copies[destination] = {"original": str(original), "sha256": sha256_bytes(data)}
            self.boundary("copied-file")
        _copy_exclusive(self.store / "contract.json", (json.dumps(self.contract, sort_keys=True) + "\n").encode())
        for directory in sorted((path for path in self.store.rglob("*") if path.is_dir()), key=lambda path: len(path.parts), reverse=True):
            fsync_directory(directory)
        fsync_directory(self.store)
        self.boundary("copies-flushed")
        if self._source() != self.journal["source"] or self._evidence() != self.journal["evidence"]:
            raise SlotError("checkpoint source/evidence changed during preservation")
        receipt = {"schema": SCHEMA, "sourceReady": False, "source": self.journal["source"],
                   "evidence": self.journal["evidence"], "copies": copies, "contract": self.contract}
        if (self.store / "complete.json").exists():
            if read_json(self.store / "complete.json") != receipt:
                raise SlotError("checkpoint immutable completion receipt drift")
        else:
            exclusive_durable_json(self.store / "complete.json", receipt)
        self.write("protected", completion_sha256=sha256_bytes(regular_bytes(self.store / "complete.json")))
        self._protection()

    def _protection(self) -> dict[str, Any]:
        if text_git(self.inv.repo_root, "rev-parse", "--verify", self.ref) != self.journal["source"]["head"]:
            raise SlotError("checkpoint ref changed")
        self._objects(self.journal["source"]["head"])
        receipt_path = self.store / "complete.json"
        if sha256_bytes(regular_bytes(receipt_path)) != self.journal["completion_sha256"]:
            raise SlotError("checkpoint durable receipt drift")
        receipt = read_json(receipt_path)
        if receipt["sourceReady"] is not False or receipt["contract"] != self.contract:
            raise SlotError("checkpoint original acceptance contract changed")
        for name, item in receipt["source"]["entries"].items():
            if item["type"] == "directory" and item["kind"] != "cache" and not (self.store / "source" / name).is_dir():
                raise SlotError("checkpoint preserved source directory missing")
            if item["type"] == "file" and item["kind"] != "cache":
                copied = receipt["copies"].get(f"source/{name}")
                if not copied or copied["sha256"] != item["sha256"]:
                    raise SlotError("checkpoint preserved source has no actual durable bytes")
        for name, item in receipt["copies"].items():
            if sha256_bytes(regular_bytes(self.store / name)) != item["sha256"]:
                raise SlotError("checkpoint durable payload drift")
        expected = {"contract.json", "complete.json", *receipt["copies"]}
        for name in list(expected):
            expected.update(parent.as_posix() for parent in Path(name).parents if parent.as_posix() != ".")
        expected.update("source/" + name for name, item in receipt["source"]["entries"].items() if item["type"] == "directory" and item["kind"] != "cache")
        actual = {path.relative_to(self.store).as_posix() for path in self.store.rglob("*")}
        if actual != expected or self.store.resolve(strict=True) != self.store:
            raise SlotError("checkpoint immutable storage contains unknown or missing entries")
        for name, binding in receipt["evidence"].items():
            original_root = Path(self.journal["original_lease"]["worktree"])
            original_path = Path(name)
            relative = original_path.relative_to(original_root).as_posix() if original_path.is_relative_to(original_root) else None
            source_entry = receipt["source"]["entries"].get(relative, {})
            if self.journal.get("reset_intent") and source_entry.get("sha256") == binding["sha256"]:
                continue  # The intentional reset retains these originals in the protected source payload/ref.
            if file_binding(Path(name)) != binding:
                raise SlotError("checkpoint original evidence drift")
        return receipt

    def _stop_observe(self, supervisor) -> None:
        from .supervisor import Supervisor
        family, errors = supervisor._role_inventories()
        if errors:
            raise SlotError("checkpoint both-role universe unavailable")
        self.write("stop-intent")
        for inv in family:
            other = inv.lease(self.number, required=False)
            if other and other.get("repo_role") != self.inv.repo_role:
                raise SlotError("checkpoint counterpart has independent lease ownership")
            sup = supervisor if inv.source == self.inv.source else Supervisor(inv)
            path = inv.process_path("backend", self.number)
            if path.exists():
                record = sup._metadata("backend", self.number)
                expected = next((row["record"] for row in self.request["native_bindings"] if row["inventory"] == str(inv.source)), None)
                allowed = {expected["sha256"]} if expected else set()
                for prior in self.journal.get("native_stop_receipts", []):
                    if prior.get("repo_role") == inv.repo_role:
                        allowed.add(sha256_bytes((json.dumps(prior, indent=2, sort_keys=True) + "\n").encode()))
                if sha256_bytes(regular_bytes(path)) not in allowed:
                    raise SlotError("checkpoint stop refuses later native registry owner/bytes")
                self.write("stop-intent", native_records=[*self.journal.get("native_records", []), copy.deepcopy(record)])
            def receipt(record):
                self.write("stop-receipt", native_stop_receipts=[*self.journal.get("native_stop_receipts", []), copy.deepcopy(record)])
            sup._checkpoint_stop_receipt = receipt
            sup._stop_backend_unlocked(self.number)
            if path.parent.exists():
                fsync_directory(path.parent)
            self.boundary("owned-stop")
        self._observe_absence(supervisor)
        self.write("stopped")

    def _native_before_quarantine(self, supervisor) -> None:
        """Original native bytes, or this transaction's exact RR stop effects.

        A recovery cannot expect an already stopped family to remain live. Its
        authority is still the original registry preimage and the independently
        guarded RR writer's durable receipts, never the holder's death or a
        missing registry alone. Live/terminal classification of a retained exact
        receipt remains the existing low-level RR stop's responsibility.
        """
        from .supervisor import Supervisor
        family, errors = supervisor._role_inventories()
        expected = self.request.get("native_bindings", [])
        if errors or {str(inv.source) for inv in family} != {row["inventory"] for row in expected}:
            raise SlotError("checkpoint original native domain changed before quarantine")
        encoded_hash = lambda record: sha256_bytes((json.dumps(record, indent=2, sort_keys=True) + "\n").encode())
        for inv in family:
            before = next(row for row in expected if row["inventory"] == str(inv.source))
            sup = supervisor if inv.source == self.inv.source else Supervisor(inv)
            current = sup._metadata("backend", self.number)
            path = inv.process_path("backend", self.number)
            if current and current.get("record_origin") == "operator_stop_only":
                raise SlotError("checkpoint original native stop-only reservation changed before quarantine")
            original_ref = before.get("record")
            current_hash = sha256_bytes(regular_bytes(path)) if current else None
            if original_ref is None:
                if current is not None:
                    raise SlotError("checkpoint later native registry owner before quarantine")
                continue
            if original_ref.get("path") != str(path):
                raise SlotError("checkpoint original native registry path drift")
            receipts = [record for record in self.journal.get("native_stop_receipts", [])
                        if record.get("repo_role") == inv.repo_role]
            if not receipts:
                if current_hash != original_ref["sha256"]:
                    raise SlotError("checkpoint original native binding changed before quarantine")
                for identity in before["identities"]:
                    observation = observe_process(identity["pid"], identity["signature"])
                    if observation.state != identity["state"]:
                        raise SlotError("checkpoint original native identity changed before quarantine", observations=(observation,))
                continue
            lease = self._lease()
            if lease.get("state") != "QUARANTINED" or lease.get("checkpoint") != self.identifier:
                raise SlotError("checkpoint native stop transitions require original durable quarantine")
            originals = [record for record in self.journal.get("native_records", [])
                         if encoded_hash(record) == original_ref["sha256"]]
            if not originals:
                raise SlotError("checkpoint original native registry preimage is unavailable")
            original = originals[0]
            sup._validate_record(original, "backend", self.number)
            immutable = lambda record: {key: value for key, value in record.items() if key not in {"descendants", "shutdown"}}
            retained = {item["pid"]: item["signature"] for item in before["identities"]}
            allowed = {original_ref["sha256"]}
            for receipt in receipts:
                sup._validate_record(receipt, "backend", self.number)
                if immutable(receipt) != immutable(original) or not isinstance(receipt.get("shutdown"), dict):
                    raise SlotError("checkpoint native stop receipt changed original owner/launch bytes")
                for child in receipt.get("descendants", []):
                    if child["pid"] in retained and retained[child["pid"]] != child["signature"]:
                        raise SlotError("checkpoint native stop receipt replaced a retained identity")
                    retained[child["pid"]] = child["signature"]
                allowed.add(encoded_hash(receipt))
            if current is not None:
                if current_hash not in allowed:
                    raise SlotError("checkpoint later native registry bytes cannot replay an old stop")
                # No signal is authorized here. The subsequent unchanged RR path
                # reclassifies every live/terminal original under its native guards.
            else:
                for pid in retained:
                    observation = observe_shutdown_process(pid)
                    if observation.state != "absent":
                        raise SlotError("checkpoint removed native registry still has retained family; reserved", observations=(observation,))

    def _observe_absence(self, supervisor) -> None:
        from .supervisor import Supervisor
        family, errors = supervisor._role_inventories()
        if errors:
            raise SlotError("checkpoint both-role absence domain unavailable")
        for _ in range(2):
            observations = []
            for inv in family:
                Supervisor(inv)._assert_quiescent("backend", self.number, observations=observations)
            census = supervisor.capacity_census()
            if not census["complete"] or census["conflicts"] or census["owners"][self.number]:
                raise SlotError("checkpoint complete conflict-free global absence required")
            self.write("quiescence-observed", observations=[item.as_dict() for item in observations], census=census)

    def preserve(self, *, recover: bool = False) -> dict[str, Any]:
        from .supervisor import Supervisor
        supervisor = Supervisor(self.inv)
        context = self._lock_context("recover" if recover else "preserve")
        with self.controller._slot_lock(self.number, checkpoint=context), supervisor.lifecycle(checkpoint=context):
            # A nominal Git read can launch fsmonitor/filters. Inspect its
            # configuration only after renewed guards/native mutation barriers,
            # before the first source/index read or transaction effect.
            self._mutation_policy(self.inv.worktree(self.number), self._lock_base)
            try:
                if recover:
                    self.journal = journal_checked(self.path, self.identifier)
                    if self.journal["request"] != self.request or self.journal["binding"] != self.binding:
                        raise SlotError("checkpoint recovery request drift")
                    self._lease()
                else:
                    lease = self.controller._lease_for_command(self.number, states={"ACTIVE", "QUARANTINED"})
                    worktree, _ = self.controller._assert_worktree_identity(self.number)
                    if sha256_bytes(regular_bytes(self.inv.lease_path(self.number))) != self.request.get("lease_sha256"):
                        raise SlotError("checkpoint original lease bytes drift")
                    if native_binding(self.inv, self.number) != self.request.get("native_bindings"):
                        raise SlotError("checkpoint original native binding drift")
                    source = self._source()
                    if canonical_digest(source) != self.request.get("source_digest"):
                        raise SlotError("checkpoint exact source manifest drift")
                    if not self.request.get("source_safe_wip"):
                        raise SlotError("checkpoint requires ROOT source-safe WIP authorization")
                    if self.request.get("original_base_sha") != lease["base_sha"]:
                        raise SlotError("checkpoint original base binding mismatch")
                    if self.store.exists() or git(self.inv.repo_root, "rev-parse", "--verify", self.ref, check=False):
                        raise SlotError("checkpoint ID/store/ref already exists")
                    self.controller._assert_paired_dependency(self.number, lease.get("public_dependency_sha"), require_primary_match=False)
                    if text_git(worktree, "merge-base", lease["base_sha"], source["head"]) != lease["base_sha"]:
                        raise SlotError("checkpoint WIP does not contain original lease base")
                    self.journal = {"schema": SCHEMA, "id": self.identifier, "sourceReady": False,
                                    "request": self.request, "binding": self.binding, "contract": self.contract,
                                    "generation": generation(lease), "original_lease": lease,
                                    "drain_generation": generation(lease),
                                    "original_lease_bytes": regular_bytes(self.inv.lease_path(self.number)).hex(),
                                    "lease_sha256": self.request["lease_sha256"], "source": source,
                                    "implementation": implementation_binding(Path(__file__).resolve().parents[2], loaded=True),
                                    "canonical_implementation": implementation_binding(self.canonical_root),
                                    "canonical_source": canonical_source_binding(self.inv, self.canonical_root), "phase": "created", "events": []}
                    self.journal["evidence"] = self._evidence()
                    exclusive_durable_json(self.path, self.journal)
                    self._journal_sha256 = sha256_bytes((json.dumps(self.journal, indent=2, sort_keys=True) + "\n").encode())
                    fsync_directory(self.inv.state_root)
                    self.boundary("created")
                self._bindings()
                self._lease()
                # A reset crash is observed, never blindly replayed.
                if self.journal.get("reset_intent"):
                    return self._recover_reset(supervisor)
                if self._source() != self.journal["source"]:
                    raise SlotError("checkpoint source changed before reset")
                self._protect_ref()
                self._copy()
                self._drain()
                self._native_before_quarantine(supervisor)
                self._legacy_generation()
                self._deny()
                self._bindings()
                self._lease()
                if self._source() != self.journal["source"]:
                    raise SlotError("checkpoint source changed after drain/quarantine")
                self._stop_observe(supervisor)
                self._reset()
                return copy.deepcopy(self.journal)
            except BaseException as exc:
                self._fail(exc)
                raise

    def _reset(self) -> None:
        self._bindings()
        lease = self._lease()
        self._protection()
        self._drain()
        if self._source() != self.journal["source"]:
            raise SlotError("checkpoint reset source drift/dirty state")
        base = self.journal["original_lease"]["base_sha"]
        self.controller._assert_paired_dependency(self.number, lease.get("public_dependency_sha"), require_primary_match=False)
        collision_preflight(self.inv.worktree(self.number), [base])
        self.write("reset-intent", reset_intent=True)
        self._bindings()
        self._lease()
        self._protection()
        self._drain()
        if self._source() != self.journal["source"]:
            raise SlotError("checkpoint source changed after durable reset intent")
        from .supervisor import Supervisor
        self._observe_absence(Supervisor(self.inv))
        collision_preflight(self.inv.worktree(self.number), [base])
        self._bindings()
        self._protection()
        self._drain()
        self._lease()
        if self._source() != self.journal["source"]:
            raise SlotError("checkpoint final clean source drift before reset")
        self._mutate_git(self.inv.worktree(self.number), "reset", "--hard", base)
        self.boundary("reset-effect")
        self._flush_source()
        self.write("reset-complete", reset_source=self._source())
        self.write("eligible-canonical-release")

    def _flush_source(self) -> None:
        root = self.inv.worktree(self.number)
        for name in git(root, "ls-files", "-z").split(b"\0"):
            if name:
                path = root / os.fsdecode(name)
                fd = os.open(path, os.O_RDONLY)
                try:
                    os.fsync(fd)
                finally:
                    os.close(fd)
        index = Path(text_git(root, "rev-parse", "--git-path", "index"))
        index = index if index.is_absolute() else root / index
        for path in (index, index.parent / "HEAD", self.common / "refs" / "heads" / self.inv.slot(self.number)["branch"]):
            fd = os.open(path, os.O_RDONLY)
            try:
                os.fsync(fd)
            finally:
                os.close(fd)
            fsync_directory(path.parent)
        for directory in sorted((path for path in root.rglob("*") if path.is_dir() and not path.is_symlink()), key=lambda path: len(path.parts), reverse=True):
            fsync_directory(directory)
        fsync_directory(root)
        self.boundary("source-flushed")

    def _recover_reset(self, supervisor) -> dict[str, Any]:
        self._deny()
        self._protection()
        self._bindings()
        current = self._source()
        if current == self.journal["source"]:
            self._drain()
            self._stop_observe(supervisor)
            self._reset()
        elif current["head"] == self.journal["original_lease"]["base_sha"]:
            original = self.journal["source"]["entries"]
            retained = {name: item for name, item in original.items() if item.get("kind") in {"source", "evidence", "cache"}}
            if any(current["entries"].get(name) != item for name, item in retained.items()):
                raise SlotError("checkpoint interrupted reset retained bytes changed")
            # A clean exact base is measured by source_manifest; no second reset.
            self._stop_observe(supervisor)
            self._flush_source()
            self.write("reset-complete", reset_source=current)
            self.write("eligible-canonical-release")
        else:
            raise SlotError("checkpoint interrupted reset is neither exact WIP nor clean contained base")
        return copy.deepcopy(self.journal)

    def observe_release(self) -> dict[str, Any]:
        from .supervisor import Supervisor
        supervisor = Supervisor(self.inv)
        context = self._lock_context("observe-release")
        with self.controller._slot_lock(self.number, checkpoint=context), supervisor.lifecycle(checkpoint=context):
            self._mutation_policy(self.inv.worktree(self.number), self._lock_base)
            self.journal = journal_checked(self.path, self.identifier)
            if not self.journal.get("reset_source"):
                raise SlotError("checkpoint reset has no durable completion")
            self._bindings()
            self._protection()
            if self.inv.lease(self.number, required=False) is not None:
                self._lease()
                raise SlotError("checkpoint canonical release not observed")
            if self._source() != self.journal["reset_source"]:
                raise SlotError("checkpoint release observation source drift or later reuse")
            census = supervisor.capacity_census()
            if not census["complete"] or census["conflicts"]:
                raise SlotError("checkpoint post-release capacity unavailable")
            self.write("canonical-release-observed", release_census=census)
            return copy.deepcopy(self.journal)

    def preflight(self, *, target_number: int) -> None:
        """Called under ordinary prepare's slot/lifecycle locks before its reset."""
        if self.number != target_number:
            raise SlotError("checkpoint request slot must match prepare command slot")
        self._canonical()
        journal = journal_checked(self.path, self.identifier)
        if journal["contract"] != self.contract or journal["binding"] != self.binding:
            raise SlotError("checkpoint resume original contract/domain drift")
        old = self.journal
        self.journal = journal
        receipt = self._protection()
        self.journal = old
        copied = [name for name, item in receipt["source"]["entries"].items() if item.get("kind") in {"source", "evidence"}]
        lease = self.controller._lease_for_command(self.number, states={"ACQUIRED", "PREPARING"})
        self._mutation_policy(self.inv.worktree(self.number), lease["base_sha"])
        destination = source_manifest(self.inv.worktree(self.number), self.request.get("classifications", {}))
        if any(name == "lean/.lake" or name.startswith("lean/.lake/") for name, item in destination["entries"].items() if item["kind"] in {"source", "evidence"}):
            raise SlotError("checkpoint prepare would replace destination-owned source/evidence in cache")
        collision_preflight(self.inv.worktree(self.number), [lease["base_sha"], journal["source"]["head"]], copied)

    def resume(self, *, recover: bool = False) -> dict[str, Any]:
        self._canonical()
        from .supervisor import Supervisor
        supervisor = Supervisor(self.inv)
        context = self._lock_context("recover-resume" if recover else "resume")
        with self.controller._slot_lock(self.number, checkpoint=context), supervisor.lifecycle(checkpoint=context):
            self._mutation_policy(self.inv.worktree(self.number), self._lock_base)
            try:
                self.journal = journal_checked(self.path, self.identifier)
                if self.journal["contract"] != self.contract or self.journal["binding"] != self.binding:
                    raise SlotError("checkpoint resume full original contract/domain mismatch")
                receipt = self._protection()
                lease = self.controller._lease_for_command(self.number, states={"ACTIVE", "QUARANTINED"})
                worktree, _ = self.controller._assert_worktree_identity(self.number)
                resume = self.journal.get("resume")
                if recover:
                    if not resume or resume["request"] != self.request:
                        raise SlotError("checkpoint resume recovery request mismatch")
                    if self.journal["generation"] != resume["generation"]:
                        raise SlotError("checkpoint resume recovery generation drift")
                    self._lease()
                    if lease.get("resume_admission", {}).get("state") == "completed":
                        authorize_readiness(self.inv, self.number, lease,
                            json.dumps(smoke_payload(_relative(self.request.get("proof_smoke_file", "")))).encode(),
                            http_method="POST", capability=None)
                        return copy.deepcopy(self.journal)
                    self._deny()
                    resulting = self.journal.get("resulting_source")
                    if not resulting or self._source() != resulting:
                        raise SlotError("checkpoint interrupted resume retained for explicit source/conflict review; no automatic restart")
                    return self._activate_resume(supervisor, self._lease(), resulting, _relative(self.request.get("proof_smoke_file", "")))
                if resume:
                    raise SlotError("checkpoint resume transaction already exists; use recovery")
                if self.journal["generation"] == generation(lease):
                    raise SlotError("checkpoint resume requires fresh ordinary acquire/prepare")
                current = self._source()
                if current["head"] != lease["base_sha"] or not lease.get("prepared_epoch"):
                    raise SlotError("checkpoint resume destination is not freshly prepared base")
                if lease.get("checkpoint_preflight") != {"id": self.identifier, "base_sha": lease["base_sha"], "contract_digest": canonical_digest(self.contract)}:
                    raise SlotError("checkpoint resume requires collision-safe canonical preparation")
                epoch = self.controller._matching_epoch(lease["base_sha"], public_dependency_sha=lease.get("public_dependency_sha"))
                if epoch["epoch_id"] != lease["prepared_epoch"]:
                    raise SlotError("checkpoint resume current prepared epoch drift")
                self.controller._assert_paired_dependency(self.number, lease.get("public_dependency_sha"))
                if sha256_bytes(regular_bytes(self.inv.lease_path(self.number))) != self.request.get("lease_sha256") or canonical_digest(current) != self.request.get("source_digest"):
                    raise SlotError("checkpoint resume destination lease/source drift")
                copied = [name for name, item in receipt["source"]["entries"].items() if item.get("kind") in {"source", "evidence"}]
                collision_preflight(worktree, [receipt["source"]["head"]], copied)
                resume = {"generation": generation(lease), "lease_sha256": self.request["lease_sha256"],
                          "destination": current, "request": self.request, "original_generation": self.journal["generation"],
                          "implementation": implementation_binding(Path(__file__).resolve().parents[2], loaded=True)}
                self.write("resume-bound", resume=resume, generation=resume["generation"],
                           lease_sha256=resume["lease_sha256"], transaction_lease=lease, drain_generation=resume["generation"])
                self._drain()
                self._deny()
                self._stop_observe(supervisor)
                self._lease()
                if self._source() != current:
                    raise SlotError("checkpoint resume destination changed after drain")
                self._protection()
                self._bindings()
                self._lease()
                collision_preflight(worktree, [receipt["source"]["head"]], copied)
                self.write("resume-source-intent")
                self._bindings()
                self._lease()
                self._protection()
                self._drain()
                if self._source() != current:
                    raise SlotError("checkpoint resume source changed after durable intent")
                self._observe_absence(supervisor)
                collision_preflight(worktree, [receipt["source"]["head"]], copied)
                self._bindings()
                self._protection()
                self._drain()
                self._lease()
                if self._source() != current:
                    raise SlotError("checkpoint final destination drift before resume")
                if lease["base_sha"] == self.journal["request"]["original_base_sha"]:
                    self._mutate_git(worktree, "reset", "--hard", receipt["source"]["head"])
                else:
                    result = self._mutate_git(worktree, "merge", "--strategy=ort", "--no-edit", "--no-ff", receipt["source"]["head"], check=False)
                    if result.returncode:
                        self.write("resume-conflict", conflict=result.stderr.decode(errors="replace"))
                        raise SlotError("checkpoint ancestry merge conflict; destination retained quarantined")
                self.boundary("resume-source-effect")
                for name in copied:
                    entry = receipt["source"]["entries"][name]
                    # Reobserve collisions immediately before each create-only copy.
                    collision_preflight(worktree, [], [name])
                    self.write("resume-copy-intent", copying=name)
                    self._lease()
                    collision_preflight(worktree, [], [name])
                    if entry["type"] == "directory":
                        (worktree / name).mkdir(mode=entry["mode"])
                        fsync_directory((worktree / name).parent)
                    else:
                        _copy_exclusive(worktree / name, regular_bytes(self.store / "source" / name), entry["mode"])
                self.restored_classifications = {**self.request.get("classifications", {}),
                    **{name: self.journal["request"]["classifications"][name] for name in copied}}
                same_base = lease["base_sha"] == self.journal["request"]["original_base_sha"]
                self._restore_source_metadata(receipt, same_base=same_base, copied=copied)
                self._flush_source()
                resulting = self._source()
                if same_base:
                    source_entries = lambda manifest: {name: item for name, item in manifest["entries"].items() if item["kind"] != "cache"}
                    if source_entries(resulting) != source_entries(receipt["source"]):
                        raise SlotError("checkpoint same-base restoration is not exact preserved source")
                self.write("resume-metadata-complete")
                smoke_file = _relative(self.request.get("proof_smoke_file", ""))
                smoke_source = (self.inv.lean_root(self.number) / smoke_file).relative_to(worktree).as_posix()
                if smoke_source not in receipt["source"]["entries"] or resulting["entries"].get(smoke_source, {}).get("type") != "file":
                    raise SlotError("checkpoint proof smoke must match preserved and resulting source")
                self.write("resume-source-complete", resulting_source=resulting, changed_scope={"old": receipt["source"], "current": current, "result": resulting}, historical_evidence=True)
                return self._activate_resume(supervisor, lease, resulting, smoke_file)
            except BaseException as exc:
                self._fail(exc)
                raise

    def _restore_source_metadata(self, receipt, *, same_base: bool, copied: list[str]) -> None:
        expected = {name: item for name, item in receipt["source"]["entries"].items()
                    if item["kind"] != "cache" and (same_base or name in copied)}
        before = self._source()
        for name, item in expected.items():
            current = before["entries"].get(name, {})
            if current.get("type") != item["type"] or (item["type"] == "file" and current.get("sha256") != item["sha256"]):
                raise SlotError("checkpoint source content changed before exact metadata restoration")
        self.write("resume-metadata-intent", metadata_source=before)
        self._lease()
        self._bindings()
        if self._source() != before:
            raise SlotError("checkpoint source changed after metadata intent")
        for name, item in sorted(expected.items(), key=lambda pair: len(Path(pair[0]).parts), reverse=True):
            path = self.inv.worktree(self.number) / name
            fd = os.open(path, os.O_RDONLY | os.O_NOFOLLOW)
            try:
                os.fchmod(fd, item["mode"])
                os.fsync(fd)
            finally:
                os.close(fd)
        self.boundary("resume-metadata-effect")
