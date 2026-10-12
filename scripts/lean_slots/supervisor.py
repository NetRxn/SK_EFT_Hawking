"""Deterministic local process lifecycle for fixed-root Lean MCP endpoints."""

from __future__ import annotations

import json
import errno
import secrets
import stat
import shlex
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
    observe_process,
    _observe_created_handle,
    process_snapshot,
    Observation,
    observe_path,
    observe_directory,
    MAX_JSON_BYTES,
    tool_cache_path,
    tool_list_key,
    read_json,
    sha256_bytes,
)


def _port_observation(host: str, port: int, timeout: float = 0.15) -> Observation:
    try:
        with socket.create_connection((host, port), timeout=timeout):
            return Observation("present", target=f"{host}:{port}", operation="connect")
    except OSError as exc:
        if exc.errno == errno.ECONNREFUSED:
            return Observation("absent", detail="connection refused", errno=exc.errno,
                               target=f"{host}:{port}", operation="connect", error_class=type(exc).__name__)
        return Observation("unavailable", detail=str(exc), errno=exc.errno,
                           target=f"{host}:{port}", operation="connect", error_class=type(exc).__name__)


def _port_open(host: str, port: int, timeout: float = 0.15) -> bool:
    """Observed-only compatibility reader; never a destructive absence gate."""
    return _port_observation(host, port, timeout).state == "present"


class Supervisor:
    def __init__(self, inventory: Inventory | None = None):
        self.inventory = inventory or Inventory.load()

    def _validate_record(self, value: dict[str, Any], kind: str, number: int) -> dict[str, Any]:
        """One existing-record shape for status, capacity, stop and quiescence."""
        path = self.inventory.process_path(kind, number)
        def invalid(detail: str) -> None:
            evidence = Observation("unavailable", detail=detail, target=str(path), operation="process-record-validate")
            error = SlotError(f"invalid process record for {kind} wt{number}: {detail}", observations=(evidence,))
            error.recorded_pid = value.get("pid")
            raise error
        if type(value.get("schema_version")) is not int or value["schema_version"] != SCHEMA_VERSION:
            invalid("unsupported process schema")
        if value.get("kind") != kind or type(value.get("slot")) is not int or value["slot"] != number or value.get("repo_role") != self.inventory.repo_role:
            invalid("process identity fields do not match the configured domain")
        version, phase = value.get("process_schema_version", 1), value.get("phase", "running")
        if type(version) is not int or version not in (1, 2) or not isinstance(phase, str) or phase not in ("running", "launch_pending", "uncertain_residual"):
            invalid("unsupported process version/phase")
        pid, signature = value.get("pid"), value.get("signature")
        if "pid" in value and (type(pid) is not int or pid <= 0):
            invalid("root PID must be a positive integer")
        if "signature" in value and (not isinstance(signature, str) or not signature.strip() or "\n" in signature or "\r" in signature):
            invalid("root signature must be a nonempty single-line string")
        if signature is not None and pid is None:
            invalid("root signature lacks its PID")
        if phase == "running" and (pid is None or signature is None):
            invalid("running record lacks a complete root identity")
        if "descendants" in value:
            descendants = value["descendants"]
            if not isinstance(descendants, list) or len(descendants) > 4096:
                invalid("descendants must be a bounded list of complete identities")
            identities = {}
            for child in descendants:
                if not isinstance(child, dict) or type(child.get("pid")) is not int or child["pid"] <= 0:
                    invalid("descendant PID must be a positive integer")
                child_signature = child.get("signature")
                if not isinstance(child_signature, str) or not child_signature.strip() or "\n" in child_signature or "\r" in child_signature:
                    invalid("descendant signature must be a nonempty single-line string")
                if child["pid"] in identities:
                    invalid("duplicate descendant PID")
                identities[child["pid"]] = child_signature
                if child["pid"] == pid and signature is not None and child_signature != signature:
                    invalid("root and retained descendant signatures conflict")
        return value  # Preserve legacy fields/bytes; never manufacture or silently drop pins.

    def _read_metadata(self, kind: str, number: int) -> tuple[dict[str, Any] | None, tuple[Observation, ...]]:
        path = self.inventory.process_path(kind, number)
        observed = observe_path(path)
        if observed.state == "absent":
            return None, (observed,)
        if observed.state != "present":
            raise SlotError(f"process record observation unavailable: {observed.detail}", observations=(observed,))
        if observed.identity["mode"] != stat.S_IFREG:
            evidence = Observation("unavailable", detail="process record is not a regular file", target=str(path), operation="process-record-read")
            raise SlotError(evidence.detail, observations=(observed, evidence))
        value = self._validate_record(read_json(path), kind, number)
        evidence = Observation("present", target=str(path), operation="process-record-validate",
                               identity={"pid": value.get("pid"), "signature": value.get("signature"),
                                         "phase": value.get("phase", "running")})
        return value, (observed, evidence)

    def _metadata(self, kind: str, number: int) -> dict[str, Any] | None:
        return self._read_metadata(kind, number)[0]

    def _running(self, kind: str, number: int) -> bool:
        return self.process_state(kind, number) == "running"

    def process_state(self, kind: str, number: int) -> str:
        return self._resource_status(kind, number)["state"]

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
        if kind in {"proxy", "backend"}:
            directory = self.inventory.repo_root / "scripts" / "lean_slots"
            entries, enumeration = observe_directory(directory)
            if enumeration.state == "unavailable":
                raise SlotError("runtime source enumeration unavailable", observations=(enumeration,))
            candidates = [self.inventory.repo_root / "scripts" / "slotctl.py"]
            candidates.extend(path for path in entries if path.suffix == ".py")
            for path in candidates:
                observed = observe_path(path)
                if observed.state == "absent":
                    continue
                if observed.state != "present" or observed.identity["mode"] != stat.S_IFREG:
                    raise SlotError("runtime source observation unavailable", observations=(observed,))
                try:
                    with path.open("rb") as handle:
                        content = handle.read(MAX_JSON_BYTES + 1)
                    if len(content) > MAX_JSON_BYTES:
                        raise ValueError("runtime source exceeds bounded read")
                except (OSError, ValueError) as exc:
                    evidence = Observation("unavailable", detail=str(exc), errno=getattr(exc, "errno", None),
                                           target=str(path), operation="runtime-source-read", error_class=type(exc).__name__)
                    raise SlotError("runtime source read unavailable", observations=(observed, evidence)) from exc
                sources[str(path.relative_to(self.inventory.repo_root))] = sha256_bytes(content)
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

    def _role_inventories(self, *, retain_aliases: bool = False,
                          observations: list[Observation] | None = None) -> tuple[list[Inventory], list[str]]:
        """Resolve the existing bounded family; native enumeration must be capable."""
        resolved = {str(self.inventory.source): self.inventory}
        errors = []
        witnesses = observations if observations is not None else []
        try:
            candidates = {self.inventory.source}
            repositories, seen = observe_directory(self.inventory.workspace_root)
            witnesses.append(seen)
            if seen.state != "present":
                raise SlotError("workspace role enumeration unavailable", observations=(seen,))
            for repository in repositories:
                entry = observe_path(repository); witnesses.append(entry)
                if entry.state == "unavailable":
                    raise SlotError("repository role observation unavailable", observations=(entry,))
                if entry.state != "present" or entry.identity["mode"] != stat.S_IFDIR:
                    continue
                configs, seen = observe_directory(repository / "config"); witnesses.append(seen)
                if seen.state == "unavailable":
                    raise SlotError("inventory family enumeration unavailable", observations=(seen,))
                candidates.update(path for path in configs if path.name.startswith("lean-slots.") and path.suffix == ".json")
            paired = self.inventory.paired_inventory()
            if paired:
                candidates.add(paired.source)
            if len(candidates) > 128:
                raise SlotError("inventory family exceeds complete resolution bound")
            for source in sorted(candidates):
                entry = observe_path(source); witnesses.append(entry)
                if entry.state != "present" or entry.identity["mode"] != stat.S_IFREG:
                    raise SlotError("configured inventory observation unavailable", observations=(entry,))
                inv = Inventory.load(source)
                if inv.state_root != self.inventory.state_root:
                    errors.append("inventory runtime-root mismatch")
                else:
                    resolved[str(inv.source)] = inv
        except (OSError, SlotError, ValueError, TypeError) as exc:
            witnesses.extend(getattr(exc, "observations", ()))
            errors.append(f"role universe unavailable: {str(exc)[:2048]}")
        # A checkout name or copied config cannot establish repository identity.
        identities = {root: self._checkout_identity(root, witnesses)
                      for root in {inv.repo_root for inv in resolved.values()}}
        canonical = [inv for inv in resolved.values()
                     if identities[inv.repo_root] is not None
                     and identities[inv.repo_root]["git_dir"] == identities[inv.repo_root]["common_dir"]]
        retained = {}
        for source, inv in resolved.items():
            identity = identities[inv.repo_root]
            if identity is None:
                errors.append("inventory checkout identity unavailable")
                retained[source] = inv
                continue
            if identity["git_dir"] == identity["common_dir"]:
                retained[source] = inv
                continue
            counterparts = [other for other in canonical
                            if identities[other.repo_root]["common_dir"] == identity["common_dir"]]
            if not counterparts:
                errors.append("secondary checkout lacks a capable canonical primary")
                retained[source] = inv
                continue
            if not any(other.repo_role == inv.repo_role and
                       self._inventory_domain(inv, other.repo_root) == self._inventory_domain(other)
                       for other in counterparts):
                errors.append("secondary checkout has a conflicting inventory domain")
                retained[source] = inv
        resolved = retained
        # An override may alter dependency inputs without adding a physical role.
        # Compare resolved domains and complete server mappings, not JSON location.
        roles: dict[str, tuple[str, Inventory]] = {}
        for inv in resolved.values():
            domain = self._inventory_domain(inv)
            prior = roles.get(inv.repo_role)
            if prior and prior[0] != domain:
                errors.append("multiple conflicting inventory domains for one role")
            elif prior is None or inv.source == self.inventory.source:
                roles[inv.repo_role] = (domain, inv)
        # Quiescence also needs every resolved input filename: old wrappers
        # can survive a supported override even though physical capacity is one role.
        return (list(resolved.values()) if retain_aliases else
                [entry[1] for entry in roles.values()]), errors

    @staticmethod
    def _inventory_domain(inv: Inventory, root=None) -> str:
        root = inv.repo_root if root is None else root
        return canonical_digest({
            "repo_root": str(root), "state_root": str(inv.state_root),
            "server": inv.raw.get("server", {}),
            "slots": [{"worktree": str((root / inv.slot(n)["worktree"]).resolve()),
                       "lean_root": str((root / inv.slot(n)["worktree"] / "lean").resolve()),
                       "branch": inv.slot(n).get("branch"),
                       "endpoint_name": inv.slot(n).get("endpoint_name"),
                       "proxy_port": int(inv.slot(n)["proxy_port"]),
                       "backend_port": int(inv.slot(n)["backend_port"])} for n in (1, 2, 3)]})

    @staticmethod
    def _checkout_identity(root, witnesses: list[Observation]):
        """Three bounded Git fields; only proven linked copies may be excluded."""
        def unavailable(detail, *, result=None, exc=None):
            witnesses.append(Observation("unavailable", detail=detail, target=str(root),
                operation="git-checkout-identity", returncode=result.returncode if result else None,
                error_class=type(exc).__name__ if exc else "ValueError", errno=getattr(exc, "errno", None)))
            return None
        try:
            result = subprocess.run(["git", "rev-parse", "--show-toplevel", "--git-common-dir", "--git-dir"],
                                    cwd=root, check=False, capture_output=True, text=True, timeout=2)
        except (OSError, subprocess.TimeoutExpired, UnicodeError, ValueError) as exc:
            return unavailable(str(exc), exc=exc)
        lines = result.stdout.splitlines()
        if result.returncode != 0 or result.stderr.strip() or len(result.stdout) > 16384 or len(lines) != 3 or any(not line.strip() or "\x00" in line for line in lines):
            return unavailable("incomplete/ambiguous Git checkout observation: " + result.stderr, result=result)
        try:
            paths = [(root / line).resolve() for line in lines]
        except (OSError, ValueError) as exc:
            return unavailable(str(exc), result=result, exc=exc)
        top, common, git_dir = paths
        if top != root or (git_dir != common and not git_dir.is_relative_to(common / "worktrees")):
            return unavailable("Git checkout top-level/common-directory identity mismatch", result=result)
        for path in (top, common, git_dir):
            seen = observe_path(path); witnesses.append(seen)
            if seen.state != "present" or seen.identity["mode"] != stat.S_IFDIR:
                return unavailable("Git checkout directory observation unavailable", result=result)
        identity = {"top_level": top, "common_dir": common, "git_dir": git_dir}
        witnesses.append(Observation("present", target=str(root), operation="git-checkout-identity",
                                    returncode=result.returncode, identity={k: str(v) for k, v in identity.items()}))
        return identity

    @staticmethod
    def _project_roots(census, project_rows, project: str, witnesses: list[Observation]):
        """Validate complete relevant chains, including generic intermediates."""
        rows = {row.pid: row for row in census.rows}
        matching = {row.pid for row in project_rows}
        def invalid(detail):
            evidence = Observation("unavailable", detail=detail, target=project,
                                   operation="process-ancestry", error_class="ValueError")
            witnesses.append(evidence)
            raise SlotError(detail, observations=(evidence,))
        if census.state != "present" or len(rows) != len(census.rows):
            invalid("complete unique process ancestry unavailable")
        roots = []
        for row in project_rows:
            visited = {row.pid}; parent = row.ppid; has_matching_ancestor = False
            while parent != 0:
                if parent in visited:
                    invalid("cyclic/self-parented relevant process ancestry")
                visited.add(parent)
                if parent not in rows:
                    invalid("missing relevant process ancestor")
                has_matching_ancestor = has_matching_ancestor or parent in matching
                parent = rows[parent].ppid
            if not has_matching_ancestor:
                roots.append(row)
        witnesses.append(Observation("present", target=project, operation="process-ancestry",
                                     identity={"project_pids": sorted(matching), "roots": [row.pid for row in roots]}))
        return roots

    def capacity_census(self) -> dict[str, Any]:
        observations = []
        inventories, errors = self._role_inventories(observations=observations)
        unbounded = bool(errors)
        census = process_snapshot()
        census_witness = census.as_dict()
        if census.state != "present":
            errors.append(census.detail or "process census unavailable"); unbounded = True
        declared = {(inv.repo_role, n): inv for inv in inventories for n in (1, 2, 3)}
        reservations: dict[int, list[str]] = {n: [] for n in (1, 2, 3)}
        confirmed = 0
        retained_pids = set()
        for (role, number), inv in declared.items():
            sup = self if inv.source == self.inventory.source else Supervisor(inv)
            port = _port_observation(str(inv.raw["server"]["host"]), int(inv.slot(number)["backend_port"]))
            observations.append(port)
            occupied = port.state != "absent"
            if port.state == "unavailable":
                errors.append(f"{role} wt{number} endpoint observation unavailable")
            try:
                m, record_witnesses = sup._read_metadata("backend", number)
                observations.extend(record_witnesses)
                if m is not None:
                    if m.get("phase", "running") != "running":
                        occupied = True
                    if m.get("signature"):
                        seen = observe_process(m["pid"], m["signature"]); observations.append(seen)
                        occupied = occupied or seen.state != "absent"
                        if seen.state == "present":
                            confirmed += 1
                        elif seen.state in {"unavailable", "mismatch"}:
                            errors.append(f"{role} wt{number} identity {seen.state}")
                    for child in m.get("descendants", []):
                        seen = observe_process(child["pid"], child["signature"]); observations.append(seen)
                        if seen.state != "absent":
                            occupied = True; retained_pids.add(child["pid"])
                        if seen.state in {"unavailable", "mismatch"}:
                            errors.append(f"{role} wt{number} retained descendant {seen.state}")
            except SlotError as exc:
                occupied = True; observations.extend(exc.observations)
                errors.append(f"{role} wt{number} record unavailable: {str(exc)[:2048]}")
            project_rows = [row for row in census.rows if str(inv.lean_root(number)) in row.command]
            if project_rows:
                occupied = True
                try:
                    roots = self._project_roots(census, project_rows, str(inv.lean_root(number)), observations)
                    if len(roots) > 1:
                        errors.append(f"multiple service roots for {role} wt{number}")
                except SlotError as exc:
                    errors.append(f"{role} wt{number} ancestry unavailable: {exc}"); unbounded = True
            if occupied:
                reservations[number].append(role)
        projects = [str(inv.lean_root(n)) for inv in inventories for n in (1, 2, 3)]
        mapped_pids = set(retained_pids)
        for row in census.rows:
            if any(project in row.command for project in projects):
                mapped_pids.update(census.descendants(row.pid))
        for row in census.rows:
            if any(mark in row.command for mark in ("lean-lsp-mcp", "lake serve", "lean --server", "lean --worker")) and row.pid not in mapped_pids:
                errors.append("unmapped heavy process: complete reverse-role capacity authority unavailable"); unbounded = True
        root = self.inventory.state_root / "processes"
        records, seen = observe_directory(root); observations.append(seen)
        if seen.state == "unavailable":
            errors.append("backend registry enumeration unavailable"); unbounded = True
        for record in records:
            if not record.name.endswith("-backend.json"):
                continue
            try:
                m = read_json(record)
                if (m.get("repo_role"), m.get("slot")) not in declared:
                    errors.append("process record outside resolved role universe"); unbounded = True
            except (SlotError, TypeError) as exc:
                observations.extend(getattr(exc, "observations", ()))
                errors.append("unreadable backend registry record"); unbounded = True
        conflicts = [n for n, owners in reservations.items() if len(owners) > 1]
        if unbounded:
            for n in (1, 2, 3):
                if not reservations[n]:
                    reservations[n].append("unavailable")
        return {"complete": not errors, "errors": errors, "confirmed_services": confirmed,
                "reserved_physical_slots": [n for n, owners in reservations.items() if owners],
                "owners": reservations, "conflicts": conflicts,
                "observations": [item.as_dict() for item in observations] + [census_witness]}

    def global_backend_count(self) -> int:
        """Observed registered services only; admission uses capacity_census."""
        return self.capacity_census()["confirmed_services"]

    def global_backend_owners(self, number: int) -> list[str]:
        return sorted(self.capacity_census()["owners"][number])

    def _assert_quiescent(self, kind: str, number: int, *,
                          observations: list[Observation] | None = None) -> None:
        host = str(self.inventory.raw["server"]["host"])
        port = _port_observation(host, int(self.inventory.slot(number)[f"{kind}_port"]))
        witnesses = observations if observations is not None else []
        witnesses.append(port)
        if port.state != "absent":
            raise SlotError(f"{kind} wt{number} not quiescent: endpoint {port.state}", observations=(port,))
        census = process_snapshot(); witnesses.append(census.as_observation())
        if census.state != "present":
            raise SlotError(f"{kind} wt{number} process census unavailable: {census.detail}", observations=(census.as_observation(),))
        registry, registry_seen = observe_directory(self.inventory.state_root / "processes")
        witnesses.append(registry_seen)
        if registry_seen.state == "unavailable":
            raise SlotError("process registry quiescence observation unavailable", observations=(registry_seen,))
        metadata, record_witnesses = self._read_metadata(kind, number); witnesses.extend(record_witnesses)
        if metadata:
            pids = ({metadata["pid"]} if "pid" in metadata else set()) | {child["pid"] for child in metadata.get("descendants", [])}
            if any(row.pid in pids for row in census.rows):
                raise SlotError(f"{kind} wt{number} owned process/descendant remains", observations=(census.as_observation(),))
        if kind == "proxy":
            family, errors = self._role_inventories(retain_aliases=True, observations=witnesses)
            if errors:
                raise SlotError("proxy inventory-alias quiescence unavailable: " + "; ".join(errors), observations=tuple(witnesses))
            aliases = {str(inv.source) for inv in family if inv.repo_role == self.inventory.repo_role}
            wrapper = str(self.inventory.repo_root / "scripts" / "slotctl.py")
            for row in census.rows:
                try:
                    arguments = shlex.split(row.command)
                except ValueError as exc:
                    raise SlotError("proxy command observation unavailable") from exc
                if wrapper in arguments and "_proxy" in arguments and "--inventory" in arguments and "--slot" in arguments:
                    try:
                        inventory = arguments[arguments.index("--inventory") + 1]
                        slot = arguments[arguments.index("--slot") + 1]
                    except IndexError as exc:
                        raise SlotError("proxy command observation incomplete") from exc
                    if slot == str(number):
                        if inventory not in aliases:
                            raise SlotError(f"proxy wt{number} unclassified fixed-slot wrapper remains")
                        # Same-domain aliases count once but retain every filename
                        # for observation; no missing record authorizes adoption.
                        raise SlotError(f"proxy wt{number} fixed-inventory wrapper remains (inventory={inventory})")
        if kind == "backend":
            project = str(self.inventory.lean_root(number))
            if any(project in row.command for row in census.rows):
                raise SlotError(f"backend wt{number} fixed-project process remains")
            invs, errors = self._role_inventories(observations=witnesses)
            mapped = set()
            for row in census.rows:
                if any(str(inv.lean_root(n)) in row.command for inv in invs for n in (1, 2, 3)):
                    mapped.update(census.descendants(row.pid))
            if errors or any(any(mark in row.command for mark in ("lean-lsp-mcp", "lake serve", "lean --server", "lean --worker")) and row.pid not in mapped for row in census.rows):
                raise SlotError("fixed-project descendant quiescence unavailable", observations=tuple(witnesses))

    def _wait_port(self, host: str, port: int, *, open_: bool) -> None:
        deadline = time.monotonic() + float(self.inventory.raw["server"].get("startup_timeout_seconds", 45))
        expected = "present" if open_ else "absent"
        while time.monotonic() < deadline:
            seen = _port_observation(host, port)
            if seen.state == "unavailable":
                raise SlotError(f"port observation unavailable: {seen.detail}", observations=(seen,))
            if seen.state == expected:
                return
            time.sleep(0.1)
        raise SlotError(f"timed out waiting for {host}:{port} to {expected}")

    def _spawn(self, kind: str, number: int, command: list[str], port: int) -> None:
        fingerprint = self._runtime_fingerprint(kind, number, command)
        metadata = self._metadata(kind, number)
        if metadata:
            seen = observe_process(int(metadata.get("pid", 0)), metadata.get("signature"))
            if metadata.get("phase", "running") == "running" and metadata.get("signature") and seen.state == "present":
                if metadata.get("runtime_fingerprint") != fingerprint:
                    raise SlotError("managed process is stale; root must coordinate drained reload")
                endpoint = _port_observation(str(self.inventory.raw["server"]["host"]), port)
                if endpoint.state != "present":
                    raise SlotError(f"managed process endpoint {endpoint.state}; registration retained")
                return
            raise SlotError(f"{kind} wt{number} has retained registration/reservation; no adoption")
        self._assert_quiescent(kind, number)
        path = self.inventory.process_path(kind, number)
        pending = {"schema_version": SCHEMA_VERSION, "process_schema_version": 2,
                   "phase": "launch_pending", "launch_token": secrets.token_hex(16),
                   "repo_role": self.inventory.repo_role, "slot": number, "kind": kind,
                   "inventory_source": str(self.inventory.source), "project": str(self.inventory.lean_root(number)),
                   "command": command, "runtime_fingerprint": fingerprint, "port": port,
                   "started_at": now_iso(), "initiator_pid": os.getpid()}
        atomic_json(path, pending)  # A failed reservation must precede and prevent Popen.
        process = None
        creation_signature = None
        try:
            environment = os.environ.copy()
            if kind == "backend":
                environment["LEAN_LSP_MCP_TOKEN"] = self.inventory.backend_token(number)
            log_path = self.inventory.log_path(kind, number)
            log_path.parent.mkdir(parents=True, exist_ok=True)
            with log_path.open("ab", buffering=0) as log:
                process = subprocess.Popen(command, cwd=self.inventory.repo_root, env=environment,
                                           stdin=subprocess.DEVNULL, stdout=log, stderr=subprocess.STDOUT,
                                           start_new_session=True)
            pending["pid"] = process.pid
            created = observe_process(process.pid)
            if created.state != "present" or not created.signature or getattr(process, "returncode", None) is not None:
                raise SlotError("new process coherent creation identity unavailable", observations=(created,))
            creation_signature = created.signature
            pending["signature"] = creation_signature
            atomic_json(path, pending)
            self._wait_port(str(self.inventory.raw["server"]["host"]), port, open_=True)
            seen = observe_process(process.pid)
            if seen.state == "present":
                creation_signature = seen.signature
            if process.poll() is not None or seen.state != "present" or not seen.signature:
                raise SlotError("new process identity unavailable")
            pending.update(phase="running", signature=seen.signature)
            atomic_json(path, pending)
        except BaseException as original:
            rollback_error = None
            if process is not None:
                try:
                    if getattr(process, "returncode", None) is not None and not creation_signature:
                        raise SlotError("rollback created handle already reaped without identity; reservation retained")
                    identity = observe_process(process.pid, creation_signature or pending.get("signature"))
                    if identity.state == "unavailable" and creation_signature:
                        identity = _observe_created_handle(process, creation_signature)
                    if identity.state not in {"present", "absent"} or (identity.state == "present" and not identity.signature):
                        raise SlotError("rollback owned identity unavailable/mismatch; reservation retained", observations=(identity,))
                    # An observation/write failure cannot disable bounded cleanup of a
                    # valid exact creation handle. Descendant uncertainty still retains
                    # the prelaunch reservation after cleanup rather than declaring free.
                    snapshot = process_snapshot()
                    descendant_error = None
                    descendants = []
                    if snapshot.state != "present":
                        descendant_error = SlotError("rollback descendant census unavailable", observations=(snapshot.as_observation(),))
                    elif identity.state == "present":
                        root = next((row for row in snapshot.rows if row.pid == process.pid), None)
                        if root is None or root.signature != identity.signature:
                            descendant_error = SlotError("rollback wrapper census identity inconsistent")
                        for row in snapshot.rows:
                            if descendant_error is None and row.pid in snapshot.descendants(process.pid):
                                expected = identity.signature if row.pid == process.pid else row.signature
                                seen = observe_process(row.pid, expected)
                                if seen.state != "present" or not seen.signature:
                                    descendant_error = SlotError("rollback descendant identity unavailable/mismatch")
                                    break
                                descendants.append({"pid": row.pid, "signature": expected})
                    pending.update(phase="launch_pending", descendants=descendants)
                    try:
                        atomic_json(path, pending)
                    except (OSError, SlotError):
                        pass  # Earlier pending reservation remains durable during cleanup.
                    if descendant_error is None:
                        for child in descendants:
                            if child["pid"] == process.pid:
                                continue
                            check = observe_process(child["pid"], child["signature"])
                            if check.state != "present":
                                descendant_error = SlotError("rollback child identity changed/unavailable")
                                break
                            os.kill(child["pid"], signal.SIGTERM)
                    # Check the original creation identity again immediately before
                    # using its unreaped handle; never signal a guessed replacement PID.
                    check = observe_process(process.pid, identity.signature)
                    if check.state == "unavailable" and creation_signature:
                        check = _observe_created_handle(process, creation_signature)
                    if check.state not in {"present", "absent"}:
                        raise SlotError("rollback wrapper identity changed/unavailable", observations=(check,))
                    if process.poll() is None:
                        process.terminate()
                    process.wait(timeout=5)
                    if descendant_error is not None:
                        raise descendant_error
                    deadline = time.monotonic() + 5
                    while True:
                        seen = [observe_process(child["pid"], child["signature"]) for child in descendants]
                        if any(item.state in {"unavailable", "mismatch"} for item in seen):
                            raise SlotError("rollback descendant exit observation unavailable/mismatch")
                        if all(item.state == "absent" for item in seen):
                            break
                        if time.monotonic() >= deadline:
                            raise SlotError("rollback descendants remain after bounded wait")
                        time.sleep(0.1)
                    self._assert_quiescent(kind, number)
                    path.unlink(missing_ok=True)
                except BaseException as exc:
                    rollback_error = exc
            else:
                # Popen never returned a handle: conservatively retain pending evidence.
                rollback_error = SlotError("launch did not return an owned handle")
            if rollback_error is not None:
                pending.update(phase="uncertain_residual", error=str(original), rollback_error=str(rollback_error))
                try:
                    atomic_json(path, pending)
                except (OSError, SlotError):
                    pass  # The earlier durable pending record continues to reserve this slot.
                raise SlotError(f"launch failed: {original}; residual retained: {rollback_error}") from original
            raise

    def _stop(self, kind: str, number: int, port: int) -> None:
        path = self.inventory.process_path(kind, number)
        metadata = self._metadata(kind, number)
        if metadata is None or not metadata.get("signature"):
            self._assert_quiescent(kind, number)
            path.unlink(missing_ok=True)
            return
        seen = observe_process(int(metadata.get("pid", 0)), metadata["signature"])
        if seen.state == "absent":
            self._assert_quiescent(kind, number)
            path.unlink(missing_ok=True)
            return
        if seen.state != "present":
            raise SlotError(f"refusing stop: process identity {seen.state}; registration retained", observations=(seen,))
        census = process_snapshot()
        if census.state != "present":
            raise SlotError("refusing stop: descendant observation unavailable", observations=(census.as_observation(),))
        identities = {int(child["pid"]): child["signature"] for child in metadata.get("descendants", [])}
        identities[int(metadata["pid"])] = metadata["signature"]
        census_identities = {row.pid: row.signature for row in census.rows}
        if census_identities.get(int(metadata["pid"])) != metadata["signature"]:
            raise SlotError("refusing stop: wrapper census identity unavailable/mismatch", observations=(census.as_observation(),))
        owned = []
        pids = census.descendants(int(metadata["pid"])) | set(identities)
        for pid in sorted(pids):
            child = observe_process(pid, identities.get(pid, census_identities.get(pid)))
            if child.state == "absent":
                continue
            if child.state != "present" or not child.signature:
                raise SlotError("refusing stop: descendant identity unavailable/mismatch", observations=(child,))
            owned.append({"pid": pid, "signature": child.signature})
        # Durable descendants survive wrapper exit/reparenting and future invocations.
        metadata["descendants"] = owned
        atomic_json(path, metadata)
        for child in reversed(owned):
            check = observe_process(child["pid"], child["signature"])
            if check.state == "absent":
                continue
            if check.state != "present":
                raise SlotError("refusing to signal mismatched/unavailable owned descendant", observations=(check,))
            os.kill(child["pid"], signal.SIGTERM)
        deadline = time.monotonic() + 10
        while time.monotonic() < deadline:
            results = [observe_process(child["pid"], child["signature"]) for child in owned]
            if any(item.state in {"unavailable", "mismatch"} for item in results):
                raise SlotError("post-SIGTERM observation unavailable/mismatch; registration retained", observations=tuple(results))
            if all(item.state == "absent" for item in results):
                self._assert_quiescent(kind, number)
                path.unlink(missing_ok=True)
                return
            time.sleep(0.1)
        raise SlotError("owned process did not stop; registration retained; no automatic SIGKILL", observations=tuple(results))

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
        if self._running("backend", number):
            return
        census = self.capacity_census()
        if not census["complete"] or census["conflicts"]:
            raise SlotError(f"global capacity unavailable/conflicting: {census['errors']}")
        if len(census["reserved_physical_slots"]) >= int(self.inventory.raw["max_active_slots"]):
            raise SlotError("global heavy-backend limit reached; residual capacity reserved")
        if census["owners"][number]:
            raise SlotError(f"physical wt{number} already reserved by {census['owners'][number]}")
        self._spawn("backend", number, self.backend_command(number), int(self.inventory.slot(number)["backend_port"]))

    def _stop_backend_unlocked(self, number: int) -> None:
        self._stop("backend", number, int(self.inventory.slot(number)["backend_port"]))

    def _assert_backend_owned_or_stopped(self, number: int) -> None:
        state = self.process_state("backend", number)
        if state in {"running", "stale"}:
            return
        if state != "down":
            raise SlotError(f"backend wt{number} is {state}; no unknown process management")
        self._assert_quiescent("backend", number)

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

        Entry requires a healthy proxy and confirmed backend/project quiescence.
        A legitimately stopped leased backend is allowed; unavailable observations
        never permit the caller's cache transition. Exit attempts healthy rewarm,
        retaining both the body failure and any restoration failure.
        """
        with self.lifecycle():
            self.assert_proxy_healthy(number)
            self._assert_backend_owned_or_stopped(number)
            if self.process_state("backend", number) in {"running", "stale"}:
                self._stop_backend_unlocked(number)
            self._assert_quiescent("backend", number)
            try:
                yield
            except BaseException as original:
                try:
                    self._start_backend_unlocked(number)
                    self.assert_healthy(number)
                except BaseException as restoration:
                    raise SlotError(f"transition failed: {original}; restoration failed: {restoration}") from original
                raise
            else:
                self._start_backend_unlocked(number)
                self.assert_healthy(number)

    @contextmanager
    def activating_from(self, number: int, counterpart: "Supervisor") -> Iterator[None]:
        """Park a paired backend, mutate the target cache, then activate target.

        The shared lifecycle lock makes the handoff atomic with respect to all
        controller-managed endpoints. Failure attempts bounded restoration; a
        restoration failure retains reservations and both error explanations.
        """
        if counterpart.inventory.state_root != self.inventory.state_root:
            raise SlotError(
                "counterpart supervisors must share one runtime state directory"
            )
        with self.lifecycle():
            self._start_proxy_unlocked(number)
            self._assert_backend_owned_or_stopped(number)
            counterpart._assert_backend_owned_or_stopped(number)
            if self.process_state("backend", number) in {"running", "stale"}:
                raise SlotError(
                    f"target backend for {self.inventory.repo_role} wt{number} is already running"
                )
            counterpart_was_running = counterpart.process_state("backend", number) in {"running", "stale"}
            if counterpart_was_running:
                counterpart._stop_backend_unlocked(number)
            self._assert_quiescent("backend", number)
            counterpart._assert_quiescent("backend", number)
            try:
                yield
                self._start_backend_unlocked(number)
                self.assert_healthy(number)
            except BaseException as original:
                try:
                    self._assert_backend_owned_or_stopped(number)
                    if self.process_state("backend", number) in {"running", "stale"}:
                        self._stop_backend_unlocked(number)
                    self._assert_quiescent("backend", number)
                    counterpart._assert_backend_owned_or_stopped(number)
                    if counterpart_was_running and not counterpart._running("backend", number):
                        counterpart._start_backend_unlocked(number)
                        counterpart.assert_healthy(number)
                except BaseException as restoration:
                    raise SlotError(f"paired transition failed: {original}; restoration failed: {restoration}") from original
                raise

    def restore_counterpart(self, number: int, counterpart: "Supervisor") -> None:
        """Return one leased slot to its default paired backend without overlap."""
        if counterpart.inventory.state_root != self.inventory.state_root:
            raise SlotError(
                "counterpart supervisors must share one runtime state directory"
            )
        with self.lifecycle():
            self._assert_backend_owned_or_stopped(number)
            counterpart._assert_backend_owned_or_stopped(number)
            target_was_running = self.process_state("backend", number) in {"running", "stale"}
            if target_was_running:
                self._stop_backend_unlocked(number)
            try:
                if not counterpart._running("backend", number):
                    counterpart._start_backend_unlocked(number)
            except BaseException as original:
                try:
                    counterpart._assert_backend_owned_or_stopped(number)
                    if counterpart.process_state("backend", number) in {"running", "stale"}:
                        counterpart._stop_backend_unlocked(number)
                    counterpart._assert_quiescent("backend", number)
                    if target_was_running and not self._running("backend", number):
                        self._start_backend_unlocked(number)
                        self.assert_healthy(number)
                except BaseException as restoration:
                    raise SlotError(f"paired restoration failed: {original}; target recovery failed: {restoration}") from original
                raise

    def start(self) -> dict[str, Any]:
        started: list[tuple[str, int]] = []
        with self.lifecycle():
            try:
                for number in (1, 2, 3):
                    if self.process_state("proxy", number) not in {"running", "down"}:
                        raise SlotError("proxy unknown/unavailable/stale; coordinate drained diagnosis/reload")
                    if self.process_state("backend", number) not in {"running", "down"}:
                        raise SlotError("backend unknown/unavailable/stale; retain physical reservation")
                    if not self._running("proxy", number):
                        self._start_proxy_unlocked(number)
                        started.append(("proxy", number))
                    expected_backend = self.inventory.backend_expected(number)
                    if expected_backend and not self._running("backend", number):
                        self._start_backend_unlocked(number)
                        started.append(("backend", number))
                    elif not expected_backend and self._running("backend", number):
                        self._stop_backend_unlocked(number)
                # Do this while the front doors are up but before any client attaches:
                # an empty tool list at attach time is permanent for that session.
                self._harvest_tool_list_unlocked()
            except Exception as original:
                rollback_errors = []
                for kind, number in reversed(started):
                    slot = self.inventory.slot(number)
                    port = int(slot[f"{kind}_port"])
                    try:
                        self._stop(kind, number, port)
                    except (SlotError, OSError) as exc:
                        rollback_errors.append(str(exc))
                if rollback_errors:
                    raise SlotError(f"global startup failed: {original}; rollback residuals: {rollback_errors}") from original
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
                f"proxy for wt{number} is not healthy; diagnose ownership/observation before coordinated reload"
            )

    def assert_healthy(self, number: int) -> None:
        slot = self.inventory.slot(number)
        host = str(self.inventory.raw["server"]["host"])
        self.assert_proxy_healthy(number)
        if not self._running("backend", number) or not _port_open(
            host, int(slot["backend_port"])
        ):
            raise SlotError(
                f"backend for wt{number} is not healthy; diagnose ownership/observation before coordinated reload"
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

    def cached_tool_list(self) -> list[dict[str, Any]] | None:
        """The tool list to advertise when a slot's backend is down, or None.

        Keyed on `tool_list_key`, so a pinned-server bump or a `disabled_tools` edit
        invalidates it while ordinary slot churn does not.
        """
        try:
            cached = read_json(tool_cache_path(self.inventory.state_root))
        except (SlotError, OSError):
            return None
        if cached.get("key") != tool_list_key(self.inventory.raw["server"]):
            return None
        tools = cached.get("tools")
        return tools if isinstance(tools, list) and tools else None

    def _fetch_tool_list(self, number: int) -> list[dict[str, Any]] | None:
        """Ask a RUNNING backend what it offers. Returns None on any failure."""
        slot = self.inventory.slot(number)
        host = str(self.inventory.raw["server"]["host"])
        headers = {
            "Accept": "application/json, text/event-stream",
            "Content-Type": "application/json",
        }
        if self.inventory.client_auth_mode == "bearer":
            headers["Authorization"] = f"Bearer {self.inventory.token('codex')}"

        def request(payload, session_id=None):
            connection = http.client.HTTPConnection(
                host, int(slot["proxy_port"]), timeout=120
            )
            current = dict(headers)
            if session_id:
                current["Mcp-Session-Id"] = session_id
            connection.request(
                "POST", "/mcp?client=codex", body=json.dumps(payload), headers=current
            )
            response = connection.getresponse()
            body = response.read()
            response_headers = dict(response.getheaders())
            connection.close()
            if response.status not in {200, 202}:
                raise SlotError(f"tool-list harvest failed ({response.status})")
            return (self._sse_json(body) if body else {}), response_headers

        try:
            _, response_headers = request(
                {
                    "jsonrpc": "2.0",
                    "id": 1,
                    "method": "initialize",
                    "params": {
                        "protocolVersion": "2025-06-18",
                        "capabilities": {},
                        "clientInfo": {"name": "slotctl-harvest", "version": "1"},
                    },
                }
            )
            session_id = response_headers.get("Mcp-Session-Id") or response_headers.get(
                "mcp-session-id"
            )
            request({"jsonrpc": "2.0", "method": "notifications/initialized"}, session_id)
            listed, _ = request(
                {"jsonrpc": "2.0", "id": 2, "method": "tools/list"}, session_id
            )
        except (SlotError, OSError, http.client.HTTPException, ValueError):
            return None
        tools = (listed.get("result") or {}).get("tools")
        return tools if isinstance(tools, list) and tools else None

    def _harvest_tool_list_unlocked(self) -> bool:
        """Populate the cache once, briefly borrowing a backend if none is running.

        Without this, the FIRST session on a fresh clone sees no slot tools at all under
        `backend_policy: "leased"` — every backend is down at attach time, and MCP tools
        are registered at session start. Borrowed backends undergo bounded cleanup;
        failed cleanup retains its reservation and prevents publishing a new cache.
        """
        if self.cached_tool_list() is not None:
            return False
        for number in (1, 2, 3):
            if not self._running("backend", number):
                continue
            tools = self._fetch_tool_list(number)
            if tools:
                self._write_tool_cache(tools)
                return True
        for number in (1, 2, 3):
            if not self.inventory.slot(number):
                continue
            try:
                self._start_backend_unlocked(number)
            except SlotError as exc:
                raise SlotError(f"tool discovery cannot borrow safe capacity: {exc}") from exc
            try:
                tools = self._fetch_tool_list(number)
            except BaseException as original:
                try:
                    self._stop_backend_unlocked(number)
                except BaseException as cleanup:
                    raise SlotError(f"tool discovery failed: {original}; borrowed cleanup failed: {cleanup}") from original
                raise
            else:
                self._stop_backend_unlocked(number)
            if tools:
                self._write_tool_cache(tools)
                return True
        return False

    def _write_tool_cache(self, tools: list[dict[str, Any]]) -> None:
        atomic_json(
            tool_cache_path(self.inventory.state_root),
            {
                "key": tool_list_key(self.inventory.raw["server"]),
                "tools": tools,
                "harvested_at": now_iso(),
            },
        )

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

    def _resource_status(self, kind: str, number: int) -> dict[str, Any]:
        errors = []
        witnesses = []
        metadata = None
        metadata_error = False
        unvalidated_pid = None
        try:
            metadata, record_witnesses = self._read_metadata(kind, number)
            witnesses.extend(record_witnesses)
        except SlotError as exc:
            metadata_error = True; unvalidated_pid = exc.recorded_pid
            witnesses.extend(exc.observations); errors.append(str(exc))
        endpoint = _port_observation(str(self.inventory.raw["server"]["host"]),
                                     int(self.inventory.slot(number)[f"{kind}_port"]))
        witnesses.append(endpoint)
        process = Observation("unavailable", detail="no authoritative recorded PID",
                              target=f"{kind} wt{number}", operation="identity-unresolved")
        if metadata and metadata.get("signature"):
            process = observe_process(metadata["pid"], metadata["signature"])
        witnesses.append(process)
        children = [observe_process(child["pid"], child["signature"])
                    for child in metadata.get("descendants", [])] if metadata else []
        witnesses.extend(children)
        identity_error = any(child.state in {"unavailable", "mismatch"} for child in children)
        if endpoint.state == "unavailable":
            errors.append(f"endpoint observation unavailable: {endpoint.detail}")
        if metadata and process.state in {"unavailable", "mismatch"}:
            errors.append(f"process observation {process.state}: {process.detail}")
        if identity_error:
            errors.append("retained descendant identity observation unavailable/mismatch")
        state = "unavailable"
        if not metadata_error and not identity_error and endpoint.state != "unavailable":
            if metadata and metadata.get("phase", "running") != "running":
                state = "uncertain_residual"
            elif metadata and process.state in {"unavailable", "mismatch"}:
                state = process.state
            elif metadata and process.state == "present":
                if endpoint.state == "present":
                    try:
                        state = "running" if metadata.get("runtime_fingerprint") == self._runtime_fingerprint(kind, number) else "stale"
                    except SlotError as exc:
                        witnesses.extend(exc.observations); errors.append(str(exc))
            elif any(child.state == "present" for child in children):
                state = "uncertain_residual"
            elif endpoint.state == "present":
                state = "unknown"
            else:
                try:
                    self._assert_quiescent(kind, number, observations=witnesses)
                    state = "down"
                except SlotError as exc:
                    witnesses.extend(exc.observations); errors.append(str(exc))
        return {"state": state,
                "record_phase": "unavailable" if metadata_error else metadata.get("phase", "running") if metadata else "missing",
                "identity_authority": "unavailable" if metadata_error or identity_error else "managed" if metadata and metadata.get("signature") else "unverified" if metadata else "none",
                "recorded_pid": metadata.get("pid") if metadata else unvalidated_pid,
                "process_observation": process.state, "process_detail": process.detail,
                "endpoint_observation": endpoint.state, "endpoint_detail": endpoint.detail,
                "observations": [item.as_dict() for item in witnesses], "errors": errors}

    def status(self) -> dict[str, Any]:
        slots = []
        for number in (1, 2, 3):
            slot = self.inventory.slot(number)
            resources = {kind: self._resource_status(kind, number) for kind in ("proxy", "backend")}
            slots.append(
                {
                    "slot": number,
                    "repo_role": self.inventory.repo_role,
                    "lease_state": (self.inventory.lease(number, required=False) or {}).get("state", "FREE"),
                    "proxy_port": int(slot["proxy_port"]),
                    "backend_port": int(slot["backend_port"]),
                    "proxy_running": resources["proxy"]["state"] == "running",
                    "backend_running": resources["backend"]["state"] == "running",
                    "proxy_state": resources["proxy"]["state"],
                    "backend_state": resources["backend"]["state"],
                    "resources": resources,
                }
            )
        census = self.capacity_census()
        return {
            "schema_version": SCHEMA_VERSION,
            "global_running_backends": census["confirmed_services"],
            "capacity_complete": census["complete"],
            "capacity_errors": census["errors"],
            "capacity_observations": census["observations"],
            "capacity_conflicts": census["conflicts"],
            "reserved_physical_slots": census["reserved_physical_slots"],
            "slots": slots,
        }
