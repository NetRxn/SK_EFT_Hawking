"""Fail-closed lease, build-epoch, and integration controller for ADR-008."""

from __future__ import annotations

import hashlib
import os
import shlex
import shutil
import subprocess
import sys
import tempfile
import tomllib
from datetime import datetime, timezone
from pathlib import Path
from typing import Any, Iterable

from .state import (
    SCHEMA_VERSION,
    Inventory,
    SlotError,
    atomic_json,
    atomic_write,
    canonical_digest,
    directory_lock,
    exclusive_json,
    now_iso,
    process_matches,
    process_start_signature,
    read_json,
    token_hash,
)


def _run(
    command: list[str],
    *,
    cwd: Path,
    check: bool = True,
    capture: bool = True,
) -> subprocess.CompletedProcess[str]:
    result = subprocess.run(
        command,
        cwd=cwd,
        check=False,
        text=True,
        capture_output=capture,
    )
    if check and result.returncode:
        detail = (result.stderr or result.stdout or "command failed").strip()
        raise SlotError(f"{' '.join(command)} failed in {cwd}: {detail}")
    return result


def _git(cwd: Path, *args: str, check: bool = True) -> str:
    return _run(["git", *args], cwd=cwd, check=check).stdout.strip()


class Controller:
    def __init__(self, inventory: Inventory | None = None):
        self.inventory = inventory or Inventory.load()
        self.inventory.state_root.mkdir(parents=True, exist_ok=True)

    @property
    def repo(self) -> Path:
        return self.inventory.repo_root

    def _slot_lock(self, number: int):
        return directory_lock(
            self.inventory.state_root / "locks" / f"wt{number}.lock",
            purpose=f"slot wt{number} operation",
        )

    def _primary_sha(self, ref: str) -> str:
        return _git(self.repo, "rev-parse", "--verify", f"{ref}^{{commit}}")

    def _dependency_primary_sha(self) -> str | None:
        paired = self.inventory.paired_inventory()
        if paired is None:
            return None
        configured = self.inventory.raw["paired_dependency"]
        dependency_ref = str(configured.get("base_ref", "main"))
        expected_root = paired.repo_root / "lean"
        actual_root = self.inventory.primary_dependency_lean_root()
        if actual_root != expected_root.resolve():
            raise SlotError(
                "primary downstream dependency path mismatch: "
                f"{actual_root} != {expected_root.resolve()}"
            )
        self._assert_lake_dependency_path(self.repo / "lean", "path_from_primary_lean")
        dependency_sha = _git(
            paired.repo_root, "rev-parse", "--verify", f"{dependency_ref}^{{commit}}"
        )
        actual_head = _git(paired.repo_root, "rev-parse", "HEAD")
        if actual_head != dependency_sha:
            raise SlotError(
                "downstream dependency primary checkout is not on its configured base: "
                f"{actual_head} != {dependency_sha}"
            )
        dirty = self._dirty(paired.repo_root)
        if dirty:
            raise SlotError(
                "downstream dependency primary checkout is dirty: "
                + ", ".join(dirty[:8])
            )
        return dependency_sha

    def _assert_lake_dependency_path(self, lean_root: Path, path_key: str) -> None:
        configured = self.inventory.raw.get("paired_dependency")
        if configured is None:
            return
        dependency_name = str(configured.get("lake_dependency_name", ""))
        if not dependency_name:
            raise SlotError("paired_dependency.lake_dependency_name is required")
        lakefile = lean_root / "lakefile.toml"
        try:
            parsed = tomllib.loads(lakefile.read_text(encoding="utf-8"))
        except (OSError, tomllib.TOMLDecodeError) as exc:
            raise SlotError(
                f"could not inspect paired Lake dependency in {lakefile}: {exc}"
            ) from exc
        requirements = parsed.get("require", [])
        if not isinstance(requirements, list):
            raise SlotError(f"invalid Lake requirements in {lakefile}")
        matches = [
            item
            for item in requirements
            if isinstance(item, dict) and str(item.get("name", "")) == dependency_name
        ]
        if len(matches) != 1 or "path" not in matches[0]:
            raise SlotError(
                f"expected exactly one path dependency {dependency_name!r} in {lakefile}"
            )
        declared = Path(os.path.normpath(str(matches[0]["path"])))
        expected = Path(os.path.normpath(str(configured.get(path_key, ""))))
        if not str(expected) or declared != expected:
            raise SlotError(
                f"Lake dependency path mismatch in {lakefile}: {declared} != {expected}"
            )

    def _assert_paired_dependency(
        self,
        number: int,
        expected_sha: str | None = None,
        *,
        require_primary_match: bool = True,
    ) -> str | None:
        paired = self.inventory.paired_inventory()
        if paired is None:
            return None
        paired_controller = Controller(paired)
        worktree, _ = paired_controller._assert_worktree_identity(number)
        actual_root = self.inventory.paired_dependency_lean_root(number)
        expected_root = paired.lean_root(number).resolve()
        if actual_root != expected_root:
            raise SlotError(
                f"paired dependency path mismatch for wt{number}: "
                f"{actual_root} != {expected_root}"
            )
        self._assert_lake_dependency_path(
            self.inventory.lean_root(number), "path_from_slot_lean"
        )
        dirty = paired_controller._dirty(worktree)
        if dirty:
            raise SlotError(
                f"paired dependency wt{number} is dirty: {', '.join(dirty[:8])}"
            )
        current_primary_sha = (
            self._dependency_primary_sha()
            if require_primary_match or expected_sha is None
            else None
        )
        dependency_sha = expected_sha or current_primary_sha
        assert dependency_sha is not None
        if expected_sha is not None and current_primary_sha not in {None, expected_sha}:
            raise SlotError(
                f"paired dependency base advanced for wt{number}: "
                f"{current_primary_sha} != {expected_sha}"
            )
        head = _git(worktree, "rev-parse", "HEAD")
        if head != dependency_sha:
            raise SlotError(
                f"paired dependency wt{number} is not pinned: {head} != {dependency_sha}"
            )
        return dependency_sha

    def _branch(self, path: Path) -> str:
        branch = _git(path, "branch", "--show-current")
        if not branch:
            raise SlotError(f"detached HEAD is not permitted: {path}")
        return branch

    def _dirty(self, path: Path) -> list[str]:
        return [
            line for line in _git(path, "status", "--porcelain=v1").splitlines() if line
        ]

    def _assert_worktree_identity(self, number: int) -> tuple[Path, dict[str, Any]]:
        slot = self.inventory.slot(number)
        worktree = self.inventory.worktree(number)
        if not worktree.is_dir():
            raise SlotError(f"configured worktree is missing: {worktree}")
        top = Path(_git(worktree, "rev-parse", "--show-toplevel")).resolve()
        if top != worktree:
            raise SlotError(
                f"worktree root mismatch for wt{number}: {top} != {worktree}"
            )
        if self._branch(worktree) != slot["branch"]:
            raise SlotError(
                f"branch mismatch for wt{number}: expected {slot['branch']!r}, "
                f"found {self._branch(worktree)!r}"
            )
        return worktree, slot

    def _owner(self) -> dict[str, Any]:
        raw = os.environ.get("LEAN_SLOT_OWNER_PID")
        if raw:
            pid = int(raw)
            return {
                "owner_kind": "process",
                "owner_pid": pid,
                "owner_signature": process_start_signature(pid),
            }
        # A slot lease outlives any one CLI invocation, so the owner must be the driving
        # session, not the shell that happened to run `acquire`. `LEAN_SLOT_OWNER_SESSION`
        # is the product-neutral override (S-J); the client variables follow it so neither
        # product needs an explicit export.
        for variable in (
            "LEAN_SLOT_OWNER_SESSION",
            "CODEX_THREAD_ID",
            "CLAUDE_CODE_SESSION_ID",
        ):
            session_id = os.environ.get(variable)
            if session_id:
                return {
                    "owner_kind": "session",
                    "owner_session_hash": hashlib.sha256(
                        session_id.encode()
                    ).hexdigest(),
                }
        pid = os.getppid()
        return {
            "owner_kind": "process",
            "owner_pid": pid,
            "owner_signature": process_start_signature(pid),
        }

    def _lease_for_command(
        self, number: int, *, states: Iterable[str] | None = None
    ) -> dict[str, Any]:
        lease = self.inventory.lease(number)
        assert lease is not None
        expected_path = str(self.inventory.worktree(number))
        if lease.get("repo_role") != self.inventory.repo_role:
            raise SlotError(f"repository-role mismatch for wt{number}")
        if lease.get("worktree") != expected_path:
            raise SlotError(f"worktree mismatch for wt{number}")
        if self.inventory.paired_inventory() is not None and not lease.get(
            "public_dependency_sha"
        ):
            raise SlotError(
                f"downstream lease for wt{number} lacks a public dependency SHA"
            )
        auth_mode = self.inventory.client_auth_mode
        if lease.get("client_auth") != auth_mode:
            raise SlotError(f"client-auth mode mismatch for wt{number}")
        if auth_mode == "bearer":
            client = str(lease.get("client", ""))
            current_hash = token_hash(self.inventory.token(client, create=False))
            if lease.get("token_hash") != current_hash:
                raise SlotError(f"session token mismatch for wt{number}")
        current_owner = self._owner()
        if lease.get("owner_kind") != current_owner.get("owner_kind"):
            raise SlotError(f"owner identity kind mismatch for wt{number}")
        if lease.get("owner_kind") == "session" and lease.get(
            "owner_session_hash"
        ) != current_owner.get("owner_session_hash"):
            raise SlotError(f"Codex session owner mismatch for wt{number}")
        if lease.get("owner_kind") == "process" and (
            lease.get("owner_pid") != current_owner.get("owner_pid")
            or lease.get("owner_signature") != current_owner.get("owner_signature")
        ):
            raise SlotError(f"process owner mismatch for wt{number}")
        if states is not None and lease.get("state") not in set(states):
            raise SlotError(
                f"wt{number} is {lease.get('state')}, expected one of {sorted(set(states))}"
            )
        return lease

    def _quarantine(
        self,
        number: int,
        lease: dict[str, Any],
        reason: str,
        *,
        create: bool = False,
    ) -> None:
        lease["state"] = "QUARANTINED"
        lease["quarantine_reason"] = reason
        lease["quarantined_at"] = now_iso()
        if create:
            exclusive_json(self.inventory.lease_path(number), lease)
        else:
            # Quarantining is the CONTROLLER acting, not the owner reporting in. Refreshing
            # the heartbeat here would reset the staleness clock `reclaim` reads, so a failed
            # reclaim would make the next one fail too — forever.
            self.inventory.save_lease(number, lease, touch_heartbeat=False)

    def acquire(self, number: int, *, client: str, base_ref: str) -> dict[str, Any]:
        with self._slot_lock(number):
            if self.inventory.lease(number, required=False) is not None:
                existing = self.inventory.lease(number)
                raise SlotError(
                    f"wt{number} is already leased by {existing.get('client')} "
                    f"in state {existing.get('state')}"
                )
            worktree, slot = self._assert_worktree_identity(number)
            base_sha = self._primary_sha(base_ref)
            public_dependency_sha = self._assert_paired_dependency(number)
            lease: dict[str, Any] = {
                "schema_version": SCHEMA_VERSION,
                "slot": number,
                "repo_role": self.inventory.repo_role,
                "client": client,
                "client_auth": self.inventory.client_auth_mode,
                "base_ref": base_ref,
                "base_sha": base_sha,
                "worktree": str(worktree),
                "branch": slot["branch"],
                "endpoint": slot["endpoint_name"],
                "state": "ACQUIRED",
                "acquired_at": now_iso(),
                "heartbeat_at": now_iso(),
                **self._owner(),
            }
            if self.inventory.client_auth_mode == "bearer":
                lease["token_hash"] = token_hash(self.inventory.token(client))
            if public_dependency_sha is not None:
                lease["public_dependency_sha"] = public_dependency_sha
            dirty = self._dirty(worktree)
            if dirty:
                reason = f"worktree is dirty: {', '.join(dirty[:8])}"
                self._quarantine(number, lease, reason, create=True)
                raise SlotError(f"wt{number} quarantined; {reason}")
            ahead = int(_git(worktree, "rev-list", "--count", f"{base_sha}..HEAD"))
            ancestor = (
                _run(
                    ["git", "merge-base", "--is-ancestor", "HEAD", base_sha],
                    cwd=worktree,
                    check=False,
                ).returncode
                == 0
            )
            if ahead or not ancestor:
                reason = (
                    f"worktree has {ahead} unabsorbed commit(s) or divergent ancestry "
                    f"relative to {base_ref}"
                )
                self._quarantine(number, lease, reason, create=True)
                raise SlotError(f"wt{number} quarantined; {reason}")
            exclusive_json(self.inventory.lease_path(number), lease)
            return lease

    def _fingerprint(
        self,
        commit_sha: str | None = None,
        *,
        public_dependency_sha: str | None = None,
    ) -> dict[str, Any]:
        commit = commit_sha or _git(self.repo, "rev-parse", "HEAD")
        files: dict[str, str] = {}
        for configured in self.inventory.raw["build"]["fingerprint_files"]:
            result = _run(
                ["git", "show", f"{commit}:{configured}"],
                cwd=self.repo,
                check=False,
            )
            if result.returncode:
                raise SlotError(
                    f"build fingerprint input is missing from {commit}: {configured}"
                )
            files[configured] = hashlib.sha256(result.stdout.encode()).hexdigest()
        fingerprint: dict[str, Any] = {
            "schema_version": SCHEMA_VERSION,
            "repo_role": self.inventory.repo_role,
            "commit_sha": commit,
            "files": files,
        }
        current_dependency_sha = self._dependency_primary_sha()
        if current_dependency_sha is not None:
            if (
                public_dependency_sha is not None
                and current_dependency_sha != public_dependency_sha
            ):
                raise SlotError(
                    "downstream public dependency advanced after lease acquisition: "
                    f"{current_dependency_sha} != {public_dependency_sha}"
                )
            fingerprint["public_dependency_sha"] = current_dependency_sha
        fingerprint["digest"] = canonical_digest(fingerprint)
        return fingerprint

    def _matching_epoch(
        self, commit_sha: str, *, public_dependency_sha: str | None = None
    ) -> dict[str, Any]:
        path = self.inventory.epoch_path()
        epoch = read_json(path)
        expected = self._fingerprint(
            commit_sha, public_dependency_sha=public_dependency_sha
        )
        if epoch.get("fingerprint") != expected:
            raise SlotError(
                "no successful-build epoch matches the acquired commit and dependency fingerprint; "
                "run slotctl build from the primary checkout"
            )
        return epoch

    def build(self) -> dict[str, Any]:
        top = Path(_git(self.repo, "rev-parse", "--show-toplevel")).resolve()
        if top != self.repo:
            raise SlotError(
                "authoritative build must run from the configured primary checkout"
            )
        dirty = self._dirty(self.repo)
        if dirty:
            raise SlotError(
                "authoritative build requires a clean committed primary checkout: "
                + ", ".join(dirty[:8])
            )
        lock = self.inventory.state_root / "locks" / "authoritative-build.lock"
        with directory_lock(lock, purpose="authoritative Lean build"):
            command = [str(item) for item in self.inventory.raw["build"]["command"]]
            cwd = self.repo / self.inventory.raw["build"]["cwd"]
            result = _run(command, cwd=cwd, check=False)
            if result.returncode:
                raise SlotError(
                    f"authoritative build failed ({result.returncode}): "
                    f"{(result.stderr or result.stdout).strip()}"
                )
            fingerprint = self._fingerprint()
            epoch = {
                "schema_version": SCHEMA_VERSION,
                "repo_role": self.inventory.repo_role,
                "published_at": now_iso(),
                "fingerprint": fingerprint,
                "build_command": command,
            }
            epoch["epoch_id"] = canonical_digest(epoch)
            atomic_json(self.inventory.epoch_path(), epoch)
            return epoch

    def _replace_lake(self, number: int) -> None:
        source = self.repo / self.inventory.raw["build"]["cwd"] / ".lake"
        destination = self.inventory.lean_root(number) / ".lake"
        if not source.is_dir() or not (source / "build").exists():
            raise SlotError(f"authoritative Lake cache is missing or unbuilt: {source}")
        parent = destination.parent
        temporary = Path(tempfile.mkdtemp(prefix=".lake.slotctl.", dir=parent))
        backup = parent / f".lake.slotctl.backup.{os.getpid()}"
        try:
            shutil.rmtree(temporary)
            clone = subprocess.run(
                ["cp", "-c", "-R", str(source), str(temporary)],
                check=False,
                capture_output=True,
                text=True,
            )
            if clone.returncode:
                if temporary.exists():
                    shutil.rmtree(temporary)
                shutil.copytree(source, temporary, symlinks=True)
            if backup.exists():
                raise SlotError(
                    f"stale Lake backup requires manual inspection: {backup}"
                )
            if destination.exists():
                os.replace(destination, backup)
            os.replace(temporary, destination)
            if backup.exists():
                shutil.rmtree(backup)
        except Exception:
            if not destination.exists() and backup.exists():
                os.replace(backup, destination)
            raise
        finally:
            if temporary.exists():
                shutil.rmtree(temporary)

    def prepare(self, number: int) -> dict[str, Any]:
        with self._slot_lock(number):
            lease = self._lease_for_command(number, states={"ACQUIRED"})
            worktree, _ = self._assert_worktree_identity(number)
            if self._dirty(worktree):
                self._quarantine(number, lease, "worktree became dirty before prepare")
                raise SlotError(
                    f"wt{number} quarantined; worktree became dirty before prepare"
                )
            current_base = self._primary_sha(str(lease["base_ref"]))
            if current_base != lease["base_sha"]:
                self._quarantine(number, lease, "base ref advanced after acquisition")
                raise SlotError(
                    f"wt{number} quarantined; base ref advanced after acquisition"
                )
            public_dependency_sha = lease.get("public_dependency_sha")
            self._assert_paired_dependency(number, public_dependency_sha)
            self._matching_epoch(
                current_base, public_dependency_sha=public_dependency_sha
            )
            lease["state"] = "PREPARING"
            self.inventory.save_lease(number, lease)
            from .supervisor import Supervisor

            supervisor = Supervisor(self.inventory)
            paired_inventory = self.inventory.paired_inventory()
            try:
                if os.environ.get("LEAN_SLOT_SKIP_SUPERVISOR"):
                    _git(worktree, "reset", "--hard", current_base)
                    self._replace_lake(number)
                elif paired_inventory is not None:
                    paired_supervisor = Supervisor(paired_inventory)
                    with supervisor.activating_from(number, paired_supervisor):
                        _git(worktree, "reset", "--hard", current_base)
                        self._replace_lake(number)
                else:
                    with supervisor.paused_backend(number):
                        _git(worktree, "reset", "--hard", current_base)
                        self._replace_lake(number)
            except Exception as exc:
                self._quarantine(number, lease, f"prepare failed: {exc}")
                raise
            lease["state"] = "ACTIVE"
            lease["prepared_epoch"] = read_json(self.inventory.epoch_path())["epoch_id"]
            lease["prepared_at"] = now_iso()
            self.inventory.save_lease(number, lease)
            return lease

    def ready(self, number: int) -> dict[str, Any]:
        with self._slot_lock(number):
            lease = self._lease_for_command(number, states={"ACTIVE"})
            worktree, _ = self._assert_worktree_identity(number)
            try:
                self._assert_paired_dependency(
                    number, lease.get("public_dependency_sha")
                )
            except SlotError as exc:
                self._quarantine(number, lease, str(exc))
                raise
            dirty = self._dirty(worktree)
            if dirty:
                self._quarantine(
                    number, lease, f"ready requires a clean commit: {dirty[:8]}"
                )
                raise SlotError(
                    f"wt{number} quarantined; ready requires a clean committed worktree"
                )
            commits = int(
                _git(worktree, "rev-list", "--count", f"{lease['base_sha']}..HEAD")
            )
            base_is_ancestor = (
                _run(
                    [
                        "git",
                        "merge-base",
                        "--is-ancestor",
                        str(lease["base_sha"]),
                        "HEAD",
                    ],
                    cwd=worktree,
                    check=False,
                ).returncode
                == 0
            )
            if commits < 1 or not base_is_ancestor:
                raise SlotError(
                    f"wt{number} has no committed changes; use release for a no-change task"
                )
            lease["state"] = "READY_TO_ABSORB"
            lease["ready_head"] = _git(worktree, "rev-parse", "HEAD")
            self.inventory.save_lease(number, lease)
            return lease

    def heartbeat(self, number: int) -> dict[str, Any]:
        with self._slot_lock(number):
            lease = self._lease_for_command(
                number,
                states={"ACQUIRED", "PREPARING", "ACTIVE", "READY_TO_ABSORB"},
            )
            self.inventory.save_lease(number, lease)
            return lease

    def release(self, number: int) -> None:
        with self._slot_lock(number):
            lease = self._lease_for_command(
                number, states={"ACQUIRED", "ACTIVE", "QUARANTINED"}
            )
            worktree, _ = self._assert_worktree_identity(number)
            dirty = self._dirty(worktree)
            try:
                self._assert_paired_dependency(
                    number,
                    lease.get("public_dependency_sha"),
                    require_primary_match=False,
                )
            except SlotError as exc:
                self._quarantine(number, lease, str(exc))
                raise
            absorbed, why = self._is_absorbed(worktree, lease)
            if dirty or not absorbed:
                reason = (
                    "release refused: dirty files remain"
                    if dirty
                    else f"release refused: {why}"
                )
                self._quarantine(number, lease, reason)
                raise SlotError(f"wt{number} quarantined; {reason}")
            try:
                self._restore_paired_backend(number)
            except Exception as exc:
                self._quarantine(number, lease, f"counterpart restore failed: {exc}")
                raise
            self.inventory.lease_path(number).unlink()
            self._reconcile_backend(number)

    def _is_absorbed(self, worktree: Path, lease: dict[str, Any]) -> tuple[bool, str]:
        """Would freeing this slot lose work? Returns (safe_to_free, explanation).

        The decider is **containment in the integration ref** — the branch `absorb`
        fast-forwards, so work reachable from it is preserved no matter what happens to the
        slot. The lease's recorded `base_ref` is a HINT, not the authority: ordinary hygiene
        (merge a feature branch, delete it) deletes or supersedes it, and testing only
        against it strands a slot whose commits are safely in `main` — with no controller
        verb able to free it. That is the wt2 trap, 2026-08-14.

        Fail-closed: if neither reference resolves, the answer is "not safe".
        """
        integration = str(self.inventory.raw.get("integration_ref", "main"))
        for label, ref in ((f"integration ref {integration!r}", integration),
                           (f"recorded base {lease.get('base_ref')!r}",
                            str(lease.get("base_ref", "")))):
            if not ref:
                continue
            try:
                sha = self._primary_sha(ref)
            except SlotError:
                continue  # a deleted or unresolvable ref is not evidence of loss
            if (
                _run(
                    ["git", "merge-base", "--is-ancestor", "HEAD", sha],
                    cwd=worktree,
                    check=False,
                ).returncode
                == 0
            ):
                return True, f"contained in {label}"
        return False, (
            f"not contained in the integration ref {integration!r} nor in the lease's "
            f"recorded base {lease.get('base_ref')!r} (which may no longer resolve); "
            "merge or rescue the slot's commits before freeing it"
        )

    def _reconcile_backend(self, number: int) -> None:
        """Align a slot's heavy backend with what its (now-updated) lease implies.

        Call AFTER the lease file is gone: `backend_expected` reads the lease, so a
        reconcile that runs first would still see the slot as leased.

        Under `backend_policy: "leased"` nothing else ever stops a backend, and a warm slot
        is not cheap — one holds `lake serve` + `lean --server` + `lean --worker`, measured
        at ~4.4 GB, for the lifetime of the supervisor. Under `"default"` this is a no-op.

        Reclaiming memory must never fail an exit path that has already succeeded, so a
        supervisor error here is reported and swallowed rather than raised: the lease is
        released either way, and a stray backend is a resource cost, not a correctness one.
        """
        if os.environ.get("LEAN_SLOT_SKIP_SUPERVISOR"):
            return
        from .supervisor import Supervisor

        try:
            if not self.inventory.backend_expected(number):
                Supervisor(self.inventory).stop_backend(number)
        except (SlotError, OSError) as exc:  # pragma: no cover - defensive
            print(
                f"slotctl: wt{number} released, but its backend could not be stopped "
                f"({exc}); run `slotctl supervisor start` to reconcile",
                file=sys.stderr,
            )

    def _restore_paired_backend(self, number: int) -> None:
        paired = self.inventory.paired_inventory()
        if paired is None or os.environ.get("LEAN_SLOT_SKIP_SUPERVISOR"):
            return
        from .supervisor import Supervisor

        Supervisor(self.inventory).restore_counterpart(number, Supervisor(paired))

    def reclaim(self, number: int, *, confirm_owner_gone: bool = False) -> None:
        with self._slot_lock(number):
            lease = self.inventory.lease(number)
            assert lease is not None
            if lease.get("repo_role") != self.inventory.repo_role:
                raise SlotError(
                    f"repository-role mismatch for stale reclaim of wt{number}: "
                    f"{lease.get('repo_role')} != {self.inventory.repo_role}"
                )
            if lease.get("worktree") != str(self.inventory.worktree(number)):
                raise SlotError(f"worktree mismatch for stale reclaim of wt{number}")
            heartbeat = datetime.strptime(
                str(lease["heartbeat_at"]), "%Y-%m-%dT%H:%M:%SZ"
            ).replace(tzinfo=timezone.utc)
            age = (datetime.now(timezone.utc) - heartbeat).total_seconds()
            timeout = int(self.inventory.raw.get("lease_timeout_seconds", 900))
            if age < timeout:
                raise SlotError(
                    f"wt{number} heartbeat is only {int(age)}s old; stale threshold is {timeout}s"
                )
            if lease.get("owner_kind") == "process":
                if process_matches(
                    int(lease.get("owner_pid", 0)), lease.get("owner_signature")
                ):
                    raise SlotError(f"wt{number} owner process is still alive")
            elif lease.get("owner_kind") == "session" and not confirm_owner_gone:
                raise SlotError(
                    f"wt{number} has a session owner; rerun with --confirm-owner-gone only after "
                    "verifying that Codex session has ended"
                )
            elif lease.get("owner_kind") not in {"process", "session"}:
                raise SlotError(f"wt{number} has an invalid owner identity")
            worktree, _ = self._assert_worktree_identity(number)
            dirty = self._dirty(worktree)
            try:
                self._assert_paired_dependency(
                    number,
                    lease.get("public_dependency_sha"),
                    require_primary_match=False,
                )
            except SlotError as exc:
                self._quarantine(number, lease, str(exc))
                raise
            absorbed, why = self._is_absorbed(worktree, lease)
            if dirty or not absorbed:
                reason = (
                    "stale owner, but dirty files require recovery"
                    if dirty
                    else f"stale owner, and {why}"
                )
                self._quarantine(number, lease, reason)
                raise SlotError(f"wt{number} quarantined; {reason}")
            try:
                self._restore_paired_backend(number)
            except Exception as exc:
                self._quarantine(number, lease, f"counterpart restore failed: {exc}")
                raise
            self.inventory.lease_path(number).unlink()
            self._reconcile_backend(number)

    def absorb(self, number: int) -> dict[str, Any]:
        integration = self.inventory.state_root / "locks" / "integration.lock"
        with directory_lock(integration, purpose="serialized slot integration"):
            with self._slot_lock(number):
                lease = self._lease_for_command(number, states={"READY_TO_ABSORB"})
                worktree, _ = self._assert_worktree_identity(number)
                if self._dirty(worktree):
                    self._quarantine(
                        number, lease, "worktree became dirty before integration"
                    )
                    raise SlotError(f"wt{number} quarantined; worktree became dirty")
                try:
                    self._assert_paired_dependency(
                        number, lease.get("public_dependency_sha")
                    )
                except SlotError as exc:
                    self._quarantine(number, lease, str(exc))
                    raise
                current_ready_head = _git(worktree, "rev-parse", "HEAD")
                if current_ready_head != lease.get("ready_head"):
                    self._quarantine(
                        number, lease, "slot HEAD changed after ready audit"
                    )
                    raise SlotError(
                        f"wt{number} quarantined; slot HEAD changed after ready"
                    )
                primary_branch = self._branch(self.repo)
                if primary_branch != lease["base_ref"]:
                    raise SlotError(
                        f"primary checkout is on {primary_branch!r}; switch to "
                        f"{lease['base_ref']!r} before absorb"
                    )
                lease["state"] = "INTEGRATING"
                self.inventory.save_lease(number, lease)
                current_base = self._primary_sha(str(lease["base_ref"]))
                if (
                    not _run(
                        ["git", "merge-base", "--is-ancestor", current_base, "HEAD"],
                        cwd=worktree,
                        check=False,
                    ).returncode
                    == 0
                ):
                    result = _run(
                        ["git", "rebase", current_base], cwd=worktree, check=False
                    )
                    if result.returncode:
                        _run(["git", "rebase", "--abort"], cwd=worktree, check=False)
                        self._quarantine(
                            number, lease, "rebase conflict during absorption"
                        )
                        raise SlotError(f"wt{number} quarantined; rebase conflict")
                slot_head = _git(worktree, "rev-parse", "HEAD")
                try:
                    _git(self.repo, "merge", "--ff-only", slot_head)
                except SlotError as exc:
                    self._quarantine(
                        number, lease, f"fast-forward integration failed: {exc}"
                    )
                    raise
                lease["state"] = "REBUILDING"
                lease["integrated_head"] = slot_head
                self.inventory.save_lease(number, lease)
                try:
                    epoch = self.build()
                    lease["state"] = "REWARMING"
                    self.inventory.save_lease(number, lease)
                    from .supervisor import Supervisor

                    supervisor = Supervisor(self.inventory)
                    if os.environ.get("LEAN_SLOT_SKIP_SUPERVISOR"):
                        self._replace_lake(number)
                    else:
                        with supervisor.paused_backend(number):
                            self._replace_lake(number)
                except Exception as exc:
                    self._quarantine(
                        number, lease, f"post-integration build/rewarm failed: {exc}"
                    )
                    raise
                try:
                    self._restore_paired_backend(number)
                except Exception as exc:
                    self._quarantine(
                        number, lease, f"counterpart restore failed: {exc}"
                    )
                    raise
                self.inventory.lease_path(number).unlink()
                self._reconcile_backend(number)
                return {"integrated_head": slot_head, "epoch": epoch}

    def status(self) -> dict[str, Any]:
        slots: list[dict[str, Any]] = []
        for number in (1, 2, 3):
            lease = self.inventory.lease(number, required=False)
            entry: dict[str, Any] = {
                "slot": number,
                "repo_role": self.inventory.repo_role,
                "worktree": str(self.inventory.worktree(number)),
                "lease": lease,
            }
            try:
                worktree, slot = self._assert_worktree_identity(number)
                entry.update(
                    {
                        "branch": slot["branch"],
                        "dirty": self._dirty(worktree),
                        "head": _git(worktree, "rev-parse", "HEAD"),
                    }
                )
            except SlotError as exc:
                entry["error"] = str(exc)
            slots.append(entry)
        return {
            "schema_version": SCHEMA_VERSION,
            "repo_role": self.inventory.repo_role,
            "state_root": str(self.inventory.state_root),
            "slots": slots,
        }

    def source_digest(self) -> str:
        paths = [
            self.inventory.source,
            self.repo / ".codex" / "config.template.toml",
            self.repo / ".codex" / "hooks" / "pre_tool_use_policy.py",
            *(self.repo / ".codex" / "agents").glob("*.toml"),
        ]
        digest = hashlib.sha256()
        for path in sorted(paths):
            digest.update(str(path.relative_to(self.repo)).encode())
            digest.update(path.read_bytes())
        return digest.hexdigest()

    def rendered_config(self) -> str:
        template = (self.repo / ".codex" / "config.template.toml").read_text(
            encoding="utf-8"
        )
        bearer_line = (
            'bearer_token_env_var = "LEAN_SLOT_CODEX_TOKEN"'
            if self.inventory.client_auth_mode == "bearer"
            else ""
        )
        agent_dir = self.repo / ".codex" / "agents"
        if self.inventory.client_auth_mode == "bearer":
            agent_dir = self.repo / ".codex" / "generated" / "agents"
        return (
            template.replace("{{SOURCE_DIGEST}}", self.source_digest())
            .replace("{{REPO_ROOT}}", str(self.repo))
            .replace("{{AGENT_CONFIG_DIR}}", str(agent_dir))
            .replace("{{MCP_CLIENT_AUTH}}", bearer_line)
        )

    def rendered_bearer_agent_configs(self) -> dict[Path, str]:
        """Render secure-mode agent profiles without dirtying versioned bases."""

        if self.inventory.client_auth_mode != "bearer":
            return {}
        rendered: dict[Path, str] = {}
        destination_root = self.repo / ".codex" / "generated" / "agents"
        for source in sorted((self.repo / ".codex" / "agents").glob("*.toml")):
            lines: list[str] = ["# GENERATED by scripts/slotctl.py config render."]
            for line in source.read_text(encoding="utf-8").splitlines():
                lines.append(line)
                if line.startswith("url = "):
                    lines.append('bearer_token_env_var = "LEAN_SLOT_CODEX_TOKEN"')
            rendered[destination_root / source.name] = "\n".join(lines) + "\n"
        return rendered

    def render_config(
        self,
        *,
        scope: str,
        force: bool = False,
        rotate_token: bool = False,
    ) -> list[Path]:
        if scope not in {"repo", "workspace", "both"}:
            raise SlotError("config scope must be repo, workspace, or both")
        if scope in {"workspace", "both"} and not bool(
            self.inventory.raw.get("config", {}).get("manage_workspace", True)
        ):
            raise SlotError(
                "this repository overlay does not manage workspace Codex configuration; "
                "render the repo scope and launch Codex from that repository"
            )
        if rotate_token and self.inventory.client_auth_mode != "bearer":
            raise SlotError(
                "token rotation is available only in bearer client-auth mode"
            )
        if rotate_token:
            active = [n for n in (1, 2, 3) if self.inventory.lease(n, required=False)]
            if active:
                raise SlotError(
                    f"cannot rotate Codex token while slots are leased: {active}"
                )
        content = self.rendered_config()
        destinations: list[Path] = []
        if scope in {"repo", "both"}:
            destinations.append(self.repo / ".codex" / "config.toml")
        if scope in {"workspace", "both"}:
            destinations.append(
                self.inventory.workspace_root / ".codex" / "config.toml"
            )
        for destination in destinations:
            if (
                destination.exists()
                and destination.read_text(encoding="utf-8") != content
            ):
                first = destination.read_text(encoding="utf-8").splitlines()[:3]
                generated = any(
                    "GENERATED by scripts/slotctl.py" in line for line in first
                )
                if not (force and generated):
                    raise SlotError(
                        f"refusing to overwrite drifted/local config {destination}; "
                        "inspect it and pass --force only for a generated file"
                    )
        bearer_agents = self.rendered_bearer_agent_configs()
        if rotate_token:
            self.inventory.token("codex", rotate=True)
        for destination, agent_content in bearer_agents.items():
            atomic_write(destination, agent_content)
        for destination in destinations:
            atomic_write(destination, content)
        return destinations

    def claude_mcp_path(self) -> Path:
        """Workspace Claude MCP configuration named by the versioned inventory (spec P4-1)."""
        relative = str(
            self.inventory.raw.get("config", {}).get("claude_mcp", ".mcp.json")
        )
        if Path(relative).is_absolute():
            raise SlotError("config.claude_mcp must be a workspace-relative path")
        return self.inventory.workspace_root / relative

    def render_claude_config(self, *, rollback: bool = False) -> list[Path]:
        from . import claude_config

        return [
            claude_config.render(
                self.inventory, self.claude_mcp_path(), rollback=rollback
            )
        ]

    def session_environment(self, *, client: str, rotate_token: bool = False) -> str:
        if rotate_token and self.inventory.client_auth_mode != "bearer":
            raise SlotError(
                "token rotation is available only in bearer client-auth mode"
            )
        if rotate_token:
            active = [n for n in (1, 2, 3) if self.inventory.lease(n, required=False)]
            if active:
                raise SlotError(
                    f"cannot rotate {client} token while slots are leased: {active}"
                )
        exports = [
            f"export LEAN_SLOT_STATE_DIR={shlex.quote(str(self.inventory.state_root))}"
        ]
        if self.inventory.client_auth_mode == "bearer":
            token = self.inventory.token(client, rotate=rotate_token)
            variable = f"LEAN_SLOT_{client.upper().replace('-', '_')}_TOKEN"
            exports.insert(0, f"export {variable}={shlex.quote(token)}")
        return "\n".join(exports)

    def doctor(self) -> dict[str, Any]:
        checks: list[dict[str, Any]] = []

        def record(name: str, ok: bool, detail: str) -> None:
            checks.append({"name": name, "ok": ok, "detail": detail})

        for number in (1, 2, 3):
            try:
                worktree, _ = self._assert_worktree_identity(number)
                dirty = self._dirty(worktree)
                record(f"wt{number}.identity", True, str(worktree))
                record(
                    f"wt{number}.clean",
                    not dirty,
                    "clean" if not dirty else "; ".join(dirty[:8]),
                )
                primary_head = _git(self.repo, "rev-parse", "HEAD")
                ahead = int(
                    _git(worktree, "rev-list", "--count", f"{primary_head}..HEAD")
                )
                contained = (
                    _run(
                        ["git", "merge-base", "--is-ancestor", "HEAD", primary_head],
                        cwd=worktree,
                        check=False,
                    ).returncode
                    == 0
                )
                record(
                    f"wt{number}.integrated",
                    ahead == 0 and contained,
                    "contained in primary HEAD"
                    if ahead == 0 and contained
                    else f"{ahead} unabsorbed commit(s) or divergent ancestry",
                )
            except SlotError as exc:
                record(f"wt{number}.identity", False, str(exc))
            try:
                lease = self.inventory.lease(number, required=False)
                lease_ok = lease is None or lease.get("state") != "QUARANTINED"
                record(
                    f"wt{number}.lease",
                    lease_ok,
                    "FREE"
                    if lease is None
                    else f"{lease.get('repo_role')}:{lease.get('state')}",
                )
            except SlotError as exc:
                record(f"wt{number}.lease", False, str(exc))
        try:
            auth_mode = self.inventory.client_auth_mode
            record(
                "client_auth",
                True,
                f"{auth_mode} on {self.inventory.raw['server']['host']}",
            )
        except SlotError as exc:
            record("client_auth", False, str(exc))
        primary_dirty = self._dirty(self.repo)
        record(
            "primary.clean",
            not primary_dirty,
            "clean" if not primary_dirty else "; ".join(primary_dirty[:8]),
        )
        try:
            epoch = self._matching_epoch(_git(self.repo, "rev-parse", "HEAD"))
            record("build_epoch", True, str(epoch.get("epoch_id")))
        except SlotError as exc:
            record("build_epoch", False, str(exc))
        expected = self.rendered_config()
        for label, path in (
            ("repo", self.repo / ".codex" / "config.toml"),
            ("workspace", self.inventory.workspace_root / ".codex" / "config.toml"),
        ):
            if label == "workspace" and not bool(
                self.inventory.raw.get("config", {}).get("manage_workspace", True)
            ):
                record(f"config.{label}", True, "not managed by this overlay")
            else:
                ok = path.exists() and path.read_text(encoding="utf-8") == expected
                record(
                    f"config.{label}",
                    ok,
                    "current" if ok else f"missing or drifted: {path}",
                )
        from . import host_limits

        for limit_name, limit_ok, limit_detail in host_limits.evaluate(self.inventory):
            record(limit_name, limit_ok, limit_detail)
        from . import claude_config

        claude_path = self.claude_mcp_path()
        if not claude_path.exists():
            record("config.claude", True, f"not managed here: {claude_path} absent")
        else:
            state, detail = claude_config.block_state(
                read_json(claude_path), self.inventory
            )
            # `not activated` is OK on purpose: Phase 4 is reversible, and a rolled-back
            # workstation must not report a broken control plane (spec P4-3).
            record(
                "config.claude",
                state in {"current", "not activated"},
                f"{state}: {detail}",
            )
        from .supervisor import Supervisor

        supervisor = Supervisor(self.inventory).status()
        running_backends = int(supervisor["global_running_backends"])
        record(
            "heavy_backend_limit",
            running_backends <= int(self.inventory.raw["max_active_slots"]),
            f"{running_backends}/3 running",
        )
        for item in supervisor["slots"]:
            expected_backend = self.inventory.backend_expected(int(item["slot"]))
            record(
                f"wt{item['slot']}.endpoint",
                item["proxy_running"] and item["backend_running"] == expected_backend,
                f"proxy={item['proxy_running']} backend={item['backend_running']} "
                f"expected_backend={expected_backend}",
            )
        paired = self.inventory.paired_inventory()
        if paired is not None:
            for number in (1, 2, 3):
                try:
                    dependency_sha = self._assert_paired_dependency(number)
                    record(
                        f"wt{number}.paired_dependency",
                        True,
                        str(dependency_sha),
                    )
                except SlotError as exc:
                    record(f"wt{number}.paired_dependency", False, str(exc))
        relative_paths = (
            all(
                not Path(str(slot["worktree"])).is_absolute()
                for slot in self.inventory.raw["slots"].values()
            )
            and not Path(str(self.inventory.raw["repo_root"])).is_absolute()
        )
        record(
            "public_boundary",
            self.inventory.repo_role != "public" or relative_paths,
            "versioned public inventory uses relative repository/worktree paths"
            if relative_paths
            else "public inventory contains an absolute repository/worktree path",
        )
        return {
            "schema_version": SCHEMA_VERSION,
            "ok": all(c["ok"] for c in checks),
            "checks": checks,
        }
