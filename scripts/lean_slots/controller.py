"""Fail-closed lease, build-epoch, and integration controller for ADR-008."""
from __future__ import annotations

import hashlib
import json
import os
import shutil
import subprocess
import tempfile
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

    def _branch(self, path: Path) -> str:
        branch = _git(path, "branch", "--show-current")
        if not branch:
            raise SlotError(f"detached HEAD is not permitted: {path}")
        return branch

    def _dirty(self, path: Path) -> list[str]:
        return [line for line in _git(path, "status", "--porcelain=v1").splitlines() if line]

    def _assert_worktree_identity(self, number: int) -> tuple[Path, dict[str, Any]]:
        slot = self.inventory.slot(number)
        worktree = self.inventory.worktree(number)
        if not worktree.is_dir():
            raise SlotError(f"configured worktree is missing: {worktree}")
        top = Path(_git(worktree, "rev-parse", "--show-toplevel")).resolve()
        if top != worktree:
            raise SlotError(f"worktree root mismatch for wt{number}: {top} != {worktree}")
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
        session_id = os.environ.get("CODEX_THREAD_ID")
        if session_id:
            return {
                "owner_kind": "session",
                "owner_session_hash": hashlib.sha256(session_id.encode()).hexdigest(),
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
            self.inventory.save_lease(number, lease)

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
            lease: dict[str, Any] = {
                "schema_version": SCHEMA_VERSION,
                "slot": number,
                "repo_role": self.inventory.repo_role,
                "client": client,
                "token_hash": token_hash(self.inventory.token(client)),
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
            dirty = self._dirty(worktree)
            if dirty:
                reason = f"worktree is dirty: {', '.join(dirty[:8])}"
                self._quarantine(number, lease, reason, create=True)
                raise SlotError(f"wt{number} quarantined; {reason}")
            ahead = int(_git(worktree, "rev-list", "--count", f"{base_sha}..HEAD"))
            ancestor = _run(
                ["git", "merge-base", "--is-ancestor", "HEAD", base_sha],
                cwd=worktree,
                check=False,
            ).returncode == 0
            if ahead or not ancestor:
                reason = (
                    f"worktree has {ahead} unabsorbed commit(s) or divergent ancestry "
                    f"relative to {base_ref}"
                )
                self._quarantine(number, lease, reason, create=True)
                raise SlotError(f"wt{number} quarantined; {reason}")
            exclusive_json(self.inventory.lease_path(number), lease)
            return lease

    def _fingerprint(self, commit_sha: str | None = None) -> dict[str, Any]:
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
        fingerprint["digest"] = canonical_digest(fingerprint)
        return fingerprint

    def _matching_epoch(self, commit_sha: str) -> dict[str, Any]:
        path = self.inventory.epoch_path()
        epoch = read_json(path)
        expected = self._fingerprint(commit_sha)
        if epoch.get("fingerprint") != expected:
            raise SlotError(
                "no successful-build epoch matches the acquired commit and dependency fingerprint; "
                "run slotctl build from the primary checkout"
            )
        return epoch

    def build(self) -> dict[str, Any]:
        top = Path(_git(self.repo, "rev-parse", "--show-toplevel")).resolve()
        if top != self.repo:
            raise SlotError("authoritative build must run from the configured primary checkout")
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
                shutil.copytree(source, temporary, symlinks=True)
            if backup.exists():
                raise SlotError(f"stale Lake backup requires manual inspection: {backup}")
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
                raise SlotError(f"wt{number} quarantined; worktree became dirty before prepare")
            current_base = self._primary_sha(str(lease["base_ref"]))
            if current_base != lease["base_sha"]:
                self._quarantine(number, lease, "base ref advanced after acquisition")
                raise SlotError(f"wt{number} quarantined; base ref advanced after acquisition")
            self._matching_epoch(current_base)
            lease["state"] = "PREPARING"
            self.inventory.save_lease(number, lease)
            from .supervisor import Supervisor

            supervisor = Supervisor(self.inventory)
            if not os.environ.get("LEAN_SLOT_SKIP_SUPERVISOR"):
                supervisor.assert_healthy(number)
                supervisor.stop_backend(number)
            try:
                _git(worktree, "reset", "--hard", current_base)
                self._replace_lake(number)
            except Exception as exc:
                self._quarantine(number, lease, f"prepare failed: {exc}")
                if not os.environ.get("LEAN_SLOT_SKIP_SUPERVISOR"):
                    supervisor.start_backend(number)
                raise
            if not os.environ.get("LEAN_SLOT_SKIP_SUPERVISOR"):
                supervisor.start_backend(number)
                supervisor.assert_healthy(number)
            lease["state"] = "ACTIVE"
            lease["prepared_epoch"] = read_json(self.inventory.epoch_path())["epoch_id"]
            lease["prepared_at"] = now_iso()
            self.inventory.save_lease(number, lease)
            return lease

    def ready(self, number: int) -> dict[str, Any]:
        with self._slot_lock(number):
            lease = self._lease_for_command(number, states={"ACTIVE"})
            worktree, _ = self._assert_worktree_identity(number)
            dirty = self._dirty(worktree)
            if dirty:
                self._quarantine(number, lease, f"ready requires a clean commit: {dirty[:8]}")
                raise SlotError(f"wt{number} quarantined; ready requires a clean committed worktree")
            commits = int(_git(worktree, "rev-list", "--count", f"{lease['base_sha']}..HEAD"))
            if commits < 1:
                raise SlotError(f"wt{number} has no committed changes; use release for a no-change task")
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
            base_sha = self._primary_sha(str(lease["base_ref"]))
            result = _run(
                ["git", "merge-base", "--is-ancestor", "HEAD", base_sha],
                cwd=worktree,
                check=False,
            )
            if dirty or result.returncode:
                reason = "release refused: dirty files or unabsorbed commits remain"
                self._quarantine(number, lease, reason)
                raise SlotError(f"wt{number} quarantined; {reason}")
            self.inventory.lease_path(number).unlink()

    def reclaim(self, number: int, *, confirm_owner_gone: bool = False) -> None:
        with self._slot_lock(number):
            lease = self.inventory.lease(number)
            assert lease is not None
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
                if process_matches(int(lease.get("owner_pid", 0)), lease.get("owner_signature")):
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
            base_sha = self._primary_sha(str(lease["base_ref"]))
            absorbed = _run(
                ["git", "merge-base", "--is-ancestor", "HEAD", base_sha],
                cwd=worktree,
                check=False,
            ).returncode == 0
            if dirty or not absorbed:
                reason = "stale owner, but dirty files or unabsorbed commits require recovery"
                self._quarantine(number, lease, reason)
                raise SlotError(f"wt{number} quarantined; {reason}")
            self.inventory.lease_path(number).unlink()

    def absorb(self, number: int) -> dict[str, Any]:
        integration = self.inventory.state_root / "locks" / "integration.lock"
        with directory_lock(integration, purpose="serialized slot integration"):
            with self._slot_lock(number):
                lease = self._lease_for_command(number, states={"READY_TO_ABSORB"})
                worktree, _ = self._assert_worktree_identity(number)
                if self._dirty(worktree):
                    self._quarantine(number, lease, "worktree became dirty before integration")
                    raise SlotError(f"wt{number} quarantined; worktree became dirty")
                primary_branch = self._branch(self.repo)
                if primary_branch != lease["base_ref"]:
                    raise SlotError(
                        f"primary checkout is on {primary_branch!r}; switch to "
                        f"{lease['base_ref']!r} before absorb"
                    )
                lease["state"] = "INTEGRATING"
                self.inventory.save_lease(number, lease)
                current_base = self._primary_sha(str(lease["base_ref"]))
                if not _run(
                    ["git", "merge-base", "--is-ancestor", current_base, "HEAD"],
                    cwd=worktree,
                    check=False,
                ).returncode == 0:
                    result = _run(["git", "rebase", current_base], cwd=worktree, check=False)
                    if result.returncode:
                        _run(["git", "rebase", "--abort"], cwd=worktree, check=False)
                        self._quarantine(number, lease, "rebase conflict during absorption")
                        raise SlotError(f"wt{number} quarantined; rebase conflict")
                slot_head = _git(worktree, "rev-parse", "HEAD")
                try:
                    _git(self.repo, "merge", "--ff-only", slot_head)
                except SlotError as exc:
                    self._quarantine(number, lease, f"fast-forward integration failed: {exc}")
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
                    if not os.environ.get("LEAN_SLOT_SKIP_SUPERVISOR"):
                        supervisor.stop_backend(number)
                    self._replace_lake(number)
                    if not os.environ.get("LEAN_SLOT_SKIP_SUPERVISOR"):
                        supervisor.start_backend(number)
                        supervisor.assert_healthy(number)
                except Exception as exc:
                    self._quarantine(number, lease, f"post-integration build/rewarm failed: {exc}")
                    raise
                self.inventory.lease_path(number).unlink()
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
        template = (self.repo / ".codex" / "config.template.toml").read_text(encoding="utf-8")
        return (
            template.replace("{{SOURCE_DIGEST}}", self.source_digest())
            .replace("{{REPO_ROOT}}", str(self.repo))
        )

    def render_config(
        self,
        *,
        scope: str,
        force: bool = False,
        rotate_token: bool = False,
    ) -> list[Path]:
        if scope not in {"repo", "workspace", "both"}:
            raise SlotError("config scope must be repo, workspace, or both")
        if rotate_token:
            active = [n for n in (1, 2, 3) if self.inventory.lease(n, required=False)]
            if active:
                raise SlotError(f"cannot rotate Codex token while slots are leased: {active}")
        if rotate_token:
            self.inventory.token("codex", rotate=True)
        content = self.rendered_config()
        destinations: list[Path] = []
        if scope in {"repo", "both"}:
            destinations.append(self.repo / ".codex" / "config.toml")
        if scope in {"workspace", "both"}:
            destinations.append(self.inventory.workspace_root / ".codex" / "config.toml")
        for destination in destinations:
            if destination.exists() and destination.read_text(encoding="utf-8") != content:
                first = destination.read_text(encoding="utf-8").splitlines()[:3]
                generated = any("GENERATED by scripts/slotctl.py" in line for line in first)
                if not (force and generated):
                    raise SlotError(
                        f"refusing to overwrite drifted/local config {destination}; "
                        "inspect it and pass --force only for a generated file"
                    )
            atomic_write(destination, content)
        return destinations

    def session_environment(self, *, client: str, rotate_token: bool = False) -> str:
        if rotate_token:
            active = [n for n in (1, 2, 3) if self.inventory.lease(n, required=False)]
            if active:
                raise SlotError(f"cannot rotate {client} token while slots are leased: {active}")
        token = self.inventory.token(client, rotate=rotate_token)
        variable = f"LEAN_SLOT_{client.upper().replace('-', '_')}_TOKEN"
        return f"export {variable}={token}"

    def doctor(self) -> dict[str, Any]:
        checks: list[dict[str, Any]] = []

        def record(name: str, ok: bool, detail: str) -> None:
            checks.append({"name": name, "ok": ok, "detail": detail})

        for number in (1, 2, 3):
            try:
                worktree, _ = self._assert_worktree_identity(number)
                dirty = self._dirty(worktree)
                record(f"wt{number}.identity", True, str(worktree))
                record(f"wt{number}.clean", not dirty, "clean" if not dirty else "; ".join(dirty[:8]))
            except SlotError as exc:
                record(f"wt{number}.identity", False, str(exc))
            try:
                lease = self.inventory.lease(number, required=False)
                record(
                    f"wt{number}.lease",
                    lease is None or lease.get("repo_role") == self.inventory.repo_role,
                    "FREE" if lease is None else str(lease.get("state")),
                )
            except SlotError as exc:
                record(f"wt{number}.lease", False, str(exc))
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
            ok = path.exists() and path.read_text(encoding="utf-8") == expected
            record(f"config.{label}", ok, "current" if ok else f"missing or drifted: {path}")
        from .supervisor import Supervisor

        supervisor = Supervisor(self.inventory).status()
        running_backends = sum(1 for item in supervisor["slots"] if item["backend_running"])
        record(
            "heavy_backend_limit",
            running_backends <= int(self.inventory.raw["max_active_slots"]),
            f"{running_backends}/3 running",
        )
        for item in supervisor["slots"]:
            record(
                f"wt{item['slot']}.endpoint",
                item["proxy_running"] and item["backend_running"],
                f"proxy={item['proxy_running']} backend={item['backend_running']}",
            )
        relative_paths = all(
            not Path(str(slot["worktree"])).is_absolute()
            for slot in self.inventory.raw["slots"].values()
        ) and not Path(str(self.inventory.raw["repo_root"])).is_absolute()
        record(
            "public_boundary",
            self.inventory.repo_role != "public" or relative_paths,
            "versioned public inventory uses relative repository/worktree paths"
            if relative_paths
            else "public inventory contains an absolute repository/worktree path",
        )
        return {"schema_version": SCHEMA_VERSION, "ok": all(c["ok"] for c in checks), "checks": checks}
