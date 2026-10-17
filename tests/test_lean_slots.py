"""Acceptance-focused tests for the ADR-008 shared Lean slot controller."""

from __future__ import annotations

import json
import os
import subprocess
import signal
from types import SimpleNamespace
from pathlib import Path

import pytest

from scripts.lean_slots.controller import Controller
from scripts.lean_slots.proxy import LeaseGate
from scripts.lean_slots.state import Inventory, SlotError
from scripts.lean_slots.state import atomic_json, process_start_signature
from scripts.lean_slots.supervisor import Supervisor


@pytest.mark.parametrize("damage", ["none","generation","node","pid","birth","argv","parent","exited","stale-only","deadline"])
def test_fixture_recursive_startup_requires_exact_fresh_ack(tmp_path,monkeypatch,isolated_process_observations,damage):
    from tests.fixtures import lean_checkpoint_native_peer as peer
    host=isolated_process_observations;generation='a'*32;argv=['python','-B','owned-peer','--fixture-child','middle']
    actual={'pid':900101,'ppid':900100,'birth':'Sun Oct 11 00:00:00 2026','start_ticks':'421','argv':argv}
    value={'generation':generation,'node':'middle','identity':dict(actual),'children':[]}
    value['identity']['argv']=list(argv)
    if damage=='generation':value['generation']='b'*32
    elif damage=='node':value['node']='leaf'
    elif damage in {'pid','parent'}:value['identity']['pid' if damage=='pid' else 'ppid']+=1
    elif damage=='birth':value['identity']['birth']='Sun Oct 11 00:00:01 2026'
    elif damage=='argv':value['identity']['argv']=['python','unrelated']
    path=tmp_path/f'startup-{generation}-middle.json'
    if damage=='stale-only':path=tmp_path/f"startup-{'b'*32}-middle.json"
    peer.publish_startup(path,value,1.0)
    # Append-only historical rows are deliberately present but confer no readiness.
    peer.append_record(tmp_path/'native-nodes.jsonl',value)
    monkeypatch.setattr(peer,'native_identity',lambda pid,deadline:dict(actual))
    child=SimpleNamespace(pid=actual['pid'],poll=lambda:0 if damage=='exited' else None)
    if damage=='deadline':host.clock=1.0
    if damage=='none':
        assert peer.wait_startup(tmp_path,'middle',generation,child,argv,actual['ppid'],1.0,lambda:False)==value
    else:
        with pytest.raises(RuntimeError,match='generation|node|PID|birth|argv|parent|exited|deadline'):
            peer.wait_startup(tmp_path,'middle',generation,child,argv,actual['ppid'],1.0,lambda:False)
    assert not host.signals and not host.launches


@pytest.mark.parametrize("damage", ["none","generation","parent","birth","argv","pid"])
def test_fixture_recursive_leaf_reobserves_actual_owned_identity(tmp_path,monkeypatch,damage):
    from tests.fixtures import lean_checkpoint_native_peer as peer
    generation='c'*32;deadline=3.0
    args=SimpleNamespace(lean_project_path=tmp_path,control_dir=tmp_path,fixture_leaf_delay=0.0,fixture_middle_delay=0.0,fixture_startup_timeout=5.0,fixture_late_child=False)
    actual={'pid':900103,'ppid':900102,'birth':'Sun Oct 11 00:00:00 2026','start_ticks':'422','argv':peer.child_argv(args,'leaf',generation,deadline)}
    value={'generation':generation,'node':'leaf','identity':dict(actual)}
    if damage=='generation':value['generation']='d'*32
    elif damage=='parent':value['identity']['ppid']=900199
    elif damage=='birth':value['identity']['birth']='Sun Oct 11 00:00:01 2026'
    elif damage=='argv':value['identity']['argv']=['different','full','argv']
    elif damage=='pid':value['identity']['pid']=None
    monkeypatch.setattr(peer,'native_identity',lambda pid,deadline:dict(actual))
    if damage=='none':peer.validate_leaf(value,args,generation,actual['ppid'],deadline)
    else:
        with pytest.raises(RuntimeError,match='acknowledgment|identity|PID'):
            peer.validate_leaf(value,args,generation,actual['ppid'],deadline)


def test_fixture_startup_ack_is_exclusive_and_rejects_substitution(tmp_path):
    from tests.fixtures import lean_checkpoint_native_peer as peer
    path=tmp_path/'startup-owned.json';value={'fresh':'actual first bytes'}
    peer.publish_startup(path,value,2.0);before=path.read_bytes()
    with pytest.raises(FileExistsError):peer.publish_startup(path,{'replaced':True},2.0)
    assert path.read_bytes()==before and peer.read_startup(path,2.0)==value
    link=tmp_path/'startup-link.json';link.symlink_to(path)
    with pytest.raises(OSError):peer.read_startup(link,2.0)
    path.chmod(0o644)
    with pytest.raises(RuntimeError,match='untrusted'):peer.read_startup(path,2.0)


@pytest.fixture(autouse=True)
def isolated_process_observations(monkeypatch, tmp_path):
    """Keep this policy suite off the actual host; all runtime state is tmp."""
    monkeypatch.setenv("LEAN_SLOT_STATE_DIR", str(tmp_path / "isolated-observation-runtime"))
    from tests.test_lean_lifecycle_observation import Host
    original = subprocess.Popen
    host = Host(monkeypatch)
    host.real_popen = original
    return host


def run(cwd: Path, *command: str) -> str:
    return subprocess.run(
        list(command), cwd=cwd, check=True, capture_output=True, text=True
    ).stdout.strip()


def _fixture_runtime_launcher(repo: Path) -> None:
    """A real transparent launcher selecting the package this suite imported."""
    from scripts.lean_slots import supervisor as loaded
    scripts = Path(loaded.__file__).resolve().parent.parent
    directory = repo / "scripts"
    directory.mkdir(exist_ok=True)
    (directory / "slotctl.py").write_text(
        "import sys\nfrom pathlib import Path\n"
        f"SELECTED_SCRIPTS = Path({str(scripts)!r})\n"
        "sys.path.insert(0, str(SELECTED_SCRIPTS))\n"
        "from lean_slots.cli import main\n"
        'if __name__ == "__main__":\n    raise SystemExit(main())\n'
    )


@pytest.fixture()
def slot_repo(
    tmp_path: Path, monkeypatch: pytest.MonkeyPatch
) -> tuple[Controller, Path, list[Path]]:
    repo = tmp_path / "primary"
    repo.mkdir()
    run(repo, "git", "init", "-b", "main")
    run(repo, "git", "config", "user.name", "Slot Test")
    run(repo, "git", "config", "user.email", "slot@example.invalid")
    (repo / "lean").mkdir()
    (repo / "lean" / "lean-toolchain").write_text("leanprover/lean4:v4.test\n")
    (repo / "lean" / "lakefile.toml").write_text("name = 'Test'\n")
    (repo / "lean" / "lake-manifest.json").write_text("{}\n")
    (repo / "README.md").write_text("slot fixture\n")
    (repo / ".gitignore").write_text("lean/.lake/\n")
    run(repo, "git", "add", ".")
    run(repo, "git", "commit", "-m", "initial")
    worktrees = []
    for number in (1, 2, 3):
        worktree = tmp_path / f"wt{number}"
        run(
            repo,
            "git",
            "worktree",
            "add",
            "-b",
            f"worktree-wt{number}",
            str(worktree),
            "main",
        )
        worktrees.append(worktree)
    lake_build = repo / "lean" / ".lake" / "build"
    lake_build.mkdir(parents=True)
    (lake_build / "artifact").write_text("built\n")
    (repo / "config").mkdir()
    inventory = {
        "schema_version": 1,
        "repo_role": "public",
        "repo_root": "..",
        "max_active_slots": 3,
        "lease_timeout_seconds": 0,
        "slots": {
            str(number): {
                "worktree": f"../wt{number}",
                "branch": f"worktree-wt{number}",
                "endpoint_name": f"test_wt{number}",
                "proxy_port": 29000 + number,
                "backend_port": 29100 + number,
            }
            for number in (1, 2, 3)
        },
        "server": {
            "host": "127.0.0.1",
            "command": ["false"],
            "disabled_tools": ["lean_build"],
            "probe_file": "Test.lean",
            "instructions": "no builds",
            "startup_timeout_seconds": 1,
        },
        "build": {
            "cwd": "lean",
            "command": ["/usr/bin/true"],
            "fingerprint_files": [
                "lean/lean-toolchain",
                "lean/lakefile.toml",
                "lean/lake-manifest.json",
            ],
        },
    }
    inventory_path = repo / "config" / "lean-slots.public.json"
    inventory_path.write_text(json.dumps(inventory))
    (repo / ".codex" / "agents").mkdir(parents=True)
    (repo / ".codex" / "hooks").mkdir()
    (repo / ".codex" / "config.template.toml").write_text(
        "# GENERATED by scripts/slotctl.py config render.\n"
        "# source-digest = {{SOURCE_DIGEST}}\n"
        'repo = "{{REPO_ROOT}}"\n'
        'agent_dir = "{{AGENT_CONFIG_DIR}}"\n'
        "{{MCP_CLIENT_AUTH}}\n"
    )
    (repo / ".codex" / "agents" / "worker.toml").write_text(
        "name = 'worker'\nurl = 'http://127.0.0.1:29001/mcp'\n"
    )
    (repo / ".codex" / "hooks" / "pre_tool_use_policy.py").write_text("# policy\n")
    _fixture_runtime_launcher(repo)
    run(repo, "git", "add", "config", ".codex", "scripts")
    run(repo, "git", "commit", "-m", "add slot infrastructure")
    monkeypatch.setenv("LEAN_SLOT_STATE_DIR", str(tmp_path / "state"))
    monkeypatch.setenv("LEAN_SLOT_SKIP_SUPERVISOR", "1")
    monkeypatch.setenv("LEAN_SLOT_OWNER_PID", str(os.getpid()))
    # Session tests select their own identity after removing the PID override.
    # Never let the launching client shadow those synthetic session identities.
    for variable in ("LEAN_SLOT_OWNER_SESSION", "CODEX_THREAD_ID", "CLAUDE_CODE_SESSION_ID"):
        monkeypatch.delenv(variable, raising=False)
    controller = Controller(Inventory.load(inventory_path))
    return controller, repo, worktrees


@pytest.fixture()
def downstream_repo(
    slot_repo, tmp_path: Path
) -> tuple[Controller, Controller, Path, list[Path]]:
    public_controller, public_repo, public_worktrees = slot_repo
    public_head = run(public_repo, "git", "rev-parse", "main")
    for number, worktree in enumerate(public_worktrees, 1):
        run(worktree, "git", "checkout", "-B", f"worktree-wt{number}", public_head)

    repo = tmp_path / "downstream"
    repo.mkdir()
    run(repo, "git", "init", "-b", "main")
    run(repo, "git", "config", "user.name", "Slot Test")
    run(repo, "git", "config", "user.email", "slot@example.invalid")
    (repo / "lean").mkdir()
    (repo / "lean" / "lean-toolchain").write_text("leanprover/lean4:v4.test\n")
    (repo / "lean" / "lakefile.toml").write_text(
        "name = 'Downstream'\n"
        "[[require]]\n"
        "name = 'Primary'\n"
        "path = '../../primary/lean'\n"
    )
    (repo / "lean" / "lake-manifest.json").write_text("{}\n")
    (repo / ".gitignore").write_text("lean/.lake/\n")
    run(repo, "git", "add", ".")
    run(repo, "git", "commit", "-m", "initial downstream")

    worktrees: list[Path] = []
    for number, public_worktree in enumerate(public_worktrees, 1):
        pair = tmp_path / "pairs" / f"wt{number}"
        pair.mkdir(parents=True)
        (pair / "primary").symlink_to(public_worktree, target_is_directory=True)
        worktree = pair / "downstream"
        run(
            repo,
            "git",
            "worktree",
            "add",
            "-b",
            f"worktree-wt{number}",
            str(worktree),
            "main",
        )
        worktrees.append(worktree)

    lake_build = repo / "lean" / ".lake" / "build"
    lake_build.mkdir(parents=True)
    (lake_build / "artifact").write_text("downstream built\n")
    (repo / "config").mkdir()
    inventory = {
        "schema_version": 1,
        "repo_role": "downstream",
        "repo_root": "..",
        "max_active_slots": 3,
        "lease_timeout_seconds": 0,
        "paired_dependency": {
            "inventory": "../../primary/config/lean-slots.public.json",
            "base_ref": "main",
            "lake_dependency_name": "Primary",
            "path_from_primary_lean": "../../primary/lean",
            "path_from_slot_lean": "../../primary/lean",
        },
        "config": {"manage_workspace": False},
        "slots": {
            str(number): {
                "worktree": f"../pairs/wt{number}/downstream",
                "branch": f"worktree-wt{number}",
                "endpoint_name": f"downstream_wt{number}",
                "proxy_port": 29200 + number,
                "backend_port": 29300 + number,
            }
            for number in (1, 2, 3)
        },
        "server": {
            "host": "127.0.0.1",
            "command": ["false"],
            "disabled_tools": ["lean_build"],
            "probe_file": "Test.lean",
            "instructions": "no builds",
            "startup_timeout_seconds": 1,
            "backend_policy": "leased",
        },
        "build": {
            "cwd": "lean",
            "command": ["/usr/bin/true"],
            "fingerprint_files": [
                "lean/lean-toolchain",
                "lean/lakefile.toml",
                "lean/lake-manifest.json",
            ],
        },
    }
    inventory_path = repo / "config" / "lean-slots.downstream.json"
    inventory_path.write_text(json.dumps(inventory))
    (repo / ".codex" / "agents").mkdir(parents=True)
    (repo / ".codex" / "hooks").mkdir()
    (repo / ".codex" / "config.template.toml").write_text(
        "# GENERATED by scripts/slotctl.py config render.\n"
        "# source-digest = {{SOURCE_DIGEST}}\n"
        'repo = "{{REPO_ROOT}}"\n'
    )
    (repo / ".codex" / "agents" / "worker.toml").write_text("name = 'worker'\n")
    (repo / ".codex" / "hooks" / "pre_tool_use_policy.py").write_text("# policy\n")
    _fixture_runtime_launcher(repo)
    run(repo, "git", "add", "config", ".codex", "scripts")
    run(repo, "git", "commit", "-m", "add downstream slot infrastructure")
    controller = Controller(Inventory.load(inventory_path))
    return controller, public_controller, repo, worktrees


def prepare(controller: Controller, number: int, *, client: str = "codex") -> None:
    controller.acquire(number, client=client, base_ref="main")
    controller.prepare(number)


def commit(worktree: Path, filename: str, content: str) -> str:
    (worktree / filename).write_text(content)
    run(worktree, "git", "add", filename)
    run(worktree, "git", "commit", "-m", f"add {filename}")
    return run(worktree, "git", "rev-parse", "HEAD")


def test_inventory_is_exactly_three_global_slots(slot_repo) -> None:
    controller, _, _ = slot_repo
    assert set(controller.inventory.raw["slots"]) == {"1", "2", "3"}
    assert controller.inventory.raw["max_active_slots"] == 3
    with pytest.raises(SlotError, match="one of 1, 2, 3"):
        controller.acquire(4, client="codex", base_ref="main")


def test_cross_client_collision_fails_closed(slot_repo) -> None:
    controller, _, _ = slot_repo
    controller.acquire(1, client="codex", base_ref="main")
    with pytest.raises(SlotError, match="already leased by codex"):
        controller.acquire(1, client="claude", base_ref="main")


def test_trusted_local_lease_needs_no_client_token(slot_repo) -> None:
    controller, _, _ = slot_repo
    lease = controller.acquire(1, client="codex", base_ref="main")
    assert lease["client_auth"] == "trusted-local"
    assert "token_hash" not in lease
    assert not controller.inventory.client_token_path("codex").exists()


def test_bearer_lease_retains_client_token_binding(slot_repo) -> None:
    controller, _, _ = slot_repo
    controller.inventory.raw["server"]["client_auth"] = "bearer"
    lease = controller.acquire(1, client="codex", base_ref="main")
    assert lease["client_auth"] == "bearer"
    assert lease["token_hash"]
    assert controller.inventory.client_token_path("codex").exists()


def test_client_auth_mode_cannot_change_under_an_existing_lease(slot_repo) -> None:
    controller, _, _ = slot_repo
    controller.acquire(1, client="codex", base_ref="main")
    controller.inventory.raw["server"]["client_auth"] = "bearer"
    with pytest.raises(SlotError, match="client-auth mode mismatch"):
        controller.heartbeat(1)


def test_trusted_local_mode_rejects_non_loopback_binding(slot_repo) -> None:
    controller, _, _ = slot_repo
    controller.inventory.raw["server"]["host"] = "0.0.0.0"
    with pytest.raises(SlotError, match="requires a loopback"):
        _ = controller.inventory.client_auth_mode


def test_three_distinct_slots_can_be_leased(slot_repo) -> None:
    controller, _, _ = slot_repo
    for number in (1, 2, 3):
        controller.acquire(number, client="codex", base_ref="main")
    assert [item["lease"]["state"] for item in controller.status()["slots"]] == [
        "ACQUIRED",
        "ACQUIRED",
        "ACQUIRED",
    ]


def test_dirty_acquire_quarantines_without_deleting_work(slot_repo) -> None:
    controller, _, worktrees = slot_repo
    protected = worktrees[0] / "protected.lean"
    protected.write_text("theorem keep : True := by trivial\n")
    with pytest.raises(SlotError, match="quarantined"):
        controller.acquire(1, client="codex", base_ref="main")
    assert protected.exists()
    assert controller.inventory.lease(1)["state"] == "QUARANTINED"
    protected.unlink()
    controller.release(1)
    assert controller.inventory.lease(1, required=False) is None


def test_build_epoch_and_atomic_cache_prepare(slot_repo) -> None:
    controller, _, worktrees = slot_repo
    epoch = controller.build()
    prepare(controller, 2)
    lease = controller.inventory.lease(2)
    assert lease["state"] == "ACTIVE"
    assert lease["prepared_epoch"] == epoch["epoch_id"]
    assert (
        worktrees[1] / "lean" / ".lake" / "build" / "artifact"
    ).read_text() == "built\n"


def test_epoch_invalidates_when_dependency_fingerprint_changes(slot_repo) -> None:
    controller, repo, _ = slot_repo
    controller.build()
    (repo / "lean" / "lake-manifest.json").write_text('{"changed": true}\n')
    run(repo, "git", "add", "lean/lake-manifest.json")
    run(repo, "git", "commit", "-m", "change manifest")
    controller.acquire(1, client="codex", base_ref="main")
    with pytest.raises(SlotError, match="no successful-build epoch"):
        controller.prepare(1)


def test_ready_requires_clean_committed_work(slot_repo) -> None:
    controller, _, worktrees = slot_repo
    controller.build()
    prepare(controller, 1)
    (worktrees[0] / "draft.lean").write_text("draft\n")
    with pytest.raises(SlotError, match="quarantined"):
        controller.ready(1)
    assert controller.inventory.lease(1)["state"] == "QUARANTINED"


def test_absorb_refuses_a_head_changed_after_ready(slot_repo) -> None:
    controller, _, worktrees = slot_repo
    controller.build()
    prepare(controller, 1)
    commit(worktrees[0], "reviewed.txt", "reviewed\n")
    controller.ready(1)
    commit(worktrees[0], "late.txt", "late\n")
    with pytest.raises(SlotError, match="HEAD changed after ready"):
        controller.absorb(1)
    assert controller.inventory.lease(1)["state"] == "QUARANTINED"


def test_lake_clone_fallback_removes_partial_copy(
    slot_repo, monkeypatch: pytest.MonkeyPatch
) -> None:
    controller, _, worktrees = slot_repo

    def failed_clone(command, **kwargs):
        destination = Path(command[-1])
        destination.mkdir(parents=True)
        (destination / "partial").write_text("partial\n")
        return SimpleNamespace(returncode=1)

    monkeypatch.setattr("scripts.lean_slots.controller.subprocess.run", failed_clone)
    controller._replace_lake(3)
    destination = worktrees[2] / "lean" / ".lake"
    assert not (destination / "partial").exists()
    assert (destination / "build" / "artifact").read_text() == "built\n"


def test_two_sibling_workers_absorb_by_rebase_and_fast_forward(slot_repo) -> None:
    controller, repo, worktrees = slot_repo
    base_count = int(run(repo, "git", "rev-list", "--count", "main"))
    controller.build()
    prepare(controller, 1)
    prepare(controller, 2)
    first = commit(worktrees[0], "first.txt", "first\n")
    second_before_rebase = commit(worktrees[1], "second.txt", "second\n")
    controller.ready(1)
    controller.ready(2)
    first_result = controller.absorb(1)
    second_result = controller.absorb(2)
    assert first_result["integrated_head"] == first
    assert second_result["integrated_head"] != second_before_rebase
    assert (repo / "first.txt").read_text() == "first\n"
    assert (repo / "second.txt").read_text() == "second\n"
    assert int(run(repo, "git", "rev-list", "--count", "main")) == base_count + 2
    assert controller.inventory.lease(1, required=False) is None
    assert controller.inventory.lease(2, required=False) is None


def test_stale_reclaim_is_safe_or_quarantines(slot_repo, monkeypatch, isolated_process_observations) -> None:
    controller, _, worktrees = slot_repo
    monkeypatch.setenv("LEAN_SLOT_OWNER_PID", "999999")
    isolated_process_observations.add(999999, "verified fixture owner")
    controller.acquire(1, client="codex", base_ref="main")
    isolated_process_observations.remove(999999)
    controller.reclaim(1)
    assert controller.inventory.lease(1, required=False) is None

    isolated_process_observations.add(999999, "verified fixture owner")
    controller.acquire(2, client="codex", base_ref="main")
    isolated_process_observations.remove(999999)
    protected = worktrees[1] / "uncommitted.txt"
    protected.write_text("keep\n")
    with pytest.raises(SlotError, match="quarantined"):
        controller.reclaim(2)
    assert protected.exists()
    assert controller.inventory.lease(2)["state"] == "QUARANTINED"


def test_session_owned_reclaim_requires_explicit_owner_confirmation(
    slot_repo, monkeypatch
) -> None:
    controller, _, _ = slot_repo
    monkeypatch.delenv("LEAN_SLOT_OWNER_PID")
    monkeypatch.setenv("CODEX_THREAD_ID", "test-thread")
    controller.acquire(1, client="codex", base_ref="main")
    lease = controller.inventory.lease(1)
    assert lease["owner_kind"] == "session"
    assert "test-thread" not in json.dumps(lease)
    with pytest.raises(SlotError, match="confirm-owner-gone"):
        controller.reclaim(1)
    controller.reclaim(1, confirm_owner_gone=True)


def test_released_lease_cannot_dispatch_on_existing_session_in_trusted_local_mode(
    slot_repo,
) -> None:
    controller, _, _ = slot_repo
    controller.build()
    prepare(controller, 1)
    gate = LeaseGate(controller.inventory, 1)
    client, supplied_hash = gate.identify(None, "codex")
    call = json.dumps(
        {
            "jsonrpc": "2.0",
            "id": 1,
            "method": "tools/call",
            "params": {"name": "lean_diagnostic_messages"},
        }
    ).encode()
    gate.authorize(client, supplied_hash, call)
    wrong_client, _ = gate.identify(None, "claude")
    with pytest.raises(SlotError, match="another client"):
        gate.authorize(wrong_client, None, call)
    unidentified, _ = gate.identify(None)
    with pytest.raises(SlotError, match="another client"):
        gate.authorize(unidentified, None, call)
    controller.release(1)
    with pytest.raises(SlotError, match="no active lease"):
        gate.authorize(client, supplied_hash, call)


def test_lean_build_is_denied_even_with_active_lease(slot_repo) -> None:
    controller, _, _ = slot_repo
    controller.build()
    prepare(controller, 1)
    gate = LeaseGate(controller.inventory, 1)
    client, supplied_hash = gate.identify(None, "codex")
    build = json.dumps(
        {
            "jsonrpc": "2.0",
            "id": 1,
            "method": "tools/call",
            "params": {"name": "lean_build"},
        }
    ).encode()
    with pytest.raises(SlotError, match="disabled"):
        gate.authorize(client, supplied_hash, build)


def test_trusted_local_discovery_needs_no_credential(slot_repo) -> None:
    controller, _, _ = slot_repo
    gate = LeaseGate(controller.inventory, 3)
    client, supplied_hash = gate.identify(None)
    listing = json.dumps({"jsonrpc": "2.0", "id": 1, "method": "tools/list"}).encode()
    gate.authorize(client, supplied_hash, listing)


def test_bearer_mode_requires_known_credential(slot_repo) -> None:
    controller, _, _ = slot_repo
    controller.inventory.raw["server"]["client_auth"] = "bearer"
    token = controller.inventory.token("codex")
    gate = LeaseGate(controller.inventory, 3)
    assert gate.identify(f"Bearer {token}", "codex")[0] == "codex"
    with pytest.raises(SlotError, match="does not match"):
        gate.identify(f"Bearer {token}", "claude")
    with pytest.raises(SlotError, match="unknown or expired"):
        gate.identify("Bearer wrong")


def test_generated_trusted_local_config_has_no_bearer_dependency_and_drift_is_fail_closed(
    slot_repo,
) -> None:
    controller, _, _ = slot_repo
    [path] = controller.render_config(scope="repo")
    assert path.stat().st_mode & 0o077 == 0
    original = path.read_text()
    assert "bearer_token_env_var" not in original
    assert str(controller.repo / ".codex" / "agents") in original
    path.write_text(original + "# local edit\n")
    with pytest.raises(SlotError, match="refusing to overwrite"):
        controller.render_config(scope="repo")


def test_trusted_local_mode_rejects_meaningless_token_rotation(slot_repo) -> None:
    controller, _, _ = slot_repo
    with pytest.raises(SlotError, match="only in bearer"):
        controller.render_config(scope="repo", rotate_token=True)


def test_bearer_config_and_token_rotation_are_available_but_fail_closed(
    slot_repo,
) -> None:
    controller, _, _ = slot_repo
    controller.inventory.raw["server"]["client_auth"] = "bearer"
    [path] = controller.render_config(scope="repo")
    assert 'bearer_token_env_var = "LEAN_SLOT_CODEX_TOKEN"' in path.read_text()
    generated_agent = (
        controller.repo / ".codex" / "generated" / "agents" / "worker.toml"
    )
    assert (
        'bearer_token_env_var = "LEAN_SLOT_CODEX_TOKEN"' in generated_agent.read_text()
    )
    controller.acquire(1, client="codex", base_ref="main")
    with pytest.raises(SlotError, match="while slots are leased"):
        controller.render_config(scope="repo", rotate_token=True)


def test_two_scope_render_preflights_before_writing(slot_repo) -> None:
    controller, _, _ = slot_repo
    [repo_config] = controller.render_config(scope="repo")
    stale = repo_config.read_text() + "# stale generated copy\n"
    repo_config.write_text(stale)
    workspace_config = controller.inventory.workspace_root / ".codex" / "config.toml"
    workspace_config.parent.mkdir(exist_ok=True)
    workspace_config.write_text("# operator-owned\n")
    with pytest.raises(SlotError, match="refusing to overwrite"):
        controller.render_config(scope="both", force=True)
    assert repo_config.read_text() == stale
    assert workspace_config.read_text() == "# operator-owned\n"


def test_global_backend_limit_counts_other_repository_roles(downstream_repo, isolated_process_observations) -> None:
    from tests.test_lean_lifecycle_observation import owned
    downstream, public, _, _ = downstream_repo
    supervisor = Supervisor(public.inventory)
    counterpart = Supervisor(downstream.inventory)
    for number in (1, 2, 3):
        owned(counterpart, isolated_process_observations, "backend", number, 811000 + number)
    assert supervisor.global_backend_count() == 3
    assert supervisor.capacity_census()["complete"]
    with pytest.raises(SlotError, match="global heavy-backend limit"):
        supervisor.start_backend(1)
    assert not isolated_process_observations.launches


def test_one_physical_slot_cannot_have_two_repository_backends(downstream_repo, isolated_process_observations) -> None:
    from tests.test_lean_lifecycle_observation import owned
    downstream, public, _, _ = downstream_repo
    owned(Supervisor(downstream.inventory), isolated_process_observations, "backend", 2, 811102)
    with pytest.raises(SlotError, match="physical wt2 already reserved"):
        Supervisor(public.inventory).start_backend(2)
    assert not isolated_process_observations.launches


def test_proxy_runtime_fingerprint_changes_with_client_auth_mode(slot_repo) -> None:
    controller, _, _ = slot_repo
    supervisor = Supervisor(controller.inventory)
    trusted_local = supervisor._runtime_fingerprint("proxy", 1)
    controller.inventory.raw["server"]["client_auth"] = "bearer"
    assert supervisor._runtime_fingerprint("proxy", 1) != trusted_local


def test_downstream_lease_pins_clean_paired_dependency(downstream_repo) -> None:
    controller, public_controller, _, _ = downstream_repo
    epoch = controller.build()
    lease = controller.acquire(2, client="codex", base_ref="main")
    public_sha = run(public_controller.repo, "git", "rev-parse", "main")
    assert lease["public_dependency_sha"] == public_sha
    assert epoch["fingerprint"]["public_dependency_sha"] == public_sha
    controller.prepare(2)
    assert controller.inventory.lease(2)["state"] == "ACTIVE"


@pytest.fixture()
def candidate_repo(downstream_repo, monkeypatch, request, isolated_process_observations):
    """Distinct task/dependency refs, with ordinary public pinning in tmp repos."""
    downstream, public, repo, worktrees = downstream_repo
    public_main = run(public.repo, "git", "rev-parse", "main")
    downstream_main = run(repo, "git", "rev-parse", "main")
    run(public.repo, "git", "checkout", "-b", "reviewed-candidate")
    run(repo, "git", "checkout", "-b", "research-task")
    source = downstream.inventory.source
    raw = json.loads(source.read_text())
    raw["paired_dependency"]["base_ref"] = "reviewed-candidate"
    source.write_text(json.dumps(raw))
    run(repo, "git", "add", "config")
    run(repo, "git", "commit", "-m", "select reviewed dependency")
    downstream = Controller(Inventory.load(source))
    task = run(repo, "git", "rev-parse", "HEAD")
    old_epoch = None
    if getattr(request, "param", None) == "old-epoch":
        old_epoch = downstream.build()
        assert old_epoch["fingerprint"]["commit_sha"] == task
        assert old_epoch["fingerprint"]["public_dependency_sha"] == public_main
    candidate = commit(public.repo, "candidate.txt", "reviewed dependency\n")
    assert public_main != candidate and downstream_main != task
    public_epoch = public.build()
    assert public_epoch["fingerprint"]["commit_sha"] == candidate
    # This fixture deliberately exercises cache-only preparation. The handoff test
    # below enables the actual Supervisor before either role's preparation.
    public.acquire(1, client="codex", base_ref="reviewed-candidate")
    public.prepare(1)
    assert public.inventory.lease(1)["prepared_epoch"] == public_epoch["epoch_id"]
    public.release(1)
    assert public.inventory.lease(1, required=False) is None
    epoch = old_epoch or downstream.build()
    rig = SimpleNamespace(
        downstream=downstream, public=public, repo=repo, worktree=worktrees[0],
        paired=public.inventory.worktree(1), public_main=public_main,
        downstream_main=downstream_main, candidate=candidate, task=task,
        epoch=epoch, public_epoch=public_epoch,
    )
    _candidate_mains(rig)
    request.node.user_properties.append(("candidate_inputs", json.dumps({
        "public_main_A": public_main, "candidate_B": candidate,
        "downstream_main_C": downstream_main, "task_D": task,
        "public_epoch": public_epoch, "downstream_epoch": epoch,
    }, sort_keys=True)))

    def final_evidence():
        host = isolated_process_observations
        request.node.user_properties.append(("candidate_exit", json.dumps({
            "public_main": run(public.repo, "git", "rev-parse", "main"),
            "downstream_main": run(repo, "git", "rev-parse", "main"),
            "public_head": run(public.repo, "git", "rev-parse", "HEAD"),
            "downstream_head": run(repo, "git", "rev-parse", "HEAD"),
            "paired_head": run(rig.paired, "git", "rev-parse", "HEAD"),
            "lease": downstream.inventory.lease(1, required=False),
            "launches": host.launches, "signals": host.signals,
            "commands": host.command_calls,
        }, sort_keys=True)))

    request.addfinalizer(final_evidence)
    return rig


def _candidate_mains(rig):
    assert run(rig.public.repo, "git", "rev-parse", "main") == rig.public_main
    assert run(rig.repo, "git", "rev-parse", "main") == rig.downstream_main


def _candidate_snapshot(rig):
    """Byte/ref preservation witness, excluding ignored runtime/cache state."""
    result = {}
    for root in (rig.public.repo, rig.repo, rig.paired, rig.worktree):
        names = run(root, "git", "ls-files", "--cached", "--others", "--exclude-standard")
        result[str(root)] = {
            "head": run(root, "git", "rev-parse", "HEAD"),
            "branch": run(root, "git", "branch", "--show-current"),
            "refs": run(root, "git", "show-ref", "--heads"),
            "status": run(root, "git", "status", "--porcelain=v1"),
            "files": {name: (root / name).read_bytes() for name in names.splitlines()},
        }
    for ctl in (rig.public, rig.downstream):
        epoch = ctl.inventory.epoch_path()
        result[str(epoch)] = epoch.read_bytes() if epoch.exists() else None
    return result


def _candidate_acquire(rig, *, base="research-task", active=False):
    lease = rig.downstream.acquire(1, client="codex", base_ref=base)
    assert lease["base_sha"] == rig.task
    assert lease["public_dependency_sha"] == rig.candidate
    assert lease["state"] == "ACQUIRED"
    if active:
        rig.downstream.prepare(1)
        lease = rig.downstream.inventory.lease(1)
        assert lease["state"] == "ACTIVE"
        assert lease["prepared_epoch"] == rig.epoch["epoch_id"]
        assert run(rig.worktree, "git", "rev-parse", "HEAD") == rig.task
    return lease


def _candidate_call(rig):
    gate = LeaseGate(rig.downstream.inventory, 1)
    client, supplied_hash = gate.identify(None, "codex")
    call = json.dumps({"jsonrpc": "2.0", "id": 1, "method": "tools/call",
                       "params": {"name": "lean_goal"}}).encode()
    return lambda: gate.authorize(client, supplied_hash, call)


def test_candidate_p1_distinct_task_and_dependency_epochs(candidate_repo):
    rig = candidate_repo
    lease = _candidate_acquire(rig, active=True)
    assert lease["base_ref"] == "research-task"
    assert rig.epoch["fingerprint"]["commit_sha"] == rig.task
    assert rig.epoch["fingerprint"]["public_dependency_sha"] == rig.candidate
    assert run(rig.paired, "git", "rev-parse", "HEAD") == rig.candidate
    assert not run(rig.paired, "git", "status", "--porcelain=v1")
    _candidate_call(rig)()
    _candidate_mains(rig)


def test_candidate_p2_absorb_with_actual_supervisor_handoff(
    candidate_repo, monkeypatch, isolated_process_observations
):
    rig = candidate_repo
    host = isolated_process_observations
    monkeypatch.delenv("LEAN_SLOT_SKIP_SUPERVISOR")
    public_sup = Supervisor(rig.public.inventory)
    downstream_sup = Supervisor(rig.downstream.inventory)
    public_sup.start_proxy(1)
    # Repeat the public ordinary lifecycle with supervision enabled throughout.
    rig.public.acquire(1, client="codex", base_ref="reviewed-candidate")
    rig.public.prepare(1)
    rig.public.release(1)
    assert public_sup.process_state("backend", 1) == "running"
    public_pid = json.loads(rig.public.inventory.process_path("backend", 1).read_text())["pid"]
    before_handoff = len(host.launches)
    _candidate_acquire(rig, active=True)
    assert (public_pid, signal.SIGTERM) in host.signals
    assert public_sup.process_state("backend", 1) == "down"
    assert downstream_sup.process_state("backend", 1) == "running"
    assert downstream_sup.backend_command(1) in host.launches[before_handoff:]
    census = downstream_sup.capacity_census()
    assert census["complete"] and not census["errors"] and not census["conflicts"]
    source = commit(rig.worktree, "allowed.lean", "-- isolated allowed source\n")
    ready = rig.downstream.ready(1)
    assert ready["state"] == "READY_TO_ABSORB" and ready["ready_head"] == source
    downstream_pid = json.loads(rig.downstream.inventory.process_path("backend", 1).read_text())["pid"]
    result = rig.downstream.absorb(1)
    assert result["integrated_head"] == source
    assert run(rig.repo, "git", "rev-parse", "research-task") == source
    assert (rig.repo / "allowed.lean").read_bytes() == b"-- isolated allowed source\n"
    assert result["epoch"]["fingerprint"]["commit_sha"] == source
    assert result["epoch"]["fingerprint"]["public_dependency_sha"] == rig.candidate
    assert result["epoch"]["epoch_id"] != rig.epoch["epoch_id"]
    assert rig.downstream.inventory.lease(1, required=False) is None
    assert (downstream_pid, signal.SIGTERM) in host.signals
    assert downstream_sup.process_state("backend", 1) == "down"
    assert public_sup.process_state("backend", 1) == "running"
    assert host.launches[-1] == public_sup.backend_command(1)
    assert run(rig.paired, "git", "rev-parse", "HEAD") == rig.candidate
    assert not run(rig.paired, "git", "status", "--porcelain=v1")
    _candidate_mains(rig)


def test_candidate_p3_no_change_normal_release(candidate_repo):
    rig = candidate_repo
    _candidate_acquire(rig, active=True)
    before = _candidate_snapshot(rig)
    rig.downstream.release(1)
    assert rig.downstream.inventory.lease(1, required=False) is None
    assert _candidate_snapshot(rig) == before
    _candidate_mains(rig)


@pytest.mark.parametrize("defect", ["configured-main", "other-primary", "dirty-primary"])
def test_candidate_n1_n2_primary_dependency_guard(candidate_repo, defect):
    rig = candidate_repo
    if defect == "configured-main":
        rig.downstream.inventory.raw["paired_dependency"]["base_ref"] = "main"
    elif defect == "other-primary":
        run(rig.public.repo, "git", "checkout", "main")
    else:
        (rig.public.repo / "protected.txt").write_text("retain primary work\n")
    before = _candidate_snapshot(rig)
    detail = "checkout is dirty" if defect == "dirty-primary" else "not on its configured base"
    with pytest.raises(SlotError, match=detail):
        _candidate_acquire(rig)
    assert rig.downstream.inventory.lease(1, required=False) is None
    assert _candidate_snapshot(rig) == before


def test_candidate_public_primary_guard_compares_sha_not_branch(candidate_repo):
    rig = candidate_repo
    run(rig.public.repo, "git", "checkout", "-b", "same-reviewed-sha")
    assert rig.public._dependency_primary_sha() is None  # public has no dependency
    _candidate_acquire(rig, active=True)
    _candidate_mains(rig)


@pytest.mark.parametrize("defect", ["clean-sha", "dirty"])
def test_candidate_n3_paired_pin_and_cleanliness(candidate_repo, defect):
    rig = candidate_repo
    if defect == "clean-sha":
        run(rig.paired, "git", "reset", "--hard", rig.public_main)
        assert not run(rig.paired, "git", "status", "--porcelain=v1")
    else:
        (rig.paired / "protected.lean").write_text("retain dependency work\n")
    before = _candidate_snapshot(rig)
    with pytest.raises(SlotError, match="not pinned" if defect == "clean-sha" else "is dirty"):
        _candidate_acquire(rig)
    assert rig.downstream.inventory.lease(1, required=False) is None
    assert _candidate_snapshot(rig) == before


@pytest.mark.parametrize("defect, detail", [
    ("branch", "branch mismatch"),
    ("realpath", "paired dependency path mismatch"),
    ("primary-lake", "Lake dependency path mismatch"),
    ("slot-lake", "Lake dependency path mismatch"),
])
def test_candidate_n4_independent_identity_and_paths(candidate_repo, defect, detail):
    rig = candidate_repo
    if defect == "branch":
        run(rig.paired, "git", "checkout", "-b", "unexpected-paired-branch")
    elif defect == "realpath":
        link = rig.worktree.parent / "primary"
        link.unlink()
        link.symlink_to(rig.public.inventory.worktree(2), target_is_directory=True)
    else:
        root = rig.repo if defect == "primary-lake" else rig.worktree
        lake = root / "lean" / "lakefile.toml"
        lake.write_text(lake.read_text().replace("../../primary/lean", "../../wrong/lean"))
    before = _candidate_snapshot(rig)
    with pytest.raises(SlotError, match=detail):
        _candidate_acquire(rig)
    assert rig.downstream.inventory.lease(1, required=False) is None
    assert _candidate_snapshot(rig) == before
    if defect == "realpath":
        assert (rig.worktree.parent / "primary").resolve() == rig.public.inventory.worktree(2)


@pytest.mark.parametrize("candidate_repo", ["old-epoch"], indirect=True)
def test_candidate_n5_old_dependency_epoch_does_not_match_new_pin(candidate_repo):
    rig = candidate_repo
    _candidate_acquire(rig)
    assert rig.epoch["fingerprint"]["commit_sha"] == rig.task
    assert rig.epoch["fingerprint"]["public_dependency_sha"] == rig.public_main
    before = _candidate_snapshot(rig)
    with pytest.raises(SlotError, match="no successful-build epoch matches"):
        rig.downstream.prepare(1)
    lease = rig.downstream.inventory.lease(1)
    assert lease["state"] == "ACQUIRED" and lease["public_dependency_sha"] == rig.candidate
    assert "prepared_epoch" not in lease
    assert _candidate_snapshot(rig) == before


@pytest.mark.parametrize("stage", ["acquired", "active-commit", "ready-commit"])
def test_candidate_n6_dependency_advance_at_each_lifecycle_guard(candidate_repo, stage):
    rig = candidate_repo
    _candidate_acquire(rig, active=stage != "acquired")
    if stage != "acquired":
        source = commit(rig.worktree, "retained.lean", "-- preserve committed work\n")
        assert source != rig.task
        # The actual per-call gate's invariant covers the retained paired pin.
        call = _candidate_call(rig)
        call()
        if stage == "ready-commit":
            assert rig.downstream.ready(1)["ready_head"] == source
    advanced = commit(rig.public.repo, "advanced.txt", "next public dependency\n")
    assert advanced != rig.candidate
    assert run(rig.paired, "git", "rev-parse", "HEAD") == rig.candidate
    assert not run(rig.paired, "git", "status", "--porcelain=v1")
    if stage == "active-commit":
        call()  # ACTIVE, before the controller quarantines; primary is not checked.
        assert rig.downstream.inventory.lease(1)["state"] == "ACTIVE"
    before = _candidate_snapshot(rig)
    operation = {"acquired": rig.downstream.prepare, "active-commit": rig.downstream.ready,
                 "ready-commit": rig.downstream.absorb}[stage]
    with pytest.raises(SlotError, match="paired dependency base advanced"):
        operation(1)
    lease = rig.downstream.inventory.lease(1)
    assert lease["public_dependency_sha"] == rig.candidate and lease["base_sha"] == rig.task
    assert lease["state"] == ("ACQUIRED" if stage == "acquired" else "QUARANTINED")
    assert _candidate_snapshot(rig) == before
    _candidate_mains(rig)


@pytest.mark.parametrize("defect, detail", [
    ("clean-sha", "paired dependency SHA changed"),
    ("dirty", "paired dependency became dirty"),
])
def test_candidate_n7_gate_rechecks_actual_paired_git(candidate_repo, defect, detail):
    rig = candidate_repo
    _candidate_acquire(rig, active=True)
    call = _candidate_call(rig)
    call()
    if defect == "clean-sha":
        run(rig.paired, "git", "reset", "--hard", rig.public_main)
        assert not run(rig.paired, "git", "status", "--porcelain=v1")
    else:
        (rig.paired / "protected.lean").write_text("retain dirty pin\n")
    before = _candidate_snapshot(rig)
    lease = rig.downstream.inventory.lease_path(1).read_bytes()
    with pytest.raises(SlotError, match=detail):
        call()
    assert rig.downstream.inventory.lease_path(1).read_bytes() == lease
    assert _candidate_snapshot(rig) == before


def test_candidate_n8_task_ref_advance_rejects_prepare(candidate_repo):
    rig = candidate_repo
    _candidate_acquire(rig)
    advanced = commit(rig.repo, "task-advance.lean", "-- new authoritative task\n")
    assert advanced != rig.task
    before = _candidate_snapshot(rig)
    with pytest.raises(SlotError, match="base ref advanced after acquisition"):
        rig.downstream.prepare(1)
    lease = rig.downstream.inventory.lease(1)
    assert lease["state"] == "QUARANTINED" and lease["base_sha"] == rig.task
    assert lease["public_dependency_sha"] == rig.candidate
    assert _candidate_snapshot(rig) == before


@pytest.mark.parametrize("base_kind", ["sha", "alias"])
def test_candidate_n8_absorb_requires_literal_task_branch(candidate_repo, base_kind):
    rig = candidate_repo
    run(rig.repo, "git", "branch", "task-alias", rig.task)
    base = rig.task if base_kind == "sha" else "task-alias"
    _candidate_acquire(rig, base=base, active=True)
    source = commit(rig.worktree, "retained.lean", "-- retain actual ready commit\n")
    assert rig.downstream.ready(1)["ready_head"] == source
    before = _candidate_snapshot(rig)
    lease_bytes = rig.downstream.inventory.lease_path(1).read_bytes()
    with pytest.raises(SlotError, match="primary checkout is on 'research-task'; switch to"):
        rig.downstream.absorb(1)
    assert rig.downstream.inventory.lease_path(1).read_bytes() == lease_bytes
    assert rig.downstream.inventory.lease(1)["state"] == "READY_TO_ABSORB"
    assert _candidate_snapshot(rig) == before


@pytest.mark.parametrize("defect", ["dirty", "failed-command"])
def test_candidate_n9_failed_build_preserves_successful_epoch(
    candidate_repo, isolated_process_observations, defect
):
    rig = candidate_repo
    if defect == "dirty":
        (rig.repo / "protected.lean").write_text("retain authoritative draft\n")
        detail = "requires a clean committed primary"
    else:
        command = ["git", "rev-parse", "--verify", "missing-build-input"]
        rig.downstream.inventory.raw["build"]["command"] = command
        detail = r"authoritative build failed \(128\)"
    before = _candidate_snapshot(rig)
    with pytest.raises(SlotError, match=detail):
        rig.downstream.build()
    if defect == "failed-command":
        assert isolated_process_observations.command_calls[-1] == command
    assert _candidate_snapshot(rig) == before
    assert rig.downstream.inventory.lease(1, required=False) is None


@pytest.mark.parametrize("defect, detail", [
    ("dirty-task", "dirty files remain"),
    ("unabsorbed", "not contained"),
    ("dirty-pair", "paired dependency wt1 is dirty"),
    ("moved-pair", "not pinned"),
])
def test_candidate_n10_release_preserves_work_and_quarantine(candidate_repo, defect, detail):
    rig = candidate_repo
    _candidate_acquire(rig, active=True)
    if defect == "dirty-task":
        (rig.worktree / "protected.lean").write_text("retain task draft\n")
    elif defect == "unabsorbed":
        commit(rig.worktree, "protected.lean", "-- retain unabsorbed commit\n")
    elif defect == "dirty-pair":
        (rig.paired / "protected.lean").write_text("retain paired draft\n")
    else:
        commit(rig.paired, "protected.lean", "-- retain moved paired commit\n")
    before = _candidate_snapshot(rig)
    with pytest.raises(SlotError, match=detail):
        rig.downstream.release(1)
    lease = rig.downstream.inventory.lease(1)
    assert lease["state"] == "QUARANTINED" and lease["public_dependency_sha"] == rig.candidate
    assert _candidate_snapshot(rig) == before


def test_candidate_n10_stop_only_reservation_preserves_lease(
    candidate_repo, monkeypatch, isolated_process_observations
):
    from tests.test_lean_lifecycle_observation import rr_orphan, rr_retained_recovery, rr_session
    rig = candidate_repo
    rr_session(monkeypatch)
    _candidate_acquire(rig, active=True)
    rig.downstream._quarantine(1, rig.downstream.inventory.lease(1), "isolated recovery case")
    monkeypatch.delenv("LEAN_SLOT_SKIP_SUPERVISOR")
    host = isolated_process_observations
    request = rr_orphan(rig.downstream, host)
    path = rr_retained_recovery(rig.downstream, host, request)
    retained = path.read_bytes()
    before = _candidate_snapshot(rig)
    lease = rig.downstream.inventory.lease_path(1).read_bytes()
    signals = list(host.signals)
    with pytest.raises(SlotError, match="pending stop-only recovery"):
        rig.downstream.release(1)
    assert rig.downstream.inventory.lease_path(1).read_bytes() == lease
    assert path.read_bytes() == retained and host.signals == signals
    assert _candidate_snapshot(rig) == before


def test_candidate_p4_retained_pin_release_after_primary_advance(candidate_repo):
    rig = candidate_repo
    _candidate_acquire(rig, active=True)
    commit(rig.public.repo, "advanced.txt", "new dependency outside retained window\n")
    before = _candidate_snapshot(rig)
    rig.downstream.release(1)
    assert rig.downstream.inventory.lease(1, required=False) is None
    assert _candidate_snapshot(rig) == before
    assert run(rig.paired, "git", "rev-parse", "HEAD") == rig.candidate
    _candidate_mains(rig)


def test_candidate_n11_selected_source_and_alternate_domain(candidate_repo, monkeypatch, tmp_path):
    from scripts.lean_slots import cli, state
    rig = candidate_repo
    selected = rig.downstream.inventory.source
    monkeypatch.setenv("LEAN_SLOT_CONFIG", str(selected))
    canonical = Inventory.load()
    assert canonical.source == selected
    assert canonical.repo_root == rig.repo
    assert canonical.state_root == rig.public.inventory.state_root
    assert canonical.paired_inventory().source == rig.public.inventory.source
    assert canonical.paired_inventory().state_root == canonical.state_root
    _candidate_acquire(rig)
    original_lease = canonical.lease_path(1).read_bytes()
    assert Controller().inventory.lease(1)["public_dependency_sha"] == rig.candidate
    # The CLI's explicit selection is passed to the same Inventory loader.
    args = cli.parser().parse_args(["--inventory", str(selected), "build"])
    assert Inventory.load(args.inventory).source == selected
    monkeypatch.delenv("LEAN_SLOT_CONFIG")
    assert Inventory.load().source == Path(state.__file__).resolve().parents[2] / "config/lean-slots.public.json"
    alternate = tmp_path / "alternate" / "config" / "slots.json"
    alternate.parent.mkdir(parents=True)
    alternate.write_text(json.dumps(canonical.raw))
    monkeypatch.setenv("LEAN_SLOT_CONFIG", str(alternate))
    monkeypatch.setenv("LEAN_SLOT_STATE_DIR", str(tmp_path / "alternate-state"))
    copied = Inventory.load()
    assert copied.source == alternate and copied.repo_root != canonical.repo_root
    assert copied.state_root != canonical.state_root
    assert copied.lease(1, required=False) is None
    assert canonical.lease_path(1).read_bytes() == original_lease
    # An alternate configured domain can load; it is not canonical availability.
    assert Inventory.load(args.inventory).source == selected  # explicit beats env
    with pytest.raises(SlotError, match="share one runtime state"):
        canonical.paired_inventory()
    monkeypatch.setenv("LEAN_SLOT_STATE_DIR", str(canonical.state_root))
    assert canonical.paired_inventory().state_root == canonical.state_root
    assert canonical.lease_path(1).read_bytes() == original_lease


@pytest.mark.parametrize("defect, detail", [
    ("slots", "exactly the global slots"),
    ("role", "repo_role must be a nonempty string"),
    ("absolute-pair", "inventory paths must be relative"),
    ("same-role", "distinct repository roles"),
])
def test_candidate_n11_existing_inventory_domain_guards(candidate_repo, tmp_path, defect, detail):
    rig = candidate_repo
    raw = json.loads(rig.downstream.inventory.source.read_text())
    if defect == "slots":
        del raw["slots"]["3"]
    elif defect == "role":
        raw["repo_role"] = ""
    elif defect == "absolute-pair":
        raw["paired_dependency"]["inventory"] = str(rig.public.inventory.source)
    else:
        raw["repo_role"] = "public"
    # An untracked ignored runtime copy can exercise schema/domain validation
    # without changing either authoritative temporary source inventory.
    path = tmp_path / "invalid-inventory.json"
    path.write_text(json.dumps(raw))
    before = _candidate_snapshot(rig)
    with pytest.raises(SlotError, match=detail):
        if defect in {"absolute-pair", "same-role"}:
            # Keep the original source directory for relative dependency lookup.
            from dataclasses import replace
            replace(rig.downstream.inventory, raw=raw).paired_inventory()
        else:
            Inventory.load(path)
    assert rig.downstream.inventory.lease(1, required=False) is None
    assert _candidate_snapshot(rig) == before


def test_downstream_acquire_refuses_dirty_or_unpinned_dependency(
    downstream_repo,
) -> None:
    controller, _, _, _ = downstream_repo
    paired = controller.inventory.paired_inventory()
    assert paired is not None
    protected = paired.worktree(1) / "protected.lean"
    protected.write_text("keep\n")
    with pytest.raises(SlotError, match="paired dependency wt1 is dirty"):
        controller.acquire(1, client="codex", base_ref="main")
    assert protected.exists()
    assert controller.inventory.lease(1, required=False) is None


def test_active_downstream_gate_rechecks_dependency_pin(downstream_repo) -> None:
    controller, _, _, _ = downstream_repo
    controller.build()
    prepare(controller, 3)
    gate = LeaseGate(controller.inventory, 3)
    client, supplied_hash = gate.identify(None, "codex")
    call = json.dumps(
        {
            "jsonrpc": "2.0",
            "id": 1,
            "method": "tools/call",
            "params": {"name": "lean_goal"},
        }
    ).encode()
    gate.authorize(client, supplied_hash, call)
    paired = controller.inventory.paired_inventory()
    assert paired is not None
    (paired.worktree(3) / "changed.lean").write_text("changed\n")
    with pytest.raises(SlotError, match="paired dependency became dirty"):
        gate.authorize(client, supplied_hash, call)


def test_downstream_lakefile_path_must_match_pair_inventory(downstream_repo) -> None:
    controller, _, repo, _ = downstream_repo
    lakefile = repo / "lean" / "lakefile.toml"
    lakefile.write_text(
        lakefile.read_text().replace("../../primary/lean", "../wrong/lean")
    )
    run(repo, "git", "add", "lean/lakefile.toml")
    run(repo, "git", "commit", "-m", "misdirect dependency")
    with pytest.raises(SlotError, match="Lake dependency path mismatch"):
        controller.acquire(2, client="codex", base_ref="main")


def test_foreign_repository_cannot_reclaim_stale_lease(
    downstream_repo, isolated_process_observations, monkeypatch: pytest.MonkeyPatch
) -> None:
    controller, public_controller, _, _ = downstream_repo
    monkeypatch.setenv("LEAN_SLOT_OWNER_PID", "999999")
    isolated_process_observations.add(999999, "verified foreign fixture owner")
    controller.acquire(2, client="codex", base_ref="main")
    isolated_process_observations.remove(999999)
    with pytest.raises(SlotError, match="repository-role mismatch"):
        public_controller.reclaim(2)
    assert controller.inventory.lease(2)["repo_role"] == "downstream"


def test_trusted_local_session_environment_exports_only_shared_state_root(
    slot_repo,
) -> None:
    controller, _, _ = slot_repo
    environment = controller.session_environment(client="codex")
    assert "LEAN_SLOT_CODEX_TOKEN" not in environment
    assert (
        f"export LEAN_SLOT_STATE_DIR={controller.inventory.state_root}" in environment
    )


def test_bearer_session_environment_exports_token(slot_repo) -> None:
    controller, _, _ = slot_repo
    controller.inventory.raw["server"]["client_auth"] = "bearer"
    environment = controller.session_environment(client="codex")
    assert "export LEAN_SLOT_CODEX_TOKEN=" in environment
    assert (
        f"export LEAN_SLOT_STATE_DIR={controller.inventory.state_root}" in environment
    )


def test_backend_pair_handoff_is_ordered_and_rolls_back(downstream_repo, isolated_process_observations) -> None:
    from tests.test_lean_lifecycle_observation import owned
    controller, public_controller, _, _ = downstream_repo
    host = isolated_process_observations
    target, counterpart = Supervisor(controller.inventory), Supervisor(public_controller.inventory)
    owned(counterpart, host, "proxy", 2, 811202)
    owned(counterpart, host, "backend", 2, 811302)
    events = []
    with target.activating_from(2, counterpart):
        assert target.process_state("backend", 2) == counterpart.process_state("backend", 2) == "down"
        assert host.signals == [(811302, signal.SIGTERM)]
        events.append("cache-transition")
    assert events == ["cache-transition"]
    assert target.process_state("backend", 2) == "running"
    target.restore_counterpart(2, counterpart)
    assert target.process_state("backend", 2) == "down" and counterpart.process_state("backend", 2) == "running"
    with pytest.raises(RuntimeError, match="copy failed"):
        with target.activating_from(2, counterpart):
            assert counterpart.process_state("backend", 2) == "down"
            raise RuntimeError("copy failed")
    assert target.process_state("backend", 2) == "down" and counterpart.process_state("backend", 2) == "running"


def test_doctor_json_shape_is_stable(slot_repo) -> None:
    controller, _, _ = slot_repo
    first = controller.doctor()
    second = controller.doctor()
    assert first == second
    assert first["schema_version"] == 1
    assert {item["name"] for item in first["checks"]} >= {
        "wt1.identity",
        "wt1.clean",
        "wt1.integrated",
        "build_epoch",
        "config.repo",
        "config.claude",
        "heavy_backend_limit",
    }


def test_doctor_fails_closed_for_quarantine_and_unabsorbed_commits(slot_repo) -> None:
    controller, _, worktrees = slot_repo
    protected = worktrees[0] / "protected.lean"
    protected.write_text("keep\n")
    with pytest.raises(SlotError, match="quarantined"):
        controller.acquire(1, client="codex", base_ref="main")
    first = {item["name"]: item for item in controller.doctor()["checks"]}
    assert not first["wt1.lease"]["ok"]
    assert "QUARANTINED" in first["wt1.lease"]["detail"]

    commit(worktrees[1], "unabsorbed.txt", "keep\n")
    second = {item["name"]: item for item in controller.doctor()["checks"]}
    assert not second["wt2.integrated"]["ok"]
    assert "1 unabsorbed commit" in second["wt2.integrated"]["detail"]


# --- ADR-008 Phase 4: Claude MCP configuration (spec P4-1..P4-3) ---------------------


#: The shape the production artifact actually has: the per-slot stdio servers this block
#: replaces, interleaved with servers owned by other projects that must survive untouched.
def _workspace_mcp(tmp_path: Path) -> Path:
    path = tmp_path / ".mcp.json"
    path.write_text(
        json.dumps(
            {
                "mcpServers": {
                    "lean-lsp": {"command": "uvx", "args": ["--lean-project-path", "/x/lean"]},
                    "lean-lsp-other": {"command": "uvx", "args": ["--lean-project-path", "/y"]},
                    "lean-lsp-wt1": {"command": "uvx", "args": ["--repl"]},
                    "lean-lsp-wt2": {"command": "uvx", "args": ["--repl"]},
                    "lean-lsp-wt3": {"command": "uvx", "args": ["--repl"]},
                    "other-client": {"command": "other"},
                }
            },
            indent=2,
        )
        + "\n"
    )
    return path


def test_claude_render_swaps_stdio_slots_for_lease_gated_http(slot_repo, tmp_path) -> None:
    controller, _, _ = slot_repo
    target = _workspace_mcp(tmp_path)
    controller.render_claude_config()
    servers = json.loads(target.read_text())["mcpServers"]
    assert not [key for key in servers if key.startswith("lean-lsp-wt")]
    for number in (1, 2, 3):
        entry = servers[f"test_wt{number}"]
        assert entry["type"] == "http"
        # The query parameter is what `proxy.py` matches against the lease's own client
        # field; without it trusted-local dispatch fails closed.
        assert entry["url"] == f"http://127.0.0.1:{29000 + number}/mcp?client=claude"


def test_claude_render_leaves_other_projects_servers_and_their_order_alone(
    slot_repo, tmp_path
) -> None:
    controller, _, _ = slot_repo
    target = _workspace_mcp(tmp_path)
    before = json.loads(target.read_text())["mcpServers"]
    unrelated = {k: v for k, v in before.items() if not k.startswith("lean-lsp-wt")}
    controller.render_claude_config()
    after = json.loads(target.read_text())["mcpServers"]
    assert {k: v for k, v in after.items() if k in unrelated} == unrelated
    assert [k for k in after if k in unrelated] == list(unrelated)


def test_claude_render_ports_come_from_the_inventory_not_a_second_list(
    slot_repo, tmp_path
) -> None:
    controller, repo, _ = slot_repo
    target = _workspace_mcp(tmp_path)
    path = repo / "config" / "lean-slots.public.json"
    inventory = json.loads(path.read_text())
    inventory["slots"]["2"]["proxy_port"] = 29777
    path.write_text(json.dumps(inventory))
    moved = Controller(Inventory.load(path))
    moved.render_claude_config()
    servers = json.loads(target.read_text())["mcpServers"]
    assert servers["test_wt2"]["url"].startswith("http://127.0.0.1:29777/")


def test_a_drifted_port_in_the_live_file_is_reported_not_overwritten(
    slot_repo, tmp_path
) -> None:
    controller, _, _ = slot_repo
    target = _workspace_mcp(tmp_path)
    controller.render_claude_config()
    document = json.loads(target.read_text())
    document["mcpServers"]["test_wt2"]["url"] = "http://127.0.0.1:29999/mcp?client=claude"
    target.write_text(json.dumps(document, indent=2))
    check = {item["name"]: item for item in controller.doctor()["checks"]}["config.claude"]
    assert not check["ok"]
    assert check["detail"].startswith("drifted")
    assert "test_wt2" in check["detail"]
    # Reporting, never writing: doctor left the operator's file exactly as it found it.
    assert json.loads(target.read_text()) == document


def test_a_missing_slot_entry_is_partial_not_current(slot_repo, tmp_path) -> None:
    controller, _, _ = slot_repo
    target = _workspace_mcp(tmp_path)
    controller.render_claude_config()
    document = json.loads(target.read_text())
    del document["mcpServers"]["test_wt3"]
    target.write_text(json.dumps(document, indent=2))
    check = {item["name"]: item for item in controller.doctor()["checks"]}["config.claude"]
    assert not check["ok"]
    assert check["detail"].startswith("partial")
    assert "test_wt3" in check["detail"]


def test_a_legacy_stdio_slot_left_beside_the_http_block_is_drift(slot_repo, tmp_path) -> None:
    """Coexistence is the process multiplication this change exists to remove."""
    controller, _, _ = slot_repo
    target = _workspace_mcp(tmp_path)
    controller.render_claude_config()
    document = json.loads(target.read_text())
    document["mcpServers"]["lean-lsp-wt1"] = {"command": "uvx", "args": ["--repl"]}
    target.write_text(json.dumps(document, indent=2))
    check = {item["name"]: item for item in controller.doctor()["checks"]}["config.claude"]
    assert not check["ok"]
    assert "lean-lsp-wt1" in check["detail"]


def test_pre_activation_and_rolled_back_states_are_healthy_not_broken(
    slot_repo, tmp_path
) -> None:
    controller, _, _ = slot_repo
    target = _workspace_mcp(tmp_path)
    pre = json.loads(target.read_text())
    before = {item["name"]: item for item in controller.doctor()["checks"]}["config.claude"]
    assert before["ok"] and before["detail"].startswith("not activated")

    controller.render_claude_config()
    controller.render_claude_config(rollback=True)
    assert json.loads(target.read_text())["mcpServers"] == pre["mcpServers"]
    after = {item["name"]: item for item in controller.doctor()["checks"]}["config.claude"]
    assert after["ok"] and after["detail"].startswith("not activated")


def test_a_second_render_cannot_destroy_the_pre_activation_snapshot(
    slot_repo, tmp_path
) -> None:
    """Otherwise the snapshot records an already-activated block and rollback is a no-op."""
    controller, _, _ = slot_repo
    target = _workspace_mcp(tmp_path)
    pre = json.loads(target.read_text())["mcpServers"]
    controller.render_claude_config()
    controller.render_claude_config()
    from scripts.lean_slots import claude_config

    snapshot = json.loads(claude_config.rollback_path(controller.inventory).read_text())
    assert snapshot == pre


def test_render_refuses_an_absolute_claude_config_path(slot_repo, tmp_path) -> None:
    controller, repo, _ = slot_repo
    path = repo / "config" / "lean-slots.public.json"
    inventory = json.loads(path.read_text())
    inventory["config"] = {"claude_mcp": str(tmp_path / ".mcp.json")}
    path.write_text(json.dumps(inventory))
    with pytest.raises(SlotError, match="workspace-relative"):
        Controller(Inventory.load(path)).render_claude_config()


def test_the_live_workspace_mcp_config_classifies_without_raising() -> None:
    """Production-seeded: run the classifier over the operator's real file, if present."""
    from scripts.lean_slots import claude_config

    inventory = Inventory.load()
    live = Controller(inventory).claude_mcp_path()
    if not live.exists():
        pytest.skip("no workspace Claude MCP configuration on this host")
    state, _ = claude_config.block_state(json.loads(live.read_text()), inventory)
    assert state in {"current", "not activated", "partial", "drifted"}


def test_a_session_owned_lease_survives_separate_cli_invocations(
    slot_repo, monkeypatch
) -> None:
    """A lease outlives the shell that acquired it, or every second command fails closed."""
    controller, repo, _ = slot_repo
    monkeypatch.delenv("LEAN_SLOT_OWNER_PID", raising=False)
    monkeypatch.setenv("CLAUDE_CODE_SESSION_ID", "session-abc")
    lease = controller.acquire(1, client="claude", base_ref="main")
    assert lease["owner_kind"] == "session"
    # A distinct invocation: same session, different parent process.
    reloaded = Controller(Inventory.load(repo / "config" / "lean-slots.public.json"))
    assert reloaded.heartbeat(1)["slot"] == 1


def test_a_different_session_cannot_drive_another_sessions_lease(
    slot_repo, monkeypatch
) -> None:
    controller, repo, _ = slot_repo
    monkeypatch.delenv("LEAN_SLOT_OWNER_PID", raising=False)
    monkeypatch.setenv("CLAUDE_CODE_SESSION_ID", "session-abc")
    controller.acquire(1, client="claude", base_ref="main")
    monkeypatch.setenv("CLAUDE_CODE_SESSION_ID", "session-xyz")
    other = Controller(Inventory.load(repo / "config" / "lean-slots.public.json"))
    with pytest.raises(SlotError, match="owner"):
        other.heartbeat(1)


def test_the_neutral_owner_variable_outranks_the_client_specific_ones(
    slot_repo, monkeypatch
) -> None:
    controller, _, _ = slot_repo
    monkeypatch.delenv("LEAN_SLOT_OWNER_PID", raising=False)
    monkeypatch.setenv("CODEX_THREAD_ID", "codex-thread")
    monkeypatch.setenv("CLAUDE_CODE_SESSION_ID", "claude-session")
    monkeypatch.setenv("LEAN_SLOT_OWNER_SESSION", "explicit-owner")
    import hashlib

    lease = controller.acquire(1, client="claude", base_ref="main")
    assert (
        lease["owner_session_hash"]
        == hashlib.sha256(b"explicit-owner").hexdigest()
    )


def test_activate_rollback_reactivate_preserves_the_original_snapshot(
    slot_repo, tmp_path
) -> None:
    """The rollback path is ADR-008 item 7 — retaining legacy stdio as recoverable state.

    render->render is guarded elsewhere; this is the sequence that actually breaks write-once,
    because after a rollback the file legitimately holds the legacy block again and a naive
    snapshot-on-render would rewrite it, silently making the NEXT rollback restore an
    already-activated block instead.
    """
    controller, _, _ = slot_repo
    target = _workspace_mcp(tmp_path)
    pre = json.loads(target.read_text())["mcpServers"]

    controller.render_claude_config()
    controller.render_claude_config(rollback=True)
    assert json.loads(target.read_text())["mcpServers"] == pre
    controller.render_claude_config()

    servers = json.loads(target.read_text())["mcpServers"]
    assert "test_wt1" in servers and "lean-lsp-wt1" not in servers

    from scripts.lean_slots import claude_config

    snapshot = json.loads(claude_config.rollback_path(controller.inventory).read_text())
    assert snapshot == pre, (
        "the snapshot no longer holds the pre-activation block, so a further rollback "
        "would restore an activated config and the legacy path would be unrecoverable")


# --- ADR-008 Phase 4: declared host kernel limits (portable across machines) -----------


def _with_limits(repo: Path, entries: list) -> Controller:
    path = repo / "config" / "lean-slots.public.json"
    inventory = json.loads(path.read_text())
    inventory["host_limits"] = entries
    path.write_text(json.dumps(inventory))
    return Controller(Inventory.load(path))


def test_a_knob_below_its_declared_minimum_fails_with_a_runnable_remedy(
    slot_repo, monkeypatch
) -> None:
    from scripts.lean_slots import host_limits

    controller, repo, _ = slot_repo
    monkeypatch.delenv(host_limits.SKIP_ENV, raising=False)
    monkeypatch.setattr(platform := __import__("platform"), "system", lambda: "TestOS")
    monkeypatch.setattr(host_limits, "read_sysctl", lambda name: 1000)
    moved = _with_limits(repo, [{"platform": "TestOS", "sysctl": "test.knob",
                                 "minimum": 5000, "remedy": "sudo sysctl -w test.knob=5000"}])
    name, ok, detail = host_limits.evaluate(moved.inventory)[0]
    assert name == "host_limit.test.knob" and not ok
    assert "1000" in detail and "5000" in detail
    assert "sudo sysctl -w test.knob=5000" in detail
    assert "lost on reboot" in detail


def test_a_remedy_that_drifted_from_the_minimum_is_replaced_not_printed(
    slot_repo, monkeypatch
) -> None:
    """A remedy naming a stale value would send the operator to run a command that
    leaves the check red — the exact defect the live output exposed."""
    from scripts.lean_slots import host_limits

    controller, repo, _ = slot_repo
    monkeypatch.delenv(host_limits.SKIP_ENV, raising=False)
    monkeypatch.setattr(__import__("platform"), "system", lambda: "TestOS")
    monkeypatch.setattr(host_limits, "read_sysctl", lambda name: 1000)
    moved = _with_limits(repo, [{"platform": "TestOS", "sysctl": "test.knob",
                                 "minimum": 9999,
                                 "remedy": "sudo sysctl -w test.knob=5000"}])
    _, ok, detail = host_limits.evaluate(moved.inventory)[0]
    assert not ok
    assert "test.knob=9999" in detail
    assert "test.knob=5000" not in detail


def test_a_platform_with_no_declared_limit_passes(slot_repo, monkeypatch) -> None:
    """A public repo must not fail a clone on a machine whose kernel has no such knob."""
    from scripts.lean_slots import host_limits

    controller, repo, _ = slot_repo
    monkeypatch.delenv(host_limits.SKIP_ENV, raising=False)
    monkeypatch.setattr(__import__("platform"), "system", lambda: "Linux")
    moved = _with_limits(repo, [{"platform": "Darwin", "sysctl": "kern.maxvnodes",
                                 "minimum": 786432}])
    name, ok, detail = host_limits.evaluate(moved.inventory)[0]
    assert name == "host_limits" and ok
    assert "Linux" in detail


def test_a_knob_this_kernel_does_not_expose_passes(slot_repo, monkeypatch) -> None:
    """Absent is not misconfigured."""
    from scripts.lean_slots import host_limits

    controller, repo, _ = slot_repo
    monkeypatch.delenv(host_limits.SKIP_ENV, raising=False)
    monkeypatch.setattr(__import__("platform"), "system", lambda: "TestOS")
    monkeypatch.setattr(host_limits, "read_sysctl", lambda name: None)
    moved = _with_limits(repo, [{"platform": "TestOS", "sysctl": "test.knob",
                                 "minimum": 5000}])
    _, ok, detail = host_limits.evaluate(moved.inventory)[0]
    assert ok and "not exposed" in detail


def test_the_skip_variable_opts_a_machine_out_without_a_repo_diff(
    slot_repo, monkeypatch
) -> None:
    from scripts.lean_slots import host_limits

    controller, repo, _ = slot_repo
    monkeypatch.setenv(host_limits.SKIP_ENV, "1")
    monkeypatch.setattr(__import__("platform"), "system", lambda: "TestOS")
    monkeypatch.setattr(host_limits, "read_sysctl", lambda name: 1)
    moved = _with_limits(repo, [{"platform": "TestOS", "sysctl": "test.knob",
                                 "minimum": 5000}])
    name, ok, detail = host_limits.evaluate(moved.inventory)[0]
    assert name == "host_limits" and ok and host_limits.SKIP_ENV in detail


def test_doctor_surfaces_the_host_limit_check(slot_repo) -> None:
    controller, _, _ = slot_repo
    names = {c["name"] for c in controller.doctor()["checks"]}
    assert any(n == "host_limits" or n.startswith("host_limit.") for n in names)


def test_the_shipped_public_inventory_declares_a_darwin_vnode_floor() -> None:
    """The committed default must actually carry the limit this ADR added."""
    from scripts.lean_slots import host_limits

    inventory = Inventory.load()
    entries = [e for e in (inventory.raw.get("host_limits") or [])
               if e.get("platform") == "Darwin"]
    assert entries, "public inventory lost its Darwin host limit"
    entry = entries[0]
    assert entry["sysctl"] == "kern.maxvnodes"
    assert int(entry["minimum"]) >= 786432
    assert str(entry["minimum"]) in entry.get("remedy", "")


# --- ADR-008 Phase 4: leased backends are reclaimed on every lease-exit path ------------


def _leased(repo: Path) -> Controller:
    path = repo / "config" / "lean-slots.public.json"
    inventory = json.loads(path.read_text())
    inventory["server"]["backend_policy"] = "leased"
    path.write_text(json.dumps(inventory))
    # `build()` refuses a dirty primary checkout, so the policy switch must be committed
    # like any other inventory change.
    run(repo, "git", "add", "config/lean-slots.public.json")
    run(repo, "git", "commit", "-m", "switch to leased backends")
    return Controller(Inventory.load(path))


def test_a_leased_slot_expects_no_backend_once_released(slot_repo) -> None:
    controller, repo, _ = slot_repo
    leased = _leased(repo)
    leased.build()
    assert not leased.inventory.backend_expected(1)
    prepare(leased, 1, client="claude")
    assert leased.inventory.backend_expected(1)
    leased.release(1)
    assert not leased.inventory.backend_expected(1)


def test_release_reconciles_the_backend_after_the_lease_is_gone(
    slot_repo, monkeypatch
) -> None:
    """Ordering is the whole point: `backend_expected` reads the lease, so a reconcile
    that ran before the unlink would still see the slot leased and keep ~4.4 GB warm."""
    controller, repo, _ = slot_repo
    leased = _leased(repo)
    leased.build()
    prepare(leased, 1, client="claude")
    seen: list[tuple[str, bool]] = []
    monkeypatch.delenv("LEAN_SLOT_SKIP_SUPERVISOR", raising=False)

    import scripts.lean_slots.supervisor as sup

    class FakeSupervisor(sup.Supervisor):
        def stop_backend(self, number):
            seen.append(("stop", leased.inventory.lease_path(number).exists()))

    monkeypatch.setattr(sup, "Supervisor", FakeSupervisor)
    leased.release(1)
    assert seen == [("stop", False)], (
        "the backend must be stopped exactly once, AFTER the lease file is removed")


def test_a_default_policy_slot_keeps_its_backend_on_release(slot_repo, monkeypatch) -> None:
    """`default` must remain a no-op — this change reclaims memory, it does not
    quietly change the other policy's behaviour."""
    controller, repo, _ = slot_repo
    controller.build()
    prepare(controller, 1, client="claude")
    calls: list[int] = []
    monkeypatch.delenv("LEAN_SLOT_SKIP_SUPERVISOR", raising=False)

    import scripts.lean_slots.supervisor as sup

    class FakeSupervisor(sup.Supervisor):
        def stop_backend(self, number):
            calls.append(number)

    monkeypatch.setattr(sup, "Supervisor", FakeSupervisor)
    controller.release(1)
    assert calls == []


def test_a_supervisor_failure_never_fails_an_already_successful_release(
    slot_repo, monkeypatch, capsys
) -> None:
    controller, repo, _ = slot_repo
    leased = _leased(repo)
    leased.build()
    prepare(leased, 1, client="claude")
    monkeypatch.delenv("LEAN_SLOT_SKIP_SUPERVISOR", raising=False)

    import scripts.lean_slots.supervisor as sup

    class ExplodingSupervisor(sup.Supervisor):
        def stop_backend(self, number):
            raise SlotError("supervisor is wedged")

    monkeypatch.setattr(sup, "Supervisor", ExplodingSupervisor)
    leased.release(1)  # must not raise
    assert not leased.inventory.lease_path(1).exists()
    assert "could not be stopped" in capsys.readouterr().err


def test_the_shipped_public_inventory_reclaims_idle_backends() -> None:
    inventory = Inventory.load()
    assert inventory.raw["server"].get("backend_policy") == "leased"


# --- ADR-008: a backendless slot must still complete the MCP handshake ------------------


def test_initialize_is_answered_when_the_slot_has_no_backend() -> None:
    """Connect-time handshake must not fail for a DISPATCH-time resource.

    Regression: `leased` backends made every unleased endpoint answer 503 to `initialize`.
    codex-cli 0.145.0 (rmcp) treats that as a fatal transport error and the whole session
    dies with no answer, `required = false` notwithstanding.
    """
    from scripts.lean_slots.proxy import offline_handshake

    reply = offline_handshake([{
        "jsonrpc": "2.0", "id": 7, "method": "initialize",
        "params": {"protocolVersion": "2025-06-18"}}])
    assert reply is not None
    assert reply["id"] == 7
    assert reply["result"]["protocolVersion"] == "2025-06-18"
    assert "no active lease" in reply["result"]["instructions"]


def test_a_backendless_slot_advertises_no_tools() -> None:
    """An empty tool list is what keeps the offline handshake from weakening the gate."""
    from scripts.lean_slots.proxy import offline_handshake

    reply = offline_handshake([{"jsonrpc": "2.0", "id": 1, "method": "tools/list"}])
    assert reply["result"]["tools"] == []


def test_the_offline_reply_never_covers_tool_dispatch() -> None:
    """`tools/call` must fall through to the 503/lease-gate path, never be answered here."""
    from scripts.lean_slots.proxy import offline_handshake

    for method in ("tools/call", "resources/read", "prompts/get"):
        assert offline_handshake([{"jsonrpc": "2.0", "id": 1, "method": method}]) is None


def test_notifications_are_recognised_so_they_take_202_not_503() -> None:
    from scripts.lean_slots.proxy import is_notification_only

    assert is_notification_only([{"jsonrpc": "2.0", "method": "notifications/initialized"}])
    assert not is_notification_only([{"jsonrpc": "2.0", "id": 1, "method": "initialize"}])
    assert not is_notification_only([])


def test_a_lease_is_disk_state_so_it_survives_an_endpoint_restart(slot_repo) -> None:
    """Gate test 3: the proxy holds no lease state, so a restart preserves rather than
    reacquires. Pinned because moving lease state into the proxy would silently turn a
    transparent reconnect into a lost lease."""
    controller, _, _ = slot_repo
    controller.build()
    prepare(controller, 1, client="claude")
    before = controller.inventory.lease(1)
    # A restart replaces processes; it must not touch the lease record at all.
    reloaded = Controller(Inventory.load(controller.inventory.source))
    after = reloaded.inventory.lease(1)
    assert after == before, "restarting the endpoints must not alter the lease"
    assert after["state"] == "ACTIVE"
    # Owner identity is what makes it a *preserved* lease rather than a reacquired one.
    owner_key = (
        "owner_session_hash" if after.get("owner_kind") == "session" else "owner_pid"
    )
    assert after[owner_key] == before[owner_key]


def test_the_backend_command_pins_the_slot_worktree_as_project_root(slot_repo) -> None:
    """`--lean-project-path` must name THIS slot's lean dir, never the primary checkout.

    A same-content comparison cannot catch a wrong root: `prepare` resets the slot to the
    base, so slot and primary hold identical files and both resolve every read.
    """
    controller, repo, worktrees = slot_repo
    command = Supervisor(controller.inventory).backend_command(1)
    assert "--lean-project-path" in command
    root = Path(command[command.index("--lean-project-path") + 1]).resolve()
    assert root == (worktrees[0] / "lean").resolve()
    assert root != (repo / "lean").resolve()


def test_quarantining_does_not_reset_the_clock_reclaim_reads(slot_repo) -> None:
    """A failed reclaim must not make the next reclaim fail too.

    `heartbeat_at` means "the owner is alive" and `reclaim` gates on it. When the
    CONTROLLER writes a quarantine, refreshing it would reset the staleness clock, so a
    genuinely stale lease could never be reclaimed by retry — each attempt resets what the
    next one reads. Observed on a three-week-old lease: one failed reclaim rewrote
    `heartbeat_at` to now, and the retry was refused for staleness instead of the real cause.
    """
    controller, _, _ = slot_repo
    lease = controller.acquire(1, client="claude", base_ref="main")
    _ = lease["heartbeat_at"]
    lease["heartbeat_at"] = "2026-07-23T19:32:03Z"          # a genuinely stale owner
    controller.inventory.save_lease(1, lease, touch_heartbeat=False)

    stale = controller.inventory.lease(1)
    assert stale["heartbeat_at"] == "2026-07-23T19:32:03Z"

    controller._quarantine(1, stale, "simulated audit failure")
    after = controller.inventory.lease(1)
    assert after["state"] == "QUARANTINED"
    assert after["heartbeat_at"] == "2026-07-23T19:32:03Z", (
        "quarantining refreshed the heartbeat, so retrying reclaim can never succeed")
    # The quarantine still records ITS own time — suppressing the heartbeat must not
    # suppress the audit trail. The audit stamp advances while the liveness stamp does not.
    assert after["quarantined_at"] > after["heartbeat_at"]


def test_an_owner_heartbeat_still_refreshes(slot_repo) -> None:
    """The fix must not disable the real heartbeat — that would let live leases expire."""
    controller, _, _ = slot_repo
    lease = controller.acquire(1, client="claude", base_ref="main")
    lease["heartbeat_at"] = "2026-07-23T19:32:03Z"
    controller.inventory.save_lease(1, lease, touch_heartbeat=False)
    refreshed = controller.heartbeat(1)
    assert refreshed["heartbeat_at"] != "2026-07-23T19:32:03Z"


# --- Absorption is containment in the INTEGRATION ref, not in a recorded SHA ------------


def test_a_slot_whose_base_branch_was_deleted_is_still_freeable(
    slot_repo, monkeypatch
) -> None:
    """The wt2 trap, 2026-08-14: lease a feature branch, merge it, delete it.

    Every controller verb was closed and the only exit was deleting runtime state by hand —
    which S-C tells operators not to do. Ordinary hygiene must not create an unrecoverable
    state.
    """
    controller, repo, worktrees = slot_repo
    run(repo, "git", "branch", "feature/tmp-base", "main")
    controller.build()
    lease = controller.acquire(1, client="claude", base_ref="feature/tmp-base")
    assert lease["base_ref"] == "feature/tmp-base"
    # The slot's work lands on main the way `absorb` would, then the branch is deleted.
    run(repo, "git", "branch", "-D", "feature/tmp-base")

    worktree = worktrees[0]
    absorbed, why = controller._is_absorbed(worktree, controller.inventory.lease(1))
    assert absorbed, f"a slot contained in main must be freeable; got: {why}"
    assert "integration ref" in why
    controller.release(1)
    assert controller.inventory.lease(1, required=False) is None


def test_real_unabsorbed_work_still_blocks(slot_repo) -> None:
    """The audit must stay fail-closed — this is what stops work being lost."""
    controller, repo, worktrees = slot_repo
    controller.build()
    prepare(controller, 1, client="claude")
    commit(worktrees[0], "unmerged.txt", "work nobody has merged\n")
    absorbed, why = controller._is_absorbed(
        worktrees[0], controller.inventory.lease(1)
    )
    assert not absorbed
    assert "merge or rescue" in why
    with pytest.raises(SlotError, match="quarantined"):
        controller.release(1)


def test_an_unresolvable_ref_is_not_evidence_of_absorption(slot_repo) -> None:
    """Fail-closed: if NOTHING resolves, the answer is 'not safe', never 'sure, go ahead'."""
    controller, repo, worktrees = slot_repo
    controller.build()
    prepare(controller, 1, client="claude")
    commit(worktrees[0], "unmerged.txt", "work nobody has merged\n")
    lease = controller.inventory.lease(1)
    lease["base_ref"] = "refs/heads/does-not-exist"
    absorbed, _ = controller._is_absorbed(worktrees[0], lease)
    assert not absorbed


def test_the_integration_ref_is_configurable(slot_repo) -> None:
    controller, repo, _ = slot_repo
    path = repo / "config" / "lean-slots.public.json"
    inventory = json.loads(path.read_text())
    inventory["integration_ref"] = "trunk"
    path.write_text(json.dumps(inventory))
    run(repo, "git", "branch", "trunk", "main")
    moved = Controller(Inventory.load(path))
    assert moved.inventory.raw["integration_ref"] == "trunk"
    _, why = moved._is_absorbed(
        moved.inventory.worktree(1),
        {"base_ref": "does-not-exist"},
    )
    assert "trunk" in why


def test_a_stale_proxy_is_reported_differently_from_a_dead_one(slot_repo, isolated_process_observations) -> None:
    """Actual stale identity/fingerprint and confirmed exit have different diagnoses."""
    from tests.test_lean_lifecycle_observation import owned

    controller, _, _ = slot_repo
    host = isolated_process_observations
    supervisor = Supervisor(controller.inventory)
    record = owned(supervisor, host, "proxy", 1, 829101, stale=True)
    original = record.read_bytes()
    detail = {c["name"]: c for c in controller.doctor()["checks"]}["wt1.endpoint"]["detail"]
    assert "stale" in detail and "drained root reload" in detail and "ALIVE" in detail
    host.remove(829101)
    detail = {c["name"]: c for c in controller.doctor()["checks"]}["wt1.endpoint"]["detail"]
    assert "proxy=down" in detail and "ALIVE" not in detail
    assert record.read_bytes() == original  # Read-only diagnostic never cleans metadata.


def test_reclaim_routes_an_owner_to_release(slot_repo) -> None:
    """Minor #3: reclaim reads like THE recovery verb; it is the one for a dead owner."""
    controller, repo, _ = slot_repo
    path = repo / "config" / "lean-slots.public.json"
    inventory = json.loads(path.read_text())
    inventory["lease_timeout_seconds"] = 900          # the shipped value, not the fixture's 0
    path.write_text(json.dumps(inventory))
    moved = Controller(Inventory.load(path))
    moved.acquire(1, client="claude", base_ref="main")
    with pytest.raises(SlotError, match=r"release --slot 1"):
        moved.reclaim(1, confirm_owner_gone=True)


# --- The advertised tool list survives an idle backend (session-start registration) -----


def _write_cache(controller, tools, key=None):
    from scripts.lean_slots.state import tool_cache_path, tool_list_key
    atomic_json(
        tool_cache_path(controller.inventory.state_root),
        {
            "key": key or tool_list_key(controller.inventory.raw["server"]),
            "tools": tools,
            "harvested_at": "2026-08-14T00:00:00Z",
        },
    )


def test_an_idle_slot_advertises_the_cached_tools(slot_repo) -> None:
    """MCP tools register at SESSION START. A slot whose backend is idle then would
    otherwise contribute zero tools to that session forever, no matter what is leased
    afterwards — which makes a leased-backend deployment undispatchable."""
    from scripts.lean_slots.proxy import cached_tool_list, offline_handshake

    controller, _, _ = slot_repo
    _write_cache(controller, [{"name": "lean_goal"}, {"name": "lean_verify"}])
    tools = cached_tool_list(controller.inventory)
    assert [t["name"] for t in tools] == ["lean_goal", "lean_verify"]
    reply = offline_handshake([{"jsonrpc": "2.0", "id": 1, "method": "tools/list"}], tools)
    assert len(reply["result"]["tools"]) == 2


def test_a_cache_from_a_different_server_build_is_ignored(slot_repo) -> None:
    """Bump the pinned server or edit disabled_tools and the cache must not be trusted."""
    from scripts.lean_slots.proxy import cached_tool_list

    controller, _, _ = slot_repo
    _write_cache(controller, [{"name": "lean_goal"}], key="a-different-build")
    assert cached_tool_list(controller.inventory) == []


def test_editing_disabled_tools_invalidates_the_cache(slot_repo) -> None:
    from scripts.lean_slots.proxy import cached_tool_list

    controller, repo, _ = slot_repo
    _write_cache(controller, [{"name": "lean_goal"}])
    assert cached_tool_list(controller.inventory) != []
    path = repo / "config" / "lean-slots.public.json"
    inventory = json.loads(path.read_text())
    inventory["server"]["disabled_tools"] = ["lean_build", "lean_run_code"]
    path.write_text(json.dumps(inventory))
    assert cached_tool_list(Inventory.load(path)) == []


def test_the_cache_key_ignores_which_slot_is_serving(slot_repo) -> None:
    """One list serves all three slots: the project path changes which PROJECT a backend
    serves, never which TOOLS exist. Keying on the per-slot fingerprint would defeat it."""
    from scripts.lean_slots.state import tool_list_key

    controller, _, _ = slot_repo
    server = dict(controller.inventory.raw["server"])
    first = tool_list_key(server)
    assert first == tool_list_key(dict(server))
    server["command"] = ["different-binary"]
    assert tool_list_key(server) != first


def test_a_missing_cache_yields_no_tools_rather_than_an_error(slot_repo) -> None:
    from scripts.lean_slots.proxy import cached_tool_list

    controller, _, _ = slot_repo
    assert cached_tool_list(controller.inventory) == []


# ── ADR-008 S-Q — the proxy owns the client-facing MCP session ────────────────
#
# ⚠️ THESE DRIVE THE REAL HTTP HANDLER, NOT `offline_handshake`.
# The pre-existing handshake tests call `offline_handshake` as a pure function and
# all passed while the defect was live, because the defect was never in that
# function — it was in the handler that calls it, which sent the reply with no
# `Mcp-Session-Id` header. Testing the seam is the whole point (CHECK_AUTHORING
# _GUIDE §2.5): a unit test one layer in from the defect cannot see it.


def _serve_proxy(inventory, number: int):
    """Construct the real handler; transport is isolated in-process HTTP byte streams."""
    from scripts.lean_slots.proxy import make_handler
    return make_handler(inventory, number), 0, lambda: None


def _post(
    host, port: int, payload: dict | None, session: str | None = None, *,
    method: str = "POST", path: str = "/mcp?client=claude",
    fields: list[tuple[str, str]] | None = None, raw_fields: bytes = b"",
    raw_output: list[bytes] | None = None,
):
    """Drive the actual Handler with ordered fields and optional exact wire bytes.

    Existing callers retain their response tuple. ``None`` omits the session;
    an empty string deliberately sends a present-empty field. Raw output is
    captured before HTTPResponse can normalize a defective header.
    """
    import io
    import http.client
    body = json.dumps(payload).encode() if payload is not None else b""
    headers = [("Content-Type", "application/json"),
               ("Accept", "application/json, text/event-stream"),
               ("Content-Length", str(len(body))), ("Connection", "close")]
    if session is not None:
        headers.append(("Mcp-Session-Id", session))
    headers.extend(fields or [])
    request = (
        f"{method} {path} HTTP/1.1\r\n".encode("ascii")
        + b"".join(f"{key}: {value}\r\n".encode("latin-1") for key, value in headers)
        + raw_fields + b"\r\n" + body
    )
    class Wire:
        def __init__(self, incoming):
            self.incoming, self.outgoing = incoming, bytearray()
        def makefile(self, mode, *args, **kwargs):
            return io.BytesIO(self.incoming)
        def sendall(self, data):
            self.outgoing.extend(data)
    wire = Wire(request)
    host(wire, ("127.0.0.1", 0), SimpleNamespace(server_name="isolated", server_port=0))
    if raw_output is not None:
        raw_output.append(bytes(wire.outgoing))
    response = http.client.HTTPResponse(Wire(bytes(wire.outgoing)), method=method)
    response.begin()
    return response.status, {key.lower(): value for key, value in response.getheaders()}, response.read()


def test_an_idle_slot_mints_a_session_on_initialize(slot_repo) -> None:
    """The defect, seeded at the seam: HTTP 200 with NO Mcp-Session-Id.

    Measured at HEAD 2026-08-15 against the live wt1 front door before the fix:
    `initialize` returned 200 and the header was absent, so a client that attached
    to an idle slot held no session any later backend had issued and every
    `tools/call` came back `-32602` for the life of that session.
    """
    controller, _repo, _worktrees = slot_repo
    host, port, close = _serve_proxy(controller.inventory, 1)
    try:
        status, headers, raw = _post(host, port, {
            "jsonrpc": "2.0", "id": 1, "method": "initialize",
            "params": {"protocolVersion": "2025-06-18", "capabilities": {},
                       "clientInfo": {"name": "probe", "version": "1"}},
        })
        assert status == 200
        assert "mcp-session-id" in headers, (
            "the idle front door answered initialize without minting a session — "
            "this is the ADR-008 S-Q defect"
        )
        assert headers["mcp-session-id"]
        assert json.loads(raw)["result"]["protocolVersion"] == "2025-06-18"
    finally:
        close()


def test_each_initialize_mints_a_distinct_session(slot_repo) -> None:
    """Two clients on one idle slot must not be handed the same session."""
    controller, _repo, _worktrees = slot_repo
    host, port, close = _serve_proxy(controller.inventory, 1)
    try:
        payload = {"jsonrpc": "2.0", "id": 1, "method": "initialize",
                   "params": {"protocolVersion": "2025-06-18"}}
        _, first, _ = _post(host, port, payload)
        _, second, _ = _post(host, port, payload)
        assert first["mcp-session-id"] != second["mcp-session-id"]
    finally:
        close()


def test_the_minted_session_does_not_weaken_the_lease_gate(slot_repo) -> None:
    """S-Q must not become a way to dispatch without a lease (S-N is unaffected)."""
    controller, _repo, _worktrees = slot_repo
    host, port, close = _serve_proxy(controller.inventory, 1)
    try:
        _, headers, _ = _post(host, port, {
            "jsonrpc": "2.0", "id": 1, "method": "initialize",
            "params": {"protocolVersion": "2025-06-18"}})
        session = headers["mcp-session-id"]
        status, _, raw = _post(host, port, {
            "jsonrpc": "2.0", "id": 2, "method": "tools/call",
            "params": {"name": "lean_goal", "arguments": {}}}, session=session)
        assert status == 403
        assert b"no active lease" in raw
    finally:
        close()


def test_a_stale_backend_mapping_is_re_established_not_surfaced() -> None:
    """`prepare` restarts the Lean server mid-wave; the client session must survive it."""
    from scripts.lean_slots.proxy import SessionBroker

    broker = SessionBroker("127.0.0.1", 1, "tok")
    established: list[str] = []

    def fake_establish() -> str:
        established.append(f"backend-{len(established)}")
        return established[-1]

    broker._establish = fake_establish  # type: ignore[method-assign]
    client = broker.mint()
    assert broker.backend_session(client) == "backend-0"
    assert broker.backend_session(client) == "backend-0", "must not re-handshake per call"
    broker.forget(client)
    assert broker.backend_session(client) == "backend-1", (
        "after the backend restarts, the SAME client session must map to a NEW backend "
        "session rather than failing"
    )


def test_an_unknown_client_session_is_adopted_not_refused() -> None:
    """After a supervisor restart the client's session is gone; refusing it would
    hand back exactly the restart-the-client tax S-Q removes."""
    from scripts.lean_slots.proxy import SessionBroker

    broker = SessionBroker("127.0.0.1", 1, "tok")
    broker._establish = lambda: "backend-x"  # type: ignore[method-assign]
    assert broker.backend_session("never-minted-by-this-proxy") == "backend-x"


# ADR-008 ST: keep the actual Handler, broker and gate; simulate only transport.
@pytest.fixture()
def st_proxy(slot_repo, monkeypatch):
    import io
    from scripts.lean_slots import proxy

    controller, _, _ = slot_repo
    rig = SimpleNamespace(
        inventory=controller.inventory, events=[], requests=[], brokers=[],
        dispatch=[], established=0, offline=False, forbid_connection=False,
    )
    original_init = proxy.SessionBroker.__init__

    def broker_init(broker, *args):
        original_init(broker, *args)
        rig.brokers.append(broker)

    monkeypatch.setattr(proxy.SessionBroker, "__init__", broker_init)
    for name in ("mint", "backend_session", "forget"):
        original = getattr(proxy.SessionBroker, name)

        def observed(broker, *args, _name=name, _original=original):
            rig.events.append((_name, *args))
            return _original(broker, *args)

        monkeypatch.setattr(proxy.SessionBroker, name, observed)
    original_cache = proxy.cached_tool_list

    def cached(inventory):
        rig.events.append(("cache",))
        return original_cache(inventory)

    monkeypatch.setattr(proxy, "cached_tool_list", cached)

    class Response:
        def __init__(self, status=200, body=b'{"result":{"ok":true}}', headers=()):
            self.status, self.reason = status, "Scripted backend"
            self.stream = io.BytesIO(body)
            self.headers = list(headers)

        def read(self, amount=-1):
            return self.stream.read(amount)

        def getheaders(self):
            return self.headers

    class Connection:
        def __init__(self, host, port, timeout):
            rig.events.append(("connection", host, port, timeout))
            assert not rig.forbid_connection, "unexpected backend connection"

        def request(self, method, path, body=None, headers=None):
            if rig.offline:
                raise OSError("scripted backend unavailable")
            self.message = json.loads(body) if body else {}
            self.record = dict(method=method, path=path, body=body,
                               headers=dict(headers or {}))
            rig.requests.append(self.record)

        def getresponse(self):
            method = self.message.get("method")
            if method == "initialize":
                token = f"backend-{rig.established}"
                rig.established += 1
                return Response(headers=[("Mcp-Session-Id", token)])
            if method == "notifications/initialized":
                return Response(status=202, body=b"")
            if rig.dispatch:
                return Response(*rig.dispatch.pop(0))
            return Response()

        def close(self):
            rig.events.append(("close",))

    monkeypatch.setattr(proxy.http.client, "HTTPConnection", Connection)
    rig.handler, rig.port, _ = _serve_proxy(rig.inventory, 1)
    return rig


def _st_payload(method="ping", request_id="independent-request"):
    return {"jsonrpc": "2.0", "id": request_id, "method": method}


def _st_static_denial(result, wire, rig, request_id="independent-request"):
    status, headers, body = result
    assert status == 400, (
        f"expected pre-backend refusal; wire={wire!r}; requests={rig.requests!r}; "
        f"events={rig.events!r}"
    )
    assert "mcp-session-id" not in headers
    assert b"\r\nMcp-Session-Id:" not in wire[0]
    error = json.loads(body)
    assert error["id"] == request_id
    assert error["error"] == {
        "code": -32001,
        "message": "ADR-008 lease gate: invalid Mcp-Session-Id header",
    }
    assert rig.events == []
    assert rig.requests == []
    assert rig.brokers[0]._backend == {}


def test_st_h06_folded_value_refuses_before_successful_backend(st_proxy):
    """A retained fold must never reach buffered success or its session echo."""
    rig = st_proxy
    wire = []
    result = _post(
        rig.handler, 0, _st_payload(), raw_output=wire,
        raw_fields=b"Mcp-Session-Id: alpha\r\n injected\r\n",
    )
    _st_static_denial(result, wire, rig)


def _st_active(rig, **changes):
    """Populate an isolated lease read by the real gate; no lifecycle operation."""
    inv = rig.inventory
    lease = {
        "schema_version": 1, "slot": 1, "state": "ACTIVE", "client": "claude",
        "repo_role": inv.repo_role, "worktree": str(inv.worktree(1)),
        "endpoint": inv.slot(1)["endpoint_name"], "owner_kind": "session",
    }
    lease.update(changes)
    atomic_json(inv.lease_path(1), lease)


def _st_session_lines(wire):
    return [line for line in wire[0].split(b"\r\n\r\n", 1)[0].split(b"\r\n")
            if line.lower().startswith(b"mcp-session-id:")]


def _st_success(result, wire, rig, token):
    assert result[0] == 200
    assert result[1]["mcp-session-id"] == token
    assert _st_session_lines(wire) == [b"Mcp-Session-Id: " + token.encode("ascii")]
    assert rig.brokers[-1]._backend == {token: f"backend-{rig.established - 1}"}
    assert [(name, *args) for name, *args in rig.events if name == "backend_session"][-1] == (
        "backend_session", token,
    )
    assert rig.requests[-1]["headers"]["Mcp-Session-Id"].startswith("backend-")


@pytest.mark.parametrize("method", ["ping", "tools/call", "GET"])
def test_st_h01_absent_reuses_sessionless_mapping(st_proxy, method):
    rig = st_proxy
    if method != "ping":
        _st_active(rig)
    payload = _st_payload(method if method != "GET" else "ping")
    for _ in range(2):
        wire = []
        result = _post(rig.handler, 0, payload, method="GET" if method == "GET" else "POST",
                       raw_output=wire)
        assert result[0] == 200
        assert "mcp-session-id" not in result[1]
        assert _st_session_lines(wire) == []
    assert rig.established == 1
    assert rig.brokers[0]._backend == {"\x00sessionless": "backend-0"}
    assert [e for e in rig.events if e[0] == "backend_session"] == [
        ("backend_session", "\x00sessionless"), ("backend_session", "\x00sessionless"),
    ]
    assert len(rig.requests) == 4  # One handshake/notification, then two forwards.


@pytest.mark.parametrize("token,request_id", [
    ("", "independent-request"), (" \t ", "independent-request"),
    ("bad\x00value", "bad\x00value"),
])
def test_st_h02_empty_and_independent_request_id(st_proxy, token, request_id):
    rig = st_proxy
    wire = []
    result = _post(rig.handler, 0, _st_payload(request_id=request_id), token, raw_output=wire)
    _st_static_denial(result, wire, rig, request_id)


@pytest.mark.parametrize("fields", [
    [("Mcp-Session-Id", "alpha"), ("Mcp-Session-Id", "alpha")],
    [("Mcp-Session-Id", "alpha"), ("Mcp-Session-Id", "beta")],
    [("mCp-SeSsIoN-Id", "alpha"), ("MCP-SESSION-ID", "alpha")],
    [("Mcp-Session-Id", "alpha"), ("Mcp-Session-Id", "bad\x00value")],
    [("Mcp-Session-Id", "bad\x00value"), ("Mcp-Session-Id", "alpha")],
])
def test_st_h03_all_duplicate_occurrences_refuse(st_proxy, fields):
    rig = st_proxy
    wire = []
    result = _post(rig.handler, 0, _st_payload(), fields=fields, raw_output=wire)
    _st_static_denial(result, wire, rig)


@pytest.mark.parametrize("method", ["POST", "DELETE"])
@pytest.mark.parametrize("token", [
    "alpha", "0123456789abcdef" * 2, "never-minted-by-this-proxy",
    "".join(chr(n) for n in range(0x21, 0x7F)), '"a,b:c/d"', "%0D%0A",
])
def test_st_h04_visible_ascii_is_opaque_on_buffered_success(st_proxy, method, token):
    rig = st_proxy
    wire = []
    result = _post(rig.handler, 0, _st_payload(), token, method=method, raw_output=wire)
    _st_success(result, wire, rig, token)
    assert rig.requests[-1]["method"] == method


def test_st_h05_only_outer_sp_htab_are_framing(st_proxy):
    rig = st_proxy
    wire = []
    result = _post(rig.handler, 0, _st_payload(), " \tAlPhA\t ", raw_output=wire)
    _st_success(result, wire, rig, "AlPhA")


@pytest.mark.parametrize("token", ["a b", "a\tb", "\valpha", "alpha\f", "\xa0alpha\xa0"])
def test_st_h05_other_whitespace_is_not_repaired(st_proxy, token):
    rig = st_proxy
    wire = []
    result = _post(rig.handler, 0, _st_payload(), token, raw_output=wire)
    _st_static_denial(result, wire, rig)


@pytest.mark.parametrize("value", [
    *(b"A" + bytes([n]) + b"Z" for n in range(0x20) if n not in {10, 13}),
    b"A\x7fZ", b"A\x80Z", b"A\xe9Z", b"A\xffZ",
    b"alpha\r\n beta", b"alpha\n beta", b"alpha\r beta", b"alpha\r\n ",
], ids=lambda value: value.hex())
def test_st_h06_retained_parsed_controls_refuse(st_proxy, value):
    rig = st_proxy
    wire = []
    result = _post(rig.handler, 0, _st_payload(), raw_output=wire,
                   raw_fields=b"Mcp-Session-Id: " + value + b"\r\n")
    _st_static_denial(result, wire, rig)


def test_st_h06_delete_retained_control_refuses(st_proxy):
    rig = st_proxy
    wire = []
    result = _post(rig.handler, 0, _st_payload(), "A\x00Z", method="DELETE", raw_output=wire)
    _st_static_denial(result, wire, rig)


@pytest.mark.parametrize("raw_fields", [
    b"Mcp-Session-Id:\r\n alpha\r\n",
    b"Mcp-Session-Id: alpha\nbeta\r\n",
    b"Mcp-Session-Id: alpha\rbeta\r\n",
    b"Mcp-Session-Id: alpha\r\nX-Separate: value\r\n",
])
def test_st_h07_parser_erasure_does_not_become_token_suffix(st_proxy, raw_fields):
    rig = st_proxy
    wire = []
    result = _post(rig.handler, 0, _st_payload(), raw_fields=raw_fields, raw_output=wire)
    _st_success(result, wire, rig, "alpha")
    if b"X-Separate" in raw_fields:
        assert rig.requests[-1]["headers"]["X-Separate"] == "value"


@pytest.mark.parametrize("length,expected", [(65518, 200), (65519, 431)])
def test_st_h08_specific_canonical_field_line_boundary(st_proxy, length, expected):
    import http.client
    rig = st_proxy
    assert http.client._MAXLINE == 65536  # This control is specific to this parser/framing.
    wire = []
    token = "a" * length
    result = _post(rig.handler, 0, _st_payload(), token, raw_output=wire)
    assert result[0] == expected
    if expected == 200:
        _st_success(result, wire, rig, token)
    else:
        assert _st_session_lines(wire) == []
        assert rig.events == rig.requests == []
        assert rig.brokers[0]._backend == {}


@pytest.mark.parametrize("supplied", [None, "valid-client,token"])
def test_st_h09_initialize_mints_locally_after_valid_selection(st_proxy, supplied):
    rig = st_proxy
    rig.forbid_connection = True
    minted = []
    for _ in range(2):
        wire = []
        result = _post(rig.handler, 0, _st_payload("initialize"), supplied, raw_output=wire)
        assert result[0] == 200
        token = result[1]["mcp-session-id"]
        assert len(token) == 32 and all(c in "0123456789abcdef" for c in token)
        assert token != supplied
        assert _st_session_lines(wire) == [b"Mcp-Session-Id: " + token.encode()]
        minted.append(token)
    assert len(set(minted)) == 2
    assert rig.events == [("mint",), ("cache",), ("mint",), ("cache",)]
    assert rig.brokers[0]._backend == {token: "" for token in minted}
    assert rig.requests == []


@pytest.mark.parametrize("fields", [
    [("Mcp-Session-Id", "")], [("Mcp-Session-Id", "A\x00Z")],
    [("Mcp-Session-Id", "valid"), ("Mcp-Session-Id", "valid")],
])
def test_st_h09_invalid_initialize_precedes_mint_and_cache(st_proxy, fields):
    rig = st_proxy
    wire = []
    result = _post(rig.handler, 0, _st_payload("initialize"), fields=fields, raw_output=wire)
    _st_static_denial(result, wire, rig)


@pytest.mark.parametrize("method", ["POST", "GET"])
@pytest.mark.parametrize("defect,detail", [
    ("unleased", "no active lease"), ("client", "another client"),
    ("role", "repository-role mismatch"), ("worktree", "project-root mismatch"),
    ("endpoint", "endpoint-identity mismatch"), ("process", "process owner identity"),
    ("state", "not active"),
])
def test_st_h10_valid_token_cannot_grant_dispatch(st_proxy, method, defect, detail):
    rig = st_proxy
    changes = {
        "client": {"client": "codex"}, "role": {"repo_role": "other"},
        "worktree": {"worktree": "wrong"}, "endpoint": {"endpoint": "wrong"},
        "process": {"owner_kind": "process", "owner_pid": 991001,
                    "owner_signature": "stale identity"},
        "state": {"state": "QUARANTINED"},
    }
    if defect != "unleased":
        _st_active(rig, **changes[defect])
    wire = []
    result = _post(rig.handler, 0, _st_payload("tools/call"), "valid-token",
                   method=method, raw_output=wire)
    assert result[0] == 403
    assert detail in json.loads(result[2])["error"]["message"]
    assert _st_session_lines(wire) == []
    assert rig.events == rig.requests == []


def test_st_h10_disabled_build_remains_denied(st_proxy):
    rig = st_proxy
    _st_active(rig)
    payload = {**_st_payload("tools/call"), "params": {"name": "lean_build"}}
    result = _post(rig.handler, 0, payload, "valid-token")
    assert result[0] == 403
    assert "lean_build is disabled" in json.loads(result[2])["error"]["message"]
    assert rig.events == rig.requests == []


@pytest.mark.parametrize("defect,detail", [
    ("sha", "paired dependency SHA changed"),
    ("dirty", "paired dependency became dirty"),
])
def test_st_h10_actual_handler_rechecks_paired_dependency(st_proxy, downstream_repo, defect, detail):
    rig = st_proxy
    downstream, public, _, _ = downstream_repo
    rig.inventory = downstream.inventory
    rig.handler, _, _ = _serve_proxy(rig.inventory, 1)
    paired = public.inventory.worktree(1)
    dependency_sha = run(paired, "git", "rev-parse", "HEAD")
    _st_active(rig, public_dependency_sha=dependency_sha)
    payload = {**_st_payload("tools/call"),
               "params": {"name": "lean_goal", "arguments": {}}}
    wire = []
    result = _post(rig.handler, 0, payload, "valid-token", raw_output=wire)
    _st_success(result, wire, rig, "valid-token")
    if defect == "sha":
        _st_active(rig, public_dependency_sha="0" * 40)
    else:
        (paired / "changed.lean").write_text("isolated dependency change\n")
    rig.events.clear()
    rig.requests.clear()
    wire = []
    result = _post(rig.handler, 0, payload, "valid-token", raw_output=wire)
    assert result[0] == 403
    assert detail in json.loads(result[2])["error"]["message"]
    assert _st_session_lines(wire) == []
    assert rig.events == rig.requests == []


def test_st_h10_valid_bearer_and_lease_dispatch_on_actual_handler(st_proxy):
    from scripts.lean_slots.state import token_hash
    rig = st_proxy
    rig.inventory.raw["server"]["client_auth"] = "bearer"
    credential = rig.inventory.token("claude")
    _st_active(rig, token_hash=token_hash(credential))
    payload = {**_st_payload("tools/call"),
               "params": {"name": "lean_goal", "arguments": {}}}
    wire = []
    result = _post(rig.handler, 0, payload, "valid-token", raw_output=wire,
                   fields=[("Authorization", f"Bearer {credential}")])
    _st_success(result, wire, rig, "valid-token")
    assert rig.requests[-1]["headers"]["Authorization"] != f"Bearer {credential}"


def test_st_h11_unknown_token_is_adopted_after_broker_replacement(st_proxy):
    rig = st_proxy
    for _ in range(2):
        wire = []
        result = _post(rig.handler, 0, _st_payload(), "unknown-before-restart", raw_output=wire)
        _st_success(result, wire, rig, "unknown-before-restart")
        rig.handler, _, _ = _serve_proxy(rig.inventory, 1)
    assert rig.established == 2
    assert rig.brokers[0]._backend == {"unknown-before-restart": "backend-0"}
    assert rig.brokers[1]._backend == {"unknown-before-restart": "backend-1"}


@pytest.mark.parametrize("failure", [
    (400, b"unknown session"), (404, b"unknown session"),
    (200, b'{"error":{"code":-32602}}'),
])
@pytest.mark.parametrize("reject_again", [False, True])
def test_st_h11_actual_handler_retries_only_once(st_proxy, failure, reject_again):
    rig = st_proxy
    rig.dispatch = [failure, failure if reject_again else (200, b"success")]
    wire = []
    result = _post(rig.handler, 0, _st_payload(), "AlPhA,token", raw_output=wire)
    assert (result[0], result[2]) == (failure if reject_again else (200, b"success"))
    assert _st_session_lines(wire) == [b"Mcp-Session-Id: AlPhA,token"]
    assert rig.established == 2 and rig.dispatch == []
    assert [e for e in rig.events if e[0] in {"backend_session", "forget"}] == [
        ("backend_session", "AlPhA,token"), ("forget", "AlPhA,token"),
        ("backend_session", "AlPhA,token"),
    ]
    assert [json.loads(x["body"])["method"] for x in rig.requests] == [
        "initialize", "notifications/initialized", "ping",
        "initialize", "notifications/initialized", "ping",
    ]
    forwarded = [x for x in rig.requests if json.loads(x["body"])["method"] == "ping"]
    assert [x["headers"]["Mcp-Session-Id"] for x in forwarded] == ["backend-0", "backend-1"]
    assert rig.brokers[0]._backend == {"AlPhA,token": "backend-1"}


@pytest.mark.parametrize("method,expected", [
    ("notifications/initialized", 202), ("tools/list", 200),
    ("ping", 200), ("tools/call", 503),
])
def test_st_h12_offline_fallbacks_keep_existing_shapes(st_proxy, method, expected):
    from scripts.lean_slots.state import tool_cache_path, tool_list_key
    rig = st_proxy
    rig.offline = True
    tools = [{"name": "lean_goal", "inputSchema": {"type": "object"}}]
    atomic_json(tool_cache_path(rig.inventory.state_root),
                {"key": tool_list_key(rig.inventory.raw["server"]), "tools": tools})
    if method == "tools/call":
        _st_active(rig)
    payload = _st_payload(method)
    if method.startswith("notifications/"):
        payload.pop("id")
    result = _post(rig.handler, 0, payload, "valid-token")
    assert result[0] == expected
    assert "mcp-session-id" not in result[1]
    if method == "notifications/initialized":
        assert result[2] == b""
        assert ("cache",) not in rig.events
    elif method == "tools/list":
        assert json.loads(result[2])["result"]["tools"] == tools
        assert ("cache",) in rig.events
    elif method == "ping":
        assert json.loads(result[2])["result"] == {}
    else:
        assert "backend unavailable" in json.loads(result[2])["error"]["message"]


def test_st_h12_invalid_discovery_precedes_cache_and_fallback(st_proxy):
    rig = st_proxy
    rig.offline = True
    wire = []
    result = _post(rig.handler, 0, _st_payload("tools/list"), "bad\x00value", raw_output=wire)
    _st_static_denial(result, wire, rig)


@pytest.mark.parametrize("auth,expected", [("trusted-local", 204), ("bearer-missing", 401),
                                          ("bearer-valid", 204)])
def test_st_h12_head_auth_does_not_consume_session(st_proxy, auth, expected, monkeypatch):
    from scripts.lean_slots import proxy
    rig = st_proxy
    fields = []
    if auth.startswith("bearer"):
        rig.inventory.raw["server"]["client_auth"] = "bearer"
        if auth == "bearer-valid":
            fields.append(("Authorization", f"Bearer {rig.inventory.token('claude')}"))
    def must_not_select(_headers):
        pytest.fail("HEAD must not consume a session value")
    monkeypatch.setattr(proxy, "_client_session_id", must_not_select)
    wire = []
    result = _post(rig.handler, 0, None, "bad\x00value", method="HEAD", raw_output=wire,
                   fields=fields)
    assert result[0] == expected and result[2] == b""
    assert _st_session_lines(wire) == []
    assert rig.events == rig.requests == []


@pytest.mark.parametrize("method", ["POST", "DELETE", "GET"])
def test_st_h13_backend_and_client_session_headers_have_distinct_owners(st_proxy, method):
    rig = st_proxy
    if method == "GET":
        _st_active(rig)
    rig.dispatch = [(200, b"stream-or-buffered", [
        ("Mcp-Session-Id", "backend-header-a"),
        ("mCp-SeSsIoN-Id", "backend-header-b"), ("X-Backend", "preserved"),
    ])]
    wire = []
    result = _post(rig.handler, 0, _st_payload(), "client,token", method=method, raw_output=wire)
    assert result[0] == 200 and result[2] == b"stream-or-buffered"
    assert result[1]["x-backend"] == "preserved"
    if method == "GET":
        assert _st_session_lines(wire) == [b"Mcp-Session-Id: backend-header-a",
                                           b"mCp-SeSsIoN-Id: backend-header-b"]
    else:
        _st_success(result, wire, rig, "client,token")
    assert rig.requests[-1]["headers"]["Mcp-Session-Id"] == "backend-0"


@pytest.mark.parametrize("bearer,expected", [(True, 401), (False, 403)])
def test_st_h14_gate_failure_precedes_invalid_session(st_proxy, bearer, expected, monkeypatch):
    from scripts.lean_slots import proxy
    rig = st_proxy
    if bearer:
        rig.inventory.raw["server"]["client_auth"] = "bearer"
    def must_not_select(_headers):
        pytest.fail("auth/lease failure must precede session selection")
    monkeypatch.setattr(proxy, "_client_session_id", must_not_select)
    wire = []
    result = _post(rig.handler, 0, _st_payload("tools/call"), "bad\x00value", raw_output=wire)
    assert result[0] == expected
    assert _st_session_lines(wire) == []
    assert rig.events == rig.requests == []
