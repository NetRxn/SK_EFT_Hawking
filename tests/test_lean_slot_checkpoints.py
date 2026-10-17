"""Checkpoint transactions through committed production packages and actual Git.

All repositories, leases, evidence and native process observations are disposable.
Host supplies OS observations only; Controller/Git/journal/proxy guards stay real.
"""
from __future__ import annotations

import copy
import importlib
import importlib.util
import json
import os
import shutil
import sys
import types
import uuid
import shlex
import socket
import http.client
import threading
from http.server import ThreadingHTTPServer
from http.server import BaseHTTPRequestHandler
from pathlib import Path
from types import SimpleNamespace

import pytest

from tests.test_lean_slots import slot_repo, downstream_repo, isolated_process_observations, run, commit

ROOT = Path(__file__).resolve().parents[1]
NATIVE_CONNECT = socket.create_connection
NATIVE_HTTP = http.client.HTTPConnection
NATIVE_KILL = os.kill


@pytest.mark.parametrize("caller", ["mutator","removed-registry"])
@pytest.mark.parametrize("nested", [False,True],ids=["no-ambient","earlier-ambient"])
def test_cp_observation_callers_receive_helper_budget_without_stop_wrapper(rig,monkeypatch,caller,nested):
    from contextlib import contextmanager, nullcontext
    state=rig.modules.state;cp=rig.modules.cp
    sup=rig.modules.sup.Supervisor(rig.ctl.inventory)
    if caller=='removed-registry':
        monkeypatch.delenv('LEAN_SLOT_SKIP_SUPERVISOR',raising=False)
        sup.start_backend(1)
    wip(rig);req=request(rig);observed=[]
    actual_budget=state.observation_budget
    def boundary(self,phase):
        target='mutation-bound' if caller=='mutator' else 'stopped'
        if phase!=target or observed:return
        entries=[];baseline=rig.host.clock
        @contextmanager
        def budget(seconds):
            with actual_budget(seconds):
                entries.append((seconds,state._OBSERVATION_DEADLINE.get()-baseline))
                yield
        before=self.path.read_bytes()
        with monkeypatch.context() as patch:
            patch.setattr(state,'observation_budget',budget)
            with actual_budget(0.25) if nested else nullcontext():
                if caller=='mutator':
                    with pytest.raises(state.SlotError,match='mutator still present'):
                        self._mutators_quiescent()
                else:self._native_before_quarantine(sup)
        assert entries and all(seconds==10.0 and deadline==pytest.approx(0.25 if nested else 10.0) for seconds,deadline in entries)
        assert self.path.read_bytes()==before,'observer cannot manufacture a transaction completion effect'
        observed.extend(entries)
    monkeypatch.setattr(cp.CheckpointTransaction,'boundary',boundary)
    result=rig.ctl.checkpoint(req)
    assert observed and result['phase']=='eligible-canonical-release' and result['sourceReady'] is False


def load_package(root):
    name = "checkpoint_fixture_" + uuid.uuid4().hex
    parent = types.ModuleType(name)
    parent.__path__ = [str(root / "scripts")]
    sys.modules[name] = parent
    package = importlib.import_module(name + ".lean_slots.checkpoints")
    ctl = importlib.import_module(name + ".lean_slots.controller")
    state = importlib.import_module(name + ".lean_slots.state")
    supervisor = importlib.import_module(name + ".lean_slots.supervisor")
    proxy = importlib.import_module(name + ".lean_slots.proxy")
    cli = importlib.import_module(name + ".lean_slots.cli")
    return SimpleNamespace(cp=package, ctl=ctl, state=state, sup=supervisor, proxy=proxy, cli=cli, prefix=name)


@pytest.fixture
def rig(slot_repo, isolated_process_observations, monkeypatch, tmp_path):
    original, repo, trees = slot_repo
    shutil.copytree(ROOT / "scripts" / "lean_slots", repo / "scripts" / "lean_slots", ignore=shutil.ignore_patterns("__pycache__"))
    (repo / "scripts" / "slotctl.py").write_text(
        "import sys\nfrom pathlib import Path\n"
        f"SELECTED_SCRIPTS = Path({str(repo / 'scripts')!r})\n"
        "sys.path.insert(0, str(SELECTED_SCRIPTS))\n"
        "from lean_slots.cli import main\nif __name__ == '__main__':\n    raise SystemExit(main())\n"
    )
    # Ignore test proof payloads without hiding them from the checkpoint enumerator.
    with (repo / ".gitignore").open("a") as stream:
        stream.write("ignored-proof.lean\nobstruction\n")
    run(repo, "git", "add", "scripts", ".gitignore")
    run(repo, "git", "commit", "-m", "install exact fixture production package")
    for number, tree in enumerate(trees, 1):
        run(tree, "git", "reset", "--hard", "main")
    modules = load_package(repo)
    ctl = modules.ctl.Controller(modules.state.Inventory.load(original.inventory.source))
    ctl.build()
    ctl.acquire(1, client="codex", base_ref="main")
    ctl.prepare(1)
    evidence = tmp_path / "evidence"
    evidence.mkdir()
    (evidence / "failure.txt").write_text("the original obligation remains open\n")
    item = SimpleNamespace(ctl=ctl, repo=repo, trees=trees, modules=modules, host=isolated_process_observations,
                           evidence=evidence, monkeypatch=monkeypatch)
    yield item
    for key in list(sys.modules):
        if key == modules.prefix or key.startswith(modules.prefix + "."):
            sys.modules.pop(key, None)


def classes(rig, number=1):
    root = rig.trees[number - 1]
    tracked = set(run(root, "git", "ls-files").splitlines())
    output = {}
    for path in root.rglob("*"):
        name = path.relative_to(root).as_posix()
        if name == ".git" or name in tracked or (path.is_dir() and any(value.startswith(name + "/") for value in tracked)):
            continue
        if name == "lean/.lake" or name.startswith("lean/.lake/"):
            authoritative = rig.repo / name
            binding = {"path": str(authoritative), "type": "directory"} if path.is_dir() else rig.modules.cp.file_binding(authoritative)
            output[name] = {"kind": "cache", "owner": "Controller._replace_lake", "owner_source": binding}
        else:
            output[name] = {"kind": "source"}
    return output


def request(rig, *, identifier="proof", number=1, contract=None):
    cp, ctl = rig.modules.cp, rig.ctl
    lease = ctl.inventory.lease(number)
    path = rig.evidence / f"drain-{number}-{uuid.uuid4().hex}.json"
    rpc = {"jsonrpc": "2.0", "id": "diagnostics-1", "method": "tools/call",
           "params": {"name": "lean_diagnostic_messages", "arguments": {"file_path": "Theorem.lean"}}}
    # Complete a request through the external transport model and real LeaseGate;
    # preserve the actual modeled wire bytes independently of checkpoint code.
    wire = json.dumps(rpc).encode()
    connection = HTTP(rig, number=number).connection()
    connection.request("POST", "/mcp", body=wire.decode())
    completed = connection.getresponse().read()
    request_path = path.with_name(path.stem + "-request.json")
    response_path = path.with_name(path.stem + "-response.json")
    request_path.write_bytes(wire)
    response_path.write_bytes(completed)
    request_ref, response_ref = cp.file_binding(request_path), cp.file_binding(response_path)
    cp.durable_json(path, {"schema": "lean-client-drain/v1", "producer": "client", "client": {"name": "proof-author", "client": "codex"},
                           "lease_generation": cp.generation(lease), "endpoint": ctl.inventory.slot(number)["endpoint_name"],
                           "owner": cp.owner(lease), "outstanding": [], "drained_at": "2026-10-16T00:00:00Z",
                           "completed_requests": [{"id": "diagnostics-1", "request": request_ref, "response": response_ref,
                                                   "request_sha256": request_ref["sha256"], "response_sha256": response_ref["sha256"],
                                                   "completed_at": "2026-10-16T00:00:00Z"}]})
    if contract is None:
        contract = {"sourceReady": False, "objective": "finish the entire original theorem", "obligations": ["original main theorem", "all original consumers"],
                    "acceptance": ["independent kernel proof and original scientific validation"], "failures": [cp.file_binding(rig.evidence / "failure.txt")],
                    "evidence": [cp.file_binding(rig.evidence / "failure.txt")], "clients": [{"name": "proof-author", "client": "codex"}]}
    classification = classes(rig, number)
    return {"id": identifier, "slot": number, "binding": cp.inventory_binding(ctl.inventory), "contract": contract,
            "lease_sha256": cp.sha256_bytes(cp.regular_bytes(ctl.inventory.lease_path(number))),
            "source_digest": cp.canonical_digest(cp.source_manifest(ctl.inventory.worktree(number), classification)),
            "classifications": classification, "source_safe_wip": True, "original_base_sha": lease["base_sha"],
            "native_bindings": cp.native_binding(ctl.inventory, number), "proof_smoke_file": "Theorem.lean",
            "evidence_roots": [str(rig.evidence)], "drain_receipts": [cp.file_binding(path)]}


def wip(rig):
    return commit(rig.trees[0], "lean/Theorem.lean", "-- unfinished full theorem\n")


def gate_denied(rig, number=1):
    inv = rig.ctl.inventory
    gate = rig.modules.proxy.LeaseGate(inv, number)
    credential = rig.modules.state.token_hash(inv.token("codex"))
    with pytest.raises(RuntimeError, match="not active"):
        gate.authorize("codex", credential, b'{"method":"tools/call","params":{"name":"lean_goal"}}')


def test_actual_controller_preserves_ref_payload_contract_and_separate_release(rig):
    head = wip(rig)
    (rig.trees[0] / "ignored-proof.lean").write_bytes(b"ignored actual source\x00bytes")
    (rig.trees[0] / "untracked.lean").write_text("untracked actual source\n")
    req = request(rig)
    journal = rig.ctl.checkpoint(req)
    cp = rig.modules.cp
    assert journal["phase"] == "eligible-canonical-release"
    assert journal["sourceReady"] is False
    assert journal["contract"] == req["contract"]
    assert rig.ctl.inventory.lease(1)["state"] == "QUARANTINED"
    gate_denied(rig)
    assert run(rig.repo, "git", "rev-parse", "refs/lean-checkpoints/proof/source") == head
    store = Path(journal["binding"]["common_git"]) / "lean-checkpoint-data" / "proof"
    receipt = cp.read_json(store / "complete.json")
    for name in ("lean/Theorem.lean", "ignored-proof.lean", "untracked.lean"):
        assert (store / "source" / name).read_bytes()
        assert receipt["copies"]["source/" + name]["sha256"] == receipt["source"]["entries"][name]["sha256"]
    assert run(rig.trees[0], "git", "rev-parse", "HEAD") == req["original_base_sha"]
    # Ordinary release continues to refuse nontracked source. No checkpoint bypass.
    with pytest.raises(RuntimeError, match="dirty"):
        rig.ctl.release(1)
    assert (rig.trees[0] / "untracked.lean").read_text() == "untracked actual source\n"
    assert (store / "complete.json").is_file()


def test_clean_wip_release_keeps_ref_but_is_not_absorbed_acceptance(rig):
    head = wip(rig)
    req = request(rig)
    assert rig.ctl._is_absorbed(rig.trees[0], rig.ctl.inventory.lease(1))[0] is False
    rig.ctl.checkpoint(req)
    rig.ctl.release(1)
    journal = rig.ctl.checkpoint_observe_release(req)
    assert journal["phase"] == "canonical-release-observed"
    assert rig.ctl.inventory.lease(1, required=False) is None
    assert run(rig.repo, "git", "rev-parse", "refs/lean-checkpoints/proof/source") == head
    assert journal["sourceReady"] is False
    assert journal["release_census"]["complete"]


@pytest.mark.parametrize("damage,match", [("unclassified", "unclassified"), ("dirty", "clean tracked"), ("evidence", "original changed"), ("denied", "readable"), ("symlink", "unsupported"), ("ref", "already exists"), ("lease", "lease bytes"), ("drain", "drain")])
def test_production_refuses_unprotected_or_drifted_inputs_without_reset(rig, damage, match):
    head = wip(rig)
    req = request(rig)
    if damage == "unclassified":
        (rig.trees[0] / "ignored-proof.lean").write_text("must preserve")
    elif damage == "dirty":
        (rig.trees[0] / "lean/Theorem.lean").write_text("uncommitted")
    elif damage == "evidence":
        (rig.evidence / "failure.txt").write_text("changed")
    elif damage == "denied":
        (rig.evidence / "failure.txt").chmod(0)
    elif damage == "symlink":
        (rig.trees[0] / "escape").symlink_to(rig.evidence / "failure.txt")
    elif damage == "ref":
        run(rig.repo, "git", "update-ref", "refs/lean-checkpoints/proof/source", head)
    elif damage == "lease":
        lease = rig.ctl.inventory.lease(1)
        lease["heartbeat_at"] = "unexpected heartbeat"
        rig.modules.state.durable_json(rig.ctl.inventory.lease_path(1), lease)
    else:
        req["drain_receipts"] = []
    with pytest.raises((RuntimeError, OSError), match=match):
        rig.ctl.checkpoint(req)
    assert run(rig.trees[0], "git", "rev-parse", "HEAD") == head
    assert (rig.trees[0] / "lean/Theorem.lean").exists()


@pytest.mark.parametrize("phase", ["created", "ref-intent", "ref-created", "ref-complete", "copy-intent", "copied-file", "copies-flushed", "protected", "lease-intent", "lease-write", "lease-complete", "quarantined", "stop-intent", "owned-stop", "quiescence-observed", "stopped", "reset-intent", "reset-effect", "source-flushed", "reset-complete", "eligible-canonical-release"])
def test_each_real_durable_crash_boundary_retains_source_and_recoverable_reservation(rig, phase, monkeypatch):
    head = wip(rig)
    req = request(rig)
    seen = []
    def crash(self, current):
        seen.append(current)
        if current == phase and seen.count(current) == 1:
            raise KeyboardInterrupt("isolated crash")
    monkeypatch.setattr(rig.modules.cp.CheckpointTransaction, "boundary", crash)
    with pytest.raises(KeyboardInterrupt):
        rig.ctl.checkpoint(req)
    assert phase in seen
    monkeypatch.setattr(rig.modules.cp.CheckpointTransaction, "boundary", lambda *_: None)
    lease = rig.ctl.inventory.lease(1)
    assert lease["state"] == "QUARANTINED"
    gate_denied(rig)
    current = run(rig.trees[0], "git", "rev-parse", "HEAD")
    if current != head:
        assert current == req["original_base_sha"]
        store = Path(req["binding"]["common_git"]) / "lean-checkpoint-data" / "proof"
        assert (store / "source" / "lean/Theorem.lean").read_text() == "-- unfinished full theorem\n"
        assert (store / "complete.json").is_file()
    recovered = rig.ctl.checkpoint(req, recover=True)
    assert recovered["phase"] == "eligible-canonical-release"
    assert recovered["sourceReady"] is False


@pytest.mark.parametrize("field,match", [("acquired_at", "later lease generation"), ("heartbeat_at", "later lease generation/byte transition")])
def test_later_owner_or_heartbeat_cannot_be_overwritten_by_recovery(rig, field, match):
    wip(rig)
    req = request(rig)
    rig.ctl.checkpoint(req)
    lease_path = rig.ctl.inventory.lease_path(1)
    later = rig.ctl.inventory.lease(1)
    later[field] = "later generation or heartbeat under same owner"
    rig.modules.state.durable_json(lease_path, later)
    before = lease_path.read_bytes()
    with pytest.raises(RuntimeError, match=match):
        rig.ctl.checkpoint(req, recover=True)
    assert lease_path.read_bytes() == before
    rig.ctl.release(1)
    with pytest.raises(RuntimeError, match="released lease cannot be recreated"):
        rig.ctl.checkpoint(req, recover=True)
    assert not lease_path.exists()


@pytest.mark.parametrize("directory", [False, True])
def test_reset_refuses_retained_ignored_file_or_directory_target_collision(rig, directory):
    # Base tracks a target; WIP deletes it and the destination owner replaces it.
    (rig.repo / "obstruction").write_text("base target")
    run(rig.repo, "git", "add", "-f", "obstruction")
    run(rig.repo, "git", "commit", "-m", "base target")
    rig.ctl.release(1)
    run(rig.trees[0], "git", "reset", "--hard", "main")
    rig.ctl.build()
    rig.ctl.acquire(1, client="codex", base_ref="main")
    rig.ctl.prepare(1)
    run(rig.trees[0], "git", "rm", "obstruction")
    run(rig.trees[0], "git", "commit", "-m", "WIP removes target")
    target = rig.trees[0] / "obstruction"
    if directory:
        target.mkdir()
        (target / "owner.txt").write_text("destination owner")
    else:
        target.write_text("destination owner")
    req = request(rig)
    head = run(rig.trees[0], "git", "rev-parse", "HEAD")
    # Check the safety effect as well as refusal: another late guard must not
    # hide a reset that already destroyed the destination owner's obstruction.
    with pytest.raises(RuntimeError):
        rig.ctl.checkpoint(req)
    assert (target / "owner.txt" if directory else target).read_text() == "destination owner"
    assert run(rig.trees[0], "git", "rev-parse", "HEAD") == head
    gate_denied(rig)


def candidate(rig):
    root = rig.repo.parent / "candidate"
    run(rig.repo, "git", "worktree", "add", "-b", "candidate-source", str(root), "main")
    return root, load_package(root)


def synthetic_bootstrap_authority(rig, root, selected, req, *, phase="isolated-native-bridge"):
    """Unit fixture data only; neither an actual A receipt nor B admission.

    Native pilots never call this helper. ROOT must independently accept actual
    full A evidence before any native bridge is run under a separate packet.
    """
    cp = selected.cp
    bootstrap = {"phase": phase, "candidate": cp.implementation_binding(root, loaded=True),
                 "canonical": cp.implementation_binding(rig.repo),
                 "root_owner": cp.owner(rig.ctl.inventory.lease(1))}
    req["bootstrap"] = bootstrap
    prior = {}
    for step in ("A", "B") if phase == "live-preservation" else ("A",):
        receipt = {"schema": "lean-checkpoint-native-admission/v1", "sourceReady": False,
                   "phase": step, "status": "accepted", "accepted_by": "ROOT",
                   "candidate_sha256": cp.canonical_digest(bootstrap["candidate"]),
                   "os_domain_sha256": cp.sha256_bytes(("SYNTHETIC unit-only domain " + step).encode()),
                   "native_receipt_sha256": cp.sha256_bytes(b"SYNTHETIC unit data, no actual native admission"),
                   "independent_review_sha256": cp.sha256_bytes(b"SYNTHETIC unit review identity")}
        if step == "B":
            receipt["canonical_sha256"] = cp.canonical_digest(bootstrap["canonical"])
        path = rig.evidence / ("synthetic-unit-admission-" + step + ".json")
        cp.durable_json(path, receipt)
        prior[step] = cp.file_binding(path)
    approval = {"schema": "lean-checkpoint-bootstrap-authorization/v1", "sourceReady": False,
                "phase": phase, "root_owner": bootstrap["root_owner"],
                "domain": {"os_domain_sha256": cp.bootstrap_os_domain(), "inventory_sha256": cp.canonical_digest(req["binding"])},
                "request_sha256": cp.canonical_digest(req),
                "candidate_sha256": cp.canonical_digest(bootstrap["candidate"]),
                "canonical_sha256": cp.canonical_digest(bootstrap["canonical"]),
                "independent_review_sha256": cp.sha256_bytes(b"SYNTHETIC unit implementation review"), "prior": prior}
    path = rig.evidence / "synthetic-unit-bootstrap-authorization.json"
    cp.durable_json(path, approval)
    bootstrap["authorization"] = cp.file_binding(path)
    return path, prior


@pytest.mark.parametrize("damage", ["default", "copied", "wrong-domain", "state-override", "config-override", "candidate", "canonical", "owner", "review", "contract"])
def test_actual_candidate_cli_rejects_bad_authority_before_constructor_or_effect(rig, monkeypatch, damage):
    wip(rig)
    monkeypatch.chdir(rig.repo)
    # Use the actual default domain; bootstrap explicitly rejects state overrides.
    new_state = rig.repo.parent / ".lean-slots"
    shutil.move(str(rig.ctl.inventory.state_root), new_state)
    monkeypatch.delenv("LEAN_SLOT_STATE_DIR")
    monkeypatch.delenv("LEAN_SLOT_SKIP_SUPERVISOR")
    rig.ctl = rig.modules.ctl.Controller(rig.modules.state.Inventory.load(rig.ctl.inventory.source))
    req = request(rig)
    root, selected = candidate(rig)
    synthetic_bootstrap_authority(rig, root, selected, req)
    inventory = rig.ctl.inventory.source
    if damage == "copied":
        copied = rig.repo / "config" / "copied.json"
        copied.write_bytes(inventory.read_bytes())
        inventory = copied
    elif damage == "wrong-domain":
        req["binding"]["state_root"] += "-other"
    elif damage == "state-override":
        monkeypatch.setenv("LEAN_SLOT_STATE_DIR", str(new_state))
    elif damage == "config-override":
        monkeypatch.setenv("LEAN_SLOT_CONFIG", str(inventory))
    elif damage == "candidate":
        with (root / "scripts" / "lean_slots" / "controller.py").open("a") as stream:
            stream.write("\n# drift\n")
    elif damage == "canonical":
        with (rig.repo / "scripts" / "lean_slots" / "controller.py").open("a") as stream:
            stream.write("\n# canonical drift\n")
    elif damage == "owner":
        req["bootstrap"]["root_owner"] = {"owner_kind": "session", "owner_session_hash": "other"}
    elif damage == "review":
        req["bootstrap"]["independent_review"] = False
    elif damage == "contract":
        req["contract"].pop("obligations")
    request_path = rig.evidence / "request.json"
    request_path.write_text(json.dumps(req))
    calls = []
    def forbidden(*_):
        calls.append("constructor")
        raise AssertionError("constructor ran before bootstrap validation")
    monkeypatch.setattr(selected.cli, "Controller", forbidden)
    monkeypatch.setattr(selected.ctl.Controller, "__init__", forbidden)
    before = rig.ctl.inventory.lease_path(1).read_bytes()
    argv = [] if damage == "default" else ["--inventory", str(inventory)]
    assert selected.cli.main([*argv, "checkpoint", "preserve", "--bootstrap", "--request", str(request_path)]) == 2
    assert calls == []
    assert before == rig.ctl.inventory.lease_path(1).read_bytes()
    assert not (new_state / "checkpoints").exists()


def test_candidate_route_uses_low_level_stop_only_and_keeps_canonical_sf_refusal(rig, monkeypatch, capsys):
    head = wip(rig)
    new_state = rig.repo.parent / ".lean-slots"
    shutil.move(str(rig.ctl.inventory.state_root), new_state)
    monkeypatch.delenv("LEAN_SLOT_STATE_DIR")
    monkeypatch.delenv("LEAN_SLOT_SKIP_SUPERVISOR")
    rig.ctl = rig.modules.ctl.Controller(rig.modules.state.Inventory.load(rig.ctl.inventory.source))
    monkeypatch.chdir(rig.repo)
    req = request(rig)
    root, selected = candidate(rig)
    synthetic_bootstrap_authority(rig, root, selected, req)
    inv = selected.cp.validate_bootstrap(rig.ctl.inventory.source, req)
    for name in ("process_state", "paused_backend", "activating_from", "_assert_backend_owned_or_stopped", "_start_backend_unlocked", "assert_healthy", "status"):
        def forbidden(*_, **__):
            raise AssertionError("candidate called forbidden SF/start helper")
        monkeypatch.setattr(selected.sup.Supervisor, name, forbidden)
    request_path = rig.evidence / "candidate-request.json"
    request_path.write_text(json.dumps(req))
    assert selected.cli.main(["--inventory", str(inv.source), "checkpoint", "preserve", "--bootstrap", "--request", str(request_path)]) == 0
    journal = json.loads(capsys.readouterr().out)
    assert journal["phase"] == "eligible-canonical-release"
    assert run(rig.repo, "git", "rev-parse", "refs/lean-checkpoints/proof/source") == head
    assert rig.host.launches == []
    # SF's actual source pass observes the alternate imported package mismatch.
    canonical = rig.modules.sup.Supervisor(rig.ctl.inventory)
    candidate_sup = selected.sup.Supervisor(inv)
    expected = canonical._runtime_inputs("proxy", 1, canonical.proxy_command(1), dict(os.environ))
    assert expected
    with pytest.raises(RuntimeError, match="selected and actual loaded roots disagree"):
        candidate_sup._runtime_inputs("proxy", 1, candidate_sup.proxy_command(1), dict(os.environ))
    # Release is a distinct unchanged canonical command after transaction locks drop.
    rig.ctl.release(1)
    assert selected.cli.main(["--inventory", str(inv.source), "checkpoint", "observe-release", "--bootstrap", "--request", str(request_path)]) == 0
    released = json.loads(capsys.readouterr().out)
    assert released["phase"] == "canonical-release-observed"
    assert rig.ctl.inventory.lease(1, required=False) is None


@pytest.mark.parametrize("damage", ["boolean-only", "phase", "request", "domain", "missing-authority", "truncated-authority",
                                    "unaccepted-A", "worker-A", "source-A", "same-OS-A", "missing-B", "canonical-B"])
def test_bootstrap_prior_phase_file_authority_refuses_before_constructor(rig, monkeypatch, damage):
    wip(rig)
    state = rig.repo.parent / ".lean-slots"
    shutil.move(str(rig.ctl.inventory.state_root), state)
    monkeypatch.delenv("LEAN_SLOT_STATE_DIR")
    monkeypatch.delenv("LEAN_SLOT_SKIP_SUPERVISOR")
    monkeypatch.chdir(rig.repo)
    rig.ctl = rig.modules.ctl.Controller(rig.modules.state.Inventory.load(rig.ctl.inventory.source))
    req = request(rig)
    root, selected = candidate(rig)
    phase = "live-preservation" if damage in {"missing-B", "canonical-B"} else "isolated-native-bridge"
    authority, prior = synthetic_bootstrap_authority(rig, root, selected, req, phase=phase)
    cp = selected.cp
    approval = cp.read_json(authority)
    if damage == "boolean-only":
        req["bootstrap"].pop("authorization")
        req["bootstrap"].pop("phase")
        req["bootstrap"]["independent_review"] = req["bootstrap"]["isolated_native_pilot"] = True
    elif damage == "phase":
        req["bootstrap"]["phase"] = "live-preservation"
    elif damage == "request":
        req["source_digest"] = "0" * 64
    elif damage == "domain":
        approval["domain"]["inventory_sha256"] = "0" * 64
    elif damage == "missing-B":
        approval["prior"].pop("B")
    elif damage in {"unaccepted-A", "worker-A", "source-A", "same-OS-A", "canonical-B"}:
        step = "B" if damage == "canonical-B" else "A"
        path = Path(prior[step]["path"])
        receipt = cp.read_json(path)
        key, value = {"unaccepted-A": ("status", "worker-reported-only"), "worker-A": ("accepted_by", "worker"),
                      "source-A": ("candidate_sha256", "0" * 64), "same-OS-A": ("os_domain_sha256", cp.bootstrap_os_domain()),
                      "canonical-B": ("canonical_sha256", "0" * 64)}[damage]
        receipt[key] = value
        cp.durable_json(path, receipt)
        approval["prior"][step] = cp.file_binding(path)
    cp.durable_json(authority, approval)
    if "authorization" in req["bootstrap"]:
        req["bootstrap"]["authorization"] = cp.file_binding(authority)
    if damage == "missing-authority":
        authority.rename(rig.evidence / "preserved-unit-authority.json")
    elif damage == "truncated-authority":
        authority.write_bytes(b"{")
    path = rig.evidence / "unit-bootstrap-request.json"
    cp.durable_json(path, req)
    def forbidden(*_):
        pytest.fail("constructor/state effects preceded exact bootstrap admission")
    monkeypatch.setattr(selected.cli, "Controller", forbidden)
    monkeypatch.setattr(selected.ctl.Controller, "__init__", forbidden)
    lease = rig.ctl.inventory.lease_path(1).read_bytes()
    assert selected.cli.main(["--inventory", str(rig.ctl.inventory.source), "checkpoint", "preserve", "--bootstrap", "--request", str(path)]) == 2
    assert rig.ctl.inventory.lease_path(1).read_bytes() == lease
    assert not (state / "checkpoints").exists()
    assert not (state / "locks/supervisor.lock.cp-guard").exists()


def test_unit_bootstrap_recovery_admits_only_official_heartbeat_between_facade_retirements(rig, monkeypatch):
    """Actual source/Git/locks and ordinary writer; synthetic authority is unit-only.

    This does not run or admit native phase B. Backend OS observations remain
    the declared Host fixture, independently of the actual fork/death/mutex.
    """
    from datetime import datetime, timedelta, timezone
    wip(rig)
    state = rig.repo.parent / ".lean-slots"
    shutil.move(str(rig.ctl.inventory.state_root), state)
    monkeypatch.delenv("LEAN_SLOT_STATE_DIR")
    monkeypatch.delenv("LEAN_SLOT_SKIP_SUPERVISOR")
    monkeypatch.chdir(rig.repo)
    rig.ctl = rig.modules.ctl.Controller(rig.modules.state.Inventory.load(rig.ctl.inventory.source))
    req = request(rig)
    root, selected = candidate(rig)
    synthetic_bootstrap_authority(rig, root, selected, req)
    path = rig.evidence / "unit-heartbeat-bootstrap.json"
    selected.cp.durable_json(path, req)
    args = ["--inventory", str(rig.ctl.inventory.source), "checkpoint", "preserve", "--bootstrap", "--request", str(path)]
    child = os.fork()
    if child == 0:
        try:
            rig.host.add(os.getpid(), "owned unit-only CP bootstrap attempt")
            def die(self, phase):
                if phase == "created":
                    os._exit(75)
            selected.cp.CheckpointTransaction.boundary = die
            selected.cli.main(args)
            os._exit(76)
        except BaseException:
            import traceback
            (rig.evidence / "unit-bootstrap-child-error.txt").write_text(traceback.format_exc())
            os._exit(77)
    assert os.waitstatus_to_exitcode(os.waitpid(child, 0)[1]) == 75
    recover = ["recover" if value == "preserve" else value for value in args]
    assert selected.cli.main(recover) == 2  # Retires only the intact abandoned target facade.
    assert not (state / "locks/wt1.lock").exists() and (state / "locks/supervisor.lock").exists()
    before = rig.ctl.inventory.lease_path(1).read_bytes()
    timestamp = (datetime.now(timezone.utc) + timedelta(seconds=2)).strftime("%Y-%m-%dT%H:%M:%SZ")
    monkeypatch.setattr(rig.modules.state, "now_iso", lambda: timestamp)
    rig.ctl.heartbeat(1)  # Unchanged ordinary legacy mkdir/writer, never a manual lease edit.
    actual = rig.ctl.inventory.lease_path(1).read_bytes()
    assert actual != before
    journal = selected.cp.journal_checked(state / "checkpoints/proof.json", "proof")
    assert selected.cp.heartbeat_transition(journal, rig.ctl.inventory.lease(1), selected.cp.sha256_bytes(actual)) is not None
    for field, value in (("lease_generation", "f" * 48), ("prepared_epoch", "f" * 64), ("unexpected_authority", True)):
        invalid = json.loads(actual)
        invalid[field] = value
        selected.cp.durable_json(rig.ctl.inventory.lease_path(1), invalid)
        malformed_bytes = rig.ctl.inventory.lease_path(1).read_bytes()
        try:
            with monkeypatch.context() as before_constructor:
                def forbidden(*_):
                    pytest.fail("non-heartbeat lease drift reached bootstrap constructor")
                before_constructor.setattr(selected.cli, "Controller", forbidden)
                assert selected.cli.main(recover) == 2
            assert rig.ctl.inventory.lease_path(1).read_bytes() == malformed_bytes
        finally:
            # Negative fixture input only; the admitted heartbeat above used
            # the unchanged official writer and remains the actual preimage.
            rig.ctl.inventory.lease_path(1).write_bytes(actual)
    assert selected.cp.validate_bootstrap(rig.ctl.inventory.source, req, recover=True).state_root == state
    for attempt in range(3):
        result = selected.cli.main(recover)
        if result == 0:
            break
        assert result == 2 and attempt < 2
    assert result == 0
    complete = selected.cp.journal_checked(state / "checkpoints/proof.json", "proof")
    assert complete["phase"] == "eligible-canonical-release" and complete["sourceReady"] is False
    assert bytes.fromhex(complete["original_lease_bytes"]) == before
    assert complete["lease_observation"]["before_sha256"] == selected.cp.sha256_bytes(before)
    assert complete["lease_observation"]["after_sha256"] == selected.cp.sha256_bytes(actual)


def test_unowned_project_or_unavailable_global_census_never_signals_or_resets(rig):
    head = wip(rig)
    req = request(rig)
    rig.host.add(910001, f"lean --server {rig.ctl.inventory.lean_root(1)}")
    with pytest.raises(RuntimeError, match="fixed-project process remains"):
        rig.ctl.checkpoint(req)
    assert rig.host.signals == []
    assert run(rig.trees[0], "git", "rev-parse", "HEAD") == head
    gate_denied(rig)


@pytest.mark.parametrize("crash", [None, "stop-receipt", "owned-stop"])
def test_actual_rr_owned_family_receipts_survive_registry_removal(rig, monkeypatch, crash):
    wip(rig)
    req = request(rig)
    inv = rig.ctl.inventory
    sup = rig.modules.sup.Supervisor(inv)
    command = sup.backend_command(1)
    signature = rig.host.add(910010, " ".join(command), port=inv.slot(1)["backend_port"])
    child = rig.host.add(910011, f"lean --server {inv.lean_root(1)}", ppid=910010)
    # The real managed registry writer/reader carries native RR provenance.
    metadata = {"schema_version": 1, "repo_role": inv.repo_role, "slot": 1, "kind": "backend", "pid": 910010,
                "signature": signature, "command": command, "port": inv.slot(1)["backend_port"],
                "inventory": str(inv.source), "phase": "running", "started_at": "2026-10-16T00:00:00Z",
                "descendants": [{"pid": 910011, "signature": child}]}
    # Reuse the actual runtime metadata producer for all required fields.
    fingerprint = sup._runtime_inputs("backend", 1, command, dict(os.environ))
    metadata["runtime_fingerprint"] = fingerprint
    rig.modules.state.durable_json(inv.process_path("backend", 1), metadata)
    req["native_bindings"] = rig.modules.cp.native_binding(inv, 1)
    if crash:
        fired = []
        def interrupt(self, phase):
            if phase == crash and not fired:
                fired.append(phase)
                raise KeyboardInterrupt("owned stop interruption")
        monkeypatch.setattr(rig.modules.cp.CheckpointTransaction, "boundary", interrupt)
        with pytest.raises(KeyboardInterrupt):
            rig.ctl.checkpoint(req)
        assert fired
        gate_denied(rig)
        assert run(rig.trees[0], "git", "rev-parse", "HEAD") != req["original_base_sha"]
        store = Path(req["binding"]["common_git"]) / "lean-checkpoint-data/proof"
        assert (store / "source/lean/Theorem.lean").read_text() == "-- unfinished full theorem\n"
        recorded = rig.modules.cp.read_json(inv.state_root / "checkpoints/proof.json")
        assert recorded["native_stop_receipts"]
        delivered = list(rig.host.signals)
        monkeypatch.setattr(rig.modules.cp.CheckpointTransaction, "boundary", lambda *_: None)
        journal = rig.ctl.checkpoint(req, recover=True)
        assert rig.host.signals[:len(delivered)] == delivered
        assert len({pid for pid, _ in rig.host.signals}) == len(rig.host.signals)
        assert journal["contract"] == req["contract"]
        assert journal["phase"] == "eligible-canonical-release"
        gate_denied(rig)
        return
    journal = rig.ctl.checkpoint(req)
    assert [pid for pid, _ in rig.host.signals] == [910011, 910010]
    assert not inv.process_path("backend", 1).exists()
    assert any(item["shutdown"]["delivered_sigterm"] for item in journal["native_stop_receipts"])
    assert journal["phase"] == "eligible-canonical-release"


def fresh_resume(rig, *, changed=False, conflict=False):
    old = wip(rig)
    req = request(rig)
    rig.ctl.checkpoint(req)
    rig.ctl.release(1)
    if changed:
        commit(rig.repo, "lean/Theorem.lean" if conflict else "Current.lean", "current upstream\n")
        rig.ctl.build()
    rig.ctl.acquire(1, client="codex", base_ref="main")
    rig.ctl.prepare(1, checkpoint_request={**req, "lease_sha256": "preflight uses current ordinary lease"})
    fresh = request(rig, contract=req["contract"])
    return old, req, fresh


class HTTP:
    """External MCP transport model; production probe and actual lease gate run."""
    def __init__(self, rig, *, fail_smoke=False, number=1):
        self.rig, self.fail_smoke = rig, fail_smoke
        self.number = number
        self.methods = []
        self.states = []
    def connection(self, *_, **__):
        host = self
        class Connection:
            def request(self, method, path, body=None, headers=None):
                self.method = method
                self.payload = json.loads(body) if body else {}
                host.methods.append(self.payload.get("method", method))
                if self.payload.get("method") == "tools/call":
                    host.states.append(host.rig.ctl.inventory.lease(host.number)["state"])
                    inv = host.rig.ctl.inventory
                    gate = host.rig.modules.proxy.LeaseGate(inv, host.number)
                    gate.authorize("codex", host.rig.modules.state.token_hash(inv.token("codex")), body.encode(),
                                   checkpoint_capability=(headers or {}).get(host.rig.modules.cp.SMOKE_HEADER))
            def getresponse(self):
                method = self.payload.get("method")
                if method == "initialize":
                    value = {"result": {"serverInfo": {"name": "isolated MCP"}}}
                elif method == "tools/list":
                    value = {"result": {"tools": [{"name": "lean_diagnostic_messages"}]}}
                elif method == "tools/call":
                    value = {"error": {"message": "isolated proof failure"}} if host.fail_smoke else {"result": {"structuredContent": {"success": True, "timed_out": False, "items": [], "failed_dependencies": []}}}
                else:
                    value = {"result": {}}
                value.update(jsonrpc="2.0", id=self.payload.get("id"))
                return SimpleNamespace(status=200, read=lambda: json.dumps(value).encode(), getheaders=lambda: [("Mcp-Session-Id", "fresh-isolated-session")])
            def close(self):
                pass
        return Connection()


@pytest.mark.parametrize("changed", [False, True])
def test_resume_preserves_ancestry_current_epoch_full_contract_and_actual_dispatch_gate(rig, monkeypatch, changed):
    old, original, fresh = fresh_resume(rig, changed=changed)
    monkeypatch.delenv("LEAN_SLOT_SKIP_SUPERVISOR")
    supervisor = rig.modules.sup.Supervisor(rig.ctl.inventory)
    supervisor.start_proxy(1)
    http = HTTP(rig)
    monkeypatch.setattr(rig.modules.sup.http.client, "HTTPConnection", http.connection)
    denied = []
    def observe(self, phase):
        if phase in {"quarantined", "resume-source-intent", "resume-source-effect", "resume-source-complete", "resume-restore-intent", "resume-reactivate-intent"}:
            gate_denied(rig)
            denied.append(phase)
    monkeypatch.setattr(rig.modules.cp.CheckpointTransaction, "boundary", observe)
    journal = rig.ctl.checkpoint_resume(fresh)
    assert journal["phase"] == "resumed"
    assert journal["sourceReady"] is False
    assert journal["contract"] == original["contract"]
    assert journal["historical_evidence"] is True
    assert rig.ctl.inventory.lease(1)["state"] == "ACTIVE"
    assert http.states == ["ACTIVE"]
    assert "resume-source-effect" in denied
    assert (rig.trees[0] / "lean/Theorem.lean").read_text() == "-- unfinished full theorem\n"
    if changed:
        assert (rig.trees[0] / "Current.lean").read_text() == "current upstream\n"
        parents = run(rig.trees[0], "git", "rev-list", "--parents", "-n", "1", "HEAD").split()
        assert old in parents[1:] and len(parents) == 3
    else:
        assert run(rig.trees[0], "git", "rev-parse", "HEAD") == old


def test_changed_base_merge_conflict_and_recovery_keep_dispatch_denied_without_start(rig, monkeypatch):
    _, _, fresh = fresh_resume(rig, changed=True, conflict=True)
    monkeypatch.delenv("LEAN_SLOT_SKIP_SUPERVISOR")
    launches = list(rig.host.launches)
    with pytest.raises(RuntimeError, match="merge conflict"):
        rig.ctl.checkpoint_resume(fresh)
    assert rig.host.launches == launches
    gate_denied(rig)
    assert "<<<<<<<" in (rig.trees[0] / "lean/Theorem.lean").read_text()
    before = (rig.trees[0] / "lean/Theorem.lean").read_bytes()
    with pytest.raises(RuntimeError, match="explicit source/conflict review"):
        rig.ctl.checkpoint_resume(fresh, recover=True)
    assert (rig.trees[0] / "lean/Theorem.lean").read_bytes() == before
    gate_denied(rig)


@pytest.mark.parametrize("phase", ["resume-bound", "lease-write", "resume-source-intent", "resume-source-effect", "resume-metadata-intent", "resume-metadata-effect", "resume-metadata-complete", "resume-source-complete", "resume-restore-intent", "resume-reactivate-intent", "resume-active", "resumed"])
def test_resume_interruption_preserves_source_and_explicit_recovery_uses_fresh_admission(rig, monkeypatch, phase):
    _, original, fresh = fresh_resume(rig)
    monkeypatch.delenv("LEAN_SLOT_SKIP_SUPERVISOR")
    rig.modules.sup.Supervisor(rig.ctl.inventory).start_proxy(1)
    http = HTTP(rig)
    monkeypatch.setattr(rig.modules.sup.http.client, "HTTPConnection", http.connection)
    fired = []
    def crash(self, current):
        if current == phase and not fired:
            fired.append(current)
            raise KeyboardInterrupt("resume crash")
    monkeypatch.setattr(rig.modules.cp.CheckpointTransaction, "boundary", crash)
    with pytest.raises(KeyboardInterrupt):
        rig.ctl.checkpoint_resume(fresh)
    assert fired == [phase]
    gate_denied(rig)
    launches = list(rig.host.launches)
    prior = rig.modules.cp.read_json(rig.ctl.inventory.state_root / "checkpoints/proof.json")
    monkeypatch.setattr(rig.modules.cp.CheckpointTransaction, "boundary", lambda *_: None)
    if prior.get("resulting_source"):
        recovered = rig.ctl.checkpoint_resume(fresh, recover=True)
        current = rig.ctl.inventory.lease(1)
        assert current["resume_admission"]["state"] == "completed"
        assert recovered["readiness"]["status"] == "completed"
        old_attempt = prior.get("readiness", {}).get("context", {}).get("attempt")
        if old_attempt:
            assert current["resume_admission"]["attempt"]["nonce"] != old_attempt["nonce"]
        assert recovered["contract"] == original["contract"] and recovered["sourceReady"] is False
        assert http.states[-1] == "ACTIVE"
    else:
        with pytest.raises(RuntimeError, match="explicit source/conflict review"):
            rig.ctl.checkpoint_resume(fresh, recover=True)
        assert rig.host.launches == launches
        gate_denied(rig)
    store = Path(original["binding"]["common_git"]) / "lean-checkpoint-data" / "proof"
    assert (store / "source" / "lean/Theorem.lean").read_text() == "-- unfinished full theorem\n"


def test_failed_matching_proof_smoke_quarantines_again(rig, monkeypatch):
    _, _, fresh = fresh_resume(rig)
    monkeypatch.delenv("LEAN_SLOT_SKIP_SUPERVISOR")
    rig.modules.sup.Supervisor(rig.ctl.inventory).start_proxy(1)
    http = HTTP(rig, fail_smoke=True)
    monkeypatch.setattr(rig.modules.sup.http.client, "HTTPConnection", http.connection)
    with pytest.raises(RuntimeError, match="clean positive terminal RPC"):
        rig.ctl.checkpoint_resume(fresh)
    assert http.states == ["ACTIVE"]
    gate_denied(rig)


def test_checkpoint_prepare_preflight_catches_current_base_collision_before_first_reset(rig):
    _, original, _ = fresh_resume(rig)
    rig.ctl.release(1)
    # The new canonical base introduces an ignored tracked target.
    (rig.repo / "obstruction").write_text("new canonical bytes")
    run(rig.repo, "git", "add", "-f", "obstruction")
    run(rig.repo, "git", "commit", "-m", "new base target")
    rig.ctl.build()
    (rig.trees[0] / "obstruction").write_text("current destination owner")
    rig.ctl.acquire(1, client="codex", base_ref="main")
    old_head = run(rig.trees[0], "git", "rev-parse", "HEAD")
    with pytest.raises(RuntimeError, match="destination collision"):
        rig.ctl.prepare(1, checkpoint_request={**original, "classifications": classes(rig)})
    assert run(rig.trees[0], "git", "rev-parse", "HEAD") == old_head
    assert (rig.trees[0] / "obstruction").read_text() == "current destination owner"


@pytest.mark.parametrize("crash", [None, "legacy-generation-intent", "lease-write", "legacy-generation-complete"])
def test_legacy_live_lease_gets_official_journal_bound_generation_without_losing_original_bytes(rig, monkeypatch, crash):
    wip(rig)
    # Simulate bytes emitted by the unchanged pre-generation canonical controller.
    lease_path = rig.ctl.inventory.lease_path(1)
    legacy = rig.ctl.inventory.lease(1)
    legacy.pop("lease_generation")
    rig.modules.state.durable_json(lease_path, legacy)
    original = lease_path.read_bytes()
    req = request(rig)
    if crash:
        fired = []
        def interrupt(self, phase):
            if phase == crash and not fired:
                fired.append(phase)
                raise KeyboardInterrupt("legacy migration crash")
        monkeypatch.setattr(rig.modules.cp.CheckpointTransaction, "boundary", interrupt)
        with pytest.raises(KeyboardInterrupt):
            rig.ctl.checkpoint(req)
        assert fired
        monkeypatch.setattr(rig.modules.cp.CheckpointTransaction, "boundary", lambda *_: None)
        journal = rig.ctl.checkpoint(req, recover=True)
    else:
        journal = rig.ctl.checkpoint(req)
    assert bytes.fromhex(journal["original_lease_bytes"]) == original
    assert "lease_generation" not in journal["original_lease"]
    assert len(rig.ctl.inventory.lease(1)["lease_generation"]) == 48
    assert journal["generation"] != journal["drain_generation"]
    assert journal["phase"] == "eligible-canonical-release"
    gate_denied(rig)
    later = rig.ctl.inventory.lease(1)
    later["lease_generation"] = "later-owner-generation"
    rig.modules.state.durable_json(lease_path, later)
    before = lease_path.read_bytes()
    with pytest.raises(RuntimeError, match="later lease generation"):
        rig.ctl.checkpoint(req, recover=True)
    assert lease_path.read_bytes() == before


def test_actual_preservation_flushes_every_payload_ref_and_directory(rig, monkeypatch):
    wip(rig)
    req = request(rig)
    real = os.fsync
    flushed = set()
    def observed(fd):
        value = os.fstat(fd)
        flushed.add((value.st_dev, value.st_ino))
        return real(fd)
    monkeypatch.setattr(os, "fsync", observed)
    journal = rig.ctl.checkpoint(req)
    store = Path(journal["binding"]["common_git"]) / "lean-checkpoint-data" / "proof"
    paths = [store, *store.rglob("*"), rig.ctl.inventory.lease_path(1), rig.ctl.inventory.lease_path(1).parent,
             rig.ctl.inventory.state_root / "checkpoints", Path(journal["binding"]["common_git"]) / "refs/lean-checkpoints/proof/source"]
    for leaf, root in ((store, Path(journal["binding"]["common_git"])),
                       (paths[-1].parent, Path(journal["binding"]["common_git"])),
                       (Path(journal["binding"]["common_git"]) / "logs/refs/lean-checkpoints/proof", Path(journal["binding"]["common_git"])),
                       (rig.ctl.inventory.state_root / "checkpoints", rig.ctl.inventory.state_root)):
        while leaf != root:
            paths.append(leaf)
            leaf = leaf.parent
        paths.append(root)
    for path in paths:
        info = path.stat()
        assert (info.st_dev, info.st_ino) in flushed, f"actual durable bytes/directory never flushed: {path}"


def test_dirty_source_is_rejected_by_actual_manifest_before_request_can_be_bound(rig):
    wip(rig)
    (rig.trees[0] / "lean/Theorem.lean").write_text("dirty source must survive")
    with pytest.raises(RuntimeError, match="clean tracked source/index"):
        request(rig)
    assert (rig.trees[0] / "lean/Theorem.lean").read_text() == "dirty source must survive"


@pytest.mark.parametrize("phase", ["copies-flushed", "reset-intent", "stopped"])
def test_concurrent_dirty_source_is_reobserved_after_protection_and_before_reset(rig, monkeypatch, phase):
    head = wip(rig)
    req = request(rig)
    def changed(self, current):
        if current == phase:
            (rig.trees[0] / "lean/Theorem.lean").write_text("later source owner bytes")
    monkeypatch.setattr(rig.modules.cp.CheckpointTransaction, "boundary", changed)
    with pytest.raises(RuntimeError, match="clean tracked|source changed|source drift"):
        rig.ctl.checkpoint(req)
    assert run(rig.trees[0], "git", "rev-parse", "HEAD") == head
    assert (rig.trees[0] / "lean/Theorem.lean").read_text() == "later source owner bytes"


def test_missing_copied_source_or_changed_ref_blocks_every_recovery(rig):
    head = wip(rig)
    req = request(rig)
    journal = rig.ctl.checkpoint(req)
    store = Path(journal["binding"]["common_git"]) / "lean-checkpoint-data" / "proof"
    (store / "source" / "lean/Theorem.lean").unlink()
    with pytest.raises(RuntimeError, match="input unavailable"):
        rig.ctl.checkpoint(req, recover=True)
    gate_denied(rig)
    # Restore the fixture payload independently, then retarget the real ref.
    (store / "source" / "lean/Theorem.lean").write_text("-- unfinished full theorem\n")
    run(rig.repo, "git", "update-ref", "refs/lean-checkpoints/proof/source", req["original_base_sha"], head)
    with pytest.raises(RuntimeError, match="ref changed"):
        rig.ctl.checkpoint(req, recover=True)
    gate_denied(rig)


def test_preservation_ref_never_changes_ordinary_containment_or_ready_route(rig):
    head = wip(rig)
    run(rig.repo, "git", "update-ref", "refs/lean-checkpoints/independent/source", head)
    assert rig.ctl._is_absorbed(rig.trees[0], rig.ctl.inventory.lease(1))[0] is False
    with pytest.raises(RuntimeError, match="unabsorbed|not contained|not reachable"):
        rig.ctl.release(1)
    assert run(rig.trees[0], "git", "rev-parse", "HEAD") == head


def test_candidate_inventory_alone_never_grants_source_identity_authority(rig):
    wip(rig)
    req = request(rig)
    _, selected = candidate(rig)
    controller = selected.ctl.Controller(selected.state.Inventory.load(rig.ctl.inventory.source))
    with pytest.raises(RuntimeError, match="normally integrated canonical code"):
        controller.checkpoint(req)
    assert not (rig.ctl.inventory.state_root / "checkpoints").exists()


def test_current_cache_owner_cannot_conceal_ignored_source(rig):
    wip(rig)
    classification = classes(rig)
    name = "lean/.lake/proof.lean"
    (rig.trees[0] / name).write_text("unique ignored proof source")
    classification[name] = {"kind": "cache", "owner": "Controller._replace_lake", "owner_source": {"path": str(rig.repo / name), "sha256": "0" * 64}}
    with pytest.raises(RuntimeError, match="input unavailable|authoritative cache owner"):
        rig.modules.cp.source_manifest(rig.trees[0], classification)
    assert (rig.trees[0] / name).read_text() == "unique ignored proof source"


def test_late_native_occupancy_is_reobserved_after_reset_intent(rig, monkeypatch):
    head = wip(rig)
    req = request(rig)
    def appeared(self, phase):
        if phase == "reset-intent":
            rig.host.add(910099, f"lean --server {rig.ctl.inventory.lean_root(1)}")
    monkeypatch.setattr(rig.modules.cp.CheckpointTransaction, "boundary", appeared)
    with pytest.raises(RuntimeError, match="fixed-project process remains"):
        rig.ctl.checkpoint(req)
    assert rig.host.signals == []
    assert run(rig.trees[0], "git", "rev-parse", "HEAD") == head
    gate_denied(rig)


def test_paired_shared_source_checkpoint_and_canonical_release_account_for_running_counterpart(downstream_repo, isolated_process_observations, tmp_path, monkeypatch):
    down, public, repo, trees = downstream_repo
    shared_root = public.repo
    shutil.copytree(ROOT / "scripts" / "lean_slots", shared_root / "scripts" / "lean_slots", ignore=shutil.ignore_patterns("__pycache__"))
    wrapper = ("import sys\nfrom pathlib import Path\n"
               f"SELECTED_SCRIPTS = Path({str(shared_root / 'scripts')!r})\n"
               "sys.path.insert(0, str(SELECTED_SCRIPTS))\nfrom lean_slots.cli import main\n"
               "if __name__ == '__main__':\n    raise SystemExit(main())\n")
    (shared_root / "scripts/slotctl.py").write_text(wrapper)
    (repo / "scripts/slotctl.py").write_text(wrapper)
    for primary in (shared_root, repo):
        run(primary, "git", "add", "scripts")
        run(primary, "git", "commit", "-m", "fixture supported shared canonical source route")
    for number in (1, 2, 3):
        run(public.inventory.worktree(number), "git", "reset", "--hard", "main")
        run(trees[number - 1], "git", "reset", "--hard", "main")
    modules = load_package(shared_root)
    controller = modules.ctl.Controller(modules.state.Inventory.load(down.inventory.source))
    controller.build()
    controller.acquire(1, client="codex", base_ref="main")
    controller.prepare(1)
    evidence = tmp_path / "pair-evidence"
    evidence.mkdir()
    (evidence / "failure.txt").write_text("original full paired scientific obligations")
    pair = SimpleNamespace(ctl=controller, repo=repo, trees=trees, modules=modules, evidence=evidence, host=isolated_process_observations)
    wip(pair)
    req = request(pair)
    journal = controller.checkpoint(req)
    assert journal["canonical_implementation"]["root"] == str(shared_root)
    assert journal["binding"]["repo"] == str(repo)
    assert len(journal["request"]["native_bindings"]) == 2
    gate_denied(pair)
    monkeypatch.delenv("LEAN_SLOT_SKIP_SUPERVISOR")
    controller.release(1)
    observed = controller.checkpoint_observe_release(req)
    assert controller.inventory.lease(1, required=False) is None
    assert observed["release_census"]["complete"]
    assert observed["release_census"]["reserved_physical_slots"] == [1]
    assert "public" in observed["release_census"]["owners"][1]
    assert pair.host.launches


def test_same_base_resume_copies_actual_ignored_source_bytes_into_fresh_other_slot(rig, monkeypatch):
    wip(rig)
    (rig.trees[0] / "ignored-proof.lean").write_text("full ignored proof source bytes\n")
    original = request(rig)
    journal = rig.ctl.checkpoint(original)
    rig.ctl.release(1)
    rig.ctl.acquire(2, client="codex", base_ref="main")
    preflight = {**original, "slot": 2, "classifications": classes(rig, 2)}
    rig.ctl.prepare(2, checkpoint_request=preflight)
    fresh = request(rig, number=2, contract=original["contract"])
    monkeypatch.delenv("LEAN_SLOT_SKIP_SUPERVISOR")
    rig.modules.sup.Supervisor(rig.ctl.inventory).start_proxy(2)
    http = HTTP(rig, number=2)
    monkeypatch.setattr(rig.modules.sup.http.client, "HTTPConnection", http.connection)
    def denied(self, phase):
        if phase in {"resume-source-intent", "resume-source-effect", "resume-copy-intent", "resume-source-complete"}:
            gate_denied(rig, 2)
    monkeypatch.setattr(rig.modules.cp.CheckpointTransaction, "boundary", denied)
    resumed = rig.ctl.checkpoint_resume(fresh)
    assert resumed["phase"] == "resumed"
    assert (rig.trees[1] / "ignored-proof.lean").read_bytes() == (rig.trees[0] / "ignored-proof.lean").read_bytes() == b"full ignored proof source bytes\n"
    store = Path(journal["binding"]["common_git"]) / "lean-checkpoint-data/proof"
    assert (store / "source/ignored-proof.lean").read_bytes() == b"full ignored proof source bytes\n"
    assert resumed["original_lease"]["slot"] == 1
    assert resumed["transaction_lease"]["slot"] == 2
    assert resumed["contract"] == original["contract"]


def test_recursive_evidence_closure_copies_raw_artifacts_and_protected_source_references(rig):
    wip(rig)
    raw = rig.evidence / "raw-native.stdout"
    raw.write_bytes(b"original exact stdout\x00full failure bytes\n")
    report = rig.evidence / "full-report.json"
    report.write_text(json.dumps({"raw": rig.modules.cp.file_binding(raw), "source": rig.modules.cp.file_binding(rig.trees[0] / "lean/Theorem.lean")}))
    req = request(rig)
    req["contract"]["evidence"].append(rig.modules.cp.file_binding(report))
    req["evidence_roots"].append(str(rig.trees[0]))
    journal = rig.ctl.checkpoint(req)
    store = Path(journal["binding"]["common_git"]) / "lean-checkpoint-data/proof"
    receipt = rig.modules.cp.read_json(store / "complete.json")
    for original in (raw, report):
        assert str(original) in receipt["evidence"]
        payload = store / "evidence" / rig.modules.cp.sha256_bytes(str(original).encode())
        assert payload.read_bytes() == original.read_bytes()
    assert str(rig.trees[0] / "lean/Theorem.lean") in receipt["evidence"]
    rig.ctl.release(1)
    assert rig.ctl.checkpoint_observe_release(req)["phase"] == "canonical-release-observed"
    assert (store / "source/lean/Theorem.lean").read_text() == "-- unfinished full theorem\n"


def test_missing_nested_evidence_reference_refuses_before_reset(rig):
    head = wip(rig)
    report = rig.evidence / "incomplete-report.json"
    report.write_text(json.dumps({"raw": {"path": str(rig.evidence / "missing.stdout"), "sha256": "a" * 64}}))
    req = request(rig)
    req["contract"]["evidence"].append(rig.modules.cp.file_binding(report))
    with pytest.raises((RuntimeError, OSError)):
        rig.ctl.checkpoint(req)
    assert run(rig.trees[0], "git", "rev-parse", "HEAD") == head
    assert (rig.trees[0] / "lean/Theorem.lean").exists()


def test_missing_reachable_git_object_refuses_before_reset_even_with_live_source_bytes(rig):
    head = wip(rig)
    req = request(rig)
    blob = run(rig.trees[0], "git", "rev-parse", "HEAD:lean/Theorem.lean")
    objects = Path(req["binding"]["common_git"]) / "objects"
    (objects / blob[:2] / blob[2:]).unlink()
    with pytest.raises(RuntimeError, match="fsck|missing|bad object"):
        rig.ctl.checkpoint(req)
    assert run(rig.trees[0], "git", "rev-parse", "HEAD") == head
    assert (rig.trees[0] / "lean/Theorem.lean").read_text() == "-- unfinished full theorem\n"


def test_final_capable_global_census_is_required_after_stop(rig, monkeypatch):
    head = wip(rig)
    req = request(rig)
    def denied(self, phase):
        if phase == "stopped":
            rig.host.census_denied = True
    monkeypatch.setattr(rig.modules.cp.CheckpointTransaction, "boundary", denied)
    with pytest.raises(RuntimeError, match="process census unavailable"):
        rig.ctl.checkpoint(req)
    assert rig.host.signals == []
    assert run(rig.trees[0], "git", "rev-parse", "HEAD") == head
    gate_denied(rig)


@pytest.mark.parametrize("later_owner", [False, True])
def test_lease_disappearance_or_replacement_after_intent_cannot_be_recreated_or_overwritten(rig, monkeypatch, later_owner):
    head = wip(rig)
    req = request(rig)
    path = rig.ctl.inventory.lease_path(1)
    replacement = []
    def changed(self, phase):
        if phase == "lease-intent" and not replacement:
            if later_owner:
                lease = rig.ctl.inventory.lease(1)
                lease["lease_generation"] = "later legitimate generation"
                rig.modules.state.durable_json(path, lease)
                replacement.append(path.read_bytes())
            else:
                path.unlink()
                replacement.append(None)
    monkeypatch.setattr(rig.modules.cp.CheckpointTransaction, "boundary", changed)
    with pytest.raises(RuntimeError, match="lease changed|input unavailable"):
        rig.ctl.checkpoint(req)
    assert replacement
    if later_owner:
        assert path.read_bytes() == replacement[0]
    else:
        assert not path.exists()
    assert run(rig.trees[0], "git", "rev-parse", "HEAD") == head
    assert rig.host.signals == []


def test_actual_manifest_requires_explicit_ignored_source_classification(rig):
    wip(rig)
    classification = classes(rig)
    (rig.trees[0] / "ignored-proof.lean").write_bytes(b"unclassified ignored proof source")
    with pytest.raises(RuntimeError, match="unclassified ignored/nontracked entry"):
        rig.modules.cp.source_manifest(rig.trees[0], classification)
    assert (rig.trees[0] / "ignored-proof.lean").read_bytes() == b"unclassified ignored proof source"


@pytest.mark.parametrize("damage", ["missing-bytes", "mismatched-id", "nonterminal"])
def test_independent_drain_requires_actual_matching_terminal_rpc_bytes(rig, damage):
    head = wip(rig)
    req = request(rig)
    receipt_path = Path(req["drain_receipts"][0]["path"])
    receipt = rig.modules.cp.read_json(receipt_path)
    completed = receipt["completed_requests"][0]
    if damage == "missing-bytes":
        completed.pop("request")
        completed.pop("response")
    else:
        artifact = Path(completed["response"]["path"])
        response = rig.modules.cp.read_json(artifact)
        if damage == "mismatched-id":
            response["id"] = "some other call"
        else:
            response.pop("result")
        rig.modules.state.durable_json(artifact, response)
        completed["response"] = rig.modules.cp.file_binding(artifact)
        completed["response_sha256"] = completed["response"]["sha256"]
    rig.modules.state.durable_json(receipt_path, receipt)
    req["drain_receipts"] = [rig.modules.cp.file_binding(receipt_path)]
    with pytest.raises(RuntimeError, match="actual request/response bytes|matching terminal response"):
        rig.ctl.checkpoint(req)
    assert run(rig.trees[0], "git", "rev-parse", "HEAD") == head
    gate_denied(rig)


def test_same_base_resume_restores_exact_source_modes_despite_restrictive_umask(rig, monkeypatch):
    wip(rig)
    ignored = rig.trees[0] / "ignored-proof.lean"
    ignored.write_text("full protected source\n")
    ignored.chmod(0o640)
    (rig.trees[0] / "lean/Theorem.lean").chmod(0o640)
    (rig.trees[0] / "lean").chmod(0o750)
    original = request(rig)
    rig.ctl.checkpoint(original)
    rig.ctl.release(1)
    rig.ctl.acquire(2, client="codex", base_ref="main")
    rig.ctl.prepare(2, checkpoint_request={**original, "slot": 2, "classifications": classes(rig, 2)})
    fresh = request(rig, number=2, contract=original["contract"])
    monkeypatch.delenv("LEAN_SLOT_SKIP_SUPERVISOR")
    rig.modules.sup.Supervisor(rig.ctl.inventory).start_proxy(2)
    monkeypatch.setattr(rig.modules.sup.http.client, "HTTPConnection", HTTP(rig, number=2).connection)
    previous = os.umask(0o077)
    try:
        resumed = rig.ctl.checkpoint_resume(fresh)
    finally:
        os.umask(previous)
    for name, expected_mode in (("ignored-proof.lean", 0o640), ("lean/Theorem.lean", 0o640), ("lean", 0o750)):
        assert resumed["resulting_source"]["entries"][name]["mode"] == expected_mode
        assert (rig.trees[1] / name).stat().st_mode & 0o7777 == expected_mode


@pytest.mark.parametrize("damage", ["schema", "sourceReady"])
def test_recovery_refuses_unknown_journal_version_or_acceptance(rig, damage):
    wip(rig)
    req = request(rig)
    rig.ctl.checkpoint(req)
    path = rig.ctl.inventory.state_root / "checkpoints/proof.json"
    journal = rig.modules.cp.read_json(path)
    journal[damage] = "unknown future version" if damage == "schema" else True
    rig.modules.state.durable_json(path, journal)
    before = rig.ctl.inventory.lease_path(1).read_bytes()
    with pytest.raises(RuntimeError, match="journal version/identity/nonacceptance"):
        rig.ctl.checkpoint(req, recover=True)
    assert rig.ctl.inventory.lease_path(1).read_bytes() == before
    gate_denied(rig)


def test_release_observation_interruption_never_recreates_released_lease(rig, monkeypatch):
    wip(rig)
    req = request(rig)
    rig.ctl.checkpoint(req)
    rig.ctl.release(1)
    def crash(self, phase):
        if phase == "canonical-release-observed":
            raise KeyboardInterrupt("release observation interruption")
    monkeypatch.setattr(rig.modules.cp.CheckpointTransaction, "boundary", crash)
    with pytest.raises(KeyboardInterrupt):
        rig.ctl.checkpoint_observe_release(req)
    assert not rig.ctl.inventory.lease_path(1).exists()
    monkeypatch.setattr(rig.modules.cp.CheckpointTransaction, "boundary", lambda *_: None)
    assert rig.ctl.checkpoint_observe_release(req)["phase"] == "canonical-release-observed"
    with pytest.raises(RuntimeError):
        rig.ctl.checkpoint(req, recover=True)
    assert not rig.ctl.inventory.lease_path(1).exists()


def test_same_owner_same_second_acquisitions_have_distinct_official_generations(rig, monkeypatch):
    rig.ctl.release(1)
    monkeypatch.setattr(rig.modules.ctl, "now_iso", lambda: "2026-10-16T00:00:00Z")
    first = rig.ctl.acquire(1, client="codex", base_ref="main")
    rig.ctl.release(1)
    second = rig.ctl.acquire(1, client="codex", base_ref="main")
    assert {key: value for key, value in first.items() if key != "lease_generation"} == {key: value for key, value in second.items() if key != "lease_generation"}
    assert first["lease_generation"] != second["lease_generation"]
    assert rig.modules.cp.generation(first) != rig.modules.cp.generation(second)


@pytest.mark.parametrize("damage", ["epoch", "source", "evidence"])
def test_resume_reobserves_current_admission_after_active_lease_intent(rig, monkeypatch, damage):
    _, _, fresh = fresh_resume(rig)
    monkeypatch.delenv("LEAN_SLOT_SKIP_SUPERVISOR")
    rig.modules.sup.Supervisor(rig.ctl.inventory).start_proxy(1)
    http = HTTP(rig)
    monkeypatch.setattr(rig.modules.sup.http.client, "HTTPConnection", http.connection)
    fired = []
    active_after_drift = []
    def changed(self, phase):
        if phase == "resume-active" and fired:
            active_after_drift.append(phase)
        transition = (self.journal or {}).get("lease_transition") or {}
        if phase == "lease-intent" and transition.get("after", {}).get("state") == "ACTIVE" and not fired:
            fired.append(phase)
            if damage == "epoch":
                path = rig.ctl.inventory.epoch_path()
                epoch = rig.modules.cp.read_json(path)
                epoch["epoch_id"] = "later epoch under the same base"
                rig.modules.state.durable_json(path, epoch)
            elif damage == "source":
                (rig.trees[0] / "lean/Theorem.lean").write_text("later source bytes must survive")
            else:
                (rig.evidence / "failure.txt").write_text("later evidence bytes must survive")
    monkeypatch.setattr(rig.modules.cp.CheckpointTransaction, "boundary", changed)
    with pytest.raises(RuntimeError):
        rig.ctl.checkpoint_resume(fresh)
    assert fired
    assert active_after_drift == [], "ACTIVE was published after its current admission inputs drifted"
    assert http.states == []
    gate_denied(rig)


@pytest.mark.parametrize("damage", ["ref", "evidence", "payload"])
def test_reset_reobserves_protected_material_after_final_native_census(rig, monkeypatch, damage):
    head = wip(rig)
    req = request(rig)
    fired = []
    def changed(self, phase):
        if phase == "quiescence-observed" and self.journal.get("reset_intent") and not fired:
            fired.append(phase)
            if damage == "ref":
                run(rig.repo, "git", "update-ref", self.ref, req["original_base_sha"])
            elif damage == "evidence":
                (rig.evidence / "failure.txt").write_text("later evidence bytes must survive")
            else:
                (self.store / "source/lean/Theorem.lean").write_text("changed payload")
    monkeypatch.setattr(rig.modules.cp.CheckpointTransaction, "boundary", changed)
    with pytest.raises(RuntimeError, match="ref changed|evidence drift|payload drift"):
        rig.ctl.checkpoint(req)
    assert fired
    assert run(rig.trees[0], "git", "rev-parse", "HEAD") == head
    gate_denied(rig)


@pytest.mark.parametrize("directory", [False, True])
def test_prepare_request_cannot_preflight_another_acquired_slot_before_target_reset(rig, directory):
    wip(rig)
    original = request(rig)
    rig.ctl.checkpoint(original)
    rig.ctl.release(1)
    # New main starts tracking a path that is ignored in both older worktrees.
    (rig.repo / "obstruction").write_text("new upstream tracked target")
    run(rig.repo, "git", "add", "-f", "obstruction")
    run(rig.repo, "git", "commit", "-m", "new base tracks former ignored path")
    rig.ctl.build()
    first = rig.ctl.acquire(1, client="codex", base_ref="main")
    second = rig.ctl.acquire(2, client="codex", base_ref="main")
    assert first["state"] == second["state"] == "ACQUIRED"
    assert rig.modules.cp.owner(first) == rig.modules.cp.owner(second)
    target = rig.trees[1] / "obstruction"
    if directory:
        target.mkdir()
        owner_path = target / "owner.txt"
    else:
        owner_path = target
    owner_path.write_bytes(b"later destination owner bytes must survive")
    assert not (rig.trees[0] / "obstruction").exists()
    def snapshot():
        state = {}
        for root in (rig.repo, *rig.trees, rig.ctl.inventory.state_root):
            for path in (root, *root.rglob("*")):
                if path.is_symlink():
                    state[str(path)] = ("symlink", os.readlink(path))
                elif path.is_file():
                    state[str(path)] = ("file", path.stat().st_mode, path.read_bytes())
                elif path.is_dir():
                    state[str(path)] = ("directory", path.stat().st_mode)
        return state
    before = snapshot()
    launches, signals = list(rig.host.launches), list(rig.host.signals)
    caught = None
    try:
        # The request names wt1; the actual prepare target/lock is wt2.
        rig.ctl.prepare(2, checkpoint_request=original)
    except RuntimeError as exc:
        caught = exc
    actual_owner_bytes = owner_path.read_bytes() if owner_path.is_file() else None
    assert actual_owner_bytes == b"later destination owner bytes must survive", "prepare overwrote destination-owner bytes"
    assert snapshot() == before, "mismatched prepare changed source/index/ref/cache/lease/process bytes before refusal"
    assert rig.host.launches == launches and rig.host.signals == signals
    assert caught is not None and "request slot" in str(caught) and "command slot" in str(caught)


@pytest.mark.parametrize("death", ["before-active", "after-active", "during-smoke", "after-smoke", "after-journal", "after-completed"])
def test_cp7_true_death_pending_resume_denies_actual_proxy_client(rig, monkeypatch, death):
    """Real os._exit and production HTTP handler/LeaseGate, living ROOT owner.

    Backend observations during the transaction remain the explicit Host model.
    The post-death client and peer are real sockets. This control is no native
    backend/Lean acceptance; it measures the actual production dispatch reader.
    """
    _, original, fresh = fresh_resume(rig)
    monkeypatch.delenv("LEAN_SLOT_SKIP_SUPERVISOR")
    rig.modules.sup.Supervisor(rig.ctl.inventory).start_proxy(1)
    child = os.fork()
    if child == 0:
        error = rig.evidence / "cp7-child-error.txt"
        try:
            rig.host.add(os.getpid(), "owned disposable CP7 checkpoint child")
            modeled_http = HTTP(rig)
            base_connection = modeled_http.connection
            def connection(*args, **kwargs):
                value = base_connection(*args, **kwargs)
                original_request = value.request
                def send(method, path, body=None, headers=None):
                    original_request(method, path, body, headers)
                    if death == "during-smoke" and body and json.loads(body).get("method") == "tools/call":
                        os._exit(75)
                value.request = send
                return value
            rig.modules.sup.http.client.HTTPConnection = connection
            def abrupt(self, phase):
                state = rig.ctl.inventory.lease(1)["state"]
                if ((death == "before-active" and phase == "resume-reactivate-intent") or
                        (death == "after-active" and phase == "lease-write" and state == "ACTIVE") or
                        (death == "after-smoke" and phase == "resume-smoke-complete") or
                        (death == "after-journal" and phase == "resume-journal-completed") or
                        (death == "after-completed" and phase == "resume-admission-completed")):
                    os._exit(75)
            rig.modules.cp.CheckpointTransaction.boundary = abrupt
            rig.ctl.checkpoint_resume(fresh)
            os._exit(76)
        except BaseException:
            import traceback
            error.write_text(traceback.format_exc())
            os._exit(77)
    actual_pid, status = os.waitpid(child, 0)
    assert actual_pid == child and os.waitstatus_to_exitcode(status) == 75, (rig.evidence / "cp7-child-error.txt").read_text() if (rig.evidence / "cp7-child-error.txt").exists() else status
    journal = rig.modules.cp.journal_checked(rig.ctl.inventory.state_root / "checkpoints/proof.json", "proof")
    if death not in {"after-journal", "after-completed"}:
        assert journal["phase"] != "resumed"
    assert journal["contract"] == original["contract"] and journal["sourceReady"] is False
    inv = rig.ctl.inventory
    class Peer(BaseHTTPRequestHandler):
        def log_message(self, *_):
            pass
        def do_POST(self):
            value = json.loads(self.rfile.read(int(self.headers.get("Content-Length", "0"))))
            data = json.dumps({"jsonrpc": "2.0", "id": value.get("id"), "result": {"peer": "controlled CP7 reader audit"}}).encode()
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(data)))
            self.send_header("Mcp-Session-Id", "owned-cp7-peer")
            self.end_headers()
            self.wfile.write(data)
    peer = ThreadingHTTPServer(("127.0.0.1", int(inv.slot(1)["backend_port"])), Peer)
    proxy = ThreadingHTTPServer(("127.0.0.1", 0), rig.modules.proxy.make_handler(inv, 1))
    with monkeypatch.context() as native:
        native.setattr(socket, "create_connection", NATIVE_CONNECT)
        native.setattr(http.client, "HTTPConnection", NATIVE_HTTP)
        threads = [threading.Thread(target=server.serve_forever, daemon=True) for server in (peer, proxy)]
        for thread in threads:
            thread.start()
        try:
            client = NATIVE_HTTP("127.0.0.1", proxy.server_address[1], timeout=5)
            wire = json.dumps({"jsonrpc": "2.0", "id": "ordinary-after-death", "method": "tools/call", "params": {"name": "lean_diagnostic_messages", "arguments": {"file_path": "Theorem.lean"}}})
            client.request("POST", "/mcp?client=codex", wire, {"Authorization": "Bearer " + inv.token("codex"), "Content-Type": "application/json"})
            response = client.getresponse()
            body, response_status = response.read(), response.status
            (rig.evidence / "cp7-post-death-response.json").write_bytes(body)
            client.close()
        finally:
            for server in (proxy, peer):
                server.shutdown()
                server.server_close()
            for thread in threads:
                thread.join(timeout=5)
    expected_status = 200 if death == "after-completed" else 403
    assert response_status == expected_status, f"CP7 death={death} unexpected ordinary response: status={response_status} body={body!r} phase={journal['phase']}"


def test_cp_git_actual_start_barrier_native_binding_and_both_guard_descriptions(rig, monkeypatch):
    wip(rig)
    req = request(rig)
    observed = []
    def audit(self, phase):
        if phase not in {"mutation-launched-blocked", "mutation-bound"}:
            return
        mutation = self.journal["mutation"]
        if mutation["argv"][-5] != "update-ref":
            return
        pid = next(iter(rig.host.checkpoint_children))
        # Actual lsof on exactly the owned disposable child, independent of the
        # backend Host model and independent of the production guard verdict.
        with monkeypatch.context() as native:
            native.setattr(rig.modules.cp.subprocess, "Popen", rig.host.real_popen)
            result = rig.host.real_run(["lsof", "-nP", "-a", "-p", str(pid),
                *[str(row["path"].with_name(row["path"].name + ".cp-guard")) for row in self.context.held]], capture_output=True, text=True, timeout=5)
        assert not (self.common / self.ref).exists(), "Git wrote before durable native launch binding/start authorization"
        assert result.returncode == 0 and not result.stderr
        for held in self.context.held:
            assert str(held["path"]) + ".cp-guard" in result.stdout, "mutating child dropped a required guard"
        durable = self.inv.state_root / "checkpoints/proof.json"
        record = rig.modules.cp.journal_checked(durable, "proof")
        assert record["mutation"] == mutation
        if phase == "mutation-bound":
            assert mutation["native"]["pid"] == pid and mutation["native"]["birth"]
            assert len(mutation["guards"]) == 2
        observed.append(phase)
    monkeypatch.setattr(rig.modules.cp.CheckpointTransaction, "boundary", audit)
    result = rig.ctl.checkpoint(req)
    assert observed == ["mutation-launched-blocked", "mutation-bound"]
    assert result["phase"] == "eligible-canonical-release"
    assert result["mutation"]["completed"] and result["mutation"]["returncode"] == 0
    assert result["mutation_history"][0]["completed"]


@pytest.mark.parametrize("helper", ["reference-transaction", "core.fsmonitor", "filter-source", "core.worktree", "checkout.workers"])
def test_cp_git_unproved_helper_refuses_before_ref_or_reset(rig, helper):
    head = wip(rig)
    req = request(rig)
    transaction = rig.modules.cp.CheckpointTransaction(rig.ctl, req)
    marker = rig.evidence / "unsupported-helper-wrote"
    if helper == "reference-transaction":
        hook = rig.repo / ".git/hooks/reference-transaction"
        hook.write_text("#!/bin/sh\nprintf 'unbounded helper' > " + shlex.quote(str(marker)) + "\nexit 0\n")
        hook.chmod(0o700)
    elif helper == "filter-source":
        commit(rig.trees[0], ".gitattributes", "*.lean filter=unproved\n")
        # Bind the now changed WIP honestly; the helper configuration is still
        # rejected independently before any checkpoint Git mutation.
        run(rig.repo, "git", "config", "filter.unproved.smudge", "false")
        req = request(rig)
        head = run(rig.trees[0], "git", "rev-parse", "HEAD")
    elif helper == "core.worktree":
        redirected = rig.evidence / "unproved-worktree"
        redirected.mkdir()
        (redirected / "owner.txt").write_text("different destination owner")
        run(rig.repo, "git", "config", "core.worktree", str(redirected))
    elif helper == "checkout.workers":
        run(rig.repo, "git", "config", "checkout.workers", "2")
        run(rig.repo, "git", "config", "checkout.thresholdForParallelism", "0")
    else:
        hook = rig.evidence / "unsupported-fsmonitor"
        hook.write_text("#!/bin/sh\nprintf 'unbounded helper' > " + shlex.quote(str(marker)) + "\nprintf '\\0'\n")
        hook.chmod(0o700)
        run(rig.repo, "git", "config", "core.fsmonitor", str(hook))
    if helper == "core.worktree":
        # The full endpoint already refuses the redirected inventory earlier.
        # Also reach the mutation policy with its original admitted domain so
        # removing this defense cannot be hidden by that independent refusal.
        with pytest.raises(RuntimeError, match="unbounded"):
            transaction._mutation_policy(rig.trees[0], head)
    with pytest.raises(RuntimeError, match="unproved|unbounded|canonical domain unavailable"):
        rig.ctl.checkpoint(req)
    assert not marker.exists()
    assert not (rig.repo / ".git/refs/lean-checkpoints/proof/source").exists()
    assert run(rig.trees[0], "git", "rev-parse", "HEAD") == head
    if helper == "core.worktree":
        assert (redirected / "owner.txt").read_text() == "different destination owner"


def test_unreadable_effective_attributes_are_not_silently_treated_as_absent(rig):
    wip(rig)
    req = request(rig)
    path = rig.evidence / "denied-git-attributes"
    path.write_text("*.lean filter=unproved\n")
    path.chmod(0)
    run(rig.repo, "git", "config", "core.attributesFile", str(path))
    try:
        with pytest.raises(RuntimeError, match="Git.*refused"):
            rig.ctl.checkpoint(req)
    finally:
        path.chmod(0o600)
    assert not (rig.repo / ".git/refs/lean-checkpoints/proof/source").exists()


def complete_resume(rig, monkeypatch):
    _, original, fresh = fresh_resume(rig)
    monkeypatch.delenv("LEAN_SLOT_SKIP_SUPERVISOR")
    rig.modules.sup.Supervisor(rig.ctl.inventory).start_proxy(1)
    http = HTTP(rig)
    monkeypatch.setattr(rig.modules.sup.http.client, "HTTPConnection", http.connection)
    return original, fresh, rig.ctl.checkpoint_resume(fresh)


@pytest.mark.parametrize("auth", ["trusted-local", "bearer"])
@pytest.mark.parametrize("owner_kind", ["process", "session"])
def test_completed_admission_survives_heartbeat_and_ordinary_proof_edits(rig, monkeypatch, auth, owner_kind):
    if auth != rig.ctl.inventory.client_auth_mode:
        rig.ctl.release(1)
        rig.modules.sup.Supervisor(rig.ctl.inventory).stop_proxy(1)
        raw = json.loads(rig.ctl.inventory.source.read_bytes())
        raw["server"]["client_auth"] = auth
        commit(rig.repo, "config/lean-slots.public.json", json.dumps(raw))
        rig.ctl = rig.modules.ctl.Controller(rig.modules.state.Inventory.load(rig.ctl.inventory.source))
        rig.ctl.build()
        for number in (2, 3):
            rig.ctl.acquire(number, client="codex", base_ref="main")
            rig.ctl.prepare(number)
            rig.ctl.release(number)
        rig.ctl.acquire(1, client="codex", base_ref="main")
        rig.ctl.prepare(1)
    if owner_kind == "session":
        rig.ctl.release(1)
        monkeypatch.delenv("LEAN_SLOT_OWNER_PID")
        monkeypatch.setenv("LEAN_SLOT_OWNER_SESSION", "owned-disposable-readiness-session")
        rig.ctl.acquire(1, client="codex", base_ref="main")
        rig.ctl.prepare(1)
    original, fresh, journal = complete_resume(rig, monkeypatch)
    inv, cp = rig.ctl.inventory, rig.modules.cp
    lease = inv.lease(1)
    assert lease["owner_kind"] == owner_kind and lease["client_auth"] == auth
    context = copy.deepcopy(lease["resume_admission"])
    assert context["state"] == "completed" and journal["readiness"]["status"] == "completed"
    assert cp.generation(lease) == journal["resume"]["generation"]
    before_journal = cp.regular_bytes(inv.state_root / "checkpoints/proof.json")
    gate = rig.modules.proxy.LeaseGate(inv, 1)
    body = json.dumps({"jsonrpc": "2.0", "id": 91, "method": "tools/call", "params": {"name": "lean_goal", "arguments": {"file_path": "Theorem.lean"}}}).encode()
    gate.authorize("codex", rig.modules.state.token_hash(inv.token("codex")), body)
    (inv.lean_root(1) / "Theorem.lean").write_text("-- later ordinary authorized proof work\n")
    heartbeat = rig.ctl.heartbeat(1)
    assert heartbeat["resume_admission"] == context
    assert cp.generation(heartbeat) == cp.generation(lease)
    assert cp.regular_bytes(inv.state_root / "checkpoints/proof.json") == before_journal
    gate.authorize("codex", rig.modules.state.token_hash(inv.token("codex")), body)
    after_heartbeat = inv.lease_path(1).read_bytes()
    completed = rig.ctl.checkpoint_resume(fresh, recover=True)
    assert completed["readiness"] == journal["readiness"]
    assert inv.lease_path(1).read_bytes() == after_heartbeat
    gate.authorize("codex", rig.modules.state.token_hash(inv.token("codex")), body)
    assert journal["contract"] == original["contract"] and journal["sourceReady"] is False
    with pytest.raises(RuntimeError, match="completed readiness"):
        gate.authorize("codex", rig.modules.state.token_hash(inv.token("codex")), body, checkpoint_capability="0" * 64)
    erased = copy.deepcopy(heartbeat)
    erased.pop("resume_admission")
    before = inv.lease_path(1).read_bytes()
    with pytest.raises(RuntimeError, match="cannot erase"):
        inv.save_lease(1, erased)
    assert inv.lease_path(1).read_bytes() == before


def test_actual_reader_denies_context_erasure_and_missing_or_changed_completion(rig, monkeypatch):
    complete_resume(rig, monkeypatch)
    cp, inv = rig.modules.cp, rig.ctl.inventory
    lease_path = inv.lease_path(1)
    journal_path = inv.state_root / "checkpoints/proof.json"
    original_lease, original_journal = lease_path.read_bytes(), journal_path.read_bytes()
    gate = rig.modules.proxy.LeaseGate(inv, 1)
    body = b'{"jsonrpc":"2.0","id":88,"method":"tools/call","params":{"name":"lean_goal","arguments":{}}}'
    credential = rig.modules.state.token_hash(inv.token("codex"))
    gate.authorize("codex", credential, body)
    for damage in ("context", "all-lease-anchors", "missing-journal", "truncated-journal", "receipt", "domain", "generation", "phase", "source-binding"):
        lease, journal = json.loads(original_lease), json.loads(original_journal)
        try:
            if damage == "context":
                lease.pop("resume_admission")
            elif damage == "all-lease-anchors":
                for key in ("resume_admission", "checkpoint", "checkpoint_preflight"):
                    lease.pop(key, None)
            elif damage == "receipt":
                journal["readiness"]["receipt"]["rpc"]["response_hex"] = b'{"jsonrpc":"2.0","id":3,"error":{"message":"not complete"}}'.hex()
            elif damage == "domain":
                lease["resume_admission"]["binding_digest"] = "0" * 64
            elif damage == "generation":
                lease["lease_generation"] = "0" * 48
            elif damage == "phase":
                journal["phase"] = "resume-source-intent"
            elif damage == "source-binding":
                journal["resulting_source"]["entries"]["lean/Theorem.lean"]["sha256"] = "0" * 64
            cp.durable_json(lease_path, lease)
            cp.durable_json(journal_path, journal)
            if damage == "missing-journal":
                journal_path.rename(rig.evidence / "preserved-missing-journal.json")
            elif damage == "truncated-journal":
                journal_path.write_bytes(b"{")
            with pytest.raises(RuntimeError, match="checkpoint"):
                gate.authorize("codex", credential, body)
        finally:
            # Fixture-only malformed-input controls; never an operational repair.
            lease_path.write_bytes(original_lease)
            journal_path.write_bytes(original_journal)
        gate.authorize("codex", credential, body)


def test_completed_reader_revalidates_semantic_smoke_after_consistent_receipt_rebinding(rig, monkeypatch):
    complete_resume(rig, monkeypatch)
    cp, inv = rig.modules.cp, rig.ctl.inventory
    lease_path = inv.lease_path(1)
    journal_path = inv.state_root / "checkpoints/proof.json"
    original_lease, original_journal = lease_path.read_bytes(), journal_path.read_bytes()
    gate = rig.modules.proxy.LeaseGate(inv, 1)
    body = b'{"jsonrpc":"2.0","id":89,"method":"tools/call","params":{"name":"lean_goal","arguments":{}}}'
    credential = rig.modules.state.token_hash(inv.token("codex"))
    gate.authorize("codex", credential, body)
    clean = {"success": True, "timed_out": False, "items": [], "failed_dependencies": []}
    replies = [{"jsonrpc": "2.0", "id": 3, "error": {"message": "actual terminal failure"}}]
    for field, value in (("success", False), ("timed_out", True),
                         ("items", [{"message": "proof error"}]),
                         ("failed_dependencies", ["dependency.lean"])):
        replies.append({"jsonrpc": "2.0", "id": 3,
                        "result": {"structuredContent": {**clean, field: value}}})
    replies.append({"jsonrpc": "2.0", "id": 4, "result": {"structuredContent": clean}})
    for reply in replies:
        lease, journal = json.loads(original_lease), json.loads(original_journal)
        try:
            # Fixture-only corrupted evidence: every byte/hash relation remains
            # consistent, so only the actual terminal RPC semantics can deny it.
            receipt = journal["readiness"]["receipt"]
            response = json.dumps(reply).encode()
            receipt["rpc"]["response_hex"] = response.hex()
            receipt["rpc"]["response_sha256"] = cp.sha256_bytes(response)
            lease["resume_admission"]["completion_sha256"] = cp.canonical_digest(receipt)
            cp.durable_json(journal_path, journal)
            cp.durable_json(lease_path, lease)
            with pytest.raises(RuntimeError, match="checkpoint"):
                gate.authorize("codex", credential, body)
        finally:
            lease_path.write_bytes(original_lease)
            journal_path.write_bytes(original_journal)
        gate.authorize("codex", credential, body)


def test_original_preservation_request_cannot_replay_over_current_resume_generation(rig, monkeypatch):
    original, fresh, journal = complete_resume(rig, monkeypatch)
    inv = rig.ctl.inventory
    path = inv.state_root / "checkpoints/proof.json"
    before = {str(p): p.read_bytes() for p in [path, inv.lease_path(1), *inv.process_path("backend", 1).parent.glob("*.json")]}
    source = {str(p): p.read_bytes() for p in rig.trees[0].rglob("*") if p.is_file()}
    locks = {str(p): p.read_bytes() for p in (inv.state_root / "locks").rglob("*") if p.is_file()}
    signals = list(rig.host.signals)
    for operation in (lambda: rig.ctl.checkpoint(original, recover=True), lambda: rig.ctl.checkpoint_observe_release(original)):
        refused = None
        try:
            operation()
        except RuntimeError as exc:
            refused = str(exc)
        assert all(Path(p).read_bytes() == value for p, value in before.items()), "stale preservation changed the new lease/journal/native bytes"
        assert source == {str(p): p.read_bytes() for p in rig.trees[0].rglob("*") if p.is_file()}
        assert locks == {str(p): p.read_bytes() for p in (inv.state_root / "locks").rglob("*") if p.is_file()}
        assert rig.host.signals == signals
        assert refused is not None and "superseded" in refused and "stale route" in refused
    gate = rig.modules.proxy.LeaseGate(inv, 1)
    gate.authorize("codex", rig.modules.state.token_hash(inv.token("codex")), b'{"method":"tools/call","params":{"name":"lean_goal"}}')
    assert journal["sourceReady"] is False and fresh["contract"] == original["contract"]


def test_pending_reader_allows_only_live_exact_internal_smoke(rig, monkeypatch):
    _, _, fresh = fresh_resume(rig)
    monkeypatch.delenv("LEAN_SLOT_SKIP_SUPERVISOR")
    sup = rig.modules.sup.Supervisor(rig.ctl.inventory)
    sup.start_proxy(1)
    http = HTTP(rig)
    monkeypatch.setattr(rig.modules.sup.http.client, "HTTPConnection", http.connection)
    production = rig.modules.sup.Supervisor.probe
    checked = []
    def inspect(self, *args, **kwargs):
        context = kwargs.get("checkpoint_smoke")
        if context is not None:
            inv = rig.ctl.inventory
            gate = rig.modules.proxy.LeaseGate(inv, 1)
            credential = rig.modules.state.token_hash(inv.token("codex"))
            exact = json.dumps(rig.modules.cp.smoke_payload("Theorem.lean")).encode()
            variants = [(exact, None, "POST"), (exact, "0" * 64, "POST"), (exact, context.capability, "GET"),
                        (exact, context.capability, "DELETE"), (b"[" + exact + b"]", context.capability, "POST")]
            for field, value in (("file_path", "Other.lean"), ("unexpected", "arbitrary code")):
                payload = rig.modules.cp.smoke_payload("Theorem.lean")
                payload["params"]["arguments"][field] = value
                variants.append((json.dumps(payload).encode(), context.capability, "POST"))
            payload = rig.modules.cp.smoke_payload("Theorem.lean")
            payload["params"]["name"] = "lean_goal"
            variants.append((json.dumps(payload).encode(), context.capability, "POST"))
            for body, capability, method in variants:
                with pytest.raises(RuntimeError, match="checkpoint"):
                    gate.authorize("codex", credential, body, http_method=method, checkpoint_capability=capability)
            gate.authorize("codex", credential, exact, checkpoint_capability=context.capability)
            lease_path, journal_path = inv.lease_path(1), inv.state_root / "checkpoints/proof.json"
            before_lease, before_journal = lease_path.read_bytes(), journal_path.read_bytes()
            # A valid capability cannot outlive its distinct CP attempt, even
            # with the original ROOT process and normal owner/auth still valid.
            for key, value in (("pid", 2147483647), ("deadline_unix", 0)):
                lease, journal = json.loads(before_lease), json.loads(before_journal)
                lease["resume_admission"]["attempt"][key] = value
                journal["readiness"]["context"] = copy.deepcopy(lease["resume_admission"])
                try:
                    rig.modules.cp.durable_json(lease_path, lease)
                    rig.modules.cp.durable_json(journal_path, journal)
                    with pytest.raises(RuntimeError, match="checkpoint"):
                        gate.authorize("codex", credential, exact, checkpoint_capability=context.capability)
                finally:
                    lease_path.write_bytes(before_lease)
                    journal_path.write_bytes(before_journal)
            assert context.capability not in json.dumps(rig.modules.cp.read_json(inv.state_root / "checkpoints/proof.json"))
            assert context.capability not in inv.lease_path(1).read_text()
            checked.append(True)
        return production(self, *args, **kwargs)
    monkeypatch.setattr(rig.modules.sup.Supervisor, "probe", inspect)
    result = rig.ctl.checkpoint_resume(fresh)
    assert checked == [True] and result["readiness"]["status"] == "completed"


@pytest.mark.parametrize("change_before_retry", [False, True])
def test_real_pending_proxy_probe_retry_capability_stripping_and_cleanup(rig, monkeypatch, change_before_retry):
    """Actual wire/proxy/probe readers; backend OS remains the disclosed Host."""
    _, _, fresh = fresh_resume(rig)
    monkeypatch.delenv("LEAN_SLOT_SKIP_SUPERVISOR")
    rig.modules.sup.Supervisor(rig.ctl.inventory).start_proxy(1)
    modeled = HTTP(rig)
    monkeypatch.setattr(rig.modules.sup.http.client, "HTTPConnection", modeled.connection)
    production = rig.modules.sup.Supervisor.probe
    records = []
    secrets_seen = []
    class NativeConnection(NATIVE_HTTP):
        def connect(self):
            self.sock = NATIVE_CONNECT((self.host, self.port), self.timeout)
    def real_smoke(self, *args, **kwargs):
        context = kwargs.get("checkpoint_smoke")
        if context is None:
            return production(self, *args, **kwargs)
        inv = rig.ctl.inventory
        secrets_seen.append(context.capability)
        proof_count = 0
        class Peer(BaseHTTPRequestHandler):
            def log_message(self, *_):
                pass
            def do_POST(self):
                nonlocal proof_count
                wire = self.rfile.read(int(self.headers.get("Content-Length", "0")))
                payload = json.loads(wire) if wire else {}
                records.append({"method": self.command, "rpc": payload.get("method"),
                                "header_names": [key.lower() for key in self.headers]})
                assert self.headers.get("Authorization") == "Bearer " + inv.backend_token(1)
                assert not self.headers.get_all(rig.modules.cp.SMOKE_HEADER, [])
                code = 200
                if payload.get("method") == "tools/call":
                    proof_count += 1
                    if proof_count == 1:
                        code = 400
                        result = {"error": {"code": -32602, "message": "controlled stale backend session"}}
                        if change_before_retry:
                            (inv.lean_root(1) / "Theorem.lean").write_text("-- later source owner bytes before retry\n")
                    else:
                        result = {"result": {"structuredContent": {"success": True, "timed_out": False, "items": [], "failed_dependencies": []}}}
                elif payload.get("method") == "tools/list":
                    result = {"result": {"tools": [{"name": "lean_diagnostic_messages"}]}}
                else:
                    result = {"result": {"serverInfo": {"name": "owned retry peer"}}}
                body = json.dumps({"jsonrpc": "2.0", "id": payload.get("id"), **result}).encode()
                self.send_response(code)
                self.send_header("Content-Type", "application/json")
                self.send_header("Content-Length", str(len(body)))
                self.send_header("Mcp-Session-Id", "owned-retry-peer-session")
                self.end_headers()
                self.wfile.write(body)
            do_DELETE = do_POST
        peer = ThreadingHTTPServer(("127.0.0.1", int(inv.slot(1)["backend_port"])), Peer)
        proxy = ThreadingHTTPServer(("127.0.0.1", int(inv.slot(1)["proxy_port"])), rig.modules.proxy.make_handler(inv, 1))
        with monkeypatch.context() as native:
            native.setattr(http.client, "HTTPConnection", NativeConnection)
            threads = [threading.Thread(target=server.serve_forever, daemon=True) for server in (peer, proxy)]
            for thread in threads:
                thread.start()
            try:
                body = json.dumps(rig.modules.cp.smoke_payload("Theorem.lean"))
                before = len(records)
                # The actual reader refuses wrong and repeated headers before
                # any backend handshake/proof. No fixture guard return is used.
                for duplicate in (False, True):
                    client = NativeConnection("127.0.0.1", int(inv.slot(1)["proxy_port"]), timeout=5)
                    client.putrequest("POST", "/mcp?client=codex")
                    client.putheader("Authorization", "Bearer " + inv.token("codex"))
                    client.putheader("Content-Length", str(len(body)))
                    client.putheader(rig.modules.cp.SMOKE_HEADER, context.capability if duplicate else "0" * 64)
                    if duplicate:
                        client.putheader(rig.modules.cp.SMOKE_HEADER, context.capability)
                    client.endheaders(body.encode())
                    response = client.getresponse()
                    denied = response.read()
                    assert response.status == 403 and context.capability.encode() not in denied
                    client.close()
                assert len(records) == before
                return production(self, *args, **kwargs)
            finally:
                for server in (proxy, peer):
                    server.shutdown()
                    server.server_close()
                for thread in threads:
                    thread.join(timeout=5)
                assert proof_count == (1 if change_before_retry else 2)
    monkeypatch.setattr(rig.modules.sup.Supervisor, "probe", real_smoke)
    if change_before_retry:
        with pytest.raises(RuntimeError, match="MCP probe failed"):
            rig.ctl.checkpoint_resume(fresh)
        gate_denied(rig)
        assert (rig.ctl.inventory.lean_root(1) / "Theorem.lean").read_text() == "-- later source owner bytes before retry\n"
    else:
        result = rig.ctl.checkpoint_resume(fresh)
        assert result["readiness"]["status"] == "completed"
        assert any(record["method"] == "DELETE" for record in records)
    durable = (rig.ctl.inventory.state_root / "checkpoints/proof.json").read_bytes() + rig.ctl.inventory.lease_path(1).read_bytes()
    for secret in secrets_seen:
        assert secret.encode() not in durable and secret not in json.dumps(records)


def test_mutator_python_startup_cannot_write_before_native_barrier(rig, monkeypatch):
    wip(rig)
    req = request(rig)
    startup = rig.evidence / "unproved-python-startup"
    startup.mkdir()
    marker = rig.evidence / "startup-before-native-binding"
    (startup / "sitecustomize.py").write_text(f"open({str(marker)!r}, 'w').write('unproved startup ran before CP native binding')\n")
    monkeypatch.setenv("PYTHONPATH", str(startup))
    result = rig.ctl.checkpoint(req)
    assert not marker.exists(), "mutator interpreter startup wrote before its durable native launch binding"
    assert result["phase"] == "eligible-canonical-release"


@pytest.mark.parametrize("variable", ["LD_PRELOAD", "DYLD_INSERT_LIBRARIES", "DYLD_LIBRARY_PATH"])
def test_unproved_loader_environment_refuses_before_any_cp_child_or_effect(rig, monkeypatch, variable):
    wip(rig)
    req = request(rig)
    before = list(rig.host.command_calls)
    lease = rig.ctl.inventory.lease_path(1).read_bytes()
    monkeypatch.setenv(variable, str(rig.evidence / "unproved-loader-input"))
    with pytest.raises(RuntimeError, match="ambient overrides refused"):
        rig.ctl.checkpoint(req)
    assert rig.host.command_calls == before, "Git/native child launched before loader environment refusal"
    assert rig.ctl.inventory.lease_path(1).read_bytes() == lease
    assert not (rig.ctl.inventory.state_root / "checkpoints/proof.json").exists()


def test_unproved_git_script_helper_refuses_before_its_first_write(rig, monkeypatch):
    wip(rig)
    req = request(rig)
    native_git = shutil.which("git")
    helper = rig.evidence / "unproved-git-helper"
    helper.mkdir()
    marker = rig.evidence / "unproved-git-before-binding"
    script = helper / "git"
    script.write_text("#!/bin/sh\nprintf 'unproved Git wrapper' > " + shlex.quote(str(marker)) + "\nexec " + shlex.quote(native_git) + ' "$@"\n')
    script.chmod(0o700)
    monkeypatch.setenv("PATH", str(helper) + os.pathsep + os.environ["PATH"])
    try:
        rig.ctl.checkpoint(req)
    except RuntimeError:
        pass
    assert not marker.exists(), "unproved Git script wrote before CP tool-family admission"
    assert not (rig.ctl.inventory.state_root / "checkpoints/proof.json").exists()


@pytest.mark.parametrize("operation", ["update-ref", "reset"])
def test_mutator_reobserves_source_at_actual_prewrite_barrier(rig, monkeypatch, operation):
    head = wip(rig)
    req = request(rig)
    changed = b"concurrent destination-owner bytes after native binding\n"
    fired = []
    def change(self, phase):
        mutation = (self.journal or {}).get("mutation") or {}
        if phase == "mutation-bound" and operation in mutation.get("argv", []) and not fired:
            (rig.trees[0] / "lean/Theorem.lean").write_bytes(changed)
            fired.append(phase)
    monkeypatch.setattr(rig.modules.cp.CheckpointTransaction, "boundary", change)
    refused = None
    try:
        rig.ctl.checkpoint(req)
    except RuntimeError as exc:
        refused = str(exc)
    assert fired == ["mutation-bound"]
    assert (rig.trees[0] / "lean/Theorem.lean").read_bytes() == changed, "Git overwrote changed source after its last durable prewrite boundary"
    assert run(rig.trees[0], "git", "rev-parse", "HEAD") == head, "Git reset ran against an unprotected preimage"
    if operation == "update-ref":
        assert rig.modules.cp.git(rig.repo, "rev-parse", "--verify", "--quiet", "refs/lean-checkpoints/proof/source", check=False) == b"", "ref effect ran before reobserving its source"
    assert refused is not None


def test_live_journal_mutation_erasure_cannot_authorize_start_or_facade_retirement(rig, monkeypatch):
    head = wip(rig)
    req = request(rig)
    changed = []
    path = rig.ctl.inventory.state_root / "checkpoints/proof.json"
    def corrupt(self, phase):
        if phase == "mutation-bound" and not changed:
            journal = rig.modules.cp.read_json(path)
            journal.pop("mutation")
            rig.modules.state.durable_json(path, journal)
            changed.append(path.read_bytes())
    monkeypatch.setattr(rig.modules.cp.CheckpointTransaction, "boundary", corrupt)
    with pytest.raises(RuntimeError, match="journal byte drift"):
        rig.ctl.checkpoint(req)
    assert changed and path.read_bytes() == changed[0], "unknown journal bytes were overwritten"
    assert run(rig.trees[0], "git", "rev-parse", "HEAD") == head
    assert rig.modules.cp.git(rig.repo, "rev-parse", "--verify", "--quiet", "refs/lean-checkpoints/proof/source", check=False) == b""
    facade = rig.ctl.inventory.state_root / "locks/wt1.lock"
    assert (facade / "owner.json").is_file()
    with pytest.raises(RuntimeError, match="already locked"):
        with rig.modules.state.directory_lock(facade, purpose="ordinary caller"):
            pytest.fail("erased mutation record retired a facade")


@pytest.mark.parametrize("interruption", ["exception", "timeout"])
def test_surviving_admitted_child_keeps_both_guards_after_exception_or_actual_timeout(rig, monkeypatch, interruption):
    import signal
    wip(rig)
    req = request(rig)
    observed = []
    def stop_child(self, phase):
        if phase == "mutation-bound" and not observed:
            identity = copy.deepcopy(self.journal["mutation"]["native"])
            seen = rig.modules.state.observe_shutdown_process(identity["pid"])
            assert seen.state == "present" and seen.identity["birth"] == identity["birth"]
            NATIVE_KILL(identity["pid"], signal.SIGSTOP)
            observed.append(identity)
        if phase == "mutation-started" and interruption == "exception":
            raise RuntimeError("owned fixture interruption after start")
    monkeypatch.setattr(rig.modules.cp.CheckpointTransaction, "boundary", stop_child)
    try:
        caught = None
        try:
            rig.ctl.checkpoint(req)
        except (RuntimeError, TimeoutError) as exc:
            caught = exc
        assert len(observed) == 1
        identity = observed[0]
        seen = rig.modules.state.observe_shutdown_process(identity["pid"])
        assert seen.state == "present" and seen.identity["birth"] == identity["birth"]
        locks = rig.ctl.inventory.state_root / "locks"
        guards = [str(path) for path in locks.glob("*.cp-guard")]
        with monkeypatch.context() as native:
            native.setattr(rig.modules.cp.subprocess, "Popen", rig.host.real_popen)
            result = rig.host.real_run(["lsof", "-nP", "-a", "-p", str(identity["pid"]), *guards], capture_output=True, text=True, timeout=5)
        assert result.returncode == 0 and len(guards) == 2
        assert all(path in result.stdout for path in guards), "exception/timeout dropped a mutator's shared guard"
        for path in guards:
            fd = os.open(path, os.O_RDWR)
            try:
                try:
                    rig.modules.state.fcntl.flock(fd, rig.modules.state.fcntl.LOCK_EX | rig.modules.state.fcntl.LOCK_NB)
                except BlockingIOError:
                    pass
                else:
                    pytest.fail("native kernel guard was released while its admitted child survived")
            finally:
                os.close(fd)  # Only this fresh open description; never LOCK_UN.
        facades = {str(p): p.read_bytes() for p in locks.glob("*.lock/owner.json")}
        legacy_overlap, legacy_denials = [], []
        for facade in (locks / "wt1.lock", locks / "supervisor.lock"):
            try:
                with rig.modules.state.directory_lock(facade, purpose="unchanged legacy caller"):
                    # This is the actual legacy mkdir protocol against the
                    # surviving child's fixture scopes, with no source effects.
                    legacy_overlap.append(str(facade))
            except RuntimeError as exc:
                legacy_denials.append(str(exc))
        assert not legacy_overlap, f"ordinary legacy caller actually acquired a scope while its admitted mutator survived: {legacy_overlap}; kernel guards remained held; retained facades={list(facades)}"
        assert len(facades) == 2
        assert len(legacy_denials) == 2 and all("already locked" in value for value in legacy_denials)
        assert caught is not None and any(value in str(caught) for value in ("mutator still present", "timed out"))
        with pytest.raises(RuntimeError, match="guard unavailable/contended"):
            rig.ctl.checkpoint(req, recover=True)
        assert facades == {str(p): p.read_bytes() for p in locks.glob("*.lock/owner.json")}
    finally:
        if observed:
            identity = observed[0]
            exact = rig.modules.state.observe_shutdown_process(identity["pid"])
            if exact.state == "present" and exact.identity["birth"] == identity["birth"]:
                NATIVE_KILL(identity["pid"], signal.SIGCONT)
                assert os.waitpid(identity["pid"], 0)[0] == identity["pid"]
    monkeypatch.setattr(rig.modules.cp.CheckpointTransaction, "boundary", lambda *_: None)
    assert rig.modules.state.observe_shutdown_process(observed[0]["pid"]).state == "absent"
    # This unit test's actual parent is still the recorded native CP holder.
    # Child completion alone must not grant retirement of that live attempt.
    # The isolated native true-death cases exercise later successful recovery.
    with pytest.raises(RuntimeError, match="native holder is not proven gone"):
        rig.ctl.checkpoint(req, recover=True)
    assert facades == {str(p): p.read_bytes() for p in locks.glob("*.lock/owner.json")}


def checkpoint_reader_http(rig, monkeypatch):
    """Actual production handler/LeaseGate and owned socket peer, no Lean."""
    inv = rig.ctl.inventory
    dispatched = []
    class Peer(BaseHTTPRequestHandler):
        def log_message(self, *_):
            pass
        def do_POST(self):
            wire = self.rfile.read(int(self.headers.get("Content-Length", "0")))
            value = json.loads(wire)
            dispatched.append(value)
            data = json.dumps({"jsonrpc": "2.0", "id": value.get("id"), "result": {"structuredContent": {
                "success": True, "timed_out": False, "items": [], "failed_dependencies": []}}}).encode()
            self.send_response(200)
            self.send_header("Content-Type", "application/json")
            self.send_header("Content-Length", str(len(data)))
            self.send_header("Mcp-Session-Id", "owned-bounded-reader-peer")
            self.end_headers()
            self.wfile.write(data)
    peer = ThreadingHTTPServer(("127.0.0.1", int(inv.slot(1)["backend_port"])), Peer)
    proxy = ThreadingHTTPServer(("127.0.0.1", 0), rig.modules.proxy.make_handler(inv, 1))
    with monkeypatch.context() as native:
        native.setattr(socket, "create_connection", NATIVE_CONNECT)
        native.setattr(http.client, "HTTPConnection", NATIVE_HTTP)
        threads = [threading.Thread(target=server.serve_forever, daemon=True) for server in (peer, proxy)]
        for thread in threads:
            thread.start()
        try:
            client = NATIVE_HTTP("127.0.0.1", proxy.server_address[1], timeout=5)
            wire = json.dumps({"jsonrpc": "2.0", "id": "bounded-reader", "method": "tools/call", "params": {
                "name": "lean_diagnostic_messages", "arguments": {"file_path": "Theorem.lean"}}})
            client.request("POST", "/mcp?client=codex", wire, {"Authorization": "Bearer " + inv.token("codex"), "Content-Type": "application/json"})
            response = client.getresponse()
            status, body = response.status, response.read()
            client.close()
        finally:
            for server in (proxy, peer):
                server.shutdown()
                server.server_close()
            for thread in threads:
                thread.join(timeout=5)
    return status, body, dispatched


@pytest.mark.parametrize("anchored", [False, True])
@pytest.mark.parametrize("growth_after_fstat", [False, True])
def test_actual_proxy_bounds_anchored_and_unrelated_journal_bytes_before_dispatch(rig, monkeypatch, anchored, growth_after_fstat):
    cp, inv = rig.modules.cp, rig.ctl.inventory
    maximum = rig.modules.state.MAX_JSON_BYTES
    root = inv.state_root / "checkpoints"
    root.mkdir(exist_ok=True)
    identifier = "anchored" if anchored else "unrelated"
    path = root / f"{identifier}.json"
    cp.durable_json(path, {"schema": cp.SCHEMA, "id": identifier, "sourceReady": False})
    if anchored:
        lease = inv.lease(1)
        lease["checkpoint"] = identifier
        cp.durable_json(inv.lease_path(1), lease)  # Disposable malformed-input fixture only.
    if not growth_after_fstat:
        with path.open("ab") as stream:
            stream.write(b" " * maximum)
    original_open = Path.open
    sizes = []
    class ObserveRead:
        def __init__(self, stream):
            self.stream = stream
        def __enter__(self):
            self.stream.__enter__()
            return self
        def __exit__(self, *args):
            return self.stream.__exit__(*args)
        def fileno(self):
            return self.stream.fileno()
        def read(self, size=-1):
            sizes.append(size)
            if growth_after_fstat:
                # The production reader has already observed the opened inode's
                # size. A size-only precheck cannot prevent this actual growth.
                with original_open(path, "ab") as writer:
                    writer.write(b" " * maximum)
            return self.stream.read(size)
    def observed_open(current, *args, **kwargs):
        stream = original_open(current, *args, **kwargs)
        mode = args[0] if args else kwargs.get("mode", "r")
        return ObserveRead(stream) if current == path and mode == "rb" else stream
    monkeypatch.setattr(Path, "open", observed_open)
    status, body, dispatched = checkpoint_reader_http(rig, monkeypatch)
    assert status == 403 and dispatched == [], (status, body, dispatched, sizes)
    assert sizes == ([maximum + 1] if growth_after_fstat else []), "journal allocated an unbounded read or read a pre-sized oversized inode"
    assert b"bound" in body, body
    assert path.stat().st_size > maximum


def test_actual_proxy_bounds_journal_enumeration_before_materialization(rig, monkeypatch):
    inv = rig.ctl.inventory
    root = inv.state_root / "checkpoints"
    root.mkdir(exist_ok=True)
    total = 5000
    for index in range(total):
        (root / f"retained-entry-{index:05}").touch()
    original_scandir = os.scandir
    enumerated = []
    class ObserveScan:
        def __init__(self, iterator):
            self.iterator = iterator
        def __enter__(self):
            self.iterator.__enter__()
            return self
        def __exit__(self, *args):
            return self.iterator.__exit__(*args)
        def __iter__(self):
            return self
        def __next__(self):
            entry = next(self.iterator)
            enumerated.append(entry.name)
            return entry
    def observed_scandir(current):
        iterator = original_scandir(current)
        return ObserveScan(iterator) if current in (root, str(root)) else iterator
    monkeypatch.setattr(os, "scandir", observed_scandir)
    status, body, dispatched = checkpoint_reader_http(rig, monkeypatch)
    assert status == 403 and dispatched == [], (status, body, dispatched)
    assert len(enumerated) < total, "reader materialized the entire oversized directory before refusing"
    assert b"bound" in body


def test_bounded_journal_reader_preserves_complete_arbitrary_source_bytes(rig):
    cp = rig.modules.cp
    data = b"\x00original source/evidence\xff" * (rig.modules.state.MAX_JSON_BYTES // 16)
    path = rig.evidence / "large-original-source.bin"
    path.write_bytes(data)
    assert len(data) > rig.modules.state.MAX_JSON_BYTES
    assert cp.regular_bytes(path) == data
    with pytest.raises(RuntimeError, match="bound"):
        cp.journal_checked(path, "large")
    assert path.read_bytes() == data
