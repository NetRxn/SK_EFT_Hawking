"""Artifact-seeded ADR-018 roster parsing; no Git, slot, server or Lean calls."""

from __future__ import annotations

import json
from pathlib import Path

import pytest

from scripts.lean_slots.state import Inventory, SlotError


@pytest.fixture(params=["trusted-local", "bearer"])
def roster_inventory(tmp_path: Path, monkeypatch: pytest.MonkeyPatch, request):
    """Use the production loader on a disposable inventory, not a helper replica."""
    state_root = tmp_path / "runtime-state"
    monkeypatch.setenv("LEAN_SLOT_STATE_DIR", str(state_root))
    config_dir = tmp_path / "config"
    config_dir.mkdir()
    source = config_dir / "lean-slots.public.json"
    raw = {
        "schema_version": 1,
        "repo_role": "public",
        "repo_root": "..",
        "max_active_slots": 3,
        "slots": {
            str(number): {"worktree": f"wt{number}"} for number in (1, 2, 3)
        },
        "server": {
            "host": "127.0.0.1",
            "client_auth": request.param,
            "allowed_clients": ["codex", "claude", "chat"],
        },
    }
    source.write_text(json.dumps(raw), encoding="utf-8")
    return source, state_root


@pytest.mark.parametrize(
    "value",
    [None, False, True, 0, 1, "", "codex", {}, []],
    ids=["null", "false", "true", "zero", "one", "empty-string", "string", "object", "empty-array"],
)
def test_present_invalid_roster_never_uses_legacy_fallback(roster_inventory, value):
    source, state_root = roster_inventory
    raw = json.loads(source.read_text(encoding="utf-8"))
    raw["server"]["allowed_clients"] = value
    source.write_text(json.dumps(raw), encoding="utf-8")
    before = source.read_bytes()

    with pytest.raises(SlotError, match="non-empty JSON array"):
        Inventory.load(source)

    assert source.read_bytes() == before
    assert not state_root.exists(), "roster parsing must not create runtime state"


def test_absent_roster_still_uses_exact_legacy_pair(roster_inventory):
    source, state_root = roster_inventory
    raw = json.loads(source.read_text(encoding="utf-8"))
    del raw["server"]["allowed_clients"]
    source.write_text(json.dumps(raw), encoding="utf-8")

    inventory = Inventory.load(source)
    assert inventory.allowed_clients == frozenset({"codex", "claude"})
    assert isinstance(inventory.allowed_clients, frozenset)
    with pytest.raises(SlotError, match="not admitted"):
        inventory.require_allowed_client("chat")
    assert not state_root.exists()


def test_explicit_narrow_roster_does_not_restore_legacy_clients(roster_inventory):
    source, state_root = roster_inventory
    raw = json.loads(source.read_text(encoding="utf-8"))
    raw["server"]["allowed_clients"] = ["chat"]
    source.write_text(json.dumps(raw), encoding="utf-8")

    inventory = Inventory.load(source)
    assert inventory.allowed_clients == frozenset({"chat"})
    assert inventory.require_allowed_client("chat") == "chat"
    for client in ("codex", "claude"):
        with pytest.raises(SlotError, match="not admitted"):
            inventory.require_allowed_client(client)
    assert not state_root.exists()


def test_valid_explicit_public_roster_remains_immutable(roster_inventory):
    source, state_root = roster_inventory
    inventory = Inventory.load(source)
    assert inventory.allowed_clients == frozenset({"codex", "claude", "chat"})
    assert isinstance(inventory.allowed_clients, frozenset)
    for client in ("codex", "claude", "chat"):
        assert inventory.require_allowed_client(client) == client
    assert not state_root.exists()
