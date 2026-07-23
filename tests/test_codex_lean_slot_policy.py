"""Defense-in-depth and public-boundary tests for Codex Lean workers."""

from __future__ import annotations

import importlib.util
import json
from pathlib import Path

import pytest


ROOT = Path(__file__).resolve().parents[1]
POLICY_PATH = ROOT / ".codex" / "hooks" / "pre_tool_use_policy.py"
spec = importlib.util.spec_from_file_location("pre_tool_use_policy", POLICY_PATH)
assert spec and spec.loader
policy = importlib.util.module_from_spec(spec)
spec.loader.exec_module(policy)


@pytest.mark.parametrize(
    "command",
    [
        "lake build",
        "cd lean && lake clean",
        "lake exe cache get",
        "git merge worker",
        "git rebase main",
        "git cherry-pick deadbeef",
        "rm -rf lean/.lake",
        "cp -R /tmp/cache lean/.lake",
        "python3 scripts/slotctl.py build",
        "python3 scripts/slotctl.py absorb --slot 2",
        "python3 scripts/slotctl.py supervisor stop",
    ],
)
def test_worker_shell_policy_denies_build_cache_and_integration(command: str) -> None:
    result = policy.decision({"tool_name": "Bash", "tool_input": {"command": command}})
    assert result["hookSpecificOutput"]["permissionDecision"] == "deny"


def test_worker_policy_allows_normal_editing_commands() -> None:
    assert (
        policy.decision(
            {"tool_name": "Bash", "tool_input": {"command": "git status --short"}}
        )
        is None
    )
    assert (
        policy.decision(
            {"tool_name": "Bash", "tool_input": {"command": "git commit -m proof"}}
        )
        is None
    )


def test_worker_policy_denies_mcp_lean_build() -> None:
    result = policy.decision(
        {"tool_name": "mcp__skeft_wt2__lean_build", "tool_input": {}}
    )
    assert result["hookSpecificOutput"]["permissionDecision"] == "deny"


def test_public_inventory_has_three_fixed_no_build_no_repl_endpoints() -> None:
    inventory = json.loads((ROOT / "config" / "lean-slots.public.json").read_text())
    assert inventory["max_active_slots"] == 3
    assert inventory["server"]["client_auth"] == "trusted-local"
    assert inventory["server"]["host"] == "127.0.0.1"
    assert set(inventory["slots"]) == {"1", "2", "3"}
    assert inventory["server"]["disabled_tools"] == ["lean_build"]
    assert "--repl" not in inventory["server"]["command"]
    assert len({slot["proxy_port"] for slot in inventory["slots"].values()}) == 3
    assert len({slot["backend_port"] for slot in inventory["slots"].values()}) == 3


def test_public_inventory_is_role_and_path_neutral() -> None:
    inventory = json.loads((ROOT / "config" / "lean-slots.public.json").read_text())
    assert inventory["repo_role"] == "public"
    assert not Path(inventory["repo_root"]).is_absolute()
    for slot in inventory["slots"].values():
        assert not Path(slot["worktree"]).is_absolute()
        assert slot["endpoint_name"].startswith("skeft_wt")


def test_trusted_local_worker_profiles_have_no_token_dependency() -> None:
    for agent in (ROOT / ".codex" / "agents").glob("*.toml"):
        content = agent.read_text()
        assert "bearer_token_env_var" not in content
        assert "?client=codex" in content
