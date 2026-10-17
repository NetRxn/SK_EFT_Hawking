"""Defense-in-depth and public-boundary tests for Codex Lean workers."""

from __future__ import annotations

import importlib.util
import json
import shlex
import subprocess
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


@pytest.mark.parametrize("tool_name,input_key", [("Bash", "command"), ("exec_command", "cmd")])
@pytest.mark.parametrize("action", ["preserve", "preserve --bootstrap", "recover", "recover --bootstrap", "observe-release", "observe-release --bootstrap", "resume", "recover-resume"])
def test_worker_shell_policy_denies_checkpoint_lifecycle(action, tool_name, input_key):
    command = f"python3 scripts/slotctl.py checkpoint {action} --request /tmp/explicit-root-request.json"
    result = policy.decision({"tool_name": tool_name, "tool_input": {input_key: command}})
    assert result["hookSpecificOutput"]["permissionDecision"] == "deny"


@pytest.mark.parametrize("tool_name,input_key", [("Bash", "command"), ("exec_command", "cmd")])
@pytest.mark.parametrize("action", ["preserve", "preserve --bootstrap", "recover", "recover --bootstrap", "observe-release", "observe-release --bootstrap", "resume", "recover-resume"])
@pytest.mark.parametrize("script,inventory", [
    ("scripts/slotctl.py", "--inventory /canonical/config/lean-slots.public.json"),
    ("scripts/slotctl.py", "--inventory /canonical/hash#path/config.json"),
    ("scripts/slotctl.py", "--inventory=/canonical/config/lean-slots.public.json"),
    ("scripts/slotctl.py", "--inventory '/canonical path/config/lean slots.json'"),
    ("scripts/slotctl.py", '--inventory="/canonical path/config/lean slots.json"'),
    ('"scripts/slotctl.py"', "'--inventory' '/canonical path/config/lean slots.json'"),
    ("scripts/slotctl.py", r"--inventory /canonical\ path/config/lean\ slots.json"),
    ("scripts/slotctl.py", "--inv=/canonical/config/lean-slots.public.json"),
    ("scripts/slotctl.py", "--inventory /first.json --inventory /canonical/config/lean-slots.public.json"),
])
def test_worker_shell_policy_denies_checkpoint_with_global_inventory(script, inventory, action, tool_name, input_key):
    from scripts.lean_slots.cli import parser
    command = f"python3 {script} {inventory} checkpoint {action} --request /tmp/explicit-root-request.json"
    # Reach the actual CLI parser: these are accepted global option spellings,
    # including quote removal/escapes and argparse's unique abbreviations.
    parsed = parser().parse_args(shlex.split(command)[2:])
    assert parsed.command == "checkpoint" and parsed.action == action.split()[0]
    assert parsed.inventory is not None
    result = policy.decision({"tool_name": tool_name, "tool_input": {input_key: command}})
    assert result is not None, f"worker policy allowed the real checkpoint CLI form: {command}"
    assert result["hookSpecificOutput"]["permissionDecision"] == "deny"


@pytest.mark.parametrize("tool_name,input_key", [("Bash", "command"), ("exec_command", "cmd")])
def test_worker_policy_keeps_inventory_status_and_normal_edits_allowed(tool_name, input_key):
    for command in ("git status --short", "git commit -m proof", "python3 scripts/slotctl.py --inventory '/canonical path/config.json' status --json"):
        assert policy.decision({"tool_name": tool_name, "tool_input": {input_key: command}}) is None


def _shell_argv_only(command: str) -> list[str]:
    # These fixed literals become positional parameters, never an executed
    # python/slotctl command. The only shell command after `set` prints argv.
    completed = subprocess.run(
        ["/bin/sh", "-c", "set -- " + command + "\nprintf '%s\\000' \"$@\""],
        capture_output=True, check=True,
    )
    return completed.stdout.decode().split("\0")[:-1]


_CONTINUATION = "\\\n"
_INVENTORY = "/canonical/config/lean-slots.public.json"
_CONTINUED_CHECKPOINT_PREFIXES = [
    ("script-boundary", f"scripts/slotctl.py {_CONTINUATION}  --inventory {_INVENTORY}", _INVENTORY),
    ("script-name", f"scripts/slotc{_CONTINUATION}tl.py --inventory {_INVENTORY}", _INVENTORY),
    ("quoted-script-name", f'"scripts/slotc{_CONTINUATION}tl.py" --inventory {_INVENTORY}', _INVENTORY),
    ("option-name", f"scripts/slotctl.py --inven{_CONTINUATION}tory {_INVENTORY}", _INVENTORY),
    ("quoted-option-part", f"scripts/slotctl.py '--inven'{_CONTINUATION}tory {_INVENTORY}", _INVENTORY),
    ("option-value", f"scripts/slotctl.py --inventory {_CONTINUATION}  {_INVENTORY}", _INVENTORY),
    ("value-verb", f"scripts/slotctl.py --inventory {_INVENTORY} {_CONTINUATION} ", _INVENTORY),
    ("repeated-options", f"scripts/slotctl.py --inventory /first.json {_CONTINUATION}  --inventory {_INVENTORY}", _INVENTORY),
    ("equals-value", f"scripts/slotctl.py --inventory={_CONTINUATION}{_INVENTORY}", _INVENTORY),
    ("quoted-path", f"scripts/slotctl.py --inventory '/canonical path/config.json' {_CONTINUATION} ", "/canonical path/config.json"),
    ("double-quoted-value", f'scripts/slotctl.py --inventory="/canonical {_CONTINUATION}path/config.json"', "/canonical path/config.json"),
    ("single-quoted-literal", f"scripts/slotctl.py --inventory '/canonical{_CONTINUATION}path/config.json' {_CONTINUATION} ", f"/canonical{_CONTINUATION}path/config.json"),
    ("hash-path", f"scripts/slotctl.py {_CONTINUATION} --inventory=/canonical/hash#path/config.json", "/canonical/hash#path/config.json"),
    ("direct", f"scripts/slotctl.py {_CONTINUATION} ", None),
]


@pytest.mark.parametrize("tool_name,input_key", [("Bash", "command"), ("exec_command", "cmd")])
@pytest.mark.parametrize("action", ["preserve", "preserve --bootstrap", "recover", "recover --bootstrap", "observe-release", "observe-release --bootstrap", "resume", "recover-resume"])
@pytest.mark.parametrize("case,prefix,inventory", _CONTINUED_CHECKPOINT_PREFIXES, ids=[row[0] for row in _CONTINUED_CHECKPOINT_PREFIXES])
def test_worker_policy_denies_shell_continued_checkpoint(case, prefix, inventory, action, tool_name, input_key):
    from scripts.lean_slots.cli import parser
    command = f"python3 {prefix} checkpoint {action} --request /tmp/explicit-root-request.json"
    argv = _shell_argv_only(command)
    assert argv[:2] == ["python3", "scripts/slotctl.py"]
    parsed = parser().parse_args(argv[2:])
    assert parsed.command == "checkpoint" and parsed.action == action.split()[0]
    assert parsed.inventory == (Path(inventory) if inventory is not None else None)
    result = policy.decision({"tool_name": tool_name, "tool_input": {input_key: command}})
    assert result is not None, f"worker policy allowed shell-accepted checkpoint ({case}): {command}"
    assert result["hookSpecificOutput"]["permissionDecision"] == "deny"


@pytest.mark.parametrize("tool_name,input_key", [("Bash", "command"), ("exec_command", "cmd")])
@pytest.mark.parametrize("inventory", ["", f"--inventory={_INVENTORY} "])
def test_worker_policy_denies_shell_continued_checkpoint_verb(inventory, tool_name, input_key):
    from scripts.lean_slots.cli import parser
    command = f"python3 scripts/slotctl.py {inventory}check{_CONTINUATION}point preserve --bootstrap --request /tmp/request.json"
    argv = _shell_argv_only(command)
    parsed = parser().parse_args(argv[2:])
    assert parsed.command == "checkpoint" and parsed.bootstrap
    result = policy.decision({"tool_name": tool_name, "tool_input": {input_key: command}})
    assert result is not None, f"worker policy allowed shell-accepted continued verb: {command}"
    assert result["hookSpecificOutput"]["permissionDecision"] == "deny"


@pytest.mark.parametrize("tool_name,input_key", [("Bash", "command"), ("exec_command", "cmd")])
def test_worker_policy_preserves_single_quoted_continuation_and_readonly(tool_name, input_key):
    from scripts.lean_slots.cli import parser
    literal_script = f"scripts/slot{_CONTINUATION}ctl.py"
    command = f"python3 '{literal_script}' --inventory={_INVENTORY} checkpoint preserve --request /tmp/request.json"
    assert _shell_argv_only(command)[1] == literal_script
    # Literal bytes in a different script name must not become slotctl.py.
    assert policy.decision({"tool_name": tool_name, "tool_input": {input_key: command}}) is None
    command = f"python3 scripts/slotctl.py {_CONTINUATION} --inventory '/canonical path/config.json' {_CONTINUATION} status --json"
    parsed = parser().parse_args(_shell_argv_only(command)[2:])
    assert parsed.command == "status" and parsed.as_json
    assert policy.decision({"tool_name": tool_name, "tool_input": {input_key: command}}) is None
    assert _shell_argv_only(f"git {_CONTINUATION} status --short") == ["git", "status", "--short"]
    assert policy.decision({"tool_name": tool_name, "tool_input": {input_key: f"git {_CONTINUATION} status --short"}}) is None


@pytest.mark.parametrize("tool_name,input_key", [("Bash", "command"), ("exec_command", "cmd")])
def test_worker_policy_keeps_unescaped_newline_command_boundary(tool_name, input_key):
    # This is two shell commands, not a slotctl checkpoint invocation. Do not
    # execute it: the argv-only oracle above is exclusively for one command.
    command = f"python3 scripts/slotctl.py --inventory {_INVENTORY}\ncheckpoint preserve --request /tmp/request.json"
    assert policy.decision({"tool_name": tool_name, "tool_input": {input_key: command}}) is None
