"""Command-line contract for the ADR-008 Lean slot controller."""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path
from typing import Any

from .controller import Controller
from .proxy import serve
from .state import Inventory, SlotError
from .supervisor import Supervisor


def _json(value: Any) -> None:
    print(json.dumps(value, indent=2, sort_keys=True))


def _status_human(value: dict[str, Any]) -> None:
    for item in value["slots"]:
        lease = item.get("lease")
        state = "FREE" if lease is None else lease.get("state", "INVALID")
        if lease is None:
            owner = ""
        elif lease.get("owner_kind") == "session":
            owner = f" {lease.get('client')} session={str(lease.get('owner_session_hash'))[:12]}"
        else:
            owner = f" {lease.get('client')} pid={lease.get('owner_pid')}"
        dirty = item.get("dirty") or []
        suffix = f" dirty={len(dirty)}" if dirty else ""
        error = f" error={item['error']}" if item.get("error") else ""
        resources = f" proxy={item.get('proxy_state', 'unavailable')} backend={item.get('backend_state', 'unavailable')} reserved={item.get('resource_reserved', False)}"
        print(f"wt{item['slot']}: {state}{owner}{resources}{suffix}{error}")
        for kind, resource in item.get("resources", {}).items():
            print(f"  {kind}: phase={resource['record_phase']} identity={resource['identity_authority']} process={resource['process_observation']} endpoint={resource['endpoint_observation']}")
            for witness in resource.get("observations", []):
                if witness["state"] in {"unavailable", "mismatch"}:
                    print(f"  {kind}: observation={json.dumps(witness, sort_keys=True)}")
            for error in resource["errors"]:
                print(f"  {kind}: {error}")
    print(f"capacity_complete={value.get('capacity_complete', False)} reserved={value.get('reserved_physical_slots', [])} conflicts={value.get('capacity_conflicts', [])}")
    for error in value.get("capacity_errors", []):
        print(f"capacity: {error}")


def _doctor_human(value: dict[str, Any]) -> None:
    for check in value["checks"]:
        marker = "OK" if check["ok"] else "FAIL"
        print(f"[{marker}] {check['name']}: {check['detail']}")
    print("doctor: " + ("healthy" if value["ok"] else "attention required"))


def parser() -> argparse.ArgumentParser:
    result = argparse.ArgumentParser(
        prog="slotctl",
        description="ADR-008 shared three-slot Lean controller",
    )
    result.add_argument("--inventory", type=Path, help="versioned slot inventory JSON")
    commands = result.add_subparsers(dest="command", required=True)

    doctor = commands.add_parser(
        "doctor", help="audit worktrees, leases, epochs, config, and endpoints"
    )
    doctor.add_argument("--json", action="store_true", dest="as_json")

    status = commands.add_parser("status", help="show global slot state")
    status.add_argument("--json", action="store_true", dest="as_json")

    acquire = commands.add_parser("acquire", help="atomically lease a clean slot")
    acquire.add_argument("--slot", type=int, required=True)
    acquire.add_argument("--repo-role")
    acquire.add_argument("--client", choices=("codex", "claude"), required=True)
    acquire.add_argument("--base-ref", required=True)

    for name, help_text in (
        ("prepare", "reset and rewarm an acquired slot"),
        ("ready", "mark a clean committed slot ready for absorption"),
        ("heartbeat", "refresh an active lease heartbeat"),
        ("absorb", "rebase, fast-forward, build, rewarm, and release"),
        ("release", "release a clean no-change slot"),
        ("reclaim", "audit and reclaim a slot whose owner is gone"),
    ):
        command = commands.add_parser(name, help=help_text)
        command.add_argument("--slot", type=int, required=True)
        if name == "prepare":
            command.add_argument("--checkpoint-request", type=Path)
        if name == "reclaim":
            command.add_argument("--confirm-owner-gone", action="store_true")

    checkpoint = commands.add_parser("checkpoint", help="preserve unfinished source without accepting it")
    checkpoint.add_argument("action", choices=("preserve", "recover", "observe-release", "resume", "recover-resume"))
    checkpoint.add_argument("--request", type=Path, required=True)
    checkpoint.add_argument("--bootstrap", action="store_true", help="explicit reviewed candidate stop-only route")

    commands.add_parser(
        "build", help="run the serialized authoritative build and publish an epoch"
    )

    config = commands.add_parser(
        "config", help="render or inspect generated client configuration"
    )
    config_commands = config.add_subparsers(dest="config_command", required=True)
    render = config_commands.add_parser(
        "render", help="render gitignored client configuration"
    )
    render.add_argument("--client", choices=("codex", "claude"), default="codex")
    render.add_argument(
        "--scope", choices=("repo", "workspace", "both"), default="repo"
    )
    render.add_argument("--force", action="store_true")
    render.add_argument("--rotate-token", action="store_true")
    render.add_argument(
        "--rollback",
        action="store_true",
        help="claude only: restore the pre-activation mcpServers snapshot",
    )

    session = commands.add_parser(
        "session", help="emit optional client-auth and shared-state environment"
    )
    session_commands = session.add_subparsers(dest="session_command", required=True)
    environment = session_commands.add_parser(
        "env", help="print shell exports required by the selected client-auth mode"
    )
    environment.add_argument("--client", choices=("codex", "claude"), required=True)
    environment.add_argument("--rotate-token", action="store_true")

    supervisor = commands.add_parser(
        "supervisor", help="manage the three fixed-root endpoints"
    )
    supervisor.add_argument("action", choices=("start", "stop", "status", "probe"))
    supervisor.add_argument("--slot", type=int)
    supervisor.add_argument("--json", action="store_true", dest="as_json")

    internal = commands.add_parser("_proxy", help=argparse.SUPPRESS)
    internal.add_argument("--slot", type=int, required=True)
    return result


def main(argv: list[str] | None = None) -> int:
    args = parser().parse_args(argv)
    try:
        if args.command == "supervisor":
            if args.action != "probe" and args.slot is not None:
                raise SlotError("supervisor start/stop/status are global; --slot is only valid for probe")
            if args.action == "probe" and args.slot is None:
                raise SlotError("supervisor probe requires --slot")
        checkpoint_request = None
        if args.command == "checkpoint":
            from .state import read_json
            checkpoint_request = read_json(args.request)
            if args.bootstrap:
                if args.action not in {"preserve", "recover", "observe-release"}:
                    raise SlotError("candidate checkpoint bootstrap is stop-only")
                from .checkpoints import validate_bootstrap
                inventory = validate_bootstrap(args.inventory, checkpoint_request, recover=args.action == "recover",
                                               observe_release=args.action == "observe-release")
            else:
                inventory = Inventory.load(args.inventory)
        else:
            inventory = Inventory.load(args.inventory)
        controller = Controller(inventory)
        if args.command == "_proxy":
            serve(inventory, args.slot)
            return 0
        if args.command == "status":
            value = controller.status()
            _json(value) if args.as_json else _status_human(value)
        elif args.command == "doctor":
            value = controller.doctor()
            _json(value) if args.as_json else _doctor_human(value)
            return 0 if value["ok"] else 1
        elif args.command == "acquire":
            if args.repo_role and args.repo_role != inventory.repo_role:
                raise SlotError(
                    f"inventory role is {inventory.repo_role!r}, not {args.repo_role!r}"
                )
            _json(
                controller.acquire(
                    args.slot,
                    client=args.client,
                    base_ref=args.base_ref,
                )
            )
        elif args.command == "prepare":
            from .state import read_json
            request = read_json(args.checkpoint_request) if args.checkpoint_request else None
            _json(controller.prepare(args.slot, checkpoint_request=request))
        elif args.command == "checkpoint":
            if args.action in {"preserve", "recover"}:
                _json(controller.checkpoint(checkpoint_request, recover=args.action == "recover", bootstrap=args.bootstrap))
            elif args.action == "observe-release":
                _json(controller.checkpoint_observe_release(checkpoint_request, bootstrap=args.bootstrap))
            else:
                _json(controller.checkpoint_resume(checkpoint_request, recover=args.action == "recover-resume"))
        elif args.command == "ready":
            _json(controller.ready(args.slot))
        elif args.command == "heartbeat":
            _json(controller.heartbeat(args.slot))
        elif args.command == "absorb":
            _json(controller.absorb(args.slot))
        elif args.command == "release":
            controller.release(args.slot)
            print(f"wt{args.slot}: FREE")
        elif args.command == "reclaim":
            controller.reclaim(args.slot, confirm_owner_gone=args.confirm_owner_gone)
            print(f"wt{args.slot}: FREE")
        elif args.command == "build":
            _json(controller.build())
        elif args.command == "config":
            if args.client == "claude":
                if args.rotate_token:
                    raise SlotError(
                        "trusted-local Claude endpoints carry no token to rotate"
                    )
                paths = controller.render_claude_config(rollback=args.rollback)
            else:
                if args.rollback:
                    raise SlotError("--rollback applies to --client claude only")
                paths = controller.render_config(
                    scope=args.scope,
                    force=args.force,
                    rotate_token=args.rotate_token,
                )
            for path in paths:
                print(path)
        elif args.command == "session":
            print(
                controller.session_environment(
                    client=args.client,
                    rotate_token=args.rotate_token,
                )
            )
        elif args.command == "supervisor":
            supervisor = Supervisor(inventory)
            if args.action == "probe":
                if args.slot is None:
                    raise SlotError("supervisor probe requires --slot")
                value = supervisor.probe(args.slot)
                _json(value)
                return 0
            value = getattr(supervisor, args.action)()
            if args.as_json:
                _json(value)
            else:
                for item in value["slots"]:
                    print(
                        f"wt{item['slot']}: lease={item['lease_state']} proxy={item['proxy_state']} "
                        f"backend={item['backend_state']} reserved={item['slot'] in value['reserved_physical_slots']}"
                    )
                    for kind, resource in item.get("resources", {}).items():
                        print(f"  {kind}: phase={resource['record_phase']} identity={resource['identity_authority']} process={resource['process_observation']} endpoint={resource['endpoint_observation']}")
                        for error in resource["errors"]:
                            print(f"  {kind}: {error}")
                print(f"capacity_complete={value['capacity_complete']} reserved={value['reserved_physical_slots']} conflicts={value['capacity_conflicts']}")
                for error in value["capacity_errors"]:
                    print(f"capacity: {error}")
        else:  # pragma: no cover - argparse enforces command selection
            raise SlotError(f"unsupported command: {args.command}")
        return 0
    except (SlotError, OSError, ValueError) as exc:
        print(f"slotctl: {exc}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
