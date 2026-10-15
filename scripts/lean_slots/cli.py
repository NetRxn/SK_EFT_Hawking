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


# These are presentation budgets, never lifecycle admission predicates.
_DIAGNOSTIC_BYTES = 65536
_DIAGNOSTIC_GROUPS = 8
_DIAGNOSTIC_EDGES = 16
_DIAGNOSTIC_OBSERVATIONS = 32


def _diagnostic_text(value: object, limit: int) -> tuple[str, bool]:
    try:
        text = str(value)
        bounded = text[:limit]
        bounded.encode("utf-8", errors="strict")
        return bounded, len(text) > limit
    except Exception:
        return "<presentation unavailable>", True


def _strict_diagnostic_json(value: Any, limit: int) -> str:
    """Refuse whole payloads before large encoding; never coerce identity values.

    The structural limits bound our traversal, not arbitrary user-defined object
    behavior. Only plain JSON containers/scalars are admitted, without hooks.
    """
    visits = 0
    active: set[int] = set()

    def check(item: Any, depth: int) -> None:
        nonlocal visits
        visits += 1
        if visits > 65536 or depth > 64:
            raise ValueError("diagnostic structure limit")
        kind = type(item)
        if kind is str:
            if len(item) > limit:
                raise OverflowError("diagnostic string limit")
        elif kind is int:
            if item.bit_length() > limit * 3:
                raise OverflowError("diagnostic integer limit")
        elif kind in (float, bool, type(None)):
            return
        elif kind in (list, tuple, dict):
            if id(item) in active:
                raise ValueError("cyclic diagnostic value")
            if len(item) > 65536:
                raise ValueError("diagnostic structure limit")
            active.add(id(item))
            try:
                if kind is dict:
                    for key, child in item.items():
                        if type(key) is not str:
                            raise ValueError("diagnostic keys must be strings")
                        check(key, depth + 1)
                        check(child, depth + 1)
                else:
                    for child in item:
                        check(child, depth + 1)
            finally:
                active.remove(id(item))
        else:
            raise ValueError("non-JSON diagnostic value")

    check(value, 0)
    parts = []
    size = 0
    encoder = json.JSONEncoder(ensure_ascii=False, allow_nan=False, separators=(",", ":"))
    for part in encoder.iterencode(value):
        size += len(part.encode("utf-8", errors="strict"))
        if size > limit:
            raise OverflowError("diagnostic byte limit")
        parts.append(part)
    return "".join(parts)


def _exception_diagnostics(exc: BaseException) -> str | None:
    """Present bounded explicit provenance without observing external state."""
    groups: list[dict[str, Any]] = []
    edges: list[dict[str, Any]] = []
    objects: dict[int, int] = {}
    stack: set[int] = set()
    pending: list[tuple[dict[str, Any], tuple]] = []
    omitted = {"relationships": 0, "group_targets": 0, "observation_budget": 0,
               "serialization": 0, "bytes": 0}
    exhausted: list[str] = []
    inspected_edges = 0
    discovered = 0

    def budget(name: str) -> None:
        if name not in exhausted:
            exhausted.append(name)

    def visit(error: BaseException) -> int:
        nonlocal inspected_edges, discovered
        number = len(groups)
        objects[id(error)] = number
        stack.add(id(error))
        name, name_cut = _diagnostic_text(type(error).__name__, 128)
        message, message_cut = _diagnostic_text(error, 1024)
        observations = error.observations if isinstance(error, SlotError) else ()
        group = {"id": number, "class": name, "class_truncated": name_cut,
                 "message": message, "message_truncated": message_cut,
                 "observations_total": len(observations), "observations": []}
        groups.append(group)
        pending.append((group, observations))
        discovered += len(observations)
        cause = error.__cause__
        secondary = error.secondary_errors if isinstance(error, SlotError) else ()
        relation_count = (cause is not None) + len(secondary)
        for index in range(relation_count):
            if inspected_edges >= _DIAGNOSTIC_EDGES:
                omitted["relationships"] += relation_count - index
                budget("relationships")
                break
            inspected_edges += 1
            if cause is not None and index == 0:
                relation, role, child = "cause", "cause", cause
            else:
                role, child = secondary[index - (cause is not None)]
                relation = "secondary"
            role_text, role_cut = _diagnostic_text(role, 128)
            target = objects.get(id(child))
            if target is not None:
                disposition = "cycle" if id(child) in stack else "shared"
            elif len(groups) >= _DIAGNOSTIC_GROUPS:
                disposition = "group_budget"
                omitted["group_targets"] += 1
                budget("groups")
            else:
                disposition = "new"
            edge = {"from": number, "to": target, "relation": relation,
                    "role": role_text, "role_truncated": role_cut,
                    "disposition": disposition}
            edges.append(edge)
            if disposition == "new":
                edge["to"] = visit(child)
        stack.remove(id(error))
        return number

    visit(exc)
    if not discovered:
        return None
    unknown = bool(omitted["relationships"] or omitted["group_targets"])
    envelope = {"schema": "slotctl-diagnostics/v1", "groups": groups, "edges": edges,
                "limits": {"groups": _DIAGNOSTIC_GROUPS, "relationships": _DIAGNOSTIC_EDGES,
                           "observations": _DIAGNOSTIC_OBSERVATIONS, "utf8_bytes": _DIAGNOSTIC_BYTES},
                "inspection": {"relationships": inspected_edges, "observations": 0,
                               "discovered_observations": discovered},
                "omitted": omitted, "budget_exhausted": exhausted,
                "unvisited_content_unknown": unknown, "traversal_complete": not unknown,
                "observations_complete": False, "fallback": False}
    try:
        # No observation is admitted until graph/omission metadata is reserved.
        reserved = len(_strict_diagnostic_json(envelope, _DIAGNOSTIC_BYTES).encode("utf-8")) + 4096
        available = max(0, _DIAGNOSTIC_BYTES - reserved)
        attempts = 0
        for group, observations in pending:
            for index in range(len(observations)):
                if attempts >= _DIAGNOSTIC_OBSERVATIONS:
                    omitted["observation_budget"] += len(observations) - index
                    budget("observations")
                    break
                attempts += 1
                try:
                    item = {"index": index, "value": observations[index].as_dict()}
                    encoded = _strict_diagnostic_json(item, _DIAGNOSTIC_BYTES)
                except OverflowError:
                    omitted["bytes"] += 1
                    budget("utf8_bytes")
                    continue
                except Exception:
                    omitted["serialization"] += 1
                    continue
                size = len(encoded.encode("utf-8")) + 1
                if size > available:
                    omitted["bytes"] += 1
                    budget("utf8_bytes")
                    continue
                group["observations"].append(item)
                available -= size
        envelope["inspection"]["observations"] = attempts
        while True:
            envelope["observations_complete"] = not unknown and not any(
                omitted[key] for key in ("observation_budget", "serialization", "bytes"))
            try:
                return _strict_diagnostic_json(envelope, _DIAGNOSTIC_BYTES)
            except OverflowError:
                for group in reversed(groups):
                    if group["observations"]:
                        group["observations"].pop()
                        omitted["bytes"] += 1
                        budget("utf8_bytes")
                        break
                else:
                    raise
    except Exception:
        # Discovered evidence exists; failure here must never look complete.
        return json.dumps({"schema": "slotctl-diagnostics/v1", "fallback": True,
                           "discovered_evidence_omitted": True,
                           "unvisited_content_unknown": True,
                           "traversal_complete": False, "observations_complete": False},
                          separators=(",", ":"), allow_nan=False)


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
        if name == "reclaim":
            command.add_argument("--confirm-owner-gone", action="store_true")

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
            _json(controller.prepare(args.slot))
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
        try:
            diagnostics = _exception_diagnostics(exc)
            if diagnostics is not None:
                print("slotctl diagnostics: " + diagnostics, file=sys.stderr)
        except Exception:
            pass  # Added presentation must not replace the original refusal.
        return 2


if __name__ == "__main__":
    raise SystemExit(main())
