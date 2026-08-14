"""Claude MCP configuration for the ADR-008 slot endpoints (spec P4-1..P4-3).

The workspace ``.mcp.json`` is shared: it also defines the primary Lean server, a downstream
project's server, and other clients. This module therefore owns a **named key block** inside
``mcpServers`` and never the file — it adds the slot endpoints, drops the legacy per-slot stdio
servers, and leaves every other entry unchanged in its original order.

Ports come from the versioned inventory, so a port cannot drift between the controller and the
rendered client configuration.
"""

from __future__ import annotations

import json
from pathlib import Path
from typing import Any

from .state import Inventory, SlotError, atomic_write

#: Per-slot stdio servers this block replaces. Their definitions survive in the rollback snapshot.
LEGACY_KEYS: tuple[str, ...] = ("lean-lsp-wt1", "lean-lsp-wt2", "lean-lsp-wt3")

#: Filename of the one-time pre-activation snapshot, under the runtime state root.
ROLLBACK_NAME = "claude-mcp.rollback.json"


def managed_servers(inventory: Inventory) -> dict[str, dict[str, str]]:
    """The `skeft_wtN` HTTP entries, keyed and ported from the versioned inventory.

    The ``?client=claude`` query parameter is not cosmetic: in trusted-local mode the proxy
    rejects a request without it, and dispatch additionally requires the active lease's own
    ``client`` field to equal it (`proxy.py`).
    """
    host = str(inventory.raw["server"]["host"])
    servers: dict[str, dict[str, str]] = {}
    for number in (1, 2, 3):
        slot = inventory.slot(number)
        port = int(slot["proxy_port"])
        servers[str(slot["endpoint_name"])] = {
            "type": "http",
            "url": f"http://{host}:{port}/mcp?client=claude",
        }
    return servers


def _servers_of(document: Any) -> dict[str, Any]:
    if not isinstance(document, dict):
        raise SlotError("Claude MCP configuration must be a JSON object")
    servers = document.get("mcpServers", {})
    if not isinstance(servers, dict):
        raise SlotError("`mcpServers` must be a JSON object")
    return servers


def apply_block(document: dict[str, Any], inventory: Inventory) -> dict[str, Any]:
    """Return `document` with the managed block applied, other entries and order intact.

    The managed keys land where the first legacy key sat, so an activated file reads in the same
    place as the one it replaced rather than accumulating entries at the end.
    """
    servers = _servers_of(document)
    managed = managed_servers(inventory)
    anchor = next(
        (key for key in servers if key in LEGACY_KEYS or key in managed), None
    )
    rebuilt: dict[str, Any] = {}
    for key, value in servers.items():
        if key == anchor:
            rebuilt.update(managed)
        if key in LEGACY_KEYS or key in managed:
            continue
        rebuilt[key] = value
    if anchor is None:
        rebuilt.update(managed)
    result = dict(document)
    result["mcpServers"] = rebuilt
    return result


def block_state(document: dict[str, Any], inventory: Inventory) -> tuple[str, str]:
    """Classify the live managed block: current / not activated / partial / drifted."""
    servers = _servers_of(document)
    managed = managed_servers(inventory)
    present = [key for key in managed if key in servers]
    legacy = [key for key in LEGACY_KEYS if key in servers]
    if not present:
        if legacy:
            return "not activated", f"legacy stdio slots still configured: {', '.join(legacy)}"
        return "not activated", "no slot servers configured"
    if len(present) != len(managed):
        missing = sorted(set(managed) - set(present))
        return "partial", f"missing {', '.join(missing)}"
    mismatched = sorted(key for key in managed if servers[key] != managed[key])
    if mismatched:
        return "drifted", f"{', '.join(mismatched)} differ from the rendered endpoints"
    if legacy:
        return "drifted", f"legacy stdio slots still present alongside: {', '.join(legacy)}"
    return "current", f"{len(managed)} slot endpoints, client=claude"


def rollback_path(inventory: Inventory) -> Path:
    return inventory.state_root / "generated" / ROLLBACK_NAME


def render(
    inventory: Inventory, target: Path, *, rollback: bool = False
) -> Path:
    """Apply (or undo) the managed block on `target`, snapshotting the pre-activation state once."""
    if not target.exists():
        raise SlotError(f"Claude MCP configuration not found: {target}")
    document = json.loads(target.read_text(encoding="utf-8"))
    snapshot = rollback_path(inventory)
    if rollback:
        if not snapshot.exists():
            raise SlotError(f"no pre-activation snapshot to restore: {snapshot}")
        document["mcpServers"] = json.loads(snapshot.read_text(encoding="utf-8"))
    else:
        # Written once. A second render must not overwrite the original legacy definitions
        # with an already-activated block, which would make the snapshot useless.
        if not snapshot.exists():
            atomic_write(
                snapshot, json.dumps(_servers_of(document), indent=2, sort_keys=False) + "\n"
            )
        document = apply_block(document, inventory)
    # Keep the operator's own permissions; `atomic_write` would otherwise narrow them to 0600.
    atomic_write(
        target,
        json.dumps(document, indent=2, sort_keys=False) + "\n",
        mode=target.stat().st_mode & 0o777,
    )
    return target
