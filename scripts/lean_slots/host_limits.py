"""Declared host kernel limits for the slot control plane.

A concurrent slot swarm is bounded by kernel resources, not just by the heavy-backend
semaphore: every Lean server memory-maps thousands of `.olean` files across Mathlib and its
dependencies, and several slots do so at once. The knob that governs this is platform-specific
and, where it is a runtime `sysctl -w`, does not survive a reboot — so it silently reverts to a
default that was adequate for one slot and is not for three.

PORTABILITY IS THE DESIGN CONSTRAINT. This is a public repository, so a limit that is right for
one workstation must not fail a clone on another:

- Entries are keyed by `platform.system()`. A platform with no declared entry PASSES — Linux has
  no vnode ceiling at all, so a Linux VM must not inherit a macOS requirement.
- A knob the running kernel does not expose PASSES. "Absent" is not "misconfigured".
- `LEAN_SLOT_SKIP_HOST_LIMITS=1` disables the check entirely, so another operator or a CI runner
  needs no repository diff to opt out.
- The remedy string is carried in the inventory, not built here, so the message an operator is
  told to run is exactly the value that was checked.
"""

from __future__ import annotations

import os
import platform
import shutil
import subprocess
from typing import Any

from .state import Inventory

#: Set to any non-empty value to skip host-limit reporting (other machines, CI, containers).
SKIP_ENV = "LEAN_SLOT_SKIP_HOST_LIMITS"


def read_sysctl(name: str) -> int | None:
    """Current integer value of a sysctl knob, or None if unreadable on this kernel."""
    if not shutil.which("sysctl"):
        return None
    try:
        result = subprocess.run(
            ["sysctl", "-n", name], capture_output=True, text=True, timeout=10
        )
    except (OSError, subprocess.SubprocessError):
        return None
    if result.returncode != 0:
        return None
    try:
        return int(result.stdout.strip().split()[0])
    except (ValueError, IndexError):
        return None


def declared_limits(inventory: Inventory) -> list[dict[str, Any]]:
    """Inventory-declared limits that apply to the platform we are running on."""
    raw = inventory.raw.get("host_limits") or []
    if not isinstance(raw, list):
        return []
    system = platform.system()
    return [
        entry
        for entry in raw
        if isinstance(entry, dict) and entry.get("platform") == system
    ]


def evaluate(inventory: Inventory) -> list[tuple[str, bool, str]]:
    """(check_name, ok, detail) per applicable limit; empty when none applies.

    `ok` is False ONLY for a knob this kernel exposes whose value is below the declared
    minimum — the one case where an operator can act and the swarm is genuinely at risk.
    """
    if os.environ.get(SKIP_ENV):
        return [("host_limits", True, f"skipped by {SKIP_ENV}")]
    entries = declared_limits(inventory)
    if not entries:
        return [
            (
                "host_limits",
                True,
                f"no host limit declared for {platform.system()}",
            )
        ]
    results: list[tuple[str, bool, str]] = []
    for entry in entries:
        knob = str(entry.get("sysctl", "")).strip()
        if not knob:
            continue
        name = f"host_limit.{knob}"
        try:
            minimum = int(entry.get("minimum"))
        except (TypeError, ValueError):
            results.append((name, True, f"{knob}: no usable minimum declared"))
            continue
        current = read_sysctl(knob)
        if current is None:
            results.append((name, True, f"{knob} is not exposed by this kernel"))
            continue
        if current >= minimum:
            results.append((name, True, f"{knob} = {current} (needs ≥ {minimum})"))
            continue
        # The remedy must SATISFY the minimum it is offered for. A hand-written remedy
        # that no longer names the declared minimum has drifted, and printing it would
        # send the operator to run a command that leaves the check red.
        derived = f"sudo sysctl -w {knob}={minimum}"
        declared_remedy = str(entry.get("remedy") or "").strip()
        remedy = declared_remedy if str(minimum) in declared_remedy else derived
        why = str(entry.get("why") or "").strip()
        detail = (
            f"{knob} = {current}, below the {minimum} a full slot swarm needs. "
            f"Run:  {remedy}"
        )
        if why:
            detail += f"  — {why}"
        detail += (
            "  This is a RUNTIME setting and is lost on reboot; see the slot operator "
            "guide for the LaunchDaemon that reapplies it at boot."
        )
        results.append((name, False, detail))
    return results
