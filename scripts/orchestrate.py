"""Plan a remediation wave — what can be dispatched right now, and what must not be.

    uv run python scripts/orchestrate.py                  # the plan, all lanes
    uv run python scripts/orchestrate.py --lane lean      # one lane
    uv run python scripts/orchestrate.py --slots 3        # cap the fan-out
    uv run python scripts/orchestrate.py --json           # machine-readable

ADR-012 P10 (D2 · D10 · D11 · D16). **This is a PLANNER AND A GUARD, not a process
supervisor.** It answers *which findings may be worked in parallel right now, by which agent
profile, in which worktree slot, and what would close each one* — and it refuses the rest with
a reason. Spawning the workers is the lead's job; a planner that also supervised would put the
decision and the execution in one place where neither could be tested alone.

⚠️ **IT REFUSES BEFORE IT FANS OUT, AND THE REFUSAL IS THE POINT.** Measured at HEAD
2026-08-13: of 965 dispatchable open findings, **74 declare a `verify` command**.
`close_finding._run_verifications` skips a finding that declares none (`if not cmd: continue`),
so the other 891 can be recorded `fixed` with an empty `verified_by` — a closure nothing
proved. D6 grandfathered that for records written *before* the writer existed; it was never a
licence for new ones. A loop that dispatches and closes at machine speed turns a slow leak into
a firehose, so an unverifiable finding is **PLANNED BUT NOT CLOSABLE** here, and says so.

⚠️ **`unclassified` IS NOT A LANE, AND IS NOT COERCED INTO ONE.** 657 of 969 open findings
carry no declared lane. Routing them to a default would hand physics work to an infra worker
and read, downstream, exactly like routing that succeeded. They are reported as an unrouted
population with the tool that fixes them (`backfill_lanes.py --propose`) named on the face of
the output. An unrouted finding is work the queue cannot yet dispatch, which is different from
work it has dispatched badly.

⚠️ **Fan-out is keyed on the TARGET, not the finding.** Two findings against the same file are
not independent: the second worker would rebase onto the first's edit or clobber it. The unit
of parallelism is therefore a target-group — every open finding naming one target, handed to
one worker as a block (`feedback-maximize-per-turn-throughput`), and only distinct targets go
to distinct slots.
"""
from __future__ import annotations

import argparse
import json
import re
import sys
from collections import defaultdict
from pathlib import Path

SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_ROOT = SCRIPT_DIR.parent
sys.path.insert(0, str(SCRIPT_DIR))

#: Agent profile + gate set per lane — ADR-012 D2's table, as data.
#: ⚠️ Keyed on the SAME strings `reviews.py` validates, so a lane that passes the check and a
#: lane this router understands cannot diverge; `test_orchestrate.py` asserts the two sets are
#: equal rather than trusting this comment.
LANE_PROFILE: dict[str, dict] = {
    "lean": {
        "agent": "skeft-qa:lean-worker",
        "isolation": "worktree-slot",
        "gates": ["lake build clean", "zero sorry", "kernel-purity", "axiom allowlist"],
    },
    "substrate": {
        "agent": "skeft-qa:lean-worker",
        "isolation": "worktree-slot",
        "gates": ["both lean and pyrust gate sets", "a test that fails before the fix"],
    },
    "pyrust": {
        "agent": "general-purpose",
        "isolation": "worktree",
        "gates": ["pytest", "verify_scope", "dependency declaration"],
    },
    "prose": {
        "agent": "skeft-qa:paper-drafter",
        "isolation": "none",
        "gates": ["Stage 9/10 sub-gates"],
    },
    "research": {
        "agent": "skeft-qa:research-scout",
        "isolation": "none",
        "gates": ["cited report vetted by the lead before filing"],
    },
    "infra": {
        "agent": "general-purpose",
        "isolation": "none",
        "gates": ["validate.py", "plugin surface tests", "the D2 dashboard exception"],
    },
}

#: Worktree slots that carry their own `.lake`, so Lean lanes build in parallel.
#: Derived from the live tree, never hardcoded: a slot that was removed must not be planned
#: into, and a slot that was added should be usable without editing this file.
def lean_slots() -> list[str]:
    """The `wtN` slots that actually exist on disk, sorted."""
    base = PROJECT_ROOT / ".claude" / "worktrees"
    if not base.is_dir():
        return []
    return sorted(p.name for p in base.iterdir()
                  if p.is_dir() and p.name.startswith("wt") and p.name[2:].isdigit())


def _load_open_findings() -> tuple[list[dict], set[str], set[str]]:
    """`(open findings, all minted ids, closed ids)` from the one extractor."""
    from build_graph import extract_review_finding_nodes
    nodes = extract_review_finding_nodes()
    ids = {n["id"] for n in nodes}
    closed = {n["id"] for n in nodes
              if (n.get("meta") or {}).get("status") in ("fixed", "accepted")}
    open_ = [n for n in nodes if (n.get("meta") or {}).get("status") == "open"]
    return open_, ids, closed


def classify(nodes: list[dict], ids: set[str], closed: set[str]) -> dict:
    """Partition the open population into dispatchable · blocked · unrouted.

    ⚠️ **The three buckets must PARTITION**, and `plan()` asserts it. A finding that fell out
    of all three would be work the queue silently forgot, which is this repository's signature
    defect wearing a scheduler's clothes.
    """
    from build_graph import finding_is_dispatchable
    dispatchable, blocked, unrouted = [], [], []
    for n in nodes:
        meta = n.get("meta") or {}
        if not finding_is_dispatchable(n, ids, closed):
            blocked.append(n)
        elif (meta.get("lane") or "unclassified") not in LANE_PROFILE:
            unrouted.append(n)
        else:
            dispatchable.append(n)
    return {"dispatchable": dispatchable, "blocked": blocked, "unrouted": unrouted}


def closable(node: dict) -> bool:
    """Can a worker actually CLOSE this, or only edit it?

    ⚠️ The decider is the finding's own `Verify:` line, because that is what
    `close_finding.py` runs. A finding without one closes through a branch that skips
    verification entirely, so planning it as closable would be planning a ledger record that
    proves nothing.
    """
    return bool(((node.get("meta") or {}).get("verify") or "").strip())


#: Gate-set strength, strongest first. A target whose findings span lanes is worked under the
#: strongest of them, because a profile's gates are a floor: a Lean edit under a prose profile
#: has no build gate at all, while prose edited under a Lean profile merely runs a build it
#: did not need.
#: ⚠️ EXPLICIT, because the first draft used `sorted(lanes)[0]` and called it "strongest".
#: For {infra, prose, pyrust, research} that is alphabetical order with a decider's label —
#: the exact substitution this session kept finding. Ordering by hand makes it reviewable.
LANE_STRENGTH: tuple[str, ...] = (
    "substrate", "lean", "pyrust", "infra", "prose", "research")

#: A `Target:` line that looks like `path`, `` `path` ``, `path:12-40`, or prose that merely
#: BEGINS with a path.
_TARGET_RE = re.compile(r"[`\s\-*]*([\w./+-]+\.[A-Za-z0-9]+)(?::[\d\-–,]+)?")


def target_file(raw: str) -> str:
    """The FILE a target names, or `""` if it names none.

    ⚠️ **THE UNIT OF PARALLELISM IS THE FILE, NOT THE `Target:` STRING**, and the first draft
    got this wrong in the direction that matters. Targets carry line ranges, so
    `DriveCalibration.lean:612-641` and `DriveCalibration.lean:67-69` grouped as two units and
    were assigned to **wt2 and wt3** — two workers editing one file in two worktrees, which is
    precisely the collision target-grouping exists to prevent. Grouping by the raw string
    looked like it was preventing collisions while causing them.

    Also strips backticks and list bullets, and tolerates a target whose text continues into
    prose (several findings quote the offending sentence after the path).
    """
    m = _TARGET_RE.match((raw or "").strip())
    return m.group(1) if m else ""


def target_groups(nodes: list[dict]) -> tuple[list[dict], list[dict]]:
    """`(groups, untargeted)` — grouped by `target`, the unit of parallelism.

    Two findings on one file are not independent: the second worker rebases onto the first's
    edit or clobbers it. So the target is the unit, and one worker takes the whole group.

    ⚠️ **A finding with no `target` is returned SEPARATELY, never as a group.** Collecting
    them under a `(untargeted)` pseudo-key produces a bucket that renders exactly like a work
    unit — the first draft did, and put 20 findings spanning four lanes under one profile as
    if they were one file. Nobody can be told where to work; that is a filing defect to
    repair, not a task to dispatch.
    """
    by_target: dict[str, list[dict]] = defaultdict(list)
    untargeted: list[dict] = []
    for n in nodes:
        t = target_file(((n.get("meta") or {}).get("target") or ""))
        if not t:
            untargeted.append(n)
            continue
        by_target[t].append(n)
    groups = []
    for target, items in by_target.items():
        lanes = {(i["meta"].get("lane") or "unclassified") for i in items}
        lane = next(l for l in LANE_STRENGTH if l in lanes)
        groups.append({
            "target": target,
            "lane": lane,
            "spans_lanes": sorted(lanes) if len(lanes) > 1 else None,
            "findings": [i["id"] for i in items],
            "closable": [i["id"] for i in items if closable(i)],
            "unverifiable": [i["id"] for i in items if not closable(i)],
            "severity": sorted({i["meta"].get("severity") for i in items} - {None}),
        })
    # Most-blocking first: criticals, then majors, then group size.
    rank = {"critical": 0, "major": 1, "minor": 2, "advisory": 3}
    groups.sort(key=lambda g: (min((rank.get(s, 9) for s in g["severity"]), default=9),
                               -len(g["findings"]), g["target"]))
    return groups, untargeted


def plan(*, lane: str | None = None, slots: int | None = None) -> dict:
    """The wave plan. Pure enough to test: reads the graph, writes nothing, spawns nothing."""
    open_, ids, closed = _load_open_findings()
    if not open_:
        raise RuntimeError(
            "the open-finding population is EMPTY. A plan with nothing to do is "
            "indistinguishable from a queue this tool failed to read — refusing to render.")
    parts = classify(open_, ids, closed)
    total = sum(len(v) for v in parts.values())
    assert total == len(open_), (                      # the partition, asserted not claimed
        f"the buckets hold {total} of {len(open_)} open findings — some fell through")

    groups, untargeted = target_groups(parts["dispatchable"])
    if lane:
        groups = [g for g in groups if g["lane"] == lane]

    wt = lean_slots()
    assigned, slot_i = [], 0
    cap = slots if slots is not None else max(len(wt), 1)
    for g in groups[:cap]:
        prof = LANE_PROFILE[g["lane"]]
        if prof["isolation"] == "worktree-slot":
            # ⚠️ A Lean group with no slot free is NOT silently downgraded to an in-place
            # edit: two Lean workers sharing one `.lake` is the build corruption the slots
            # exist to prevent. It stays queued and says why.
            g = {**g, "slot": wt[slot_i] if slot_i < len(wt) else None}
            if g["slot"] is None:
                g["deferred"] = f"no free wtN slot ({len(wt)} exist, all assigned)"
            else:
                slot_i += 1
        assigned.append({**g, "agent": prof["agent"], "gates": prof["gates"]})

    return {
        "dispatch": assigned,
        "queued": len(groups) - len(assigned),
        "counts": {
            "open": len(open_),
            "dispatchable": len(parts["dispatchable"]),
            "blocked": len(parts["blocked"]),
            "unrouted": len(parts["unrouted"]),
            "target_groups": len(groups),
            "untargeted": len(untargeted),
            "lean_slots": len(wt),
        },
        "caveats": caveats(parts, groups, untargeted),
    }


def caveats(parts: dict, groups: list[dict], untargeted: list[dict]) -> list[str]:
    """What the plan cannot see — rendered beside it, never instead of it."""
    out = []
    n_unrouted = len(parts["unrouted"])
    if n_unrouted:
        out.append(
            f"{n_unrouted} open finding(s) carry no lane this router understands and are "
            f"NOT dispatched. They are not a backlog of easy work — they are unrouted, and "
            f"a default lane would hand physics to an infra worker. Run "
            f"`uv run python scripts/backfill_lanes.py --propose` and work the proposals.")
    unver = sum(len(g["unverifiable"]) for g in groups)
    if unver:
        out.append(
            f"{unver} dispatchable finding(s) declare NO `Verify:` command. They are planned "
            f"as work but NOT as closable: `close_finding` skips verification when none is "
            f"declared, so closing them would write `fixed` with an empty `verified_by`. "
            f"Authoring the verify line is part of the fix.")
    if untargeted:
        out.append(
            f"{len(untargeted)} dispatchable finding(s) name NO target and are not planned. "
            f"A worker cannot be told where to work, and grouping them under one pseudo-key "
            f"would render as a work unit while spanning unrelated lanes. This is a FILING "
            f"defect — add a `Location:`/`Target:` line to each — not a task to dispatch.")
    spanning = [g["target"] for g in groups if g["spans_lanes"]]
    if spanning:
        out.append(
            f"{len(spanning)} target(s) carry findings from more than one lane; each is "
            f"planned under the STRONGEST profile of those lanes, never an arbitrary one.")
    if not lean_slots():
        out.append("no `wtN` worktree slots exist — Lean and substrate groups cannot be "
                   "dispatched in isolation. `scripts/setup_lean_worktree_slots.sh` creates "
                   "them.")
    return out


def render(p: dict) -> str:
    c = p["counts"]
    out = [
        "REMEDIATION WAVE PLAN — ADR-012 P10",
        "",
        f"  open {c['open']} · dispatchable {c['dispatchable']} · blocked {c['blocked']} "
        f"· unrouted {c['unrouted']}",
        f"  {c['target_groups']} target group(s); {len(p['dispatch'])} dispatched now, "
        f"{p['queued']} queued; {c['lean_slots']} Lean slot(s)",
        "",
    ]
    for g in p["dispatch"]:
        head = f"  ▸ {g['lane']:<9} {g['target']}"
        if g.get("slot"):
            head += f"   [{g['slot']}]"
        if g.get("deferred"):
            head += f"   ⏸ {g['deferred']}"
        out.append(head)
        out.append(f"      {g['agent']} · {len(g['findings'])} finding(s) · "
                   f"{len(g['closable'])} closable, {len(g['unverifiable'])} unverifiable")
        if g["spans_lanes"]:
            out.append(f"      ⚠️ spans lanes {g['spans_lanes']} — strongest profile applied")
    if p["caveats"]:
        out.append("")
        for line in p["caveats"]:
            out.append(f"  ⚠️ {line}")
    out.append("")
    return "\n".join(out)


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    ap.add_argument("--lane", choices=sorted(LANE_PROFILE), help="plan one lane only")
    ap.add_argument("--slots", type=int, help="cap the fan-out (default: one per wtN slot)")
    ap.add_argument("--json", action="store_true", help="machine-readable")
    args = ap.parse_args(argv)

    p = plan(lane=args.lane, slots=args.slots)
    print(json.dumps(p, indent=2, default=str) if args.json else render(p), end="")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
