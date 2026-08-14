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
2026-08-13: **969 open** findings, **308 dispatchable**, of which **74 declare a `verify`
command**. (This paragraph said "965 dispatchable … the other 891" — 965 was no population
at all and 891 was computed over *open*, printed directly above the tool's own
`open 969 · dispatchable 308` line. Two scopes in one sentence, pr-review 2026-08-13.)
`close_finding._run_verifications` skips a finding that declares none (`if not cmd: continue`),
so the rest can be recorded `fixed` with an empty `verified_by` — a closure nothing proved.
D6 grandfathered that for records written *before* the writer existed; it was never a licence
for new ones. A loop that dispatches and closes at machine speed turns a slow leak into
a firehose, so an unverifiable finding is **PLANNED BUT NOT CLOSABLE** here, and says so.

⚠️ **`unclassified` IS NOT A LANE, AND IS NOT COERCED INTO ONE.** 657 of 969 open findings
carry no declared lane. Routing them to a default would hand physics work to an infra worker
and read, downstream, exactly like routing that succeeded. They are reported as an unrouted
population with the tool that fixes them (`backfill_lanes.py --propose`) named on the face of
the output. An unrouted finding is work the queue cannot yet dispatch, which is different from
work it has dispatched badly.

⚠️ **Fan-out is keyed on FILES, and the unit is a CONNECTED COMPONENT over them.** Two
findings touching one file are not independent — the second worker rebases onto the first's
edit or clobbers it — and 56 of 308 dispatchable findings name MORE than one file, so
"one finding, one target" is not even well defined. Findings that share any file share a
worker, which makes the grouping a union-find rather than a dict. Three separate drafts of
this put one file in two workers' hands; see `target_files`.
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
    """The `wtN` slots that are USABLE Lean worktrees, sorted.

    ⚠️ **A DIRECTORY NAMED `wtN` IS NOT A SLOT** (pr-review 2026-08-13). The first version
    accepted any `wt*` directory, so `mkdir .claude/worktrees/wt9` — an empty dir, no
    checkout, no `.lake` — became a plannable slot and a Lean group was assigned to it. The
    decider for "a Lean worker can build here in isolation" is a git worktree with its own
    Lean tree, so both are required: a leftover or half-removed slot must not be planned into.
    """
    base = PROJECT_ROOT / ".claude" / "worktrees"
    if not base.is_dir():
        return []
    return sorted(
        p.name for p in base.iterdir()
        if p.is_dir() and p.name.startswith("wt") and p.name[2:].isdigit()
        and (p / "lean").is_dir() and (p / ".git").exists())


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

    ⚠️ **The three buckets partition by construction — if/elif/else — so DO NOT "assert" it.**
    `plan()` used to, and both that statement and the test restating it were theorems about
    the loop rather than measurements of it (and the assert vanishes under `python -O`). The
    population that IS droppable is dropped downstream — untargeted, cap-queued, and whatever
    a `--lane` filter removes — so that is where a real conservation check belongs.
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


#: Files EVERY substrate/lean unit implicitly writes, which no finding ever declares.
#: ⚠️ THE ORCHESTRATOR'S DISJOINTNESS IS OVER DECLARED TARGETS, AND A FIX WRITES MORE THAN
#: ITS TARGET. Measured 2026-08-13: wt2 and wt3 were dispatched as disjoint (their Lean files
#: were), then both edited `constants.py` and `aristotle_interface.py`, because a substrate
#: repair that changes a theorem's provenance MUST touch the registries. They auto-merged only
#: because the two workers happened to edit different regions — git's line-level merge, not
#: this planner's guarantee.
#:
#: Serialising the lane on these files would be correct and useless: nearly every substrate fix
#: touches them, so the fan-out would collapse to one. The rule instead follows the doctrine
#: already in force for the ledger — **a registry has ONE writer** (`close_finding.py`). A
#: worker reports the registry change it needs; the LEAD applies it at merge.
SHARED_REGISTRIES: tuple[str, ...] = (
    "src/core/constants.py",
    "src/core/aristotle_interface.py",
)


def registry_note(lane: str) -> str | None:
    """The instruction a dispatched worker in a registry-writing lane must carry."""
    if lane not in ("lean", "substrate", "pyrust"):
        return None
    return ("do NOT edit " + " or ".join(SHARED_REGISTRIES) + " — report the registry change "
            "you need and the lead applies it at merge. Two workers dispatched as disjoint "
            "both wrote these files on 2026-08-13 and merged cleanly by luck.")


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


def target_files(raw: str) -> list[str]:
    """EVERY repo file a target names, canonical and existing — possibly none, possibly many.

    ⚠️ **THREE SEPARATE WAYS THE FIRST TWO DRAFTS PUT ONE FILE IN TWO WORKERS' HANDS.**
    Draft 1 keyed on the raw `Target:` string, so `Drive.lean:612-641` and `Drive.lean:67-69`
    became two units. Draft 2 stripped the line range but returned the path *as written* and
    took only the FIRST match, which left two more holes, both measured live:

    * **Spelling.** `SK_EFT_Hawking/papers/I2/paper_draft.tex` and `papers/I2/paper_draft.tex`
      are one file and were two group keys. 10 of 95 keys did not exist from the repo root at
      all — including a bare `paper_draft.tex` (a 2-finding group keyed on a name that is not
      a file: the `(untargeted)` pseudo-group again, wearing a filename) and a bare
      `OnsagerAlgebra.lean`, which consumed **wt3** for a path no worker could open.
    * **Multiplicity.** 56 of 308 dispatchable findings name more than one file, and the rest
      were silently dropped — including `…/RokhlinBridge.lean, papers/L2/paper_draft.tex`,
      which resolved to the `.tex` and was therefore planned under **prose**, with no build
      gate, for a finding requiring a Lean edit. `LANE_STRENGTH` cannot save that: it ranks
      the lanes of findings sharing a key, and the key had already thrown the Lean file away.

    So this returns **all** of them, each `resolve()`d against the repo and **required to
    exist**. A path that does not resolve is not a target — reporting it as one is how a
    worker gets sent to a file that is not there.
    """
    out, seen = [], set()
    for m in _TARGET_RE.finditer(raw or ""):
        cand = m.group(1).strip("`.,;")
        for base in (PROJECT_ROOT, PROJECT_ROOT.parent):   # tolerate a `SK_EFT_Hawking/` prefix
            try:
                p = (base / cand).resolve()
                rel = p.relative_to(PROJECT_ROOT).as_posix()
            except (ValueError, OSError):
                continue
            if not p.is_file():
                continue          # ⚠️ NOT `break` — the first draft of this very fix broke
                                  # out of the base loop unconditionally, so the
                                  # `SK_EFT_Hawking/…` spelling never reached the second
                                  # base and stayed a separate group key: the defect being
                                  # repaired, surviving inside its own repair.
            if rel not in seen:
                seen.add(rel)
                out.append(rel)
            break
    return out


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
    # ⚠️ A SHARED FILE IS A RESOURCE CONFLICT, NOT A REASON TO WELD TASKS TOGETHER.
    # The previous version merged findings transitively over shared files (a union-find).
    # It was collision-safe but conflated "what is one task" with "what may run at once":
    # a hub file like `src/core/citations.py` chained unrelated work into ONE unit of 107
    # findings spanning four lanes, which would have gone to a single lean-worker carrying
    # prose and infra. Measured alternative: group by a finding's OWN file set and enforce
    # disjointness at DISPATCH — 120 units instead of 69, largest 22 instead of 107, and
    # 86 runnable concurrently instead of 69. Better on unit size, parallelism AND the
    # safety property at once, so this is a repair, not a tradeoff.
    by_component: dict[tuple, list[dict]] = defaultdict(list)
    untargeted: list[dict] = []
    files_of: dict[str, list[str]] = {}
    for n in nodes:
        fs = target_files((n.get("meta") or {}).get("target") or "")
        if not fs:
            untargeted.append(n)
            continue
        files_of[n["id"]] = fs
        by_component[tuple(fs)].append(n)

    groups = []
    for _root, items in by_component.items():
        lanes = {(i["meta"].get("lane") or "unclassified") for i in items}
        lane = next(l for l in LANE_STRENGTH if l in lanes)
        files = sorted({f for i in items for f in files_of[i["id"]]})
        groups.append({
            "target": files[0] if len(files) == 1 else f"{files[0]} (+{len(files) - 1})",
            "files": files,
            "lane": lane,
            "spans_lanes": sorted(lanes) if len(lanes) > 1 else None,
            "findings": [i["id"] for i in items],
            "closable": [i["id"] for i in items if closable(i)],
            "unverifiable": [i["id"] for i in items if not closable(i)],
            "severity": sorted({i["meta"].get("severity") for i in items} - {None}),
        })
    # Most-blocking first: criticals, then majors, then group size.
    # ⚠️ The order is DERIVED from the declared vocabulary, not restated. A hand-written
    # rank silently sorts a newly-declared severity BELOW advisory — never dispatched, no
    # error — which is the "hand-maintained list parallel to a registry" the authoring
    # guide names. `_LANE_DECL_MAP` is already pinned this way for lanes.
    from build_graph import _SEVERITY_DECL_MAP
    order = ["critical", "major", "minor", "advisory"]
    rank = {s: order.index(s) if s in order else len(order)
            for s in set(_SEVERITY_DECL_MAP.values()) | set(order)}
    groups.sort(key=lambda g: (min((rank.get(s, len(order)) for s in g["severity"]),
                                   default=len(order)),
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

    groups, untargeted = target_groups(parts["dispatchable"])
    if lane:
        groups = [g for g in groups if g["lane"] == lane]

    wt = lean_slots()
    if slots is not None and slots < 0:
        raise ValueError(f"--slots must be >= 0, got {slots}; a negative slice bound "
                         f"dispatches all but the last group and reports queued=1")

    # ⚠️ THE CAP IS PER ISOLATION CLASS. One global cap of `len(wt)` was a Lean-worktree
    # budget applied to every lane: measured at HEAD it dispatched three PROSE groups,
    # left all three slots idle, and never reached a Lean group — a fan-out tool planning
    # zero parallel Lean work while its isolated slots sat empty, against the standing
    # rule to saturate them. Slot-bound lanes are capped by free slots; the rest are
    # capped separately.
    slot_cap = len(wt) if slots is None else slots
    free_cap = 3 if slots is None else slots

    assigned, queued, slot_i, free_i = [], [], 0, 0
    held: set[str] = set()          # files a dispatched group is already editing
    for g in groups:
        # ⚠️ THE COLLISION GUARANTEE LIVES HERE, at dispatch, not in the grouping. Two
        # units touching one file are both valid tasks; they simply may not run at the
        # same time. A hub file therefore means "one unit per wave", and the rest queue —
        # instead of every task that mentions it being fused into one.
        overlap = held & set(g["files"])
        if overlap:
            queued.append({**g, "deferred":
                           f"file(s) held by a dispatched group: {sorted(overlap)[:3]}"})
            continue
        prof = LANE_PROFILE[g["lane"]]
        if prof["isolation"] == "worktree-slot":
            # ⚠️ A Lean group with no free slot is EXCLUDED from dispatch, not annotated.
            # It was previously left in `dispatch[]` carrying a `deferred` string while
            # `queued` reported 0 — so a `--json` consumer spawning one worker per entry
            # spawned 13 Lean workers onto 3 `.lake`s: exactly the build corruption the
            # slots exist to prevent, produced by the code that documents preventing it.
            if slot_i >= slot_cap or slot_i >= len(wt):
                queued.append({**g, "deferred": f"no free wtN slot ({len(wt)} exist)"})
                continue
            g = {**g, "slot": wt[slot_i]}
            slot_i += 1
        else:
            if free_i >= free_cap:
                queued.append({**g, "deferred": "beyond the non-isolated fan-out cap"})
                continue
            free_i += 1
        held |= set(g["files"])
        assigned.append({**g, "agent": prof["agent"], "gates": prof["gates"],
                         "isolation": prof["isolation"],
                         "registry_rule": registry_note(g["lane"])})

    return {
        "dispatch": assigned,
        "queued": len(queued),
        "queued_groups": queued,
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
