"""Shared helpers for the skeft-qa dev-harness (hooks + skills). Stdlib only; fail-open.
Runs under THIS repo's uv-managed Python (>=3.14) — the hooks invoke it via
`uv run --no-sync python` and the plugin's requires-python is >=3.14; modern 3.14 syntax
is fine (no legacy interpreter constraint).

DEFAULT-INERT: acts only for a *managed* /goal loop (a marker exists for this
session_id in THIS plugin's repo) and NEVER for a subagent (agent_id present).

State is PROJECT-SCOPED at <repo>/.claude/dev-harness/, where
  <repo> = repo_root() = find_workspace() / REPO_DIR_NAME.
REPO_DIR_NAME is a constant naming THIS plugin copy's OWN repo dir ("SK_EFT_Hawking").
(A sibling deployment ships its own copy with its own dir name.) This is:
  * cwd-based / CACHE-SAFE: it does NOT walk $CLAUDE_PLUGIN_ROOT — for a marketplace
    install that path lives in the ~/.claude cache, itself a git repo, so a git-root
    walk would resolve to ~/.claude, not the project (review BLOCKER);
  * launch-robust: works from inside the repo OR the non-git workspace root;
  * leak-safe by construction: this copy's constant is its OWN repo dir name only, so it
    resolves to (and reads markers in) only its own repo — never a sibling's.

This is the harness's OWN copy of find_workspace (spec A.3, review item 5) — it is
NOT an import of src.core.workspace. That module is ours and fine for the repo's own
scripts, but it defaults `start` to Path(__file__) and its fallback derives from
__file__'s position; for a marketplace-cache plugin that fallback resolves into
~/.claude (the cache git repo — the A.3 trap). This copy instead (a) takes the hook
payload's `cwd` (hooks) / os.getcwd() (skills) as `start`, and (b) uses the cache-safe
fallback (a cwd git-root only if its basename == REPO_DIR_NAME, else None -> inert). It
shares the structural detection but cannot rely on src.core being importable from a
plugin and needs cwd-start semantics — hence the own copy, not the import.
"""

import json
import os
import subprocess
import sys
import time
from pathlib import Path

# This plugin copy's OWN repo dir name. A sibling deployment ships its own copy + name.
REPO_DIR_NAME = "SK_EFT_Hawking"


def _git_root(start):
    try:
        out = subprocess.run(
            ["git", "-C", str(start), "rev-parse", "--show-toplevel"],
            capture_output=True,
            text=True,
        )
        if out.returncode == 0 and out.stdout.strip():
            return Path(out.stdout.strip())
    except Exception:
        pass
    return None


def find_workspace(start=None):
    """Workspace root: the ancestor (or self) of `start` (default cwd) that contains
    `.mcp.json` AND `SK_EFT_Hawking/` and is NOT itself a git repo. None if not found.
    Public-safe: keys only on this repo's own dir name."""
    try:
        cur = Path(start or os.getcwd()).resolve()
    except Exception:
        return None
    for d in [cur] + list(cur.parents):
        try:
            if (
                (d / ".mcp.json").is_file()
                and (d / REPO_DIR_NAME).is_dir()
                and not (d / ".git").exists()
            ):
                return d
        except Exception:
            continue
    return None


def repo_root(start=None):
    """This plugin's OWN repo root. cwd-based, cache-safe, leak-safe. None if unresolved."""
    ws = find_workspace(start)
    if ws is not None:
        cand = ws / REPO_DIR_NAME
        if cand.is_dir():
            return cand
    # Fallback (leak-safe): a cwd git-root, accepted ONLY if its basename is our repo.
    r = _git_root(Path(start) if start else Path.cwd())
    if r is not None and r.name == REPO_DIR_NAME:
        return r
    return None


def jsonl_path(sid, start=None):
    """Resolve THIS session's transcript path. We do NOT guess or compute a session id: `sid` is the
    REAL current id, supplied by Claude Code as ${CLAUDE_SESSION_ID} — the same UUID CC names the
    transcript <sid>.jsonl by. The id is GIVEN; only the PATH around it is assembled, and that path is
    fully DETERMINISTIC given the id: ~/.claude/projects/<cwd-slug>/<sid>.jsonl. That is what lets
    goal-prompt record the path on a FIRST-turn arm, when CC has not yet flushed the .jsonl to disk
    (the harvest reads it later, by which point CC has written it to exactly that path).

      (1) If a transcript literally named <sid>.jsonl already exists under ~/.claude/projects/*/ ,
          return that actual file (exact; covers a resumed session whose file is already on disk).
      (2) Else reconstruct ~/.claude/projects/<slug>/<sid>.jsonl, where <slug> = the session cwd with
          every non-alphanumeric char -> '-' (CC's encoding; verified against real slug dirs incl. the
          double-'-' `.claude-worktrees` case). This is the exact path CC WILL write this session to.

    FAIL-SAFE: returns '' when `sid` is empty (no id -> goal-prompt STOPs rather than arm a marker
    pointing at no/the-wrong transcript). It never resolves a DIFFERENT session's file. The glob in (1)
    is also the safety net: if the dir encoding were ever off, an existing file is still found by id.
    `start` overrides the cwd (tests)."""
    if not sid:
        return ""
    import re

    proj = Path.home() / ".claude" / "projects"
    try:
        hits = sorted(proj.glob("*/" + str(sid) + ".jsonl"))
        if hits:
            return str(hits[0])
    except Exception:
        pass
    cwd = str(start) if start else os.getcwd()
    slug = re.sub(r"[^A-Za-z0-9]", "-", cwd)
    return str(proj / slug / (str(sid) + ".jsonl"))


def harness_dir(root):
    return root / ".claude" / "dev-harness"


def marker_path(root, sid):
    return harness_dir(root) / "managed" / (sid + ".json")


def remove_marker(root, sid):
    """Tear down THIS session's managed-loop marker (+ its watermark). Used by the explicit
    `/goal-end` command and the SessionEnd cleanup hook (RC5 — the marker has no teardown on
    `/goal clear`, so a dead loop's marker keeps the re-inject + guard firing). Best-effort /
    fail-open; returns True iff a marker existed and was removed. Leak-safe: only this repo."""
    if root is None or not sid:
        return False
    try:
        mp = marker_path(root, sid)
        existed = mp.exists()
        mp.unlink(missing_ok=True)
        wp = watermark_path(root, sid)
        wp.unlink(missing_ok=True)
        return existed
    except Exception:
        return False


def active_issues_path(root):
    # Contract: Plan 3's harvest consolidator WRITES this gitignored cache.
    return harness_dir(root) / "active_issues.json"


def blocked_questions_path(root):
    # Contract C: the guard APPENDS intercepted questions here; Plan 3 reads it.
    return harness_dir(root) / "blocked_questions.jsonl"


def read_event():
    try:
        return json.load(sys.stdin)
    except Exception:
        return {}


def read_marker(ev):
    """This session's managed-loop marker, or None (== inert).

    None when: not a dict, a subagent (agent_id), no session_id, repo unresolved,
    or no marker file for this session in this plugin's repo. The workspace walk
    starts from the event's `cwd` (authoritative) when present.
    """
    if not isinstance(ev, dict) or ev.get("agent_id"):
        return None
    sid = ev.get("session_id")
    root = repo_root(ev.get("cwd"))
    if not sid or root is None:
        return None
    try:
        return json.loads(marker_path(root, sid).read_text())
    except Exception:
        return None


def emit_context(event_name, text):
    try:
        print(
            json.dumps(
                {
                    "hookSpecificOutput": {
                        "hookEventName": event_name,
                        "additionalContext": text,
                    }
                }
            )
        )
    except Exception:
        pass


# The platform HARD LIMIT on a hook's hookSpecificOutput.additionalContext is 10,000 chars. Over it,
# Claude Code does NOT truncate — it writes the text to a session file and hands the model a path +
# short preview (verified against the official hooks docs), recreating the exact "model sees a pointer,
# not the content" failure the post-compaction durability fix exists to prevent. So the EMITTED
# additionalContext must stay under this END-TO-END (payload + the compose_directive frame + notes).
ADDITIONAL_CONTEXT_LIMIT = 10000
# Reserve for what is appended AFTER the payload (the trimmed compose_directive frame one-liner + the
# conditional drift/notebook notes) + a safety margin — so bounding the PAYLOAD alone guarantees the
# emitted additionalContext stays under the limit end-to-end.
_WRAPPER_RESERVE = 700
# Effective PAYLOAD budget. The /goal condition (≤4k, ALWAYS full — overrides every other item) and the
# always-on RE_ANCHOR are kept in full; only the per-goal COACHING BLOCK is droppable. The pre-decisions
# are NO LONGER injected — they are a MANDATORY READ (FIRST_ACTION), so they grow UNBOUNDED in
# docs/dev-loops/PRE_DECISIONS.md with zero payload-budget pressure (CORE_MAX_CHARS retired).
PAYLOAD_MAX_CHARS = ADDITIONAL_CONTEXT_LIMIT - _WRAPPER_RESERVE
ACTIVE_ISSUES_MAX = 8  # at most the top-N findings, dropped further until under cap


def _tier_rank(issue):
    """Sort key helper: human-reviewed > agent-reviewed > automatic (desc), then tally desc.
    Tolerates plain-string issues (rank 0 / tally 0). Returns a tuple sorted descending."""
    order = {"human-reviewed": 3, "agent-reviewed": 2, "automatic": 1}
    if isinstance(issue, dict):
        tier = order.get(str(issue.get("tier", "")).lower(), 0)
        try:
            tally = int(issue.get("tally", 0) or 0)
        except Exception:
            tally = 0
        return (tier, tally)
    return (0, 0)


def _read_active_issues(root, max_items=ACTIVE_ISSUES_MAX):
    """The active System-2 issues view (contract: written by Plan 3's harvest).
    Absent / first-run / malformed -> '' so the payload omits the section gracefully.
    Returns at most `max_items` findings, sorted by tier (human-reviewed > agent-reviewed
    > automatic) desc, then tally desc — the truncatable part of the budgeted payload (C1)."""
    if root is None:
        return ""
    try:
        data = json.loads(active_issues_path(root).read_text())
    except Exception:
        return ""
    # Tolerate either a list of issue strings/objects or a {"issues": [...]} wrapper.
    items = data.get("issues", data) if isinstance(data, dict) else data
    if not isinstance(items, list):
        return ""
    # Sort by tier desc, then tally desc; keep only the top `max_items`.
    try:
        items = sorted(items, key=_tier_rank, reverse=True)
    except Exception:
        pass
    lines = []
    for it in items[: max(0, int(max_items))]:
        # Process wins are NOT injected (ruling 2026-06-20): the active-issues view is open
        # issues only; a win reaches the loop via /debrief -> human-reviewed -> harness integration.
        if isinstance(it, dict):
            lines.append("- " + str(it.get("summary") or it.get("title") or it))
        else:
            lines.append("- " + str(it))
    return "\n".join(lines)


# Short, static decision-heuristics summary (the full text lives in the goal-dev
# skill's references/decision-heuristics.md; this is the in-loop reminder).
DECISION_HEURISTICS = (
    "Decision heuristics: scope is SETTLED — do the next increment of real work THIS "
    "turn. A stop-hook firing is a GO signal, never a cue to stop/hold/re-scope. If "
    "you feel blocked, run full diligence first (re-read the roadmap + notebook, "
    "reason about tradeoffs); if one option is clearly best, TAKE IT and log the "
    "rationale in the notebook. Legitimate stops only: a kernel-checked no-go or a "
    "genuine user-only decision."
)

# (self-check headroom retired — the budget is now end-to-end via _WRAPPER_RESERVE, and the
# separate first-turn self-check is folded into the always-injected RE_ANCHOR.)


def _frontier_for(marker):
    """Extract the lab-notebook FRONTIER digest (from the marker's INDEX) for in-context
    re-grounding — so a post-compaction turn acts on the next brick with ZERO Reads. Guarded +
    fail-soft: returns '' if notebook_lib / the INDEX / the FRONTIER is unavailable, so the
    payload degrades cleanly to the INDEX pointer in the SessionStart frame."""
    try:
        nb = marker.get("notebook_path", "")
        if not nb:
            return ""
        sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
        import notebook_lib as nl

        return nl.extract_frontier(nb)
    except Exception:
        return ""


def frontier_from_atlas(root, max_items=8):
    """Read the DERIVED atlas frontier (`<repo>/lean/atlas_view.json`, ADR-005 D-I) — the project's
    OPEN assumptions ranked by how much each gates — for atlas-GUIDED fan-out (vs roadmap-opaque work
    selection). Returns ``{"frontier": [top max_items], "apex_ids": [...], "tracks": {...}}`` or
    ``None`` if the atlas is absent/unreadable. FAIL-SOFT by design: the atlas is a VIEW the lead
    CONSULTS to prioritize, never a dependency — a missing/stale atlas degrades to ``None`` and the
    loop falls back to the roadmap + lab-notebook frontier. Read-only (never triggers extraction)."""
    if root is None:
        return None
    try:
        atlas = json.loads((root / "lean" / "atlas_view.json").read_text())
    except Exception:
        return None
    return {
        "frontier": list(atlas.get("frontier", []))[: max(0, int(max_items))],
        "apex_ids": list(atlas.get("summary", {}).get("apex_ids", [])),
        "tracks": dict(atlas.get("tracks", {})),
    }


def format_atlas_frontier(root, max_items=8):
    """Bounded plain-text digest of :func:`frontier_from_atlas` — the lead's atlas-guided fan-out
    compass (a per-track rollup + the most-gating open assumptions). FAIL-SOFT -> ``''`` if the atlas
    is absent, so callers can ``if s: ...``. ASCII-only (it rides the SessionStart payload)."""
    data = frontier_from_atlas(root, max_items)
    if not data or not data.get("frontier"):
        return ""
    lines = []
    tracks = data.get("tracks") or {}
    if tracks:
        roll = ", ".join(
            "%s:%d%s" % (t, v.get("open_count", 0),
                        ("/%dapex" % v["apex_count"]) if v.get("apex_count") else "")
            for t, v in tracks.items()
        )
        lines.append("tracks (open by area): " + roll)
    lines.append("most-gating OPEN assumptions (discharge unlocks the most downstream):")
    for f in data["frontier"]:
        star = " *apex" if f.get("is_apex") else ""
        lines.append("  %3d  %s  [%s/%s]%s" % (
            int(f.get("frontier_impact", 0)), f.get("id", "?"),
            f.get("tier", "?"), f.get("eliminability", "?"), star))
    return "\n".join(lines)


def _read_predecisions_core(root):
    """The pre-decisions CORE — the `## Core` section of the tracked docs/dev-loops/PRE_DECISIONS.md.
    NO LONGER injected into the payload (the Core is now a MANDATORY READ — see FIRST_ACTION — so it
    grows unbounded with zero payload pressure); kept as a helper (coach / tests / future checks).
    The store lives in docs/ (NOT the plugin) so /debrief graduates a pre-decision by editing that file
    alone — no plugin cache refresh. Fail-soft: returns the static DECISION_HEURISTICS digest if the
    file / the Core section is absent or unreadable."""
    if root is None:
        return DECISION_HEURISTICS
    try:
        import re
        text = (root / "docs" / "dev-loops" / "PRE_DECISIONS.md").read_text()
        m = re.search(r"\n## Core\b.*?(?=\n## )", "\n" + text, re.DOTALL)
        core = re.sub(r"^## Core[^\n]*\n+", "", m.group(0).strip()).strip() if m else ""
        return ("PRE-DECISIONS (always-on — apply WITHOUT asking):\n" + core) if core else DECISION_HEURISTICS
    except Exception:
        return DECISION_HEURISTICS


RE_ANCHOR = (
    "RE-ANCHOR before resuming (do this FIRST): a compaction summary optimizes tactical continuity "
    "over strategic anchoring — it can surface a mid-air tactic and drop the close-path. Before "
    "continuing whatever tactic the summary surfaced, confirm it still matches the close-path: the "
    "live LAB-NOTEBOOK FRONTIER below (always current — the loop's own latest state) and the COACHING "
    "BLOCK if present (an external harvest read — sharper analysis, but it may lag). If they conflict "
    "and the coaching block is recent, the harvest likely caught a drift you can't self-see."
)

FIRST_ACTION = (
    "FIRST ACTION this turn, before anything else: (1) READ docs/dev-loops/PRE_DECISIONS.md — the "
    "standing pre-decisions you MUST apply this turn (when to stop, climb the ladder, bank a "
    "hypothesis, re-anchor at a boundary); do NOT skip — they are not injected here, this read is how "
    "you load them. (2) Invoke /skeft-qa:goal-dev (the MCP-first proof loop, kernel-purity rules, "
    "/reset-slot + worktree fan-out, the symptom-indexed friction catalog). (3) If the goal involves "
    "Lean, also invoke lean4. Then resume the next increment."
)


def coaching_path(root, goal_id):
    """Per-goal COACHING BLOCK cache (the tier-2 re-orientation brief). Contract: the
    /skeft-qa:harvest consolidator WRITES it; build_reorientation_payload READS it. Per-goal so a
    multi-goal workspace can't cross-contaminate. Gitignored; absent until the first harvest."""
    return harness_dir(root) / "coaching" / (str(goal_id) + ".json")


def _read_coaching_block(root, goal_id, now):
    """Read the per-goal COACHING BLOCK (harvest-authored re-orientation) -> {"text","age_label"} or
    None. OPTIONAL BY DESIGN: absent for a new goal until the first harvest (≤ the cadence, default
    4h) and it AGES between harvests — so it is NEVER a dependency; the always-injected RE_ANCHOR + the
    live FRONTIER are the baseline. The age_label lets the loop treat a laggy block as advisory and
    defer to the live frontier. Fail-soft -> None."""
    if root is None or not goal_id:
        return None
    try:
        data = json.loads(coaching_path(root, goal_id).read_text())
    except Exception:
        return None
    text = str(data.get("text") or data.get("block") or "").strip()
    if not text:
        return None
    try:
        age_h = max(0.0, (float(now) - float(data.get("authored_ts", 0))) / 3600.0)
    except Exception:
        age_h = 0.0
    if age_h < 1.0:
        age_label = "harvest-authored <1h ago"
    elif age_h < 8.0:
        age_label = "harvest-authored ~%.0fh ago" % age_h
    else:
        age_label = "harvest-authored ~%.0fh ago — LIKELY SUPERSEDED, treat as advisory" % age_h
    return {"text": text, "age_label": age_label}


def build_reorientation_payload(marker, repo_root):
    """Contract B — the SHARED re-orientation payload (SessionStart re-inject + the
    PreToolUse(AskUserQuestion) guard). Structure (post-redesign):
      * SETTLED GOAL (marker['goal'], ≤4k, ALWAYS in full — overrides every other budget item; the
        durable copy is the tracked goal_prompt_<goal_id>.md),
      * RE_ANCHOR — the always-on generic re-anchor (PD-4 essence; coaching-INDEPENDENT, so it
        survives an absent/lagging coaching block),
      * the live LAB-NOTEBOOK FRONTIER digest (always current; a ZERO-Read next brick),
      * a 're-read CLAUDE.md' pointer,
      * FIRST_ACTION — mandates the pre-decisions READ + goal-dev (the pre-decisions are NO LONGER
        injected; the read is how they load -> they grow unbounded with no payload pressure),
      * the per-goal COACHING BLOCK if present (staleness-labeled; the droppable ENHANCEMENT —
        included whole only if it fits, never required, never truncated mid-text).
    `marker` is the managed marker; `repo_root` may be None (coaching omitted). Fail-soft.

    END-TO-END BUDGET: the payload stays < PAYLOAD_MAX_CHARS (= ADDITIONAL_CONTEXT_LIMIT −
    _WRAPPER_RESERVE), so the EMITTED additionalContext (payload + the compose_directive frame +
    conditional notes) stays under the real 10k platform limit. Goal + RE_ANCHOR are always full;
    only the COACHING BLOCK is droppable."""
    if not isinstance(marker, dict):
        marker = {}
    goal = marker.get("goal", "")
    parts = []
    if goal:
        parts.append("SETTLED GOAL (the /goal condition):\n" + goal)
    parts.append(RE_ANCHOR)
    frontier = _frontier_for(marker)
    if frontier:
        parts.append(
            "LAB-NOTEBOOK FRONTIER (the live, always-current next-brick digest — act on its NEXT "
            "BRICK directly; no Read needed; open the INDEX / shards only for deeper context):\n" + frontier
        )
    parts.append("Re-read CLAUDE.md (the giant-ref pointer that should be re-read).")
    parts.append(FIRST_ACTION)
    # ATLAS FRONTIER (ADR-005 D-I) — the cross-project most-gating OPEN assumptions, a complementary
    # lens to the lab-notebook's LOCAL next-brick: consult it to aim fan-out at high-leverage provable
    # work. Small + droppable (included only if it fits the budget); fail-soft -> '' (never a dependency).
    atlas_fr = format_atlas_frontier(repo_root)
    if atlas_fr:
        block = ("ATLAS FRONTIER (derived; most-gating OPEN assumptions across the project — consult to "
                 "aim fan-out, `/skeft-qa:frontier` for the full ranked list):\n" + atlas_fr)
        if len("\n\n".join(parts + [block])) < PAYLOAD_MAX_CHARS:
            parts.append(block)
    # COACHING BLOCK — the OPTIONAL enhancement (see _read_coaching_block). Included whole only if the
    # whole payload still fits the budget; else dropped (graceful — the RE_ANCHOR + live FRONTIER above
    # are the baseline). Never required, never truncated mid-text.
    coaching = _read_coaching_block(repo_root, marker.get("goal_id"), time.time())
    if coaching:
        block = (
            "COACHING BLOCK (%s — an external harvest read; advisory, defer to the live FRONTIER if "
            "they conflict and this is old):\n%s" % (coaching["age_label"], coaching["text"])
        )
        if len("\n\n".join(parts + [block])) < PAYLOAD_MAX_CHARS:
            parts.append(block)
    return "\n\n".join(parts)


# ── Plan 3 (System-2 harvest) helpers ────────────────────────────────────────────────
# All resolve <repo> via repo_root() (cwd-based) and are FAIL-OPEN unless noted. The
# watermark is a per-session BYTE-OFFSET (NOT a uuid — uuids are ~39% duplicated in real
# transcripts, spec A.1), advanced atomically + monotonically only after a findings write.


def watermark_path(root, sid):
    return harness_dir(root) / "watermarks" / (sid + ".json")


def read_watermark(sid):
    """Per-session byte-offset watermark (0 if absent / unresolved)."""
    root = repo_root()
    if root is None:
        return 0
    try:
        return int(
            json.loads(watermark_path(root, sid).read_text()).get("byte_offset", 0)
        )
    except Exception:
        return 0


def advance_watermark(sid, offset):
    """Advance the watermark atomically (temp + os.replace) and MONOTONICALLY (max(old,new))
    — append-only transcripts make byte offsets stable, so the watermark never regresses.
    Best-effort / fail-open."""
    root = repo_root()
    if root is None:
        return
    try:
        new = max(int(read_watermark(sid)), int(offset))
        p = watermark_path(root, sid)
        p.parent.mkdir(parents=True, exist_ok=True)
        tmp = p.parent / (p.name + ".tmp")
        tmp.write_text(json.dumps({"session_id": sid, "byte_offset": new}))
        os.replace(str(tmp), str(p))
    except Exception:
        pass


def harvest_state_path(root):
    return harness_dir(root) / "harvest_state.json"


def read_harvest_state():
    """{} if absent (first run -> the SessionStart drift warning stays silent)."""
    root = repo_root()
    if root is None:
        return {}
    try:
        return json.loads(harvest_state_path(root).read_text())
    except Exception:
        return {}


def write_harvest_state(ts, cadence_hours):
    """Record the harvest's last-run timestamp + configured cadence (the drift warning
    reads BOTH, so its threshold is 2x cadence, not hardcoded). Atomic / fail-open."""
    root = repo_root()
    if root is None:
        return
    try:
        p = harvest_state_path(root)
        p.parent.mkdir(parents=True, exist_ok=True)
        tmp = p.parent / (p.name + ".tmp")
        tmp.write_text(json.dumps({"last_run_ts": ts, "cadence_hours": cadence_hours}))
        os.replace(str(tmp), str(p))
    except Exception:
        pass


def gc_dead_markers():
    """Prune managed markers + their watermarks UNDER THIS REPO whose `jsonl_path` no longer
    exists (the transcript aged out at cleanupPeriodDays) — so the harvest never iterates
    hundreds of dead sessions. Leak-safe (only this plugin's repo). Best-effort."""
    root = repo_root()
    if root is None:
        return
    try:
        for mf in (harness_dir(root) / "managed").glob("*.json"):
            try:
                jp = json.loads(mf.read_text()).get("jsonl_path")
                if jp and not Path(jp).exists():
                    mf.unlink()
                    wf = watermark_path(root, mf.stem)
                    if wf.exists():
                        wf.unlink()
            except Exception:
                continue
    except Exception:
        pass


def any_managed_marker_in_workspace(sid):
    """Self-abort guard (review MAJOR-1): True iff ANY workspace child repo holds a managed
    marker for `sid`. GENERIC existence scan — no private name in source (the private repo is
    DISCOVERED by iterating, never hardcoded). FAIL-CLOSED: if the workspace can't be resolved
    -> True (the harvest must NOT run when it cannot prove it is outside a /goal session)."""
    ws = find_workspace()
    if ws is None:
        return True
    try:
        for child in Path(ws).iterdir():
            if (
                child.is_dir()
                and (
                    child / ".claude" / "dev-harness" / "managed" / (sid + ".json")
                ).exists()
            ):
                return True
    except Exception:
        return True  # fail-closed on any scan error
    return False
