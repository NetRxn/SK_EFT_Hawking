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
from pathlib import Path

# This plugin copy's OWN repo dir name. A sibling deployment ships its own copy + name.
REPO_DIR_NAME = "SK_EFT_Hawking"


def _git_root(start):
    try:
        out = subprocess.run(
            ["git", "-C", str(start), "rev-parse", "--show-toplevel"],
            capture_output=True, text=True,
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
            if (d / ".mcp.json").is_file() and (d / REPO_DIR_NAME).is_dir() \
                    and not (d / ".git").exists():
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
        print(json.dumps({"hookSpecificOutput": {
            "hookEventName": event_name, "additionalContext": text}}))
    except Exception:
        pass


# Hard payload budget (review C1): hook `additionalContext` over the 10k cap is REPLACED
# by a file-path preview (hooks.md:704) — which recreates the exact "model sees a pointer,
# not the content" failure the durability fix exists to prevent. So the assembled payload
# MUST stay under this budget; the /goal condition + first-turn self-check are always kept
# in full, and the active-System-2-issues section is the only truncatable part.
PAYLOAD_MAX_CHARS = 9000          # hard cap (< the 10k additionalContext limit, hooks.md:704)
ACTIVE_ISSUES_MAX = 8             # at most the top-N findings, dropped further until under cap


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

# Headroom reserved for the first-turn self-check directive the SessionStart composer
# appends to this payload (harness_reinject._SELF_CHECK). The PreToolUse guard does NOT
# append it, so reserving it here keeps BOTH callers under the 9000-char cap (C1).
_SELF_CHECK_RESERVE = 400


def build_reorientation_payload(marker, repo_root):
    """Contract B — the SHARED re-orientation payload, single source of the string.
    Used by BOTH the SessionStart re-inject (harness_reinject.py) and the
    PreToolUse(AskUserQuestion) guard (harness_question_guard.py). Assembled from:
      * the settled /goal condition (marker['goal'] — the FAST-READ copy; the durable,
        crash-recoverable source is the tracked goal_prompt_<goal_id>.md, spec A.5/A.8),
      * 're-read CLAUDE.md',
      * the active System-2 issues view (omitted gracefully if absent),
      * a short decision-heuristics summary.
    `marker` is the managed marker dict; `repo_root` is this plugin's resolved repo
    (may be None -> active-issues section omitted). Fail-soft on any error.

    HARD BUDGET (review C1): the assembled payload MUST stay < PAYLOAD_MAX_CHARS (9000),
    because hook additionalContext over the 10k cap is replaced by a file-path preview
    (hooks.md:704) — defeating the durability fix. The /goal condition (marker['goal'])
    AND the first-turn self-check directive are ALWAYS included in full; only the
    active-System-2-issues section is truncatable — include at most ACTIVE_ISSUES_MAX (8)
    findings (sorted by tier then tally, in _read_active_issues), dropping more until the
    total fits. The SessionStart composer appends the self-check, so to keep this function
    self-bounded we reserve that headroom here via _SELF_CHECK_RESERVE."""
    if not isinstance(marker, dict):
        marker = {}
    goal = marker.get("goal", "")
    head = []
    if goal:
        head.append("SETTLED GOAL (the /goal condition):\n" + goal)
    head.append("Re-read CLAUDE.md (the giant-ref pointer that should be re-read).")
    head.append(
        "For in-loop Lean development or worktree fan-out, invoke /skeft-qa:goal-dev — it carries "
        "the MCP-first proof loop, kernel-purity rules, /reset-slot, and a symptom-indexed friction "
        "catalog (the dev references that used to be stranded in goal-prompt)."
    )
    tail = [DECISION_HEURISTICS]
    # Budget the truncatable middle: try the full top-N, then drop findings until the
    # whole payload (incl. the self-check headroom the composer later appends) fits.
    n = ACTIVE_ISSUES_MAX
    while True:
        issues = _read_active_issues(repo_root, n) if n > 0 else ""
        parts = list(head)
        if issues:
            parts.append("Active System-2 issues (current open/recurring drift findings):\n" + issues)
        parts += tail
        payload = "\n\n".join(parts)
        if len(payload) + _SELF_CHECK_RESERVE < PAYLOAD_MAX_CHARS or n <= 0:
            return payload
        n -= 1


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
        return int(json.loads(watermark_path(root, sid).read_text()).get("byte_offset", 0))
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
            if child.is_dir() and (child / ".claude" / "dev-harness" / "managed"
                                   / (sid + ".json")).exists():
                return True
    except Exception:
        return True   # fail-closed on any scan error
    return False
