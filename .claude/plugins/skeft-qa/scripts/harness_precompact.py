#!/usr/bin/env python3
"""PreCompact hook — DURABLE-CHANNEL STAGING ONLY (Live-Anchor redesign Move 3; spec
docs/dev-loops/LIVE_ANCHOR_REDESIGN_SPEC.md §E).

Capability-bounded (verified via claude-code-guide, finding 1.6): a PreCompact hook has a ~60s
timeout, CANNOT reliably inject context / steer the compaction summary, and CANNOT safely
fire-and-forget a long child. So this hook does ONLY fast, synchronous, deterministic work — it
*stages* artifacts that survive compaction as FILES (principle 7: align to autocompact, never own
it; we never push content through post-compact context). Post-compact, the agent recomputes the
anchor from these artifacts (repo_state_probe.py).

Two jobs (both fast, well inside the timeout):
  1. Write the gitignored pre-loss SNAPSHOT artifact (.claude/dev-harness/snapshot_<goal_id>.json):
     the last substantive assistant message (the next-brick the summary may drop, finding :34141867)
     + HEAD + a transcript high-water-mark.
  2. (Lean goals only) STAGE the boundary atlas regen by writing a gitignored regen_requested.flag.
     The hook does NOT run `lake build` (1.6: unsafe from a hook); the agent's FIRST_ACTION executes
     the regen post-compact via its own backgrounded Bash (ENFILE-single-flighted), writing the
     gitignored atlas_view.boundary.json (NOT the tracked lean/atlas_view.json — BLOCKER 1.2/QI).

MARKER-GATED + mode-gated + FAIL-OPEN: inert for any non-managed session (no marker) and for a
subagent; emits NOTHING to context; any error is swallowed. Default-inert by construction.
"""
import json
import os
import subprocess
import sys
import time
from pathlib import Path

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from harness_common import read_event, read_marker, repo_root, harness_dir

# Tail window: read only the last slice of the (large, ~100MB) transcript — fast + bounded.
_TAIL_BYTES = 512 * 1024
_MSG_CAP = 6000  # cap the stored last_message so the snapshot stays small


def _git_head(root):
    try:
        o = subprocess.run(["git", "-C", str(root), "rev-parse", "--short=8", "HEAD"],
                           capture_output=True, text=True, timeout=5)
        return o.stdout.strip() if o.returncode == 0 else ""
    except Exception:
        return ""


def _last_assistant_text(transcript_path):
    """Tail-read the transcript and return (text, hwm) for the last substantive assistant message.
    Bounded read (only the last _TAIL_BYTES) so it is fast even on a 100MB transcript. Fail-soft
    -> ('', size)."""
    try:
        sz = os.path.getsize(transcript_path)
    except Exception:
        return "", 0
    try:
        with open(transcript_path, "rb") as f:
            start = max(0, sz - _TAIL_BYTES)
            f.seek(start)
            data = f.read()
        # drop a partial first line if we seeked into the middle
        if start > 0:
            nl = data.find(b"\n")
            data = data[nl + 1:] if nl != -1 else b""
        best = ""
        for line in data.splitlines():
            try:
                obj = json.loads(line)
            except Exception:
                continue
            if obj.get("type") != "assistant":
                continue
            msg = obj.get("message") or {}
            content = msg.get("content")
            txt = ""
            if isinstance(content, list):
                txt = "".join(
                    b.get("text", "") for b in content
                    if isinstance(b, dict) and b.get("type") == "text"
                )
            elif isinstance(content, str):
                txt = content
            txt = txt.strip()
            if len(txt) > 40:  # substantive (skip terse tool-call-only turns)
                best = txt  # keep walking → the LAST substantive one wins
        return best[:_MSG_CAP], sz
    except Exception:
        return "", sz


def main():
    ev = read_event()
    m = read_marker(ev)  # marker-gated + subagent-gated (returns None → inert)
    if not m:
        return 0
    root = repo_root(ev.get("cwd"))
    if root is None:
        return 0
    gid = m.get("goal_id")
    if not gid:
        return 0
    hd = harness_dir(root)
    try:
        hd.mkdir(parents=True, exist_ok=True)
    except Exception:
        return 0

    head = _git_head(root)
    transcript = ev.get("transcript_path") or m.get("jsonl_path") or ""
    msg, hwm = _last_assistant_text(transcript) if transcript else ("", 0)

    # Job 1: snapshot artifact (mode-agnostic — useful for ANY goal).
    try:
        snap = {"ts": time.time(), "transcript_hwm": hwm, "head_sha": head, "last_message": msg}
        tmp = hd / f"snapshot_{gid}.json.tmp"
        tmp.write_text(json.dumps(snap, indent=2))
        os.replace(str(tmp), str(hd / f"snapshot_{gid}.json"))
    except Exception:
        pass

    # Job 2: stage the boundary atlas regen — LEAN goals only (principle 8). The agent executes it.
    if (m.get("mode") or "general").strip().lower() == "lean":
        try:
            (hd / "regen_requested.flag").write_text(
                json.dumps({"ts": time.time(), "head_sha": head, "goal_id": gid})
            )
        except Exception:
            pass

    # NO context injection (1.6 / principle 7): emit nothing.
    return 0


if __name__ == "__main__":
    sys.exit(main())
