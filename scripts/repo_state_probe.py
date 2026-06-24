#!/usr/bin/env python3
"""Live repo-state probe — the LIVE ANCHOR for an autonomous /goal loop (Move 1 of the
Live-Anchor redesign; spec docs/dev-loops/LIVE_ANCHOR_REDESIGN_SPEC.md).

WHY: the post-compaction loop kept re-deriving committed engines, re-opening settled forks, and
trusting a drifted prose FRONTIER (System-2 finding `compaction-summary-quality`, tally 23). The
fix is to RECOMPUTE positive structural state live from durable sources (git + the derived atlas)
rather than remember it in prose. This script is RUN BY THE AGENT as a FIRST_ACTION, so its output
lands in the agent's own context at full fidelity — unbounded, never truncated, zero re-injection
payload cost (progressive disclosure, like the mandated PRE_DECISIONS.md read).

It is the POSITIVE half of the split; the NEGATIVE half (settled forks / route bans) lives in
docs/dev-loops/SETTLED_FORKS.md (a separate mandated read). The authoritative LIVE per-file sorry
is the agent's own `lean_diagnostic_messages` MCP call (comment-proof, LSP-backed) — this script
cannot reach the LSP, so it prints that as the explicit next step (§A.5) and surfaces the
batch-but-closure-true CONDITIONALLY_PROVED set from the atlas as the broad map.

Stdlib only; git + json; never imports src.core (no numpy). FAIL-OPEN throughout: any section that
cannot be computed prints `(... unavailable)` and the rest proceeds; the script never blocks the
loop. Local-only — output is injected into the running agent, never egressed.
"""
from __future__ import annotations

import argparse
import json
import os
import subprocess
import sys
from pathlib import Path

# Active-module heuristic: the lean files most recently/frequently touched since the anchor.
_LEAN_GLOB = "lean/SKEFTHawking"
_TOP_ACTIVE = 3
_LASTN = 40  # rung-3 fallback: most-recent lean commits when no since-anchor resolves


def _run(args, cwd):
    """Run a git command; return stdout (stripped) or None on any failure (fail-open)."""
    try:
        out = subprocess.run(args, cwd=str(cwd), capture_output=True, text=True, timeout=20)
        if out.returncode == 0:
            return out.stdout.rstrip("\n")
    except Exception:
        pass
    return None


def default_repo():
    """Resolve the repo root LAUNCH-INDEPENDENTLY by anchoring on this script's own location
    (<repo>/scripts/repo_state_probe.py → parent.parent == <repo>), the same pattern as
    atlas_view.py. This is critical: a /goal is often launched from the WORKSPACE PARENT, which is
    intentionally NOT a git repo, so a cwd-based `git rev-parse --show-toplevel` FAILS there. The
    __file__ anchor resolves to SK_EFT_Hawking from the parent, the repo, or any subdir alike;
    git subcommands then run with cwd=repo so they operate on the right tree regardless of cwd.
    Fallback to a cwd git-toplevel only if the anchor is implausible (script copied out of repo)."""
    anchor = Path(__file__).resolve().parent.parent
    if (anchor / "scripts").is_dir() and ((anchor / "lean").is_dir() or (anchor / ".git").exists()):
        return anchor
    r = _run(["git", "rev-parse", "--show-toplevel"], os.getcwd())
    return Path(r) if r else anchor


def _sha_resolvable(repo, sha):
    """True iff `sha` names an object that still exists (a rebase/force-push can GC it)."""
    if not sha:
        return False
    return _run(["git", "rev-parse", "--verify", "--quiet", f"{sha}^{{commit}}"], repo) is not None


def resolve_marker(repo, session_id, goal_id, override):
    """Resolve THIS session's marker (never iterate-all unless exactly one exists). Returns the
    marker dict (possibly synthesized from overrides) + a source label."""
    if override:  # tests / explicit
        return override, "override"
    mgr = repo / ".claude" / "dev-harness" / "managed"
    # Prefer the exact session marker.
    if session_id:
        p = mgr / f"{session_id}.json"
        try:
            return json.loads(p.read_text()), f"marker {session_id[:8]}"
        except Exception:
            pass
    # Else by goal_id across markers (still THIS session's goal, not all goals' work).
    try:
        cands = []
        for mf in mgr.glob("*.json"):
            try:
                m = json.loads(mf.read_text())
            except Exception:
                continue
            if goal_id and m.get("goal_id") == goal_id:
                return m, f"marker (goal {goal_id})"
            cands.append(m)
        if len(cands) == 1:  # unambiguous single managed goal
            return cands[0], "marker (sole)"
    except Exception:
        pass
    return {}, "no-marker"


def resolve_anchor(repo, marker):
    """The degrade cascade (§A.2a). Returns (mode, value, label) where mode ∈
    {sha, since, lastn} and value feeds the git-log range/filter."""
    arm = marker.get("arm_sha")
    if arm and _sha_resolvable(repo, arm):
        return "sha", arm, f"arm_sha {arm[:8]} (exact)"
    # rung 2: timestamp — explicit armed_ts, else parse the goal_id datetime stamp.
    ts = marker.get("armed_ts")
    gid = marker.get("goal_id") or ""
    since = None
    if ts:
        # git's approxidate does NOT parse a bare integer as an epoch (it returns ALL history) —
        # use the `@<epoch>` form so the delta stays bounded to the session (finding M1).
        try:
            since = "@%d" % int(float(ts))
        except Exception:
            since = str(ts)
    elif len(gid) >= 15 and gid[8] == "T":
        # goal_id = YYYYMMDDTHHMMSS
        since = f"{gid[0:4]}-{gid[4:6]}-{gid[6:8]} {gid[9:11]}:{gid[11:13]}:{gid[13:15]}"
    if since:
        why = "no arm_sha" if not arm else "arm_sha GC'd/unresolvable"
        return "since", since, f"timestamp {since} ({why} — approximate)"
    # rung 3
    return "lastn", _LASTN, f"last {_LASTN} commits (no since-anchor)"


def git_delta(repo, anchor_mode, value, lean):
    """The commit delta for the resolved anchor rung. In LEAN mode the delta + active-file scan are
    scoped to `lean/`; in GENERAL mode they are repo-wide (principle 8). Returns (lines, files)."""
    base = ["git", "log", "--oneline"]
    pathspec = ["--", "lean/"] if lean else []
    if anchor_mode == "sha":
        rng = [f"{value}..HEAD"]
    elif anchor_mode == "since":
        rng = [f"--since={value}"]
    else:
        rng = [f"-n{value}"]
    oneline = _run(base + rng + pathspec, repo)
    # name-only (for active-file detection): lean -> lean/ glob + .lean filter; general -> all files.
    no_path = ["--", _LEAN_GLOB] if lean else []
    no = _run(["git", "log", "--name-only", "--pretty=format:"] + rng + no_path, repo)
    raw = [f for f in (no or "").splitlines() if f.strip()]
    files = [f for f in raw if f.endswith(".lean")] if lean else raw
    return (oneline or ""), files


def active_files(touched_files, hint, lean):
    """Top-N most-frequently-touched files + the marker hint (tie-breaker). In LEAN mode the hint
    must be a .lean path; in GENERAL mode any file."""
    from collections import Counter
    c = Counter(touched_files)
    ranked = [f for f, _ in c.most_common()]
    out = []
    if hint and (hint.endswith(".lean") or not lean):
        out.append(hint)
    for f in ranked:
        if f not in out:
            out.append(f)
        if len([x for x in out if x]) >= _TOP_ACTIVE:
            break
    return [x for x in out if x][:_TOP_ACTIVE]


def load_atlas(repo):
    """Prefer the gitignored boundary atlas when fresher than the tracked one (BLOCKER 1.2)."""
    tracked = repo / "lean" / "atlas_view.json"
    boundary = repo / ".claude" / "dev-harness" / "atlas_view.boundary.json"
    chosen, label = None, None
    try:
        t_m = tracked.stat().st_mtime if tracked.exists() else -1
        b_m = boundary.stat().st_mtime if boundary.exists() else -1
        if b_m > t_m:
            chosen, label = boundary, "boundary (gitignored)"
        elif t_m >= 0:
            chosen, label = tracked, "tracked"
    except Exception:
        pass
    if not chosen:
        return None, None, None
    try:
        import datetime
        data = json.loads(chosen.read_text())
        mtime = datetime.datetime.fromtimestamp(chosen.stat().st_mtime).strftime("%Y-%m-%d %H:%M")
        return data, label, mtime
    except Exception:
        return None, None, None


def module_inventory(atlas, modules):
    """Scan atlas['nodes'] (no per-module index — explicit O(nodes) scan, §A.4/1.3) for the active
    modules. Returns {module: [(fqn, status, kernel_pure)]} + the project-wide CONDITIONALLY_PROVED
    module set (§A.5)."""
    inv = {m: [] for m in modules}
    cond_modules = set()

    # Map each active file PATH to its FULL dotted module and match the atlas node's full
    # `module` (NOT the tail — finding M2: tails like `Basic`/`Predicates` collide across
    # namespaces, e.g. SKEFTHawking.Basic vs SKEFTHawking.SymTFT.Basic).
    def to_dotted(path):
        p = path
        if p.startswith("lean/"):
            p = p[len("lean/"):]
        if p.endswith(".lean"):
            p = p[:-5]
        return p.replace("/", ".")

    dotted = {to_dotted(m): m for m in modules}
    for n in atlas.get("nodes", []):
        nmod = n.get("module") or ""
        status = n.get("atlas_status")
        if status == "CONDITIONALLY_PROVED" and nmod:
            cond_modules.add(nmod)
        if nmod in dotted:  # full-module equality
            inv[dotted[nmod]].append((n.get("fqn", "?"), status, bool(n.get("kernel_pure"))))
    return inv, cond_modules


def load_snapshot(repo, goal_id):
    """The PreCompact pre-loss snapshot artifact (§A.6), if present."""
    if not goal_id:
        return None
    try:
        p = repo / ".claude" / "dev-harness" / f"snapshot_{goal_id}.json"
        return json.loads(p.read_text())
    except Exception:
        return None


def atlas_keystone(atlas):
    """The most-gating OPEN HYPOTHESIS (atlas['frontier'][0]) — distinct from CONDITIONALLY_PROVED
    theorem nodes (MAJOR 1.4). A pointer, not the inventory."""
    fr = (atlas or {}).get("frontier") or []
    return fr[0] if fr else None


def build_report(repo, session_id, goal_id, override, mode_override=None):
    L = []
    p = L.append
    marker, msrc = resolve_marker(repo, session_id, goal_id, override)
    if mode_override:  # explicit --mode wins over the marker (tests / ad-hoc)
        marker = {**marker, "mode": mode_override}
    gid = marker.get("goal_id") or goal_id
    domain = (marker.get("mode") or "general").strip().lower()
    if domain not in ("lean", "general"):
        domain = "general"  # principle 8: unknown ⇒ general (never assume Lean)
    lean = domain == "lean"
    head = _run(["git", "rev-parse", "--short=8", "HEAD"], repo) or "?"
    head_subj = _run(["git", "log", "-1", "--pretty=%s"], repo) or ""

    p("=== LIVE REPO-STATE ANCHOR (recomputed now — supersedes any narrated frontier/summary) ===")
    p(f"resolved via: {msrc}" + (f"; goal_id={gid}" if gid else "") + f"; mode={domain}")
    p(f"HEAD={head}  ({head_subj})")

    # 1-2: anchor + delta (mode-scoped)
    anchor_mode, value, alabel = resolve_anchor(repo, marker)
    p(f"armed-at: {alabel}")
    oneline, touched = git_delta(repo, anchor_mode, value, lean)
    mods = active_files(touched, marker.get("active_hint"), lean)
    scope = "commits to lean/" if lean else "repo-wide commits"
    p("")
    p(f"--- repo delta since arm ({scope}; SUPERSET — may include parallel-session,")
    p("    manual, or other-goal work; reconcile, do NOT assume authorship) ---")
    p(oneline if oneline.strip() else "(none / git unavailable)")
    p("")
    p(f"likely active file(s) (most-touched since anchor): {', '.join(mods) or '(none)'}")

    # 3: working tree (mode-agnostic — all goals benefit; lean filter only narrows the noise)
    status = _run(["git", "status", "--porcelain"], repo)
    lines = [ln for ln in (status or "").splitlines() if ln.strip()]
    dirty = [ln for ln in lines if ln.strip().endswith(".lean")] if lean else lines
    p("")
    p(f"--- working tree (uncommitted/untracked{' .lean' if lean else ''} — reconcile against the summary FIRST) ---")
    p("\n".join(dirty) if dirty else "(clean)")

    # 4-5: atlas inventory + open-sorry map — LEAN-ONLY (principle 8)
    if lean:
        atlas, albl, amtime = load_atlas(repo)
        p("")
        if atlas is None:
            p("--- active-module engine inventory: (atlas unavailable — run extraction:")
            p("    rm -rf lean/.lake/build && lake build SKEFTHawking.ExtractDeps; python scripts/atlas_view.py --write) ---")
        else:
            p(f"--- active-module engine inventory  [atlas: {albl}, as of {amtime}] ---")
            inv, cond_modules = module_inventory(atlas, mods)
            for m in mods:
                rows = inv.get(m, [])
                if not rows:
                    p(f"  {m}: (no theorem nodes — module new/unextracted)")
                    continue
                kp = sum(1 for _, s, k in rows if s == "PROVED" and k)
                cp = [f for f, s, _ in rows if s == "CONDITIONALLY_PROVED"]
                ax = [f for f, s, _ in rows if s == "AXIOM_TAINTED"]
                p(f"  {m}: {len(rows)} thm, {kp} PROVED·kernel-pure"
                  + (f", {len(cp)} CONDITIONALLY_PROVED(sorry)" if cp else "")
                  + (f", {len(ax)} AXIOM_TAINTED" if ax else ""))
                for f in cp:
                    p(f"      sorry-bearing: {f}")
                for f in ax:
                    p(f"      axiom-tainted: {f}")
            p("")
            p(f"  project-wide open-sorry modules (atlas CONDITIONALLY_PROVED): {len(cond_modules)}")
            ks = atlas_keystone(atlas)
            if ks:
                p(f"  atlas frontier KEYSTONE (most-gating OPEN hypothesis): {ks.get('id')}"
                  f"  gates {ks.get('frontier_impact')}")

    # 6: pre-loss snapshot
    snap = load_snapshot(repo, gid)
    p("")
    if snap:
        p(f"--- pre-loss snapshot (PreCompact-captured; ts {snap.get('ts')}, hwm {snap.get('transcript_hwm')}) ---")
        p("last substantive message before the boundary (the next-brick the summary may have dropped):")
        p(str(snap.get("last_message", "")).strip()[:4000])
    else:
        p("--- pre-loss snapshot: (none for this goal) ---")

    # 7: next step + pointers (programmatic sorry is the agent's LSP call, not grep)
    p("")
    p("--- NEXT (do these now) ---")
    if lean:
        p("  * LIVE sorry (authoritative, comment-proof): run `lean_diagnostic_messages` on the active")
        p("    file via the lean-lsp MCP — the atlas CONDITIONALLY_PROVED set above is the batch map.")
    sf = repo / "docs" / "dev-loops" / "SETTLED_FORKS.md"
    if sf.exists():
        try:
            n = sum(1 for ln in sf.read_text().splitlines() if ln.startswith("## "))
        except Exception:
            n = "?"
        p(f"  * SETTLED_FORKS.md: {n} settled fork(s) — grep BEFORE any 'impossible/needs-banned' reasoning.")
    p("  * PRE_DECISIONS.md: the standing pre-decisions (mandatory read).")
    if lean:
        flag = repo / ".claude" / "dev-harness" / "regen_requested.flag"
        if flag.exists():
            p("  * regen_requested.flag present (PreCompact staged a boundary atlas refresh). If Lean")
            p("    slots are idle, run this EXACT command in the BACKGROUND (Bash run_in_background) — it")
            p("    is single-flighted (mkdir-lock; flock is absent on macOS), concurrency-gated, writes")
            p("    ONLY the gitignored boundary atlas, and self-clears the flag:")
            p("      sh -c 'd=.claude/dev-harness/regen.lock; mkdir \"$d\" 2>/dev/null || exit 0; "
              "trap \"rmdir \\\"$d\\\"\" EXIT; [ \"$(pgrep -fc \"lake|lean-lsp-mcp\")\" -lt 3 ] || exit 0; "
              "lake build SKEFTHawking.ExtractDeps && uv run python scripts/atlas_view.py "
              "--write-boundary && rm -f .claude/dev-harness/regen_requested.flag'")
    return "\n".join(L)


def main(argv=None):
    ap = argparse.ArgumentParser(description="Live repo-state anchor for a /goal loop.")
    ap.add_argument("--session-id", default=os.environ.get("CLAUDE_SESSION_ID", ""))
    ap.add_argument("--goal-id", default="")
    ap.add_argument("--arm-sha", default="")
    ap.add_argument("--mode", default="", choices=["", "lean", "general"])
    ap.add_argument("--repo", default="")
    a = ap.parse_args(argv)
    repo = Path(a.repo) if a.repo else default_repo()
    if repo is None or not repo.exists():
        print("(repo_state_probe: cannot resolve repo — no anchor)")
        return 0
    override = None
    if a.goal_id or a.arm_sha:
        override = {"goal_id": a.goal_id, "arm_sha": a.arm_sha}
    try:
        print(build_report(repo, a.session_id, a.goal_id, override, a.mode or None))
    except Exception as e:  # fail-open: never block the loop
        print(f"(repo_state_probe degraded: {e}; HEAD="
              f"{_run(['git', 'rev-parse', '--short=8', 'HEAD'], repo) or '?'})")
    return 0


if __name__ == "__main__":
    sys.exit(main())
