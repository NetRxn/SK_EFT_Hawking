#!/usr/bin/env bash
# L2 mechanical-sync commit gate (public-safe). Chained AFTER the leak-guard by the
# canonical installer. FAIL-OPEN by design: a missing toolchain or a transient crash
# NEVER blocks a commit. Auto-fixes cheap staleness; INCREMENTAL lean guard (never
# the 30-min clean ExtractDeps — that's /skeft-qa:sync); HARD-BLOCKS only genuine
# SOUNDNESS breakage, and only on `main`.
set -uo pipefail

# (−1) Worktree-safety (review BLOCKER). This is a MAIN-oriented gate (auto-restage +
#      sync.py + incremental lake build). It must NOT run for a commit made in a *linked
#      worktree* (e.g. a lean-worker slot under .claude/worktrees/): the shared hook would
#      `cd` to the wrong tree, run heavy uv/lake against the slot, and — worst — stitch a
#      cloned dependency's files into the slot's commit index (the top-level `.github/*`
#      Physlib-blob phantom → "error: invalid object … Error building trees"). The pure-bash
#      leak-guard is chained BEFORE this and already ran on the slot's staged diff, so leaks
#      are still caught. The lead re-runs the full gate on the authoritative `main` commit
#      after merging the worker's branch. Detect a worktree by the per-commit --git-dir (= env
#      GIT_DIR = .git/worktrees/<name>) differing from --git-common-dir (= .git) — env-resolved, so
#      it is robust to the shared hook having already `cd`'d to the main checkout (which makes the
#      cwd-based --show-toplevel useless here).
_gd="$(git rev-parse --path-format=absolute --git-dir 2>/dev/null || true)"
_gcd="$(git rev-parse --path-format=absolute --git-common-dir 2>/dev/null || true)"
if [ -n "$_gd" ] && [ -n "$_gcd" ] && [ "$_gd" != "$_gcd" ]; then
  echo "(skeft-sync: worktree commit — leak-guard ran; skipping the main-oriented sync gate (lead re-syncs on merge))"
  exit 0
fi

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"; cd "$REPO_ROOT"
BRANCH="$(git rev-parse --abbrev-ref HEAD 2>/dev/null || echo HEAD)"

# (0) Toolchain-resolution guard (review BLOCKER). Git hooks run in a minimal env
#     (GUI clients / non-login shells) where uv/lake are NOT on PATH. Resolve them;
#     if still missing, SKIP the gate (exit 0) — never block a commit on a missing
#     interpreter. (The pure-bash leak-guard already ran, before this.)
command -v uv >/dev/null 2>&1 || { [ -f "$HOME/.local/bin/env" ] && . "$HOME/.local/bin/env" 2>/dev/null; export PATH="$HOME/.local/bin:$HOME/.elan/bin:$PATH"; }
command -v uv >/dev/null 2>&1 || { echo "(skeft-sync: uv not on PATH — skipping mechanical gate)"; exit 0; }

run_check() {  # PASS (rc0) / FAIL (rc1 = real failure) / SKIP (other = crash/127 → never blocks)
  uv run python scripts/validate.py --check "$1" >/tmp/skeft-chk.$$ 2>&1
  rc=$?; [ $rc -eq 0 ] && echo PASS || { [ $rc -eq 1 ] && echo FAIL || echo SKIP; }
}

# (a) Auto-fix cheap stale derivations + restage (Q2: never block on a self-fixable fix).
#     NOTE: docs/counts.tex is deliberately NOT restaged here — it regenerates only with the
#     HEAVY counts.json edge (update_counts.py / ExtractDeps), which `--fast` skips; restaging
#     it would stage an un-regenerated file. Only genuinely cheap-derived artifacts are restaged.
#     The cheap regen below is serialized by the regen concurrency lock INSIDE sync.py (spec 12
#     / Task 7), so the gate inherits the lock for free — no shell-side lock is needed here.
uv run python scripts/sync.py --fast >/tmp/skeft-sync.$$ 2>&1 || true
for f in SK_EFT_Hawking_Inventory_Index.md $(git ls-files 'papers/*/tables/*.tex'); do
  [ -f "$f" ] && ! git diff --quiet -- "$f" && git add "$f"
done

# (b) On .lean changes: GENUINE soundness breakage only → hard-block (main only).
if git diff --cached --name-only --diff-filter=ACM | grep -q '\.lean$'; then
  if command -v lake >/dev/null 2>&1; then
    if ! ( cd lean && lake build >/tmp/skeft-lean.$$ 2>&1 ); then   # INCREMENTAL (warm cache), not clean
      echo "ERROR: incremental 'lake build' failed (genuine breakage)."
      [ "$BRANCH" = "main" ] && { tail -20 /tmp/skeft-lean.$$; exit 1; } || echo "(off-main: warn only)"
    fi
  else echo "(skeft-sync: lake not on PATH — skipping lean guard)"; fi
  # Genuine-sorry guard (precise). A naive source grep (`grep -RnE '^\s*sorry'`) matches
  # commented-out `sorry`s, docstring code-fence examples, and `.backup` files — all false
  # positives, none of them compiled (it blocked EVERY commit once such pre-existing lines
  # existed). Instead trust the build we just ran: Lean prints "declaration uses 'sorry'"
  # ONLY for a genuine sorry in a built declaration (and replays it for cached modules), so
  # the captured build log is the precise, false-positive-free signal.
  if [ -f /tmp/skeft-lean.$$ ] && grep -qF "declaration uses 'sorry'" /tmp/skeft-lean.$$; then
    echo "ERROR: genuine 'sorry' in a built lean/SKEFTHawking declaration (lake reported it)."
    [ "$BRANCH" = "main" ] && { grep -nF "declaration uses 'sorry'" /tmp/skeft-lean.$$ | head -10; exit 1; } || echo "(off-main: warn only)"
  fi
  # counts.json is now stale vs .lean — but its regen IS the 30-min ExtractDeps, so do
  # NOT run it here. Staleness is a METRIC, not soundness → WARN even on `main` (review
  # MAJOR); never block a routine .lean commit (that would stall the /goal loop).
  if uv run python -c "import sys;sys.path.insert(0,'scripts');import sync_manifest as m;sys.exit(0 if any('counts.json' in s for s in m.stale_artifacts()) else 1)" 2>/dev/null; then
    echo "(skeft-sync: counts.json stale vs .lean — run /skeft-qa:sync (full) when ready; not blocking)"
  fi
fi

# (c) Fast deterministic SOUNDNESS checks. Hard-block (main only) ONLY on a real FAIL;
#     a SKIP (crash/127) never blocks (review MAJOR — don't wedge the loop on a transient).
for c in formula_grounding placeholder_not_cited native_decide_regression; do
  case "$(run_check "$c")" in
    FAIL) echo "ERROR: validate.py --check $c FAILED (genuine breakage)."
          [ "$BRANCH" = "main" ] && { tail -15 /tmp/skeft-chk.$$; exit 1; } || echo "(off-main: warn only)";;
    SKIP) echo "(skeft-sync: $c could not run — skipping, not blocking)";;
  esac
done

# (d) Lab-notebook health (ADVISORY — never blocks). For each managed /goal marker, warn if its
#     active shard is over the ~25k-token budget, the INDEX lacks a DECISIONS block, or the FRONTIER
#     SHA is stale vs HEAD. Read-only: the agent self-levels via /skeft-qa:notebook (no hook mutates
#     the notebook). Fail-open — a missing tool / unreadable marker is silently skipped.
NB_LIB="$REPO_ROOT/.claude/plugins/skeft-qa/scripts/notebook_lib.py"
if [ -f "$NB_LIB" ] && [ -d "$REPO_ROOT/.claude/dev-harness/managed" ]; then
  for mk in "$REPO_ROOT"/.claude/dev-harness/managed/*.json; do
    [ -f "$mk" ] || continue
    nbp="$(uv run python -c "import json,sys;print(json.load(open(sys.argv[1])).get('notebook_path',''))" "$mk" 2>/dev/null)" || continue
    [ -n "$nbp" ] || continue
    uv run python "$NB_LIB" check "$(dirname "$nbp")" --repo "$REPO_ROOT" 2>/dev/null | grep '⚠' || true
  done
fi
exit 0
