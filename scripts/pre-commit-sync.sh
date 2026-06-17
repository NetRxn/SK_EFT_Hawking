#!/usr/bin/env bash
# L2 mechanical-sync commit gate (public-safe). Chained AFTER the leak-guard by the
# canonical installer. FAIL-OPEN by design: a missing toolchain or a transient crash
# NEVER blocks a commit. Auto-fixes cheap staleness; INCREMENTAL lean guard (never
# the 30-min clean ExtractDeps — that's /skeft-qa:sync); HARD-BLOCKS only genuine
# SOUNDNESS breakage, and only on `main`.
set -uo pipefail
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
  if grep -RnE '^[[:space:]]*sorry' lean/SKEFTHawking >/dev/null 2>&1; then
    echo "ERROR: new 'sorry' in lean/SKEFTHawking (genuine breakage)."
    [ "$BRANCH" = "main" ] && exit 1 || echo "(off-main: warn only)"
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
exit 0
