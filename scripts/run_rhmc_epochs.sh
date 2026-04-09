#!/bin/bash
#
# RHMC Production Runner (Epoch-Based)
# =====================================
#
# THE RECOMMENDED WAY to run RHMC production. Wraps run_rhmc_production.py
# with automatic epoch cycling to prevent thermal throttling and memory
# fragmentation in long runs.
#
# Why epochs?
# -----------
# Long-running Python/Rust processes on laptops degrade 5-8x over hours due to:
#   1. Thermal throttling (macOS reduces CPU clock under sustained load)
#   2. Memory fragmentation (Python heap + Rust allocator bloat)
#   3. OS scheduling pressure (6+ workers compete for CPU time)
#
# The fix: run N short invocations instead of 1 long one. The production
# script's checkpoint/resume handles continuity automatically — each epoch
# picks up exactly where the last one left off, including h-field state.
#
# Usage:
# ------
#   # Standard L=8 production (recommended settings baked in):
#   nohup ./scripts/run_rhmc_epochs.sh --l 8 > data/rhmc/rhmc_l8.log 2>&1 &
#
#   # L=4 scan (faster, for testing):
#   ./scripts/run_rhmc_epochs.sh --l 4 --n-md-steps 20 --workers 6
#
#   # Custom epoch count and cooldown:
#   EPOCHS=10 COOLDOWN=60 ./scripts/run_rhmc_epochs.sh --l 8
#
# Defaults:
# ---------
#   EPOCHS=5, TRAJ_PER_EPOCH=100 → 500 total trajectories per coupling
#   COOLDOWN=30s between epochs (thermal recovery)
#   --n-md-steps 80  (target |dH|<1 for L=8; production script default)
#   --workers 4      (leaves CPU headroom; production script default)
#   --chunk-size 10  (frequent checkpoints; production script default)
#
# For critical-region focused runs:
#   ./scripts/run_rhmc_epochs.sh --l 8 --g-critical-min 3.0 --g-critical-max 5.0
#
# The production script (run_rhmc_production.py) handles:
#   - Checkpoint/resume via per-coupling .npz files
#   - Atomic writes (tmp + rename, Ctrl-C safe)
#   - Automatic detection of completed/partial couplings
#   - h-field state continuity across invocations
#
# Pipeline reference: Phase5d_Roadmap.md Wave 3, Phase5f_Roadmap.md Wave 5-6
# See also: docs/references/production_rhmc.md
#

set -e
cd "$(dirname "$0")/.."  # Always run from SK_EFT_Hawking root

# ── Cleanup: kill workers on ANY exit (signal, error, normal) ──
# The production script writes a PID file; we use it + process group kill
# to ensure no orphaned workers survive if this script is killed.
cleanup() {
    echo ""
    echo "--- Cleaning up worker processes ---"
    # Kill the Python production script's entire process group
    if [ -n "$PROD_PID" ] && kill -0 "$PROD_PID" 2>/dev/null; then
        # Send TERM to the process group (negative PID = group)
        kill -- -"$PROD_PID" 2>/dev/null || kill "$PROD_PID" 2>/dev/null
        wait "$PROD_PID" 2>/dev/null
    fi
    # Belt and suspenders: kill any remaining workers via PID file
    for pidfile in data/rhmc/L*/.rhmc.pid; do
        if [ -f "$pidfile" ]; then
            pid=$(cat "$pidfile")
            if kill -0 "$pid" 2>/dev/null; then
                kill -- -"$pid" 2>/dev/null || kill "$pid" 2>/dev/null
            fi
            rm -f "$pidfile"
        fi
    done
    echo "--- Cleanup complete ---"
}
trap cleanup EXIT INT TERM

# Epoch configuration (override via environment variables)
EPOCHS="${EPOCHS:-5}"
TRAJ_PER_EPOCH="${TRAJ_PER_EPOCH:-100}"
COOLDOWN="${COOLDOWN:-30}"

echo "========================================================================"
echo "RHMC Epoch Runner"
echo "  Epochs: $EPOCHS x $TRAJ_PER_EPOCH traj = $((EPOCHS * TRAJ_PER_EPOCH)) total"
echo "  Cooldown: ${COOLDOWN}s between epochs (thermal recovery)"
echo "  Production args: $@"
echo "  Started: $(date)"
echo "========================================================================"

for epoch in $(seq 1 $EPOCHS); do
    echo ""
    echo "=== Epoch $epoch/$EPOCHS — $(date) ==="
    echo ""

    uv run python scripts/run_rhmc_production.py \
        --n-traj $TRAJ_PER_EPOCH \
        "$@" &
    PROD_PID=$!
    wait "$PROD_PID"
    EXIT_CODE=$?
    PROD_PID=""

    if [ $EXIT_CODE -ne 0 ]; then
        echo "ERROR: Epoch $epoch failed with exit code $EXIT_CODE"
        exit $EXIT_CODE
    fi

    if [ $epoch -lt $EPOCHS ]; then
        echo ""
        echo "--- Cooldown: ${COOLDOWN}s (thermal + memory recovery) ---"
        sleep $COOLDOWN
    fi
done

echo ""
echo "========================================================================"
echo "All $EPOCHS epochs complete — $(date)"
echo "========================================================================"
