#!/usr/bin/env bash
# Pre-commit hook: verify all notebooks execute without errors.
#
# Install:
#   ln -sf ../../scripts/pre-commit-notebooks.sh .git/hooks/pre-commit
#
# Or add to your .pre-commit-config.yaml / settings.local.json hooks.
#
# This runs ONLY if any .ipynb file is staged. Skips quickly otherwise.

set -euo pipefail

REPO_ROOT="$(cd "$(dirname "$0")/.." && pwd)"
cd "$REPO_ROOT"

# Check if any notebooks are staged
STAGED_NBS=$(git diff --cached --name-only --diff-filter=ACM -- '*.ipynb' 2>/dev/null || true)

if [ -z "$STAGED_NBS" ]; then
    exit 0
fi

echo "Pre-commit: executing staged notebooks..."

FAILED=0
for nb in $STAGED_NBS; do
    if [ ! -f "$nb" ]; then
        continue
    fi
    echo -n "  $nb ... "
    if uv run jupyter nbconvert --to notebook --execute "$nb" \
        --output /tmp/pre-commit-nb-check.ipynb \
        --ExecutePreprocessor.timeout=120 \
        >/dev/null 2>&1; then
        echo "OK"
    else
        echo "FAILED"
        FAILED=1
        # Show the error
        uv run jupyter nbconvert --to notebook --execute "$nb" \
            --output /tmp/pre-commit-nb-check.ipynb \
            --ExecutePreprocessor.timeout=120 2>&1 | tail -20
    fi
done

if [ "$FAILED" -ne 0 ]; then
    echo ""
    echo "ERROR: One or more notebooks failed to execute."
    echo "Fix the errors before committing."
    exit 1
fi

echo "All staged notebooks execute successfully."
