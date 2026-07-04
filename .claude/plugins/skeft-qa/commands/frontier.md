---
description: Surface the derived atlas frontier — the project's OPEN assumptions ranked by how much each gates, AND the NEGATIVE frontier (settled-dead forks to avoid) — so fan-out targets high-leverage provable work and steers clear of kernel-checked dead paths. Read-only.
---

Surface **both fronts** of the atlas — the positive frontier (ADR-005 D-I) for atlas-guided fan-out AND the negative frontier (ADR-007 N-D) so fan-out avoids settled-dead forks. No preamble.

1. Read both ranked frontiers (a derived VIEW over the dependency graph; read-only, never triggers extraction):
   ```bash
   REPO="$(uv run --no-sync python "${CLAUDE_PLUGIN_ROOT}/scripts/harness_common_cli.py" repo-root 2>/dev/null)"
   test -n "$REPO" || REPO="$(git rev-parse --show-toplevel 2>/dev/null || echo UNRESOLVED)"
   uv run --no-sync python "${CLAUDE_PLUGIN_ROOT}/scripts/harness_common_cli.py" atlas-frontier 12
   uv run --no-sync python "${CLAUDE_PLUGIN_ROOT}/scripts/harness_common_cli.py" atlas-antifrontier 8
   ```
   If they print nothing, the atlas view is unbuilt — regenerate with
   `uv run python scripts/atlas_view.py --write` (and `scripts/atlas_heatmap.py --write` for the doc), then retry.

2. Interpret for fan-out (do NOT mutate the atlas — this is a read-only compass):
   - **`*apex`** rows are HEADLINE open targets — the project's flagship goals.
   - **Higher gating impact** ⇒ discharging it unlocks more downstream decls ⇒ better fan-out leverage.
   - **tracks** are separate workstreams (areas); pick **disjoint tracks** to fan out without overlap.
   - Cross-reference the current `/goal` + roadmap: prefer frontier nodes on the path to THIS goal's apex.
   - **NEGATIVE frontier** = kernel-checked settled-dead forks (each with its `false_statement`). Before
     dispatching a brick, check it does not re-enter one of these — a worker with no shared context is the
     highest-risk re-deriver. These are provably-false; do NOT re-attempt them (read `SETTLED_FORKS.md` +
     `KERNEL_NOGO_REGISTRY` for the full reasons). Policy/route bans stay prose-only in `SETTLED_FORKS.md`.

3. Output a tight ranked shortlist (≤ 8 rows: impact · open node · track · what it gates), then name
   the **1–2 highest-leverage provable bricks to dispatch next** (e.g. "assign `hyp:X` to wt2"), and note
   any negative-frontier fork the dispatch must steer clear of. Do not re-plan the whole goal — surface
   the work (both fronts) and stop.
