---
description: Surface the derived atlas frontier — the project's OPEN assumptions ranked by how much each gates — so fan-out targets high-leverage provable work instead of being roadmap-opaque. Read-only.
---

Surface the **atlas frontier** (ADR-005 D-I) for atlas-guided fan-out. No preamble.

1. Read the ranked frontier (a derived VIEW over the dependency graph; read-only, never triggers extraction):
   ```bash
   REPO="$(uv run --no-sync python "${CLAUDE_PLUGIN_ROOT}/scripts/harness_common_cli.py" repo-root 2>/dev/null)"
   test -n "$REPO" || REPO="$(git rev-parse --show-toplevel 2>/dev/null || echo UNRESOLVED)"
   uv run --no-sync python "${CLAUDE_PLUGIN_ROOT}/scripts/harness_common_cli.py" atlas-frontier 12
   ```
   If it prints nothing, the atlas view is unbuilt — regenerate with
   `uv run python scripts/atlas_view.py --write` (and `scripts/atlas_heatmap.py --write` for the doc), then retry.

2. Interpret for fan-out (do NOT mutate the atlas — this is a read-only compass):
   - **`*apex`** rows are HEADLINE open targets — the project's flagship goals.
   - **Higher gating impact** ⇒ discharging it unlocks more downstream decls ⇒ better fan-out leverage.
   - **tracks** are separate workstreams (areas); pick **disjoint tracks** to fan out without overlap.
   - Cross-reference the current `/goal` + roadmap: prefer frontier nodes on the path to THIS goal's apex.

3. Output a tight ranked shortlist (≤ 8 rows: impact · open node · track · what it gates), then name
   the **1–2 highest-leverage provable bricks to dispatch next** (e.g. "assign `hyp:X` to wt2"). Do not
   re-plan the whole goal — surface the work and stop.
