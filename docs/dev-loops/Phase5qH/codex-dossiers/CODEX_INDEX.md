# Codex dossier index — the codex-specific lab notebook

> **This is the codex layer, not the canonical notebook.** Codex runs land here first. The
> orchestrator decides what gets **promoted** into `LAB_NOTEBOOK.md` / the canonical
> `LAB_NOTEBOOK_INDEX.md` — nothing flows automatically. Raw transcripts are never read or
> committed; `scripts/codex_dossier.py harvest` extracts the deliverable mechanically.
>
> **Per run, the orchestrator fills in three fields by hand** (the script never overwrites them):
> - **VERDICT** — one line: what the run concluded, and whether it was lead-verified.
> - **FINDINGS FOR DISPATCH** — paste-ready facts for worker briefs (exact identifiers, file:line,
>   traced dead ends). This is the reason the dossier exists: it should shorten the next brief.
> - **PROMOTED** — `no`, or where it went (SETTLED_FORKS / KERNEL_NOGO_REGISTRY / notebook FRONTIER).
>
> ⚠ **A codex claim is UNVERIFIED until the lead checks it in the Lean.** Dossiers are advisory;
> they have been wrong (see the `codex_212_collarpair_design` route-defect note). Mark verified
> claims explicitly before they enter a worker brief.

| date | dossier | verdict | promoted |
|---|---|---|---|
| 2026-07-21 | [`codex_212_collarpair_design`](codex_212_collarpair_design.md) | 8-point CollarPairBuild spec. **LEAD-VERIFIED (6 citations real).** Consumed → #212 UNFROZEN. ⚠ its `hp_det` via `collarCorePrism` is NOT provable from the current row (traced by wt1) | yes → wt1 brief; route defect noted in notebook |
| 2026-07-21 | [`codex_212_gate`](codex_212_gate.md) | The gate FAIL that froze #212 (open-complement split shape). **Backed by kernel no-go `seam-transfer-open-support-uninhabitable`.** | yes → KERNEL_NOGO_REGISTRY |
| 2026-07-21 | [`codex_H1_scoping`](codex_H1_scoping.md) | Lane H-1 compression-disk scoping. | no — H-1 not yet staffed |
| 2026-07-21 | [`codex_K8b_adjudication`](codex_K8b_adjudication.md) | K8b route-(i) adjudication → `StableNegRank16` floor. | partial → ReblockToK3 landed |
| 2026-07-21 | [`codex_hcolD_B1_design`](codex_hcolD_B1_design.md) | B1 `RankZeroSurfaceBoundingDatum` design, option (c) adopted. One invented name (`pinCharSurfaceOfBundled`); everything else verified real. | yes → B1 interface built |
| 2026-07-21 | [`codex_hcolD_route`](codex_hcolD_route.md) | hcolD brick table B0–B7 + demand-narrowing to `SectorIsGeometric`. Risks 2/6 → the one-sphere/3-handle framing caution. | yes → SETTLED_FORKS (prose caution) |
| 2026-07-21 | [`codex_hcross_route`](codex_hcross_route.md) | 4th route for hcross via one-factor MV Stokes peel. **Consumed → hcross_pm now UNCONDITIONAL.** | yes → lane closed |
| 2026-07-21 | [`codex_rowside_scoping`](codex_rowside_scoping.md) | Row-side floor: NO unconditional row instance at HEAD; #257's 'collapse' was interface-level only. Brick table R0–R7/A1–A3. | yes → notebook row-side status corrected |
| 2026-07-21 | [`codex_strength_audit_20260721`](codex_strength_audit_20260721.md) | Fresh-context strength audit. B1 separability overclaim (lead-verified), B2 missing K3→row bridge, M3/M4 fences. | yes → tasks #304/#305 + notebook |

<!-- PER-RUN NOTES -->

## The protocol (why this layer exists)

Codex runs on a **different provider** so its reasoning happens in *its* context, not the
orchestrator's. A raw `codex exec` transcript is 1–2 MB; reading one would overflow the lead and
destroy the entire benefit. So the transcript is **never read and never committed** — a script
extracts the run's final deliverable mechanically.

```
codex exec ... > $SCRATCH/codex_<slug>.md        # raw, ephemeral, NEVER read by the lead
uv run python scripts/codex_dossier.py harvest \
    $SCRATCH/codex_<slug>.md --slug <slug> \
    --question "<the question asked>"            # -> codex_<slug>.md (~15-30 KB) + index row
uv run python scripts/codex_dossier.py check \
    --scratchpad $SCRATCH                        # flags UNHARVESTED runs + oversize dossiers
```

**Launch recipe** (the `< /dev/null` is required — without it codex hangs ~90 min on stdin):

```
codex exec --skip-git-repo-check --sandbox read-only -m gpt-5.6-sol \
  -c model_reasoning_effort=xhigh "$(cat <<'PROMPT'
<the question>
PROMPT
)" < /dev/null > "$SCRATCH/codex_<slug>.md" 2>&1 &
```

### Flow of authority

1. **Codex → this notebook.** Every run lands here as a dossier + a row above. Automatic.
2. **This notebook → worker briefs.** The lead cites the dossier path and pastes its specific
   findings (exact identifiers, file:line, traced dead ends) into the brief. This is the payoff:
   a good dossier *shortens the next brief* and stops a worker re-surveying.
3. **This notebook → canonical.** Nothing flows automatically. The lead promotes — a line in
   `SETTLED_FORKS.md`, an entry in `KERNEL_NOGO_REGISTRY`, or a FRONTIER pointer — and records
   where in the `promoted` column.

### Standing cautions (both learned the hard way, 2026-07-21)

- **A codex claim is UNVERIFIED until the lead checks it in the Lean.** Dossiers have been wrong:
  `codex_hcolD_B1_design` invented one identifier, and `codex_212_collarpair_design`'s `hp_det`
  route is not provable from the current parameter row. Mark a claim lead-verified before it
  enters a worker brief; otherwise label it UNVERIFIED so the worker checks it.
- **Harvest immediately.** These nine dossiers lived ~13 MB deep in a session-scoped scratchpad
  with nothing in `docs/`, while the notebook cited them as durable paths. A cleanup would have
  destroyed the #212 spec and the strength audit. `check --scratchpad` exists to catch exactly
  that; run it before ending a session with codex work in flight.
