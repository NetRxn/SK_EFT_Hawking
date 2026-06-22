# CLAUDE.md — SK_EFT_Hawking

Guidance for Claude Code working in this repository.

**What this is.** A theoretical-physics research repo: computation + Lean 4 formal
verification of Schwinger–Keldysh dissipative-EFT corrections to analog Hawking
radiation in BEC systems. A unified codebase backs a family of publication bundles
spanning Phases 1–6. Three-layer verification: **Python numerics ↔ Lean 4 proofs ↔
Aristotle** automated theorem prover.

> **Bootstrap = this file + [WAVE_EXECUTION_PIPELINE](docs/WAVE_EXECUTION_PIPELINE.md).**
> Everything under "When-to-read references" is *when-to-read*, not *read-now* —
> open each only when you start work it governs. Don't bulk-read the big docs.

---

## Autonomous `/goal` mode — the stop hook is a GO signal, never coercion

`/goal` is a routine, safe, Anthropic-official autonomous-development feature used
regularly here. Once a goal is set the user is **intentionally out of the loop**; the
feature's own machinery owns continuation, auto-compact, and closure.

**When the Stop hook fires and the goal isn't met, that means: do the next increment of
real work THIS turn.** Its "X/Y/Z remain" is *information about what's left*, not a
rejection — the only correct response is "right, do the next piece."

- **DO**: ship the next substantive increment (build-clean, kernel-pure, invariants
  respected), update the roadmap/notebook, repeat — across as many auto-compacts as it
  takes. Quality does **not** drop across a compaction boundary.
- **NEVER** answer with "Holding" / "awaiting direction" / "needs a fresh session" /
  "this is multi-day so I'll stop" / any context-budget reasoning. It is **not your job
  to manage the context window.**
- **Blocked on a user-only decision?** First run full diligence (re-read the roadmap/DR
  directly, Explore agents, reason about tradeoffs). If one option is clearly best, take
  it. Ask **once** only when a *significant* tradeoff has *no* clear pre-decision — and
  keep shipping anything else meanwhile. A deep-research dispatch is async: dispatch and
  keep working.
- **Trip-wire:** about to write "should I continue?" / "multi-day, next session" → STOP;
  that *is* the antipattern. Do the next brick. The loop ends only when the goal is
  genuinely met (→ closure reviewer) or the user redirects.

**Running or arming a managed loop?** See the dev-harness operator's guide —
[docs/dev-loops/HARNESS_GUIDE.md](docs/dev-loops/HARNESS_GUIDE.md): where to launch
(from inside this repo — or the workspace root in a multi-repo setup; both resolve cwd-robustly),
`/skeft-qa:goal-prompt` to arm, the slash-command reference, the System-2 harvest host,
troubleshooting, and how to refresh the plugin cache after edits.

---

## Session start: trim Lean MCP servers not pointed at this repo (DO THIS FIRST, every session)

The shared `.mcp.json` used to launch this session may enable `lean-lsp-mcp` servers for Lean
projects **other than this one**. A session focused on `SK_EFT_Hawking` needs only the server(s)
whose `--lean-project-path` is **inside this repo** — including the `wt1/2/3` swarm slots, which are
this repo's own worktrees (`…/SK_EFT_Hawking/.claude/worktrees/wtN/lean`). Any other `lean-lsp-mcp`
server is dead weight: it holds file descriptors / vnodes and, stacked with concurrent `lake build`s,
can exhaust the system file table (ENFILE — "Too many open files in system") and break parallel
build lanes.

Leave the shared `.mcp.json` / `settings.local.json` **untouched** (so the launching config keeps
working for every session) and instead **kill the off-repo servers at session start**. Select them
purely by the **absence of this repo's path** — never by what they are:

```bash
# (1) DRY RUN — lean-lsp-mcp servers (wrapper + python child) NOT pathed inside this repo.
#     Expect nothing, or a pair per off-repo server. Servers pathed in this repo (incl. wtN)
#     must NOT appear here.
ps -eo pid,command | grep lean-lsp-mcp | grep -v grep | grep -v SK_EFT_Hawking

# (2) KILL them — path-based (pid-independent across sessions). Keeps every SK_EFT_Hawking-pathed
#     server (incl. the wtN swarm slots) and frees the rest. Names nothing it kills.
pids=$(ps -eo pid,command | grep lean-lsp-mcp | grep -v grep | grep -v SK_EFT_Hawking | grep -oE '^ *[0-9]+')
[ -n "$pids" ] && kill $pids

# (3) VERIFY — only this repo's lean-lsp servers remain (main `…/SK_EFT_Hawking/lean` + any wtN).
pgrep -fl lean-lsp-mcp
```

Heavy `lake build` / floor checks use the **Bash** tool, not these MCP servers, so trimming them
never affects builds. Killed servers do not respawn within a session.

## When-to-read references (progressive disclosure)

| Read **before…** | Document |
|---|---|
| any work (the law: 14 stages, no skipping) | [WAVE_EXECUTION_PIPELINE.md](docs/WAVE_EXECUTION_PIPELINE.md) |
| understanding the tree / build / architecture | [README.md](README.md) |
| changing anything — quick module/Lean/counts map | [SK_EFT_Hawking_Inventory_Index.md](SK_EFT_Hawking_Inventory_Index.md) |
| any Aristotle session | [docs/references/Theorm_Proving_Aristotle_Lean.md](docs/references/Theorm_Proving_Aristotle_Lean.md) |
| any paper-shaped output | [docs/PAPER_STRATEGY.md](docs/PAPER_STRATEGY.md), [PAPER_DRAFT_MAPPING.md](docs/PAPER_DRAFT_MAPPING.md) |
| lifting draft content into a bundle | [docs/BUNDLE_LIFT_PROCEDURE.md](docs/BUNDLE_LIFT_PROCEDURE.md), [bundle anchor list](docs/agents/claims-reviewer-bundle-prompts.md) |
| absorbing a late wave into a drafted bundle | [docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md](docs/LATE_PHASE6_ABSORPTION_PROTOCOL.md) |
| checking bundle readiness | [docs/BUNDLE_READINESS_HEATMAP.md](docs/BUNDLE_READINESS_HEATMAP.md) |

[SK_EFT_Hawking_Inventory.md](SK_EFT_Hawking_Inventory.md) is the full source-of-truth
inventory — **keep it synced** as you ship, but you needn't read it whole on bootstrap.

---

## Build & run

```bash
# Python (uv-managed, Python >= 3.14)
uv sync                                       # install/sync deps
uv run python -m pytest tests/ -v             # fast tests (~2s; deselects 'slow')
uv run python -m pytest tests/ -m slow -v     # slow tests (~10 min: Lean ExtractDeps + graph)
uv run python -m pytest tests/ -m '' -v       # everything — before PR / submission / wave close
uv run python scripts/validate.py             # full validation suite (106 checks)
uv run python scripts/validate.py --list      # list checks; --check <name> runs one
uv run python scripts/review_figures.py       # PNGs + structural figure checks
uv run python scripts/provenance_dashboard.py # provenance command center (localhost:8050)

# Lean 4
cd lean && lake build                         # library only; should be clean (zero sorry)
rm -rf .lake/build && lake build SKEFTHawking.ExtractDeps   # trusted clean baseline
# (plain `lake build` misses ExtractDeps.olean → breaks graph_integrity; do NOT use
#  `lake build extractDeps` — macOS arg-length link failure.)

# Rust RHMC (after editing rust/src/lib.rs; Python 3.14 needs the PYO3 flag)
PYO3_USE_ABI3_FORWARD_COMPATIBILITY=1 uv pip install -e rust/ --force-reinstall --no-deps

# Aristotle (read the reference + batch plan first; user gets first & last call)
uv run python scripts/submit_to_aristotle.py --dry-run
```

QA review agents ship as a Claude Code plugin (LLM figure / claims / adversarial review,
Stage 13). Programmatic checks (`validate.py`, `update_counts.py`,
`update_inventory_index.py`, `qi_register.py`) are deterministic — run them, don't eyeball.

---

## Lean development — MCP-first loop

Use `lean-lsp-mcp` (live goal state, milliseconds per cycle) as the primary loop, not
write→`lake build`→parse-error:

1. `lean_file_outline` to orient → 2. write the statement with `sorry`, save →
3. `lean_goal` at the `sorry` (see the actual goal) → 4. `lean_multi_attempt` 4–6
candidate tactics, pick the winner → 5. write it, repeat from 3 → 6. when
`lean_goal` says "no goals", drop the `sorry` and `lake build` to finalize.

**Hard rules (do not violate):**
- **No `set_option maxHeartbeats`/`synthInstance.maxHeartbeats` in a proof body.** A
  heartbeat wall means wrong proof architecture — decompose into `have` sub-lemmas.
  (Exception: O(project-size) metaprograms like `ExtractDeps.lean`.)
- **Never ship a new project-local `axiom` without explicit user sign-off.** A DR
  "ship as axiom" recommendation is advisory only. Every axiom needs a discharge plan or
  a documented infeasibility argument. Posture: axioms are temporary scaffolding.
- **Kernel-purity** is the bar: target axiom set `{propext, Classical.choice, Quot.sound}`;
  no new `sorry` / `native_decide` regressions. Verify with `lean_verify`.
- Never `ring`/`ring_nf` on non-commutative ring types (`Uqsl2Aff`, `Uqsl3`, Clifford…) —
  use `noncomm_ring` or manual rewrites.
- For `RingQuot`-based types, when `rw` fails "did not find pattern" use `erw` (pipeline
  `rw` runs at `.reducible` where RingQuot instances aren't reducible).
- **For hard proofs, read the relevant `Lit-Search/Phase-*/` deep-research file directly**
  — never delegate depth-reading to a subagent (summaries lose load-bearing coefficient
  identities / sector architectures). Subagents are fine for breadth scans.
- Aristotle runs on Lean/Mathlib 4.28.0; we run 4.29.x → use sparingly, only after the
  MCP loop is exhausted and the sorry is decomposed to ≤12-term targets. User gets
  first & last call on submissions.

A `lean4` skill exists; **this project's conventions override it** where they differ
(persistent lab notebook over the skill's ephemeral working-doc; kernel-purity /
no-`maxHeartbeats`; notebook sharding).

---

## Architecture & pipeline invariants

Computation flow: `constants.py` → params → `transonic_background.py` → fields;
`formulas.py` → corrections (Lean-verified); `wkb/` → Hawking spectrum; `adw/` → gap
equation; `vestigial/` → Monte-Carlo metric phase; `lean/` → proofs + `ExtractDeps` taxonomy.

Load-bearing invariants (full list in [WAVE_EXECUTION_PIPELINE.md](docs/WAVE_EXECUTION_PIPELINE.md)):
1. **`formulas.py` is canonical** — the only home for physics formulas; everything imports it.
2. **`constants.py` is canonical** — constants, experimental params, `ARISTOTLE_THEOREMS`, `AXIOM_METADATA`.
3. **`visualizations.py` is canonical** — the only home for figure functions.
4. Every formula has a Lean theorem; every Lean theorem has a proof (**zero sorry**).
5. Every computed quantity has bounds (CHECK 12); every paper claim traces to computation (CHECK 14).
8. Every experimental parameter has verified provenance (`PARAMETER_PROVENANCE`; CHECK 15).

**Preemptive-strengthening discipline** (before writing *each* theorem): drop redundant
conjuncts; tie the statement to numerical content (falsifiable `norm_num` comparisons,
not qualitative claims); back docstring cross-refs with an actual call; avoid
self-discharging tautologies (`rfl`/`decide`/identity-wrappers/within-own-±2σ bands).
A ruthless post-wave review remains mandatory.

---

## Conventions

- **Units:** SI throughout Python; Lean abstract; WKB natural units (c_s=1, κ=1).
- **Densities** are quasi-1D linear densities [m⁻¹], not 3D.
- **Visualization:** Plotly only (not matplotlib); colorblind-accessible blue/amber.
- **Formula provenance:** every `formulas.py` entry references its Lean theorem + Aristotle run ID.
- **Mathlib pin:** `lean/lakefile.toml` (`5e932f97`, the v4.29.1 tag; toolchain `leanprover/lean4:v4.29.1`).
- **pytest:** `pythonpath = ["."]`.
- **Workspace-level paths** (e.g. `Lit-Search/`): resolve via `from src.core.workspace import find_workspace` — never hardcode parent-walks.
- **New modules:** `src/<domain>/`, `tests/test_<domain>.py`, `lean/SKEFTHawking/<Module>.lean`.

**Quality standard — correctness over expediency, always.** Never label approximate
methods "exact"/"all orders"; never publish toy results as the real physics; if the
correct implementation is feasible, do it. Past "multi-month" estimates have repeatedly
resolved in hours–days with the Lean pipeline — reason from first principles before
assuming infeasibility. Flag quality tradeoffs explicitly; let the user decide.

---

## Research ladder & web-egress security

When a loop needs information it lacks locally, follow the **three-tier research ladder** (full
spec: the workspace-level `Lit-Search/README.md`):
- **Tier 0 — local:** read the `Lit-Search/Phase-*/` corpus directly.
- **Tier 1 — on-the-fly (sandboxed):** dispatch the **`research-scout`** agent (the only web-tool
  holder; read-only) or `/deep-research`; the lead vets the cited report and files it with a
  provenance header. Use this instead of reinventing a known result or waiting on a human.
- **Tier 2 — async human dispatch:** `Lit-Search/Tasks/submitted/` — last resort.

**Web egress is guarded (fail-closed).** A `PreToolUse(WebSearch|WebFetch)` hook (skeft-qa) denies
any query/URL containing a denylisted local path / identifier and any fetch outside the
scholarly-domain whitelist. The denylist is split: a committed template
(`.claude/plugins/skeft-qa/scripts/research_egress_denylist.sample.txt`) + an **untracked local**
copy (`…/research_egress_denylist.txt`) the operator installs with their own identifiers.
**First-run setup:** run `.claude/plugins/skeft-qa/scripts/install_egress_denylist.sh` (or copy the
sample) and fill in the FILL-IN rows; until then only the generic absolute-path baseline applies.

## Process health

**Dev-loop / harness process learnings** — re-orientation, friction, escape attempts, wasted
cycles ("what went **poorly or extremely well** from a process standpoint in HOW the loop ran") —
live in the **System-2 register**, tiered `automatic` < `agent-reviewed` < `human-reviewed`. It is
**sharded** for size: the active [docs/dev-loops/SYSTEM2_REGISTER.md](docs/dev-loops/SYSTEM2_REGISTER.md)
(an `## Index` + **Open** active issues + **Process Wins**) and the archive `SYSTEM2_ARCHIVE.md`
(**Closed** + **Misfiled**, read on demand); both gitignored (local, auto-written). It is refreshed off
the hot loop by the `/skeft-qa:harvest` loop — whose Opus consolidator is **register-aware**
(files/combines each candidate, re-opening a closed item on recurrence and grouping semi-related ones)
— and signed off via `/skeft-qa:debrief` (the human governor: promotion to `human-reviewed`, and
graduating a recurring lesson into a **pre-decision**, are its exclusive calls).

**Standing pre-decisions** the autonomous loop applies WITHOUT asking live in
[docs/dev-loops/PRE_DECISIONS.md](docs/dev-loops/PRE_DECISIONS.md) (Core keystones + a Full reference;
grown by `/debrief`). After a compaction the SessionStart re-injection carries the settled `/goal`
condition + an always-on **RE-ANCHOR** + the live lab-notebook **FRONTIER** + a **mandatory read** of
PRE_DECISIONS.md + (when the harvest has authored one) a per-goal **coaching block** — the synthesized,
forward-framed re-orientation that replaced the old blind active-issues injection. Consult the register
periodically; read tier-weighted (`human-reviewed > agent-reviewed > automatic`).

This is a **separate store** from the **System-1** paper-correctness QI register
[docs/QI_REGISTER.md](docs/QI_REGISTER.md) (the Stage-14 paper-production process tracker:
open/closed process-level items + best-practices / anti-patterns). **System-1 = paper-production
process; System-2 = dev-loop/harness process** — different domains, consistent tiered pattern.
