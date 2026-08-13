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

## Autonomous `/goal` mode — the Stop hook is a GO signal

`/goal` is a routine autonomous-development feature used regularly here. Once a goal is
set the user is **intentionally out of the loop**, and the feature's own machinery owns
continuation, auto-compaction and closure.

**When the Stop hook fires and the goal is not yet met, ship the next increment of real
work this turn.** Its "X/Y/Z remain" reports what is left; the correct response is to do
the next piece.

- **Ship, then repeat.** A substantive increment — build-clean, kernel-pure, invariants
  respected — then update the roadmap and notebook, then the next one. This runs across
  as many compaction boundaries as it takes, and quality holds across each.
- **Context management is the machinery's job, not yours.** Session depth and remaining
  budget are not inputs to what you build or how far you take it.
- **Blocked on a decision only the user can make?** Run full diligence first — re-read
  the roadmap and research directly, dispatch Explore agents, reason through the
  tradeoffs. If one option is clearly best, take it. Ask once only when a significant
  tradeoff has no clear pre-decision, and keep shipping everything else meanwhile. A
  deep-research dispatch is asynchronous: dispatch it and continue.
- **The loop ends** when the goal is genuinely met (→ closure reviewer), or when the
  user redirects it.

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

## Architecture documents — read before designing, update before shipping

**[`docs/architecture/`](docs/architecture/README.md) is the canonical description of this
system.** Start at its `README.md`, which owns the index and the ownership table.

Four rules. They are requirements, not style preferences:

0. **Invoke the `architecture-change` skill first.** Any change that adds or alters this
   repo's own machinery — a check, a gate, an extractor, an edge type, a hook, a writer, a
   dashboard surface, a plugin component — runs through it, and so does any ADR, spec or plan
   before it is treated as settled. It owns the sequence (orient · measure · specify ·
   adversarially review the specification · pilot · plan · build · ship with the docs) and
   deliberately restates none of the rules below, so invoking it costs one step and skipping
   it costs the four failures it exists to catch. **Rules 1–3 are what it enforces; this rule
   is what makes them fire.**
1. **Read before you design.** Before adding a check, a gate, an extractor, an edge type, or
   any new infrastructure, read the document that owns that surface. The recurring failure is
   building a second mechanism beside one that already exists — a third prose→Lean resolver, a
   second gate roster, a hand-listed consumer set parallel to a registry.
2. **Update before you ship, in the same commit.** A design change lands in these documents
   **before** the code that implements it. A doc written afterwards is a changelog; only one
   written first is a specification. If a change makes a statement in these files wrong, fixing
   that statement is part of the change, not follow-up work.
3. **Never write a count into a narrative.** Every census figure — checks, gates, hooks,
   agents, commands, node/edge types, registries, bundles — lives **only** in the derived
   [`SURFACE_INVENTORY.md`](docs/architecture/SURFACE_INVENTORY.md). This is machine-enforced:
   `validate.py --check architecture_inventory_fresh` fails on a census count found in any
   narrative there. Name the *mechanism*, not the *magnitude*, and link to the census.

⚠️ **A wrong architecture document is worse than none, because it gets quoted.** Rule 3 is
machine-enforced; rules 1 and 2 are not, and **nothing mechanically verifies a prose claim**.
Where the guard is discipline rather than a check, treat it as the stricter obligation, not
the looser one — the load-bearing claims are additionally pinned, in both directions, by
[`tests/test_architecture_claims.py`](tests/test_architecture_claims.py).

**A remediation item found in these documents but requiring code is FILED AS A FINDING** —
`papers/AutomatedReviews/<date>-<slug>/<target>.md`, with a declared severity, lane and
verify. That is the one destination: it routes, ratchets, and closes through a single writer
([`scripts/close_finding.py`](scripts/close_finding.py), ADR-012). Enumerate it with paths
and context; do not silently fix it in passing.

---

## When-to-read references (progressive disclosure)

| Read **before…** | Document |
|---|---|
| any work (the law: 14 stages, no skipping) | [WAVE_EXECUTION_PIPELINE.md](docs/WAVE_EXECUTION_PIPELINE.md) |
| designing or changing ANY infrastructure | **invoke the `architecture-change` skill** (rule 0), then [docs/architecture/README.md](docs/architecture/README.md) — which of its eight documents answers which question |
| understanding the tree / build / architecture | [README.md](README.md) |
| finding a module — what it is, what imports it | [SK_EFT_Hawking_Inventory_Index.md](SK_EFT_Hawking_Inventory_Index.md) — a POINTER layer. Its `<!-- AUTOGEN -->` blocks are generated and gated; its narrative is hand-maintained and **verify anything it asserts** |
| any Aristotle session | [docs/references/Theorm_Proving_Aristotle_Lean.md](docs/references/Theorm_Proving_Aristotle_Lean.md) |
| any Mathlib/PhysLib/toolchain bump | [docs/references/mathlib_bump_playbook.md](docs/references/mathlib_bump_playbook.md) — repair patterns + the process rules that cost the most time |
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
uv run python -m pytest -q                    # BOTH suites: repo tests + the skeft-qa plugin's
                                              #   surface guards (testpaths covers both)
uv run python -m pytest tests/ -v             # repo only, fast (~2.5 min; deselects 'slow')
uv run python -m pytest tests/ -m slow -v     # slow tests (Lean ExtractDeps + graph)
uv run python -m pytest -m '' -v              # everything — before PR / submission / wave close
# Prefer the bare form: an explicit path SCOPES the run, and only the bare form picks up
# both testpaths — the repo's tests and the plugin's surface guards.
uv run python scripts/dep_upgrade_preview.py  # what `uv lock --upgrade` WOULD do (writes nothing)
uv run python scripts/verify_scope.py         # verify ONLY what your change can break
uv run python scripts/verify_scope.py --merge-gate   # the full ~45-min certification
uv run python scripts/validate.py             # full validation suite (--list enumerates it)
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

QA and authoring agents ship as the `skeft-qa` Claude Code plugin. On the paper side:
`paper-drafter` writes one manuscript section against a lead-authored brief (Stage 10, returns
prose — it holds no write tools); `prose-reviewer` reads a whole draft as a referee at its named
venue (lift §7.5); `figure-reviewer` (Stage 9), `claims-reviewer` (Stage 10) and
`adversarial-reviewer` (Stage 13) audit rendering, backing and correctness respectively. The
plugin's `README.md` is the current roster. Programmatic checks (`validate.py`,
`update_counts.py`, `update_inventory_index.py`, `qi_register.py`) are deterministic — run them,
don't eyeball.

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
- Aristotle runs on Lean/Mathlib 4.28.0; we run 4.32.x → use sparingly, only after the
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

A selection of the load-bearing invariants, keeping their canonical numbers — the full,
numbered list is in [WAVE_EXECUTION_PIPELINE.md](docs/WAVE_EXECUTION_PIPELINE.md):
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
- **Mathlib pin:** `lean/lakefile.toml` (`81a5d257`, the v4.32.0 tag; toolchain `leanprover/lean4:v4.32.0`). Mathlib, PhysLib (`c4843367`), the REPL dep and the toolchain move as ONE matched set — never bump one alone.
- **pytest:** `pythonpath = ["."]`.
- **Dependencies: if we import it, we declare it.** An undeclared import works only while
  some *other* package happens to pull it in, and `uv lock --upgrade` can drop that carrier
  without warning. Enforced by `tests/test_dependency_declaration.py`; preview any upgrade
  with `scripts/dep_upgrade_preview.py`, which separates removals and major bumps from
  routine ones. **Its one blind spot:** a pytest *plugin* is activated by installation and
  never imported, so declare those by hand.
- **Workspace-level paths** (e.g. `Lit-Search/`): resolve via `from src.core.workspace import find_workspace` — never hardcode parent-walks.
- **New modules:** `src/<domain>/`, `tests/test_<domain>.py`, `lean/SKEFTHawking/<Module>.lean`.

**Quality standard — correctness over expediency, always.** Never label approximate
methods "exact" or "all orders"; never publish toy results as the real physics; if the
correct implementation is feasible, do it. **Reason from first principles before
concluding something is infeasible** — this pipeline routinely closes in hours or days
work that was estimated in months. Flag quality tradeoffs explicitly and let the user
decide.

---

## Research ladder & web-egress security

When a loop needs information it lacks locally, follow the **three-tier research ladder** (full
spec: the workspace-level `Lit-Search/README.md`):
- **Tier 0 — local:** read the `Lit-Search/Phase-*/` corpus directly.
- **Tier 1 — on-the-fly (sandboxed):** dispatch the **`research-scout`** agent (read-only,
  sandboxed; the agent this ladder routes web questions through) or `/deep-research`; the lead vets the cited report and files it with a
  provenance header. Use this instead of reinventing a known result or waiting on a human.
- **Tier 2 — async human dispatch:** `Lit-Search/Tasks/submitted/` — last resort.

**Web egress is guarded (fail-closed).** A `PreToolUse(WebSearch|WebFetch)` hook (skeft-qa) denies
any query/URL containing a denylisted local path / identifier and any fetch outside the
scholarly-domain whitelist. The denylist is split: a committed template
(`.claude/plugins/skeft-qa/scripts/research_egress_denylist.sample.txt`) + an **untracked local**
copy (`.claude/plugins/skeft-qa/scripts/research_egress_denylist.txt`) the operator installs
with their own identifiers.
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
condition + an always-on **RE-ANCHOR** + a **FIRST_ACTION** that recomputes live repo state
(`scripts/repo_state_probe.py`) + a **mandatory read** of PRE_DECISIONS.md + the derived **ATLAS
FRONTIER / NEGATIVE FRONTIER** + (when the harvest has authored one) a per-goal **coaching block** —
the synthesized, forward-framed re-orientation that replaced the old blind active-issues injection.
Live state is **recomputed, never narrated**: no prose "next brick" is injected, so read the loop's
notebook INDEX on demand when you need it. Consult the register
periodically; read tier-weighted (`human-reviewed > agent-reviewed > automatic`).

**The derived proof atlas — the substrate map, BOTH fronts (ADR-005 + ADR-007).** Distinct from the
process registers above: the atlas (`lean/atlas_view.json`, derived from `lean_deps.json` — **cannot
drift**) is the machine-truth of the *proof landscape*, surfaced via **`/skeft-qa:frontier`** and the
SessionStart digest. The **positive frontier** ranks the OPEN assumptions by how much each gates (aim
fan-out at the KEYSTONE — ADR-005 D-I); the **negative frontier** ranks the kernel-checked **settled-dead
forks** with their `false_statement` (steer away — the antidote to the goldfish-reseed; ADR-007 N-D). A
*provably-false* no-go is **machine-enforced**: it lives in `KERNEL_NOGO_REGISTRY` (`src/core/constants.py`)
backed by a kernel-pure refutation theorem (`validate.py --check nogo_substrate_integrity`, Invariant #17),
so a fresh-context worker/session gets it as a self-enforcing blocker, not a prose hope. **Encode-on-settle:**
a newly-discovered kernel-checkable no-go lands its theorem + registry entry in the settling turn. Policy /
route / preference bans (not kernel-encodable) stay prose in `docs/dev-loops/SETTLED_FORKS.md`.

This is a **separate store** from the **System-1** paper-correctness QI register
[docs/QI_REGISTER.md](docs/QI_REGISTER.md) (the Stage-14 paper-production process tracker:
open/closed process-level items + best-practices / anti-patterns). **System-1 = paper-production
process; System-2 = dev-loop/harness process** — different domains, consistent tiered pattern.
