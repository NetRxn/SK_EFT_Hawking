# Lean development reference (MCP-first)

Loaded on demand for hard Lean proof work in a `/goal` loop. (Project conventions also live
in `SK_EFT_Hawking/CLAUDE.md`; this is the in-loop quick reference. Project conventions
OVERRIDE the generic `lean4` skill where they differ.)

## The MCP-first loop (milliseconds/cycle, not the ~15s write→lake-build cycle)

1. `lean_file_outline` — orient in the file.
2. Write the statement with `sorry`; save.
3. `lean_goal` at the `sorry` — **see the actual goal** before writing tactics.
4. `lean_multi_attempt` with 4–6 candidate tactic sequences at the position — pick the winner.
5. Write the winner; repeat from 3 at the new state.
6. When `lean_goal` says **"no goals"**, drop the `sorry`; `lake build` to finalize.

## Hard rules (do NOT violate)

- **Kernel-purity is the bar.** Target axiom set `{propext, Classical.choice, Quot.sound}`.
  **No new project-local `axiom`** without explicit user sign-off (advisory DR recs are not
  sign-off). **No new `sorry` / `native_decide` regressions.** Verify with `lean_verify`.
- **No `set_option maxHeartbeats` / `synthInstance.maxHeartbeats` in a proof body.** A
  heartbeat wall means a wrong proof architecture — **decompose into `have` sub-lemmas**
  (target ≤ 12-term sub-lemmas Aristotle/the kernel can chew). (Exception: O(project-size)
  metaprograms like `ExtractDeps.lean`.)
- **Search before prove:** `lean_local_search` first; then `lean_leansearch` / `lean_loogle`
  / `lean_leanfinder` / `lean_state_search` (rate-limited).
- **Read the deep-research directly for hard proofs.** Read the relevant
  `Lit-Search/Phase-*/` file yourself — never delegate depth-reading to a subagent
  (summaries lose load-bearing coefficient identities / sector architectures). Subagents are
  fine for breadth scans.
- **Non-commutative ring types** (`Uqsl2Aff`, `Uqsl3`, Clifford, …) are `Ring`, not
  `CommRing` — use `noncomm_ring` or manual rewrites, never `ring`/`ring_nf`.
- **`RingQuot`-based types:** when `rw` fails "did not find pattern", use `erw` (pipeline
  `rw` runs at `.reducible` where RingQuot instances aren't reducible).

## Aristotle (fallback only — Stage 4)

Use **sparingly**, only after the MCP loop is exhausted on a sorry AND the sorry is
decomposed into ≤ 12-term sector/sub-lemma targets. Aristotle runs Lean/Mathlib 4.28.0; we
run 4.29.x — compatibility differences possible. **The user gets first & last call** on
submissions (each pushes a whole-project batch, ~1-day turnaround). This is a *genuine
user-only decision* (a legitimate stop / ask-once), not an escape.

## Preemptive-strengthening (before writing each theorem statement)

Tie the statement to numerical content (falsifiable `norm_num` comparisons, not qualitative
claims); drop redundant conjuncts; back docstring cross-refs with an actual call; avoid
self-discharging tautologies (`rfl`/`decide`/identity-wrappers/within-own-±2σ bands).

## Parallel Lean development (worktree fan-out — a `lead` orchestrating Lean subagents)

When a proof program **branches into independent sub-chains** (NOT a tightly-coupled single-file
chain — those stay solo with one fast MCP), a `lead` can fan the bricks out to subagents, each in
its own git worktree with its own fast MCP server. The workspace `.mcp.json` pre-defines **three
fixed slots** (enabled in `.claude/settings.local.json`; **loaded on session restart**):

| Slot (create with this exact name) | Lean project path | MCP server the subagent uses |
|---|---|---|
| `wt1` | `<repo>/.claude/worktrees/wt1/lean` | `mcp__lean-lsp-wt1__*` |
| `wt2` | `<repo>/.claude/worktrees/wt2/lean` | `mcp__lean-lsp-wt2__*` |
| `wt3` | `<repo>/.claude/worktrees/wt3/lean` | `mcp__lean-lsp-wt3__*` |

The binding is **by the fixed name** — the server paths are static, so a worktree MUST be named
`wtN` (not a random/`isolation: worktree` name) for `lean-lsp-wtN` to serve it.
`<repo>/.claude/worktrees/` is gitignored.

**Lead's spin-up, per slot:**
1. **Create the slot with the matching name:** `git worktree add .claude/worktrees/wt1 -b
   worktree-wt1` (or `EnterWorktree name=wt1` / `claude --worktree wt1` — all land at the same
   deterministic path). Do **not** use `Agent isolation: worktree` for a slot — it generates a
   random name no static server matches.
2. **Seed its Lean build** so the LSP loads instantly (a fresh worktree's `.lake/` is gitignored →
   empty). The slot is checked out at the **same commit** as the main tree, so the main build is
   valid for it — **fastest: symlink (or copy) the main tree's `lean/.lake` into the slot**
   (`lean-lsp` / `lake env lean` only *read* the oleans → no rebuild; verified instant, main build
   untouched). From-clean alternative: `lake exe cache get` + `lake build` in the slot's `lean/`, or
   list `.lake/` in a `.worktreeinclude` so CC copies the oleans in at creation.
3. **Dispatch one independent sub-chain** to a subagent working under that slot's path.

⚠ **Ordering (load-bearing — verified):** the `lean-lsp-wtN` servers attach at **session start** and
register their tools only if the worktree path **already exists then**. A slot whose worktree is
absent fails to connect *harmlessly*, but its tools stay absent for the **whole** session (**no
mid-session hot-reload** — confirmed: creating a slot mid-session does NOT surface its tools). So
**create + seed the slots BEFORE launching the consuming session**, or restart it after creating
them. The clean fit for static servers = **persistent slots**: keep `wt1/2/3` on disk (gitignored),
`git reset --hard <base>` + re-seed per task, rather than create-and-destroy each time.

**Subagent contract (state it in the dispatch prompt):**
- Edit files under the slot path and drive proofs with the **`lean4` skill + the matching
  `mcp__lean-lsp-wtN__*` tools** — the MCP-first loop above (`lean_goal` / `lean_multi_attempt` /
  `lean_diagnostic`), **NOT** write→`lake build` cycles. (Project conventions override the generic
  skill.)
- Same hard rules: kernel-pure `{propext, Classical.choice, Quot.sound}`; no new axiom / `sorry` /
  `native_decide` / `maxHeartbeats`; ≤12-term sub-lemmas; search before prove.
- **Stage own paths only; never touch another slot's / agent's files.** Commit GREEN shards on the
  slot's branch; never push (user action).

**Fan out only when the DAG has genuinely branched** (independent files / sub-lemmas). A
tightly-coupled chain (each brick depends on the prior, one file) is faster solo with one fast MCP
— fanning it out just serializes through the dependency with extra coordination cost.
