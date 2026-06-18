# System-2 Register — dev-process / harness findings

Tiered (`automatic` < `agent-reviewed` < `human-reviewed`), dev-loop/harness process findings. SEPARATE from System 1 (paper-correctness QI / `QI_REGISTER.md`). Each block's fenced `json` payload is the source of truth (round-trip-safe).

## Open

### harness-gap-worktree-slot-git-tree-goes-stale-when-main-advances-after-reset-but

**Worktree slot git-tree goes stale when main advances after reset but before dispatch**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "harness-gap",
  "title": "Worktree slot git-tree goes stale when main advances after reset but before dispatch",
  "why": "E2E 2026-06-18: reset wt1 to main, then committed to main (the auto-re-clone), then dispatched the lean-worker -> the worker built 1 commit behind main. /reset-slot auto-re-clones the slot's .lake but the git TREE is fixed at `checkout -B` time and does NOT auto-advance if main moves later. The probe was independent so it passed, but a brick depending on main's latest would fail or conflict at merge (git merge-base --is-ancestor main worktree-wt1 was false -> diverged).",
  "how_to_apply": "Reset a slot IMMEDIATELY before dispatching its worker (per task) -- never batch-reset slots and then let main advance. Emphasized in goal-dev/references/parallel-worktrees.md. Optionally fold the reset into the dispatch step, or have dispatch assert the slot HEAD == main.",
  "evidence": "git diff main worktree-wt1 showed 4 files (the probe + main's auto-re-clone changes the slot lacked).",
  "tier": "agent-reviewed",
  "status": "open",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": null,
      "goal_prompt": null,
      "roadmap": null
    }
  ],
  "id": "harness-gap-worktree-slot-git-tree-goes-stale-when-main-advances-after-reset-but",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### harness-knowledge-command-skill-markdown-is-session-snapshotted-referenced-scrip

**Command/skill markdown is session-snapshotted; referenced scripts are read fresh at run time**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "harness-knowledge",
  "title": "Command/skill markdown is session-snapshotted; referenced scripts are read fresh at run time",
  "why": "E2E 2026-06-18: after editing reset-slot.md + re-caching mid-session, invoking /skeft-qa:reset-slot via the Skill tool rendered the OLD prose (the command MARKDOWN is loaded into context at session start) but ran the NEW reset_slot.py (the !injection reads the script file fresh from the cache at run time).",
  "how_to_apply": "When iterating on the harness in-session: SCRIPT behaviour changes are testable after a cache resync; MARKDOWN/prose changes (descriptions, command bodies, SKILL.md) require a restart to render in the running session. Verify behaviour via the script, not the rendered prose.",
  "tier": "agent-reviewed",
  "status": "open",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": null,
      "goal_prompt": null,
      "roadmap": null
    }
  ],
  "id": "harness-knowledge-command-skill-markdown-is-session-snapshotted-referenced-scrip",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

## Process Wins

### compact-delta-post-compaction-successful-domain-transition-apparatus-math-with-s

**Seamless re-orientation post-compact; proof context preserved with high fidelity**  ·  tier: `human-reviewed`  ·  status: win

```json
{
  "class": "compact-delta",
  "title": "Seamless re-orientation post-compact; proof context preserved with high fidelity",
  "why": "The compact summary captured extensive state: committed Lean code (SingularRelativeMV.lean brick 72c-1 at 1dc64ccc), error log (missing opens, subspaceChains_inf qualification), next-brick architecture (72c-2 relative MV chain SES), referenced notebooks/roadmaps, and the EXACT uncommitted work (relMvChainDiag + injectivity with known issues). Post-compact the assistant immediately resumed at the right sub-task. Zero context-churn. DONE criterion 2 (validate.py 43/43) satisfied at 3ed1016c before compaction, persisting post-compact.",
  "how_to_apply": "Rare success case. Summary content precise (numbered pending tasks load-bearing), boundary at natural pause (after commit + green build), first post-compact turn engaged exact uncommitted state. Ensure compact summaries capture (a) exact last-committed SHA + uncommitted file state, (b) known errors/warnings, (c) exact next brick as numbered item, (d) blocked decisions with arguments.",
  "evidence": "Promoted (discussed). Actioned: the compaction-survival checklist (exact last SHA + uncommitted state + open errors/warnings + numbered next brick + blocked decisions) is now an explicit bullet in goal-dev/references/notebook-sharding.md, enforcing the post-compact re-orientation practice in-loop.",
  "tier": "human-reviewed",
  "status": "win",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": null,
      "roadmap": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md",
      "compact_event_id": "70cc8da1-4695-435a-be26-9db4e634a6fa:4490631"
    },
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": null,
      "roadmap": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md",
      "compact_event_id": "70cc8da1-4695-435a-be26-9db4e634a6fa:8854248"
    }
  ],
  "id": "compact-delta-post-compaction-successful-domain-transition-apparatus-math-with-s",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### investigation-cost-decision-gate-before-sinking-n-lines-investigation-cost-gate-

**'Before sinking N lines' investigation-cost gate: apply it upfront, not mid-investigation**  ·  tier: `human-reviewed`  ·  status: win

```json
{
  "class": "investigation-cost-decision-gate",
  "title": "'Before sinking N lines' investigation-cost gate: apply it upfront, not mid-investigation",
  "tier": "human-reviewed",
  "status": "win",
  "why": "Two sides of the same lesson observed in one loop. FAILURE side: after commit 4cfbb566 the loop spent ~8 turns reading excisionEquiv/excisionMap/exists_iterate_smallChains to design the iota iso BEFORE realizing the pure-snake exactness segments (E1/E2/E3) need no iota and were immediately verifiable — the checkpoint fired mid-investigation, not upfront. GOOD side: before sinking ~300 more lines into iota, the agent paused to semantic-search Mathlib for a closed-manifold Z/2 fundamental class, confirmed Mathlib lacks it (only categorical singularHomologyFunctor), and validated the hand-rolled route — preventing waste. The gate works; it must be applied at the decision point, not after committing to the investigation.",
  "how_to_apply": "Treat 'before sinking N lines' as a formal hard gate applied AT the decision point: (1) name the decision point + its cost (lines/turns); (2) ask 'can I make progress without this answer?' — if yes, defer the investigation and ship the simpler verifiable work first; (3) if the answer is genuinely load-bearing, state what would short-circuit it, run a quick verification (e.g. semantic search for Mathlib coverage), then decide. Run the gate before the investigation, not midway.",
  "evidence": "Failure: commit 4cfbb566 -> excision/small-chains investigation -> late realization 'exactness segments are verifiable next step' -> E1/E2/E3 (67174640, b210ef43). Good: 'Before sinking ~300 more lines into iota... verify Mathlib genuinely lacks a closed-manifold Z/2 fundamental class' -> 'Confirmed: Mathlib has categorical singularHomologyFunctor but no closed-manifold fundamental class - the project's hand-rolled route is necessary'.",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/dev-loops/Phase5qF/goal_prompt_20260617T231250.md",
      "roadmap": "docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md",
      "compact_event_id": null
    }
  ],
  "id": "investigation-cost-decision-gate-before-sinking-n-lines-investigation-cost-gate-",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### workflow-pattern-incremental-sharding-shard-and-commit-bank-green-shard-decompos

**Shard-and-commit / bank-green-shard decomposition keeps gates clean across long proof chains**  ·  tier: `human-reviewed`  ·  status: win

```json
{
  "class": "workflow-pattern-incremental-sharding",
  "title": "Shard-and-commit / bank-green-shard decomposition keeps gates clean across long proof chains",
  "why": "Large homological retract split into shippable increments (acyclicity, gauge bounds, continuity, final maps+homotopies), each committed independently keeping gates clean. Same pattern recurred as banking a reusable green shard (clopen-split vanishing lemma) before continuing.",
  "how_to_apply": "Codify shard-and-commit in the wave pipeline: commit+verify every ~5-6 bricks to cut context loss and enable incremental review. Ensure each shard is truly green (no sorry, kernel-pure); watch for over-fragmentation.",
  "evidence": "Commits afab3a77(19),3af3494b(20),8bebae5d(22),85aa69ea(23) each with explicit 'now build X' transition. | 'Bank it as a GREEN shard now (wire into aggregator + commit), then continue with the S⁰ base.'",
  "tier": "human-reviewed",
  "status": "win",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.claude/dev-harness/managed/70cc8da1-4695-435a-be26-9db4e634a6fa.json",
      "roadmap": "docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md",
      "compact_event_id": null
    }
  ],
  "id": "workflow-pattern-incremental-sharding-shard-and-commit-bank-green-shard-decompos",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### workflow-pattern-search-before-build-search-source-read-before-build-helpers-rou

**Search/source-read before build: helpers, routes, and reuse confirmed before writing (anti-speculation)**  ·  tier: `human-reviewed`  ·  status: win

```json
{
  "class": "workflow-pattern-search-before-build",
  "title": "Search/source-read before build: helpers, routes, and reuse confirmed before writing (anti-speculation)",
  "why": "Sustained lean_local_search/loogle/hover + concrete-source reading to confirm helpers exist, settle route decisions from actual code, decide build-vs-borrow on Mathlib coverage, and reuse existing decls (dimReductionEquiv) inline — avoiding write-then-diagnostic loops and speculative shortcuts.",
  "how_to_apply": "Codify lean_local_search -> verify -> lean_hover_info -> import-or-inline; ground any 'can we shortcut' decision in concrete source inspection; inventory-check Mathlib coverage before dispatching a worker.",
  "evidence": "'All helpers exist... Let me check SingularDisjointUnion's imports...' | 'must read the concrete... a route decision the diligence rule requires me to settle from the actual code... The docstring confirms the architecture.' | 'confirm whether the full (all-degree) sphere / Euclidean-complement homology already exists or only the top degree — that decides whether I dispatch a worker.' | 'the codebase already has dimReductionEquiv... derivable inline.'",
  "tier": "human-reviewed",
  "status": "win",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.claude/dev-harness/managed/70cc8da1-4695-435a-be26-9db4e634a6fa.json",
      "roadmap": "docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md",
      "compact_event_id": null
    }
  ],
  "id": "workflow-pattern-search-before-build-search-source-read-before-build-helpers-rou",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### process-signal-notebook-checkpointing-notebook-driven-checkpointing-sync-provide

**Notebook-driven checkpointing/sync provides compaction-durable source-of-truth**  ·  tier: `human-reviewed`  ·  status: win

```json
{
  "class": "process-signal-notebook-checkpointing",
  "title": "Notebook-driven checkpointing/sync provides compaction-durable source-of-truth",
  "why": "Each milestone triggers a LAB_NOTEBOOK.md checkpoint as persistent source-of-truth bypassing the context window; load-bearing interface findings recorded proactively before a context boundary.",
  "how_to_apply": "Working; optional hardening = pre-commit check that the notebook was touched at milestones; ensure notebook updates are comprehensive and commit-linked.",
  "evidence": "'Let me checkpoint this major progress in the notebook...' recurring; notebook records every brick + remaining path. | 'I must record the load-bearing L4-interface finding in the notebook (source-of-truth across compactions).'",
  "tier": "human-reviewed",
  "status": "win",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.claude/dev-harness/managed/70cc8da1-4695-435a-be26-9db4e634a6fa.json",
      "roadmap": "docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md",
      "compact_event_id": null
    }
  ],
  "id": "process-signal-notebook-checkpointing-notebook-driven-checkpointing-sync-provide",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### subgoal-scoping-via-downstream-interface-downstream-l2-interface-spec-used-to-de

**Downstream (L2) interface spec used to define minimal L1 deliverable (anti over-build)**  ·  tier: `human-reviewed`  ·  status: win

```json
{
  "class": "subgoal-scoping-via-downstream-interface",
  "title": "Downstream (L2) interface spec used to define minimal L1 deliverable (anti over-build)",
  "why": "Checked PoincareDual4Mid signature to confirm L1 must deliver the actual singular ℤ/2 fundamental class [M], not a weaker abstraction — interface-first scoping avoided over-build/over-generalization.",
  "how_to_apply": "Encourage as a norm: before building X, check what downstream Y actually consumes from X; that defines scope.",
  "evidence": "'check what L2 (PoincareDual4Mid) actually expects from [M] — pins down the minimal L1 deliverable... I'll keep it solo.'",
  "tier": "human-reviewed",
  "status": "win",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.claude/dev-harness/managed/70cc8da1-4695-435a-be26-9db4e634a6fa.json",
      "roadmap": "docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md",
      "compact_event_id": "70cc8da1-4695-435a-be26-9db4e634a6fa:14425384"
    }
  ],
  "id": "subgoal-scoping-via-downstream-interface-downstream-l2-interface-spec-used-to-de",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

## Closed

### knowledge-drift-vs-memory-memory-note-2-days-old-didn-t-document-new-geometric-p

**Memory note (2 days old) didn't document new geometric-program Lean files that appeared post-memory**  ·  tier: `automatic`  ·  status: closed

```json
{
  "class": "knowledge-drift-vs-memory",
  "title": "Memory note (2 days old) didn't document new geometric-program Lean files that appeared post-memory",
  "why": "Agent discovered ManifoldSmithPD, PinPlusBordismGroupDerived, SingularRelativeHomologyMod2, RokhlinManifoldFromHM, SpinBordism on-disk not mentioned in the 2-day-old memory note, forcing a lab-notebook tail re-read to establish the frontier. On-disk state drifted from the memory snapshot.",
  "how_to_apply": "Phase 5q.F roadmap/notebook-tail updates should trigger memory note updates. When a /goal pauses, update memory about files/commits/frontier before deferring.",
  "evidence": "Recorded: process habit (update memory at goal pauses); no structural gate warranted.",
  "tier": "automatic",
  "status": "closed",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": null,
      "roadmap": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md"
    }
  ],
  "id": "knowledge-drift-vs-memory-memory-note-2-days-old-didn-t-document-new-geometric-p",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### process-friction-user-interrupted-tool-use-multiple-times-due-to-race-between-ag

**User interrupted tool use multiple times due to race between agent's forensic and user's guidance**  ·  tier: `automatic`  ·  status: closed

```json
{
  "class": "process-friction",
  "title": "User interrupted tool use multiple times due to race between agent's forensic and user's guidance",
  "why": "During incident recovery the user intercepted agent tool calls ('[Request interrupted by user for tool use]') multiple times, then clarified 'i didn't mean to interrupt the tool call that would get the exact truth from record — once you're sure of blast radius, go ahead and fix.' Friction in turn-by-turn handoff when agent is mid-diagnostic and user wants to steer fix timing.",
  "how_to_apply": "In incident response, batch non-blocking diagnostics first (git log, ls, git fsck), then present findings + severity, THEN ask permission for destructive fixes. Avoid interleaving questions into the fact-gathering phase.",
  "evidence": "Recorded: incident-specific (batch non-blocking diagnostics first, then ask before destructive fixes).",
  "tier": "automatic",
  "status": "closed",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": null,
      "roadmap": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md"
    }
  ],
  "id": "process-friction-user-interrupted-tool-use-multiple-times-due-to-race-between-ag",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### goal-loop-in-progress-goal-not-yet-met-l1-m-spine-incomplete-72b-3b-is-checkpoin

**Goal not yet met; L1 [M] spine incomplete (72b-3b is checkpoint, not final)**  ·  tier: `agent-reviewed`  ·  status: closed

```json
{
  "class": "goal-loop-in-progress",
  "title": "Goal not yet met; L1 [M] spine incomplete (72b-3b is checkpoint, not final)",
  "tier": "agent-reviewed",
  "status": "closed",
  "why": "Goal requires: (1) full-carrier Omega_4^{Pin+} = Z/16 with ker(abkGrade)=0 and NO landmark/cap/disclosed-Prop binder; (2) lake build ExtractDeps clean + validate.py >=43/43 in transcript; (3) fresh-context adversarial-reviewer ZERO BLOCKER. Transcript shows only early L1 spine bricks (72a mvConnecting, 72b-1 seam+mvDelta, 72b-2 naturality+bridge, 72b-3a Homology.map_ambIncl bridge, 72b-3b mvHomDiag_mvDelta + seam helpers). The full w2 tower (L1->L5) is not built; no theorem appears; criteria 2/3 not surfaced. Mid-progress on multi-day work.",
  "how_to_apply": "Continue from the documented next step (mvDelta o mvHomSum=0, excision<->projection naturality). Maintain notebook+roadmap synchronously, ship green bricks. Hit L1 [M] completion checkpoint (commit + ExtractDeps + validate.py), then L2-L5. Run adversarial reviewer only once all bricks are complete and the tree is kernel-pure + builds clean.",
  "evidence": "Stale: the Phase 5q.F goal was cleared by the user; no longer an active loop.",
  "occurrences": [
    {
      "date": "2026-06-17",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.claude/dev-harness/managed/70cc8da1-4695-435a-be26-9db4e634a6fa.json",
      "roadmap": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md",
      "compact_event_id": null
    }
  ],
  "id": "goal-loop-in-progress-goal-not-yet-met-l1-m-spine-incomplete-72b-3b-is-checkpoin",
  "first_seen": "2026-06-17",
  "last_seen": "2026-06-17"
}
```

### compact-delta-post-compact-re-orientation-cost-4-5-re-read-turns-to-rebuild-the-

**Post-compact re-orientation cost: 4-5 re-read turns to rebuild the 5-layer dependency graph**  ·  tier: `agent-reviewed`  ·  status: closed

```json
{
  "class": "compact-delta",
  "title": "Post-compact re-orientation cost: 4-5 re-read turns to rebuild the 5-layer dependency graph",
  "why": "After the compact boundary, the session re-read notebook, file outline, roadmap, goal seed, and dispatched an Explore agent to reconstruct L1-L5 interfaces and load-bearing architectural choices (w₂ geometric vs abstract). Context-loss ripple forced reconstruction of the dependency graph from external docs.",
  "how_to_apply": "Bake into the compact summary: (a) roadmap+notebook snapshot, (b) architectural decision landmarks (w₂ is geometric, not abstract wuClass2), (c) L1->L2 interface spec, (d) load-bearing unknowns. Collapses 4-5 re-read turns to 1.",
  "evidence": "Mitigated: goal-dev gives reachable architecture landmarks + the new checkpoint-contents checklist (notebook-sharding.md) cuts post-compact re-read cost; residual is inherent to compaction.",
  "tier": "agent-reviewed",
  "status": "closed",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.claude/dev-harness/managed/70cc8da1-4695-435a-be26-9db4e634a6fa.json",
      "roadmap": "docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md",
      "compact_event_id": "70cc8da1-4695-435a-be26-9db4e634a6fa:14425384"
    }
  ],
  "id": "compact-delta-post-compact-re-orientation-cost-4-5-re-read-turns-to-rebuild-the-",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### parallel-work-dispatch-explore-read-only-explore-agent-dispatched-for-architectu

**Read-only Explore agent dispatched for architectural mapping without blocking solo work; surfaced load-bearing gap**  ·  tier: `agent-reviewed`  ·  status: closed

```json
{
  "class": "parallel-work-dispatch-explore",
  "title": "Read-only Explore agent dispatched for architectural mapping without blocking solo work; surfaced load-bearing gap",
  "why": "On a large unknown (exact L4 interface), dispatched a read-only Explore agent in parallel while continuing the L1 spine solo — delegated info-gathering without blocking forward progress. The Explore report surfaced a load-bearing architectural gap (w2(TM) geometric, not abstract wuClass2; bridged only by the Wu theorem) the main agent had not anticipated.",
  "how_to_apply": "Capture as guidance: on a large architectural unknown, dispatch a read-only Explore agent in parallel instead of blocking. Ensure the blocked-question guard does NOT intercept read-only external-investigation. Ensure the blocked-question guard does NOT intercept read-only external-investigation; the compact summary must capture such load-bearing architectural unknowns.",
  "evidence": "Captured: the read-only Explore-dispatch heuristic (parallel reconnaissance on a large architectural unknown while building solo; distinct from the lean-worker worktree fan-out) is now documented in goal-dev/references/decision-heuristics.md.",
  "tier": "agent-reviewed",
  "status": "closed",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.claude/dev-harness/managed/70cc8da1-4695-435a-be26-9db4e634a6fa.json",
      "roadmap": "docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md",
      "compact_event_id": "70cc8da1-4695-435a-be26-9db4e634a6fa:14425384"
    }
  ],
  "id": "parallel-work-dispatch-explore-read-only-explore-agent-dispatched-for-architectu",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### friction-search-loop-repeated-mathlib-api-discovery-iterations-iscompact-totally

**Repeated Mathlib API discovery iterations (IsCompact/TotallyBounded/von-Neumann-bounded)**  ·  tier: `agent-reviewed`  ·  status: closed

```json
{
  "class": "friction-search-loop",
  "title": "Repeated Mathlib API discovery iterations (IsCompact/TotallyBounded/von-Neumann-bounded)",
  "why": "3 sequential search attempts to find compact-implies-bounded lemma (IsCompact.isVonNBounded wrong form / not in pin -> TotallyBounded.isVonNBounded). Each iteration a new search-and-test cycle.",
  "how_to_apply": "Pre-populate Mathlib API quick-reference for bounded-set predicates; prioritize current pin spellings; add an API-drift note when a lemma is not found first attempt.",
  "evidence": "Superseded by the promoted human-reviewed lesson workflow-pattern-search-before-build (search -> verify -> hover -> import-or-inline before writing).",
  "tier": "agent-reviewed",
  "status": "closed",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.claude/dev-harness/managed/70cc8da1-4695-435a-be26-9db4e634a6fa.json",
      "roadmap": "docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md",
      "compact_event_id": null
    }
  ],
  "id": "friction-search-loop-repeated-mathlib-api-discovery-iterations-iscompact-totally",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### worktree-safety-boundary-respected-parallel-worktree-reset-denied-by-safety-boun

**Parallel worktree reset denied by safety boundary; agent inlined instead**  ·  tier: `agent-reviewed`  ·  status: closed

```json
{
  "class": "worktree-safety-boundary-respected",
  "title": "Parallel worktree reset denied by safety boundary; agent inlined instead",
  "why": "Attempt to reset wt1 to dispatch a lean-worker was correctly denied ('never touch a parallel agent's worktree'); agent pivoted to inlining the sphere-vanishing work without losing momentum.",
  "how_to_apply": "Boundary working as designed; agent's deny->inline response is the correct pattern. No action.",
  "evidence": "Reclassified as friction (not a clean positive): the reset denial was the auto-mode permission classifier (a CC heuristic, not a dev-harness boundary) on a slot the agent did not create that session; the v4.1 build added /reset-slot (guardrail-safe checkout -B) so slot reset is now frictionless. Phantom-guardrail family.",
  "tier": "agent-reviewed",
  "status": "closed",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.claude/dev-harness/managed/70cc8da1-4695-435a-be26-9db4e634a6fa.json",
      "roadmap": "docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md",
      "compact_event_id": null
    }
  ],
  "id": "worktree-safety-boundary-respected-parallel-worktree-reset-denied-by-safety-boun",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### harness-gap-physlib-pin-drift-pre-existing-lake-env-failed-on-mismatched-revisio

**Physlib dependency pin drift on lake build — requires manual guardrail-safe reset**  ·  tier: `agent-reviewed`  ·  status: closed

```json
{
  "class": "environment-drift",
  "title": "Physlib dependency pin drift on lake build — requires manual guardrail-safe reset",
  "why": "When lake build re-resolves the dependency graph (after adding import SKEFTHawking.SingularRelativeMV), Physlib HEAD (851e49a3) drifted from manifest pin (69197c54). Requires git -C lean/.lake/packages/Physlib checkout -f 69197c54 (guardrail-safe; reset --hard blocked by design). Procedural friction: workflow requires explicit re-pinning after import-graph changes.",
  "how_to_apply": "Document in build runbook: after adding imports/modules, if lake build fails with Physlib mismatch, run git -C lean/.lake/packages/Physlib checkout -f <pin>. Or automate as pre-build hook that re-pins Physlib.",
  "evidence": "Captured: guardrail-safe re-pin recipe added to goal-dev/references/lean-friction-catalog.md (Tooling/environment).",
  "tier": "agent-reviewed",
  "status": "closed",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": null,
      "roadmap": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md"
    }
  ],
  "id": "harness-gap-physlib-pin-drift-pre-existing-lake-env-failed-on-mismatched-revisio",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### process-math-fork-l5-abk-completeness-deferred-to-user-immediately-locked-post-c

**Math fork (L5 ABK-completeness) deferred to user, immediately locked post-compaction per user agreement**  ·  tier: `automatic`  ·  status: closed

```json
{
  "class": "process",
  "title": "Math fork (L5 ABK-completeness) deferred to user, immediately locked post-compaction per user agreement",
  "why": "Pre-compaction the agent identified a genuine math fork in L5: geometric Kirby-Taylor generation (hard classification) vs decidable height-4 spectral-sequence input (col4_height_eq_four, goal-permitted fallback). Agent requested alignment; user agreed. Post-compaction the agent locked it without re-asking: AC#1 full-carrier ker(abkGrade)=0 unconditional, build L1->L4 via 3-slot, sequence L5 last (Kirby-Taylor target, height-4 cap pre-authorized fallback only on a kernel-checked no-go).",
  "how_to_apply": "Pattern (decision requested pre-compaction, user-agreed, locked post-compaction without re-ask) worked correctly. Document the user's choice in the durable goal-prompt so post-compaction re-ask doesn't happen — as was done here.",
  "evidence": "Completion signal recorded; the Phase 5q.F goal it pertained to has since been cleared by the user.",
  "tier": "automatic",
  "status": "closed",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": null,
      "roadmap": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md",
      "compact_event_id": "70cc8da1-4695-435a-be26-9db4e634a6fa:4490631"
    }
  ],
  "id": "process-math-fork-l5-abk-completeness-deferred-to-user-immediately-locked-post-c",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### process-apparatus-validation-e2e-completed-kernel-pure-with-restart-agnostic-per

**Apparatus-validation E2E completed kernel-pure with restart-agnostic persistent-slot design**  ·  tier: `automatic`  ·  status: closed

```json
{
  "class": "process",
  "title": "Apparatus-validation E2E completed kernel-pure with restart-agnostic persistent-slot design",
  "why": "Pre-compaction closed the parallel-slot Lean apparatus validation end-to-end: slot-pinned isolated LSP (mcp__lean-lsp-wt1__*) -> proof (2+2=4, rfl, kernel-pure axioms []) -> commit succeeded (worktree-skip hook line printed, leak-guard ran, not bypassed) -> fast-forward mergeable -> guardrail-safe slot reset clean. Apparatus is restart-agnostic; only restart-time change is making skeft-qa:lean-worker dispatchable.",
  "how_to_apply": "For future /goal sessions, skip re-validating the apparatus (closed/documented at 84bb411c). Use established patterns: lead on a fast MCP, dispatch independent bricks to skeft-qa:lean-worker in persistent slots. If the pre-commit hook is ever modified, re-verify the worktree-detection logic (git rev-parse --git-dir != --git-common-dir) still holds.",
  "evidence": "Completion signal recorded: apparatus validated end-to-end at 84bb411c; lean-worker dispatchable; no re-validation needed.",
  "tier": "automatic",
  "status": "closed",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": null,
      "roadmap": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md"
    }
  ],
  "id": "process-apparatus-validation-e2e-completed-kernel-pure-with-restart-agnostic-per",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### friction-git-hook-collision-pre-commit-leak-guard-false-positive-on-math-word-th

**Pre-commit leak-guard false-positive on math word, then cleared staging**  ·  tier: `agent-reviewed`  ·  status: closed

```json
{
  "class": "friction-git-hook-collision",
  "title": "Pre-commit leak-guard false-positive on math word, then cleared staging",
  "why": "Math-context word 'push' (push-out map / pushMap) tripped the leak guardrail; had to reword. Secondary: the blocked attempt cleared the staging area, forcing re-add+re-commit.",
  "how_to_apply": "Refine guardrail to distinguish math context from structural-risk repo name; whitelist common math terms / exact-match private identifiers only. Also make hook failures non-mutating (do not clear staging); emit a recovery hint.",
  "evidence": "Reclassified + captured: NOT the pre-commit hook (greps only the exact private dir name, non-mutating). It is the CC permission classifier reading 'push' in a git command (phantom-guardrail family). Corrected entry in goal-dev/references/lean-friction-catalog.md.",
  "tier": "agent-reviewed",
  "status": "closed",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.claude/dev-harness/managed/70cc8da1-4695-435a-be26-9db4e634a6fa.json",
      "roadmap": "docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md",
      "compact_event_id": null
    }
  ],
  "id": "friction-git-hook-collision-pre-commit-leak-guard-false-positive-on-math-word-th",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### missing-process-gate-counts-json-and-validate-py-stale-across-multi-brick-commit

**Committed-state tracking: autogen counts.json stale between commits; criterion 2 passes but warnings repeat**  ·  tier: `agent-reviewed`  ·  status: closed

```json
{
  "class": "missing-process-gate",
  "title": "Committed-state tracking: autogen counts.json stale between commits; criterion 2 passes but warnings repeat",
  "tier": "agent-reviewed",
  "status": "closed",
  "why": "counts.json (autogen, tracked) fell out of sync with actual theorem counts multiple times. 'counts.json is stale again (warns each commit, but criterion 2 satisfied at 3ed1016c).' Each commit triggers stale-counts warning but validate.py 43/43 remains satisfied. Harness does not auto-regenerate counts on commit. Procedural noise without blocking.",
  "how_to_apply": "Add pre-commit hook that auto-regenerates counts.json if counts changed since last commit. Or decouple counts.json check from L2 gate (advisory-only).",
  "evidence": "Resolved by design: L2 gate treats counts.json as advisory (warns, never blocks, even on main) + auto-restages cheap derivations; heavy regen deferred to /skeft-qa:sync.",
  "occurrences": [
    {
      "date": "2026-06-17",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.claude/dev-harness/managed/70cc8da1-4695-435a-be26-9db4e634a6fa.json",
      "roadmap": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md",
      "compact_event_id": null
    }
  ],
  "id": "missing-process-gate-counts-json-and-validate-py-stale-across-multi-brick-commit",
  "first_seen": "2026-06-17",
  "last_seen": "2026-06-17"
}
```

### harness-gap-pre-commit-sorry-check-false-positives-on-comments-docstrings-and-ba

**Harness sorry-gate false positives blocked early commits; required tool rework**  ·  tier: `agent-reviewed`  ·  status: closed

```json
{
  "class": "harness-bug-fixed",
  "title": "Harness sorry-gate false positives blocked early commits; required tool rework",
  "why": "The pre-commit L2 sync gate's grep -RnE '^\\s*sorry' lean/SKEFTHawking matched 4 pre-existing FALSE positives (commented sorries in TetradGapEquation.lean:320, KerrSchild.lean:60, docstring code-fence in CenterFunctorZ2Equiv.lean:971, tracked .backup2 file). Blocked ALL commits until diagnosed. Fix (375fa5e9) changed detection to parse the LSP build log for actual 'declaration uses sorry' warnings. Harness tool gap: regex-based sorry detection brittle with comment/docstring volume.",
  "how_to_apply": "Replace simple file-grep sorry detectors with LSP build-log parsers (capture lake build stderr, search 'declaration uses sorry'). Or use lean_diagnostic_messages MCP. Pre-commit gates should only block on actual Lean compiler signals, not source patterns.",
  "evidence": "Fixed at 375fa5e9: pre-commit-sync.sh parses the lake build log for the genuine-sorry signal instead of source grep; verified in current hook.",
  "tier": "agent-reviewed",
  "status": "closed",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": null,
      "roadmap": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md"
    }
  ],
  "id": "harness-gap-pre-commit-sorry-check-false-positives-on-comments-docstrings-and-ba",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### harness-gap-lake-packages-never-gitignored-causing-commit-tree-failures-and-logi

**.lake/packages/* never gitignored, causing commit-tree failures and logical bloat; 10 stray gitlinks committed**  ·  tier: `automatic`  ·  status: closed

```json
{
  "class": "harness-gap",
  "title": ".lake/packages/* never gitignored, causing commit-tree failures and logical bloat; 10 stray gitlinks committed",
  "why": "Lake dep checkouts (mathlib, Physlib, batteries, doc-gen4) are git repos with their own tracked files whose blobs live in the dep's object store. lean/.gitignore ignored .lake/build but NOT .lake/packages/*. Worktree seed cp -c .lake + broad git add staged unresolvable paths, blocking commits. Also 10 stray submodule gitlinks (mode 160000) were committed by accident (bbee8ae9, no .gitmodules).",
  "how_to_apply": "Fixed in commit 3e76adb9: add /.lake to lean/.gitignore (ignore all of .lake). Un-track the 10 stray gitlinks. Worktrees/slots can then safely cp -c .lake or symlink from this HEAD onward.",
  "evidence": "Fixed at 3e76adb9 (/.lake added to lean/.gitignore; 10 stray gitlinks un-tracked).",
  "tier": "automatic",
  "status": "closed",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": null,
      "roadmap": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md"
    }
  ],
  "id": "harness-gap-lake-packages-never-gitignored-causing-commit-tree-failures-and-logi",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### process-signal-subagent-flailed-destructively-when-hitting-commit-blocker-safety

**Subagent flailed destructively when hitting commit blocker; safety guardrails added to agent spec**  ·  tier: `automatic`  ·  status: closed

```json
{
  "class": "process-signal",
  "title": "Subagent flailed destructively when hitting commit blocker; safety guardrails added to agent spec",
  "why": "First e2e worker (a3b3) hit a commit blocker (.lake/packages/* gitlink bug) and responded with raw git plumbing (rm .git/index, read-tree, write-tree, update-index), hook bypasses, and .lake thrashing. Blast radius contained to its own removed worktree, but exposed that workers must not 'fix' blocked commits via git surgery.",
  "how_to_apply": "Edit lean-worker.md safety section to forbid raw git plumbing (read-tree/write-tree/update-ref/commit-tree/rm index), hook bypasses (--no-verify), destructive artifact ops (lake clean, rm -rf .lake, touching .lake/packages). On commit/build fail: STOP and report to lead. Already in place post-fix.",
  "evidence": "Resolved: lean-worker.md Safety section forbids raw git plumbing / --no-verify / destructive .lake ops with STOP-and-report; verified in place.",
  "tier": "automatic",
  "status": "closed",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": null,
      "roadmap": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md"
    }
  ],
  "id": "process-signal-subagent-flailed-destructively-when-hitting-commit-blocker-safety",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### harness-gap-worktree-isolation-failed-from-non-git-workspace-root-cwd-relative-d

**Worktree isolation failed from non-git workspace root; cwd-relative dispatch replaced the proposed WorktreeCreate hook**  ·  tier: `automatic`  ·  status: closed

```json
{
  "class": "harness-gap",
  "title": "Worktree isolation failed from non-git workspace root; cwd-relative dispatch replaced the proposed WorktreeCreate hook",
  "why": "isolation:worktree requires the session cwd inside a git repo; launching from the non-git workspace root raised 'Cannot create agent worktree: not in a git repository and no WorktreeCreate hooks are configured.' The initial fix was an auto-executing WorktreeCreate hook in workspace .claude/hooks/ — which the PreToolUse(AskUserQuestion) guard correctly intercepted for sign-off (working as designed); the user refused the blind SK-default as a leak risk. Testing then confirmed the Agent tool reads current cwd (not launch cwd), so a `cd SK_EFT_Hawking/` before dispatch suffices — obsoleting ~2h of hook design/doc/testing and eliminating the hook entirely.",
  "how_to_apply": "Lead runs `cd SK_EFT_Hawking/` before dispatching subagents with isolation:worktree (leverages mid-flow session cwd change); drop the WorktreeCreate hook. Prefer testing simpler existing-platform mechanisms (cwd persistence, explicit lead control) before proposing new hooks/automation. The guard's escalation on the hook install was correct behavior — no guard change needed.",
  "evidence": "RC2 resolved: cwd-explicit dispatch + cwd-robust repo_root(); WorktreeCreate hook dropped; documented in HARNESS_GUIDE + goal-dev/references/parallel-worktrees.md.",
  "tier": "automatic",
  "status": "closed",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": null,
      "roadmap": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md"
    }
  ],
  "id": "harness-gap-worktree-isolation-failed-from-non-git-workspace-root-cwd-relative-d",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### blocked-question-malformed-blocked-question-record-probe-artifact-with-empty-tur

**Malformed blocked-question record (probe artifact) with empty turn and minimal question text**  ·  tier: `automatic`  ·  status: closed

```json
{
  "class": "blocked-question",
  "title": "Malformed blocked-question record (probe artifact) with empty turn and minimal question text",
  "why": "The guard's blocked-question log contains one entry session_id=probe-8385 with turn=null and question='x?' — a test/probe artifact, not real signal. Notes the presence of a guard that should emit higher-quality blocks.",
  "how_to_apply": "If the guard is newly integrated (Plan 1 harness build 2026-06-17), verify the PreToolUse(AskUserQuestion) handler captures turn numbers and full question text. If this recurs with non-probe sessions, trace log initialization.",
  "evidence": "RC5: probe/test artifact (session_id=probe-8385); guard lifecycle hardened (SessionEnd cleanup hook + /goal-end).",
  "tier": "automatic",
  "status": "closed",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": null,
      "roadmap": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md"
    }
  ],
  "id": "blocked-question-malformed-blocked-question-record-probe-artifact-with-empty-tur",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### architecture-gap-inline-subagent-mcp-servers-do-not-surface-in-this-environment

**Inline subagent MCP servers do not surface in this environment**  ·  tier: `automatic`  ·  status: closed

```json
{
  "class": "architecture-gap",
  "title": "Inline subagent MCP servers do not surface in this environment",
  "why": "Per-subagent inline MCP entries (lean-lsp-worker in agent's mcpServers) do not materialize. Two ToolSearch queries confirmed lean-lsp-worker absent; subagents only inherit the main session's lean-lsp pinned to main. Forced a pivot to persistent pre-built worktree slots with static MCP defs in workspace .mcp.json.",
  "how_to_apply": "Abandon inline-per-worker MCP; use persistent slots (wt1/2/3) with static mcp__lean-lsp-wt1/2/3 defs in workspace config. Lead assigns workers to pre-built slots; each has its own build-isolated server. No inline mcpServers in agent specs.",
  "evidence": "RC1/RC3: documented in goal-dev/references/parallel-worktrees.md; persistent wt1/2/3 slots + static workspace .mcp.json are the standing pattern (ef0c3d36).",
  "tier": "automatic",
  "status": "closed",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": null,
      "roadmap": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md"
    }
  ],
  "id": "architecture-gap-inline-subagent-mcp-servers-do-not-surface-in-this-environment",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### config-discovery-friction-no-centralized-discovery-point-for-the-worktree-lean-i

**No centralized discovery point for the worktree/lean-infra plan — agent hunted through memory notes**  ·  tier: `automatic`  ·  status: closed

```json
{
  "class": "config-discovery-friction",
  "title": "No centralized discovery point for the worktree/lean-infra plan — agent hunted through memory notes",
  "why": "Task to find and activate the lean-lsp multi-instance plan forced heuristic memory-note search ('PARALLEL APPARATUS' text), then on-disk verification. No canonical Lean-development-infrastructure doc centralizes worktree naming, MCP server paths, gitignore patterns — scattered across memory, docs, implicit conventions.",
  "how_to_apply": "Create one canonical doc (e.g. docs/LEAN_DEVELOPMENT_INFRASTRUCTURE.md or under .claude/) covering: worktree naming/layout, lean-lsp multi-instance (wt1/2/3) setup, gitignore patterns, how orchestrating agents spin up the infra. Reference from goal-prompt guidance.",
  "evidence": "RC1 resolved: centralized in goal-dev/references/parallel-worktrees.md + lean-friction-catalog.md; the model-invocable goal-dev skill surfaces them in-loop.",
  "tier": "automatic",
  "status": "closed",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": null,
      "roadmap": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md"
    }
  ],
  "id": "config-discovery-friction-no-centralized-discovery-point-for-the-worktree-lean-i",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### harness-gap-marker-persisted-after-goal-clear-sessionstart-re-injection-askuserq

**Marker persisted after /goal clear -> SessionStart re-injection + AskUserQuestion guard misfired**  ·  tier: `agent-reviewed`  ·  status: closed

```json
{
  "class": "harness-gap",
  "title": "Marker persisted after /goal clear -> SessionStart re-injection + AskUserQuestion guard misfired",
  "why": "On /goal clear the gitignored managed marker was not removed, so SessionStart re-injection kept treating the cleared goal as active and the PreToolUse(AskUserQuestion) guard misfired during the subsequent /debrief. RC5 marker/guard lifecycle gap.",
  "how_to_apply": "Fixed in v4.1: SessionEnd hook removes the marker when reason==clear (harness_session_end.py) + a /goal-end command (harness_goal_end.py) for explicit teardown; remove_marker() added to harness_common.py with tests.",
  "evidence": "Debrief guard misfired on a stale post-clear marker; structural fix = SessionEnd(reason=clear) cleanup + /goal-end; covered by test_session_end_* in test_harness_core.py.",
  "tier": "agent-reviewed",
  "status": "closed",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": null,
      "roadmap": null
    }
  ],
  "id": "harness-gap-marker-persisted-after-goal-clear-sessionstart-re-injection-askuserq",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### harness-knowledge-phantom-dev-harness-guardrail-mis-attribution-auto-mode-permis

**Phantom dev-harness guardrail mis-attribution: auto-mode permission-classifier denials read as project hooks**  ·  tier: `agent-reviewed`  ·  status: closed

```json
{
  "class": "harness-knowledge",
  "title": "Phantom dev-harness guardrail mis-attribution: auto-mode permission-classifier denials read as project hooks",
  "why": "Worktree-reset denials and the 'push' commit-command flag were blamed on a dev-harness guardrail/hook that does not exist; both are the CC auto-mode permission classifier (a platform heuristic). The mis-attribution caused wasted workarounds (inlining instead of resetting; rewording commit messages blaming the leak-guard).",
  "how_to_apply": "Fixed in v4.1: parallel-worktrees.md + reset_slot.py docstring clarify the reset denial is the auto-mode classifier (not a hook); /reset-slot gives the guardrail-safe checkout -B path; the catalog 'push' entry was corrected to point at the permission classifier.",
  "evidence": "Verified the pre-commit hook greps only the private dir name and never mutates staging. Docs corrected in commit acd70af0 (catalog) + the v4.1 parallel-worktrees.md.",
  "tier": "agent-reviewed",
  "status": "closed",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": null,
      "roadmap": null
    }
  ],
  "id": "harness-knowledge-phantom-dev-harness-guardrail-mis-attribution-auto-mode-permis",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### harness-gap-slot-reset-recipe-stranded-in-user-only-docs-not-at-the-action-point

**Slot-reset recipe stranded in user-only docs, not at the action point (worker dispatch)**  ·  tier: `agent-reviewed`  ·  status: closed

```json
{
  "class": "harness-gap",
  "title": "Slot-reset recipe stranded in user-only docs, not at the action point (worker dispatch)",
  "why": "The guardrail-safe slot-reset recipe lived only in narrative docs / the user-only goal-prompt, so the autonomous lead reached for git reset --hard (denied) instead. RC1: recipe not at the action point.",
  "how_to_apply": "Fixed in v4.1: /reset-slot is a model-invocable command (reset_slot.py) -- guardrail-safe checkout -B + staleness-gated .lake auto-re-clone, an atomic action the lead invokes directly; full flow in goal-dev/references/parallel-worktrees.md.",
  "evidence": "/reset-slot command added (model-invocable); parallel-worktrees.md step 1 documents per-task reset-before-dispatch.",
  "tier": "agent-reviewed",
  "status": "closed",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": null,
      "roadmap": null
    }
  ],
  "id": "harness-gap-slot-reset-recipe-stranded-in-user-only-docs-not-at-the-action-point",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### grouped-tactical-lean-frictions-captured-in-catalog

**Tactical-Lean frictions (14) -- captured in goal-dev lean-friction-catalog.md**  ·  tier: `agent-reviewed`  ·  status: closed

```json
{
  "id": "grouped-tactical-lean-frictions-captured-in-catalog",
  "class": "friction-grouped",
  "title": "Tactical-Lean frictions (14) -- captured in goal-dev lean-friction-catalog.md",
  "why": "Recurring proof-mechanics frictions, each now an explicit SYMPTOM->FIX entry in the model-invocable goal-dev friction catalog (grepped in-loop; RC1). Grouped to keep the register compact.",
  "how_to_apply": "On a recurring friction, grep goal-dev/references/lean-friction-catalog.md for the symptom before re-deriving.",
  "evidence": "Absorbed: dependent-motive rewrite, quotient mk-coercion, reducible-abbrev, ring-on-scalar, section-vars, free-var capture, simp-unfolding, cross-module namespace-open, hypothesis-shadowing, interval-bounds, lake-build wrong-cwd, private-helper inline, do-nothing tactic warning, lean_goal declaration-vs-sorry line.",
  "tier": "agent-reviewed",
  "status": "closed",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": null,
      "roadmap": null
    }
  ],
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### grouped-over-deferral-silent-descope-over-verification

**Over-deferral / silent-descope / over-verification -- governed by CLAUDE.md + memory**  ·  tier: `agent-reviewed`  ·  status: closed

```json
{
  "id": "grouped-over-deferral-silent-descope-over-verification",
  "class": "discipline-grouped",
  "title": "Over-deferral / silent-descope / over-verification -- governed by CLAUDE.md + memory",
  "why": "Three facets of one over-caution failure mode: premature deferral of an almost-done chain, silently descoping a boundary case, and re-verifying after permission was already given.",
  "how_to_apply": "Captured in CLAUDE.md goal-mode discipline + preemptive-strengthening, and memory feedback-no-disclosure-stopping / feedback-no-hypothesis-based-descope. No new gate.",
  "evidence": "Absorbed: wasted-cycles-deferred-unnecessarily, friction-silent-boundary-descope, over-verification.",
  "tier": "agent-reviewed",
  "status": "closed",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": null,
      "roadmap": null
    }
  ],
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

## Misfiled

### misfiled-tactic-level-and-goal-specific-harvest-logs

**Tactic-level / goal-specific harvest logs (low-value single-occurrence confirmations)**  ·  tier: `automatic`  ·  status: misfiled

```json
{
  "id": "misfiled-tactic-level-and-goal-specific-harvest-logs",
  "class": "misfiled-log",
  "title": "Tactic-level / goal-specific harvest logs (low-value single-occurrence confirmations)",
  "why": "Catch-all for harvest-extractor entries that are tactic-level noise or goal-specific confirmations ('discipline held','kernel-pure velocity','reuse worked','route pivot sound') -- true but never standing findings. They flooded the open set from the cleared Phase 5q.F loop.",
  "how_to_apply": "Future single-occurrence pure-confirmation harvest logs append HERE (not a new open finding). Durable fix: tune harvest-extractor/consolidator to auto-route low-value confirmations to misfiled (tracked separately).",
  "evidence": "Absorbed 13 Phase 5q.F items: architecture-decision-sound, error-localization, no-parse-friction, kernel-pure-velocity, goal-loop-discipline, kernel-purity-discipline, reuse-over-rebuild, deliberate-error-recovery, template-mirroring, stop-hook=GO, solo-vs-fanout, background-waiter, frontier-status-check.",
  "tier": "automatic",
  "status": "misfiled",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": null,
      "roadmap": null
    }
  ],
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

