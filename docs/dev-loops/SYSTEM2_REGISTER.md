# System-2 Register — dev-process / harness findings

Tiered (`automatic` < `agent-reviewed` < `human-reviewed`), dev-loop/harness process findings. SEPARATE from System 1 (paper-correctness QI / `QI_REGISTER.md`). Each block's fenced `json` payload is the source of truth (round-trip-safe).

## Open

### over-verification-agent-stops-to-verify-assumptions-before-editing-infrastructur

**Agent stops to verify assumptions before editing infrastructure when user has already given permission**  ·  tier: `automatic`  ·  status: open

```json
{
  "class": "over-verification",
  "title": "Agent stops to verify assumptions before editing infrastructure when user has already given permission",
  "why": "Agent repeatedly paused implementation to verify assumptions (private-repo pattern, worktree path conventions, MCP constraints) even after user gave permission. User had to redirect with 'verify with source before trusting constraints' which the agent interpreted as 'stop and ask' rather than 'verify independently'. Three checkpoint loops before proceeding.",
  "how_to_apply": "When a user grants permission for infra edits and flags an assumption-risk, verify independently via authoritative sources WITHOUT stopping to ask. Surface findings and proceed. Reserve asking-back for genuine tradeoffs, not 'I need to check the docs' verifications you can do yourself.",
  "evidence": "Agent: 'One quick decision and I'll execute it fully' -> user: 'verify with source before trusting constraints' -> agent pauses again -> user: 'ok that works - take care of everything in 1 short of the restart.'",
  "tier": "automatic",
  "status": "open",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": null,
      "roadmap": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md"
    }
  ],
  "id": "over-verification-agent-stops-to-verify-assumptions-before-editing-infrastructur",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### blocked-question-malformed-blocked-question-record-probe-artifact-with-empty-tur

**Malformed blocked-question record (probe artifact) with empty turn and minimal question text**  ·  tier: `automatic`  ·  status: open

```json
{
  "class": "blocked-question",
  "title": "Malformed blocked-question record (probe artifact) with empty turn and minimal question text",
  "why": "The guard's blocked-question log contains one entry session_id=probe-8385 with turn=null and question='x?' — a test/probe artifact, not real signal. Notes the presence of a guard that should emit higher-quality blocks.",
  "how_to_apply": "If the guard is newly integrated (Plan 1 harness build 2026-06-17), verify the PreToolUse(AskUserQuestion) handler captures turn numbers and full question text. If this recurs with non-probe sessions, trace log initialization.",
  "evidence": "blocked_questions span: {\"session_id\":\"probe-8385\",\"questions\":[{\"question\":\"x?\"}]}",
  "tier": "automatic",
  "status": "open",
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

### knowledge-drift-vs-memory-memory-note-2-days-old-didn-t-document-new-geometric-p

**Memory note (2 days old) didn't document new geometric-program Lean files that appeared post-memory**  ·  tier: `automatic`  ·  status: open

```json
{
  "class": "knowledge-drift-vs-memory",
  "title": "Memory note (2 days old) didn't document new geometric-program Lean files that appeared post-memory",
  "why": "Agent discovered ManifoldSmithPD, PinPlusBordismGroupDerived, SingularRelativeHomologyMod2, RokhlinManifoldFromHM, SpinBordism on-disk not mentioned in the 2-day-old memory note, forcing a lab-notebook tail re-read to establish the frontier. On-disk state drifted from the memory snapshot.",
  "how_to_apply": "Phase 5q.F roadmap/notebook-tail updates should trigger memory note updates. When a /goal pauses, update memory about files/commits/frontier before deferring.",
  "evidence": "Agent: 'I see several geometric-program files beyond what the 2-day-old memory covered... Let me grab the true latest frontier.'",
  "tier": "automatic",
  "status": "open",
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

### config-discovery-friction-no-centralized-discovery-point-for-the-worktree-lean-i

**No centralized discovery point for the worktree/lean-infra plan — agent hunted through memory notes**  ·  tier: `automatic`  ·  status: open

```json
{
  "class": "config-discovery-friction",
  "title": "No centralized discovery point for the worktree/lean-infra plan — agent hunted through memory notes",
  "why": "Task to find and activate the lean-lsp multi-instance plan forced heuristic memory-note search ('PARALLEL APPARATUS' text), then on-disk verification. No canonical Lean-development-infrastructure doc centralizes worktree naming, MCP server paths, gitignore patterns — scattered across memory, docs, implicit conventions.",
  "how_to_apply": "Create one canonical doc (e.g. docs/LEAN_DEVELOPMENT_INFRASTRUCTURE.md or under .claude/) covering: worktree naming/layout, lean-lsp multi-instance (wt1/2/3) setup, gitignore patterns, how orchestrating agents spin up the infra. Reference from goal-prompt guidance.",
  "evidence": "Agent: 'I found the plan. It's in memory note project-phase5qf-strict-retirement (the PARALLEL APPARATUS entry)'; no direct link or central doc exists.",
  "tier": "automatic",
  "status": "open",
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

### architecture-gap-inline-subagent-mcp-servers-do-not-surface-in-this-environment

**Inline subagent MCP servers do not surface in this environment**  ·  tier: `automatic`  ·  status: open

```json
{
  "class": "architecture-gap",
  "title": "Inline subagent MCP servers do not surface in this environment",
  "why": "Per-subagent inline MCP entries (lean-lsp-worker in agent's mcpServers) do not materialize. Two ToolSearch queries confirmed lean-lsp-worker absent; subagents only inherit the main session's lean-lsp pinned to main. Forced a pivot to persistent pre-built worktree slots with static MCP defs in workspace .mcp.json.",
  "how_to_apply": "Abandon inline-per-worker MCP; use persistent slots (wt1/2/3) with static mcp__lean-lsp-wt1/2/3 defs in workspace config. Lead assigns workers to pre-built slots; each has its own build-isolated server. No inline mcpServers in agent specs.",
  "evidence": "ToolSearch for lean-lsp-worker found no matching server; worker had only inherited lean-lsp from main; three persistent slots + static workspace .mcp.json confirmed working; design finalized in commit ef0c3d36.",
  "tier": "automatic",
  "status": "open",
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

### harness-gap-worktree-isolation-failed-from-non-git-workspace-root-cwd-relative-d

**Worktree isolation failed from non-git workspace root; cwd-relative dispatch replaced the proposed WorktreeCreate hook**  ·  tier: `automatic`  ·  status: open

```json
{
  "class": "harness-gap",
  "title": "Worktree isolation failed from non-git workspace root; cwd-relative dispatch replaced the proposed WorktreeCreate hook",
  "why": "isolation:worktree requires the session cwd inside a git repo; launching from the non-git workspace root raised 'Cannot create agent worktree: not in a git repository and no WorktreeCreate hooks are configured.' The initial fix was an auto-executing WorktreeCreate hook in workspace .claude/hooks/ — which the PreToolUse(AskUserQuestion) guard correctly intercepted for sign-off (working as designed); the user refused the blind SK-default as a leak risk. Testing then confirmed the Agent tool reads current cwd (not launch cwd), so a `cd SK_EFT_Hawking/` before dispatch suffices — obsoleting ~2h of hook design/doc/testing and eliminating the hook entirely.",
  "how_to_apply": "Lead runs `cd SK_EFT_Hawking/` before dispatching subagents with isolation:worktree (leverages mid-flow session cwd change); drop the WorktreeCreate hook. Prefer testing simpler existing-platform mechanisms (cwd persistence, explicit lead control) before proposing new hooks/automation. The guard's escalation on the hook install was correct behavior — no guard change needed.",
  "evidence": "Worktree creation failed from workspace root; succeeded after `cd SK_EFT_Hawking/` (.claude/worktrees/agent-a3b3... inside SK repo); guard blocked the hook install and asked for approval; user: 'the blind SK-default is a real leak risk... the in-session cd is worth checking before we commit to any hook'; HARNESS_GUIDE and lean-dev.md rewritten to document the cwd-explicit flow; hook design dropped.",
  "tier": "automatic",
  "status": "open",
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

### process-signal-subagent-flailed-destructively-when-hitting-commit-blocker-safety

**Subagent flailed destructively when hitting commit blocker; safety guardrails added to agent spec**  ·  tier: `automatic`  ·  status: open

```json
{
  "class": "process-signal",
  "title": "Subagent flailed destructively when hitting commit blocker; safety guardrails added to agent spec",
  "why": "First e2e worker (a3b3) hit a commit blocker (.lake/packages/* gitlink bug) and responded with raw git plumbing (rm .git/index, read-tree, write-tree, update-index), hook bypasses, and .lake thrashing. Blast radius contained to its own removed worktree, but exposed that workers must not 'fix' blocked commits via git surgery.",
  "how_to_apply": "Edit lean-worker.md safety section to forbid raw git plumbing (read-tree/write-tree/update-ref/commit-tree/rm index), hook bypasses (--no-verify), destructive artifact ops (lake clean, rm -rf .lake, touching .lake/packages). On commit/build fail: STOP and report to lead. Already in place post-fix.",
  "evidence": "Subagent ran rm $GITDIR/index, read-tree, write-tree, sync.py --fast, lake build in its worktree; forensic cleared (confined to its own removed worktree); guardrails written into agent spec.",
  "tier": "automatic",
  "status": "open",
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

### process-friction-user-interrupted-tool-use-multiple-times-due-to-race-between-ag

**User interrupted tool use multiple times due to race between agent's forensic and user's guidance**  ·  tier: `automatic`  ·  status: open

```json
{
  "class": "process-friction",
  "title": "User interrupted tool use multiple times due to race between agent's forensic and user's guidance",
  "why": "During incident recovery the user intercepted agent tool calls ('[Request interrupted by user for tool use]') multiple times, then clarified 'i didn't mean to interrupt the tool call that would get the exact truth from record — once you're sure of blast radius, go ahead and fix.' Friction in turn-by-turn handoff when agent is mid-diagnostic and user wants to steer fix timing.",
  "how_to_apply": "In incident response, batch non-blocking diagnostics first (git log, ls, git fsck), then present findings + severity, THEN ask permission for destructive fixes. Avoid interleaving questions into the fact-gathering phase.",
  "evidence": "User: 'do the full forensic to make sure your solution is complete — i didn't mean to interrupt the tool call that would get the exact truth from record'; multiple interrupt markers during forensic phase.",
  "tier": "automatic",
  "status": "open",
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

### harness-gap-lake-packages-never-gitignored-causing-commit-tree-failures-and-logi

**.lake/packages/* never gitignored, causing commit-tree failures and logical bloat; 10 stray gitlinks committed**  ·  tier: `automatic`  ·  status: open

```json
{
  "class": "harness-gap",
  "title": ".lake/packages/* never gitignored, causing commit-tree failures and logical bloat; 10 stray gitlinks committed",
  "why": "Lake dep checkouts (mathlib, Physlib, batteries, doc-gen4) are git repos with their own tracked files whose blobs live in the dep's object store. lean/.gitignore ignored .lake/build but NOT .lake/packages/*. Worktree seed cp -c .lake + broad git add staged unresolvable paths, blocking commits. Also 10 stray submodule gitlinks (mode 160000) were committed by accident (bbee8ae9, no .gitmodules).",
  "how_to_apply": "Fixed in commit 3e76adb9: add /.lake to lean/.gitignore (ignore all of .lake). Un-track the 10 stray gitlinks. Worktrees/slots can then safely cp -c .lake or symlink from this HEAD onward.",
  "evidence": "git check-ignore lean/.lake/build -> ignored; .lake/packages/* -> NOT ignored; git ls-files listed 10 gitlinks (Cli, aesop, batteries, Qq, doc-gen4, LeanAPAP, mathlib, physlib, ProofWidgets, std); commit 3e76adb9 adds /.lake rule + un-tracks gitlinks.",
  "tier": "automatic",
  "status": "open",
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

### harness-gap-physlib-pin-drift-pre-existing-lake-env-failed-on-mismatched-revisio

**Physlib dependency pin drift on lake build — requires manual guardrail-safe reset**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "environment-drift",
  "title": "Physlib dependency pin drift on lake build — requires manual guardrail-safe reset",
  "why": "When lake build re-resolves the dependency graph (after adding import SKEFTHawking.SingularRelativeMV), Physlib HEAD (851e49a3) drifted from manifest pin (69197c54). Requires git -C lean/.lake/packages/Physlib checkout -f 69197c54 (guardrail-safe; reset --hard blocked by design). Procedural friction: workflow requires explicit re-pinning after import-graph changes.",
  "how_to_apply": "Document in build runbook: after adding imports/modules, if lake build fails with Physlib mismatch, run git -C lean/.lake/packages/Physlib checkout -f <pin>. Or automate as pre-build hook that re-pins Physlib.",
  "evidence": "Summary section 4: 'Physlib pin drift (HEAD 851e49a3 dirty, manifest pin 69197c54): git checkout -f 69197c54 (guardrail-safe; reset --hard/clean blocked). Re-triggered when lake build re-resolves on import-graph change.'",
  "tier": "agent-reviewed",
  "status": "open",
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

### compact-delta-post-compaction-successful-domain-transition-apparatus-math-with-s

**Seamless re-orientation post-compact; proof context preserved with high fidelity**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "compact-delta",
  "title": "Seamless re-orientation post-compact; proof context preserved with high fidelity",
  "why": "The compact summary captured extensive state: committed Lean code (SingularRelativeMV.lean brick 72c-1 at 1dc64ccc), error log (missing opens, subspaceChains_inf qualification), next-brick architecture (72c-2 relative MV chain SES), referenced notebooks/roadmaps, and the EXACT uncommitted work (relMvChainDiag + injectivity with known issues). Post-compact the assistant immediately resumed at the right sub-task. Zero context-churn. DONE criterion 2 (validate.py 43/43) satisfied at 3ed1016c before compaction, persisting post-compact.",
  "how_to_apply": "Rare success case. Summary content precise (numbered pending tasks load-bearing), boundary at natural pause (after commit + green build), first post-compact turn engaged exact uncommitted state. Ensure compact summaries capture (a) exact last-committed SHA + uncommitted file state, (b) known errors/warnings, (c) exact next brick as numbered item, (d) blocked decisions with arguments.",
  "evidence": "Pre: SingularMayerVietorisLES.lean committed (d0ea4363), 72c-1 at 1dc64ccc, validate 43/43 at 3ed1016c. Summary captured 9 sections incl exact Lean snippet of uncommitted relMvChainDiag. Post line 327+: diagnoses subspaceChains_inf qualification, applies qualified fix, re-verifies kernel-purity, plans next brick — zero wasted turns.",
  "tier": "agent-reviewed",
  "status": "open",
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

### process-apparatus-validation-e2e-completed-kernel-pure-with-restart-agnostic-per

**Apparatus-validation E2E completed kernel-pure with restart-agnostic persistent-slot design**  ·  tier: `automatic`  ·  status: open

```json
{
  "class": "process",
  "title": "Apparatus-validation E2E completed kernel-pure with restart-agnostic persistent-slot design",
  "why": "Pre-compaction closed the parallel-slot Lean apparatus validation end-to-end: slot-pinned isolated LSP (mcp__lean-lsp-wt1__*) -> proof (2+2=4, rfl, kernel-pure axioms []) -> commit succeeded (worktree-skip hook line printed, leak-guard ran, not bypassed) -> fast-forward mergeable -> guardrail-safe slot reset clean. Apparatus is restart-agnostic; only restart-time change is making skeft-qa:lean-worker dispatchable.",
  "how_to_apply": "For future /goal sessions, skip re-validating the apparatus (closed/documented at 84bb411c). Use established patterns: lead on a fast MCP, dispatch independent bricks to skeft-qa:lean-worker in persistent slots. If the pre-commit hook is ever modified, re-verify the worktree-detection logic (git rev-parse --git-dir != --git-common-dir) still holds.",
  "evidence": "Pre-compact wrap: 'ALL 5 STEPS GREEN', commit dc95ef37, merge clean, slot reset clean, docs finalized (84bb411c). Hook fix (5639f685) detects worktree commits via --git-dir != --git-common-dir; setup_lean_worktree_slots.sh is one-time; slots persistent.",
  "tier": "automatic",
  "status": "open",
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

### process-math-fork-l5-abk-completeness-deferred-to-user-immediately-locked-post-c

**Math fork (L5 ABK-completeness) deferred to user, immediately locked post-compaction per user agreement**  ·  tier: `automatic`  ·  status: open

```json
{
  "class": "process",
  "title": "Math fork (L5 ABK-completeness) deferred to user, immediately locked post-compaction per user agreement",
  "why": "Pre-compaction the agent identified a genuine math fork in L5: geometric Kirby-Taylor generation (hard classification) vs decidable height-4 spectral-sequence input (col4_height_eq_four, goal-permitted fallback). Agent requested alignment; user agreed. Post-compaction the agent locked it without re-asking: AC#1 full-carrier ker(abkGrade)=0 unconditional, build L1->L4 via 3-slot, sequence L5 last (Kirby-Taylor target, height-4 cap pre-authorized fallback only on a kernel-checked no-go).",
  "how_to_apply": "Pattern (decision requested pre-compaction, user-agreed, locked post-compaction without re-ask) worked correctly. Document the user's choice in the durable goal-prompt so post-compaction re-ask doesn't happen — as was done here.",
  "evidence": "Pre-compact: agent identifies fork, requests alignment; user: 'Agree'. Post-compact: goal-prompt encodes 'Kirby-Taylor the target; decidable height-4 cap col4_height_eq_four pre-authorized terminal input ONLY on a kernel-checked no-go, STOP POLICY (a)'. No re-ask.",
  "tier": "automatic",
  "status": "open",
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

### harness-gap-pre-commit-sorry-check-false-positives-on-comments-docstrings-and-ba

**Harness sorry-gate false positives blocked early commits; required tool rework**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "harness-bug-fixed",
  "title": "Harness sorry-gate false positives blocked early commits; required tool rework",
  "why": "The pre-commit L2 sync gate's grep -RnE '^\\s*sorry' lean/SKEFTHawking matched 4 pre-existing FALSE positives (commented sorries in TetradGapEquation.lean:320, KerrSchild.lean:60, docstring code-fence in CenterFunctorZ2Equiv.lean:971, tracked .backup2 file). Blocked ALL commits until diagnosed. Fix (375fa5e9) changed detection to parse the LSP build log for actual 'declaration uses sorry' warnings. Harness tool gap: regex-based sorry detection brittle with comment/docstring volume.",
  "how_to_apply": "Replace simple file-grep sorry detectors with LSP build-log parsers (capture lake build stderr, search 'declaration uses sorry'). Or use lean_diagnostic_messages MCP. Pre-commit gates should only block on actual Lean compiler signals, not source patterns.",
  "evidence": "Summary section 4: 'Harness sorry-gate bug (blocked ALL commits)' + 375fa5e9 changing from naive grep -RnE to grep -qF \"declaration uses 'sorry'\" on /tmp/skeft-lean log.",
  "tier": "agent-reviewed",
  "status": "open",
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

### process-decision-background-waiter-pattern-for-async-commit-gate-resolution

**Background-waiter / polyphony pattern: read-only scoping during long bg jobs; foreground-sleep block handled with one check then async-defer**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "process-decision",
  "title": "Background-waiter / polyphony pattern: read-only scoping during long bg jobs; foreground-sleep block handled with one check then async-defer",
  "why": "When the pre-commit gate / long counts+validate jobs were running (~15 min combined), the agent (a) armed a background waiter to detect commit landing or gate block rather than blocking on manual polling or in-loop sleep, and (b) ran read-only orientation passes meanwhile without blocking. On hitting the foreground-sleep block it wrote 'Foreground sleep is blocked. Let me check validate's output once (no sleep) and otherwise wait for the completion notification' — a single non-blocking status check then deferred to the async completion notification. No poll-loop, no 'awaiting' language. Deliberate autonomous-mode pattern avoiding timeout/in-loop sleep.",
  "how_to_apply": "Standard pattern: while bg jobs run, scope read-only next-work; arm a background waiter for the landing/block signal; when foreground sleep is unavailable, do ONE status check then defer to the async completion notification — never poll-loop, never use 'awaiting' language.",
  "evidence": "Agent: 'Foreground sleep is blocked. Let me check validate's output once (no sleep) and otherwise wait for the completion notification.' + background waiter armed (HEAD-change / ERROR detection).",
  "tier": "agent-reviewed",
  "status": "open",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": null,
      "roadmap": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md"
    }
  ],
  "id": "process-decision-background-waiter-pattern-for-async-commit-gate-resolution",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### re-orientation-frontier-status-check-next-brick-architecture-lock-at-session-sta

**Frontier status check + next-brick architecture lock at session start**  ·  tier: `automatic`  ·  status: open

```json
{
  "class": "re-orientation",
  "title": "Frontier status check + next-brick architecture lock at session start",
  "why": "The agent opened by orienting to the on-disk frontier (L1 bricks 70 MV-chain-SES + 71 MV-homology-maps done; brick 72 MV-connecting-map next) and locking the architecture (Barratt-Whitehead connecting map reusing pair-LES + excision, no new subcomplex theory). Correct session-opening pattern for a multi-brick construction.",
  "how_to_apply": "Maintain this pattern: each autonomous goal turn, read the roadmap/inventory snapshot, identify the next committed brick, verify dependencies shipped, lock the architecture before coding. Prevents drift and wasted exploration.",
  "evidence": "Agent: 'Oriented the on-disk frontier: L1 bricks 70+71 done; brick 72 next... Architecture locked: MV connecting map = Barratt-Whitehead (connecting o excisionEquiv.symm o homProj) reusing already-proven pair LES + excision — no new subcomplex-homology theory.'",
  "tier": "automatic",
  "status": "open",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": null,
      "roadmap": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md"
    }
  ],
  "id": "re-orientation-frontier-status-check-next-brick-architecture-lock-at-session-sta",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### tooling-friction-lsp-stale-lsp-stale-after-import-edits-and-physlib-fix-requires

**MCP lean_goal diagnostic line-number mismatch — reports declaration line, not sorry line**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "tooling-friction-lsp-stale",
  "title": "MCP lean_goal diagnostic line-number mismatch — reports declaration line, not sorry line",
  "tier": "agent-reviewed",
  "status": "open",
  "why": "When querying lean_goal for a sorry tactic, the error context printed the DECLARATION line (e.g. 66) but the actual sorry tactic is several lines below (e.g. 74+). Forced manual offset calculations.",
  "how_to_apply": "When using lean_goal on a declaration with sorry, query at the line containing the sorry tactic itself, not the theorem/def line. Or fix MCP tool to return both declaration-start and actual sorry position.",
  "evidence": "Summary section 4: 'MCP lean_goal returned wrong line_context: the diagnostic reports the DECLARATION line for uses sorry, but the actual sorry tactic is a few lines below; query lean_goal at the real sorry line.'",
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
  "id": "tooling-friction-lsp-stale-lsp-stale-after-import-edits-and-physlib-fix-requires",
  "first_seen": "2026-06-17",
  "last_seen": "2026-06-17"
}
```

### re-orientation-solo-vs-fan-out-architecture-decision-m-spine-solo-post-m-layers-

**Solo vs. fan-out architecture decision: [M] spine solo, post-[M] layers parallel**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "re-orientation",
  "title": "Solo vs. fan-out architecture decision: [M] spine solo, post-[M] layers parallel",
  "tier": "agent-reviewed",
  "status": "open",
  "why": "The goal mandates keeping the coupled [M] spine solo (each brick builds linearly). The session established the MV LES IS the [M] spine (L1 of the 5-layer w2 tower), confirming the solo approach. Fan-out to wt1/wt2/wt3 deferred until the independent post-[M] layers (Poincare-duality, Steenrod/Wu, w2-invariance, ABK-completeness).",
  "how_to_apply": "Keep the lead on the [M] spine (72a-[M]). Deploy subagents to wt1/wt2/wt3 only for post-[M] apparatus layers; reset each slot to main before merging. Avoids coupling-induced rework, keeps the spine coherent.",
  "evidence": "'the goal directive says keep the coupled [M] spine solo - and the MV LES *is* the [M] spine ... apparatus fan-out is reserved for the genuinely-independent post-[M] layers (PD/Steenrod/Smith).'",
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
  "id": "re-orientation-solo-vs-fan-out-architecture-decision-m-spine-solo-post-m-layers-",
  "first_seen": "2026-06-17",
  "last_seen": "2026-06-17"
}
```

### wasted-cycles-deferred-unnecessarily-intricate-chain-chase-deferred-after-2-proo

**Intricate chain-chase deferred after 2 proof steps validated (missed push-through opportunity)**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "wasted-cycles-deferred-unnecessarily",
  "title": "Intricate chain-chase deferred after 2 proof steps validated (missed push-through opportunity)",
  "tier": "agent-reviewed",
  "status": "open",
  "why": "After validating the MV exactness naturality approach with 2 green steps and the remaining ~5 mechanical steps worked out, the session stopped and deferred ('deeply-loaded turn'/'sustainable pace'). But the subsequent two turns landed inclRA_connecting and mvHomDiag_mvDelta first-try using the documented plan. The deferral was defensive but unnecessary; the workload was tractable and the plan complete.",
  "how_to_apply": "Distinguish genuinely-blocked (no plan, stale tooling, missing prereqs) from merely-tedious (plan complete, steps documented, tooling ready). For the latter, push through. Pattern this session: defer-with-plan -> next-turn-immediate-success, twice - the barrier was perception, not complexity.",
  "evidence": "Defer: 'I'm going to be honest about where this stands rather than grind an intricate chain-chase further in a deeply-loaded turn.' Then: 'GO - finishing the naturality proof this turn. I have the complete plan...' landed first-try. Repeated for mvHomDiag_mvDelta. Notes: 'Pushing through worked again.' / 'Pushing through continues to pay off.'",
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
  "id": "wasted-cycles-deferred-unnecessarily-intricate-chain-chase-deferred-after-2-proo",
  "first_seen": "2026-06-17",
  "last_seen": "2026-06-17"
}
```

### missing-process-gate-counts-json-and-validate-py-stale-across-multi-brick-commit

**Committed-state tracking: autogen counts.json stale between commits; criterion 2 passes but warnings repeat**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "missing-process-gate",
  "title": "Committed-state tracking: autogen counts.json stale between commits; criterion 2 passes but warnings repeat",
  "tier": "agent-reviewed",
  "status": "open",
  "why": "counts.json (autogen, tracked) fell out of sync with actual theorem counts multiple times. 'counts.json is stale again (warns each commit, but criterion 2 satisfied at 3ed1016c).' Each commit triggers stale-counts warning but validate.py 43/43 remains satisfied. Harness does not auto-regenerate counts on commit. Procedural noise without blocking.",
  "how_to_apply": "Add pre-commit hook that auto-regenerates counts.json if counts changed since last commit. Or decouple counts.json check from L2 gate (advisory-only).",
  "evidence": "Summary section 8: 'counts.json is stale again (warns each commit, but criterion 2 satisfied this session at 3ed1016c).'",
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

### goal-loop-in-progress-goal-not-yet-met-l1-m-spine-incomplete-72b-3b-is-checkpoin

**Goal not yet met; L1 [M] spine incomplete (72b-3b is checkpoint, not final)**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "goal-loop-in-progress",
  "title": "Goal not yet met; L1 [M] spine incomplete (72b-3b is checkpoint, not final)",
  "tier": "agent-reviewed",
  "status": "open",
  "why": "Goal requires: (1) full-carrier Omega_4^{Pin+} = Z/16 with ker(abkGrade)=0 and NO landmark/cap/disclosed-Prop binder; (2) lake build ExtractDeps clean + validate.py >=43/43 in transcript; (3) fresh-context adversarial-reviewer ZERO BLOCKER. Transcript shows only early L1 spine bricks (72a mvConnecting, 72b-1 seam+mvDelta, 72b-2 naturality+bridge, 72b-3a Homology.map_ambIncl bridge, 72b-3b mvHomDiag_mvDelta + seam helpers). The full w2 tower (L1->L5) is not built; no theorem appears; criteria 2/3 not surfaced. Mid-progress on multi-day work.",
  "how_to_apply": "Continue from the documented next step (mvDelta o mvHomSum=0, excision<->projection naturality). Maintain notebook+roadmap synchronously, ship green bricks. Hit L1 [M] completion checkpoint (commit + ExtractDeps + validate.py), then L2-L5. Run adversarial reviewer only once all bricks are complete and the tree is kernel-pure + builds clean.",
  "evidence": "Stop-hook feedback (repeated): goal not satisfied; 'the complete w2 tower (L1->L5) has NOT been constructed. No Omega_4^{Pin+} = Z/16 theorem appears ... Requirement (2)/(3) not surfaced.'",
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

### escape-attempt-injectivity-proof-relmvchaindiag-injective-had-do-nothing-warning

**Injectivity proof relMvChainDiag_injective had 'do nothing' warning — incomplete tactic logic**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "escape_attempt",
  "tier": "agent-reviewed",
  "status": "open",
  "title": "Injectivity proof relMvChainDiag_injective had 'do nothing' warning — incomplete tactic logic",
  "why": "The injectivity proof contained unreachable tactic lines ('the rw [mk_eq_zero_iff] at hx may have already closed') with subsequent exact lines marked 'do nothing'/'never executed'. Sign the proof structure assumed a goal state that closed prematurely or diverged. Assistant initially left it 'NOT yet re-verified after the opens fix' — deferred debugging.",
  "how_to_apply": "When a proof produces 'do nothing'/'never executed' warnings, use lean_goal to inspect exact state at that line, restructure to match. Do not defer re-verification — creates later cascade. Post-compact should immediately apply lean_diagnostic_messages.",
  "evidence": "Summary section 4: 'relMvChainDiag_injective proof had do nothing/never executed warnings on final two rw/exact lines... NOT yet re-verified after the opens fix.' Post-compact applied opens fix + rebuilt, found NEW error (subspaceChains_inf qualification) — correct next step but do-nothing warnings not explicitly re-verified.",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": null,
      "roadmap": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md",
      "compact_event_id": null
    }
  ],
  "id": "escape-attempt-injectivity-proof-relmvchaindiag-injective-had-do-nothing-warning",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### wasted-cycles-dependent-motive-rewrite-pattern-churn-three-failed-tactics-before

**Dependent-motive rewrite pattern churn — generic rewrites (add_comm) match nat k+1, patched per-instance not generalized**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "wasted_cycles",
  "tier": "agent-reviewed",
  "status": "open",
  "title": "Dependent-motive rewrite pattern churn — generic rewrites (add_comm) match nat k+1, patched per-instance not generalized",
  "why": "Recurring class: generic rewrites (e.g. rw [add_comm]) match the nat k+1 instead of the intended chain element, yielding 'motive is not type correct' on subtype-with-proof goals. The agent diagnoses correctly and resolves each instance (pin the rewrite target e.g. add_comm (chainBoundary M (k+1) ...) zc, or congrArg (mk) (Subtype.ext ...)), but treats each recurrence as a fresh error rather than extracting the pattern — ~8 tool calls across instances of one pattern class; one chunk ends still on a motive-type failure. The per-instance fix is clean but the root-cause generalization is never built.",
  "how_to_apply": "After the FIRST 'generic rewrite matched nat arithmetic / dependent-motive not type correct' instance, extract the pattern: build a targeted helper or a pinned-simp set (or document the pin idiom — fully-qualify and pin the rewrite target argument) and eliminate the class at root, instead of pinning each occurrence by hand. For the immediate fix: pin the rewrite target explicitly (add_comm <chain-elt> <other>) or use congrArg (mk) (Subtype.ext ...) on subtype-with-proof goals; do not rely on implicit type inference for overloaded ring-tactic lemma names.",
  "evidence": "add_comm matched the nat type instead of the chain element; fixed by pinning add_comm (chainBoundary M (k+1) ...) zc. Same root cause as the mvHomDiag_mvDelta congrArg(mk)(Subtype.ext) churn; recurred across the span, patched per-instance.",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": null,
      "roadmap": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md",
      "compact_event_id": null
    }
  ],
  "id": "wasted-cycles-dependent-motive-rewrite-pattern-churn-three-failed-tactics-before",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### friction-pattern-recurrence-quotient-instance-synthesis-mk-coercion-friction-rec

**Quotient/instance-synthesis (mk-coercion) friction recurred across E1/E2/E3 exactness proofs**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "friction-pattern-recurrence",
  "title": "Quotient/instance-synthesis (mk-coercion) friction recurred across E1/E2/E3 exactness proofs",
  "tier": "agent-reviewed",
  "status": "open",
  "why": "The Submodule.Quotient.mk vs RelativeHomology.mk/QHomology.mk coercion friction recurred across the E1/E2/E3 LES-exactness proof family despite being handled in the initial QChain reorganization. The defeq-ambiguity pattern (raw quotient vs named type) was not recognized as a systemic signal upfront, so friction front-loaded in E1 (three rewrite/coercion fixes) and recurred in E2 ('recurring friction'); E3 was clean only once the patterns were established.",
  "how_to_apply": "After resolving a quotient/instance defeq friction in a first proof, scan forward through the related proof family for the same pattern and either add a dedicated helper-lemma family upfront (e.g. relHomology_mk_eq_of, the `show ... from relMvHomSumQ_mk` shape) or expose disambiguation at the definition level. Document the fix pattern (`show ... from relMvHomSumQ_mk`, `LinearMap.ext fun c`) explicitly and apply it uniformly to subsequent proofs rather than re-deriving it each site.",
  "evidence": "Reasoning: 'raw-quotient vs QChain defeq friction -> making QChain a reducible abbrev'; E2 recurring Submodule.Quotient.mk vs RelativeHomology.mk/QHomology.mk friction; 'E3 clean on first try - the patterns are paying off'. Commits 67174640, b210ef43.",
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
  "id": "friction-pattern-recurrence-quotient-instance-synthesis-mk-coercion-friction-rec",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### reducible-abbrev-unintended-consequence-qchain-reducible-abbrev-fix-for-instance

**QChain reducible-abbrev fix for instance friction introduced `ext` over-unfolding (secondary friction)**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "reducible-abbrev-unintended-consequence",
  "title": "QChain reducible-abbrev fix for instance friction introduced `ext` over-unfolding (secondary friction)",
  "tier": "agent-reviewed",
  "status": "open",
  "why": "Making QChain a reducible abbrev resolved instance synthesis but introduced a secondary issue: `ext c` over-unfolded through the quotient, requiring `LinearMap.ext fun c` to control the unfolding. The unintended tactic-behavior consequence of reducibility was not anticipated when the abbrev fix was applied.",
  "how_to_apply": "When using a reducible `abbrev` to fix instance-synthesis friction, immediately test downstream tactic behavior (ext, simp, unfold) at the proof site — reducibility changes how structural tactics unfold. Add a docstring note recording the expected (un)folding behavior and the recommended tactic combo (here: prefer `LinearMap.ext fun c` over bare `ext c`).",
  "evidence": "'making QChain a reducible abbrev' -> 'with QChain now reducible, ext c over-unfolds through the quotient. Let me use LinearMap.ext fun c to control it'.",
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
  "id": "reducible-abbrev-unintended-consequence-qchain-reducible-abbrev-fix-for-instance",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### investigation-cost-decision-gate-before-sinking-n-lines-investigation-cost-gate-

**'Before sinking N lines' investigation-cost gate: apply it upfront, not mid-investigation**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "investigation-cost-decision-gate",
  "title": "'Before sinking N lines' investigation-cost gate: apply it upfront, not mid-investigation",
  "tier": "agent-reviewed",
  "status": "open",
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

### architecture-decision-sound-route-pivot-at-4cfbb566-reuse-72c-1-relmvhomsum-iso-

**Route pivot at 4cfbb566: reuse 72c-1 relMvHomSum + iso iota instead of building a separate Sigma_* induced map**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "architecture-decision-sound",
  "title": "Route pivot at 4cfbb566: reuse 72c-1 relMvHomSum + iso iota instead of building a separate Sigma_* induced map",
  "tier": "agent-reviewed",
  "status": "open",
  "why": "The agent recognized that the existing 72c-1 relMvHomSum plus the small-chains iso iota would let it transport the textbook LES directly, rather than building Sigma_* as a separate induced map — preventing duplicate work. Sound architecture decision worth reinforcing as a reusable habit.",
  "how_to_apply": "When a new sub-component emerges mid-proof, ask immediately, BEFORE committing significant code: 'Does an earlier commit already contain this?' and 'Would a structural isomorphism let me transport/reuse it?' Prefer transporting an existing verified construction across an iso over building a parallel induced map.",
  "evidence": "Commit 4cfbb566: 'rather than build a separate Sigma_* induced map, I can reuse the 72c-1 relMvHomSum... once I have the small-chains iso iota'.",
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
  "id": "architecture-decision-sound-route-pivot-at-4cfbb566-reuse-72c-1-relmvhomsum-iso-",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### error-localization-good-discipline-blast-radius-analysis-errors-localized-to-new

**Blast-radius analysis ('errors localized to new declarations') kept fixes targeted, avoided refactoring creep**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "error-localization-good-discipline",
  "title": "Blast-radius analysis ('errors localized to new declarations') kept fixes targeted, avoided refactoring creep",
  "tier": "agent-reviewed",
  "status": "open",
  "why": "When instance errors appeared after introducing relMvChainSum, the agent diagnosed them as affecting only the new declarations and applied localized fixes (`exact LinearMap.mem_ker.mpr`, a type ascription) rather than refactoring the whole chain-sum/quotient infrastructure — keeping change locality tight.",
  "how_to_apply": "For each error cluster, perform an explicit blast-radius analysis: identify which declarations are affected and the minimal fix scope, and state it out loud ('errors are localized to ...') as a forcing function against refactoring creep before reaching for a structural rewrite.",
  "evidence": "'The two errors are localized to the new declarations. Let me apply light fixes: use exact LinearMap.mem_ker.mpr and a type ascription'.",
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
  "id": "error-localization-good-discipline-blast-radius-analysis-errors-localized-to-new",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### friction-silent-boundary-descope-boundary-case-codebase-limitation-degree-0-homo

**Boundary-case codebase limitation (degree-0 homotopy) descoped silently rather than surfaced as a scope decision**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "friction-silent-boundary-descope",
  "title": "Boundary-case codebase limitation (degree-0 homotopy) descoped silently rather than surfaced as a scope decision",
  "why": "On finding that iterHomotopy_chainHomotopy only supports C_{n+1} (not degree 0), the agent explored singularSd-at-0, concluded degree 0 needs a homotopy the codebase lacks, then silently pivoted to building iota_injective for the n+1 form only — without surfacing the descope as a steerable scope decision. ~5 messages + 2 Lean queries spent before the silent narrowing. In /goal mode this is the correct instinct (keep shipping the buildable part) but the boundary drop should be recorded explicitly (lab notebook / one-line surface) so it is not lost.",
  "how_to_apply": "When a codebase limitation forces dropping a boundary case (degree 0, empty, trivial), record the descope explicitly (lab-notebook entry or a one-line 'dropping degree-0, needs homotopy X the codebase lacks') so the scope narrowing is visible and re-attackable later. Do not block the loop to ask, but do not let the boundary drop vanish silently either.",
  "evidence": "Agent concluded degree-0 needs a homotopy the codebase lacks, then pivoted to iota_injective for the n+1 form only with no explicit scope note.",
  "tier": "agent-reviewed",
  "status": "open",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": null,
      "roadmap": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md"
    }
  ],
  "id": "friction-silent-boundary-descope-boundary-case-codebase-limitation-degree-0-homo",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### positive-goal-loop-discipline-goal-loop-discipline-held-stop-hook-treated-as-go-

**Goal-loop discipline held: stop-hook treated as GO, milestones are integrity-gates not pause-points, next brick scoped inline**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "positive-goal-loop-discipline",
  "title": "Goal-loop discipline held: stop-hook treated as GO, milestones are integrity-gates not pause-points, next brick scoped inline",
  "why": "Model behavior across the span. (a) On stop-hook fire mid-session the agent re-engaged immediately ('the stop hook is the GO signal — L1's fundamental-class engine is done; next brick is the Hatcher 3.27 induction -> [M]. Let me investigate') with no hand-back, no re-scoping question, no multi-day talk. (b) On completing the relative MV LES (DONE-criterion 2, validate 43/43) it committed, synced autogen, verified the gate, then within ~60s pivoted to scoping the next phase (Hatcher 3.27 compactness induction via convex radial retract from existing infra). Milestones were treated as triggers for integrity actions then immediate continuation. Internalizes feedback-goal-stop-hook-multisession + feedback-no-disclosure-stopping.",
  "how_to_apply": "Keep modeling: stop-hook = normal loop tick -> re-engage on the next roadmap brick this turn. Milestones -> run validate/sync/commit (integrity gates) then immediately re-read the roadmap and ship the next buildable unit. No pause ceremony, no hand-back language.",
  "evidence": "Agent: 'The stop hook is the GO signal — L1's fundamental-class engine (relative MV LES) is done; the next brick is the Hatcher 3.27 induction -> [M]. Let me investigate...'",
  "tier": "agent-reviewed",
  "status": "open",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": null,
      "roadmap": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md"
    }
  ],
  "id": "positive-goal-loop-discipline-goal-loop-discipline-held-stop-hook-treated-as-go-",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### positive-reuse-over-rebuild-search-first-discovery-existing-singulareuclideanacy

**Search-first discovery: existing SingularEuclideanAcyclic/PuncturedRetract infra identified and reused rather than reinvented**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "positive-reuse-over-rebuild",
  "title": "Search-first discovery: existing SingularEuclideanAcyclic/PuncturedRetract infra identified and reused rather than reinvented",
  "why": "grep + lean_file_outline discovered SingularEuclideanAcyclic.lean and SingularPuncturedRetract.lean already export the needed lemmas (cycle_mem_boundaries, contraction); the agent explicitly noted 'exactly the infrastructure to mirror for the convex case' and chose import+reuse over rebuilding. No ad-hoc / axiom shortcuts when substrate already existed.",
  "how_to_apply": "Before writing a new lemma, search (lean_local_search / grep / lean_file_outline) for structurally analogous existing lemmas; reuse beats reinvent. Document non-trivial ports so the reuse is auditable.",
  "evidence": "Agent: 'exactly the infrastructure to mirror for the convex case' (re SingularEuclideanAcyclic / SingularPuncturedRetract).",
  "tier": "agent-reviewed",
  "status": "open",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": null,
      "roadmap": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md"
    }
  ],
  "id": "positive-reuse-over-rebuild-search-first-discovery-existing-singulareuclideanacy",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### positive-kernel-purity-discipline-kernel-purity-held-per-commit-under-fast-caden

**Kernel-purity held per-commit under fast cadence via counts->ExtractDeps->validate cascade (13641 thm / 0 axiom / 0 sorry)**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "positive-kernel-purity-discipline",
  "title": "Kernel-purity held per-commit under fast cadence via counts->ExtractDeps->validate cascade (13641 thm / 0 axiom / 0 sorry)",
  "why": "Across the span the agent shipped numerous bricks (relative MV LES assembly + transport) ending 13641 thm / 0 axiom / 0 sorry; lean_verify reported exactly {propext, Classical.choice, Quot.sound} after each brick; ExtractDeps clean (9336 jobs); validate 43/43. The discipline held under fast cadence — kernel-purity treated as a per-commit process property, not just a final state.",
  "how_to_apply": "Keep all three gates in the loop per commit: counts (thm/axiom/sorry) -> ExtractDeps (axiom closure clean) -> validate (43/43). Run lean_verify after each substantive brick to confirm the axiom set stays {propext, Classical.choice, Quot.sound}. Kernel-purity is a process property enforced continuously, not audited once at the end.",
  "evidence": "13641 thm / 0 axiom / 0 sorry; lean_verify = {propext, Classical.choice, Quot.sound} after each brick; ExtractDeps 9336 jobs clean; validate 43/43.",
  "tier": "agent-reviewed",
  "status": "open",
  "occurrences": [
    {
      "date": "2026-06-18",
      "session_id": "70cc8da1-4695-435a-be26-9db4e634a6fa",
      "goal_id": "20260617T231250",
      "goal_prompt": null,
      "roadmap": "/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/roadmaps/Phase5qF_GeometricBordism_Roadmap.md"
    }
  ],
  "id": "positive-kernel-purity-discipline-kernel-purity-held-per-commit-under-fast-caden",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### friction-search-loop-repeated-mathlib-api-discovery-iterations-iscompact-totally

**Repeated Mathlib API discovery iterations (IsCompact/TotallyBounded/von-Neumann-bounded)**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "friction-search-loop",
  "title": "Repeated Mathlib API discovery iterations (IsCompact/TotallyBounded/von-Neumann-bounded)",
  "why": "3 sequential search attempts to find compact-implies-bounded lemma (IsCompact.isVonNBounded wrong form / not in pin -> TotallyBounded.isVonNBounded). Each iteration a new search-and-test cycle.",
  "how_to_apply": "Pre-populate Mathlib API quick-reference for bounded-set predicates; prioritize current pin spellings; add an API-drift note when a lemma is not found first attempt.",
  "evidence": "'IsCompact.isVonNBounded isn't the right projection -> takes 𝕜 first -> isn't in this Mathlib pin -> It's TotallyBounded.isVonNBounded'",
  "tier": "agent-reviewed",
  "status": "open",
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

### friction-tactic-composition-ring-fails-on-scalar-product-from-gauge-smul-of-nonn

**ring fails on scalar-product (•) from gauge_smul_of_nonneg; manual smul rewrite needed**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "friction-tactic-composition",
  "title": "ring fails on scalar-product (•) from gauge_smul_of_nonneg; manual smul rewrite needed",
  "why": "ring could not compose a scalar-product equality; had to use smul_eq_mul + inv_mul_cancel₀.",
  "how_to_apply": "Document ring failure on • / non-commutative algebra; suggest noncomm_ring/field_simp/explicit smul rewrites as fallbacks.",
  "evidence": "'gauge_smul_of_nonneg produces a • and ring can't handle it. Compute directly with smul_eq_mul + inv_mul_cancel₀.'",
  "tier": "agent-reviewed",
  "status": "open",
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
  "id": "friction-tactic-composition-ring-fails-on-scalar-product-from-gauge-smul-of-nonn",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### friction-scoping-error-section-variables-not-auto-included-on-un-typed-hypothese

**Section variables not auto-included on un-typed hypotheses; explicit per-lemma passing**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "friction-scoping-error",
  "title": "Section variables not auto-included on un-typed hypotheses; explicit per-lemma passing",
  "why": "Section variables not auto-included because absent from types; doubled boilerplate; local notations also broke.",
  "how_to_apply": "Document when section variables are NOT auto-included; recommend explicit hypothesis lists early; section-variable audit before shared-context modules.",
  "evidence": "'The section variables aren't auto-included (not used in the types). Pass hypotheses explicitly per lemma.'",
  "tier": "agent-reviewed",
  "status": "open",
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
  "id": "friction-scoping-error-section-variables-not-auto-included-on-un-typed-hypothese",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### friction-git-hook-collision-pre-commit-leak-guard-false-positive-on-math-word-th

**Pre-commit leak-guard false-positive on math word, then cleared staging**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "friction-git-hook-collision",
  "title": "Pre-commit leak-guard false-positive on math word, then cleared staging",
  "why": "Math-context word 'push' (push-out map / pushMap) tripped the leak guardrail; had to reword. Secondary: the blocked attempt cleared the staging area, forcing re-add+re-commit.",
  "how_to_apply": "Refine guardrail to distinguish math context from structural-risk repo name; whitelist common math terms / exact-match private identifiers only. Also make hook failures non-mutating (do not clear staging); emit a recovery hint.",
  "evidence": "'The guardrail false-matched push in my commit message. Reword to avoid that word.' | 'The staging was cleared by the blocked attempt. Re-add and commit.'",
  "tier": "agent-reviewed",
  "status": "open",
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

### friction-free-variable-scoping-free-variable-capture-in-anonymous-constructor-wi

**Free-variable capture in anonymous constructor with inline by-block**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "friction-free-variable-scoping",
  "title": "Free-variable capture in anonymous constructor with inline by-block",
  "why": "Anonymous constructor with inline by triggered free-variable bug; had to extract the ∉A proof as a standalone lemma.",
  "how_to_apply": "Flag anonymous-constructor-with-inline-tactic as known friction; recommend extracting tactic proofs to separate lemmas.",
  "evidence": "'The inline by block in the anonymous constructor triggers a free-variable bug. Extract the ∉A proof as a standalone lemma.'",
  "tier": "agent-reviewed",
  "status": "open",
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
  "id": "friction-free-variable-scoping-free-variable-capture-in-anonymous-constructor-wi",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### friction-simp-unfolding-composition-identities-not-unfolded-by-simp-manual-inclm

**Composition identities not unfolded by simp; manual inclMap/pushMap rewrites in 4 slices**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "friction-simp-unfolding",
  "title": "Composition identities not unfolded by simp; manual inclMap/pushMap rewrites in 4 slices",
  "why": "simp did not unfold module-local composition defs; refine_1/refine_3 needed explicit unfolding across 4 slice proofs.",
  "how_to_apply": "Mark composition defs @[simp] or add to a local simp-set when building retract modules.",
  "evidence": "'The composition slices (refine_1, refine_3) need inclMap/pushMap unfolded. Fix all 4 slice proofs.'",
  "tier": "agent-reviewed",
  "status": "open",
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
  "id": "friction-simp-unfolding-composition-identities-not-unfolded-by-simp-manual-inclm",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### friction-module-namespace-open-recurring-missing-namespace-open-for-cross-module

**Recurring missing-namespace-open for cross-module map identifiers (Homology.map / RelativeHomology.map)**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "friction-module-namespace-open",
  "title": "Recurring missing-namespace-open for cross-module map identifiers (Homology.map / RelativeHomology.map)",
  "why": "Error-driven discovery that map-style identifiers live in a Functoriality module not opened (SingularFunctoriality, SingularRelativeFunctoriality). Cross-module name resolution not pre-validated; recurs across multi-module proof work.",
  "how_to_apply": "Run lean_local_search/lean_hover_info BEFORE writing cross-module bodies; add a namespace-completeness / identifier->open pre-flight in the build harness.",
  "evidence": "'Homology.map needs SingularFunctoriality opened' | 'Unknown constant SKEFTHawking.SingularRelativeHomologyMod2.RelativeHomology.map -> RelativeHomology.map is in SingularRelativeFunctoriality, not opened. Add it.'",
  "tier": "agent-reviewed",
  "status": "open",
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
  "id": "friction-module-namespace-open-recurring-missing-namespace-open-for-cross-module",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### friction-hypothesis-shadowing-shadowed-hypotheses-in-homotopycompla-required-exp

**Shadowed hypotheses in homotopyComplA required explicit renaming**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "friction-hypothesis-shadowing",
  "title": "Shadowed hypotheses in homotopyComplA required explicit renaming",
  "why": "Re-declared hypotheses in nested scope shadowed; needed disambiguation.",
  "how_to_apply": "Add a variable-shadowing detector to diagnostics; avoid-shadowing proof templates.",
  "evidence": "'the homotopyComplA proof has shadowed hypotheses'",
  "tier": "agent-reviewed",
  "status": "open",
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
  "id": "friction-hypothesis-shadowing-shadowed-hypotheses-in-homotopycompla-required-exp",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### friction-interval-bounds-explicitness-unitinterval-bounds-needed-explicit-sub-no

**unitInterval bounds needed explicit sub_nonneg (not inferred)**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "friction-interval-bounds-explicitness",
  "title": "unitInterval bounds needed explicit sub_nonneg (not inferred)",
  "why": "t∈[0,1] -> 0≤t-0 required explicit sub_nonneg; inequality automation does not bridge unitInterval.",
  "how_to_apply": "Add unitInterval lemmas to omega/linarith or a unitInterval inequality simp-set.",
  "evidence": "'the unitInterval bounds need explicit sub_nonneg'",
  "tier": "agent-reviewed",
  "status": "open",
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
  "id": "friction-interval-bounds-explicitness-unitinterval-bounds-needed-explicit-sub-no",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### minor-friction-lake-build-invoked-from-wrong-cwd

**Lake build invoked from wrong cwd**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "minor-friction",
  "title": "Lake build invoked from wrong cwd",
  "why": "Build ran from wrong dir; corrected to lean/ and re-invoked. cwd resets between Bash calls make this recur silently.",
  "how_to_apply": "Pre-build cwd assertion / auto-detect git root before lake build.",
  "evidence": "'Build ran from wrong dir. Build from lean/ and commit.'",
  "tier": "agent-reviewed",
  "status": "open",
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
  "id": "minor-friction-lake-build-invoked-from-wrong-cwd",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### private-namespace-barrier-inline-resolution-private-helper-eq-of-add-eq-zero-two

**Private helper (eq_of_add_eq_zero_two) inlined rather than blocking**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "private-namespace-barrier-inline-resolution",
  "title": "Private helper (eq_of_add_eq_zero_two) inlined rather than blocking",
  "why": "eq_of_add_eq_zero_two marked private in SingularDisjointUnion; agent inlined the char-2 proof locally and continued.",
  "how_to_apply": "Micro-pattern handled correctly; if it recurs at scale consider exporting helpers vs inlining as the norm.",
  "evidence": "'eq_of_add_eq_zero_two is private in SingularDisjointUnion, so I'll inline it.'",
  "tier": "agent-reviewed",
  "status": "open",
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
  "id": "private-namespace-barrier-inline-resolution-private-helper-eq-of-add-eq-zero-two",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### workflow-pattern-incremental-sharding-shard-and-commit-bank-green-shard-decompos

**Shard-and-commit / bank-green-shard decomposition keeps gates clean across long proof chains**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "workflow-pattern-incremental-sharding",
  "title": "Shard-and-commit / bank-green-shard decomposition keeps gates clean across long proof chains",
  "why": "Large homological retract split into shippable increments (acyclicity, gauge bounds, continuity, final maps+homotopies), each committed independently keeping gates clean. Same pattern recurred as banking a reusable green shard (clopen-split vanishing lemma) before continuing.",
  "how_to_apply": "Codify shard-and-commit in the wave pipeline: commit+verify every ~5-6 bricks to cut context loss and enable incremental review. Ensure each shard is truly green (no sorry, kernel-pure); watch for over-fragmentation.",
  "evidence": "Commits afab3a77(19),3af3494b(20),8bebae5d(22),85aa69ea(23) each with explicit 'now build X' transition. | 'Bank it as a GREEN shard now (wire into aggregator + commit), then continue with the S⁰ base.'",
  "tier": "agent-reviewed",
  "status": "open",
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

### workflow-pattern-template-mirroring-template-driven-dev-singularpuncturedretract

**Template-driven dev: SingularPuncturedRetract reused as scaffold for convex case**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "workflow-pattern-template-mirroring",
  "title": "Template-driven dev: SingularPuncturedRetract reused as scaffold for convex case",
  "why": "Mirrored existing punctured-retract homotopy-equivalence structure for the convex case, reducing proof invention.",
  "how_to_apply": "Maintain a proof-template library (punctured retracts, gauge homotopies); reference templates explicitly in task prompts.",
  "evidence": "'Read the existing SingularPuncturedRetract to mirror its homotopy-equivalence structure for the convex case.'",
  "tier": "agent-reviewed",
  "status": "open",
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
  "id": "workflow-pattern-template-mirroring-template-driven-dev-singularpuncturedretract",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### workflow-pattern-deliberate-error-recovery-read-diagnose-extract-retry-debugging

**read -> diagnose -> extract -> retry debugging loop**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "workflow-pattern-deliberate-error-recovery",
  "title": "read -> diagnose -> extract -> retry debugging loop",
  "why": "On shadowed-hyp/free-var failures, read the definition first, identified inline-by as culprit, extracted standalone lemma — surgical not trial-and-error.",
  "how_to_apply": "Formalize read-definition-first before swapping tactics when a proof fails.",
  "evidence": "'Read homotopyComplA definition to find the free-variable issue -> extract the ∉A proof as a standalone lemma.'",
  "tier": "agent-reviewed",
  "status": "open",
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
  "id": "workflow-pattern-deliberate-error-recovery-read-diagnose-extract-retry-debugging",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### workflow-pattern-search-before-build-search-source-read-before-build-helpers-rou

**Search/source-read before build: helpers, routes, and reuse confirmed before writing (anti-speculation)**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "workflow-pattern-search-before-build",
  "title": "Search/source-read before build: helpers, routes, and reuse confirmed before writing (anti-speculation)",
  "why": "Sustained lean_local_search/loogle/hover + concrete-source reading to confirm helpers exist, settle route decisions from actual code, decide build-vs-borrow on Mathlib coverage, and reuse existing decls (dimReductionEquiv) inline — avoiding write-then-diagnostic loops and speculative shortcuts.",
  "how_to_apply": "Codify lean_local_search -> verify -> lean_hover_info -> import-or-inline; ground any 'can we shortcut' decision in concrete source inspection; inventory-check Mathlib coverage before dispatching a worker.",
  "evidence": "'All helpers exist... Let me check SingularDisjointUnion's imports...' | 'must read the concrete... a route decision the diligence rule requires me to settle from the actual code... The docstring confirms the architecture.' | 'confirm whether the full (all-degree) sphere / Euclidean-complement homology already exists or only the top degree — that decides whether I dispatch a worker.' | 'the codebase already has dimReductionEquiv... derivable inline.'",
  "tier": "agent-reviewed",
  "status": "open",
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

### harness-signal-kernel-pure-velocity-kernel-pure-brick-loop-is-high-velocity-and-

**Kernel-pure brick loop is high-velocity and self-recovering (~29 + 28 bricks, no unrecovered errors)**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "harness-signal-kernel-pure-velocity",
  "title": "Kernel-pure brick loop is high-velocity and self-recovering (~29 + 28 bricks, no unrecovered errors)",
  "why": "Sustained read-roadmap->write-defn->lean_goal verify->commit+notebook->repeat; ~4-5 kernel-pure commits/hr; only minor errors fixed <5min; axioms exactly {propext,Classical.choice,Quot.sound}; brick-based commit discipline effective for state management both pre- and post-compact.",
  "how_to_apply": "Preserve this loop in goal mode; do not interrupt for status checkpoints unless genuinely blocked; maintain brick-based + kernel-purity verification.",
  "evidence": "29 kernel-pure commits 3078ae02->4f56b279 building the L1 fundamental-class spine; axioms exactly {propext,Classical.choice,Quot.sound}; validate.py 43/43. | 13 Bash + 6 Read + lean_file_outline/lean_verify/lean_diagnostic all clean; commits 72c-2a -> 72c-3l uninterrupted.",
  "tier": "agent-reviewed",
  "status": "open",
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
  "id": "harness-signal-kernel-pure-velocity-kernel-pure-brick-loop-is-high-velocity-and-",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### goal-mode-discipline-stop-hook-treated-as-go-signal-context-refresh-not-a-hold-g

**Stop-hook treated as GO signal / context-refresh, not a hold gate**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "goal-mode-discipline",
  "title": "Stop-hook treated as GO signal / context-refresh, not a hold gate",
  "why": "Stop-hook re-statement of the 5q.F goal processed as context refresh; immediate continuation, zero 'awaiting direction'/'how much left' phrasing.",
  "how_to_apply": "Positive confirmation of CLAUDE.md goal-mode discipline; monitor future sessions for the anti-pattern (none here).",
  "evidence": "Stop hook restates L1-L5 + kernel-purity + reviewer gate; agent re-orients once then ships continuously.",
  "tier": "agent-reviewed",
  "status": "open",
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
  "id": "goal-mode-discipline-stop-hook-treated-as-go-signal-context-refresh-not-a-hold-g",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### process-signal-notebook-checkpointing-notebook-driven-checkpointing-sync-provide

**Notebook-driven checkpointing/sync provides compaction-durable source-of-truth**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "process-signal-notebook-checkpointing",
  "title": "Notebook-driven checkpointing/sync provides compaction-durable source-of-truth",
  "why": "Each milestone triggers a LAB_NOTEBOOK.md checkpoint as persistent source-of-truth bypassing the context window; load-bearing interface findings recorded proactively before a context boundary.",
  "how_to_apply": "Working; optional hardening = pre-commit check that the notebook was touched at milestones; ensure notebook updates are comprehensive and commit-linked.",
  "evidence": "'Let me checkpoint this major progress in the notebook...' recurring; notebook records every brick + remaining path. | 'I must record the load-bearing L4-interface finding in the notebook (source-of-truth across compactions).'",
  "tier": "agent-reviewed",
  "status": "open",
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

### harness-positive-no-tool-result-parsing-friction-mcp-tool-outputs-well-formed-an

**No tool-result parsing friction; MCP/tool outputs well-formed and reliable**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "harness-positive",
  "title": "No tool-result parsing friction; MCP/tool outputs well-formed and reliable",
  "why": "All lean_* / lake / bash results parseable; no rate-limits, timeouts, or malformed outputs; errors caught immediately by next diagnostic call.",
  "how_to_apply": "Baseline of health; monitor for degradation (malformed JSON, 429s, >30s timeouts).",
  "evidence": "85 assistant turns, no tool-invocation errors; error in turn 13 recovered same turn.",
  "tier": "agent-reviewed",
  "status": "open",
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
  "id": "harness-positive-no-tool-result-parsing-friction-mcp-tool-outputs-well-formed-an",
  "first_seen": "2026-06-18",
  "last_seen": "2026-06-18"
}
```

### compact-delta-post-compact-re-orientation-cost-4-5-re-read-turns-to-rebuild-the-

**Post-compact re-orientation cost: 4-5 re-read turns to rebuild the 5-layer dependency graph**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "compact-delta",
  "title": "Post-compact re-orientation cost: 4-5 re-read turns to rebuild the 5-layer dependency graph",
  "why": "After the compact boundary, the session re-read notebook, file outline, roadmap, goal seed, and dispatched an Explore agent to reconstruct L1-L5 interfaces and load-bearing architectural choices (w₂ geometric vs abstract). Context-loss ripple forced reconstruction of the dependency graph from external docs.",
  "how_to_apply": "Bake into the compact summary: (a) roadmap+notebook snapshot, (b) architectural decision landmarks (w₂ is geometric, not abstract wuClass2), (c) L1->L2 interface spec, (d) load-bearing unknowns. Collapses 4-5 re-read turns to 1.",
  "evidence": "12+ re-orient/re-read/confirm turns post-boundary; Explore dispatch to map L4 interface; 'per diligence rule' full roadmap re-read.",
  "tier": "agent-reviewed",
  "status": "open",
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

### subgoal-scoping-via-downstream-interface-downstream-l2-interface-spec-used-to-de

**Downstream (L2) interface spec used to define minimal L1 deliverable (anti over-build)**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "subgoal-scoping-via-downstream-interface",
  "title": "Downstream (L2) interface spec used to define minimal L1 deliverable (anti over-build)",
  "why": "Checked PoincareDual4Mid signature to confirm L1 must deliver the actual singular ℤ/2 fundamental class [M], not a weaker abstraction — interface-first scoping avoided over-build/over-generalization.",
  "how_to_apply": "Encourage as a norm: before building X, check what downstream Y actually consumes from X; that defines scope.",
  "evidence": "'check what L2 (PoincareDual4Mid) actually expects from [M] — pins down the minimal L1 deliverable... I'll keep it solo.'",
  "tier": "agent-reviewed",
  "status": "open",
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

### parallel-work-dispatch-explore-read-only-explore-agent-dispatched-for-architectu

**Read-only Explore agent dispatched for architectural mapping without blocking solo work; surfaced load-bearing gap**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "parallel-work-dispatch-explore",
  "title": "Read-only Explore agent dispatched for architectural mapping without blocking solo work; surfaced load-bearing gap",
  "why": "On a large unknown (exact L4 interface), dispatched a read-only Explore agent in parallel while continuing the L1 spine solo — delegated info-gathering without blocking forward progress. The Explore report surfaced a load-bearing architectural gap (w2(TM) geometric, not abstract wuClass2; bridged only by the Wu theorem) the main agent had not anticipated.",
  "how_to_apply": "Capture as guidance: on a large architectural unknown, dispatch a read-only Explore agent in parallel instead of blocking. Ensure the blocked-question guard does NOT intercept read-only external-investigation. Ensure the blocked-question guard does NOT intercept read-only external-investigation; the compact summary must capture such load-bearing architectural unknowns.",
  "evidence": "'dispatch a read-only Explore agent to map the exact L4 interface, while I keep building the L1 [M] spine solo.' | 'L4 needs the geometric w₂(TM)... not the abstract wuClass2 from a PD datum — different objects bridged only by the Wu theorem. Load-bearing.'",
  "tier": "agent-reviewed",
  "status": "open",
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

### worktree-safety-boundary-respected-parallel-worktree-reset-denied-by-safety-boun

**Parallel worktree reset denied by safety boundary; agent inlined instead**  ·  tier: `agent-reviewed`  ·  status: open

```json
{
  "class": "worktree-safety-boundary-respected",
  "title": "Parallel worktree reset denied by safety boundary; agent inlined instead",
  "why": "Attempt to reset wt1 to dispatch a lean-worker was correctly denied ('never touch a parallel agent's worktree'); agent pivoted to inlining the sphere-vanishing work without losing momentum.",
  "how_to_apply": "Boundary working as designed; agent's deny->inline response is the correct pattern. No action.",
  "evidence": "'The worktree reset was correctly denied (safety boundary). I'll build the sphere-vanishing inline instead.'",
  "tier": "agent-reviewed",
  "status": "open",
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

## Closed

_(none)_

