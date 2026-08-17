# Slot E findings — broad process scan (lines 24001–27871)

### E-1 — Agent brief incompleteness: propagation list omits dependent modules

- **Class:** AB
- **Evidence:** `/tmp/slice_E.md:914–917` — "InducedGravityEntropy needed propagation the brief didn't list. Its Frolov–Fursaev S_ent = N_f Λ²/(48π)·A is proportional to the same a₂, so it moved with it (48π → 12π)."
- **Recurrence:** 1 (InducedGravityEntropy explicit, but this pattern of "module not on the brief's propagation list discovers a dependency at commit time" is structural)
- **Cost:** Post-commit discovery requiring theorem rewrites; should be pre-build check
- **Escalate:** YES — the heat-kernel correction brief is narrow, but briefs for other substrate changes will face the same module-dependency-closure problem

### E-2 — Stale metadata field not refreshed post-merge

- **Class:** DD
- **Evidence:** `/tmp/slice_E.md:639–642` — "D8 metadata flags two apex theorems as 'also named by D4 §9'... Those warnings are now stale — D4 no longer has a §9 naming them. The current D4 has 1512 lines and neither name appears. You can retire both ⚠️ notes in the D8 metadata."
- **Recurrence:** 1 (D8-specific, but bundle_metadata.json carries multiple cross-references that can drift on upstream edits)
- **Cost:** Stale warnings reduce signal; false leads on code review
- **Escalate:** YES — metadata refresh is not automated post-merge when upstream changes

### E-3 — Harness guard evaded by flag coalescing

- **Class:** TF
- **Evidence:** `/tmp/slice_E.md:2470–2475` — "TOOL_ERROR: sed: No such file or directory" after cache-seeding attempt; `cp -c -R` splits flags so the regex `-[a-zA-Z]*R[a-zA-Z]*` (matching coalesced R flag) did not fire. Guard pattern asserts a *flag spelling* as a proxy for the intent (cache seeding)."
- **Recurrence:** 1 (this specific evasion), but the root pattern (proxy assertions) is systemic in guards
- **Cost:** One subagent slipped past the orchestrator-only cache-seeding restriction; worktree-level leak
- **Escalate:** YES — guard design has weak assertion (asserts the flag token, not the action)

### E-4 — Transient test run collision from broad kill pattern

- **Class:** TF
- **Evidence:** `/tmp/slice_E.md:1433–1435` (relative 1433 = absolute ~25434) — "While stopping my own contending processes I used a pytest -q pattern broad enough that it may have killed another agent's run in the main repo; recoverable by re-running, but my error."
- **Recurrence:** 1 (this instance), but collisions among parallel agents indicate no per-agent process isolation
- **Cost:** Silent test-run interruption; requires re-run cycle
- **Escalate:** YES — signals need for agent-scoped process namespacing or stricter kill patterns

### E-5 — Operator redirect on validation discipline (oral, policy not in brief)

- **Class:** OC
- **Evidence:** `/tmp/slice_E.md:842–846` (absolute 24825 approx) — USER message: "great findings - in your downtime, validate lean findings with lean4 skill just to be sure context is complete. I have no doubt papers have these issues, but since it appears systemic, your eyes on the details would be helpful"
- **Recurrence:** 1 explicit message; systemic pattern of trusting aggregated findings without personal verification
- **Cost:** Several citations/findings required operator correction after import from aggregator agents
- **Escalate:** YES — no automated pass-through for findings from read-only agents; manual re-check required when systemic

### E-6 — Papers predate substrate corrections; brief does not account for staleness

- **Class:** OC
- **Evidence:** `/tmp/slice_E.md:2995–3003` (absolute 27196 approx) — USER message: "Ok, so let's make sure our prompts to the subagents relevant to the drafting/reviewing should be checking relevant roadmaps and context and git history - since these papers were originally drafted before we did significant substrate work to improve"
- **Recurrence:** 1 explicit message, but affects ALL redraft briefs (L3, D2, D3, L2, D1, D4, E1, E2, D6, D8, D9, D10, D7)
- **Cost:** Redraft agents shipped revised content against stale physics substrate; required post-hoc corrections
- **Escalate:** YES — systemic: briefs for paper redrafts do not account for substrate evolution between draft date and redraft

### E-7 — lean_local_search false absence silently passed (methodological)

- **Class:** FA
- **Evidence:** `/tmp/slice_E.md:1041–1046` (absolute ~25142) — "lean_local_search silently missed them [five E1 declarations]... All five exist and are built. Had I stopped there I'd have filed a fabricated finding against a correct agent, and 'the language server says it isn't there' would have been hard to argue with."
- **Recurrence:** 3 distinct times in this agent's work (lines 949, 1041, 1110/1377); described as expected per CLAUDE.md but operator warning needed
- **Cost:** One wrong finding would have blamed E1; cascade of meta-findings added to System-2 register instead
- **Escalate:** YES — tooling's documented blind spot is not compensated in agent briefs or workflows; creates vulnerability to fabricated findings

### E-8 — Brief's propagation scope incomplete; discovered at test time

- **Class:** RW
- **Evidence:** `/tmp/slice_E.md:912–917` (absolute ~25013) — "G_N_sakharov asserted *equality* and becomes false... phase 6a.1 propagation [was] not included... Rather than silently change Phase 6a.1 (independently sourced to Adler RMP 54, 729 Eq. 3.3), I restated the bridge."
- **Recurrence:** 1 (G_N_sakharov), but the shape is "brief lists modules to propagate → build time discovers additional module → manual re-measure cycle"
- **Cost:** Post-merge rework; theorem renaming; cross-module discrepancy handling
- **Escalate:** YES — propagation lists in briefs should be derived from dependency graph, not hand-listed

### E-9 — Incomplete failure attribution from worktree isolation

- **Class:** CL
- **Evidence:** `/tmp/slice_E.md:939–941` (absolute ~26040) — "Full-suite failure attribution is incomplete... stale-lean_deps dangling ref above. [Also:] harness_worker_shell_guard denies lake build to subagents..."
- **Recurrence:** 1 agent, 10 new failures introduced, attribution incomplete
- **Cost:** Required baseline diff to untangle introduced vs. pre-existing failures; adds verification step
- **Escalate:** YES — worker isolation blocks subagents from full dependency regeneration, creating measurement debt

### E-10 — Metadata staleness flag exists but not enforced pre-merge

- **Class:** VG
- **Evidence:** `/tmp/slice_E.md:790–793` (absolute ~25891) — "bundle_metadata.json carries freshness_stale: true with last_lift: 2026-06-10T20:22:22Z against a paper_draft.tex mtime of 2026-08-11... metadata's own staleness flag is accurate."
- **Recurrence:** 1 bundle (D8) explicitly checked; pattern is warn-only, so no gate
- **Cost:** Stale metadata passed through without rejection; required manual verification
- **Escalate:** YES — staleness flag exists but has no enforcement; metadata drift not caught by CI

---

## Compact table

| ID | Class | Finding | Recurrence | Escalate |
|---|---|---|---|---|
| E-1 | AB | Brief incompleteness: propagation list omits dependent modules discovered at commit time | 1 (structural) | YES |
| E-2 | DD | Stale metadata warnings not refreshed post-merge when upstream changes | 1 (bundle-scope pattern) | YES |
| E-3 | TF | Harness guard evaded by flag coalescing; asserts flag token not action | 1 (systemic pattern) | YES |
| E-4 | TF | Transient test-run collision from broad kill pattern; no per-agent process isolation | 1 (collision) | YES |
| E-5 | OC | Operator redirect: systemic findings require lean4 skill manual verification, not aggregator-only | 1 (policy) | YES |
| E-6 | OC | Papers predate substrate; redraft briefs do not account for staleness between draft/redraft | 1 (affects 12 bundles) | YES |
| E-7 | FA | lean_local_search false absence; tool's documented blind spot not compensated in workflows | 3 occurrences | YES |
| E-8 | RW | Brief propagation scope incomplete; discovered at test time, requires manual re-measure | 1 (shape recurs) | YES |
| E-9 | CL | Incomplete failure attribution from worktree isolation blocking lake build | 1 instance | YES |
| E-10 | VG | Metadata staleness flag exists but warn-only; no enforcement gate | 1 bundle | YES |
