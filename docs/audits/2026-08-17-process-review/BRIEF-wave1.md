# Wave 1 brief — broad process scan

**Audit window:** t0 = 2026-08-15 09:46 CDT (14:46Z), the moment this session's process started
against plugin cache `f33dc0a1b2e5`. Everything before t0 ran a different machine and is out of
scope. Window ends at HEAD, 2026-08-17.

**What the window contains:** the Stage-10 redraft campaign across publication bundles — L3 (pilot),
D2, D3, L2, D1, D4, E1, E2, D6, D8 on Aug 15; D9, D10, D7 on Aug 17 — plus substrate corrections
(heat kernel, KZM exponents, A1 kernel purity) and harness work.

## What you are auditing

The **development process**, not the physics. The machine under review is:

- a `skeft-qa` Claude Code plugin — hooks, subagent definitions, skills, slash commands
- a Python validation harness — `scripts/validation/checks/*`, run as gates
- architecture documents and ADRs under `docs/architecture/` and `docs/adrs/`
- a Lean 4 substrate the papers cite
- an orchestration pattern: the lead dispatches subagents into git worktrees, then merges

## Your input format

A "process spine" extracted from the transcript. Lines are:

- `### [ts] USER` — operator message, verbatim
- `[ts] ASSISTANT:` — assistant prose, verbatim
- `  -> Tool(param=…)` — a tool call signature
- `  !! TOOL_ERROR: …` — a failed tool call

Tool *result* payloads were dropped. Absence of evidence in the spine is not evidence of absence —
say so when a finding depends on something you cannot see.

## Method

Work grep-first over your assigned slice, then read around the hits. Useful signatures:

`Actually`, `I was wrong`, `correction`, `re-measure`, `stale`, `I had`, `turns out`, `missed`,
`didn't`, `failed`, `TOOL_ERROR`, `blind`, `pre-existing`, `false`, `should have`, `again`,
`re-run`, `rework`, `no such`, `not found`, `unknown constant`.

Operator messages are the highest-value signal in the file. Read **every** `### [ts] USER` block in
your slice in full — a correction from the operator is by definition a gap in the machine.

## Defect classes to report

| code | class | what it looks like |
|---|---|---|
| RW | rework | the same work done twice because the first pass was wrong or blind |
| OC | operator correction | the operator had to redirect; the machine should have known |
| FA | false absence / false green | a check, search or measurement reported nothing when something was there |
| AB | agent-brief defect | a subagent was dispatched with a wrong, stale or incomplete brief |
| TF | tool / harness friction | commands that failed, needed retries, or have confusing interfaces |
| CL | context loss | something rediscovered after a compaction, or a settled question relitigated |
| VG | verification gap | a claim accepted without measurement and later found wrong |
| DD | document drift | an artifact asserting something the code does not do |
| OR | orchestration | dispatch, parallelism, worktree, merge, or integration inefficiency |

## Output

Write your report to the path given in your assignment. Use exactly this shape per finding:

```
### <SLOT>-NN — <one-line claim, stated as the defect not the story>

- **Class:** RW | OC | FA | AB | TF | CL | VG | DD | OR
- **Evidence:** `<file>:<line>–<line>` — then a short verbatim quote (≤3 lines)
- **Recurrence:** how many distinct times you saw this pattern in your slice
- **Cost:** what it cost — wall-clock rework, a wrong artifact shipped, a wasted dispatch
- **Escalate:** YES | NO — YES if it looks systemic (recurs, or would recur on the next bundle)
```

Rank findings within your report most-systemic first. Aim for 5–12 findings; do not pad. A slice
with genuinely little signal should say so rather than manufacture findings.

Then return to the dispatcher **only** a compact table: ID, class, one-line claim, recurrence,
escalate. Do not return the full report body.

## Rules

- Quote evidence with file and line numbers. A finding without a line reference will be dropped.
- Do not diagnose root cause in the harness code — you are not reading the code, only the spine.
  State what was observed; wave 3 traces implementation.
- Do not propose fixes. Wave 3 owns remediation design.
- Do not edit any file other than your own report.
