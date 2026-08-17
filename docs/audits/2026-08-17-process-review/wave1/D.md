# Slot D audit — Process review, wave 1

Lines 20101–24000 of main-2026-08-15.md spine.

## Findings

### D-01 — Working directory assumption breaks Bash commands without explicit path

- **Class:** TF
- **Evidence:** `main-2026-08-15.md:21022` — `Bash(command=cd .claude/worktrees/redraft-D2 && …)` fails with `(eval):cd:1: no such file or directory: .claude/worktrees/redraft-D2` because cwd was not inside the repo. Rerun with absolute path succeeded immediately.
- **Recurrence:** 2 distinct occurrences (line 21022 redraft-D2, line 23251 git merge)
- **Cost:** Wasted cycle diagnosing a cwd assumption; operator would have caught this faster with an explicit safeguard
- **Escalate:** YES — pattern recurs; harness could enforce absolute paths or pre-validate cwd

### D-02 — Kitaev scoping relayed twice in wrong direction; corrected by subagents

- **Class:** RW
- **Evidence:** `main-2026-08-15.md:21018` — "it corrected my Kitaev relay a second time, in the opposite direction from L2"; L2 relayed one scoping, D2 agent read source and relayed the opposite. `21060`: "I was wrong about Kitaev, twice over. I relayed that 'the sixteen is correct, free-fermion is the error.' Both L2's and D2's agents read Kitaev 2009 Tables 1–2 and found the reverse."
- **Recurrence:** 1 finding but specifically called out as a *second* correction (implying L2 had also caught and reversed an earlier wrong relay)
- **Cost:** Two subagent dispatches each had to verify and correct the lead's brief; lost dispatch efficiency because the brief was backwards
- **Escalate:** YES — the lead explicitly states "what I hand them is a lead to check, not a fact" (21068), conceding that the relay process has a verification gap

### D-03 — Metadata assertion defect shipped undetected through prior GREEN sweeps

- **Class:** VG
- **Evidence:** `main-2026-08-15.md:21025–21028` — "D2's prose is disarmed. Its `bundle_metadata.json` is not: 47 apex entries still assert physics for `hom_tensor_adjunction_dim` (…it's `rank = rank := rfl`), plus the retracted 48ℤ claim. A future lift reading that metadata regenerates the whole overclaim." Also: "Every one invisible to every existing check, on bundles that had passed prior GREEN sweeps."
- **Recurrence:** 47 entries × portfolio-wide = spanning multiple bundles, pre-existing
- **Cost:** Silent correctness violation in submitted artifact; no check catches metadata-theorem-content mismatch
- **Escalate:** YES — systemic: "The metadata trap is portfolio-wide, not D2-specific" (21028); dispatched as architecture-change to build a check

### D-04 — Bash guardrail correctly caught suppressed stderr; required reruns  

- **Class:** TF
- **Evidence:** `main-2026-08-15.md:23272` — `TOOL_ERROR: PreToolUse:Bash hook error: […] BLOCKED (Lean guardrail): suppressed stderr on Lean script invocation hides real errors. Remove '/dev/null' redirection and rerun.` Command re-run without suppression succeeded.
- **Recurrence:** 1 occurrence; guard working as designed
- **Cost:** One extra rerun; guardrail prevented silent errors
- **Escalate:** NO — this is the guardrail functioning correctly; not a defect

### D-05 — Native-decide verification deferred to post-merge; cannot self-verify in worktree

- **Class:** OR
- **Evidence:** `main-2026-08-15.md:21430–21432` — "One caveat I'd flag for the merge: because those 8 gates cannot execute in any redraft worktree, neither I nor the D2/D3 leads can self-verify the native-decide surface. That verification has to happen on main after merge, and it's the one part of L2's gate story I could not close myself."
- **Recurrence:** 1 structural constraint (ExtractDeps gates require full `.lake` build)
- **Cost:** Incomplete verification before merge; integration risk pushed to post-merge verification
- **Escalate:** YES — orchestration inefficiency: worktree isolation prevents full gate closure, forcing operator to verify on main

### D-06 — Multiple brief-vs-source mismatches in D1 section; all caught and documented

- **Class:** DD
- **Evidence:** `main-2026-08-15.md:22328–22356` (Device description, Falque method, reservoir factor, D values, temperature convention, stronger failure than brief asked). Each item is listed as "Where the brief is wrong against the sources" with full reconciliation against primary PDFs held locally.
- **Recurrence:** 6 distinct mismatches in one section; lead caught and documented all before section was declared done
- **Cost:** Section required iterative reconciliation against primary sources; no automated check for brief-source alignment
- **Escalate:** NO — caught and documented; process working; suggests documentation drift rather than agent error

### D-07 — Docstring contradiction in seed_journal.py pinned and fixed

- **Class:** RW  
- **Evidence:** `main-2026-08-15.md:21436` — Bash commit message: "Two source-of-truth docstrings said opposite things, and the false one said 'contained'. `seed_journal.py` asserted that…"
- **Recurrence:** 1 finding; fixed with accompanying test pin
- **Cost:** Test had to be written to detect both directions after fix to prevent regression
- **Escalate:** NO — caught, fixed, test pin added; resolved

## Summary

Primary defects are **tool/harness friction** (2× working directory assumptions causing re-runs) and **verification gaps** (Kitaev relay miscommunication × 2, metadata assertions shipped undetected, brief-source drift caught ad-hoc). Orchestration constraint (native-decide deferral) is structural, not processdefect. Most issues caught by subagents reading primary sources; no automation for brief-source alignment or metadata-content consistency.

