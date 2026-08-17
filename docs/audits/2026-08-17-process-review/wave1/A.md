# Slot A: Lines 8378–12300 — Process Audit Report

## Key Findings

### A-01 — False-absence trap: Charters probed three ways with wrong shapes

- **Class:** FA
- **Evidence:** Line 8669–8823 — assistant measures charter coverage by probing for `CHARTER.md` files (line 8669), then `section_plan` metadata keys (line 8674–8677), then markdown headings (line 8818). Each probe returns false absence; the charters live in `docs/PAPER_STRATEGY.md` tier sections + 21-row summary table, discovered after operator correction at line 8739.
- **Recurrence:** 3 distinct times within the same diagnostic loop (all before operator redirect)
- **Cost:** Minimal (measurement cycles), but delays process checkpoint; near-blocker: would have caused authoring of 21 redundant charter documents that duplicate PAPER_STRATEGY and drift from it (line 8691).
- **Escalate:** YES — measurement-by-proxy pattern recurred three times on the same question with the same failure mode (wrong shape → false absence). Line 8818 acknowledges: *"I measured markdown headings when the charters live in tier sections plus a 21-row table."* The loop shows this is a standing pattern in the harness's diagnostic repertoire.

### A-02 — Measurement stopped by discovery of load-bearing fallback population

- **Class:** VG + measurement insight, not a defect
- **Evidence:** Line 8479–8486 — review-resolution bug fix proposed as "replace folder-name matching with declared-kind" (line 8479 "obvious fix") until measurement revealed **389 of 404 review docs carry no `kind:` field at all** (line 8479). Wholesale replacement would have blinded resolver to 96% of historical corpus.
- **Recurrence:** 1 incident, 2 directions (false-negative L1 invisible; false-positive D12 docs admitted)
- **Cost:** Prevented a catastrophic regression (blind resolver) via pre-commit measurement; the cost is that both directions of the bug stayed live for days.
- **Escalate:** NO — this is validation working correctly, not a process defect.

### A-03 — Three-defect family: System records proxy for act instead of act itself

- **Class:** VG + DD (architecture drift)
- **Evidence:** Line 8612–8624 — three independent mechanisms all committed the same error: (1) discovery folder-keyed instead of asking document first (line 8614); (2) metadata date preferred silently without caveat (line 8618); (3) record-writer stamped "now" instead of review's declared date (line 8620). Each was a proxy (folder name, recorded date, write time) substituted for the real act (declared kind, review date, review date).
- **Recurrence:** 3 separate codepaths, same shape
- **Cost:** **Three bundles** have newer reviews on disk than their records (D10, D11, L1); L1's review date was 2026-08-14 but recorded as 2026-08-15; heatmap was systematically out of sync with reality.
- **Escalate:** YES — this is a systemic architecture pattern (proxy instead of fact) that will recur wherever configuration/record/reality diverge. The brief calls out: "config says yes, reality says otherwise."

### A-04 — Silent configuration-reality drift in ratchet ceilings

- **Class:** VG
- **Evidence:** Line 8628–8637 — **per-bundle blocking ratchets frozen at `{D1: 14, … D12: 44}` (total 232)** against **live population of 6** (line 8635 "enormous headroom"). Last night's 245 closures lowered the actual population; no commit lowered a ceiling. Every per-bundle ratchet became unfireable. Line 8635: *"A new blocker on D1 could land and nothing would catch it."*
- **Recurrence:** 1 event (245 closures on 2026-08-14), but represents the standing failure mode: cleanup obligation left undone.
- **Cost:** Ratchet cannot fire; gate broken by configuration staleness
- **Escalate:** YES — systemic: any large closure/remediation event that doesn't trigger a ratchet re-freeze leaves the gates broken.

### A-05 — Phantom finding: Test residue counted as live CRITICAL for 3 days

- **Class:** TF + RW
- **Evidence:** Line 8213–8224 — `D10:99.9` titled *"seeded mutation"*, marked CRITICAL, body *"Seeded by the test suite."* Residue from a killed mutation test. Line 8214: *"test residue from a killed run masquerading as a live CRITICAL, exactly the filed defect."* Discovered during ratchet re-freeze (line 8204: *"D10 shows 1 blocker where this morning's measurement had zero"*). Test attempt: `try/finally` doesn't survive a kill (line 8238).
- **Recurrence:** 1 incident (live 3 days, 08-12 to 08-15); the failure mode is filed as systemic: "seeded-mutation-survives-a-killed-run"
- **Cost:** Ratchet ceiling would have been re-frozen to 1 blocker that wasn't real; test artifact would have entered the corpus's definition of acceptable (line 8271: *"Freezing `D10: 1` would have written a test artifact into the corpus's definition of acceptable"*).
- **Escalate:** YES — same failure mode identified before this slice as a filed defect; it re-occurred during this audit window.

### A-06 — Test assertion pinned accident, not contract

- **Class:** VG
- **Evidence:** Line 8602–8624 — test `test_the_live_roster_resolves_a_kind_for_the_bundles_that_declare_one` asserted every kind came from an evidence document; true only while no bundle had one recorded. Recording L1's review through the correct writer (`record_review.py`) broke it. Line 8603: *"That test pins an incidental state rather than its contract — and its own failure message gives it away"*. Test message: *"somewhere other than metadata **or** an evidence document"*; the assertion didn't permit metadata (line 8603).
- **Recurrence:** 1 test failure (caused by correct behavior from the lead)
- **Cost:** Correct path was blocked; assertion had to be widened to match contract (metadata **or** evidence document).
- **Escalate:** NO — test was corrected; it was pinning an accident rather than a real invariant.

### A-07 — False absences in charter/plan inventory checks

- **Class:** FA
- **Evidence:** Line 8669–8693 — assistant reports **"1. Section and figure plans exist for zero bundles. `length_target` is in all 21; `section_plan` and `figure_plan` are in none"** (line 8685). Operator and assistant discover ADR-011 P4 deliberately retired stored plans; section plan is read *from the draft's own sections* (line 8688: *"because a plan stored beside the document it describes drifts from it while a plan read *from* the document cannot"*). Figures use `\figuredeferred` in draft (40 already declared). *No missing artifact; the architecture deliberately removed the stored-plan approach.*
- **Recurrence:** 2 false absences in same diagnostic pass (section plans, figure plans)
- **Cost:** Would have led to authoring 21 redundant charters and re-introducing the drift problem F-02 was written to prevent (line 8688–8691).
- **Escalate:** YES — the false-absence trap triggered multiple times. Line 8669: *"Before I report that as missing — that's exactly the false-absence trap."* But operator's question (line 8739) was needed to redirect; the assistant's measurement was still failing.

### A-08 — Agent dispatch authorization request not made until after measurement failed

- **Class:** OC
- **Evidence:** Line 8697–8699 — operator corrects: *"how are section & figure plans created? is that not a step in our pipeline? if not, than doing a one-off here is misguided, because it will be an undocumented dependency"* (line 8739). Assistant had proposed *authoring 21 plans in-band* (line 8695: *"draft plans from each bundle's existing content and charter target for you to review, or we treat plan-authoring as the first per-paper workstream"*) **without checking the pipeline first**. Assistant says: *"I'll hold until you confirm"* about agent dispatch, but the architecture question was upstream of that decision and was never checked.
- **Recurrence:** 1 incident
- **Cost:** Authorization question was asked after a failed diagnostic (should have been asked upstream)
- **Escalate:** NO — corrected; but shows ordering: architecture check before dispatch authorization.

### A-09 — Three pre-existing test failures ignored when a fourth introduced; only one isolated

- **Class:** VG
- **Evidence:** Line 8582–8587 — assistant stashes work, runs test suite against HEAD, observes **7 failures at HEAD**. After restore: **8 failures with my changes** (line 8587: *"Baseline is **7 failures at HEAD** vs 8 with my changes — so one is mine"*). The assistant proceeds to isolate the one regression (test assertion on kind source). The other 7 pre-existing failures are named (line 8628: *"This module had **7 pre-existing failures at HEAD**"*) but flagged, not addressed.
- **Recurrence:** 7 pre-existing failures, 1 new; focus on isolating the new one was correct, but the 7 remain unfixed.
- **Cost:** Low (work scope correct), but the important failure (ratchet headroom `{'D12': 5, 'L1': 1} == {'D1': 14, ...}`) was flagged as requiring cleanup before redraft wave (line 8635: *"That's the loop's cleanup obligation left undone"*).
- **Escalate:** NO — the isolation strategy was sound; the pre-existing failures were flagged, not silently left.

### A-10 — Operator-redirected false-absence probes and operator-clarified pipeline step

- **Class:** OC
- **Evidence:** Line 8739 (operator message) redirects assistant's diagnostic at the critical juncture: *"if not, than doing a one-off here is misguided, because it will be an undocumented dependency"*. Assistant then checks pipeline (line 8750–8756) and discovers: (1) ADR-011 P4 explicitly retired the stored-plan approach (line 8688); (2) section plan is read *from* draft by design; (3) outline is authored *inside* Stage 10. The operator's correction prevented authoring of 21 redundant documents.
- **Recurrence:** 1 key operator correction that stopped a wrong direction
- **Cost:** If assistant had continued alone, would have created undocumented dependency and duplicate-drift problem
- **Escalate:** NO — operator correction worked as intended; but it shows the machine needed the operator's architecture knowledge to route correctly.

### A-11 — PAPER_STRATEGY measured as stale via three wrong probes

- **Class:** FA
- **Evidence:** Line 8795–8825 — assistant measures PAPER_STRATEGY staleness three ways with wrong methods: (1) git log fails (cwd issue); (2) module import fails (import path error); (3) markdown heading count wrong (measuring headings when charters are in table rows). After operator points to first check (line 8790–8791), assistant runs correct measurement: touched yesterday, all 21 codes present, zero legacy refs, zero count literals (line 8811 *"Not stale"*). Line 8825: *"PAPER_STRATEGY is synced, not stale. It's in better shape than I implied twice."*
- **Recurrence:** 3 measurement attempts, all failed before the correct one
- **Cost:** Delayed progress checkpoint; nearly caused incorrect plan to populate a stale doc (line 8795: *"populating a stale doc would be building on sand"*).
- **Escalate:** YES — same measurement-by-proxy pattern as A-01. The assistant measured the wrong properties three times before getting the right one.

## Compact Table

| ID | Class | Claim | Recurrence | Escalate |
|---|---|---|---|---|
| A-01 | FA | Charters probed 3× with wrong shapes (files, metadata, headings) before checking table | 3 | YES |
| A-02 | VG | 389/404 review docs carry no `kind` field; obvious fix would blind resolver | 1 | NO |
| A-03 | VG | System records proxy (folder, record-time, write-time) instead of fact (kind, review-date) | 3 | YES |
| A-04 | VG | Ratchet ceilings frozen at 232, live pop 6; gate became unfireable after 245 closures | 1 | YES |
| A-05 | TF | Test residue (D10:99.9) counted as live CRITICAL for 3 days; kill not survive-safe | 1 | YES |
| A-06 | VG | Test assertion pinned accident (no-kind-before-any-recorded) not contract | 1 | NO |
| A-07 | FA | Plans exist zero bundles; architecture deliberately retired stored plans; double false absence | 2 | YES |
| A-08 | OC | Proposed authoring 21 charters in-band without checking pipeline step first | 1 | NO |
| A-09 | VG | 7 pre-existing test failures at HEAD; isolated 1 new failure correctly | 1 | NO |
| A-10 | OC | Operator redirect prevented authoring undocumented 21 charters; architecture knowledge needed | 1 | NO |
| A-11 | FA | PAPER_STRATEGY measured stale 3× (git log fail, import fail, heading count); was synced | 3 | YES |
