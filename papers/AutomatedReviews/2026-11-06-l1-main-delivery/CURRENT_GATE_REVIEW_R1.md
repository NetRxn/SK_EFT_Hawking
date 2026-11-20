# Independent canonical gate/chart review R1

Verdict: **REVISE** the visible status and stale current scalar. The actual canonical gate data are exact. ROOT remains acceptance/integration owner; L1 remains lead.

## Verified artifact consistency

The actual unmodified producer JSON contains legacy-paper gates as well as publication-bundle gates. Filtering by the AST-read authoritative `BUNDLES` roster (the source of `BUNDLE_CODES`) yields exactly21bundles ×11gates=231cells. The supplied readback `gates` equals that entire filtered node list exactly. Counts are160passed,25blocked,28open,18needs-recheck. Against actual AF255 readback there is exactly one state transition: **L1 G9 NumericalFreshness needs-recheck → passed**. This compares different branch populations; it is not a per-commit causal experiment.

Every candidate cell preserves every canonical meta field and detail exactly, including measurement, evidence, blocker/accepted-blocker arrays, totals, truncation flags, notes, priority and timestamp. There are231serialized blocker refs (244total),55serialized accepted blockers (55total). All serialized refs resolve to ReviewFinding nodes with matching severity/lane/status/target (producer null→empty-string normalization accounted for). D11 FixPropagation retains producer63total/50serialized refs and blockers,13omitted with explicit truncation flags. Therefore “all231gate payloads exact” is verified; “all244full blocker refs serialized” is not.

All63candidate stage values equal the actual per-bundle `bundle_metadata.json` values. This is only the actual S9/S10/S13 subset; it does not confer newer reviews or acceptance. All21historical baseline/current gate lists and then/current metadata are unchanged against `.before-main8b-20261106-r1`. Prior AF255 candidate measurement is preserved exactly in its dedicated historical field. Both HTML files are identical,847427bytes each (<1MB), and both embedded JSON documents equal the snapshot exactly. Copied candidate payload is byte-exact readback. Existing control tags are unchanged; runtime diff is only status-string text, with no new evaluator/predicate/control. ROOT's structural receipt records Node exit0/ID resolution and explicitly no browser inspection; this reviewer did not execute it.

L1 G3 remains blocked on20missing human dates; G4 passes typed static coverage of7declared formulas, not execution/physical validation; G6 explicitly states vacuity; G11 has1open originalAug14§2.1 and1accepted historical§7.1. Canonically fixed§2.3 is absent from current open refs.

## Required repairs and clarifications

- **R1-1 (required) — both HTML files, static candidate control:** Candidate gates · Nov 5 is stale: actual candidate measurement ended 2026-11-06T12:05:20.498660+00:00. Repair: Update visible date to Nov 6 or derive from the existing measurement.

- **R1-2 (required) — both HTML files, Latest verified increments / L1 fix propagation:** Latest cell says 2 at 4b6408; current canonical L1 FixPropagation has 1 open reference and 1 accepted blocker. Repair: Identify main-based PR117 current1 open/original2.1 and separately disclose1accepted; preserve historical2 as historical if retained.

- **R1-3 (required) — both HTML files, Latest verified increments / Broader qualification:** Latest cell still reports 01d72 7167pass/29fail/8skip/92deselected/no full rerun at af255. This is historical evidence, while new current default suite is7084pass/27fail/11skip/92deselected. Dynamic pr-mode correctly reports new result, causing an on-screen contradiction. Repair: Move historical result to earlier evidence; label current default suite RED and full merge profile remains failed. Do not call static failure classification baseline execution.

- **R1-4 (required) — snapshot and embedded JSON, counts.current_gate_state_changes_since_baseline:** Scalar remains3 although current candidate differs in4cells from Oct16 baseline (L1 G3,G4,G9 and I1 G9). Candidate_measurement.differences_from_baseline and JavaScript dynamic count correctly give4. Repair: Reconcile this current scalar without altering preserved historical cells/counts.

- **R1-5 (clarify) — both HTML files, Latest verified increments / L1 selected k4 words and source-register producer:** These accepted historical/cumulative milestones remain true at their stated bounded scope, but Latest verified evidence gives no branch identifier. PR117 current gate data do not establish the cumulative PR113 science/source checkpoints on the main-based branch. Repair: Label cumulative/historical PR113 evidence explicitly; keep PR117 dependency/G9 increment separate.

- **R1-6 (clarify) — dynamic pr-date header:** Header renders main ce194cdc from live_main_checkpoint, whose own observed_at is Nov5 09:19UTC and basis is historical PR113 base_sha. No main refresh was performed in this review. Repair: Call this dated main checkpoint (or show observation date); do not imply current live-main verification.

## Exact limits

The visible L1 dynamic progress paragraph correctly separates main-based PR117 dependency/G9 work from cumulative PR113 finite nonzero normalization and conditional two-slice positive/PPT/CPTP work. Preserve that distinction throughout the static latest-increments table. Neither branch's gate display establishes physical metric/state/causal matching or originalB3acceptance.

Graph source hashes34fa083674600b86 and oldf05067d944cb41f5 are limited staleness keys over selected sources/Lean files, not full manuscript/evidence/source proofs. The explicit graph/readback SHA256 hashes bind the supplied artifact bytes only. Current qualification's clean-source shorthand must be read with the packet exception: regenerated Paper25PDF is modified; all other source state matches HEAD8b. No new bundle GREEN/acceptance is established. Full merge profile remains failed. Current default suite result and failure attribution are supplied receipt evidence, not tests re-executed here. Remote PR/main freshness was not checked.

The existing detail renderer displays gate detail/evidence, not raw refs/accepted-ref arrays; those arrays remain exact in JSON. D11 caps are producer limitations, not chart data reduction. G4 detail/mode text explicitly discloses static coverage even though L1/D12 G4 quality_caveat booleans are false; no new inference of numerical/physical proof is warranted.

Only read-only file/AST/git/hash commands and report writes were run. No browser/evaluator/tests/graph/native/scientific imports or execution, no repository/artifact/packet/notebook changes. Initial diagnostic counts included704legacy+bundle gates, corrected using the authoritative roster; graph stage-field comparison was discarded in favor of actual metadata; an incomplete attempted FLAGS severity reconstruction was discarded, with producer cap semantics preserved. No missing proof or defect was inferred from those diagnostics.

## Continuity and delivery

First command and final verification both checked the **same R1 packet** and returned fresh=true, changed=[]; no refresh/reissue by reviewer. Current HEAD is8b0ab67533918d4aabdf04c22499b3768dc05314; only packet-bound Paper25PDF is modified. Report JSON includes exact input hashes and command classes. No publication/physics/human/main/full-tree acceptance. ROOT should repair the enumerated display/scalar issues after this report, then deliberately issue a fresh packet for R2.
