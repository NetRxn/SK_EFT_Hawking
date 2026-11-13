# NJL November 3 fast qualification

The configured fast suite ran both testpaths on frozen `4bab86c6`. It returned 7,218 passes, 11 failures, nine skips, and 92 deselections. The before and after source and protected stub snapshots match. Compared with the previous broad run, two sentence checks and the real-document Blocked-by mutation now pass. No new failure identity appeared.

| Remaining pre-integration failures | Count | Evidence and next repair |
|---|---:|---|
| Bundle Lean reach and deregistration seed | 2 | 185 unreachable registrations against 147. Check actual consumers and the branch's typed declarations, imports and built dependencies before changing registrations. The mutation needs a valid baseline. |
| Open required finding populations | 4 | Live findings exceed frozen limits. The unattributed count is 56 against 44. Reconcile real attribution, dependencies and reviewed repairs through the canonical ledger. |
| Generated tables | 2 | 14 handwritten tables against 1 on the frozen run. The reviewed D2 integration reduces that to 12. |
| Review Verify format | 1 | 55 malformed entries on the frozen run. The reviewed integration leaves two D8 diagnostics that require fixed-state checks. |
| Inline numerical literals | 2 | 143 against 117. Bind actual values and their consumers to the canonical computation or generated outputs. |

The normal merge `e5e171fd` integrates D2, Verify formatting and D7/E2 ingestion. Target-local census regeneration changed only the timestamp and Lean index provenance relative to the D2-generated census. The combined focused run returned 139 passes and the one known D8 Verify-format failure. D7/E2 now expose 20 additional historical critical or major findings, all open. Their recovered identities and closure safeguards are in the [ingestion readback](D7_E2_INGESTION.md).

The broad result is the pre-integration baseline. The composed source still needs complete qualification, and no new scientific or publication closure follows from this checkpoint.
