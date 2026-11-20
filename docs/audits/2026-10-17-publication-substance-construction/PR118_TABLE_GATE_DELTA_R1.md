# Exact PR118 table delivery gate differential

Paired canonical graph producer reads on ddc320ec and 68e4310a6 cover all
21 bundle codes and 231 distinct publication gates. Each produces 159
pass, 22 blocked, 30 open and 20 recheck. No gate state or measured flag
changed, and zero bundles became green. The dedicated existing table
pipeline check changed from 11 handwritten tables across six drafts
against ceiling 1 (FAIL) to zero against ceiling 0 (PASS).

The exact Git checkouts were isolated while the full merge profile ran on
the pushed draft. The first graph attempt stopped when the inherited
stale extraction stamp triggered dependency acquisition without network.
Both Git source inventories contain 2,058 Lean module files with the
same actual source digest, fc377552dec9e27e, and the same committed
declaration JSON. The full profile has already regenerated that source
stamp on the live candidate without changing the declaration JSON.
The paired graph runs use that same verified stamp in each isolated
checkout. It is their only tracked difference from the respective
named commits. No check or source edits were applied to either lane.
The shared graph source hash does not bind all payloads, so the
distinct complete graph digests and all 231 node payloads per lane
are recorded separately.

These are paired PR118 candidate results. Earlier integrated publication
snapshots have different source populations and cannot serve as a
same-source comparison. Full merge qualification and final human
approval remain separate.
