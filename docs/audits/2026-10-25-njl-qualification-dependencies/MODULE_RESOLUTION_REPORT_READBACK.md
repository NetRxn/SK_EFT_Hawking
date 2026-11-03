# Independent module-resolution reporting readback

**Accept the two reporting edits.** I found no mandatory report correction at this scope.

FIRST checked the original absolute `publication-module-report-review-20261103-r1.json` packet from the NJL integration checkout. Exit 0, `fresh=true`, `changed=[]`. The tracked diff contains only the dashboard caveat and the coverage check's diagnostic message.

- The dashboard still counts unresolved registrations across measured bundles and reports unreadable append logs separately. The validator still counts the same unresolved subset of draft-unreached registrations, keeps its warning/detail status, and uses the same reachability, resolution, exemption and ratchet paths. No resolver, registry, threshold, status or count calculation changed. The validator now lists the actual sorted names by bundle, which identifies the records to reconcile. Both messages correctly place the observation at current declaration-index resolution and direct the reader to lift records, declarations, imports and built dependencies before drawing a substrate conclusion.
- D1's append log lists `KMSOptimality` in the second-order lift. The current declaration index contains no module with that basename and does contain theorem `SKEFTHawking.SKDoubling.firstOrder_KMS_optimal` in module `SKEFTHawking.SKDoubling`. D1 cites that exact theorem in the manuscript, names it in bundle metadata and targets it in claim review. That is a concrete reason to trace an apparent historical label against current declarations. The evidence does not equate the scope of the historical registration with the current theorem or authorize deregistration.
- The retained focused run reports 53 passes and 4 deselections in 0.60 seconds. Its JUnit records 53 executed cases with zero failures, errors or skips. `git diff --check` passed. I ran no project tests, writer or Lean operation, and made no source, notebook, Git or ledger edit. The only owned write is this report.

This accepts reporting accuracy only. The underlying registration coverage debt, missing-source conclusions, independent alias validation and broader gate qualification remain separate.

FINAL checked the original packet and returned exit 1, `fresh=false`, `changed=["owned-files"]` only.
