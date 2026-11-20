# Generated artifact synchronization and post-build qualification

Independent R2 review accepts four exact canonical artifacts: counts JSON,
its complete LaTeX companion, native declaration-source hash, and Paper15's
registered-check description table. ROOT read both full review reports and
verified every final artifact hash. R1's REVISE verdict is preserved: its
three-file image left the paper-facing test macro stale.

The existing `update_counts.py` producer repaired that companion. Both JSON
and LaTeX now report 7,019 collected tests. The independent reviewer compared
all 4,717 generated LaTeX bytes and 107 macros, all count fields, canonical
source hash, and complete Paper15 table render. Its one changed description
matches current code; advisory YELLOW/OPEN does not establish human readiness.
No generator, validation predicate, threshold, scientific claim or ledger
was changed. The LaTeX/header changes came from the existing producer.

The post-build canonical extraction completed successfully: 41,034 declarations,
byte-identical JSON to committed source, with a fresh source-cache hash.
Eight previously failing extraction/graph/readiness test modules then completed
with 182 passed and three skipped. The first mistyped test-path invocation
ran no tests and is retained separately.

Canonical CI, measured before the counts.tex correction, completed 67/85
checks passed and reported the Lean/Python substrate clean. Eighteen
paper-corpus checks remained red. Full stdout/stderr, including warnings and
individual failures, are retained; neither this result nor the narrow graph
run is a complete successful merge profile or a new 231-gate snapshot.
The prior full merge profile remains failed. Current source and remaining
scientific/publication/human gates must still satisfy their acceptance.

The existing planner's actual output is retained. Its checkout-local zero-slot
message is not runtime admission or permission to create, reset or reclaim
slots. Original physics BUILD obligations and ROOT's complete ordinary L1
ownership remain unchanged; Executor supplies only bounded deeper constructions.

Evidence: [independent R1 rejection](GENERATED_ARTIFACT_REVIEW_R1.md),
[independent R2 acceptance](GENERATED_ARTIFACT_REVIEW_R2.md),
[archive](GENERATED_ARTIFACT_SYNC_R2_EVIDENCE.zip),
[hash readback](GENERATED_ARTIFACT_SYNC_R2_READBACK.json).

After R2 review, the existing counts_fresh and tables_fresh checks both PASS
(exit0). Their existing generators regenerated metadata as required; all four
reviewed artifact hashes and every other tracked output remained byte-exact.
The table producer reported90tables across15papers. This proves scoped
freshness/idempotence, not the remaining scientific or full merge gates.
