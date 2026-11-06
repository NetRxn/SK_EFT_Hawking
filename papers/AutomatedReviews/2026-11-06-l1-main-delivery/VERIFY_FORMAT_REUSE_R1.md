# Existing review-command repair: current composition

The existing reviewed repair `be0b4fa476a571fa415625a88243f60ec8f0dad3`
supplies 53 command-format transformations across five historical review
documents. Each original command block matched the current source exactly.
Only those blocks were replaced; surrounding current findings were retained.
The whole donor patch did not apply because D1's surrounding context differs.

The unchanged canonical `review_verify_is_one_command` check measures:

| Source | Markers | Malformed controls | Exit |
| --- | ---: | ---: | ---: |
| Before composition | 282 | 56 | 1 |
| After composition | 282 | 3 | 1 |

ROOT checked shell syntax for all 53 commands, shell-decoded Python AST
conservation for 45 and shell argument conservation for eight, after removing
Markdown delimiters. These checks execute none of the scientific assertions.
They do not establish that an original assertion is sufficient or currently
passes. No scientific source, test, gate predicate, ceiling or closure ledger
was changed by this repair.

The three remaining malformed controls are deliberately unmodified in this
composition: D1's original August finding 1.1 and D8's original findings 1.4
and 1.8. D1's crossover/unit/consumer obligation remains open. The donor's
independent review excluded both D8 controls because simply normalizing their
`grep -c` diagnostics can accept a defect and reject the fixed state. They
require scientifically adequate fixed-state witnesses under their original
findings. This composition supplies no waiver or deferral.

Historical E2/D7 heading ingestion gaps also remain: formatting a command
does not mint an absent finding or authorize renaming historical identities.
Independent current-composition review and evidence are recorded alongside
this document before the repair is accepted as a checkpoint. No scientific
finding closure, complete corpus pass, publication acceptance or main merge
is claimed.

Independent current-composition review ACCEPTS this exact scope. It measured
1,852 finding IDs and statuses unchanged, with25 intended Verify changes and
15 generated display-snippet changes only. Deliberate R2 initial/final checks
are fresh; the disclosed R1 explanatory-document drift remains in the report.
Evidence: [independent review](VERIFY_FORMAT_REUSE_INDEPENDENT_R1.md),
[archive](VERIFY_FORMAT_REUSE_R1_EVIDENCE.zip),
[hash readback](VERIFY_FORMAT_REUSE_R1_READBACK.json).
