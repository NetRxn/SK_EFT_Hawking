# Proposed ADR-009 clarification for the D1 hierarchy table reader

Candidate base ddc320ec on draft PR118. The actual unchanged D1 table
passes the canonical evaluator when inline. Moving the same bytes to a
canonical table input makes the old reader miss all three BEC rows. It
crosses the end of the labelled float and matches D1's status table.
The existing draft input closure resolves the migrated table. The pilot
changes storage form only and records every reported comparison.

## Proposed decisions

1. Keep the existing d1_hierarchy_table registration, evaluator, crossover
   parser and numerical tolerance. The labelled hierarchy float bounds the
   table search, so a later table cannot satisfy it. Strip TeX comments with
   the existing validation helper for source selection.
2. Allow the existing inline tabular or the single canonical direct
   tables/platform_hierarchy input within that float, accepting the usual
   optional .tex extension. Refuse missing, duplicate, mixed or unrelated
   candidates. Reuse the shared TEX_INPUT_RE and comment stripping for
   the single direct token. Resolve only the known generated artifact
   after confirming that exact token. Confine the resolved file below
   the real D1 directory's lexical tables child. The broader recursive
   dependency collector remains the freshness authority. It does not
   select or authorize the input for this validator. Missing, unreadable,
   noncanonical or escaped paths fail the check. Retain the manuscript
   text as the crossover input.
3. Keep the renderer and check roster unchanged. Reuse compute_bec_hierarchy
   for scientific values. Compare the same row cells, directions and
   crossover values. Do not use generated rows as the evaluator's authority.

## Verification and delivery

Propose the targeted change to the existing physics validator and its
existing test file, with ADR-009/validation architecture clarification
in the same source checkpoint. First independently review this scope
and the measured production artifact. Then exercise inline and generated
forms, missing or misbound input, and a changed BEC cell in the actual
generated artifact. A later valid tabular cannot mask a failed hierarchy.
Canonical render/freshness and the whole table-pipeline gate run on
the composed eleven-table candidate. Independent source and rendered
review precede the existing finding closure and exact merge qualification.

No threshold change, new table parser, additional check or broad TeX
resolver is proposed. The original publication acceptance remains owed.

R2 adopts the independent decision-2 finding. The actual all-eleven
source candidate also needs theorem-reference coverage reconciliation
before it qualifies. That separate reader surface remains under measurement.
