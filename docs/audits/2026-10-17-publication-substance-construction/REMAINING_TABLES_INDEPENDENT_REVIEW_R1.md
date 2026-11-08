# Independent review of the remaining eleven canonical table migrations

**ACCEPT_SCOPED** for the source migration and rendered differential at
`ddc320ec365a1f42fd5d8d81796ae07bc0bb029c` and patch
`f963e4a5edd0659fee26b6cb9f8d990ce1b87001a28a7b4f396d80d87da61516`.
**Merge qualification remains open.** Intake and terminal continuity matched
the pinned clean draft. Work was read-only in the repository and ran in scratch.
The archive integrity check and source patch manifest passed.

I exported the exact tracked inputs from Git for two independent scratch trees,
applied the frozen patch, and wrote a separate span and cell audit. It verified
each table's alignment, all 36 heading cells, 108 data rows and 340 data cells.
Every byte outside the eleven replaced spans matches, including the captions,
label anchors, bibliography and surrounding reference text. Inside the spans,
cell comparison normalizes whitespace and separates layout rules. The generated
D1 numerical BEC rows match a fresh execution of the pinned canonical producer.
D2 uses the existing rational SM charge data and reproduces the six held-source
charges from García-Etxebarria and Montero Eq. (4.13) and Table 2 after the draft's
rescaling. The computed last column is the exact difference. D6 count inputs
match the held AGP Sec. 8.3 and depolarizing example, and their reciprocals retain
the baseline rounding. Both held PDFs matched the source digests in the author
report.

Two complete canonical renders per lane were byte-identical within each lane.
All pre-existing table paths match across lanes after rendering. The production
table pipeline check moves from eleven handwritten tables to zero and passes
against the unchanged ceiling of one. Its own advice flags the below-ceiling
headroom for the eventual composed delivery. Canonical freshness passes on both
lanes, with the candidate reporting 96 outputs across 20 specs.

Both forced compile runs pass six of six. The page counts 20, 18, 30, 8, 14 and 9
and overfull counts 15, 5, 2, 3, 9 and 4 match in D1, D2, D4, D6, D9 and D10.
Both runs report zero TeX errors, unresolved PDF references and dropped class
options. Named destination sets match. I inspected independent baseline and
candidate page pairs for every migrated table. D1 page 20 still overlaps the
bibliography and D4 page 5 still clips the long trust-grade descriptions.
D6 page 6 and D9 pages 4–5 also show pre-existing overlong material around the
tables or adjacent prose in both renders. These are visual defects despite a
passing compile. D9 page 5 loses the rule before the two bounds rows, but the
caption still identifies the last two rows as exceptions and their bracket or
inequality entries remain distinct. D10 page 3 loses four small inter-group
spacings, while indentation, blank cells and row order still identify the
groups. None of this provides Stage 9 or whole-paper visual clearance.

Two reader defects remain explicit prerequisites. The unmodified production
`d1_hierarchy_table` passes the baseline, then fails with the missing-tabular
error on the complete migration. The unmodified theorem reader loses 32 unique
resolved names and 64 resolved occurrences across the six affected drafts.
I independently reproduced these counts with the pinned committed Lean index
and the actual token and shallow-resolution functions. A control using the
existing TeX dependency closure with draft preamble context reproduced each
baseline verbatim-token multiset exactly. This establishes recovery potential
and preserves D9's preamble-defined alias. It supplies no production checker
change or permission to accept a reduced coverage population.

Independent evidence includes the exact input digests, cell and token audits,
canonical render manifests, compile and gate logs and viewed baseline/candidate
page pairs. The current draft source was left unchanged.
