# I1 canonical stage table source repair

Author candidate against exact PR118 ddc320ec and the all-eleven migration.
The existing I1 PDF used a hand-authored stage table despite its caption
attributing it to the canonical pipeline. The canonical compiler recorder
confirmed that the old output is live. This repair registers the existing
filename in the I1 table spec and calls the same pipeline_stages producer as
Paper 15. The displayed Stage 14 advisory status remains explicit in the
caption. The output updates the gate descriptions to the current authority,
including the Figure Review verdict record and Paper Draft qualification.
The stage labels retain all 15 rows, including 3a and 3b.

Two canonical renders give byte-identical output. The neighboring finding
classes table is byte-identical. The forced canonical compile has 37 pages
and no TeX errors, unresolved references or dropped options, matching
baseline. Its 41 overfull notices are inherited in count. On page 17 all
15 rows render within the page, and the advisory caption is visible.
The recorder opens exactly the two renderer-owned I1 files.
Scoped prose, reader voice and length checks pass before and after.

The three-path patch applies cleanly on the all-eleven candidate. This is
an author checkpoint. It still requires independent exact review and
qualification on the final composed candidate.
