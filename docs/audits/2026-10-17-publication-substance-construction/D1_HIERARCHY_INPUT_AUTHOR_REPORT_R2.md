# D1 numerical hierarchy reader R2

Author candidate for independent review. The reader patch is based on
`ddc320ec365a1f42fd5d8d81796ae07bc0bb029c`. The patch has four paths and no
manuscript or generated-table edits. The generated-form tests use the exact
all-eleven migration patch `f963e4a5edd0659fee26b6cb9f8d990ce1b87001a28a7b4f396d80d87da61516`.
The reader applies cleanly to the pinned candidate. Terminal continuity matched.

## Binding and numerical evidence

The generated path requires a literal direct canonical table input as the
entire body after the unique hierarchy label. Before the label it accepts the
actual D1 float structure with optional standard placement, centering and
one balanced caption. The caption accepts D1 math and reference commands
and ordinary escaped punctuation. The grammar rejects TeX's encoded
character notation in the prologue. It preserves the R1 canonical path and
standalone tabular guards and the legacy inline path.

The six new direct-binding controls all reproduce false passes on R1. They
journal mutations to the actual generated-form draft for a post-label false
branch, unused macro and escaped input, a pre-label false branch and input
redefinition, and redefinition nested inside the caption. The additional
encoded caption control went red against the first correction before the
encoding guard. The generated candidate passes all 41 focused tests. The
legacy inline candidate passes 34, with the seven live generated-form
controls skipped. The canonical `d1_hierarchy_table` check passes all 13
details on both forms. The 4,753 bytes implementing row and crossover
comparisons are identical to the pinned source. Both journals are clean.

## Actual PDF control

The exact draft compiled through `compile_bundle_pdf.py D1 --force`.
`pdftotext -layout` recovered each of the three BEC rows exactly once
with its expected numerical pair. A journaled false branch around the
whole float retained all 13 local numerical passes while the canonical
compile gate failed for three unresolved references in the produced PDF.
All three rows were absent. Restoration recovered the exact draft bytes
and a byte-identical active PDF with all rows present. The compiled proof
of presence covers the local reader's outer-context limitation. The
initial run in a minimal scratch export lacked two exact tracked TeX
inputs. They were exported from the pinned source before this replay.

## Qualification boundary

The registration probe on the pinned repository reports a pre-existing
specific verify-scope mapping omission. The actual `verify_scope._plan`
routes the changed code, tests and composed inputs through its existing
fast suite and architecture and generated-artifact checks. Its output is
a plan. This work did not execute the full plan, close a finding, touch
theorem-reference coverage, or integrate any tracked checkout. The
independent reader review and full composed qualification remain open.
