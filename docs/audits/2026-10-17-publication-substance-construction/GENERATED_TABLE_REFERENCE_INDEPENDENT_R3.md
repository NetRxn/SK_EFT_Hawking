# Independent R3 generated-table theorem-reference review

**REVISE the exact R3 reader.** Its renderer-owned scope fixes the real
R2 D9 conditional bypass and composes cleanly with all five patches.
The generated-source comment pass introduces a separate, reproducible
false pass for a theorem visible in the actual D9 PDF.

## Exact scope and normal replay

- Exported exact PR118 ddc320ec365a1f42fd5d8d81796ae07bc0bb029c independently,
  verified the R3 author manifest, and applied the exact all-eleven,
  D1 reader R2, D1/D4 layout, I1 stage table and R3 patches with whitespace
  errors enabled. The patch SHA-256 values are in patches.sha256.
  The same clean PhysLib c48433678e8fb6306ebcd48453300c8e16058a62 supplies
  both lanes.
- All 21 complete per-bundle token multisets match the pinned draft baseline.
  The composition contains 2,540 token occurrences and 84 renderer-owned
  outputs. The complete registered theorem-reference checker payload matches
  baseline exactly, including every legacy detail. The composed D1 hierarchy,
  table freshness and pipeline checks also pass.
- Independently regenerated the 13 affected outputs byte for byte and forced
  canonical compiles for D1, D2, D4, D6, D9, D10 and I1. All seven passed.
  The final recorders verify all 13 table reads against ownership. On pinned
  baseline I1 the same check rejects the actual live unowned stage table.
  The composed D1 PDF shows all three BEC rows once with the expected
  numerical pairs. All 69 combined D1 and theorem tests and 67 existing
  compiler/prose tests pass in the scratch composition.
- The first set of forced compiles overlapped a test that journaled a D9 seed.
  That run was excluded from final clean-render evidence. The affected compiles
  were repeated serially after all test and seed processes ended.
- Architecture inventory remains red with identical payloads before and after.
  It reports the existing hook census mismatch and missing architecture
  reference. This is targeted qualification and does not establish a full
  merge profile.

## Journaled rendered controls

The ordinary R2 conditional probe on the real D9 table now exits 1 and reports
papers/D9/tables/exact.tex:9. The new name is visible in the PDF. The canonical
compiler recorder opens the owned table and all original bytes, mtimes and
journal state are restored.

A second journaled mutation changes that same cell to:

```tex
\verb|%| \lean{d9\_percent\_bad\_ref}
```

The canonical checker exits 0 and supplies no unresolved-name finding. The
canonical compiler succeeds with 14 pages and no TeX errors, unresolved
references or dropped options. The recorder confirms the owned table opened.
The PDF visibly prints both the percent sign and d9_percent_bad_ref. Exact
source bytes, mtimes and journal state restore. A separate minimal TeX control
also prints the unresolved name after the percent sign. On its raw row the
existing tokenizer sees the theorem. When that same row passes through the
new generated-source comment stripping, the tokenizer sees zero tokens.

At scripts/validation/checks/prose_lean_refs.py, the table reader calls
_strip_tex_comments before extracting verbatim theorem tokens. The shared
comment function treats every unescaped percent sign as the start of a comment.
In standard TeX the percent sign inside a complete verb span is printable
content. The erroneous stripping drops all later tokens on the same line,
which defeats complete registered-source coverage even with correct file
ownership. Preserve renderer-owned enumeration and handle complete verbatim
spans at the comment/token boundary. Keep offset and line preservation, true
comment exclusion and escaped percent behavior. The real D9 control should
fail at exact.tex:9 after revision.

All source edits and runs were confined to scratch. No tracked checkout, Lean
slot, finding ledger, main integration or publication state was changed.
