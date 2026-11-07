# Independent theorem-reference reader R2 review

**REVISE** frozen reader patch
`eee0b42495419cd7472ca4c1b9d835ab44fa038299c2392928b732e1be2821e3`.
The direct generated-table path and exact migration parity are verified.
A common LaTeX macro inside a skipped branch can conceal a rendered direct
input from the registered checker.

## Exact replay

- Intake and terminal continuity matched. Independently exported PR118
  `ddc320ec365a1f42fd5d8d81796ae07bc0bb029c` and applied the all-11
  patch `f963e4a5edd0659fee26b6cb9f8d990ce1b87001a28a7b4f396d80d87da61516`
  followed by the exact R2 patch. Application with whitespace errors
  enabled passed, and the author manifest verified.
- The complete registered clean checks payload is byte-identical for
  baseline and composition against the same clean PhysLib dependency
  `c48433678e8fb6306ebcd48453300c8e16058a62`. Both checks pass with 1,418
  bundle candidates, zero unresolved, two advisories and one waiver.
  The legacy 43-draft leg retains 1,057 candidates and 90 unresolved
  under the 90 ceiling. Independent per-bundle token counters matched
  for all 21 bundles, totaling 2,540 occurrences. Direct table files
  moved from 71 to 82.
- Independently ran the theorem-reference and existing prose test modules
  in a separate clean composition. All 91 tests passed.
- Compiled four independent minimal TeX sources. Canonical, dot-prefixed
  and post-newif declaration inputs render and are reached. An input
  in an ordinary false branch is absent and yields no event.

## Blocking adverse result on actual D9

Journaled a fresh unresolved name at `papers/D9/tables/exact.tex:9`.
With the canonical input, the registered checker exits 1 and identifies
the exact file and line. A second journaled edit adds the standard
`ifthen` package and replaces the same input with:

```tex
\iffalse\ifthenelse{1=1}{True}{False}\else\input{tables/exact.tex}\fi
```

Both seeded D9 variants compile successfully. PDF text extraction shows
the same unique seeded declaration in the dephasing row of each. For
the second variant, the registered checker exits 0, supplies no finding
for the seeded reference and drops seven distinct candidates. Both D9
files' bytes and modification timestamps and the journal are restored.

The scanner classifies any control beginning with `if` except `iff`
as an opening TeX conditional. TeX treats `ifthenelse` as a macro and
does not expand it in the skipped branch. The next else belongs to the
actual outer iffalse. The scanner instead associates that else with
its invented nested branch and still treats the active input as
skipped. An ordinary active ifthenelse followed by an unrelated
canonical input also produces a false undecidable error.

Three extra minimal compiled controls show the boundary of claiming
general active-input recognition. A definition in a skipped branch can
contain the fi that ends the branch, which the scanner skips with the
rest of the would-be definition. A constructed definition with csname
can hide an invoked table input without producing an explicit coverage
failure. A macro that discards its argument can contain an unexecuted
input that the scanner accepts as active. These are separate controls,
with the direct D9 adverse case sufficient to require revision.

The bounded reader should only advance structural branch state for
actual conditional starts it recognizes. When an unsupported construct
can change whether a literal table input is executed, surface an
explicit coverage failure instead of silently omitting it. Keep the
exact 21-bundle and legacy comparisons and seed the rendered D9 case as
a regression control. Preserve the direct-literal scope and avoid
claiming general TeX evaluation.

All work occurred in private scratch. No tracked writes, slot changes
or main integration were performed.
