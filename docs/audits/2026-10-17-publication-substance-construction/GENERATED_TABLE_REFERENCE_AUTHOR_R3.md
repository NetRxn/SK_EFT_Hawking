# R3 renderer-owned theorem-reference candidate

Base is PR118 `ddc320ec365a1f42fd5d8d81796ae07bc0bb029c`. The six-path scratch
patch `theorem-ref-reader-r3.patch` has SHA-256
`b6ee40b7c05bebf0eb9e3c6a5b5174afd068b71667743118dfc2431a5f271cb6`.
The patch applies with whitespace errors enabled to the pinned base.
The exact all-eleven migration `f963e4a5edd0659fee26b6cb9f8d990ce1b87001a28a7b4f396d80d87da61516`
was added in scratch for the composed replay.

The bundle leg scans every strict spec-owned table output with the manuscript's
existing aliases. References keep their original locations and disclaimer
context. Broken specs and duplicate, unsafe, missing and escaping outputs
produce explicit source coverage failures. Default freshness output discovery
retains its existing fallback. The historical legacy leg retains its resolver
and frozen ceiling. The source leg avoids TeX branch interpretation.

A forced compile with retained private artifacts writes the TeX recorder.
The ownership verifier compares lexical and resolved bundle paths to the strict
spec population. The six migrated drafts compiled and recorded all eleven
expected local table inputs. I1 compiled at 37 pages and recorder verification
rejected the existing unowned `tables/table1_stages.tex` open. ROOT owns the
separate I1 candidate. No I1 source is included here. Exact PDF row checks
remain separate from recorder ownership.

## Evidence

- Exact registered clean checks pass at both base and scratch composition.
  Their complete checks payloads are equal, including the legacy leg. Every
  bundle's complete token multiset matches the baseline. The composition has
  2,540 token occurrences and 83 registered outputs before the I1 correction.
- The focused and existing prose suites pass all 77 tests. The added
  source controls failed on the original implementation before the repair.
  The added recorder test also failed before the verifier existed.
- The journaled D9 seed reruns the actual registered CLI with the same
  ordinary LaTeX conditional that hid the seed from R2. The exact source line
  fails and the seeded name is visible in the PDF text. The recorder captures
  the table open. The source bytes, timestamps and journal are restored.
- Architecture inventory reports the same existing hook census and missing
  architecture path failures at both base and composition. The current
  registration probe reports no check-definition, canonical order, mutation
  or census wiring delta. Its existing named verify_scope mapping omission
  remains. The actual plan includes the fast suite and the existing
  architecture, module census and count checks.
- Terminal continuity is in `continuity.terminal.json`. The work occurred
  in private scratch. Independent patch review and composed qualification
  remain pending.
