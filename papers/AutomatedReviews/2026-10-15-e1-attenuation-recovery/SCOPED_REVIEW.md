# Independent focused review: E1 attenuation recovery

Reviewed 2026-10-15 by independent Codex reviewer `e1_focused_review`.
The reviewer was read-only and separate from the author. Acceptance covers
findings 1.1–1.3 of the sibling E1 report and the coherent attenuation-section
trim, not a full Stage-10 or Stage-13 review.

The reviewer independently reproduced recovery multiplication in canonical
Python, read the full manuscript and exact diff, reconciled the imported Lean
statements and module hash, and verified all three declared commands. The
explicit final sentence change to “At zero propagation distance” reconciled
the snapshot without changing its meaning or the Verify command.

The review accepted the recovery direction, one-way zero-decay claim,
explicit velocity identification, theorem/model distinction and retained
validity/fabrication disclosures. No unresolved issue was found within this
scope. The closing report stated no contradictions between its brief and sources.

## Source and verification evidence

Base: `ce194cdc4bf939b108c17edc9530a7f0a14565f9`.
Manuscript SHA-256 at independent acceptance:
`d9a89ed4d364897d0b529b0a134be77b6f0a63bc26ead897fed9ba4718856fcd`.
The retained Lean source hash and imported statements are in `E1.md`.
The relevant canonical Python function is identical to that base.

Author verification after the final sentence change:

- `compile_bundle_pdf.py E1 --force`: clean; five pages, zero TeX errors,
  zero overfull boxes, zero unresolved references in the rendered PDF.
- Existing compiled-length algorithm: 3725 word equivalents, below unchanged
  3750 ceiling; an isolated unmodified-baseline compile measured 3981.
- All three exact finding Verify commands: exit 0 after failing before their fixes.
- `bundle_manuscript_length`: passes. Existing em-dash and reader-voice checks
  contain no E1 issue; the corpus still fails on other manuscripts.
- Rendered changed paragraphs, equations and caption on pages two and three:
  inspected, readable and unclipped. `git diff --check`: passes.

## Remaining limits

The unchanged E1 abstract exceeds its declared ceiling; module-coverage and
structural-coherence findings also remain. Historical corpus severity and
Verify-format failures remain. No full-suite, fresh authoritative extraction,
whole-project build, whole-bundle readiness, human acceptance or submission is
certified here. All bundle reviewer statuses remain pending. Closures are
recorded only through `close_finding.py`, not through this report's wording.
