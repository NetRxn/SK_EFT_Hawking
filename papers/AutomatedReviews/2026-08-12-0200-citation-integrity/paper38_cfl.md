---
paper: paper38_cfl
reviewer: lead (mechanical sweep)
model: claude-opus-5
review_date: 2026-08-12T02:00:00Z
readiness_gates_version: 1
kind: citation-integrity
---

# Citation Integrity Sweep — paper38_cfl

## Summary

Mechanical sweep of `papers/paper38_cfl/paper_draft.tex` for keys cited in reader-visible prose with
no `\bibitem` defining them. **1 BLOCKER.** Every key below is present in
`CITATION_REGISTRY`, so this is a rendering gap, not a sourcing gap: the sources are known and
recorded, and the manuscript does not emit their bibliography entries. Each renders as an
undefined citation in the compiled PDF.

**Method.** LaTeX comments are stripped before matching, so a key surviving only in a
commented-out block does not count as cited. Matching is exact-key on the contents of
`\cite*{...}` and `\bibitem{...}`, never substring — a substring test on this corpus is
wrong, and produced a false finding during this same triage (`Crossley2017` matches
`Crossley2017II`). Reproduce with `scripts/check_undefined_citations.py`.

**Provenance.** Found during the triage of the open-critical backlog (ADR-012 P2), not by a
reviewer pass. Triage surfacing new defects is itself a result and is recorded in that ADR.

Gate affected: CitationIntegrity (1). Per Stage 13, citation findings of any kind are BLOCKER
at submission time, no exceptions.

### 1.1 — 🔴 BLOCKER — `SvetitskyYaffe1982` is cited with no `\bibitem`

`SvetitskyYaffe1982` appears in a `\cite` in reader-visible prose of `papers/paper38_cfl/paper_draft.tex`, and no
`\bibitem{SvetitskyYaffe1982}` defines it, so the reference renders undefined. The key resolves in
`CITATION_REGISTRY`, so the repair is to emit the entry from the registry rather than to find
a source.

- **lane:** `prose`
- **target:** `papers/paper38_cfl/paper_draft.tex`
- **blocks:** CitationIntegrity (1)
- **verify:** `uv run python scripts/check_undefined_citations.py paper38_cfl --key SvetitskyYaffe1982`
