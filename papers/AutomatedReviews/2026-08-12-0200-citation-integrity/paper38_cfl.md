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
- **Severity:** blocker

- **Lane:** `prose`
- **Location:** `papers/paper38_cfl/paper_draft.tex`
- **Gate:** CitationIntegrity (1)
- **Verify:** `cd "$REPO" && uv run python -c "import sys; sys.path.insert(0,'scripts'); from pathlib import Path; import check_undefined_citations as C; p=Path('papers/paper38_cfl/paper_draft.tex'); b=C._COMMENT.sub('',p.read_text()); c={k.strip() for m in C._CITE.finditer(b) for k in m.group(1).split(',') if k.strip()}; assert 'SvetitskyYaffe1982' in c, 'VACUOUS: the key is not cited at all'; u=C.undefined_keys(p); assert not u, ('unresolvable', u)"`
  ⚠️ **Amended 2026-08-15 — the original was VACUOUS, and measurably so.** It was
  `check_undefined_citations.py paper38_cfl --key SvetitskyYaffe1982`, and that tool reports
  "resolves" for a key **that is not cited at all**: confirmed by running it with
  `--key NotACitedKeyXYZ`, which exits 0. So deleting the `\cite` would have satisfied the
  verify while the citation vanished — the failure mode is not "the bibitem is missing" but
  "nothing is asserted". The replacement requires the key to be in the CITED population
  first, then requires every cited key in the draft to resolve.
