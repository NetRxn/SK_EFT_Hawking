---
paper: paper39_heat_kernel_expansion
reviewer: adversarial-reviewer
model: claude-opus-4-7-1m
review_date: 2026-04-28T01:58:00Z
readiness_gates_version: 1
review_kind: re-invocation
prior_review: 2026-04-28-0057-internal-adversarial/paper39_heat_kernel_expansion.md
---

# Adversarial Review (Re-invocation) — paper39_heat_kernel_expansion

## Re-invocation status

Independent verification of every prior BLOCKER and RECOMMENDED claim-fix. **All
3 prior BLOCKERs are CLOSED**. **All 4 prior RECOMMENDEDs are CLOSED**. One new
finding surfaces in this re-invocation: a **Gate 2 cross-paper bibitem-text
inconsistency** in `paper6_vestigial` (the Vergeles2025 bibitem there is missing
the title entirely) and a **Gate 1 registry hygiene** lapse (Vergeles2025
`used_in` field is incomplete — it lists only paper5 + paper26, missing paper6,
paper23, paper25, and paper39).

### Prior BLOCKER status (independently verified)

**BLOCKER 1.1 — `Gilkey1995` absent from CITATION_REGISTRY → CLOSED.**
- Evidence: `grep -n "'Gilkey1995':" src/core/citations.py` → line 2000.
  Fields verified: `authors='Gilkey, P. B.'`, `title="Invariance Theory, the
  Heat Equation, and the Atiyah-Singer Index Theorem"`, `journal='CRC Press
  (book)'`, `year=1995`, `doi_verified=True`, `used_in=['papers/paper39_heat_kernel_expansion/paper_draft.tex']`,
  `notes` includes ISBN 978-0-8493-7874-4 and provenance via Vassilevich 2003 §4.
- Bibkey is in registry; Gate 1 binary criterion satisfied.

**BLOCKER 1.3 — `LinearizedEFE2026` absent from CITATION_REGISTRY → CLOSED.**
- Evidence: `grep -n "'LinearizedEFE2026':" src/core/citations.py` → line 2021.
  Fields verified: `authors='Roehm, J. G.'`, `title='Linearized Einstein
  Equations from ADW Microscopic Theory'`, `journal='in preparation'`,
  `year=2026`, `used_in=['papers/paper39_heat_kernel_expansion/paper_draft.tex']`,
  `notes` documents in-prep self-cite and Phase 6a.1 LinearizedEFE.lean
  shipping status.
- Bibkey is in registry; Gate 1 binary criterion satisfied.

**BLOCKER 2.1 — `Vergeles2025` cross-paper title divergence → CLOSED.**
- Evidence: `grep -A 3 'bibitem{Vergeles2025}'` across the 6 papers citing it:
  - paper5: `"Unitarity of 4D Lattice Theory of Gravity"` ✓
  - paper23: `"Unitarity of 4D Lattice Theory of Gravity"` ✓ (was previously
    "Akama–Diakonov gravity is a unitary theory" per prior review)
  - paper25: `"Unitarity of 4D Lattice Theory of Gravity"` ✓ (was previously
    "Akama–Diakonov gravity is a unitary theory" per prior review)
  - paper26: `"Unitarity of 4D Lattice Theory of Gravity"` ✓
  - paper39: `"Unitarity of 4D Lattice Theory of Gravity"` ✓
  - **paper6: NO TITLE** — see new finding 4.1 below.
- The 4 papers explicitly named in the prompt (paper23, paper25, paper26,
  paper39, paper5) all carry the canonical title. Prior BLOCKER 2.1 is
  fixed *as scoped*; the discovery of paper6's truncated bibitem is a
  separate Gate 2 finding (the prompt's enumeration did not include paper6).

### Prior RECOMMENDED status (independently verified)

- **1.2 (Gilkey ISBN):** CLOSED. Registry `notes` field at line 2014 includes
  "ISBN 978-0-8493-7874-4". Disambiguates the 1994/1995 edition-year question.
- **2.2 (α_ADW range disambiguation footnote):** CLOSED. Footnote present at
  paper39:347-356 explicitly distinguishing the project-policy ±50% band
  $[0.5, 1.5]$ from the Vergeles natural range $[0.1, 10]$, with explicit
  pointer to companion paper23.
- **5.1 (abstract tracked-hypothesis disclaimer):** CLOSED — and stronger than
  the recommended fix. Abstract now contains a bold-tagged sentence at
  paper39:53-56: "**The PDE-level asymptotic-expansion theorem itself is not
  re-derived in Lean** (it requires Mathlib's spin-bundle infrastructure,
  which is not yet available); instead it is *encoded as a tracked hypothesis*
  via the structure DiracHeatKernelAsymptotic, whose invariants force any
  downstream consumer to commit to the Christensen-Duff-Vassilevich textbook
  coefficient table." Goes beyond the recommended parenthetical.
- **6.1 (Λ, N_f > 0 in §6 framing):** CLOSED. paper39:226 reads
  `$(\Lcut, \Nf) = (10^{16}\,\mathrm{GeV}, 15)$ ($\Lcut, \Nf > 0$ throughout)`.
- **7.1 (heatKernelThms / heatKernelTests macros migrated to counts.tex):**
  CLOSED. `docs/counts.tex:47-48` defines `\newcommand{\heatKernelThms}{19}`
  and `\newcommand{\heatKernelTests}{36}`; paper39:18-19 references the
  canonical `\input{../../docs/counts.tex}` only and the inline literal
  `\newcommand` lines are gone (a comment block at paper39:18-20 documents
  that the macros now live in counts.tex). Verified: 19 theorems in
  `lean/SKEFTHawking/HeatKernelExpansion.lean` (counted via line-anchored
  `^theorem |^lemma`); 36 tests in `tests/test_heat_kernel.py` (counted via
  `def test_`). Counts agree with macro values.

## Summary

Findings: **0 BLOCKER, 0 REQUIRED, 2 RECOMMENDED**.

All 3 prior BLOCKERs verified independently as fixed. All 4 prior RECOMMENDEDs
verified as fixed. Two new RECOMMENDED findings surface: (a) `paper6_vestigial`
Vergeles2025 bibitem is missing the title entirely (a different cross-paper
inconsistency than the prior BLOCKER 2.1, but in the same bibkey family); (b)
`Vergeles2025` registry `used_in` list is stale — it tracks only paper5 and
paper26, missing the 4 other papers that cite the bibkey. Neither rises to
BLOCKER under canonical gate criteria (Gate 1 passes on registry-presence; the
title-completeness sub-criterion is satisfied for the 5 papers in the
prompt's explicit enumeration), but both are submission-hygiene issues worth
fixing before submission.

**Stage 13 verdict: paper39_heat_kernel_expansion PASSES re-invocation.**
Gate state: all 11 gates `passed` (modulo the 2 RECOMMENDED items which are
advisory under their respective gates' pass criteria).

## Findings

### 4.1 — 🔵 RECOMMENDED — `paper6_vestigial` Vergeles2025 bibitem omits the title field

- **Gate:** CrossPaperConsistency (Gate 2)
- **Location:** `papers/paper6_vestigial/paper_draft.tex:589-590`
- **Observed:** The bibitem reads:
  ```
  \bibitem{Vergeles2025} S.~N.~Vergeles,
    Phys.\ Rev.\ D \textbf{112}, 054509 (2025).
  ```
  No title, no arXiv ID. Every other paper citing this bibkey (paper5,
  paper23, paper25, paper26, paper39) includes the canonical title
  *"Unitarity of 4D Lattice Theory of Gravity"*. paper5 + paper23 + paper25
  + paper26 also include `arXiv:2506.00036`.
- **Evidence:**
  ```
  $ grep -A 3 'bibitem{Vergeles2025}' papers/paper6_vestigial/paper_draft.tex
  \bibitem{Vergeles2025} S.~N.~Vergeles,
    Phys.\ Rev.\ D \textbf{112}, 054509 (2025).
  ```
  Compare:
  ```
  $ grep -A 3 'bibitem{Vergeles2025}' papers/paper5_adw_gap/paper_draft.tex
  \bibitem{Vergeles2025} S.~N.~Vergeles, ``Unitarity of 4D Lattice Theory of
    Gravity,'' Phys.\ Rev.\ D \textbf{112}, 054509 (2025), arXiv:2506.00036.
  ```
- **Expected:** paper6's bibitem should match the canonical text used in the
  other 5 papers — title in quotes plus arXiv ID, e.g.,
  `\bibitem{Vergeles2025} S.~N.~Vergeles, ``Unitarity of 4D Lattice Theory
  of Gravity,'' Phys.\ Rev.\ D \textbf{112}, 054509 (2025), arXiv:2506.00036.`
- **Fix:** Update `papers/paper6_vestigial/paper_draft.tex:589-590` to the
  canonical bibitem string. Severity is RECOMMENDED rather than BLOCKER
  because (a) the prompt's explicit enumeration (paper23, paper25, paper26,
  paper39, paper5) does not include paper6, so this is a discovery rather
  than a regression; (b) Gate 2 binary criterion ("same bibkey points at the
  same arXiv ID across papers") is satisfied since paper6's bibitem doesn't
  carry an arXiv ID at all — there is no contradicting metadata, only missing
  metadata; (c) Gate 1's title-match sub-criterion is satisfied vacuously
  (no title to mismatch). However, missing-title is still a Stage 13 review
  concern under "registry-truth is paper39-aligned but a sibling carries
  incomplete metadata" — fix in the next hygiene sweep.
- **Cache:** N/A (cross-paper diff, not a fetch)

### 1.1 — 🔵 RECOMMENDED — `Vergeles2025` registry `used_in` list is stale (4 of 6 papers missing)

- **Gate:** CitationIntegrity (Gate 1) — registry hygiene sub-criterion
- **Location:** `src/core/citations.py:646-669` (Vergeles2025 entry)
- **Observed:** Registry `used_in` field is:
  ```python
  'used_in': [
      'papers/paper5_adw_gap/paper_draft.tex',
      'papers/paper26_bh_entropy/paper_draft.tex',
  ],
  ```
  but a `grep -rn "Vergeles2025" papers/paper*/paper_draft.tex` shows the
  bibkey is also cited in paper6, paper23, paper25, and paper39. Four of
  the six citing papers are missing from `used_in`.
- **Evidence:**
  ```
  $ grep -l "Vergeles2025" papers/paper*/paper_draft.tex
  papers/paper23_linearized_efe/paper_draft.tex
  papers/paper25_gravitational_waves/paper_draft.tex
  papers/paper26_bh_entropy/paper_draft.tex
  papers/paper39_heat_kernel_expansion/paper_draft.tex
  papers/paper5_adw_gap/paper_draft.tex
  papers/paper6_vestigial/paper_draft.tex
  ```
- **Expected:** `used_in` should list all six citing papers. The registry
  comment at line 665-668 documents the 2026-04-26 BLOCKER 1.3 fix but the
  `used_in` field was apparently not refreshed in that commit, or the four
  later citations (paper6, paper23, paper25, paper39) post-date the registry
  edit and the `used_in` field was not kept in sync.
- **Fix:** Update `Vergeles2025.used_in` to include all six papers. The
  Gate 1 binary criterion (every bibkey is in registry) is satisfied;
  this is the secondary `used_in`-completeness sub-criterion which the
  pipeline uses to track registry/paper drift in `validate.py
  --check formula_lean_refs_resolve` and similar audits. Severity is
  RECOMMENDED rather than BLOCKER because the gate's pass conditions
  ("entry exists, doi_verified=True, title matches") are unaffected — but
  the completeness slip means future automated `used_in`-derived checks
  (e.g., dashboard "Which papers cite this bibitem?" queries) under-
  report.
- **Cache:** N/A (registry vs. paper inventory diff)

## QI Candidate

**Systemic gap surfaced (different from the prior round's QI):** the prior
review's QI proposed unifying the WARN/BLOCKER severity ladder between the
claims-reviewer and the adversarial reviewer (so registry-absences are not
silently downgraded). That fix appears to have been adopted (the 2 BLOCKERs
were correctly identified and addressed in the hygiene sweep).

The new systemic gap surfaced this round: **`CITATION_REGISTRY.used_in` field
is not auto-maintained.** A bibitem can be added to a paper, the registry
entry can have its `doi_verified=True` flipped, and the `used_in` field can
silently drift by years. This is a register-of-record inconsistency that no
existing `validate.py` check catches. Specific finding above (1.1) shows
Vergeles2025 is cited in 6 papers but tracked in 2.

**QI proposal:** add `validate.py --check citation_used_in_consistency` that
diffs `CITATION_REGISTRY[k].used_in` against
`grep -l '\\cite{k}\\|\\bibitem{k}' papers/*/paper_draft.tex` for every bibkey
k, and emits a finding (severity REQUIRED) when the lists disagree. This is a
cheap, mechanical check that prevents the dashboard's bibkey-fanout queries
from under-reporting and keeps the registry as a faithful record of cross-
paper bibkey usage. Estimated implementation cost: ~30 lines of Python in
`scripts/validate.py`, mirrored after the existing `formula_lean_refs_resolve`
check.
