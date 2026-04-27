---
paper: paper37_chiral_ssb
reviewer: adversarial-reviewer
model: claude-opus-4-7-1m
review_date: 2026-04-29T00:00:00Z
readiness_gates_version: 1
---

# Adversarial Review — paper37_chiral_ssb

## Summary

Re-scan after strengthening pass. **Prior REQUIRED 5.1** (abstract overclaim "structural consequence" vs. Lean theorem proves only contrapositive) is **resolved**: abstract at lines 34-41 has been rewritten to: "The chiral-broken phase is encoded as a structural sign assumption on $\qbarq$, with the Gell-Mann-Oakes-Renner relation $\mpi^2 \fpi^2 = -2\,\mq\,\qbarq$ then serving as a falsifier: parametric over a raw scalar $\sigma \ge 0$, we prove **contrapositively** that the relation forces a contradiction with non-vanishing pion mass and decay constant for positive quark mass. The forward direction (constructing $\qbarq < 0$ from GMOR alone) is left as a corollary at the prose level." The contrapositive shape is now explicitly named, and the missing forward-direction theorem is acknowledged as out-of-scope. **Prior REQUIRED 7.1** (`H_TetradQuarkScalesNatural` docstring "two" vs. body's three constraints) is **resolved**: Lean docstring at lines 187-190 now reads "Three independent constraints (drop-conjunct test passes per conjunct):" — count corrected to match the three Prop fields. **Prior RECOMMENDED 5.2** (counts macro retrofit) is **resolved**: abstract line 52 and §VII line 222 now use `\chiralSsbThms{}` (resolves to 10). Counts macro `\chiralSsbTests` resolves to 14. No new BLOCKER/REQUIRED/RECOMMENDED findings. Submission-ready.

## Findings

(none — re-scan finds no new issues; all three prior findings resolved)

## Verification of strengthening-pass changes

### Class 5 — abstract rewritten as contrapositive falsification

- **File:** `papers/paper37_chiral_ssb/paper_draft.tex:34-41`
- New abstract:
  > "The chiral-broken phase is encoded as a structural sign assumption on $\qbarq$, with the Gell-Mann-Oakes-Renner relation $\mpi^2 \fpi^2 = -2\,\mq\,\qbarq$ then serving as a falsifier: parametric over a raw scalar $\sigma \ge 0$, we prove **contrapositively** that the relation forces a contradiction with non-vanishing pion mass and decay constant for positive quark mass. The forward direction (constructing $\qbarq < 0$ from GMOR alone) is left as a corollary at the prose level."
- The "structural consequence" overclaim (prior abstract) has been replaced with explicit contrapositive language. The forward direction is acknowledged as out-of-scope at the prose-level / corollary status. ✓
- Body §III at line 146-160 retains the contrapositive theorem framing (`chiral_unbroken_violates_gmor`); shape consistent with abstract.

### Class 6 — `H_TetradQuarkScalesNatural` docstring count corrected

- **File:** `lean/SKEFTHawking/ChiralSSB_QCD.lean:187-190`
- Old docstring (per prior review): "Two independent constraints (drop-conjunct test passes):"
- New docstring (verified): "Three independent constraints (drop-conjunct test passes per conjunct):" — count matches the three Prop fields (a) `sigma_scale > 0`, (b) `sigma_scale / 10 ≤ v_tetrad`, (c) `v_tetrad ≤ 10 * sigma_scale`. ✓
- Drop-conjunct discipline: each conjunct is genuinely independent (witness/falsifier coverage at lines 196-206 of the file establishes non-vacuity).

### Class 7 — counts macros

- `\chiralSsbThms{}` → 10 — matches `grep -cE "^theorem " ChiralSSB_QCD.lean = 10` ✓
- `\chiralSsbTests{}` → 14 — matches `tests/test_chiral_ssb.py` test count ✓
- Abstract line 52 ("\chiralSsbThms{} substantive theorems") and §VII line 222 ("\chiralSsbThms{} substantive theorems") use the macro consistently ✓
- No "Undefined control sequence" in `paper_draft.log`. ✓

## Class 1 cache-skip summary (unchanged)

All four bibitems re-inspected:
- `NambuJonaLasinio1961` — Phys. Rev. 122, 345 (1961) — `cache-skip` (foundational paper)
- `GMOR1968` — Phys. Rev. 175, 2195 (1968) — `cache-skip`
- `FLAG2021` — arXiv:2111.09849, EPJC 82, 869 (2022) — `cache-skip` (year-of-review = 2021, journal-publication = 2022; consistent with FLAG-WG convention as noted in prior review)
- `PDG2022` — Prog. Theor. Exp. Phys. 2022, 083C01 (2022) — `cache-skip`

## Class 4 cross-paper consistency

No bibkeys shared with the other six papers in this batch. Paper 38 (CFL) cross-references the GMOR1968 *concept* via §V cross-bridge but does not re-cite the bibkey. No contradiction.

## Class 3 substantive-body confirmation

All 10 cited theorems re-inspected; no new P3/P4/P5 patterns introduced. `gmor_pdg_match` remains `norm_num`-backed numerical agreement at ~1 part in 10⁴. `chiral_unbroken_violates_gmor` uses all four hypotheses in the proof body (m_q > 0, m_pi ≠ 0, f_pi ≠ 0, σ ≥ 0); the abstract's contrapositive framing is now consistent with this load-bearing structure.
