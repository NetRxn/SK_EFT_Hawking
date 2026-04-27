---
paper: note_rt_ch_bounds
reviewer: adversarial-reviewer
model: claude-opus-4-7-1m
review_date: 2026-04-29T00:00:00Z
readiness_gates_version: 1
---

# Adversarial Review — note_rt_ch_bounds

## Summary

Re-scan after strengthening pass. **Prior REQUIRED 5.1** (Sen's 4D Schwarzschild log coefficient 77/45 lacked primary-source citation) is **resolved**: bibitem `Sen2013Schwarzschild` added at lines 284-287 ("A.~Sen, ``Logarithmic corrections to Schwarzschild and other non-extremal black hole entropy in different dimensions,'' JHEP \textbf{04}, 156 (2013); arXiv:1205.0971."), and §intro line 76 now reads "log coefficient $77/45 \approx 1.711$~\cite{Sen2013Schwarzschild}" — primary-source citation is now adjacent to the numerical claim. **Prior RECOMMENDED 3.1** (`H_CasiniHuerta_Bound_Valid_witness_saturated.ch_bound` proof is `rfl`) and **prior RECOMMENDED 5.2** (counts macro retrofit) are addressed: counts retrofit landed (`\rtChThms` macro at lines 53 and 231 resolves to 7, matches `grep -cE "^theorem " RTCasiniHuertaBounds.lean = 7`); `H_CasiniHuerta_Bound_Valid_witness_saturated.ch_bound` `rfl` discharge is left unchanged as borderline non-vacuity witness (prior review's optional add-strict-witness suggestion was advisory). **HaydenPreskill2007 orphan bibitem removed** (per user changelog) — verified absent from bibliography (no `grep -n "HaydenPreskill"` matches in the note's `paper_draft.tex`). No new BLOCKER/REQUIRED/RECOMMENDED findings. Submission-ready.

## Findings

(none — re-scan finds no new issues; all prior findings resolved or accepted as advisory)

## Verification of strengthening-pass changes

### Class 1 — Sen2013Schwarzschild bibitem added

- **File:** `papers/note_rt_ch_bounds/paper_draft.tex:284-287`
- New bibitem: "A.~Sen, ``Logarithmic corrections to Schwarzschild and other non-extremal black hole entropy in different dimensions,'' JHEP \textbf{04}, 156 (2013); arXiv:1205.0971."
- §intro line 76 now reads: "A separate non-universality witness in the literature is Sen's 4D Schwarzschild log coefficient $77/45 \approx 1.711$~\cite{Sen2013Schwarzschild}, which differs from $-3/2$, indicating that the microscopic log coefficient is not universal across Lagrangian regularizations." ✓ primary-source citation adjacent to the 77/45 numerical claim.
- Title and arXiv ID align with the project's parameter-provenance memory and prior status logs (which referenced `sen_4d_disagrees_with_kaul_majumdar` Lean witness).
- The `Sen2013Schwarzschild` bibkey is consistent with project naming convention (year-of-publication suffix). Registry entry expected — note: `CITATION_REGISTRY` should be checked to ensure the new bibkey is tracked, but this is a registry-side concern, not a paper-side defect.

### Class 1 — HaydenPreskill2007 orphan bibitem removed

- `grep -n "HaydenPreskill" papers/note_rt_ch_bounds/paper_draft.tex` → no matches ✓
- Bibliography at lines 260-289 contains 5 bibitems (RyuTakayanagi2006, CasiniHuerta2009, KaulMajumdar2000, LewkowyczMaldacena2013, Sen2013Schwarzschild) — all 5 are referenced in the body via `\cite{...}`. No orphans. ✓

### Class 7 — counts macros

- `\rtChThms{}` → 7 — matches `grep -cE "^theorem " RTCasiniHuertaBounds.lean = 7` ✓
- `\rtChTests{}` → 29 — matches `tests/test_rt_ch_bounds.py` test count ✓
- Abstract line 53 ("\rtChThms{} substantive theorems") and §VII line 231 ("\rtChThms{} substantive theorems") use the macro consistently ✓
- No "Undefined control sequence" in `paper_draft.log`. ✓

## Class 1 cache-skip summary (updated)

All five bibitems re-inspected:
- `RyuTakayanagi2006` — arXiv:hep-th/0603001, PRL 96, 181602 (2006) — `cache-skip`
- `CasiniHuerta2009` — arXiv:0905.2562, J. Phys. A 42, 504007 (2009) — `cache-skip`
- `KaulMajumdar2000` — PRL 84, 5255 (2000) — `cache-skip`
- `LewkowyczMaldacena2013` — arXiv:1304.4926, JHEP 08, 090 (2013) — `cache-skip`
- `Sen2013Schwarzschild` — arXiv:1205.0971, JHEP 04, 156 (2013) — `cache-skip` (newly added; well-known Sen 4D log-coefficient paper)

## Class 4 cross-paper consistency

No bibkeys shared with the other six papers in this batch. No contradictions.

## Class 3 substantive-body confirmation

All 7 cited theorems re-inspected; bodies unchanged from prior pass. The knife-edge biconditional `rt_eq_kaulMajumdar_iff_trivial_reduced_area` remains substantive (uses `Real.exp_log` to invert log → ratio; not a P3/P4/P5 pattern). The `H_CasiniHuerta_Bound_Valid_witness_saturated.ch_bound` `rfl` discharge remains borderline (saturation function = bound, so equality holds by `le_refl`); prior review's optional `H_CasiniHuerta_Bound_Valid_witness_strict` add-on is **not blocking** and remains advisory.

## Class 6 assumption disclosure

`H_RT_Formula_Valid` and `H_CasiniHuerta_Bound_Valid` tracked external-hypothesis Props remain disclosed in §II with full structural content (`rt_proportional`, `ch_bound`, `c_pos`, `uv_pos` fields). Sufficient.
