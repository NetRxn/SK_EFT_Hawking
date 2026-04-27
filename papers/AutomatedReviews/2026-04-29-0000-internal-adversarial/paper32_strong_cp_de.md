---
paper: paper32_strong_cp_de
reviewer: adversarial-reviewer
model: claude-opus-4-7-1m
review_date: 2026-04-29T00:00:00Z
readiness_gates_version: 1
---

# Adversarial Review — paper32_strong_cp_de

## Summary

Re-scan after strengthening pass. **Prior REQUIRED 3.1** (`combined_zhitnitsky_qtheory_exceeds_observation` did not establish a load-bearing q-theory positivity claim) is **resolved**: `H_BothActiveGivesInconsistency` Prop is now `rho > zhitnitskyDE_eV4 0.1` (line 191-192), so q-theory `> 0` is genuinely needed in `linarith` discharge — drop the hypothesis and the proof breaks. **Prior REQUIRED 5.1** (Planck-natural θ=1 misnomer) is **resolved**: prose now uses "naturally-$O(1)$ value $\theta = 1$" at lines 46, 118, 204, 259, reserving "Planck-natural" for the M_P^4 ≈ 10^112 eV^4 estimate. **Prior RECOMMENDED 5.2** (`zhitnitsky_DE_far_below_planck` weak `< 1e10` upper bound) is **resolved**: Lean theorem at line 124-127 now asserts `zhitnitskyDE_eV4 0.1 < 1.0e-8`, certifying ≥120 orders below 10^112 (matches prose claim). Counts macro `\strongCpDeThms` resolves to 8 (verified `grep -cE "^theorem " StrongCPTopologicalDE.lean = 8`); `\strongCpDeTests` to 14. No new BLOCKER/REQUIRED/RECOMMENDED findings. Submission-ready.

## Findings

(none — re-scan finds no new issues; all three prior findings resolved)

## Verification of strengthening-pass changes

### Class 3 / Class 5 — `H_BothActiveGivesInconsistency` Prop tightened

- **File:** `lean/SKEFTHawking/StrongCPTopologicalDE.lean:191-206`
- **Old Prop body:** `rho_DE_combined > 1.0e-10`
- **New Prop body:** `rho_DE_combined > zhitnitskyDE_eV4 0.1` (line 192)
- **Load-bearing check:** With the new threshold, `zhitnitskyDE_eV4 0.1` alone does not satisfy the Prop (it equals the threshold, not strictly greater); only `zhitnitskyDE_eV4 0.1 + ρ_q` with `ρ_q > 0` clears it. The `linarith` discharge at line 206 consumes both `h_qtheory_pos` and the equality. Drop-test: removing `h_qtheory_pos` makes `linarith` fail. ✓

### Class 5 — "Planck-natural θ=1" prose replaced

- **File:** `papers/paper32_strong_cp_de/paper_draft.tex`
- **Lines updated:** 46, 118, 204, 259 — all now "naturally-$O(1)$ value $\theta = 1$"
- **Lines retaining "Planck-natural":** 42-43 ("Planck-natural estimate $M_P^4 \approx 10^{112}\,\mathrm{eV}^4$"), 67 ("Planck-natural estimate"), 160-162 ("Planck-natural estimate $M_P^4 \approx 10^{112}\,\mathrm{eV}^4$"), 181-182 ("Planck-natural $M_P^4 \approx 10^{112}\,\mathrm{eV}^4$") — all referring to the energy-density estimate, not the angle. ✓ correct semantics.

### Class 3 — `zhitnitsky_DE_far_below_planck` upper bound tightened

- **File:** `lean/SKEFTHawking/StrongCPTopologicalDE.lean:124-127`
- **Old:** `zhitnitskyDE_eV4 0.1 < 1.0e10` (102 orders below M_P^4)
- **New:** `zhitnitskyDE_eV4 0.1 < 1.0e-8` (120 orders below M_P^4) — matches prose claim of "approximately 120 orders of magnitude below" at lines 42, 161
- `norm_num` discharge succeeds (computational; verified by build status of all theorems / `lake build` clean).

### Class 7 — counts macros

- `\strongCpDeThms{}` → 8 — matches `grep -cE "^theorem " StrongCPTopologicalDE.lean = 8` ✓
- `\strongCpDeTests{}` → 14 — matches `tests/test_strong_cp_de.py` test count ✓
- No "Undefined control sequence" in `paper_draft.log`. ✓

## Class 1 cache-skip summary (unchanged from prior run)

All five bibitems are major published works with no smell:
- `VanWaerbeke2025` — arXiv:2506.14182 — `cache-skip`
- `KlinkhamerVolovik2010` — arXiv:0907.4887 — `cache-skip`
- `Pendlebury2015` — arXiv:1509.04411 — `cache-skip`
- `Planck2018` — A&A 641, A6 (2020) — `cache-skip`
- `DESI2024` — JCAP 02, 021 (2025) — `cache-skip`

## Class 4 cross-paper consistency

No bibkeys shared with the other six papers in this batch. No cross-paper contradictions.
