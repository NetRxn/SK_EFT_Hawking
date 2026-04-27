# Notebook Claims Review — note_rt_ch_bounds

**Reviewer:** claims-reviewer-v2 (notebook adaptation)
**Review date:** 2026-04-29T01:00:00Z
**Reviewer model:** claude-opus-4-7-1m
**Notebooks reviewed:**
- `SK_EFT_Hawking/notebooks/Phase6c5_RTCasiniHuerta_Technical.ipynb`
- `SK_EFT_Hawking/notebooks/Phase6c5_RTCasiniHuerta_Stakeholder.ipynb`

**Cross-reference state observed:**
- Lean module `lean/SKEFTHawking/RTCasiniHuertaBounds.lean` — 7 `theorem` declarations + 2 `structure` Props + 1 `noncomputable def`; 0 sorry; axiom closure `{propext, Classical.choice, Quot.sound}` for every declaration (verified via `lean_deps.json`).
- `docs/counts.tex`: `\rtChThms = 7`, `\rtChTests = 29`.
- Python: `tests/test_rt_ch_bounds.py` has 29 `def test_*` definitions (matches counts).
- Paper: `papers/note_rt_ch_bounds/paper_draft.tex` — 3 pages compiled (latex log "3 pages"), 5 `\bibitem` entries.
- `lean-toolchain` = `leanprover/lean4:v4.29.0`.

---

## Summary by finding class

| Class | Count | Severity | Description |
|---|---|---|---|
| IA | 1 | non-blocking | Stakeholder §7 "9 bibitems" — paper has 5 |
| TP | 0 | — | No literal toolchain pin in either notebook |
| SD | 1 | non-blocking | Technical §9 inventory table omits `ch_log_bound_pos_at_log_pos` (7 thms in module, table lists 6 thms + 2 structures) |
| TN | 0 | — | All 8 theorem references resolve in `lean_deps.json`; the 1 mention of `rt_classical_inconsistent_with_kaul_majumdar` is correctly framed as "removed in cross-wave strengthening" |
| HD | 0 | — | All theorem citations correctly disclose external-hypothesis status (`H_RT_Formula_Valid`, `H_CasiniHuerta_Bound_Valid`) and out-of-scope deferrals |

**Verdict counts (estimated across both notebooks ~30 prose units):** PASS heavy. No blocking issues.

---

## Class IA — Internal arithmetic / count drift

### IA-1 (non-blocking) — Stakeholder bibitem count overstated

- **Notebook:** `Phase6c5_RTCasiniHuerta_Stakeholder.ipynb`, cell `rtch-s-7-md` ("Where to go next").
- **Quote:** "**Note:** `papers/note_rt_ch_bounds/paper_draft.tex` — short formalization note (3 pages, 9 bibitems)."
- **Observed.** `grep -cE "^\\bibitem" papers/note_rt_ch_bounds/paper_draft.tex` = **5**, not 9. The bibliography has exactly Ryu-Takayanagi 2006, Casini-Huerta 2009, Kaul-Majumdar 2000, Lewkowycz-Maldacena 2013, Sen 2013Schwarzschild — all five resolve in `CITATION_REGISTRY` with consistent metadata.
- **Severity.** Non-blocking — the page count (3) is correct. Trivial drift; correct to either "5 bibitems" or expand the bibliography.
- **Maps to:** Gate 9 NumericalFreshness.

---

## Class SD — Stealth pipeline-vs-prose drift

### SD-1 (non-blocking) — Technical §9 inventory table inconsistent with `\rtChThms = 7`

- **Notebook:** `Phase6c5_RTCasiniHuerta_Technical.ipynb`, cell `rtch-t-9-md` ("Lean theorem inventory (7 substantive)").
- **Heading:** "Lean theorem inventory (7 substantive)". The table that follows lists 8 numbered rows.
- **Observed.** Of the 8 rows, 2 are `structure` Props (`H_RT_Formula_Valid`, `H_CasiniHuerta_Bound_Valid`) and 6 are theorems. The Lean module ships **7** `theorem` declarations:
  - rt_entropy_pos
  - rt_kaulMajumdar_gap_at_reduced_area_two
  - rt_eq_kaulMajumdar_iff_trivial_reduced_area
  - rt_falsified_by_kaul_majumdar
  - **ch_log_bound_pos_at_log_pos** (omitted from the table)
  - H_CasiniHuerta_Bound_Valid_witness_saturated
  - kaulMajumdar_not_H_RT
- The Section 5 prose of the notebook discusses `rt_falsified_by_kaul_majumdar` and `kaulMajumdar_not_H_RT`; Section 6 discusses the saturated witness; but `ch_log_bound_pos_at_log_pos` is referenced in the figure docstring (`src/core/visualizations.py:9700`) and the paper draft (`papers/note_rt_ch_bounds/paper_draft.tex` line 181), yet the notebook inventory table never lists it. This is the *only* CH-positivity theorem in the module.
- **Severity.** Non-blocking. The heading "(7 substantive)" matches `\rtChThms` and matches `grep -c "^theorem "` = 7, but the table has only 6 of those 7 theorems plus the 2 structures, giving 8 entries that don't reconcile cleanly with the heading.
- **Recommendation.** Either (a) add a row 9 for `ch_log_bound_pos_at_log_pos` and update heading to "9 entries (7 theorems + 2 external-hypothesis Props)", or (b) drop the structures from the table and restore the count to 7 actual theorems.
- **Maps to:** Gate 5 LeanProofSubstance.

---

## Class TN — Theorem-name reference drift

**No findings.** Verified all theorem references against `lean_deps.json`:

| Reference | Found in `lean_deps.json` |
|---|---|
| `H_RT_Formula_Valid` | yes (RTCasiniHuertaBounds) |
| `H_CasiniHuerta_Bound_Valid` | yes (RTCasiniHuertaBounds) |
| `rt_entropy_pos` | yes |
| `rt_kaulMajumdar_gap_at_reduced_area_two` | yes |
| `rt_eq_kaulMajumdar_iff_trivial_reduced_area` | yes |
| `rt_falsified_by_kaul_majumdar` | yes |
| `H_CasiniHuerta_Bound_Valid_witness_saturated` | yes |
| `kaulMajumdar_not_H_RT` | yes |
| `kaulMajumdarS` | yes (BHEntropyMicroscopic) |
| `senFourDimSchwarzschildLogCoeff` | implicitly via `sen_4d_log_coeff()` Python wrapper; Lean target also exists |
| `sen_4d_disagrees_with_kaul_majumdar` | yes (BHEntropyMicroscopic) |
| `rt_classical_inconsistent_with_kaul_majumdar` | **MISSING** — but notebook **correctly** discloses this as "removed (2026-04-28-0030) cross-wave strengthening" in cell `rtch-t-9-md`; the prose framing absorbs the absence. PASS. |

The notebook's only mention of the removed theorem is as a historical reference — never asserted as currently existing.

---

## Class TP — Toolchain pin drift

**No findings.** Neither notebook contains a literal Lean version mention (e.g. "Lean v4.29.0") or Mathlib `rev` hash. The intro text "verified `propext, Classical.choice, Quot.sound` only" is verified — every theorem in the module has axiom closure exactly that set (per `lean_deps.json` `axiom_deps_core` field).

---

## Class HD — Hypothesis disclosure gap

**No findings.** The notebooks repeatedly and explicitly disclose:

1. The two external hypotheses `H_RT_Formula_Valid` and `H_CasiniHuerta_Bound_Valid` are introduced in cell `rtch-t-1-md` and tracked through the rest of the technical notebook.
2. Stakeholder §1 makes the same disclosure in plain language.
3. Stakeholder §6 ("Honest scope") explicitly lists **four** out-of-scope items (bulk minimal-surface Lewkowycz-Maldacena replica trick, full CH derivation from modular Hamiltonian, AdS/CFT spectrum identification, Sen-vs-Kaul-Majumdar adjudication) — matches the paper draft §7 deferrals.
4. Technical §9 ends with the same out-of-scope list.

No theorem is cited as "verified" without disclosing its tracked-hypothesis dependence.

---

## Quantitative anchor verifications (Class IA cross-checks)

| Claim | Notebook | Source-of-truth | Observed | Status |
|---|---|---|---|---|
| Gap at reduced area = 2 is exactly (3/2) log 2 ≈ 1.040 | Tech §3, Stake §2 | `rt_kaulMajumdar_gap_at_reduced_area_two` | 1.0397207708 (computed); 1.5·log(2) = 1.0397207708 (exact match to 1e-12) | PASS |
| Sen 4D log coefficient = 77/45 ≈ 1.711 | Tech §7, Stake §3 | `senFourDimSchwarzschildLogCoeff = 212/45 - 3` | 212/45 - 3 = 1.711111… = 77/45 | PASS |
| Kaul-Majumdar log coefficient = -3/2 = -1.5 | Tech §7, Stake §3 | `kaulMajumdarS` definition | -3/2 in Lean module line 87 | PASS |
| Sen-Kaul-Majumdar gap = 289/90 ≈ 3.211 | Tech §7, Stake §3 | `SEN_KAUL_MAJUMDAR_COEFF_GAP = 289/90` | 77/45 - (-3/2) = (154+135)/90 = 289/90 = 3.2111… | PASS |
| Knife-edge agreement at A = 4 G_N (reduced area = 1) | Tech §4, Stake §5 | `rt_eq_kaulMajumdar_iff_trivial_reduced_area` | Verified via Python: agree only at A=4, G_N=1 | PASS |
| 2D CFT central charges: Ising 1/2, tricritical Ising 7/10, 3-state Potts 4/5, free boson 1 | Tech §6, Stake §4 | Standard 2D CFT (also in `fig_rt_ch_bounds_mtc`) | matches | PASS |
| 0 sorry / 0 new axioms / kernel axioms only | Tech intro, §9 | `grep -c "  sorry"` = 0; `lean_deps.json` axiom_deps | confirmed | PASS |
| Test count `\rtChTests = 29` (paper draft only) | (notebooks don't claim a number, but reference test suite) | `tests/test_rt_ch_bounds.py` | 29 | PASS |
| Falsifier witness: A=8, G_N=1 → S_KM ≈ 0.96 ≠ 2 | Tech §5, Stake §3-implicit | `kaulMajumdar_not_H_RT` proof body | 2 - (3/2)·log 2 = 0.9602792292 | PASS |

All numeric anchors agree to 1e-12.

---

## Citation cross-check (Class IA / general)

Verified each notebook citation against `src/core/citations.py::CITATION_REGISTRY`:

| Bibkey | Notebook claim | Registry entry | Match |
|---|---|---|---|
| RyuTakayanagi2006 | "Ryu and Takayanagi (2006)" | PRL 96, 181602 (2006); hep-th/0603001 | ✓ |
| CasiniHuerta2009 | "Casini and Huerta (2009)" | J. Phys. A 42, 504007 (2009); 0905.2562 | ✓ |
| KaulMajumdar2000 | "Kaul–Majumdar (2000)" | PRL 84, 5255 (2000); gr-qc/0002040 | ✓ |
| LewkowyczMaldacena2013 | "Lewkowycz-Maldacena replica trick" | JHEP 08, 090 (2013); 1304.4926 | ✓ |
| Sen2013Schwarzschild | "Sen (2012) computed … using string-theory loop amplitudes for 4D Schwarzschild" + "(arXiv:1205.0971, JHEP 2013)" | JHEP 04, 156 (2013); 1205.0971 | ✓ — arXiv 2012 / journal 2013, both correctly cited |

All five citations have `doi_verified: None` flag in `CITATION_REGISTRY` (per memory `feedback_citation_verification_required.md`, this means LLM-cataloged but not WebFetch-verified). This is **not** a finding for the notebooks — the notebooks accurately reflect the registry's metadata. It is a registry-side TODO outside the scope of this notebook review.

---

## Reconciliation with prior `claims_review.json`

The paper draft's `papers/note_rt_ch_bounds/claims_review.json` (review_date 2026-04-27) reported 0 blocking issues, 3 IA findings (all already absorbed), 0 TP/SD/TN/HD. Current notebook review surfaces:

- **IA-1 (bibitem 9 vs 5)** — new, notebook-specific (paper draft `claims_review.json` did not surface a bibitem-count claim because the paper itself does not claim a count).
- **SD-1 (inventory table inconsistency)** — new, notebook-specific (the paper draft summary §6 only references `\rtChThms` macro + `\rtChTests` macro, which expand correctly).

No prior notebook review exists at `papers/AutomatedReviews/2026-04-29-0100-notebook-claims-review/` for reconciliation; this is a first-pass review.

---

## Honest-scope and out-of-scope disclosure

Both notebooks honestly disclose all four deferrals (replica-trick, modular-Hamiltonian CH derivation, AdS/CFT spectrum, Sen-vs-KM adjudication). Stakeholder §6 ("Honest scope") is particularly explicit about what the note does **not** prove. Technical §9 closes with the same out-of-scope list in compressed form.

The notebooks' only "stretch" claim is the meta-claim "Quantum-gravity model-builders write down classical RT and ignore log corrections all the time" (Stakeholder §6). This is a qualitative editorial assertion, not a verifiable claim — assigned `qualitative` / INFO verdict; non-blocking.

---

## Recommendations

1. **IA-1 (Stakeholder §7).** Replace "9 bibitems" with "5 bibitems", or add 4 more bibitems to the paper draft if the stakeholder count was the intended target.
2. **SD-1 (Technical §9).** Either:
   - Add a 9th row to the inventory table for `ch_log_bound_pos_at_log_pos` (simplest fix), and rephrase heading to "Lean inventory (7 substantive theorems + 2 external-hypothesis Props)"; or
   - Restrict the table to the 7 theorems and move structures to §1.
3. (Non-finding) Consider adding a one-line cross-reference in the Technical notebook §9 to the visualization function `fig_rt_ch_bounds_mtc` Lean dependency list, which already lists `ch_log_bound_pos_at_log_pos` — would make the inventory drift self-correcting.

---

## Verdict summary

**Notebooks are publication-ready modulo two trivial drift issues (IA-1 bibitem count, SD-1 table omission).** No blocking issues. All theorem references resolve. All numeric anchors verified to 1e-12. All hypothesis disclosures clean. All citations registered with consistent metadata. The cross-wave-strengthening removal of `rt_classical_inconsistent_with_kaul_majumdar` is correctly disclosed as historical, not asserted as live.
