---
paper: paper43_einstein_cartan
reviewer: adversarial-reviewer
model: claude-opus-4-7
review_date: 2026-04-28T17:30:00Z
readiness_gates_version: 1
---

# Adversarial Review — paper43_einstein_cartan

## Summary

Stage-13 fresh-context review of paper43 finds **0 BLOCKER**, **5 REQUIRED**, **5 RECOMMENDED**. All 12 bibkeys are present in CITATION_REGISTRY; the three Wave-6-specific external bibkeys (`Hehl1976`, `KosteleckyRussellTasson2008`, `Lammerzahl2001`) Crossref-verified to canonical metadata. All cited Lean theorem names (`torsionAtCosmologicalBackground_at_planck_natural_below_kostelecky`, `ecResidual_eq_zero_iff_alpha_unity`, `torsionBoundKostelecky_lt_hughesDrever`, `below_kostelecky_implies_below_hughes_drever`, `torsionAmplitude_at_alpha_one_eq_G_N_emerg_times_n`, `torsionAmplitude_pos`, `gNMicroscopic_at_alpha_one_eq_G_N_emerg`, `G_N_from_a2_pos`, `dirac_H_EinsteinCartanExtensionHolds_at_alpha_one`, `perturbed_alpha_not_H_EinsteinCartanExtensionHolds`) exist in the cited Lean modules with substantive (not trivial) proof bodies. Numerical |T_EC| ≃ 2.05×10⁻⁷⁷ GeV at physical M_Pl = 1.221×10¹⁹ verified. Paper draft-ready; submission requires resolution of one wrong-target DOI in `PARAMETER_PROVENANCE`, one stale Lean docstring numerical claim, two human-verification gaps, and one parameter-provenance Lean-name drift.

## Findings

### 1.1 — 🔵 RECOMMENDED — KosteleckyRussellTasson2008 bibitem title minor variant

- **Gate:** CitationIntegrity
- **Location:** `paper43_einstein_cartan/paper_draft.tex:428-430`
- **Observed:** Bibitem title reads "New constraints on torsion from Lorentz-violation searches".
- **Evidence:** Crossref canonical title (https://api.crossref.org/works/10.1103/PhysRevLett.100.111102): "Constraints on Torsion from Bounds on Lorentz Violation". DOI / PRL volume / page / year / author list all match.
- **Expected:** Bibitem title should match the Crossref canonical form.
- **Fix:** Change bibitem #9 title to "Constraints on Torsion from Bounds on Lorentz Violation".
- **Cache:** fresh-fetch

### 2.1 — 🔴 BLOCKER — TORSION_BOUND_HUGHES_DREVER provenance points at a different paper

- **Gate:** ParameterProvenance
- **Location:** `src/core/provenance.py:2942-2961` (`EINSTEIN_CARTAN.TORSION_BOUND_HUGHES_DREVER_GEV`)
- **Observed:** `source: 'Lämmerzahl, Phys. Rev. D 64, 084014 (2001) — Hughes-Drever updated atomic-clock anisotropy bound'`, `doi: '10.1103/PhysRevD.64.084014'`. The paper bibitem `Lammerzahl2001` and the CITATION_REGISTRY entry both correctly point to **Lämmerzahl, Phys. Lett. A 228, 223 (1997)** (DOI 10.1016/S0375-9601(97)00127-8).
- **Evidence:** Crossref `10.1103/PhysRevD.64.084014` resolves to Maluf & da Rocha-Neto, "Hamiltonian formulation of general relativity in the teleparallel geometry", PRD 64, 084014 (2001) — **a different paper, by different authors, on a different topic**. The 2001 PRD attribution is repeated in `lean/SKEFTHawking/EinsteinCartanExtension.lean:78,147` as "Lämmerzahl, Phys. Rev. D 64, 084014 (2001)".
- **Expected:** Provenance entry should cite Lämmerzahl, Phys. Lett. A 228, 223 (1997), DOI `10.1016/S0375-9601(97)00127-8`, matching the CITATION_REGISTRY and bibitem.
- **Fix:** (a) Update `provenance.py` `source` field to "Lämmerzahl, Phys. Lett. A 228, 223 (1997)" and `doi` to `10.1016/S0375-9601(97)00127-8`. (b) Update Lean module docstring lines 78 + 147 to remove the wrong "PRD 64, 084014 (2001)" attribution and replace with "PLA 228, 223 (1997)". Wrong-target DOI in provenance is functionally identical to a wrong-target citation: a reader following the DOI lands at an unrelated paper.
- **Cache:** fresh-fetch

### 2.2 — 🟡 REQUIRED — TORSION_BOUND_KOSTELECKY_GEV unverified by human

- **Gate:** ParameterProvenance
- **Location:** `src/core/provenance.py:2922-2941`
- **Observed:** `human_verified_date: None`. Used in paper §3.1 as the load-bearing observational comparator.
- **Expected:** Submission requires `human_verified_date` populated for any MEASURED-tier parameter that grounds a paper claim.
- **Fix:** Author runs `provenance_dashboard.py`, manually verifies KRT 2008 PRL Table I bound, populates `human_verified_date`.
- **Cache:** —

### 2.3 — 🟡 REQUIRED — TORSION_BOUND_HUGHES_DREVER_GEV unverified by human

- **Gate:** ParameterProvenance
- **Location:** `src/core/provenance.py:2942-2961`
- **Observed:** `human_verified_date: None` AND wrong-target DOI per finding 2.1.
- **Expected:** Submission requires both correct DOI and `human_verified_date`.
- **Fix:** After 2.1 is fixed, populate `human_verified_date`.
- **Cache:** —

### 2.4 — 🟡 REQUIRED — COSMOLOGICAL_SPIN_DENSITY_GEV3 unverified by human

- **Gate:** ParameterProvenance
- **Location:** `src/core/provenance.py:2961-2981`
- **Observed:** `human_verified_date: None` for a DERIVED-tier parameter that grounds the §3.3 numerical verdict.
- **Expected:** Same as above — submission gate requires human verification.
- **Fix:** Verify Kolb-Turner Eq. 3.59 estimate and populate.
- **Cache:** —

### 2.5 — 🟡 REQUIRED — T_CMB_GEV unverified by human

- **Gate:** ParameterProvenance
- **Location:** `src/core/provenance.py:2982-3000`
- **Observed:** `human_verified_date: None`.
- **Expected:** Same.
- **Fix:** Verify Fixsen 2009 ApJ measurement and populate.
- **Cache:** —

### 2.6 — 🔵 RECOMMENDED — Numerical claim 2.05×10⁻⁷⁷ uses physical M_Pl, but Lean theorem proves at planckMassGeV = 1.2×10¹⁹

- **Gate:** ParameterProvenance
- **Location:** `paper_draft.tex:198`; `lean/SKEFTHawking/MicroscopicCoefficientMatch.lean:107` defines `planckMassGeV := 12 * 10^18`.
- **Observed:** Paper §3.3 reports `|T_EC|(M_Pl,16,1) ≃ 2.05×10⁻⁷⁷ GeV`. Numerical reproduction at physical M_Pl=1.221×10¹⁹ → 2.055×10⁻⁷⁷ ✓; at Lean encoding M_Pl=1.2×10¹⁹ → 2.127×10⁻⁷⁷. The 46-decade headroom claim is robust under both, but the headline number quotes the physical-M_Pl variant while the Lean theorem statement is in terms of the `planckMassGeV` encoding.
- **Expected:** Either disclose the rational encoding adopted in Lean (12×10¹⁸ instead of physical 1.221×10¹⁹) or quote the value computed at the Lean encoding for tight Lean↔Python alignment.
- **Fix:** Add a parenthetical remark in §3.3 stating "computed at the rational Lean encoding `planckMassGeV = 12×10¹⁸ GeV` and at the physical `M_Pl = 1.221×10¹⁹ GeV`; both yield ~2×10⁻⁷⁷ GeV with ~46-decade headroom."
- **Cache:** —

### 3.1 — 🔵 RECOMMENDED — Stale numerical claim in Lean module docstring

- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/EinsteinCartanExtension.lean:31-33`
- **Observed:** Module docstring says `|T_EC| ≃ 1.3×10⁻¹¹⁴ GeV` and `~83 orders of magnitude below … 10⁻³¹ GeV`. The paper and the proven theorem assert ~2×10⁻⁷⁷ GeV with ~46-decade headroom.
- **Evidence:** Numerical reproduction (this review): `12*pi/(16*(1.2e19)^2) * 1.3e-39 = 2.13e-77`. The 1.3e-114 / 83-decade values appear nowhere in the proven Lean theorem statement — the actual theorem `torsionAtCosmologicalBackground_at_planck_natural_below_kostelecky` proves only the qualitative `< 1/10^31` inequality (correct) without quoting the saturating value.
- **Expected:** Docstring numerical claim should match the proved theorem and the paper headline number.
- **Fix:** Edit lines 31-33 to read `|T_EC| ≃ 2.1×10⁻⁷⁷ GeV` and `~46 orders of magnitude below`.
- **Cache:** —

### 3.2 — 🔵 RECOMMENDED — Stale Lean theorem name in TORSION_BOUND_KOSTELECKY provenance `notes`

- **Gate:** LeanProofSubstance (per `feedback_python_lean_refs_drift.md`)
- **Location:** `src/core/provenance.py:2939-2941`
- **Observed:** Notes field references Lean theorem `torsionAmplitude_at_planck_natural_below_kostelecky`. The actual shipped name is `torsionAtCosmologicalBackground_at_planck_natural_below_kostelecky`.
- **Expected:** Provenance notes should track the canonical Lean name.
- **Fix:** Replace with `torsionAtCosmologicalBackground_at_planck_natural_below_kostelecky`.
- **Cache:** —

### 3.3 — 🔵 RECOMMENDED — Lammerzahl2001 bibkey naming inconsistency

- **Gate:** CitationIntegrity (informational; bibitem itself is correct)
- **Location:** `src/core/citations.py:2259`; bibkey is `Lammerzahl2001` but registry+bibitem cite the 1997 PLA paper. Lean docstring still has the spurious 2001 PRD attribution.
- **Observed:** Naming-vs-content mismatch. Sub-issue is captured under finding 2.1; this is the bibkey-name shadow.
- **Fix:** Either rename the bibkey to `Lammerzahl1997` project-wide, or document the legacy name explicitly in `notes`. Cosmetic-only after 2.1 is fixed.
- **Cache:** —

## Class coverage

- **Class 1 (citations):** 12 bibkeys. 3 Wave-6-new fresh-fetched; all match modulo the title-variant flagged in 1.1.
- **Class 2 (parameter drift):** Wrong-target DOI in HD provenance (BLOCKER 2.1); 4 entries `unverified` (REQUIRED 2.2-2.5).
- **Class 3 (placeholder/trivial Lean theorems):** All 11 cited theorems reviewed; bodies are substantive (`nlinarith`, `mul_pos`, biconditional with two non-trivial directions, `lt_trans` on a substantively-proved inequality). No P3/P4/P5 flags.
- **Class 4 (cross-paper):** Sakharov1968/Adler1982/Diakonov2011/VladimirovDiakonov2012/Vergeles2025/Vassilevich2003 bibitems consistent with paper42b/paper42.
- **Class 5 (narrative overclaims):** "First formalization" not claimed. "Below all published bounds" backed by a Lean-proved quantitative inequality. No flag.
- **Class 6 (undisclosed assumptions):** Theorem 1's hypotheses (positive Λ_UV, N_f=16, α_EC=1, cosmological-bath spin density) are explicit in §3.2. Match-residual biconditional's `n_spin ≠ 0` hypothesis is disclosed in §4. No flag.
- **Class 7 (counts):** `validate.py --check counts_fresh` PASS; `--check count_literals` PASS for paper43.
- **Class 8 (production runs):** Figure `figures/fig_torsion_obs_bound.png` exists and is mirrored at `papers/paper43_einstein_cartan/figures/`. Notebooks `Phase6e6_EinsteinCartanExtension_{Stakeholder,Technical}.ipynb` exist. Pipeline `src/einstein_cartan/{torsion_amplitude,observational_bounds,ec_residual_assessment}.py` exists. No production-run gap.

## QI Candidate (optional)

`PARAMETER_PROVENANCE` entries are not currently checked for DOI consistency against `CITATION_REGISTRY`: the wrong-target HD DOI (finding 2.1) would have been caught by a `validate.py --check provenance_doi_resolves_to_registry` check that flags any provenance `doi`/`source` whose canonical bibitem (per Crossref) is not also a CITATION_REGISTRY entry, or whose author/year disagrees with a same-keyed bibitem. Suggest adding to Phase 6i Wave 1 hygiene roadmap.
