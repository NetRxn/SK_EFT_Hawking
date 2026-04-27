---
paper: paper37_chiral_ssb
artifact: notebooks (Phase6d2_ChiralSSB_Technical.ipynb + Phase6d2_ChiralSSB_Stakeholder.ipynb)
reviewer: adversarial-reviewer (notebook variant)
model: claude-opus-4-7[1m]
review_date: 2026-04-29T02:00:00Z
readiness_gates_version: 1
---

# Adversarial Review — paper37_chiral_ssb (notebooks)

## Summary

Three BLOCKER findings, four REQUIRED, two RECOMMENDED across the technical and stakeholder notebooks. The most material defects are (a) "1 part in 10⁴" precision claim that the notebooks' own console output contradicts (true value: 1 part in **4054**, i.e. 2.5×10⁻⁴, not 10⁻⁴), (b) PDG charged pion / decay constant values labeled "PDG" without disclosing they are rounded working values (139.57→137 MeV, 92.4→92 MeV) — the technical notebook does this; the stakeholder notebook discloses honestly, (c) the proton-mass-Higgs-fraction stakeholder claim "Higgs ~3% / chiral SSB ~97%" is off by a factor of ~3 from the standard textbook ~1%/~99% breakdown. The Lean substance, the cross-bridge to `WetterichNJL.njl_scalar_upper_bound`, and the `chiral_unbroken_violates_gmor` contrapositive all check out as genuinely load-bearing on direct inspection. The CITATION_REGISTRY entry for FLAG2021 has an internal arithmetic inconsistency (`-(272 MeV)^3 ~= -0.0227 GeV^3` is wrong; 272³ ≈ 0.0201 GeV³ — the figure 0.0227 implies (283 MeV)³). The notebooks are not submission-ready until the precision claim and the PDG-anchor labeling are fixed.

## Findings

### 1.1 — 🔴 BLOCKER — FLAG2021 registry entry has an internal arithmetic inconsistency

- **Gate:** CitationIntegrity (also touches ParameterProvenance Gate 3)
- **Location:** `src/core/citations.py:3327` (registry); both notebooks reference `FLAG_LATTICE_VALUE = -0.0227 GeV³` and the Lean module `lean/SKEFTHawking/ChiralSSB_QCD.lean:54` says `≈ −(283 MeV)³ ≈ −0.0227 GeV³`.
- **Observed:** Registry entry `FLAG2021.provides` says `'Lattice quark condensate <q-bar q> = -(272 MeV)^3 ~= -0.0227 GeV^3'`. But 272³ MeV³ = 2.012×10⁷ MeV³ = 0.02012 GeV³, NOT 0.0227 GeV³. 0.0227 GeV³ corresponds to (283 MeV)³ (since 283³ = 2.267×10⁷). The Lean module and the notebooks consistently use 283 MeV; the registry alone is wrong.
- **Evidence:** `python3 -c "print(0.272**3, 0.283**3, 0.0227**(1/3))"` → `0.02011 0.02266 0.2831`.
- **Expected:** Either `-(283 MeV)^3 ~= -0.0227 GeV^3` (matches downstream artifacts) or `-(272 MeV)^3 ~= -0.0201 GeV^3` (matches the FLAG SU(3)-flavor-limit value if that is the chosen anchor).
- **Fix:** Update `src/core/citations.py:3327` `provides` field to match the value actually used (presumably 283 MeV → 0.0227 GeV³), then run `validate.py --check citations_resolve` to confirm the registry-vs-paper agreement.
- **Cache:** fresh-fetch (FLAG2021 arXiv 2111.09849 abstract verified; specific numerical FLAG-2021 condensate value not directly readable from the abstract page; primary source pull-from-PDF failed in this fresh-context — flag for human verification).

### 1.2 — 🟡 REQUIRED — FLAG-2021 primary-source numerical anchor unverified against published tables

- **Gate:** ParameterProvenance
- **Location:** `src/chiral_ssb/quark_condensate.py:34` `FLAG_LATTICE_VALUE = QuarkCondensate(sigma=-0.0227)`; `lean/SKEFTHawking/ChiralSSB_QCD.lean:54-59` `flagLatticeValue := ⟨-0.0227, by norm_num⟩`.
- **Observed:** No `PARAMETER_PROVENANCE` entry exists for `PDG_M_PI`, `PDG_F_PI`, `PDG_M_Q`, or `FLAG_LATTICE_VALUE`. `grep -in "pdg_m_pi\|pdg_f_pi\|pdg_m_q\|flag_lattice\|chiral_ssb\|m_pi\|f_pi\|gmor\|0.137\|0.092\|0.0035\|0.0227" src/core/provenance.py` returns nothing. The notebooks both display these values as if PDG/FLAG ground-truth without any human-verified provenance trace.
- **Evidence:** Empty grep output for any of these parameters in `src/core/provenance.py`.
- **Expected:** Each of {PDG_M_PI, PDG_F_PI, PDG_M_Q, FLAG_LATTICE_VALUE} should have a `PARAMETER_PROVENANCE` entry with `primary_source` (FLAG-2021 table reference / PDG-2022 page reference), `llm_verified_date`, and ultimately `human_verified_date`.
- **Fix:** Add four entries to `PARAMETER_PROVENANCE`. Cite the specific FLAG 2021 table/section for the chiral condensate (the review distinguishes N_f=2 and N_f=2+1 averages; the value adopted should be explicitly tied to one of them); cite PDG-2022 listings pages for m_π±, f_π, (m_u+m_d)/2.
- **Cache:** fresh-fetch attempted; arXiv abstract page for 2111.09849 confirmed paper exists (Aoki et al., FLAG, EPJC 82, 869, 2022), but the abstract page does not surface the specific σ value — the assertion `σ=-0.0227 GeV³` was not cross-checked against a primary table in this review.

### 1.3 — 🔴 BLOCKER — "1 part in 10⁴" precision claim contradicts the notebooks' own computed residual

- **Gate:** NumericalFreshness (Gate 9) + NarrativeGrounding (Gate 7) — both apply.
- **Location:** Multiple. Paper draft `paper_draft.tex:47, 134, 176, 236`; technical notebook `Phase6d2_ChiralSSB_Technical.ipynb` cells `p37t-3-md/code` and figure annotation; stakeholder notebook `Phase6d2_ChiralSSB_Stakeholder.ipynb` markdown cells `p37s-intro` and `p37s-2-md` and the figure annotation.
- **Observed:** All four artifacts assert "~1 part in 10⁴" precision. The actual computed relative residual from both notebooks' own console output is `2.47e-04`, i.e. `~1 part in 4054`. The notebook explicitly prints `relative residual = 2.47e-04 (~1 part in 4054)` immediately above markdown that says "1 part in 10⁴". The factor-2.5 mismatch is not a rounding nuance — `1 part in 10⁴` typically denotes 10⁻⁴ precision; the actual value is 2.5×10⁻⁴, which is "1 part in ~4000". The stakeholder narrative leans on this number to argue "no fitted parameter; identity must hold to high precision". Sloppy precision arithmetic in a notebook explicitly demonstrating an IDENTITY between four numbers undermines the central rhetorical claim.
- **Evidence:** Notebook output cells show `relative residual = 2.47e-04 (~1 part in 4054)` (technical line 128, stakeholder line 64). Independent recomputation confirms: `(0.137² × 0.092² − 2 × 0.0035 × 0.0227) / (0.137² × 0.092²) = 3.918e-08 / 1.589e-04 = 2.466e-04`.
- **Expected:** Replace "~1 part in 10⁴" with "~2.5 parts in 10⁴" or "~1 part in 4000" or "absolute residual ~4×10⁻⁸ GeV⁴" (which is honest and unambiguous). Choose ONE phrasing and propagate consistently across paper, technical notebook, stakeholder notebook, figure annotation.
- **Fix:** Mechanical text edit across 8 occurrences (4 in paper, 2 in technical notebook, 2 in stakeholder notebook). Re-run figure render so that the bar-chart annotation aligns.
- **Cache:** N/A (numerical recomputation).

### 1.4 — 🔴 BLOCKER — Technical notebook labels rounded working values as "PDG" without disclosure

- **Gate:** ParameterProvenance + NarrativeGrounding
- **Location:** `Phase6d2_ChiralSSB_Technical.ipynb` cell `p37t-2-code` (lines 90-92 of the JSON, output lines 82-84). The print statements read:
    `PDG charged pion mass m_π = 0.137 GeV (137.0 MeV)`
    `PDG pion decay constant f_π = 0.092 GeV (92.0 MeV)`
    `PDG light-quark mass m_q = 0.0035 GeV (3.50 MeV, MS-bar at 2 GeV)`
- **Observed:** PDG-2022 charged pion mass is 139.57 MeV (not 137 MeV — discrepancy 1.85%). PDG-quoted f_π in the chiral-limit convention is 92.4 MeV (the notebook's 92 MeV is fine to half a percent), but the experimental convention uses ~130 MeV — the choice of convention should be stated. The technical notebook prints these as "PDG" values without flagging that they are rounded. Contrast: the *stakeholder* notebook DOES disclose honestly (`"PDG 139.57 MeV charged ... this notebook uses the project's working value ≈ 137 MeV"`, `"PDG 92.4 MeV; this notebook uses ≈ 92 MeV"`). The technical notebook does not.
- **Evidence:** Wikipedia/Pion confirms m_π± = 139.57039(18) MeV per PDG; the Pion Wikipedia page also reports f_π = "about 130 MeV" in the experimental convention. The notebook's docstring `src/chiral_ssb/gmor_check.py:22` does say `PDG_M_PI: float = 0.137  #: PDG charged pion mass in GeV` — same labeling drift.
- **Expected:** Either (a) update PDG_M_PI to 0.13957 GeV and re-run; or (b) keep 0.137 but rename and relabel ("WORKING_M_PI" or print as "rounded working value"). The technical notebook should at minimum mirror the stakeholder notebook's honest disclosure language.
- **Fix:** Change technical notebook print labels to `'  Working m_π = 0.137 GeV  (PDG charged-pion mass is 139.57 MeV; 0.137 used here as a 1.5%-rounded working value)'`. Same pattern for f_π. Apply the matching change in `src/chiral_ssb/gmor_check.py` docstrings.
- **Cache:** fresh-fetch (PDG charged pion 139.57 MeV via Wikipedia/Pion page; PDG f_π chiral-limit ≈ 92.4 MeV).

### 1.5 — 🟡 REQUIRED — Stakeholder notebook "Higgs 3% / QCD 97%" overstates Higgs share by ~3×

- **Gate:** NarrativeGrounding (overclaim — feasibility/attribution-claim)
- **Location:** `Phase6d2_ChiralSSB_Stakeholder.ipynb` markdown cell `p37s-intro`: "the Higgs contributes only ∼3%. The remaining 97% comes from a different mechanism: chiral symmetry breaking in QCD."
- **Observed:** The standard textbook breakdown is **~1% from Higgs / ~99% from QCD** (binding energy + condensate + gluon contributions), not 3%/97%. Wikipedia/Proton: "rest masses of quarks contribute only about 1% of a proton's mass, while the remaining ~99% comes from quantum chromodynamics binding energy." Wikipedia/Higgs_boson: "approximately 99% of the mass of baryons (composite particles such as the proton and neutron) is due instead to quantum chromodynamic binding energy". The 3%/97% framing is a factor-of-3 overstatement of the Higgs share that doesn't appear in standard reviews.
- **Evidence:** Two independent Wikipedia sources (Proton article quark mass section; Higgs boson article on baryon mass) both state ~1%/~99%.
- **Expected:** Revise to "the Higgs contributes only ∼1%; the remaining ∼99% comes from QCD dynamics — quark binding energy, gluon kinetic energy, and the chiral condensate." The intended rhetorical point (Higgs is small compared to QCD) is even stronger at the correct ratio. Note also that the stakeholder narrative attributes the QCD 99% specifically to "chiral symmetry breaking" — but the breakdown per Wikipedia/Proton is roughly 9% condensate + 32% quark KE + 37% gluon KE + 23% anomalous gluon trace; chiral-condensate fraction is the smallest of the four QCD-side components, not "the dominant mass scale of the proton" as the cell asserts.
- **Fix:** Replace numerical fractions with primary-source values (Wikipedia/Proton breakdown is a starting point; better is a review article or PDG mini-review). Soften "the dominant mass scale" — the chiral condensate sets ONE mass scale (≈283 MeV); the gluon dynamics set another comparable one. Better phrasing: "an essential ingredient of QCD vacuum structure that drives chiral SSB" — without the misleading "dominant" superlative.
- **Cache:** fresh-fetch (Wikipedia/Proton, Wikipedia/Higgs_boson).

### 2.1 — 🟡 REQUIRED — Technical notebook says `H_TetradQuarkScalesNatural` is "Two-conjunct" but Lean has THREE

- **Gate:** AssumptionDisclosure (Gate 6) + LeanProofSubstance (Gate 5 — accuracy of paper-to-Lean reference)
- **Location:** `Phase6d2_ChiralSSB_Technical.ipynb` markdown cell `p37t-5-md`: `"Two-conjunct (drop-conjunct test passes — both halves load-bearing)."`
- **Observed:** The Lean Prop has three conjuncts: `0 < sigma_scale ∧ sigma_scale / 10 ≤ v_tetrad ∧ v_tetrad ≤ 10 * sigma_scale` (`ChiralSSB_QCD.lean:191-194`). The Lean docstring even labels them `(a) sigma_scale > 0`, `(b) sigma_scale / 10 ≤ v_tetrad`, `(c) v_tetrad ≤ 10 * sigma_scale`. The `H_TetradQuarkScalesNatural` Python dataclass also exposes three properties (`positivity`, `lower_bound`, `upper_bound`).
- **Evidence:** `lean/SKEFTHawking/ChiralSSB_QCD.lean:188-194`; `src/chiral_ssb/tetrad_ratio.py:32-49`.
- **Expected:** "Three-conjunct (drop-conjunct test passes per conjunct — `sigma_scale > 0`, lower factor-10 bound, upper factor-10 bound)."
- **Fix:** One-line edit in technical notebook cell `p37t-5-md`.

### 2.2 — 🔵 RECOMMENDED — Lean theorem `gmor_pdg_match` proves `< 1.0e-4 GeV⁴`, NOT `< 1 part in 10⁴ relative`

- **Gate:** LeanProofSubstance (gate-5 honesty about what the Lean theorem actually establishes)
- **Location:** `lean/SKEFTHawking/ChiralSSB_QCD.lean:134-138`. Notebook prose `Phase6d2_ChiralSSB_Technical.ipynb:p37t-3-code` says `"Lean theorem gmor_pdg_match: |LHS - RHS| < 1e-4 GeV⁴ (proved by norm_num)."` then earlier prose says `"GMOR holds to ~1 part in 10⁴"`.
- **Observed:** The Lean theorem statement is `|gmor_lhs 0.137 0.092 - gmor_rhs_real 0.0035 (-0.0227)| < 1.0e-4` — an absolute bound on the residual in GeV⁴. This is consistent with the actual residual `≈ 3.92e-8` (well within `1.0e-4`). What the Lean theorem proves is a LOOSE absolute bound, not a tight relative-precision claim. The notebook's "1 part in 10⁴" prose adjacent to the Lean theorem citation can be misread as the *Lean theorem* establishing relative precision; it does not.
- **Expected:** Be explicit: "Lean theorem `gmor_pdg_match` establishes the loose absolute bound `|LHS − RHS| < 10⁻⁴ GeV⁴`, with the actual achieved residual being ~4×10⁻⁸ GeV⁴ (~2.5 parts in 10⁴ of LHS)."
- **Fix:** Add one clarifying sentence to cell `p37t-3-code` markdown immediately following the `gmor_pdg_match` reference.

### 3.1 — 🟡 REQUIRED — Discipline trend "6c.3 = 12, 6b.1 = 5, 6d.1 = 6, 6d.2 = 4" — not directly verifiable in this notebook context

- **Gate:** NarrativeGrounding (project-internal claim that should be ledger-backed)
- **Location:** `Phase6d2_ChiralSSB_Technical.ipynb` cell `p37t-8-md` (final inventory): `"Discipline trend: 6c.3 = 12, 6b.1 = 5, 6d.1 = 6, **6d.2 = 4** (1 first-pass + 2 second-pass + 1 third-pass)."`
- **Observed:** The 6d.2=4 (1+2+1) breakdown matches the in-module narrative in `ChiralSSB_QCD.lean:296-307`. The other three values (6c.3=12, 6b.1=5, 6d.1=6) reproduce the trend recorded in the project memory index (per CLAUDE.md memory anchors `project_phase6c_w3_shipped.md`, `project_phase6b_w1_shipped.md`, `project_phase6d_w1_shipped.md`). However, the notebook itself does not link to a project ledger or trend document — a fresh-context reader cannot verify these earlier counts without project-internal access.
- **Evidence:** `ChiralSSB_QCD.lean:286-307` corroborates 6d.2=4. The 6c.3=12 etc. values are corroborated only by project memory anchors, which are not committed primary sources.
- **Expected:** Either (a) link to a project doc that consolidates the discipline trend (e.g. `docs/discipline_trend.md` or similar), or (b) drop the cross-wave comparison from the notebook and keep it in a project-internal document.
- **Fix:** Add a footnote: "Cross-wave numbers per `feedback_post_wave_strengthening_audit.md` and per-wave `project_phase6*_shipped.md` memory anchors." Or remove the trend from the public notebook.

### 4.1 — 🔵 RECOMMENDED — Technical notebook uses "1 part in 4054" implicit precision but renders figure annotation "~1 part in 10⁴"

- **Gate:** NumericalFreshness
- **Location:** Figure annotation `Phase6d2_ChiralSSB_Technical.ipynb:437`: `"|LHS − RHS| ≈ 3.92e-08 GeV⁴<br>(~1 part in 10⁴)"`. Console output `Phase6d2_ChiralSSB_Technical.ipynb:128`: `"relative residual = 2.47e-04 (~1 part in 4054)"`.
- **Observed:** Same internal-conflict pattern as 1.3, surfaced through the figure annotation. The figure ships the misleading "1 part in 10⁴" text rendered into the PNG; same defect appears in `Phase6d2_ChiralSSB_Stakeholder.ipynb:317`.
- **Expected:** Update the figure-generation code in `src/core/visualizations.py:fig_gmor_relation_verification` to use the corrected language; re-render via `scripts/review_figures.py`.
- **Fix:** Same as 1.3 — fixing the figure source resolves both notebooks' annotations.

### 5.1 — 🟡 REQUIRED — `gmor_pdg_match` and the chiral_unbroken_violates_gmor proof are paper-grade BUT depend on a 1.5%-off `m_π` value

- **Gate:** ComputationCorrectness (Gate 4) + LeanProofSubstance honesty
- **Location:** `lean/SKEFTHawking/ChiralSSB_QCD.lean:134-138`.
- **Observed:** The Lean theorem `gmor_pdg_match` proves `|gmor_lhs 0.137 0.092 - gmor_rhs_real 0.0035 (-0.0227)| < 1.0e-4` — a `norm_num`-discharged numerical identity at the *literal* values 0.137, 0.092, 0.0035, -0.0227. None of these are the precise PDG/FLAG central values; m_π is 1.5% off (139.57 → 137); f_π is 0.4% off (92.4 → 92). The theorem is technically sound — it proves what its statement says — but the paper prose (and the notebook) describe this as the "PDG/FLAG numerical agreement check at central values". A reader expecting the published-PDG value would be misled.
- **Evidence:** PDG charged pion 139.57 MeV (Wikipedia/Pion + PDG ID 22 page); PDG f_π chiral-limit ≈ 92.4 MeV (Wikipedia/Pion).
- **Expected:** Either (a) re-prove `gmor_pdg_match` at the actual PDG values (0.13957, 0.0924, 0.0035, -0.0227) — `norm_num` should still close it; the residual will shift slightly but stay below 10⁻⁴; or (b) rename the theorem `gmor_working_match` and acknowledge in the docstring that the literal values are rounded for `norm_num` arithmetic convenience.
- **Fix:** Option (a) is cleaner — the proof tactic `rw [abs_lt]; refine ⟨?_, ?_⟩ <;> norm_num` is robust. Re-run `lake build SKEFTHawking.ChiralSSB_QCD` to confirm.

### 6.1 — 🟡 REQUIRED — Technical notebook describes the cross-bridge but does not surface that the GMOR identity has known O(1%) chiral-perturbation-theory corrections at higher order

- **Gate:** AssumptionDisclosure
- **Location:** `Phase6d2_ChiralSSB_Technical.ipynb` cell `p37t-3-md`: "This is an algebraic consequence of soft-pion theorems and PCAC applied to QCD." Stakeholder notebook §6 ("Honest scope") DOES disclose: "It is leading-order in chiral perturbation theory. Higher-order corrections at the ~1% level exist; the ~0.01% residual is well below those corrections, which is why the identity holds at this precision."
- **Observed:** The technical notebook does not flag that GMOR is the leading-order ChPT relation. Without this caveat, the prose "the identity is verified at the precision of the underlying inputs" reads as if GMOR is exact, which it is not.
- **Expected:** One sentence in the technical notebook (likely in cell `p37t-3-md` or `p37t-7-md`) acknowledging GMOR is leading-order ChPT.
- **Fix:** Mirror the stakeholder notebook's "Honest scope" §3 caveat in the technical notebook.

## QI Candidate

**Pattern: numerical-precision claims drift from the notebook's own console output.** The same notebook prints "1 part in 4054" in its console and then asserts "1 part in 10⁴" in adjacent markdown — a factor-2.5 mismatch the author and prior reviewers missed. This is structurally identical to the count-literal-drift pattern that drove `validate.py --check count_literals` (Gate 9 — NumericalFreshness). Suggested QI: extend `numerical_literals` validation to scan notebooks (`*.ipynb`) for inline "X part(s) in 10^N" / "10^{-N}" strings and cross-check against printed cell output of `relative residual = ...`. Alternatively, parse the markdown cell's precision claim and compare to the immediately-preceding code cell's printed `relative residual` value; any drift > 50% should fail the check.

## Methodology notes

- WebFetch successes: arXiv abstract page for 2111.09849 (FLAG Review 2021 confirmed); Wikipedia/Nambu-Jona-Lasinio model (PR 122, 345 (1961) confirmed); Wikipedia/Gell-Mann-Oakes-Renner (PR 175, 2195 (1968) confirmed); Wikipedia/Pion (m_π± = 139.57 MeV); Wikipedia/Quark (m_u, m_d ≈ 3.5 MeV avg); Wikipedia/Proton + Wikipedia/Higgs_boson (proton-mass breakdown 1%/99%); academic.oup.com PTEP page for PDG2022 (Workman et al., PTEP 2022, article number not retrievable from page metadata — registry value 083C01 not directly verified).
- WebFetch failures (403 / 404 / timeout): doi.org redirects to APS for PR 122/175 returned 403; flag.unibe.ch timed out; PDG PDF listings binary-unreadable.
- Cross-paper consistency: `paper37_chiral_ssb` is the only paper using `GMOR1968`, `FLAG2021`, `NambuJonaLasinio1961` bibkeys; `PDG2022` is shared but registry values agree across papers. No CONTRADICTS edges induced.
- Lean substance: `chiral_unbroken_violates_gmor` proof body genuinely uses all five hypotheses (positivity composition); `njl_scalar_bounded_consistent_with_chiral_broken` cross-bridge invokes the upstream `WetterichNJL.njl_scalar_upper_bound` whose body is `field_simp; nlinarith [mul_le_mul_of_nonneg_left ...]` — substantive. Both pass adversarial scrutiny.
- The technical-notebook discipline-trend value `6d.2 = 4 (1 first-pass + 2 second-pass + 1 third-pass)` is corroborated by the in-module narrative (`ChiralSSB_QCD.lean:285-307`) and by the project memory anchor `project_phase6d_w2_shipped.md`.
