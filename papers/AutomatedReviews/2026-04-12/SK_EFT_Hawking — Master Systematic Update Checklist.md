# SK_EFT_Hawking — Master Systematic Update Checklist
*Consolidated from three review rounds: citation audit, LKB/Paper 12 deep-dive, 16-convergence narrative audit, and Lean source audit. Every item is actionable. Work top-to-bottom; items within a section are independent unless noted.*

***

## How to Use This Document

- **🔴 BLOCKER** — Will cause desk rejection or immediate referee rejection. Fix before any submission.
- **🟡 REQUIRED** — Will generate a major revision request. Fix before submission.
- **🔵 RECOMMENDED** — Will generate a minor revision request or referee query. Fix to strengthen submission.
- **Owner column** — which file(s) to edit.
- **Check box** — mark `[x]` when done.

***

## PART 1 — Citation Errors (Catastrophic)

These three citations resolve to papers in completely unrelated fields. Any referee who clicks the link will desk-reject.

### 1.1 — Paper 7: `[TPF2024]` points to a galaxy survey

- [ ] **File:** `papers/paper7_chirality_formal/paper_draft.tex`
- **Wrong arXiv:** 2411.18738 (*SOFIA infrared AGN survey*)[^1]
- **Correct arXiv:** 2601.04304 — Thorngren, Preskill, Fidkowski, *"Chiral Lattice Gauge Theories from Symmetry Disentanglers"* (2026)[^2]
- **Action:** Replace `arXiv:2411.18738` → `arXiv:2601.04304` in bibitem. Also replace every instance of "Tong-Preskill-Fidkowski" with "Thorngren-Preskill-Fidkowski" throughout the entire paper body, abstract, section headings, and conclusions (~10+ instances). The abbreviation "TPF" may be retained.

### 1.2 — Paper 12: `[Burkhard2025]` points to an LLM paper

- [ ] **File:** `papers/paper12_polariton/paper_draft.tex`
- **Wrong arXiv:** 2511.13189 (*"Large Language Models Meet Extreme Multi-label Classification"*)
- **Correct arXiv:** 2511.12339 — Burkhard, Kroj, Falque, Bramati, Carusotto, Jacquet, *"Stimulated Hawking effect and quasinormal mode resonance in a polariton simulator"*, *Comptes Rendus Physique* (2026)[^3][^4]
- **Action:** Replace `arXiv:2511.13189` → `arXiv:2511.12339` in bibitem. Update journal to: *Comptes Rendus Physique* (2026).

### 1.3 — Paper 3: `[NastaseSonnenschein2025]` points to an MRI engineering paper

- [ ] **File:** `papers/paper3_gauge_erasure/paper_draft.tex`
- **Wrong arXiv:** 2501.13263 (*"A simple method for deriving the birdcage coil magnetic field..."*)
- **Most likely correct arXiv:** 2502.13765 — Nastase & Sonnenschein, *"Nonabelian fluids and helicities"* (2025)
- **Action:** Replace `arXiv:2501.13263` → `arXiv:2502.13765`. Verify the claim the paper supports still matches this source before finalizing.

***

## PART 2 — Author Name Errors (Systematic, High Visibility)

### 2.1 — Paper 7 calls the construction "Tong-Preskill-Fidkowski"

- [ ] **File:** `papers/paper7_chirality_formal/paper_draft.tex`
- **Correct name:** Thorngren-Preskill-Fidkowski. David Tong is a different physicist (Cambridge); his work is cited separately as `[Tong2022]`.[^5][^2]
- **Note:** Paper 8 correctly uses "Thorngren-Preskill-Fidkowski" — Paper 7 directly contradicts it.
- **Action:** Global find-replace "Tong-Preskill-Fidkowski" → "Thorngren-Preskill-Fidkowski" throughout Paper 7. Search for "Tong, Preskill" and "D. Tong, J. Preskill" and correct those too.

***

## PART 3 — Bibliographic Errors (Title, Page, Volume)

### 3.1 — Papers 5 & 6: `[Volovik2024]` wrong title

- [ ] **Files:** `papers/paper5_adw_gap/paper_draft.tex`, `papers/paper6_vestigial/paper_draft.tex`
- **Wrong title in bibitem:** *"Gravity through the prism of condensed matter physics"*
- **Correct title for arXiv:2312.09435:** *"Fermionic quartet and vestigial gravity"*, JETP Lett. **119**, 330 (2024)[^6][^7]
- **Note:** The other Volovik paper *"Gravity through the prism..."* is arXiv:2307.14370, JETP Lett. **118**, 546 (2023) — a different paper. The arXiv ID in the bibitem is correct; only the title is wrong.
- **Action:** Update bibitem title only.

### 3.2 — Paper 3: `[Adler2024]` wrong first page

- [ ] **File:** `papers/paper3_gauge_erasure/paper_draft.tex`
- **Cited as:** *Nature* **636**, 87 (2024)
- **Correct:** *Nature* **636**, 80–85 (2024), DOI: 10.1038/s41586-024-08188-0[^8]
- **Action:** Change page 87 → 80.

### 3.3 — Papers 1, 2, 12: `` journal volume needs verification

- [ ] **Files:** `papers/paper1_first_order/paper_draft.tex`, `papers/paper2_second_order/paper_draft.tex`, `papers/paper12_polariton/paper_draft.tex`
- **Cited as:** *Comptes Rendus Physique* **25**, 1–21 (2025)
- **Risk:** CRP volume 25 may correspond to 2024, not 2025 (one volume per year).
- **Action:** Check the CRP website for the published volume of arXiv:2408.17292 and correct volume number if needed.

### 3.4 — Paper 7: `[Tong2022]` year ambiguity

- [ ] **File:** `papers/paper7_chirality_formal/paper_draft.tex`
- **Issue:** arXiv:2104.03997 was submitted April 2021; published in JHEP **2022**(07), 001. Bibitem key says "2022" but the arXiv year is 2021.
- **Action:** Standardize to journal publication year 2022 and add arXiv:2104.03997 explicitly. Or use "Tong2021" with "published JHEP 2022."

### 3.5 — Paper 12: `[Falque2025]` bibitem title may be stale

- [ ] **File:** `papers/paper12_polariton/paper_draft.tex`
- **Published title (PRL 135, 023401, 2025):** *"Polariton Fluids as Quantum Field Theory Simulators on Tailored Curved Spacetimes"*[^9][^10]
- **Original arXiv v1 title:** *"Spectroscopic measurement of the excitation spectrum on effectively curved spacetimes in a polaritonic fluid of light"*
- **Action:** Confirm bibitem uses the published PRL title.

***

## PART 4 — Physics Values (Paper 12 / LKB Platform)

All items in this section require numerical recalculation. Do them together.

### 4.1 — Speed of sound c_s wrong by 25%

- [ ] **File:** `papers/paper12_polariton/paper_draft.tex`
- **Paper 12 states:** c_s = 0.5 μm/ps
- **Falque PRL measured value:** c_s ≈ 0.40 μm/ps (dark reservoir correction β = 1.84)[^11]
- **Action:** Replace c_s = 0.5 → 0.40 μm/ps. Recalculate T_H and D wherever c_s appears.

### 4.2 — Surface gravity κ underestimated

- [ ] **File:** `papers/paper12_polariton/paper_draft.tex`
- **Paper 12 states:** κ = 5 × 10¹⁰ s⁻¹
- **Falque PRL demonstrated range:** κ = 0.07–0.11 ps⁻¹ = 7–11 × 10¹⁰ s⁻¹ (smooth to steep horizon)[^11]
- **Action:** Update κ to the actually demonstrated range. Use κ = 0.07 ps⁻¹ as the conservative smooth-horizon value and κ = 0.11 ps⁻¹ for the steep-horizon upper bound. Recalculate T_H for both.

### 4.3 — Hawking temperature T_H should be recalculated

- [ ] **File:** `papers/paper12_polariton/paper_draft.tex`
- **Paper 12 states:** T_H ≈ 61 mK
- **Recalculated from Falque values:** T_H ≈ 85 mK (smooth, κ=0.07) to 134 mK (steep, κ=0.11)
- **Note:** The higher actual T_H *strengthens* Paper 12's detection case. Report the range.

### 4.4 — Dispersive parameter D likely underestimated

- [ ] **File:** `papers/paper12_polariton/paper_draft.tex`
- **Paper 12 states:** D ≈ 0.3–0.5 (near-adiabatic, ~10% dispersive correction)
- **Estimated from Falque values:** ξ ≈ 3.4 μm, κ = 0.07 ps⁻¹, c_s = 0.40 μm/ps → D = ξκ/c_s ≈ 0.60
- **Action:** Recompute D with corrected c_s and κ. Update the claim about "near-adiabatic regime." Higher D increases dispersive corrections; the quantitative claim about ~10% must be reverified.

### 4.5 — "Three independent measurements" claim overstated

- [ ] **File:** `papers/paper12_polariton/paper_draft.tex`
- **Paper 12 claims:** reservoir suppression of c_s "confirmed by three independent measurements"
- **Falque PRL reality:** One β = 1.84 value used across multiple horizon configurations — not three independent c_s measurements
- **Action:** Replace with: "dark reservoir contribution β = 1.84 reported by Falque et al. (2025)"

### 4.6 — "Programmable" attributed to Falque PRL — wrong source

- [ ] **File:** `papers/paper12_polariton/paper_draft.tex`
- **"Programmable"** appears in Giacobino & Jacquet lecture notes (arXiv:2512.14194), not in the Falque PRL body text which uses "tunable" and "all-optical control"[^12][^9]
- **Action:** Either replace "programmable" with "all-optically tunable" (Falque's language), or add `[Giacobino2025]` (arXiv:2512.14194) as a co-citation wherever the word "programmable" is used.

### 4.7 — "First observation of negative-energy modes inside the horizon" — phrasing refinement

- [ ] **File:** `papers/paper12_polariton/paper_draft.tex`
- **Status:** The claim is substantively correct — Falque PRL confirms "first time" in fluids of light[^13][^9]
- **Refinement needed:** Replace "inside the horizon" with "in the supersonic (post-horizon) region" to match Falque's exact language ("in the supersonic regions")
- **Action:** Minor wording fix in abstract and body.

***

## PART 5 — Missing Citations (Paper 12)

Add all four of these to Paper 12's bibliography. They are directly relevant and from the same LKB group.

### 5.1 — Giacobino & Jacquet 2025 lecture notes (52 pp.)

- [ ] **File:** `papers/paper12_polariton/paper_draft.tex`
- **Add bibitem:**
```
\bibitem{Giacobino2025}
E.~Giacobino and M.~J.~Jacquet,
``Acoustic horizons and the Hawking effect in polariton fluids of light,''
arXiv:2512.14194 (2025).
```
- **Cite in text:** when using "programmable simulators" language; when describing the experimental roadmap.

### 5.2 — Gil de Olivera et al. 2025 (momentum correlations)

- [ ] **File:** `papers/paper12_polariton/paper_draft.tex`
- **Add bibitem:**
```
\bibitem{GilDeOlivera2025}
M.~Gil de Olivera, M.~Joly, A.~Z.~Khoury, A.~Bramati, M.~J.~Jacquet,
``Momentum correlations of the Hawking effect in a quantum fluid,''
arXiv:2512.17807 (2025).
```
- **Cite in text:** as the spontaneous-emission baseline for SNR comparison.

### 5.3 — Claude et al. 2022 (CW probe spectroscopy method)

- [ ] **File:** `papers/paper12_polariton/paper_draft.tex`
- **Add bibitem:**
```
\bibitem{Claude2022}
F.~Claude \textit{et al.},
``High-resolution coherent probe spectroscopy of a polariton quantum fluid,''
Phys.\ Rev.\ Lett.\ \textbf{129}, 103601 (2022).
```
- **Cite in text:** when describing the CW pump-probe spectroscopy detection method.

### 5.4 — Guerrero et al. 2025 (vortex spectroscopy, generalization)

- [ ] **File:** `papers/paper12_polariton/paper_draft.tex`
- **Add bibitem:**
```
\bibitem{Guerrero2025}
J.~Guerrero, K.~Falque, E.~Giacobino, A.~Bramati, M.~J.~Jacquet,
``Multiply Quantized Vortex Spectroscopy in a Quantum Fluid of Light,''
Phys.\ Rev.\ Lett.\ \textbf{135}, 243801 (2025).
```
- **Cite in text:** in the discussion of future extensions to rotating-geometry Hawking.

***

## PART 6 — Physics Content / Interpretation Errors

### 6.1 — Papers 1 & 2: Son:2002 described as non-relativistic

- [ ] **Files:** `papers/paper1_first_order/paper_draft.tex`, `papers/paper2_second_order/paper_draft.tex`
- **Problem:** Son:2002 (hep-ph/0204199) is titled *"Low-Energy Quantum Effective Action for **Relativistic** Superfluids"* — it constructs a relativistic EFT. The action written in Paper 1 is the non-relativistic Madelung form.
- **Action:** Distinguish in body text: "Son's relativistic EFT framework (hep-ph/0204199) provides the symmetry-breaking structure; the non-relativistic adaptation follows Son-Wingate (2005) / Endlich et al. (2013)." Add Son-Wingate 2005 (hep-th/0510180) or Endlich et al. PRD **88**, 105001 (2013) as a co-citation for the non-relativistic form.

### 6.2 — Paper 9: "forces hidden sectors" overclaims GE2019

- [ ] **File:** `papers/paper9_sm_anomaly_drinfeld/paper_draft.tex`
- **Problem:** GE2019 (arXiv:1808.00009) identifies the anomaly and states its resolution is adding ν_R — not hidden sectors. "Forces hidden sectors" is one possible extension, not what the source says.[^14][^15]
- **Action:** Replace "forces hidden sectors to cancel the anomaly" with "requires either right-handed neutrinos or beyond-SM physics to cancel, consistent with Garcia-Etxebarria and Montero (2019)."

### 6.3 — Paper 10: Spin manifold/cobordism assumption undisclosed

- [ ] **File:** `papers/paper10_modular_generation/paper_draft.tex`
- **Problem:** The step "framing anomaly requires c₋ ≡ 0 (mod 24)" rests on placing the system on a compact spin 3-manifold with specific framing — an implicit physics axiom. Paper 10 acknowledges one axiom (gapped interface) but not this deeper geometric assumption.
- **Action:** Add one sentence in Section 2 or 3: "This argument applies to theories placed on spin 3-manifolds with a fixed framing / p₁-structure; the validity of this placement for the SM is established in Wang (2024) via the string bordism ℤ₂₄ class."

### 6.4 — Papers 1 & 2: κ profile-dependence (60× discrepancy) not explained in body text

- [ ] **Files:** `papers/paper1_first_order/paper_draft.tex`, `papers/paper2_second_order/paper_draft.tex`
- **Problem:** Table 1 gives κ = 4.8 s⁻¹ for Steinhauer ⁸⁷Rb; caption notes Steinhauer's published κ ≈ 290 s⁻¹. This 60× discrepancy (tanh vs. step potential profile) is explained only in the caption.
- **Action:** Add a main-text sentence in Section 3 or 4: "The smooth tanh profile used here gives κ ≈ 4.8 s⁻¹, roughly 60× smaller than the step-potential value κ ≈ 290 s⁻¹ published by Steinhauer (2016); the difference is entirely due to velocity profile geometry."

### 6.5 — Paper 6: Monte Carlo claim unsupported

- [ ] **File:** `papers/paper6_vestigial/paper_draft.tex`
- **Problem:** Abstract claims "mean-field and Monte Carlo evidence" for the vestigial metric phase. The MC production run crashed (BrokenPipeError, 1/5 sub-runs completed).
- **Action:** Either (a) complete the MC run and verify output, or (b) replace "Monte Carlo evidence" with "mean-field prediction" in the abstract, with a note: "Monte Carlo validation is in preparation."

***

## PART 7 — The "16 Convergence" Narrative

These items span README, Paper 10, Paper 9, and the Lean source. All are visible to any specialist referee.

### 7.1 — "All the same 16" — remove or qualify this claim everywhere

- [ ] **Files:** `README.md`, `papers/paper10_modular_generation/paper_draft.tex`, and any paper citing RokhlinBridge
- **Problem:** The four 16s (SM Weyl, Z/16 anomaly, Rokhlin, Kitaev) are *related* through cobordism morphisms — they are not the *same* mathematical object. The Lean theorem `sixteen_convergence_full` proves only that the number 16 appears in a tuple, not that there is a single theorem with all four as corollaries.
- **Action:** Replace "We proved these are all the same 16" with: "These four appearances of 16 are non-coincidentally connected through the algebraic topology of spin structures in four dimensions, as established by Wang (2024) via cobordism." Remove "same" everywhere it implies a direct identification.

### 7.2 — "16 Weyl fermions per generation" requires explicit ν_R disclosure

- [ ] **Files:** `README.md`, `papers/paper9_sm_anomaly_drinfeld/paper_draft.tex`, `papers/paper10_modular_generation/paper_draft.tex`
- **Problem:** The SM without ν_R has 15 Weyl fermions per generation, not 16. GE2019 is explicit that 16 requires including right-handed neutrinos. The *code* handles this correctly (SMFermionData.lean has separate 15 and 16 theorems), but the papers and README do not disclose it.[^16]
- **Action:** Add on first use of "16 Weyl fermions": "(including one right-handed neutrino ν_R per generation, which is an assumption about beyond-SM content rather than a measured property)." Consider citing the `total_components_without_nu_R = 15` result explicitly to show the sensitivity.

### 7.3 — "Kitaev's periodic table repeats with period 16" — wrong general claim

- [ ] **File:** `README.md` (popular summary section)
- **Problem:** The Bott period is 8, not 16. Period 16 is specific to 2D class D (Kitaev sixteenfold way) or to 3D DIII with interactions. The unqualified claim will trigger a reviewer comment from any condensed matter theorist.[^17][^18]
- **Action:** Add qualifier: "Kitaev's periodic table repeats with period 8 (Bott period); within the 2D class-D topological superconductor sector, the anyonic classification has period 16 (Kitaev's sixteenfold way)."

### 7.4 — "Quaternionic structure of spinors" as causal origin — remove or reframe

- [ ] **File:** `README.md`, `papers/paper10_modular_generation/paper_draft.tex`
- **Problem:** The claim "all rooted in the quaternionic structure of spinors in four dimensions" cannot simultaneously explain a 2D condensed matter classification and a 4D manifold theorem. It is a physics intuition, not a proven theorem.
- **Action:** Reframe as motivation: "The quaternionic structure of the 4D Dirac algebra (Cl(0,4) ≅ ℍ ⊗ ℍ) provides the unifying physical intuition; the precise mathematical connections are established through spin cobordism as detailed in Wang (2024)."

### 7.5 — "Modular invariance rooted in Dedekind eta studied by Ramanujan" — misleading attribution

- [ ] **Files:** `README.md`, `papers/paper10_modular_generation/paper_draft.tex`
- **Problem:** The c₋ ≡ 0 (mod 24) constraint comes from the framing anomaly of 3D Chern-Simons theory on spin manifolds (Wang 2024 / string bordism ℤ₂₄ class). Attributing it to Ramanujan's 1916 work on eta functions is historically inaccurate and will alienate specialists.
- **Action:** Replace "studied by Ramanujan in 1916" with "arising from the framing anomaly on spin 3-manifolds, formalized via the string bordism ℤ₂₄ class (Wang 2024, following Atiyah-Patodi-Singer)."

### 7.6 — E8 "lattice" vs. E8 "manifold" conflation

- [ ] **Files:** `README.md`, `papers/paper10_modular_generation/paper_draft.tex`
- **Problem:** "algebra alone (specifically, the E8 lattice)" — the counterexample to Rokhlin is the E8 *manifold* (a 4-manifold with E8 intersection form, not spin), not the E8 root lattice (an 8-dimensional lattice). These are distinct objects; conflating them is a visible error.
- **Action:** Replace "E8 lattice" → "E8 manifold (a 4-manifold with E8 intersection form that is not spin)".

### 7.7 — Wang 2024's generation constraint is a proposal, not a derivation

- [ ] **Files:** `papers/paper10_modular_generation/paper_draft.tex`, `README.md`
- **Problem:** Wang (2024) abstract says "we **propose** a novel solution to the family puzzle." The repository presents it as a derivation.
- **Action:** Add one sentence acknowledging the epistemic status: "Following Wang's proposed mechanism (2024), which provides a novel solution to the family puzzle rather than a derivation from unambiguous first principles, we formalize..."

***

## PART 8 — Lean Proof Issues

### 8.1 — `sixteen_convergence_full` is a structural tautology

- [ ] **File:** `lean/SKEFTHawking/RokhlinBridge.lean`
- **Problem:** The theorem takes Rokhlin as a hypothesis `h_rokhlin` and then includes `h_rokhlin` itself as the third conjunct of the conclusion. The "all the same 16" conclusion is: (count = 16) ∧ (16 : ZMod 16) = 0 ∧ (h_rokhlin) ∧ (count = 16). The second conjunct is `decide`-trivial. There is no Kitaev term in the proof at all.
- **Action:** Either (a) add a comment to the docstring acknowledging the tautological structure and clarifying what the theorem *does* and *does not* prove, or (b) strengthen the theorem by finding a Lean statement that connects two of the four domains non-trivially (e.g., `rokhlin_from_bordism` composed with `generation_mod3_constraint` as a single theorem). The paper text should not describe this theorem as proving unification.

### 8.2 — `dai_freed_spin_z4` is discharged as `Equiv.refl`

- [ ] **File:** `lean/SKEFTHawking/Z16AnomalyComputation.lean`
- **Problem:** The theorem purporting to verify `Ω₅^{Spin^{Z₄}} ≅ ℤ₁₆` is discharged as the trivial identity equivalence on ZMod 16. It proves nothing about bordism groups.
- **Action:** Add a comment: "This theorem is a placeholder. The actual cobordism computation (Ω₅^{Spin^{Z₄}} ≅ ℤ₁₆, Dai-Freed 1994) is beyond current Mathlib scope and remains an external hypothesis. It should not be cited as a Lean-verified result in the papers."
- **Paper action:** In Paper 9 and Paper 10, change "Lean-verified Dai-Freed theorem" → "Lean-formalized consequence of the Dai-Freed theorem (cobordism computation taken as external hypothesis)."

### 8.3 — False axiom `modular_invariance_constraint` was removed — disclose this

- [ ] **File:** `lean/SKEFTHawking/GenerationConstraint.lean`
- **Status:** The removed axiom (which claimed ∀ c_minus, if c_minus = 8*N_f then 24 | c_minus) was false — counterexample N_f=1 gives c_minus=8 and 24 ∤ 8. The comment in the file documents this. The false axiom was never used in any proof, so the theorems are clean.
- **Action:** No math fix needed. But Paper 10's methodology section should note: "An early axiomatization of the modular invariance constraint was found to be false (universally quantified over all N_f rather than only physically valid ones); it was replaced by a correctly stated conditional hypothesis."

### 8.4 — Paper 15 module/theorem counts are stale

- [ ] **File:** `papers/paper15_methodology/paper_draft.tex`
- **Problem:** Paper 15 says "2237 theorems across 94 Lean modules with 33 remaining gaps." The current README says "2237+ theorems, 131 modules, 17 sorry." Three numbers are wrong.
- **Action:** Update Paper 15 to: "2237+ theorems across 131 modules; 17 remaining `sorry` placeholders (down from 33 at initial submission)."

***

## PART 9 — Submission-Level Structural Issues

### 9.1 — Papers 7 and 8 contradict each other on author name

- [ ] **Files:** `papers/paper7_chirality_formal/paper_draft.tex`, `papers/paper8_chirality_master/paper_draft.tex`
- Same series, companion papers, different author names for the same construction (see 1.1 / 2.1 above). When submitted together or cross-cited, a referee handling both will immediately note the contradiction.
- **Action:** Fix Paper 7 per items 1.1 and 2.1. After fixing, do a cross-check: every instance of the construction name in Paper 8 should match Paper 7 after correction.

### 9.2 — Paper 12 strategic reframing for collaboration

- [ ] **File:** `papers/paper12_polariton/paper_draft.tex`
- **Opportunity:** The LKB Paris group's Burkhard et al. (2025) explicitly calls its results "a practical guide for future experimental investigations" — but the experiment has not been done. Paper 12's EFT predictions fill exactly this gap.[^19][^3]
- **Action:** Reframe the abstract and introduction to position Paper 12 as: "Building on the all-optically tunable polariton platform of Falque et al. (2025) and the numerical stimulated-Hawking predictions of Burkhard et al. (2025), we provide analytically derived, formally verified EFT predictions for the stimulated Hawking gain spectrum, constituting a ready-to-implement experimental protocol."
- **Collaboration note:** Contact Maxime Jacquet (LKB Paris) before submission. His group is the natural recipient of these predictions and co-authorship or acknowledgment would strengthen the paper significantly.

### 9.3 — "First formally verified X in any proof assistant" claims need verification

- [ ] **Files:** All papers claiming "first"
- **Items already confirmed first:** first quantum group (U_q(sl₂)), first rank-2 quantum group (U_q(sl₃)), first SU(3) fusion category in Lean 4[^2]
- **Items needing spot-check:** "first Ext computation over Steenrod subalgebra A(1)" — verify no prior Agda/Coq formalization exists before making the claim
- **Action:** For each "first in any proof assistant" claim, search the Lean4/Mathlib GitHub issues, the Agda standard library, and the Coq/Rocq ecosystem for any prior relevant formalization.

***

## Quick Reference: Files and Their Open Issues

| File | Open Items |
|------|-----------|
| `README.md` | 7.1, 7.2, 7.3, 7.4, 7.5, 7.6, 7.7 |
| `paper1_first_order` | 3.3, 6.1, 6.4 |
| `paper2_second_order` | 3.3, 6.1, 6.4 |
| `paper3_gauge_erasure` | 1.3, 3.2 |
| `paper5_adw_gap` | 3.1 |
| `paper6_vestigial` | 3.1, 6.5 |
| `paper7_chirality_formal` | **1.1 🔴**, **2.1 🔴**, 3.4, 9.1 |
| `paper8_chirality_master` | 9.1 (cross-check after fixing p7) |
| `paper9_sm_anomaly_drinfeld` | 6.2, 7.2, 8.2 |
| `paper10_modular_generation` | 6.3, 7.1, 7.2, 7.5, 7.6, 7.7, 8.2, 8.3 |
| `paper12_polariton` | **1.2 🔴**, 3.3, 3.5, 4.1–4.7, 5.1–5.4, 6.7, 8.1 (narrative), 9.2 |
| `paper15_methodology` | 8.4 |
| `RokhlinBridge.lean` | 8.1 |
| `Z16AnomalyComputation.lean` | 8.2 |
| `GenerationConstraint.lean` | 8.3 |

***

## Verified Clean — No Changes Needed

The following key citations and claims were independently verified correct:

| Item | Status |
|------|--------|
| Nielsen-Ninomiya PLB **105**, 219 (1981) and NPB **185**, 20 (1981) | ✅ Correct[^20][^21] |
| GarciaEtxebarria2019 arXiv:1808.00009 | ✅ Correct[^14][^15] |
| Kitaev2003 anyons Ann. Phys. **303**, 2 (2003) | ✅ Correct[^22][^23] |
| TPF2026 arXiv:2601.04304 (after fix in P7) | ✅ Correct[^2] |
| GioiaThorngrenPRL2026 PRL **136**, 061601 | ✅ Correct[^24] |
| Wang2024 arXiv:2312.14928, PRD **110**, 125028 | ✅ Correct title/venue[^25] |
| Steinhauer2016 Nat. Phys. **12**, 959 | ✅ Correct[^26][^27] |
| GoltermanShamir2026 arXiv:2603.15985 | ✅ Correct[^28] |
| Drinfeld1986 ICM 1986 quantum groups | ✅ Correct[^29][^30] |
| Crossley2017 JHEP 1709, 095 | ✅ Correct[^31][^32] |
| Kolobov2021 Nat. Phys. **17**, 362 | ✅ Correct[^33] |
| Falque PRL 135, 023401 (2025) — main experimental platform | ✅ Correct[^9][^10] |
| Burkhard arXiv:2511.12339 (after fix in P12) | ✅ Correct[^3][^4] |
| `generation_mod3_constraint` Lean theorem | ✅ Sound conditional proof, zero sorries |
| `framing_anomaly_constraint` Lean theorem | ✅ Sound Mathlib proof |
| `rokhlin_from_bordism` Lean theorem | ✅ Sound conditional proof |
| `AlgebraicRokhlin` Serre σ ≡ 0 mod 8 | ✅ Sound |

---

## References

1. [Low-Energy Quantum Effective Action for Relativistic Superfluids](https://arxiv.org/abs/hep-ph/0204199) - We show that the low-energy dynamics of the superfluid Goldstone boson is completely determined by t...

2. [Chiral Lattice Gauge Theories from Symmetry Disentanglers - arXiv](https://arxiv.org/abs/2601.04304) - Abstract page for arXiv paper 2601.04304: Chiral Lattice Gauge ... Authors:Ryan Thorngren, John Pres...

3. [Stimulated Hawking effect and quasinormal mode resonance in a polariton simulator of field theory on curved spacetime](https://arxiv.org/html/2511.12339v1)

4. [[PDF] Stimulated Hawking effect and quasinormal mode resonance in a ...](https://comptes-rendus.academie-sciences.fr/physique/item/10.5802/crphys.278.pdf) - We stimulate the Hawking effect by injecting a finite-amplitude continuous-wave (CW) probe into the ...

5. [Chiral Lattice Gauge Theories from Symmetry Disentanglers](https://www.arxiv.org/abs/2601.04304) - We propose a Hamiltonian framework for constructing chiral gauge theories on the lattice based on sy...

6. [[2312.09435] Fermionic quartet and vestigial gravity - arXiv](https://arxiv.org/abs/2312.09435) - We discuss different types of the vestigial order, which are possible in the spin-triplet superfluid...

7. [[2307.14370] Gravity through the prism of condensed matter physics](https://arxiv.org/abs/2307.14370) - Here, based on the condensed matter experience, we suggest the answers to some questions concerning ...

8. [Observation of Hilbert space fragmentation and fractonic excitations ...](https://www.nature.com/articles/s41586-024-08188-0) - Here we experimentally observe Hilbert space fragmentation in a two-dimensional tilted Bose–Hubbard ...

9. [Polariton Fluids as Quantum Field Theory Simulators on Tailored ...](https://link.aps.org/doi/10.1103/t5dh-rx6w) - We introduce such a QFT simulator in a one-dimensional polaritonic fluid of light. We demonstrate th...

10. [Polariton Fluids as Quantum Field Theory Simulators on Tailored Curved Spacetimes](https://journals.aps.org/prl/abstract/10.1103/t5dh-rx6w) - A fluid made of light can simulate a black hole's boundary, providing insights into the mysterious q...

11. [Polariton Fluids as Quantum Field Theory Simulators on ...](https://arxiv.org/html/2311.01392v2)

12. [Acoustic horizons and the Hawking effect in polariton fluids of light](https://arxiv.org/abs/2512.14194) - View a PDF of the paper titled Acoustic horizons and the Hawking effect in polariton fluids of light...

13. [Polariton Fluids as Quantum Field Theory Simulators on Tailored ...](https://arxiv.org/abs/2311.01392) - Quantum fields in curved spacetime exhibit a wealth of effects like Hawking radiation from black hol...

14. [[1808.00009] Dai-Freed anomalies in particle physics - arXiv](https://arxiv.org/abs/1808.00009) - We analyze these more refined anomaly cancellation conditions in a variety of theories of physical i...

15. [[PDF] arXiv:1808.00009v3 [hep-th] 2 Apr 2020](https://arxiv.org/pdf/1808.00009.pdf)

16. [JHEP08(2019)003](https://d-nb.info/1240297661/34)

17. [[PDF] arXiv:1406.3032v1 [cond-mat.str-el] 11 Jun 2014](https://arxiv.org/pdf/1406.3032.pdf) - We begin in Section II with a brief introduction to topological superconductors in 3D with time reve...

18. [[PDF] Anyons in an exactly solved model and beyond](https://www.physics.rutgers.edu/~coleman/603/texts/kitaev_annals.pdf) - In the preceding discussion we. A. Kitaev / Annals of Physics 321 (2006) 2–111. 3. Page 3. assumed t...

19. [[PDF] Stimulated Hawking effect and quasinormal mode resonance ... - arXiv](https://arxiv.org/pdf/2511.12339.pdf) - Here, we consider a polariton simulator and numerically examine the stimulated. Hawking effect using...

20. [Nielsen–Ninomiya theorem - Wikipedia](https://en.wikipedia.org/wiki/Nielsen%E2%80%93Ninomiya_theorem) - In lattice field theory, the Nielsen–Ninomiya theorem is a no-go theorem about placing chiral fermio...

21. [A no-go theorem for regularizing chiral fermions - NASA ADS](http://ui.adsabs.harvard.edu/abs/1981PhLB..105..219N/abstract) - We present a no-go theorem for regularizing chiral fermions in a general and abstract form, together...

22. [[quant-ph/9707021] Fault-tolerant quantum computation by anyons](https://arxiv.org/abs/quant-ph/9707021) - A two-dimensional quantum system with anyonic excitations can be considered as a quantum computer. U...

23. [Fault-tolerant quantum computation by anyons](https://cognitivemedium.com/assets/matter/Kitaev2003.pdf)

24. [Exact Chiral Symmetries of 3+1D Hamiltonian Lattice Fermions - PubMed](https://pubmed.ncbi.nlm.nih.gov/41765793/) - We construct Hamiltonian models on a 3+1D cubic lattice for a single Weyl fermion and for a single W...

25. [Family Puzzle, Framing Topology, $c_-=24$ and 3(E8)$_1$ Conformal Field Theories: 48/16 = 45/15 = 24/8 =3](https://arxiv.org/abs/2312.14928) - Family Puzzle or Generation Problem demands an explanation of why there are 3 families or generation...

26. [Observation of self-amplifying Hawking radiation in an analog black ...](https://arxiv.org/abs/1409.6550) - We observe Hawking radiation emitted by the black hole. This is the output of the black hole laser. ...

27. [Jeff Steinhauer and his group measure Hawking radiation from an ...](https://phys.technion.ac.il/en/about-us/research-bits/steinhauer-nature-may2019) - This work confirms the prediction of Hawking's theory regarding the value of the Hawking temperature...

28. [Symmetric mass generation and the Nielsen-Ninomiya theorem - arXiv](https://arxiv.org/abs/2603.15985) - The symmetric mass generation (SMG) approach to the construction of lattice chiral gauge theories at...

29. [[PDF] Quantum Groups](https://maths-people.anu.edu.au/~nwhite/crystals/drinfeldICM.pdf) - This is a report on recent works on Hopf algebras (or quantum groups, which is more or less the same...

30. [[PDF] QUANTUM GROUPS 1 | Inspire HEP](https://inspirehep.net/files/2edd6350ea1b86dc4b889846d9dab18a) - [5] Drinfeld, V. G., Quantum Groups, Proceedings of the ICM, Berkley, (1986). [6] Faddeev, L. D., Re...

31. [[1511.03646] Effective field theory of dissipative fluids - arXiv](https://arxiv.org/abs/1511.03646) - We develop an effective field theory for dissipative fluids which governs the dynamics of long-lived...

32. [[1701.07817] Effective field theory for dissipative fluids (II) - arXiv](https://arxiv.org/abs/1701.07817) - Effective field theory for dissipative fluids (II): classical limit, dynamical KMS symmetry and entr...

33. [Observation of stationary spontaneous Hawking radiation and the ...](https://arxiv.org/abs/1910.09363) - Spontaneous Hawking radiation was observed in analogue black holes in atomic Bose-Einstein condensat...

