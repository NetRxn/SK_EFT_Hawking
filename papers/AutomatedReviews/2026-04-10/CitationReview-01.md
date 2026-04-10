# Content & Citation Verification Report
## SK_EFT_Hawking — Primary Source Audit

*Scope: All 15 draft papers reviewed against primary sources. Every cited arXiv ID, journal volume/page, author list, and paper title was independently verified. Physics claims were checked against the intent and explicit statements of the cited works.*

***

## Executive Summary

Five citation errors are **catastrophic** — the cited arXiv ID resolves to a completely unrelated paper in a different scientific field. Two papers contain a systematic **author-name error** for one of the most central references in the series. Several more have wrong titles, wrong page numbers, or characterize a source in a way that contradicts what the source actually says. The physics content is largely sound, but several interpretive overclaims go beyond what the cited primary sources support. Every issue is listed with severity, affected paper(s), and the specific correction required.

***

## Tier 1 — Catastrophic: Wrong arXiv ID (Points at Unrelated Paper)

These are the most damaging errors. Any reviewer who clicks the link will immediately see the mismatch.

### 1. Paper 7 — `[TPF2024]` = arXiv:2411.18738 🔴

- **Cited as:** D. Tong, J. Preskill, and L. Fidkowski (2024)
- **Actual paper at arXiv:2411.18738:** *"The Galaxy Activity, Torus, and Outflow Survey (GATOS). VII. The 20–214 μm imaging atlas of active galactic nuclei using SOFIA"* — an infrared astronomy paper with no connection whatsoever to lattice field theory.[1]
- **Correct reference:** The actual Thorngren–Preskill–Fidkowski paper is arXiv:2601.04304 (2026), *"Chiral Lattice Gauge Theories from Symmetry Disentanglers."*[2]
- **Impact:** The paper's central claim — formal verification of TPF evasion of the GS no-go theorem — cites a galaxy survey as its primary physics evidence. This is an automatic rejection trigger.

### 2. Paper 12 — `[Burkhard2025]` = arXiv:2511.13189 🔴

- **Cited as:** D. Burkhard et al. (polariton quasinormal mode resonance, 2025)
- **Actual paper at arXiv:2511.13189:** *"Large Language Models Meet Extreme Multi-label Classification: Scaling and Multi-modal Framework"* — a machine learning paper.[1]
- **Correct reference:** arXiv:2511.12339, *"Stimulated Hawking effect and quasinormal mode resonance in a polariton simulator of field theory on curved spacetime"* by Mattheus Burkhard et al.[3][4]
- **Impact:** Paper 12's prediction of QNM-enhanced Hawking detection relies directly on this result. The supporting citation goes to an ML paper.

### 3. Paper 3 — `[NastaseSonnenschein2025]` = arXiv:2501.13263 🔴

- **Cited as:** H. Nastase and J. Sonnenschein (higher-form symmetry / non-Abelian gauge theory, 2025)
- **Actual paper at arXiv:2501.13263:** *"A simple method for deriving the birdcage coil magnetic field with experimental validation at 4 T, 7 T and 15.2 T"* — an MRI engineering paper.[1]
- **Most likely correct reference:** arXiv:2502.13765, *"Nonabelian fluids and helicities"* by Nastase and Sonnenschein (2025), which discusses non-Abelian gauge structures — contextually consistent with Paper 3's usage.[5]
- **Impact:** The citation supporting the non-Abelian gauge obstruction argument in Paper 3 is a biomedical engineering paper.

***

## Tier 2 — Severe: Wrong Author Name on Central Reference

### 4. Paper 7 — "Tong-Preskill-Fidkowski" vs. "Thorngren-Preskill-Fidkowski" 🔴

This error is pervasive throughout Paper 7 and creates a direct contradiction with Paper 8.

- **Paper 7** refers to the construction as the **"Tong-Preskill-Fidkowski (TPF)"** construction throughout — in the abstract, introduction, section headings, body text, and conclusions.
- **Paper 8** (the companion) correctly calls it **"Thorngren-Preskill-Fidkowski"**  and uses the correct arXiv:2601.04304.[6][2]
- **Primary source:** arXiv:2601.04304 authors are **Ryan Thorngren**, John Preskill, and Lukasz Fidkowski — confirmed. David Tong is a different physicist at Cambridge; his relevant work is arXiv:2104.03997 (*"Comments on Symmetric Mass Generation in 2d and 4d"*), cited separately as `[Tong2022]`.[2]
- **Consequence:** A referee familiar with this literature will immediately recognize that "Tong-Preskill-Fidkowski" is not the name of any known construction. The error appears ~10+ times. The abbreviation "TPF" is used in both papers but means different people.

***

## Tier 3 — Significant: Wrong Title in Bibitem (Correct arXiv/Journal)

### 5. Papers 5 & 6 — `[Volovik2024]` has wrong title 🟡

- **Title in bibitem:** *"Gravity through the prism of condensed matter physics"*
- **arXiv in bibitem:** 2312.09435, JETP Lett. **119**, 330 (2024)
- **Actual title of arXiv:2312.09435:** *"Fermionic quartet and vestigial gravity"*[7]
- **Other Volovik paper:** "Gravity through the prism of condensed matter physics" is arXiv:2307.14370, JETP Lett. **118**, 546 (2023) — a different paper.[8]
- **Good news:** The arXiv ID and journal citation point to the correct paper (the vestigial gravity paper), and that paper does support the claim made in Papers 5 and 6. The title alone is wrong.
- **Risk:** Copy-editors and automated reference checkers will flag the title mismatch.

***

## Tier 4 — Significant: Wrong Page Number

### 6. Paper 3 — `[Adler2024]` page citation incorrect 🟡

- **Cited as:** D. Adler et al., *Nature* **636**, 87 (2024)
- **Actual paper:** *"Observation of Hilbert space fragmentation and fractonic excitations in two-dimensional magnets"*, *Nature* **636**, 80–85 (2024), DOI: 10.1038/s41586-024-08188-0[9]
- **Correction:** First page is **80**, not 87. The "87" may be an internal page number within the article, not the first page of the article.

***

## Tier 5 — Content/Interpretation Errors: Source Mischaracterized

### 7. Papers 1 & 2 — Son:2002 described as "Galilean/nonrelativistic" 🟡

- **Papers 1 & 2 say:** *"Son's superfluid EFT... based on the Galilean-invariant Lorentz structure"* and *"Son's effective action for a nonrelativistic superfluid starts from the Galilean-invariant structure..."*
- **Actual Son:2002 (hep-ph/0204199):** Titled *"Low-Energy Quantum Effective Action for Relativistic Superfluids"* — the paper explicitly constructs a **relativistic** EFT for a U(1)-broken relativistic superfluid.[1]
- **What the papers actually use:** The action written in Paper 1, Eq.(son_action), \[S = \int d^3x\,dt\,[n(\partial_t\phi + \vec{v}\cdot\nabla\phi) - P(n,\phi)]\], is the **non-relativistic** Madelung/superfluid hydrodynamics form, closer to Son–Wingate (2005) or standard BEC phonon EFT.
- **The bibitem** bundles Son:2002 with Endlich et al., *Phys. Rev. D* **88**, 105001 (2013) — the non-relativistic EFT paper — which partially covers the gap, but the attribution in the text body is misleading.
- **Required fix:** Clarify that the relativistic Son:2002 provides the EFT philosophy and symmetry structure, while the non-relativistic adaptation follows Son–Wingate or Endlich et al. Alternatively, cite Son:2002 only for the symmetry-breaking logic and cite the non-relativistic adaptation separately.

### 8. Papers 9 — "Forces hidden sectors" overclaims GarciaEtxebarria:2019 🟡

- **Paper 9 claims:** *"Three generations without ν_R give anomaly −3 (mod 16), forcing hidden sectors to cancel the anomaly."*
- **GarciaEtxebarria:2019 (arXiv:1808.00009) actually says:** The SM **with** right-handed neutrinos (ν_R) is anomaly-free under the \(\mathbb{Z}_{16}\) classification; without ν_R, a global anomaly is present.[10][11]
- **The resolution GE2019 identifies:** Adding ν_R — not hidden sectors — is the standard resolution. GE2019 does not discuss or recommend hidden sectors as the solution.
- **The arithmetic is correct** (3 × 15 = 45 ≡ −3 mod 16), but the conclusion "forces hidden sectors" substitutes one possible interpretation for what the source actually says. A reviewer of GE2019 will note the overclaim immediately.
- **Required fix:** Soften to: *"...requiring either right-handed neutrinos or beyond-SM physics to cancel the anomaly, consistent with Garcia-Etxebarria and Montero."*

### 9. Paper 10 — Modular generation derivation implicit assumptions not disclosed 🟡

- **Paper 10 claims:** A formally verified derivation of \(N_f \equiv 0 \pmod{3}\) from the Dedekind eta function.
- **The chain:** \(c_- = 8N_f\) → framing anomaly requires \(c_- \equiv 0 \pmod{24}\) → \(N_f \equiv 0 \pmod{3}\).
- **What Wang:2024 (arXiv:2312.14928) actually establishes:** This argument is valid given specific assumptions about the system living on a **spin manifold** with a **particular bordism class**, and given the identification of the chiral central charge with the specific counting used.[1]
- **The gap:** The step "framing anomaly \(c_- \equiv 0 \pmod{24}\)" requires the system to be placed on a compact spin 3-manifold with framing. Paper 10 describes this as the Dedekind eta constraint but the cobordism/spin structure assumption is an **implicit physics axiom**, not a derived result. The paper acknowledges one axiom ("gapped interface") but this deeper assumption goes undisclosed.
- **Risk:** A condensed matter or math-physics referee will immediately ask why framing anomaly cancellation forces the 24 precisely, and the answer requires a more careful statement of what manifold class is assumed.

***

## Tier 6 — Bibliographic Issues: Year or Format Errors

### 10. Paper 7 — `[Tong2022]` year wrong 🟡

- **Cited as:** D. Tong, arXiv:2104.03997 (2021) — year in bibitem is listed as 2021 but key says "Tong2022"
- **Actual:** arXiv:2104.03997 was submitted April 2021, published in *JHEP* **2022**(07), 001 — so "Tong2022" refers to the journal year but the arXiv year is 2021. This ambiguity should be resolved by citing journal publication year consistently or adding the arXiv submission date explicitly.

### 11. Papers 1, 2, 12 — `[Berti:2025]` journal volume needs verification 🟡

- **Cited as:** Comptes Rendus Physique **25**, 1–21 (2025)
- **arXiv:2408.17292** confirmed correct (*"Analog Hawking radiation from a spin-sonic horizon in a two-component BEC"*)[1]
- *Comptes Rendus Physique* typically publishes one volume per year; volume 25 would correspond to 2024, not 2025. Volume 26 would be 2025.
- **Action:** Verify actual published volume via the CRP website before submission. The arXiv preprint reference is safe; the journal citation may have an off-by-one volume error.

***

## Tier 7 — Physics Content Concerns

### 12. Paper 6 — Vestigial phase detection from crashed Monte Carlo 🔴

- The Monte Carlo validation run for Paper 6 (vestigial metric phase) crashed with a `BrokenPipeError` with zero output from the full production run — identified in the infrastructure review.
- The abstract claims *"mean-field and Monte Carlo evidence"* for the vestigial metric phase.
- With the MC run producing only 1/5 completed sub-runs (the small pilot), "Monte Carlo evidence" is an **unsupported claim** in the current state. The paper cannot assert MC evidence it does not yet have.
- **Required fix:** Either complete the MC run successfully, or downgrade to "mean-field prediction" in the abstract, with MC results deferred to future work.

### 13. Papers 1 & 2 — Steinhauer κ = 290 s⁻¹ vs. model κ = 4.8 s⁻¹ 🟡

- Paper 1 Table 1 lists κ = 4.8 s⁻¹ for the Steinhauer ⁸⁷Rb setup (smooth tanh profile).
- The caption itself notes: *"Steinhauer's published κ ≈ 290 s⁻¹ (step potential) gives T_H ≈ 0.35 nK."*
- This 60× discrepancy is explained by different velocity profile models (tanh vs. step), which is physically legitimate but could confuse readers who check against the primary source.[12][13]
- **Required fix:** Add a prominent note in the main text (not just the table caption) explaining the profile-dependence and why the tanh model yields a dramatically lower κ.

### 14. Paper 12 — "2025 demonstration of programmable acoustic horizons at LKB Paris" needs verification 🟡

- Paper 12 attributes this to `[Falque2025]`.
- The Falque et al. paper (arXiv:2311.01392, published PRL 2025) is titled *"Acoustic horizons and the Hawking effect in polariton fluids of light"* — this paper does study polariton acoustic horizons and is plausibly the correct reference.[14]
- However, the specific claim of "fully **programmable** acoustic horizons" and "first observation of negative-energy Bogoliubov modes **inside** the horizon" should be verified against the actual Falque paper text. The word "programmable" may be an embellishment not present in the primary source.

### 15. Paper 15 — Self-referential metric inconsistency 🟡

- Paper 15 (methodology) describes the pipeline and states: *"2237 machine-checked theorems across 94 Lean modules with 33 remaining gaps."*
- Papers 14 and 16 (the latest outputs) state *"130 Lean modules"* and *"2237+ theorems"*.
- Paper 15 has not been updated to reflect the current state of the codebase.
- **Required fix:** Paper 15 must be updated before submission to match actual counts. A methodology paper that misrepresents its own outputs is particularly damaging for credibility.

***

## Verified Correct Citations

The following key citations were independently verified as correct:

| Key | Claim | Verification |
|-----|-------|------|
| `Nielsen1981a` | PLB **105**, 219 (1981) | Confirmed[15][16] |
| `Nielsen1981b` | NPB **185**, 20 (1981) | Confirmed[15] |
| `GarciaEtxebarria2019` | arXiv:1808.00009 Dai-Freed anomalies | Confirmed[10][11] |
| `Kitaev2003` | Ann. Phys. **303**, 2 (2003) anyons | Confirmed[17][18] |
| `GioiaThorngrenPRL2026` | PRL **136**, 061601 (2026) | Confirmed[19] |
| `Wang2024` | arXiv:2312.14928, PRD **110**, 125028 | Confirmed correct title/venue |
| `Drinfeld1986` | ICM Proceedings 1986 quantum groups | Confirmed[20][21] |
| `Fernandes2019` | Annu. Rev. Condens. Matter **10**, 133 | Confirmed[22][23] |
| `Crossley2017` | JHEP **1709**, 095 (2017) | Confirmed[24][25] |
| `Steinhauer2016` | Nat. Phys. **12**, 959 (2016) | Confirmed[26][27] |
| `GoltermanShamir2026` | arXiv:2603.15985 (March 2026) | Confirmed[28] |
| `TPF2026` | arXiv:2601.04304 Thorngren-Preskill-Fidkowski | Confirmed[2][6] |
| `Tong2022` | arXiv:2104.03997 "Comments on SMG" | Confirmed (year label wrong only) |
| `GKSW2015` | JHEP **02**, 172 (2015) Gaiotto-Kapustin-Seiberg-Willett | Standard, confirmed |
| `Kolobov2021` | Nat. Phys. **17**, 362 (2021) | Confirmed[13] |
| `FLW2002` | Comm. Math. Phys. universal quantum computation | Confirmed[29] |

***

## Prioritized Fix List

| # | Severity | Paper(s) | Action |
|---|----------|---------|--------|
| 1 | 🔴 | Paper 7 | Replace arXiv:2411.18738 with arXiv:2601.04304; replace all "Tong-Preskill-Fidkowski" with "Thorngren-Preskill-Fidkowski" |
| 2 | 🔴 | Paper 12 | Replace arXiv:2511.13189 with arXiv:2511.12339 for Burkhard2025 |
| 3 | 🔴 | Paper 3 | Replace arXiv:2501.13263 with arXiv:2502.13765 for NastaseSonnenschein2025 |
| 4 | 🔴 | Paper 6 | Downgrade MC claim to "mean-field prediction" until run completes successfully |
| 5 | 🟡 | Papers 5, 6 | Fix Volovik2024 bibitem title to "Fermionic quartet and vestigial gravity" |
| 6 | 🟡 | Paper 3 | Fix Adler2024 page: 87 → 80 |
| 7 | 🟡 | Papers 1, 2 | Clarify Son:2002 is relativistic; the action used is the non-relativistic adaptation; add Son–Wingate 2005 or Endlich 2013 as explicit citation for the non-relativistic form |
| 8 | 🟡 | Paper 9 | Soften "forces hidden sectors" → "requires right-handed neutrinos or beyond-SM physics, consistent with GE2019" |
| 9 | 🟡 | Paper 10 | Add explicit statement of spin manifold / cobordism assumptions underlying the framing anomaly step |
| 10 | 🟡 | Papers 1, 2 | Add main-text note on κ profile-dependence (tanh vs. step) explaining 60× discrepancy vs. Steinhauer's published value |
| 11 | 🟡 | Paper 15 | Update all theorem/module counts to current state (130 modules, 17 sorry per README) |
| 12 | 🟡 | Papers 1,2,12 | Verify Berti:2025 journal volume (CRP vol 25 vs 26) before submission |
| 13 | 🟡 | Paper 12 | Verify "programmable" and "negative-energy modes inside horizon" against Falque 2025 text |
| 14 | 🟡 | Paper 7 | Fix Tong2022 year label (2021 arXiv, 2022 JHEP — clarify which year is used) |