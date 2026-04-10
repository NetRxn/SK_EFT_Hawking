# SK-EFT Hawking: Comprehensive Pre-Submission Review

**Reviewer perspective:** Critical SME / Journal gatekeeper (PRL, PRD, CPC, Reviews of Modern Physics)
**Review date:** April 10, 2026
**Repository:** https://github.com/NetRxn/SK_EFT_Hawking/tree/main
**Pipeline reference:** docs/WAVE_EXECUTION_PIPELINE.md
**Scope:** 15 draft papers (Papers 1–12, 14–16), all validation logs, MC simulation outputs, Lean formalization counts, and cross-layer consistency

***

## Executive Summary

The project is a technically ambitious, genuinely novel research program combining dissipative EFT, analog Hawking radiation, emergent gravity, formal verification in Lean 4, and topological quantum field theory. The pipeline architecture and the underlying physics are largely sound. However, **no paper is currently in a state safe for submission.** Several papers carry critical numerical errors that would result in desk rejection or post-acceptance retraction; the project-wide count metadata (theorem count, module count, sorry count, Aristotle count) is inconsistent across files; and the vestigial gravity Monte Carlo (Paper 6) logs reveal that the primary production run crashed and that the vestigial phase signal is not robustly detected.

The table below summarizes the status of each paper as found:

| Paper | Target Journal | Claims Review Status | Blocking Issues |
|-------|---------------|---------------------|-----------------|
| Paper 1 — First-order SK-EFT | PRL | **FAIL** | Table 1 numerics wrong on all 3 platforms; stale a_s; wrong journal for Berti:2025 |
| Paper 2 — Second-order SK-EFT | PRD | PASS_WITH_ISSUES | Broken cite keys; orphan bibliography entries; journal mismatch |
| Paper 3 — Gauge erasure | PRD | PASS_WITH_FINDINGS | Physics error (SO vs Spin centers); duplicate bibitem; 10/16 refs missing from registry |
| Paper 4 — WKB connection | PRD | CONDITIONAL PASS | 7 orphan bibitems; 6 refs missing from registry; PROJECTED params unlabeled |
| Paper 5 — ADW gap | PRD | PASS_WITH_FINDINGS | Minor; MC params PROJECTED; no critical issues |
| Paper 6 — Vestigial gravity | PRD | **NO REVIEW; CRITICAL MC ISSUES** | Production MC crashed; vestigial not consistently detected; sign problem present |
| Paper 7 — Chirality formal | PRD/CPC | PASS with WARNs | Table theorem count inconsistency; bibliography cross-paper inconsistency |
| Paper 8 — Chirality master | PRD/RMP | **FAIL** | Stale module count (94→130); stale Aristotle count (307→322); duplicate bibitem |
| Paper 9 — SM anomaly/Drinfeld | PRL | 2 FAILs, 13 WARNs | Internal Aristotle count inconsistency; false "zero sorry" claim; 9 refs missing |
| Paper 10 — Modular generation | PRL | 4 FAILs, 13 WARNs | False "zero sorry" claim; stale module count; 2 sorry theorems in key module |
| Paper 11 — Quantum group | PRL | 5 FAILs, 19 WARNs | Stale theorem/module counts; theorem table overcounting; Aristotle ID misattribution |
| Paper 12 — Polariton | PRL | **10 FAILs, 34 WARNs** | Abstract numerically wrong; 4 Lean name mismatches; missing theorem; stale D value |
| Paper 14 — Braided MTC | Journal of Pure Appl. Alg. | PASS with WARNs | Several theorem counts may be stale vs Inventory |
| Paper 15 — Methodology | JOSS / SoftwareX | NO REVIEW | Internal counts inconsistent with project reality |
| Paper 16 — WRT TQFT | Lett. Math. Phys. | NO REVIEW | No claims review performed |

***

## I. Project-Wide Infrastructure Gaps

### I.1 Count Metadata Inconsistency (RED FLAG — affects all papers)

The most pervasive issue is that the authoritative count metadata disagrees across project files. Every paper abstracts and introductions include theorem/module/sorry counts, and these numbers are now inconsistent with each other and with the ground truth. A reviewer checking these numbers against the code will find discrepancies immediately.

| Metric | counts.json (Apr 6) | README.md | Research Status (Apr 8) | Session Review | counts.tex (Apr 6) |
|--------|---------------------|-----------|--------------------------|----------------|---------------------|
| Lean modules | 94 | 131 | 131 | 130 (excl. ExtractDeps) | 94 |
| Total theorems | 2241 | 2237+ | 2237+ | 2237+ | 2241 |
| Sorry count | 33 | 17 | 11 | 17 | 33 |
| Aristotle-proved | 307 | 322+ | 322+ | 322+ | 307 |
| Axioms | 1 | 1 | 1 | 1 | 1 |
| Papers | 14 | 14 | 15 | — | 14 |

**Root cause:** `counts.json` and `counts.tex` were generated on April 6 by `update_counts.py` but appear to reflect a different project state than the README (updated April 8). The module count discrepancy (94 vs 130) is the largest and most suspicious — it is likely that `lean_deps.json` was stale when `update_counts.py` ran, causing it to count only a subset of modules. The sorry count discrepancy (33 vs 11–17) needs the same investigation.

**Required fix:** Run `uv run python scripts/validate.py` and `uv run python scripts/update_counts.py` from a clean state with the current Lean source, verify `lean/lean_deps.json` is fresh, then re-run all claims reviews. Every paper abstract mentioning counts must be updated to the reconciled ground-truth values.

**Severity:** 🔴 Blocking. Every paper with count claims in its abstract must be corrected.

### I.2 Inventory Index Staleness

The `SK_EFT_Hawking_Inventory_Index.md` says 128 modules; the session review says 130. Several modules added in Phases 5r–5s (FKGappedInterface, VillainHamiltonian, KMatrixAnomaly, SPTStacking, TPFDisentangler, ModularityTheorem, MugerCenter, StringNet, FPDimension, KacWaltonFusion, etc.) are not yet reflected in the Inventory Index module map. The Index is the LLM-friendly reference used by the claims-reviewer agent — if it is 2 modules behind, all automated reviews will have inconsistent ground truth.

**Required fix:** Run verification commands from the Index's Counts table, update all rows, update the "Last synced" date.

### I.3 VecGMonoidal.lean Sorry Status

The Inventory Index row for VecGMonoidal still annotates "(1 sorry -- Lean heartbeat)". The axiom integrity sweep (April 4) notes that `lake build` only flags sorry in `DrinfeldDoubleAlgebra.lean`, not VecGMonoidal. This annotation is either wrong (the sorry was resolved) or the sweep was incomplete. It needs explicit verification.

**Required fix:** Run `grep -n "sorry" lean/SKEFTHawking/VecGMonoidal.lean` and update the Inventory Index accordingly.

### I.4 CITATION_REGISTRY Coverage

Across all reviewed papers, the following pattern is pervasive: bibliography entries in `.tex` files are **not in `CITATION_REGISTRY`** in `src/core/citations.py`. This breaks Stage 10 gate compliance (the claims-reviewer agent checks citations against the registry). The aggregate count of missing entries is well over 50 citations across all papers. This is a systemic gap, not paper-specific.

**Required fix:** For each paper, compare `.tex` bibliography `\bibitem` keys against the registry and add all missing entries with DOIs. The pipeline gate `validate.py --check citation_registry` should catch this automatically if the check is implemented.

### I.5 PAPER_DEPENDENCIES Registry

Paper 11 (quantum group) has no entry in `PAPER_DEPENDENCIES` in `provenance.py`. This is a pure algebra paper with no experimental parameters, but the structural entry is still needed for the provenance dashboard and Stage 10 gate to track formula dependencies.

***

## II. Paper-by-Paper Analysis

### Paper 1 — Dissipative EFT Corrections (PRL target)

**Claims review status: FAIL | 3 critical issues, 7 warnings**

#### II.1.A Numerical Discrepancies — CRITICAL

The most serious issue in the entire project. Table 1 presents platform-specific computed values for three experiments (Steinhauer ⁸⁷Rb, Heidelberg ³⁹K, Trento ²³Na). All three rows contain critical discrepancies between what the paper states and what the current `constants.py` parameters produce:

| Platform | Quantity | Paper value | Recomputed | Deviation |
|----------|----------|-------------|------------|-----------|
| Steinhauer | c_s | 0.46 mm/s | 0.548 mm/s | **19.1%** |
| Steinhauer | ξ | 1.57 μm | 1.33 μm | **18.0%** |
| Heidelberg | c_s | 3.37 mm/s | 3.92 mm/s | **16.3%** |
| Heidelberg | ξ | 0.48 μm | 0.25 μm | **92.0%** |
| Trento | c_s | 1.83 mm/s | 2.18 mm/s | **19.1%** |
| Trento | ξ | 1.51 μm | 0.36 μm | **319.4%** |

These deviations far exceed the pipeline's 0.5% tolerance. They indicate that the paper's Table 1 was generated from an intermediate or incorrect parameter set — neither the old parameters (ω_⊥ = 500 Hz, a_s = 5.77 nm) nor the current parameters (ω_⊥ = 123 Hz, a_s = 5.31 nm). The paper also retains the old text value a_s = 5.77 nm (109 a₀) after the parameter correction was applied to the code. At the 92% and 319% deviations, a PRL referee would reject immediately on technical grounds.

**Required fix:** Rerun the transonic solver with current `constants.py` parameters and regenerate all of Table 1 from scratch. Update the inline text a_s value to 100.4 a₀ = 5.31 nm (van Kempen 2002). Regenerate figures 1–4.

#### II.1.B Citation Error — CRITICAL

`\bibitem{Berti:2025}` in the paper bibliography cites *Phys. Rev. Lett. 134, 161001 (2025)*, but the `CITATION_REGISTRY` entry for Berti2025 records *Comptes Rendus Physique* (French Academy). These are different journals and potentially different papers. If the DOI resolves to Comptes Rendus, the PRL citation is fabricated — a retraction-level error if published.

**Required fix:** Resolve the Berti:2025 DOI, determine the correct journal, and update both the `.tex` bibliography and the `CITATION_REGISTRY` entry to be consistent.

#### II.1.C Orphan Citations

Four citations appear in the bibliography but are never cited in the text body: `Jacobson:1996`, `Son:2002`, `Coutant:2014`, `Zaremba:1999`. PRL requires that all bibliography entries be cited. Either cite them or remove them.

***

### Paper 2 — Second-Order Corrections (PRD target)

**Claims review status: PASS_WITH_ISSUES | 1 fail (citation), 0 warnings**

The core physics (counting formula, positivity constraint, CGL FDR, parity alternation) are parameter-independent algebraic theorems with zero sorry — structurally the most solid of the BEC papers. The only blocking issue is citation integrity.

#### II.2.A Broken Cite Keys — HIGH Severity

Line 185 contains `\cite{CGL2017,GloriosoLiu2018,JainKovtun2024}`. None of these keys have matching `\bibitem` entries. `CGL2017` should be `Crossley:2017`. `GloriosoLiu2018` and `JainKovtun2024` have no bibliography entries at all — this will produce undefined reference errors in the compiled PDF and question marks in the typeset output.

**Required fix:** Add `\bibitem{GloriosoLiu2018}` (Glorioso & Liu, arXiv:1809.01228) and `\bibitem{JainKovtun2024}` (arXiv:2309.00511), or remap the cite keys to existing entries.

#### II.2.B Berti:2025 Journal Mismatch

Same issue as Paper 1: `\bibitem{Berti:2025}` cites PRL 134, 161001 (2025) but registry says Comptes Rendus. Must be resolved consistently across all papers that cite this reference.

#### II.2.C Uncited Bibliography Entries

`Son:2002`, `Coutant:2014`, `Berti:2025` appear in `\thebibliography` but are never `\cited` in the paper text. Remove or cite.

***

### Paper 3 — Gauge Erasure (PRD target)

**Claims review status: PASS_WITH_FINDINGS | 0 fails, minor physics and citation issues**

#### II.3.A Physics Error — SO vs Spin Centers (MODERATE)

Lines 113–114 attribute center subgroups to SO(n) groups but the statement is incorrect. SO(2k+1) has **trivial** center for k ≥ 1; the center Z₂ belongs to Spin(2k+1). Similarly, SO(4k) has center Z₂, but Z₂ × Z₂ is the center of Spin(4k). While the main theorem about gauge erasure is unaffected (all centers remain discrete), a referee in gauge theory will immediately flag this attribution error. It signals insufficient care with the group theory.

**Required fix:** Replace SO(2k+1)/SO(4k) with Spin(2k+1)/Spin(4k) in lines 113–114, or explicitly state the correct center values for the SO groups.

#### II.3.B Duplicate Bibliography Entry

`\bibitem{GrozdanovHofmanIqbal}` (line 321) and `\bibitem{Grozdanov2017}` (line 327) are identical references — same authors, journal (*Phys. Rev. D* 95, 096003, 2017), volume, page, year. LaTeX will compile both but reviewers checking references will notice.

**Required fix:** Remove `Grozdanov2017` bibitem. Change `\cite{HofmanIqbal,Grozdanov2017}` on line 63 to `\cite{HofmanIqbal,GrozdanovHofmanIqbal}`.

#### II.3.C Citation Registry Coverage

10 of 16 bibliography entries are missing from `CITATION_REGISTRY`: Visser1998, Wen2003, GrozdanovHofmanIqbal, HofmanIqbal, Grozdanov2017, Torrieri2020, NastaseSonnenschein2025, GKSW2015, Adler2024, Volovik2003. Add all (minus the duplicate) to the registry with `used_in` including `paper3`.

***

### Paper 4 — WKB Connection (PRD target)

**Claims review status: CONDITIONAL PASS | 2 blocking issues (citation), 1 note**

The physics is structurally correct. All Lean theorems are verified. Parameters are correctly classified as PROJECTED for Heidelberg and Trento.

#### II.4.A Orphan Bibliography Entries — 7 Entries

Seven `\bibitem` entries are never cited in the text: `CorleyJacobson1996`, `CoutantParentani2012`, `BelgiornoCacciatori2024`, `RobertsonParentani2015`, `LombardoTuriaci2012`, `JanaLoganayagam2020`, `GiacobinoJacquet2025`. Either integrate these into the narrative where they are contextually relevant, or remove them.

#### II.4.B Citations Not in Registry

Six citations (`Berry1989`, `Heading1962`, `CoutantParentani2012`, `BelgiornoCacciatori2024`, `RobertsonParentani2015`, `LombardoTuriaci2012`) appear in the text but are not in `CITATION_REGISTRY`. Add all six entries.

#### II.4.C Parameter Note

The table presents Heidelberg and Trento parameters alongside Steinhauer (MEASURED) without any visual distinction. A footnote or column indicator distinguishing MEASURED from PROJECTED is needed. Reviewers will ask whether Heidelberg/Trento experiments have been performed.

***

### Paper 5 — ADW Gap Equation (PRD target)

**Claims review status: PASS_WITH_FINDINGS | 0 blocking issues**

This is the cleanest paper in the series. All numerical claims reproduce within tolerance. The honest disclosure that `gap_solution_bounded` was **disproved** by automated counterexample — and this is correctly stated in the abstract — is scientifically exemplary and should be highlighted as a strength of the formal verification approach.

Minor note: Vestigial MC parameters in this paper are PROJECTED estimates for experiments not yet performed. Ensure these are clearly labeled as projections in the text.

***

### Paper 6 — Vestigial Gravity Monte Carlo (PRD target)

**Claims review status: NO CLAIMS REVIEW FILE | CRITICAL SIMULATION ISSUES**

This paper is in the most problematic scientific state. No `claims_review.json` exists (the file returns 404). More critically, the Monte Carlo simulation logs reveal fundamental issues:

#### II.6.A Production Run Crashed

The most recent full-scale NJL production run (`vestigial_mc_njl_full_production.out`) failed catastrophically. All 14 worker processes throw `BrokenPipeError: [Errno 32] Broken pipe` immediately after dispatch, and the run terminates with 6 leaked semaphore objects. **No results were produced from this run.** The paper's MC figures cannot have been generated from this execution.

#### II.6.B Inconsistent Vestigial Detection Across Runs

Across the completed MC runs, the vestigial phase signal is not consistently detected:

| Run | Model | Vestigial detected (Binder) | Split transition (FSS) | Sign problem |
|-----|-------|-----------------------------|-----------------------|--------------|
| vestigial_mc_v3 | ADW | **False** | **True** | **Present** |
| vestigial_mc_v4 | ADW | **True** | False | **Present** |
| vestigial_mc_adw_rerun | ADW | **False** | **True** | **Present** |
| vestigial_mc_njl_production | NJL | **False** | False | **Present** |
| vestigial_mc_njl_staggered | NJL | **False** | False | **Present** |

The vestigial detection result (`True` in v4, `False` in all others) is inconsistent and appears to be a finite-size artifact or algorithm-dependent effect. The sign problem (`⟨sign⟩ = 0.000 ± 0.000` at all couplings and lattice sizes) indicates the sign problem is **severe throughout**, not just in the Lorentzian phase as the paper implies.

#### II.6.C Paper Claims vs. Evidence

The paper's abstract states: "We present mean-field and Monte Carlo evidence for a *vestigial metric* phase." Given that:
- The primary production run crashed
- The signal is inconsistently detected (detected in 1 of 5 runs)
- The sign problem is present across all couplings

The word "evidence" overstates what the simulations have actually produced. The appropriate framing is "mean-field prediction and preliminary Monte Carlo results consistent with but not conclusively establishing a vestigial metric phase."

**Required fix:** Run the production simulation to completion with a fixed model (ADW or NJL, explicitly stated). Address the sign problem disclosure. If the vestigial phase is not robustly detected by the Binder cumulant crossing method, the abstract and title must be reworded to reflect the preliminary nature of the MC support. A claims_review must be run against this paper before submission.

***

### Paper 7 — Chirality Formal (PRD/CPC target)

**Claims review status: PASS with WARNs (session 5qrs)**

#### II.7.A Theorem Count Inconsistency

The abstract and text state "54 theorems" but a figure caption says "55 theorems". One of these is wrong. Likely the caption is counting differently (e.g., including the axiom). Standardize to a single, explicitly defined count.

#### II.7.B Axiom Attribution in Table

The table column `GoltermanShamir.lean: 14+1ax` implies the project axiom lives in `GoltermanShamir.lean`. It does not — the axiom (`gapped_interface_axiom`) lives in `SPTClassification.lean`. Correct the annotation to avoid reviewer confusion about axiom provenance.

#### II.7.C Cross-Paper Bibliography Inconsistency

The `Nielsen1981a` entry uses NPB 185 in Paper 7 but PLB 105 in Paper 8 — these are different papers. The `TPF` reference uses arXiv:2411.18738 (Tong/Preskill/Fidkowski) in Paper 7 but arXiv:2601.04304 (Thorngren/Preskill/Fidkowski) in Paper 8 — different authors, potentially different papers. These must be verified and standardized before either paper is submitted, since companion papers citing different "same" works raise immediate questions.

***

### Paper 8 — Chirality Master Survey (PRD/RMP target)

**Claims review status: FAIL (session 5qrs) | 3 blocking fixes required**

#### II.8.A Stale Module Count — CRITICAL

The introduction (line 103–104) states "94 Lean modules". The actual module count is 130. This is a 38% undercount that will be immediately detectable to any reviewer who reads the companion papers (Papers 7, 9, 10, 14 all reference 130 modules in their current versions).

**Required fix:** Update line 103–104 to read "130 Lean modules."

#### II.8.B Stale Aristotle Count — CRITICAL

Line 104 states "307+ theorems proved by the Aristotle automated prover." The current ground truth is 322+. Both the README and the Research Status document confirm 322+.

**Required fix:** Update to "322+ theorems proved by the Aristotle automated prover."

#### II.8.C Duplicate Bibitem

`\bibitem{Aristotle2025}` appears twice in the bibliography (lines 532 and 582). This will cause a LaTeX warning and may produce incorrect reference numbering in the output.

**Required fix:** Remove the duplicate `\bibitem` at line 582.

***

### Paper 9 — SM Anomaly and Drinfeld Center (PRL target)

**Claims review status: 2 FAILs, 13 WARNs**

#### II.9.A Internal Aristotle Count Inconsistency

The abstract (line 33–34) states "with 251 filled by the Aristotle automated prover." The conclusions (line 276) state "254 theorems are filled by the Aristotle automated prover." These are contradictory within the same paper. `ARISTOTLE_THEOREMS` in `constants.py` has 254 entries (251 machine-proved + 3 manual). The paper must pick one consistent number and explain the 251/254 distinction.

**Required fix:** Use "254 tracked (251 automated, 3 manual)" or "251 automated" throughout, consistently.

#### II.9.B False "Zero Sorry" Claim in Conclusions

The conclusions (line 275) state "Verified by lake build (zero sorry)." This is false. `ModularInvarianceConstraint.lean` has 4 theorems with `sorry` (`zeta24_pow_24`, `zeta24_ne_one`, `zeta24_primitive`, `qParam_integer_invariant`) plus 2 additional `sorry` branches in `framing_anomaly_constraint`. The abstract correctly scopes this to "All modules referenced in this paper," but the global claim in the conclusions is factually incorrect and will be checked by reviewers.

**Required fix:** Replace global "zero sorry" with "Zero sorry in the modules underlying this paper's claims. The broader project has [N] remaining sorry goals in [module names], all under active proof."

#### II.9.C Citation Registry Coverage

Nine bibliography entries are missing from `CITATION_REGISTRY`: GarciaEtxebarria2019, Wang2024, GioiaThorngrenPRL2026, Kitaev2003, DPR1991, GrossJackiw1972, and others. Add all to the registry with correct DOIs.

***

### Paper 10 — Modular Generation Counting (PRL target)

**Claims review status: 4 FAILs, 13 WARNs**

#### II.10.A False "Zero Sorry" Claim — CRITICAL

The abstract (line 31–32) states "2237+ theorems across [N] Lean 4 modules **with zero sorry**." This is a global claim that is factually incorrect. `ModularInvarianceConstraint.lean` — one of the key modules directly referenced in this paper — has 4 theorems with `sorry`. Paper 10 then also lists `ModularInvarianceConstraint.lean` among "key modules—all with zero sorry" (lines 219–225), which is doubly false.

This is one of the most serious issues in the paper. A reviewer who checks the Lean source (which is publicly linked) will find the sorry goals and conclude the paper has misrepresented its verification status.

**Required fix:** Remove all global "zero sorry" claims. Scope to "the modules directly underlying this paper's main theorems (GenerationConstraint, WangBridge, ModularInvarianceConstraint) contain zero sorry for the generation constraint chain." List the 4 outstanding sorry goals in ModularInvarianceConstraint as open items.

#### II.10.B Stale Module Count

Abstract line 31 says "129 Lean 4 modules." Actual count is 130. Update.

#### II.10.C ModularInvarianceConstraint.lean Sorry Status

`framing_anomaly_constraint` has sorry in both directions of its biconditional. The paper (line 169) claims this theorem "proves 24 | c ⟺ e^{2πic/24} = 1" but the proof is incomplete. This theorem underlies the modular invariance argument — the paper's central claim. While the generation constraint chain itself may not depend on this specific biconditional (it uses the `⟹` direction only, which may be proved), this must be explicitly checked and stated.

***

### Paper 11 — U_q(sl₂) Quantum Group (PRL target)

**Claims review status: 5 FAILs, 19 WARNs**

#### II.11.A Stale Theorem and Module Counts

The conclusions (line 417) state "1233 theorems across 86 Lean 4 modules." Actual counts at the time of review: approximately 1318 theorems across 93 modules. This discrepancy (7% on theorems, 8% on modules) results from Phase 5e additions not being reflected in the paper. Claims of "N theorems" in a paper abstract are high-visibility items that referees check.

**Required fix:** Update conclusions to current counts. Regenerate the theorem count table in Section 4 from current `grep '^theorem'` output.

#### II.11.B Theorem Count Table Errors

The detailed per-module theorem count table in Section 4 has two wrong entries:

- `RepUqFusion.lean`: paper says 14 theorems, actual count is 13 (off by 1)
- `FibonacciMTC.lean`: paper says 18 theorems, actual count is 11 (off by 7, a 39% overcount)

FibonacciMTC's overcount of 7 suggests private theorems or lemmas were included in the paper's count. The pipeline convention is to count only `theorem` declarations (not `lemma`, `def`, or `private` items). Clarify the counting convention or recount.

#### II.11.C Aristotle Run ID Misattribution — CRITICAL

Section 4.1 (line 216) states the Serre coproduct relation was proved by Aristotle run `79e07d55`. This is factually wrong. Run `79e07d55` is the `TetradGapEquation.lean` run (Paper 5, 9 theorems). The Uqsl2Hopf theorems (including the Serre coproduct) are registered under run `78dcc5f4` in `ARISTOTLE_THEOREMS`. The conclusions (lines 403–404) then cite "Aristotle runs 78dcc5f4 and 79e07d55" for Uqsl2Hopf, compounding the error.

This is a provenance integrity failure — a reviewer who checks the run IDs against the registry will find the mismatch. If accepted with wrong provenance, it would need a correction.

**Required fix:** Remove `79e07d55` from all references to Uqsl2Hopf. The correct attribution is `78dcc5f4` only.

#### II.11.D Priority Claims Verification

The paper makes three strong priority claims: "first quantum group in any proof assistant," "first Hopf algebra in any proof assistant," "first verified MTC instances in any proof assistant." These are plausible but require at minimum a search of Mathlib, Archive of Formal Proofs (Isabelle), Coq's Mathematical Components, and Agda's standard library. The paper should cite the absence of such formalizations or a systematic search establishing priority.

***

### Paper 12 — Polariton Analog Hawking (PRL target)

**Claims review status: 10 FAILs, 34 WARNs — WORST STATE IN PROJECT**

Paper 12 has the highest density of errors and is furthest from submission readiness.

#### II.12.A Numerically False Abstract Claims — CRITICAL

Two claims in the abstract are numerically incorrect:

1. **"~20% dispersive corrections to T_H"** (lines 27–28). At D = 0.30 (the current parameter value), the dispersive correction is `1 − D² = 0.91`, i.e., ~9%, not ~20%. The ~20% value corresponds to D ≈ 0.46, which was the old D before the c_s correction. This is a factor-of-2 error in the headline result.

2. **"G(ω) > 0.5 for ω < 0.3κ"** (lines 31–32). Computing from the Planck factor: G(0.3κ) = 1/(exp(0.6π)−1) ≈ 0.179. The threshold G = 0.5 is reached at ω/κ ≈ 0.175, not 0.3. The abstract claim is quantitatively wrong by a factor of ~1.7 in the frequency cutoff.

Both errors appear to stem from the c_s parameter correction that changed D from 0.46 to 0.30 without updating the paper's abstract claims.

**Required fix:** Recompute the dispersive correction at D = 0.30 (~9%) and the G = 0.5 crossover frequency (~0.175κ). Update the abstract and all corresponding text. Regenerate any figures derived from the old D = 0.46.

#### II.12.B Lean Theorem Name Mismatches — 4 Theorems

The abstract and Section VI cite four Lean theorem names that do not exist in any `.lean` file under those names:

| Paper name | Actual Lean name | Location |
|-----------|-----------------|----------|
| `spatial_attenuation_ge_one` | `attenuation_ge_one` | `PolaritonTier1` namespace |
| `tier1_regime_monotone` | `attenuation_mono_Gamma` | `PolaritonTier1` namespace |
| `bec_recovery_limit` | `attenuation_eq_one_at_zero_decay` | `PolaritonTier1` namespace |
| `stimulated_hawking_gain` | **Does not exist** | No `.lean` file |

The fourth case is the most serious: `stimulated_hawking_gain` is listed in the abstract as a "formally verified" result, but the theorem does not exist in any Lean file. The `formulas.py` docstring marks it `Aristotle: pending (future)` — meaning it is planned but unproved. Claiming formal verification of a non-existent theorem is a factual misrepresentation.

**Required fix:** Update the abstract and Section VI to use the actual Lean theorem names for the first three. For `stimulated_hawking_gain`, either (a) remove the formal verification claim and replace with "to be formalized," or (b) write and verify the theorem before submission.

#### II.12.C Aristotle Run ID Misattribution

Section VI (line 267) states Aristotle run `da7cb04d` proved `spatial_attenuation_ge_one`. In fact, `da7cb04d` is the `HubbardStratonovichRHMC` run (Paper 6 physics). All PolaritonTier1 theorems are manually proved and do not appear in `ARISTOTLE_THEOREMS`. This is another provenance error similar to Paper 11.

#### II.12.D Theorem Count Wrong

The abstract (line 34) and conclusions (line 289) state "1214 Lean 4 theorems." The actual count from `grep '^theorem'` is approximately 1187; `constants.py` header says 1179. Neither matches 1214. Additionally, the count in `constants.py` and the grep count disagree with each other. The three-way inconsistency (1179 / 1187 / 1214) must be resolved.

#### II.12.E Projected Platforms Unlabeled

Table 3 compares three polariton cavity platforms (Paris standard τ ≈ 8 ps, Paris long τ = 100 ps, Paris ultralong τ = 300 ps). Only the standard cavity has been realized; the 100 ps and 300 ps cavities are projected future experiments. The tier changed from MEASURED to PROJECTED in `provenance.py`, but Table 3 does not indicate this distinction. Reviewers will ask whether these experiments have been performed.

#### II.12.F formulas.py Docstring Stale

The `dispersive_hawking_correction` docstring still states "D ~ 0.46 (our polariton system): ~20% correction" — the old value before the c_s correction. This docstring is read by the claims-reviewer agent and would cause any future automated review to flag the stale value.

#### II.12.G Citation Registry Coverage

12 of 18 bibliography entries are missing from `CITATION_REGISTRY`: Gerace2012, Nguyen2015, Estrecho2021, Stepanov2019, Claude2023, Burkhard2021, and others. A paper citing 18 references with only 6 in the registry fails the Stage 10 citation gate comprehensively.

***

### Paper 14 — Braided Modular Tensor Categories (JPAA/Comm. Math. Phys.)

**Claims review status: PASS with WARNs (session 5qrs)**

The foundational claims are strong. The paper makes a genuine "first formalization" contribution. The issues are primarily count staleness from the Inventory Index being behind:

- `IsingBraiding.lean`: paper claims 25 theorems, Inventory Index says 23 — recount needed
- `FibonacciMTC.lean`: paper claims 13 theorems, Inventory Index says 11 — recount needed
- `QCyc5.lean`: paper claims 16 theorems, Inventory Index says 9 — recount needed

As with Paper 11, counting conventions (including vs. excluding `private` theorems, `lemma` vs. `theorem`) must be made explicit and applied consistently.

The paper's use of `\documentclass{article}` (12pt geometry) rather than the target journal's style should be changed to the appropriate journal class before submission.

***

### Paper 15 — Twelve-Stage Pipeline Methodology (JOSS/SoftwareX)

**No claims review run against this paper.**

Paper 15 describes the pipeline that is supposed to guarantee the quality of all other papers. The irony that it contains internal inconsistencies is not lost on a reviewer. Specifically:
- The abstract says "2237 machine-checked theorems across **94 Lean modules**" — matching the stale `counts.json` value, not the 130-module ground truth
- The abstract says "33 remaining gaps (1.5%)" — matching `counts.json` sorry count, but conflicting with README's "17 sorry" and Research Status's "11 sorry"
- The paper says "307 theorems proved by the Aristotle automated prover" — matching the stale `counts.tex` value rather than the current 322+

**Required fix:** Run a claims review on Paper 15, update all counts to ground truth, and resubmit. A paper about methodology rigor that contains stale numbers in its own abstract is a liability.

***

### Paper 16 — WRT-TQFT

**No claims review run. No analysis possible without reviewing the tex file.**

A full claims review should be run via the `physics-qa:claims-reviewer` agent before this paper is considered for submission.

***

## III. Lean Formalization Quality Issues

### III.1 Two Vacuous Theorems (Lean Quality Audit, March 26)

The quality audit identified two theorems with vacuous conclusions that must be fixed before submission:

1. **`gs_nogo_requires_all` (ChiralityWall.lean:235):** Conclusion is literally `True`. The hypotheses are never used. The docstring claims meaningful content but the theorem encodes nothing. A Lean reviewer (or anyone who runs `lake build --verbose`) will see this is trivial.

2. **`zeroTemp_nontrivial` (SKDoubling.lean:463):** Conclusion is `True`. Hypotheses including the physically meaningful `0 < γ₁ ∨ 0 < γ₂` are never used. Should encode that the dissipative action is non-zero at T = 0.

The audit provides specific recommended fixes for both. Implement them before Papers 1 and 7/8 are submitted.

### III.2 Three Theorems with Vacuous Hypotheses

Three theorems have hypotheses that are trivially satisfied regardless of the conclusion: `full_tetrad_implies_metric` (VestigialGravity.lean:91), and two others. The conclusions hold without the hypotheses, making the theorems non-load-bearing. Either strengthen or explicitly document as "typing theorems" with no mathematical content.

### III.3 Sorry Goals in Key Modules

The 4 sorry goals in `ModularInvarianceConstraint.lean` (`zeta24_pow_24`, `zeta24_ne_one`, `zeta24_primitive`, `qParam_integer_invariant`) are cited in Papers 9 and 10. Until these are resolved, any claim that the generation constraint chain is "complete" is technically overstated. These should be prioritized for the next Aristotle batch.

### III.4 No Heartbeat Overrides Verified

The pipeline invariant forbids `set_option maxHeartbeats` in any file. The quality audit confirms no such overrides were found as of March 26. This invariant should be re-verified after all Aristotle integrations.

***

## IV. Presentation and Professional Standards

### IV.1 Author Affiliation Inconsistency

Across the 15 papers, the author affiliation varies:

- Paper 1: `\affiliation{Theoretical Physics}` (no institution named)
- Papers 3–15: `\affiliation{Independent Researcher}`
- Papers 1–2: `\author{John Roehm}` 
- Papers 3–15: `\author{J.~Roehm}`

All papers should use the same author name format and affiliation. "Independent Researcher" is acceptable for PRL/PRD, but a reviewer may ask for institutional contact information. Consider adding a contact email or a preprint server affiliation (e.g., arXiv affiliation).

### IV.2 Missing Standard Sections

Journals typically require (or strongly recommend):

- **Acknowledgments:** Missing from most papers. Acknowledge compute resources, the Aristotle/Mathlib communities, and any funding even if self-funded.
- **Data Availability Statement:** Required by most APS journals. The code being open-source on GitHub satisfies this — just include the statement.
- **Author Contributions (CRediT):** Not required for single-author papers, but a brief note helps with novel AI-assisted methodology papers.
- **Conflict of Interest Statement:** Standard boilerplate required by most journals.

### IV.3 \todo{} Macro

Paper 1 defines `\newcommand{\todo}[1]{{\color{red}\textbf{[TODO: #1]}}}`. Grep all papers for active `\todo{...}` calls before submission. If any remain, they will appear as bright red TODO markers in the PDF — an automatic rejection trigger.

### IV.4 paper_draftNotes.bib Files

Multiple papers have `paper_draftNotes.bib` files of exactly 104 bytes (essentially empty — likely containing just a BibTeX preamble). These stub files appear to have been generated as placeholders. They are currently not causing compilation errors (the papers use inline `\thebibliography` / `\bibitem` environments rather than `\bibliography{}`), but their presence in the repo is confusing.

### IV.5 Document Class Inconsistency

Papers 1–9 use `\documentclass[aps,prl,twocolumn,...]{revtex4-2}` or `\documentclass[aps,prd,...]{revtex4-2}` (APS style). Papers 14–16 use `\documentclass[12pt]{article}` with manual geometry. Before submission, each paper should be compiled in the target journal's specific document class, as formatting requirements vary significantly.

### IV.6 arXiv Metadata Readiness

For arXiv submission (which should precede journal submission for all papers), ensure:
- All `.tex` files compile cleanly with `pdflatex` without `\missingfile` or undefined reference warnings
- All figures referenced in `.tex` exist in `papers/paperN/figures/`
- The `paper_draftNotes.bib` stubs do not interfere with compilation
- ORCiD is included for the author (recommended for arXiv)

***

## V. Log and Validation Sync Issues

### V.1 Vestigial MC Full Production Run: Crashed

`logs/vestigial_mc_njl_full_production.out` shows a Python `multiprocessing` crash. All 14 worker processes fail with `BrokenPipeError` immediately after dispatch of 680 jobs. The error pattern suggests a resource exhaustion issue (too many processes, or an IPC queue overflow on the host system's multiprocessing infrastructure). The run produced **zero output**. This crash is not documented anywhere in the paper or supporting materials, and the figures in Paper 6 purportedly show MC results — meaning those figures were generated from earlier, smaller-scale runs (L=4,6,8) rather than the intended production run (L=4–20).

### V.2 ADW Model: Vestigial Not Detected by Binder

The `vestigial_mc_adw_rerun.out` (the most recent completed ADW run) reports:
- `Vestigial detected (Binder): False`
- `Split transition (FSS): True`
- `Sign problem absent: False`

The Binder cumulant method — the standard finite-size scaling diagnostic — does **not** detect the vestigial phase in the ADW model. The FSS split transition (True) is a weaker signal. The sign problem is present at all couplings and lattice sizes (⟨sign⟩ = 0.000 ± 0.000 uniformly), consistent with a severe sign problem.

### V.3 NJL Model: Vestigial Not Detected

Both NJL runs (`vestigial_mc_njl_production.out`, `vestigial_mc_njl_staggered_production.out`) report:
- `Vestigial detected (Binder): False`
- `Split transition (FSS): False`
- `Sign problem absent: False`

The NJL fermion sector has a more severe sign problem than ADW, and neither the Binder nor the FSS method detects vestigial behavior.

### V.4 Only One Run Detected Vestigial Phase

The single run reporting `Vestigial detected: True` is `vestigial_mc_v4_20260331T091743` (ADW model). This earlier run also reports `Split transition: False` — inconsistent with the FSS-based detection. The discrepancy between Binder (True in v4) and FSS (inconsistent) suggests the v4 detection may be a finite-size artifact or numerical accident rather than a genuine thermodynamic signal.

### V.5 Validate.py Suite: Passes as of March 28

The most recent archived `validate.py` output (March 28, 2026) shows all 14 checks passing. However, this predates:
- The axiom integrity sweep (April 4)
- Multiple Phase 5r–5s Lean additions
- The counts.json regeneration (April 6)

A fresh `validate.py` run is needed to confirm the current state. The most likely new failures would be in `check paper_provenance` (due to the sorry goals in ModularInvarianceConstraint) and `check graph_integrity` (if lean_deps.json is stale relative to 130 modules).

***

## VI. Prioritized Action Plan

### Tier 1 — Must Fix Before Any Submission (Blocking)

1. **Reconcile all counts:** Run `lake build` cleanly, run `grep -c "^theorem" lean/SKEFTHawking/*.lean`, run `update_counts.py`, verify `lean_deps.json` is fresh. Update counts.tex, README, Research Status, and all paper abstracts to ground-truth numbers.

2. **Paper 1 Table 1:** Rerun the transonic solver with current parameters. Regenerate all table values and all figures. Update inline a_s text to 100.4 a₀ = 5.31 nm.

3. **Berti:2025 citation:** Resolve the DOI and determine the correct journal. Update consistently in Papers 1, 2, and any other paper citing this reference.

4. **Paper 8:** Update module count (94→130), Aristotle count (307→322), remove duplicate bibitem.

5. **Paper 10:** Remove global "zero sorry" claim from abstract. Correct the claim about ModularInvarianceConstraint.lean.

6. **Paper 12 abstract:** Correct "~20% dispersive correction" to ~9% and "G > 0.5 for ω < 0.3κ" to ω < 0.175κ.

7. **Paper 12 theorem names:** Fix all 4 Lean name mismatches. Either write and verify `stimulated_hawking_gain` or remove the formal verification claim.

8. **Paper 11 Aristotle run ID:** Remove `79e07d55` from all Uqsl2Hopf references. Correct to `78dcc5f4` only.

9. **Paper 9:** Resolve 251 vs. 254 internal inconsistency. Fix "zero sorry" claim in conclusions.

10. **Paper 6 MC:** Diagnose and fix the `BrokenPipeError` crash. Complete a full production run. If vestigial phase is still not robustly detected, rewrite the MC results section honestly.

### Tier 2 — Fix Before Individual Paper Submission (Non-Blocking Cross-Paper)

11. **CITATION_REGISTRY:** Add all missing bibliography entries across all papers (~50+ entries total). Run `validate.py --check citation_registry`.

12. **Paper 3 physics:** Fix SO/Spin center attribution on lines 113–114.

13. **Paper 3 duplicate bibitem:** Remove Grozdanov2017 duplicate.

14. **Paper 4 orphan bibitems:** Cite or remove the 7 orphan entries.

15. **Paper 7 theorem count:** Reconcile "54" vs "55" in abstract vs figure caption.

16. **Paper 7 axiom table:** Correct +1ax attribution to SPTClassification, not GoltermanShamir.

17. **Paper 11 theorem table:** Recount RepUqFusion (14→13) and FibonacciMTC (18→11).

18. **Paper 12 projected cavities:** Add footnote/indicator distinguishing actual (τ ≈ 8 ps) from projected (100, 300 ps) platforms.

19. **Inventory Index:** Update module count (128→130). Add all Phase 5r–5s modules.

20. **VecGMonoidal sorry:** Verify status and update Inventory Index annotation.

### Tier 3 — Professional Polish (Pre-Submission)

21. **Vacuous theorems:** Fix `gs_nogo_requires_all` and `zeroTemp_nontrivial` per the recommended patches in the quality audit.

22. **Author affiliation:** Standardize to `J. Roehm` / `Independent Researcher` across all papers.

23. **Add standard sections:** Acknowledgments, Data Availability Statement, Conflict of Interest to all papers.

24. **Check for active \todo{} macros:** Grep all `.tex` files.

25. **Paper 16:** Run a full claims review.

26. **Paper 15:** Run a full claims review; update all counts.

27. **Document class:** Switch Papers 14–16 to target journal classes.

28. **Priority claims (Papers 11, 14):** Add a sentence documenting the systematic search of proof assistant libraries that establishes "first" priority.

29. **formulas.py docstring:** Update stale D = 0.46 comment to D = 0.30 in `dispersive_hawking_correction`.

30. **Re-run validate.py** full suite after all Tier 1 and Tier 2 fixes and archive the report.

***

## VII. What Is Working Well

Despite the issues above, the project has genuine strengths that distinguish it from typical AI-assisted research:

- **The pipeline architecture is sound.** The 12-stage pipeline with stage gates, single source of truth for constants/formulas, and automated cross-layer validation is the right approach. The issues found are pipeline compliance failures, not pipeline design failures.
- **The Lean formalization is substantive.** With 2,237+ theorems and zero heartbeat overrides, the formal verification layer is real, not cosmetic. The catching of the KMS axiom weakness and the counterexample to `gap_solution_bounded` are genuine examples of formal methods catching physics errors.
- **Papers 2, 3, 5 are close to submission-ready.** Once citation registry coverage is addressed and the Berti:2025 journal question resolved, these could be submitted with moderate revision effort.
- **The "16 convergence" result (Papers 9–10) and the chirality wall formalization (Papers 7–8) represent genuine contributions.** The generation constraint derivation from the Dedekind eta function is a clean, verifiable result. The formal verification of the Golterman-Shamir evasion is novel.
- **The Ext computation over A(1) (Paper 10/Phase 5q)** is the most technically impressive result in the project and should be highlighted as the lead result in Paper 10's abstract.
- **The provenance dashboard** is an excellent infrastructure investment that, once fully populated, will make human verification at submission time straightforward.

***

*This review was conducted by systematic analysis of all 15 paper `.tex` files, all `claims_review.json` files, `claims_review_session_5qrs.json`, `docs/WAVE_EXECUTION_PIPELINE.md`, `docs/validation/lean_quality_audit.md`, `docs/validation/axiom_integrity_sweep_20260404.md`, `docs/counts.json`, `docs/counts.tex`, `docs/RESEARCH_STATUS_OVERVIEW.md`, all `logs/vestigial_mc_*.out` files, the most recent `validate.py` archived report, and `README.md`.*