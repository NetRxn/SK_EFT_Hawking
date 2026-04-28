---
paper: paper42b_cc_emergent
reviewer: adversarial-reviewer
model: claude-opus-4-7
review_date: 2026-04-28T15:30:00Z
readiness_gates_version: 1
---

# Adversarial Review — paper42b_cc_emergent

## Summary

Paper 42b (Phase 6e Wave 5, MicroscopicCoefficientMatch, closes Decision
Gate E.4) is structurally clean on the major axes — 11 substantive Lean
theorems / 0 sorry / 0 new axioms (`lake build` clean), 42/42 pytest
PASS, all 8 cited Lean theorem names resolve, the cross-bridge calls
into LinearizedEFE / HeatKernelExpansion / HigherCurvatureStructure
are real, and the Decision-Gate-E.4 quantitative anchor `Λ^emerg / Λ_obs
> 10¹⁰⁰` reproduces from `formulas.py` (`cc_problem_ratio` returns
3.46e122; lower-bound margin to the proven 10¹⁰⁰ is ~22 orders).
`validate.py` reports paper42b "all P1 passed; advisory on
NumericalFreshness, ComputationCorrectness."

**Findings: 1 BLOCKER, 3 REQUIRED, 6 RECOMMENDED.** The BLOCKER is
Gate 1 / Gate 2 — paper42b's `Vergeles2025` bibitem text (line 386–388)
gives a different title than the verified registry value AND from
sibling papers (paper23, paper25, paper26) that bibcite the same key.
The REQUIREDs are: (i) numerical drift between paper-prose
"4.5×10⁻¹² GeV = 4.5 meV" diagnostic resolution locus and the actual
computed value (~2.83×10⁻¹² GeV = 2.83 meV) — same drift seeded in
`MICRO_MACRO_PARAMS['LAMBDA_UV_RESOLUTION_LOCUS_DIAGNOSTIC_GEV']`; (ii)
no MICRO_MACRO_PARAMS keys (`LAMBDA_OBSERVED_GEV4`, `M_PLANCK_GEV`,
`N_F_SM_DIRAC`, `LAMBDA_UV_RESOLUTION_LOCUS_DIAGNOSTIC_GEV`) carry
PARAMETER_PROVENANCE entries, despite being load-bearing for paper-prose
numerics; (iii) inaccurate Lean-proof attribution in §Method
("the cross-bridge to Wave 2 invokes the `a4_alpha_neg`,
`a4_beta_neg`, `a4_gamma_pos` sign theorems through the closed-form
aggregate `higherCurvature_stelle_sum_eq`") — the actual proof body
unfolds the *definitions* `a4_alpha/a4_beta/a4_gamma` and closes via
`ring` + `nlinarith`; it does **not** invoke the sign theorems.
RECOMMENDEDs cluster on Gate 1 (citation cache rollout to Phase 6i W1),
Gate 5 (formulas.py docstring drift to non-existent `ccProblemRatio`
Lean ref), Gate 6 (figure caption claims both contour bands but only
the cc_reproduced=60 contour is actually in-frame), and a few
narrative/forward-look cleanups.

Verdict: **draft-ready, NOT submission-ready** until the BLOCKER and
the three REQUIREDs land.

## Findings

### 1.1 — 🔴 BLOCKER — Vergeles2025 bibitem title disagrees with verified registry AND with sibling papers

- **Gate:** CitationIntegrity (Gate 1); CrossPaperConsistency (Gate 2 — sibling-paper title divergence)
- **Location:** `papers/paper42b_cc_emergent/paper_draft.tex:385-388` (bibitem); `src/core/citations.py:648-676` (registry); `papers/paper23_linearized_efe/paper_draft.tex:548`, `papers/paper25_gravitational_waves/paper_draft.tex:458` (sibling-paper bibitems); `docs/citation_verifications.jsonl:15` (cache).
- **Observed:** The paper-42b bibitem text reads:
  ```
  S. N. Vergeles, ``Self-consistent action of induced gravity from a
  free Dirac field on a lattice'', Phys. Rev. D 112, 054509 (2025).
  ```
  The CITATION_REGISTRY entry for `Vergeles2025` (verified via
  arXiv:2506.00036, registry `notes` field) has title **"Unitarity of
  4D Lattice Theory of Gravity"**. Paper 23 line 548 and paper 25 line
  458 both use the registry-verified title. Paper 42b's text is the
  *only* bibitem in the project that uses the "Self-consistent action
  of induced gravity from a free Dirac field on a lattice" string.
- **Evidence:** `docs/citation_verifications.jsonl:15` records the
  fresh-fetch verdict: `verdict:"match"` for `arxiv_id:"2506.00036"`,
  `fetched_title:"Unitarity of 4D Lattice Theory of Gravity"`. The
  cache `detail` field explicitly notes this came from a *prior*
  Stage-13 BLOCKER fix where a different mistaken title was caught and
  corrected — exactly the same failure pattern is now recurring in
  paper 42b. The paper-42b string also doesn't match anything in the
  Vergeles arXiv record list (Vergeles' lattice-spinor preprints
  exist, e.g., arXiv:1903.09957 "Self-consistent action of induced
  gravity from a free Dirac field on a lattice", but that is **a
  different paper** at arXiv:1903.09957 (PRD 100, 104020, 2019), NOT
  PRD 112, 054509 (2025)). So the bibitem mixes the title of a 2019
  paper with the venue of the 2025 paper — a wrong-target citation.
- **Expected:** Replace the bibitem title with "Unitarity of 4D Lattice
  Theory of Gravity" (the actual title at PRD 112, 054509 / arXiv:2506.00036),
  matching paper23/paper25/paper26/registry. If the
  paper-42b authors specifically intended the 2019
  self-consistent-action result, they need a *different* bibkey
  (e.g., `Vergeles2019`) registered against arXiv:1903.09957 / PRD 100,
  104020 with `provides` documenting the load-bearing claim. Given the
  abstract/intro language references the ADW heat-kernel programme +
  microscopic-to-macroscopic match — the 2025 unitarity paper is the
  intended primary anchor.
- **Fix:** One-line edit to lines 386–388:
  ```
  \bibitem{Vergeles2025}
  S. N. Vergeles, ``Unitarity of 4D Lattice Theory of Gravity'',
  \emph{Phys. Rev. D} \textbf{112}, 054509 (2025).
  ```
- **Cache:** cache-verified for the registry entry (arXiv:2506.00036 ↔ PRD 112, 054509). The bibitem text simply has not been updated to match.

### 2.1 — 🟡 REQUIRED — Resolution-locus prose value (4.5 meV) drifts from computed value (2.83 meV)

- **Gate:** ComputationCorrectness (Gate 4); also tags ParameterProvenance (Gate 3) at the constants seed
- **Location:** `paper_draft.tex:212-213` (prose); `src/core/constants.py:2702` (`LAMBDA_UV_RESOLUTION_LOCUS_DIAGNOSTIC_GEV: 4.5e-12`)
- **Observed:** Paper prose at line 212-213 states:
  > "The diagnostic resolution locus
  > $\Lambda_{UV} \simeq 4.5 \times 10^{-12}\,\mathrm{GeV} = 4.5\,\mathrm{meV}$
  > (four-meV scale, far sub-electroweak) is the unique unphysical band
  > where $\Lambda^{emerg} \simeq \Lambda_{obs}$ holds."

  Independent computation from
  `Lambda_UV_resolution = (Lambda_obs / a_0(16))^(1/4)`
  (the equation defining the locus) using the project's own constants
  yields **2.83 × 10⁻¹² GeV = 2.83 meV**, not 4.5×10⁻¹². The seed
  constant `MICRO_MACRO_PARAMS['LAMBDA_UV_RESOLUTION_LOCUS_DIAGNOSTIC_GEV']`
  in `src/core/constants.py:2702` carries the same 4.5e-12 value.
- **Evidence:**
  ```
  uv run python -c "
  import math; from src.core.constants import MICRO_MACRO_PARAMS
  a0_16 = 4*16/(4*math.pi)**2
  res = (MICRO_MACRO_PARAMS['LAMBDA_OBSERVED_GEV4']/a0_16)**(1/4)
  print(f'{res:.4e}')   # → 2.8301e-12
  "
  ```
  Result: 2.83×10⁻¹² GeV (= 2.83 meV), 60% smaller than the paper's
  4.5×10⁻¹² GeV figure. The brief states "4-meV resolution-locus" — so
  the *target* phrasing is fine, but the literal "4.5" specifically
  is wrong.
  Conversion check: 1 GeV = 10⁹ eV = 10¹² meV, so 2.83×10⁻¹² GeV =
  2.83 meV (sanity); 4.5×10⁻¹² GeV = 4.5 meV (sanity). Both
  conversions are arithmetic-correct; what's wrong is the *value*.
  The "(four-meV scale, far sub-electroweak)" parenthetical is
  consistent with either ~3 meV or ~5 meV (both are "four-ish meV"),
  but the specific 4.5 number is load-bearing in the verdict-band
  caption + Fig. 1 marker.
- **Expected:** Either
  (a) Update both `MICRO_MACRO_PARAMS['LAMBDA_UV_RESOLUTION_LOCUS_DIAGNOSTIC_GEV']`
  and the paper prose to the actually-computed 2.83×10⁻¹² GeV (= 2.83
  meV); say "≃ 2.8 meV" or "≃ 3 meV" colloquially; OR
  (b) Document in `MICRO_MACRO_PARAMS` what convention produces 4.5,
  and confirm the paper prose calls out *which* convention (e.g., a
  different `a_0` normalization). No such convention is presently
  documented.
- **Fix:** Recompute and replace:
  - `src/core/constants.py:2702`: `'LAMBDA_UV_RESOLUTION_LOCUS_DIAGNOSTIC_GEV': 2.83e-12`
  - `paper_draft.tex:212-213`: "$\Lambda_{UV} \simeq 2.83 \times 10^{-12}\,\mathrm{GeV} = 2.83\,\mathrm{meV}$
    (sub-meV-cubed-electroweak)" — and adjust `(four-meV scale,...)` to
    `(few-meV scale,...)` or similar honest hedging.
  - Figure caption (line 226-227) and figure marker — verify
    `fig_lambda_emerg_parameter_scan` source uses the same updated value.

### 2.2 — 🟡 REQUIRED — Wave 5 microscopic params have no PARAMETER_PROVENANCE entries

- **Gate:** ParameterProvenance (Gate 3)
- **Location:** `src/core/constants.py:2653-2703` (`MICRO_MACRO_PARAMS`); `src/core/provenance.py` (`PARAMETER_PROVENANCE` dict)
- **Observed:** None of the load-bearing Wave-5 microscopic-match
  parameters used in paper42b's prose has a corresponding
  `PARAMETER_PROVENANCE` entry:
  - `LAMBDA_OBSERVED_GEV4 = 2.6e-47` (cited in paper42b §3 as Planck
    2018; primary source = Aghanim+ 2020 A&A 641, A6, Table 2 / Eq. 17)
  - `M_PLANCK_GEV = 1.221e19` (cited at line 100 / Theorem 1)
  - `N_F_SM_DIRAC = 16` (cited as the SM-like benchmark at line 100,
    163, 186, etc.)
  - `LAMBDA_UV_RESOLUTION_LOCUS_DIAGNOSTIC_GEV = 4.5e-12` (cited at
    line 212; load-bearing for the paper's resolution-locus claim)
  - `CC_REPRODUCED_RATIO_FLOOR = 1.0e60` (verdict-band threshold,
    cited line 204)
  - `CC_RESOLVED_LOG10_BAND = 1.0` (verdict-band threshold, cited
    line 202)
  Search:
  `grep -nE "LAMBDA_OBSERVED|N_F_SM_DIRAC|MICRO_MACRO|LAMBDA_UV_RESOLUTION|CC_REPRODUCED|CC_RESOLVED" src/core/provenance.py`
  returns **0 lines**.
  `M_PLANCK_GEV` does have an entry under the key `GRAV.M_PLANCK_GEV`
  in `provenance.py:1657`, but the bare key `M_PLANCK_GEV` used by
  `MICRO_MACRO_PARAMS` does not link there.
- **Evidence:** Pipeline Invariant 8 + CHECK 15 require every
  experimental parameter to have a verified provenance entry. paper42b
  cites Planck-2018 (Aghanim+ 2020) for Λ_obs at line 79–80 / 147–151
  but doesn't run the value through provenance.
- **Expected:** Add Wave-5-specific PARAMETER_PROVENANCE entries:
  - `MICRO_MACRO.LAMBDA_OBSERVED_GEV4` → Planck 2018 A&A 641, A6, Table 2
    (Ω_Λ h² = 0.3155, h = 0.6736 → ρ_Λ derivation chain)
  - `MICRO_MACRO.LAMBDA_UV_RESOLUTION_LOCUS_DIAGNOSTIC_GEV` →
    *PROJECTED / DERIVED* (algebraic from `LAMBDA_OBSERVED_GEV4` /
    `a_0(16)`); the value should be flagged DERIVED, marked
    `human_verified_date: <today>`, and cross-checked against the
    actual `(Lambda_obs / a_0(16))^(1/4)` calculation (which is
    finding 2.1's main hit).
  - `MICRO_MACRO.N_F_SM_DIRAC` → derivation note: 16 = standard Dirac
    benchmark (Christensen-Duff convention; matches Vassilevich
    Eq. 4.37 spinor count).
- **Fix:** Add 4–6 entries to `PARAMETER_PROVENANCE` keyed
  `MICRO_MACRO.<NAME>`; flip `llm_verified_date` to today, add
  `human_verified_date` after author confirmation. Same pattern
  already used for `GRAV.*` keys.

### 5.1 — 🟡 REQUIRED — Method-section attribution claim about Wave 2 cross-bridge inaccurate

- **Gate:** LeanProofSubstance (Gate 5); AssumptionDisclosure (Gate 6)
- **Location:** `paper_draft.tex:344-347` (Method §)
- **Observed:** Paper prose:
  > "the cross-bridge to Wave 2 invokes the `a4_alpha_neg`,
  > `a4_beta_neg`, `a4_gamma_pos` sign theorems through the closed-form
  > aggregate `higherCurvature_stelle_sum_eq`."

  Inspection of `lean/SKEFTHawking/MicroscopicCoefficientMatch.lean:353-358`:
  ```lean
  theorem higherCurvature_stelle_sum_eq (N_f : ℝ) :
      a4_alpha N_f + a4_beta N_f + a4_gamma N_f =
        -(7 * N_f / 810) * fourPiSqInv := by
    unfold a4_alpha a4_beta a4_gamma
    ring
  ```
  And `higherCurvature_stelle_sum_negative` (line 364-369):
  ```lean
  theorem higherCurvature_stelle_sum_negative
      {N_f : ℝ} (hN : 0 < N_f) :
      a4_alpha N_f + a4_beta N_f + a4_gamma N_f < 0 := by
    rw [higherCurvature_stelle_sum_eq]
    have h_inv_pos : 0 < fourPiSqInv := fourPiSqInv_pos
    nlinarith
  ```
  Neither proof body invokes `a4_alpha_neg`, `a4_beta_neg`, or
  `a4_gamma_pos`. The aggregate is closed by *unfolding the
  definitions* of a4_alpha/a4_beta/a4_gamma (not the sign theorems)
  and then ring/nlinarith. The sign theorems exist in
  `HigherCurvatureStructure.lean:163, 170, 180` and could in principle
  participate, but the actual proof bypasses them.
- **Evidence:**
  ```
  grep "a4_alpha_neg\|a4_beta_neg\|a4_gamma_pos" lean/SKEFTHawking/MicroscopicCoefficientMatch.lean
  → 1 hit (line 362, in a *docstring* comment), 0 hits in proof bodies.
  ```
  This is a P6 cross-bridge integrity drift — the paper claims a
  cross-module Lean call by name that doesn't actually occur. Per
  the project's own `feedback_python_lean_refs_drift.md` discipline,
  every cross-reference in prose must be backed by a Lean call in the
  body.
- **Expected:** Either (a) **rewrite the proof body** to actually invoke
  the sign theorems (e.g., re-prove `higherCurvature_stelle_sum_negative`
  by `linarith [a4_alpha_neg hN, a4_beta_neg hN, a4_gamma_pos hN, ...]`
  — but note this won't work directly because α + β is negative
  enough to dominate γ > 0; the current ring-based aggregate proof is
  actually the stronger / cleaner path), OR (b) **rewrite the prose**
  to accurately describe the cross-bridge as a closed-form aggregate
  that is *consistent with* the individual sign theorems (Wave 2)
  but proven directly. (b) is the cleaner fix.
- **Fix:** Replace lines 344-347 with:
  > "the cross-bridge to Wave 2 invokes the
  > `a4_alpha`, `a4_beta`, `a4_gamma` definitions (Wave 2 §) directly,
  > collapsed to the closed-form aggregate
  > `higherCurvature_stelle_sum_eq` via `ring`, with the sign claim
  > established by `nlinarith` on the rational `-7/810` coefficient.
  > The Wave 2 sign theorems (`a4_alpha_neg`, `a4_beta_neg`,
  > `a4_gamma_pos`) provide the corresponding individual-coefficient
  > facts."
  This is honest about the proof structure and still attributes the
  Wave 2 sign witnesses correctly.

### 1.2 — 🔵 RECOMMENDED — All 8 external bibkeys lack citation_verifications.jsonl records

- **Gate:** CitationIntegrity (Gate 1; cache-completeness audit)
- **Location:** `docs/citation_verifications.jsonl` (cache); `src/core/citations.py` (registry).
- **Observed:** Of the 12 bibitems in paper42b, 4 are `inprep: True`
  self-cites (LinearizedEFE2026, Roehm2026Wave1, HigherCurvature2026,
  Roehm2026Wave4) and exempt from cache requirement. The other 8 —
  Sakharov1968, Adler1982, Diakonov2011, VladimirovDiakonov2012,
  Vergeles2025, Vassilevich2003, Stelle1977, Planck2018 — all carry
  `doi_verified: True` (or, for Sakharov1968, registry-flagged
  no-DOI), but the only entry in
  `docs/citation_verifications.jsonl` is **the single Vergeles2025
  record from a prior paper26 review**. The other 7 have **zero cache
  records**.
- **Evidence:**
  `grep -nE "Sakharov1968|Adler1982|Diakonov2011|VladimirovDiakonov2012|Vassilevich2003|Stelle1977|Planck2018" docs/citation_verifications.jsonl`
  → **0 lines**.
- **Expected:** Per the new Phase 6i Wave 1 hygiene roadmap (memory
  `feedback_primary_sources_cache.md`, `project_phase6i_opened.md`),
  this is the project-wide deferred citation-cache rollout — not a
  Wave-5-specific failure. Same pattern caught at paper42 review
  (finding 1.3 there). Note as RECOMMENDED with "deferred to Phase
  6i Wave 1" tag.
- **Fix:** No paper-local fix; queued for Phase 6i Wave 1.

### 1.3 — 🔵 RECOMMENDED — Diakonov2011 bibitem and registry both lack a venue/DOI

- **Gate:** CitationIntegrity (Gate 1; advisory)
- **Location:** `paper_draft.tex:376-378` (bibitem); `src/core/citations.py:617-632` (registry)
- **Observed:** The Diakonov2011 bibitem cites:
  > D. I. Diakonov, ``Towards lattice-regularized quantum gravity'',
  > arXiv:1109.0091 (2011).
  Registry: `doi: None, journal: None, page: None`. arXiv:1109.0091
  is the registered identifier. The arxiv-only entry is allowed for
  conference/preprint references, but Diakonov's "Towards lattice-
  regularized Quantum Gravity" (arXiv:1109.0091) is the proceedings
  paper of the Eichten-honoring volume — `Beauty in physics: theory
  and experiment` (AIP Conf. Proc. 1388 (2011), 41), so a DOI does
  exist (10.1063/1.3647344) and could be filled in.
- **Evidence:** No cache record; arXiv:1109.0091 is the only ID
  on record.
- **Expected:** Add the AIP DOI and venue to the registry; add a
  `match`-record to citation_verifications.jsonl. Same project-wide
  rollout as 1.2.
- **Fix:** Phase 6i Wave 1 candidate; minor.

### 1.4 — 🔵 RECOMMENDED — In-prep self-cite chain (Roehm2026Wave1, LinearizedEFE2026, HigherCurvature2026, Roehm2026Wave4) carries the same on-publication drift hazard as paper42

- **Gate:** CrossPaperConsistency (Gate 2; advisory)
- **Location:** `paper_draft.tex:404-419` (4 in-prep self-cites)
- **Observed:** All 4 self-cites are `inprep: True` in registry, with
  `journal: 'in preparation'`. Bibitem text mirrors that. As soon as
  paper23 / paper39 / paper40 / paper42 are submitted to a venue, the
  registry will need to be flipped, AND every paper that back-cites
  these (paper41, paper42, paper42b) needs to be rebuilt with the
  published metadata, otherwise the bibitem strings drift from the
  registry.
- **Evidence:** Same finding as paper42 review's 8.1; same fix pattern.
- **Expected:** No paper-local fix. Add to Phase 6i Wave 1 queue:
  on-publication-flag-flip + back-citing-paper-rebuild.
- **Fix:** QI register entry (no edit to paper42b today).

### 5.2 — 🔵 RECOMMENDED — formulas.py docstring Lean ref `MicroscopicCoefficientMatch.ccProblemRatio` does not exist in the Lean source

- **Gate:** LeanProofSubstance (Gate 5); P6 drift per `feedback_python_lean_refs_drift.md`
- **Location:** `src/core/formulas.py:8819` (`cc_problem_ratio` docstring)
- **Observed:** `cc_problem_ratio` docstring contains:
  > Lean: MicroscopicCoefficientMatch.ccProblemRatio

  But:
  ```
  grep -n "ccProblemRatio" lean/SKEFTHawking/MicroscopicCoefficientMatch.lean
  → 0 hits
  ```
  No `ccProblemRatio` declaration exists in the Lean module. The
  closest Lean equivalent would be a definition like
  `def ccProblemRatio Λ_UV N_f := lambdaEmergMicroscopic Λ_UV N_f / lambdaObservedGeV4`
  but this has not been added.
- **Evidence:** Direct grep on the Lean file.
- **Expected:** Either (a) add a `ccProblemRatio` definition + a
  positivity lemma to the Lean module so the Python docstring's
  cross-reference resolves, OR (b) update the docstring to
  `Lean: MicroscopicCoefficientMatch.lambdaEmergMicroscopic /
  MicroscopicCoefficientMatch.lambdaObservedGeV4 (algebraic
  composition; not a separate def)` and remove the dangling reference.
  Project memory says (b) is acceptable when downstream doesn't need
  the named def, but the cross-ref must be honest.
- **Fix:** 5-minute edit to formulas.py docstring; or 10-line addition
  to Lean module (preferred, as it surfaces the ratio as its own
  named object).

### 6.1 — 🔵 RECOMMENDED — Figure caption claims two contour bands but only one (cc_reproduced=60) is in-frame

- **Gate:** NarrativeGrounding (Gate 7; figure-caption fidelity)
- **Location:** `paper_draft.tex:222-232` (Fig. 1 caption);
  `papers/paper42b_cc_emergent/figures/fig_lambda_emerg_parameter_scan.png`
- **Observed:** Caption claims:
  > "...the |log₁₀(Λ^emerg/Λ_obs)|=1 (`cc_resolved` boundary) and
  > log₁₀(ratio)=60 (`cc_reproduced` boundary) contours overlaid."

  Visual inspection of the rendered figure shows the right panel has
  exactly one contour line drawn (labeled "60"); the
  |log₁₀ ratio|=1 contour is presumably off-scale in the right panel
  because the plotted Λ_UV range starts at QCD-scale ~1 GeV and the
  resolution locus is at ~10⁻¹² GeV — the cc_resolved boundary is
  to the left of the visible Λ_UV axis. The caption's claim "both
  contours overlaid" is technically false — only one is in-frame.
  Also: the left panel's four `N_f = 1, 4, 16, 100` curves visually
  collapse to a single line because the y-axis spans 50+ orders of
  magnitude and the N_f-induced spread is only ~2 orders.
- **Evidence:** Direct PNG inspection.
- **Expected:** Either (a) update caption to say "log₁₀(ratio)=60
  contour overlaid; the |log₁₀ ratio|=1 boundary lies at
  Λ_UV ≃ 2.83×10⁻¹² GeV, beyond the displayed Λ_UV range", OR
  (b) extend the right-panel Λ_UV axis to 10⁻¹⁴ GeV so the cc_resolved
  contour is visible, OR (c) add a separate inset showing the
  meV-scale resolution locus. Option (a) is cheapest. Note that
  fixing finding 2.1 (resolution locus value) and this caption
  consistency together is preferable.
- **Fix:** 1-line caption rewording, OR one figure-source change in
  `visualizations.py` to extend the verdict-map's x-axis range.

### 7.1 — 🔵 RECOMMENDED — "no shelter from the cosmological-constant fine-tuning problem" is interpretive prose

- **Gate:** NarrativeGrounding (Gate 7; advisory)
- **Location:** `paper_draft.tex:55-57` (abstract); also §Discussion line 311-313
- **Observed:** Abstract concludes:
  > "Together with Wave~1's Decision Gate~E.2 (heat-kernel ↔
  > linearized-EFE Newton-constant calibration), this closes the
  > microscopic-coefficient match question: the ADW programme provides
  > **no shelter** from the cosmological-constant fine-tuning problem."

  And §7 line 311-313: "The emergent-gravity reformulation does *not*
  provide shelter from the Weinberg cosmological-constant problem."

  These are interpretive claims about the *space of all possible
  emergent-gravity formulations* — what's actually proven in Lean is
  the narrower quantitative anchor (`Λ^emerg(M_Pl, 16) > 10¹⁰⁰ Λ_obs`)
  + a verdict-band scan in `MICRO_MACRO_PARAMS` ranges. The paper's
  prose generalizes from "the natural-cutoff a_0 calculation in the
  ADW heat-kernel programme" to "the ADW programme as a whole" — but
  e.g. a topological CC mechanism (Phase 6c W1) inside the ADW
  programme could still resolve the problem (and in fact paper32 +
  the Discussion §7 line 318-324 explicitly say so). The claim "ADW
  programme provides no shelter" is therefore over-strong vs. what's
  in scope; paper32's strong-CP topological-DE mechanism is itself an
  ADW-compatible CC source.
- **Evidence:** Lean theorem `lambdaEmergMicroscopic_at_planck_natural_far_exceeds_observed`
  is specifically about the *heat-kernel a_0 channel* at the natural
  cutoff. It does not exclude *other* CC channels in the ADW programme.
  The paper's own §Discussion line 320-324 acknowledges this:
  "Phase~6c Wave~1 strong-CP topological dark energy achieves Λ_obs
  via a separate mechanism (Zhitnitsky topological-charge density)."
- **Expected:** Tighten the abstract + §Discussion language to
  "the heat-kernel-a_0 channel of the ADW programme" rather than
  "the ADW programme" — making explicit that the paper's no-shelter
  result is for the dimension-correct vacuum-energy channel, not for
  alternative CC mechanisms (Zhitnitsky topological, etc.).
- **Fix:** Replace "ADW programme provides no shelter" → "the
  heat-kernel a_0 channel of the ADW programme provides no shelter"
  in abstract (line 56-57) and §Discussion (line 311-313). The
  Conclusion §line 351-355 already does this correctly ("the
  ADW heat-kernel programme reproduces the cosmological-constant
  problem in emergent form, with no fine-tuning shelter under
  natural (Λ_UV, N_f)") — abstract should mirror.

### 7.2 — 🔵 RECOMMENDED — "matching Vassilevich Eq.(4.37) up to the spinor-trace convention" — primary-source check

- **Gate:** CitationIntegrity (Gate 1) / NarrativeGrounding (Gate 7); advisory
- **Location:** `paper_draft.tex:115-117`
- **Observed:** Paper claims `a_0(N_f) = 4N_f/(4π)²` "matches
  Vassilevich Eq. (4.37) up to the spinor-trace convention". The
  literature convention is that Eq. (4.37) of Vassilevich 2003 gives
  `a_0(x) = (4π)⁻²` for a *single* spin-1/2 Dirac fermion (per the
  trace convention `tr 1 = 4` for the Dirac matrices implicit in the
  fermion-loop measure), so a `4 N_f / (4π)²` aggregate over `N_f`
  Dirac species is consistent. The hedge "up to the spinor-trace
  convention" is the right hedge. But the cached
  `Lit-Search/Phase-6e/primary-sources/Vassilevich2003.pdf` was not
  re-spot-checked at this Stage 13 — the registry `provides` field
  says "Christensen-Duff Dirac a₀, a₂, a₄ coefficients (Eqs. 4.37-4.42)",
  consistent with paper42b's claim.
- **Evidence:** PDF cached + `primary_source_path` populated, but
  no per-paper Stage-13 spot-check appended.
- **Expected:** Either re-spot-check the Vassilevich PDF at Eq.(4.37)
  during Phase 6i Wave 1 mass-cache rollout, OR add a one-line
  acknowledgement in paper prose: "Eq. (1) follows from Vassilevich
  Eq.(4.37) summed over `N_f` Dirac species and integrated against
  the `Λ_UV⁴` UV-momentum measure" — making the conversion factor
  explicit.
- **Fix:** Minor; defer to Phase 6i Wave 1 Vassilevich audit OR add
  a half-sentence parenthetical at line 115-117.

## Spot-check results (no findings)

The following paper-42b-specific questions raised in the review brief
were checked and do **not** produce findings:

- **(a) 11 substantive theorems / 0 sorry / 0 new axioms.**
  `grep -c '^theorem ' lean/SKEFTHawking/MicroscopicCoefficientMatch.lean`
  returns 11 (one of the 12 grep hits is a `theorem` token in a
  docstring, not a declaration). Final-pass `lake build SKEFTHawking.MicroscopicCoefficientMatch`
  returns "Build completed successfully (8269 jobs)" with no warnings.
- **(b) 42/42 pytest PASS.** `uv run python -m pytest tests/test_micro_macro_match.py -q`
  → "42 passed in 0.08s".
- **(c) Counts macros exist.** `grep "microscopicCoefficientMatch" docs/counts.tex`
  returns `\microscopicCoefficientMatchThms{11}` and
  `\microscopicCoefficientMatchTests{42}`. Both resolve. Both used in
  paper line 331 + 336.
- **(d) Quantitative ratio match.** `cc_problem_ratio(M_Pl, 16)` from
  formulas.py returns 3.4646e+122 (Python). Paper claims "approximately
  10¹²² ... 3.5×10¹²² ratio". ✓ within 1.5% rounding.
- **(e) `a_0(16) > 4/10` arithmetic.** `4*16/(4π)²` = 0.4053 > 0.4. ✓
- **(f) Lean theorem `lambdaEmergMicroscopic_at_planck_natural_far_exceeds_observed`
  proof body.** Inspected at `MicroscopicCoefficientMatch.lean:198-278`.
  Substantive: chain of `Real.pi_lt_d2` → `(4π)² < 160` → `a_0(16) >
  4/10` → `Λ_UV⁴ = 20736 · 10⁷²` → `8294.4 · 10⁷² > 26 · 10⁵²` (20
  orders margin). Not a placeholder — full nlinarith / norm_num /
  field_simp arithmetic chain. **Gate 5 PASS for this theorem.**
- **(g) Bundled `H_MicroscopicCoefficientMatch` is a `def`, not a
  theorem.** Cannot smuggle a theorem. Three conjuncts each backed
  by a substantive theorem call in the Dirac witness body
  (`matchResidual_at_alpha_one`, `lambdaEmergMicroscopic_pos`,
  `higherCurvature_stelle_sum_negative`). Falsifier
  `perturbed_alpha_not_H_MicroscopicCoefficientMatch` invokes
  `matchResidual_eq_zero_iff_alpha_unity` by name — confirmed not
  vacuous. **Gate 6 PASS for the bundle.**
- **(h) All 12 bibkeys present in CITATION_REGISTRY.** Verified via
  `grep` on each key in `src/core/citations.py`.
- **(i) Wave 4 deferred RECOMMENDED 8.1 closed.** `Roehm2026Wave4`
  registry entry exists at line 2132, used_in lists paper42b only,
  notes explicitly mention closure of "deferred RECOMMENDED 8.1 from
  Wave 4 Stage 13 review per project_phase6e_w4_shipped.md memory". ✓
- **(j) paper42b assignment in PAPER_DRAFT_MAPPING.md.** Line 62
  shows: "**D3 §21** (Λ^emerg microscopic prediction + CC-problem
  reproduction) + **D5 §7** (CC-channel constraint: heat-kernel a₀
  does not produce Λ_obs naturally) + **F §6, §8**". ✓
- **(k) `validate.py --check readiness_submission_gate` for paper42b.**
  Reports "all P1 passed; advisory on NumericalFreshness,
  ComputationCorrectness". Validate-pass at paper level even with the
  findings above; the Stage-13 review surfaces what validate doesn't
  catch.

## QI Candidate

**Pattern:** Two related citation-integrity drifts both involve title
strings — the Vergeles2025 BLOCKER (1.1) is a *third* recurrence of
title divergence between bibitem and registry across the project
(paper26 caught this at the prior Stage 13; paper40 caught the
hallucinated CalmetCapozzielloPryer2019; paper42b ships with a wrong
title for the same Vergeles2025 already-fixed-in-other-papers
arXiv:2506.00036 entry). The QI is that **the registry truth field
isn't being applied as a check at Stage 5/9 build time**.

**Suggestion:** Phase 6i Wave 1 should add
`validate.py --check bibitem_titles_match_registry` — for every
`\bibitem{key}` in any `paper_draft.tex`, parse the bibitem text via
naive regex, extract the title string, and compare against the
registry's `title` field (allow a registry-known-aliases list for
edge cases like "supertheorems" / "super theorems"). This is one-shot
scriptable; the `bibitem_hash` helper in `scripts/citation_cache.py`
already exists and tokenizes title/author strings, so the diff can be
mechanical.

**Pipeline gap:** Stage 13's job is precisely to catch what this QI
suggests automating. The third title-mismatch recurrence in the
project's history is the threshold for promoting it to a
`validate.py` check rather than relying on adversarial review alone.
