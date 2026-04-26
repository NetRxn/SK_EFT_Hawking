---
paper: paper20_scalar_rung
reviewer: adversarial-reviewer
model: claude-opus-4-7
review_date: 2026-04-26T19:25:00Z
readiness_gates_version: 1
scope: Wave 1b BHL gauge-embedding additions on top of Wave 1
---

# Adversarial Review — paper20_scalar_rung (Wave 1b)

## Summary

Aggregate verdict: **RED**. Findings: **3 BLOCKER**, **3 REQUIRED**, **1 RECOMMENDED**. Wave 1b §6 BHL embedding adds quantitative-branch claims but ships at least one wrong-target citation (`AndrianovAndrianovAfonin2020` arXiv → different authors/DOI/page), one structurally tautological "tracked hypothesis" (`H_FierzCompletenessExtended`), an internal Higgs-mass contradiction (Wave 1 uses 125.25 GeV, Wave 1b uses 125.20 GeV in the same paper), and a paper-table count drift (paper claims 23 BHLGaugeEmbedding theorems; module has 22). All four newly-introduced bibkeys still carry `doi_verified: None` in `CITATION_REGISTRY`. Submission blocked on Gates 1, 2, 3, 5; Gate 9 NumericalFreshness reopens on the count drift; Gate 7 NarrativeGrounding reopens on the tautology-misrepresentation.

## Findings

### 1.1 — 🔴 BLOCKER — `AndrianovAndrianovAfonin2020` is a wrong-target citation

- **Gate:** CitationIntegrity
- **Location:** `papers/paper20_scalar_rung/paper_draft.tex:645-648`; `src/core/citations.py:1533-1551`
- **Observed:** Bibitem claims authors "A.~A.~Andrianov, V.~A.~Andrianov, S.~S.~Afonin", DOI `10.1140/epjc/s10052-020-08691-4`, page 1179, arXiv `1906.09579`, EPJC 80.
- **Evidence (fresh-fetch, 2026-04-26):**
  - `https://arxiv.org/abs/1906.09579` (and v3) → title matches ("Top condensation model: a step towards the correct prediction of the Higgs mass") but **authors are A.A. Osipov, B. Hiller, A.H. Blin, F. Palanca, J. Moreira, M. Sampaio**. DOI returned by arXiv is `10.1140/epjc/s10052-020-08716-y`. Published as **EPJC 80:1135**, NOT 80:1179.
  - The registry's claimed DOI `10.1140/epjc/s10052-020-08691-4` was not fetched independently (Springer redirect path requires a follow-up resolver), but the arXiv-side authoritative metadata directly contradicts the registry's authors, DOI, and page.
- **Expected:** Either (a) update the registry/bibitem to the actual arXiv-1906.09579 paper (Osipov et al., EPJC 80:1135, DOI `…08716-y`), in which case the bibkey/cite text should be renamed; OR (b) retain the AAA bibkey only if there is a *different* AAA paper that genuinely matches the metadata — arXiv ID would have to change.
- **Fix:** WebFetch the registry's claimed DOI directly; if it resolves to a real Andrianov/Andrianov/Afonin paper, update arXiv ID to match; if it resolves to nothing or the same Osipov paper, replace the bibitem and registry entry with the correct primary source. Append a `verdict: wrong_author/wrong_venue` record to `docs/citation_verifications.jsonl`.
- **Cache:** fresh-fetch (https://arxiv.org/abs/1906.09579, https://arxiv.org/abs/1906.09579v3); no prior cache record for this bibkey.

### 1.2 — 🔴 BLOCKER — Four Wave 1b bibkeys still carry `doi_verified: None`

- **Gate:** CitationIntegrity
- **Location:** `src/core/citations.py:1502, 1521, 1542, 1617` (`MiranskyTanabashiYamawaki1989`, `Hill2025Redux`, `AndrianovAndrianovAfonin2020`, `Cvetic1999`)
- **Observed:** All four entries have `doi_verified: None`. Notes field repeatedly says "doi_verified pending — … fetch round."
- **Evidence (fresh-fetch, 2026-04-26):**
  - `Hill2025Redux` → arXiv 2503.21518 confirms title "Natural Top Quark Condensation (a Redux)", author Christopher T. Hill, year 2025, hep-ph. **Verdict: match**, can be flipped to `True`.
  - `Cvetic1999` → arXiv hep-ph/9702381 confirms title "Top quark condensation", author G. Cvetic, RMP 71:513 (1999), DOI 10.1103/RevModPhys.71.513. **Verdict: match**, can be flipped to `True`.
  - `MiranskyTanabashiYamawaki1989` → DOI 10.1142/S0217732389001210 redirects to worldscientific.com which blocked WebFetch (gateway 403/permission). NASA ADS bibcode `1989MPLA....4.1043M` likewise blocked. **Verdict: fetch_failed.** Independent verification still pending; cannot be flipped without a successful fetch.
  - `AndrianovAndrianovAfonin2020` → see 1.1, **Verdict: wrong_author/wrong_venue.**
- **Expected:** Each bibitem entered into the registry as part of Wave 1b should have either `doi_verified: True` with a recorded fetch evidence, or a tracked finding with verdict and last-attempted-fetch timestamp. None of these four are in `docs/citation_verifications.jsonl`.
- **Fix:** Append four records to `docs/citation_verifications.jsonl` (Hill = match; Cvetic = match; MTY = fetch_failed; AAA = wrong_author). Flip Hill + Cvetic `doi_verified: True`. Defer MTY (or use NASA ADS via a non-WebFetch path). Resolve AAA per 1.1.
- **Cache:** fresh-fetch for Hill and Cvetic; fetch_failed for MTY; fresh-fetch for AAA (1906.09579).

### 1.3 — 🔵 RECOMMENDED — `AndrianovAndrianovAfonin2020` cited but not used in body

- **Gate:** CitationIntegrity
- **Location:** `papers/paper20_scalar_rung/paper_draft.tex:358` (cite block in §6) and bibitem at line 645-648
- **Observed:** Bibkey appears once in a multi-cite `~\cite{BardeenHillLindner,MiranskyTanabashiYamawaki1989,Hill2025Redux,Cvetic1999}` … wait, AAA is **not** in this cite list. The bibitem is included but the body never `\cite`s it. The Lean module docstring at `BHLGaugeEmbedding.lean:44` references it ("Andrianov, Andrianov, Afonin, Eur. Phys. J. C 80, 1179 (2020)") but the .tex does not.
- **Evidence:** `grep -n "AndrianovAndrianovAfonin2020" papers/paper20_scalar_rung/paper_draft.tex` → only the `\bibitem{...}` line at 645.
- **Expected:** Either cite it in the body (e.g., as alternative-mechanism reference in §6.3 Hill correction) or remove the orphan bibitem.
- **Fix:** If finding 1.1 results in correcting the bibkey to point at Osipov et al., decide whether the Osipov paper is actually the intended Wave 1b alternative-bilocal reference and add a body cite; otherwise remove. Lean docstring at `BHLGaugeEmbedding.lean:44` must be updated in lockstep.
- **Cache:** N/A (orphan-cite, not a target verification).

### 2.1 — 🔴 BLOCKER — Internal Higgs-mass contradiction within paper 20

- **Gate:** CrossPaperConsistency (intra-paper variant) → also Gate 9 NumericalFreshness
- **Location:**
  - `paper_draft.tex:206` — Wave 1: `m_H = 125.06\text{ GeV}$, against the observed $125.25 \pm 0.17$~GeV`.
  - `paper_draft.tex:394` — Wave 1b: `against PDG~2024 $m_H = 125.20\pm 0.11$~GeV~\cite{PDG2024}`.
  - Same paper, same observable (PDG 2024 Higgs mass), two different central values + uncertainties.
- **Evidence:**
  - `src/core/constants.py:1824` `EW.M_H_GEV = 125.25` (registry-canonical).
  - `papers/paper22_ew_phase_transition/paper_draft.tex:40,68,167,173,184` all use 125.20 GeV.
  - `src/core/citations.py:1635-1644` `PDG2024` is `doi_verified: True`. Per pdg.lbl.gov, the PDG 2024 Review reports `m_H = 125.20 ± 0.11 GeV` (averaged); 125.25 was the 2022/early-2024 value before the latest update.
- **Expected:** Either 125.20 or 125.25 chosen consistently across (a) `EW.M_H_GEV` constant, (b) paper 20 Wave 1 and Wave 1b prose, (c) figure captions, (d) paper 22. Pick one canonical value; propagate.
- **Fix:** Update `EW.M_H_GEV` to the current PDG 2024 value (likely 125.20), update paper 20 Wave 1 prose at line 206 (and `EW.M_H_MATCH_TOLERANCE` consumers), and re-verify the figure heatmap target `125.25` at line 319-331 + 425-432. Document in the change log.
- **Cache:** N/A — internal/cross-paper contradiction.

### 2.2 — 🟡 REQUIRED — Top-quark mass `172.57` GeV vs registry `172.76` / PDG note `172.69`

- **Gate:** ParameterProvenance + CrossPaperConsistency
- **Location:** `paper_draft.tex:430` (figure caption: `PDG $m_t = 172.57$~GeV`); compare `src/core/provenance.py:1078,1084` (`m_t = 172.76 GeV`, "PDG 2024 top mass m_t = 172.69 ± 0.30 GeV"). `constants.py` does not define an `M_TOP_GEV` symbol.
- **Observed:** Figure caption uses `172.57` (likely the most recent 2024 PDG mass-combination). Provenance notes say `172.69`. Y_TOP derivation uses `172.76`. Three values, one parameter, no canonical entry.
- **Expected:** A single `EW.M_TOP_GEV` constant in `constants.py` with a `PARAMETER_PROVENANCE` entry citing PDG 2024 page/table; all paper prose, figure captions, and Lean comments referring to PDG top mass should pull this value (or at least agree on it).
- **Fix:** (a) Add `EW.M_TOP_GEV` to `constants.py` and `PARAMETER_PROVENANCE` (with `human_verified_date`). (b) Choose a single PDG 2024 value — verify via pdg.lbl.gov which is current. (c) Update paper figure-caption + Lean module docstrings (`BHLGaugeEmbedding.lean` references `m_t ≈ 172.6`) to match.
- **Cache:** N/A.

### 3.1 — 🔴 BLOCKER — `H_FierzCompletenessExtended` is a structural tautology

- **Gate:** LeanProofSubstance + NarrativeGrounding
- **Location:**
  - `lean/SKEFTHawking/BHLGaugeEmbedding.lean:87-88` defines `bhlBilinearBasisDim cfg := 66 * (cfg.n_doublet * cfg.n_singlet * cfg.n_color * cfg.n_gen)`.
  - Lines 124-126 define `H_FierzCompletenessExtended cfg : Prop := bhlBilinearBasisDim cfg = 66 * (cfg.n_doublet * cfg.n_singlet * cfg.n_color * cfg.n_gen)`.
  - Lines 137-140: `theorem fierz_completeness_holds (cfg : BHLConfig) : H_FierzCompletenessExtended cfg := by unfold H_FierzCompletenessExtended; rfl`.
- **Observed:** The Prop unfolds to `X = X` by definition. There is no possible `cfg : BHLConfig` for which it can fail. The docstring (lines 122-123) explicitly claims "The hypothesis is genuinely non-trivial: a configuration with miscounted blocks would fail." This is **false**: the LHS is *defined* as the RHS, so miscounting is structurally impossible.
- **Evidence:** `\unfold H_FierzCompletenessExtended bhlBilinearBasisDim → 66 * (...) = 66 * (...)` reduces by `rfl` for any `cfg`. This matches the project anti-pattern in memory `feedback_tracked_hypothesis_nontrivial.md` ("Anti-pattern: `def H (x) := x = x`").
- **Expected:** A non-trivial Prop. The right structural shape would be a tracked equality between `bhlBilinearBasisDim cfg` and *an independently-defined Clifford × gauge tensor-product dimension* (e.g., `4 * 4 * (2 * cfg.n_doublet + cfg.n_singlet)^2 * cfg.n_color^2 * cfg.n_gen^2`, or whatever the actual block count is). Or parameterize over an abstract `dim_predicted : BHLConfig → ℕ` and require `dim_predicted cfg = bhlBilinearBasisDim cfg` — that *can* fail.
- **Fix:** (a) Replace `H_FierzCompletenessExtended` with a parametric form requiring agreement between the BHL-dimension constant and an independently-derived gauge-Clifford count. (b) Update paper §6.1 prose at lines 374-378 ("non-trivial in that miscounted configurations would fail") to reflect the real content. (c) Re-prove `fierz_completeness_holds` and `wave1b_open_manifest_consistent` accordingly. (d) Add a falsifier theorem (a concrete `cfg` for which the hypothesis would fail under a *wrong* `dim_predicted`).
- **Cache:** N/A.

### 3.2 — 🟡 REQUIRED — `H_HSCovariantBosonisation` is a definitional re-aliasing

- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/BHLGaugeEmbedding.lean:175-176`: `def H_HSCovariantBosonisation (φ : BHLAuxField) : Prop := IsHiggsBilinear φ`. Extraction theorem `hs_bosonisation_yields_higgs_bilinear` at line 180-182 is `(h_cov : ...) : IsHiggsBilinear φ := h_cov`.
- **Observed:** The "tracked hypothesis" is *literally* `IsHiggsBilinear`. The Prop has non-trivial content (some `BHLAuxField` values fail it), so this is not a tautology in the strict sense — but the abstraction adds zero structure. The paper at line 379-381 frames this as a separate tracked hypothesis ("inherits hypercharge `+1/2`") suggesting it encodes the BHL-bosonisation step *beyond* `IsHiggsBilinear`. It does not.
- **Expected:** Either (a) drop `H_HSCovariantBosonisation` and have downstream code consume `IsHiggsBilinear` directly, OR (b) make it strictly stronger than `IsHiggsBilinear` — e.g., add a constraint that the components transform in a specific way under the SU(2)_L action that `IsHiggsBilinear` doesn't capture.
- **Fix:** If (a), simplify the module and update paper §6.1 prose. If (b), strengthen the Prop (e.g., add a transformation-law field) and re-prove dependents. Currently the paper overclaims the abstraction's content.
- **Cache:** N/A.

### 4.1 — 🟡 REQUIRED — Paper claims 23 theorems in `BHLGaugeEmbedding.lean`; actual count is 22

- **Gate:** NumericalFreshness (count drift)
- **Location:**
  - `paper_draft.tex:471` — table cell `\texttt{BHLGaugeEmbedding.lean} (Wave~1b) & 23`.
  - `paper_draft.tex:498` — "A 48-test pytest suite covers every Lean theorem (24 Wave 1 + 24 Wave 1b)" — also implies 24 BHL theorems, internally inconsistent with the table.
- **Observed:** `grep -cE "^theorem [a-zA-Z_]" lean/SKEFTHawking/BHLGaugeEmbedding.lean → 23`, but inspection shows one match is at line 16 (`theorem that the BHL gauge-indexed extension is compatible with the`) which is **prose inside a docstring**, not a theorem decl. Real theorem count is 22 (lines 104, 129, 137, 180, 185, 191, 219, 233, 240, 258, 278, 285, 289, 311, 331, 340, 354, 382, 396, 411, 432, 454).
- **Expected:** Both literals (23 in table, 24 implied at line 498) must reference the canonical count macro (e.g., `\bhlGaugeEmbeddingTheorems{}` from `counts.tex`) and reflect the live module count.
- **Fix:** Reword the docstring at line 16 to avoid `^theorem ` (e.g., "structural transplant lemma") OR fix the count to 22. Add a counts macro and `\input{}` it. Reconcile the "48-test" claim with the actual test count.
- **Cache:** N/A.

### 5.1 — 🔵 RECOMMENDED — `\cite{Hill2025Redux}` predates publication; clarify preprint status

- **Gate:** NarrativeGrounding (feasibility-claim)
- **Location:** `paper_draft.tex:642-643` bibitem describes Hill 2025 as `arXiv:2503.21518 (2025)` only.
- **Observed:** Hill 2025 is currently a Fermilab preprint (FERMILAB-PUB-25-0219-T, v4 May 2025) with no journal publication confirmed. The paper relies on Hill's bilocal mechanism for the Wave 1b quantitative recovery (lines 397-417 + figure 2), framing it as load-bearing. A reader following the cite reaches a preprint without peer review.
- **Expected:** Bibitem should explicitly mark this as `(unpublished preprint)` so readers do not expect a peer-reviewed source. Wave 1b body prose should also flag the preprint dependency at the load-bearing point.
- **Fix:** Append `(arXiv preprint, unpublished)` to the bibitem and add a sentence in §6.3 noting the preprint status. Re-monitor for journal publication; flip the bibitem when published.
- **Cache:** match (verdict on Hill 2025 itself), but venue is preprint.

## QI Candidate

**Tracked-hypothesis tautology detection.** `H_FierzCompletenessExtended` was shipped with a docstring claiming non-trivial content while the Prop is `X = X` by definition. The same anti-pattern was caught in Wave 5y (`feedback_tracked_hypothesis_nontrivial.md`) and presumably hand-audited out of more recent waves, but Wave 1b regresses. Proposed: a `validate.py --check tracked_hypothesis_substance` extending the existing `PlaceholderMarker` extractor — for every `def H_<name> : Prop := ...`, attempt to prove `H_<name> arg = (X = X)` by `rfl` for an arbitrary `arg`; if successful, flag. Catches both the present case and any future def aliasing. Pairs with the existing semantic-tautology audit but at the `def Prop` layer rather than at the proof-body layer.
