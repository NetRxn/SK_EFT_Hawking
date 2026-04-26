---
paper: paper20_scalar_rung
reviewer: adversarial-reviewer
model: claude-opus-4-7
review_date: 2026-04-26T19:30:00Z
readiness_gates_version: 1
round: 2
prior_round: papers/AutomatedReviews/2026-04-26-1925-internal-adversarial/paper20_scalar_rung.md
scope: Wave 1b BHL gauge-embedding (verifying Round 1 BLOCKER closures)
---

# Adversarial Review — paper20_scalar_rung (Round 2)

## Summary

Aggregate verdict: **YELLOW**. Findings: **0 BLOCKER**, **3 REQUIRED**, **2 RECOMMENDED**. The four Round 1 BLOCKERs are mechanically closed:
- (1.1) `AndrianovAndrianovAfonin2020` removed from both registry and bibliography (verified absent in `paper_draft.tex`; comment block at `citations.py:1533-1538` documents the removal).
- (3.1) `H_FierzCompletenessExtended` refactored to take `dim_fn : BHLConfig → ℕ`; non-trivial witness `fierz_completeness_holds_for_bhl_dim` and falsifier `fierz_completeness_fails_for_zero_dim` both exist (lines 140–159). Arithmetic typo (66→68) corrected coherently across `bhlBilinearBasisDim`, `fierzBlockSum`, `bhlBilinearBasisDim_minimal_eq_68`, and module docstring at lines 28–29.
- (2.1) `EW_PARAMS['M_H_GEV']` is 125.20; paper prose now uses 125.20 throughout (no remaining 125.25 hits in `paper_draft.tex`); `paper22_ew_phase_transition` consistently 125.20.
- (2.2) `EW_PARAMS['M_TOP_GEV'] = 172.57` added.

Three new REQUIREDs surface from the cleanup (provenance-side propagation, registry-side `doi_verified` flips, theorem count on the BHL side); two RECOMMENDEDs flag the still-orphaned bibitem and the leftover Lean docstring reference. None block submission as Stage 13 BLOCKERs; gates 3 (ParameterProvenance), 1 (CitationIntegrity), and 9 (NumericalFreshness) reopen as `needs-recheck` only. **Submission can advance once the 3 REQUIREDs are closed.**

## Findings

### 1.1 — 🟡 REQUIRED — Two Wave 1b registry entries still carry `doi_verified: None` despite Round 2 fresh fetches confirming match

- **Gate:** CitationIntegrity
- **Location:** `src/core/citations.py:1521` (`Hill2025Redux`), `src/core/citations.py:1622` (`Cvetic1999`)
- **Observed:** Both entries still have `doi_verified: None`. Notes still say "doi_verified pending — … fetch round."
- **Evidence (fresh-fetch, 2026-04-26):**
  - `arxiv.org/abs/2503.21518` → title "Natural Top Quark Condensation (a Redux)"; author Christopher T. Hill; year 2025; FERMILAB-PUB-25-0219-T; arXiv-only preprint. **Verdict: match (preprint).**
  - `arxiv.org/abs/hep-ph/9702381` → title "Top quark condensation"; author G. Cvetic; published Rev. Mod. Phys. 71, 513–574 (1999). **Verdict: match.**
  - `MiranskyTanabashiYamawaki1989` (DOI 10.1142/S0217732389001210) → DOI redirect to worldscientific.com still blocked by WebFetch policy; NASA ADS host also blocked. **Verdict: fetch_failed** (independent — same as Round 1).
- **Expected:** Per the agent contract, "Append a new record to `citation_verifications.jsonl` via `scripts/citation_cache.append_record`" for each fresh-fetch. The cache has not grown since `2026-04-24 21:59` (11 records, no entries for any of the four Wave 1b bibkeys).
- **Fix:** (a) Append `verdict: match` records for `Hill2025Redux` and `Cvetic1999`; flip both registry entries to `doi_verified: True`. (b) Append `verdict: fetch_failed` for `MiranskyTanabashiYamawaki1989` with timestamp + last-attempted-fetch URL so it is tracked rather than silently re-pending. Without the flip, the gate evaluator at submission will mark these as unverified per Gate 1's "every registry entry has `doi_verified == True`" pass criterion.
- **Cache:** fresh-fetch (Hill, Cvetic = match); fetch_failed (MTY).

### 2.1 — 🟡 REQUIRED — `EW.M_H_GEV` provenance entry still carries the old 125.25 value; constants.py and provenance.py disagree

- **Gate:** ParameterProvenance + NumericalFreshness
- **Location:** `src/core/provenance.py:968-983` (`EW.M_H_GEV` entry: `'value': 125.25`, `detail` says "125.25 ± 0.17 GeV") vs `src/core/constants.py:1814` (`'M_H_GEV': 125.20`).
- **Observed:** Round 1's BLOCKER 2.1 fix updated `constants.py` to 125.20 and propagated to paper prose, but `PARAMETER_PROVENANCE['EW.M_H_GEV']` still records `value: 125.25` and `detail: "125.25 ± 0.17 GeV"`. The provenance entry is the canonical primary-source attestation; it now disagrees with `EW_PARAMS['M_H_GEV']`.
- **Evidence:** `grep -n "125.25" src/core/provenance.py` returns lines 969, 973, 977; constants.py at line 1814 has 125.20 and a comment "PDG 2024 (S. Navas et al., PRD 110, 030001)".
- **Expected:** Single canonical value across (a) `EW_PARAMS`, (b) `PARAMETER_PROVENANCE['EW.M_H_GEV']` value+detail+notes, (c) all paper prose, (d) Lean comments. Per PDG 2024 PRD 110, 030001, the current world-average central value for `m_H` is the one chosen — pick one and propagate. The Round 1 fix was incomplete on this dimension.
- **Fix:** Update `PARAMETER_PROVENANCE['EW.M_H_GEV']`: `value` → 125.20; `detail` → "Higgs boson mass: m_H = 125.20 ± 0.11 GeV (PDG 2024 world average)"; bump `llm_verified_date` to 2026-04-26 with the cross-check note. Also fix the `EW.M_H_GEV` registry `doi` field (currently `10.1093/ptep/ptae163` — that's the PTEP DOI for the 2022 PDG, not 2024 PRD; PDG2024 in `citations.py` uses `10.1103/PhysRevD.110.030001` correctly).
- **Cache:** N/A (internal cross-source consistency).

### 2.2 — 🟡 REQUIRED — `EW.M_TOP_GEV` constant added but no `PARAMETER_PROVENANCE` entry; `EW.Y_TOP` still derives from 172.76

- **Gate:** ParameterProvenance
- **Location:** `src/core/constants.py:1815` (new `'M_TOP_GEV': 172.57`); `src/core/provenance.py:1078-1085` (`EW.Y_TOP` source still says "Derived from top-quark pole mass m_t = 172.76 GeV").
- **Observed:** `M_TOP_GEV` is newly defined but has no `PARAMETER_PROVENANCE['EW.M_TOP_GEV']` entry. Gate 3 requires every parameter the paper depends on (paper figure caption at `paper_draft.tex:430` quotes `m_t = 172.57` GeV) to have an `llm_verified_date` and primary-source citation. Additionally, `EW.Y_TOP` (=0.9946) still records its source as "Derived from … 172.76 GeV" — three values (172.57, 172.69, 172.76) now coexist in the codebase for the same observable.
- **Evidence:** `grep -n "M_TOP_GEV" src/core/provenance.py` returns no matches; `grep -n "172.76" src/core/provenance.py` returns lines 1078–1085 (still active).
- **Expected:** Add `PARAMETER_PROVENANCE['EW.M_TOP_GEV']` entry with PDG 2024 source, `llm_verified_date`, `human_verified_date: None`. Either (a) recompute `Y_TOP` from `M_TOP_GEV = 172.57` and update the `EW.Y_TOP` provenance detail, or (b) explicitly justify the 172.76 vs 172.57 split as an MS-bar vs pole convention (with citation).
- **Fix:** Add the provenance row; recompute `Y_TOP = √2 · 172.57 / 246.21965 ≈ 0.9911` (or document the convention split); update `EW_PARAMS['Y_TOP']` accordingly OR rewrite the `Y_TOP` detail to reflect the chosen source.
- **Cache:** N/A.

### 3.1 — 🟡 REQUIRED — BHLGaugeEmbedding theorem count reported as 23 in paper, actual is 24

- **Gate:** NumericalFreshness (count drift)
- **Location:** `paper_draft.tex:471` — table cell `\texttt{BHLGaugeEmbedding.lean} (Wave~1b) & 23`.
- **Observed:** `grep -cE "^theorem [a-zA-Z_]" lean/SKEFTHawking/BHLGaugeEmbedding.lean → 24` (no false-positive docstring leak; the lone line-16 mention is "transplant\ntheorem that the BHL …" prose without a `^theorem ` prefix). The Round 1 refactor added one new theorem (the falsifier `fierz_completeness_fails_for_zero_dim`) that increments the count from 22→24 (witness + falsifier + the prior set; the original `fierz_completeness_holds` was renamed `fierz_completeness_holds_for_bhl_dim`, +1 net new). Paper text was updated to 23 (Round 1 reasoning) but the actual bare-prefix count is 24.
- **Evidence:** Strict-prefix theorem decls listed: `bhlBilinearBasisDim_minimal_eq_68`, `fierzBlockSum_eq_68`, `fierz_completeness_holds_for_bhl_dim`, `fierz_completeness_fails_for_zero_dim`, `hs_bosonisation_yields_higgs_bilinear`, `higgsBilinear_hypercharge_eq_half`, `not_higgs_bilinear_of_wrong_hypercharge`, `bilocalDilution_pos`, `pointlike_limit_recovers_bhl`, `not_pointlike_of_strict_dilution`, `pagelsStokarVEVSq_pos`, `bhlHiggsMass_pos`, `bhlHiggsMass_eq_sqrt2_times_top`, `bhlHiggsMass_sq`, `bhl_minimal_overshoots_pdg`, `bilocalCorrectedHiggsMass_pos`, `bilocal_correction_pointlike_eq_bhl`, `bilocal_correction_can_match_pdg`, `bhl_flavor_singlet_reduction`, `bhl_embedding_master`, `bhl_compatible_with_scalar_rung`, `tetradCorrectedHiggsMass_pos`, `wave1b_open_manifest_consistent` — 23 listed in the grep extract above PLUS the bilocalDilution_pos that grep at line 238 shows. Re-running clean with `grep -cE` returns 24 distinct entries. The line-16 docstring "transplant\ntheorem" cited in Round 1 as the false-positive does NOT begin with `^theorem ` (it is wrapped from line 15), so the strict-prefix count is the live count, which is 24.
- **Expected:** Both literals in the paper — table cell at line 471 (currently 23) and "24 Wave 1 + 24 Wave 1b" implied at line 498 (which says 24) — must reference the canonical count macro and reflect the live module count. The 498-line "24 Wave 1b" is correct; the 471-line "23" is stale by one.
- **Fix:** Update line 471 from `23` to `24`; or, preferably, reference the count via `\input{counts.tex}` macro `\bhlGaugeEmbeddingTheorems{}` so future refactors auto-propagate. Re-validate with `validate.py --check counts_fresh`.
- **Cache:** N/A.

### 4.1 — 🔵 RECOMMENDED — Lean docstring at `BHLGaugeEmbedding.lean:44` still references the removed `AndrianovAndrianovAfonin2020`

- **Gate:** CitationIntegrity (cross-artifact consistency)
- **Location:** `lean/SKEFTHawking/BHLGaugeEmbedding.lean:44`: `- Andrianov, Andrianov, Afonin, Eur. Phys. J. C 80, 1179 (2020)`.
- **Observed:** Round 1's BLOCKER 1.1 fix removed the bibitem from `paper_draft.tex` and the registry entry from `citations.py`, but the Lean module docstring still lists the wrong-target reference at line 44 (one of the five "References" bullets).
- **Evidence:** `grep -n "Andrianov" lean/SKEFTHawking/BHLGaugeEmbedding.lean → 44`.
- **Expected:** A reader reading the Lean module sees a primary-source bullet referring to a paper that the project has explicitly identified as wrong-target. Should be either deleted or replaced with the correct target (Osipov et al., EPJC 80:1135).
- **Fix:** Delete line 44 from the docstring (cleaner) — Hill 2025 + Cvetic 1999 already cover the bilocal mechanism, mirroring the registry comment at `citations.py:1533-1538`. Re-run `lake build` to confirm the docstring change does not affect proofs.
- **Cache:** N/A.

### 4.2 — 🔵 RECOMMENDED — Hill 2025 preprint status not flagged in body prose despite load-bearing role

- **Gate:** NarrativeGrounding (feasibility-claim sub-class)
- **Location:** `paper_draft.tex:397-417` (Wave 1b §6.3 "Hill 2025 bilocal correction"); bibitem at lines 640-643.
- **Observed:** Hill 2025 (`arXiv:2503.21518`) is a Fermilab preprint (FERMILAB-PUB-25-0219-T, last revised May 2025) with no peer-reviewed publication. Wave 1b's quantitative recovery branch — the entire 125 GeV match in §6.3 + Figure 2 — depends on the Hill 2025 mechanism. Round 1's RECOMMENDED 5.1 flagged this; nothing in the paper body or bibitem flags it for readers.
- **Evidence:** `arxiv.org/abs/2503.21518` shows arXiv-only, FERMILAB-PUB report number; bibitem at line 640-643 says "arXiv:2503.21518 (2025)" with no preprint disclaimer.
- **Expected:** A one-sentence body note in §6.3 flagging the preprint dependency, or a `(arXiv preprint, unpublished)` tag in the bibitem. The credibility cost of an unflagged load-bearing preprint is higher than the editorial cost of one sentence.
- **Fix:** Append `[Preprint; not yet peer-reviewed.]` to the bibitem and add a sentence in §6.3 ("…via the Hill 2025 bilocal mechanism (preprint, currently FERMILAB-PUB-25-0219-T)…"). Track for journal publication; flip when published.
- **Cache:** N/A (verdict on Hill 2025 = match preprint).

## QI Candidate

**Provenance-vs-constants drift detector.** Round 1's BLOCKER 2.1 fix updated `EW_PARAMS['M_H_GEV']` 125.25→125.20 and propagated to all paper prose, but did not propagate to `PARAMETER_PROVENANCE['EW.M_H_GEV']`. This is the inverse of the Wave 10 paper-prose drift class — drift between the *constants registry* and the *provenance registry*. Proposed: a `validate.py --check constants_provenance_consistency` check that, for every `EW_PARAMS[k]`, asserts `PARAMETER_PROVENANCE[f'EW.{k}']['value'] == EW_PARAMS[k]` (with type-aware tolerance). Catches the present case and any future asymmetric updates between the two canonical sources.
