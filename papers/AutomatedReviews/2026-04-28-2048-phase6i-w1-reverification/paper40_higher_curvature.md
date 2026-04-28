---
paper: paper40_higher_curvature
reviewer: adversarial-reviewer
model: claude-opus-4-7
review_date: 2026-04-28T20:48:00Z
readiness_gates_version: 1
prior_review: papers/AutomatedReviews/2026-04-28-0158-internal-adversarial-reinvocation/paper40_higher_curvature.md
slug: phase6i-w1-reverification
---

# Adversarial Review (Phase 6i Wave 1 Re-verification) — paper40_higher_curvature

## Summary

Two findings: 0 BLOCKER, 2 REQUIRED, 0 RECOMMENDED. Gates affected:
ParameterProvenance (Gate 3), CitationIntegrity (Gate 1) advisory.
The original round-1 BLOCKER (`CalmetCapozzielloPryer2019` /
arXiv:1905.13728 hallucinated graph-NN citation) is **structurally
fixed**: the bibkey is renamed `CalmetCapozzielloPryer2017`, registry
points at the correct EPJC 77:589 (2017) / arXiv 1708.08253 paper with
`doi_verified: True`, and Phase-6e cache holds a non-empty 153 KB PDF
of the actual primary source. Phase 6i Wave 1's project-wide
primary-source cache rollout makes the failure mode structurally
non-recurrable for future bibitems. **Not submission-ready** strictly
on Gate 3 (`human_verified_date: None` on four HC_BOUND provenance
entries) — explicitly deferred to Phase 6i later waves per the close
report; not a re-verification regression.

## Wave 1 Verification

**Original BLOCKER status: STRUCTURALLY FIXED.**

| Original BLOCKER finding | Verification | Evidence |
|---|---|---|
| Round-1 1.1 — `CalmetCapozzielloPryer2019` arXiv:1905.13728 wrong-target (graph-NN paper, not gravity) | ✅ FIXED | (a) Registry entry `CalmetCapozzielloPryer2017` at `src/core/citations.py:2748-2771` carries arxiv `1708.08253`, DOI `10.1140/epjc/s10052-017-5172-3`, EPJC 77:589 (2017), `doi_verified: True`. (b) `paper_draft.tex:379-384` bibitem agrees: title "Gravitational effective action at second order in curvature and gravitational waves", arXiv:1708.08253, EPJC 77:589 (2017). (c) Cache file `Lit-Search/Phase-6e/primary-sources/CalmetCapozzielloPryer2017.pdf` exists, 153 735 bytes, non-empty PDF. (d) Fresh WebFetch of `arxiv.org/abs/1708.08253` returned title + author triple matching registry; Crossref API for the DOI returned volume 77, article 589, 2017. (e) Cache record appended to `docs/citation_verifications.jsonl` (verdict: match) for both Calmet2017 and Berti2015. |
| Round-1 1.2 — `Berti2015` venue Living Rev. Rel. → CQG | ✅ FIXED | Registry `Berti2015` (`citations.py:2772-2795`) reads `journal: 'Class. Quantum Grav.', volume: 32, page: '243001', doi: '10.1088/0264-9381/32/24/243001'`, `doi_verified: True`. Bibitem `paper_draft.tex:386-391` agrees. Cache PDF (7.1 MB) present at `Lit-Search/Phase-6e/primary-sources/Berti2015.pdf`. arXiv 1501.07274 fresh-fetch confirms journal-ref. |
| Round-1 1.3 — six bibitems `doi_verified: None` | ✅ FIXED | All seven paper40 bibkeys (Vassilevich2003, ChristensenDuff1979, Stelle1977, Lovelock1971, CalmetCapozzielloPryer2017, Berti2015, Roehm2026Wave1 with `inprep: True`) now read `doi_verified: True`. |
| Round-1 3.1 — HC_OBS_BOUNDS not in `constants.py`, no provenance | ✅ FIXED | `HIGHER_CURVATURE_PARAMS` lives in `constants.py`; four `PARAMETER_PROVENANCE` entries (HC_BOUND_LIGO_C_SQ, HC_BOUND_SRG_R_SQ, HC_BOUND_PULSAR_C_SQ, HC_BOUND_CASSINI_C_SQ) at `provenance.py:2756-2844` carry primary-source DOIs (PRL 119:161101, PRL 98:021101, ApJ 829:55, Nature 425:374) and `llm_verified_date: '2026-04-30'`. |
| Re-invocation 1.1, 1.2 — stale block-comment / docstring drift in `constants.py:2419-2422` and `visualizations.py:10212-10213` | ✅ FIXED | `grep -n "Calmet\|Berti" src/core/constants.py src/core/visualizations.py` returns only the corrected `EPJC 77, 589 (2017) [arXiv:1708.08253]` and `Class. Quantum Grav. 32, 243001 (2015)` strings; zero hits on retired `1905.13728` / `LRR 18, 1 (2015)` outside the legitimate `notes` traceability field of the new bibkey (citations.py:2768). |

**Recommendation:** QI item `qi-citationintegrity` may flip
`open → closed` with `evidence_on_close` pointing to
`docs/phase6i_wave1_close.md`. The structural failure mode that
permitted the round-1 hallucination — agents confabulating bibkeys
without a content-layer cross-check — is now blocked by Pipeline
Invariant #11 (every external bibitem has a primary-source cache file)
and the mandatory Stage-13 check
`validate.py --check citation_primary_sources_present`. Paper40's
seven bibkeys all satisfy the new invariant.

**Residuals (do not block QI closure):** `human_verified_date: None`
on the four HC_BOUND provenance entries (Finding 3.1 below) is a
ParameterProvenance gate item, not CitationIntegrity. Gate 3
remediation is tracked separately in Phase 6i Wave 2.

## Findings

### 1.1 — 🟡 REQUIRED — HC_BOUND primary-source experimental papers (Kapner, Weisberg-Huang, Bertotti-Iess-Tortora) are not entries in `CITATION_REGISTRY`

- **Gate:** CitationIntegrity (transitive)
- **Location:** `src/core/provenance.py:2767, 2790, 2813, 2836` cite DOIs `10.1103/PhysRevLett.119.161101`, `10.1103/PhysRevLett.98.021101`, `10.3847/0004-637X/829/1/55`, `10.1038/nature01997`. Of these, only `Abbott2017GW170817` (PRL 119:161101) appears in registry (`citations.py:2996`); the Kapner et al 2007 (Eöt-Wash), Weisberg-Huang 2016 (binary pulsar), and Bertotti-Iess-Tortora 2003 (Cassini) papers are not registered.
- **Observed:** Three of the four HC_BOUND ceilings the paper consumes (Eöt-Wash, pulsar, Cassini) trace through `provenance.py` to primary experimental papers that are not in `CITATION_REGISTRY`. Paper40 prose §4 lists the four ceilings and attributes them via `\cite{CalmetCapozzielloPryer2017,Berti2015}` only — i.e. via review/EFT-translation papers, not the primary measurements. Per Gate 3, "every non-PROJECTED parameter has a primary-source citation that resolves (via Gate 1)"; the underlying experimental sources are presently unverifiable through the project's citation infrastructure.
- **Evidence:** `grep -nE "'Kapner|'Weisberg|'Bertotti" src/core/citations.py` returns zero hits; `grep -n "Abbott2017GW170817" citations.py:2996` returns one hit (LIGO source registered for paper29, not paper40). Paper40's `\bibitem` block has no entry for any of these experimental papers.
- **Expected:** Either (a) add `Kapner2007EotWash`, `WeisbergHuang2016`, `BertottiIessTortora2003` to `CITATION_REGISTRY` with primary-source PDFs cached under `Lit-Search/Phase-6e/primary-sources/`, and add the corresponding `\bibitem`s to paper40 alongside the EFT-translation reference, OR (b) document explicitly in the paper that the four ceilings are quoted "via Calmet-Capozziello-Pryer 2017 EFT translation of [primary measurements]" — naming the primary measurements in prose rather than as bibitems.
- **Fix:** Option (a) is preferred per Pipeline Invariant #11 (every external bibitem cached). Phase 6i Wave 2 (parameter-provenance closure) is the natural place; this finding is structurally identical to the round-1 1.1 failure mode but at one transitive step further from the prose. Severity REQUIRED (not BLOCKER) because the paper does cite the EFT-translation reviews that themselves cite the primary papers — the chain is one indirect step, not a hallucination.
- **Cache:** N/A (registry gap, not citation cache)

### 3.1 — 🟡 REQUIRED — `human_verified_date: None` on all four HC_BOUND provenance entries

- **Gate:** ParameterProvenance (Gate 3)
- **Location:** `src/core/provenance.py:2771-2772, 2794-2795, 2817-2818, 2840-2841`
- **Observed:** All four HC_BOUND entries (`HC_BOUND_LIGO_C_SQ`, `HC_BOUND_SRG_R_SQ`, `HC_BOUND_PULSAR_C_SQ`, `HC_BOUND_CASSINI_C_SQ`) have `llm_verified_date: '2026-04-30'` and `human_verified_date: None`. Gate 3 in `READINESS_GATES.md` says "every parameter the paper depends on has `llm_verified_date` AND `human_verified_date` set" for submission; Pipeline Invariant 8 ("Paper submission requires human verification via the provenance dashboard") reinforces.
- **Evidence:** Direct inspection of `provenance.py:2771-2772` (`'human_verified_date': None,` / `'human_verified_notes': None,`) and analogous lines for the other three entries.
- **Expected:** Provenance dashboard human-verification pass on each of the four entries; populate `human_verified_date` with the verification ISO date. Per Phase 6e Wave 6 close memo (`project_phase6e_w6_shipped.md`), this item is explicitly deferred to Phase 6i. This finding is therefore a known, scheduled remediation, not a re-verification regression.
- **Fix:** Workflow step (provenance dashboard at localhost:8050), not a code edit. Acceptable at draft stage; blocks submission.
- **Cache:** N/A

### Other classes — no findings

- **Class 1 (CitationIntegrity, primary):** Seven paper40 bibkeys all in `CITATION_REGISTRY` with `doi_verified: True`. Six external entries (all but `Roehm2026Wave1` which is `inprep: True`) point to populated primary-source cache files in `Lit-Search/Phase-6e/primary-sources/` (Vassilevich2003.pdf 763 KB, ChristensenDuff1979.json 17 KB, Stelle1977.json 5.8 KB, Lovelock1971.abstract.txt 439 B, CalmetCapozzielloPryer2017.pdf 154 KB, Berti2015.pdf 7.1 MB). Fresh WebFetch verifications appended to `docs/citation_verifications.jsonl` for the two formerly-disputed entries (Calmet2017, Berti2015) — both verdict `match`.
- **Class 2 (ParameterDrift):** Section §3 closed-form coefficients $(\alpha, \beta, \gamma) = (-N_f/(324 (4\pi)^2), -41 N_f/(4320 (4\pi)^2), +17 N_f/(4320 (4\pi)^2))$ verified against Christensen-Duff $(c_R, c_{\mathrm{Ric}}, c_{\mathrm{Riem}}) = (-5/2160, +7/2160, -12/2160)$ by independent linear-system solve. Match. The closed-form rationals $5/2160, 7/2160, 12/2160$ in `lean/SKEFTHawking/HigherCurvatureStructure.lean:280-329` are bit-identical to the bibitem's Christensen-Duff convention.
- **Class 3 (LeanProofSubstance):** All cited Lean theorems (`a4_density_eq_a4_density_in_RC2GB_basis`, `a4_alpha_neg`, `a4_beta_neg`, `a4_gamma_pos`, `higher_curvature_below_pulsar_bound`, `higher_curvature_predictions_strictly_positive`, `H_HigherCurvatureWithinObservationalBounds_pulsar_witness`, `gaussBonnet_minus_weyl_eq_R_minus_Ricci_combination`, `weylSquared4D_eq_zero_iff_conformally_flat`) have substantive tactic-mode proof bodies (linarith / norm_num / abs_neg chains, mul_le_mul / positivity, ring after unfold) — no `rfl`-on-non-trivial, no hypothesis-as-output anonymous constructors. The 3-conjunct bundle in `higher_curvature_below_pulsar_bound` invokes three distinct Wave 1 coefficients with three distinct positivity arguments (P3 not redundant); the tracked-Prop witness is `refine ⟨_, _⟩` consuming the correctness-push, fully discharged at `B = 10^59` (P5 not vacuous).
- **Class 4 (CrossPaperConsistency):** Three shared bibkeys with companion papers — Vassilevich2003 (paper39, paper41, paper42b), ChristensenDuff1979 (paper39, paper41), Berti2015 (paper42), Stelle1977 (paper41, paper42b). Sampled cross-paper bibitems (paper42 Berti2015 — `paper42_nonlinear_efe/paper_draft.tex` `\bibitem{Berti2015}`) match paper40 bibitem character-for-character on the load-bearing fields (arXiv ID, journal, volume, page). No CONTRADICTS surfaces.
- **Class 5 (NarrativeOverclaims):** No `first formally verified` / `first in any proof assistant` / unification claims. The `~62 orders of magnitude below` feasibility claim (abstract:50-51, fig caption:218-222, conclusion:343-345) is now anchored quantitatively in the §5 paragraph "Anchoring the '62 orders below' claim" with explicit calculation of $|c_{\mathrm{Riem}}(N_f=27)| = 27/180/(4\pi)^2 \approx 9.49 \times 10^{-4}$ and ratio $10^{59}/9.49\times 10^{-4} \approx 10^{62}$ — verified arithmetically: $\log_{10}(10^{59}/10^{-3.02}) \approx 62$. The paragraph references `tests/test_higher_curvature.py::TestObservationalBounds`. ✓
- **Class 6 (AssumptionDisclosure):** `higher_curvature_below_pulsar_bound` carries hypotheses `0 < N_f` and `N_f ≤ 100`; both disclosed in `paper_draft.tex:232` (Lean code-block: `(hN_pos : 0 < N_f) (hN_max : N_f ≤ 100)`) and §5 prose ("natural fermion-count window $0 < N_f \le 100$"). The tracked-Prop framing in §5 ("forward-compatibility hook for tighter ceilings") is now framed correctly per round-1 Finding 6.1 closure. ✓
- **Class 7 (CountFreshness):** Macros `\higherCurvatureThms{}` (= 11) and `\higherCurvatureTests{}` (= 40) sourced from `\input{../../docs/counts.tex}`; no inline count literals. `validate.py --check counts_fresh` PASSES.
- **Class 8 (ProductionRunHealth):** Paper makes no Monte Carlo / numerical-simulation evidence claims. `grep -E "Monte Carlo|numerical evidence|simulation evidence" paper_draft.tex` returns zero. Gate 8 N/A.

## QI Candidate

**Recommended QI: `qi-citationintegrity` flip `open → closed`.**

The Phase 6i Wave 1 close report documents the structural cure for
the round-1 hallucination failure mode: every external bibitem now
carries a `primary_source_path` and a cached PDF / JSON / abstract
under `Lit-Search/Phase-X/primary-sources/`. The mandatory Stage-13
check `validate.py --check citation_primary_sources_present`
(`scripts/validate.py` CHECK 19) refuses any paper with a missing
cache. Pipeline Invariant #11 codifies the rule. Paper40's seven
bibkeys all satisfy it. The `evidence_on_close` field should point
at `SK_EFT_Hawking/docs/phase6i_wave1_close.md`.

**Adjacent QI surfaced: `qi-provenance-citation-coverage`.** Finding
1.1 of this re-review notes that primary-experimental sources (Kapner,
Weisberg-Huang, Bertotti-Iess-Tortora) referenced by `provenance.py`
DOI fields are not themselves in `CITATION_REGISTRY`. This is a new
pattern class — the citation infrastructure covers what papers cite
in `\bibitem`s but not what `provenance.py` cites in `source` /
`detail` / `doi` fields. A `validate.py --check provenance_doi_in_registry`
extension would close this loop. Phase 6i Wave 2 (parameter-provenance
closure) is the natural owner.
