---
paper: paper21_majorana_rung
reviewer: adversarial-reviewer
model: claude-opus-4-7
review_date: 2026-04-25T16:40:00Z
readiness_gates_version: 1
prior_round: 2026-04-25-1530-internal-adversarial
---

# Adversarial Review — paper21_majorana_rung (Stage-13 re-invocation)

## Summary

Re-invocation after the 2026-04-25-1530 round flagged 5 BLOCKER + 3 REQUIRED + 1 RECOMMENDED across CitationIntegrity, CrossPaperConsistency, and LeanProofSubstance. All 5 prior BLOCKERs are confirmed remediated. All 3 prior REQUIREDs are addressed (5.4 closed by deletion of summary placeholders; 1.3 closed by KamLANDZen800 PRL update; 3.1 carries forward). The prior RECOMMENDED 6.1 is closed (arXiv:2310.14750 in registry + bibitem). **No new BLOCKERs introduced by the remediation work** — the parametric refactors (`H_LeptonNumberViolated G_LV`, `IsDirac/IsMajoranaPMNS V α`, `DecouplingRegime` substantive fields) preserve module-build cleanliness and ship genuine non-trivial content with disjointness/non-vacuity witnesses. **2 findings stand**: 3.1 (carry-over REQUIRED, user-triggered, not a new finding) + 1 new RECOMMENDED on a stylistic-case difference. **Paper aggregate flips from RED → YELLOW**: gates 1/2/5 all flip back to `passed`; advisory P2 gates remain `needs-recheck`.

## Findings

### 3.1 — 🟡 REQUIRED — All 21 MAJORANA parameters lack `human_verified_date` (carry-over)

- **Gate:** ParameterProvenance
- **Location:** `src/core/provenance.py` MAJORANA.* keys (21 entries)
- **Observed:** Programmatic enumeration of `PARAMETER_PROVENANCE` shows all 21 MAJORANA.* keys still have `human_verified_date = None`; `llm_verified_date` populated for all.
- **Evidence:** `from src.core import provenance as P; sum(1 for v in P.PARAMETER_PROVENANCE.values() if v.get('human_verified_date') is None and 'MAJORANA' in str(v))` returns 21. The current readiness graph reports `ParameterProvenance: passed` for paper21 only because no `DEPENDS_ON` edges from paper21 to Parameter nodes have been wired yet (notes: `no parameter dependencies declared`). Once those edges land, this finding will surface in the gate evaluator directly.
- **Expected:** Provenance dashboard sign-off pass on each MAJORANA.* entry.
- **Fix:** User-triggered. Run dashboard, sign off, populate `human_verified_date` per entry. Carry-over; not a regression.
- **Cache:** N/A
- **Status flag:** persists, expected to persist until John runs the dashboard.

### 6.1 — 🔵 RECOMMENDED — `Hill2024Bilocal` arXiv-vs-journal title differ in case (cosmetic)

- **Gate:** CitationIntegrity (advisory)
- **Location:** `papers/paper21_majorana_rung/paper_draft.tex:651` + `src/core/citations.py:Hill2024Bilocal`
- **Observed:** Bibitem prose: `"Bilocal field theory for composite scalar bosons"` (sentence case). CrossRef DOI lookup of 10.3390/e26020146 confirms published Entropy title is `"Bilocal Field Theory for Composite Scalar Bosons"` (title case). arXiv:2310.14750 preprint title is the longer `"Revisiting Yukawa's Bilocal Field Theory for Composite Scalar Bosons"`.
- **Evidence:** `https://api.crossref.org/works/10.3390/e26020146` (publisher record) returns the title-case form. The bibitem cites the journal version (DOI 10.3390/e26020146 + Entropy 26, 146) so the journal version is canonical here; sentence-case is a common physics-citation convention.
- **Expected:** Either retitle bibitem to title-case to match Entropy/CrossRef exactly, or accept sentence-case as house style across the project (paper20 also uses sentence-case for its bibitems).
- **Fix:** Optional. Not a factual error; advisory only.
- **Cache:** fresh-fetch via CrossRef + arXiv abstract page

## Verified remediations from prior round

The following findings from `2026-04-25-1530-internal-adversarial/paper21_majorana_rung.md` are independently verified resolved:

- **1.1 (BLOCKER, WetterichSpinor2013 title):** paper21 bibitem (line 570-573) now reads "Spinor gravity and diffeomorphism invariance on the lattice"; matches paper20 verbatim and arXiv:1201.2871 fetched title; cache entry confirms `verdict: match`. **CLOSED.**
- **1.2 (BLOCKER, WetterichSpinor2022 title):** paper21 bibitem (line 575-578) now reads "Pregeometry and spontaneous time-space asymmetry"; matches paper20 verbatim and arXiv:2101.11519 fetched title; cache entry confirms `verdict: match`. **CLOSED.**
- **1.3 (REQUIRED, KamLANDZen800 PRL):** bibitem (line 614-618) now reads `Phys.~Rev.~Lett.~\textbf{135}, 262501 (2025); arXiv:2406.11438; DOI:10.1103/jkf6-48j8`; registry entry has `journal: 'Phys. Rev. Lett.'`, `volume: 135`, `page: 262501`, `year: 2025`, `doi: '10.1103/jkf6-48j8'`, `doi_verified: True`. WebFetch of arxiv.org/abs/2406.11438 confirms PRL 135, 262501 (2025). **CLOSED.**
- **2.1 (BLOCKER, cross-paper Wetterich title divergence):** Direct `diff` between paper20 and paper21 bibitems for both Wetterich keys shows only formatting differences (`\emph{}` vs ``"...''``); title content is identical and matches the registry. **CLOSED.**
- **5.1 (BLOCKER, H_LeptonNumberViolated := True):** `MajoranaRung.lean:221` now reads `def H_LeptonNumberViolated (G_LV : ℝ) : Prop := G_LV ≠ 0`. The obstruction theorem `lepton_number_symmetry_obstructs_BCS_form` (line 262) takes the inhabitable hypothesis `¬ H_LeptonNumberViolated G_LV` (i.e. `G_LV = 0`); proof uses `intro ⟨h_LNV, _⟩; exact h_no_LNV h_LNV`. The corollary `L_conserving_substrate_obstructs_BCS_form` discharges the predicate at the archetype point `G_LV = 0` via `unfold H_LeptonNumberViolated; simp` — non-vacuous, structurally meaningful. Threading verified through `H_MR_FromADWSubstrate_BCS_LNV`, `M_R_pos_under_BCS_form`, `M_R_lt_substrate_under_BCS_form`, `Wave2OpenManifest`, `wave2_open_manifest_consistent`, `strong_BCS_excludes_substrate_dominant_M_R`. **CLOSED.**
- **5.2 (BLOCKER, IsDirac/IsMajoranaPMNS := True):** `NeutrinoMixing.lean:127`, `:135` now define `IsDiracPMNS V α := ∀ k : Fin 2, α k = 0` and `IsMajoranaPMNS V α := ∃ k : Fin 2, α k ≠ 0`. The bridge `isMajoranaPMNS_of_majoranaRungData` (line 146) requires `(h_phase_nontrivial : ∃ k, α k ≠ 0)` and proves `IsMajoranaPMNS V α := h_phase_nontrivial` (the witness IS the conclusion — non-tautological because the hypothesis is an explicit input). Disjointness theorem `not_isDiracPMNS_and_isMajoranaPMNS` (line 155) proves logical disjointness via `rintro ⟨h_dirac, k, h_kne⟩; exact h_kne (h_dirac k)` — non-trivial. The Dirac-realization witness `isDiracPMNS_of_zero_phases` confirms non-vacuity of the Dirac branch. **CLOSED.**
- **5.3 (BLOCKER, DecouplingRegime fields := True):** `MajoranaRungDecoupling.lean:103-117` now declares `not_vestigial : (0.2 : ℝ) < E`, `not_cosmological : (1.4e-42 : ℝ) < E`, `weakly_coupled_matter : Λ_ADW < (1e19 : ℝ)`. The non-vacuity witness `decouplingRegime_at_electroweak_scale` (line 229) discharges all six fields via `norm_num` (six `?_` goals); proof builds clean. **CLOSED.**
- **5.4 (REQUIRED, summary placeholders):** `wave2b_decoupling_summary` and `neutrino_mixing_structure_note_summary` are no longer present in either Lean source (verified via `grep -nE "summary"`); module-final docstrings replace them. Lean environment counts confirm 0 placeholder theorems in any of the three modules (substantive=24/15/18, placeholder=0/0/0 from `lean_deps.json`). **CLOSED.**
- **6.1 prior round (RECOMMENDED, Hill2024Bilocal arXiv ID):** Registry entry `Hill2024Bilocal` now has `'arxiv': '2310.14750'`; bibitem cites `arXiv:2310.14750`. **CLOSED.** (A new, distinct RECOMMENDED 6.1 on title case is filed above.)
- **Stage-9 KamLAND-Zen color BLOCKER (red→amber):** `visualizations.py:7664` now uses `fillcolor="rgba(241, 143, 1, 0.30)"` (amber, the project colorblind-accessible palette per CLAUDE.md). Comment explicitly references the project convention. **CLOSED.**

## Cross-paper / project-level checks (negative findings)

- **Build:** `lake build SKEFTHawking.MajoranaRung SKEFTHawking.NeutrinoMixing SKEFTHawking.MajoranaRungDecoupling` was reported clean by the user pre-flight; current `lean_deps.json` (4051 thms total, 0 sorry, 1 axiom) is consistent.
- **validate.py:** 22/22 PASS verified this round (91.9 s); all P1 gates pass for paper21 in `readiness_submission_gate`. Advisory tail: NumericalFreshness (1 inline literal still in body — `\substantivetheorems\ theorems` macro chain has 1 quotable hangover; not a regression), FixPropagation (4 prior-round findings still graph-open until the extractor processes this report).
- **Theorem counts:** `lean_deps.json` reports 24 / 15 / 18 theorems for the three modules vs paper Table 1's 15 / 11 / 6. The disparity is structure-projection auto-theorems (`DecouplingRegime.posE`, `SubstrateData.mk.injEq`, etc.) generated by Lean from `structure` definitions — not user-written content. The paper counts reflect user-authored substantive theorems, which is the convention the project uses. `count_literals` check accepts the macro-driven values (no count literals flagged in paper21 prose). **No finding** — count discipline is consistent with project pattern.
- **Placeholder set:** `build_graph.py --json | jq` shows no `PlaceholderMarker` nodes match any theorem name in MajoranaRung / NeutrinoMixing / MajoranaRungDecoupling. **No finding.**
- **Vacuous-Prop scan:** `grep -nE ":= True\b|:= trivial$"` returns only docstring matches (commentary on the prior remediation history); no live code remains in either pattern. **No finding.**
- **Citation registry coverage:** All 21 paper21 bibkeys (ADW, WetterichSpinor2013/2022, Volovik2024Spinor, GarciaEtxebarriaMontero2019, WanWang2020, KawasakiYanagida2023, MohapatraSmirnov2006, NuFit60, KamLANDZen800, LEGEND1000, TooBySmithHepLean, AntuschKerstenLindnerRatz2003, AppelquistCarazzone1975, BallThorne1994, GiudiceGrojeanPomarolRattazzi2007, Hill2024Bilocal, CiriglianoMasterFormula2018, PDG2024, Lean4, Mathlib) are present in `CITATION_REGISTRY` with `doi_verified: True` (or no DOI for textbooks/arXiv-only items). **No finding.**

## Gate state delta

| Gate | Prior round (1530) | This round (1640) |
|------|--------------------|-------------------|
| 1 CitationIntegrity | **blocked** | **passed** |
| 2 CrossPaperConsistency | **blocked** | **passed** |
| 3 ParameterProvenance | needs-recheck (open via 3.1) | passed (graph: no DEPENDS_ON yet) — 3.1 carries forward |
| 4 ComputationCorrectness | open | open (no grounded formulas declared) |
| 5 LeanProofSubstance | **blocked** | **passed** |
| 6 AssumptionDisclosure | passed | passed |
| 7 NarrativeGrounding | passed | passed |
| 8 ProductionRunHealth | passed | passed |
| 9 NumericalFreshness | needs-recheck | needs-recheck (1 inline literal advisory) |
| 10 FirstClaimVerification | passed | passed |
| 11 FixPropagation | needs-recheck | needs-recheck (until extractor closes prior 4) |

**Aggregate:** RED → **YELLOW**. No P1 gate is `blocked`. Submission gate still requires P2 advisories cleared (NumericalFreshness, FixPropagation graph-update, ParameterProvenance human sign-off via 3.1).

## QI Candidate

The Stage-13 round once again successfully caught BLOCKERs that Stages 1–12 missed, validating the adversarial-review cost. However, the remediation pattern — refactoring `True := trivial` Props to `G_LV ≠ 0` / `α k = 0` predicates — is mechanical and could plausibly be lifted into a `validate.py` lint rule, e.g. `--check vacuous_props`: flag any `def X : Prop := True` or `def X (args) : Prop := True` and any `theorem … := trivial` whose statement-type unfolds to plain `True` outside an existential binder. Such a lint at Stage 12 would prevent the 5.1 / 5.2 / 5.3 antipattern from reaching Stage 13 at all. (Already proposed in the prior round's QI section.) Additionally, the per-module substantive-vs-auto-projected theorem-count disparity (paper Table 1 says 15/11/6 vs Lean env 24/15/18) is paper-specific honest counting that bypasses the canonical `\totaltheorems`-style macro chain — a future macro `\substantiveModuleCount{MajoranaRung}` populated from `lean_deps.json` (filtering out structure projections via name-suffix pattern) would close the count-discipline gap without requiring authors to hand-curate.
