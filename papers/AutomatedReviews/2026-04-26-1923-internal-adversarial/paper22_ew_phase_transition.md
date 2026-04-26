---
paper: paper22_ew_phase_transition
reviewer: adversarial-reviewer
model: claude-opus-4-7[1m]
review_date: 2026-04-26T19:23:00Z
readiness_gates_version: 1
---

# Adversarial Review — paper22_ew_phase_transition

## Summary

Paper 22 ("EW Phase Transition Order from a Microscopic Scalar Rung")
ships 19 Lean theorems but the headline narrative materially overclaims
what those theorems establish. **Aggregate verdict: RED.** 4 BLOCKERs,
4 REQUIRED, 2 RECOMMENDED. The two load-bearing failures are (i) the
"master correctness-push theorem"
`transition_order_from_microscopic_parameters` is `rfl ∧ rfl` on a
definitional unfolding (Gate 5 LeanProofSubstance), and (ii) the
abstract / intro frame "the SM is unambiguously a crossover" while the
Lean module formalizes the *opposite verdict*
(`sm_benchmark_is_first_order`) at LO and provides no Lean artifact for
the loop-corrected crossover claim (Gate 7 NarrativeGrounding). Plus
the m_H ≈ 72 GeV crossover threshold is misattributed to KLRS96 (the
KLRS96 paper actually says 70–95 GeV / ≈ 80 GeV; 72 GeV is the
Csikor-Fodor-Heitger 1999 refinement, which the Lean module's own
header comments correctly attribute). counts.tex is stale (papercount
= 21, has not yet absorbed paper 22 / its 19 new theorems).

## Findings

### 1.1 — 🔴 BLOCKER — KLRS96 misattributed for m_H ≈ 72 GeV crossover threshold

- **Gate:** CitationIntegrity
- **Location:** `papers/paper22_ew_phase_transition/paper_draft.tex:42–43, 168–172, 184–187`
- **Observed:** Paper repeatedly attributes "m_H ≈ 72 GeV crossover threshold" to `\cite{KLRS1996}` (e.g. abstract: "falls below the Kajantie-Laine-Rummukainen-Shaposhnikov 1996 lattice crossover threshold m_H ≈ 72 GeV").
- **Evidence:** Fresh fetch of arXiv hep-ph/9605288 abstract returns the verbatim quote: "In the minimal standard electroweak theory 70 GeV $< m_{H,c} <$ 95 GeV and most likely $m_{H,c} \approx 80$ GeV." The 72 GeV value is **not** in KLRS96; it is the Csikor-Fodor-Heitger 1999 refinement (PRL 82, 21). The Lean module header at `lean/SKEFTHawking/EWPhaseTransition.lean:43–44` correctly cites: "Csikor-Fodor-Heitger, PRL 82, 21 (1999): m_H = 72.4 ± 1.7 GeV (lattice, refined)" — so the project already has the right reference, the paper just cites the wrong one.
- **Expected:** Either cite Csikor-Fodor-Heitger 1999 for the 72 GeV figure, or use KLRS96's actual range (70–95 GeV, central ≈ 80 GeV). Both is best.
- **Fix:** Add `CsikorFodorHeitger1999` bibitem (PRL 82, 21 (1999); arXiv:hep-ph/9809291); cite it for 72 GeV; keep KLRS96 for the qualitative crossover-threshold result. Add the new bibkey to `CITATION_REGISTRY` with `doi_verified: None` pending a fresh CrossRef sweep.
- **Cache:** fresh-fetch (arxiv.org/abs/hep-ph/9605288 returned KLRS96 numerical range)

### 1.2 — 🟡 REQUIRED — Three new bibkeys carry `doi_verified: None`

- **Gate:** CitationIntegrity
- **Location:** `src/core/citations.py:1552, 1571, 1589`
- **Observed:** `KLRS1996`, `ButtazzoEtAl2013`, `ShaposhnikovWetterich2010` all flagged `doi_verified: None`.
- **Evidence:** Fresh arXiv fetches confirm titles + author lists + journal/volume/page match registry for all three. arXiv-side is `match`; only `doi_verified` flag is unset.
- **Expected:** Run CrossRef live-resolution sweep on the three DOIs (`10.1103/PhysRevLett.77.2887`, `10.1007/JHEP12(2013)089`, `10.1016/j.physletb.2009.12.022`) and flip `doi_verified: None → True` if titles match.
- **Fix:** `uv run python scripts/citation_cache.py --resolve KLRS1996 ButtazzoEtAl2013 ShaposhnikovWetterich2010` (or equivalent CrossRef batch). Submission gate requires `doi_verified == True`.
- **Cache:** fresh-fetch (arXiv side); DOI side **un-fetched** — flag stands.

### 3.1 — 🔴 BLOCKER — `transition_order_from_microscopic_parameters` is structurally tautological

- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/EWPhaseTransition.lean:259–264`
- **Observed:** Theorem statement is `(IsFirstOrderEW p ↔ 0 < p.cubic_coeff) ∧ (IsCrossoverEW p ↔ p.cubic_coeff = 0)` and the proof body is literally `refine ⟨?_, ?_⟩; · unfold IsFirstOrderEW; rfl; · unfold IsCrossoverEW; rfl`. The definitions are `IsFirstOrderEW p := 0 < p.cubic_coeff` and `IsCrossoverEW p := p.cubic_coeff = 0` (lines 147, 152) — the theorem is `def-unfold ↔ def-body`, i.e. the conclusion is *definitionally* the hypothesis with the abbreviation expanded. No mathematical content.
- **Evidence:** Both branches close by `rfl` after `unfold`; this is the canonical PlaceholderMarker pattern (`rfl` on a non-trivial-looking statement that is in fact definitional). The paper at `paper_draft.tex:126–129` calls this "the master correctness-push theorem … reduces the predicate to the explicit cubic-coefficient inequality, providing the biconditional reduction from microscopic data to phase order." The reduction is purely a definitional unfold; there is no microscopic-to-macroscopic content.
- **Expected:** Either (i) downgrade the prose claim to "definitional unfolding lemma" and remove the "master correctness-push" framing, or (ii) replace the trivial statement with a substantive one — e.g., a theorem connecting the cubic coefficient to a physical observable (barrier height, latent-heat-positivity-iff-firstorder) that requires real proof work. The actual non-trivial connection between `cubic_coeff > 0` and "barrier survives" is *not* formalized in this module.
- **Fix:** Strengthen to `theorem first_order_iff_barrier_at_T_c (p : EWFiniteTParams) (hT : 0 < criticalTemperature p) : IsFirstOrderEW p ↔ ∃ φ > 0, finiteTPotential p φ (criticalTemperature p) > finiteTPotential p 0 (criticalTemperature p)` — this would actually require non-trivial calculus (existence of a saddle / barrier extremum) rather than an unfold.

### 3.2 — 🟡 REQUIRED — `ew_latent_heat` docstring cites nonexistent Lean theorem

- **Gate:** LeanProofSubstance
- **Location:** `src/core/formulas.py:7013`
- **Observed:** `Lean: EWPhaseTransition.latentHeat_nonneg, latentHeat_zero_iff_crossover` — but `latentHeat_zero_iff_crossover` does not exist in `lean/SKEFTHawking/EWPhaseTransition.lean`. The module ships `crossover_has_zero_latent_heat` (one direction only); the iff is unproven.
- **Evidence:** `grep -n "latentHeat_zero_iff_crossover" lean/SKEFTHawking/EWPhaseTransition.lean` returns zero matches.
- **Expected:** Either add the iff theorem (the converse — `latentHeat p = 0 → IsCrossoverEW p` — is the non-trivial direction; needs `T_c > 0` and `λ > 0`, then `E^2 = 0 → E = 0`), or fix the docstring to cite only `crossover_has_zero_latent_heat`.
- **Fix:** Add `theorem latentHeat_zero_iff_crossover (p : EWFiniteTParams) : latentHeat p = 0 ↔ IsCrossoverEW p` proved via `pow_eq_zero_iff` on `cubic_coeff^2`, OR update the formulas.py docstring.

### 3.3 — 🔵 RECOMMENDED — `wave3_open_manifest_consistent` arm trivialised by `cubic_coeff_nonneg`

- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/EWPhaseTransition.lean:340–344` and structure constraint at line 81
- **Observed:** `Wave3OpenManifest` includes `(IsFirstOrderEW p ∨ IsCrossoverEW p) := (0 < p.cubic_coeff) ∨ (p.cubic_coeff = 0)`. Because `EWFiniteTParams` carries the structure-field constraint `cubic_coeff_nonneg : 0 ≤ cubic_coeff`, this disjunction is **automatically satisfied** for *any* inhabitant of `EWFiniteTParams` — the manifest's third arm is always-true by construction.
- **Evidence:** Compare to a similar manifest pattern in `MajoranaRung.lean` / `Wave2OpenManifest`. Here the open-manifest "consistency" theorem is mostly a vacuous combination, since the only non-trivial arms are `H_VacuumStableUnderRG smBenchmarkParams 0.05` (one inequality) and `H_HierarchyEWLambdaUV (10^16) 246` (one inequality).
- **Expected:** Either tighten the third arm to a non-trivial predicate (e.g. require `IsBaryogenesisViable p threshold` for the first-order case) or document that the third arm is structurally satisfied.
- **Fix:** Add a comment line in the Lean explaining why the disjunction is vacuous-by-structure, or replace with a stronger predicate.

### 4.1 — 🔵 RECOMMENDED — Cross-paper bibkey consistency check

- **Gate:** CrossPaperConsistency
- **Location:** `papers/paper22_*/paper_draft.tex` vs other papers
- **Observed:** None of the three new bibkeys (`KLRS1996`, `ButtazzoEtAl2013`, `ShaposhnikovWetterich2010`) appear in any other `papers/paper*_*/paper_draft.tex`. Cross-paper consistency is vacuously satisfied for these. Shared bibkeys (`BardeenHillLindner`, `Hill2025Redux`, `PDG2024`) point at the same arXiv IDs / DOIs in the registry — no cross-paper drift detected.
- **Evidence:** `grep -l "KLRS1996" papers/*/paper_draft.tex` returns only paper22.
- **Expected:** Pass. Re-run cross-paper consistency once paper 22 is graph-extracted.
- **Fix:** No action required.

### 6.1 — 🟡 REQUIRED — `cubic_coeff_nonneg` structure constraint not disclosed in paper

- **Gate:** AssumptionDisclosure
- **Location:** `lean/SKEFTHawking/EWPhaseTransition.lean:81` vs `paper_draft.tex` Section 2 / Section 3
- **Observed:** `EWFiniteTParams` carries the load-bearing constraint `cubic_coeff_nonneg : 0 ≤ cubic_coeff`. This is **why** the partition `IsFirstOrderEW := (E > 0)` ∨ `IsCrossoverEW := (E = 0)` is exhaustive — without `cubic_coeff_nonneg`, negative-E configurations would be unclassified. The paper does not mention this hypothesis anywhere; the partition is presented as if it were complete on the full parameter space.
- **Evidence:** `grep -n "cubic_coeff_nonneg\|nonnegative.*cubic\|E.*0.*≤" papers/paper22_ew_phase_transition/paper_draft.tex` returns zero matches.
- **Expected:** Add a sentence in §2 (Finite-T Effective Potential) noting that the analysis assumes E ≥ 0 (physically motivated by hard-thermal-loop gauge-boson contributions; E < 0 would require new physics).
- **Fix:** One sentence in the paragraph at line 105–117, e.g. "We restrict to the physically relevant regime E ≥ 0 (encoded as `cubic_coeff_nonneg` in the Lean structure); negative-cubic configurations would require BSM hard-thermal-loop contributions and are excluded here."

### 7.1 — 🔴 BLOCKER — Abstract/intro contradicts shipped Lean theorem on SM verdict

- **Gate:** NarrativeGrounding
- **Location:** `paper_draft.tex:38–43` (abstract), `66–70` (intro), `163–187` (Section 3) vs `lean/SKEFTHawking/EWPhaseTransition.lean:201–203`
- **Observed:** Abstract claims SM "falls below the … crossover threshold m_H ≈ 72 GeV" → "confirming the SM is a crossover at LO." But the Lean theorem `sm_benchmark_is_first_order : IsFirstOrderEW smBenchmarkParams` proves the **opposite** (first-order at LO with E_SM = 0.01 > 0). The paper acknowledges this contradiction in §3 ("the theorem `sm_benchmark_is_first_order` certifies that *at the strict-LO* thermal expansion, E_SM > 0 yields a first-order transition. **However** … the actual SM is a crossover") — but the abstract still tells the reader the opposite. The "SM-as-crossover" verdict that the paper headlines is **not** formalized in any Lean theorem; it rests entirely on KLRS96 (cited externally), with the Lean module's actual SM-benchmark theorem proving the reverse.
- **Evidence:** `sm_benchmark_is_first_order` is at line 201, body `unfold IsFirstOrderEW smBenchmarkParams; norm_num` (provable since 0.01 > 0). The abstract conclusion "the SM is a crossover at LO" is contradicted by this theorem at LO.
- **Expected:** Either (i) reframe the abstract: "the SM benchmark is first-order at strict-LO with E_SM > 0; the actual SM-as-crossover verdict at the physical Higgs mass requires the lattice / two-loop corrections of KLRS96 + Csikor-Fodor-Heitger 1999, which are *outside the scope of this Lean module*", or (ii) ship a Lean theorem `sm_loop_corrected_is_crossover` that actually formalizes the loop-corrected verdict (would require ingesting two-loop thermal corrections — explicitly OUT OF SCOPE per Lean header lines 53–55).
- **Fix:** Rewrite the abstract sentence "confirming the SM is a crossover at LO" → "the formalized strict-LO benchmark predicts first-order; the SM-as-crossover verdict at physical m_H is established externally by KLRS96 lattice and Csikor-Fodor-Heitger 1999 refinement, with two-loop thermal corrections deferred to future Phase 6b work." Update intro and §3 accordingly; ensure no place in the paper claims the Lean-shipped artifacts establish the crossover verdict.

### 7.2 — 🟡 REQUIRED — "load-bearing input to … Phase 6c.2" is forward-reference, not formal artifact

- **Gate:** NarrativeGrounding
- **Location:** `paper_draft.tex:46–48, 218–224, 318–323`
- **Observed:** Repeated phrasing "the load-bearing input to the future Phase 6c.2 EW-baryogenesis bridge theorem" — but no formal Phase 6c.2 artifact exists, no `Phase6c2*.lean` module is referenced in the bibliography or the project. This is interpretive forward-reference framing; the load-bearing-ness is asserted, not proven.
- **Evidence:** `find lean -name "Phase6c*"` returns no files.
- **Expected:** Tag the forward-reference as projection / outlook explicitly, OR remove the "load-bearing" framing in favor of "is intended to feed".
- **Fix:** Replace "is the load-bearing input to" with "is intended to feed the future Phase 6c.2" everywhere (lines 46, 219, 318).

### 9.1 — 🔴 BLOCKER — counts.tex stale: paper 22 not yet ingested

- **Gate:** NumericalFreshness
- **Location:** `docs/counts.tex` and `paper_draft.tex:97` (uses `\substantivetheorems{}` macro)
- **Observed:** `docs/counts.tex` reports `\papercount{21}`, `\totaltheorems{4115}`, `\substantivetheorems{4004}`, `\leanmodules{172}` — but paper 22 is the 22nd paper, ships 19 new theorems and adds `EWPhaseTransition.lean` as a new module. The counts macros the paper *itself* uses (`\substantivetheorems`) are pulled from a stale counts.tex generated 2026-04-25 14:24 UTC — *before* paper 22 / EWPhaseTransition.lean were added.
- **Evidence:** `docs/counts.tex:3` and the user prompt's stated current totals (4049 substantive, 170 modules) — neither matches the file. Note: the prompt claims 4049 substantive and 170 modules; counts.tex claims 4004 substantive and 172 modules. There is also internal disagreement between the prompt and the file. Either way, paper 22's 19 new theorems + 1 new module are NOT reflected.
- **Expected:** Re-run `uv run python scripts/update_counts.py` after paper 22 ingestion; verify totals match the project's actual Lean state.
- **Fix:** `uv run python scripts/update_counts.py && uv run python scripts/validate.py --check counts_fresh`.

### 9.2 — 🔵 RECOMMENDED — T_c rounding inconsistency: 139.13 vs 139.15

- **Gate:** NumericalFreshness
- **Location:** `paper_draft.tex:114, 158` ("T_c ≈ 139.13") vs canonical `T_c = 88 / sqrt(0.4) = 88 / 0.632456 = 139.1535`
- **Observed:** Paper reports T_c ≈ 139.13 GeV; canonical pipeline value is 139.1535 (the test at `tests/test_ew_phase_transition.py:88` uses `pytest.approx(139.13, abs=0.5)` — passes by tolerance, not equality).
- **Evidence:** 88 / 0.6324555 = 139.1535. Paper's 139.13 is rounded to 4 sig figs but inconsistently — should be 139.15 to match the formula's actual output.
- **Expected:** Round consistently. 139.15 is the correct 5-sig-fig value.
- **Fix:** s/139.13/139.15/g in paper, or generate via `\input{tables/<id>.tex}` per Phase 5v Wave 10 freshness pipeline.

## QI Candidate

- Pattern: definitional-unfold theorems framed as "master correctness-push" / "biconditional reduction" in paper prose. Same anti-pattern caught in Wave 2a (`H_PMNSAnglesFromSubstrate`) and Wave 5y per memory. Recommend a syntactic check: any theorem whose proof body is `unfold X; rfl` or `unfold X Y; rfl` whose statement type is an iff or conjunction of iffs against the unfolded definition is structurally tautological. Add to `scripts/lean_substance_check.py` as a lint pass.
- Pattern: paper prose makes a verdict claim ("SM is a crossover") that the shipped Lean theorem contradicts ("sm_benchmark_is_first_order"). Recommend: build a verdict-direction-check that pairs each `\texttt{theorem_name}` cite in prose with a direction tag {asserts, contradicts, neutral} and flags contradictions.
