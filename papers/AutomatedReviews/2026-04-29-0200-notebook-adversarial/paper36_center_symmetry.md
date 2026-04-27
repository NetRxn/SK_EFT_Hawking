---
paper: paper36_center_symmetry
artifacts:
  - notebooks/Phase6d1_CenterSymmetry_Technical.ipynb
  - notebooks/Phase6d1_CenterSymmetry_Stakeholder.ipynb
  - papers/paper36_center_symmetry/paper_draft.tex
  - lean/SKEFTHawking/CenterSymmetryConfinement.lean
  - src/center_symmetry/{__init__,polyakov_loop,svetitsky_yaffe,eta_over_s_prediction}.py
reviewer: adversarial-reviewer (notebook-adapted, fresh context)
model: claude-opus-4-7[1m]
review_date: 2026-04-29T02:00:00Z
readiness_gates_version: 1
---

# Adversarial Review — paper36_center_symmetry (notebooks + paper)

## Summary

Two BLOCKER citation defects (KosPolandSimmonsDuffin2016 and HofmanIqbal2018 carry wrong titles, and KPSD additionally has wrong author count and an apparently wrong JHEP volume/page that points at an unrelated black-hole-thermodynamics paper). One BLOCKER attribution defect ("Walker-Wang anyon-mediated transport" is named throughout the title, abstract, body, figure caption, and notebooks but no Walker-Wang reference is in the bibliography; the only citation backing it (Hofman-Iqbal 2018) is verified by WebFetch to NOT discuss Walker-Wang, anyons, or the [KSS, 2·KSS] bracket). One REQUIRED quantitative-drift finding (β_Potts = 0.111 used in the figure is the 2D Potts critical exponent — the 3D 3-state Potts transition is weakly first-order and has no β; using the 2D value silently for a "3-state Potts" curve in the figure is misleading). Several REQUIRED and RECOMMENDED secondary findings on cross-bridge substantive depth, narrative overclaims, and registry drift. Both notebooks inherit the bibliographic / attribution defects via citation cells. Paper is **NOT submission-ready** until the citation block is rewritten.

## Findings

### 1.1 — 🔴 BLOCKER — KosPolandSimmonsDuffin2016 carries wrong title, wrong author count, and wrong JHEP venue under arXiv ID 1603.04436

- **Gate:** CitationIntegrity
- **Location:** `papers/paper36_center_symmetry/paper_draft.tex:316–319`; `src/core/citations.py:3234–3249`; both notebooks cell 5 (technical) / cell 5 (stakeholder) reference KPSD 2016 in prose.
- **Observed (bibitem):**
  ```
  \bibitem{KosPolandSimmonsDuffin2016}
  F.~Kos, D.~Poland, and D.~Simmons-Duffin,
  ``Bootstrapping the O(N) archipelago,''
  JHEP \textbf{03}, 086 (2016); arXiv:1603.04436.
  ```
- **Evidence (fresh fetch):**
  - WebFetch arXiv:1603.04436 → title "**Precision Islands in the Ising and O(N) Models**", authors "**Kos, Poland, Simmons-Duffin, Vichi**" (4 authors, not 3), JHEP **08, 036** (2016).
  - WebFetch InspireHEP for j="JHEP,1603,086" → JHEP 03 (2016) 086 = "Black hole thermodynamics from a variational principle: Asymptotically conical backgrounds" by An, Cvetič, Papadimitriou, arXiv:1602.01508 (an entirely unrelated paper).
  - The "Bootstrapping the O(N) Archipelago" paper is arXiv:1504.07997, JHEP 11 (2015) 106 by Kos, Poland, Simmons-Duffin, Vichi.
- **Expected:** If the intended source is the precision-island ν_Ising = 0.62997(1), the bibitem should read:
  ```
  F.~Kos, D.~Poland, D.~Simmons-Duffin, and A.~Vichi,
  ``Precision Islands in the Ising and O(N) Models,''
  JHEP \textbf{08}, 036 (2016); arXiv:1603.04436.
  ```
  If the intended source is the archipelago paper, the arXiv ID must change to 1504.07997 and the venue to JHEP 11 (2015) 106.
- **Fix:** Correct title, add author Vichi, fix venue from `\textbf{03}, 086` → `\textbf{08}, 036`. Update `src/core/citations.py:3234–3249` to match. Re-run `validate.py --check citation_live_resolution`. Both notebooks (Technical cell 5, Stakeholder cell 5) reference "Kos-Poland-Simmons-Duffin 2016 conformal bootstrap" — also update notebook prose to four-author form or stop attributing the precision value to a paper that includes Vichi.
- **Cache:** fresh-fetch (arxiv:1603.04436 + InspireHEP + DOI redirect chain).

### 1.2 — 🔴 BLOCKER — HofmanIqbal2018 carries wrong title

- **Gate:** CitationIntegrity
- **Location:** `papers/paper36_center_symmetry/paper_draft.tex:306–309`; `src/core/citations.py:3266–3281`.
- **Observed (bibitem):**
  ```
  D.~M.~Hofman and N.~Iqbal,
  ``Goldstone modes and photonization for higher form symmetries,''
  SciPost Phys.\ \textbf{4}, 005 (2018); arXiv:1707.08577.
  ```
- **Evidence (fresh fetch):** WebFetch arXiv:1707.08577 → actual title is "**Generalized global symmetries and holography**", SciPost Phys. 4, 005 (2018), Hofman & Iqbal. The "Goldstone modes and photonization" phrasing does not match the arXiv listing. "Goldstone bosons and photonization for higher form symmetries" / similar phrasings appear in a later companion preprint by Hofman & Iqbal (arXiv:1802.09512); the registry / bibitem is conflating the two.
- **Expected:**
  ```
  D.~M.~Hofman and N.~Iqbal,
  ``Generalized global symmetries and holography,''
  SciPost Phys.\ \textbf{4}, 005 (2018); arXiv:1707.08577.
  ```
- **Fix:** Correct title in bibitem and `src/core/citations.py:3268`. If the intent was to cite the Goldstone/photonization companion paper, the arXiv ID and DOI also need to change.
- **Cache:** fresh-fetch.

### 1.3 — 🔴 BLOCKER — "Walker-Wang anyon-mediated transport" attributed throughout the paper and notebooks with no Walker-Wang reference in bibliography; the only backing citation (HofmanIqbal2018) does not discuss Walker-Wang, anyons, or the [KSS, 2·KSS] bracket

- **Gate:** CitationIntegrity (and NarrativeGrounding — attribution-claim)
- **Location:** Paper title line 20 ("…with a Walker--Wang transport bracket"); abstract line 45 ("A Walker--Wang anyon-mediated transport prediction is encoded…"); §4 line 204 ("The Walker--Wang anyon-mediated transport prediction is encoded…with…non-Abelian anyon-mediated transport stays within a factor of two of the universal lower bound~\cite{HofmanIqbal2018}"); figure caption line 240 ("Walker--Wang transport bracket"); 11 total textual mentions vs zero bibitem entries. Stakeholder notebook cell 0 ("higher-form-symmetry topological-defect transport correction — building on Hofman-Iqbal 2018 generalized hydrodynamics") *partially* honest at one location, but cell 7 then says "the paper proposes a **Walker-Wang topological-defect transport correction**" with no Walker-Wang citation. Technical notebook §5 (cell 9) and §7 (cell 14) name the prediction "Walker-Wang transport correctness-push" without any backing reference.
- **Evidence (fresh fetch):** WebFetch arXiv:1707.08577 abstract — "We argue that any global symmetry whose conserved charge can be written as the integral of a closed (D-1)-form … is a higher-form global symmetry … hydrodynamic behavior at finite temperature … magnetohydrodynamics." No mention of Walker-Wang, anyons, or transport-coefficient brackets. Confirmed by direct content scan: "the paper does **not** appear to concern Walker-Wang models or anyon-mediated transport". The original Walker-Wang construction (Walker & Wang, "(3+1)-TQFTs and topological insulators," arXiv:1104.2632) is nowhere cited.
- **Expected:** Either (a) cite Walker & Wang 2012 (arXiv:1104.2632) as the source of the Walker-Wang construction and additionally a derivation that establishes the [KSS, 2·KSS] window for anyon-mediated transport in such models — note this derivation does not appear to exist in the published literature; or (b) drop "Walker-Wang" from the title, abstract, body, figure, and notebooks and rename the prediction to something the cited Hofman-Iqbal paper actually supports (e.g., "higher-form-symmetry topological-defect transport"); or (c) acknowledge explicitly that "Walker-Wang" is being used as a label for an *original* prediction the project is making (with no prior literature backing) and remove the Hofman-Iqbal cite at the point where the [KSS, 2·KSS] window is announced.
- **Fix:** Decision-point for the author. Without remediation this is a wrong-target citation in the strongest sense — readers will follow the cite, find a paper that does not contain the claim, and lose trust.
- **Cache:** fresh-fetch.

### 1.4 — 🟡 REQUIRED — Citation registry `doi_verified: None` for all six paper-36 bibitems

- **Gate:** CitationIntegrity
- **Location:** `src/core/citations.py:3038, 3184, 3201, 3218, 3243, 3259, 3275` — Polyakov1978, SvetitskyYaffe1982, PelissettoVicari2002, KosPolandSimmonsDuffin2016, KovtunSonStarinets2005, HofmanIqbal2018, KitaevAnyons2003 all carry `doi_verified: None`. Per project memory `feedback_citation_verification_required.md` (2026-04-26): "never trust `doi_verified`; hallucinated citations and wrong-target arXiv IDs DO occur. Always WebFetch CrossRef + arXiv + NASA ADS before flipping `doi_verified: None → True`."
- **Observed:** Two of seven verified by this review (Polyakov, Svetitsky-Yaffe) are clean. Two (KPSD, HofmanIqbal) are demonstrably wrong (findings 1.1, 1.2). Three (Kovtun-Son-Starinets, Pelissetto-Vicari, Kitaev) match WebFetch metadata at the level of title + arXiv ID.
- **Expected:** After correcting findings 1.1–1.2, run a full `--check citation_live_resolution` pass and flip `doi_verified: True` on the clean entries.
- **Fix:** After 1.1 and 1.2 close, mark each `doi_verified: True` with the WebFetch-derived metadata in the verification cache.
- **Cache:** fresh-fetch (this review).

### 2.1 — 🟡 REQUIRED — β_Potts = 0.111 used in the figure is the 2D 3-state Potts critical exponent; the figure label says "Z_3 / 3-state Potts (ν = 0.5)" implying 3D, but the 3D 3-state Potts deconfinement transition is weakly first-order and has no defined critical β

- **Gate:** ParameterProvenance
- **Location:** `src/core/visualizations.py:9007–9012` (β_ising = 0.326, β_potts = 0.111); `papers/paper36_center_symmetry/paper_draft.tex:179–180` ("β_Ising = 0.326, β_Potts = 0.111"); both notebooks figure section (Technical cell 13, Stakeholder cell 9).
- **Observed:** β = 0.111 is the textbook value of the order-parameter critical exponent for the **2D** 3-state Potts model (which is second-order, with η = 4/15, ν = 5/6, β = 1/9 ≈ 0.111). The 3D 3-state Potts ferromagnet transition is weakly **first-order**, so β is undefined; the deconfinement transition in 4D SU(3) gauge theory inherits this first-order character. The paper text §3 lines 158–163 *does* acknowledge "the 3D 3-state Potts transition is weakly first order, so ν_Potts is not a measured exponent and the literal value is illustrative only" — but the figure (which is the most-viewed artifact) silently extrapolates the 2D β value into a 3D plot with no caveat in the figure caption or in either notebook's figure section.
- **Evidence:**
  - 2D 3-state Potts: β = 1/9 (Wu, "The Potts model," Rev. Mod. Phys. 54, 235 (1982)).
  - 3D 3-state Potts: first-order transition; no β. Universality-class assignment to deconfinement is structural (Z_3 broken/unbroken), not numerical.
  - The Lean module's `critical_exponent_nu` comment on line 224 already says "mean-field-like, weak first order" but no β is named in Lean — so the disagreement is between Lean (honest about absence) and Python visualization (uses 2D β silently).
- **Expected:** Either (a) caveat the figure label as "β_Potts = 1/9 (2D 3-state Potts; 3D transition is first-order; shown as illustrative scaling only)"; or (b) drop the Z_3/Potts curve from the figure and replace with a discontinuous step (consistent with the first-order nature) plus narrative; or (c) at minimum, add a figure caption note about the dimensional extrapolation.
- **Fix:** Add caveat to the figure caption + both notebook figure-cell prose. Annotate the visualization source with the dimensional-mismatch note.

### 3.1 — 🔵 RECOMMENDED — `higher_form_discrete_iff_non_abelian` is presented as "the most substantive cross-bridge" but reduces to a 2×2 case-split on inductive constructors after a single rewrite, given the algorithmic structure of `higher_form_symmetry`

- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/CenterSymmetryConfinement.lean:351–359`; paper §5.1 line 252 ("The most substantive cross-bridge to the project's existing gauge-erasure infrastructure is the biconditional `higher_form_discrete_iff_non_abelian`"); both notebooks §6 / §6 prose.
- **Observed:** The proof is `unfold; rw [h_cont]; cases G.is_abelian <;> simp` — a four-line case-split on a Boolean. The substantive content is the *definition* of `higher_form_symmetry` (`GaugeErasure.lean:106–108`):
  ```
  | true,  true  => HigherFormType.continuous_1form
  | false, true  => HigherFormType.discrete_1form
  | _,     false => HigherFormType.none
  ```
  not the biconditional theorem. Per the preemptive-strengthening discipline question 5 ("If I make the function := <obvious target>, does the theorem become trivially 0 ≤ C/A?") this is a "defining-the-conclusion" pattern. The Lean docstring already self-classifies the theorem as "NOT identity wrapper" but the alternative — the substantive load living in the prior `higher_form_symmetry` definition — is not surfaced in the paper or notebooks.
- **Evidence:** The proof body, plus the structure of `higher_form_symmetry` shown above. The biconditional is decide-able once the Boolean truth table is in place.
- **Expected:** Either downgrade the prose ("a structural specialization of `higher_form_symmetry`'s definition to the non-Abelian case"), or acknowledge that the substantive content is the design of the `HigherFormType` inductive + the `higher_form_symmetry` match, not the cross-bridge theorem itself. Per `feedback_post_wave_strengthening_audit.md`, definitional-unfolding-as-physics is one of the four anti-patterns.
- **Fix:** Adjust paper §5.1 prose and notebook §6 prose. Lean theorem is fine as-is.

### 3.2 — 🔵 RECOMMENDED — `su3k1_fusion_card_matches_z3_order` is `Fintype.card SU3k1Obj = Z3.N` reduced via `native_decide` — substantive (small) but the paper / notebook framing as "categorified center symmetry" overstates its mathematical depth

- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/CenterSymmetryConfinement.lean:366–369` and `lean/SKEFTHawking/SU3kFusion.lean:39` (`su3k1_object_count : Fintype.card SU3k1Obj = 3 := by native_decide`); paper §5.2 lines 261–266; notebook §6 (Technical) and stakeholder cell 12.
- **Observed:** The cross-bridge theorem proves "3 = 3" via a `rw` chain that reduces to the SU3kFusion `native_decide` count. It is genuinely calling another module's theorem (✓ per feedback_python_lean_refs_drift), but the load-bearing statement reduces to "the inductive type SU3k1Obj has three constructors" which is by-construction. The notebook stakeholder cell 12 narrative goes further: "Fusion rules of SU(3)_1 are isomorphic to Z_3 group addition: fund⊗fund=conj (1+1=2 mod 3) …" — this assertion (that the fusion is isomorphic to Z_3 group ring) is NOT proved by `su3k1_fusion_card_matches_z3_order`; it is only asserted. The matching of cardinalities is necessary but not sufficient for ring isomorphism.
- **Evidence:** The Lean theorem statement is `Fintype.card SU3k1Obj = Z3.N`. There is no `theorem su3k1_fusion_iso_z3_group_ring` in either CenterSymmetryConfinement.lean or SU3kFusion.lean.
- **Expected:** Tighten the notebook stakeholder prose: replace "Fusion rules of SU(3)_1 are isomorphic to Z_3 group addition: …" with "the *cardinality* of the SU(3)_1 fusion category matches |Z_3| = 3; the explicit fusion-rules → Z_3-group-ring isomorphism is asserted in physics but not formalized here." Or formalize the iso (small additional theorem) and cite it.
- **Fix:** Notebook prose tightening, or add a small theorem.

### 4.1 — 🟡 REQUIRED — RHIC η/s ≈ 0.10–0.20 quoted in stakeholder notebook with no provenance entry and no published-source citation

- **Gate:** ParameterProvenance / NarrativeGrounding (feasibility-claim)
- **Location:** `notebooks/Phase6d1_CenterSymmetry_Stakeholder.ipynb` cell 0 ("most *perfect* fluid known: shear-viscosity-to-entropy ratio η/s ≈ 0.1-0.2, only ∼1.3-2.5× the universal lower bound") and cell 8 ("RHIC quark-gluon plasma     ≈ 0.10–0.20 (~1.3–2.5× KSS)").
- **Observed:** No primary-source citation supports the 0.10–0.20 bracket. Bayesian global-fit analyses (e.g., Bernhard, Moreland, Bass, Nature Phys. 15, 1113 (2019); JETSCAPE collaboration, PRC 103, 054904 (2021)) typically extract η/s in the range 0.08–0.20 with strong T-dependence; the conventional headline "η/s ≈ 1/(4π)" is consistent with the *minimum* near T_c, not a temperature-averaged value. Quoting "0.10–0.20" without primary-source attribution leaves the reader unable to verify.
- **Evidence:** No `PARAMETER_PROVENANCE` entry for "RHIC_eta_over_s" in `src/core/provenance.py` (not directly verified by this review; the absence of citations in the registry for the value is sufficient).
- **Expected:** Add a primary-source citation in the stakeholder notebook (e.g., Bernhard-Moreland-Bass 2019 or a JETSCAPE 2021 review), and add a `PARAMETER_PROVENANCE` entry for the heavy-ion η/s extraction band.
- **Fix:** Add citation + provenance entry, or rephrase as "extracted in heavy-ion phenomenological fits to be a few times the KSS bound" without a numerical interval.

### 5.1 — 🟡 REQUIRED — "First formalization in any proof assistant" type narrative is implicit but not searched

- **Gate:** NarrativeGrounding (first-claim)
- **Location:** Paper does not say "first formalization in any proof assistant" explicitly, but Technical notebook cell 0 says "Lean module: `lean/SKEFTHawking/CenterSymmetryConfinement.lean` (18 substantive theorems / 0 sorry / 0 new axioms)" and the project-side memory entry `project_phase6d_w1_shipped.md` strongly implies novelty. The stakeholder notebook §6 ("Honest scope") does NOT explicitly claim first-in-any-proof-assistant for confinement-as-Z_N-1-form-center, but this is the *implicit* contribution of the wave.
- **Observed:** No GitHub / Mathlib / Agda / Coq search documented before submission.
- **Expected:** Document a search of Mathlib's `Mathlib.Analysis.LatticeGauge`, ProofGround / Lean Community Zulip, and Agda's HoTT / Mathstad libraries for prior formalizations of: (a) Polyakov-loop order parameter, (b) Z_N 1-form center symmetry, (c) Svetitsky-Yaffe universality. Even a negative result is valuable to the audit trail.
- **Fix:** Add a literature-search note to the stakeholder notebook §6 ("Honest scope") of the form "Searched Mathlib (no Polyakov-loop or center-symmetry lemmas as of {date}); searched Coq library of formalized math (no entries); searched Agda standard library (no entries). To our knowledge this is the first proof-assistant formalization of the structural framing."

### 5.2 — 🔵 RECOMMENDED — Stakeholder notebook cell 0 attribution "the most *perfect* fluid known" + "stunning surprise" carries an evaluative tone that the paper draft does not

- **Gate:** NarrativeGrounding (style)
- **Location:** Stakeholder notebook cell 0.
- **Observed:** The stakeholder framing is colloquial; the paper draft is restrained. This is acceptable for a stakeholder notebook but inconsistent if the notebook is later cited in the paper.
- **Fix:** None required if the stakeholder notebook stays out of formal citation graphs.

### 6.1 — 🔵 RECOMMENDED — `H_WalkerWangTransportNearKSS` is honestly disclosed as a tracked Prop ("def" not "theorem") in the Lean module; the paper §4 line 205 ("structural assumption") and notebook §5 ("tracked-Prop") match — disclosure is correct

- **Gate:** AssumptionDisclosure
- **Location:** `lean/SKEFTHawking/CenterSymmetryConfinement.lean:292–293` (`def H_WalkerWangTransportNearKSS`); paper line 205 ("encoded as a structural assumption"); Technical notebook cell 9 ("Lean tracked-Prop"); Stakeholder notebook cell 11 ("tracked Prop — testable prediction, not a derived consequence").
- **Observed:** Disclosure is honest. No finding required.
- **Fix:** None.

### 6.2 — 🟡 REQUIRED — Mathlib `Real.pi_gt_d4` and `Real.pi_lt_d4` exist and are used correctly; the Lean proofs of `KSS_bound_below_0_08` and `KSS_bound_above_0_07` are valid

- **Gate:** LeanProofSubstance
- **Location:** `lean/SKEFTHawking/CenterSymmetryConfinement.lean:256–278`.
- **Evidence:** Direct grep of `Mathlib/Analysis/Real/Pi/Bounds.lean:171,176`:
  ```
  theorem pi_gt_d4 : 3.1415 < π := by …
  theorem pi_lt_d4 : π < 3.1416 := by …
  ```
  The proof body uses `linarith` from `Real.pi_gt_d4` to derive `π > 3.141` (weaker — valid) and `Real.pi_lt_d4` to derive `π < 3.142` (weaker — valid). `nlinarith` then closes the goal. Proofs are sound; no finding required.
- **Fix:** None.

### 7.1 — 🔵 RECOMMENDED — Theorem count in `feedback_post_wave_strengthening_audit.md` and `project_phase6d_w1_shipped.md` memory says "20 substantive thms / 30 tests" but current Lean file has 18 theorems and `tests/test_center_symmetry.py` has 28 tests; the paper macros `\centerSymmThms` (= 18) and `\centerSymmTests` (= 28) match the current files

- **Gate:** CountFreshness
- **Location:** `docs/counts.tex` (18, 28 — matches files); MEMORY.md entry `project_phase6d_w1_shipped.md` (20, 30 — stale).
- **Observed:** Paper / notebook / Lean counts agree at 18 / 28. Memory entry has drifted by 2 / 2. This is *outside* the paper, not a paper-internal inconsistency, but if the memory note is the basis for any future status report or commit message, the drift will propagate.
- **Fix:** Update memory note (out-of-scope for paper submission).

### 7.2 — 🔵 RECOMMENDED — ν_Ising = 0.6299 anchored to BOTH Pelissetto-Vicari (2002) and Kos-Poland-Simmons-Duffin (2016); only the latter matches at the 4th decimal

- **Gate:** ParameterProvenance
- **Location:** `papers/paper36_center_symmetry/paper_draft.tex:152–158`; both notebooks §3.
- **Observed:** PV 2002 reports ν = 0.6301(4) for 3D Ising; KPSD 2016 ("Precision Islands") reports ν = 0.62997(1). The paper rounds to 0.6299, which matches KPSD at 4 decimals but disagrees with PV at the 4th decimal. Since the paper attributes 0.6299 jointly to both papers, the joint attribution is precision-inconsistent (the PV value rounded to 4 decimals is 0.6301, not 0.6299).
- **Fix:** Cite KPSD 2016 only (and only after fixing finding 1.1) for the 4-decimal value, and cite PV 2002 separately for the broader survey context with a sentence acknowledging the per-author precision differences.

## QI Candidate

The combination of findings 1.1, 1.2, 1.4 strongly suggests a systemic issue: the citation registry was bulk-imported with author-supplied metadata that was never WebFetch-verified (`doi_verified: None` on all paper-36 entries), and the bibitem text propagated those errors directly into the paper. Memory `feedback_citation_verification_required.md` already flags this class. Strengthen the project-wide validation:

1. Pipeline check `validate.py --check citation_live_resolution` should be a **hard gate** for paper submission, not advisory. Run it whenever a bibitem text is added or edited.
2. Add a registry-vs-bibitem text-diff check: any paper whose `\bibitem{key}` block disagrees with the corresponding registry entry (title / authors / venue / arXiv) is a Stage 13 BLOCKER regardless of whether the cited paper is real. (KPSD's bibitem disagrees with the registry on the venue field — the bibitem says "JHEP 03, 086" but the registry says "JHEP volume '03', page '086'" — both wrong.)
3. Treat *any* bibitem whose claimed title is not exactly the title returned by `arxiv.org/abs/<id>` JSON metadata as a wrong-target candidate. The cost of an LLM fabricating a plausible-sounding title (e.g., "Goldstone modes and photonization for higher form symmetries") is zero; the cost of a peer reviewer finding it is reputational. WebFetch every bibitem at Stage 13.
