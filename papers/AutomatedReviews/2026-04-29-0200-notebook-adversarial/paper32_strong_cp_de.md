---
paper: paper32_strong_cp_de (notebooks)
reviewer: adversarial-reviewer (notebook adaptation)
model: claude-opus-4-7
review_date: 2026-04-29T02:00:00Z
readiness_gates_version: 1
notebooks:
  - notebooks/Phase6c1_StrongCPDarkEnergy_Technical.ipynb
  - notebooks/Phase6c1_StrongCPDarkEnergy_Stakeholder.ipynb
sources_of_truth:
  - papers/paper32_strong_cp_de/paper_draft.tex
  - lean/SKEFTHawking/StrongCPTopologicalDE.lean
  - src/strong_cp_de/{__init__,zhitnitsky_eval,combined_de_consistency}.py
  - src/core/citations.py (CITATION_REGISTRY)
  - docs/counts.tex
---

# Adversarial Review — paper32 notebooks (Phase6c1_StrongCPDarkEnergy)

## Summary

- BLOCKER: 2
- REQUIRED: 4
- RECOMMENDED: 3
- INFO: 1

Two BLOCKER citation findings (`KlinkhamerVolovik2010` wrong-title — bibitem
title in `paper_draft.tex` describes a different paper than arXiv:0907.4887
actually is; `VanWaerbeke2025` wrong-title — bibitem and registry both carry
a title that does not match the actual arXiv:2506.14182 title) propagate
straight into both notebooks via the prose attributions. Numerical anchors
(ρ_DE = 6.71e-9 eV⁴, 240× ratio, ~120 orders, M_P⁴ ≈ 2.22e112) recompute
correctly. Counts (\strongCpDeThms{8} / \strongCpDeTests{14}) match the
actual artifacts. The H_BothActiveGivesInconsistency tracked-Prop disclosure
is honest in both notebooks. Theorem `IsAnomalyMatchingCompatible_no_planck_theta`
is described slightly inaccurately in the technical notebook prose. The
notebooks are NOT submission-ready: the two BLOCKER citation issues must be
fixed before paper32 ships, and they will appear in any pre-print
distribution of the notebooks themselves.

## Findings

### F-1 — 🔴 BLOCKER — KlinkhamerVolovik2010 bibitem describes wrong paper [class: citation]

- **Gate:** CitationIntegrity
- **Location:**
  - `papers/paper32_strong_cp_de/paper_draft.tex:278-281` (bibitem)
  - `notebooks/Phase6c1_StrongCPDarkEnergy_Stakeholder.ipynb` cell `p32s-4-md` (prose attribution)
  - `src/core/citations.py:3093-3107` (registry)
- **Observed:** Bibitem reads "F.~R.~Klinkhamer and G.~E.~Volovik, *Cosmological constant from gravitating Skyrmions*, JETP Lett. 91, 259 (2010); arXiv:0907.4887." The stakeholder notebook cell 4 (`p32s-4-md`) attributes the q-theory mechanism to "the gravitating-Skyrmion / q-theory family of cosmological-constant-from-topology models" — same Skyrmion attribution.
- **Evidence:** Independent fetch of `https://arxiv.org/abs/0907.4887` returns title "**Towards a solution of the cosmological constant problem**" by Klinkhamer & Volovik. Abstract first sentence describes "a vacuum variable... three-form gauge fields or aether-type velocity fields" — NO mention of Skyrmions. JETP Lett. 91, 259 (2010) journal reference is correct for arXiv:0907.4887 (q-theory paper), not for any Skyrmion paper. The Klinkhamer–Volovik Skyrmion-DE paper is a separate work (arXiv:0903.1326, "Self-tuning vacuum variable and cosmological constant" / related Skyrmion variants). The author has **conflated two different K–V papers**.
- **Expected:** Either (a) update bibitem title to "Towards a solution of the cosmological constant problem" if arXiv:0907.4887 is the intended cite (consistent with q-theory framing in §1, §5), or (b) keep "gravitating Skyrmions" framing and replace arXiv ID + JETP Lett. ref with the correct Skyrmion paper. The paper currently reads as q-theory throughout (§5 "Klinkhamer–Volovik q-theory contribution"), so option (a) is consistent. Stakeholder notebook cell `p32s-4-md` must drop "gravitating-Skyrmion" phrasing.
- **Cache:** fresh-fetch (no prior cache record loaded). doi_verified is `None` in registry (line 3102) — never verified. CITATION_REGISTRY entry's title "Cosmological constant from gravitating Skyrmions" is also wrong and must be corrected.

### F-2 — 🔴 BLOCKER — VanWaerbeke2025 bibitem title does not match arXiv [class: citation]

- **Gate:** CitationIntegrity
- **Location:**
  - `papers/paper32_strong_cp_de/paper_draft.tex:273-276` (bibitem)
  - `src/core/citations.py:1064-1077` (registry, title field line 1066)
  - Both notebooks reference "Van Waerbeke and Zhitnitsky (arXiv:2506.14182)" by descriptive paraphrase only (technical cell `p32t-3-md`, stakeholder cell `p32s-3-md`); neither quotes the paper title directly so the notebooks themselves do not propagate a wrong-title.
- **Observed:** Bibitem reads "L.~Van Waerbeke and A.~R.~Zhitnitsky, *Topological dark energy from QCD vacuum*, arXiv:2506.14182 (2025)." Registry title field reads "QCD topological dark energy".
- **Evidence:** Independent fetch of `https://arxiv.org/abs/2506.14182` returns title "**DESI results and Dark Energy from QCD topological sectors**" by Ludovic Van Waerbeke and Ariel Zhitnitsky (v1 June 2025; v2 January 2026). Both the bibitem title AND the registry title are wrong — they paraphrase the topic but disagree with the actual title.
- **Expected:** Update bibitem to "DESI results and Dark Energy from QCD topological sectors". Update registry `title` field to match. The arXiv ID and authors are correct. Set `doi_verified` after CrossRef confirmation when journal publication lands.
- **Cache:** fresh-fetch. Registry doi_verified is `None`.

### F-3 — 🟡 REQUIRED — Strong-CP / DE experimental anchors missing from PARAMETER_PROVENANCE [class: parameter]

- **Gate:** ParameterProvenance
- **Location:**
  - `src/strong_cp_de/zhitnitsky_eval.py:20-24` (LAMBDA_QCD_GEV, NEUTRON_EDM_BOUND, RHO_DE_OBSERVED_EV4 declared as plain module constants)
  - `src/core/provenance.py:29` (PARAMETER_PROVENANCE dict — no entries match LAMBDA_QCD, NEUTRON_EDM, RHO_DE, theta, Pendlebury, Zhitnitsky)
  - Both notebooks consume these constants as load-bearing inputs (cells `p32t-1-code`, `p32s-1-code`).
- **Observed:** Three load-bearing experimental parameters used throughout both notebooks (and in the paper's quantitative anchors) are not registered in `PARAMETER_PROVENANCE`. Pipeline Invariant 8 in `CLAUDE.md` says "Every experimental parameter has verified provenance — traced to a published source via PARAMETER_PROVENANCE in src/core/provenance.py… Enforced by CHECK 15."
- **Evidence:** `grep -nE "Pendlebury|2.8e-11|EDM|theta|Zhitnitsky|RHO_DE|LAMBDA_QCD|neutron" src/core/provenance.py` returns one unrelated GW170817 hit. The strong-CP / DE parameters are absent.
- **Expected:** Add three PARAMETER_PROVENANCE entries — `LAMBDA_QCD_PDG` (PDG-anchored 0.1 GeV; cite `ParticleDataGroup` registry entry), `NEUTRON_EDM_THETA_BOUND` (cite Pendlebury2015), `RHO_DE_PLANCK_DESI` (cite Planck2018 + DESI2024 with the Ω_Λ → eV⁴ conversion documented). Each must include `human_verified_date` before paper32 submission (per Invariant 8: "human verification … unblocks paper submission").
- **Cache:** N/A.

### F-4 — 🟡 REQUIRED — Technical notebook misdescribes IsAnomalyMatchingCompatible_no_planck_theta semantics [class: overclaim]

- **Gate:** NarrativeGrounding
- **Location:** `notebooks/Phase6c1_StrongCPDarkEnergy_Technical.ipynb` cell `p32t-4-md`.
- **Observed:** Cell prose: "any attempt to instantiate a θ-vacuum at θ = 1 is structurally rejected at the `ThetaVacuum` construction step (Lean: `IsAnomalyMatchingCompatible_no_planck_theta` short-circuits via the `theta_small` invariant — the other two pillars are not even evaluated)."
- **Evidence:** Reading `lean/SKEFTHawking/StrongCPTopologicalDE.lean:168-174`, the theorem signature is

  ```lean
  theorem IsAnomalyMatchingCompatible_no_planck_theta
      (tv : ThetaVacuum) (h_planck : tv.theta = 1) :
      False
  ```

  i.e. it proves an unconditional `False` from the contradictory premises `(tv : ThetaVacuum)` and `tv.theta = 1`. It is **not** a statement about `IsAnomalyMatchingCompatible` and never references that predicate in its body — it never evaluates *any* of the three pillars; it derives `False` from the EDM invariant alone. The cell's "short-circuits via the theta_small invariant — the other two pillars are not even evaluated" reads as a description of evaluating `IsAnomalyMatchingCompatible` at θ = 1, which is wrong: the theorem is vacuously about a non-existent `ThetaVacuum`, not about the predicate.
- **Expected:** Reword to: "At θ = 1, no `ThetaVacuum` exists at all — the theorem `IsAnomalyMatchingCompatible_no_planck_theta` proves `False` from the impossible pair of hypotheses (any `tv : ThetaVacuum`) ∧ (`tv.theta = 1`). The predicate `IsAnomalyMatchingCompatible` is never instantiated at θ = 1 because the structural premise of the conjunction (a valid `ThetaVacuum`) is uninhabitable."
- **Note:** The Lean theorem's name is misleading on its own — `IsAnomalyMatchingCompatible_no_planck_theta` advertises a property of the predicate, but the body proves `False` directly without referencing the predicate. The naming is project-internal and not a notebook finding, but the notebook prose treats the name at face value, which is what produced the drift.

### F-5 — 🟡 REQUIRED — Paper-vs-figure-vs-notebook orders-of-magnitude inconsistency [class: contradiction]

- **Gate:** CrossPaperConsistency
- **Location:**
  - `src/core/visualizations.py:9141` — figure docstring: "Zhitnitsky prediction matches observation within ~2 orders without free parameters"
  - `papers/paper32_strong_cp_de/paper_draft.tex:40-41,146-148` — paper: "within roughly 240× of the observed value --- well within the three-orders-of-magnitude window"
  - Both notebooks (cells `p32t-3-md`, `p32s-3-md`): "within 3 orders of magnitude" / "within a factor of a few hundred"
- **Observed:** The figure-generation function's docstring asserts "~2 orders" while the paper and both notebooks assert "3 orders". 240× is approximately 10^2.38 — strictly 3 orders, not 2. The figure docstring is wrong.
- **Evidence:** log10(6.71e-9 / 2.8e-11) = log10(239.6) = 2.379. So "within 3 orders" is correct (the canonical "Zhitnitsky proposal precision" is 3 orders, per the paper line 41); "within ~2 orders" is mathematically false (2.379 > 2).
- **Expected:** Fix `src/core/visualizations.py:9141` docstring to "within ~3 orders without free parameters" (or "within a factor of ~240"). The figure file itself is unaffected — only the docstring drifts.

### F-6 — 🟡 REQUIRED — Stakeholder notebook unverified physics-mechanism interpretive claim [class: overclaim]

- **Gate:** NarrativeGrounding
- **Location:** `notebooks/Phase6c1_StrongCPDarkEnergy_Stakeholder.ipynb` cell `p32s-3-md`.
- **Observed:** "Van Waerbeke and Zhitnitsky (2025) pointed out that the QCD topological vacuum, viewed through **gauge/gravity duality and the analog of black-body emission for topological excitations**, naturally produces a vacuum energy density…"
- **Evidence:** WebFetch of `https://arxiv.org/abs/2506.14182` abstract reports "physically motivated dark-energy (DE) model rooted in the topological structure of the Quantum ChromoDynamic (QCD) vacuum" — does not mention gauge/gravity duality nor "black-body emission for topological excitations" in the visible abstract. PDF body could not be fetched (binary content). The two specific mechanism phrases the notebook prose attributes to VW-Z are not verified against the paper body and are not load-bearing for any claim downstream — they are colour for a non-specialist tour. Risk: a stakeholder reader who clicks through to arXiv:2506.14182 and finds neither phrase will lose confidence in the notebook.
- **Expected:** Either (a) drop the mechanistic phrases and use the abstract-grounded "rooted in the topological structure of the QCD vacuum" language, or (b) verify the phrases against the paper body and add the page/section citation. Until verified, the cell should not assert mechanistic detail beyond what the abstract supports.

### F-7 — 🔵 RECOMMENDED — "no free parameters" claim relies on input scales already chosen [class: overclaim]

- **Gate:** NarrativeGrounding
- **Location:**
  - Technical cell `p32t-3-code` print: "(within 3 orders, NO free parameters)"
  - Stakeholder cell `p32s-3-md`: "no fitted constants, no anthropic selection, no extra fields. Just two scales already measured: Λ_QCD from PDG and M_P from gravity."
- **Observed:** The "no free parameters" framing is borrowed from the Van Waerbeke–Zhitnitsky paper. Technically, the formula ρ_DE ∼ Λ_QCD^6 / M_P^2 absorbs an O(1) coefficient (the project encodes 6.71e-3 eV⁴/GeV⁶ in `_PLANCK_SUPPRESSION_EV4_PER_GEV6`) which is the unit-conversion factor 10^54 / M_P_eV^2. Whether the leading dimensional combination is exactly Λ_QCD^6/M_P^2 vs. e.g. (Λ_QCD/M_P)^4 · Λ_QCD^2 / Λ_other (which would change the prediction by orders of magnitude) is a *modelling choice*, not a derivation. The "no free parameters" claim assumes (a) the exponent on Λ_QCD is 6 and (b) the suppressing scale is M_P^2 with no O(1) prefactor.
- **Evidence:** The Lean theorem `zhitnitsky_DE_at_lambda_qcd_within_3_orders` only proves `zhitnitskyDE_eV4 0.1 < 1.0e-7` — it does not prove the dimensional analysis is uniquely fixed. The literature claim of zero free parameters is only as strong as the dimensional ansatz in arXiv:2506.14182.
- **Expected:** Soften to "no tuneable parameters once the dimensional ansatz Λ_QCD^6 / M_P^2 is adopted" or attribute the framing explicitly: "the no-free-parameter claim of Van Waerbeke–Zhitnitsky 2025". The paper draft already uses the more careful "no tuneable parameters" + "the no-free-parameter Zhitnitsky prediction" attributed framing in §3 and §6 (lines 36, 232-235, 264-265); the notebooks are stronger and should match the paper's hedge.

### F-8 — 🔵 RECOMMENDED — H_BothActiveGivesInconsistency technical disclosure could be explicit about Lean theorem scope [class: placeholder]

- **Gate:** AssumptionDisclosure
- **Location:**
  - Technical notebook cell `p32t-5-md` and stakeholder notebook cell `p32s-4-md`.
- **Observed:** Both notebooks honestly disclose `H_BothActiveGivesInconsistency` as a "tracked-Prop predicate" / "modeling-threshold predicate". However, both also assert that the Lean theorem `combined_zhitnitsky_qtheory_exceeds_observation` proves "exceeding observed dark energy" / "the inconsistency triggers" / paper-§5 "exceeds the Zhitnitsky-alone saturation point (which itself already lies within ~240× of observation)".
- **Evidence:** Reading `StrongCPTopologicalDE.lean:191-205`, the theorem proves only `combined > zhitnitskyDE_eV4 0.1` — i.e. combined > Zhitnitsky-alone. The link "Zhitnitsky-alone is already 240× observation, therefore combined >> observation" is true but is *not* a separate Lean theorem; it relies on `zhitnitsky_DE_at_lambda_qcd_within_3_orders` (which only certifies < 1e-7, not "240× of 2.8e-11"). The chain is a Python-side numerical inference, not a Lean-side proof. Neither notebook misrepresents this, but the prose blends the two without flagging the boundary.
- **Expected:** In §5 / §4 prose, add one sentence: "The Lean theorem proves only that combined > Zhitnitsky-alone; the further chain to ‘exceeds observation by ~240×’ is the Python-level numerical inference using the Zhitnitsky-alone value 6.71e-9 eV⁴ vs. observed 2.8e-11 eV⁴."

### F-9 — 🔵 RECOMMENDED — "Z₁₆ anomaly per generation" wording could mislead [class: overclaim]

- **Gate:** NarrativeGrounding
- **Location:** `notebooks/Phase6c1_StrongCPDarkEnergy_Technical.ipynb` cell `p32t-4-code` print output.
- **Observed:** Print line: "Z₁₆ anomaly per generation (SM only): 15 (= -1 mod 16, anomalous)". The phrase "= -1 mod 16" is technically equivalent to 15 mod 16 but the asymmetric framing (–1 vs. 15) is unmotivated for a stakeholder reader and inconsistent with the upstream Lean module's convention `(15 : ZMod 16)` (per `Z16AnomalyComputation.lean:90-93`).
- **Evidence:** `Z16AnomalyComputation.lean:90` describes the without-ν_R anomaly as "15" not "–1". The project's `sm_anomaly_with_nu_R` proves `(16 : ZMod 16) = 0`. Using "–1" needlessly reframes the modular arithmetic.
- **Expected:** Replace "= -1 mod 16, anomalous" with "= 15 mod 16 ≠ 0, anomalous" to match the upstream Lean naming convention.

### F-10 — 🔵 INFO — Counts current and consistent [class: count]

- **Gate:** CountFreshness
- **Location:**
  - `docs/counts.tex:33-34` declares `\strongCpDeThms{8}` and `\strongCpDeTests{14}`.
  - Technical notebook intro: "8 substantive theorems, 0 sorry, 0 new axioms".
  - `tests/test_strong_cp_de.py` has 14 `def test_*` (independently counted via grep).
  - `lean/SKEFTHawking/StrongCPTopologicalDE.lean` has 8 substantive theorems (lines 66, 95, 111, 124, 154, 168, 200, 220); plus structure `ThetaVacuum`, defs `cpSymmetricVacuum`, `zhitnitskyDE_eV4`, `rho_DE_observed_eV4`, `IsAnomalyMatchingCompatible`, `H_BothActiveGivesInconsistency`.
- **Observed:** All counts match. No drift between docs/counts.tex, paper, notebook prose, and the artifacts.
- **Evidence:** Cross-checked above.
- **Status:** Clean.

## QI Candidate

**Systemic citation-registry hygiene gap.** Two BLOCKER-class wrong-title
findings (F-1, F-2) on the *same paper*'s bibliography section both stem
from `doi_verified: None` entries in `src/core/citations.py`. Memory
`feedback_citation_verification_required.md` (2026-04-26) explicitly flagged
this anti-pattern after the WetterichNJL hallucination. Both Phase 6c.1
citations (KlinkhamerVolovik2010 line 3093, VanWaerbeke2025 line 1064)
were added with `doi_verified: None` and registry-`notes` claiming
"arXiv verified" — but the registry `title` field for both is wrong.
"arXiv verified" appears to mean only "arXiv ID resolves to a paper", not
"title field matches the paper at that arXiv ID".

Recommend a `validate.py --check citation_title_match` rule that flags any
CITATION_REGISTRY entry whose `arxiv` is non-null but whose `title` has not
been WebFetch-confirmed against `arxiv.org/abs/<arxiv>`. Such a check would
have caught both F-1 and F-2 prior to paper32 wave-close. The `notes`
"arXiv verified" string is currently a low-trust signal — promote it to a
machine-checked field (`arxiv_title_verified: True/False/None`) so future
authors cannot conflate "arXiv ID resolves" with "title matches".
