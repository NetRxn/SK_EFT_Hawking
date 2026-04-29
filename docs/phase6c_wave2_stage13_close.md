# Phase 6c Wave 2 — Stage 13 Reflexive Re-Close

**Date:** 2026-04-29
**Wave:** 6c.2 — `EWBaryogenesisChiralityWall.lean` / paper33
**Status:** **CLOSED end-to-end through Stage 14.**
**Decision Gate C.2:** **PASS reaffirmed** — SM EWBG remains *doubly forbidden* under `H_KLRS_SM_Crossover` (content unchanged; this re-close addresses Stage 13 hygiene).

---

## Why this re-close exists

Wave 6c.2 originally shipped 2026-04-29 through Stage 12, with Stage 13 (adversarial review) explicitly *deferred* per the then-current pipeline policy ("user-triggered"). Memory `feedback_stages_11_13_reflexive.md` (2026-04-30) corrected that policy: Stage 11 (notebooks) and Stage 13 (adversarial review) are **reflexive** parts of the pipeline and run automatically after Stage 10. Only Stage 4 (Aristotle) and explicit roadmap-labelled gates remain user-authorized.

This close runs Stage 13 against paper33 and addresses every BLOCKER and REQUIRED in-session, then refreshes the Wave 7 bundle infrastructure that paper33 was missing from.

---

## Stage 13 review results

### Figure-reviewer on `fig_ewbg_allowed_region` (PRL Fig. 1)

**Verdict:** **WARNING** — physics PASS, rendering BLOCKER + 3 REQUIRED (all fixed in-session).

| ID | Severity | Issue | Fix |
|----|----------|-------|-----|
| R1 | BLOCKER | Right-panel subplot title `(m_H, E) phase diagram with KLRS endpoint` collided with the KLRS-vline annotation `KLRS endpoint m_H = 72.4 GeV` (`annotation_position="top"` over-rode the title band). | `annotation_position="bottom right"` + white bgcolor; `annotation_text` now line-broken (`KLRS endpoint<br>m_H = 72.4 GeV`). |
| R2 | REQUIRED | y-tick `0.05` crowded into top-left corner of right panel (side-effect of R1). | Cleared by R1 fix. |
| R3 | REQUIRED | `SM overshoot: 1.73× KLRS` annotation was `COLORS["cross"]` light-grey on grey crossover fill — low contrast. | Black text + `bgcolor="rgba(255,255,255,0.85)"` + bordered. |
| R4 | REQUIRED | Left-panel marker labels (`SM-as-is`, `SM+3ν_R`, `BSM target`) overlapped the bold quadrant labels (`DOUBLY FORBIDDEN` etc.) — both inside the same heatmap cells. | Quadrant labels lifted to top-of-cell annotations (`yshift=42`); markers now occupy cell centers cleanly. Marker labels removed in-figure (legend names them). |

Single-function edit at `src/core/visualizations.py:fig_ewbg_allowed_region` (lines 7708-7898). PNG regenerated; visual inspection confirms all four findings cleared. Report at `papers/paper33_ewbg_chirality_wall/figures/figure_review_report.json`.

### Claims-reviewer (sentence-walker v2) on `paper_draft.tex`

**Verdict:** 83 sentences; 53 PASS / 19 TRANSITION / 7 INFO / **3 FAIL** / 1 WARN.
**Finding classes:** 0 IA / 0 TP / 0 SD / 0 TN / 1 HD.

#### BLOCKERS — Wang2020 bibkey collision (Gate1 CitationIntegrity, 3 sentences)

The `\bibitem{Wang2020}` text in paper33 (lines 393-397) read:

> J. Wang, *Anomaly and cobordism constraints beyond grand unification: Energy hierarchy*, Nucl. Phys. B **980**, 115798 (2022); arXiv:2008.06499.

But `CITATION_REGISTRY['Wang2020']` resolves to a *different* Wang paper:

> J. Wang, *Anomaly and cobordism constraints beyond the Standard Model*, Phys. Rev. Research **2**, 013189 (2020); arXiv:1910.14664.

These are two distinct Wang papers. Three sentences cite this bibkey (abstract line 33-37; intro line 82-87; §3 line 161-166); each chain FAILed against the registry. This is the **same wrong-target failure mode** that paper40 round-1 surfaced (see memory `feedback_hallucinated_citation_paper40.md`).

**Fix:** repointed `\bibitem{Wang2020}` to match the registry. The substantive content cited in all three paper33 sites (Z₁₆-anomaly classification of the SM, non-perturbative gauging-step obstruction) is **exactly** what the registry's Wang2020 (PRR 2 013189) covers. The NPB 2022 paper extends to GUT-scale phenomenology, which paper33 never addresses; the original bibitem text was a paste-error (different Wang paper accidentally given the same bibkey).

#### REQUIRED (mitigated by prose disclosure → WARN) — `H_KLRS_SM_Crossover` not in HYPOTHESIS_REGISTRY (Gate6 AssumptionDisclosure, class HD)

The Lean module `EWBaryogenesisChiralityWall.lean:288` defines `H_KLRS_SM_Crossover` as a tracked Prop (load-bearing physics input behind the doubly-forbidden punchline), but the hypothesis was not registered in `src/core/constants.py::HYPOTHESIS_REGISTRY` (which previously held 6 entries: rokhlin_sigma_mod_16, modular_invariance_framing, c_minus_equals_8Nf, characteristic_square_mod_8, spin_bordism_iso_Z, H_ScalarChannelIsTetradBifurcationOutput). The dashboard-side disclosure layer therefore had no entry mirroring the Lean tracked Prop.

**Fix:** added `H_KLRS_SM_Crossover` to `HYPOTHESIS_REGISTRY` with full schema (statement / status=active / eliminability=hard / elimination_path / dependent_theorems / module=EWBaryogenesisChiralityWall / source / risk / circularity_note). `dependent_theorems` lists the two punchline theorems consuming the hypothesis (`sm_with_3nu_R_ewbg_forbidden_under_klrs` and `sm_no_nu_R_ewbg_doubly_forbidden`).

Paper §5 prose adequately discloses the hypothesis ("encoded as a tracked Prop because the lattice result is not derived in our framework") — that's why the original verdict was WARN rather than FAIL. The registry entry closes the dashboard-side gap.

#### Verifications that PASSed (no findings)

- IA arithmetic: 3×15=45 ✓; 45 mod 16=13 ✓; 48 mod 16=0 ✓; 13≡-3 (mod 16) ✓; 125.20/72.4≈1.7293 ✓; 1.5<1.73 ✓.
- Theorem count: paper "16 theorems" matches `grep -c "^theorem " EWBaryogenesisChiralityWall.lean` = 16.
- Pytest count: paper "23-test pytest suite" matches `pytest --collect-only` = 23.
- Module count: paper "3 modules in src/ew_baryogenesis/" matches `ls` = 3.
- TP: paper does not state a Lean / Mathlib pin → no TP findings.
- TN: every `\texttt{<Module>.<Symbol>}` in paper33 resolves in `lean_deps.json`. The cross-module `<Module>.<symbol>` documentation idiom (`Z16AnomalyComputation.three_gen_anomalous`, `GaugingStep.gauging_requires_z16_cancellation`, `SMFermionData.total_components_without_nu_R`, `EWPhaseTransition.crossover_excludes_baryogenesis`) is the project's Wave-4-accepted pattern (memory `project_phase6i_w4_shipped.md`). All 35+ theorem refs resolve.
- All 10 bibitems present in CITATION_REGISTRY with primary-source cache (CHECK 19 PASS post-fix).
- All EWBG_PARAMS values match `constants.py`.

Report at `papers/paper33_ewbg_chirality_wall/claims_review.json` (schema-validated via `scripts/sentence_state.py validate`, exit 0).

---

## Wave 7 gap closure (paper33 missing from `PAPER_DRAFT_MAPPING.md`)

paper33 was shipped 2026-04-29 but never added to the bundle mapping table — likely an oversight during the Wave 7 bundle-architecture wiring (Wave 7 was driven from existing-draft mapping, and paper33 was created on the same day Wave 7 closed).

**Mapping added** (PAPER_DRAFT_MAPPING.md table 1):

| Existing draft | Working title | New destination(s) | Lift action |
|---|---|---|---|
| `paper33_ewbg_chirality_wall` (Phase 6c W2) | EW baryogenesis ↔ chirality wall (doubly forbidden) | **D3 §13.5** (EWBG-doubly-forbidden bridge: chirality-wall × crossover, extending §13 EWPT) + **F §6, §10** | Lift-section |

**Total mapping** updated 39 → 40. **D3 source set** updated to include paper33 (alongside paper22 in the EWPT region, since paper33's bridge claim consumes paper22's EWPT verdict).

**Bundle infra refreshed** post-mapping:
- `scripts/bundle_clusters.py` re-run; cluster index unchanged (paper33 has no `prose_state.json` claim_clusters yet — like most papers, will populate as v2 claims-reviewer downstream sweeps run).
- `scripts/bundle_readiness.py` re-run; verdicts unchanged (4 GREEN: E2/I1/I2/L1; 4 YELLOW: D1/D2/E1/L2; 5 RED: D3/D4/D5/F/L3 — same as Wave 7 close).
- `validate.py --check bundle_consistency` (CHECK 21) PASS — 2 exact-match clusters guaranteed consistent; 0 normalized-match flagged.

---

## Decision Gate C.2 — reaffirmed

The original Wave-2 close-doc verdict stands unchanged:

> EWBG is **doubly forbidden** in SM under H_KLRS (`sm_no_nu_R_ewbg_doubly_forbidden`). Both branches fail: SM-no-ν_R chirality wall intact (anomaly = 13 mod 16); SM+3ν_R wall cracks but transition is crossover (m_H = 125.20 GeV > KLRS endpoint 72.4 GeV; overshoot 1.73). Dispatches: (a) **leptogenesis** via Phase 5z W2 sterile-neutrino seesaw + above-EWPT sphaleron conversion (preferred); (b) **BSM EWBG** via extra-scalar models producing first-order EWPT.

The Stage 13 fixes did not alter Lean theorem statements, Python computations, or numerical predictions. Only:
- One bibitem corrected (different Wang paper than originally pasted)
- One figure visualization function edited (rendering only; no data changes)
- One HYPOTHESIS_REGISTRY entry added (dashboard mirror of existing Lean tracked Prop)
- One PAPER_DRAFT_MAPPING.md row added (Wave 7 gap)

Phase 6e (nonlinear EFE) inherits the verdict unchanged; downstream model-building chooses between leptogenesis and BSM EWBG.

---

## Final state — Phase 6c Wave 2

| Component | State |
|---|---|
| Lean module `EWBaryogenesisChiralityWall.lean` | 16 substantive theorems / 0 sorry / 0 new axioms |
| Python `src/ew_baryogenesis/` | 3 modules / 23 pytest cases / 23/23 PASS in 0.04s |
| Paper33 PDF | 4 pages, 465 KB, compiles clean |
| Figure `fig_ewbg_allowed_region.png` | Regenerated; all Stage-13 issues cleared |
| `claims_review.json` | Schema-validated, 83 sentences |
| `figure_review_report.json` | Written |
| Bundle target | D3 §13.5 + F §6, §10 (Lift-section) |
| HYPOTHESIS_REGISTRY | +1 entry: `H_KLRS_SM_Crossover` |
| CITATION_REGISTRY | Wang2020 entry unchanged; paper33 bibitem repointed to match |
| Phase 6i validate.py checks | 5/5 PASS (parameter_provenance, citation_primary_sources_present, provenance_doi_in_registry, bundle_consistency, counts_fresh) |
| Decision Gate C.2 | PASS reaffirmed |

---

## Phase 6 outstanding work — final state

**Phase 6c FULLY CLOSED** — all 5 waves SHIPPED + Stage-13-reflexively re-closed:

- W1 `StrongCPTopologicalDE.lean` — SHIPPED 2026-04-27 (Stage 13 cleared 2026-04-29)
- **W2 `EWBaryogenesisChiralityWall.lean` — SHIPPED 2026-04-29 (Stage 13 cleared 2026-04-29 in this re-close)**
- W3 `EquivalencePrinciple.lean` — SHIPPED 2026-04-27
- W4 `QECHolographyBridge.lean` — SHIPPED 2026-04-27 (Stage 13 cleared 2026-04-29)
- W5 `RTCasiniHuertaBounds.lean` — SHIPPED 2026-04-27 (Stage 13 cleared 2026-04-29)

**Only outstanding Phase 6 work remaining:**

- **Phase 6f.1 (`Curvature.lean`)** — gated on the upstream Bonn Massot↔Rothgang Levi-Civita branch. Implementation deferred until Mathlib upstream lands.

All other Phase 6 sub-phases (6a-6e, 6h, 6i) are SHIPPED.

---

*Phase 6c Wave 2 Stage 13 reflexive re-close. Prepared 2026-04-29. Companion to original Wave 2 close (recorded inline in `docs/roadmaps/Phase6c_Roadmap.md` lines 98-111).*
