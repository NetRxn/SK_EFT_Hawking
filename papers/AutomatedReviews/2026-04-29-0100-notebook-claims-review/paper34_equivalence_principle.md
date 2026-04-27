# Claims Review — paper34 notebooks (Phase6c3_EquivalencePrinciple)

Reviewer: claims-reviewer-v2 (notebook adaptation)
Date: 2026-04-29-0100
Targets:
- `SK_EFT_Hawking/notebooks/Phase6c3_EquivalencePrinciple_Technical.ipynb`
- `SK_EFT_Hawking/notebooks/Phase6c3_EquivalencePrinciple_Stakeholder.ipynb`
Sources of truth consulted:
- `lean/SKEFTHawking/EquivalencePrinciple.lean` (lines 196–553; 24 declarations of `theorem`)
- `src/equivalence_principle/{__init__,mechanism_classifier}.py`
- `papers/paper34_equivalence_principle/paper_draft.tex`
- `src/core/visualizations.py:8806` (`fig_ep_violation_matrix`)
- `src/core/citations.py` (`Touboul2017`, `Will2018`, `Pretko2017`, `Berezhiani2015`)
- `docs/counts.tex` (`\epThms`, `\epTests`)
- `scripts/update_counts.py:314` (`_module_thm_count_strict`)
- `SK_EFT_Hawking_Inventory_Index.md` (post-strengthening sync 2026-04-28-1130)

## Summary
- BLOCKER: 0
- REQUIRED: 1
- RECOMMENDED: 1
- INFO: 2

## Findings

### F-1: Theorem-count drift — "25 substantive theorems" claim is off-by-one (actual = 24) [REQUIRED] [class: IA]
- **Location:** Phase6c3_EquivalencePrinciple_Technical.ipynb cell `p34t-intro` (introduction); cell `p34t-8-md` (§8 Lean theorem inventory header); Phase6c3_EquivalencePrinciple_Stakeholder.ipynb cell `p34s-6-md` (§6) and cell `p34s-7-md` (§7).
- **Quote (Technical, p34t-intro):** "**Lean module:** `lean/SKEFTHawking/EquivalencePrinciple.lean` (25 substantive theorems = 13 original + 12 strengthening / 0 sorry / 0 new axioms; verified `propext, Classical.choice, Quot.sound` only via `lean_verify`)."
- **Quote (Technical, p34t-8-md):** "## 8. Lean theorem inventory (25 substantive)" ... "**Original 13 (Wave 6c.3):**" ... "**Strengthening 12 (Wave 6c.3 strengthening pass):**"
- **Quote (Stakeholder, p34s-6-md):** "The classification is encoded as 25 machine-checked Lean theorems with zero `sorry` statements."
- **Quote (Stakeholder, p34s-7-md):** "**Lean module:** `lean/SKEFTHawking/EquivalencePrinciple.lean` — 25 theorems (13 original + 12 strengthening)."
- **Issue:** The actual file `lean/SKEFTHawking/EquivalencePrinciple.lean` declares **24** theorems, not 25. The breakdown is **12 original** (lines 196–387: vestigialDifferentialCoupling_violates_WEP, vestigialReliscSTEPClass_violates_WEP, four `*_satisfies_all_EP`, violationLevel_is_function, ep_violation_is_vestigial_only, two_vestigial_mechanisms_distinct, distinct_violationLevel_implies_distinct_mechanism, vestigial_vs_fangGu_distinct_EP_profile, vestigial_microscope_violation_consistent) **+ 12 strengthening** (lines 423–553). The "13 original" claim is internally contradicted by §8's own bullet list: items 1–12 are theorems and item 13 reads "*(structural)* `EPLevel`, `EPMechanism`, `violationLevel`, `violatesAt`, `satisfiesAt` — types" — i.e., type definitions, not theorems. The aggregate "25 = 13 + 12" therefore counts the inductive type block as a theorem.

  Compounding this, `docs/counts.tex` declares `\newcommand{\epThms}{25}`, and the paper draft uses `\epThms{}` in the abstract. The drift is upstream of the notebooks: `scripts/update_counts.py::_module_thm_count_strict` (line 314) counts every line whose first column is `theorem ` or `lemma `, and line 538 of the Lean module is the docstring word-wrap "*theorem* provides that." (continuation of "this") which BOL-matches but is not a declaration. Strict grep (`grep -c "^theorem " EquivalencePrinciple.lean` returns 25) confirms the false positive.
- **Evidence:**
  - `grep -n "^theorem " lean/SKEFTHawking/EquivalencePrinciple.lean` returns 25 lines, but line 538 is `theorem provides that.` inside the docstring of `fangGu_failure_mode_is_kinematic_not_ep` (lines 531–547).
  - Verified declaration list (24 unique `theorem` declarations) at lines 196, 211, 226, 239, 252, 266, 285, 302, 326, 340, 356, 383, 423, 442, 446, 450, 454, 458, 462, 474, 495, 506, 520, 548.
  - Inventory Index sync 2026-04-27-1555 line: "Module: 24 substantive theorems + 1 marker (was 12 + 1)" — the "+1 marker" was `module_summary_marker`, which was REMOVED in the 2026-04-28-1130 strengthening pass (also recorded in the same inventory: "decorative `EquivalencePrinciple.module_summary_marker` REMOVED").
  - Stakeholder §7 reuses paper34's count macro mental model but spelled out in prose.
- **Suggested fix:** Either (a) fix `_module_thm_count_strict` to exclude docstring matches (e.g., skip lines inside `/-...-/` and `/--...-/` blocks), regenerate counts.tex so `\epThms = 24`, then update both notebooks' "25 substantive" / "13 original + 12 strengthening" prose to "24 substantive / 12 + 12"; or (b) accept the strict counter as the canonical bookkeeping number, but then update the Lean docstring at line 537–538 (re-flow so "theorem" is not at column 0 — e.g., insert a leading space or move the word) so the strict counter genuinely returns 24, and re-run `update_counts.py`. Path (a) is the structural fix. Either path then propagates: paper34 abstract recompiles via `\epThms`, both notebooks update prose, and the §8 enumeration of the technical notebook should be relabeled "**Original 12 (Wave 6c.3):**" with item 13 dropped (or moved out of the numbered list as a "Supporting type definitions" note).

### F-2: Stakeholder cell `p34s-1-code` mis-attributes vestigial-relics η as "AT the STEP target" without the projected/discussed hedge from paper abstract [RECOMMENDED] [class: SD]
- **Location:** Phase6c3_EquivalencePrinciple_Stakeholder.ipynb cell `p34s-1-code` (output line); cell `p34s-3-code` (output line); cell `p34s-4-md`.
- **Quote (p34s-1-code output):** "→ vestigial relics sit AT the STEP target, well below MICROSCOPE."
- **Quote (p34s-3-code output):** "Pattern: only the two vestigial rows show \"✗ violates\". This is a MEASURABLE classification — STEP-class precision tests can directly distinguish them."
- **Quote (p34s-4-md):** "right at the *STEP design sensitivity*."
- **Issue:** The paper34 abstract carries an explicit hedge — "at the projected design sensitivity discussed for STEP-class satellite missions" (paper_draft.tex line 41–42, post-strengthening fix per inventory 2026-04-28-1130: '"within reach" → "at the projected design sensitivity discussed for STEP-class satellite missions"'). The stakeholder notebook prose collapses this to bare "AT the STEP target" / "MEASURABLE classification — STEP-class precision tests can directly distinguish them." which reads as an existing-experiment promise rather than a projection. The technical notebook handles this correctly (cell `p34t-1-md` says "STEP-class projection η ∼ 10⁻¹⁸ (post-strengthening hedge in paper §II)" and `p34t-1-code` prints "STEP-class target ... (projected design sensitivity)"), but the stakeholder doc — which by audience is the more sensitive surface — does not mirror the hedge.
- **Evidence:**
  - paper_draft.tex line 41–42 (abstract): "...sub-MICROSCOPE and at the projected design sensitivity discussed for STEP-class satellite missions."
  - paper_draft.tex line 244–246 (Outlook): "A positive next-generation satellite-EP-test result at η ∼ 10⁻¹⁸ would corroborate the vestigial-relics mechanism..." — the paper consistently uses "next-generation"/"projected design sensitivity" framing.
  - Inventory Index 2026-04-28-1130: '"within reach" → "at the projected design sensitivity discussed for STEP-class satellite missions"' is recorded as one of the eight RECOMMENDEDs cleared.
  - `mechanism_classifier.py` line 67 docstring: "STEP_TARGET ... Next-generation EP-violation test"; line 79: "STEP-detectable" — Python annotates this as an anchor, not a current bound.
- **Suggested fix:** Update the three stakeholder cell outputs to mirror the paper-abstract hedge. Concretely:
  - `p34s-1-code`: change the printed line to `'  η ~ 10⁻¹⁸         — STEP-class **projected design sensitivity** (discussed for next-generation missions)'` and the trailing `→` summary to `'  → vestigial relics sit AT the STEP-class projected target, well below MICROSCOPE.'`
  - `p34s-3-code`: replace "MEASURABLE classification — STEP-class precision tests can directly distinguish them." with "MEASURABLE classification — at projected STEP-class design sensitivity, future missions could directly distinguish them."
  - `p34s-4-md` and `p34s-5-md`: replace bare "STEP design sensitivity" / "at the STEP target" with "projected STEP-class design sensitivity" wherever it stands as the primary descriptor.

### F-3: Technical notebook §5 explicitly cites a removed theorem with a transparency caveat that should be tightened [INFO] [class: TN]
- **Location:** Phase6c3_EquivalencePrinciple_Technical.ipynb cell `p34t-5-md`.
- **Quote:** "- `step_target_can_test_vestigial_relics` (was a P5 self-equality, REMOVED in strengthening pass; STEP=relics equality survives via inspection)."
- **Issue:** Marginal. The bullet correctly discloses that `step_target_can_test_vestigial_relics` was removed, so this is **not** stale TN drift in the failure-mode sense — but the bullet is rendered in-line with two surviving theorems (`vestigial_phase_eta_violates_microscope_bound`, `vestigial_relics_below_microscope_bound`) using the same dash-bullet structure, which a reader skimming may parse as a third surviving theorem. The §8 inventory bullet at the end already documents the same removal cleanly. The §5 bullet is therefore informational redundancy but with mild ambiguity risk.
- **Evidence:**
  - Lean grep confirms `step_target_can_test_vestigial_relics` is NOT in the file.
  - Inventory Index 2026-04-28-1130: "P5 self-equality tautology `step_target_can_test_vestigial_relics : 1.0e-18 ≤ 1.0e-18 := le_refl _` REMOVED from `EquivalencePrinciple.lean`".
  - The §8 bullet at the bottom of the technical notebook says: "Note: a P5 self-equality `step_target_can_test_vestigial_relics : 1.0e-18 ≤ 1.0e-18 := le_refl _` and a `module_summary_marker : True := trivial` were REMOVED in the post-wave audit; the substantive content survives via `vestigial_relics_below_microscope_bound`." — this is the cleaner formulation.
- **Suggested fix:** In §5 (`p34t-5-md`), change the third bullet from a same-style dash to an indented "(historical note: ...)" parenthetical or strike it entirely, since §8 already records the removal authoritatively. Suggested replacement: keep the two surviving bullets (`vestigial_phase_eta_violates_microscope_bound`, `vestigial_relics_below_microscope_bound`) only; move the removal note to a footnote-style line or omit (§8 covers it).

### F-4: Technical notebook §3 prose mis-states "four 3-conjunct ... bundles plus two `*_violates_WEP` per-mechanism theorems" — should be "four bundles plus two violators" [INFO] [class: IA]
- **Location:** Phase6c3_EquivalencePrinciple_Technical.ipynb cell `p34t-3-md`.
- **Quote:** "The original wave shipped four 3-conjunct `*_satisfies_all_EP` bundles plus two `*_violates_WEP` per-mechanism theorems. The strengthening pass replaced the bundles with single-claim `violationLevel m = some WEP` (violators) or `violationLevel m = none` (non-violators) plus a shared `violatesAt_mono` extraction lemma — eliminating P2 redundancy."
- **Issue:** The phrasing "**replaced** the bundles" overstates the strengthening-pass mechanic. Per the actual Lean module, the four `*_satisfies_all_EP` 3-conjunct bundles still exist (lines 226, 239, 252, 266 — `fangGuTorsionTrace_satisfies_all_EP`, `fractonSubdiffusion_satisfies_all_EP`, `sfdmThomasFermi_satisfies_all_EP`, `hiddenSectorZ16Singlet_satisfies_all_EP`). The strengthening pass **added** the single-claim `*_has_no_violation` forms (lines 450, 454, 458, 462) and a shared `noViolation_implies_satisfiesAt` extraction lemma (line 474), demonstrating that the bundles are derivable; it did not delete the bundles. Same for the two violators: `*_violates_WEP` (lines 196, 211) coexist with new `*_violationLevel` (lines 442, 446). The notebook's "replaced" verb suggests deletion that did not occur.
- **Evidence:**
  - `grep -n "^theorem " EquivalencePrinciple.lean` shows both `*_satisfies_all_EP` (4 entries) and `*_has_no_violation` (4 entries); both `*_violates_WEP` (2 entries) and `*_violationLevel` (2 entries) — total 12 in this cluster.
  - Inventory Index 2026-04-27-1555 sync: "Strengthening pass added 12 substantive theorems closing three 6-pattern audit findings: (1) bundle redundancy (P2) — replaced 4 redundant 3-conjunct `*_satisfies_all_EP` bundles with 6 single-claim `*_violationLevel` / `*_has_no_violation` theorems + shared `noViolation_implies_satisfiesAt` extraction lemma + `violatesAt_mono`..." — the inventory uses the same loose verb "replaced" but in a context where the old theorems are still present (count went 12→24, not 12→18→24); this is the source of the loose phrasing in the notebook.
- **Suggested fix:** Replace "replaced the bundles with single-claim..." in p34t-3-md with "added single-claim `violationLevel m = some WEP` (violators) and `violationLevel m = none` (non-violators) forms alongside the original bundles, plus a shared `violatesAt_mono` extraction lemma and `noViolation_implies_satisfiesAt` bundle-derivation lemma — demonstrating the bundles are 1-line corollaries of the single-claim forms (P2 redundancy made structurally explicit, not deleted)." Same correction is mild for the §8 inventory item 16–19, which already lists `*_has_no_violation` separately from items 3–6 (`*_satisfies_all_EP`), so §8 is consistent.

## Verifications that PASSED (no findings emitted)

The following checks were performed and confirmed clean — listed for traceability, not to inflate the findings count.

- **Constants.** MICROSCOPE_BOUND = 1e-15, STEP_TARGET = 1e-18, VESTIGIAL_PHASE_ETA_MAX = 1.0, VESTIGIAL_RELICS_ETA = 1e-18 in `mechanism_classifier.py:64,68,75,80` match every numerical citation in both notebooks.
- **6×3 matrix.** Both notebooks' tabular outputs (Technical p34t-2-code, Stakeholder p34s-3-code) reproduce `EP_VIOLATION_MATRIX` faithfully: vestigialDifferentialCoupling and vestigialReliscSTEPClass violate at all three levels; the four others satisfy at all three.
- **Theorem-name references that DO exist** (TN-resolvable): `violatesAt_mono` (line 423), `ep_violation_is_vestigial_only` (line 302), `vestigial_microscope_violation_consistent` (line 383), `non_violators_share_violationLevel` (line 520), `fangGu_failure_mode_is_kinematic_not_ep` (line 548), `vestigial_phase_eta_violates_microscope_bound` (line 495), `vestigial_relics_below_microscope_bound` (line 506), `vestigialDifferentialCoupling_violationLevel` (line 442), `vestigialReliscSTEPClass_violationLevel` (line 446), `fangGuTorsionTrace_has_no_violation` (line 450), `fractonSubdiffusion_has_no_violation` (line 454), `sfdmThomasFermi_has_no_violation` (line 458), `hiddenSectorZ16Singlet_has_no_violation` (line 462), `noViolation_implies_satisfiesAt` (line 474), `vestigialDifferentialCoupling_violates_WEP` (line 196), `vestigialReliscSTEPClass_violates_WEP` (line 211), the four `*_satisfies_all_EP` (lines 226, 239, 252, 266), `violationLevel_is_function` (line 285), `two_vestigial_mechanisms_distinct` (line 326), `distinct_violationLevel_implies_distinct_mechanism` (line 340), `vestigial_vs_fangGu_distinct_EP_profile` (line 356).
- **Removed theorems are correctly disclosed.** `step_target_can_test_vestigial_relics` and `module_summary_marker` are NOT referenced in the notebooks as if existing; both notebooks' §8 footer (Technical) explicitly notes their removal. (Stakeholder doesn't reference either, correctly.)
- **Cross-bridge to FangGu.** `fangGu_failure_mode_is_kinematic_not_ep` (line 548) imports `SKEFTHawking.FangGuTorsionDM` (line 4) and calls `fg_cdm_obstruction` in its body (line 553). Notebook prose (Technical p34t-6-md, Stakeholder p34s-6-md) consistent with the actual Lean call.
- **Citations.** `Touboul2017`, `Will2018`, `Pretko2017`, `Berezhiani2015` all resolve in `src/core/citations.py` (lines 3131, 3147, 1106, 3163). All four bibitems present in `paper_draft.tex` (lines 267, 262, 273, 278).
- **Vestigial-only structural claim.** Both notebooks correctly hedge `ep_violation_is_vestigial_only` as substrate-specific (Stakeholder §6 explicitly: "The conclusion is *substrate-specific*: \"In this substrate, EP violation is vestigial-only.\" It is not a universal claim about all DM models."). No overstatement detected.
- **`epTests = 38`.** counts.tex declaration matches `grep -c "^def test_" tests/test_equivalence_principle.py` = 38. (No drift on the test side.)
- **Visualization function.** `fig_ep_violation_matrix` at `src/core/visualizations.py:8806` imports the same four constants from `src.equivalence_principle` that the notebooks import; mechanism labels in the figure (e.g., "Vestigial differential coupling (η=1 max)", "FangGu torsion DM (w_FG=1/3, kinematic)") match the notebook prose framings.
- **Toolchain pin (TP).** No literal Lean / Mathlib / Aristotle version strings appear in either notebook; no drift to detect.
- **Hypothesis disclosure (HD).** None of the cited theorems depend on tracked `Prop` hypotheses (`HYPOTHESIS_REGISTRY`) — `EquivalencePrinciple.lean` is built on inductive types + `decide` + `norm_num`, not on tracked hypotheses. No HD finding applicable.

## Closing note

The two notebooks are structurally clean and the 6×3 matrix, constants, theorem-name references, citations, removed-theorem disclosures, and substrate-specific hedging are all correctly grounded in the pipeline. The single REQUIRED finding (F-1) is an upstream count drift in `_module_thm_count_strict` that propagates through `counts.tex` to both notebooks and the paper abstract macro; fixing it once at the counter (or at line 538 of the Lean module) corrects all downstream surfaces. F-2 is a notebook-only stakeholder-prose hedge tightening to match the paper's post-strengthening abstract revision. F-3 and F-4 are minor INFO-class clarity points.
