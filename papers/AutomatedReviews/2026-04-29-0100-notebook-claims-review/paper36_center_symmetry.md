# paper36 Center Symmetry / Walker-Wang KSS — Notebook Claims Review

**Notebooks under review**
- `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/notebooks/Phase6d1_CenterSymmetry_Technical.ipynb`
- `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/notebooks/Phase6d1_CenterSymmetry_Stakeholder.ipynb`

**Sources of truth consulted**
- `lean/SKEFTHawking/CenterSymmetryConfinement.lean` (18 substantive theorems verified by direct grep + line-by-line read)
- `lean/SKEFTHawking/SU3kFusion.lean` (`su3k1_object_count : Fintype.card SU3k1Obj = 3`)
- `src/center_symmetry/{__init__.py, polyakov_loop.py, svetitsky_yaffe.py, eta_over_s_prediction.py}`
- `src/core/visualizations.py:8956` (`fig_polyakov_loop_deconfinement`)
- `papers/paper36_center_symmetry/paper_draft.tex` (full bibliography + `\centerSymmThms` macro usage)
- `docs/counts.tex` (`\centerSymmThms = 18`, `\centerSymmTests = 28`)
- `SK_EFT_Hawking_Inventory_Index.md` (strengthening pass record)

---

## TL;DR

Both notebooks are largely clean against the live Lean source and Python module. **All 19 theorem names referenced exist** in `CenterSymmetryConfinement.lean` (Class TN: clean). The strengthening-pass removals (`ising_nu_above_0_6` / `potts_nu_below_0_6`) are properly described as "REMOVED" in the technical notebook, not cited as live theorems. The `18 substantive theorems` claim matches `\centerSymmThms{}` in `docs/counts.tex` and the live grep on the module. Numerics ($\zeta_2 = -1$, $\zeta_3 = -0.5 + 0.866i$, $\mathrm{KSS} \approx 0.0796$, $2\cdot\mathrm{KSS} \approx 0.1592$) match to printed precision.

**One IA finding (non-blocking):** stakeholder cell 4 markdown vs print disagree on the RHIC factor: markdown says "1.5–2× the universal lower bound"; the print line in cell 4 says "1.5–2.5× KSS"; the actual ratio for the cited range $\eta/s \approx 0.10\text{–}0.20$ is $1.26\text{–}2.51$, so "1.5–2.5×" is closer (but rounds the lower endpoint). Self-inconsistent but neither figure crosses a load-bearing falsifier.

**One HD/SD finding (informational):** the stakeholder framing "**Walker-Wang topological-defect transport correction** that says $\eta/s$ should sit in a narrow window" elides the tracked-Prop status disclosed in the technical notebook (and HPC-gated status disclosed in the paper). Notebook cell 6 (Honest Scope) does correctly state the Prop is "a tracked Prop — a testable prediction, not a derived consequence", so HD is partial-coverage rather than blocking.

---

## Class IA — Internal arithmetic / count drift

### IA-1 (non-blocking, intra-notebook): Stakeholder RHIC-factor inconsistency

- **Stakeholder.ipynb cell intro (line 31):** "shear-viscosity-to-entropy ratio $\eta/s \approx 0.1\text{–}0.2$, only **1.5–2×** the universal lower bound"
- **Stakeholder.ipynb cell 4 markdown (line 208):** "Quark-gluon plasma sits **1.5–2×** this value."
- **Stakeholder.ipynb cell 4 code output (line 230):** `RHIC quark-gluon plasma ≈ 0.10–0.20 (1.5–2.5× KSS)`

Arithmetic: $0.10/0.0796 \approx 1.26$ and $0.20/0.0796 \approx 2.51$. The technical notebook does not surface this prose; it appears only in the stakeholder file. The print statement in `print(f'  RHIC quark-gluon plasma     ≈ 0.10–0.20 (1.5–2.5× KSS)')` is mathematically closer (though "1.26" is the actual lower endpoint, not 1.5). The two markdown sentences ("1.5–2×") and the print line ("1.5–2.5×") are internally inconsistent.

**Verdict.** WARN. Suggest harmonizing both prose lines to "$\approx 1.3\text{–}2.5\times$" (matches print and arithmetic) OR loosening to "within a factor of $\sim$2 of the bound" if a sharper claim is not load-bearing. Not blocking — the qualitative claim "RHIC sits a factor-of-a-few above KSS" is preserved either way, and no Lean theorem depends on the precise factor.

### IA-2 (PASS): Theorem count "18 substantive"

- **Technical.ipynb cell intro (line 5):** "18 substantive theorems / 0 sorry / 0 new axioms"
- **Technical.ipynb cell 8 markdown:** "## 8. Lean theorem inventory (18 substantive)"

Live grep `grep -c "^theorem " lean/SKEFTHawking/CenterSymmetryConfinement.lean` returns **18**. Matches `\centerSymmThms{}` macro in `docs/counts.tex` (= 18). Matches paper §VI invocation. **PASS.**

### IA-3 (PASS): KSS bound numeric

`KSS_BOUND = 1/(4π) = 0.07957747154594767`. Notebook cell 4 prints `0.0795774715`. Bracket $[0.07, 0.08]$ matches Lean `KSS_bound_above_0_07` + `KSS_bound_below_0_08`. Walker-Wang upper $2\cdot\text{KSS} \approx 0.1592$ matches both notebooks' output and `H_WalkerWangTransportNearKSS` upper conjunct. **PASS.**

### IA-4 (PASS): Center phases

$\zeta_2 = -1.000000 + 0.000000i$ and $\zeta_3 = -0.500000 + 0.866025i$ both match (i) Lean theorem `centerPhase_Z2_eq_neg_one` and (ii) the analytical value $\zeta_3 = -1/2 + i\sqrt{3}/2$ (numpy printed to 6 decimals: $\sqrt{3}/2 = 0.8660254$). $\zeta_4 = +0.000000 + 1.000000i = i$ also matches $\exp(i\pi/2)$. **PASS.**

### IA-5 (PASS): Critical exponents $\nu$

Both notebooks print `ν_Ising = 0.6299, ν_Potts = 0.5`. Matches `_CRITICAL_NU` dict in `src/center_symmetry/svetitsky_yaffe.py:50`, the `critical_exponent_nu` Lean function, and `ising_nu_gt_potts_nu`. **PASS.**

---

## Class TP — Toolchain pin drift

No literal Lean / Mathlib / Aristotle version strings appear in either notebook. **PASS / N/A.**

---

## Class SD — Stealth pipeline-vs-prose drift

### SD-1 (PASS): SU(3)$_1$ object count = 3

Technical cell 6 prints `|SU(3)_1 fusion objects| = 3` and asserts $\mathbb{Z}_3$-categorification match. Live: `lean/SKEFTHawking/SU3kFusion.lean:39` proves `Fintype.card SU3k1Obj = 3 := by native_decide` and the inductive `SU3k1Obj` enumerates exactly `vac | fund | conj` (3 constructors). The fusion-rule assignments printed by the notebook (`fund ⊗ fund = conj` (1+1=2), `fund ⊗ conj = vac` (1+2=0), `conj ⊗ conj = fund` (2+2=1)) match `su3k1_f_squared`, `su3k1_f_conj`, and `su3k1_conj_squared` in `SU3kFusion.lean:73-79`. **PASS.**

### SD-2 (PASS): "drop-conjunct test passes — both halves load-bearing"

Technical cell 5 markdown asserts the Walker-Wang predicate's two conjuncts are both load-bearing. Live: `walker_wang_zero_eta_violator` falsifies the lower bound by setting $\eta/s = 0$; `walker_wang_unit_eta_violator` falsifies the upper bound by setting $\eta/s = 1$. Each falsifier closes only ONE conjunct via the absurdity. So the conjunction is genuinely binding (neither half is implied by the other). **PASS.**

---

## Class TN — Theorem-name reference drift

I checked every theorem/def name surfaced in the two notebooks against `lean/SKEFTHawking/CenterSymmetryConfinement.lean` and (for the cross-bridge) `lean/SKEFTHawking/SU3kFusion.lean`. Match summary:

| Name | Status |
|---|---|
| `centerPhase_pow_N` | EXISTS (line 59) |
| `centerPhase_norm_one` | EXISTS (line 75) |
| `centerPhase_Z2_eq_neg_one` | EXISTS (line 89) |
| `confining_invariant_under_center_action` | EXISTS (line 121) |
| `nonzero_breaks_center_invariance` | EXISTS (line 133) |
| `confining_iff_center_invariant` | EXISTS (line 154) |
| `confining_iff_magnitude_zero` | EXISTS (line 174) |
| `deconfining_implies_magnitude_positive` | EXISTS (line 184) |
| `ising_nu_gt_potts_nu` | EXISTS (line 233) |
| `KSS_bound_positive` | EXISTS (line 248) |
| `KSS_bound_below_0_08` | EXISTS (line 256) |
| `KSS_bound_above_0_07` | EXISTS (line 270) |
| `H_WalkerWangTransportNearKSS` | EXISTS (def, line 292) |
| `walker_wang_witness_at_kss_lower` | EXISTS (line 302) |
| `walker_wang_zero_eta_violator` | EXISTS (line 319) |
| `walker_wang_unit_eta_violator` | EXISTS (line 330) |
| `higher_form_discrete_iff_non_abelian` | EXISTS (line 351) |
| `su3k1_fusion_card_matches_z3_order` | EXISTS (line 366) |
| `centerAction_Z2_unit_eq_neg_one` | EXISTS (line 380) |
| `SKEFTHawking.su3k1_object_count` (cross-bridge target) | EXISTS in SU3kFusion.lean:39 |

### TN-1 (PASS): Removed-theorem references are correctly captioned

Strengthening pass removed `ising_nu_above_0_6` and `potts_nu_below_0_6` (verified: `grep` returns no matches in `CenterSymmetryConfinement.lean`). Technical notebook cell 3 markdown explicitly labels them "REMOVED in strengthening pass" and cell 8 inventory says "threshold-pair `ising_nu_above_0_6` and `potts_nu_below_0_6` REMOVED in strengthening pass". This is correct historical context, **not** a live theorem reference. **PASS.**

### TN-2 (PASS): Lean module path

Technical cell intro: `lean/SKEFTHawking/CenterSymmetryConfinement.lean`. File exists at that path. **PASS.**

### TN-3 (PASS): Cross-bridge call chain

Technical cell 6 says "calls `SKEFTHawking.su3k1_object_count` from `SU3kFusion.lean`". Verified in `CenterSymmetryConfinement.lean:368`: `theorem su3k1_fusion_card_matches_z3_order : Fintype.card SKEFTHawking.SU3k1Obj = Z3.N := by rw [SKEFTHawking.su3k1_object_count]; rfl`. The `rw` invokes the upstream theorem by exactly the name claimed. **PASS.**

---

## Class HD — Hypothesis disclosure gap

### HD-1 (partial coverage): `H_WalkerWangTransportNearKSS` disclosure

Technical cell 5 explicitly labels `H_WalkerWangTransportNearKSS` as a "Lean tracked-Prop" with a witness + two falsifiers, and cell 7 disclaims the figure shows the Walker-Wang window as a *prediction*. **PASS for technical notebook.**

Stakeholder cell 4 markdown introduces "a **Walker-Wang topological-defect transport correction** that says $\eta/s$ should sit in a narrow window" — phrasing that could be read as a derived consequence rather than a hypothesis. Cell 6 ("Honest scope") then disambiguates: "The $[\mathrm{KSS}, 2\cdot\mathrm{KSS}]$ window is a tracked Prop — a testable prediction, not a derived consequence. HPC validation in Phase 6B is gated." This matches the disclosure pattern in `paper_draft.tex` (which also calls it a "tracked structural" claim).

**Verdict.** PASS — disclosure is present, just placed in cell 6 rather than cell 4. Not a blocker; consider promoting one sentence from cell 6 (e.g., the "tracked Prop" line) into cell 4 for proximity to the introduction of the prediction. Optional polish, not a finding.

### HD-2 (PASS): SU(3)$_1$ ↔ $\mathbb{Z}_3$ identification

Technical cell 6 attributes the $|\mathrm{SU}(3)_1\,\text{Obj}| = 3$ ↔ $|\mathbb{Z}_3| = 3$ correspondence to Lean theorem `su3k1_fusion_card_matches_z3_order` and traces it back to `su3k1_object_count`. The proof is just `rw [su3k1_object_count]; rfl` — no hypothesis injection, no axioms used beyond `propext, Classical.choice, Quot.sound`. **PASS.**

---

## Citations

Notebooks reference (by name): Polyakov (1978), Svetitsky-Yaffe (1982), Pelissetto-Vicari (2002), Kos-Poland-Simmons-Duffin (2016), Kovtun-Son-Starinets (2005), Walker-Wang (2012), Kitaev (2003), Hofman-Iqbal (2018).

Bibliography in `paper_draft.tex` confirmed to contain `\bibitem` for: `Polyakov1978`, `SvetitskyYaffe1982`, `PelissettoVicari2002`, `KosPolandSimmonsDuffin2016`, `KovtunSonStarinets2005`, `HofmanIqbal2018`, `KitaevAnyons2003`.

### CIT-1 (informational / non-blocking): "Walker-Wang 2012" not in paper bibliography

The stakeholder + technical notebooks both attribute the prediction to "Walker-Wang topological-defect transport". The paper's bibliography does not include a `\bibitem{WalkerWang2012}` (PRB 85, 134306, 2012). Walker-Wang is referenced in the paper *only* via `KitaevAnyons2003` (anyon language) and `HofmanIqbal2018` (higher-form transport). The notebooks do not invoke `\cite{}` style names so this is not a Class TN finding, but the *attribution* in the stakeholder intro is asymmetric with the paper: paper cites Hofman-Iqbal as the transport prediction source; notebook says "Walker-Wang" without bibitem traceback.

**Verdict.** WARN. Recommend adding a `WalkerWang2012` bibitem (Walker & Wang, "(3+1)-dimensional topological phases and self-dual tensor networks", PRB 85, 134306) for the Walker-Wang construction proper, OR adjusting the notebook prose to match paper attribution ("Hofman-Iqbal higher-form transport" rather than "Walker-Wang topological-defect transport"). Not blocking the notebook (no Lean theorem depends on this attribution), but the prose-paper drift is concrete.

---

## Visualization (`fig_polyakov_loop_deconfinement`)

Function exists at `src/core/visualizations.py:8956`. Both notebook cells call `fig_polyakov_loop_deconfinement().show()` (technical cell 7-code, stakeholder cell 5-code). The function references the cited Lean theorems in its docstring:

```
Lean: CenterSymmetryConfinement.confining_iff_magnitude_zero,
      deconfining_implies_magnitude_positive,
      ising_nu_gt_potts_nu, KSS_bound_below_0_08,
      walker_wang_zero_eta_violator, walker_wang_unit_eta_violator.
```

All six docstring theorem references resolve in the live Lean module (verified in TN table above). Color keys `steel_blue`, `amber`, `horizon` exist in the `COLORS` dict (`visualizations.py:45-63`). **PASS.**

The figure docstring caption "Z_2 / Ising (ν = 0.6299)" and "Z_3 / 3-state Potts (ν = 0.5)" matches the literature anchors used in both notebooks. The β values (β_Ising ≈ 0.326, β_Potts ≈ 0.111) for the schematic |P| ∝ (T/T_c−1)^β scaling are noted in the function as illustrative (line 9007 comment: "Use β ≈ 0.326 (Ising) and β ≈ 0.111 (3-state Potts) as illustrative … scaling"). The technical notebook cell 7 also says "β_Ising ≈ 0.326, β_Potts ≈ 0.111" — match.

---

## Reconciliation with prior `claims_review.json` for paper36

Per `papers/paper36_center_symmetry/claims_review.json`, prior runs already auto-closed an IA blocker by macroizing `\centerSymmThms{}`. That fix is reflected in current state (`docs/counts.tex` ↔ paper ↔ live grep all = 18). No new prior findings reproduced in the notebook scan; no `non_reproducing_prior_findings` entries needed in this notebook-scoped report.

---

## Summary

- **Total findings:** 2 WARN, 0 FAIL, 0 BLOCKER.
- **Blocking issues:** none. The notebooks are submission-grade against the current Lean module + Python source + paper bibliography modulo the two warns below.
- **Non-blocking warns:**
  - **IA-1**: stakeholder RHIC-factor prose self-inconsistent (1.5–2× vs 1.5–2.5×). Pick one (1.3–2.5× is the actual range for $\eta/s \in [0.10, 0.20]$).
  - **CIT-1**: "Walker-Wang" attribution in stakeholder/technical prose without a `WalkerWang2012` bibitem in the paper. Either add the bibitem or align prose with paper's `HofmanIqbal2018` attribution.
- **All Lean theorem references resolve.** All numeric values match. Strengthening-pass removals correctly captioned. SU(3)$_1$ ↔ $\mathbb{Z}_3$ cross-bridge to `SU3kFusion.lean` clean.
- **Theorem count:** 18 substantive (matches `\centerSymmThms{}`, matches live grep on `CenterSymmetryConfinement.lean`).
- **No edits performed.** Per the instruction this report is the only file written.
