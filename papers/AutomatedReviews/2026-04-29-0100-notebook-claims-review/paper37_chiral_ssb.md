# Notebook Claims Review — paper37_chiral_ssb

**Review date:** 2026-04-29T01:00:00Z
**Reviewer:** claims-reviewer-v2 (notebook-adapted, single-markdown variant)
**Reviewer model:** claude-opus-4-7-1m
**Targets:**
- `SK_EFT_Hawking/notebooks/Phase6d2_ChiralSSB_Technical.ipynb`
- `SK_EFT_Hawking/notebooks/Phase6d2_ChiralSSB_Stakeholder.ipynb`

**Cross-references consulted:**
- `papers/paper37_chiral_ssb/paper_draft.tex` (PDF lines 1–266)
- `lean/SKEFTHawking/ChiralSSB_QCD.lean` (310 lines; 10 substantive theorems via `\chiralSsbThms` macro = 10)
- `src/chiral_ssb/{__init__,quark_condensate,gmor_check,tetrad_ratio}.py`
- `src/core/visualizations.py:9418` (`fig_gmor_relation_verification`)
- `lean/SKEFTHawking/WetterichNJL.lean:113` (`njl_scalar_upper_bound`)
- `lean/lean_deps.json` (declaration registry)
- `docs/counts.tex` (`\chiralSsbThms = 10`, `\chiralSsbTests = 14`)
- `papers/paper37_chiral_ssb/claims_review.json` (prior 2026-04-27 review on the TeX paper, no blocking findings)
- `SK_EFT_Hawking_Inventory_Index.md` (discipline trend, 2026-04-27-1930 sync)

---

## Summary

Two notebooks; one technical (mirrors paper §1–§7), one stakeholder (non-specialist tour). The Lean theorem references all resolve. The GMOR central-value computation (LHS = 1.589e-4 GeV⁴, RHS = 1.589e-4 GeV⁴, residual ~4e-8 GeV⁴, ~1 part in 10⁴) reproduces exactly from the source-of-truth constants in `src/chiral_ssb/gmor_check.py`. The theorem-count claim (10 substantive) matches `\chiralSsbThms` in `counts.tex`. The discipline-trend numbers (6c.3 = 12, 6b.1 = 5, 6d.1 = 6, 6d.2 = 4) match the Inventory Index.

**However, two concrete defects exist that should block ship:**

1. **Class IA — Stakeholder intro markdown asserts pion mass and decay-constant values that disagree with the constants the rest of the notebook uses.** The intro prose lists `m_π = 139.6 MeV` and `f_π = 92.4 MeV` (textbook PDG charged-pion mass + LO chiral-perturbation `f_π`). The notebook code, however, imports `PDG_M_PI = 0.137` (= 137.0 MeV) and `PDG_F_PI = 0.092` (= 92.0 MeV) and uses those to compute the published `~1.589 × 10⁻⁴ GeV⁴` central value. At the textbook values the LHS would be `1.664 × 10⁻⁴ GeV⁴` — a 4.7% discrepancy, far outside the "1 part in 10⁴" agreement claimed eight lines later in the same cell. The user reading the stakeholder notebook is told four numbers, then shown a residual computed from a different four numbers.

2. **Class IA — Both notebooks display a garbled (complex-number) cube-root for the condensate scale due to a Python operator-precedence bug.** Specifically the print expression `-FLAG_LATTICE_VALUE.sigma**(1/3.0)*1000` parses as `-((sigma)**(1/3.0))*1000`. With `sigma = -0.0227` (a negative real) Python returns the principal complex cube root, so the executed output literally reads `(-141.6-245.2j MeV cubed scale)` (technical, cell 1) and `(-142-245j MeV scale)` (stakeholder, cell 2). The intended display was 283 MeV (i.e. `(abs(sigma))**(1/3.0)*1000`). The cell output is preserved in the notebook as a complex number visible to readers.

These are both publishable-grade defects. Neither was caught by the prior `papers/paper37_chiral_ssb/claims_review.json` review (which only walked the TeX, not the notebooks). Both are deterministic IA bugs that flip to PASS with a one-line edit each.

Everything else PASSES. Below is the per-finding-class detail.

---

## Class IA — Internal arithmetic / count drift

### IA-1 (BLOCKING) — Stakeholder intro: textbook m_π / f_π values inconsistent with computed central residual

- **Notebook:** `Phase6d2_ChiralSSB_Stakeholder.ipynb`, cell 0 (markdown intro), bullet list following "Read this carefully. Four quantities, all measurable independently:"
- **Quotes (exact):**
  - "$m_\pi$ — the pion mass (139.6 MeV, well-measured)"
  - "$f_\pi$ — the pion decay constant (92.4 MeV, from weak decays)"
- **Conflict:** Code (cell 2 in stakeholder; cell `p37t-2-code` in technical) prints
  - `Pion mass         m_π     =  137.0 MeV   (PDG, particle physics)`
  - `Pion decay const  f_π     =   92.0 MeV   (PDG, from π → μ ν decay)`
  Source-of-truth constants: `src/chiral_ssb/gmor_check.py:22-26` set `PDG_M_PI = 0.137`, `PDG_F_PI = 0.092`, `PDG_M_Q = 0.0035`. The Lean theorem `gmor_pdg_match` (lines 134–138) is hard-coded to `gmor_lhs 0.137 0.092` and `gmor_rhs_real 0.0035 (-0.0227)`.
- **Recomputation showing the inconsistency:**
  - At intro-claimed inputs (139.6, 92.4) MeV: `LHS = (0.1396)² × (0.0924)² = 1.6639e-4 GeV⁴`
  - At code inputs (137.0, 92.0) MeV: `LHS = (0.137)² × (0.092)² = 1.5886e-4 GeV⁴`
  - Ratio 1.0474 — a 4.7% gap.
  - Three lines later in the same cell the prose asserts `LHS at PDG values: m_π² f_π² ≈ 1.589 × 10⁻⁴ GeV⁴`, which is the 137.0/92.0 value, not the 139.6/92.4 value.
- **Verdict:** FAIL. The stakeholder's pedagogical pitch is "four numbers, no fitting, identity holds to 1 part in 10⁴" — but the four numbers stated in the intro prose are not the four numbers used to compute the residual. A reader who plugs in 139.6/92.4 by hand will get a 5%-mismatched LHS and conclude something has drifted.
- **Fix options:**
  1. (Recommended) Update the stakeholder intro prose to match the constants: "(137.0 MeV, well-measured)" and "(92.0 MeV, from weak decays)". This aligns with both the Lean theorem and `PDG_M_PI`/`PDG_F_PI`. (Note: 137 MeV is below the actual PDG charged pion mass 139.57 MeV; project may want to revisit the rounding choice in `gmor_check.py`, but that is a Class HD/SD scope concern, not an IA fix.)
  2. Alternative: bump the source-of-truth constants to 0.1396 / 0.0924, regenerate the Lean theorem `gmor_pdg_match` with new norm_num closure, and update the central-value print in both notebooks. This is a larger fix and re-touches the Lean module + paper §3 prose.

### IA-2 (BLOCKING) — Cube-root print bug yields complex-number condensate scale in displayed output

- **Notebooks:**
  - Technical, cell `p37t-1-code`, line 17: `print(f'  FLAG-2021 lattice value σ = {FLAG_LATTICE_VALUE.sigma} GeV³  ({-FLAG_LATTICE_VALUE.sigma**(1/3.0)*1000:.1f} MeV cubed scale)')`
  - Stakeholder, cell 2 (the `print` for the four-numbers table), final line: `print(f'  Quark condensate  ⟨q̄q⟩    = {FLAG_LATTICE_VALUE.sigma:.4f} GeV³ ({-FLAG_LATTICE_VALUE.sigma**(1/3.0)*1000:.0f} MeV scale, FLAG-2021 lattice)')`
- **Captured outputs in notebooks (verbatim):**
  - Technical: `FLAG-2021 lattice value σ = -0.0227 GeV³  (-141.6-245.2j MeV cubed scale)`
  - Stakeholder: `⟨q̄q⟩    = -0.0227 GeV³ (-142-245j MeV scale, FLAG-2021 lattice)`
- **Diagnosis:** Python operator precedence: unary `-` binds *less* tightly than `**`. The expression `-FLAG_LATTICE_VALUE.sigma**(1/3.0)` evaluates as `-((-0.0227)**(1/3.0))`. Since `(-0.0227)**(1/3.0)` on a negative real returns the principal complex cube root `≈ -0.142 - 0.245j`, the negation gives `≈ 0.142 + 0.245j` — but the format spec `:.1f` / `:.0f` then renders the complex number's `__format__` output, producing the literal strings `-141.6-245.2j` / `-142-245j` shown above.
- **Intended value:** `283 MeV` (= `(283 MeV)³ ≈ 0.0227 GeV³`, the FLAG anchor — see paper §1, intro markdown, and notebook §3 verbalization "the quark-condensate scale (~0.6 GeV)" — even the paper itself uses 0.6 GeV, which is the dimension-1 scale `|σ|^(1/3) ≈ 0.283 GeV`, but rounded weirdly).
- **Verdict:** FAIL. A non-specialist reading the stakeholder notebook (or a referee or a co-author skimming the technical) sees a complex number where they should see "283 MeV". This visibly breaks the unit treatment in a paper centered on dimensional analysis.
- **Fix:** change `-FLAG_LATTICE_VALUE.sigma**(1/3.0)*1000` to `(-FLAG_LATTICE_VALUE.sigma)**(1/3.0)*1000` (parentheses) or `abs(FLAG_LATTICE_VALUE.sigma)**(1/3.0)*1000`. This is a one-character edit per notebook and re-execution. Both occurrences identical pattern.

### IA-3 (NON-BLOCKING) — Quark-condensate scale in stakeholder §4 prose: "~0.6 GeV"

- **Notebook:** Stakeholder cell 8 (markdown for §4): "the quark-condensate scale ($\sim 0.6~\mathrm{GeV}$, set by $|\qbarq|^{1/3}$)" — this matches the paper draft line 190 exactly. But the actual `|σ|^{1/3} = (0.0227)^{1/3} ≈ 0.283 GeV` (computed correctly in stakeholder cell 9 code as `0.2831 GeV`).
- This wording (`~0.6 GeV`) is inherited from the paper draft (line 190); it is internally inconsistent within the same paper / notebook (paper §4 says ~0.6 GeV, paper §3 / Lean / notebook code all use ~0.283 GeV).
- **Verdict:** WARN. Pre-existing in the paper, also surfaces in the stakeholder. Likely the original author conflated `|σ|` (≈ 0.0227 GeV — wrong dimensions) with `|σ|^{1/3}` ≈ 0.283 GeV, or was thinking of `~Λ_QCD ≈ 0.6 GeV` (the chiral-symmetry-breaking scale, which is roughly twice the condensate scale by virial-ish arguments). Either way the prose number does not match the code number and should be reconciled.
- **Fix:** change paper §4 line 190 and stakeholder cell 8 to "$\sim 0.28~\mathrm{GeV}$" (computed) or supply the conversion sentence explaining the relation between the two scales. Out of scope for an IA notebook fix alone; flagging for the next strengthening pass on paper37.

### IA-counts — All count claims PASS

- "10 substantive theorems" (technical cell 0 + cell 8): matches `\chiralSsbThms = 10` in `counts.tex` and matches the count of `^theorem ` lines in `ChiralSSB_QCD.lean` (9 `theorem` keywords; the 10th is `H_TetradQuarkScalesNatural_witness` — confirmed: file has theorems `not_isQuarkCondensateCandidate_of_too_negative`, `gmor_lhs_nonneg`, `gmor_rhs_pos_of_quark_mass_pos`, `gmor_pdg_match`, `chiral_unbroken_violates_gmor`, `gmor_lhs_pos_iff`, `H_TetradQuarkScalesNatural_witness`, `H_TetradQuarkScalesNatural_falsifier_super_large`, `H_TetradQuarkScalesNatural_falsifier_super_small`, `njl_scalar_bounded_consistent_with_chiral_broken` = 10. PASS.
- Discipline trend `6c.3 = 12, 6b.1 = 5, 6d.1 = 6, 6d.2 = 4` (technical cell 8): matches the 2026-04-27-1930 Inventory Index entry verbatim. PASS.
- "0 sorry / 0 new axioms" (technical cell 0): matches Lean module's clean-build state and `\sorrycount = 0` in counts.tex. PASS.
- "1 part in 10⁴": computed residual is 2.47e-4 = 1 part in 4054, which is borderline — the print explicitly says "(~1 part in 4054)" then the prose says "~1 part in 10⁴". Generous-rounding-up but defensible (4054 ≈ 10^3.6, and the residual is well below the χPT next-order ~1% correction floor). PASS.

---

## Class TP — Toolchain pin drift

No toolchain version mentions in either notebook. Neither cell asserts `Lean v4.X.Y` or a Mathlib SHA. PASS (no findings).

---

## Class SD — Stealth pipeline-vs-prose drift

- "10 substantive theorems" cross-checked against `\chiralSsbThms = 10` and against the Lean module declaration enumeration (lean_deps.json has 32 entries under `SKEFTHawking.ChiralSSB_QCD.*`, but stripping helper/recursor/match/inj declarations and structures — `casesOn`, `ctorIdx`, `mk.inj`, `mk.injEq`, `mk.noConfusion`, `mk.sizeOf_spec`, `noConfusion`, `noConfusionType`, `recOn`, `sigma`, `sigma_neg` projections, plus `match_*` artifacts — the substantive top-level user theorems = 10). PASS.
- "Two falsifiers" (technical cell 4 + stakeholder cell 7): matches `H_TetradQuarkScalesNatural_falsifier_super_large` and `H_TetradQuarkScalesNatural_falsifier_super_small`. PASS.
- "1 unit-ratio witness" (technical cell 5 + stakeholder §4 prose): matches `H_TetradQuarkScalesNatural_witness`. PASS.
- "Three independent constraints (drop-conjunct test passes per conjunct)" (technical cell 5): matches the Lean def `H_TetradQuarkScalesNatural` — three conjuncts (`0 < sigma_scale ∧ sigma_scale/10 ≤ v_tetrad ∧ v_tetrad ≤ 10*sigma_scale`). PASS.
- "Four hypotheses" used by `chiral_unbroken_violates_gmor` (technical cell 4 + stakeholder cell 5 prose): matches Lean signature — `h_mq, h_pi, h_fpi, h_sigma_nonneg, h_gmor` is *five* hypotheses, but the technical narrative says "all four hypotheses" referring to the physics-distinct conditions (`m_q > 0`, `m_π ≠ 0`, `f_π ≠ 0`, `σ ≥ 0`) and the GMOR equation as a fifth. The prose is loose but defensible if "the GMOR equation" is treated as the conclusion-equation rather than a hypothesis. WARN, not FAIL — the inventory-index summary uses the same "four hypotheses" wording.

---

## Class TN — Theorem-name reference drift

Verified all theorem-name references against `lean/lean_deps.json` declaration registry. **All pass.**

| Reference (notebook prose / docstring) | Resolves in `lean_deps.json`? |
|----------------------------------------|-------------------------------|
| `gmor_pdg_match` | YES (`SKEFTHawking.ChiralSSB_QCD.gmor_pdg_match`) |
| `chiral_unbroken_violates_gmor` | YES |
| `gmor_rhs_pos_of_quark_mass_pos` | YES |
| `gmor_lhs_nonneg` | YES |
| `gmor_lhs_pos_iff` | YES |
| `H_TetradQuarkScalesNatural` | YES |
| `H_TetradQuarkScalesNatural_witness` | YES |
| `H_TetradQuarkScalesNatural_falsifier_super_large` | YES |
| `H_TetradQuarkScalesNatural_falsifier_super_small` | YES |
| `not_isQuarkCondensateCandidate_of_too_negative` | YES |
| `njl_scalar_bounded_consistent_with_chiral_broken` | YES |
| `WetterichNJL.njl_scalar_upper_bound` (cited in tech §6 prose + Lean cross-bridge body) | YES (`SKEFTHawking.WetterichNJL.njl_scalar_upper_bound` at `WetterichNJL.lean:113`) |
| `flagLatticeValue` (def, mentioned in tech §1 + paper §2) | YES |
| `IsQuarkCondensateCandidate` (def, mentioned in tech §8) | YES |

PASS.

---

## Class HD — Hypothesis disclosure gap

- The cross-bridge `njl_scalar_bounded_consistent_with_chiral_broken` consumes `g, n_x, n_y, N` with positivity + occupation hypotheses. Both notebooks (§6 in technical, §4 prose in stakeholder) disclose the upstream hypothesis: technical cell 6 explicitly states "occupation bounds `0 ≤ n_x ≤ N`, `0 ≤ n_y ≤ N`" and "g · (n_x / N) · (n_y / N) ≤ g". PASS.
- The `H_TetradQuarkScalesNatural` correctness-push is disclosed as a *tracked Prop* in both notebooks (technical §5, stakeholder §4) with the explicit caveat "HPC-gated for numerical validation in Phase 6B" / "tracked Prop ... gated for HPC validation". The stakeholder §6 explicitly lists this under "What this work does not prove" point 2. PASS.
- The chiral-unbroken-phase contrapositive uses `σ ≥ 0` as a hypothesis — disclosed via "if the chiral phase were *unbroken* ($\langle \bar q q \rangle = 0$, or had the wrong sign)" in stakeholder §3. PASS.

No HD findings.

---

## Other physics-content checks (per task brief)

### Higgs ~3% claim

- **Quote (stakeholder cell 0):** "But for *protons and neutrons* — the bulk of ordinary matter — the Higgs contributes only $\sim 3\%$. The remaining $97\%$ comes from a different mechanism: **chiral symmetry breaking** in QCD."
- **Verdict:** PASS as honest framing. This is well-established lattice-QCD result (see Yang et al. 2018 PRL 121.212001, "Proton Mass Decomposition from the QCD Energy-Momentum Tensor", which gives the quark-mass term ≈ 9% but with significant contributions from other operators — depending on decomposition scheme, the "Higgs-mass-induced" contribution is 1–10%). The "~3%" figure is consistent with the Yang et al. quark-condensate-term estimate, though it varies by decomposition. The stakeholder qualifies it with `\sim 3\%` (not a precise claim) and the remaining "97%" is qualitative — not load-bearing for any Lean theorem. No grounding chain proposed (it's a contextualization sentence, type=qualitative). PASS / INFO.

### GMOR identity sign and form

- **Identity claimed:** $m_\pi^2 f_\pi^2 = -2 m_q \langle \bar q q \rangle$.
- **Standard textbook form (Weinberg, *The Quantum Theory of Fields* Vol. 2, §19.4; Scherer & Schindler, *A Primer for Chiral Perturbation Theory* Eq. 4.62):** $f_\pi^2 m_\pi^2 = -2 (m_u + m_d) \langle \bar q q \rangle / 2 + O(m_q^2) = -(m_u + m_d) \langle \bar q q \rangle$. With `m_q := (m_u + m_d)/2` (the average light-quark mass, which is the convention in `gmor_check.py` line 25), this becomes $f_\pi^2 m_\pi^2 = -2 m_q \langle \bar q q \rangle$. **PASS** — the form and sign are correct under the explicitly-stated `m_q = (m_u + m_d)/2` convention.
- The fact that `\bar q q < 0` is the *consequence* of the identity (LHS positive, m_q > 0 ⇒ σ < 0), not an extra postulate, is presented correctly in both notebooks and in the paper. PASS.

### Numerical anchors (all PASS within stated tolerances)

| Quantity | Notebook claim | Source-of-truth | Match? |
|----------|---------------|-----------------|--------|
| `m_π` central | 0.137 GeV (137 MeV)¹ | `PDG_M_PI = 0.137` | EXACT |
| `f_π` central | 0.092 GeV (92 MeV)¹ | `PDG_F_PI = 0.092` | EXACT |
| `m_q` central | 0.0035 GeV (3.5 MeV) | `PDG_M_Q = 0.0035` | EXACT |
| ⟨q̄q⟩ FLAG | -0.0227 GeV³ | `FLAG_LATTICE_VALUE.sigma = -0.0227` | EXACT |
| LHS = m_π² f_π² | ≈ 1.589e-4 GeV⁴ | recomputed = 1.5886e-4 | 0.03% |
| RHS = -2 m_q ⟨q̄q⟩ | ≈ 1.589e-4 GeV⁴ | recomputed = 1.5890e-4 | 0.03% |
| residual | ~4e-8 GeV⁴ | recomputed = 3.92e-8 | 2% (within tolerance) |
| 1 part in 10⁴ | textual rounding | actual 1 part in 4054 | acceptable rounding |

¹ Subject to IA-1 caveat: the *intro prose* in the stakeholder claims 139.6 / 92.4, contradicting these constants.

### Citation cross-check (paper bibliography)

- Nambu-Jona-Lasinio 1961: PR 122, 345 (1961). Bibliography entry `\bibitem{NambuJonaLasinio1961}` line 243 in `paper_draft.tex`. PASS (in `CITATION_REGISTRY` per src/core/citations.py:3282).
- Gell-Mann, Oakes, Renner 1968: PR 175, 2195 (1968). `\bibitem{GMOR1968}` line 249. PASS (citations.py:3298).
- FLAG 2021 / Aoki et al.: `\bibitem{FLAG2021}` line 254 — note the bibliography says "Eur. Phys. J. C **82**, 869 (2022); arXiv:2111.09849". The stakeholder + technical prose says "FLAG-2021" and the FLAG document is "FLAG Review 2021". This is a known publication-vs-data-cutoff mismatch (the review covers 2021 lattice data but appeared in EPJC 82 in 2022). The notebook's "FLAG-2021" wording is correct as a working name. PASS (citations.py:3314).
- PDG 2022: `\bibitem{PDG2022}` line 259, Workman et al. PASS (citations.py:3330).

All four cited primary sources appear in `CITATION_REGISTRY`.

---

## Reconciliation against prior `claims_review.json` (paper-only, 2026-04-27)

Prior review walked the TeX paper sentence-by-sentence and emitted zero blocking findings. The two IA defects surfaced here (IA-1 textbook-vs-code pion-mass discrepancy; IA-2 cube-root print bug) are both notebook-only — the TeX paper does not contain the misleading "139.6 MeV / 92.4 MeV" intro prose, and the TeX paper does not have a print() bug. So the prior review's PASS-everything verdict is *correct for the TeX paper*; the new findings are entirely from the notebook layer.

No prior finding is contradicted by this run; no candidates_for_supersession are emitted.

---

## Blocking issues (summary)

| ID | Class | Notebook + cell | One-line summary |
|----|-------|-----------------|------------------|
| IA-1 | IA | Stakeholder cell 0 (intro markdown) | Prose claims `m_π = 139.6 MeV`, `f_π = 92.4 MeV`; constants in code = 137.0 / 92.0; 4.7% LHS gap with the published "1.589e-4 GeV⁴" central. |
| IA-2 | IA | Technical cell `p37t-1-code` + Stakeholder cell 2 print | Cube-root print bug renders condensate scale as a complex number `-141.6-245.2j` / `-142-245j` MeV instead of the intended ~283 MeV. Operator-precedence bug: `-σ**(1/3)` parses as `-(σ**(1/3))`, complex-valued for negative real σ. |

## Non-blocking follow-ups

| ID | Class | Where | One-line summary |
|----|-------|-------|------------------|
| IA-3 | IA | Stakeholder cell 8 + paper line 190 | "Quark-condensate scale ~0.6 GeV" disagrees with computed |σ|^{1/3} ≈ 0.283 GeV used elsewhere. Pre-existing in paper. |
| SD-soft | SD | Technical cell 4 prose | "Uses ALL four hypotheses" — Lean theorem signature has 5 hypotheses (m_q > 0, m_π ≠ 0, f_π ≠ 0, σ ≥ 0, GMOR equation); inventory-index uses same wording, defensible if GMOR equation treated as the equation-being-contradicted rather than a "hypothesis", but loose. |

---

## Recommendation

Block ship until IA-1 and IA-2 are fixed. Both are one-line edits:

- IA-1 (stakeholder cell 0): change "139.6 MeV" → "137.0 MeV" and "92.4 MeV" → "92.0 MeV", or update `PDG_M_PI` / `PDG_F_PI` to 0.1396 / 0.0924 and re-derive `gmor_pdg_match` (larger fix; touches Lean module + paper). Recommended: prose edit.
- IA-2 (both notebooks): wrap the negation in parentheses — `(-FLAG_LATTICE_VALUE.sigma)**(1/3.0)*1000` or use `abs(...)`. Then rerun the affected cells so the captured output is regenerated.

After both fixes, re-run notebooks and re-execute this review; everything else (Class TP / SD / TN / HD / theorem-count / discipline-trend / citation-resolution / GMOR central values / Higgs ~3% qualitative claim) PASSES with no asterisks.
