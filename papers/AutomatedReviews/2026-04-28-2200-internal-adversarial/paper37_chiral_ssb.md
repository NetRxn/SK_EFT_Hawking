---
paper: paper37_chiral_ssb
reviewer: adversarial-reviewer
model: claude-opus-4-7-1m
review_date: 2026-04-28T22:00:00Z
readiness_gates_version: 1
---

# Adversarial Review — paper37_chiral_ssb

## Summary

Cost-bounded review (Classes 1, 3, 4, 5, 6 only). The Lean module
`ChiralSSB_QCD.lean` ships 10 substantive theorems with load-bearing
bodies (no `rfl`/`trivial`/structural-tautology placeholders);
`gmor_pdg_match` is a real `norm_num`-backed numerical agreement at
~1 part in 10⁴. Class 1 cache-skip on all four bibitems. Two REQUIRED
issues: (a) abstract claim "the chiral-broken phase then follows from
the Gell-Mann–Oakes–Renner relation as a structural consequence" is
overstated — the Lean theorem `chiral_unbroken_violates_gmor` proves
the *contrapositive*, not the forward direction; the prose conflates
the two; the formalization does *not* construct a `QuarkCondensate` from
the GMOR relation, only rules out the chiral-unbroken phase under it.
(b) Paper §IV claims naturalness predicate has "two independent
constraints" but the Lean Prop has *three* fields (positivity +
lower bound + upper bound), and the docstring at line 192 also says "Two
independent constraints" while the body has three — a count drift inside
a single declaration.

## Findings

### 5.1 — 🟡 REQUIRED — Abstract overclaim: "chiral-broken phase follows from GMOR as structural consequence" — Lean only proves the contrapositive

- **Gate:** NarrativeGrounding (Gate 7)
- **Location:** `paper37_chiral_ssb/paper_draft.tex:34-39, 141-157`; `lean/SKEFTHawking/ChiralSSB_QCD.lean:152-163`
- **Observed:** Abstract: "The chiral-broken phase then follows from the Gell-Mann–Oakes–Renner relation `m_π² f_π² = -2 m_q ⟨q̄q⟩` as a structural consequence: the left-hand side is strictly positive for non-vanishing pion mass and decay constant, the right-hand side is strictly positive when m_q > 0, so the equation forces ⟨q̄q⟩ < 0." The Lean theorem `chiral_unbroken_violates_gmor` proves the *contrapositive* — given σ ≥ 0 (i.e., chiral-unbroken) and the GMOR equation, derives False. There is no constructive theorem that takes the GMOR relation + (m_q > 0, m_π ≠ 0, f_π ≠ 0) and *produces* a `QuarkCondensate` (i.e., a σ < 0). The structural content is "GMOR is incompatible with σ ≥ 0," which is exactly the contrapositive.
- **Evidence:** `ChiralSSB_QCD.lean:152-163`: `theorem chiral_unbroken_violates_gmor ... → False`. The forward "GMOR forces σ < 0" is provable but is not formalized as a theorem of that shape; the closest is the contrapositive shipped.
- **Expected:** Either (a) prose accurately describes the formalization as a contrapositive falsification ("the chiral-unbroken phase is ruled out by GMOR for positive quark mass and non-trivial pion sector"), or (b) ship a forward theorem `gmor_implies_chiralBroken : 0 < m_q → m_pi ≠ 0 → f_pi ≠ 0 → m_pi^2 * f_pi^2 = -2 * m_q * sigma → sigma < 0`, which is essentially `chiral_unbroken_violates_gmor` repackaged with `not_le.mp`.
- **Fix:** Either add the forward theorem (recommended, 1-2 lines), or rewrite abstract lines 34-39 to state: "the chiral-broken phase is the unique consistent phase: assuming the GMOR relation, positive quark mass, and non-trivial pion sector, the chiral-unbroken hypothesis σ ≥ 0 is structurally ruled out (Lean theorem `chiral_unbroken_violates_gmor`)."

### 7.1 — 🟡 REQUIRED — `H_TetradQuarkScalesNatural` docstring claims "two independent constraints" but the Prop has three fields

- **Gate:** AssumptionDisclosure (Gate 6) / NumericalFreshness (Gate 9, descriptor drift)
- **Location:** `paper37_chiral_ssb/paper_draft.tex:189-198`; `lean/SKEFTHawking/ChiralSSB_QCD.lean:185-194`
- **Observed:** Lean docstring at lines 185-189: "Two independent constraints (drop-conjunct test passes): (a) `sigma_scale > 0` (positivity precondition) (b) `sigma_scale / 10 ≤ v_tetrad` (lower factor-10 bound) (c) `v_tetrad ≤ 10 * sigma_scale` (upper factor-10 bound)". The numbered list has *three* items but the docstring summary line says "two independent constraints." Paper §IV at line 191-194 reproduces a 3-conjunct Prop ("0 < t ∧ 0 < q ∧ t/q ∈ [0.1, 10]") aligned with the Lean three-field structure, but does not address the count discrepancy.
- **Evidence:** `ChiralSSB_QCD.lean:188-194`: docstring says "Two", body has three conjuncts. The drop-conjunct test would actually need *three* checks (one per conjunct), not two.
- **Expected:** Either rephrase the docstring summary to "three independent constraints" or consolidate to two conjuncts (e.g., `0 < sigma_scale ∧ v_tetrad ∈ [sigma_scale/10, 10*sigma_scale]` — but `Set.Icc` membership is itself a conjunction, so the underlying count is still three).
- **Fix:** At `ChiralSSB_QCD.lean:188`, change "Two independent constraints (drop-conjunct test passes):" to "Three independent constraints (drop-conjunct test passes per conjunct):". Verify the drop-conjunct test passes for all three: (a) drop positivity → can have `sigma_scale = -1` and the bounds still hold trivially; (b) drop lower bound → can violate; (c) drop upper bound → can violate. Witness/falsifier coverage already verifies the drop-conjunct discipline, so the only fix is the docstring count.

### 5.2 — 🔵 RECOMMENDED — Abstract claim "$10$ substantive theorems" matches the file's `theorem` declaration count

- **Gate:** NumericalFreshness (Gate 9)
- **Location:** `paper37_chiral_ssb/paper_draft.tex:49, 219`
- **Observed:** Both abstract and §formalization say "$10$ substantive theorems." `grep -cE "^theorem " ChiralSSB_QCD.lean = 10`. Match.
- **Expected:** Same retrofit advisory as papers 35, 36, 38.

## Class 1 cache-skip summary

All four bibitems are major published works:
- `NambuJonaLasinio1961` — Phys. Rev. 122, 345 (1961) — `cache-skip` (foundational paper).
- `GMOR1968` — Phys. Rev. 175, 2195 (1968) — `cache-skip`.
- `FLAG2021` — arXiv:2111.09849, EPJC 82, 869 (2022) — `cache-skip`. (Note: paper says "EPJC 82, 869 (2022)" but bibitem says "FLAG Review 2021" — the year-of-review is 2021 even though the journal publication is 2022; this is consistent with FLAG-WG convention.)
- `PDG2022` — Prog. Theor. Exp. Phys. 2022, 083C01 (2022) — `cache-skip`.

## Class 4 cross-paper consistency

`GMOR1968` is referenced in paper 38 (CFL) §V cross-bridge as a companion paper, but paper 38 does *not* re-cite the GMOR1968 bibkey directly — it only references the *companion paper on the GMOR relation*. No bibkey shared, no contradiction. (The GMOR1968 bibkey is unique to paper 37.)

## Class 3 substantive-body confirmation

All 10 cited theorems inspected:
- `not_isQuarkCondensateCandidate_of_too_negative` — uses `abs_of_neg` + `abs_lt`, substantive, OK.
- `gmor_lhs_nonneg` — `positivity`, OK (trivial but substantive).
- `gmor_rhs_pos_of_quark_mass_pos` — uses `qc.sigma_neg` + `nlinarith`, substantive, OK.
- `gmor_pdg_match` — `norm_num`-backed numerical agreement at 4e-8 / 1e-4, substantive, OK.
- `chiral_unbroken_violates_gmor` — uses all four hypotheses, substantive, OK.
- `gmor_lhs_pos_iff` — biconditional with `mul_pos`, OK.
- `H_TetradQuarkScalesNatural_witness` — `linarith` from positivity, OK (modest).
- `H_TetradQuarkScalesNatural_falsifier_super_large` — `linarith` from upper bound, OK.
- `H_TetradQuarkScalesNatural_falsifier_super_small` — `linarith` from lower bound, OK.
- `njl_scalar_bounded_consistent_with_chiral_broken` — substantive cross-bridge invoking `WetterichNJL.njl_scalar_upper_bound` and `gmor_rhs_pos_of_quark_mass_pos`, OK.

No P3/P4/P5 tautology patterns detected.

## Class 6 assumption disclosure

`njl_scalar_bounded_consistent_with_chiral_broken` consumes the upstream NJL scalar-channel bound which assumes occupation-number bounds `n_x ≤ N`, `n_y ≤ N` and `0 < N`. Paper §VI prose ("a substantive upper-bound theorem requiring an occupation-number constraint") names this assumption type but does not give the specific occupation bounds. Marginal; not a finding for a structural-formalization paper.
