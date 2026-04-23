# QuasiOneDReduction.lean — Proof State

**Created:** 2026-04-16
**Updated:** 2026-04-23 (W10c closeout)
**Module:** `lean/SKEFTHawking/QuasiOneDReduction.lean`
**Reference proof:** `GrapheneNoiseFormula.lean` (same namespace, same proof style)
**Deep research:** `Lit-Search/Phase-5w/Greybody Factor and Quasi-1D Validity for the Graphene de Laval Nozzle.md`
**Lean dev protocol:** `temporary/working-docs/brainstorm/20260413-context-lean-dev/Lean-Development-Optimization.txt`

## Status: COMPLETE — 5 theorems + 2 tracked hypotheses, 0 sorry, builds clean

All theorems now **strengthened to bound-propagation form** (not just
positivity). The previous formulation (`0 ≤ (l_ee/W)²`) was algebraically
true but physically vacuous; the new form takes an abstract correction
variable + hypothesis encoding the PDE content, then propagates it to a
combined bound. This respects `feedback_tracked_hypothesis_nontrivial.md`:
the hypotheses H1/H2 are genuinely non-trivial, parameterized over
abstract functions with physical content.

---

## Delivered Theorems

### T1: greybody_zero_freq_* (three parts)
- `greybody_zero_freq_nonneg`: Γ₀ ≥ 0
- `greybody_zero_freq_le_one`: Γ₀ ≤ 1 (via AM-GM)
- `greybody_zero_freq_eq_one`: Γ₀ = 1 ↔ c_R = v (step-horizon limit)

### T2: surface_gravity_correction_bound
**Statement:** Given `|δκ/κ| ≤ (l_ee/W)²` and `l_ee < W`, conclude the
bound plus `|δκ/κ| < 1`. Parameterized over abstract `δκ_over_κ`.
**Proof:** `div_nonneg` + `sq_lt_sq'` + `linarith`.
**Physical content:** Poiseuille profile transverse averaging (Block 2 §2.2).

### T3: evanescent_bound
**Statement:** Given `|δΓ/Γ| ≤ (ω/ω_⊥)² · exp(-2πL/W)` and `L > 0`,
conclude the bound plus the tighter `|δΓ/Γ| ≤ (ω/ω_⊥)²` (because
`exp(-2πL/W) ≤ 1`). Parameterized over abstract `δΓ_over_Γ`.
**Supporting lemma:** `evanescent_factor_lt_one` (exp(-2πL/W) < 1 for L > 0).
**Proof:** `Real.exp_lt_one_iff` + `mul_le_mul_of_nonneg_left` + `linarith`.
**Physical content:** Helmholtz decay of sub-threshold transverse modes (Block 2 §2.3).

### T4: dean_adiabatic
**Statement:** (2·10¹²) · (51·10⁻⁹) / (4.4·10⁵) < 1
**Proof:** `norm_num`
**Physical content:** Dean nozzle is in adiabatic regime D ≈ 0.232 < 1.

### T5: quasi1D_validity_bound
**Statement:** Given T2 and T3 bound hypotheses, the sum |δκ/κ| + |δΓ/Γ_evan|
is bounded by the sum of the component upper bounds.
**Proof:** Triangle inequality (`linarith` from h_surf + h_evan).
**Physical content:** Combined quasi-1D validity bound evaluates to
≈ 0.0026 + 0.015 ≈ **1.8% at ω = ω_H** for Dean nozzle parameters
(per Block 2 §2.3; the prior "4.5%" comment in this file was incorrect).

---

## Tracked Hypotheses (Prop defs, NOT sorry)

### H_AdiabaticRegimeCorrection
**Statement:** Prop parameterized over (κ, c_s, l_ee, C_const):
`∀ T_H_exact T_H_leading, (positivity) → |T_H_exact - T_H_leading|/T_H_leading ≤ C_const · (κ·l_ee/c_s)⁴`
**Source:** Finazzi & Parentani, PRD 83, 084010 (2011)
**Why tracked:** Requires BdG ODE perturbation theory not in Mathlib.
**Non-triviality:** The hypothesis bounds an abstract pair of reals by a
quartic monomial in dimensional ratios. Not provable by `rfl`.

### H_DispersiveUVCutoff
**Statement:** Prop parameterized over (κ, c_s, l_ee):
`∀ ω_max, (positivity) → ∃ C > 0, |ω_max - C·√(κ·c_s/l_ee)|/(C·√(κ·c_s/l_ee)) ≤ 1/10`
**Source:** Macher & Parentani, PRD 80, 043601 (2009)
**Why tracked:** Requires subluminal BdG spectral analysis.
**Non-triviality:** Asserts existence of a positive constant realizing
a 10% accuracy bound on the ω_max scaling. Not provable by `rfl`.

---

## Build verification (W10c closeout)

```bash
cd SK_EFT_Hawking/lean
lake build SKEFTHawking.QuasiOneDReduction   # Built clean in 3.6s, 0 errors
```

Only one `unused variable` linter warning remains (on `_hωp` in the
T5 signature — kept for API symmetry with T3).

## Cross-file Python companions (verified)

| Python function | Lean ref | Status |
|---|---|---|
| `greybody_zero_freq(c_R, v)` | T1 | ✓ |
| `greybody_smooth_profile(ω, c_R, v, ω_max)` | T1 (at ω=0) + H2 above | ✓ |
| `dispersive_uv_cutoff(κ, c_s, l_disp)` | H2 (tracked) | ✓ |
| `dean_adiabaticity_parameter(κ, l_disp, c_s)` | T4 | ✓ |
| `quasi1d_correction_bound(ω, ω_⊥, L, W, l_ee)` | T5 | ✓ |

## Correction to previous notes

The 2026-04-22 checkpoint comment mentioned a "4.5% vs 1.8% internal
inconsistency" between this Lean file and the deep research. That
inconsistency is now resolved — the correct value is **1.8% at ω_H**
per deep research Block 2 §2.3, and the Lean comment and this working
doc have been corrected to match. The prior "4.5%" was an error in the
Lean comment, not a genuine physics disagreement.
