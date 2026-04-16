# QuasiOneDReduction.lean — Proof State

**Created:** 2026-04-16
**Module:** `lean/SKEFTHawking/QuasiOneDReduction.lean`
**Reference proof:** `GrapheneNoiseFormula.lean` (same namespace, same proof style)
**Deep research:** `Lit-Search/Phase-5w/Greybody Factor and Quasi-1D Validity for the Graphene de Laval Nozzle.md`
**Lean dev protocol:** `temporary/working-docs/brainstorm/20260413-context-lean-dev/Lean-Development-Optimization.txt`

## Target: 5 theorems + 2 tracked hypotheses, 0 sorry

---

## Theorem Blueprints

### T1: greybody_zero_freq (Γ₀ identity)
**Statement:** Γ₀ = 4 c_R v / (c_R + v)²
**Type:** Algebraic identity (pure real arithmetic)
**Proof sketch:** Definition + `field_simp; ring` or direct computation. Positivity needs `0 < c_R`, `0 < v`.
**Properties to prove:**
- 0 < Γ₀ ≤ 1 (transmission probability)
- Γ₀ = 1 iff c_R = v (impedance matching)
- Γ₀ is symmetric in c_R ↔ v
**Mathlib dependencies:** Basic real analysis, `div_le_one`, `sq_nonneg`
**Status:** NOT STARTED
**Risk:** LOW — pure algebra

### T2: kappa_correction_bound (surface gravity)
**Statement:** |δκ/κ| ≤ C × (l_ee/W)²
**Type:** Algebraic bound given flow profile monotonicity
**Proof sketch:** Poiseuille profile v(x,y) = v_center(x)(1 - (2y/W)²), average κ over width. The deviation from centerline scales as y²/W². Need: `0 < W`, `0 < l_ee`, monotonicity of v_center.
**Key insight:** The bound is (l_ee/W)² ≈ 0.003, not (l_ee/W) ≈ 0.05. The quadratic scaling comes from the transverse Laplacian.
**Status:** NOT STARTED
**Risk:** MEDIUM — needs careful statement of the flow profile assumption

### T3: evanescent_suppression (transverse mode bound)
**Statement:** |δΓ/Γ| ≤ (ω/ω_perp)² × exp(-2πL/W)
**Type:** Algebraic from Helmholtz equation
**Proof sketch:** Transverse mode k_perp = nπ/W → threshold ω_perp = c_s π/W. For ω < ω_perp, evanescent decay over length L gives transmission ~ exp(-2k_perp L). The (ω/ω_perp)² factor comes from the leading-order perturbation of the 1D scattering problem.
**Mathlib dependencies:** `Real.exp_le_exp`, `Real.exp_pos`, basic inequalities
**Status:** NOT STARTED
**Risk:** MEDIUM — need to encode the perturbative structure cleanly

### T4: dean_adiabatic (D < 1 numerical check)
**Statement:** D_dean = 0.232 < 1
**Type:** Numerical inequality
**Proof sketch:** `norm_num` or `native_decide`
**Status:** NOT STARTED
**Risk:** NONE

### T5: quasi1D_combined_bound
**Statement:** |Γ_2D(ω) - Γ_1D(ω)| / Γ_1D(ω) ≤ f(l_ee/W, ω/κ)
  where f = (l_ee/W)² + (ω/ω_perp)² × exp(-2πL/W)
**Type:** Composition of T2 + T3
**Proof sketch:** Triangle inequality + T2 + T3
**Status:** NOT STARTED — depends on T2, T3
**Risk:** LOW once T2, T3 are done

---

## Tracked Hypotheses (Prop defs, NOT sorry)

### H1: AdiabaticRegimeCorrection
**Statement:** D < 1 → |δT_H/T_H| ≤ C × D⁴
**Source:** Finazzi & Parentani, PRD 85, 124027 (2012), "two regimes" paper
**Why not proved:** Requires analyzing the BdG equation with subluminal dispersion. This is a PDE eigenvalue problem, not an algebraic identity.
**Used by:** Bounding the temperature correction for the Dean nozzle
**Template:** CenterFunctor.lean `Prop` def pattern

### H2: DispersiveUVCutoff
**Statement:** ω_max ~ √(κ × c_s / l_ee)
**Source:** Macher & Parentani, PRD 79, 124008 (2009)
**Why not proved:** Requires dispersion relation analysis for the graphene acoustic mode
**Used by:** Confirming the detection band lies below the UV cutoff
**Template:** CenterFunctor.lean `Prop` def pattern

---

## Disproved Approaches (from deep research — don't retry)

- **Γ(ω) → 0 as ω → 0:** WRONG for 1D acoustic BHs. Anderson et al. proved Γ₀ is finite and profile-independent. This is the 4D Schwarzschild behavior, not the 1D analog result.
- **Greybody ~ 1/ω at low ω:** WRONG. This was the adversarial reviewer's assumption. Γ₀ = 4c_R v/(c_R+v)² ≈ 0.9994, essentially constant.

---

## Development Plan (following Lean-Development-Optimization.txt)

### Phase 1: Verify foundations (before any tactic work)
- [ ] Check GrapheneNoiseFormula.lean compiles clean (reference)
- [ ] Check that `Real.exp`, `Real.sqrt` are available in our Mathlib pin
- [ ] Verify `div_le_one` or `div_nonneg` for the Γ₀ ≤ 1 bound
- [ ] Check `sq_nonneg` availability for the AM-GM step

### Phase 2: Scaffold + diagnostics
- [ ] Write all 5 theorem statements + 2 Prop defs with `sorry` bodies
- [ ] `lake build` to confirm all statements typecheck
- [ ] `lean_goal` at each `sorry` to see the actual goal state
- [ ] Compare goal structure with GrapheneNoiseFormula.lean proofs

### Phase 3: Prove (easiest first, time-boxed)
- [ ] T4 (dean_adiabatic): `norm_num` — should be instant
- [ ] T1 (greybody_zero_freq): `field_simp; ring` or structured proof
- [ ] T1 properties (positivity, ≤ 1, symmetry)
- [ ] T3 (evanescent): structured proof with `exp` inequalities
- [ ] T2 (kappa_correction): structured proof with flow profile assumption
- [ ] T5 (combined): composition

### Phase 4: Validate
- [ ] `lean_diagnostic_messages` — zero errors, zero warnings
- [ ] `lake build` — clean
- [ ] `lean_verify` on each theorem — no suspicious axioms
