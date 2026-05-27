/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track S.2g — n-parameter exp product strict F-derivative formula

The d-generic n-parameter exp product `multiDirExpProduct` (shipped in
`GenericSUdMultiParamExpProduct.lean`) admits a strict Fréchet
derivative at 0 equal to the linear combination map
`t ↦ ∑ i, t_i • X_i`.

Ports the SU(2)-specific `threeDirProduct_hasStrictFDerivAt_zero`
pattern from `SU2BCHBracketClosure.lean` (Phase 6u/6p) to d-generic
n parameters via:

  * `expAmbient_smul_real_hasStrictDerivAt_zero` — single-direction
    derivative at SU(d) (d-generic lift of the SU(2) version).
  * `expAmbient_proj_hasStrictFDerivAt_zero` — per-direction projection
    via any `ContinuousLinearMap E →L[ℝ] ℝ` (generic in E; line 840
    of SU2 version is already E-generic).
  * Multi-fold `.mul'` chain via `Fin.induction`/`List.prod` structure,
    with `MulOpposite.op_one`, `one_smul`, `abel` killshot after
    specializing all factor values to 1.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track S provenance

Phase 6y Roadmap §"Track S detail" sub-wave S.2g (substrate part —
n-parameter exp product derivative formula; ports the SU(2) Phase
6u/6p pattern).

-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdMatrixExpDiffeo
import SKEFTHawking.FKLW.GenericSUdMultiParamExpProduct

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix NormedSpace

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## 1. Single-direction strict derivative (d-generic)

`fun a : ℝ => exp((a : ℂ) • X)` has strict derivative `X` at `0`. -/

/-- **Single-direction strict derivative**: `a ↦ exp((a : ℂ) • X)` has
strict derivative `X` at `0 : ℝ`.

d-generic lift of `SU2BCHBracketClosure.expAmbient_smul_real_hasStrictDerivAt_zero`
(SU(2) Phase 6u/6p version). Uses Mathlib's `IsScalarTower.algebraMap_smul`
to bridge ℝ-smul vs ℂ-smul, chain `hasStrictDerivAt_id.smul_const`, then
compose with `hasStrictFDerivAt_exp_zero`. -/
theorem expAmbient_smul_real_hasStrictDerivAt_zero {d : ℕ}
    (X : Matrix (Fin d) (Fin d) ℂ) :
    HasStrictDerivAt
      (fun a : ℝ => NormedSpace.exp ((a : ℂ) • X : Matrix (Fin d) (Fin d) ℂ)) X 0 := by
  -- Step 1: `gx : a ↦ (a : ℂ) • X` is linear with derivative X.
  have h_lin : (fun a : ℝ => ((a : ℂ) • X : Matrix (Fin d) (Fin d) ℂ))
      = fun a : ℝ => a • X := by
    funext a
    exact IsScalarTower.algebraMap_smul ℂ a X
  have hgx : HasStrictDerivAt (fun a : ℝ => ((a : ℂ) • X : Matrix (Fin d) (Fin d) ℂ))
      X 0 := by
    rw [h_lin]
    simpa using (hasStrictDerivAt_id (0 : ℝ)).smul_const X
  -- Step 2: exp has strict derivative identity at 0.
  have hexp : HasStrictFDerivAt (NormedSpace.exp :
      Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ)
      (1 : Matrix (Fin d) (Fin d) ℂ →L[ℝ] Matrix (Fin d) (Fin d) ℂ)
      (((0 : ℝ) : ℂ) • X) := by
    have hzero : ((0 : ℝ) : ℂ) • X = (0 : Matrix (Fin d) (Fin d) ℂ) := by simp
    rw [hzero]
    exact hasStrictFDerivAt_exp_zero
  -- Chain rule.
  have h_comp := hexp.comp_hasStrictDerivAt 0 hgx
  simpa using h_comp

/-! ## 2. Per-direction projection strict F-derivative (E-generic) -/

/-- **Per-direction strict F-derivative**: for any normed space `E` and
projection `proj : E →L[ℝ] ℝ`, `fun v => exp((proj v : ℂ) • X)` has
strict F-derivative `proj.smulRight X` at 0.

E-generic lift of the SU(2) Phase 6u/6p version. -/
theorem expAmbient_proj_hasStrictFDerivAt_zero {d : ℕ}
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (X : Matrix (Fin d) (Fin d) ℂ) (proj : E →L[ℝ] ℝ) :
    HasStrictFDerivAt (fun v : E =>
        NormedSpace.exp ((proj v : ℂ) • X : Matrix (Fin d) (Fin d) ℂ))
      (proj.smulRight X) 0 := by
  -- Inner: a ↦ exp((a : ℂ) • X) at proj 0 = 0.
  have h_inner_F : HasStrictFDerivAt
      (fun a : ℝ => NormedSpace.exp ((a : ℂ) • X : Matrix (Fin d) (Fin d) ℂ))
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) X) (proj 0) := by
    rw [proj.map_zero]
    exact (expAmbient_smul_real_hasStrictDerivAt_zero X).hasStrictFDerivAt
  -- proj has strict F-deriv = proj.
  have h_proj : HasStrictFDerivAt (proj : E → ℝ) proj 0 := proj.hasStrictFDerivAt
  -- Compose via HasStrictFDerivAt.comp.
  have h_comp := h_inner_F.comp (0 : E) h_proj
  -- Convert CLM: (smulRight 1 X).comp proj = proj.smulRight X.
  have h_CLM_eq :
      (ContinuousLinearMap.smulRight (1 : ℝ →L[ℝ] ℝ) X).comp proj
      = proj.smulRight X := by
    ext v
    simp
  rw [← h_CLM_eq]
  exact h_comp

/-! ## 3. The n-parameter linear combination map -/

/-- **Linear combination CLM** `t ↦ ∑ i, t_i • X_i` as a
ContinuousLinearMap from `(Fin n → ℝ) →L[ℝ] Matrix (Fin d) (Fin d) ℂ`.

This is the candidate strict F-derivative of `multiDirExpProduct X` at 0.
Constructed as a Finset.sum of per-coordinate `(proj i).smulRight (X i)`,
where `proj i := ContinuousLinearMap.proj i` is the i-th coordinate
projection. -/
noncomputable def multiDirDerivCLM {d n : ℕ}
    (X : Fin n → Matrix (Fin d) (Fin d) ℂ) :
    (Fin n → ℝ) →L[ℝ] Matrix (Fin d) (Fin d) ℂ :=
  ∑ i, (ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).smulRight (X i)

/-- **`multiDirDerivCLM X` evaluated at `t`** is `∑ i, t i • X i`. -/
@[simp]
theorem multiDirDerivCLM_apply {d n : ℕ}
    (X : Fin n → Matrix (Fin d) (Fin d) ℂ) (t : Fin n → ℝ) :
    multiDirDerivCLM X t = ∑ i, t i • X i := by
  unfold multiDirDerivCLM
  rw [ContinuousLinearMap.sum_apply]
  rfl

/-! ## 4. The n-parameter exp product strict F-derivative at 0

The main theorem: `multiDirExpProduct X` has strict F-derivative
`multiDirDerivCLM X` at the zero vector.

Uses Mathlib's `HasStrictFDerivAt.list_prod'` (the non-commutative-ring
multi-factor product-rule lemma) which packages the entire n-fold
product-rule chain into a single application. The `MulOpposite.op`
right-action factors evaluate to 1 at the origin (since each
`exp(0) = 1`), so the prefix and suffix products in the formula become
identity, and the derivative simplifies to the simple sum
`∑ i, f'_i = multiDirDerivCLM X`. -/

/-! ## 4. The n-parameter exp product strict F-derivative at 0

The main theorem composes the per-direction substrate via Mathlib's
`HasStrictFDerivAt.list_prod'` (non-commutative product rule).

The required scalar-tower instances are provided locally via
`NormedAlgebra.complexToReal` (which gives `NormedAlgebra ℝ
(Matrix (Fin d) (Fin d) ℂ)` from the `ℂ`-version) and
`IsScalarTower.left ℝ` (which gives the trivial `IsScalarTower ℝ ℝ X`
chain). -/

open scoped RightActions

/-- **n-parameter exp product strict F-derivative at 0** (substantive headline).

`multiDirExpProduct X` has strict Fréchet derivative `multiDirDerivCLM X`
at `(0 : Fin n → ℝ)`.

Via Mathlib's `HasStrictFDerivAt.list_prod'` (non-commutative product
rule at line 493 of `Mathlib/Analysis/Calculus/FDeriv/Mul.lean`),
applied to the per-direction factors with the explicit scalar-tower
instances. At `t = 0`, each `exp(0) = 1` so prefix and suffix products
collapse to identity; the `MulOpposite.op 1` right-action factors
simplify via `MulOpposite.op_one` + `one_smul`, leaving the simple sum
`∑ i, (proj i).smulRight (X i)` which equals `multiDirDerivCLM X` by
list-to-Fin bijection. -/
theorem multiDirExpProduct_hasStrictFDerivAt_zero {d n : ℕ}
    (X : Fin n → Matrix (Fin d) (Fin d) ℂ) :
    HasStrictFDerivAt (multiDirExpProduct X)
      (multiDirDerivCLM X) (0 : Fin n → ℝ) := by
  -- Supply the scalar-tower instances Mathlib's list_prod' needs.
  letI inst_NA_real : NormedAlgebra ℝ (Matrix (Fin d) (Fin d) ℂ) :=
    NormedAlgebra.complexToReal
  letI inst_IST : IsScalarTower ℝ ℝ (Matrix (Fin d) (Fin d) ℂ) :=
    @IsScalarTower.left ℝ _ _ _
  -- Per-factor strict F-derivatives at 0.
  have h_per : ∀ i ∈ List.finRange n,
      HasStrictFDerivAt
        (fun t : Fin n → ℝ =>
          NormedSpace.exp ((t i : ℂ) • X i : Matrix (Fin d) (Fin d) ℂ))
        ((ContinuousLinearMap.proj i :
            (Fin n → ℝ) →L[ℝ] ℝ).smulRight (X i)) 0 := by
    intro i _
    exact expAmbient_proj_hasStrictFDerivAt_zero
      (d := d) (E := Fin n → ℝ) (X i) (ContinuousLinearMap.proj i)
  -- Apply HasStrictFDerivAt.list_prod' to lift to the product derivative.
  have h_prod := HasStrictFDerivAt.list_prod' (𝕜 := ℝ) (l := List.finRange n)
    (f := fun i t =>
      NormedSpace.exp ((t i : ℂ) • X i : Matrix (Fin d) (Fin d) ℂ))
    (f' := fun i =>
      (ContinuousLinearMap.proj i :
        (Fin n → ℝ) →L[ℝ] ℝ).smulRight (X i))
    h_per
  -- h_prod has the form:
  -- HasStrictFDerivAt (fun t => (l.map (f · t)).prod)
  --   (∑ i : Fin l.length, ((l.take i).map (f · 0)).prod •
  --     f' l[i] <• ((l.drop (.succ i)).map (f · 0)).prod) 0
  -- LHS function = multiDirExpProduct X (definitionally).
  -- Derivative: at t=0, all f(·, 0) = exp(0) = 1, so prefix and suffix products
  -- collapse to 1. Derivative simplifies to ∑ i, 1 • f' l[i] <• 1 = ∑ i, f' l[i].
  -- This equals multiDirDerivCLM X via the Fin l.length → Fin n bijection.
  -- The LHS function equality:
  have h_lhs : (fun t : Fin n → ℝ =>
      (List.map (fun i =>
        NormedSpace.exp ((t i : ℂ) • X i : Matrix (Fin d) (Fin d) ℂ))
        (List.finRange n)).prod) = multiDirExpProduct X := by
    funext t
    unfold multiDirExpProduct
    rfl
  rw [h_lhs] at h_prod
  -- Now align the derivative formula with multiDirDerivCLM X via .congr_fderiv.
  refine h_prod.congr_fderiv ?_
  -- Simplify the derivative form: at t = 0, each f(·, 0) = 1.
  apply ContinuousLinearMap.ext
  intro t
  -- Goal: (∑ i : Fin l.length, prefix • f' l[i] <• suffix) t = multiDirDerivCLM X t
  simp only [ContinuousLinearMap.sum_apply, multiDirDerivCLM_apply]
  -- Simplify factor values at 0.
  simp only [Pi.zero_apply, Complex.ofReal_zero, zero_smul, NormedSpace.exp_zero]
  -- prefix/suffix lists become List.replicate _ 1; prod = 1.
  simp only [List.map_const', List.prod_replicate, one_pow]
  -- Killshot: MulOpposite.op 1 right-action collapses.
  simp only [MulOpposite.op_one, one_smul]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.proj_apply]
  -- Bridge Fin (List.finRange n).length → Fin n.
  refine Fintype.sum_equiv (finCongr (List.length_finRange (n := n)))
    (fun i : Fin (List.finRange n).length =>
      t (List.finRange n)[i] • X (List.finRange n)[i])
    (fun j : Fin n => t j • X j) ?_
  intro i
  simp [finCongr, Fin.cast, List.getElem_finRange]

end SKEFTHawking.FKLW.GenericSUd
