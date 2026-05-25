/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6u Track T-S.1 — Clifford+T generating set

Instantiates the `GeneratingSet` abstraction (Wave 1) at the canonical
Clifford+T single-qubit universal gate set.

## Headline definitions

  * `H_SU_mat : Matrix (Fin 2) (Fin 2) ℂ` — the SU(2)-corrected Hadamard
    `H_SU := (i/√2) · [[1, 1], [1, -1]]`. Note: the textbook
    `H := (1/√2) · [[1, 1], [1, -1]]` has `det = -1`, so we multiply by
    `i` to land in SU(2) (det becomes `i² · (-1) = 1`).

  * `T_SU_mat : Matrix (Fin 2) (Fin 2) ℂ` — the SU(2)-corrected T-gate
    `T_SU := diag(e^{-iπ/8}, e^{iπ/8})`. The textbook
    `T := diag(1, e^{iπ/4})` has `det = e^{iπ/4}`; we multiply by
    `e^{-iπ/8}` to land in SU(2).

  * `H_SU, T_SU : ↥(SU(2))` — the SU(2)-bundled versions with membership
    proofs.

  * `cliffordTGeneratingSet : GeneratingSet` — the `GeneratingSet`
    instance with `W := FreeGroup (Fin 2)`, `gens := {of 0, of 1}`,
    `ρ_hom := FreeGroup.lift (![H_SU, T_SU] ∘ .)`, `gens_generate`
    discharged via `FreeGroup.closure_range_of`.

  * `S_SU_mat = T_SU_mat^2` and `S_SU = T_SU^2` — the SU(2)-corrected
    S-gate as a derived element. Since `S = T²`, no separate generator
    is needed; the closure `⟨H_SU, T_SU⟩` contains S automatically.

## BMPRV reference

The closure-density of `⟨H, T⟩` in SU(2) (the substantive content of
Track T-S.2) is per:

  Boykin, Mor, Pulver, Roychowdhury, Vatan, *Quantum Inf. Comput.* 6
  (2006), 81–95; arXiv:quant-ph/9906054 §3 — the canonical "Clifford+T
  closure is dense in SU(2)" theorem.

The Lean formalization of the closure-density witness for cliffordTGeneratingSet
is shipped in `CliffordTClosureDenseWitness.lean` (Track T-S.2). This
file's job is the lightweight `GeneratingSet`-instance setup.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new axioms): respected.
- **Strengthening discipline**: every definition has direct downstream
  consumption (the `cliffordTGeneratingSet` is the Track T-S substrate
  for all subsequent T-S.2–5 work); `H_SU_mem_specialUnitaryGroup` and
  `T_SU_mem_specialUnitaryGroup` are load-bearing for the SU(2)-bundled
  versions; the `S_SU` derived equality is consumed by anyone needing
  `S` access through the generating set.

-/

import SKEFTHawking.FKLW.GenericSU2GeneratingSet
import Mathlib.GroupTheory.FreeGroup.Basic

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSU2

open Matrix Complex Real
open SKEFTHawking.FKLW

/-! ## 1. The SU(2)-corrected Clifford+T gates as matrices

We work with the SU(2)-versions (not the textbook U(2) versions) so that
both gates land in `↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)` directly. -/

/-- **SU(2)-corrected Hadamard matrix**.

`H_SU_mat := (i/√2) · [[1, 1], [1, -1]]`. The textbook Hadamard
`H := (1/√2) · [[1, 1], [1, -1]]` has `det = -1`; multiplying by `i`
gives `det(iH) = i² · (-1) = 1`, so `H_SU_mat ∈ SU(2)`. -/
noncomputable def H_SU_mat : Matrix (Fin 2) (Fin 2) ℂ :=
  ((Complex.I / Real.sqrt 2 : ℂ)) •
    !![(1 : ℂ), 1; 1, -1]

/-- **SU(2)-corrected T-gate matrix** (a.k.a. π/8-gate).

`T_SU_mat := diag(e^{-iπ/8}, e^{iπ/8})`. The textbook T-gate
`T := diag(1, e^{iπ/4})` has `det = e^{iπ/4}`; multiplying by
`e^{-iπ/8}` gives the SU(2)-corrected diagonal form above. -/
noncomputable def T_SU_mat : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (-(Complex.I * Real.pi / 8)), 0;
     0, Complex.exp (Complex.I * Real.pi / 8)]

/-- **SU(2)-corrected S-gate matrix** (= `T_SU_mat ^ 2`).

`S_SU_mat := diag(e^{-iπ/4}, e^{iπ/4})`. As a derived element
(`S = T²` in the U(2) sense), no separate generator is needed; this
definition is for downstream convenience. -/
noncomputable def S_SU_mat : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (-(Complex.I * Real.pi / 4)), 0;
     0, Complex.exp (Complex.I * Real.pi / 4)]

/-! ## 2. SU(2) membership proofs for H_SU_mat and T_SU_mat

Establishes the SU(2) membership (unitary + det = 1) for both gates,
enabling the `↥(specialUnitaryGroup (Fin 2) ℂ)` bundled forms.

We factor out two key algebraic helpers used in both proofs:
  * `sqrt_two_cast_sq` — `((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2`.
  * `cexp_imag_mul_conj` — for `z = c·i` with `c : ℝ`, the product
    `cexp(z) · conj(cexp(z)) = 1`. -/

/-- `((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2`. -/
private theorem sqrt_two_cast_sq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by
  rw [show ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = (((Real.sqrt 2 : ℝ) ^ 2 : ℝ) : ℂ) from by push_cast; ring]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  push_cast; ring

/-- For purely imaginary z (z = ±c·I·π/8), cexp(z) · conj(cexp(z)) = 1. -/
private theorem cexp_imag_mul_conj_eq_one (c : ℝ) :
    Complex.exp (c * Complex.I) * (starRingEnd ℂ) (Complex.exp (c * Complex.I)) = 1 := by
  rw [show (starRingEnd ℂ) (Complex.exp (c * Complex.I))
        = Complex.exp ((starRingEnd ℂ) (c * Complex.I)) from
      (Complex.exp_conj _).symm]
  rw [show (starRingEnd ℂ) ((c : ℂ) * Complex.I) = -(c * Complex.I) by
        rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring]
  rw [← Complex.exp_add, show (c : ℂ) * Complex.I + (-(c * Complex.I)) = 0 from by ring,
      Complex.exp_zero]

/-- `T_SU_mat ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ`. -/
theorem T_SU_mat_mem_specialUnitaryGroup :
    T_SU_mat ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · -- Unitary: T_SU * T_SU† = 1.
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [T_SU_mat, Matrix.mul_apply, Fin.sum_univ_two,
            Matrix.conjTranspose_apply, Matrix.one_apply]
    · -- T(0,0) · conj(T(0,0)) = 1.
      -- T(0,0) = cexp(-(I·π/8)) = cexp((-π/8)·I) after factor reorder.
      rw [show -(Complex.I * (Real.pi : ℂ) / 8) = (-(Real.pi / 8) : ℝ) * Complex.I from by
            push_cast; ring]
      exact cexp_imag_mul_conj_eq_one (-(Real.pi / 8))
    · -- T(1,1) · conj(T(1,1)) = 1.
      rw [show Complex.I * (Real.pi : ℂ) / 8 = ((Real.pi / 8) : ℝ) * Complex.I from by
            push_cast; ring]
      exact cexp_imag_mul_conj_eq_one (Real.pi / 8)
  · -- det = 1.
    rw [show T_SU_mat = !![Complex.exp (-(Complex.I * (Real.pi : ℂ) / 8)), 0;
                              0, Complex.exp (Complex.I * (Real.pi : ℂ) / 8)] from rfl]
    rw [Matrix.det_fin_two_of, mul_zero, sub_zero, ← Complex.exp_add]
    rw [show -(Complex.I * (Real.pi : ℂ) / 8) + Complex.I * (Real.pi : ℂ) / 8 = 0 from by ring]
    exact Complex.exp_zero

/-- `H_SU_mat ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ`. -/
theorem H_SU_mat_mem_specialUnitaryGroup :
    H_SU_mat ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · -- Unitary: H_SU · H_SU† = 1.  Reduces to: (i/√2)·(−i/√2) · M·Mᴴ where
    -- M·Mᴴ = !![2, 0; 0, 2], and (i/√2)·(−i/√2) = 1/2, so product = identity.
    rw [Matrix.mem_unitaryGroup_iff]
    -- We compute H_SU_mat * H_SU_matᴴ entrywise via Matrix.smul_apply.
    have h_sqrt_ne_zero : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
      push_cast
      exact_mod_cast (Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 2)).ne'
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [H_SU_mat, Matrix.mul_apply, Fin.sum_univ_two,
            Matrix.conjTranspose_apply, Matrix.one_apply,
            Matrix.smul_apply, smul_eq_mul, Complex.star_def,
            Complex.conj_I, Complex.conj_ofReal,
            show (((-1 : ℂ)) = (-(1 : ℂ))) from rfl]
    all_goals (
      field_simp
      rw [show ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 from sqrt_two_cast_sq,
          show (Complex.I ^ 2 : ℂ) = -1 from Complex.I_sq]
      ring)
  · -- det = 1.
    rw [show H_SU_mat
          = ((Complex.I / Real.sqrt 2 : ℂ)) • !![(1 : ℂ), 1; 1, -1] from rfl]
    rw [Matrix.det_smul]
    rw [show (!![(1 : ℂ), 1; 1, -1]).det = -2 by
          rw [Matrix.det_fin_two_of]; ring]
    have h_card : (Fintype.card (Fin 2) : ℕ) = 2 := by decide
    rw [h_card]
    rw [show ((Complex.I / Real.sqrt 2 : ℂ)) ^ 2 = -(1/2 : ℂ) by
      rw [div_pow, Complex.I_sq, sqrt_two_cast_sq]; ring]
    ring

/-! ## 3. SU(2)-bundled gate elements -/

/-- **The SU(2)-bundled Hadamard gate**. -/
noncomputable def H_SU : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  ⟨H_SU_mat, H_SU_mat_mem_specialUnitaryGroup⟩

/-- **The SU(2)-bundled T-gate**. -/
noncomputable def T_SU : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  ⟨T_SU_mat, T_SU_mat_mem_specialUnitaryGroup⟩

/-! ## 4. The Clifford+T representation `ρ_CliffT : FreeGroup (Fin 2) →* SU(2)` -/

/-- **Clifford+T generator function**: maps `0 ↦ H_SU`, `1 ↦ T_SU`. -/
noncomputable def cliffordTGenFn :
    Fin 2 → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)
  | ⟨0, _⟩ => H_SU
  | ⟨1, _⟩ => T_SU

/-- **The Clifford+T representation**: free-group lift of `cliffordTGenFn`.

`ρ_CliffT (FreeGroup.of i)` returns `H_SU` for `i = 0`, `T_SU` for `i = 1`,
and extends to all of `FreeGroup (Fin 2)` by the free-group universal
property. -/
noncomputable def ρ_CliffT :
    FreeGroup (Fin 2) →* ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  FreeGroup.lift cliffordTGenFn

/-- `ρ_CliffT (of 0) = H_SU`. -/
@[simp]
theorem ρ_CliffT_of_0 :
    ρ_CliffT (FreeGroup.of (⟨0, by decide⟩ : Fin 2)) = H_SU := by
  unfold ρ_CliffT
  rw [FreeGroup.lift_apply_of]
  rfl

/-- `ρ_CliffT (of 1) = T_SU`. -/
@[simp]
theorem ρ_CliffT_of_1 :
    ρ_CliffT (FreeGroup.of (⟨1, by decide⟩ : Fin 2)) = T_SU := by
  unfold ρ_CliffT
  rw [FreeGroup.lift_apply_of]
  rfl

/-! ## 5. The Clifford+T `GeneratingSet` instance -/

/-- **Clifford+T `FreeGroup (Fin 2)` generator set** = `{of 0, of 1}`. -/
noncomputable def cliffordTGens : Finset (FreeGroup (Fin 2)) :=
  {FreeGroup.of (⟨0, by decide⟩ : Fin 2),
    FreeGroup.of (⟨1, by decide⟩ : Fin 2)}

/-- The Clifford+T generator set is non-empty. -/
theorem cliffordTGens_nonempty : cliffordTGens.Nonempty := by
  refine ⟨FreeGroup.of (⟨0, by decide⟩ : Fin 2), ?_⟩
  simp [cliffordTGens]

/-- The Clifford+T generators generate `FreeGroup (Fin 2)` as a group.

Composes `FreeGroup.closure_range_of` (Mathlib) with the observation that
`Set.range FreeGroup.of` over `Fin 2 = {0, 1}` equals
`{of 0, of 1} = cliffordTGens`. -/
theorem cliffordTGens_generate :
    Subgroup.closure (cliffordTGens : Set (FreeGroup (Fin 2))) =
      (⊤ : Subgroup (FreeGroup (Fin 2))) := by
  -- Step 1: rewrite cliffordTGens as the image (Set.range) of FreeGroup.of.
  have h_eq : (cliffordTGens : Set (FreeGroup (Fin 2)))
              = Set.range (FreeGroup.of : Fin 2 → FreeGroup (Fin 2)) := by
    ext x
    constructor
    · intro hx
      simp [cliffordTGens] at hx
      rcases hx with hx0 | hx1
      · exact ⟨⟨0, by decide⟩, hx0.symm⟩
      · exact ⟨⟨1, by decide⟩, hx1.symm⟩
    · rintro ⟨i, hi⟩
      simp [cliffordTGens]
      fin_cases i
      · left; exact hi.symm
      · right; exact hi.symm
  rw [h_eq]
  exact FreeGroup.closure_range_of (Fin 2)

/-- **The Clifford+T generating-set instance**.

Phase 6u Track T-S.1's deliverable. Provides the `GeneratingSet`
substrate for all subsequent Track T-S work (closure-density witness,
ε₀-net, calibration discharge, headline). -/
noncomputable def cliffordTGeneratingSet : GeneratingSet where
  W := FreeGroup (Fin 2)
  Wgroup := inferInstance
  ρ_hom := ρ_CliffT
  gens := cliffordTGens
  gens_nonempty := cliffordTGens_nonempty
  gens_generate := cliffordTGens_generate

/-! ## 6. S-gate as a derived element

Since `S = T²` (up to phase), the SU(2)-corrected `S_SU` is `T_SU²`.
This is a derived value, not a separate generator. -/

/-- **`S_SU` as a derived element**: `S_SU := T_SU²`. -/
noncomputable def S_SU : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  T_SU ^ 2

/-! ## 7. Generator membership in `H_of_G cliffordTGeneratingSet`

Both H_SU and T_SU are in `H_of_G cliffordTGeneratingSet` (since they are
images of `FreeGroup.of 0` and `FreeGroup.of 1` under `ρ_CliffT`). -/

/-- `H_SU ∈ H_of_G cliffordTGeneratingSet`. -/
theorem H_SU_mem_H_of_G_cliffordT :
    H_SU ∈ H_of_G cliffordTGeneratingSet := by
  apply Subgroup.le_topologicalClosure
  refine ⟨FreeGroup.of (⟨0, by decide⟩ : Fin 2), ?_⟩
  -- ρ_CliffT (of 0) = H_SU
  exact ρ_CliffT_of_0

/-- `T_SU ∈ H_of_G cliffordTGeneratingSet`. -/
theorem T_SU_mem_H_of_G_cliffordT :
    T_SU ∈ H_of_G cliffordTGeneratingSet := by
  apply Subgroup.le_topologicalClosure
  refine ⟨FreeGroup.of (⟨1, by decide⟩ : Fin 2), ?_⟩
  exact ρ_CliffT_of_1

/-- `S_SU ∈ H_of_G cliffordTGeneratingSet` (as a derived element T_SU²). -/
theorem S_SU_mem_H_of_G_cliffordT :
    S_SU ∈ H_of_G cliffordTGeneratingSet := by
  unfold S_SU
  rw [sq]
  exact (H_of_G cliffordTGeneratingSet).mul_mem
    T_SU_mem_H_of_G_cliffordT T_SU_mem_H_of_G_cliffordT

end SKEFTHawking.FKLW.GenericSU2
