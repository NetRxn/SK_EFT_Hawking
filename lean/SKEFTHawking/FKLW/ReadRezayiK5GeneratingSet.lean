/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Track T-B.5.1 — Read-Rezayi `SU(2)_5` generating set

Instantiates the `GeneratingSet` abstraction (Phase 6u Wave 1) at the
Read-Rezayi `SU(2)_5` universal-anyon model, the next universal level
above Fibonacci (`SU(2)_3`). This is Track T-B.5's deliverable for
sub-wave T-B.5.1; downstream sub-waves T-B.5.{2..5} consume this
`GeneratingSet` instance directly.

## Headline definitions

  * `T_RR5_mat : Matrix (Fin 2) (Fin 2) ℂ` — the "level-5" phase rotation
    `T_RR5 := diag(e^{-iπ/14}, e^{iπ/14})`. The exponent `π/14 = π/(2·(k+2))`
    with `k = 5` matches the spin-1/2 braid-eigenvalue phase scale at
    `SU(2)_5` (see Read–Rezayi 1999, arXiv:cond-mat/9809384; trace
    quantities involve `2·cos(πj/(k+2)) = 2·cos(πj/7)` for `j` coprime
    to 7, which is the algebraic-integer obstruction anchor consumed
    by Track T-B.5.2 in `ReadRezayiK5InfiniteOrder.lean`).

  * `T_RR5 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)` — bundled SU(2)
    version with membership proof.

  * `readRezayiK5GeneratingSet : GeneratingSet` — the alphabet's
    `GeneratingSet` instance with
      `W := FreeGroup (Fin 2)`,
      `gens := {of 0, of 1}`,
      `ρ_hom := FreeGroup.lift (![H_SU, T_RR5] ∘ .)`,
      `gens_generate` discharged via `FreeGroup.closure_range_of`.

## Reuse from Phase 6u Track T-S

`σ_5_1 := H_SU` (the SU(2)-corrected Hadamard from
`CliffordTGeneratingSet.lean`) is reused verbatim. The Hadamard is
level-independent — it is the universal SU(2) rotation that mixes the
two computational-basis components. Only `σ_5_2 := T_RR5` is freshly
defined here, with the level-5-specific phase `π/14`.

## Read–Rezayi reference

For the SU(2)_k universal-anyon model and its braid-group
representation:

  N. Read and E. Rezayi, *Phys. Rev. B* **59** (1999), 8084;
  arXiv:cond-mat/9809384.

The closure-density of `⟨H_SU, T_RR5⟩` in SU(2) is established in
`ReadRezayiK5ClosureDenseWitness.lean` (Track T-B.5.2) following the
BMPRV Niven template (Phase 6u Track T-S.2's `CliffordTInfiniteOrder.lean`).
This file's job is the lightweight `GeneratingSet`-instance setup.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new axioms): respected.
- **Strengthening discipline**: every definition has direct downstream
  consumption (`readRezayiK5GeneratingSet` is the Track T-B.5 substrate
  for all subsequent T-B.5.{2..5} work); `T_RR5_mat_mem_specialUnitaryGroup`
  is load-bearing for the SU(2)-bundled `T_RR5`; no decorative bundled
  forms.

-/

import SKEFTHawking.FKLW.CliffordTGeneratingSet
import SKEFTHawking.FKLW.GenericSU2GeneratingSet
import Mathlib.GroupTheory.FreeGroup.Basic

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSU2

open Matrix Complex Real
open SKEFTHawking.FKLW

/-! ## 1. The level-5 phase gate `T_RR5` as a matrix

The Read–Rezayi `SU(2)_5` instance uses the SU(2)-corrected Hadamard
`H_SU` (already shipped in `CliffordTGeneratingSet.lean`) as the
first generator, and a level-5 phase rotation
`T_RR5 := diag(e^{-iπ/14}, e^{iπ/14})` as the second generator.

The choice of `π/14` matches the `SU(2)_5` braid phase scale
`π/(2(k+2))` for `k = 5`, which gives `k + 2 = 7` in the denominator.
The Niven obstruction in Track T-B.5.2 then runs against
`cos(2·(π/14)) = cos(π/7)`, whose minimal polynomial `8x³ − 4x² − 4x + 1`
is not monic over ℤ (the leading coefficient is 8, not 1), so `cos(π/7)`
is not an algebraic integer. -/

/-- **Level-5 phase gate matrix** `T_RR5 := diag(e^{-iπ/14}, e^{iπ/14})`.

The exponent `π/14 = π/(2·(k+2))` with `k = 5` is the Read–Rezayi
`SU(2)_5` braid-eigenvalue phase scale. Multiplying the diagonal
entries gives `det = 1`, so `T_RR5 ∈ SU(2)` directly (no extra global
phase needed, in contrast to `T_SU` for Clifford+T which required
multiplying by `e^{-iπ/8}` to land in SU(2)). -/
noncomputable def T_RR5_mat : Matrix (Fin 2) (Fin 2) ℂ :=
  !![Complex.exp (-(Complex.I * Real.pi / 14)), 0;
     0, Complex.exp (Complex.I * Real.pi / 14)]

/-! ## 2. SU(2) membership for `T_RR5_mat`

The proof structure mirrors `T_SU_mat_mem_specialUnitaryGroup` in
`CliffordTGeneratingSet.lean` — unitarity reduces to
`exp(z) · conj(exp(z)) = 1` for purely imaginary `z`, and `det = 1`
follows from `exp(-iπ/14) · exp(iπ/14) = exp(0) = 1`. -/

/-- For purely imaginary `z = c·I` (with `c : ℝ`), the product
`cexp(z) · conj(cexp(z)) = 1`.

This is the same helper as `cexp_imag_mul_conj_eq_one` in
`CliffordTGeneratingSet.lean`, inlined here (the original is `private`
and so not re-exportable across modules; the technique is generic and
the duplication cost is ~6 LoC). -/
private theorem cexp_imag_mul_conj_eq_one_RR5 (c : ℝ) :
    Complex.exp (c * Complex.I) * (starRingEnd ℂ) (Complex.exp (c * Complex.I)) = 1 := by
  rw [show (starRingEnd ℂ) (Complex.exp (c * Complex.I))
        = Complex.exp ((starRingEnd ℂ) (c * Complex.I)) from
      (Complex.exp_conj _).symm]
  rw [show (starRingEnd ℂ) ((c : ℂ) * Complex.I) = -(c * Complex.I) by
        rw [map_mul, Complex.conj_ofReal, Complex.conj_I]; ring]
  rw [← Complex.exp_add, show (c : ℂ) * Complex.I + (-(c * Complex.I)) = 0 from by ring,
      Complex.exp_zero]

/-- `T_RR5_mat ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ`. -/
theorem T_RR5_mat_mem_specialUnitaryGroup :
    T_RR5_mat ∈ Matrix.specialUnitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_specialUnitaryGroup_iff]
  refine ⟨?_, ?_⟩
  · -- Unitary: T_RR5 * T_RR5† = 1.
    rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [T_RR5_mat, Matrix.mul_apply, Fin.sum_univ_two]
    · -- T(0,0) · conj(T(0,0)) = 1.
      rw [show -(Complex.I * (Real.pi : ℂ) / 14) = (-(Real.pi / 14) : ℝ) * Complex.I from by
            push_cast; ring]
      exact cexp_imag_mul_conj_eq_one_RR5 (-(Real.pi / 14))
    · -- T(1,1) · conj(T(1,1)) = 1.
      rw [show Complex.I * (Real.pi : ℂ) / 14 = ((Real.pi / 14) : ℝ) * Complex.I from by
            push_cast; ring]
      exact cexp_imag_mul_conj_eq_one_RR5 (Real.pi / 14)
  · -- det = 1: e^{-iπ/14} · e^{iπ/14} = e^0 = 1.
    rw [show T_RR5_mat = !![Complex.exp (-(Complex.I * (Real.pi : ℂ) / 14)), 0;
                              0, Complex.exp (Complex.I * (Real.pi : ℂ) / 14)] from rfl]
    rw [Matrix.det_fin_two_of, mul_zero, sub_zero, ← Complex.exp_add]
    rw [show -(Complex.I * (Real.pi : ℂ) / 14) + Complex.I * (Real.pi : ℂ) / 14 = 0 from by ring]
    exact Complex.exp_zero

/-! ## 3. SU(2)-bundled level-5 phase gate

The bundled element `T_RR5 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)`
is the second generator of Read–Rezayi `SU(2)_5`. The first generator
is `H_SU` (level-independent Hadamard, reused from Clifford+T). -/

/-- **The SU(2)-bundled level-5 phase gate**. -/
noncomputable def T_RR5 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  ⟨T_RR5_mat, T_RR5_mat_mem_specialUnitaryGroup⟩

/-! ## 4. The Read–Rezayi `SU(2)_5` representation
`ρ_RR5 : FreeGroup (Fin 2) →* SU(2)` -/

/-- **`SU(2)_5` generator function**: maps `0 ↦ H_SU`, `1 ↦ T_RR5`. -/
noncomputable def readRezayiK5GenFn :
    Fin 2 → ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)
  | ⟨0, _⟩ => H_SU
  | ⟨1, _⟩ => T_RR5

/-- **The `SU(2)_5` representation**: free-group lift of `readRezayiK5GenFn`.

`ρ_RR5 (FreeGroup.of i)` returns `H_SU` for `i = 0`, `T_RR5` for
`i = 1`, and extends to all of `FreeGroup (Fin 2)` by the free-group
universal property. -/
noncomputable def ρ_RR5 :
    FreeGroup (Fin 2) →* ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) :=
  FreeGroup.lift readRezayiK5GenFn

/-- `ρ_RR5 (of 0) = H_SU`. -/
@[simp]
theorem ρ_RR5_of_0 :
    ρ_RR5 (FreeGroup.of (⟨0, by decide⟩ : Fin 2)) = H_SU := by
  unfold ρ_RR5
  rw [FreeGroup.lift_apply_of]
  rfl

/-- `ρ_RR5 (of 1) = T_RR5`. -/
@[simp]
theorem ρ_RR5_of_1 :
    ρ_RR5 (FreeGroup.of (⟨1, by decide⟩ : Fin 2)) = T_RR5 := by
  unfold ρ_RR5
  rw [FreeGroup.lift_apply_of]
  rfl

/-! ## 5. The Read–Rezayi `SU(2)_5` `GeneratingSet` instance -/

/-- **`SU(2)_5` `FreeGroup (Fin 2)` generator set** = `{of 0, of 1}`. -/
noncomputable def readRezayiK5Gens : Finset (FreeGroup (Fin 2)) :=
  {FreeGroup.of (⟨0, by decide⟩ : Fin 2),
    FreeGroup.of (⟨1, by decide⟩ : Fin 2)}

/-- The `SU(2)_5` generator set is non-empty. -/
theorem readRezayiK5Gens_nonempty : readRezayiK5Gens.Nonempty := by
  refine ⟨FreeGroup.of (⟨0, by decide⟩ : Fin 2), ?_⟩
  simp [readRezayiK5Gens]

/-- The `SU(2)_5` generators generate `FreeGroup (Fin 2)` as a group. -/
theorem readRezayiK5Gens_generate :
    Subgroup.closure (readRezayiK5Gens : Set (FreeGroup (Fin 2))) =
      (⊤ : Subgroup (FreeGroup (Fin 2))) := by
  have h_eq : (readRezayiK5Gens : Set (FreeGroup (Fin 2)))
              = Set.range (FreeGroup.of : Fin 2 → FreeGroup (Fin 2)) := by
    ext x
    constructor
    · intro hx
      simp [readRezayiK5Gens] at hx
      rcases hx with hx0 | hx1
      · exact ⟨⟨0, by decide⟩, hx0.symm⟩
      · exact ⟨⟨1, by decide⟩, hx1.symm⟩
    · rintro ⟨i, hi⟩
      simp [readRezayiK5Gens]
      fin_cases i
      · left; exact hi.symm
      · right; exact hi.symm
  rw [h_eq]
  exact FreeGroup.closure_range_of (Fin 2)

/-- **The Read–Rezayi `SU(2)_5` generating-set instance**.

Phase 6x Track T-B.5.1's deliverable. Provides the `GeneratingSet`
substrate for all subsequent Track T-B.5 work (closure-density witness,
ε₀-net, calibration discharge, bundled-strict headline). -/
noncomputable def readRezayiK5GeneratingSet : GeneratingSet where
  W := FreeGroup (Fin 2)
  Wgroup := inferInstance
  ρ_hom := ρ_RR5
  gens := readRezayiK5Gens
  gens_nonempty := readRezayiK5Gens_nonempty
  gens_generate := readRezayiK5Gens_generate

/-! ## 6. Generator membership in `H_of_G readRezayiK5GeneratingSet`

Both `H_SU` and `T_RR5` are in `H_of_G readRezayiK5GeneratingSet`
(since they are images of `FreeGroup.of 0` and `FreeGroup.of 1` under
`ρ_RR5`). Consumed by Track T-B.5.2's closure-density witness. -/

/-- `H_SU ∈ H_of_G readRezayiK5GeneratingSet`. -/
theorem H_SU_mem_H_of_G_RR5 :
    H_SU ∈ H_of_G readRezayiK5GeneratingSet := by
  apply Subgroup.le_topologicalClosure
  refine ⟨FreeGroup.of (⟨0, by decide⟩ : Fin 2), ?_⟩
  exact ρ_RR5_of_0

/-- `T_RR5 ∈ H_of_G readRezayiK5GeneratingSet`. -/
theorem T_RR5_mem_H_of_G_RR5 :
    T_RR5 ∈ H_of_G readRezayiK5GeneratingSet := by
  apply Subgroup.le_topologicalClosure
  refine ⟨FreeGroup.of (⟨1, by decide⟩ : Fin 2), ?_⟩
  exact ρ_RR5_of_1

end SKEFTHawking.FKLW.GenericSU2
