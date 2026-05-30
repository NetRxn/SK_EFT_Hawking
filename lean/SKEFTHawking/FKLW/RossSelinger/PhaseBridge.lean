/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item G — the KMM-gate → FreeGroup map (phase-bridge defs)

KMM exact synthesis produces a `List CliffordTGate` (8-gate ADT over the U(2) ring
`ZOmegaSqrt2`); the SK headline's `ρ_CliffT` consumes a `FreeGroup (Fin 2)` word
(`of 0 = H_SU`, `of 1 = T_SU`, the two SU(2) generators). This file ships the
translation `gateWord : CliffordTGate → FreeGroup (Fin 2)` and its list lift
`freeword`, plus the per-gate global phase `gatePhase`/`phaseProd` that relates the
two pictures:

  `toComplexMat (interp gs) = phaseProd gs • ρ_CliffT (freeword gs)`     (the bridge)

The phase is unavoidable: KMM gates are `U(2)` (det `ωᵏ`), `ρ_CliffT` is `SU(2)`. Per
gate `toComplexMat (gateMatrix g) = gatePhase g • ρ_CliffT (gateWord g)` with
`gatePhase g = e^{iπk/8}` (a 16th root, ∉ `ℤ[ω][1/√2]`). For a `det = 1` word — the
shape Ross-Selinger assembles — `phaseProd gs = ±1`, and `ρ_CliffT (H·H) = -I` makes
the residual sign `HH`-correctable.

**Validated** `scripts/phase_bridge_validation.py` (0/2000 failures, incl. the ±1
reduction). The per-gate `toComplexMat (gateMatrix g) = gatePhase g • ρ_CliffT (gateWord g)`
identities and the word-level bridge are the next increment (this file ships the
underlying definitions).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.ComplexEmbeddingMatrix
import SKEFTHawking.FKLW.CliffordTGeneratingSet

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

open CliffordTGate

/-- The two SU(2) generators as `FreeGroup (Fin 2)` letters. -/
abbrev fgH : FreeGroup (Fin 2) := FreeGroup.of (⟨0, by decide⟩ : Fin 2)
/-- The `T` generator letter. -/
abbrev fgT : FreeGroup (Fin 2) := FreeGroup.of (⟨1, by decide⟩ : Fin 2)

/-- **KMM gate → `FreeGroup (Fin 2)` word** over the SU(2) generators `H_SU = of 0`,
`T_SU = of 1` (validated, `scripts/phase_bridge_validation.py`):
`H↦H, T↦T, S↦T², Z↦T⁴, X↦H·T⁴·H, Y↦X·Z-word, id/ω↦1`. The global phase the U(2)
`gateMatrix` carries over the SU(2) image is tracked by `gatePhase`. -/
def gateWord : CliffordTGate → FreeGroup (Fin 2)
  | .H => fgH
  | .T => fgT
  | .S => fgT ^ 2
  | .Z => fgT ^ 4
  | .X => fgH * fgT ^ 4 * fgH
  | .Y => (fgH * fgT ^ 4 * fgH) * fgT ^ 4
  | .id => 1
  | .omega => 1

/-- **The per-gate global phase** `gatePhase g ∈ U(1)` with
`toComplexMat (gateMatrix g) = gatePhase g • ρ_CliffT (gateWord g)` (validated). A
power of `e^{iπ/8}`; not in `ℤ[ω][1/√2]`, hence valued in `ℂ`. -/
noncomputable def gatePhase : CliffordTGate → ℂ
  | .H => -Complex.I
  | .T => Complex.exp (Real.pi / 8 * Complex.I)
  | .S => ZOmega.omegaC
  | .Z => Complex.I
  | .X => -Complex.I
  | .Y => Complex.I
  | .id => 1
  | .omega => ZOmega.omegaC

/-- **The FreeGroup word of a KMM gate list** (the map `cliffordTBaseFinder_kmm` uses:
`List CliffordTGate → FreeGroup (Fin 2)`). -/
def freeword (gs : List CliffordTGate) : FreeGroup (Fin 2) := (gs.map gateWord).prod

/-- **The accumulated global phase of a KMM gate list** (`= ±1` for `det`-1 words). -/
noncomputable def phaseProd (gs : List CliffordTGate) : ℂ := (gs.map gatePhase).prod

@[simp] theorem freeword_nil : freeword [] = 1 := rfl
@[simp] theorem freeword_cons (g : CliffordTGate) (gs : List CliffordTGate) :
    freeword (g :: gs) = gateWord g * freeword gs := by
  simp [freeword]
@[simp] theorem phaseProd_nil : phaseProd [] = 1 := rfl
@[simp] theorem phaseProd_cons (g : CliffordTGate) (gs : List CliffordTGate) :
    phaseProd (g :: gs) = gatePhase g * phaseProd gs := by
  simp [phaseProd]

/-! ## Per-gate phase-bridge identities (generators)

`toComplexMat (gateMatrix g) = gatePhase g • ρ_CliffT (gateWord g)` — the per-gate
bridge connecting the U(2) KMM gate to its SU(2) `ρ_CliffT` image (validated for all 8;
the two generators `H, T` shipped here, the derived gates `S/Z/X/Y/id/ω` are the next
increment via the same `eta_fin_two` + `congr` RHS-value pattern). -/

open scoped Matrix in
open SKEFTHawking.FKLW.GenericSU2 in
/-- **H phase-bridge identity**: `toComplexMat (gateMatrix H) = (-i) • ρ_CliffT (of 0)`. -/
theorem toComplexMat_gateMatrix_eq_H :
    toComplexMat (gateMatrix CliffordTGate.H)
      = gatePhase CliffordTGate.H • ((ρ_CliffT (gateWord CliffordTGate.H) :
          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [show gatePhase CliffordTGate.H = -Complex.I from rfl,
      show gateWord CliffordTGate.H = fgH from rfl, fgH, ρ_CliffT_of_0,
      toComplexMat_gateMatrix_H]
  show _ = (-Complex.I) • H_SU_mat
  rw [Matrix.eta_fin_two ((-Complex.I) • H_SU_mat), H_SU_mat]
  congr 1 <;>
    (simp only [Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
      smul_eq_mul, mul_one, mul_neg, Complex.ofReal_inv]
     rw [show -Complex.I * (Complex.I / (↑(Real.sqrt 2))) = (↑(Real.sqrt 2))⁻¹ from by
       rw [div_eq_mul_inv, ← mul_assoc, neg_mul, Complex.I_mul_I]; ring])

open scoped Matrix in
open SKEFTHawking.FKLW.GenericSU2 in
/-- **T phase-bridge identity**: `toComplexMat (gateMatrix T) = e^{iπ/8} • ρ_CliffT (of 1)`. -/
theorem toComplexMat_gateMatrix_eq_T :
    toComplexMat (gateMatrix CliffordTGate.T)
      = gatePhase CliffordTGate.T • ((ρ_CliffT (gateWord CliffordTGate.T) :
          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h00 : Complex.exp (↑Real.pi / 8 * Complex.I) * Complex.exp (-(Complex.I * ↑Real.pi / 8)) = 1 := by
    rw [← Complex.exp_add,
      show (↑Real.pi / 8 * Complex.I + -(Complex.I * ↑Real.pi / 8)) = 0 from by ring, Complex.exp_zero]
  have h11 : Complex.exp (↑Real.pi / 8 * Complex.I) * Complex.exp (Complex.I * ↑Real.pi / 8)
      = ZOmega.omegaC := by rw [← Complex.exp_add, ZOmega.omegaC]; congr 1; ring
  rw [show gatePhase CliffordTGate.T = Complex.exp (Real.pi / 8 * Complex.I) from rfl,
      show gateWord CliffordTGate.T = fgT from rfl, fgT, ρ_CliffT_of_1,
      toComplexMat_gateMatrix_T]
  show _ = (Complex.exp (Real.pi / 8 * Complex.I)) • T_SU_mat
  rw [Matrix.eta_fin_two ((Complex.exp (Real.pi / 8 * Complex.I)) • T_SU_mat), T_SU_mat]
  congr 1 <;>
    simp only [Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply,
      smul_eq_mul, mul_zero, h00, h11]

open scoped Matrix in
open SKEFTHawking.FKLW.GenericSU2 in
/-- `ρ_CliffT (fgT^k)` embeds to `T_SU_mat^k` (`ρ_CliffT (of 1) = T_SU`, coe is a monoid hom). -/
theorem ρ_CliffT_fgT_pow (k : ℕ) :
    ((ρ_CliffT (fgT ^ k) : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
      Matrix (Fin 2) (Fin 2) ℂ) = T_SU_mat ^ k := by
  rw [map_pow, ρ_CliffT_of_1, SubmonoidClass.coe_pow]; rfl

open scoped Matrix in
open SKEFTHawking.FKLW.GenericSU2 in
/-- **id phase-bridge identity**: `toComplexMat (gateMatrix id) = 1 • ρ_CliffT 1`. -/
theorem toComplexMat_gateMatrix_eq_id :
    toComplexMat (gateMatrix CliffordTGate.id)
      = gatePhase CliffordTGate.id • ((ρ_CliffT (gateWord CliffordTGate.id) :
          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [show gatePhase CliffordTGate.id = 1 from rfl, show gateWord CliffordTGate.id = 1 from rfl,
      map_one, OneMemClass.coe_one, one_smul, toComplexMat_gateMatrix_id, Matrix.one_fin_two]

open scoped Matrix in
open SKEFTHawking.FKLW.GenericSU2 in
/-- **ω phase-bridge identity**: `toComplexMat (gateMatrix ω) = e^{iπ/4} • ρ_CliffT 1`. -/
theorem toComplexMat_gateMatrix_eq_omega :
    toComplexMat (gateMatrix CliffordTGate.omega)
      = gatePhase CliffordTGate.omega • ((ρ_CliffT (gateWord CliffordTGate.omega) :
          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) := by
  rw [show gatePhase CliffordTGate.omega = ZOmega.omegaC from rfl,
      show gateWord CliffordTGate.omega = 1 from rfl, map_one, OneMemClass.coe_one,
      toComplexMat_gateMatrix_omega,
      Matrix.eta_fin_two (ZOmega.omegaC • (1 : Matrix (Fin 2) (Fin 2) ℂ))]
  congr 1 <;> simp [Matrix.smul_apply, Matrix.one_apply]

open scoped Matrix in
open SKEFTHawking.FKLW.GenericSU2 in
/-- **S phase-bridge identity**: `toComplexMat (gateMatrix S) = e^{iπ/4} • ρ_CliffT (of 1)²`. -/
theorem toComplexMat_gateMatrix_eq_S :
    toComplexMat (gateMatrix CliffordTGate.S)
      = gatePhase CliffordTGate.S • ((ρ_CliffT (gateWord CliffordTGate.S) :
          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have e1 : T_SU_mat ^ 2 = !![Complex.exp (-(Complex.I * ↑Real.pi / 4)), 0;
      0, Complex.exp (Complex.I * ↑Real.pi / 4)] := by
    rw [sq, T_SU_mat, Matrix.eta_fin_two (_ * _)]
    congr 1 <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.of_apply, mul_zero, zero_mul, add_zero, zero_add, ← Complex.exp_add] <;>
      congr 1 <;> ring
  have h0 : ZOmega.omegaC * Complex.exp (-(Complex.I * ↑Real.pi / 4)) = 1 := by
    rw [ZOmega.omegaC, ← Complex.exp_add,
      show (↑Real.pi / 4 * Complex.I + -(Complex.I * ↑Real.pi / 4)) = 0 from by ring, Complex.exp_zero]
  have h1 : ZOmega.omegaC * Complex.exp (Complex.I * ↑Real.pi / 4) = Complex.I := by
    rw [ZOmega.omegaC, ← Complex.exp_add,
      show (↑Real.pi / 4 * Complex.I + Complex.I * ↑Real.pi / 4) = ↑(Real.pi / 2) * Complex.I from by
        push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
      Real.sin_pi_div_two]; push_cast; ring
  rw [show gatePhase CliffordTGate.S = ZOmega.omegaC from rfl,
      show gateWord CliffordTGate.S = fgT ^ 2 from rfl, ρ_CliffT_fgT_pow,
      toComplexMat_gateMatrix_S, e1, Matrix.eta_fin_two (ZOmega.omegaC • _)]
  congr 1 <;> simp only [Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.of_apply, smul_eq_mul, mul_zero, h0, h1]

open scoped Matrix in
open SKEFTHawking.FKLW.GenericSU2 in
/-- **Z phase-bridge identity**: `toComplexMat (gateMatrix Z) = i • ρ_CliffT (of 1)⁴`. -/
theorem toComplexMat_gateMatrix_eq_Z :
    toComplexMat (gateMatrix CliffordTGate.Z)
      = gatePhase CliffordTGate.Z • ((ρ_CliffT (gateWord CliffordTGate.Z) :
          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have e2 : T_SU_mat ^ 2 = !![Complex.exp (-(Complex.I * ↑Real.pi / 4)), 0;
      0, Complex.exp (Complex.I * ↑Real.pi / 4)] := by
    rw [sq, T_SU_mat, Matrix.eta_fin_two (_ * _)]
    congr 1 <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.of_apply, mul_zero, zero_mul, add_zero, zero_add, ← Complex.exp_add] <;>
      congr 1 <;> ring
  have e1 : T_SU_mat ^ 4 = !![Complex.exp (-(Complex.I * ↑Real.pi / 2)), 0;
      0, Complex.exp (Complex.I * ↑Real.pi / 2)] := by
    rw [show (4:ℕ) = 2 + 2 from rfl, pow_add, e2, Matrix.eta_fin_two (_ * _)]
    congr 1 <;>
      simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.of_apply, mul_zero, zero_mul, add_zero, zero_add, ← Complex.exp_add] <;>
      congr 1 <;> ring
  have h0 : Complex.I * Complex.exp (-(Complex.I * ↑Real.pi / 2)) = 1 := by
    rw [show -(Complex.I * ↑Real.pi / 2) = (↑(-(Real.pi / 2)) * Complex.I) from by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
      Real.cos_pi_div_two, Real.sin_pi_div_two]; push_cast; linear_combination -Complex.I_mul_I
  have h1 : Complex.I * Complex.exp (Complex.I * ↑Real.pi / 2) = -1 := by
    rw [show (Complex.I * ↑Real.pi / 2) = (↑(Real.pi / 2) * Complex.I) from by push_cast; ring,
      Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
      Real.sin_pi_div_two]; push_cast; linear_combination Complex.I_mul_I
  rw [show gatePhase CliffordTGate.Z = Complex.I from rfl,
      show gateWord CliffordTGate.Z = fgT ^ 4 from rfl, ρ_CliffT_fgT_pow,
      toComplexMat_gateMatrix_Z, e1, Matrix.eta_fin_two (Complex.I • _)]
  congr 1 <;> simp only [Matrix.smul_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.of_apply, smul_eq_mul, mul_zero, h0, h1]

open scoped Matrix in
open SKEFTHawking.FKLW.GenericSU2 in
/-- `T_SU_mat⁴ = diag(-i, i)` (= `diag(e^{-iπ/2}, e^{iπ/2})`). -/
theorem T_SU_mat_pow_four : T_SU_mat ^ 4 = !![-Complex.I, 0; 0, Complex.I] := by
  have e1 : T_SU_mat ^ 4 = !![Complex.exp (-(Complex.I * ↑Real.pi / 2)), 0;
      0, Complex.exp (Complex.I * ↑Real.pi / 2)] := by
    have e2 : T_SU_mat ^ 2 = !![Complex.exp (-(Complex.I * ↑Real.pi / 4)), 0;
        0, Complex.exp (Complex.I * ↑Real.pi / 4)] := by
      rw [sq, T_SU_mat, Matrix.eta_fin_two (_ * _)]
      congr 1 <;> simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.of_apply, mul_zero, zero_mul, add_zero, zero_add,
        ← Complex.exp_add] <;> congr 1 <;> ring
    rw [show (4:ℕ) = 2 + 2 from rfl, pow_add, e2, Matrix.eta_fin_two (_ * _)]
    congr 1 <;> simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.of_apply, mul_zero, zero_mul, add_zero, zero_add,
      ← Complex.exp_add] <;> congr 1 <;> ring
  rw [e1,
    show Complex.exp (-(Complex.I * ↑Real.pi / 2)) = -Complex.I from by
      rw [show -(Complex.I * ↑Real.pi / 2) = (↑(-(Real.pi/2)) * Complex.I) from by push_cast; ring,
        Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_neg, Real.sin_neg,
        Real.cos_pi_div_two, Real.sin_pi_div_two]; push_cast; ring,
    show Complex.exp (Complex.I * ↑Real.pi / 2) = Complex.I from by
      rw [show (Complex.I * ↑Real.pi / 2) = (↑(Real.pi/2) * Complex.I) from by push_cast; ring,
        Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin, Real.cos_pi_div_two,
        Real.sin_pi_div_two]; push_cast; ring]

open scoped Matrix in
open SKEFTHawking.FKLW.GenericSU2 in
/-- **X phase-bridge identity**: `toComplexMat (gateMatrix X) = (-i) • ρ_CliffT (of0·of1⁴·of0)`
(the off-diagonal product `H_SU·T_SU⁴·H_SU = !![0,i;i,0]`). -/
theorem toComplexMat_gateMatrix_eq_X :
    toComplexMat (gateMatrix CliffordTGate.X)
      = gatePhase CliffordTGate.X • ((ρ_CliffT (gateWord CliffordTGate.X) :
          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hsqrt : ((↑(Real.sqrt 2) : ℂ))⁻¹ ^ 2 * 2 = 1 := by
    rw [inv_pow, show (↑(Real.sqrt 2):ℂ)^2 = 2 from by
      rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num]; norm_num
  have hcoe : ((ρ_CliffT (gateWord CliffordTGate.X) :
      ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ)
      = H_SU_mat * T_SU_mat ^ 4 * H_SU_mat := by
    rw [show gateWord CliffordTGate.X = fgH * fgT ^ 4 * fgH from rfl,
      map_mul, map_mul, Submonoid.coe_mul, Submonoid.coe_mul, ρ_CliffT_of_0, ρ_CliffT_fgT_pow]
    rfl
  rw [show gatePhase CliffordTGate.X = -Complex.I from rfl, hcoe, T_SU_mat_pow_four, H_SU_mat,
      toComplexMat_gateMatrix_X, Matrix.eta_fin_two ((-Complex.I) • _)]
  congr 1 <;>
    (simp only [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.of_apply, smul_eq_mul] <;> ring_nf <;>
     rw [show Complex.I ^ 4 = 1 from by rw [show (4:ℕ)=2+2 from rfl, pow_add, Complex.I_sq]; ring] <;>
     simp only [one_mul, hsqrt])

open scoped Matrix in
open SKEFTHawking.FKLW.GenericSU2 in
/-- **Y phase-bridge identity**: `toComplexMat (gateMatrix Y) = i • ρ_CliffT (of0·of1⁴·of0·of1⁴)`
(the 4-matrix product `H_SU·T_SU⁴·H_SU·T_SU⁴ = !![0,-1;1,0]`). -/
theorem toComplexMat_gateMatrix_eq_Y :
    toComplexMat (gateMatrix CliffordTGate.Y)
      = gatePhase CliffordTGate.Y • ((ρ_CliffT (gateWord CliffordTGate.Y) :
          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) := by
  have hI5 : Complex.I ^ 5 * (↑(Real.sqrt 2) : ℂ)⁻¹ ^ 2 * 2 = Complex.I := by
    rw [show Complex.I ^ 5 = Complex.I from by
        rw [show (5:ℕ) = 2 + 2 + 1 from rfl, pow_add, pow_add, Complex.I_sq]; ring,
      mul_assoc, show ((↑(Real.sqrt 2) : ℂ)⁻¹ ^ 2 * 2) = 1 from by
        rw [inv_pow, show (↑(Real.sqrt 2):ℂ)^2 = 2 from by
          rw [← Complex.ofReal_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]; norm_num]; norm_num,
      mul_one]
  have hcoe : ((ρ_CliffT (gateWord CliffordTGate.Y) :
      ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ)
      = H_SU_mat * T_SU_mat ^ 4 * H_SU_mat * T_SU_mat ^ 4 := by
    rw [show gateWord CliffordTGate.Y = fgH * fgT ^ 4 * fgH * fgT ^ 4 from rfl,
      map_mul, map_mul, map_mul, Submonoid.coe_mul, Submonoid.coe_mul, Submonoid.coe_mul,
      ρ_CliffT_of_0, ρ_CliffT_fgT_pow]
    rfl
  rw [show gatePhase CliffordTGate.Y = Complex.I from rfl, hcoe, T_SU_mat_pow_four, H_SU_mat,
      toComplexMat_gateMatrix_Y, Matrix.eta_fin_two (Complex.I • _)]
  congr 1 <;>
    (simp only [Matrix.smul_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.of_apply, smul_eq_mul] <;> ring_nf <;> simp only [hI5])

/-! ## The word-level phase bridge -/

open scoped Matrix in
open SKEFTHawking.FKLW.GenericSU2 in
/-- **Per-gate phase bridge** (all 8 gates combined): `toComplexMat (gateMatrix g) =
gatePhase g • ρ_CliffT (gateWord g)`. -/
theorem toComplexMat_gateMatrix_eq (g : CliffordTGate) :
    toComplexMat (gateMatrix g) = gatePhase g • ((ρ_CliffT (gateWord g) :
      ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) := by
  cases g
  · exact toComplexMat_gateMatrix_eq_H
  · exact toComplexMat_gateMatrix_eq_S
  · exact toComplexMat_gateMatrix_eq_T
  · exact toComplexMat_gateMatrix_eq_X
  · exact toComplexMat_gateMatrix_eq_Y
  · exact toComplexMat_gateMatrix_eq_Z
  · exact toComplexMat_gateMatrix_eq_id
  · exact toComplexMat_gateMatrix_eq_omega

open scoped Matrix in
open SKEFTHawking.FKLW.GenericSU2 in
/-- **The word-level U(2)↔SU(2) phase bridge**: a KMM gate word's complex matrix equals its
SU(2) `ρ_CliffT` image up to the accumulated global phase —
`toComplexMat (interp gs) = phaseProd gs • ρ_CliffT (freeword gs)`. (Induction over `gs`;
`toComplexMat`/`ρ_CliffT` are monoid homs, the per-gate phases factor as central scalars.)
For a `det`-1 (`SU(2)`) word `phaseProd gs = ±1` (`scripts/phase_bridge_validation.py`),
so `ρ_CliffT (freeword gs) = ±toComplexMat (interp gs)` — the finder's approximation hook. -/
theorem toComplexMat_interp_eq (gs : List CliffordTGate) :
    toComplexMat (interp gs) = phaseProd gs • ((ρ_CliffT (freeword gs) :
      ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) := by
  induction gs with
  | nil => simp [toComplexMat, interp_nil, phaseProd_nil, freeword_nil, map_one]
  | cons g gs ih =>
      rw [interp_cons, freeword_cons, phaseProd_cons]
      show toComplexMat (gateMatrix g * interp gs) = _
      rw [show toComplexMat (gateMatrix g * interp gs)
            = toComplexMat (gateMatrix g) * toComplexMat (interp gs) from by
          simp only [toComplexMat, map_mul], toComplexMat_gateMatrix_eq, ih, map_mul,
        Submonoid.coe_mul, smul_mul_smul_comm]

/-! ## The ±1 global-phase lift for det-1 words

For a `det`-1 (`SU(2)`) KMM gate word, the word-level bridge's global phase
`phaseProd gs` is exactly `±1` — proven here (previously only validated via
`scripts/phase_bridge_validation.py`). The argument: `det` commutes with the entrywise
ring-hom `toComplexMat`, and the bridge `toComplexMat (interp gs) = phaseProd gs •
ρ_CliffT (freeword gs)` puts the `SU(2)` factor (det 1) under `Matrix.det_smul`
(card `Fin 2 = 2`), so `(phaseProd gs)² = toComplex (det (interp gs))`; at `det = 1`
this is `(phaseProd gs)² = 1`, hence `phaseProd gs = ±1`. The corollary
`ρ_CliffT_freeword_eq` then aligns the `SU(2)` image to `±toComplexMat (interp gs)` —
the approximation hook `cliffordTBaseFinder_kmm` uses. -/

open scoped Matrix in
open SKEFTHawking.FKLW.GenericSU2 in
/-- **Squared global phase = ℂ-image of the abstract determinant.** `(phaseProd gs)² =
toComplex (det (interp gs))`: `det` commutes with the ring-hom `toComplexMat`, and the
word-level bridge puts the `SU(2)` (det 1) factor under `Matrix.det_smul` (card 2). -/
theorem phaseProd_sq_eq_toComplex_det (gs : List CliffordTGate) :
    (phaseProd gs) ^ 2 = ZOmegaSqrt2.toComplex (interp gs).det := by
  have hbridge := toComplexMat_interp_eq gs
  have hmap : (toComplexMat (interp gs)).det = ZOmegaSqrt2.toComplex (interp gs).det := by
    simp only [toComplexMat, ← RingHom.map_det]
  have hsu : ((ρ_CliffT (freeword gs) : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
      Matrix (Fin 2) (Fin 2) ℂ).det = 1 :=
    (Matrix.mem_specialUnitaryGroup_iff.mp (ρ_CliffT (freeword gs)).2).2
  rw [hbridge, Matrix.det_smul, Fintype.card_fin, hsu, mul_one] at hmap
  exact hmap

open scoped Matrix in
open SKEFTHawking.FKLW.GenericSU2 in
/-- **The ±1 global-phase lift.** For a `det`-1 KMM gate word, `phaseProd gs = ±1`. -/
theorem phaseProd_eq_one_or_neg_one (gs : List CliffordTGate)
    (hdet : (interp gs).det = 1) : phaseProd gs = 1 ∨ phaseProd gs = -1 := by
  have h := phaseProd_sq_eq_toComplex_det gs
  rw [hdet, map_one] at h
  rw [sq] at h
  exact mul_self_eq_one_iff.mp h

open scoped Matrix in
open SKEFTHawking.FKLW.GenericSU2 in
/-- **SU(2) image of a det-1 KMM word = `±toComplexMat (interp gs)`.** Multiplying the
word-level bridge by `phaseProd gs` and using `(phaseProd gs)² = 1` (`det = 1`). -/
theorem ρ_CliffT_freeword_eq (gs : List CliffordTGate) (hdet : (interp gs).det = 1) :
    ((ρ_CliffT (freeword gs) : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ)
      = phaseProd gs • toComplexMat (interp gs) := by
  have hbridge := toComplexMat_interp_eq gs
  have hsq : phaseProd gs * phaseProd gs = 1 := by
    have h := phaseProd_sq_eq_toComplex_det gs
    rw [hdet, map_one, sq] at h; exact h
  rw [hbridge, smul_smul, hsq, one_smul]

end SKEFTHawking.RossSelinger
