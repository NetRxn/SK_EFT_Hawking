/-
# Phase 5q.H — K6′b Leg 14: THE THICKENED E-COLLAR IS A CHART-LEVEL PRODUCT

Chart family 3/3 of the weld atlas is built on the **double collar**
`dblCollar c : ℝP³ × [−1/8, 1/2] → K3`, whose `v = 0` slice is the seam. `KummerSeamSmooth`
established the smoothness of that slice (`contMDiff_bdryMapRP3`); the transition classes against
the two interior families need the **thickened** (`v ≠ 0`) statement. This module supplies the
E-side algebraic core of the thickening — the reason the thickened case does **not** need a fresh
geometric argument.

**The product formula.** The E half of the double collar is
`eCollar (r, t) = deform (bdryMapRP3 r, t)` (`KummerSeamCollarE`), i.e. the seam point of `r` pushed
inwards to fiber radius `t`. Every one of the three E-side *collar-type* charts of `ResE` —
`collarChart u₀`, `collarChart1 u₀`, `annulusCollarChart u₀` — reads a point as

    (base ⊕ fiber *direction*  ,  1 − fiber *radius*),

and `deform (·, t)` scales the fiber by `t` **without moving its direction** (`t > 0`). Hence, in
every one of the three charts,

* the `𝓔³` block of `deform (y, t)` equals the `𝓔³` block of `y` (§2, §4), and
* the half-space (radial) block is `1 − t · fiberNorm y` — and `fiberNorm (eCollar (r,t)) = t`, so
  on the collar it is exactly `1 − t` (§3, §4).

So in charts the thickened collar is **literally a product**: `(r, t) ↦ (chart block of the
boundary point `bdryMapRP3 r`, 1 − t)`. The thickening parameter decouples; the already-proved
boundary smoothness carries over unchanged, and no second geometric branch is needed. This is the
one-dimension-up analogue of the equator *unification* that `annulusTrivFun_bdryMap` performed for
the `v = 0` case.

**Residual (sharply named).** This module is the chart-level identity only. Turning it into
`ContMDiff` of the thickened collar — and thence into the seam transition classes (1,3) and (2,3) of
the weld atlas — additionally needs the *inverse* direction (the radial projection
`{1/2 < fiberNorm < 1} → ℝP³` read in the stereographic `ℝP³` atlas of `KummerRP3Smooth`), which is
NOT built here. Nothing in this module is blocked on it.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerSeamSmooth
import SKEFTHawking.KummerSeamCollarE

namespace SKEFTHawking.KummerSeamCollarSmooth

open SKEFTHawking.DiskChartGeneric
open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerResolutionPieceBoundary
open SKEFTHawking.KummerWeldFiberFlow
open SKEFTHawking.KummerSeamSmooth
open SKEFTHawking.KummerSeamCollarE

noncomputable section

/-! ## §1. Scaling the fiber -/

theorem toE2_scaleDisk (t : unitInterval) (w : Disk) :
    toE2 ((scaleDisk t w : Disk) : ℂ) = (t : ℝ) • toE2 (w : ℂ) := by
  ext i; fin_cases i <;> simp [toE2]

theorem norm_toE2_scaleDisk (t : unitInterval) (w : Disk) :
    ‖toE2 ((scaleDisk t w : Disk) : ℂ)‖ = (t : ℝ) * ‖toE2 (w : ℂ)‖ := by
  rw [toE2_scaleDisk, norm_smul, Real.norm_eq_abs, abs_of_nonneg (unitInterval.nonneg t)]

theorem fiberND_scaleDisk_coe (t : unitInterval) (w : Disk) :
    (fiberND (scaleDisk t w) : EuclideanSpace ℝ (Fin 2))
      = (t : ℝ) • (fiberND w : EuclideanSpace ℝ (Fin 2)) := by
  rw [fiberND_coe, fiberND_coe, toE2_scaleDisk]

theorem diskDir_fiberND_scaleDisk {t : unitInterval} (ht : 0 < (t : ℝ)) (w : Disk) :
    diskDir 1 (fiberND (scaleDisk t w)) = diskDir 1 (fiberND w) := by
  by_cases h : (fiberND w : EuclideanSpace ℝ (Fin 2)) = 0
  · have h' : (fiberND (scaleDisk t w) : EuclideanSpace ℝ (Fin 2)) = 0 := by
      rw [fiberND_scaleDisk_coe, h, smul_zero]
    rw [diskDir, dif_pos h', diskDir, dif_pos h]
  · have h' : (fiberND (scaleDisk t w) : EuclideanSpace ℝ (Fin 2)) ≠ 0 := by
      rw [fiberND_scaleDisk_coe]
      exact smul_ne_zero (ne_of_gt ht) h
    apply Subtype.ext
    rw [diskDir_coe h', diskDir_coe h, fiberND_scaleDisk_coe, norm_smul, Real.norm_eq_abs,
      abs_of_pos ht, smul_smul, mul_inv]
    congr 1
    field_simp

/-! ## §2. The deformation in the three E-side collar charts -/

theorem deform_chart0 (p : ResChart) (t : unitInterval) :
    deform (chart0 p, t) = chart0 (p.1, scaleDisk t p.2) := rfl

theorem deform_chart1 (p : ResChart) (t : unitInterval) :
    deform (chart1 p, t) = chart1 (p.1, scaleDisk t p.2) := rfl

theorem collarChart_deform_fst (u₀ : NSphere 1) {p : ResChart} (hp : p ∈ baseInterior)
    {t : unitInterval} (ht : 0 < (t : ℝ)) :
    (collarChart u₀ (deform (chart0 p, t))).1 = (collarChart u₀ (chart0 p)).1 := by
  rw [deform_chart0, collarChart_chart0_fst u₀ (p := (p.1, scaleDisk t p.2)) hp,
    collarChart_chart0_fst u₀ hp, diskDir_fiberND_scaleDisk ht]

theorem collarChart_deform_snd (u₀ : NSphere 1) {p : ResChart} (hp : p ∈ baseInterior)
    (t : unitInterval) :
    ((collarChart u₀ (deform (chart0 p, t))).2).val
      = WithLp.toLp 2 (fun _ : Fin 1 => 1 - (t : ℝ) * ‖toE2 (p.2 : ℂ)‖) := by
  rw [deform_chart0, collarChart_chart0_snd u₀ (p := (p.1, scaleDisk t p.2)) hp,
    norm_toE2_scaleDisk]

theorem trivFiber_scaleDisk (z : ℂ) (t : unitInterval) (w : Disk) :
    trivFiber z (scaleDisk t w) = scaleDisk t (trivFiber z w) := by
  apply Subtype.ext
  rw [trivFiber_coe, scaleDisk_coe, scaleDisk_coe, trivFiber_coe]
  ring

theorem annulusTrivFun_deform (y : ResE) (t : unitInterval) :
    annulusTrivFun (deform (y, t))
      = ((annulusTrivFun y).1, scaleDisk t (annulusTrivFun y).2) := by
  induction y using Quotient.ind with | _ a =>
  cases a with
  | inl p => exact Prod.ext rfl (trivFiber_scaleDisk _ _ _)
  | inr q => exact Prod.ext rfl (trivFiber_scaleDisk _ _ _)

theorem collarChart1_deform_fst (u₀ : NSphere 1) {p : ResChart} (hp : p ∈ baseInterior)
    {t : unitInterval} (ht : 0 < (t : ℝ)) :
    (collarChart1 u₀ (deform (chart1 p, t))).1 = (collarChart1 u₀ (chart1 p)).1 := by
  rw [deform_chart1, collarChart1_chart1_fst u₀ (p := (p.1, scaleDisk t p.2)) hp,
    collarChart1_chart1_fst u₀ hp, diskDir_fiberND_scaleDisk ht]

theorem collarChart1_deform_snd (u₀ : NSphere 1) {p : ResChart} (hp : p ∈ baseInterior)
    (t : unitInterval) :
    ((collarChart1 u₀ (deform (chart1 p, t))).2).val
      = WithLp.toLp 2 (fun _ : Fin 1 => 1 - (t : ℝ) * ‖toE2 (p.2 : ℂ)‖) := by
  rw [deform_chart1, collarChart1_chart1_snd u₀ (p := (p.1, scaleDisk t p.2)) hp,
    norm_toE2_scaleDisk]

theorem annulusCollarChart_deform_fst (u₀ : NSphere 1) (y : ResE) {t : unitInterval}
    (ht : 0 < (t : ℝ)) :
    (annulusCollarChart u₀ (deform (y, t))).1 = (annulusCollarChart u₀ y).1 := by
  rw [annulusCollarChart_fst u₀ (deform (y, t)), annulusCollarChart_fst u₀ y,
    annulusTrivFun_deform, diskDir_fiberND_scaleDisk ht]

theorem annulusCollarChart_deform_snd (u₀ : NSphere 1) (y : ResE) (t : unitInterval) :
    ((annulusCollarChart u₀ (deform (y, t))).2).val
      = WithLp.toLp 2 (fun _ : Fin 1 => 1 - (t : ℝ) * ‖toE2 ((annulusTrivFun y).2 : ℂ)‖) := by
  rw [annulusCollarChart_snd u₀ (deform (y, t)), annulusTrivFun_deform, norm_toE2_scaleDisk]

/-! ## §3. The radial chart coordinate IS `1 − fiberNorm` -/

theorem collarChart_snd_fiberNorm (u₀ : NSphere 1) {p : ResChart} (hp : p ∈ baseInterior) :
    ((collarChart u₀ (chart0 p)).2).val
      = WithLp.toLp 2 (fun _ : Fin 1 => 1 - fiberNorm (chart0 p)) := by
  rw [collarChart_chart0_snd u₀ hp, fiberNorm_chart0, norm_toE2]

theorem collarChart1_snd_fiberNorm (u₀ : NSphere 1) {p : ResChart} (hp : p ∈ baseInterior) :
    ((collarChart1 u₀ (chart1 p)).2).val
      = WithLp.toLp 2 (fun _ : Fin 1 => 1 - fiberNorm (chart1 p)) := by
  rw [collarChart1_chart1_snd u₀ hp, fiberNorm_chart1, norm_toE2]

theorem norm_annulusTrivFun_snd {y : ResE} (hy : y ∈ annulusRegion) :
    ‖((annulusTrivFun y).2 : ℂ)‖ = fiberNorm y := by
  rcases hy with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · rw [annulusTrivFun_chart0, fiberNorm_chart0]
    show ‖((trivFiber (p.1 : ℂ) p.2 : Disk) : ℂ)‖ = _
    rw [trivFiber_coe, norm_mul, norm_regDir_of (le_of_lt hp), one_mul]
  · rw [annulusTrivFun_chart1, fiberNorm_chart1]
    show ‖((trivFiber (p.1 : ℂ) p.2 : Disk) : ℂ)‖ = _
    rw [trivFiber_coe, norm_mul, norm_regDir_of (le_of_lt hp), one_mul]

theorem annulusCollarChart_snd_fiberNorm (u₀ : NSphere 1) {y : ResE} (hy : y ∈ annulusRegion) :
    ((annulusCollarChart u₀ y).2).val
      = WithLp.toLp 2 (fun _ : Fin 1 => 1 - fiberNorm y) := by
  rw [annulusCollarChart_snd u₀ y, norm_toE2, norm_annulusTrivFun_snd hy]

/-! ## §4. The thickened collar is a chart-level product -/

theorem deform_mem_annulusRegion {y : ResE} (hy : y ∈ annulusRegion) (t : unitInterval) :
    deform (y, t) ∈ annulusRegion := by
  rcases hy with ⟨p, hp, rfl⟩ | ⟨p, hp, rfl⟩
  · exact Or.inl ⟨(p.1, scaleDisk t p.2), hp, (deform_chart0 p t).symm⟩
  · exact Or.inr ⟨(p.1, scaleDisk t p.2), hp, (deform_chart1 p t).symm⟩

theorem eCollar_mem_annulusRegion {r : RP3} (hr : bdryMapRP3 r ∈ annulusRegion)
    (t : unitInterval) : eCollar (r, t) ∈ annulusRegion :=
  deform_mem_annulusRegion hr t

theorem collarChart_eCollar_fst (u₀ : NSphere 1) {p : ResChart} (hp : p ∈ baseInterior) {r : RP3}
    (hr : bdryMapRP3 r = chart0 p) {t : unitInterval} (ht : 0 < (t : ℝ)) :
    (collarChart u₀ (eCollar (r, t))).1 = (collarChart u₀ (bdryMapRP3 r)).1 := by
  show (collarChart u₀ (deform (bdryMapRP3 r, t))).1 = _
  rw [hr]
  exact collarChart_deform_fst u₀ hp ht

theorem collarChart_eCollar_snd (u₀ : NSphere 1) {p : ResChart} (hp : p ∈ baseInterior) {r : RP3}
    (hr : bdryMapRP3 r = chart0 p) (t : unitInterval) :
    ((collarChart u₀ (eCollar (r, t))).2).val
      = WithLp.toLp 2 (fun _ : Fin 1 => 1 - (t : ℝ)) := by
  have h : eCollar (r, t) = chart0 (p.1, scaleDisk t p.2) := by
    show deform (bdryMapRP3 r, t) = _
    rw [hr, deform_chart0]
  rw [h, collarChart_snd_fiberNorm u₀ (p := (p.1, scaleDisk t p.2)) hp, ← h,
    fiberNorm_eCollar (r, t)]

theorem collarChart1_eCollar_fst (u₀ : NSphere 1) {p : ResChart} (hp : p ∈ baseInterior) {r : RP3}
    (hr : bdryMapRP3 r = chart1 p) {t : unitInterval} (ht : 0 < (t : ℝ)) :
    (collarChart1 u₀ (eCollar (r, t))).1 = (collarChart1 u₀ (bdryMapRP3 r)).1 := by
  show (collarChart1 u₀ (deform (bdryMapRP3 r, t))).1 = _
  rw [hr]
  exact collarChart1_deform_fst u₀ hp ht

theorem collarChart1_eCollar_snd (u₀ : NSphere 1) {p : ResChart} (hp : p ∈ baseInterior) {r : RP3}
    (hr : bdryMapRP3 r = chart1 p) (t : unitInterval) :
    ((collarChart1 u₀ (eCollar (r, t))).2).val
      = WithLp.toLp 2 (fun _ : Fin 1 => 1 - (t : ℝ)) := by
  have h : eCollar (r, t) = chart1 (p.1, scaleDisk t p.2) := by
    show deform (bdryMapRP3 r, t) = _
    rw [hr, deform_chart1]
  rw [h, collarChart1_snd_fiberNorm u₀ (p := (p.1, scaleDisk t p.2)) hp, ← h,
    fiberNorm_eCollar (r, t)]

theorem annulusCollarChart_eCollar_fst (u₀ : NSphere 1) (r : RP3) {t : unitInterval}
    (ht : 0 < (t : ℝ)) :
    (annulusCollarChart u₀ (eCollar (r, t))).1 = (annulusCollarChart u₀ (bdryMapRP3 r)).1 :=
  annulusCollarChart_deform_fst u₀ (bdryMapRP3 r) ht

theorem annulusCollarChart_eCollar_snd (u₀ : NSphere 1) {r : RP3}
    (hr : bdryMapRP3 r ∈ annulusRegion) (t : unitInterval) :
    ((annulusCollarChart u₀ (eCollar (r, t))).2).val
      = WithLp.toLp 2 (fun _ : Fin 1 => 1 - (t : ℝ)) := by
  rw [annulusCollarChart_snd_fiberNorm u₀ (eCollar_mem_annulusRegion hr t),
    fiberNorm_eCollar (r, t)]

end

end SKEFTHawking.KummerSeamCollarSmooth
