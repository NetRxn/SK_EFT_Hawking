/-
# Phase 5q.H — K7 instruments: the fiber norm and the outward fiber flow on the Kummer weld

Two global instruments for the K7 collar-thickened Mayer–Vietoris over the Kummer weld
`K3 = Q ∪_{16 × ℝP³} (16 × E)` (`KummerWeld.KummerK3`):

* §1 **`fiberNorm : E → ℝ`** — the fiber radius `‖w‖` of a point of the Euler−2 disk bundle
  `ResE`, chart-independent because the clutch preserves fiber norms on its gluing locus
  (`‖z² w‖ = ‖w‖` when `‖z‖ = 1`). The boundary `∂E` is exactly the `fiberNorm = 1` level set
  (`fiberNorm_eq_one_iff`).
* §2 **the outward disk flow** `flowDisk t w = min(1/‖w‖, 2−t)·w` — radial profile
  `r ↦ min(1, (2−t)·r)`: at `t = 1` the identity, at `t = 0` it maps the outer collar
  `r ≥ 1/2` onto `r = 1`, and it fixes `‖w‖ = 1` pointwise at every time. (Lean's `1/0 = 0`
  junk value makes the formula total; continuity at `w = 0` is a squeeze.)
* §3 **`resFlow : E × [0,1] → E`** — the outward flow descended to the disk bundle, mirroring the
  banked inward scaling `KummerResolutionPiece.deform` (the scalar depends only on `‖w‖`, so the
  clutch identity `s·(z²w) = z²·(s·w)` carries it through the weld).
* §4 **`weldFlow : K3 × [0,1] → K3`** — the identity on the `Q`-side, `resFlow` on each `E`-copy;
  descends through the 16-fold seam because `resFlow` fixes `∂E` pointwise. This single homotopy
  deformation-retracts BOTH the collar-thickened piece `Q ∪ (outer collars)` onto `Q` AND the
  collar intersection onto the seam in the K7 MV assembly (`KummerK7MVAssembly`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerResolutionPiece
import SKEFTHawking.KummerWeld

namespace SKEFTHawking.KummerWeldFiberFlow

open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerWeld
open SKEFTHawking.KummerFreeQuotient (FreeQuotient)

noncomputable section

/-! ## §1. The fiber norm on `E` -/

/-- The chart-level fiber norm `(z, w) ↦ ‖w‖` on the two-chart disjoint union. -/
def fiberNormSum : ResChart ⊕ ResChart → ℝ :=
  Sum.elim (fun p => ‖(p.2 : ℂ)‖) (fun p => ‖(p.2 : ℂ)‖)

/-- **The clutch preserves fiber norms**: on the gluing locus `‖z‖ = 1` the transition multiplies
the fiber by `z²` of norm `1`. So the fiber norm descends to `E`. -/
theorem fiberNormSum_respects {a b : ResChart ⊕ ResChart} (h : resRel a b) :
    fiberNormSum a = fiberNormSum b := by
  rcases h with rfl | hg
  · rfl
  · cases a with
    | inl p =>
      cases b with
      | inr q =>
        obtain ⟨hz, _, hq2⟩ := (hg : glued p q)
        show ‖(p.2 : ℂ)‖ = ‖(q.2 : ℂ)‖
        rw [hq2, norm_mul, norm_pow, hz, one_pow, one_mul]
      | inl _ => exact (hg : False).elim
    | inr q =>
      cases b with
      | inl p =>
        obtain ⟨hz, _, hq2⟩ := (hg : glued p q)
        show ‖(q.2 : ℂ)‖ = ‖(p.2 : ℂ)‖
        rw [hq2, norm_mul, norm_pow, hz, one_pow, one_mul]
      | inr _ => exact (hg : False).elim

/-- **The fiber norm** `E → ℝ` — the fiber radius of a disk-bundle point, chart-independent. -/
def fiberNorm : ResE → ℝ :=
  Quotient.lift fiberNormSum (fun _ _ h => fiberNormSum_respects h)

@[simp] theorem fiberNorm_mk (a : ResChart ⊕ ResChart) :
    fiberNorm (Quotient.mk resSetoid a) = fiberNormSum a := rfl

@[simp] theorem fiberNorm_chart0 (p : ResChart) : fiberNorm (chart0 p) = ‖(p.2 : ℂ)‖ := rfl

@[simp] theorem fiberNorm_chart1 (p : ResChart) : fiberNorm (chart1 p) = ‖(p.2 : ℂ)‖ := rfl

theorem continuous_fiberNorm : Continuous fiberNorm :=
  (isQuotientMap_quotient_mk' (s := resSetoid)).continuous_iff.mpr
    (((continuous_subtype_val.comp continuous_snd).norm).sumElim
      ((continuous_subtype_val.comp continuous_snd).norm))

theorem fiberNorm_nonneg (x : ResE) : 0 ≤ fiberNorm x := by
  induction x using Quotient.ind with
  | _ a => cases a with
    | inl p => exact norm_nonneg _
    | inr p => exact norm_nonneg _

theorem fiberNorm_le_one (x : ResE) : fiberNorm x ≤ 1 := by
  induction x using Quotient.ind with
  | _ a => cases a with
    | inl p => exact p.2.2
    | inr p => exact p.2.2

/-- **`∂E` is the `fiberNorm = 1` level set** — the boundary is exactly the fiber-radius-1 locus. -/
theorem fiberNorm_eq_one_iff {x : ResE} : fiberNorm x = 1 ↔ x ∈ boundaryE := by
  constructor
  · intro h
    induction x using Quotient.ind with
    | _ a => cases a with
      | inl p => exact ⟨p, h, Or.inl rfl⟩
      | inr p => exact ⟨p, h, Or.inr rfl⟩
  · rintro ⟨p, hp, rfl | rfl⟩
    · exact hp
    · exact hp

theorem fiberNorm_bdryMapRP3 (r : RP3) : fiberNorm (bdryMapRP3 r) = 1 :=
  fiberNorm_eq_one_iff.mpr (range_bdryMapRP3_eq_boundaryE ▸ Set.mem_range_self r)

/-! ## §2. The outward disk flow `w ↦ min(1/‖w‖, 2−t)·w` -/

/-- The outward-flow scalar `min(1/‖w‖, 2−t)` (radial profile `r ↦ min(1, (2−t)·r)`). At `w = 0`
Lean's `1/0 = 0` gives scalar `0` — the correct junk value (`0·0 = 0`). -/
def flowScalar (t : unitInterval) (w : Disk) : ℝ := min (1 / ‖(w : ℂ)‖) (2 - (t : ℝ))

theorem one_le_two_sub (t : unitInterval) : 1 ≤ 2 - (t : ℝ) := by
  have := unitInterval.le_one t; linarith

theorem two_sub_le_two (t : unitInterval) : 2 - (t : ℝ) ≤ 2 := by
  have := unitInterval.nonneg t; linarith

theorem flowScalar_nonneg (t : unitInterval) (w : Disk) : 0 ≤ flowScalar t w :=
  le_min (div_nonneg zero_le_one (norm_nonneg _)) (by linarith [one_le_two_sub t])

/-- **The outward disk flow** on the fiber disk: `w ↦ min(1/‖w‖, 2−t)·w`, staying in `D²`. -/
def flowDisk (t : unitInterval) (w : Disk) : Disk :=
  ⟨(flowScalar t w : ℂ) * (w : ℂ), by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (flowScalar_nonneg t w)]
    rcases eq_or_lt_of_le (norm_nonneg (w : ℂ)) with h0 | h0
    · rw [← h0, mul_zero]; exact zero_le_one
    · calc flowScalar t w * ‖(w : ℂ)‖
          ≤ (1 / ‖(w : ℂ)‖) * ‖(w : ℂ)‖ :=
            mul_le_mul_of_nonneg_right (min_le_left _ _) (norm_nonneg _)
        _ = 1 := by field_simp⟩

@[simp] theorem flowDisk_coe (t : unitInterval) (w : Disk) :
    ((flowDisk t w : Disk) : ℂ) = (flowScalar t w : ℂ) * (w : ℂ) := rfl

/-- **The radial profile**: `‖flowDisk t w‖ = min(1, (2−t)·‖w‖)`. -/
theorem norm_flowDisk (t : unitInterval) (w : Disk) :
    ‖((flowDisk t w : Disk) : ℂ)‖ = min 1 ((2 - (t : ℝ)) * ‖(w : ℂ)‖) := by
  rw [flowDisk_coe, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (flowScalar_nonneg t w)]
  rcases eq_or_lt_of_le (norm_nonneg (w : ℂ)) with h0 | h0
  · rw [← h0, mul_zero, mul_zero, min_eq_right zero_le_one]
  · rw [flowScalar, min_mul_of_nonneg _ _ (le_of_lt h0), one_div,
      inv_mul_cancel₀ (ne_of_gt h0)]

/-- The flow fixes the fiber boundary `‖w‖ = 1` pointwise at every time. -/
theorem flowDisk_boundary (t : unitInterval) {w : Disk} (hw : ‖(w : ℂ)‖ = 1) :
    flowDisk t w = w := by
  apply Subtype.ext
  rw [flowDisk_coe, flowScalar, hw, div_one, min_eq_left (one_le_two_sub t),
    Complex.ofReal_one, one_mul]

/-- The `t = 1` slice of the outward flow is the identity (`min(1/r, 1) = 1` for `r ≤ 1`). -/
theorem flowDisk_one (w : Disk) : flowDisk 1 w = w := by
  apply Subtype.ext
  rcases eq_or_lt_of_le (norm_nonneg (w : ℂ)) with h0 | h0
  · rw [flowDisk_coe, (norm_eq_zero.mp h0.symm : (w : ℂ) = 0), mul_zero]
  · have h1 : (1 : ℝ) ≤ 1 / ‖(w : ℂ)‖ := (le_div_iff₀ h0).mpr (by rw [one_mul]; exact w.2)
    rw [flowDisk_coe, flowScalar, show ((1 : unitInterval) : ℝ) = 1 from rfl,
      show (2 : ℝ) - 1 = 1 by norm_num, min_eq_right h1, Complex.ofReal_one, one_mul]

/-- The outer collar `‖w‖ ≥ 1/2` is flow-invariant. -/
theorem flowDisk_collar (t : unitInterval) {w : Disk} (hw : 1 / 2 ≤ ‖(w : ℂ)‖) :
    1 / 2 ≤ ‖((flowDisk t w : Disk) : ℂ)‖ := by
  rw [norm_flowDisk]
  refine le_min (by norm_num) ?_
  calc (1 : ℝ) / 2 ≤ ‖(w : ℂ)‖ := hw
    _ = 1 * ‖(w : ℂ)‖ := (one_mul _).symm
    _ ≤ (2 - (t : ℝ)) * ‖(w : ℂ)‖ :=
        mul_le_mul_of_nonneg_right (one_le_two_sub t) (norm_nonneg _)

/-- At `t = 0` the flow pushes the outer collar `‖w‖ ≥ 1/2` onto the boundary `‖w‖ = 1`. -/
theorem flowDisk_zero_norm {w : Disk} (hw : 1 / 2 ≤ ‖(w : ℂ)‖) :
    ‖((flowDisk 0 w : Disk) : ℂ)‖ = 1 := by
  rw [norm_flowDisk, show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_zero]
  exact min_eq_left (by linarith)

/-- **Continuity of the outward flow** — off `w = 0` by algebra, at `w = 0` by the squeeze
`‖flowDisk t w‖ ≤ 2‖w‖`. -/
theorem continuous_flowDisk : Continuous (fun p : unitInterval × Disk => flowDisk p.1 p.2) := by
  apply Continuous.subtype_mk
  rw [continuous_iff_continuousAt]
  intro p
  by_cases hw : ((p.2 : Disk) : ℂ) = 0
  · -- squeeze at the fiber origin
    have hval : (flowScalar p.1 p.2 : ℂ) * ((p.2 : Disk) : ℂ) = 0 := by rw [hw, mul_zero]
    rw [ContinuousAt, hval]
    apply squeeze_zero_norm (a := fun q : unitInterval × Disk => 2 * ‖((q.2 : Disk) : ℂ)‖)
    · intro q
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (flowScalar_nonneg q.1 q.2)]
      exact mul_le_mul_of_nonneg_right
        (le_trans (min_le_right _ _) (two_sub_le_two q.1)) (norm_nonneg _)
    · have hcont : Continuous (fun q : unitInterval × Disk => 2 * ‖((q.2 : Disk) : ℂ)‖) :=
        continuous_const.mul ((continuous_subtype_val.comp continuous_snd).norm)
      have hlim := hcont.continuousAt (x := p)
      rw [ContinuousAt, hw, norm_zero, mul_zero] at hlim
      exact hlim
  · -- away from the fiber origin the scalar is continuous
    have hnorm : ContinuousAt (fun q : unitInterval × Disk => ‖((q.2 : Disk) : ℂ)‖) p :=
      ((continuous_subtype_val.comp continuous_snd).norm).continuousAt
    have hs : ContinuousAt (fun q : unitInterval × Disk => flowScalar q.1 q.2) p := by
      refine Filter.Tendsto.min ?_ ?_
      · exact ContinuousAt.div continuousAt_const hnorm (norm_ne_zero_iff.mpr hw)
      · exact (continuous_const.sub
          (continuous_subtype_val.comp continuous_fst)).continuousAt
    exact ((Complex.continuous_ofReal.continuousAt.comp hs).mul
      ((continuous_subtype_val.comp continuous_snd).continuousAt))

-- Freeze the flow's ℝ-arithmetic body: every fact needed downstream is banked above, and leaving
-- `flowDisk`/`flowScalar` reducible lets `whnf` dive into real-number arithmetic during the
-- continuity compositions below (deterministic-timeout wall).
attribute [irreducible] flowDisk flowScalar

/-! ## §3. The outward flow on `E` -/

/-- The outward-flowed point of `E`, before descent: the chart-`i` point `(z, flowDisk t w)`. -/
def flowSum (a : ResChart ⊕ ResChart) (t : unitInterval) : ResE :=
  Sum.elim (fun p => chart0 (p.1, flowDisk t p.2)) (fun p => chart1 (p.1, flowDisk t p.2)) a

/-- **The outward flow respects the weld** — the scalar depends only on `‖w‖` (clutch-invariant),
so `s·(z²·w) = z²·(s·w)` carries the flow through the gluing. -/
theorem flowSum_respects {a b : ResChart ⊕ ResChart} (t : unitInterval) (h : resRel a b) :
    flowSum a t = flowSum b t := by
  rcases h with rfl | hg
  · rfl
  · cases a with
    | inl p =>
      cases b with
      | inr q =>
        obtain ⟨hz, hq1, hq2⟩ := (hg : glued p q)
        refine chart0_eq_chart1' (q := (p.1, flowDisk t p.2)) (p := (q.1, flowDisk t q.2))
          hz hq1 ?_
        have hn : ‖(q.2 : ℂ)‖ = ‖(p.2 : ℂ)‖ := by
          rw [hq2, norm_mul, norm_pow, hz, one_pow, one_mul]
        show ((flowDisk t q.2 : Disk) : ℂ) = (p.1 : ℂ) ^ 2 * ((flowDisk t p.2 : Disk) : ℂ)
        rw [flowDisk_coe, flowDisk_coe,
          show flowScalar t q.2 = flowScalar t p.2 from by
            unfold flowScalar; rw [hn], hq2]
        ring
      | inl _ => exact (hg : False).elim
    | inr q =>
      cases b with
      | inl p =>
        obtain ⟨hz, hq1, hq2⟩ := (hg : glued p q)
        have hn : ‖(q.2 : ℂ)‖ = ‖(p.2 : ℂ)‖ := by
          rw [hq2, norm_mul, norm_pow, hz, one_pow, one_mul]
        have key : chart0 (p.1, flowDisk t p.2) = chart1 (q.1, flowDisk t q.2) := by
          refine chart0_eq_chart1' (q := (p.1, flowDisk t p.2)) (p := (q.1, flowDisk t q.2))
            hz hq1 ?_
          show ((flowDisk t q.2 : Disk) : ℂ) = (p.1 : ℂ) ^ 2 * ((flowDisk t p.2 : Disk) : ℂ)
          rw [flowDisk_coe, flowDisk_coe,
            show flowScalar t q.2 = flowScalar t p.2 from by
              unfold flowScalar; rw [hn], hq2]
          ring
        show chart1 (q.1, flowDisk t q.2) = chart0 (p.1, flowDisk t p.2)
        exact key.symm
      | inr _ => exact (hg : False).elim

/-- **The outward fiber flow** `E × [0,1] → E` — `t = 1` is the identity (`resFlow_one`), `t = 0`
pushes the outer collar onto `∂E` (`fiberNorm_resFlow`), and `∂E` is fixed pointwise at every time
(`resFlow_boundary`). -/
def resFlow : ResE × unitInterval → ResE :=
  fun p => Quotient.liftOn p.1 (fun a => flowSum a p.2) (fun _ _ h => flowSum_respects p.2 h)

@[simp] theorem resFlow_mk (a : ResChart ⊕ ResChart) (t : unitInterval) :
    resFlow (Quotient.mk resSetoid a, t) = flowSum a t := rfl

theorem continuous_flowSum :
    Continuous (fun p : (ResChart ⊕ ResChart) × unitInterval => flowSum p.1 p.2) := by
  have hg0 : Continuous (fun q : ResChart × unitInterval => chart0 (q.1.1, flowDisk q.2 q.1.2)) :=
    continuous_chart0.comp (Continuous.prodMk (continuous_fst.comp continuous_fst)
      (continuous_flowDisk.comp
        (Continuous.prodMk continuous_snd (continuous_snd.comp continuous_fst))))
  have hg1 : Continuous (fun q : ResChart × unitInterval => chart1 (q.1.1, flowDisk q.2 q.1.2)) :=
    continuous_chart1.comp (Continuous.prodMk (continuous_fst.comp continuous_fst)
      (continuous_flowDisk.comp
        (Continuous.prodMk continuous_snd (continuous_snd.comp continuous_fst))))
  have hcongr : (fun p : (ResChart ⊕ ResChart) × unitInterval => flowSum p.1 p.2)
      = (Sum.elim (fun q : ResChart × unitInterval => chart0 (q.1.1, flowDisk q.2 q.1.2))
          (fun q : ResChart × unitInterval => chart1 (q.1.1, flowDisk q.2 q.1.2)))
        ∘ Homeomorph.sumProdDistrib := by
    funext p
    obtain ⟨a, t⟩ := p
    cases a with
    | inl q => rfl
    | inr q => rfl
  rw [hcongr]
  exact (hg0.sumElim hg1).comp Homeomorph.sumProdDistrib.continuous

theorem continuous_resFlow : Continuous resFlow := by
  have hq : Topology.IsQuotientMap (Quotient.mk resSetoid) := isQuotientMap_quotient_mk'
  exact hq.continuous_lift_prod_left continuous_flowSum

/-- **`resFlow(·, 1) = id`.** -/
theorem resFlow_one (x : ResE) : resFlow (x, 1) = x := by
  induction x using Quotient.ind with
  | _ a => cases a with
    | inl q =>
      show chart0 (q.1, flowDisk 1 q.2) = chart0 q
      exact congrArg chart0 (Prod.ext rfl (flowDisk_one q.2))
    | inr q =>
      show chart1 (q.1, flowDisk 1 q.2) = chart1 q
      exact congrArg chart1 (Prod.ext rfl (flowDisk_one q.2))

/-- **`resFlow` fixes `∂E` pointwise** at every time — the seam-compatibility that lets the flow
descend through the Kummer weld. -/
theorem resFlow_boundary {x : ResE} (hx : x ∈ boundaryE) (t : unitInterval) :
    resFlow (x, t) = x := by
  obtain ⟨p, hp, rfl | rfl⟩ := hx
  · show chart0 (p.1, flowDisk t p.2) = chart0 p
    exact congrArg chart0 (Prod.ext rfl (flowDisk_boundary t hp))
  · show chart1 (p.1, flowDisk t p.2) = chart1 p
    exact congrArg chart1 (Prod.ext rfl (flowDisk_boundary t hp))

/-- **The radial profile of the flow on `E`**: `fiberNorm(resFlow(x,t)) = min(1, (2−t)·fiberNorm x)`. -/
theorem fiberNorm_resFlow (x : ResE) (t : unitInterval) :
    fiberNorm (resFlow (x, t)) = min 1 ((2 - (t : ℝ)) * fiberNorm x) := by
  induction x using Quotient.ind with
  | _ a => cases a with
    | inl q =>
      show fiberNorm (chart0 (q.1, flowDisk t q.2)) = _
      rw [fiberNorm_chart0]
      exact norm_flowDisk t q.2
    | inr q =>
      show fiberNorm (chart1 (q.1, flowDisk t q.2)) = _
      rw [fiberNorm_chart1]
      exact norm_flowDisk t q.2

/-! ## §4. The weld flow on `K3` -/

/-- The weld-carrier-level flow: identity on the `Q`-side, `resFlow` on each `E`-copy, valued in
`K3`. -/
def weldFlowSum (a : WeldCarrier) (t : unitInterval) : KummerK3 :=
  Sum.elim (fun q => weldMk (Sum.inl q)) (fun p => weldMk (Sum.inr (p.1, resFlow (p.2, t)))) a

/-- **The flow respects the weld** — the only nontrivial identifications are the 16 seams, where
the `E`-side point is a boundary point and `resFlow` fixes it. -/
theorem weldFlowSum_respects {a b : WeldCarrier} (t : unitInterval) (h : weldRel a b) :
    weldFlowSum a t = weldFlowSum b t := by
  rcases h with rfl | hsj | hsj
  · rfl
  · obtain ⟨c, r, rfl, rfl⟩ := hsj
    show weldMk (Sum.inl (qBdryMap c r)) = weldMk (Sum.inr (c, resFlow (bdryMapRP3 r, t)))
    rw [resFlow_boundary (range_bdryMapRP3_eq_boundaryE ▸ Set.mem_range_self r) t]
    exact weldMk_seam c r
  · obtain ⟨c, r, rfl, rfl⟩ := hsj
    show weldMk (Sum.inr (c, resFlow (bdryMapRP3 r, t))) = weldMk (Sum.inl (qBdryMap c r))
    rw [resFlow_boundary (range_bdryMapRP3_eq_boundaryE ▸ Set.mem_range_self r) t]
    exact (weldMk_seam c r).symm

/-- **The weld flow** `K3 × [0,1] → K3` — identity on the `Q`-side, the outward fiber flow on each
`E`-copy. The single homotopy behind both K7 collar retractions. -/
def weldFlow : KummerK3 × unitInterval → KummerK3 :=
  fun p => Quotient.liftOn p.1 (fun a => weldFlowSum a p.2)
    (fun _ _ h => weldFlowSum_respects p.2 h)

@[simp] theorem weldFlow_mk_inl (q : FreeQuotient) (t : unitInterval) :
    weldFlow (weldMk (Sum.inl q), t) = weldMk (Sum.inl q) := rfl

@[simp] theorem weldFlow_mk_inr (c : EIndex) (e : ResE) (t : unitInterval) :
    weldFlow (weldMk (Sum.inr (c, e)), t) = weldMk (Sum.inr (c, resFlow (e, t))) := rfl

theorem continuous_weldFlowSum :
    Continuous (fun p : WeldCarrier × unitInterval => weldFlowSum p.1 p.2) := by
  have hg0 : Continuous (fun q : FreeQuotient × unitInterval => weldMk (Sum.inl q.1)) :=
    continuous_weldMk.comp (continuous_inl.comp continuous_fst)
  have hg1 : Continuous (fun q : (EIndex × ResE) × unitInterval =>
      weldMk (Sum.inr (q.1.1, resFlow (q.1.2, q.2)))) :=
    continuous_weldMk.comp (continuous_inr.comp
      ((continuous_fst.comp continuous_fst).prodMk
        (continuous_resFlow.comp
          ((continuous_snd.comp continuous_fst).prodMk continuous_snd))))
  have hcongr : (fun p : WeldCarrier × unitInterval => weldFlowSum p.1 p.2)
      = (Sum.elim (fun q : FreeQuotient × unitInterval => weldMk (Sum.inl q.1))
          (fun q : (EIndex × ResE) × unitInterval =>
            weldMk (Sum.inr (q.1.1, resFlow (q.1.2, q.2)))))
        ∘ Homeomorph.sumProdDistrib := by
    funext p
    obtain ⟨a, t⟩ := p
    cases a with
    | inl q => rfl
    | inr q => rfl
  rw [hcongr]
  exact (hg0.sumElim hg1).comp Homeomorph.sumProdDistrib.continuous

theorem continuous_weldFlow : Continuous weldFlow := by
  have hq : Topology.IsQuotientMap (Quotient.mk weldSetoid) := isQuotientMap_quotient_mk'
  exact hq.continuous_lift_prod_left continuous_weldFlowSum

/-- **`weldFlow(·, 1) = id`.** -/
theorem weldFlow_one (x : KummerK3) : weldFlow (x, 1) = x := by
  induction x using Quotient.ind with
  | _ a => cases a with
    | inl q => rfl
    | inr p =>
      show weldMk (Sum.inr (p.1, resFlow (p.2, 1))) = weldMk (Sum.inr p)
      rw [resFlow_one]

/-- **`weldFlow` fixes the `Q`-piece pointwise** at every time. -/
theorem weldFlow_qImage {x : KummerK3} (hx : x ∈ qImage) (t : unitInterval) :
    weldFlow (x, t) = x := by
  obtain ⟨q, rfl⟩ := hx
  rfl

/-- **`weldFlow` fixes the seam pointwise** at every time. -/
theorem weldFlow_seam {x : KummerK3} (hx : x ∈ seam) (t : unitInterval) :
    weldFlow (x, t) = x := by
  simp only [seam, Set.mem_iUnion, Set.mem_range] at hx
  obtain ⟨c, r, rfl⟩ := hx
  rw [weldFlow_mk_inr, resFlow_boundary (range_bdryMapRP3_eq_boundaryE ▸ Set.mem_range_self r) t]

end

end SKEFTHawking.KummerWeldFiberFlow
