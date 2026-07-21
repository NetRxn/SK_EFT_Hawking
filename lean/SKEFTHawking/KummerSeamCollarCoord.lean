/-
# Phase 5q.H — K6′b Leg 19: the E-SIDE SEAM PARAMETRIZATION IN CHART COORDINATES

The two open weld-atlas transition classes (1,3) and (2,3) compare an *interior* chart of a weld
piece with the *seam* chart. On the E side the comparison needs one explicit identity: what the seam
parametrization `seamParam c : ℝP³ × (−1/8,1/2) → K3` looks like when its value is read in an
E-interior chart.

**§1 — the collar bookkeeping (chart-free).** On the `E` half of the double collar the parameter is
just the complement of the fiber radius:

    seamParam c (mkRP3 σ, 1 − t) = weldMk (inr (c, deform (bdryMap σ, t))) ,   0 ≤ t ≤ 1 .

**§2 — the fiber-scaled boundary point, per chart.** `deform (bdryMap σ, t)` is the boundary point
of `σ` pushed to fiber radius `t`, and in each of the three E-interior charts it is the *product*
`(β, t·ζ)` of the boundary datum with the scaling `t` (`deform_bdryMap_chart0` /
`_chart1` / `annulusTrivFun_deform_bdryMap`) — the chart-level product statement of
`KummerSeamCollarSmooth`, now on the interior charts rather than the collar charts.

**§3 — the section closes the loop.** Feeding `KummerSeamSectionAt`'s based section into §1–§2
produces, for *any* fiber phase, an explicit `(r, v) ∈ ℝP³ × (−1/8,1/2)` whose seam-parametrization
value is a prescribed collar-band point of the `c`-th E-interior copy
(`seamParam_eq_weldMk_chart0`). The `ℝP³` coordinate `r = mkRP3 (seamPointAt …)` is an explicitly
`C^k` function of the chart coordinates, which is exactly the direction
`KummerSeamSmooth.contMDiff_bdryMapRP3` does not supply.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerSeamSectionAt
import SKEFTHawking.KummerSeamChart
import SKEFTHawking.KummerEIntChartCoord

namespace SKEFTHawking.KummerSeamCollarCoord

open Set Topology
open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerResolutionPieceBoundary
open SKEFTHawking.KummerWeldFiberFlow
open SKEFTHawking.KummerWeld
open SKEFTHawking.KummerSeamSmooth
open SKEFTHawking.KummerSeamSection
open SKEFTHawking.KummerSeamSectionAt
open SKEFTHawking.KummerSeamCollarE (eCollar)
open SKEFTHawking.KummerSeamDoubleCollar
open SKEFTHawking.KummerSeamChart

noncomputable section

/-! ## §1. The `E` half of the double collar, chart-free -/

/-- **The `E`-half collar bookkeeping.** On the `E` side the seam parameter is `1 − t`, where `t` is
the fiber radius the boundary point is pushed to. -/
theorem seamParam_eq_weldMk (c : EIndex) (σ : S3) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hv : (1 - t) ∈ openParam) :
    seamParam c (mkRP3 σ, ⟨1 - t, hv⟩)
      = weldMk (Sum.inr (c, deform (bdryMap σ, ⟨t, ht0, ht1⟩))) := by
  have hnn : (0 : ℝ) ≤ ((toDbl ⟨1 - t, hv⟩ : ↥dblParam) : ℝ) := by
    show (0 : ℝ) ≤ 1 - t; linarith
  have hE : clampE (toDbl ⟨1 - t, hv⟩) = (⟨t, ht0, ht1⟩ : unitInterval) := by
    apply Subtype.ext
    rw [clampE_coe]
    show 1 - max (1 - t) 0 = t
    rw [max_eq_left (by linarith)]
    ring
  show dblCollar c (mkRP3 σ, toDbl ⟨1 - t, hv⟩) = _
  rw [dblCollar_of_nonneg c hnn]
  show weldMk (Sum.inr (c, eCollar (mkRP3 σ, clampE (toDbl ⟨1 - t, hv⟩)))) = _
  rw [hE]
  rfl

/-! ## §2. The fiber-scaled boundary point in the three E-interior charts -/

/-- **Chart-0 branch** — on the chart-0 hemisphere the fiber-scaled boundary point is
`chart0 (β, t·u)` with `(β, u) = hopf0 σ`. -/
theorem deform_bdryMap_chart0 {σ : S3} (h : ‖(σ : ℂ × ℂ).1‖ ≤ ‖(σ : ℂ × ℂ).2‖) (t : unitInterval) :
    deform (bdryMap σ, t)
      = chart0 ((hopfChart0 h).1, scaleDisk t (hopfChart0 h).2) := by
  rw [bdryMap_eq_chart0 h]
  rfl

/-- **Chart-1 branch.** -/
theorem deform_bdryMap_chart1 {σ : S3} (h : ¬ ‖(σ : ℂ × ℂ).1‖ ≤ ‖(σ : ℂ × ℂ).2‖)
    (t : unitInterval) :
    deform (bdryMap σ, t)
      = chart1 ((hopfChart1 h).1, scaleDisk t (hopfChart1 h).2) := by
  rw [bdryMap_eq_chart1 h]
  rfl

/-- **Equatorial branch** — in the annulus trivialization the fiber-scaled boundary point is the
product `(seamAnnulusBase σ, t · seamAnnulusFiberD σ)`. -/
theorem annulusTrivFun_deform_bdryMap {σ : S3} (hq : (σ : ℂ × ℂ) ∈ nearEquator)
    (t : unitInterval) :
    annulusTrivFun (deform (bdryMap σ, t))
      = (seamAnnulusBase (σ : ℂ × ℂ), scaleDisk t (seamAnnulusFiberD (σ : ℂ × ℂ))) := by
  rw [SKEFTHawking.KummerSeamCollarSmooth.annulusTrivFun_deform, annulusTrivFun_bdryMap σ hq]

/-! ## §3. Feeding in the based section: an explicit seam preimage of a collar-band point -/

/-- The unit fiber direction of a nonzero fiber coordinate. -/
def fiberDir (w : ℂ) : ℂ := w / ((‖w‖ : ℝ) : ℂ)

theorem norm_fiberDir {w : ℂ} (hw : w ≠ 0) : ‖fiberDir w‖ = 1 := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  rw [fiberDir, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self hn]

theorem scaleDisk_fiberDir {w : ℂ} (hw : w ≠ 0) (hw1 : ‖w‖ ≤ 1) :
    ((scaleDisk ⟨‖w‖, norm_nonneg w, hw1⟩ ⟨fiberDir w, le_of_eq (norm_fiberDir hw)⟩ : Disk) : ℂ)
      = w := by
  have hn : ((‖w‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr hw
  show ((‖w‖ : ℝ) : ℂ) * fiberDir w = w
  rw [fiberDir]
  field_simp

/-- **THE CHART-0 SEAM PREIMAGE.** Every collar-band point of the `c`-th E-interior copy presented
in chart-0 coordinates `(z, w)` with `1/2 < ‖w‖ ≤ 1` is the seam-parametrization value of the
explicit pair `(mkRP3 (seamPointAt …), 1 − ‖w‖)` — for *every* fiber phase, since the based section
of `KummerSeamSectionAt` has no branch obstruction. -/
theorem seamParam_eq_weldMk_chart0 (c : EIndex) {m : ℂ} (hm : ‖m‖ = 1) {z w : ℂ}
    (hz : ‖z‖ ≤ 1) (hw0 : w ≠ 0) (hw1 : 1 / 2 < ‖w‖) (hw2 : ‖w‖ ≤ 1)
    (h : (z, fiberDir w) ∈ seamDomAt m) :
    seamParam c (mkRP3 (seamPointAt hm h),
        ⟨1 - ‖w‖, by
          constructor
          · show -(1 / 8 : ℝ) < 1 - ‖w‖; linarith
          · show 1 - ‖w‖ < 1 / 2; linarith⟩)
      = weldMk (Sum.inr (c, chart0 (⟨z, hz⟩, ⟨w, hw2⟩))) := by
  have hu : ‖fiberDir w‖ = 1 := norm_fiberDir hw0
  have hle : ‖((seamPointAt hm h : S3) : ℂ × ℂ).1‖ ≤ ‖((seamPointAt hm h : S3) : ℂ × ℂ).2‖ :=
    norm_seamSectionAt_fst_le hm hz h
  have hbdry : bdryMap (seamPointAt hm h) = chart0 (⟨z, hz⟩, ⟨fiberDir w, le_of_eq hu⟩) :=
    bdryMap_seamPointAt hm hz hu h
  rw [seamParam_eq_weldMk c (seamPointAt hm h) (norm_nonneg w) hw2, hbdry]
  refine congrArg (fun x : ResE => weldMk (Sum.inr (c, x))) ?_
  show chart0 ((⟨z, hz⟩ : Disk), scaleDisk ⟨‖w‖, norm_nonneg w, hw2⟩
    (⟨fiberDir w, le_of_eq hu⟩ : Disk)) = _
  exact congrArg chart0 (Prod.ext rfl (Subtype.ext (scaleDisk_fiberDir hw0 hw2)))

end

end SKEFTHawking.KummerSeamCollarCoord
