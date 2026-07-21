/-
# Phase 5q.H — K6′b Leg 21: THE TWO SMOOTH HALVES OF THE E-INTERIOR ↔ SEAM TRANSITION

Legs 18–20 supply the three ingredients of the weld's open transition class (1,3): the flat
E-interior charts are one affine map `intCoord` of a `(β, ζ)` pair (Leg 18); the seam
parametrization of a collar-band point is `(mkRP3 (seamPointAt …), 1 − ‖ζ‖)` in all three chart
branches (Leg 19); and the pinned `ℝP³` chart is `rp3Coord` (Leg 20). This module composes them
into the **two explicit maps `𝓔³ × ℝ → 𝓔³ × ℝ`** the transition and its inverse must equal, and
proves each `C^k` on an explicit open set:

    seamFwd m x₀ (p)  =  ( rp3Coord x₀ (seamSectionAt m (β, ζ/‖ζ‖)) , 1 − ‖ζ‖ ) ,  (β,ζ) = intCoordInv p
    seamBwd x₀ (v)    =  intCoord ( β , (1 − v₂)·u ) ,   (β,u) = hopf0 (eucToC2 ((Φ x₀).symm v₁)) .

`seamBwd` is the composite the *inverse* direction needs: read the `ℝP³` coordinate back through
the stereographic chart, take its Hopf chart-0 coordinates, and scale the fiber by the collar
radius `1 − v₂`. `seamFwd` is the composite the forward direction needs, and it is the one that
consumes the based section — the direction `KummerSeamSmooth.contMDiff_bdryMapRP3` does not give.

Both are `C^k` for every `k` (`contDiffOn_seamFwd`, `contDiffOn_seamBwd`) on open sets
(`isOpen_seamFwdDom`, `isOpen_seamBwdDom`). What is *not* here — named exactly — is the set-level
identification of the weld-atlas transition `(eFamChart c y).symm ≫ₕ seamChart c r₀` with these two
maps on the overlap, and hence the groupoid membership itself.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerSeamCollarCoord
import SKEFTHawking.KummerRP3ChartCoord

namespace SKEFTHawking.KummerSeamTransCoord

open Set Topology
open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.HalfSpaceInteriorFlatten
open SKEFTHawking.KummerSeamSmooth
open SKEFTHawking.KummerSeamSectionAt
open SKEFTHawking.KummerSeamCollarCoord
open SKEFTHawking.KummerEIntChartCoord
open SKEFTHawking.KummerRP3ChartCoord
open SKEFTHawking.KummerRP3Smooth
open SKEFTHawking.KummerRP3EuclCharts

noncomputable section

variable {k : WithTop ℕ∞}

/-! ## §1. The fiber direction is smooth off the zero section -/

theorem contDiffOn_fiberDir : ContDiffOn ℝ k fiberDir {w : ℂ | w ≠ 0} := by
  have hid : ContDiffOn ℝ k (fun w : ℂ => w) {w : ℂ | w ≠ 0} := contDiff_id.contDiffOn
  have hn : ContDiffOn ℝ k (fun w : ℂ => (‖w‖)⁻¹) {w : ℂ | w ≠ 0} :=
    (hid.norm ℝ (fun w hw => hw)).inv (fun w hw => norm_ne_zero_iff.mpr hw)
  refine (hn.smul hid).congr ?_
  intro w hw
  simp only [Pi.smul_apply']
  rw [fiberDir, div_eq_inv_mul, ← Complex.ofReal_inv]
  norm_cast

/-! ## §2. The forward half -/

/-- **The forward transition map.** Read the flat E-interior coordinate as `(β, ζ)`, take the based
section at the fiber direction `ζ/‖ζ‖`, and read the resulting `ℝP³` point in the `x₀`-chart; the
second coordinate is the collar parameter `1 − ‖ζ‖`. -/
def seamFwd (m : ℂ) (x₀ : S3E) (p : FModel) : FModel :=
  (rp3Coord x₀ (seamSectionAt m ((intCoordInv p).1, fiberDir (intCoordInv p).2)),
   1 - ‖(intCoordInv p).2‖)

/-- The open set on which `seamFwd` is defined: the fiber coordinate is nonzero, the section's
branch is live, and the section point misses the stereographic pole. -/
def seamFwdDom (m : ℂ) (x₀ : S3E) : Set FModel :=
  {p : FModel | (intCoordInv p).2 ≠ 0}
    ∩ (fun p : FModel => ((intCoordInv p).1, fiberDir (intCoordInv p).2)) ⁻¹' seamDomAt m
    ∩ (fun p : FModel =>
        seamSectionAt m ((intCoordInv p).1, fiberDir (intCoordInv p).2)) ⁻¹' rp3CoordDom x₀

theorem continuous_intCoordInv : Continuous intCoordInv :=
  (contDiff_intCoordInv (k := (0 : WithTop ℕ∞))).continuous

theorem continuousOn_seamPre :
    ContinuousOn (fun p : FModel => ((intCoordInv p).1, fiberDir (intCoordInv p).2))
      {p : FModel | (intCoordInv p).2 ≠ 0} :=
  (continuous_fst.comp continuous_intCoordInv).continuousOn.prodMk
    ((contDiffOn_fiberDir (k := (0 : WithTop ℕ∞))).continuousOn.comp
      (continuous_snd.comp continuous_intCoordInv).continuousOn (fun _ hp => hp))

theorem isOpen_seamFwdDom (m : ℂ) (x₀ : S3E) : IsOpen (seamFwdDom m x₀) := by
  have h0 : IsOpen {p : FModel | (intCoordInv p).2 ≠ 0} :=
    isOpen_compl_singleton.preimage (continuous_snd.comp continuous_intCoordInv)
  have h1 : IsOpen ({p : FModel | (intCoordInv p).2 ≠ 0}
      ∩ (fun p : FModel => ((intCoordInv p).1, fiberDir (intCoordInv p).2)) ⁻¹' seamDomAt m) :=
    continuousOn_seamPre.isOpen_inter_preimage h0 (isOpen_seamDomAt m)
  have hsec : ContinuousOn (fun p : FModel =>
      seamSectionAt m ((intCoordInv p).1, fiberDir (intCoordInv p).2))
      ({p : FModel | (intCoordInv p).2 ≠ 0}
        ∩ (fun p : FModel => ((intCoordInv p).1, fiberDir (intCoordInv p).2)) ⁻¹' seamDomAt m) :=
    ((contDiffOn_seamSectionAt (k := (0 : WithTop ℕ∞)) m).continuousOn).comp
      (continuousOn_seamPre.mono Set.inter_subset_left) (fun _ hp => hp.2)
  exact hsec.isOpen_inter_preimage h1 (isOpen_rp3CoordDom x₀)

/-- **The forward half is `C^k`.** -/
theorem contDiffOn_seamFwd (m : ℂ) (x₀ : S3E) :
    ContDiffOn ℝ k (seamFwd m x₀) (seamFwdDom m x₀) := by
  have hbase : ContDiffOn ℝ k (fun p : FModel => ((intCoordInv p).1, fiberDir (intCoordInv p).2))
      (seamFwdDom m x₀) :=
    (contDiff_fst.comp contDiff_intCoordInv).contDiffOn.prodMk
      (contDiffOn_fiberDir.comp (contDiff_snd.comp contDiff_intCoordInv).contDiffOn
        (fun _ hp => hp.1.1))
  have hsec : ContDiffOn ℝ k
      (fun p : FModel => seamSectionAt m ((intCoordInv p).1, fiberDir (intCoordInv p).2))
      (seamFwdDom m x₀) :=
    (contDiffOn_seamSectionAt m).comp hbase (fun _ hp => hp.1.2)
  refine ContDiffOn.prodMk ((contDiffOn_rp3Coord x₀).comp hsec (fun _ hp => hp.2)) ?_
  refine contDiffOn_const.sub ?_
  exact (contDiff_snd.comp contDiff_intCoordInv).contDiffOn.norm ℝ (fun _ hp => hp.1.1)

/-! ## §3. The backward half -/

/-- The pinned `ℂ²` representative of the `ℝP³` point a chart coordinate names. -/
def seamLift (x₀ : S3E) (t : E3) : ℂ × ℂ :=
  SKEFTHawking.KummerK7Opener.eucToC2 (((Φ x₀).symm t : S3E) : E4)

theorem contDiff_seamLift (x₀ : S3E) : ContDiff ℝ k (seamLift x₀) :=
  contDiff_eucToC2.comp (contDiff_chartSymm_coe_S3E x₀)

/-- **The backward transition map.** Lift the `ℝP³` coordinate to `S³`, take its Hopf chart-0
coordinates `(β, u)`, scale the fiber by the collar radius `1 − v₂`, and read the result in the
E-interior coordinate. -/
def seamBwd (x₀ : S3E) (v : FModel) : FModel :=
  intCoord ((hopf0 (seamLift x₀ v.1)).1,
    ((1 - v.2 : ℝ) : ℂ) * (hopf0 (seamLift x₀ v.1)).2)

/-- The open set on which `seamBwd` is defined: the lifted point misses the chart-0 pole. -/
def seamBwdDom (x₀ : S3E) : Set FModel := {v : FModel | (seamLift x₀ v.1).2 ≠ 0}

theorem isOpen_seamBwdDom (x₀ : S3E) : IsOpen (seamBwdDom x₀) :=
  isOpen_compl_singleton.preimage
    (continuous_snd.comp
      ((contDiff_seamLift (k := (0 : WithTop ℕ∞)) x₀).continuous.comp continuous_fst))

/-- **The backward half is `C^k`.** -/
theorem contDiffOn_seamBwd (x₀ : S3E) :
    ContDiffOn ℝ k (seamBwd x₀) (seamBwdDom x₀) := by
  have hlift : ContDiffOn ℝ k (fun v : FModel => seamLift x₀ v.1) (seamBwdDom x₀) :=
    ((contDiff_seamLift x₀).comp contDiff_fst).contDiffOn
  have hhopf : ContDiffOn ℝ k (fun v : FModel => hopf0 (seamLift x₀ v.1)) (seamBwdDom x₀) :=
    contDiffOn_hopf0.comp hlift (fun _ hv => hv)
  have hscale : ContDiffOn ℝ k (fun v : FModel => (((1 - v.2 : ℝ) : ℂ))) (seamBwdDom x₀) :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_const.sub contDiff_snd)).contDiffOn
  exact contDiff_intCoord.comp_contDiffOn (hhopf.fst.prodMk (hscale.mul hhopf.snd))

end

end SKEFTHawking.KummerSeamTransCoord
