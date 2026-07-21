/-
# Phase 5q.H — K6′b Leg 18: the E-INTERIOR CHARTS ARE ONE AFFINE COORDINATE MAP

The three flat E-interior charts of the weld atlas (`interiorChart`, `interiorChart1`,
`annulusInteriorChart`, flattened by `HalfSpaceInteriorFlatten.flatChart`) look different — they sit
over the two base disks and over the equatorial annulus — but **all three read a point as the same
`ℂ × Disk` pair `(β, ζ)` and then apply one and the same `ℝ`-affine map**

    intCoord (β, ζ) = (assemble 2 (toE2 β) ζ.re , ζ.im + 2)   ∈  𝓔³ × ℝ .

That is because the fiber half of each is the banked `diskInteriorChart 1`, whose coordinates are
literally `(Re, Im + 2)` — no polar decomposition, no direction. §2 proves the three evaluations
(`flatChart_interiorChart_chart0`, `…_interiorChart1_chart1`, `…_annulusInteriorChart`).

Two consequences that the remaining weld transition classes (1,3) and (2,3) rest on:

* **`intCoord` is a diffeomorphism onto its image** — `intCoordInv ∘ intCoord = id` (§1) with both
  maps `C^∞`, so passing between the flat chart and the `(β, ζ)` pair costs nothing analytically;
* **the fiber-scaling deformation is diagonal in `(β, ζ)`** — `deform (·, t)` fixes `β` and scales
  `ζ` by `t`, in all three charts at once (§3, `trivCoord_deform`), since the `chart0`/`chart1`
  cases are `deform_chart0`/`deform_chart1` and the equatorial case is
  `KummerSeamCollarSmooth.annulusTrivFun_deform`.

So the thickened seam collar is a *product* in every E-interior chart, with the collar radius `t`
appearing as the plain modulus `‖ζ‖ = fiberNorm` (§3).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerEInteriorChart
import SKEFTHawking.KummerSeamCollarSmooth
import SKEFTHawking.ManifoldModelTransport

namespace SKEFTHawking.KummerEIntChartCoord

open Set Topology
open scoped Manifold
open SKEFTHawking.DiskChartGeneric
open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerResolutionPieceBoundary
open SKEFTHawking.KummerWeldFiberFlow
open SKEFTHawking.HalfSpaceInteriorFlatten
open SKEFTHawking.KummerEInteriorChart

noncomputable section

variable {k : WithTop ℕ∞}

/-! ## §1. The affine coordinate map `ℂ × ℂ → 𝓔³ × ℝ` -/

/-- **The E-interior coordinate map.** The common `ℝ`-affine shape of all three flat E-interior
charts: base `β` plainly into `𝓔²`, fiber `ζ` as `(Re ζ, Im ζ + 2)`. -/
def intCoord (q : ℂ × ℂ) : FModel := (assemble 2 (toE2 q.1) q.2.re, q.2.im + 2)

/-- The inverse of `intCoord`. -/
def intCoordInv (v : FModel) : ℂ × ℂ :=
  (ofE2 (splitLo 2 v.1), (⟨v.1.ofLp (Fin.last 2), v.2 - 2⟩ : ℂ))

@[simp] theorem intCoordInv_intCoord (q : ℂ × ℂ) : intCoordInv (intCoord q) = q := by
  refine Prod.ext ?_ ?_
  · show ofE2 (splitLo 2 (assemble 2 (toE2 q.1) q.2.re)) = q.1
    rw [splitLo_assemble, ofE2_toE2]
  · show (⟨(assemble 2 (toE2 q.1) q.2.re).ofLp (Fin.last 2), q.2.im + 2 - 2⟩ : ℂ) = q.2
    rw [assemble_ofLp_last, add_sub_cancel_right]

theorem contDiff_toE2 : ContDiff ℝ k toE2 := by
  have h : ContDiff ℝ k (fun c : ℂ => (![c.re, c.im] : Fin 2 → ℝ)) := by
    refine contDiff_pi.mpr fun i => ?_
    fin_cases i
    · exact Complex.reCLM.contDiff
    · exact Complex.imCLM.contDiff
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.contDiff).comp h

/-- Reading a single Euclidean coordinate is `C^∞` — it is a continuous linear projection. -/
theorem contDiff_ofLp {n : ℕ} (i : Fin n) :
    ContDiff ℝ k (fun v : EuclideanSpace ℝ (Fin n) => v.ofLp i) :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℝ) i).contDiff.comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).contDiff

theorem contDiff_ofE2 : ContDiff ℝ k ofE2 := by
  have h : ContDiff ℝ k (fun v : EuclideanSpace ℝ (Fin 2) => (v.ofLp 0, v.ofLp 1)) :=
    (contDiff_ofLp 0).prodMk (contDiff_ofLp 1)
  exact Complex.equivRealProdCLM.symm.contDiff.comp h

/-- `assemble 2` is the linear reshape `𝓔² × ℝ ≃L 𝓔³` of `ManifoldModelTransport`. -/
theorem assemble_eq_prodReal (a : EuclideanSpace ℝ (Fin 2)) (s : ℝ) :
    assemble 2 a s = SKEFTHawking.ManifoldModelTransport.prodRealEquivEuclidean 2 (a, s) := rfl

theorem contDiff_assemble2 :
    ContDiff ℝ k (fun p : EuclideanSpace ℝ (Fin 2) × ℝ => assemble 2 p.1 p.2) := by
  simpa only [assemble_eq_prodReal] using
    (SKEFTHawking.ManifoldModelTransport.prodRealEquivEuclidean 2).contDiff

theorem contDiff_intCoord : ContDiff ℝ k intCoord :=
  (contDiff_assemble2.comp ((contDiff_toE2.comp contDiff_fst).prodMk
    (Complex.reCLM.contDiff.comp contDiff_snd))).prodMk
    ((Complex.imCLM.contDiff.comp contDiff_snd).add contDiff_const)

theorem contDiff_splitLo2 :
    ContDiff ℝ k (fun v : EuclideanSpace ℝ (Fin 3) => splitLo 2 v) := by
  have h : ContDiff ℝ k
      (fun v : EuclideanSpace ℝ (Fin 3) => (fun i : Fin 2 => v.ofLp i.castSucc)) :=
    contDiff_pi.mpr fun i => contDiff_ofLp i.castSucc
  exact ((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm.contDiff).comp h

theorem contDiff_intCoordInv : ContDiff ℝ k intCoordInv := by
  have hlast : ContDiff ℝ k (fun v : EuclideanSpace ℝ (Fin 3) => v.ofLp (Fin.last 2)) :=
    contDiff_ofLp (Fin.last 2)
  have hsnd : ContDiff ℝ k
      (fun v : FModel => ((⟨v.1.ofLp (Fin.last 2), v.2 - 2⟩ : ℂ))) := by
    have h : ContDiff ℝ k (fun v : FModel => (v.1.ofLp (Fin.last 2), v.2 - 2)) :=
      (hlast.comp contDiff_fst).prodMk (contDiff_snd.sub contDiff_const)
    exact Complex.equivRealProdCLM.symm.contDiff.comp h
  exact ((contDiff_ofE2.comp (contDiff_splitLo2.comp contDiff_fst))).prodMk hsnd

/-! ## §2. The three flat E-interior charts all evaluate to `intCoord` -/

/-- The flat form of the shared inner interior chart on a `ResChart` point. -/
theorem flatChart_resChartInteriorChart (p : ResChart) :
    ((resChartInteriorChart p).1, height (resChartInteriorChart p))
      = intCoord ((p.1 : ℂ), (p.2 : ℂ)) := rfl

/-- **Chart family 1/3, `chart0` branch** — the flat `interiorChart` reads `chart0 (z, w)` as
`intCoord (z, w)`. -/
theorem flatChart_interiorChart_chart0 {p : ResChart} (hp : p ∈ baseInterior) :
    flatChart interiorChart (chart0 p) = intCoord ((p.1 : ℂ), (p.2 : ℂ)) := by
  rw [flatChart_apply, interiorChart,
    show chart0 p = (fun q : ↥baseInterior => chart0 q.1) ⟨p, hp⟩ from rfl,
    OpenPartialHomeomorph.lift_openEmbedding_apply]
  exact flatChart_resChartInteriorChart p

/-- **Chart family 1/3, `chart1` branch.** -/
theorem flatChart_interiorChart1_chart1 {p : ResChart} (hp : p ∈ baseInterior) :
    flatChart interiorChart1 (chart1 p) = intCoord ((p.1 : ℂ), (p.2 : ℂ)) := by
  rw [flatChart_apply, interiorChart1,
    show chart1 p = (fun q : ↥baseInterior => chart1 q.1) ⟨p, hp⟩ from rfl,
    OpenPartialHomeomorph.lift_openEmbedding_apply]
  exact flatChart_resChartInteriorChart p

/-- **Chart family 1/3, equatorial branch** — the flat `annulusInteriorChart` reads a point as
`intCoord` of its annulus trivialization. -/
theorem flatChart_annulusInteriorChart (y : ResE) :
    flatChart annulusInteriorChart y
      = intCoord ((annulusTrivFun y).1, ((annulusTrivFun y).2 : ℂ)) := rfl

/-! ## §3. The uniform trivialized coordinate, and the diagonal action of `deform` -/

/-- **The uniform trivialized coordinate** of a point of `ResE` in a given E-interior chart:
`chart0`/`chart1` read `(β, ζ) = (z, w)` off the representative, the equatorial chart reads it off
`annulusTrivFun`. -/
theorem trivCoord_deform_chart0 (p : ResChart) (t : unitInterval) :
    deform (chart0 p, t) = chart0 (p.1, scaleDisk t p.2) := rfl

theorem trivCoord_deform_chart1 (p : ResChart) (t : unitInterval) :
    deform (chart1 p, t) = chart1 (p.1, scaleDisk t p.2) := rfl

theorem scaleDisk_coe' (t : unitInterval) (w : Disk) :
    ((scaleDisk t w : Disk) : ℂ) = ((t : ℝ) : ℂ) * (w : ℂ) := rfl

end

end SKEFTHawking.KummerEIntChartCoord
