/-
# Phase 5q.H — K6′b Leg 22: the E-INTERIOR ↔ SEAM transition class (1,3)

Legs 17–21 built the analytic substrate; this module closes the **set-level** residual and with it
the ordered transition class (1,3) of the weld atlas (and its `symm` mirror (3,1)).

**The generic shape.** Both halves of the transition are one generic composite each:

    seamFwdG S x₀ p = (rp3Coord x₀ (S (intCoordInv p)), 1 − ‖(intCoordInv p).2‖)
    seamBwdG R x₀ v = intCoord ((R (seamLift x₀ v.1)).1, (1 − v.2) · (R (seamLift x₀ v.1)).2)

parameterised by a **section builder** `S : ℂ² → ℂ²` (a smooth right inverse of the branch's Hopf
coordinates) and its **coordinate reader** `R`. The three E-interior chart branches instantiate the
pair `(S, R)` three ways — chart-0 by `(seamSectionAt m ∘ dir, hopf0)`, chart-1 by the same section
*swapped* (`hopf1 (swap x) = hopf0 x` is definitional), and the equatorial branch by the section at
the *rotated* fiber phase with the `regDir`-twisted reader — so §1's two smoothness lemmas are proved
once and used three times.

**The four set-level facts** (§3):

* distinct components have empty overlap — `weldMk (inr (c, z))` lies in `seamCompNbhd c'` only for
  `c' = c`, by saturation of the per-component carrier (`preimage_image_seamCompCarrier`);
* the collar parameter of an overlap point is **strictly** inside `(0, 1/2)` — the E-side carrier is
  the fiber-radius-`> 1/2` locus and the interior is the `< 1` locus;
* the branch sign is free — `mkRP3_seamPointAt_neg` lets the section be normalised into whichever
  hemisphere the `ℝP³` chart at `r₀` needs;
* the `cc ∈ atlasEInt` dispatch is the three-way `rcases`.

**The inverse comes for free.** Rather than a second set-level analysis, §2 proves the *round trip*
`seamBwdG R x₀ (seamFwdG S x₀ p) = p` as pure algebra; the inverse identification then follows from
surjectivity of the transition onto its target.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerSeamTransCoord
import SKEFTHawking.KummerInteriorManifold
import SKEFTHawking.KummerSeamTransition

namespace SKEFTHawking.KummerSeamTransE

open Set Topology
open scoped Manifold RealInnerProductSpace
open SKEFTHawking.KummerK3Base
open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerRP3SphereHomeo (sphToS3 sphHomeoS3)
open SKEFTHawking.KummerResolutionPieceBoundary
open SKEFTHawking.KummerWeldFiberFlow
open SKEFTHawking.HalfSpaceInteriorFlatten
open SKEFTHawking.KummerSeamSmooth
open SKEFTHawking.KummerSeamSection
open SKEFTHawking.KummerSeamSectionAt
open SKEFTHawking.KummerSeamCollarCoord
open SKEFTHawking.KummerEIntChartCoord
open SKEFTHawking.KummerRP3ChartCoord
open SKEFTHawking.KummerRP3Smooth
open SKEFTHawking.KummerRP3EuclCharts
open SKEFTHawking.KummerEInteriorChart
open SKEFTHawking.KummerWeldOpenPieces (interiorE isOpen_interiorE eInteriorCopy
  isOpenEmbedding_eInteriorCopy)
open SKEFTHawking.KummerSeamTransCoord

noncomputable section

variable {k : WithTop ℕ∞}

/-! ## §1. The two generic halves -/

/-- **The hemisphere domain in pinned `ℂ²` coordinates** — the open locus on which the pinned `ℝP³`
chart at `x₀` may be evaluated through `rp3Coord`. -/
def hemiDom (x₀ : S3E) : Set (ℂ × ℂ) := {q : ℂ × ℂ | 0 < ⟪(x₀ : E4), c2ToEuc q⟫}

theorem isOpen_hemiDom (x₀ : S3E) : IsOpen (hemiDom x₀) := by
  refine isOpen_lt continuous_const ?_
  exact (innerSL ℝ (x₀ : E4)).continuous.comp continuous_c2ToEuc

theorem hemiDom_subset_rp3CoordDom (x₀ : S3E) : hemiDom x₀ ⊆ rp3CoordDom x₀ := by
  intro q hq
  have hpos : 0 < ⟪(x₀ : E4), c2ToEuc q⟫ := hq
  show innerSL ℝ ((-x₀ : S3E) : E4) (c2ToEuc q) ≠ 1
  rw [innerSL_apply_apply, show ((-x₀ : S3E) : E4) = -(x₀ : E4) from rfl, inner_neg_left]
  intro heq; linarith

/-- A pinned `S³` point whose coordinates are in `hemiDom x₀` lies in the `x₀`-hemisphere. -/
theorem s3ToSphE_mem_hemi {x₀ : S3E} {σ : S3} (hq : (σ : ℂ × ℂ) ∈ hemiDom x₀) :
    s3ToSphE σ ∈ hemi x₀ := hq

/-- **The generic forward half** of the E-interior ↔ seam transition. -/
def seamFwdG (S : ℂ × ℂ → ℂ × ℂ) (x₀ : S3E) (p : FModel) : FModel :=
  (rp3Coord x₀ (S (intCoordInv p)), 1 - ‖(intCoordInv p).2‖)

/-- The open set on which `seamFwdG S x₀` is defined. -/
def seamFwdGDom (S : ℂ × ℂ → ℂ × ℂ) (DS : Set (ℂ × ℂ)) (x₀ : S3E) : Set FModel :=
  ({p : FModel | (intCoordInv p).2 ≠ 0} ∩ intCoordInv ⁻¹' DS)
    ∩ (fun p : FModel => S (intCoordInv p)) ⁻¹' hemiDom x₀

theorem isOpen_seamFwdGDom {S : ℂ × ℂ → ℂ × ℂ} {DS : Set (ℂ × ℂ)} (hDS : IsOpen DS)
    (hS : ContinuousOn S DS) (x₀ : S3E) : IsOpen (seamFwdGDom S DS x₀) := by
  have h1 : IsOpen ({p : FModel | (intCoordInv p).2 ≠ 0} ∩ intCoordInv ⁻¹' DS) :=
    (isOpen_compl_singleton.preimage (continuous_snd.comp continuous_intCoordInv)).inter
      (hDS.preimage continuous_intCoordInv)
  refine ContinuousOn.isOpen_inter_preimage ?_ h1 (isOpen_hemiDom x₀)
  exact hS.comp continuous_intCoordInv.continuousOn (fun _ hp => hp.2)

/-- **The generic forward half is `C^k`.** -/
theorem contDiffOn_seamFwdG {S : ℂ × ℂ → ℂ × ℂ} {DS : Set (ℂ × ℂ)}
    (hS : ContDiffOn ℝ k S DS) (x₀ : S3E) :
    ContDiffOn ℝ k (seamFwdG S x₀) (seamFwdGDom S DS x₀) := by
  have hsec : ContDiffOn ℝ k (fun p : FModel => S (intCoordInv p)) (seamFwdGDom S DS x₀) :=
    hS.comp contDiff_intCoordInv.contDiffOn (fun _ hp => hp.1.2)
  refine ContDiffOn.prodMk ?_ ?_
  · exact (contDiffOn_rp3Coord x₀).comp hsec (fun _ hp => hemiDom_subset_rp3CoordDom x₀ hp.2)
  · exact contDiffOn_const.sub
      ((contDiff_snd.comp contDiff_intCoordInv).contDiffOn.norm ℝ (fun _ hp => hp.1.1))

/-- **The generic backward half** of the E-interior ↔ seam transition. -/
def seamBwdG (R : ℂ × ℂ → ℂ × ℂ) (x₀ : S3E) (v : FModel) : FModel :=
  intCoord ((R (seamLift x₀ v.1)).1, ((1 - v.2 : ℝ) : ℂ) * (R (seamLift x₀ v.1)).2)

/-- The open set on which `seamBwdG R x₀` is defined. -/
def seamBwdGDom (DR : Set (ℂ × ℂ)) (x₀ : S3E) : Set FModel :=
  (fun v : FModel => seamLift x₀ v.1) ⁻¹' DR

theorem isOpen_seamBwdGDom {DR : Set (ℂ × ℂ)} (hDR : IsOpen DR) (x₀ : S3E) :
    IsOpen (seamBwdGDom DR x₀) :=
  hDR.preimage ((contDiff_seamLift (k := (0 : WithTop ℕ∞)) x₀).continuous.comp continuous_fst)

/-- **The generic backward half is `C^k`.** -/
theorem contDiffOn_seamBwdG {R : ℂ × ℂ → ℂ × ℂ} {DR : Set (ℂ × ℂ)}
    (hR : ContDiffOn ℝ k R DR) (x₀ : S3E) :
    ContDiffOn ℝ k (seamBwdG R x₀) (seamBwdGDom DR x₀) := by
  have hlift : ContDiffOn ℝ k (fun v : FModel => seamLift x₀ v.1) (seamBwdGDom DR x₀) :=
    ((contDiff_seamLift x₀).comp contDiff_fst).contDiffOn
  have hR' : ContDiffOn ℝ k (fun v : FModel => R (seamLift x₀ v.1)) (seamBwdGDom DR x₀) :=
    hR.comp hlift (fun _ hv => hv)
  have hscale : ContDiffOn ℝ k (fun v : FModel => (((1 - v.2 : ℝ) : ℂ))) (seamBwdGDom DR x₀) :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_const.sub contDiff_snd)).contDiffOn
  exact contDiff_intCoord.comp_contDiffOn (hR'.fst.prodMk (hscale.mul hR'.snd))

/-! ## §2. The round trip — the inverse identification for free -/

/-- `intCoord` is a two-sided inverse of `intCoordInv` (the other half of Leg 18's §1). -/
@[simp] theorem intCoord_intCoordInv (v : FModel) : intCoord (intCoordInv v) = v := by
  refine Prod.ext ?_ ?_
  · show SKEFTHawking.DiskChartGeneric.assemble 2
      (toE2 (ofE2 (SKEFTHawking.DiskChartGeneric.splitLo 2 v.1)))
      (⟨v.1.ofLp (Fin.last 2), v.2 - 2⟩ : ℂ).re = v.1
    rw [show (⟨v.1.ofLp (Fin.last 2), v.2 - 2⟩ : ℂ).re = v.1.ofLp (Fin.last 2) from rfl,
      toE2_ofE2]
    exact SKEFTHawking.DiskChartGeneric.assemble_splitLo 2 v.1
  · show (⟨v.1.ofLp (Fin.last 2), v.2 - 2⟩ : ℂ).im + 2 = v.2
    show v.2 - 2 + 2 = v.2
    ring

/-- The unit direction rescaled by the modulus recovers the number. -/
theorem norm_mul_fiberDir {w : ℂ} (hw : w ≠ 0) : ((‖w‖ : ℝ) : ℂ) * fiberDir w = w := by
  have hn : ((‖w‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hw
  rw [KummerSeamCollarCoord.fiberDir]; field_simp

/-- **The `ℝP³` coordinate is inverted by the lift** on the hemisphere: reading a pinned `S³` point
in the `x₀`-chart and lifting the result back returns the point. -/
theorem seamLift_rp3Coord {x₀ : S3E} {σ : S3} (hs : s3ToSphE σ ∈ hemi x₀) :
    seamLift x₀ (rp3Coord x₀ (σ : ℂ × ℂ)) = (σ : ℂ × ℂ) := by
  have hval : rp3Coord x₀ (σ : ℂ × ℂ) = Φ x₀ (s3ToSphE σ) := by
    rw [chartAt_S3E_apply]; rfl
  rw [hval, seamLift, (Φ x₀).left_inv (hemi_subset_source x₀ hs)]
  exact eucToC2_c2ToEuc (σ : ℂ × ℂ)

/-- **THE ROUND TRIP.** Whenever the section builder `S` lands on `S³` inside the `x₀`-hemisphere
and the reader `R` inverts it back to the Hopf datum `(β, ζ/‖ζ‖)`, the generic backward half undoes
the generic forward half. This is what makes the inverse direction of the transition free of a
second set-level analysis. -/
theorem seamBwdG_seamFwdG {R S : ℂ × ℂ → ℂ × ℂ} {x₀ : S3E} {p : FModel}
    (hζ : (intCoordInv p).2 ≠ 0)
    (hσ : ‖(S (intCoordInv p)).1‖ ^ 2 + ‖(S (intCoordInv p)).2‖ ^ 2 = 1)
    (hhemi : S (intCoordInv p) ∈ hemiDom x₀)
    (hR : R (S (intCoordInv p)) = ((intCoordInv p).1, fiberDir (intCoordInv p).2)) :
    seamBwdG R x₀ (seamFwdG S x₀ p) = p := by
  set σ : S3 := ⟨S (intCoordInv p), hσ⟩ with hσdef
  have hlift : seamLift x₀ (seamFwdG S x₀ p).1 = S (intCoordInv p) :=
    seamLift_rp3Coord (σ := σ) (s3ToSphE_mem_hemi (σ := σ) hhemi)
  rw [seamBwdG, hlift, hR]
  have h2 : ((1 - (seamFwdG S x₀ p).2 : ℝ) : ℂ) = ((‖(intCoordInv p).2‖ : ℝ) : ℂ) := by
    norm_num [seamFwdG]
  rw [h2, norm_mul_fiberDir hζ, intCoord_intCoordInv]

/-! ## §3. The three branch instantiations of `(S, R)` -/

/-- The **chart-0 branch** section builder: the based section at the fiber direction. -/
def sectE (m : ℂ) (q : ℂ × ℂ) : ℂ × ℂ :=
  seamSectionAt m (q.1, KummerSeamCollarCoord.fiberDir q.2)

/-- The **chart-1 branch** section builder: the chart-0 one, swapped
(`hopf1 (swap x) = hopf0 x` is definitional). -/
def sectE1 (m : ℂ) (q : ℂ × ℂ) : ℂ × ℂ := Prod.swap (sectE m q)

/-- The **equatorial branch** section builder: the chart-0 one at the `regDir`-rotated fiber
phase `ζ/‖ζ‖ · ‖β‖/β`. -/
def sectEA (m : ℂ) (q : ℂ × ℂ) : ℂ × ℂ :=
  seamSectionAt m (q.1, KummerSeamCollarCoord.fiberDir q.2 * ((‖q.1‖ : ℝ) : ℂ) / q.1)

/-- The domain of the chart-0 / chart-1 section builders. -/
def sectEDom (m : ℂ) : Set (ℂ × ℂ) :=
  {q : ℂ × ℂ | q.2 ≠ 0}
    ∩ (fun q : ℂ × ℂ => (q.1, KummerSeamCollarCoord.fiberDir q.2)) ⁻¹' seamDomAt m

/-- The domain of the equatorial section builder. -/
def sectEADom (m : ℂ) : Set (ℂ × ℂ) :=
  ({q : ℂ × ℂ | q.1 ≠ 0} ∩ {q : ℂ × ℂ | q.2 ≠ 0})
    ∩ (fun q : ℂ × ℂ =>
        (q.1, KummerSeamCollarCoord.fiberDir q.2 * ((‖q.1‖ : ℝ) : ℂ) / q.1)) ⁻¹' seamDomAt m

theorem continuousOn_dirPair :
    ContinuousOn (fun q : ℂ × ℂ => (q.1, KummerSeamCollarCoord.fiberDir q.2))
      {q : ℂ × ℂ | q.2 ≠ 0} :=
  continuous_fst.continuousOn.prodMk
    ((contDiffOn_fiberDir (k := (0 : WithTop ℕ∞))).continuousOn.comp
      continuous_snd.continuousOn (fun _ hq => hq))

theorem isOpen_snd_ne_zero : IsOpen {q : ℂ × ℂ | q.2 ≠ 0} :=
  isOpen_compl_singleton.preimage continuous_snd

theorem isOpen_fst_ne_zero : IsOpen {q : ℂ × ℂ | q.1 ≠ 0} :=
  isOpen_compl_singleton.preimage continuous_fst

theorem isOpen_sectEDom (m : ℂ) : IsOpen (sectEDom m) :=
  continuousOn_dirPair.isOpen_inter_preimage isOpen_snd_ne_zero (isOpen_seamDomAt m)

theorem contDiffOn_dirPair :
    ContDiffOn ℝ k (fun q : ℂ × ℂ => (q.1, KummerSeamCollarCoord.fiberDir q.2))
      {q : ℂ × ℂ | q.2 ≠ 0} :=
  contDiff_fst.contDiffOn.prodMk
    (contDiffOn_fiberDir.comp contDiff_snd.contDiffOn (fun _ hq => hq))

theorem contDiffOn_sectE (m : ℂ) : ContDiffOn ℝ k (sectE m) (sectEDom m) :=
  (contDiffOn_seamSectionAt m).comp (contDiffOn_dirPair.mono Set.inter_subset_left)
    (fun _ hq => hq.2)

theorem contDiffOn_sectE1 (m : ℂ) : ContDiffOn ℝ k (sectE1 m) (sectEDom m) :=
  ((contDiffOn_sectE m).snd).prodMk ((contDiffOn_sectE m).fst)

theorem contDiffOn_twistPair :
    ContDiffOn ℝ k
      (fun q : ℂ × ℂ =>
        (q.1, KummerSeamCollarCoord.fiberDir q.2 * ((‖q.1‖ : ℝ) : ℂ) / q.1))
      ({q : ℂ × ℂ | q.1 ≠ 0} ∩ {q : ℂ × ℂ | q.2 ≠ 0}) := by
  have hfst : ContDiffOn ℝ k (fun q : ℂ × ℂ => q.1)
      ({q : ℂ × ℂ | q.1 ≠ 0} ∩ {q : ℂ × ℂ | q.2 ≠ 0}) := contDiff_fst.contDiffOn
  have hdir : ContDiffOn ℝ k (fun q : ℂ × ℂ => KummerSeamCollarCoord.fiberDir q.2)
      ({q : ℂ × ℂ | q.1 ≠ 0} ∩ {q : ℂ × ℂ | q.2 ≠ 0}) :=
    contDiffOn_fiberDir.comp contDiff_snd.contDiffOn (fun _ hq => hq.2)
  have hnorm : ContDiffOn ℝ k (fun q : ℂ × ℂ => ((‖q.1‖ : ℝ) : ℂ))
      ({q : ℂ × ℂ | q.1 ≠ 0} ∩ {q : ℂ × ℂ | q.2 ≠ 0}) :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn
      (hfst.norm ℝ (fun (q : ℂ × ℂ) (hq : q ∈ ({q : ℂ × ℂ | q.1 ≠ 0} ∩ {q : ℂ × ℂ | q.2 ≠ 0})) =>
        hq.1))
  have hnum : ContDiffOn ℝ k
      (fun q : ℂ × ℂ => KummerSeamCollarCoord.fiberDir q.2 * ((‖q.1‖ : ℝ) : ℂ))
      ({q : ℂ × ℂ | q.1 ≠ 0} ∩ {q : ℂ × ℂ | q.2 ≠ 0}) := hdir.mul hnorm
  have hquot : ContDiffOn ℝ k
      (fun q : ℂ × ℂ => KummerSeamCollarCoord.fiberDir q.2 * ((‖q.1‖ : ℝ) : ℂ) / q.1)
      ({q : ℂ × ℂ | q.1 ≠ 0} ∩ {q : ℂ × ℂ | q.2 ≠ 0}) :=
    hnum.mul (hfst.inv (fun (q : ℂ × ℂ)
      (hq : q ∈ ({q : ℂ × ℂ | q.1 ≠ 0} ∩ {q : ℂ × ℂ | q.2 ≠ 0})) => hq.1))
  exact hfst.prodMk hquot

theorem isOpen_sectEADom (m : ℂ) : IsOpen (sectEADom m) :=
  (contDiffOn_twistPair (k := (0 : WithTop ℕ∞))).continuousOn.isOpen_inter_preimage
    (isOpen_fst_ne_zero.inter isOpen_snd_ne_zero) (isOpen_seamDomAt m)

theorem contDiffOn_sectEA (m : ℂ) : ContDiffOn ℝ k (sectEA m) (sectEADom m) :=
  (contDiffOn_seamSectionAt m).comp (contDiffOn_twistPair.mono Set.inter_subset_left)
    (fun _ hq => hq.2)

/-- The **chart-1 branch** coordinate reader. -/
def readE1 (x : ℂ × ℂ) : ℂ × ℂ := hopf0 (Prod.swap x)

/-- The **equatorial branch** coordinate reader — the `regDir` twist applied to the fiber phase. -/
def readEA (x : ℂ × ℂ) : ℂ × ℂ :=
  ((hopf0 x).1, KummerSeamCollarCoord.fiberDir (hopf0 x).1 * (hopf0 x).2)

theorem contDiffOn_readE1 : ContDiffOn ℝ k readE1 {x : ℂ × ℂ | x.1 ≠ 0} :=
  contDiffOn_hopf0.comp (contDiff_snd.prodMk contDiff_fst).contDiffOn (fun _ hx => hx)

theorem contDiffOn_readEA :
    ContDiffOn ℝ k readEA ({x : ℂ × ℂ | x.1 ≠ 0} ∩ {x : ℂ × ℂ | x.2 ≠ 0}) := by
  have hh : ContDiffOn ℝ k hopf0 ({x : ℂ × ℂ | x.1 ≠ 0} ∩ {x : ℂ × ℂ | x.2 ≠ 0}) :=
    contDiffOn_hopf0.mono (fun _ hx => hx.2)
  have hne : ∀ x ∈ ({x : ℂ × ℂ | x.1 ≠ 0} ∩ {x : ℂ × ℂ | x.2 ≠ 0}), (hopf0 x).1 ≠ 0 := by
    rintro x ⟨hx1, hx2⟩
    rw [hopf0_fst]
    exact div_ne_zero hx1 hx2
  exact hh.fst.prodMk ((contDiffOn_fiberDir.comp hh.fst hne).mul hh.snd)

/-! ## §4. Each reader inverts its section builder back to the Hopf datum -/

theorem readE_sectE {m : ℂ} (hm : ‖m‖ = 1) {q : ℂ × ℂ} (hq : q ∈ sectEDom m) :
    hopf0 (sectE m q) = (q.1, KummerSeamCollarCoord.fiberDir q.2) :=
  hopf0_seamSectionAt hm (norm_fiberDir hq.1) hq.2

theorem readE1_sectE1 {m : ℂ} (hm : ‖m‖ = 1) {q : ℂ × ℂ} (hq : q ∈ sectEDom m) :
    readE1 (sectE1 m q) = (q.1, KummerSeamCollarCoord.fiberDir q.2) := by
  rw [readE1, sectE1, Prod.swap_swap]
  exact readE_sectE hm hq

theorem norm_twist {q : ℂ × ℂ} (hβ : q.1 ≠ 0) (hζ : q.2 ≠ 0) :
    ‖KummerSeamCollarCoord.fiberDir q.2 * ((‖q.1‖ : ℝ) : ℂ) / q.1‖ = 1 := by
  rw [norm_div, norm_mul, norm_fiberDir hζ, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_norm, div_self (norm_ne_zero_iff.mpr hβ)]

theorem readEA_sectEA {m : ℂ} (hm : ‖m‖ = 1) {q : ℂ × ℂ} (hq : q ∈ sectEADom m) :
    readEA (sectEA m q) = (q.1, KummerSeamCollarCoord.fiberDir q.2) := by
  have hβ : q.1 ≠ 0 := hq.1.1
  have hζ : q.2 ≠ 0 := hq.1.2
  have h0 : hopf0 (sectEA m q)
      = (q.1, KummerSeamCollarCoord.fiberDir q.2 * ((‖q.1‖ : ℝ) : ℂ) / q.1) :=
    hopf0_seamSectionAt hm (norm_twist hβ hζ) hq.2
  rw [readEA, h0]
  refine Prod.ext rfl ?_
  have hn : ((‖q.1‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hβ
  show KummerSeamCollarCoord.fiberDir q.1
      * (KummerSeamCollarCoord.fiberDir q.2 * ((‖q.1‖ : ℝ) : ℂ) / q.1)
    = KummerSeamCollarCoord.fiberDir q.2
  rw [show KummerSeamCollarCoord.fiberDir q.1 = q.1 / ((‖q.1‖ : ℝ) : ℂ) from rfl]
  field_simp

/-! ## §5. The seam chart on a point presented by its seam parametrization -/

open SKEFTHawking.KummerWeld (EIndex weldMk KummerK3)
open SKEFTHawking.KummerSeamChart
open SKEFTHawking.KummerSeamComponentOpen (seamCompCarrier seamCompNbhd
  preimage_image_seamCompCarrier)
open SKEFTHawking.KummerSeamOpenNbhd (eOpenSet)

/-- The `S³_𝔼` base point of the pinned `ℝP³` chart at `r₀`. -/
def pinPt (r₀ : RP3) : S3E := (rp3ToRP3E r₀).out

theorem chartAt_rp3_eq (r₀ : RP3) : chartAt E3 r₀ = rp3PinChart (pinPt r₀) := rfl

/-- **THE SEAM CHART ON A PARAMETRIZED POINT.** A point presented as `seamParam c (mkRP3 σ, v)` is
read by the `r₀`-seam chart as `(rp3Coord (pinPt r₀) σ, v)` — provided the pinned lift of `σ` sits
in the chart's hemisphere. -/
theorem seamChart_seamParam (c : EIndex) (r₀ : RP3) {σ : S3} (v : ↥openParam)
    (hs : s3ToSphE σ ∈ hemi (pinPt r₀)) :
    seamChart c r₀ (seamParam c (mkRP3 σ, v)) = (rp3Coord (pinPt r₀) (σ : ℂ × ℂ), (v : ℝ)) := by
  have hsymm : (seamParamHomeo c).symm (seamParam c (mkRP3 σ, v)) = (mkRP3 σ, v) :=
    (seamParamHomeo c).left_inv (by trivial)
  show ((chartAt E3 r₀).prod paramChart) ((seamParamHomeo c).symm (seamParam c (mkRP3 σ, v))) = _
  rw [hsymm]
  refine Prod.ext ?_ rfl
  show chartAt E3 r₀ (mkRP3 σ) = _
  rw [chartAt_rp3_eq, rp3PinChart_mkRP3_eq_rp3Coord _ hs]

/-! ## §6. The two set-level facts about the E-side of a seam neighbourhood -/

/-- **Component separation and the strict collar band.** An E-interior copy point that lies in the
`c'`-th seam neighbourhood forces `c = c'` (the sixteen per-component carriers are saturated and
pairwise disjoint on the `inr` side) and has fiber radius **strictly** greater than `1/2`. -/
theorem eq_and_band_of_mem_seamCompNbhd {c c' : EIndex} {z : ResE}
    (h : weldMk (Sum.inr (c, z)) ∈ seamCompNbhd c') : c = c' ∧ 1 / 2 < fiberNorm z := by
  have hcar : (Sum.inr (c, z) : SKEFTHawking.KummerWeld.WeldCarrier) ∈ seamCompCarrier c' := by
    rw [← preimage_image_seamCompCarrier c']
    exact h
  rcases hcar with ⟨y, -, hy⟩ | ⟨w, hw, hwz⟩
  · exact absurd hy (by simp)
  · have hw' : w = (c, z) := Sum.inr.inj hwz
    subst hw'
    exact ⟨hw.1, hw.2⟩

/-! ## §7. The three branch identifications -/

theorem exists_chart0_of_mem_interiorChart_source {x : ResE} (hx : x ∈ interiorChart.source) :
    ∃ q : ResChart, ‖(q.1 : ℂ)‖ < 1 ∧ x = chart0 q := by
  rw [interiorChart, OpenPartialHomeomorph.lift_openEmbedding_source] at hx
  obtain ⟨q, -, rfl⟩ := hx
  exact ⟨q.val, q.property, rfl⟩

theorem exists_chart1_of_mem_interiorChart1_source {x : ResE} (hx : x ∈ interiorChart1.source) :
    ∃ q : ResChart, ‖(q.1 : ℂ)‖ < 1 ∧ x = chart1 q := by
  rw [interiorChart1, OpenPartialHomeomorph.lift_openEmbedding_source] at hx
  obtain ⟨q, -, rfl⟩ := hx
  exact ⟨q.val, q.property, rfl⟩

theorem mem_annulusRegion_of_mem_annulusInteriorChart_source {x : ResE}
    (hx : x ∈ annulusInteriorChart.source) : x ∈ annulusRegion := by
  rw [annulusInteriorChart, OpenPartialHomeomorph.trans_source] at hx
  exact hx.1

theorem eIntChart_apply (cc : OpenPartialHomeomorph ResE HModel) (z : ↥interiorE) :
    eIntChart cc z = flatChart cc (z : ResE) := rfl

/-- **THE CHART-0 BRANCH IDENTIFICATION.** -/
theorem seamParam_eq_of_interiorChart (c : EIndex) {m : ℂ} (hm : ‖m‖ = 1) {z : ↥interiorE}
    (hz : (z : ResE) ∈ interiorChart.source) (hband : 1 / 2 < fiberNorm (z : ResE))
    (hdom : intCoordInv (eIntChart interiorChart z) ∈ sectEDom m)
    {σ : S3} (hσ : (σ : ℂ × ℂ) = sectE m (intCoordInv (eIntChart interiorChart z)))
    {v : ↥openParam} (hv : (v : ℝ) = 1 - ‖(intCoordInv (eIntChart interiorChart z)).2‖) :
    seamParam c (mkRP3 σ, v) = weldMk (Sum.inr (c, (z : ResE))) := by
  obtain ⟨q, hq1, hzq⟩ := exists_chart0_of_mem_interiorChart_source hz
  have hcoord : intCoordInv (eIntChart interiorChart z) = ((q.1 : ℂ), (q.2 : ℂ)) := by
    rw [eIntChart_apply, hzq, flatChart_interiorChart_chart0 hq1, intCoordInv_intCoord]
  rw [hcoord] at hdom hσ hv
  have hw0 : (q.2 : ℂ) ≠ 0 := hdom.1
  have hw1 : 1 / 2 < ‖(q.2 : ℂ)‖ := by rw [hzq, fiberNorm_chart0] at hband; exact hband
  have hw2 : ‖(q.2 : ℂ)‖ ≤ 1 := q.2.2
  have hd : ((q.1 : ℂ), KummerSeamCollarCoord.fiberDir (q.2 : ℂ)) ∈ seamDomAt m := hdom.2
  have hkey := seamParam_eq_weldMk_chart0 c hm (le_of_lt hq1) hw0 hw1 hw2 hd
  have hσeq : σ = seamPointAt hm hd := Subtype.ext hσ
  have hveq : v = ⟨1 - ‖(q.2 : ℂ)‖, by
      constructor
      · show -(1 / 8 : ℝ) < 1 - ‖(q.2 : ℂ)‖; linarith
      · show 1 - ‖(q.2 : ℂ)‖ < 1 / 2; linarith⟩ := Subtype.ext hv
  rw [hσeq, hveq, hkey, hzq]

/-- **THE CHART-1 BRANCH IDENTIFICATION.** -/
theorem seamParam_eq_of_interiorChart1 (c : EIndex) {m : ℂ} (hm : ‖m‖ = 1) {z : ↥interiorE}
    (hz : (z : ResE) ∈ interiorChart1.source) (hband : 1 / 2 < fiberNorm (z : ResE))
    (hdom : intCoordInv (eIntChart interiorChart1 z) ∈ sectEDom m)
    {σ : S3} (hσ : (σ : ℂ × ℂ) = sectE1 m (intCoordInv (eIntChart interiorChart1 z)))
    {v : ↥openParam} (hv : (v : ℝ) = 1 - ‖(intCoordInv (eIntChart interiorChart1 z)).2‖) :
    seamParam c (mkRP3 σ, v) = weldMk (Sum.inr (c, (z : ResE))) := by
  obtain ⟨q, hq1, hzq⟩ := exists_chart1_of_mem_interiorChart1_source hz
  have hcoord : intCoordInv (eIntChart interiorChart1 z) = ((q.1 : ℂ), (q.2 : ℂ)) := by
    rw [eIntChart_apply, hzq, flatChart_interiorChart1_chart1 hq1, intCoordInv_intCoord]
  rw [hcoord] at hdom hσ hv
  have hw0 : (q.2 : ℂ) ≠ 0 := hdom.1
  have hw1 : 1 / 2 < ‖(q.2 : ℂ)‖ := by rw [hzq, fiberNorm_chart1] at hband; exact hband
  have hw2 : ‖(q.2 : ℂ)‖ ≤ 1 := q.2.2
  have hd : ((q.1 : ℂ), KummerSeamCollarCoord.fiberDir (q.2 : ℂ)) ∈ seamDomAt m := hdom.2
  have hkey := seamParam_eq_weldMk_chart1 c hm hq1 hw0 hw1 hw2 hd
  have hσeq : σ = seamPointAt1 hm hd := Subtype.ext hσ
  have hveq : v = ⟨1 - ‖(q.2 : ℂ)‖, by
      constructor
      · show -(1 / 8 : ℝ) < 1 - ‖(q.2 : ℂ)‖; linarith
      · show 1 - ‖(q.2 : ℂ)‖ < 1 / 2; linarith⟩ := Subtype.ext hv
  rw [hσeq, hveq, hkey, hzq]

/-- **The equatorial section point is near the Hopf equator** — its two `ℂ` coordinates have norms
`ρ(β)·‖β‖` and `ρ(β)`, so `1/2 < ‖β‖ < 2` (the annulus condition) is exactly `nearEquator`. -/
theorem seamPointAt_mem_nearEquator {m : ℂ} (hm : ‖m‖ = 1) {q : ℂ × ℂ} (h : q ∈ seamDomAt m)
    (hlo : 1 / 2 < ‖q.1‖) (hhi : ‖q.1‖ < 2) :
    ((seamPointAt hm h : S3) : ℂ × ℂ) ∈ nearEquator := by
  have hρ := seamRho_pos q.1
  have hfst : ‖((seamPointAt hm h : S3) : ℂ × ℂ).1‖ = seamRho q.1 * ‖q.1‖ := by
    rw [seamPointAt_coe, norm_seamSectionAt_fst hm q]
    exact norm_seamSection0_fst (q := (q.1, q.2 / m ^ 2)) h
  have hsnd : ‖((seamPointAt hm h : S3) : ℂ × ℂ).2‖ = seamRho q.1 := by
    rw [seamPointAt_coe, norm_seamSectionAt_snd hm q]
    exact norm_seamSection0_snd (q := (q.1, q.2 / m ^ 2)) h
  constructor
  · rw [hfst, hsnd]; nlinarith
  · rw [hfst, hsnd]; nlinarith

/-- **THE EQUATORIAL BRANCH IDENTIFICATION.** -/
theorem seamParam_eq_of_annulusInteriorChart (c : EIndex) {m : ℂ} (hm : ‖m‖ = 1) {z : ↥interiorE}
    (hz : (z : ResE) ∈ annulusInteriorChart.source) (hband : 1 / 2 < fiberNorm (z : ResE))
    (hdom : intCoordInv (eIntChart annulusInteriorChart z) ∈ sectEADom m)
    {σ : S3} (hσ : (σ : ℂ × ℂ) = sectEA m (intCoordInv (eIntChart annulusInteriorChart z)))
    {v : ↥openParam} (hv : (v : ℝ) = 1 - ‖(intCoordInv (eIntChart annulusInteriorChart z)).2‖) :
    seamParam c (mkRP3 σ, v) = weldMk (Sum.inr (c, (z : ResE))) := by
  have hx : (z : ResE) ∈ annulusRegion :=
    mem_annulusRegion_of_mem_annulusInteriorChart_source hz
  have hcoord : intCoordInv (eIntChart annulusInteriorChart z)
      = ((annulusTrivFun (z : ResE)).1, ((annulusTrivFun (z : ResE)).2 : ℂ)) := by
    rw [eIntChart_apply, flatChart_annulusInteriorChart, intCoordInv_intCoord]
  rw [hcoord] at hdom hσ hv
  obtain ⟨hlo, hhi⟩ := annulusTriv_mapsTo hx
  have hβ0 : (annulusTrivFun (z : ResE)).1 ≠ 0 :=
    norm_ne_zero_iff.mp (ne_of_gt (lt_trans (by norm_num) hlo))
  have hζ0 : ((annulusTrivFun (z : ResE)).2 : ℂ) ≠ 0 := hdom.1.2
  have hζ1 : 1 / 2 < ‖((annulusTrivFun (z : ResE)).2 : ℂ)‖ := by
    rw [SKEFTHawking.KummerSeamCollarSmooth.norm_annulusTrivFun_snd hx]; exact hband
  have hd : ((annulusTrivFun (z : ResE)).1,
      KummerSeamCollarCoord.fiberDir ((annulusTrivFun (z : ResE)).2 : ℂ)
        * ((‖(annulusTrivFun (z : ResE)).1‖ : ℝ) : ℂ) / (annulusTrivFun (z : ResE)).1)
      ∈ seamDomAt m := hdom.2
  have hne : ((seamPointAt hm hd : S3) : ℂ × ℂ) ∈ nearEquator :=
    seamPointAt_mem_nearEquator hm hd hlo hhi
  have hkey := seamParam_eq_weldMk_annulus c hm hx hβ0 hζ0 hζ1 hd hne
  have hσeq : σ = seamPointAt hm hd := Subtype.ext hσ
  have hveq : v = ⟨1 - ‖((annulusTrivFun (z : ResE)).2 : ℂ)‖, by
      have h2 := (annulusTrivFun (z : ResE)).2.2
      constructor
      · show -(1 / 8 : ℝ) < 1 - ‖((annulusTrivFun (z : ResE)).2 : ℂ)‖; linarith
      · show 1 - ‖((annulusTrivFun (z : ResE)).2 : ℂ)‖ < 1 / 2; linarith⟩ := Subtype.ext hv
  rw [hσeq, hveq, hkey]

/-! ## §8. The branch record, and the three instances -/

theorem seamSectionAt_snd_ne_zero {m : ℂ} (hm : ‖m‖ = 1) {q : ℂ × ℂ} (h : q ∈ seamDomAt m) :
    (seamSectionAt m q).2 ≠ 0 := by
  refine norm_ne_zero_iff.mp (ne_of_gt ?_)
  rw [norm_seamSectionAt_snd hm q, norm_seamSection0_snd (q := (q.1, q.2 / m ^ 2)) h]
  exact seamRho_pos q.1

theorem seamSectionAt_fst_ne_zero {m : ℂ} (hm : ‖m‖ = 1) {q : ℂ × ℂ} (h : q ∈ seamDomAt m)
    (hβ : q.1 ≠ 0) : (seamSectionAt m q).1 ≠ 0 := by
  refine norm_ne_zero_iff.mp (ne_of_gt ?_)
  rw [norm_seamSectionAt_fst hm q, norm_seamSection0_fst (q := (q.1, q.2 / m ^ 2)) h]
  exact mul_pos (seamRho_pos q.1) (norm_pos_iff.mpr hβ)

/-- Every fiber phase admits a square-root base, so the based section's domain is never empty:
`1 + u/m² = 2 ≠ 0` at `m² = u`. -/
theorem exists_mem_seamDomAt {u : ℂ} (hu : ‖u‖ = 1) (β : ℂ) :
    ∃ m : ℂ, ‖m‖ = 1 ∧ (β, u) ∈ seamDomAt m := by
  obtain ⟨m, hm, hsq⟩ := exists_sq_eq_of_norm_one hu
  exact ⟨m, hm, hsq ▸ mem_seamDomAt_base hm β⟩

/-- **ONE BRANCH OF THE E-INTERIOR ATLAS**, packaged with everything the (1,3) transition assembly
consumes: the half-space chart, the branch's smooth section builder `sect` (indexed by the
square-root base `m`) and coordinate reader `read`, and the branch's own seam identification. The
assembly of §9 is written once against this record and instantiated three times. -/
structure EBranch where
  /-- The half-space chart of `ResE` this branch flattens. -/
  chart : OpenPartialHomeomorph ResE HModel
  /-- The branch's smooth right inverse of its Hopf coordinates, at square-root base `m`. -/
  sect : ℂ → (ℂ × ℂ) → (ℂ × ℂ)
  /-- The section builder's smooth domain. -/
  dom : ℂ → Set (ℂ × ℂ)
  /-- The branch's coordinate reader — the inverse of `sect` on the Hopf datum. -/
  read : (ℂ × ℂ) → (ℂ × ℂ)
  /-- The reader's smooth domain. -/
  rdom : Set (ℂ × ℂ)
  mem_atlas : chart ∈ atlasEInt
  isOpen_dom : ∀ m : ℂ, IsOpen (dom m)
  isOpen_rdom : IsOpen rdom
  contDiffOn_sect : ∀ (k : WithTop ℕ∞) (m : ℂ), ContDiffOn ℝ k (sect m) (dom m)
  contDiffOn_read : ∀ k : WithTop ℕ∞, ContDiffOn ℝ k read rdom
  sect_mem : ∀ (m : ℂ), ‖m‖ = 1 → ∀ (q : ℂ × ℂ), q ∈ dom m →
    ‖(sect m q).1‖ ^ 2 + ‖(sect m q).2‖ ^ 2 = 1
  read_sect : ∀ (m : ℂ), ‖m‖ = 1 → ∀ (q : ℂ × ℂ), q ∈ dom m →
    read (sect m q) = (q.1, KummerSeamCollarCoord.fiberDir q.2)
  sect_mem_rdom : ∀ (m : ℂ), ‖m‖ = 1 → ∀ (q : ℂ × ℂ), q ∈ dom m → sect m q ∈ rdom
  sect_neg : ∀ (m : ℂ) (q : ℂ × ℂ), sect (-m) q = (-(sect m q).1, -(sect m q).2)
  dom_neg : ∀ (m : ℂ) (q : ℂ × ℂ), q ∈ dom (-m) ↔ q ∈ dom m
  norm_snd : ∀ (z : ↥interiorE), (z : ResE) ∈ chart.source →
    ‖(intCoordInv (eIntChart chart z)).2‖ = fiberNorm (z : ResE)
  exists_dom : ∀ (z : ↥interiorE), (z : ResE) ∈ chart.source → 1 / 2 < fiberNorm (z : ResE) →
    ∃ m : ℂ, ‖m‖ = 1 ∧ intCoordInv (eIntChart chart z) ∈ dom m
  ident : ∀ (c : EIndex) (m : ℂ), ‖m‖ = 1 → ∀ (z : ↥interiorE), (z : ResE) ∈ chart.source →
    1 / 2 < fiberNorm (z : ResE) → intCoordInv (eIntChart chart z) ∈ dom m →
    ∀ (σ : S3), (σ : ℂ × ℂ) = sect m (intCoordInv (eIntChart chart z)) →
    ∀ (v : ↥openParam), (v : ℝ) = 1 - ‖(intCoordInv (eIntChart chart z)).2‖ →
    seamParam c (mkRP3 σ, v) = weldMk (Sum.inr (c, (z : ResE)))

theorem norm_snd_interiorChart {z : ↥interiorE} (hz : (z : ResE) ∈ interiorChart.source) :
    ‖(intCoordInv (eIntChart interiorChart z)).2‖ = fiberNorm (z : ResE) := by
  obtain ⟨q, hq1, hzq⟩ := exists_chart0_of_mem_interiorChart_source hz
  rw [eIntChart_apply, hzq, flatChart_interiorChart_chart0 hq1, intCoordInv_intCoord,
    fiberNorm_chart0]

theorem norm_snd_interiorChart1 {z : ↥interiorE} (hz : (z : ResE) ∈ interiorChart1.source) :
    ‖(intCoordInv (eIntChart interiorChart1 z)).2‖ = fiberNorm (z : ResE) := by
  obtain ⟨q, hq1, hzq⟩ := exists_chart1_of_mem_interiorChart1_source hz
  rw [eIntChart_apply, hzq, flatChart_interiorChart1_chart1 hq1, intCoordInv_intCoord,
    fiberNorm_chart1]

theorem norm_snd_annulusInteriorChart {z : ↥interiorE}
    (hz : (z : ResE) ∈ annulusInteriorChart.source) :
    ‖(intCoordInv (eIntChart annulusInteriorChart z)).2‖ = fiberNorm (z : ResE) := by
  rw [eIntChart_apply, flatChart_annulusInteriorChart, intCoordInv_intCoord]
  exact SKEFTHawking.KummerSeamCollarSmooth.norm_annulusTrivFun_snd
    (mem_annulusRegion_of_mem_annulusInteriorChart_source hz)

theorem exists_sectEDom {q : ℂ × ℂ} (hq : q.2 ≠ 0) : ∃ m : ℂ, ‖m‖ = 1 ∧ q ∈ sectEDom m := by
  obtain ⟨m, hm, hd⟩ := exists_mem_seamDomAt (norm_fiberDir hq) q.1
  exact ⟨m, hm, hq, hd⟩

/-- **The chart-0 branch record.** -/
def branch0 : EBranch where
  chart := interiorChart
  sect := sectE
  dom := sectEDom
  read := hopf0
  rdom := {x : ℂ × ℂ | x.2 ≠ 0}
  mem_atlas := Set.mem_insert _ _
  isOpen_dom := isOpen_sectEDom
  isOpen_rdom := isOpen_snd_ne_zero
  contDiffOn_sect := fun _ m => contDiffOn_sectE m
  contDiffOn_read := fun _ => contDiffOn_hopf0
  sect_mem := fun _ hm _ hq => seamSectionAt_mem hm hq.2
  read_sect := fun _ hm _ hq => readE_sectE hm hq
  sect_mem_rdom := fun _ hm _ hq => seamSectionAt_snd_ne_zero hm hq.2
  sect_neg := fun m q => seamSectionAt_neg m (q.1, KummerSeamCollarCoord.fiberDir q.2)
  dom_neg := fun m q => and_congr Iff.rfl (mem_seamDomAt_neg m _)
  norm_snd := fun _ hz => norm_snd_interiorChart hz
  exists_dom := fun z hz hband =>
    exists_sectEDom (by
      rw [← norm_snd_interiorChart hz] at hband
      exact norm_ne_zero_iff.mp (ne_of_gt (lt_trans (by norm_num) hband)))
  ident := fun c _ hm _ hz hband hdom _ hσ _ hv =>
    seamParam_eq_of_interiorChart c hm hz hband hdom hσ hv

/-- **The chart-1 branch record** — the same section, swapped. -/
def branch1 : EBranch where
  chart := interiorChart1
  sect := sectE1
  dom := sectEDom
  read := readE1
  rdom := {x : ℂ × ℂ | x.1 ≠ 0}
  mem_atlas := Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  isOpen_dom := isOpen_sectEDom
  isOpen_rdom := isOpen_fst_ne_zero
  contDiffOn_sect := fun _ m => contDiffOn_sectE1 m
  contDiffOn_read := fun _ => contDiffOn_readE1
  sect_mem := fun m hm q hq => by
    have h : ‖(sectE m q).1‖ ^ 2 + ‖(sectE m q).2‖ ^ 2 = 1 := seamSectionAt_mem hm hq.2
    show ‖(sectE m q).2‖ ^ 2 + ‖(sectE m q).1‖ ^ 2 = 1
    linarith
  read_sect := fun _ hm _ hq => readE1_sectE1 hm hq
  sect_mem_rdom := fun _ hm _ hq => seamSectionAt_snd_ne_zero hm hq.2
  sect_neg := fun m q => by
    have h : sectE (-m) q = (-(sectE m q).1, -(sectE m q).2) :=
      seamSectionAt_neg m (q.1, KummerSeamCollarCoord.fiberDir q.2)
    show Prod.swap (sectE (-m) q) = _
    rw [h]
    rfl
  dom_neg := fun m q => and_congr Iff.rfl (mem_seamDomAt_neg m _)
  norm_snd := fun _ hz => norm_snd_interiorChart1 hz
  exists_dom := fun z hz hband =>
    exists_sectEDom (by
      rw [← norm_snd_interiorChart1 hz] at hband
      exact norm_ne_zero_iff.mp (ne_of_gt (lt_trans (by norm_num) hband)))
  ident := fun c _ hm _ hz hband hdom _ hσ _ hv =>
    seamParam_eq_of_interiorChart1 c hm hz hband hdom hσ hv

/-- **The equatorial branch record** — the same section at the `regDir`-rotated fiber phase. -/
def branchA : EBranch where
  chart := annulusInteriorChart
  sect := sectEA
  dom := sectEADom
  read := readEA
  rdom := {x : ℂ × ℂ | x.1 ≠ 0} ∩ {x : ℂ × ℂ | x.2 ≠ 0}
  mem_atlas := Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ rfl)
  isOpen_dom := isOpen_sectEADom
  isOpen_rdom := isOpen_fst_ne_zero.inter isOpen_snd_ne_zero
  contDiffOn_sect := fun _ m => contDiffOn_sectEA m
  contDiffOn_read := fun _ => contDiffOn_readEA
  sect_mem := fun _ hm _ hq => seamSectionAt_mem hm hq.2
  read_sect := fun _ hm _ hq => readEA_sectEA hm hq
  sect_mem_rdom := fun _ hm _ hq =>
    ⟨seamSectionAt_fst_ne_zero hm hq.2 hq.1.1, seamSectionAt_snd_ne_zero hm hq.2⟩
  sect_neg := fun m q => seamSectionAt_neg m _
  dom_neg := fun m q => and_congr Iff.rfl (mem_seamDomAt_neg m _)
  norm_snd := fun _ hz => norm_snd_annulusInteriorChart hz
  exists_dom := fun z hz hband => by
    have hx : (z : ResE) ∈ annulusRegion :=
      mem_annulusRegion_of_mem_annulusInteriorChart_source hz
    have hcoord : intCoordInv (eIntChart annulusInteriorChart z)
        = ((annulusTrivFun (z : ResE)).1, ((annulusTrivFun (z : ResE)).2 : ℂ)) := by
      rw [eIntChart_apply, flatChart_annulusInteriorChart, intCoordInv_intCoord]
    obtain ⟨hlo, -⟩ := annulusTriv_mapsTo hx
    have hβ : (annulusTrivFun (z : ResE)).1 ≠ 0 :=
      norm_ne_zero_iff.mp (ne_of_gt (lt_trans (by norm_num) hlo))
    have hζ : ((annulusTrivFun (z : ResE)).2 : ℂ) ≠ 0 := by
      rw [← norm_snd_annulusInteriorChart hz] at hband
      rw [hcoord] at hband
      exact norm_ne_zero_iff.mp (ne_of_gt (lt_trans (by norm_num) hband))
    obtain ⟨m, hm, hd⟩ := exists_mem_seamDomAt
      (norm_twist (q := ((annulusTrivFun (z : ResE)).1, ((annulusTrivFun (z : ResE)).2 : ℂ)))
        hβ hζ) (annulusTrivFun (z : ResE)).1
    exact ⟨m, hm, by rw [hcoord]; exact ⟨⟨hβ, hζ⟩, hd⟩⟩
  ident := fun c _ hm _ hz hband hdom _ hσ _ hv =>
    seamParam_eq_of_annulusInteriorChart c hm hz hband hdom hσ hv

/-- **THE THREE-WAY DISPATCH.** Every chart of the E-interior atlas is one of the three branches. -/
theorem exists_branch {cc : OpenPartialHomeomorph ResE HModel} (hcc : cc ∈ atlasEInt) :
    ∃ B : EBranch, B.chart = cc := by
  rcases hcc with rfl | rfl | rfl
  · exact ⟨branch0, rfl⟩
  · exact ⟨branch1, rfl⟩
  · exact ⟨branchA, rfl⟩

/-! ## §9. The source of the transition, and the free branch sign -/

/-- The E-interior chart family of `K3`, at a fixed branch chart of `ResE`. -/
def eLift (c : EIndex) (cc : OpenPartialHomeomorph ResE HModel) :
    OpenPartialHomeomorph KummerK3 FModel :=
  (eIntChart cc).lift_openEmbedding (isOpenEmbedding_eInteriorCopy c)

theorem eLift_symm_apply (c : EIndex) (cc : OpenPartialHomeomorph ResE HModel) (p : FModel) :
    (eLift c cc).symm p = eInteriorCopy c ((eIntChart cc).symm p) := by
  show ((eIntChart cc).lift_openEmbedding (isOpenEmbedding_eInteriorCopy c)).symm p = _
  rw [OpenPartialHomeomorph.lift_openEmbedding_symm]
  rfl

theorem eLift_target (c : EIndex) (cc : OpenPartialHomeomorph ResE HModel) :
    (eLift c cc).target = (eIntChart cc).target :=
  OpenPartialHomeomorph.lift_openEmbedding_target _ _

theorem mem_chart_source_of_mem_eIntChart_source {cc : OpenPartialHomeomorph ResE HModel}
    {z : ↥interiorE} (hz : z ∈ (eIntChart cc).source) : (z : ResE) ∈ cc.source := by
  rw [eIntChart, OpenPartialHomeomorph.trans_source] at hz
  have h2 : (z : ResE) ∈ (flatChart cc).source := hz.2
  rw [flatChart, OpenPartialHomeomorph.trans_source] at h2
  exact h2.1

/-- **The data extracted from a point of the (1,3) transition source.** -/
theorem transE_source_data (B : EBranch) {c c' : EIndex} {r₀ : RP3} {p : FModel}
    (hp : p ∈ ((eLift c B.chart).symm.trans (seamChart c' r₀)).source) :
    c = c' ∧ (eIntChart B.chart).symm p ∈ (eIntChart B.chart).source
      ∧ eIntChart B.chart ((eIntChart B.chart).symm p) = p
      ∧ 1 / 2 < fiberNorm (((eIntChart B.chart).symm p : ↥interiorE) : ResE) := by
  rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
    Set.mem_inter_iff, Set.mem_preimage] at hp
  obtain ⟨hp1, hp2⟩ := hp
  rw [eLift_target] at hp1
  have hz1 : (eIntChart B.chart).symm p ∈ (eIntChart B.chart).source :=
    (eIntChart B.chart).map_target hp1
  have hzp : eIntChart B.chart ((eIntChart B.chart).symm p) = p :=
    (eIntChart B.chart).right_inv hp1
  rw [eLift_symm_apply] at hp2
  have hnb : weldMk (Sum.inr (c, (((eIntChart B.chart).symm p : ↥interiorE) : ResE)))
      ∈ seamCompNbhd c' := seamChart_source_subset c' r₀ hp2
  obtain ⟨hcc, hband⟩ := eq_and_band_of_mem_seamCompNbhd hnb
  exact ⟨hcc, hz1, hzp, hband⟩

/-- Every point of the pinned `ℝP³` chart's source has a hemisphere lift; so of the two antipodal
`S³` representatives of the class at least one is in the hemisphere. -/
theorem exists_hemi_lift {x₀ : S3E} {r : RP3} (h : r ∈ (rp3PinChart x₀).source) :
    ∃ s ∈ hemi x₀, mkRP3 (sphToS3 s) = r := by
  rw [rp3PinChart, OpenPartialHomeomorph.lift_openEmbedding_source] at h
  obtain ⟨e, he, rfl⟩ := h
  rw [rp3Chart_source] at he
  obtain ⟨s, hs, rfl⟩ := he
  exact ⟨s, hs, rfl⟩

/-- **THE BRANCH SIGN IS FREE.** Of the two antipodal section points over a seam class, one lies in
the `x₀`-hemisphere — `mkRP3_seamPointAt_neg` says both name the same `ℝP³` point. -/
theorem hemi_or_neg {x₀ : S3E} {σ : S3} (h : mkRP3 σ ∈ (rp3PinChart x₀).source) :
    s3ToSphE σ ∈ hemi x₀ ∨ s3ToSphE (negS3 σ) ∈ hemi x₀ := by
  obtain ⟨s, hs, hsr⟩ := exists_hemi_lift h
  rcases Quotient.exact hsr with hcase | hcase
  · left
    have hse : s = s3ToSphE σ := by
      rw [← sphHomeoS3_symm_eq σ, hcase, ← sphHomeoS3_apply, sphHomeoS3.symm_apply_apply]
    rwa [← hse]
  · right
    have hse : s = s3ToSphE (negS3 σ) := by
      rw [← sphHomeoS3_symm_eq (negS3 σ), hcase, negS3_involutive, ← sphHomeoS3_apply,
        sphHomeoS3.symm_apply_apply]
    rwa [← hse]

/-- The negated `S³` point in pinned coordinates. -/
theorem s3ToSphE_negS3 (σ : S3) : s3ToSphE (negS3 σ) = -(s3ToSphE σ) := by
  apply Subtype.ext
  show c2ToEuc ((negS3 σ : S3) : ℂ × ℂ) = -(c2ToEuc (σ : ℂ × ℂ))
  refine PiLp.ext fun i => ?_
  fin_cases i <;> simp [c2ToEuc]

/-! ## §10. The local identification, and the transition class (1,3) -/

/-- **THE LOCAL FORWARD IDENTITY.** -/
theorem transE_apply_eq (B : EBranch) (c : EIndex) (r₀ : RP3) {m : ℂ} (hm : ‖m‖ = 1)
    {p : FModel}
    (hz1 : (eIntChart B.chart).symm p ∈ (eIntChart B.chart).source)
    (hzp : eIntChart B.chart ((eIntChart B.chart).symm p) = p)
    (hband : 1 / 2 < fiberNorm (((eIntChart B.chart).symm p : ↥interiorE) : ResE))
    (hdom : intCoordInv p ∈ B.dom m)
    (hhemi : B.sect m (intCoordInv p) ∈ hemiDom (pinPt r₀)) :
    seamChart c r₀ ((eLift c B.chart).symm p) = seamFwdG (B.sect m) (pinPt r₀) p := by
  have hzc : (((eIntChart B.chart).symm p : ↥interiorE) : ResE) ∈ B.chart.source :=
    mem_chart_source_of_mem_eIntChart_source hz1
  have hnorm : ‖(intCoordInv p).2‖ = fiberNorm (((eIntChart B.chart).symm p : ↥interiorE) : ResE) :=
    by have h := B.norm_snd _ hzc; rwa [hzp] at h
  have hlt1 : fiberNorm (((eIntChart B.chart).symm p : ↥interiorE) : ResE) < 1 :=
    ((eIntChart B.chart).symm p).2
  have hv : 1 - ‖(intCoordInv p).2‖ ∈ openParam := by
    rw [hnorm]
    constructor
    · show -(1 / 8 : ℝ) < 1 - fiberNorm (((eIntChart B.chart).symm p : ↥interiorE) : ResE)
      linarith
    · show 1 - fiberNorm (((eIntChart B.chart).symm p : ↥interiorE) : ResE) < 1 / 2
      linarith
  have hident : seamParam c (mkRP3 ⟨B.sect m (intCoordInv p), B.sect_mem m hm _ hdom⟩,
      ⟨1 - ‖(intCoordInv p).2‖, hv⟩)
      = weldMk (Sum.inr (c, (((eIntChart B.chart).symm p : ↥interiorE) : ResE))) := by
    refine B.ident c m hm _ hzc hband ?_ _ ?_ _ ?_
    · rw [hzp]; exact hdom
    · show B.sect m (intCoordInv p) = B.sect m (intCoordInv (eIntChart B.chart _))
      rw [hzp]
    · show (1 : ℝ) - ‖(intCoordInv p).2‖ = 1 - ‖(intCoordInv (eIntChart B.chart _)).2‖
      rw [hzp]
  rw [eLift_symm_apply,
    show eInteriorCopy c ((eIntChart B.chart).symm p)
      = weldMk (Sum.inr (c, (((eIntChart B.chart).symm p : ↥interiorE) : ResE))) from rfl,
    ← hident, seamChart_seamParam c r₀ _ (s3ToSphE_mem_hemi hhemi)]
  rfl

/-- **THE LOCAL BRANCH BASE.** At every point of the (1,3) transition source there is a unit
square-root base `m` — normalised in sign so the section lands in the `r₀`-chart's hemisphere — for
which the transition is `seamFwdG (B.sect m)` on an explicit open neighbourhood. -/
theorem exists_local_seamFwdG (B : EBranch) (c : EIndex) (r₀ : RP3) {p₀ : FModel}
    (hp₀ : p₀ ∈ ((eLift c B.chart).symm.trans (seamChart c r₀)).source) :
    ∃ m : ℂ, ‖m‖ = 1 ∧ p₀ ∈ seamFwdGDom (B.sect m) (B.dom m) (pinPt r₀) ∧
      ∀ p ∈ ((eLift c B.chart).symm.trans (seamChart c r₀)).source
          ∩ seamFwdGDom (B.sect m) (B.dom m) (pinPt r₀),
        ((eLift c B.chart).symm.trans (seamChart c r₀)) p = seamFwdG (B.sect m) (pinPt r₀) p := by
  obtain ⟨-, hz1, hzp, hband⟩ := transE_source_data B hp₀
  have hzc : (((eIntChart B.chart).symm p₀ : ↥interiorE) : ResE) ∈ B.chart.source :=
    mem_chart_source_of_mem_eIntChart_source hz1
  have hnorm : ‖(intCoordInv p₀).2‖
      = fiberNorm (((eIntChart B.chart).symm p₀ : ↥interiorE) : ResE) := by
    have h := B.norm_snd _ hzc; rwa [hzp] at h
  have hζ : (intCoordInv p₀).2 ≠ 0 := by
    refine norm_ne_zero_iff.mp (ne_of_gt ?_)
    rw [hnorm]; linarith
  obtain ⟨m₀, hm₀, hdom₀'⟩ := B.exists_dom _ hzc hband
  rw [hzp] at hdom₀'
  -- the seam class of the `m₀`-section point lies in the `ℝP³` chart's source
  have hlt1 : fiberNorm (((eIntChart B.chart).symm p₀ : ↥interiorE) : ResE) < 1 :=
    ((eIntChart B.chart).symm p₀).2
  have hv : 1 - ‖(intCoordInv p₀).2‖ ∈ openParam := by
    rw [hnorm]
    refine ⟨by show -(1 / 8 : ℝ) < _; linarith, by show (1 : ℝ) - _ < 1 / 2; linarith⟩
  have hident : seamParam c (mkRP3 ⟨B.sect m₀ (intCoordInv p₀), B.sect_mem m₀ hm₀ _ hdom₀'⟩,
      ⟨1 - ‖(intCoordInv p₀).2‖, hv⟩)
      = (eLift c B.chart).symm p₀ := by
    rw [eLift_symm_apply,
      show eInteriorCopy c ((eIntChart B.chart).symm p₀)
        = weldMk (Sum.inr (c, (((eIntChart B.chart).symm p₀ : ↥interiorE) : ResE))) from rfl]
    refine B.ident c m₀ hm₀ _ hzc hband ?_ _ ?_ _ ?_
    · rw [hzp]; exact hdom₀'
    · show B.sect m₀ (intCoordInv p₀) = B.sect m₀ (intCoordInv (eIntChart B.chart _))
      rw [hzp]
    · show (1 : ℝ) - ‖(intCoordInv p₀).2‖ = 1 - ‖(intCoordInv (eIntChart B.chart _)).2‖
      rw [hzp]
  have hsrc : (eLift c B.chart).symm p₀ ∈ (seamChart c r₀).source := by
    rw [OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.symm_source,
      Set.mem_inter_iff, Set.mem_preimage] at hp₀
    exact hp₀.2
  have hmk : mkRP3 (⟨B.sect m₀ (intCoordInv p₀), B.sect_mem m₀ hm₀ _ hdom₀'⟩ : S3)
      ∈ (rp3PinChart (pinPt r₀)).source := by
    rw [← hident] at hsrc
    rw [seamChart, OpenPartialHomeomorph.trans_source, Set.mem_inter_iff,
      Set.mem_preimage] at hsrc
    have h2 := hsrc.2
    rw [show (seamParamHomeo c).symm (seamParam c
        (mkRP3 ⟨B.sect m₀ (intCoordInv p₀), B.sect_mem m₀ hm₀ _ hdom₀'⟩,
          ⟨1 - ‖(intCoordInv p₀).2‖, hv⟩))
        = (mkRP3 ⟨B.sect m₀ (intCoordInv p₀), B.sect_mem m₀ hm₀ _ hdom₀'⟩,
          ⟨1 - ‖(intCoordInv p₀).2‖, hv⟩) from (seamParamHomeo c).left_inv (by trivial)] at h2
    exact h2.1
  -- choose the sign
  have hkey : ∃ m : ℂ, ‖m‖ = 1 ∧ ∃ h : intCoordInv p₀ ∈ B.dom m,
      B.sect m (intCoordInv p₀) ∈ hemiDom (pinPt r₀) := by
    rcases hemi_or_neg hmk with hpos | hneg
    · exact ⟨m₀, hm₀, hdom₀', hpos⟩
    · refine ⟨-m₀, by rwa [norm_neg], (B.dom_neg m₀ _).mpr hdom₀', ?_⟩
      show (0 : ℝ) < ⟪((pinPt r₀ : S3E) : E4), c2ToEuc (B.sect (-m₀) (intCoordInv p₀))⟫
      rw [B.sect_neg m₀ (intCoordInv p₀)]
      have h1 : (0 : ℝ) < ⟪((pinPt r₀ : S3E) : E4),
          ((s3ToSphE (negS3 ⟨B.sect m₀ (intCoordInv p₀), B.sect_mem m₀ hm₀ _ hdom₀'⟩) : S3E) :
            E4)⟫ := hneg
      exact h1
  obtain ⟨m, hm, hdom, hhemi⟩ := hkey
  refine ⟨m, hm, ⟨⟨hζ, hdom⟩, hhemi⟩, ?_⟩
  intro p hp
  obtain ⟨-, hz1', hzp', hband'⟩ := transE_source_data B hp.1
  exact transE_apply_eq B c r₀ hm hz1' hzp' hband' hp.2.1.2 hp.2.2

/-! ## §11. Class (1,3), and its `symm` mirror (3,1) -/

/-- **CLASS (1,3) CLOSED for a fixed branch chart and a matching component.** -/
theorem mem_contDiffGroupoid_eLift_seam_same (B : EBranch) (c : EIndex) (r₀ : RP3) :
    ((eLift c B.chart).symm.trans (seamChart c r₀)) ∈ contDiffGroupoid k 𝓘(ℝ, FModel) := by
  set g := (eLift c B.chart).symm.trans (seamChart c r₀) with hg
  rw [SKEFTHawking.ManifoldModelTransport.mem_contDiffGroupoid_self]
  constructor
  · refine contDiffOn_of_locally_contDiffOn fun p₀ hp₀ => ?_
    obtain ⟨m, hm, hmem, heq⟩ := exists_local_seamFwdG B c r₀ hp₀
    refine ⟨seamFwdGDom (B.sect m) (B.dom m) (pinPt r₀),
      isOpen_seamFwdGDom (B.isOpen_dom m) ((B.contDiffOn_sect 0 m).continuousOn) (pinPt r₀),
      hmem, ?_⟩
    exact ((contDiffOn_seamFwdG (B.contDiffOn_sect k m) (pinPt r₀)).mono
      Set.inter_subset_right).congr heq
  · refine contDiffOn_of_locally_contDiffOn fun v₀ hv₀ => ?_
    have hp₀ : g.symm v₀ ∈ g.source := g.map_target hv₀
    obtain ⟨m, hm, hmem, heq⟩ := exists_local_seamFwdG B c r₀ hp₀
    have hUopen := isOpen_seamFwdGDom (B.isOpen_dom m)
      ((B.contDiffOn_sect 0 m).continuousOn) (pinPt r₀)
    have hmain : ∀ v ∈ g.target ∩ (g.target ∩ g.symm ⁻¹' seamFwdGDom (B.sect m) (B.dom m)
        (pinPt r₀)),
        v ∈ seamBwdGDom B.rdom (pinPt r₀) ∧ g.symm v = seamBwdG B.read (pinPt r₀) v := by
      intro v hv
      have hpU : g.symm v ∈ seamFwdGDom (B.sect m) (B.dom m) (pinPt r₀) := hv.2.2
      have hpS : g.symm v ∈ g.source := g.map_target hv.1
      have hvp : g (g.symm v) = v := g.right_inv hv.1
      have hveq : v = seamFwdG (B.sect m) (pinPt r₀) (g.symm v) :=
        hvp.symm.trans (heq _ ⟨hpS, hpU⟩)
      have hσ : ‖(B.sect m (intCoordInv (g.symm v))).1‖ ^ 2
          + ‖(B.sect m (intCoordInv (g.symm v))).2‖ ^ 2 = 1 := B.sect_mem m hm _ hpU.1.2
      have hlift : seamLift (pinPt r₀) (seamFwdG (B.sect m) (pinPt r₀) (g.symm v)).1
          = B.sect m (intCoordInv (g.symm v)) :=
        seamLift_rp3Coord (σ := ⟨B.sect m (intCoordInv (g.symm v)), hσ⟩)
          (s3ToSphE_mem_hemi hpU.2)
      have hL : seamLift (pinPt r₀) v.1 = B.sect m (intCoordInv (g.symm v)) := by
        conv_lhs => rw [hveq]
        exact hlift
      refine ⟨?_, ?_⟩
      · show seamLift (pinPt r₀) v.1 ∈ B.rdom
        rw [hL]
        exact B.sect_mem_rdom m hm _ hpU.1.2
      · calc g.symm v
            = seamBwdG B.read (pinPt r₀) (seamFwdG (B.sect m) (pinPt r₀) (g.symm v)) :=
              (seamBwdG_seamFwdG hpU.1.1 hσ hpU.2 (B.read_sect m hm _ hpU.1.2)).symm
          _ = seamBwdG B.read (pinPt r₀) v := by rw [← hveq]
    refine ⟨g.target ∩ g.symm ⁻¹' seamFwdGDom (B.sect m) (B.dom m) (pinPt r₀),
      g.continuousOn_symm.isOpen_inter_preimage g.open_target hUopen, ⟨hv₀, hmem⟩, ?_⟩
    refine ((contDiffOn_seamBwdG (B.contDiffOn_read k) (pinPt r₀)).mono
      (fun v hv => (hmain v hv).1)).congr (fun v hv => (hmain v hv).2)

/-- **CLASS (1,3) CLOSED** — an E-interior chart of the weld atlas and a seam chart have a `C^k`
transition on the flat model `𝓔³ × ℝ`. Distinct components are vacuous; a matching component is the
explicit `seamFwdG`/`seamBwdG` pair, `C^k` on an open neighbourhood of every overlap point. -/
theorem mem_contDiffGroupoid_eFam_trans_seamFam (c c' : EIndex) (y : ↥interiorE) (r₀ : RP3) :
    ((SKEFTHawking.KummerK3Chart.eFamChart c y).symm.trans (seamChart c' r₀))
      ∈ contDiffGroupoid k 𝓘(ℝ, FModel) := by
  obtain ⟨B, hB⟩ := exists_branch (Classical.choose_spec (exists_eIntChart y)).1
  have hfam : SKEFTHawking.KummerK3Chart.eFamChart c y = eLift c B.chart := by
    rw [hB]; rfl
  rw [hfam]
  by_cases h : c = c'
  · subst h
    exact mem_contDiffGroupoid_eLift_seam_same B c r₀
  · refine SKEFTHawking.KummerInteriorManifold.mem_groupoid_of_source_empty ?_
    rw [Set.eq_empty_iff_forall_notMem]
    intro p hp
    exact h (transE_source_data B hp).1

/-- **CLASS (3,1) CLOSED** — the `symm` mirror: a structure groupoid is closed under `symm`, and
`(e.symm ≫ₕ f).symm = f.symm ≫ₕ e`. -/
theorem mem_contDiffGroupoid_seamFam_trans_eFam (c c' : EIndex) (y : ↥interiorE) (r₀ : RP3) :
    ((seamChart c' r₀).symm.trans (SKEFTHawking.KummerK3Chart.eFamChart c y))
      ∈ contDiffGroupoid k 𝓘(ℝ, FModel) := by
  have h := (contDiffGroupoid k 𝓘(ℝ, FModel)).symm
    (mem_contDiffGroupoid_eFam_trans_seamFam (k := k) c c' y r₀)
  rwa [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm,
    OpenPartialHomeomorph.symm_symm] at h

end

end SKEFTHawking.KummerSeamTransE
