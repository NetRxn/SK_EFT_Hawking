/-
# Phase 5q.H — the collar retraction, LOCALISED to a flow-invariant region

`KummerCollarRetractInt` used the banked outward fiber flow `KummerWeldFiberFlow.resFlow` to
deformation-retract the whole collar `outerE = {fiberNorm ≥ 1/2}` onto `∂E ≅ ℝP³`. The flow moves
**only the fiber coordinate** (`resFlow (chartᵢ (z, w), t) = chartᵢ (z, flowDisk t w)`), so the same
retraction runs verbatim inside any region `S ⊆ E` the flow preserves — in particular inside any
region cut out by a condition on the **base** coordinate alone.

§1 is that generalisation:

> `outerRegionBdryHomologyEquiv` : `Hₙ₊₁(outerE ∩ S; ℤ) ≅ Hₙ₊₁(∂E ∩ S; ℤ)` for any flow-invariant
> `S`.

§2 supplies the instance the `b₂` residual needs: the chart-1 neighbourhoods
`chartNbhd1 r' = (deepChart0 r')ᶜ` are base-determined, hence flow-invariant
(`resFlow_mem_chartNbhd1`, for `r' < 1`). Consequently the third and last chart-local input of
`KummerSplitBChart1ExcisionInt.kummerK3_b2_target_of_chart1_geometry` —

> `H₁(outerE ∩ chartNbhd1 r'; ℤ)` cyclic

— is equivalent to the **3-manifold** statement

> `H₁(∂E ∩ chartNbhd1 r'; ℤ)` cyclic,

i.e. cyclicity of `H₁` of the part of the lens space `∂E ≅ ℝP³` lying over the chart-1 base disk (a
solid torus). §3 chains that into the headline: `kummerK3_b2_target_of_chart1_bdry`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.KummerCollarRetractInt
import SKEFTHawking.KummerSplitBChart1ExcisionInt

open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularFunctorialityInt (Homology.mapInt
  Homology.mapInt_bijective_of_homotopyEquiv)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularHomotopyInvariance (slice)
open SKEFTHawking.SingularRelativeTripleSurjInt (cyclic_of_surjective)
open SKEFTHawking.KummerResolutionPiece (ResE ResChart boundaryE chart0 chart1 chart0_inj_iff
  chart0_eq_chart1_iff)
open SKEFTHawking.KummerWeldFiberFlow (resFlow resFlow_one resFlow_boundary continuous_resFlow)
open SKEFTHawking.KummerK7H1Window (resFlow_mem_outerE resFlow_zero_mem_boundary)
open SKEFTHawking.KummerPairTransportInt (ResEtop)
open SKEFTHawking.KummerPieceCollarInt (outerE boundaryE_subset_outerE)
open SKEFTHawking.KummerChartNbhdInt (deepChart0 chartNbhd1)
open SKEFTHawking.KummerSplitBChart1ExcisionInt (chart1Piece chart1Collar
  kummerK3_b2_target_of_chart1_geometry)

namespace SKEFTHawking.KummerCollarRegionRetractInt

noncomputable section

/-! ## §1. The localised collar retraction -/

variable (S : Set ↑ResEtop)

/-- The collar inside the region `S`. -/
abbrev OuterRegion : TopCat := sub (X := ResEtop) (outerE ∩ S)

/-- The boundary inside the region `S`. -/
abbrev BdryRegion : TopCat := sub (X := ResEtop) (boundaryE ∩ S)

variable {S}

/-- The retraction `outerE ∩ S ↠ ∂E ∩ S` — flow to time `0`, which stays in `S` by invariance. -/
def outerRetrRegion (hS : ∀ x ∈ S, ∀ t : unitInterval, resFlow (x, t) ∈ S) :
    C(↑(OuterRegion S), ↑(BdryRegion S)) where
  toFun e := ⟨resFlow (e.1, 0), resFlow_zero_mem_boundary e.2.1, hS _ e.2.2 0⟩
  continuous_toFun :=
    (continuous_resFlow.comp (continuous_subtype_val.prodMk continuous_const)).subtype_mk _

/-- The inclusion `∂E ∩ S ↪ outerE ∩ S`. -/
def bdryInclRegion : C(↑(BdryRegion S), ↑(OuterRegion S)) :=
  ⟨fun b => ⟨b.1, boundaryE_subset_outerE b.2.1, b.2.2⟩, continuous_subtype_val.subtype_mk _⟩

/-- The deformation homotopy inside `outerE ∩ S`. -/
def regionHomotopy (hS : ∀ x ∈ S, ∀ t : unitInterval, resFlow (x, t) ∈ S) :
    C(↑(OuterRegion S) × unitInterval, ↑(OuterRegion S)) where
  toFun p := ⟨resFlow (p.1.1, p.2), resFlow_mem_outerE p.1.2.1 p.2, hS _ p.1.2.2 p.2⟩
  continuous_toFun :=
    (continuous_resFlow.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).subtype_mk _

theorem slice_regionHomotopy_one (hS : ∀ x ∈ S, ∀ t : unitInterval, resFlow (x, t) ∈ S) :
    slice (regionHomotopy hS) 1 = ContinuousMap.id _ :=
  ContinuousMap.ext fun e => Subtype.ext (resFlow_one e.1)

theorem slice_regionHomotopy_zero (hS : ∀ x ∈ S, ∀ t : unitInterval, resFlow (x, t) ∈ S) :
    slice (regionHomotopy hS) 0 = bdryInclRegion.comp (outerRetrRegion hS) :=
  ContinuousMap.ext fun _ => Subtype.ext rfl

theorem outerRetrRegion_comp_bdryIncl (hS : ∀ x ∈ S, ∀ t : unitInterval, resFlow (x, t) ∈ S) :
    (outerRetrRegion hS).comp bdryInclRegion = ContinuousMap.id _ :=
  ContinuousMap.ext fun b => Subtype.ext (resFlow_boundary b.2.1 0)

/-- The constant homotopy on `∂E ∩ S`. -/
def bdryRegionConstHomotopy : C(↑(BdryRegion S) × unitInterval, ↑(BdryRegion S)) :=
  ⟨fun p => p.1, continuous_fst⟩

theorem slice_bdryRegionConstHomotopy (t : unitInterval) :
    slice (bdryRegionConstHomotopy (S := S)) t = ContinuousMap.id _ :=
  ContinuousMap.ext fun _ => rfl

theorem mapInt_outerRetrRegion_bijective
    (hS : ∀ x ∈ S, ∀ t : unitInterval, resFlow (x, t) ∈ S) (n : ℕ) :
    Function.Bijective
      (Homology.mapInt (X := OuterRegion S) (Y := BdryRegion S) (outerRetrRegion hS) (n + 1)) :=
  Homology.mapInt_bijective_of_homotopyEquiv (outerRetrRegion hS) bdryInclRegion
    (regionHomotopy hS) (slice_regionHomotopy_zero hS) (slice_regionHomotopy_one hS)
    bdryRegionConstHomotopy
    ((slice_bdryRegionConstHomotopy 0).trans (outerRetrRegion_comp_bdryIncl hS).symm)
    (slice_bdryRegionConstHomotopy 1) n

/-- **The localised collar retraction on homology**: `Hₙ₊₁(outerE ∩ S; ℤ) ≅ Hₙ₊₁(∂E ∩ S; ℤ)` for
every region `S` the outward fiber flow preserves. -/
def outerRegionBdryHomologyEquiv (hS : ∀ x ∈ S, ∀ t : unitInterval, resFlow (x, t) ∈ S) (n : ℕ) :
    Homology (OuterRegion S) (n + 1) ≃ₗ[ℤ] Homology (BdryRegion S) (n + 1) :=
  LinearEquiv.ofBijective _ (mapInt_outerRetrRegion_bijective hS n)

/-- **Cyclicity descends from the boundary to the collar**, inside a flow-invariant region. -/
theorem outerRegion_cyclic_of_bdry (hS : ∀ x ∈ S, ∀ t : unitInterval, resFlow (x, t) ∈ S) (n : ℕ)
    (h : ∃ a : Homology (BdryRegion S) (n + 1),
      ∀ x : Homology (BdryRegion S) (n + 1), ∃ k : ℤ, x = k • a) :
    ∃ a : Homology (OuterRegion S) (n + 1),
      ∀ x : Homology (OuterRegion S) (n + 1), ∃ k : ℤ, x = k • a := by
  obtain ⟨a, hgen⟩ := h
  exact ⟨(outerRegionBdryHomologyEquiv hS n).symm a,
    cyclic_of_surjective (outerRegionBdryHomologyEquiv hS n).symm.toLinearMap
      (outerRegionBdryHomologyEquiv hS n).symm.surjective hgen⟩

/-! ## §2. The chart-1 neighbourhoods are flow-invariant -/

/-- **A base-determined region is flow-invariant**: `chartNbhd1 r' = (deepChart0 r')ᶜ` is cut out by
the base coordinate alone, and `resFlow` moves only the fiber coordinate. (`r' < 1` is needed for the
chart-1 branch: a chart-1 point can only be a chart-0 point across a weld, which forces base norm
`1`.) -/
theorem resFlow_mem_chartNbhd1 {r' : ℝ} (hr' : r' < 1) {x : ResE} (hx : x ∈ chartNbhd1 r')
    (t : unitInterval) : resFlow (x, t) ∈ chartNbhd1 r' := by
  intro hmem
  refine hx ?_
  induction x using Quotient.ind with
  | _ a =>
    cases a with
    | inl p =>
      obtain ⟨p', hp', hmk⟩ := hmem
      have hmk' : chart0 p'
          = chart0 (p.1, SKEFTHawking.KummerWeldFiberFlow.flowDisk t p.2) := hmk
      have heq : p' = (p.1, SKEFTHawking.KummerWeldFiberFlow.flowDisk t p.2) :=
        chart0_inj_iff.mp hmk'
      have hbase : p'.1 = p.1 := by rw [heq]
      have hle : ‖(p'.1 : ℂ)‖ ≤ r' := hp'
      exact ⟨p, by show ‖(p.1 : ℂ)‖ ≤ r'; rw [← hbase]; exact hle, rfl⟩
    | inr q =>
      exfalso
      obtain ⟨p', hp', hmk⟩ := hmem
      have hmk' : chart0 p'
          = chart1 (q.1, SKEFTHawking.KummerWeldFiberFlow.flowDisk t q.2) := hmk
      obtain ⟨hseam, -, -⟩ := chart0_eq_chart1_iff.mp hmk'
      have : ‖(p'.1 : ℂ)‖ ≤ r' := hp'
      rw [hseam] at this
      linarith

/-! ## §3. The headline with the last input moved to the boundary lens space -/

/-- **The headline, with the collar input replaced by a `∂E ≅ ℝP³` input.**

`H₂(K3;ℤ) ≅ ℤ²²` follows from:

* acyclicity of the retained chart-1 piece `chartNbhd1 r' ∩ splitBOpen r` in degrees `1` and `2`, and
* cyclicity of `H₁` of `∂E ∩ chartNbhd1 r'` — the part of the lens space `∂E` lying over the chart-1
  base disk, a solid torus.

The collar input of `KummerSplitBChart1ExcisionInt.kummerK3_b2_target_of_chart1_geometry` has been
traded for this one by the localised collar retraction of §1, at no cost: the outward fiber flow
already banked in `KummerWeldFiberFlow` preserves every base-determined region. -/
theorem kummerK3_b2_target_of_chart1_bdry {r r' : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hr'1 : r' < 1)
    (hr' : r' < r)
    (h2 : ∀ x : Homology (sub (chart1Piece r r')) 2, x = 0)
    (h1 : ∀ x : Homology (sub (chart1Piece r r')) 1, x = 0)
    (hbdry : ∃ a : Homology (BdryRegion (chartNbhd1 r')) 1,
      ∀ x : Homology (BdryRegion (chartNbhd1 r')) 1, ∃ k : ℤ, x = k • a) :
    SKEFTHawking.KummerK7Opener.kummerK3_b2_target :=
  kummerK3_b2_target_of_chart1_geometry hr0 hr1 hr'1 hr' h2 h1
    (outerRegion_cyclic_of_bdry (fun _ hx t => resFlow_mem_chartNbhd1 hr'1 hx t) 0 hbdry)

end

end SKEFTHawking.KummerCollarRegionRetractInt
