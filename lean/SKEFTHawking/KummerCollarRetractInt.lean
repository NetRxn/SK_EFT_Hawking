/-
# Phase 5q.H — the outer collar deformation-retracts onto `∂E ≅ ℝP³`

`KummerPieceCollarInt.pairH2TwoTorsionFree_iff_outerE` made the `b₂` residual one statement about the
single explicit pair `(E, outerE)` with `outerE = {fiberNorm ≥ 1/2}`. To run the pair long exact
sequence on that pair one needs `H_*(outerE; ℤ)` — and the collar is *not* an opaque space: the
already-banked outward fiber flow `KummerWeldFiberFlow.resFlow` **is** a strong deformation
retraction of the collar onto its outer boundary.

Three banked facts assemble it, with no new geometry:

* `KummerK7H1Window.resFlow_mem_outerE` — the flow preserves the collar at every time;
* `KummerK7H1Window.resFlow_zero_mem_boundary` — at `t = 0` it lands on `∂E`;
* `KummerWeldFiberFlow.resFlow_boundary` / `resFlow_one` — it fixes `∂E` pointwise, and is the
  identity at `t = 1`.

So `outerRetrC : outerE → ∂E` and the inclusion `∂E ↪ outerE` are mutually inverse **up to
homotopy** — in fact `outerRetrC ∘ incl = id` on the nose (`outerRetr_comp_bdryIncl`), the homotopy
is only needed in the other direction. Feeding
`SingularFunctorialityInt.Homology.mapInt_bijective_of_homotopyEquiv` gives
`Hₙ₊₁(outerE; ℤ) ≅ Hₙ₊₁(∂E; ℤ)`, and `KummerResolutionPiece.bdryHomeoRP3 : ℝP³ ≃ₜ ∂E` transports
that to the fully banked `H_*(ℝP³; ℤ)`:

> **`outerE_homology_two_eq_zero` : `H₂(outerE; ℤ) = 0`**
> **`outerH1EquivZMod2` : `H₁(outerE; ℤ) ≅ ℤ/2`**

These are exactly the two ends of the pair-LES segment that pins `H₂(E, outerE; ℤ)` as an extension
of `ℤ/2` by `ℤ` (`KummerCollarPairLESInt`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.KummerPieceCollarInt
import SKEFTHawking.KummerK7H1Window
import SKEFTHawking.KummerRP3HomologySolve
import SKEFTHawking.SingularProdContractibleInt

open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularFunctorialityInt (Homology.mapInt
  Homology.mapInt_bijective_of_homotopyEquiv)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularHomotopyInvariance (slice)
open SKEFTHawking.SingularProdContractibleInt (homeoHomologyEquivInt)
open SKEFTHawking.KummerResolutionPiece (ResE RP3 boundaryE bdryHomeoRP3)
open SKEFTHawking.KummerWeldFiberFlow (resFlow resFlow_one resFlow_boundary continuous_resFlow)
open SKEFTHawking.KummerK7H1Window (resFlow_mem_outerE resFlow_zero_mem_boundary)
open SKEFTHawking.KummerPairTransportInt (ResEtop)
open SKEFTHawking.KummerPieceCollarInt (outerE boundaryE_subset_outerE)

namespace SKEFTHawking.KummerCollarRetractInt

noncomputable section

/-! ## §0. The two carriers, as `TopCat` objects -/

/-- The outer collar `{fiberNorm ≥ 1/2} ⊆ E` as a topological space. -/
abbrev OuterTop : TopCat := sub (X := ResEtop) outerE

/-- The fiber boundary `∂E = {fiberNorm = 1} ⊆ E` as a topological space. -/
abbrev BdryTop : TopCat := TopCat.of ↥(boundaryE : Set ResE)

/-! ## §1. The retraction, the inclusion and the deformation homotopy -/

/-- **The collar retraction** `outerE ↠ ∂E` — flow to time `0`. Well defined by
`resFlow_zero_mem_boundary`: on the collar the radial profile `min 1 (2·r)` saturates at `1`. -/
def outerRetrC : C(↑OuterTop, ↑BdryTop) where
  toFun e := ⟨resFlow (e.1, 0), resFlow_zero_mem_boundary e.2⟩
  continuous_toFun :=
    (continuous_resFlow.comp (continuous_subtype_val.prodMk continuous_const)).subtype_mk _

/-- The boundary inclusion `∂E ↪ outerE` (`boundaryE_subset_outerE`). -/
def bdryInclOuterC : C(↑BdryTop, ↑OuterTop) :=
  ⟨fun b => ⟨b.1, boundaryE_subset_outerE b.2⟩, continuous_subtype_val.subtype_mk _⟩

/-- **The deformation homotopy inside the collar** — `resFlow` restricted to `outerE`, which the
flow preserves at every time (`resFlow_mem_outerE`). -/
def collarHomotopy : C(↑OuterTop × unitInterval, ↑OuterTop) where
  toFun p := ⟨resFlow (p.1.1, p.2), resFlow_mem_outerE p.1.2 p.2⟩
  continuous_toFun :=
    (continuous_resFlow.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).subtype_mk _

theorem slice_collarHomotopy_one : slice collarHomotopy 1 = ContinuousMap.id _ :=
  ContinuousMap.ext fun e => Subtype.ext (resFlow_one e.1)

theorem slice_collarHomotopy_zero :
    slice collarHomotopy 0 = bdryInclOuterC.comp outerRetrC :=
  ContinuousMap.ext fun _ => Subtype.ext rfl

/-- **The retraction is a genuine retraction**: it is the identity on `∂E`, on the nose — the flow
fixes the boundary pointwise (`resFlow_boundary`). -/
theorem outerRetr_comp_bdryIncl : outerRetrC.comp bdryInclOuterC = ContinuousMap.id _ :=
  ContinuousMap.ext fun b => Subtype.ext (resFlow_boundary b.2 0)

/-- The constant homotopy on `∂E`. -/
def bdryConstHomotopy : C(↑BdryTop × unitInterval, ↑BdryTop) :=
  ⟨fun p => p.1, continuous_fst⟩

theorem slice_bdryConstHomotopy (r : unitInterval) :
    slice bdryConstHomotopy r = ContinuousMap.id _ :=
  ContinuousMap.ext fun _ => rfl

/-! ## §2. `H_*(outerE;ℤ) ≅ H_*(∂E;ℤ) ≅ H_*(ℝP³;ℤ)` -/

/-- **The collar deformation-retracts onto its boundary** (integral homology, positive degrees). -/
theorem mapInt_outerRetr_bijective (n : ℕ) :
    Function.Bijective (Homology.mapInt (X := OuterTop) (Y := BdryTop) outerRetrC (n + 1)) :=
  Homology.mapInt_bijective_of_homotopyEquiv outerRetrC bdryInclOuterC collarHomotopy
    slice_collarHomotopy_zero slice_collarHomotopy_one bdryConstHomotopy
    ((slice_bdryConstHomotopy 0).trans outerRetr_comp_bdryIncl.symm)
    (slice_bdryConstHomotopy 1) n

/-- `Hₙ₊₁(outerE;ℤ) ≅ Hₙ₊₁(∂E;ℤ)`. -/
def outerBdryHomologyEquiv (n : ℕ) :
    Homology OuterTop (n + 1) ≃ₗ[ℤ] Homology BdryTop (n + 1) :=
  LinearEquiv.ofBijective _ (mapInt_outerRetr_bijective n)

/-- **`Hₙ₊₁(outerE;ℤ) ≅ Hₙ₊₁(ℝP³;ℤ)`** — the collar has the integral homology of `ℝP³`. -/
def outerRP3HomologyEquiv (n : ℕ) :
    Homology OuterTop (n + 1) ≃ₗ[ℤ] Homology (TopCat.of RP3) (n + 1) :=
  (outerBdryHomologyEquiv n).trans (homeoHomologyEquivInt bdryHomeoRP3 (n + 1)).symm

/-! ## §3. The two values the pair LES consumes -/

/-- **`H₂(outerE;ℤ) = 0`** — the collar's second integral homology vanishes, because
`H₂(ℝP³;ℤ) = 0` (`KummerRP3HomologySolve.rp3_homology_two_eq_zero`). -/
theorem outerE_homology_two_eq_zero (x : Homology OuterTop 2) : x = 0 := by
  have h := SKEFTHawking.KummerRP3HomologySolve.rp3_homology_two_eq_zero
    (outerRP3HomologyEquiv 1 x)
  have h2 := congrArg (outerRP3HomologyEquiv 1).symm h
  rwa [LinearEquiv.symm_apply_apply, map_zero] at h2

/-- **`H₁(outerE;ℤ) ≅ ℤ/2`** — the collar's first integral homology is the deck class of
`∂E ≅ ℝP³` (`KummerRP3HomologySolve.rp3H1EquivZMod2`). -/
def outerH1EquivZMod2 : Homology OuterTop 1 ≃ₗ[ℤ] ZMod 2 :=
  (outerRP3HomologyEquiv 0).trans SKEFTHawking.KummerRP3HomologySolve.rp3H1EquivZMod2

/-- **`H₁(outerE;ℤ) ≠ 0`** — a falsifiable pin on §3: the collar is *not* simply connected in
homology, which is exactly why the pair `(E, outerE)` can have relative `H₂` bigger than
`H₂(E) ≅ ℤ`. -/
theorem exists_ne_zero_outerH1 : ∃ x : Homology OuterTop 1, x ≠ 0 := by
  refine ⟨outerH1EquivZMod2.symm 1, fun h => ?_⟩
  have := congrArg outerH1EquivZMod2 h
  rw [LinearEquiv.apply_symm_apply, map_zero] at this
  exact one_ne_zero this

end

end SKEFTHawking.KummerCollarRetractInt
