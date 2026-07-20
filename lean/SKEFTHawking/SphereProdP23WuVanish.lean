/-
# Phase 5q.H — the `(2,3)` Wu-class vanishing for `S²×D³` (P23): `hv2`

The last content atom of `hBbord`'s P23 (besides the `nondeg` feeder, `SphereProdP23Nondeg`).
For the FIXED carrier `W = SphereDisk = S²×D³`, `∂W = sphereDiskBoundarySet ≃ S²×S²`, the middle
Wu class of any `(2,3)` Lefschetz–Wu datum whose `sqOp` is the genuine relative Steenrod square
`relSq2` vanishes: `wuClass P₂₃ = 0`.

## The δ-square route (lead design, 2026-07-20)

`wuClass P₂₃ = 0 ↔ wuFunctional P₂₃ = P₂₃.mu ∘ P₂₃.sqOp = 0`. With `sqOp := relSq2` (`ofRelFund23`)
it suffices to show the DATUM-FREE, μ-independent fact

  `relSq2 = 0`  on  `H³(S²×D³, S²×S²; ℤ/2)`.

Every `b ∈ H³(W,∂W)` is a δ-image `deltaRelH z h` (§1 exactness — `relToAbs b = 0` because
`H³(S²×D³;ℤ/2) = 0`, collapsing to `H³(S²) = 0`). The Hirsch cochain identity
`relSq2 (deltaRelH z h) = deltaRelH (z ⌣ z) h'` (`relSq2_deltaRelH`, folding Sq²–δ naturality and
`Sq² = ⌣²` on degree 2) then carries `b` to the δ-image of the cup-square `z ⌣ z`. On the boundary
`∂W ≃ S²×S²` every degree-2 cohomology class squares to `0` (the two-factor mod-2 cup structure —
`αᵢ ⌣ αᵢ = prᵢ*(g ⌣ g) = 0` by `H⁴(S²;ℤ/2)=0`, cross terms `2αβ = 0`), so the δ-image
`deltaRelH (z ⌣ z) h'` vanishes, hence `relSq2 b = 0`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SphereProdP23
import SKEFTHawking.SingularRelativeCohomDelta
import SKEFTHawking.SingularCohomologyPairRestrict
import SKEFTHawking.SingularUniversalCoeff

open scoped Manifold
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.SingularRelativeSteenrodSq2
open SKEFTHawking.SingularRelativeCohomDelta
open SKEFTHawking.SingularRelativeAbsCompat
open SKEFTHawking.SingularCohomologyFunctoriality
open SKEFTHawking.SingularCohomologyPairRestrict
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.PinPlusKTSphereProdRelFundWuRoots
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.SingularUniversalCoeff

namespace SKEFTHawking.SphereProdP23WuVanish

noncomputable section

variable {X : TopCat} {S : Set ↑X}

/-! ## §1. Generic mod-2 δ-descent lemmas (mod-2 mirror of `SingularRelativeCohomDeltaInt`). -/

/-- **Middle exactness `im ι* = ker δ` on lifts (mod 2).** `[δz] = 0` iff the lift `z` differs from
an absolute cocycle by a relative cochain. Mod-2 mirror of `deltaRelHInt_eq_zero_iff`. -/
theorem deltaRelH_eq_zero_iff {n : ℕ} (z : SingularCochain X n)
    (h : coboundaryₗ X n z ∈ relCochains S (n + 1)) :
    deltaRelH z h = 0 ↔
      ∃ z' : SingularCochain X n, coboundaryₗ X n z' = 0 ∧ z - z' ∈ relCochains S n := by
  rw [deltaRelH, RelativeCohomology.mk_eq_zero_iff]
  show (↑(deltaRelCocycle z h) : relCochains S (n + 1)) ∈ relCoboundaryRange S (n + 1) ↔ _
  rw [show relCoboundaryRange S (n + 1) = LinearMap.range (relCoboundaryₗ S n) from rfl,
    LinearMap.mem_range]
  constructor
  · rintro ⟨w, hw⟩
    refine ⟨z - (w : SingularCochain X n), ?_, ?_⟩
    · have hw' : coboundaryₗ X n (w : SingularCochain X n) = coboundaryₗ X n z := by
        have := Subtype.ext_iff.mp hw
        rwa [relCoboundaryₗ_coe, deltaRelCocycle_coe] at this
      rw [map_sub, hw', sub_self]
    · rw [sub_sub_cancel]
      exact w.2
  · rintro ⟨z', hz', hmem⟩
    refine ⟨⟨z - z', hmem⟩, ?_⟩
    apply Subtype.ext
    rw [relCoboundaryₗ_coe, deltaRelCocycle_coe]
    show coboundaryₗ X n (z - z') = coboundaryₗ X n z
    rw [map_sub, hz', sub_zero]

/-- A **relative** lift has vanishing δ-image class (mod 2): if `z ∈ relCochains S n` then `[δz] = 0`.
The well-definedness engine — `δ` factors through the restriction `z ↦ z|∂W`. -/
theorem deltaRelH_relCochain_eq_zero {n : ℕ} (z : SingularCochain X n)
    (hz : z ∈ relCochains S n) (h : coboundaryₗ X n z ∈ relCochains S (n + 1)) :
    deltaRelH z h = 0 :=
  (deltaRelH_eq_zero_iff z h).mpr ⟨0, map_zero _, by rwa [sub_zero]⟩

/-! ## §2. `H³(S²×D³;ℤ/2) = 0` and the δ-decomposability of every `b ∈ H³(W,∂W)`. -/

/-- **`H³(S²×D³;ℤ/2) = 0`** — the absolute degree-3 cohomology of the carrier vanishes. By mod-2
universal coefficients (`cohomology_eq_zero_of_kroneckerH`) any class pairs to `0` against
`H₃(S²×D³;ℤ/2) = 0` (`sphereDisk_homology_three_eq_zero`), hence is `0`. -/
theorem sphereDisk_cohomology_three_eq_zero
    (ω : Cohomology (TopCat.of SphereDisk) 3) : ω = 0 :=
  cohomology_eq_zero_of_kroneckerH 2 ω
    (fun β => by rw [SphereProdP23.sphereDisk_homology_three_eq_zero β]; simp)

/-- **`relToAbs` vanishes on `H³(S²×D³, S²×S²)`** — the restriction `j* : H³(W,∂W) → H³(W)` is `0`
because its target `H³(S²×D³;ℤ/2)` is `0`. This is the exactness hypothesis feeding
`exists_deltaRelH_of_relToAbs_eq_zero`. -/
theorem relToAbs_sphereDisk23_eq_zero
    (b : RelativeCohomology sphereDiskBoundarySet 3) :
    relToAbs (X := TopCat.of SphereDisk) b = 0 :=
  sphereDisk_cohomology_three_eq_zero _

/-! ## §3. The δ-image of `z ⌣ z` vanishes when the boundary cup-square does. -/

/-- **Generic δ-image cup-square vanishing.** If every degree-2 class of the subspace `sub S` squares
to `0` in `H⁴` (`cupH24 c c = 0`), then for any lift `z` with `δz` relative, `deltaRelH (z ⌣ z) = 0`.
The restriction of `z ⌣ z` to `sub S` is `cup rz rz` (`rz := z|sub S`, a cocycle); its class
`cupH24 [rz] [rz] = 0`, so `cup rz rz = δv`; extending `v` gives a global cocycle `δ(extend v)`
agreeing with `z ⌣ z` on `sub S`, so their difference is relative and `deltaRelH_eq_zero_iff` closes. -/
theorem deltaRelH_cupSelf_eq_zero_of_cupSquare
    (z : SingularCochain X 2) (h : coboundaryₗ X 2 z ∈ relCochains S 3)
    (hbsq : ∀ c : Cohomology (sub S) 2, cupH24 c c = 0) :
    deltaRelH (n := 4) (cup z z) (coboundary_cup_self_mem_relCochains z h) = 0 := by
  -- `rz := z|sub S` is a cocycle (`δz` is relative).
  have hrz_ker : cochainPullback (subInclCM S) 2 z ∈ LinearMap.ker (coboundaryₗ (sub S) 2) := by
    rw [LinearMap.mem_ker]
    show coboundary (sub S) 2 (cochainPullback (subInclCM S) 2 z) = 0
    rw [coboundary_cochainPullback]
    exact (cochainPullback_subInclCM_eq_zero_iff S 3 _).2 h
  -- restriction of `z ⌣ z` = `cup rz rz`.
  have hcup : cochainPullback (subInclCM S) 4 (cup z z)
      = cup (cochainPullback (subInclCM S) 2 z) (cochainPullback (subInclCM S) 2 z) :=
    cochainPullback_cup (subInclCM S) z z
  -- its class `cupH24 [rz] [rz] = 0`, so it is a coboundary `δ v`.
  obtain ⟨v, hv⟩ : ∃ v, coboundary (sub S) 3 v = cochainPullback (subInclCM S) 4 (cup z z) := by
    have hzero := hbsq (Submodule.Quotient.mk
      (⟨cochainPullback (subInclCM S) 2 z, hrz_ker⟩ : LinearMap.ker (coboundaryₗ (sub S) 2)))
    rw [cupH24_mk_mk] at hzero
    have hmem := (Submodule.Quotient.mk_eq_zero _).mp hzero
    rw [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype,
      show coboundaryRange (sub S) 4 = LinearMap.range (coboundaryₗ (sub S) 3) from rfl,
      LinearMap.mem_range] at hmem
    obtain ⟨v, hvv⟩ := hmem
    exact ⟨v, hvv.trans hcup.symm⟩
  -- `δ(extend v)` is a global cocycle agreeing with `z ⌣ z` on `sub S`; apply the middle exactness.
  refine (deltaRelH_eq_zero_iff (cup z z) (coboundary_cup_self_mem_relCochains z h)).mpr
    ⟨coboundaryₗ X 3 (extendCochain S v), ?_, ?_⟩
  · exact coboundary_comp_coboundary X 3 (extendCochain S v)
  · refine (cochainPullback_subInclCM_eq_zero_iff S 4 _).1 ?_
    rw [map_sub]
    show cochainPullback (subInclCM S) 4 (cup z z)
        - cochainPullback (subInclCM S) 4 (coboundary X 3 (extendCochain S v)) = 0
    rw [← coboundary_cochainPullback, cochainPullback_extendCochain, hv, sub_self]

/-! ## §4. `relSq2 = 0` on `H³(S²×D³, S²×S²)` and the Wu-class vanishing `hv2`.

The ONE remaining geometric feeder is the **boundary mod-2 cohomology cup-square vanishing**

  `BoundaryCupSquareVanishes := ∀ c : Cohomology (sub ∂W) 2, cupH24 c c = 0`

on `∂W = sphereDiskBoundarySet ≃ S²×S²`. It is the project's isolated "basis-ID" atom: with the
factor-pullback basis `{α, β}` (`α := pr₁*g`, `β := pr₂*g`) of `H²(S²×S²;ℤ/2)`, `cupH24 c c = 0`
follows from `αᵢ ⌣ αᵢ = prᵢ*(g ⌣ g) = 0` (`cupH24_cohomologyPullback_factor` + `H⁴(S²;ℤ/2)=0`) and
the char-2 cross-term cancellation (`cupH24_symm`). The spanning of `H²(S²×S²;ℤ/2)` by `{α, β}` is
the same Künneth/cross-product datum flagged OPEN in `SphereProdCrossInt` (the integral Gram
`crossFamily_gram_eq_hyp` is conditional on it); it is left as a hypothesis here so `hv2` composes
with the (in-flight) `nondeg` feeder and that atom at the final concrete-datum assembly. -/

/-- The boundary mod-2 cohomology cup-square vanishing on `∂(S²×D³) ≃ S²×S²` — the single geometric
feeder of `hv2` (the isolated Künneth/"basis-ID" atom, see `SphereProdCrossInt`). -/
def BoundaryCupSquareVanishes : Prop :=
  ∀ c : Cohomology (sub (X := TopCat.of SphereDisk) sphereDiskBoundarySet) 2, cupH24 c c = 0

/-- **`relSq2 = 0` on `H³(S²×D³, S²×S²; ℤ/2)`** (given the boundary cup-square). Datum-free,
μ-independent: every `b` is a δ-image `deltaRelH z h` (§2), `relSq2` carries it to `deltaRelH (z ⌣ z)`
(`relSq2_deltaRelH`), which is `0` (`deltaRelH_cupSelf_eq_zero_of_cupSquare`, §3). -/
theorem sphereDiskRelSq2_eq_zero (hbsq : BoundaryCupSquareVanishes)
    (b : RelativeCohomology sphereDiskBoundarySet 3) :
    relSq2 (X := TopCat.of SphereDisk) b = 0 := by
  obtain ⟨z, h, rfl⟩ := exists_deltaRelH_of_relToAbs_eq_zero b (relToAbs_sphereDisk23_eq_zero b)
  rw [relSq2_deltaRelH z h]
  exact deltaRelH_cupSelf_eq_zero_of_cupSquare z h hbsq

/-- **`hv2` — the `(2,3)` Wu-class vanishing for the `S²×D³` datum** (given the boundary cup-square).
For any Lefschetz–Wu datum `P₂₃` on `(S²×D³, S²×S²)` whose `sqOp` is the genuine relative Steenrod
square `relSq2` (in particular every `LefschetzWuDatum.ofRelFund23 D …`), the middle Wu class
vanishes: `wuClass P₂₃ = 0`. Proof: `wuFunctional P₂₃ = P₂₃.mu ∘ relSq2 = 0`
(`sphereDiskRelSq2_eq_zero`), and the Wu class is the Lefschetz-dual of the Wu functional
(`pairing P (wuClass P) = wuFunctional P`), so it is `0`. Parametrised over `P₂₃` (mirroring
`sphereDiskNondeg23_of_intertwining`) so it composes with the `nondeg` feeder without collision. -/
theorem sphereDiskWuClass23_eq_zero (hbsq : BoundaryCupSquareVanishes)
    (P₂₃ : LefschetzWuDatum (TopCat.of SphereDisk) sphereDiskBoundarySet 2 3 5)
    (hsq : P₂₃.sqOp = relSq2 (X := TopCat.of SphereDisk)) :
    wuClass P₂₃ = 0 := by
  have hfun : wuFunctional P₂₃ = 0 := by
    simp only [wuFunctional, hsq]
    ext b
    rw [LinearMap.comp_apply, sphereDiskRelSq2_eq_zero hbsq b, map_zero, LinearMap.zero_apply]
  have hpair : pairing P₂₃ (0 : Cohomology (TopCat.of SphereDisk) 2) = wuFunctional P₂₃ := by
    rw [map_zero, hfun]
  rw [wuClass, Equiv.symm_apply_eq]
  exact hpair.symm

end

end SKEFTHawking.SphereProdP23WuVanish
