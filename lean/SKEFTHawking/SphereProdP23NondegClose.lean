/-
# Route (c′) P5 — the `(2,3)` `nondeg` assembly by the DIRECT cap-injectivity argument

The `S²×D³` `(2,3)` Poincaré–Lefschetz non-degeneracy — `Function.Injective ((relCupH23).compr₂ D.mu)`
for the relative fundamental-class datum `D` — proven DIRECTLY, with NO `β`/`hcompat` intertwining
(no `[D³,∂D³]` cup-Fubini residual). The chain is P1→P4:

* the cap–connecting square (`SingularCapConnecting.connecting_capRelH`, P2) +
  `connecting_sphereDiskBoundary_ne_zero` (P1) + `eq_betaClass_of_ne_zero` (P3) +
  `capH21_sub_ne_zero` (P4) give the **cap detection** `a ≠ 0 ⟹ capRelH 2 2 a [W,∂W] ≠ 0`;
* the banked adjunction `SingularRelativeCupCap23.relKroneckerH_relCupH23`
  (`⟨a ∪ b, [W,∂W]⟩ = ⟨b, a ⌢ [W,∂W]⟩`) + the perfect relative Kronecker pairing
  (`SingularRelativeKroneckerEquiv.relKroneckerHEquiv`) turn the nonzero cap into a nonzero pairing
  functional, hence injectivity.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`.
-/
import Mathlib
import SKEFTHawking.SphereProdP23Nondeg
import SKEFTHawking.SphereDiskConnectingDetect
import SKEFTHawking.SingularCapConnecting
import SKEFTHawking.SphereProdHFourMod2Detect
import SKEFTHawking.SphereProdCapDetect
import SKEFTHawking.SingularRelativeKroneckerEquiv
import SKEFTHawking.SingularRelativeCupCap23
import SKEFTHawking.PinPlusKTSphereProdRelFund

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularCohomologyFunctoriality
open SKEFTHawking.SingularCapHomology
open SKEFTHawking.SingularRelativeCapHomology
open SKEFTHawking.SingularRelativePairing
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.SingularPairLES
open SKEFTHawking.PinPlusKTSphereProdRelFundWuRoots
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.SphereDiskConnectingDetect
open SKEFTHawking.SphereProdHFourMod2Detect
open SKEFTHawking.SphereProdCapDetect
open SKEFTHawking.SingularRelativeKroneckerEquiv
open SKEFTHawking.SingularRelativeCupCap23

namespace SKEFTHawking.SphereProdP23NondegClose

/-- **The `(2,3)` `nondeg`, direct cap-injectivity argument (parametrized).** For any relative
fundamental-class datum `D` on `(S²×D³, S²×S²)` whose class is nonzero (`hcls`) and whose cohomology
restriction to the boundary is nonzero on nonzero classes (`hfeeder`), the sphereDisk `(2,3)` pairing
`(a,b) ↦ ⟨a ∪ b, [W,∂W]⟩` is left non-degenerate. No `β`/`hcompat` residual — the detection is the
P1→P4 cap chain + the perfect relative Kronecker pairing. -/
theorem sphereDiskNondeg23_direct
    [FiniteDimensional (ZMod 2)
      (RelativeHomology (X := TopCat.of SphereDisk) sphereDiskBoundarySet 3)]
    (D : RelFundClassDatum (m := 3) (X := TopCat.of SphereDisk) sphereDiskBoundarySet)
    (hcls : D.cls ≠ 0)
    (hfeeder : ∀ a : Cohomology (TopCat.of SphereDisk) 2, a ≠ 0 →
        cohomologyPullback (SingularCapConnecting.inclC sphereDiskBoundarySet) 2 a ≠ 0) :
    Function.Injective
      ⇑((relCupH23 (X := TopCat.of SphereDisk) (S := sphereDiskBoundarySet)).compr₂ D.mu) := by
  -- (B) the cap detection: a ≠ 0 ⟹ capRelH 2 2 a D.cls ≠ 0
  have hcapdet : ∀ a : Cohomology (TopCat.of SphereDisk) 2, a ≠ 0 →
      capRelH 2 2 a D.cls ≠ 0 := by
    intro a ha hcap0
    have hg' := hfeeder a ha
    have hconn4 : connecting (X := TopCat.of SphereDisk) sphereDiskBoundarySet 4 D.cls = betaClass :=
      eq_betaClass_of_ne_zero (connecting (X := TopCat.of SphereDisk) sphereDiskBoundarySet 4 D.cls)
        (connecting_sphereDiskBoundary_ne_zero D.cls hcls)
    have hnat := SingularCapConnecting.connecting_capRelH (X := TopCat.of SphereDisk)
      sphereDiskBoundarySet a D.cls
    -- term-mode chain (avoids concrete-type `rw`/`apply` isDefEq blowup):
    --   capH 2 1 g' β = capH 2 1 g' (δ₄ cls) = δ₂ (a ⌢ cls) = δ₂ 0 = 0
    have hzero : capH 2 1 (cohomologyPullback (SingularCapConnecting.inclC sphereDiskBoundarySet) 2 a)
        betaClass = 0 :=
      (congrArg (fun z => capH 2 1
          (cohomologyPullback (SingularCapConnecting.inclC sphereDiskBoundarySet) 2 a) z)
        hconn4.symm).trans
        (hnat.symm.trans
          ((congrArg (fun w => connecting (X := TopCat.of SphereDisk) sphereDiskBoundarySet 2 w)
            hcap0).trans (map_zero _)))
    exact capH21_sub_ne_zero _ hg' hzero
  -- (C) the perfect-pairing finish + assembly
  rw [injective_iff_map_eq_zero]
  intro a ha
  by_contra hane
  apply hcapdet a hane
  refine (Module.forall_dual_apply_eq_zero_iff (ZMod 2) (capRelH 2 2 a D.cls)).mp ?_
  intro φ
  obtain ⟨ω, rfl⟩ :=
    (relKroneckerHEquiv (X := TopCat.of SphereDisk) sphereDiskBoundarySet 2).surjective φ
  exact (LinearMap.congr_fun (relKroneckerHEquiv_apply (X := TopCat.of SphereDisk)
      sphereDiskBoundarySet 2 ω) (capRelH 2 2 a D.cls)).trans
    ((relKroneckerH_relCupH23 a ω D.cls).symm.trans
      ((D.mu_apply (relCupH23 a ω)).symm.trans (LinearMap.congr_fun ha ω)))

/-! ## §2. The concrete inputs: the feeder (section trick), the finite-dim instance, `D.cls ≠ 0`. -/

open SKEFTHawking.SingularCohomologyFunctoriality in
/-- **The feeder** — the boundary-restriction `H²(S²×D³) → H²(∂W)` is injective, so `a ≠ 0 ⟹ a|_∂W ≠ 0`.
Section trick: `τ : S² → S²×D³`, `y ↦ (y, y₀)` with `y₀ ∈ ∂D³ ⊆ D³`, factors through `∂W`
(`τ = (inclC ∂W) ∘ σ`) and has `pr₁ ∘ τ = id`, so `τ^*` is a retraction — surjective, hence (rank-1
`H²(S²×D³) = H²(S²) = ℤ/2`) injective; being the composite `σ^* ∘ (inclC)^*`, the boundary restriction
`(inclC)^*` is its injective inner factor. -/
theorem feeder_sphereDisk (a : Cohomology (TopCat.of SphereDisk) 2) (ha : a ≠ 0) :
    cohomologyPullback (SingularCapConnecting.inclC sphereDiskBoundarySet) 2 a ≠ 0 := by
  obtain ⟨v, hv⟩ : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  let y₀ : ThreeDisk := ⟨v, Metric.sphere_subset_closedBall hv⟩
  let τ : C(↑(TopCat.of TwoSphere), ↑(TopCat.of SphereDisk)) :=
    ⟨fun y => (y, y₀), by fun_prop⟩
  have hmem : ∀ y : ↑(TopCat.of TwoSphere), ((y, y₀) : SphereDisk) ∈ sphereDiskBoundarySet :=
    fun _ => hv
  let σ : C(↑(TopCat.of TwoSphere), ↑(sub (X := TopCat.of SphereDisk) sphereDiskBoundarySet)) :=
    ⟨fun y => (⟨(y, y₀), hmem y⟩ :
        ↑(sub (X := TopCat.of SphereDisk) sphereDiskBoundarySet)), by fun_prop⟩
  let pr₁ : C(↑(TopCat.of SphereDisk), ↑(TopCat.of TwoSphere)) := ⟨Prod.fst, continuous_fst⟩
  have hστ : (SingularCapConnecting.inclC sphereDiskBoundarySet).comp σ = τ :=
    ContinuousMap.ext fun _ => rfl
  have hpr : pr₁.comp τ = ContinuousMap.id ↑(TopCat.of TwoSphere) := ContinuousMap.ext fun _ => rfl
  -- τ^* is surjective (right inverse pr₁^*)
  have hrinv : (cohomologyPullback τ 2).comp (cohomologyPullback pr₁ 2) = LinearMap.id := by
    rw [← cohomologyPullback_comp, hpr, cohomologyPullback_id]
  have hsurj : Function.Surjective (cohomologyPullback τ 2) :=
    Function.RightInverse.surjective (g := cohomologyPullback pr₁ 2)
      (fun x => LinearMap.congr_fun hrinv x)
  -- τ^* injective (rank-1: H²(S²×D³) = H²(S²) = ℤ/2)
  haveI : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of SphereDisk) 2) :=
    SphereProdP23.sphereDisk_findimAbs23
  haveI : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of TwoSphere) 2) :=
    SKEFTHawking.SingularMVCohomologyFinite.finiteDimensional_cohomology_of_homology
      (X := TopCat.of TwoSphere) 1 SphereProdP23.finiteDimensional_twoSphere_homology_two
  have hdim : Module.finrank (ZMod 2) (Cohomology (TopCat.of SphereDisk) 2)
      = Module.finrank (ZMod 2) (Cohomology (TopCat.of TwoSphere) 2) :=
    SphereProdP23.finrank_sphereDisk_cohomology_two.trans
      SphereProdP23Nondeg.finrank_twoSphere_cohomology_two.symm
  have hinjτ : Function.Injective (cohomologyPullback τ 2) :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdim).mpr hsurj
  -- (inclC)^* is the injective inner factor of τ^* = σ^* ∘ (inclC)^*. The composed LinearMap TYPE
  -- over `Cohomology (sub …)` whnf-blows if written as an annotation, so we only ever consume the
  -- pre-elaborated functoriality term `hc` (pinned TopCats) POINTWISE at `a` — no composed-type ascription.
  have hc := @cohomologyPullback_comp (TopCat.of TwoSphere) _ (TopCat.of SphereDisk)
    (SingularCapConnecting.inclC sphereDiskBoundarySet) σ 2
  have hτeq := (congrArg (fun f => cohomologyPullback f 2) hστ).symm.trans hc
  exact fun h0 => ha (hinjτ
    (((LinearMap.congr_fun hτeq a).trans
        ((LinearMap.comp_apply _ _ a).trans
          ((congrArg (cohomologyPullback σ 2) h0).trans (map_zero _)))).trans
      (map_zero (cohomologyPullback τ 2)).symm))

/-! ## §3. Piece 1 (finite-dim instance) + the generic interior-point `cls ≠ 0` + the concrete close. -/

open SKEFTHawking.PoincareLefschetzRelFundClassGeom
open SKEFTHawking.PinPlusTraceRelFundReduce
open SKEFTHawking.PinPlusKTSphereProdRelFund
-- `J6`'s `HC`-atlas on `SphereDisk` is registered `local` in `PinPlusKTSphereProdReassoc`; the
-- provider `relFundClassDatumOf` needs it as the `[ChartedSpace HC SphereDisk]` instance.
attribute [local instance] SKEFTHawking.SpinSigmaRoute.chartW6


/-- **Piece 1** — `H₃(S²×D³, S²×S²;ℤ/2)` is finite-dimensional, the `[FiniteDimensional …]` instance
`sphereDiskNondeg23_direct` requires. Pair-LES sandwich (`finiteDimensional_relativeHomology_of_pair`)
fed by `H₃(W;ℤ/2) = 0` (`finiteDimensional_sphereDisk_homology_three`) and `H₂(∂W;ℤ/2)` finite
(`finiteDimensional_sphereDiskBoundary_homology_two`). The relative-homology twin of the banked
relative-cohomology `sphereDisk_findimRel23`. -/
instance sphereDiskBoundary_finiteDimensional_relativeHomology_three :
    FiniteDimensional (ZMod 2)
      (RelativeHomology (X := TopCat.of SphereDisk) sphereDiskBoundarySet 3) :=
  SKEFTHawking.SingularMVCohomologyFinite.finiteDimensional_relativeHomology_of_pair
    (X := TopCat.of SphereDisk) sphereDiskBoundarySet 2
    SphereProdP23.finiteDimensional_sphereDisk_homology_three
    SphereProdP23.finiteDimensional_sphereDiskBoundary_homology_two

/-- **Generic `cls ≠ 0` from the interior-generator restriction.** Any relative fundamental-class
datum `D` on `(W, ∂W)` is nonzero: at any interior point `x ∉ ∂W`, `D.restricts` pins
`restrictBd D.cls = (gen x hx)⁻¹ 1`, and `(gen x hx)⁻¹ 1 ≠ 0` (an iso, `1 ≠ 0` in `ℤ/2`); were
`D.cls = 0` the restriction would vanish. The relative twin of
`IntOrientationSection.intOrientationData_restricts_ne_zero`. -/
theorem relFundClassDatum_cls_ne_zero {X : TopCat} {m : ℕ} {S : Set ↑X}
    (D : PoincareLefschetzRelFundClass.RelFundClassDatum (m := m) S) {x : ↑X} (hx : x ∉ S) :
    D.cls ≠ 0 := by
  intro h0
  have hr : PoincareLefschetzRelFundClass.restrictBd S hx (m + 2) D.cls = (D.gen x hx).symm 1 :=
    D.restricts x hx
  rw [h0, map_zero] at hr
  have hfwd : (D.gen x hx) ((D.gen x hx).symm 1) = (D.gen x hx) 0 := congrArg (D.gen x hx) hr.symm
  rw [LinearEquiv.apply_symm_apply, map_zero] at hfwd
  exact one_ne_zero hfwd

/-- **The concrete `S²×D³` relative fundamental-class datum** on `sphereDiskBoundarySet`, transported
from the carrier-agnostic provider `relFundClassDatumOf` (canonical `εtrace`, interior trace generators)
applied to the UNCONDITIONAL existence witness `hasRelFundClass_sphereDisk`, along the reducible
`sphereDisk_boundary_eq : (J6).boundary SphereDisk = sphereDiskBoundarySet`. -/
noncomputable def sphereDiskRelFundDatum :
    PoincareLefschetzRelFundClass.RelFundClassDatum (X := TopCat.of SphereDisk) (m := 3)
      sphereDiskBoundarySet :=
  sphereDisk_boundary_eq ▸ relFundClassDatumOf (W := SphereDisk) J6 εtrace hasRelFundClass_sphereDisk

/-- **The concrete `(2,3)` `nondeg`, UNCONDITIONAL.** The `S²×D³` Poincaré–Lefschetz `(2,3)`
non-degeneracy `Function.Injective ((relCupH23).compr₂ sphereDiskRelFundDatum.mu)` — the direct
cap-injectivity route (`sphereDiskNondeg23_direct`) instantiated at the concrete transported datum,
with all three inputs discharged: piece 1 (`FiniteDimensional (RelativeHomology … 3)` instance), the
class non-vanishing (`relFundClassDatum_cls_ne_zero` at the interior point `(p, 0)`, `0 ∉ ∂D³`), and the
boundary-restriction feeder (`feeder_sphereDisk`). No `β`/`hcompat` residual, no hypotheses. -/
theorem sphereDiskNondeg23 :
    Function.Injective
      ⇑((relCupH23 (X := TopCat.of SphereDisk) (S := sphereDiskBoundarySet)).compr₂
        sphereDiskRelFundDatum.mu) := by
  obtain ⟨p, hp⟩ : (Metric.sphere (0 : EuclideanSpace ℝ (Fin 3)) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  exact sphereDiskNondeg23_direct sphereDiskRelFundDatum
    (relFundClassDatum_cls_ne_zero sphereDiskRelFundDatum
      (x := (⟨p, hp⟩, ⟨0, Metric.mem_closedBall_self zero_le_one⟩))
      (by simp [sphereDiskBoundarySet]))
    feeder_sphereDisk

/-! ## §4. STRETCH — the `dimeq` residual (`homIncl ≠ 0`) from the feeder, and the assembled `(2,3)` datum. -/

/-- **The boundary inclusion `S²×S² ↪ S²×D³` is nonzero on `H₂(·;ℤ/2)`** — the surviving-`S²`-class
`dimeq` residual, discharged from the feeder by the Kronecker adjunction. If `homIncl = 0` then for
every `a, z`, `⟨a|_∂W, z⟩ = ⟨a, homIncl z⟩ = 0` (`kroneckerH_cohomologyPullback` + `homIncl_eq_map`),
so `a|_∂W = 0` by the perfect boundary pairing (`kroneckerHEquiv`); but `feeder_sphereDisk` makes
`a|_∂W ≠ 0` for the nonzero `a₀ ∈ H²(W)` (rank `1`). -/
theorem sphereDiskHomIncl_ne_zero :
    homIncl (X := TopCat.of SphereDisk) sphereDiskBoundarySet 2 ≠ 0 := by
  intro h0
  haveI : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of SphereDisk) 2) :=
    SphereProdP23.sphereDisk_findimAbs23
  haveI : Nontrivial (Cohomology (TopCat.of SphereDisk) 2) :=
    Module.nontrivial_of_finrank_pos (R := ZMod 2)
      (by rw [SphereProdP23.finrank_sphereDisk_cohomology_two]; norm_num)
  obtain ⟨a₀, ha₀⟩ := exists_ne (0 : Cohomology (TopCat.of SphereDisk) 2)
  have hmaps : SingularCapConnecting.inclC (X := TopCat.of SphereDisk) sphereDiskBoundarySet
      = SingularCohomologyPairRestrict.subInclCM (X := TopCat.of SphereDisk) sphereDiskBoundarySet := by
    apply ContinuousMap.ext; intro x; rfl
  refine feeder_sphereDisk a₀ ha₀ ?_
  refine (SKEFTHawking.SingularKroneckerEquiv.kroneckerHEquiv
    (X := sub (X := TopCat.of SphereDisk) sphereDiskBoundarySet) 1).injective ?_
  rw [map_zero]
  ext z
  rw [SKEFTHawking.SingularKroneckerEquiv.kroneckerHEquiv_apply,
    kroneckerH_cohomologyPullback, hmaps,
    ← PoincareLefschetzRelFundClassCylinderSuspension.homIncl_eq_map, h0]
  simp

/-- **The `(2,3)` `dimeq`, UNCONDITIONAL** — the sole boundary residual `homIncl ≠ 0`
(`sphereDiskHomIncl_ne_zero`) discharged, so `dim H²(S²×D³;ℤ/2) = dim H³(S²×D³,S²×S²;ℤ/2)`. -/
theorem sphereDiskDimeq23 :
    Module.finrank (ZMod 2) (Cohomology (TopCat.of SphereDisk) 2)
      = Module.finrank (ZMod 2)
        (RelativeCohomology (X := TopCat.of SphereDisk) sphereDiskBoundarySet 3) :=
  SphereProdP23.sphereDiskDimeq23_of_homIncl_ne_zero sphereDiskHomIncl_ne_zero

/-- **The `S²×D³` `(2,3)` Lefschetz–Wu datum, UNCONDITIONAL** — `LefschetzWuDatum … 2 3 5` assembled by
`ofRelFund23` from the concrete relative fundamental-class datum with all four PL-duality numerics
discharged: `findimAbs`, `findimRel` (banked), the direct cap-injectivity `nondeg`
(`sphereDiskNondeg23`), and `dimeq` (`sphereDiskDimeq23`; the boundary residual closed via the feeder).
No `β`/`hcompat` residual, no open hypotheses — the full `(2,3)` leg of the `S²×D³` W-admissibility. -/
noncomputable def sphereDiskP23 :
    PoincareLefschetzWu5.LefschetzWuDatum (TopCat.of SphereDisk) sphereDiskBoundarySet 2 3 5 :=
  PoincareLefschetzWuAssembly.LefschetzWuDatum.ofRelFund23 sphereDiskRelFundDatum
    SphereProdP23.sphereDisk_findimAbs23 SphereProdP23.sphereDisk_findimRel23
    sphereDiskNondeg23 sphereDiskDimeq23

/-- **`ofRelFund23_pinned`** — the assembled `(2,3)` datum's `mu` field is exactly the concrete relative
fundamental-class functional `sphereDiskRelFundDatum.mu` (the Wu tower consumes `μ = ⟨·, [W,∂W]⟩`). -/
theorem sphereDiskP23_mu : (sphereDiskP23).mu = sphereDiskRelFundDatum.mu := rfl

end SKEFTHawking.SphereProdP23NondegClose
