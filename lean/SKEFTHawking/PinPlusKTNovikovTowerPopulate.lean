/-
# Phase 5q.H close-out (#201) — THE TOWER POPULATION: the δ descent + the concrete-W data

`#196` built the ⊗ℝ FORM layer, the genuine-tower reduction `NovikovRealPairLES.ofGeometricPairLESData`,
and the 3b crux (`pullbackCochainInt_surjective`, `exists_lift_of_boundaryCocycle`). It stopped at a clean
boundary, deferring the **δ two-quotient descent** — packaging the lift-model `deltaRelHInt` as a genuine
`LinearMap` OUT of the boundary cohomology object `H²(∂W;ℤ) = Cohomology (sub S) 2` — and the population of
`NovikovGeometricPairLESData` from a concrete bounding `W`. This module lands the descent and the honest
population reduction.

## §1 — the δ two-quotient descent (the deferred chunk)

`deltaRelHInt z hz` is defined on an absolute **lift** `z` of a boundary class, not on the class itself.
To make `δ : H²(∂W;ℤ) → H³(W,∂W;ℤ)` a genuine `ℤ`-`LinearMap` we descend through the two quotients:

* **(i) lift-choice independence** (`deltaRelHInt_congr_of_pullback_eq`): two lifts `z, z'` of the same
  boundary cochain (`ι*z = ι*z'`) give the same `deltaRelHInt` — the difference `z − z'` restricts to `0`,
  hence is relative, and a relative lift has vanishing δ-class (`deltaRelHInt_relCochain_eq_zero`). The
  proof-transport `z = (z − z') + z'` under the dependent membership proof is routed through the abstract
  `deltaRelHInt_congr` (the `#191` abstract-X dodge — `subst` + definitional proof-irrelevance), never a
  raw dependent rewrite.
* **(ii) descent through the cocycle→cohomology quotient** (`deltaRelHIntLin`): the lift-choosing cocycle map
  `deltaBdryCocycleLin` (built via `exists_lift_of_boundaryCocycle` + independence) kills coboundaries — a
  boundary cocycle `δ_∂W u` has the convenient lift `δ_W ũ` (`ũ` any pullback lift of `u`), whose δ-class is
  `0` by `deltaRelHInt_of_cocycle_eq_zero` — so it descends via `Submodule.liftQ`.
* **(iii) the ℝ extension** — the coordinate route of `#196` (`SingularRelativeRealBaseChange`), matching the
  substrate's `Fin n → ℝ` boundary space; landed alongside the population in §2.

The money compatibility (`deltaRelHIntLin_restrictLift`): the descended map applied to the restriction class
`[ι*z]` recovers `deltaRelHInt z hz` — so the substrate's `hadj` argument `Cohomology.mk (sub S) 2
(restrictLiftCocycleInt v hv)` is exactly `δ[ι*v]`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTNovikovTowerInstantiate

namespace SKEFTHawking.PinPlusKTNovikovTowerPopulate

open scoped Matrix
open SKEFTHawking
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularRelativeUCInt
open SKEFTHawking.SingularRelativeCohomDeltaInt
open SKEFTHawking.SingularRelativeCapConnectingInt
open SKEFTHawking.SingularRelativeCapHadjInt
open SKEFTHawking.SingularCapChainInclInt (pullbackCochainInt pullbackCochainInt_apply)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.PinPlusKTNovikovTowerInstantiate

variable {X : TopCat} {S : Set X}

/-! ## §1. The δ two-quotient descent -/

/-- Pointwise additivity of the cochain pullback (`SingularCochainInt` is a Pi type; pullback precomposes
with `simplexIncl`, so the module operations pass through definitionally). -/
theorem pullbackCochainInt_add (k : ℕ) (a b : SingularCochainInt X k) :
    pullbackCochainInt S k (a + b) = pullbackCochainInt S k a + pullbackCochainInt S k b := rfl

theorem pullbackCochainInt_sub (k : ℕ) (a b : SingularCochainInt X k) :
    pullbackCochainInt S k (a - b) = pullbackCochainInt S k a - pullbackCochainInt S k b := rfl

theorem pullbackCochainInt_smul (k : ℕ) (s : ℤ) (a : SingularCochainInt X k) :
    pullbackCochainInt S k (s • a) = s • pullbackCochainInt S k a := rfl

/-- **`deltaRelHInt` respects propositional equality of the lift.** The dependent membership proof is
irrelevant: once the cochains agree, the δ-classes agree (definitional proof-irrelevance after `subst`).
The `#191` abstract-X transport primitive — used to avoid raw dependent rewrites of `deltaRelHInt`. -/
theorem deltaRelHInt_congr {n : ℕ} {z₁ z₂ : SingularCochainInt X n}
    (h₁ : coboundaryₗ X n z₁ ∈ relCochainsInt S (n + 1))
    (h₂ : coboundaryₗ X n z₂ ∈ relCochainsInt S (n + 1)) (hz : z₁ = z₂) :
    deltaRelHInt z₁ h₁ = deltaRelHInt z₂ h₂ := by
  subst hz; rfl

/-- **(i) Lift-choice independence of `deltaRelHInt`.** Two absolute lifts `z, z'` with equal restriction
(`ι*z = ι*z'`) have equal δ-class. The difference `z − z'` restricts to `0`, hence is relative
(`mem_relCochainsInt_of_pullbackCochainInt_eq_zero`); a relative lift has vanishing δ-class, and
`deltaRelHInt_add` splits `deltaRelHInt z = deltaRelHInt (z − z') + deltaRelHInt z' = deltaRelHInt z'`. -/
theorem deltaRelHInt_congr_of_pullback_eq (z z' : SingularCochainInt X 2)
    (h : coboundaryₗ X 2 z ∈ relCochainsInt S (2 + 1))
    (h' : coboundaryₗ X 2 z' ∈ relCochainsInt S (2 + 1))
    (hpb : pullbackCochainInt S 2 z = pullbackCochainInt S 2 z') :
    deltaRelHInt z h = deltaRelHInt z' h' := by
  have hd_rel : z - z' ∈ relCochainsInt S 2 :=
    mem_relCochainsInt_of_pullbackCochainInt_eq_zero _ (by rw [pullbackCochainInt_sub, hpb, sub_self])
  have hd : coboundaryₗ X 2 (z - z') ∈ relCochainsInt S (2 + 1) := by
    rw [map_sub]; exact Submodule.sub_mem _ h h'
  have key : deltaRelHInt (z - z' + z') (by rw [map_add]; exact Submodule.add_mem _ hd h')
      = deltaRelHInt z' h' := by
    rw [deltaRelHInt_add (z - z') z' hd h', deltaRelHInt_relCochain_eq_zero _ hd_rel, zero_add]
  rw [← key]
  exact deltaRelHInt_congr h _ (sub_add_cancel z z').symm

/-! ### The lift-choosing cocycle map and its descent -/

/-- A chosen absolute lift of a boundary cocycle `w` (`exists_lift_of_boundaryCocycle` + choice). -/
noncomputable def bdryLift (w : LinearMap.ker (coboundaryₗ (sub S) 2)) : SingularCochainInt X 2 :=
  (exists_lift_of_boundaryCocycle w).choose

theorem bdryLift_delta_mem (w : LinearMap.ker (coboundaryₗ (sub S) 2)) :
    coboundaryₗ X 2 (bdryLift w) ∈ relCochainsInt S (2 + 1) :=
  (exists_lift_of_boundaryCocycle w).choose_spec.1

theorem bdryLift_pullback (w : LinearMap.ker (coboundaryₗ (sub S) 2)) :
    pullbackCochainInt S 2 (bdryLift w) = (w : SingularCochainInt (sub S) 2) :=
  (exists_lift_of_boundaryCocycle w).choose_spec.2

/-- **The lift-choosing δ map on boundary cocycles.** `w ↦ deltaRelHInt (bdryLift w)`, `ℤ`-linear by
lift-choice independence: the chosen lift of `w₁ + w₂` and the sum of chosen lifts both restrict to
`w₁ + w₂`, so `deltaRelHInt_congr_of_pullback_eq` + `deltaRelHInt_add` give additivity (and `_smul`
scaling). -/
noncomputable def deltaBdryCocycleLin :
    LinearMap.ker (coboundaryₗ (sub S) 2) →ₗ[ℤ] RelativeCohomologyInt S (2 + 1) where
  toFun w := deltaRelHInt (bdryLift w) (bdryLift_delta_mem w)
  map_add' w₁ w₂ := by
    rw [← deltaRelHInt_add (bdryLift w₁) (bdryLift w₂) (bdryLift_delta_mem w₁) (bdryLift_delta_mem w₂)]
    exact deltaRelHInt_congr_of_pullback_eq _ _ _ _ (by
      rw [bdryLift_pullback, pullbackCochainInt_add, bdryLift_pullback, bdryLift_pullback,
        Submodule.coe_add])
  map_smul' s w := by
    rw [RingHom.id_apply, ← deltaRelHInt_smul s (bdryLift w) (bdryLift_delta_mem w)]
    exact deltaRelHInt_congr_of_pullback_eq _ _ _ _ (by
      rw [bdryLift_pullback, pullbackCochainInt_smul, bdryLift_pullback, SetLike.val_smul])

/-- **The lift-choosing δ map kills coboundaries.** A boundary coboundary `↑w = δ_∂W u` has the convenient
lift `δ_W ũ` (`ũ` any pullback lift of `u`), which restricts to `δ_∂W u = ↑w`; by independence
`deltaBdryCocycleLin w = deltaRelHInt (δ_W ũ)`, and that is `0` since `δ_W (δ_W ũ) = 0`
(`deltaRelHInt_of_cocycle_eq_zero`). -/
theorem deltaBdryCocycleLin_coboundary_eq_zero (w : LinearMap.ker (coboundaryₗ (sub S) 2))
    (hw : (w : SingularCochainInt (sub S) 2) ∈ coboundaryRange (sub S) 2) :
    deltaBdryCocycleLin w = 0 := by
  rw [show coboundaryRange (sub S) 2 = LinearMap.range (coboundaryₗ (sub S) 1) from rfl,
    LinearMap.mem_range] at hw
  obtain ⟨u, hu⟩ := hw
  obtain ⟨ut, hut⟩ := pullbackCochainInt_surjective 1 u
  have hcoc : coboundaryₗ X 2 (coboundaryₗ X 1 ut) = 0 := coboundary_comp_coboundary X 1 ut
  have hlift : pullbackCochainInt S 2 (coboundaryₗ X 1 ut) = (w : SingularCochainInt (sub S) 2) := by
    rw [show coboundaryₗ X 1 ut = coboundary X 1 ut from rfl,
      ← SKEFTHawking.SingularPullbackDualityCapSubInt.coboundary_pullbackCochainInt, hut,
      show coboundary (sub S) 1 u = coboundaryₗ (sub S) 1 u from rfl, hu]
  show deltaRelHInt (bdryLift w) (bdryLift_delta_mem w) = 0
  rw [deltaRelHInt_congr_of_pullback_eq (bdryLift w) (coboundaryₗ X 1 ut) (bdryLift_delta_mem w)
    (by rw [hcoc]; exact Submodule.zero_mem _) (by rw [bdryLift_pullback, hlift])]
  exact deltaRelHInt_of_cocycle_eq_zero _ _ hcoc

/-- **(ii) The δ connecting map, descended to `H²(∂W;ℤ)`.** `deltaRelHIntLin : H²(∂W;ℤ) → H³(W,∂W;ℤ)` — the
genuine `ℤ`-`LinearMap` obtained by `Submodule.liftQ` of the lift-choosing `deltaBdryCocycleLin` through the
cocycle→cohomology quotient (it kills coboundaries by `deltaBdryCocycleLin_coboundary_eq_zero`). This is the
pair-LES connecting map as a map out of the boundary cohomology OBJECT. -/
noncomputable def deltaRelHIntLin :
    Cohomology (sub S) 2 →ₗ[ℤ] RelativeCohomologyInt S (2 + 1) :=
  Submodule.liftQ _ deltaBdryCocycleLin (by
    intro w hw
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at hw
    rw [LinearMap.mem_ker]
    exact deltaBdryCocycleLin_coboundary_eq_zero w hw)

@[simp] theorem deltaRelHIntLin_mk (w : LinearMap.ker (coboundaryₗ (sub S) 2)) :
    deltaRelHIntLin (Cohomology.mk (sub S) 2 w) = deltaRelHInt (bdryLift w) (bdryLift_delta_mem w) := rfl

/-- **The money compatibility: `deltaRelHIntLin [ι*z] = deltaRelHInt z`.** The descended δ applied to the
restriction class `[ι*z]` recovers the lift-model δ-class of `z`. So the substrate's `hadj` argument
`Cohomology.mk (sub S) 2 (restrictLiftCocycleInt v hv)` IS `δ[ι*v]` — the connecting map of the boundary
class `[ι*v]`. Proof: both `bdryLift (ι*z)` and `z` restrict to `ι*z`, so lift-choice independence. -/
theorem deltaRelHIntLin_restrictLift (z : SingularCochainInt X 2)
    (hz : coboundaryₗ X 2 z ∈ relCochainsInt S (2 + 1)) :
    deltaRelHIntLin (Cohomology.mk (sub S) 2 (restrictLiftCocycleInt z hz)) = deltaRelHInt z hz := by
  rw [deltaRelHIntLin_mk]
  exact deltaRelHInt_congr_of_pullback_eq _ _ _ _ (by
    rw [bdryLift_pullback, restrictLiftCocycleInt_coe])

/-! ## §2. The integral restriction `ι*` on cohomology and the pair-LES composite `δ ∘ ι* = 0`

The substrate's `rest2` is the base-change of the integral `ι* : H²(W;ℤ) → H²(∂W;ℤ)` on the cohomology
OBJECTS. `#196` had the cocycle-level `restrictCocycleInt`; here it is descended to a genuine `ℤ`-`LinearMap`
`restrictHInt` (integral mirror of the ZMod-2 `restrictToSub`), and coupled to the §1 descended `δ` to give
the pair-LES composite `δ ∘ ι* = 0` (the `im ι* ⊆ ker δ` half of the middle exactness, on the objects). -/

/-- The cochain pullback `ι*` as an integral `LinearMap` (pointwise; `#196` had it as a bare function). -/
noncomputable def pullbackCochainIntLin (k : ℕ) :
    SingularCochainInt X k →ₗ[ℤ] SingularCochainInt (sub S) k where
  toFun := pullbackCochainInt S k
  map_add' := pullbackCochainInt_add k
  map_smul' := pullbackCochainInt_smul k

/-- The restriction `ι*` on cocycle representatives, as an integral `LinearMap`
`ker δ_W → ker δ_∂W` (codRestrict of the pullback; cocycles restrict to cocycles). -/
noncomputable def restrictCocycleIntLin (k : ℕ) :
    LinearMap.ker (coboundaryₗ X k) →ₗ[ℤ] LinearMap.ker (coboundaryₗ (sub S) k) :=
  ((pullbackCochainIntLin k).comp (LinearMap.ker (coboundaryₗ X k)).subtype).codRestrict
    (LinearMap.ker (coboundaryₗ (sub S) k)) (fun a => (restrictCocycleInt a).2)

@[simp] theorem restrictCocycleIntLin_coe (k : ℕ) (a : LinearMap.ker (coboundaryₗ X k)) :
    ((restrictCocycleIntLin k a : LinearMap.ker (coboundaryₗ (sub S) k)) :
      SingularCochainInt (sub S) k) = pullbackCochainInt S k a.1 := rfl

/-- **The integral restriction `ι* : H²(W;ℤ) → H²(∂W;ℤ)` on cohomology.** The descent of the cocycle map
`restrictCocycleIntLin` through the cohomology quotient (it kills coboundaries: `ι*(δ_W β) = δ_∂W(ι*β)` is a
`∂W`-coboundary, via `coboundary_pullbackCochainInt`). The integral mirror of the ZMod-2 `restrictToSub`;
the substrate's `rest2` carrier at the integral level. -/
noncomputable def restrictHInt : Cohomology X 2 →ₗ[ℤ] Cohomology (sub S) 2 :=
  Submodule.liftQ _ ((Submodule.mkQ _).comp (restrictCocycleIntLin 2)) (by
    intro a ha
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply] at ha
    rw [LinearMap.mem_ker]
    change Submodule.Quotient.mk _ = 0
    rw [Submodule.Quotient.mk_eq_zero]
    simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]
    rw [show coboundaryRange X 2 = LinearMap.range (coboundaryₗ X 1) from rfl] at ha
    obtain ⟨β, hβ⟩ := ha
    rw [show coboundaryRange (sub S) 2 = LinearMap.range (coboundaryₗ (sub S) 1) from rfl]
    refine ⟨pullbackCochainInt S 1 β, ?_⟩
    rw [restrictCocycleIntLin_coe, ← hβ,
      show coboundaryₗ (sub S) 1 (pullbackCochainInt S 1 β) = coboundary (sub S) 1 (pullbackCochainInt S 1 β)
        from rfl, SKEFTHawking.SingularPullbackDualityCapSubInt.coboundary_pullbackCochainInt]
    rfl)

@[simp] theorem restrictHInt_mk (a : LinearMap.ker (coboundaryₗ X 2)) :
    restrictHInt (Cohomology.mk X 2 a) = Cohomology.mk (sub S) 2 (restrictCocycleIntLin 2 a) := rfl

/-- **The pair-LES composite `δ ∘ ι* = 0` on cohomology.** The connecting map of a restricted absolute class
vanishes — the `im ι* ⊆ ker δ` half of the pair-LES middle exactness, on the cohomology objects. Proof: an
absolute cocycle `a` is its own boundary lift (`ι*a = pullbackCochainInt a`, `δa = 0` relative), so
`deltaRelHIntLin [ι*a] = deltaRelHInt a = 0` (`deltaRelHIntLin_restrictLift` + `deltaRelHInt_of_cocycle_eq_zero`). -/
theorem deltaRelHIntLin_restrictHInt (c : Cohomology X 2) :
    deltaRelHIntLin (restrictHInt (S := S) c) = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  have hz : coboundaryₗ X 2 (a : SingularCochainInt X 2) ∈ relCochainsInt S (2 + 1) := by
    rw [LinearMap.mem_ker.mp a.2]; exact Submodule.zero_mem _
  rw [show (Submodule.Quotient.mk a : Cohomology X 2) = Cohomology.mk X 2 a from rfl, restrictHInt_mk,
    show Cohomology.mk (sub S) 2 (restrictCocycleIntLin 2 a)
      = Cohomology.mk (sub S) 2 (restrictLiftCocycleInt (a : SingularCochainInt X 2) hz) from
      congrArg (Cohomology.mk (sub S) 2) (Subtype.ext (by rw [restrictCocycleIntLin_coe,
        restrictLiftCocycleInt_coe])), deltaRelHIntLin_restrictLift]
  exact deltaRelHInt_of_cocycle_eq_zero _ hz (LinearMap.mem_ker.mp a.2)

end SKEFTHawking.PinPlusKTNovikovTowerPopulate
