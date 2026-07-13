/-
# Phase 5q.H (W-A.1e cyl) — the S-side restriction leg of the cohomology pair sequence

The cohomology-pair companion of the forgetful leg `relToAbs : Hⁿ(X,S) → Hⁿ(X)`
(`SingularRelativeAbsCompat`): the **restriction to the subspace** `i* : Hⁿ(X) → Hⁿ(sub S)`, the
pullback along the inclusion `sub S ↪ X`, together with the pair-sequence *complex property*
`i* ∘ relToAbs = 0` — the middle-of-the-pair leg of

  ⋯ → Hⁿ(X, S) --relToAbs--> Hⁿ(X) --i*--> Hⁿ(sub S) --∂--> Hⁿ⁺¹(X, S) → ⋯

The technical heart is the **cochain-level characterization** `i*(f) = 0 ⟺ f ∈ relCochains(X,S)`: a
singular cochain restricts to `0` on the subspace exactly when it annihilates the subspace chains
(the definition of a relative cochain). This is proved via the identification of the inclusion
pushforward `mapSimplex (incl) = simplexIncl` and the Kronecker adjunction
`⟨incl*f, c⟩ = ⟨f, incl_# c⟩`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SingularRelativeAbsCompat
import SKEFTHawking.SingularCohomologyFunctoriality
import SKEFTHawking.SingularExcision

namespace SKEFTHawking.SingularCohomologyPairRestrict

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativeAbsCompat
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularCohomologyFunctoriality
open SKEFTHawking.SingularExcision

variable {X : TopCat} (S : Set ↑X)

/-! ## §1. The inclusion as a bundled continuous map, and its pushforward = `simplexIncl` -/

/-- The subspace inclusion `sub S ↪ X` as a bundled continuous map. -/
noncomputable def subInclCM : C(↑(sub S), ↑X) := ConcreteCategory.hom (inclMap S)

/-- The inclusion pushforward on simplices is exactly `simplexIncl`. -/
theorem mapSimplex_subInclCM (n : ℕ)
    (σ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk n))) :
    mapSimplex (subInclCM S) σ = simplexIncl S n σ := by
  apply (X.toSSetObjEquiv (op (SimplexCategory.mk n))).injective
  simp only [mapSimplex, Equiv.apply_symm_apply]
  rw [toSSetObjEquiv_simplexIncl]
  rfl

/-- The inclusion pushforward on chains is exactly `chainIncl`. -/
theorem mapChain_subInclCM (n : ℕ) : mapChain (subInclCM S) n = chainIncl S n := by
  apply Finsupp.lhom_ext
  intro σ a
  rw [mapChain_single, chainIncl_single, mapSimplex_subInclCM]

/-! ## §2. The cochain-level characterization of relative cochains -/

/-- **A cochain restricts to `0` on the subspace iff it is a relative cochain.** `i*(f) = 0` means
`f` vanishes on every inclusion-pushed simplex `simplexIncl σ`, i.e. (by linearity + the Kronecker
adjunction) `f` annihilates every subspace chain — the definition of `relCochains`. -/
theorem cochainPullback_subInclCM_eq_zero_iff (n : ℕ) (f : SingularCochain X n) :
    cochainPullback (subInclCM S) n f = 0 ↔ f ∈ relCochains S n := by
  constructor
  · intro h c hc
    obtain ⟨c', rfl⟩ := hc
    rw [← mapChain_subInclCM, ← kronecker_cochainPullback, h]
    simp only [kronecker_apply, Pi.zero_apply, mul_zero, Finsupp.sum_fun_zero]
  · intro hf
    funext σ
    show cochainPullback (subInclCM S) n f σ = 0
    rw [cochainPullback_apply, mapSimplex_subInclCM]
    have hmem : Finsupp.single (simplexIncl S n σ) (1 : ZMod 2) ∈ subspaceChains S n :=
      ⟨Finsupp.single σ 1, by rw [chainIncl_single]⟩
    have h0 := hf _ hmem
    rwa [kronecker_single, one_mul] at h0

/-! ## §3. The restriction leg `i* : Hⁿ(X) → Hⁿ(sub S)` and the complex property -/

/-- **The S-side restriction** `i* : Hⁿ(X; ℤ/2) → Hⁿ(sub S; ℤ/2)` — the pullback along the subspace
inclusion `sub S ↪ X`. The third leg of the cohomology pair sequence. -/
noncomputable def restrictToSub (n : ℕ) : Cohomology X n →ₗ[ZMod 2] Cohomology (sub S) n :=
  cohomologyPullback (subInclCM S) n

@[simp] theorem restrictToSub_mk (n : ℕ) (a : LinearMap.ker (coboundaryₗ X n)) :
    restrictToSub S n (Cohomology.mk X n a)
      = Cohomology.mk (sub S) n ⟨cochainPullback (subInclCM S) n a.1,
          cochainPullback_mem_ker (subInclCM S) a⟩ :=
  rfl

/-- **The pair-sequence complex property** `i* ∘ relToAbs = 0`: the restriction of an
absolutified relative class is `0`, because the underlying relative cochain restricts to `0` on the
subspace (`cochainPullback_subInclCM_eq_zero_iff`). This is the honest middle leg of the pair
sequence (`im relToAbs ⊆ ker i*`). -/
theorem restrictToSub_relToAbs (n : ℕ) (y : RelativeCohomology S n) :
    restrictToSub S n (relToAbs y) = 0 := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  show restrictToSub S n (relToAbs (RelativeCohomology.mk S n a)) = 0
  rw [relToAbs_mk, restrictToSub_mk]
  have hz : cochainPullback (subInclCM S) n (relToAbsCocycleₗ a).1 = 0 :=
    (cochainPullback_subInclCM_eq_zero_iff S n _).2 (by
      rw [relToAbsCocycleₗ_coe]; exact a.1.2)
  rw [show Cohomology.mk (sub S) n ⟨cochainPullback (subInclCM S) n (relToAbsCocycleₗ a).1, _⟩
      = Cohomology.mk (sub S) n ⟨(0 : SingularCochain (sub S) n),
          (LinearMap.mem_ker).mpr (by simp)⟩ from congrArg (Cohomology.mk (sub S) n) (Subtype.ext hz)]
  rfl

/-! ## §4. The cochain extension: `i*` is surjective on cochains -/

open Classical in
/-- Extend a cochain `g` on `sub S` to `X`: on a simplex `τ` of `X` whose realization lands in `S`,
evaluate `g` on the corestricted simplex; elsewhere `0`. -/
noncomputable def extendCochain {n : ℕ} (g : SingularCochain (sub S) n) : SingularCochain X n :=
  fun τ =>
    if h : Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) ⊆ S then
      g ((sub S).toSSetObjEquiv (op (SimplexCategory.mk n))|>.symm
        ⟨Set.codRestrict (X.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) S (fun t => h ⟨t, rfl⟩),
          (X.toSSetObjEquiv (op (SimplexCategory.mk n)) τ).continuous.codRestrict _⟩)
    else 0

/-- **The S-restriction is surjective on cochains**: `i*(extend g) = g`. On a simplex `σ` of `sub S`,
`i*(extend g) σ = extend g (simplexIncl σ)`, whose realization lands in `S`, so the extension picks the
`g`-branch and the corestriction of `simplexIncl σ` is `σ` again. -/
theorem cochainPullback_extendCochain {n : ℕ} (g : SingularCochain (sub S) n) :
    cochainPullback (subInclCM S) n (extendCochain S g) = g := by
  funext σ
  rw [cochainPullback_apply, mapSimplex_subInclCM]
  have hsub : Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) (simplexIncl S n σ)) ⊆ S := by
    rw [toSSetObjEquiv_simplexIncl]
    rintro x ⟨t, rfl⟩
    exact (((sub S).toSSetObjEquiv (op (SimplexCategory.mk n)) σ) t).2
  show extendCochain S g (simplexIncl S n σ) = g σ
  rw [extendCochain, dif_pos hsub]
  refine congrArg g ?_
  apply (sub S).toSSetObjEquiv (op (SimplexCategory.mk n)) |>.injective
  rw [Equiv.apply_symm_apply]
  apply ContinuousMap.ext
  intro t
  apply Subtype.ext
  show (X.toSSetObjEquiv (op (SimplexCategory.mk n)) (simplexIncl S n σ)) t
      = ((sub S).toSSetObjEquiv (op (SimplexCategory.mk n)) σ t : ↑X)
  rw [toSSetObjEquiv_simplexIncl]
  rfl

/-! ## §5. Middle exactness of the pair sequence: `im relToAbs = ker i*` -/

private theorem mkSub_eq_zero_iff {n : ℕ} (a : LinearMap.ker (coboundaryₗ (sub S) n)) :
    Cohomology.mk (sub S) n a = 0 ↔ (a : SingularCochain (sub S) n) ∈ coboundaryRange (sub S) n := by
  show Submodule.Quotient.mk a = 0 ↔ _
  rw [Submodule.Quotient.mk_eq_zero]
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply]

/-- A relative cocycle built from an absolute cocycle `f` that already annihilates the subspace
(`hrel : f.1 ∈ relCochains`). -/
private theorem relToAbs_mk_of_relCochain {n : ℕ} (f : LinearMap.ker (coboundaryₗ X n))
    (hrel : (f : SingularCochain X n) ∈ relCochains S n) :
    Cohomology.mk X n f ∈ Set.range (relToAbs (S := S) (m := n)) := by
  have hker : (⟨(f : SingularCochain X n), hrel⟩ : relCochains S n)
      ∈ LinearMap.ker (relCoboundaryₗ S n) := by
    rw [LinearMap.mem_ker]; apply Subtype.ext
    rw [relCoboundaryₗ_coe]; exact LinearMap.mem_ker.mp f.2
  refine ⟨RelativeCohomology.mk S n ⟨⟨(f : SingularCochain X n), hrel⟩, hker⟩, ?_⟩
  rw [relToAbs_mk]
  rfl

/-- **Middle exactness of the cohomology pair sequence**: `im relToAbs = ker i*`. The forward
inclusion is the complex property `restrictToSub_relToAbs`; the reverse inclusion modifies a cocycle
`f` with `i*[f] = 0` by `δ(extend g)` (where `i*f = δg`) to make it annihilate the subspace, using
the extension surjectivity `cochainPullback_extendCochain`. -/
theorem exact_relToAbs_restrictToSub (n : ℕ) :
    Function.Exact (relToAbs (S := S) (m := n)) (restrictToSub S n) := by
  intro y
  constructor
  · intro hy
    obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ y
    rw [show (Submodule.Quotient.mk f : Cohomology X n) = Cohomology.mk X n f from rfl,
      restrictToSub_mk, mkSub_eq_zero_iff] at hy
    have hmem : cochainPullback (subInclCM S) n (f : SingularCochain X n) ∈ coboundaryRange (sub S) n :=
      hy
    cases n with
    | zero =>
        rw [show coboundaryRange (sub S) 0 = (⊥ : Submodule (ZMod 2) _) from rfl,
          Submodule.mem_bot] at hmem
        exact relToAbs_mk_of_relCochain S f ((cochainPullback_subInclCM_eq_zero_iff S 0 _).1 hmem)
    | succ m =>
        obtain ⟨g, hg⟩ := hmem
        have hcpb : cochainPullback (subInclCM S) (m + 1) (coboundary X m (extendCochain S g))
            = cochainPullback (subInclCM S) (m + 1) (f : SingularCochain X (m + 1)) := by
          rw [← coboundary_cochainPullback, cochainPullback_extendCochain]
          exact hg
        have harel : ((f : SingularCochain X (m + 1)) - coboundary X m (extendCochain S g))
            ∈ relCochains S (m + 1) := by
          rw [← cochainPullback_subInclCM_eq_zero_iff, map_sub, hcpb, sub_self]
        have hacoc : coboundaryₗ X (m + 1)
            ((f : SingularCochain X (m + 1)) - coboundary X m (extendCochain S g)) = 0 := by
          rw [map_sub, LinearMap.mem_ker.mp f.2, zero_sub, neg_eq_zero]
          exact coboundary_comp_coboundary X m (extendCochain S g)
        have hpre := relToAbs_mk_of_relCochain S ⟨_, hacoc⟩ harel
        refine Set.mem_of_eq_of_mem ?_ hpre
        refine (Submodule.Quotient.eq _).2 ?_
        rw [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype]
        show (f : SingularCochain X (m + 1))
            - ((f : SingularCochain X (m + 1)) - coboundary X m (extendCochain S g))
            ∈ coboundaryRange X (m + 1)
        rw [show (f : SingularCochain X (m + 1))
              - ((f : SingularCochain X (m + 1)) - coboundary X m (extendCochain S g))
              = coboundary X m (extendCochain S g) by abel]
        exact ⟨extendCochain S g, rfl⟩
  · rintro ⟨z, rfl⟩
    exact restrictToSub_relToAbs S n z

end SKEFTHawking.SingularCohomologyPairRestrict
