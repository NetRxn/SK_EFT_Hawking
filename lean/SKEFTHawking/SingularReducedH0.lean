import Mathlib
import SKEFTHawking.SingularH0
import SKEFTHawking.SingularFunctoriality
import SKEFTHawking.SingularHomotopyInvariance
import SKEFTHawking.SingularPairLES

/-!
# Reduced `H̃₀` — the bottom-degree pair-LES isomorphisms

The degree-`0` boundary of the local-homology computation. The connecting iso
`connecting_bijective_of_acyclic` and `homProj_bijective_of_acyclic` require the relevant space to be
acyclic in degrees `n` and `n+1`; at the bottom (`n = 0`) `H₀ = 0` is **false** (a nonempty space has
`H₀ ≠ 0`). The fix is the **reduced** statement: replace "`H₀ = 0`" by "the augmentation
`ε̄ : H₀ → ℤ/2` is injective" (reduced `H̃₀ = 0`). The augmentation is natural, so the bottom of the
pair LES `H₁(X, S) → H₀(S) → H₀(X)` becomes, on kernels, `H₁(X, S) ≅ ker(ε̄_S) = H̃₀(S)` when `X` is
reduced-acyclic. This is what makes the bottom suspension `H₁(Sⁿ) ≅ H̃₀(Sⁿ ∖ {v, -v})` work, hence the
base case `H₁(S¹) ≅ H̃₀(S⁰) ≅ ℤ/2` of the sphere/local-homology induction.
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularH0
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularPairLES

namespace SKEFTHawking.SingularReducedH0

/-- **The augmentation is preserved by pushforward**: `ε_Y(f_# c) = ε_X(c)` — each simplex pushes to
exactly one simplex, so the coefficient sum is unchanged. -/
theorem augmentation_mapChain {X Y : TopCat} (f : C(↑X, ↑Y)) (c : SingularChain X 0) :
    augmentation Y (mapChain f 0 c) = augmentation X c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | single σ a => rw [mapChain_single, augmentation_single, augmentation_single]

/-- **The augmentation `ε̄ : H₀ → ℤ/2` is natural**: `ε̄_Y ∘ H₀(f) = ε̄_X`. The reduced homology
`ker ε̄` is therefore a functor, and `ker(H₀(f)) ⊇ ker(ε̄_X)` whenever `ε̄_Y` is injective. -/
theorem augH_naturality {X Y : TopCat} (f : C(↑X, ↑Y)) (x : Homology X 0) :
    augH Y (Homology.map f 0 x) = augH X x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show augH Y (Homology.map f 0 (Homology.mk X 0 z)) = augH X (Homology.mk X 0 z)
  rw [Homology.map_mk, augH_mk, augH_mk, cyclesMap_coe]
  exact augmentation_mapChain f (z : SingularChain X 0)

/-- **Reduced-acyclicity transports backwards across a homology map**: if `H₀(f)` is injective and
`Y` is reduced-acyclic (`ε̄_Y` injective), then `X` is reduced-acyclic. In particular a homotopy
equivalence (or homeomorphism) `X ≃ Y` with `Y` contractible makes `X` reduced-acyclic. -/
theorem augH_injective_of_map {X Y : TopCat} (f : C(↑X, ↑Y))
    (hf : Function.Injective (Homology.map f 0)) (hY : Function.Injective (augH Y)) :
    Function.Injective (augH X) := by
  intro a b hab
  apply hf
  apply hY
  rw [augH_naturality, augH_naturality]
  exact hab

/-! ## §2. The augmentation along the inclusion `S ↪ X` -/

/-- The augmentation is preserved by the inclusion chain map `chainIncl : C₀(S) → C₀(X)`. -/
theorem augmentation_chainIncl {X : TopCat} (S : Set ↑X) (c : SingularChain (sub S) 0) :
    augmentation X (chainIncl S 0 c) = augmentation (sub S) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | single τ a => rw [chainIncl_single, augmentation_single, augmentation_single]

/-- **`ε̄` along the inclusion** `i_* : H₀(S) → H₀(X)`: `ε̄_X ∘ i_* = ε̄_S`. -/
theorem augH_homIncl {X : TopCat} (S : Set ↑X) (y : Homology (sub S) 0) :
    augH X (homIncl S 0 y) = augH (sub S) y := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  show augH X (homIncl S 0 (Homology.mk (sub S) 0 z)) = augH (sub S) (Homology.mk (sub S) 0 z)
  rw [homIncl_mk, augH_mk, augH_mk]
  exact augmentation_chainIncl S (z : SingularChain (sub S) 0)

/-- **The inclusion `i_* : H₀(S) → H₀(X)` is injective when `S` is reduced-acyclic** (`ε̄_S` injective).
Since `ε̄_S = ε̄_X ∘ i_*` factors through `i_*`, injectivity of `ε̄_S` forces `i_*` injective. -/
theorem homIncl_zero_injective_of_augH_injective {X : TopCat} (S : Set ↑X)
    (hS : Function.Injective (augH (sub S))) : Function.Injective (homIncl S 0) := by
  intro a b hab
  apply hS
  rw [← augH_homIncl, ← augH_homIncl, hab]

/-! ## §3. The bottom-degree reduced pair-LES isomorphisms -/

/-- **The bottom projection `j_* : H₁(X) → H₁(X, S)` is an isomorphism when `S` is reduced-acyclic**:
`H₁(S) = 0` (kills `i_*` in degree 1 ⟹ `j_*` injective) and `ε̄_S` injective (⟹ `i_*` injective in
degree 0 ⟹ the connecting map `H₁(X,S) → H₀(S)` is zero ⟹ `j_*` surjective). The bottom-degree
(reduced) analogue of `homProj_bijective_of_acyclic`, where the false hypothesis `H₀(S) = 0` is
replaced by `ε̄_S` injective (reduced `H̃₀(S) = 0`). -/
theorem homProj_one_bijective_of_reduced_acyclic {X : TopCat} (S : Set ↑X)
    (hS1 : ∀ x : Homology (sub S) 1, x = 0) (hSaug : Function.Injective (augH (sub S))) :
    Function.Bijective (homProj S 1) := by
  have hincl1 : homIncl S 1 = 0 := by
    ext y; rw [LinearMap.zero_apply, hS1 y, map_zero]
  have hincl0_inj : Function.Injective (homIncl S 0) :=
    homIncl_zero_injective_of_augH_injective S hSaug
  have hconn0 : connecting S 0 = 0 := by
    apply LinearMap.ext; intro y
    rw [LinearMap.zero_apply]
    apply hincl0_inj
    rw [map_zero, ← LinearMap.mem_ker, (exact_connecting_homIncl S 0).linearMap_ker_eq]
    exact LinearMap.mem_range_self _ y
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, (exact_homIncl_homProj S 1).linearMap_ker_eq, hincl1,
      LinearMap.range_zero]
  · rw [← LinearMap.range_eq_top, ← (exact_homProj_connecting S 0).linearMap_ker_eq, hconn0,
      LinearMap.ker_zero]

/-- **The bottom connecting map `δ : H₁(X, S) → H₀(S)` is injective when `X` is acyclic in degree 1**
(`H₁(X) = 0` ⟹ `j_* : H₁(X) → H₁(X,S)` is zero ⟹ `δ` injective). -/
theorem connecting_zero_injective_of_acyclic {X : TopCat} (S : Set ↑X)
    (hX1 : ∀ x : Homology X 1, x = 0) : Function.Injective (connecting S 0) := by
  have hproj1 : homProj S 1 = 0 := by
    ext x; rw [LinearMap.zero_apply, hX1 x, map_zero]
  rw [← LinearMap.ker_eq_bot, (exact_homProj_connecting S 0).linearMap_ker_eq, hproj1,
    LinearMap.range_zero]

/-- **The bottom connecting map has range exactly reduced `H̃₀(S) = ker ε̄_S`, when `X` is
reduced-acyclic** (`ε̄_X` injective): `range δ = ker(i_*) = ker(ε̄_S)`, since `i_* : H₀(S) → H₀(X)`
and `ε̄_X` is injective so `i_* y = 0 ↔ ε̄_X(i_* y) = ε̄_S y = 0`. -/
theorem connecting_zero_range_of_augH_injective {X : TopCat} (S : Set ↑X)
    (hXaug : Function.Injective (augH X)) :
    LinearMap.range (connecting S 0) = LinearMap.ker (augH (sub S)) := by
  rw [← (exact_connecting_homIncl S 0).linearMap_ker_eq]
  ext y
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  constructor
  · intro h; rw [← augH_homIncl, h, map_zero]
  · intro h; apply hXaug; rw [map_zero, augH_homIncl]; exact h

end SKEFTHawking.SingularReducedH0
