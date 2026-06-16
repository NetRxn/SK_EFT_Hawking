import Mathlib
import SKEFTHawking.SingularExcisionPushforward

/-!
# Functoriality of singular ℤ/2 homology

A continuous map `φ : X → Y` post-composes each singular simplex `σ : Δⁿ → X` to `φ ∘ σ : Δⁿ → Y`,
inducing a chain map `mapChain φ : Cₙ(X) → Cₙ(Y)` and hence `Hₙ(X) → Hₙ(Y)`. This is the covariant
functor `Hₙ(·; ℤ/2)` on `TopCat`. Together with the homotopy invariance of `SingularPrism`, it gives:
homotopy-equivalent spaces have isomorphic homology, and contractible spaces are acyclic.

The prism's `endMap H r` is exactly `mapChain` of the time-`r` slice `H(·, r)` (`endMap_eq_mapChain`),
which transports the chain-level homotopy invariance to the functor level.

## §1. The pushforward chain map
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularExcisionPushforward
open SKEFTHawking.SingularCohomologyMod2

namespace SKEFTHawking.SingularFunctoriality

/-- The pushforward of a singular simplex along a continuous map `φ : X → Y`: post-compose the
realization `σ : Δⁿ → X` by `φ` to get `φ ∘ σ : Δⁿ → Y`. -/
noncomputable def mapSimplex {X Y : TopCat} {n : ℕ} (φ : C(↑X, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    (TopCat.toSSet.obj Y).obj (op (SimplexCategory.mk n)) :=
  (Y.toSSetObjEquiv (op (SimplexCategory.mk n))).symm
    (φ.comp (X.toSSetObjEquiv (op (SimplexCategory.mk n)) σ))

/-- **The pushforward chain map** `φ_# : Cₙ(X) → Cₙ(Y)`, the linear extension of `mapSimplex φ`. -/
noncomputable def mapChain {X Y : TopCat} (φ : C(↑X, ↑Y)) (n : ℕ) :
    SingularChain X n →ₗ[ZMod 2] SingularChain Y n :=
  Finsupp.linearCombination (ZMod 2) (fun σ => Finsupp.single (mapSimplex φ σ) 1)

@[simp] theorem mapChain_single {X Y : TopCat} (φ : C(↑X, ↑Y)) (n : ℕ)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) (a : ZMod 2) :
    mapChain φ n (Finsupp.single σ a) = Finsupp.single (mapSimplex φ σ) a := by
  rw [mapChain, Finsupp.linearCombination_single, Finsupp.smul_single, smul_eq_mul, mul_one]

/-- **Pushforward face-naturality**: `face i (mapSimplex φ σ) = mapSimplex φ (face i σ)` — post-
composing by `φ` commutes with the simplicial face. -/
theorem face_mapSimplex {X Y : TopCat} {n : ℕ} (φ : C(↑X, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (n + 1)))) (i : Fin (n + 2)) :
    face i (mapSimplex φ σ) = mapSimplex φ (face i σ) := by
  apply (Y.toSSetObjEquiv (op (SimplexCategory.mk n))).injective
  simp only [mapSimplex, toSSetObjEquiv_face, Equiv.apply_symm_apply]
  rfl

/-- **`mapChain φ` is a chain map**: `∂ ∘ φ_# = φ_# ∘ ∂`. -/
theorem chainBoundary_mapChain {X Y : TopCat} {n : ℕ} (φ : C(↑X, ↑Y))
    (c : SingularChain X (n + 1)) :
    chainBoundary Y n (mapChain φ (n + 1) c) = mapChain φ n (chainBoundary X n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | single σ a =>
      have hsa : Finsupp.single σ a = a • Finsupp.single σ (1 : ZMod 2) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rw [hsa]
      simp only [map_smul]
      congr 1
      rw [mapChain_single, chainBoundary_single, chainBoundary_single]
      simp only [boundaryBasis, map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [mapChain_single, face_mapSimplex]

/-! ## §2. Functoriality -/

/-- The pushforward of a composite is the composite of pushforwards (on simplices). -/
theorem mapSimplex_comp {X Y Z : TopCat} {n : ℕ} (ψ : C(↑Y, ↑Z)) (φ : C(↑X, ↑Y))
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    mapSimplex (ψ.comp φ) σ = mapSimplex ψ (mapSimplex φ σ) := by
  apply (Z.toSSetObjEquiv (op (SimplexCategory.mk n))).injective
  simp only [mapSimplex, Equiv.apply_symm_apply]
  rfl

/-- The pushforward of the identity is the identity (on simplices). -/
theorem mapSimplex_id {X : TopCat} {n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    mapSimplex (ContinuousMap.id ↑X) σ = σ := by
  rw [mapSimplex, ContinuousMap.id_comp, Equiv.symm_apply_apply]

/-- **Functoriality**: `(ψ ∘ φ)_# = ψ_# ∘ φ_#`. -/
theorem mapChain_comp {X Y Z : TopCat} (ψ : C(↑Y, ↑Z)) (φ : C(↑X, ↑Y)) (n : ℕ)
    (c : SingularChain X n) :
    mapChain (ψ.comp φ) n c = mapChain ψ n (mapChain φ n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | single σ a => simp only [mapChain_single, mapSimplex_comp]

/-- **Functoriality**: `(id_X)_# = id`. -/
theorem mapChain_id {X : TopCat} (n : ℕ) (c : SingularChain X n) :
    mapChain (ContinuousMap.id ↑X) n c = c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | single σ a => simp only [mapChain_single, mapSimplex_id]

end SKEFTHawking.SingularFunctoriality
