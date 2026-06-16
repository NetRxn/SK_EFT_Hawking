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

/-! ## §3. The induced map on homology -/

/-- `mapChain φ` preserves cycles (`ker ∂`). -/
theorem mapChain_mem_cycles {X Y : TopCat} (φ : C(↑X, ↑Y)) {n : ℕ} {z : SingularChain X n}
    (hz : z ∈ cycles X n) : mapChain φ n z ∈ cycles Y n := by
  cases n with
  | zero => exact Submodule.mem_top
  | succ m =>
      have hz' : chainBoundary X m z = 0 := hz
      show chainBoundary Y m (mapChain φ (m + 1) z) = 0
      rw [chainBoundary_mapChain, hz', map_zero]

/-- `mapChain φ` preserves boundaries (`im ∂`). -/
theorem mapChain_mem_boundaries {X Y : TopCat} (φ : C(↑X, ↑Y)) {n : ℕ} {w : SingularChain X n}
    (hw : w ∈ boundaries X n) : mapChain φ n w ∈ boundaries Y n := by
  obtain ⟨u, rfl⟩ := hw
  exact ⟨mapChain φ (n + 1) u, chainBoundary_mapChain φ u⟩

/-- The induced map on cycles `Zₙ(X) → Zₙ(Y)`. -/
noncomputable def cyclesMap {X Y : TopCat} (φ : C(↑X, ↑Y)) (n : ℕ) :
    cycles X n →ₗ[ZMod 2] cycles Y n :=
  (mapChain φ n).restrict (fun _ hz => mapChain_mem_cycles φ hz)

@[simp] theorem cyclesMap_coe {X Y : TopCat} (φ : C(↑X, ↑Y)) (n : ℕ) (z : cycles X n) :
    (cyclesMap φ n z : SingularChain Y n) = mapChain φ n (z : SingularChain X n) := rfl

/-- **The induced map on homology** `Hₙ(φ) : Hₙ(X; ℤ/2) → Hₙ(Y; ℤ/2)`. -/
noncomputable def Homology.map {X Y : TopCat} (φ : C(↑X, ↑Y)) (n : ℕ) :
    Homology X n →ₗ[ZMod 2] Homology Y n :=
  Submodule.mapQ _ _ (cyclesMap φ n) (by
    rintro ⟨z, hz⟩ hzb
    rw [Submodule.mem_comap]
    exact mapChain_mem_boundaries φ hzb)

@[simp] theorem Homology.map_mk {X Y : TopCat} (φ : C(↑X, ↑Y)) (n : ℕ) (z : cycles X n) :
    Homology.map φ n (Homology.mk X n z) = Homology.mk Y n (cyclesMap φ n z) :=
  Submodule.mapQ_apply _ _ _ _

/-- **Homology functoriality**: `Hₙ(ψ ∘ φ) = Hₙ(ψ) ∘ Hₙ(φ)`. -/
theorem Homology.map_comp {X Y Z : TopCat} (ψ : C(↑Y, ↑Z)) (φ : C(↑X, ↑Y)) (n : ℕ) :
    Homology.map (ψ.comp φ) n = (Homology.map ψ n).comp (Homology.map φ n) := by
  ext x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show Homology.map (ψ.comp φ) n (Homology.mk X n z)
    = Homology.map ψ n (Homology.map φ n (Homology.mk X n z))
  simp only [Homology.map_mk]
  exact congrArg (Homology.mk Z n) (Subtype.ext (mapChain_comp ψ φ n z))

end SKEFTHawking.SingularFunctoriality
