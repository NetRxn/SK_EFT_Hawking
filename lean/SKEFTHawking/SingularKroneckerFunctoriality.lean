import Mathlib
import SKEFTHawking.SingularFunctoriality

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4-R1a) — Kronecker naturality under pushforward

The chain-level naturality of the Kronecker pairing under a continuous map `φ : X → Y`:
`⟨f, φ_# z⟩_Y = ⟨φ^* f, z⟩_X`, where `φ_# = mapChain` is the singular pushforward and `φ^* = pullbackCochainMap`
the cochain precomposition `(φ^* f) σ = f (mapSimplex φ σ)`. Plus the cocycle-preservation
`δ(φ^* f) = φ^* (δf)` (`coboundary` commutes with the cochain pullback, dual to `chainBoundary_mapChain`).

These are the foundation of the **seam-dual naturality** (R1) needed to pair the connecting square's two
legs against a single class: both `seamI` and `seamHomologyEquiv` are `Homology.map` of a homeomorphism
(`subSeamEquiv`, `seamHomologyEquiv`), so transporting a cohomology class through them is exactly this
pullback.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularFunctoriality

namespace SKEFTHawking.SingularKroneckerFunctoriality

variable {X Y : TopCat}

/-- **Cochain pullback** `φ^* : Cⁿ(Y) → Cⁿ(X)`, `(φ^* f) σ = f (mapSimplex φ σ)` — precomposition of a
cochain with the simplex pushforward, dual to `mapChain`. -/
noncomputable def pullbackCochainMap (φ : C(↑X, ↑Y)) (n : ℕ) (f : SingularCochain Y n) :
    SingularCochain X n :=
  fun σ => f (mapSimplex φ σ)

@[simp] theorem pullbackCochainMap_apply (φ : C(↑X, ↑Y)) (n : ℕ) (f : SingularCochain Y n)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    pullbackCochainMap φ n f σ = f (mapSimplex φ σ) := rfl

/-- **Contravariant functoriality**: `(ψ ∘ φ)^* = φ^* ∘ ψ^*` — the cochain pullback reverses
composition (dual to `mapChain_comp`). Used to compose the two seam pullbacks into one. -/
theorem pullbackCochainMap_comp {X Y Z : TopCat} (ψ : C(↑Y, ↑Z)) (φ : C(↑X, ↑Y)) (n : ℕ)
    (f : SingularCochain Z n) :
    pullbackCochainMap (ψ.comp φ) n f = pullbackCochainMap φ n (pullbackCochainMap ψ n f) := by
  funext σ
  rw [pullbackCochainMap_apply, pullbackCochainMap_apply, pullbackCochainMap_apply, mapSimplex_comp]

/-- The pullback along the identity is the identity. -/
theorem pullbackCochainMap_id {X : TopCat} (n : ℕ) (f : SingularCochain X n) :
    pullbackCochainMap (ContinuousMap.id ↑X) n f = f := by
  funext σ; rw [pullbackCochainMap_apply, mapSimplex_id]

/-- **Kronecker naturality (chain level)**: `⟨f, φ_# z⟩ = ⟨φ^* f, z⟩`. -/
theorem kronecker_mapChain (φ : C(↑X, ↑Y)) (n : ℕ) (f : SingularCochain Y n)
    (z : SingularChain X n) :
    kronecker f (mapChain φ n z) = kronecker (pullbackCochainMap φ n f) z := by
  induction z using Finsupp.induction_linear with
  | zero => rw [map_zero, kronecker_apply, kronecker_apply, Finsupp.sum_zero_index,
      Finsupp.sum_zero_index]
  | add c d hc hd => rw [map_add, kronecker_add_right, hc, hd, ← kronecker_add_right]
  | single σ s => rw [mapChain_single, kronecker_single, kronecker_single, pullbackCochainMap_apply]

/-- **The cochain pullback commutes with the coboundary**: `δ(φ^* f) = φ^* (δf)` — dual to
`chainBoundary_mapChain`. (`(δ φ^* f) σ = ∑ᵢ f(mapSimplex φ (face i σ)) = ∑ᵢ f(face i (mapSimplex φ σ))
= (φ^* δf) σ`, using `face_mapSimplex`.) -/
theorem coboundary_pullbackCochainMap (φ : C(↑X, ↑Y)) (n : ℕ) (f : SingularCochain Y n) :
    coboundary X n (pullbackCochainMap φ n f) = pullbackCochainMap φ (n + 1) (coboundary Y n f) := by
  funext σ
  rw [coboundary_apply, pullbackCochainMap_apply, coboundary_apply]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rw [pullbackCochainMap_apply, face_mapSimplex]

/-- **The cochain pullback preserves cocycles**: `φ^*` of a cocycle is a cocycle (`δ(φ^* a) = φ^*(δa)
= φ^* 0 = 0`). -/
theorem pullbackCochainMap_mem_ker (φ : C(↑X, ↑Y)) (n : ℕ) (a : LinearMap.ker (coboundaryₗ Y n)) :
    pullbackCochainMap φ n a.1 ∈ LinearMap.ker (coboundaryₗ X n) := by
  rw [LinearMap.mem_ker]
  have ha : coboundary Y n a.1 = 0 := by have h := a.2; rwa [LinearMap.mem_ker] at h
  show coboundary X n (pullbackCochainMap φ n a.1) = 0
  rw [coboundary_pullbackCochainMap, ha]
  rfl

/-- **Kronecker naturality (homology level)**: `⟨a, Hₙ(φ) c⟩_Y = ⟨φ^* a, c⟩_X`, the descent of
`kronecker_mapChain` to homology/cohomology classes. The seam-dual transport: `seamI` and
`seamHomologyEquiv` are `Homology.map` of a homeomorphism, so a cohomology class transported through them
pairs as the cochain pullback. -/
theorem kroneckerH_Homology_map (φ : C(↑X, ↑Y)) (n : ℕ)
    (a : LinearMap.ker (coboundaryₗ Y n)) (z : cycles X n) :
    kroneckerH (X := Y) n (Submodule.Quotient.mk a) (Homology.map φ n (Homology.mk X n z))
      = kroneckerH (X := X) n
          (Submodule.Quotient.mk ⟨pullbackCochainMap φ n a.1, pullbackCochainMap_mem_ker φ n a⟩)
          (Homology.mk X n z) := by
  rw [Homology.map_mk]
  simp only [Homology.mk]
  rw [kroneckerH_mk_mk, kroneckerH_mk_mk, cyclesMap_coe, kronecker_mapChain]

end SKEFTHawking.SingularKroneckerFunctoriality
