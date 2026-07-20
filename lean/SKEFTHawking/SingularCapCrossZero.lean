/-
# The degree-0-source interval cross `× [I, ∂I]` and the iterated 3-cycle `[·] × [I,∂I]³`

Brick N1 of the `hBbord` → P23-nondeg → `hcompat` keystone (Phase 5q.H). The existing interval-cross
engine (`SingularRelativeCrossProduct.crossH`, `SingularRelativeCrossProductRel.crossH_rel`) is
`(p+1)`-typed — its source degree is `≥ 1`. This module builds the missing **degree-0 corner**: the
cross of a `0`-chain (every `0`-chain is a cycle, `cycles X 0 = ⊤`, so no boundary hypothesis is
needed), and the three-fold iterate

  `crossIter3ZeroH : Homology M 0 →ₗ RelativeHomology (subI3 M) 3`

the degree-0 analogue of `SingularRelativeCrossProductRel.crossIter3H`. This is the target-side of the
final application `H²(M) ⌢ H₂(M) → H₀(M)` crossed up to the relative fundamental degree.

**No new chain machinery.** Everything mirrors the `≥ 1` engine one degree down, with the degree-0
prism identity `SingularPrism.prism_chainHomotopy_zero` (`∂(P z) = end₁ z + end₀ z`, no `P∂` term) in
place of the general `prism_chainHomotopy`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`.
-/
import Mathlib
import SKEFTHawking.SingularRelativeCrossProduct
import SKEFTHawking.SingularRelativeCrossProductRel

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularRelativeFunctoriality
open SKEFTHawking.SingularPrism
open SKEFTHawking.SingularHomotopyInvariance (slice endMap_eq_mapChain)
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularRelativeCrossProductRel

namespace SKEFTHawking.SingularCapCrossZero

variable {X : TopCat}

/-! ## §1. The degree-0 cross chain map `C₀(X) → C₁(X × I, S)` and its relative-cycle property -/

/-- **The degree-0 cross chain map** `C₀(X) → C₁(X × I, S)`, the prism `crossChain 0 = prismOp graphHom 0`
post-composed with the relative quotient. The degree-0 analogue of
`SingularRelativeCrossProduct.crossChainLM`. -/
noncomputable def crossChainZeroLM {S : Set ↑(cyl X)} :
    SingularChain X 0 →ₗ[ZMod 2] RelativeChain S 1 :=
  (Submodule.mkQ (subspaceChains S 1)).comp (prismOp (graphHom X) 0)

theorem crossChainZeroLM_apply {S : Set ↑(cyl X)} (z : SingularChain X 0) :
    crossChainZeroLM (S := S) z = RelativeChain.mk S 1 (crossChain 0 z) := rfl

/-- **The degree-0 cross of a `0`-chain is a relative `1`-cycle** of `(X × I, S)` for any subspace `S`
containing both endpoint slices `X × {0}`, `X × {1}`. `∂(prismOp z) = end₁ z + end₀ z` (degree-0 prism
homotopy, no `P∂` term), and both endpoint pushes are `S`-chains. No cycle hypothesis on `z` is needed —
every `0`-chain is a cycle. -/
theorem crossChainZeroLM_mem_relCycles {S : Set ↑(cyl X)}
    (h1 : Set.MapsTo (slice (graphHom X) 1) (Set.univ : Set ↑X) S)
    (h0 : Set.MapsTo (slice (graphHom X) 0) (Set.univ : Set ↑X) S)
    (z : SingularChain X 0) :
    crossChainZeroLM (S := S) z ∈ relCycles S 1 := by
  rw [crossChainZeroLM_apply]
  show RelativeChain.mk S 1 (crossChain 0 z) ∈ LinearMap.ker (relBoundary S 0)
  rw [LinearMap.mem_ker, relBoundary_mk, RelativeChain.mk_eq_zero_iff]
  show chainBoundary (cyl X) 0 (prismOp (graphHom X) 0 z) ∈ subspaceChains S 0
  rw [prism_chainHomotopy_zero, endMap_eq_mapChain, endMap_eq_mapChain]
  exact Submodule.add_mem _
    (mapChain_mem_subspaceChains (slice (graphHom X) 1) h1 0 z (mem_subspaceChains_univ _ z))
    (mapChain_mem_subspaceChains (slice (graphHom X) 0) h0 0 z (mem_subspaceChains_univ _ z))

/-- The degree-0 cross chain map lands in relative boundaries on a boundary (well-definedness on
homology): `∂w × [I, ∂I]` is the relative boundary of `prismOp w`. Mirrors
`SingularRelativeCrossProduct.crossChainLM_mem_relBoundaries` one degree down. -/
theorem crossChainZeroLM_mem_relBoundaries {S : Set ↑(cyl X)}
    (h1 : Set.MapsTo (slice (graphHom X) 1) (Set.univ : Set ↑X) S)
    (h0 : Set.MapsTo (slice (graphHom X) 0) (Set.univ : Set ↑X) S)
    (z : SingularChain X 0) (hz : z ∈ boundaries X 0) :
    crossChainZeroLM (S := S) z ∈ relBoundaries S 1 := by
  obtain ⟨w, rfl⟩ := hz
  rw [crossChainZeroLM_apply]
  change RelativeChain.mk S 1 (prismOp (graphHom X) 0 (chainBoundary X 0 w)) ∈ _
  have hkey := prism_chainHomotopy (graphHom X) (n := 0) w
  have hmkadd : ∀ a b : SingularChain (cyl X) 1,
      RelativeChain.mk S 1 (a + b) = RelativeChain.mk S 1 a + RelativeChain.mk S 1 b :=
    fun a b => map_add (Submodule.mkQ (subspaceChains S 1)) a b
  have hA : RelativeChain.mk S 1 (chainBoundary (cyl X) 1 (prismOp (graphHom X) 1 w))
      ∈ relBoundaries S 1 :=
    ⟨RelativeChain.mk S 2 (prismOp (graphHom X) 1 w),
      relBoundary_mk S 1 (prismOp (graphHom X) 1 w)⟩
  have hD : RelativeChain.mk S 1 (endMap (graphHom X) 1 1 w + endMap (graphHom X) 0 1 w) = 0 := by
    rw [RelativeChain.mk_eq_zero_iff]
    exact Submodule.add_mem _ (endMap_mem_subspaceChains h1 _ w) (endMap_mem_subspaceChains h0 _ w)
  have hsum : RelativeChain.mk S 1 (chainBoundary (cyl X) 1 (prismOp (graphHom X) 1 w))
      + RelativeChain.mk S 1 (prismOp (graphHom X) 0 (chainBoundary X 0 w)) = 0 := by
    rw [← hmkadd, hkey]; exact hD
  rw [eq_neg_of_add_eq_zero_right hsum]
  exact Submodule.neg_mem _ hA

/-! ## §2. The degree-0 homology-level cross `Hₙ(X, ∅) = Homology X 0 → Hₙ₊₁(X × I, S)` -/

/-- **The degree-0 homology-level cross** `× [I, ∂I] : Homology X 0 →ₗ RelativeHomology S 1`,
`[z] ↦ [z × [I, ∂I]]`. Well-defined by `crossChainZeroLM_mem_relCycles` (chains ↦ relative cycles;
`cycles X 0 = ⊤`) and `crossChainZeroLM_mem_relBoundaries` (boundaries ↦ relative boundaries). The
degree-0 corner of the honest `[·] × [I, ∂I]` engine, mod-2. -/
noncomputable def crossHZero {S : Set ↑(cyl X)}
    (h1 : Set.MapsTo (slice (graphHom X) 1) (Set.univ : Set ↑X) S)
    (h0 : Set.MapsTo (slice (graphHom X) 0) (Set.univ : Set ↑X) S) :
    Homology X 0 →ₗ[ZMod 2] RelativeHomology S 1 :=
  Submodule.mapQ _ _
    (LinearMap.restrict (crossChainZeroLM (S := S))
      (fun z _ => crossChainZeroLM_mem_relCycles h1 h0 z))
    (fun z hz => by
      rw [Submodule.mem_comap, Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype]
      exact crossChainZeroLM_mem_relBoundaries h1 h0 (z : SingularChain X 0)
        (by rwa [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype] at hz))

/-- `crossHZero` on a homology class: unwinds to the relative class of the degree-0 cross chain. -/
theorem crossHZero_mk {S : Set ↑(cyl X)}
    (h1 : Set.MapsTo (slice (graphHom X) 1) (Set.univ : Set ↑X) S)
    (h0 : Set.MapsTo (slice (graphHom X) 0) (Set.univ : Set ↑X) S)
    (z : cycles X 0) :
    crossHZero h1 h0 (Homology.mk X 0 z)
      = RelativeHomology.mk S 1
          ⟨crossChainZeroLM (S := S) (z : SingularChain X 0),
            crossChainZeroLM_mem_relCycles h1 h0 (z : SingularChain X 0)⟩ :=
  rfl

/-! ## §3. The iterated degree-0 cross `[·] × [I, ∂I]³ : Homology M 0 → RelativeHomology (subI3 M) 3` -/

/-- **The iterated degree-0 cross** `Homology M 0 →ₗ RelativeHomology (subI3 M) 3` — one degree-0
absolute cross (`crossHZero`) followed by two relative-input crosses (`crossH_rel`), the degree-0
analogue of `SingularRelativeCrossProductRel.crossIter3H`. The accumulated subspaces match `subI2`/`subI3`
definitionally (they are the iterates of `crossSubspace`). -/
noncomputable def crossIter3ZeroH (M : TopCat) :
    Homology M 0 →ₗ[ZMod 2] RelativeHomology (subI3 M) 3 :=
  (crossH_rel (subI2 M) 1).comp
    ((crossH_rel (subI1 M) 0).comp
      (crossHZero (slice_mem_crossSubspace (∅ : Set ↑M) 1 one_mem_boundaryI)
        (slice_mem_crossSubspace (∅ : Set ↑M) 0 zero_mem_boundaryI)))

end SKEFTHawking.SingularCapCrossZero
