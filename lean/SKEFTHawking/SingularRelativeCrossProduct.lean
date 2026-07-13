/-
# The mod-2 relative cross-product with `[I, ∂I]` — the cylinder existence engine

Tool 1 of the cylinder relative-fundamental-class programme. The exact missing map for the
`[W, ∂W] = [M] × [I, ∂I]` existence route is a relative cross-product
`Hₚ(M; ℤ/2) → Hₚ₊₁(M × I, M × ∂I; ℤ/2)`. The `⊗ H₁(I, ∂I)` slot is 1-dimensional, so this is a
single map (the slant with the relative fundamental cycle of `(I, ∂I)`).

**No new chain machinery is needed.** The classical prism operator triangulating `Δᵖ × I` ALREADY
exists in-tree as `SingularPrism.prismOp`, applied to the *identity graph* homotopy
`graphHom : M × I → M × I`, `(x,t) ↦ (x,t)`. For a `p`-cycle `z` the prism chain homotopy gives
`∂(prismOp z) = (·,1)_# z + (·,0)_# z` (the `P∂` term dies since `∂z = 0`), and both endpoint pushes
land in `M × ∂I` — so `prismOp z` is a RELATIVE `(p+1)`-cycle of `(M × I, M × ∂I)`. That relative
cycle IS the cross-product `z × [I, ∂I]`.

This module banks the cycle-level engine, stated GENERICALLY against any subspace
`S ⊆ M × I` containing both endpoint slices `M × {0}` and `M × {1}` (the cylinder consumer supplies
`S := M × {⊥,⊤}` and the two `MapsTo` facts). Kernel-pure (`{propext, Classical.choice, Quot.sound}`);
no `sorry`/`native_decide`/`maxHeartbeats`/axiom.

**Status: written pending build verification** — the wt2 build lane is currently ENFILE-blocked by
concurrent sibling sessions; this file is a faithful port of the verified prism/subspace patterns
(`SingularHomotopyInvariance.mapChain_slice_add_mem_boundaries`,
`SingularRelativeFunctoriality.mapChain_mem_subspaceChains`) and awaits a clean build window.
-/
import Mathlib
import SKEFTHawking.SingularHomotopyInvariance
import SKEFTHawking.SingularRelativeFunctoriality

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularRelativeFunctoriality
open SKEFTHawking.SingularPrism
open SKEFTHawking.SingularHomotopyInvariance (slice endMap_eq_mapChain)
open SKEFTHawking.SingularExcision (single_mem_subspaceChains_of_subordinate)

namespace SKEFTHawking.SingularRelativeCrossProduct

variable {M : TopCat}

/-- **The cylinder target** `M × I` as a `TopCat` (`I = unitInterval = Set.Icc 0 1`). -/
abbrev cyl (M : TopCat) : TopCat := TopCat.of (↑M × unitInterval)

/-- **The identity graph homotopy** `M × I → M × I`, `(x, t) ↦ (x, t)` — the homotopy witness the
prism operator triangulates into `Δᵖ × I ↪ M × I`. -/
def graphHom (M : TopCat) : C(↑M × unitInterval, ↑(cyl M)) :=
  ContinuousMap.id (↑M × unitInterval)

/-- The time-`r` slice of the graph homotopy is the endpoint slice inclusion `x ↦ (x, r)`. -/
@[simp] theorem slice_graphHom (r : unitInterval) (x : ↑M) :
    slice (graphHom M) r x = (x, r) := rfl

/-! ## §1. Every chain is a `univ`-subspace chain -/

/-- **`subspaceChains univ = ⊤`**: every singular chain realises into `univ`, so it lies in the
`univ`-subspace chains. The input that lets endpoint pushes be recognised as `S`-chains. -/
theorem mem_subspaceChains_univ (n : ℕ) (z : SingularChain M n) :
    z ∈ subspaceChains (Set.univ : Set ↑M) n := by
  induction z using Finsupp.induction_linear with
  | zero => exact Submodule.zero_mem _
  | add a b ha hb => exact Submodule.add_mem _ ha hb
  | single σ a =>
      rw [show Finsupp.single σ a = a • Finsupp.single σ (1 : ZMod 2) by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
      exact Submodule.smul_mem _ _ (single_mem_subspaceChains_of_subordinate (Set.subset_univ _))

/-! ## §2. The cross-product chain and its relative-cycle property -/

/-- **The cross-product chain** `z ↦ prismOp graphHom z`, the prism over `M × I` of a chain of `M`.
For a `p`-cycle this is a relative `(p+1)`-cycle of `(M × I, M × ∂I)` (`crossChain_mem_relCycles`). -/
noncomputable def crossChain (p : ℕ) (z : SingularChain M p) : SingularChain (cyl M) (p + 1) :=
  prismOp (graphHom M) p z

/-- **The cross-product of a cycle is a relative cycle** of `(M × I, S)` for any subspace `S`
containing both endpoint slices `M × {1}`, `M × {0}` (`h1`, `h0`). The prism chain homotopy
`∂(prismOp z) + prismOp(∂z) = (·,1)_# z + (·,0)_# z` collapses (since `∂z = 0`) to
`∂(prismOp z) = (·,1)_# z + (·,0)_# z`, and both pushes are `S`-chains — so the relative boundary
of `[prismOp z]` vanishes. This is the honest `[M] × [I, ∂I]` construction, mod-2. -/
theorem crossChain_mem_relCycles {S : Set ↑(cyl M)}
    (h1 : Set.MapsTo (slice (graphHom M) 1) (Set.univ : Set ↑M) S)
    (h0 : Set.MapsTo (slice (graphHom M) 0) (Set.univ : Set ↑M) S)
    (p : ℕ) (z : SingularChain M (p + 1)) (hz : chainBoundary M p z = 0) :
    RelativeChain.mk S (p + 1 + 1) (crossChain (p + 1) z) ∈ relCycles S (p + 1 + 1) := by
  show RelativeChain.mk S (p + 1 + 1) (crossChain (p + 1) z) ∈ LinearMap.ker (relBoundary S (p + 1))
  rw [LinearMap.mem_ker, relBoundary_mk, RelativeChain.mk_eq_zero_iff]
  -- goal: chainBoundary (cyl M) (p+1) (crossChain (p+1) z) ∈ subspaceChains S (p+1)
  have hkey := prism_chainHomotopy (graphHom M) z
  rw [hz, map_zero, add_zero] at hkey
  show chainBoundary (cyl M) (p + 1) (prismOp (graphHom M) (p + 1) z) ∈ subspaceChains S (p + 1)
  rw [hkey, endMap_eq_mapChain, endMap_eq_mapChain]
  exact Submodule.add_mem _
    (mapChain_mem_subspaceChains (slice (graphHom M) 1) h1 (p + 1) z (mem_subspaceChains_univ _ z))
    (mapChain_mem_subspaceChains (slice (graphHom M) 0) h0 (p + 1) z (mem_subspaceChains_univ _ z))

/-- **The cross-product relative cycle** packaged as an element of `relCycles S (p+2)` — the input to
the homology-level cross product `Hₚ₊₁(M) → Hₚ₊₁(M × I, S)`. -/
noncomputable def crossRelCycle {S : Set ↑(cyl M)}
    (h1 : Set.MapsTo (slice (graphHom M) 1) (Set.univ : Set ↑M) S)
    (h0 : Set.MapsTo (slice (graphHom M) 0) (Set.univ : Set ↑M) S)
    (p : ℕ) (z : cycles M (p + 1)) : relCycles S (p + 1 + 1) :=
  ⟨RelativeChain.mk S (p + 1 + 1) (crossChain (p + 1) (z : SingularChain M (p + 1))),
    crossChain_mem_relCycles h1 h0 p z (LinearMap.mem_ker.mp z.2)⟩

end SKEFTHawking.SingularRelativeCrossProduct
