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

/-! ## §3. The homology-level cross product `Hₚ₊₁(M) → Hₚ₊₂(M×I, S)`

The cycle-level engine descends to homology: the cross of a *boundary* `∂w` is the relative
boundary of `prismOp w` — from the prism chain homotopy `∂(Pw) + P(∂w) = end₁ w + end₀ w`, with both
endpoint pushes killed in the `C(M×I, S)` quotient. This is the map `× [I, ∂I]` the cylinder route
`[W, ∂W] = [M] × [I, ∂I]` uses. -/

/-- Both endpoint pushes of any chain are `S`-subspace chains, when `S` contains the endpoint slice
(`hr`). The relative-quotient input: endpoint boundary terms die in `C(M × I, S)`. -/
theorem endMap_mem_subspaceChains {S : Set ↑(cyl M)} {r : unitInterval}
    (hr : Set.MapsTo (slice (graphHom M) r) (Set.univ : Set ↑M) S) (n : ℕ)
    (w : SingularChain M n) :
    endMap (graphHom M) r n w ∈ subspaceChains S n := by
  rw [endMap_eq_mapChain]
  exact mapChain_mem_subspaceChains (slice (graphHom M) r) hr n w (mem_subspaceChains_univ n w)

/-- **The cross-product relative chain map** `C_{p+1}(M) → C_{p+2}(M × I, S)`, the prism chain
post-composed with the relative quotient. -/
noncomputable def crossChainLM {S : Set ↑(cyl M)} (p : ℕ) :
    SingularChain M (p + 1) →ₗ[ZMod 2] RelativeChain S (p + 1 + 1) :=
  (Submodule.mkQ (subspaceChains S (p + 1 + 1))).comp (prismOp (graphHom M) (p + 1))

theorem crossChainLM_apply {S : Set ↑(cyl M)} (p : ℕ) (z : SingularChain M (p + 1)) :
    crossChainLM (S := S) p z = RelativeChain.mk S (p + 1 + 1) (crossChain (p + 1) z) := rfl

/-- The cross-product chain map lands in relative cycles on a cycle. -/
theorem crossChainLM_mem_relCycles {S : Set ↑(cyl M)}
    (h1 : Set.MapsTo (slice (graphHom M) 1) (Set.univ : Set ↑M) S)
    (h0 : Set.MapsTo (slice (graphHom M) 0) (Set.univ : Set ↑M) S)
    (p : ℕ) (z : SingularChain M (p + 1)) (hz : z ∈ cycles M (p + 1)) :
    crossChainLM (S := S) p z ∈ relCycles S (p + 1 + 1) := by
  rw [crossChainLM_apply]
  exact crossChain_mem_relCycles h1 h0 p z (LinearMap.mem_ker.mp hz)

/-- The cross-product chain map lands in relative boundaries on a boundary (well-definedness on
homology): `∂w × [I, ∂I]` is the relative boundary of `prismOp w`. -/
theorem crossChainLM_mem_relBoundaries {S : Set ↑(cyl M)}
    (h1 : Set.MapsTo (slice (graphHom M) 1) (Set.univ : Set ↑M) S)
    (h0 : Set.MapsTo (slice (graphHom M) 0) (Set.univ : Set ↑M) S)
    (p : ℕ) (z : SingularChain M (p + 1)) (hz : z ∈ boundaries M (p + 1)) :
    crossChainLM (S := S) p z ∈ relBoundaries S (p + 1 + 1) := by
  obtain ⟨w, rfl⟩ := hz
  rw [crossChainLM_apply]
  change RelativeChain.mk S (p + 1 + 1)
      (prismOp (graphHom M) (p + 1) (chainBoundary M (p + 1) w)) ∈ _
  have hkey := prism_chainHomotopy (graphHom M) (n := p + 1) w
  have hmkadd : ∀ a b : SingularChain (cyl M) (p + 1 + 1),
      RelativeChain.mk S (p + 1 + 1) (a + b)
        = RelativeChain.mk S (p + 1 + 1) a + RelativeChain.mk S (p + 1 + 1) b :=
    fun a b => map_add (Submodule.mkQ (subspaceChains S (p + 1 + 1))) a b
  have hA : RelativeChain.mk S (p + 1 + 1)
      (chainBoundary (cyl M) (p + 1 + 1) (prismOp (graphHom M) (p + 1 + 1) w))
      ∈ relBoundaries S (p + 1 + 1) :=
    ⟨RelativeChain.mk S (p + 1 + 1 + 1) (prismOp (graphHom M) (p + 1 + 1) w),
      relBoundary_mk S (p + 1 + 1) (prismOp (graphHom M) (p + 1 + 1) w)⟩
  have hD : RelativeChain.mk S (p + 1 + 1)
      (endMap (graphHom M) 1 (p + 1 + 1) w + endMap (graphHom M) 0 (p + 1 + 1) w) = 0 := by
    rw [RelativeChain.mk_eq_zero_iff]
    exact Submodule.add_mem _ (endMap_mem_subspaceChains h1 _ w) (endMap_mem_subspaceChains h0 _ w)
  have hsum : RelativeChain.mk S (p + 1 + 1)
        (chainBoundary (cyl M) (p + 1 + 1) (prismOp (graphHom M) (p + 1 + 1) w))
      + RelativeChain.mk S (p + 1 + 1) (prismOp (graphHom M) (p + 1) (chainBoundary M (p + 1) w))
      = 0 := by
    rw [← hmkadd, hkey]; exact hD
  rw [eq_neg_of_add_eq_zero_right hsum]
  exact Submodule.neg_mem _ hA

/-- **The homology-level cross product** `× [I, ∂I] : Hₚ₊₁(M) → Hₚ₊₂(M × I, S)`, `[z] ↦ [z × [I,∂I]]`
(`[prismOp graphHom z]` in `Hₚ₊₂(M × I, S)`). Well-defined on homology by `crossChainLM_mem_relCycles`
(cycles ↦ relative cycles) and `crossChainLM_mem_relBoundaries` (boundaries ↦ relative boundaries).
This is the honest `[W, ∂W] = [M] × [I, ∂I]` engine at the homology level, mod-2. -/
noncomputable def crossH {S : Set ↑(cyl M)}
    (h1 : Set.MapsTo (slice (graphHom M) 1) (Set.univ : Set ↑M) S)
    (h0 : Set.MapsTo (slice (graphHom M) 0) (Set.univ : Set ↑M) S)
    (p : ℕ) : Homology M (p + 1) →ₗ[ZMod 2] RelativeHomology S (p + 1 + 1) :=
  Submodule.mapQ _ _
    (LinearMap.restrict (crossChainLM (S := S) p)
      (fun z hz => crossChainLM_mem_relCycles h1 h0 p z hz))
    (fun z hz => by
      rw [Submodule.mem_comap, Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype]
      exact crossChainLM_mem_relBoundaries h1 h0 p (z : SingularChain M (p + 1))
        (by rwa [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype] at hz))

/-- **`crossH` on a cycle class**: `× [I, ∂I]` sends the class of a cycle `z` to the relative class of
`crossRelCycle z` — the concrete `[z] × [I, ∂I]` representative. -/
theorem crossH_mk {S : Set ↑(cyl M)}
    (h1 : Set.MapsTo (slice (graphHom M) 1) (Set.univ : Set ↑M) S)
    (h0 : Set.MapsTo (slice (graphHom M) 0) (Set.univ : Set ↑M) S)
    (p : ℕ) (z : cycles M (p + 1)) :
    crossH h1 h0 p (Homology.mk M (p + 1) z)
      = RelativeHomology.mk S (p + 1 + 1) (crossRelCycle h1 h0 p z) := rfl

end SKEFTHawking.SingularRelativeCrossProduct
