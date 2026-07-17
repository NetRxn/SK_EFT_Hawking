/-
# The relative-INPUT mod-2 cross-product with `[I, ∂I]`, and the iterated 5-cycle `[M]×[I,∂I]³`

Brick B2+B3 of the `hBbord` relative-fundamental-class keystone. This module generalises the
interval cross-product of `SingularRelativeCrossProduct` from an **absolute** cycle input
(`∂z = 0`) to a **relative** input (`∂z ∈ C(A)` for a subspace `A ⊆ X`), then iterates it three
times to build the candidate relative-fundamental class `[M] × [I, ∂I]³` on the clean product
`M × I³`, generic in a topological space `M` with a chosen degree-2 homology class.

**No new chain machinery.** Everything reuses the already-verified prism engine:
* `SingularPrism.prism_chainHomotopy` — `∂(Pc) + P(∂c) = end₁ c + end₀ c` over ℤ/2;
* `SingularRelativeCrossProduct.{crossChain, graphHom, cyl, endMap_mem_subspaceChains}` — the
  absolute interval cross and its endpoint-slice bookkeeping;
* `SingularRelativeHomotopyInvariance.prismOp_mem_subspaceChains` — the prism carries `A`-chains to
  `B`-chains when the homotopy maps `A × I ⊆ B` (instantiated with `H := graphHom X`, the identity,
  `B := A ×ˢ univ`, so the hypothesis is trivial);
* `SingularMayerVietoris.subspaceChains_mono` — monotonicity of subspace chains.

The accumulated relative subspace after one cross is `crossSubspace X A = (univ ×ˢ ∂I) ∪ (A ×ˢ I)`
— the endpoint slices `X × ∂I` glued to the thickened previous subspace `A × I`. Iterating three
times from `A₀ = ∅` yields `M × ∂(I³)` on `M × I³`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.SingularRelativeCrossProduct
import SKEFTHawking.SingularRelativeHomotopyInvariance
import SKEFTHawking.SingularMayerVietoris

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularRelativeFunctoriality
open SKEFTHawking.SingularPrism
open SKEFTHawking.SingularHomotopyInvariance (slice endMap_eq_mapChain)
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularRelativeHomotopyInvariance (prismOp_mem_subspaceChains)
open SKEFTHawking.SingularMayerVietoris (subspaceChains_mono)

namespace SKEFTHawking.SingularRelativeCrossProductRel

variable {M X : TopCat}

/-! ## §1. The accumulated relative subspace `crossSubspace X A = (univ ×ˢ ∂I) ∪ (A ×ˢ I)` -/

/-- **`∂I`** — the boundary of the interval as the two endpoints `{0, 1} ⊆ unitInterval`. -/
def boundaryI : Set unitInterval := {0, 1}

theorem zero_mem_boundaryI : (0 : unitInterval) ∈ boundaryI := Set.mem_insert _ _

theorem one_mem_boundaryI : (1 : unitInterval) ∈ boundaryI := Set.mem_insert_of_mem _ rfl

/-- **The accumulated relative subspace of one cross** `crossSubspace X A ⊆ cyl X = X × I`: the
endpoint slices `X × ∂I` (making both endpoint pushes die) together with the thickened previous
relative subspace `A × I`. Both `crossChain_boundary_mem` inputs live here. -/
def crossSubspace (X : TopCat) (A : Set ↑X) : Set ↑(cyl X) :=
  (Set.univ ×ˢ boundaryI) ∪ (A ×ˢ (Set.univ : Set unitInterval))

/-- `A × I ⊆ crossSubspace X A` — the `P∂` prism term lands here. -/
theorem prod_univ_subset_crossSubspace (A : Set ↑X) :
    A ×ˢ (Set.univ : Set unitInterval) ⊆ crossSubspace X A := Set.subset_union_right

/-- The endpoint slice `x ↦ (x, r)` (for `r ∈ ∂I`) lands in `crossSubspace X A` — the input the
endpoint-slice bookkeeping needs. -/
theorem slice_mem_crossSubspace (A : Set ↑X) (r : unitInterval) (hr : r ∈ boundaryI) :
    Set.MapsTo (slice (graphHom X) r) (Set.univ : Set ↑X) (crossSubspace X A) := by
  intro x _
  rw [slice_graphHom]
  exact Set.mem_union_left _ (Set.mk_mem_prod (Set.mem_univ x) hr)

/-! ## §2. The relative-input cross carries `A`-relative-cycles to `crossSubspace`-relative-cycles -/

/-- **The prism of an `A`-chain is a `crossSubspace X A`-chain.** Instantiates
`prismOp_mem_subspaceChains` with the identity homotopy `graphHom X` and `B := A ×ˢ univ` (the
hypothesis `graphHom X (a, t) = (a, t) ∈ A ×ˢ univ` is trivial), then monotone into the union. -/
theorem crossChain_mem_subspaceChains (A : Set ↑X) (n : ℕ) {c : SingularChain X n}
    (hc : c ∈ subspaceChains A n) :
    crossChain n c ∈ subspaceChains (crossSubspace X A) (n + 1) := by
  have hH : ∀ a ∈ A, ∀ t : unitInterval,
      graphHom X (a, t) ∈ (A ×ˢ (Set.univ : Set unitInterval)) :=
    fun a ha _ => Set.mk_mem_prod ha (Set.mem_univ _)
  exact subspaceChains_mono (prod_univ_subset_crossSubspace A) (n + 1)
    (prismOp_mem_subspaceChains (graphHom X) hH n hc)

/-- **The boundary of the relative-input cross is a `crossSubspace X A`-chain** — the cycle-level
core. From `∂(Pz) = end₁ z + end₀ z − P(∂z)` (mod 2): the endpoint pushes are `crossSubspace`-chains
(`endMap_mem_subspaceChains` + endpoint slices `⊆ crossSubspace`), and `P(∂z)` is one too, because
`∂z ∈ C(A)` (`crossChain_mem_subspaceChains`). Relaxes `crossChain_mem_relCycles` from `∂z = 0`. -/
theorem crossChain_boundary_mem (A : Set ↑X) (p : ℕ) (z : SingularChain X (p + 1))
    (hz : chainBoundary X p z ∈ subspaceChains A p) :
    chainBoundary (cyl X) (p + 1) (crossChain (p + 1) z)
      ∈ subspaceChains (crossSubspace X A) (p + 1) := by
  show chainBoundary (cyl X) (p + 1) (prismOp (graphHom X) (p + 1) z)
      ∈ subspaceChains (crossSubspace X A) (p + 1)
  have hkey := prism_chainHomotopy (graphHom X) z
  have hbdry : chainBoundary (cyl X) (p + 1) (prismOp (graphHom X) (p + 1) z)
      = (endMap (graphHom X) 1 (p + 1) z + endMap (graphHom X) 0 (p + 1) z)
        - prismOp (graphHom X) p (chainBoundary X p z) :=
    eq_sub_of_add_eq hkey
  rw [hbdry]
  refine Submodule.sub_mem _ (Submodule.add_mem _ ?_ ?_) ?_
  · exact endMap_mem_subspaceChains (slice_mem_crossSubspace A 1 one_mem_boundaryI) _ z
  · exact endMap_mem_subspaceChains (slice_mem_crossSubspace A 0 zero_mem_boundaryI) _ z
  · exact crossChain_mem_subspaceChains A p hz

/-- **B2 (cycle level): the relative-input cross of an `A`-relative-cycle is a
`crossSubspace X A`-relative-cycle.** The generalisation of
`SingularRelativeCrossProduct.crossChain_mem_relCycles` from `∂z = 0` to `∂z ∈ C(A)`. -/
theorem crossChain_rel_mem_relCycles (A : Set ↑X) (p : ℕ) (z : SingularChain X (p + 1))
    (hz : chainBoundary X p z ∈ subspaceChains A p) :
    RelativeChain.mk (crossSubspace X A) (p + 1 + 1) (crossChain (p + 1) z)
      ∈ relCycles (crossSubspace X A) (p + 1 + 1) := by
  show RelativeChain.mk (crossSubspace X A) (p + 1 + 1) (crossChain (p + 1) z)
      ∈ LinearMap.ker (relBoundary (crossSubspace X A) (p + 1))
  rw [LinearMap.mem_ker, relBoundary_mk, RelativeChain.mk_eq_zero_iff]
  exact crossChain_boundary_mem A p z hz

/-! ## §3. The relative-input cross chain map and its homology-level descent -/

/-- **The relative-input cross chain map** `C_{p+1}(X, A) → C_{p+2}(X × I, crossSubspace X A)` — the
prism `crossChain = prismOp graphHom` descended over the `A`-quotient (well-defined:
`crossChain_mem_subspaceChains` sends `A`-chains to `crossSubspace`-chains). The relative-input
generalisation of `SingularRelativeCrossProduct.crossChainLM`. -/
noncomputable def crossChainLM_rel (A : Set ↑X) (p : ℕ) :
    RelativeChain A (p + 1) →ₗ[ZMod 2] RelativeChain (crossSubspace X A) (p + 1 + 1) :=
  Submodule.mapQ (subspaceChains A (p + 1)) (subspaceChains (crossSubspace X A) (p + 1 + 1))
    (prismOp (graphHom X) (p + 1))
    (fun _ hc => crossChain_mem_subspaceChains A (p + 1) hc)

theorem crossChainLM_rel_apply (A : Set ↑X) (p : ℕ) (c : SingularChain X (p + 1)) :
    crossChainLM_rel A p (RelativeChain.mk A (p + 1) c)
      = RelativeChain.mk (crossSubspace X A) (p + 1 + 1) (crossChain (p + 1) c) := rfl

/-- The relative-input cross chain map lands in relative cycles on a relative cycle. -/
theorem crossChainLM_rel_mem_relCycles (A : Set ↑X) (p : ℕ) (z : RelativeChain A (p + 1))
    (hz : z ∈ relCycles A (p + 1)) :
    crossChainLM_rel A p z ∈ relCycles (crossSubspace X A) (p + 1 + 1) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  have hzb : chainBoundary X p c ∈ subspaceChains A p := by
    rw [← RelativeChain.mk_eq_zero_iff A p, ← relBoundary_mk A p c]
    exact LinearMap.mem_ker.mp hz
  rw [show (Submodule.Quotient.mk c : RelativeChain A (p + 1)) = RelativeChain.mk A (p + 1) c from
    rfl, crossChainLM_rel_apply]
  exact crossChain_rel_mem_relCycles A p c hzb

/-- The relative-input cross chain map lands in relative boundaries on a relative boundary
(well-definedness on relative homology): the same argument as
`SingularRelativeCrossProduct.crossChainLM_mem_relBoundaries`, with the relative-input lift. -/
theorem crossChainLM_rel_mem_relBoundaries (A : Set ↑X) (p : ℕ) (z : RelativeChain A (p + 1))
    (hz : z ∈ relBoundaries A (p + 1)) :
    crossChainLM_rel A p z ∈ relBoundaries (crossSubspace X A) (p + 1 + 1) := by
  obtain ⟨W, rfl⟩ := hz
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ W
  rw [show (Submodule.Quotient.mk w : RelativeChain A (p + 1 + 1)) = RelativeChain.mk A (p + 1 + 1) w
    from rfl, relBoundary_mk, crossChainLM_rel_apply]
  change RelativeChain.mk (crossSubspace X A) (p + 1 + 1)
      (prismOp (graphHom X) (p + 1) (chainBoundary X (p + 1) w)) ∈ _
  have hkey := prism_chainHomotopy (graphHom X) (n := p + 1) w
  have hmkadd : ∀ a b : SingularChain (cyl X) (p + 1 + 1),
      RelativeChain.mk (crossSubspace X A) (p + 1 + 1) (a + b)
        = RelativeChain.mk (crossSubspace X A) (p + 1 + 1) a
          + RelativeChain.mk (crossSubspace X A) (p + 1 + 1) b :=
    fun a b => map_add (Submodule.mkQ (subspaceChains (crossSubspace X A) (p + 1 + 1))) a b
  have hA : RelativeChain.mk (crossSubspace X A) (p + 1 + 1)
      (chainBoundary (cyl X) (p + 1 + 1) (prismOp (graphHom X) (p + 1 + 1) w))
      ∈ relBoundaries (crossSubspace X A) (p + 1 + 1) :=
    ⟨RelativeChain.mk (crossSubspace X A) (p + 1 + 1 + 1) (prismOp (graphHom X) (p + 1 + 1) w),
      relBoundary_mk (crossSubspace X A) (p + 1 + 1) (prismOp (graphHom X) (p + 1 + 1) w)⟩
  have hD : RelativeChain.mk (crossSubspace X A) (p + 1 + 1)
      (endMap (graphHom X) 1 (p + 1 + 1) w + endMap (graphHom X) 0 (p + 1 + 1) w) = 0 := by
    rw [RelativeChain.mk_eq_zero_iff]
    exact Submodule.add_mem _
      (endMap_mem_subspaceChains (slice_mem_crossSubspace A 1 one_mem_boundaryI) _ w)
      (endMap_mem_subspaceChains (slice_mem_crossSubspace A 0 zero_mem_boundaryI) _ w)
  have hsum : RelativeChain.mk (crossSubspace X A) (p + 1 + 1)
        (chainBoundary (cyl X) (p + 1 + 1) (prismOp (graphHom X) (p + 1 + 1) w))
      + RelativeChain.mk (crossSubspace X A) (p + 1 + 1)
        (prismOp (graphHom X) (p + 1) (chainBoundary X (p + 1) w))
      = 0 := by
    rw [← hmkadd, hkey]; exact hD
  rw [eq_neg_of_add_eq_zero_right hsum]
  exact Submodule.neg_mem _ hA

/-- **B2 (homology level): the relative-input cross** `× [I, ∂I]`
`Hₚ₊₁(X, A; ℤ/2) → Hₚ₊₂(X × I, crossSubspace X A; ℤ/2)`. Well-defined on relative homology by
`crossChainLM_rel_mem_relCycles` (relative cycles ↦ relative cycles) and
`crossChainLM_rel_mem_relBoundaries` (relative boundaries ↦ relative boundaries). The relative-input
generalisation of `SingularRelativeCrossProduct.crossH`; the engine of the iteration in §4. -/
noncomputable def crossH_rel (A : Set ↑X) (p : ℕ) :
    RelativeHomology A (p + 1) →ₗ[ZMod 2] RelativeHomology (crossSubspace X A) (p + 1 + 1) :=
  Submodule.mapQ _ _
    (LinearMap.restrict (crossChainLM_rel A p)
      (fun z hz => crossChainLM_rel_mem_relCycles A p z hz))
    (fun z hz => by
      rw [Submodule.mem_comap, Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype]
      exact crossChainLM_rel_mem_relBoundaries A p (z : RelativeChain A (p + 1))
        (by rwa [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype] at hz))

/-! ## §4. The iterated candidate relative-fundamental 5-cycle `[M] × [I, ∂I]³` on `M × I³` -/

/-- Accumulated subspace `M × ∂I ⊆ M × I` (= `crossSubspace M ∅`). -/
def subI1 (M : TopCat) : Set ↑(cyl M) := crossSubspace M (∅ : Set ↑M)

/-- Accumulated subspace `M × ∂(I²) ⊆ M × I²`. -/
def subI2 (M : TopCat) : Set ↑(cyl (cyl M)) := crossSubspace (cyl M) (subI1 M)

/-- Accumulated subspace `M × ∂(I³) ⊆ M × I³` — the pair subspace of the candidate class. -/
def subI3 (M : TopCat) : Set ↑(cyl (cyl (cyl M))) := crossSubspace (cyl (cyl M)) (subI2 M)

/-- **The concrete iterated 5-cycle chain** `[M] × [I, ∂I]³` — three interval crosses of a 2-cycle
representative, a `SingularChain (M × I³) 5`. The explicit handle the restriction proof (B5) needs. -/
noncomputable def crossIter3Chain (z : cycles M 2) : SingularChain (cyl (cyl (cyl M))) 5 :=
  crossChain 4 (crossChain 3 (crossChain 2 (z : SingularChain M 2)))

/-- **The iterated 5-cycle is a relative cycle of `(M × I³, M × ∂(I³))`.** Three applications of
`crossChain_boundary_mem`, starting from `∂[M] = 0 ∈ C(∅)`. -/
theorem crossIter3_mem_relCycles (z : cycles M 2) :
    RelativeChain.mk (subI3 M) 5 (crossIter3Chain z) ∈ relCycles (subI3 M) 5 := by
  have h0 : chainBoundary M 1 (z : SingularChain M 2) ∈ subspaceChains (∅ : Set ↑M) 1 := by
    rw [show chainBoundary M 1 (z : SingularChain M 2) = 0 from LinearMap.mem_ker.mp z.2]
    exact Submodule.zero_mem _
  have h1 : chainBoundary (cyl M) 2 (crossChain 2 (z : SingularChain M 2))
      ∈ subspaceChains (subI1 M) 2 :=
    crossChain_boundary_mem (∅ : Set ↑M) 1 (z : SingularChain M 2) h0
  have h2 : chainBoundary (cyl (cyl M)) 3 (crossChain 3 (crossChain 2 (z : SingularChain M 2)))
      ∈ subspaceChains (subI2 M) 3 :=
    crossChain_boundary_mem (subI1 M) 2 (crossChain 2 (z : SingularChain M 2)) h1
  have h3 : chainBoundary (cyl (cyl (cyl M))) 4
        (crossChain 4 (crossChain 3 (crossChain 2 (z : SingularChain M 2))))
      ∈ subspaceChains (subI3 M) 4 :=
    crossChain_boundary_mem (subI2 M) 3 (crossChain 3 (crossChain 2 (z : SingularChain M 2))) h2
  show RelativeChain.mk (subI3 M) 5 (crossIter3Chain z)
      ∈ LinearMap.ker (relBoundary (subI3 M) 4)
  rw [LinearMap.mem_ker, relBoundary_mk, RelativeChain.mk_eq_zero_iff]
  exact h3

/-- **The iterated 5-cycle**, packaged as an element of `relCycles (M × ∂(I³)) 5` — the candidate
relative fundamental cycle, cycle representative `crossIter3Chain` exposed. -/
noncomputable def crossIter3 (z : cycles M 2) : relCycles (subI3 M) 5 :=
  ⟨RelativeChain.mk (subI3 M) 5 (crossIter3Chain z), crossIter3_mem_relCycles z⟩

/-- **The candidate relative-fundamental class** `[M] × [I, ∂I]³ ∈ Hₙ(M × I³, M × ∂(I³); ℤ/2)`
(degree `5`), generic in `M` and a chosen degree-2 homology class. -/
noncomputable def crossIter3Class (z : cycles M 2) : RelativeHomology (subI3 M) 5 :=
  RelativeHomology.mk (subI3 M) 5 (crossIter3 z)

/-- **The iterated relative-fundamental map at the homology level** `Hₚ₊₁ → Hₚ₊₅` … concretely
`Homology M 2 → Hₙ(M × I³, M × ∂(I³))`, the honest three-fold `× [I, ∂I]`: one absolute cross
(`crossH`) followed by two relative-input crosses (`crossH_rel`). -/
noncomputable def crossIter3H (M : TopCat) : Homology M 2 →ₗ[ZMod 2] RelativeHomology (subI3 M) 5 :=
  (crossH_rel (subI2 M) 3).comp
    ((crossH_rel (subI1 M) 2).comp
      (crossH (slice_mem_crossSubspace (∅ : Set ↑M) 1 one_mem_boundaryI)
        (slice_mem_crossSubspace (∅ : Set ↑M) 0 zero_mem_boundaryI) 1))

end SKEFTHawking.SingularRelativeCrossProductRel
