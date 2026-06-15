/-
# Phase 5q.F (w₂-foundation, brick 6a) — relative singular ℤ/2 homology `Hₙ(X, S)`

Toward the **fully-unconditional** `Ω₄^{Pin⁺} ≅ ℤ/16` on the full bordism carrier: the floor is
collapsed by restricting the carrier to genuine Pin⁺ classes, which needs `w₂(TM) ∈ H²(M;ℤ/2)` as a
manifold invariant. The route is the **Wu class** `v₂` (`PoincareDualityWu.lean`, brick 5), defined by
Poincaré duality. Brick 6 turns the Poincaré-duality datum `PoincareDual4Mid` from a hypothesis into a
theorem: the ℤ/2 **fundamental class** of a closed manifold + **Poincaré duality**. Mathlib has neither
(verified 2026-06-15: only the singular chain/homology *functor* `AlgebraicTopology.SingularHomology`,
no relative homology, no excision, no fundamental class, no Poincaré duality).

This first sub-brick (6a) builds the **relative singular ℤ/2 homology** `Hₙ(X, S)` of a subspace
`S ⊆ X` — the foundation for local homology `Hₙ(M, M∖x) ≅ ℤ/2` (→ the fundamental class) and the
Mayer–Vietoris / excision machinery that Poincaré duality runs on. It is built on this phase's genuine
singular ℤ/2 chains (`SingularHomologyMod2`: `SingularChain`, `chainBoundary`, `∂²=0`).

## Construction (faithful, functorial — avoids the `range ⊆ S` simplex plumbing)
The subspace chains `C_•(S) ↪ C_•(X)` are the *image* of the chain map induced by the inclusion
`S ↪ X` (a `TopCat` morphism). The induced map is a genuine chain map (commutes with `∂`) because
`toSSet.map (incl)` is a morphism of simplicial sets — its components commute with the cofaces `δ i`
by naturality. Relative chains are the quotient `C_•(X) / C_•(S)`, relative homology its `ker ∂ / im ∂`.
Kernel-pure (`{propext, Classical.choice, Quot.sound}` only).
-/
import Mathlib
import SKEFTHawking.SingularHomologyMod2

namespace SKEFTHawking.SingularRelativeHomologyMod2

open CategoryTheory Opposite
open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularHomologyMod2

variable {X : TopCat} (S : Set X)

/-! ## §1. The induced chain map `C_•(S) → C_•(X)` of a subspace inclusion -/

/-- The subspace `S ⊆ X` as a `TopCat`. -/
abbrev sub : TopCat := TopCat.of ↥S

/-- The inclusion `S ↪ X` as a `TopCat` morphism. -/
noncomputable def inclMap : sub S ⟶ X := TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

/-- The induced map on singular `n`-simplices: a simplex of `S` post-composed into `X` (the component
of `toSSet.map (incl)` in degree `n`). -/
noncomputable def simplexIncl (n : ℕ) :
    (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk n)) →
      (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n)) :=
  (TopCat.toSSet.map (inclMap S)).app (op (SimplexCategory.mk n))

/-- **Naturality**: the induced simplex map commutes with the `i`-th face — `toSSet.map (incl)` is a
morphism of simplicial sets, so its components commute with the coface `δ i`. -/
theorem simplexIncl_face (n : ℕ)
    (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk (n + 1)))) (i : Fin (n + 2)) :
    simplexIncl S n (face i τ) = face i (simplexIncl S (n + 1) τ) := by
  simpa only [simplexIncl, face] using
    (FunctorToTypes.naturality _ _ (TopCat.toSSet.map (inclMap S)) (SimplexCategory.δ i).op τ).symm

/-- The induced simplex map is **injective**: `toSSet` (a right adjoint) preserves the mono
`incl : S ↪ X`, and monos of simplicial sets are levelwise injective. -/
theorem simplexIncl_injective (n : ℕ) : Function.Injective (simplexIncl S n) := by
  have hmono : Mono (inclMap S) := (TopCat.mono_iff_injective _).2 Subtype.val_injective
  have : Mono (TopCat.toSSet.map (inclMap S)) := inferInstance
  have happ : Mono ((TopCat.toSSet.map (inclMap S)).app (op (SimplexCategory.mk n))) :=
    inferInstance
  exact (CategoryTheory.mono_iff_injective _).1 happ

/-- The induced chain map `C_n(S) → C_n(X)`, `ℤ/2`-linear (`Finsupp.lmapDomain` of `simplexIncl`). -/
noncomputable def chainIncl (n : ℕ) : SingularChain (sub S) n →ₗ[ZMod 2] SingularChain X n :=
  Finsupp.lmapDomain (ZMod 2) (ZMod 2) (simplexIncl S n)

/-- The induced chain map is **injective** (`mapDomain` of the injective simplex map). -/
theorem chainIncl_injective (n : ℕ) : Function.Injective (chainIncl S n) :=
  Finsupp.mapDomain_injective (simplexIncl_injective S n)

theorem chainIncl_single (n : ℕ)
    (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk n))) (a : ZMod 2) :
    chainIncl S n (Finsupp.single τ a) = Finsupp.single (simplexIncl S n τ) a := by
  rw [chainIncl, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

/-- **`chainIncl` is a chain map**: `∂ ∘ chainIncl = chainIncl ∘ ∂`. From `simplexIncl_face` (the
induced simplex map commutes with faces), reduced to a basis simplex. -/
theorem chainIncl_chainBoundary (n : ℕ) (c : SingularChain (sub S) (n + 1)) :
    chainIncl S n (chainBoundary (sub S) n c) = chainBoundary X n (chainIncl S (n + 1) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => rw [map_add, map_add, map_add, map_add, hc, hd]
  | single τ a =>
      rw [chainIncl_single, chainBoundary_single_smul, chainBoundary_single_smul, map_smul]
      congr 1
      rw [boundaryBasis, boundaryBasis, map_sum]
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [chainIncl_single, simplexIncl_face]

/-! ## §2. The subspace chains and the relative chain complex -/

/-- The **subspace chains** `C_n(S) ⊆ C_n(X)`: the image of the inclusion-induced chain map. -/
noncomputable def subspaceChains (n : ℕ) : Submodule (ZMod 2) (SingularChain X n) :=
  LinearMap.range (chainIncl S n)

/-- The boundary maps subspace chains to subspace chains (`chainIncl` is a chain map). -/
theorem chainBoundary_mem_subspaceChains (n : ℕ) (c : SingularChain X (n + 1))
    (hc : c ∈ subspaceChains S (n + 1)) : chainBoundary X n c ∈ subspaceChains S n := by
  obtain ⟨d, rfl⟩ := hc
  exact ⟨chainBoundary (sub S) n d, chainIncl_chainBoundary S n d⟩

/-- **Relative `n`-chains** `C_n(X, S) = C_n(X) / C_n(S)` — a genuine quotient `ℤ/2`-vector space. -/
def RelativeChain (n : ℕ) : Type := SingularChain X n ⧸ subspaceChains S n

noncomputable instance (n : ℕ) : AddCommGroup (RelativeChain S n) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))

noncomputable instance (n : ℕ) : Module (ZMod 2) (RelativeChain S n) :=
  inferInstanceAs (Module (ZMod 2) (_ ⧸ _))

/-- The relative-chain class of an absolute chain. -/
noncomputable def RelativeChain.mk (n : ℕ) (c : SingularChain X n) : RelativeChain S n :=
  Submodule.Quotient.mk c

/-- **The relative boundary** `∂ : C_{n+1}(X,S) → C_n(X,S)`, induced on quotients by the absolute
boundary (well-defined: `∂` preserves the subspace chains). -/
noncomputable def relBoundary (n : ℕ) : RelativeChain S (n + 1) →ₗ[ZMod 2] RelativeChain S n :=
  Submodule.mapQ (subspaceChains S (n + 1)) (subspaceChains S n) (chainBoundary X n)
    (fun c hc => chainBoundary_mem_subspaceChains S n c hc)

theorem relBoundary_mk (n : ℕ) (c : SingularChain X (n + 1)) :
    relBoundary S n (RelativeChain.mk S (n + 1) c) = RelativeChain.mk S n (chainBoundary X n c) :=
  rfl

/-- **`∂² = 0` on relative chains** — induced from the absolute `∂² = 0`. -/
theorem relBoundary_comp_relBoundary (n : ℕ) :
    (relBoundary S n).comp (relBoundary S (n + 1)) = 0 := by
  ext c
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  rw [LinearMap.comp_apply, LinearMap.zero_apply]
  show relBoundary S n (relBoundary S (n + 1) (RelativeChain.mk S (n + 1 + 1) c)) = 0
  rw [relBoundary_mk, relBoundary_mk, chainBoundary_chainBoundary_apply]
  rfl

/-! ## §3. Relative homology `Hₙ(X, S; ℤ/2) = ker ∂ₙ / im ∂ₙ₊₁` -/

/-- The relative **`n`-cycles** (`⊤` in degree 0; `ker ∂ₙ` otherwise). -/
noncomputable def relCycles (n : ℕ) : Submodule (ZMod 2) (RelativeChain S n) :=
  match n with
  | 0 => ⊤
  | m + 1 => LinearMap.ker (relBoundary S m)

/-- The relative **`n`-boundaries** `im ∂ₙ₊₁`. -/
noncomputable def relBoundaries (n : ℕ) : Submodule (ZMod 2) (RelativeChain S n) :=
  LinearMap.range (relBoundary S n)

/-- Relative boundaries are relative cycles (`∂² = 0`). -/
theorem relBoundaries_le_relCycles (n : ℕ) : relBoundaries S n ≤ relCycles S n := by
  cases n with
  | zero => exact le_top
  | succ m =>
    show LinearMap.range (relBoundary S (m + 1)) ≤ LinearMap.ker (relBoundary S m)
    rw [LinearMap.range_le_ker_iff]
    exact relBoundary_comp_relBoundary S m

/-- **Relative singular ℤ/2 homology** `Hₙ(X, S; ℤ/2) = ker ∂ₙ / im ∂ₙ₊₁` — a genuine quotient
`ℤ/2`-vector space (the homology of the pair `(X, S)`). -/
def RelativeHomology (n : ℕ) : Type :=
  (relCycles S n) ⧸ (relBoundaries S n).submoduleOf (relCycles S n)

noncomputable instance (n : ℕ) : AddCommGroup (RelativeHomology S n) :=
  inferInstanceAs (AddCommGroup (_ ⧸ _))

noncomputable instance (n : ℕ) : Module (ZMod 2) (RelativeHomology S n) :=
  inferInstanceAs (Module (ZMod 2) (_ ⧸ _))

/-- The relative homology class of a relative cycle. -/
noncomputable def RelativeHomology.mk (n : ℕ) (z : relCycles S n) : RelativeHomology S n :=
  Submodule.Quotient.mk z

/-- `RelativeChain.mk c = 0` iff `c` is a subspace chain. -/
theorem RelativeChain.mk_eq_zero_iff (n : ℕ) (c : SingularChain X n) :
    RelativeChain.mk S n c = 0 ↔ c ∈ subspaceChains S n :=
  Submodule.Quotient.mk_eq_zero _

/-- A relative homology class `[z]` vanishes iff its representative chain is a relative boundary. -/
theorem RelativeHomology.mk_eq_zero_iff (n : ℕ) (z : relCycles S n) :
    RelativeHomology.mk S n z = 0 ↔ (z : RelativeChain S n) ∈ relBoundaries S n := by
  constructor
  · intro h
    have h2 : z ∈ (relBoundaries S n).submoduleOf (relCycles S n) :=
      (Submodule.Quotient.mk_eq_zero _).1 h
    rwa [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype] at h2
  · intro h
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    rwa [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype]

end SKEFTHawking.SingularRelativeHomologyMod2
