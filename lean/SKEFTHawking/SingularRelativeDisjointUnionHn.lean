import Mathlib
import SKEFTHawking.SingularExcisionIso
import SKEFTHawking.SingularDisjointUnionHn

/-!
# Phase 5q.H — THE RELATIVE CLOPEN-SPLIT ENGINE (`Hₙ(X, S) ≅ Hₙ(U, S∩U) × Hₙ(Uᶜ, S∩Uᶜ)`)

The **relative analogue** of `SingularDisjointUnionHn.splitHnEquiv`: for a clopen decomposition
`X = U ⊔ Uᶜ` of the ambient `X : TopCat` and an arbitrary subspace `S : Set ↑X`, relative singular
`ℤ/2`-homology splits over the two clopen pieces,
`RelativeHomology S n ≅ RelativeHomology (restr S U) n × RelativeHomology (restr S Uᶜ) n`,
where `restr S U = Subtype.val ⁻¹' S : Set ↑(sub U)` is `S` pulled back to the clopen piece `↥U`.

## The mechanism (the absolute engine's pattern, quotiented compatibly)

A singular simplex has connected image, so it lands wholly in `U` or in `Uᶜ`; hence every absolute
chain splits `Cₖ(X) = Cₖ(U) ⊔ Cₖ(Uᶜ)` at every degree (`subspaceChains_sup_compl_eq_top`,
`subspaceChains_inf_compl_eq_bot`). The **new** relative ingredient is that this split is compatible
with the subspace-chain filtration `C•(S)`: the reflection `chainIncl_mem_subspaceChains_iff` plus the
disjoint-support separation (`chainIncl_mem_subspaceChains_of_add`) show the `U`-part of any
`S`-subspace chain is again an `S`-subspace chain, so the two clopen inclusions
`relChainIncl S U` / `relChainIncl S Uᶜ` (`SingularExcisionIso`) assemble to a relative-chain
isomorphism, which — being a relative chain map (`relBoundary_relChainIncl`) — descends to relative
homology in every degree.

* `chainIncl_mem_subspaceChains_of_add` — the disjoint-support separation: if a `U`-chain plus a
  `Uᶜ`-chain is an `S`-subspace chain, each summand is (their supports are disjoint, so the sum's
  support contains each — `range_of_mem_subspaceChains`).
* `relChainIncl_sum_eq_zero_split` — the relative injectivity core (`chainIncl_mem_subspaceChains_iff`
  ∘ the separation).
* `relCycles_split` / `relSplitHn_surjective` / `relBoundaries_split` / `relSplitHn_injective` —
  the surjectivity (chain split) + injectivity pattern of `SingularDisjointUnionHn`, at the pair level.
* `relSplitHn` / `relSplitHnEquiv` — the additivity map `(a, b) ↦ excisionMap(a) + excisionMap(b)`
  and its bijectivity.

This is the in-tree tool the disconnected `cylData` discharge (Phase 5q.H) needs: it peels the
per-component cross-class over the clopen decomposition of `cylW M` **without** a homeomorphism
transport (the standing wall), summing per-component connected classes and killing the off-component
classes by the engine's projection.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no
`native_decide`, no `maxHeartbeats`.
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularExcision
open SKEFTHawking.SingularDisjointUnion
open SKEFTHawking.SingularExcisionIso

namespace SKEFTHawking.SingularRelativeDisjointUnionHn

variable {X : TopCat}

/-- Over a `ℤ/2`-module, `a + b = 0` forces `a = b` (every element is its own negative). -/
private theorem eq_of_add_eq_zero_two {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {a b : M}
    (h : a + b = 0) : a = b := by
  rw [← neg_eq_of_add_eq_zero_left h]; exact neg_eq_of_add_eq_zero_left (ZModModule.add_self b)

/-! ## §1. The disjoint-support separation of an `S`-subspace chain. -/

/-- **The `U`/`Uᶜ`-simplex ranges are disjoint**: a simplex that is `U`-valued (in the range of
`simplexIncl U`) is not `Uᶜ`-valued. Its image is nonempty (`stdSimplex` is nonempty), so cannot lie
in both `U` and `Uᶜ`. -/
theorem simplexIncl_range_disjoint {U : Set ↑X} {n : ℕ}
    {τ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))}
    (hτU : τ ∈ Set.range (simplexIncl U n)) (hτUc : τ ∈ Set.range (simplexIncl Uᶜ n)) : False := by
  obtain ⟨σU, rfl⟩ := hτU
  obtain ⟨σUc, hσUc⟩ := hτUc
  obtain ⟨x, hx⟩ :=
    Set.range_nonempty (X.toSSetObjEquiv (op (SimplexCategory.mk n)) (simplexIncl U n σU))
  have hxU : x ∈ U := range_realize_simplexIncl U σU hx
  have hxUc : x ∈ Uᶜ := range_realize_simplexIncl Uᶜ σUc (by rw [hσUc]; exact hx)
  exact hxUc hxU

/-- **The disjoint-support separation**: if a `U`-chain `chainIncl U cU` plus a `Uᶜ`-chain
`chainIncl Uᶜ cUc` lies in the `S`-subspace chains, then the `U`-summand does on its own. Their
supports are disjoint (`simplexIncl_range_disjoint`), so every `U`-supported simplex is in the sum's
support and hence `S`-valued (`range_of_mem_subspaceChains`). -/
theorem chainIncl_mem_subspaceChains_of_add {U : Set ↑X} (S : Set ↑X) (n : ℕ)
    (cU : SingularChain (sub U) n) (cUc : SingularChain (sub Uᶜ) n)
    (h : chainIncl U n cU + chainIncl Uᶜ n cUc ∈ subspaceChains S n) :
    chainIncl U n cU ∈ subspaceChains S n := by
  classical
  refine mem_subspaceChains_of_support (fun τ hτ => ?_)
  refine range_of_mem_subspaceChains h ?_
  -- `τ` is in the range of `simplexIncl U`, so the `Uᶜ`-summand vanishes at `τ`.
  have hτrange : τ ∈ Set.range (simplexIncl U n) := by
    have := Finsupp.mapDomain_support (s := cU) (f := simplexIncl U n)
      (by rw [chainIncl, Finsupp.lmapDomain_apply] at hτ; exact hτ)
    obtain ⟨σ, _, rfl⟩ := Finset.mem_image.1 this
    exact ⟨σ, rfl⟩
  have hUc0 : (chainIncl Uᶜ n cUc) τ = 0 := by
    by_contra hne
    exact simplexIncl_range_disjoint hτrange
      (by
        rw [chainIncl, Finsupp.lmapDomain_apply] at hne
        by_contra hnr
        exact hne (Finsupp.mapDomain_notin_range cUc τ hnr))
  have hUne : (chainIncl U n cU) τ ≠ 0 := Finsupp.mem_support_iff.1 hτ
  rw [Finsupp.mem_support_iff, Finsupp.add_apply, hUc0, add_zero]
  exact hUne

/-! ## §2. The relative injectivity core. -/

/-- **The relative injectivity core**: if `relChainIncl S U aU + relChainIncl S Uᶜ aUc = 0` in the
relative chains of `(X, S)`, then each summand is `0`. Reduces (via `relChainIncl_mk` and
`RelativeChain.mk_eq_zero_iff`) to: the `U`-part `chainIncl U cU` is an `S`-subspace chain
(`chainIncl_mem_subspaceChains_of_add`), reflected back to `sub U` by
`chainIncl_mem_subspaceChains_iff`. -/
theorem relChainIncl_sum_eq_zero_split {U : Set ↑X} (S : Set ↑X) (n : ℕ)
    (aU : RelativeChain (restr S U) n) (aUc : RelativeChain (restr S Uᶜ) n)
    (h : relChainIncl S U n aU + relChainIncl S Uᶜ n aUc = 0) :
    aU = 0 ∧ aUc = 0 := by
  obtain ⟨cU, rfl⟩ := Submodule.Quotient.mk_surjective _ aU
  obtain ⟨cUc, rfl⟩ := Submodule.Quotient.mk_surjective _ aUc
  rw [show (Submodule.Quotient.mk cU : RelativeChain (restr S U) n)
        = RelativeChain.mk (restr S U) n cU from rfl,
    show (Submodule.Quotient.mk cUc : RelativeChain (restr S Uᶜ) n)
        = RelativeChain.mk (restr S Uᶜ) n cUc from rfl,
    relChainIncl_mk, relChainIncl_mk] at h
  have hsum : chainIncl U n cU + chainIncl Uᶜ n cUc ∈ subspaceChains S n := by
    have := (RelativeChain.mk_eq_zero_iff S n (chainIncl U n cU + chainIncl Uᶜ n cUc)).1 ?_
    · exact this
    · rw [show RelativeChain.mk S n (chainIncl U n cU + chainIncl Uᶜ n cUc)
          = RelativeChain.mk S n (chainIncl U n cU) + RelativeChain.mk S n (chainIncl Uᶜ n cUc) from
        (Submodule.Quotient.mk_add _)]
      exact h
  have hU : chainIncl U n cU ∈ subspaceChains S n :=
    chainIncl_mem_subspaceChains_of_add S n cU cUc hsum
  have hUc : chainIncl Uᶜ n cUc ∈ subspaceChains S n := by
    have heq : chainIncl Uᶜ n cUc
        = (chainIncl U n cU + chainIncl Uᶜ n cUc) + chainIncl U n cU := by
      rw [add_comm (chainIncl U n cU) (chainIncl Uᶜ n cUc), add_assoc, ZModModule.add_self,
        add_zero]
    rw [heq]; exact Submodule.add_mem _ hsum hU
  refine ⟨?_, ?_⟩
  · rw [show (Submodule.Quotient.mk cU : RelativeChain (restr S U) n)
        = RelativeChain.mk (restr S U) n cU from rfl, RelativeChain.mk_eq_zero_iff]
    exact (chainIncl_mem_subspaceChains_iff S U cU).1 hU
  · rw [show (Submodule.Quotient.mk cUc : RelativeChain (restr S Uᶜ) n)
        = RelativeChain.mk (restr S Uᶜ) n cUc from rfl, RelativeChain.mk_eq_zero_iff]
    exact (chainIncl_mem_subspaceChains_iff S Uᶜ cUc).1 hUc

/-- **The two-piece relative-chain map is surjective**: every relative chain of `(X, S)` splits as
`relChainIncl S U wU + relChainIncl S Uᶜ wUc` (the absolute chain split
`subspaceChains_sup_compl_eq_top`, quotiented). -/
theorem relChainIncl_sum_surjective {U : Set ↑X} (hU : IsClopen U) (S : Set ↑X) (n : ℕ)
    (w : RelativeChain S n) :
    ∃ (wU : RelativeChain (restr S U) n) (wUc : RelativeChain (restr S Uᶜ) n),
      w = relChainIncl S U n wU + relChainIncl S Uᶜ n wUc := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ w
  have hc : (c : SingularChain X n) ∈ subspaceChains (S := U) n ⊔ subspaceChains (S := Uᶜ) n := by
    rw [subspaceChains_sup_compl_eq_top hU]; exact Submodule.mem_top
  rw [Submodule.mem_sup] at hc
  obtain ⟨_, ⟨cU, rfl⟩, _, ⟨cUc, rfl⟩, hsum⟩ := hc
  refine ⟨RelativeChain.mk (restr S U) n cU, RelativeChain.mk (restr S Uᶜ) n cUc, ?_⟩
  rw [relChainIncl_mk, relChainIncl_mk,
    show (Submodule.Quotient.mk c : RelativeChain S n) = RelativeChain.mk S n c from rfl, ← hsum,
    show RelativeChain.mk S n (chainIncl U n cU + chainIncl Uᶜ n cUc)
      = RelativeChain.mk S n (chainIncl U n cU) + RelativeChain.mk S n (chainIncl Uᶜ n cUc) from
      (Submodule.Quotient.mk_add _)]

/-! ## §3. The cycle and boundary splits. -/

/-- **The relative cycle split**: a sum `relChainIncl S U aU + relChainIncl S Uᶜ aUc` is a relative
cycle of `(X, S)` iff each piece is a relative cycle of its own pair. The only degree-sensitive step;
in degree `m+1` the relative boundary splits (`relBoundary_relChainIncl`) and the two pieces separate
(`relChainIncl_sum_eq_zero_split`). -/
theorem relCycles_split {U : Set ↑X} (S : Set ↑X) (n : ℕ)
    (aU : RelativeChain (restr S U) n) (aUc : RelativeChain (restr S Uᶜ) n)
    (h : relChainIncl S U n aU + relChainIncl S Uᶜ n aUc ∈ relCycles S n) :
    aU ∈ relCycles (restr S U) n ∧ aUc ∈ relCycles (restr S Uᶜ) n := by
  cases n with
  | zero => exact ⟨Submodule.mem_top, Submodule.mem_top⟩
  | succ m =>
    rw [relCycles, LinearMap.mem_ker, map_add, relBoundary_relChainIncl, relBoundary_relChainIncl]
      at h
    obtain ⟨h1, h2⟩ := relChainIncl_sum_eq_zero_split S m _ _ h
    exact ⟨LinearMap.mem_ker.mpr h1, LinearMap.mem_ker.mpr h2⟩

/-- **The relative boundary split**: if a sum of relative cycles `relChainIncl S U zU +
relChainIncl S Uᶜ zUc` is a relative boundary of `(X, S)`, each piece is a relative boundary of its
pair. Splits the bounding chain (`relChainIncl_sum_surjective`), applies the relative-chain-map
property, and separates (`relChainIncl_sum_eq_zero_split`). -/
theorem relBoundaries_split {U : Set ↑X} (hU : IsClopen U) (S : Set ↑X) (n : ℕ)
    (zU : RelativeChain (restr S U) n) (zUc : RelativeChain (restr S Uᶜ) n)
    (h : relChainIncl S U n zU + relChainIncl S Uᶜ n zUc ∈ relBoundaries S n) :
    zU ∈ relBoundaries (restr S U) n ∧ zUc ∈ relBoundaries (restr S Uᶜ) n := by
  obtain ⟨w, hw⟩ := h
  obtain ⟨wU, wUc, rfl⟩ := relChainIncl_sum_surjective hU S (n + 1) w
  rw [map_add, relBoundary_relChainIncl, relBoundary_relChainIncl] at hw
  -- `relChainIncl S U (∂wU + zU) + relChainIncl S Uᶜ (∂wUc + zUc) = 0`
  have hkey : relChainIncl S U n (relBoundary (restr S U) n wU + zU)
      + relChainIncl S Uᶜ n (relBoundary (restr S Uᶜ) n wUc + zUc) = 0 := by
    rw [map_add, map_add]
    have : relChainIncl S U n (relBoundary (restr S U) n wU)
          + relChainIncl S Uᶜ n (relBoundary (restr S Uᶜ) n wUc)
        + (relChainIncl S U n zU + relChainIncl S Uᶜ n zUc) = 0 := by
      rw [hw, ZModModule.add_self]
    rw [← this]; abel
  obtain ⟨h1, h2⟩ := relChainIncl_sum_eq_zero_split S n _ _ hkey
  refine ⟨⟨wU, ?_⟩, ⟨wUc, ?_⟩⟩
  · exact eq_of_add_eq_zero_two h1
  · exact eq_of_add_eq_zero_two h2

/-! ## §4. The additivity map and its bijectivity. -/

/-- **The relative additivity map** `Hₙ(U, S∩U) × Hₙ(Uᶜ, S∩Uᶜ) → Hₙ(X, S)`,
`(a, b) ↦ excisionMap(a) + excisionMap(b)`. -/
noncomputable def relSplitHn (U : Set ↑X) (S : Set ↑X) (n : ℕ) :
    RelativeHomology (restr S U) n × RelativeHomology (restr S Uᶜ) n
      →ₗ[ZMod 2] RelativeHomology S n :=
  (excisionMap S U n).coprod (excisionMap S Uᶜ n)

theorem relSplitHn_apply (U : Set ↑X) (S : Set ↑X) (n : ℕ)
    (a : RelativeHomology (restr S U) n) (b : RelativeHomology (restr S Uᶜ) n) :
    relSplitHn U S n (a, b) = excisionMap S U n a + excisionMap S Uᶜ n b := rfl

/-- `relSplitHn` is **surjective**: every relative cycle of `(X, S)` splits across the clopen
partition (`relChainIncl_sum_surjective`), and each piece is again a relative cycle
(`relCycles_split`). -/
theorem relSplitHn_surjective {U : Set ↑X} (hU : IsClopen U) (S : Set ↑X) (n : ℕ) :
    Function.Surjective (relSplitHn U S n) := by
  intro y
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  obtain ⟨wU, wUc, hzsplit⟩ := relChainIncl_sum_surjective hU S n (z : RelativeChain S n)
  have hcyc : relChainIncl S U n wU + relChainIncl S Uᶜ n wUc ∈ relCycles S n := hzsplit ▸ z.2
  obtain ⟨hwU, hwUc⟩ := relCycles_split S n wU wUc hcyc
  refine ⟨(RelativeHomology.mk (restr S U) n ⟨wU, hwU⟩,
      RelativeHomology.mk (restr S Uᶜ) n ⟨wUc, hwUc⟩), ?_⟩
  rw [relSplitHn_apply]
  show excisionMap S U n (RelativeHomology.mk (restr S U) n ⟨wU, hwU⟩)
      + excisionMap S Uᶜ n (RelativeHomology.mk (restr S Uᶜ) n ⟨wUc, hwUc⟩)
    = RelativeHomology.mk S n z
  rw [excisionMap_mk, excisionMap_mk,
    show (RelativeHomology.mk S n ⟨relChainIncl S U n wU, _⟩
        + RelativeHomology.mk S n ⟨relChainIncl S Uᶜ n wUc, _⟩)
      = RelativeHomology.mk S n (⟨relChainIncl S U n wU, _⟩ + ⟨relChainIncl S Uᶜ n wUc, _⟩) from
      (Submodule.Quotient.mk_add _)]
  refine congrArg (RelativeHomology.mk S n) (Subtype.ext ?_)
  simpa using hzsplit.symm

/-- `relSplitHn` is **injective** (the chain-level core `relBoundaries_split`). -/
theorem relSplitHn_injective {U : Set ↑X} (hU : IsClopen U) (S : Set ↑X) (n : ℕ) :
    Function.Injective (relSplitHn U S n) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  rintro ⟨a, b⟩ hab
  rw [LinearMap.mem_ker] at hab
  obtain ⟨zU, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨zUc, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [relSplitHn_apply] at hab
  rw [show (Submodule.Quotient.mk zU : RelativeHomology (restr S U) n)
        = RelativeHomology.mk (restr S U) n zU from rfl,
    show (Submodule.Quotient.mk zUc : RelativeHomology (restr S Uᶜ) n)
        = RelativeHomology.mk (restr S Uᶜ) n zUc from rfl,
    excisionMap_mk, excisionMap_mk,
    show (RelativeHomology.mk S n ⟨relChainIncl S U n (zU : RelativeChain (restr S U) n), _⟩
        + RelativeHomology.mk S n ⟨relChainIncl S Uᶜ n (zUc : RelativeChain (restr S Uᶜ) n), _⟩)
      = RelativeHomology.mk S n (⟨relChainIncl S U n zU, _⟩ + ⟨relChainIncl S Uᶜ n zUc, _⟩) from
      (Submodule.Quotient.mk_add _)] at hab
  have hb : (relChainIncl S U n (zU : RelativeChain (restr S U) n)
      + relChainIncl S Uᶜ n (zUc : RelativeChain (restr S Uᶜ) n)) ∈ relBoundaries S n :=
    (RelativeHomology.mk_eq_zero_iff S n _).1 hab
  obtain ⟨hzU, hzUc⟩ := relBoundaries_split hU S n zU zUc hb
  have e1 : (Submodule.Quotient.mk zU : RelativeHomology (restr S U) n) = 0 :=
    (RelativeHomology.mk_eq_zero_iff (restr S U) n zU).mpr hzU
  have e2 : (Submodule.Quotient.mk zUc : RelativeHomology (restr S Uᶜ) n) = 0 :=
    (RelativeHomology.mk_eq_zero_iff (restr S Uᶜ) n zUc).mpr hzUc
  rw [Submodule.mem_bot]
  exact Prod.ext e1 e2

/-- **The relative clopen-split isomorphism** `Hₙ(X, S) ≅ Hₙ(U, S∩U) × Hₙ(Uᶜ, S∩Uᶜ)` for a clopen
partition `X = U ⊔ Uᶜ` and an arbitrary subspace `S ⊆ X` — the relative analogue of
`SingularDisjointUnionHn.splitHnEquiv`. -/
noncomputable def relSplitHnEquiv {U : Set ↑X} (hU : IsClopen U) (S : Set ↑X) (n : ℕ) :
    (RelativeHomology (restr S U) n × RelativeHomology (restr S Uᶜ) n) ≃ₗ[ZMod 2]
      RelativeHomology S n :=
  LinearEquiv.ofBijective (relSplitHn U S n)
    ⟨relSplitHn_injective hU S n, relSplitHn_surjective hU S n⟩

end SKEFTHawking.SingularRelativeDisjointUnionHn
