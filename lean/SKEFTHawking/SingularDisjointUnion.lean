import Mathlib
import SKEFTHawking.SingularReducedH0
import SKEFTHawking.SingularExcision

/-!
# Reduced `H̃₀` of a two-component space (disjoint-union additivity at degree 0)

The base value `H̃₀(S⁰) ≅ ℤ/2` of the sphere/local-homology induction. The relevant space — the
equator `Sⁿ∖{v,-v}` for `n = 1`, or equivalently `ℝ¹∖0` — is a disjoint union of two contractible
pieces (open rays). This module builds:

* `clopenSumHomeo` — for a clopen `U ⊆ X`, the homeomorphism `↥U ⊕ ↥Uᶜ ≃ₜ X`;
* the degree-`0` chain splitting `C₀(A ⊕ B) ≅ C₀(A) ⊕ C₀(B)` and (since `Δⁿ` is connected) every
  `1`-simplex of `A ⊕ B` lands in one summand, giving `boundaries₀` and the augmentation splitting;
* hence `H̃₀(A ⊕ B) ≅ ℤ/2` when `A`, `B` are each reduced-acyclic (e.g. contractible).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularH0
open SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularReducedH0
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularExcision
open SKEFTHawking.SingularPairLES SKEFTHawking.SingularHomotopyInvariance

namespace SKEFTHawking.SingularDisjointUnion

/-- **The clopen-sum homeomorphism**: a clopen subset `U ⊆ X` splits `X` as `↥U ⊕ ↥Uᶜ`. The underlying
equivalence is `Equiv.Set.sumCompl`; it is a homeomorphism because the inclusions of the open sets
`U`, `Uᶜ` are open maps, so `Sum.elim val val` is a continuous open bijection. -/
noncomputable def clopenSumHomeo {X : Type*} [TopologicalSpace X] {U : Set X} (hU : IsClopen U) :
    (↥U ⊕ ↥Uᶜ) ≃ₜ X :=
  letI : DecidablePred (· ∈ U) := Classical.decPred _
  Equiv.toHomeomorphOfContinuousOpen (Equiv.Set.sumCompl U)
    (continuous_subtype_val.sumElim continuous_subtype_val)
    ((hU.isOpen.isOpenMap_subtype_val).sumElim (hU.compl.isOpen.isOpenMap_subtype_val))

/-- The standard topological `n`-simplex `Δⁿ = stdSimplex ℝ (Fin (n+1))` is **preconnected** (convex). -/
instance instPreconnectedStdSimplex (n : ℕ) :
    PreconnectedSpace (stdSimplex ℝ (Fin (n + 1))) :=
  isPreconnected_iff_preconnectedSpace.mp (convex_stdSimplex ℝ (Fin (n + 1))).isPreconnected

/-- **Every singular `n`-simplex of `X` lands in one piece of a clopen partition**: for a clopen
`U ⊆ X`, the (connected) image of a simplex `Δⁿ → X` is contained in `U` or in `Uᶜ`. This is the
combinatorial heart of degree-wise disjoint-union additivity. -/
theorem simplex_range_subset_or_compl {X : TopCat} {U : Set ↑X} (hU : IsClopen U) {n : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))) :
    Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) σ) ⊆ U ∨
      Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) σ) ⊆ Uᶜ := by
  rcases disjoint_or_subset_of_isClopen
    (isPreconnected_range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) σ).continuous) hU with h | h
  · exact Or.inr (Set.subset_compl_iff_disjoint_right.mpr h)
  · exact Or.inl h

/-- **Every `k`-chain of `X` splits across a clopen partition**: `Cₖ(X) = Cₖ(U) ⊔ Cₖ(Uᶜ)` — each
simplex lands in one piece (`simplex_range_subset_or_compl`) hence in the image of the corresponding
inclusion chain map (`single_mem_subspaceChains_of_subordinate`). -/
theorem subspaceChains_sup_compl_eq_top {X : TopCat} {U : Set ↑X} (hU : IsClopen U) (k : ℕ) :
    subspaceChains (S := U) k ⊔ subspaceChains (S := Uᶜ) k = ⊤ := by
  rw [eq_top_iff]
  rintro c -
  induction c using Finsupp.induction_linear with
  | zero => exact Submodule.zero_mem _
  | add c₁ c₂ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂
  | single σ a =>
      have hsmul : Finsupp.single σ a = a • Finsupp.single σ (1 : ZMod 2) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rcases simplex_range_subset_or_compl hU σ with h | h
      · exact hsmul ▸ Submodule.mem_sup_left
          (Submodule.smul_mem _ a (single_mem_subspaceChains_of_subordinate h))
      · exact hsmul ▸ Submodule.mem_sup_right
          (Submodule.smul_mem _ a (single_mem_subspaceChains_of_subordinate h))

/-- The realization of an included simplex `simplexIncl A σ'` has range inside `A`. -/
theorem range_realize_simplexIncl {X : TopCat} (A : Set ↑X) {k : ℕ}
    (σ' : (TopCat.toSSet.obj (sub A)).obj (op (SimplexCategory.mk k))) :
    Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk k)) (simplexIncl A k σ')) ⊆ A := by
  rw [toSSetObjEquiv_simplexIncl]
  rintro x ⟨t, rfl⟩
  exact (((sub A).toSSetObjEquiv (op (SimplexCategory.mk k)) σ') t).2

/-- **Disjoint supports**: a chain that is both an `U`-chain and a `Uᶜ`-chain is zero — a simplex
cannot be both `U`-valued and `Uᶜ`-valued (its image is nonempty, so cannot lie in `U ∩ Uᶜ = ∅`).
The injectivity half of degree-`0` disjoint-union additivity. -/
theorem subspaceChains_inf_compl_eq_bot {X : TopCat} {U : Set ↑X} (k : ℕ) :
    subspaceChains (S := U) k ⊓ subspaceChains (S := Uᶜ) k = ⊥ := by
  rw [eq_bot_iff]
  rintro c ⟨⟨a, rfl⟩, b, hb⟩
  rw [Submodule.mem_bot]
  ext τ
  rw [Finsupp.coe_zero, Pi.zero_apply]
  by_contra hne
  have hτU : τ ∈ Set.range (simplexIncl U k) := by
    by_contra hnr
    exact hne (by rw [chainIncl, Finsupp.lmapDomain_apply]; exact Finsupp.mapDomain_notin_range a τ hnr)
  have hτUc : τ ∈ Set.range (simplexIncl Uᶜ k) := by
    by_contra hnr
    refine hne ?_
    rw [← hb, chainIncl, Finsupp.lmapDomain_apply]
    exact Finsupp.mapDomain_notin_range b τ hnr
  obtain ⟨σU, rfl⟩ := hτU
  obtain ⟨σUc, hσUc⟩ := hτUc
  obtain ⟨x, hx⟩ :=
    Set.range_nonempty (X.toSSetObjEquiv (op (SimplexCategory.mk k)) (simplexIncl U k σU))
  have hxU : x ∈ U := range_realize_simplexIncl U σU hx
  have hxUc : x ∈ Uᶜ := range_realize_simplexIncl Uᶜ σUc (by rw [hσUc]; exact hx)
  exact hxUc hxU

/-! ## §4. The degree-0 additivity isomorphism and reduced `H̃₀` -/

/-- Over a `ℤ/2`-module, `a + b = 0` forces `a = b` (every element is its own negative). -/
private theorem eq_of_add_eq_zero_two {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] {a b : M}
    (h : a + b = 0) : a = b := by
  rw [← neg_eq_of_add_eq_zero_left h]; exact neg_eq_of_add_eq_zero_left (ZModModule.add_self b)

/-- **The degree-0 additivity map** `H₀(U) × H₀(Uᶜ) → H₀(X)`, `(a, b) ↦ i_*(a) + i_*(b)`. -/
noncomputable def splitH0 {X : TopCat} (U : Set ↑X) :
    Homology (sub U) 0 × Homology (sub Uᶜ) 0 →ₗ[ZMod 2] Homology X 0 :=
  (homIncl U 0).coprod (homIncl Uᶜ 0)

/-- `splitH0` is **surjective**: every `0`-chain of `X` splits across the clopen partition
(`subspaceChains_sup_compl_eq_top`), and every `0`-chain is a cycle. -/
theorem splitH0_surjective {X : TopCat} {U : Set ↑X} (hU : IsClopen U) :
    Function.Surjective (splitH0 U) := by
  intro x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hz : (z : SingularChain X 0) ∈ subspaceChains (S := U) 0 ⊔ subspaceChains (S := Uᶜ) 0 := by
    rw [subspaceChains_sup_compl_eq_top hU]; exact Submodule.mem_top
  rw [Submodule.mem_sup] at hz
  obtain ⟨_, ⟨zU, rfl⟩, _, ⟨zUc, rfl⟩, hsum⟩ := hz
  refine ⟨(Homology.mk (sub U) 0 ⟨zU, Submodule.mem_top⟩,
    Homology.mk (sub Uᶜ) 0 ⟨zUc, Submodule.mem_top⟩), ?_⟩
  show homIncl U 0 (Homology.mk (sub U) 0 _) + homIncl Uᶜ 0 (Homology.mk (sub Uᶜ) 0 _)
      = Homology.mk X 0 z
  rw [homIncl_mk, homIncl_mk,
    show z = (⟨_, Submodule.mem_top⟩ : cycles X 0) + ⟨_, Submodule.mem_top⟩ from Subtype.ext hsum.symm]
  rfl

/-- **The chain-level injectivity core**: if a `U`-chain plus a `Uᶜ`-chain is a boundary in `X`, then
each piece is a boundary in its own subspace. Splits the bounding `1`-chain across the clopen
partition (`subspaceChains_sup_compl_eq_top`) and separates the two pieces (`..._inf_compl_eq_bot`). -/
theorem chainIncl_add_mem_boundaries_split {X : TopCat} {U : Set ↑X} (hU : IsClopen U)
    (zU : SingularChain (sub U) 0) (zUc : SingularChain (sub Uᶜ) 0)
    (h : chainIncl U 0 zU + chainIncl Uᶜ 0 zUc ∈ boundaries X 0) :
    zU ∈ boundaries (sub U) 0 ∧ zUc ∈ boundaries (sub Uᶜ) 0 := by
  obtain ⟨w, hw⟩ := h
  have hwsplit : w ∈ subspaceChains (S := U) 1 ⊔ subspaceChains (S := Uᶜ) 1 := by
    rw [subspaceChains_sup_compl_eq_top hU]; exact Submodule.mem_top
  rw [Submodule.mem_sup] at hwsplit
  obtain ⟨_, ⟨wU, rfl⟩, _, ⟨wUc, rfl⟩, hwsum⟩ := hwsplit
  rw [← hwsum, map_add, ← chainIncl_chainBoundary, ← chainIncl_chainBoundary] at hw
  -- hw : chainIncl U (∂wU) + chainIncl Uᶜ (∂wUc) = chainIncl U zU + chainIncl Uᶜ zUc
  set bU := chainBoundary (sub U) 0 wU
  set bUc := chainBoundary (sub Uᶜ) 0 wUc
  have hkey : chainIncl U 0 (bU + zU) = chainIncl Uᶜ 0 (bUc + zUc) := by
    apply eq_of_add_eq_zero_two
    rw [map_add, map_add,
      show chainIncl U 0 bU + chainIncl U 0 zU + (chainIncl Uᶜ 0 bUc + chainIncl Uᶜ 0 zUc)
        = (chainIncl U 0 bU + chainIncl Uᶜ 0 bUc) + (chainIncl U 0 zU + chainIncl Uᶜ 0 zUc) from by abel,
      hw, ZModModule.add_self]
  have hmemU : chainIncl U 0 (bU + zU) ∈ subspaceChains (S := U) 0 ⊓ subspaceChains (S := Uᶜ) 0 :=
    ⟨⟨_, rfl⟩, hkey ▸ ⟨_, rfl⟩⟩
  rw [subspaceChains_inf_compl_eq_bot, Submodule.mem_bot] at hmemU
  have hzU : zU = bU :=
    (eq_of_add_eq_zero_two (chainIncl_injective U 0 (hmemU.trans (map_zero _).symm))).symm
  have hzUc : zUc = bUc :=
    (eq_of_add_eq_zero_two
      (chainIncl_injective Uᶜ 0 ((hkey ▸ hmemU).trans (map_zero _).symm))).symm
  exact ⟨⟨wU, hzU.symm⟩, ⟨wUc, hzUc.symm⟩⟩

/-- `splitH0` is **injective** (the chain-level core `chainIncl_add_mem_boundaries_split`). -/
theorem splitH0_injective {X : TopCat} {U : Set ↑X} (hU : IsClopen U) :
    Function.Injective (splitH0 U) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  rintro ⟨a, b⟩ hab
  rw [LinearMap.mem_ker] at hab
  obtain ⟨zU, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨zUc, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [show splitH0 U (Submodule.Quotient.mk zU, Submodule.Quotient.mk zUc)
        = Homology.mk X 0 ⟨chainIncl U 0 (zU : SingularChain (sub U) 0)
            + chainIncl Uᶜ 0 (zUc : SingularChain (sub Uᶜ) 0), Submodule.mem_top⟩ from rfl] at hab
  have hab' : chainIncl U 0 (zU : SingularChain (sub U) 0)
      + chainIncl Uᶜ 0 (zUc : SingularChain (sub Uᶜ) 0) ∈ boundaries X 0 :=
    (Submodule.Quotient.mk_eq_zero ((boundaries X 0).submoduleOf (cycles X 0))).mp hab
  obtain ⟨hzU, hzUc⟩ := chainIncl_add_mem_boundaries_split hU _ _ hab'
  rw [Submodule.mem_bot, Prod.ext_iff]
  exact ⟨(Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_comap.mpr hzU),
    (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_comap.mpr hzUc)⟩

/-- **Degree-0 disjoint-union additivity**: `H₀(X) ≅ H₀(U) × H₀(Uᶜ)` for a clopen partition. -/
noncomputable def splitH0Equiv {X : TopCat} {U : Set ↑X} (hU : IsClopen U) :
    (Homology (sub U) 0 × Homology (sub Uᶜ) 0) ≃ₗ[ZMod 2] Homology X 0 :=
  LinearEquiv.ofBijective (splitH0 U) ⟨splitH0_injective hU, splitH0_surjective hU⟩

/-- **Augmentation compatibility**: under the additivity map, `ε̄_X` is the sum
`(a, b) ↦ ε̄_U(a) + ε̄_{Uᶜ}(b)` (each inclusion is augmentation-preserving, `augH_homIncl`). -/
theorem augH_splitH0 {X : TopCat} (U : Set ↑X)
    (p : Homology (sub U) 0 × Homology (sub Uᶜ) 0) :
    augH X (splitH0 U p) = augH (sub U) p.1 + augH (sub Uᶜ) p.2 := by
  rw [splitH0, LinearMap.coprod_apply, map_add, augH_homIncl, augH_homIncl]

/-- **Reduced `H̃₀` of a two-piece clopen space is `ℤ/2`**: if `X` splits as a clopen `U ⊔ Uᶜ` with
each piece reduced-acyclic *and* `H₀`-nonzero (`ε̄` bijective, e.g. each piece contractible), then
`H̃₀(X) = ker ε̄_X ≅ ℤ/2`. Dimension count: `H₀(X) ≅ H₀(U) × H₀(Uᶜ)` has `finrank = 1 + 1 = 2`, `ε̄_X`
is surjective (it already is on each piece), so `finrank(ker ε̄_X) = 2 - 1 = 1`. The base value of the
sphere/local-homology induction (`H̃₀(S⁰) ≅ ℤ/2`). -/
theorem augH_ker_iso_zmod2 {X : TopCat} {U : Set ↑X} (hU : IsClopen U)
    (hUbij : Function.Bijective (augH (sub U))) (hUcbij : Function.Bijective (augH (sub Uᶜ))) :
    Nonempty (↥(LinearMap.ker (augH X)) ≃ₗ[ZMod 2] ZMod 2) := by
  let eU := LinearEquiv.ofBijective (augH (sub U)) hUbij
  let eUc := LinearEquiv.ofBijective (augH (sub Uᶜ)) hUcbij
  haveI : FiniteDimensional (ZMod 2) (Homology (sub U) 0) := eU.symm.finiteDimensional
  haveI : FiniteDimensional (ZMod 2) (Homology (sub Uᶜ) 0) := eUc.symm.finiteDimensional
  haveI : FiniteDimensional (ZMod 2) (Homology X 0) := (splitH0Equiv hU).finiteDimensional
  have hfX : Module.finrank (ZMod 2) (Homology X 0) = 2 := by
    rw [← (splitH0Equiv hU).finrank_eq, Module.finrank_prod, eU.finrank_eq, eUc.finrank_eq,
      Module.finrank_self]
  have hsurj : Function.Surjective (augH X) := fun t => by
    obtain ⟨a, ha⟩ := hUbij.surjective t
    exact ⟨homIncl U 0 a, by rw [augH_homIncl, ha]⟩
  have hker : Module.finrank (ZMod 2) (LinearMap.ker (augH X)) = 1 := by
    have h := LinearMap.finrank_range_add_finrank_ker (augH X)
    rw [LinearMap.range_eq_top.mpr hsurj, finrank_top, Module.finrank_self, hfX] at h
    omega
  exact ⟨(Module.finBasisOfFinrankEq (ZMod 2) _ hker).equivFun.trans
    (LinearEquiv.funUnique (Fin 1) (ZMod 2) (ZMod 2))⟩

/-- **A nonempty convex subset of a normed space is reduced-acyclic with nonzero `H₀`**: `ε̄` is
bijective. Injective via the straight-line contraction `(x, t) ↦ (1-t)•x + t•p` to a basepoint `p`
(stays in `C` by convexity); surjective since `C` is nonempty. The reduced-acyclic input the two
pieces of `ℝ¹∖0` (open half-lines, convex) feed to `augH_ker_iso_zmod2`. -/
theorem convex_augH_bijective {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} (hC : Convex ℝ C) {p : E} (hp : p ∈ C) :
    Function.Bijective (augH (sub (X := TopCat.of E) C)) := by
  let hcont : C(↑(sub (X := TopCat.of E) C) × unitInterval, ↑(sub (X := TopCat.of E) C)) :=
    ⟨fun q => ⟨(1 - (q.2 : ℝ)) • (q.1 : E) + (q.2 : ℝ) • p,
        hC q.1.2 hp (by linarith [q.2.2.2]) q.2.2.1 (by ring)⟩, by fun_prop⟩
  refine ⟨augH_injective_of_contraction hcont ⟨p, hp⟩ ?_ ?_,
    augH_surjective (sub (X := TopCat.of E) C)
      (constSimplex (⟨p, hp⟩ : ↑(sub (X := TopCat.of E) C)) 0)⟩
  · refine ContinuousMap.ext fun x => Subtype.ext ?_
    show (1 - ((0 : unitInterval) : ℝ)) • (x : E) + ((0 : unitInterval) : ℝ) • p = (x : E)
    simp
  · refine ContinuousMap.ext fun x => Subtype.ext ?_
    show (1 - ((1 : unitInterval) : ℝ)) • (x : E) + ((1 : unitInterval) : ℝ) • p = p
    simp

end SKEFTHawking.SingularDisjointUnion
