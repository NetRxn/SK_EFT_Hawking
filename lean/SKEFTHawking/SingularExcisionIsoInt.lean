import Mathlib
import SKEFTHawking.SingularExcisionInt
import SKEFTHawking.SingularRelHomologyInt

/-!
# The singular excision isomorphism over ℤ (brick 14d)

Integral (signed) mirror of `SingularExcisionIso`. For sets `A B : Set X` whose interiors cover `X`,
the inclusion of pairs `(B, A ∩ B) ↪ (X, A)` induces an isomorphism
`Hₙ(B, A ∩ B; ℤ) ≅ Hₙ(X, A; ℤ)` (positive degree).

This packages the **integral** relative small-chains theorem (`relative_small_boundaryInt` and
`relative_add_singularSdInt_iterate_mem_relBoundariesInt`, built here from 14c's
`exists_iterate_smallChainsInt` + `smallChainsInt`) with the two-cover decomposition
`smallChainsInt {A, B} = C(A) + C(B)` (`smallChainsInt_two_eq`) and `C(A) ⊓ C(B) = C(A ∩ B)`
(`subspaceChainsInt_inf`), over the `SingularRelHomologyInt.RelHomologyInt` API.

All geometric/simplex-level inputs (`simplexIncl`, `IsSubordinate`, `toSSetObjEquiv_simplexIncl`,
`single_mem_subspaceChains_of_subordinate`, ...) are coefficient-agnostic and reused from the mod-2
`SingularExcision` / `SingularExcisionIso` verbatim; only the ℤ-linear operators and the SIGNED
(subtraction, not `+`) homotopy identities are new.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularExcisionInt
open SKEFTHawking.SingularSubdivisionInt
open SKEFTHawking.SingularAffineChainInt
open SKEFTHawking.SingularExcision (IsSubordinate)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub inclMap simplexIncl simplexIncl_injective)

namespace SKEFTHawking.SingularExcisionIsoInt

variable {X : TopCat}

/-! ## §0. `Sd`/`D` commute with the integral chain inclusion -/

/-- Chain-level: pushing an in-simplex affine chain along an included simplex equals including the
pushforward (integral): `(simplexIncl A τ')_# c = chainIncl A ((τ')_# c)`. Mirror of the mod-2
`pushChainM_simplexIncl`, reusing the geometric `pushSimplexM_simplexIncl`. -/
theorem pushChainMInt_simplexIncl (A : Set X) {n k : ℕ}
    (τ' : (TopCat.toSSet.obj (sub A)).obj (op (SimplexCategory.mk n)))
    {c : LinChainInt (Fin (n + 1) → ℝ) k} (hc : c ∈ chainsInInt (stdSimplex ℝ (Fin (n + 1))) k) :
    pushChainMInt (simplexIncl A n τ') c = chainIncl A k (pushChainMInt τ' c) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨w, hw, rfl⟩
    rw [pushChainMInt_single, SingularExcision.pushSimplexM_simplexIncl A τ' hw,
      pushChainMInt_single, chainIncl_single]
  · rw [map_zero, map_zero, map_zero]
  · intro a b _ _ ha hb; rw [map_add, map_add, map_add, ha, hb]
  · intro r a _ ha; rw [map_smul, map_smul, map_smul, ha]

/-- **`Sd` commutes with the subspace inclusion** (integral): `Sd ∘ chainIncl A = chainIncl A ∘ Sd`. -/
theorem singularSdInt_chainIncl (A : Set X) (n : ℕ) (d : SingularChainInt (sub A) n) :
    singularSdInt X n (chainIncl A n d) = chainIncl A n (singularSdInt (sub A) n d) := by
  induction d using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add, hc, hd]
  | single τ' a =>
    rw [chainIncl_single,
      show (Finsupp.single (simplexIncl A n τ') a)
          = a • Finsupp.single (simplexIncl A n τ') (1 : ℤ) by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one],
      show (Finsupp.single τ' a) = a • Finsupp.single τ' (1 : ℤ) by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one],
      map_smul, map_smul, map_smul, singularSdInt_single, singularSdInt_single,
      pushChainMInt_simplexIncl A τ'
        (linSubdivInt_mem_chainsInInt (convex_stdSimplex ℝ _) n (idChainInt_mem n))]

/-- **`D` commutes with the subspace inclusion** (integral): `D ∘ chainIncl A = chainIncl A ∘ D`. -/
theorem singularDInt_chainIncl (A : Set X) (n : ℕ) (d : SingularChainInt (sub A) n) :
    singularDInt X n (chainIncl A n d) = chainIncl A (n + 1) (singularDInt (sub A) n d) := by
  induction d using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add, hc, hd]
  | single τ' a =>
    rw [chainIncl_single,
      show (Finsupp.single (simplexIncl A n τ') a)
          = a • Finsupp.single (simplexIncl A n τ') (1 : ℤ) by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one],
      show (Finsupp.single τ' a) = a • Finsupp.single τ' (1 : ℤ) by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one],
      map_smul, map_smul, map_smul, singularDInt_single, singularDInt_single,
      pushChainMInt_simplexIncl A τ'
        (linHomotopyInt_mem_chainsInInt (convex_stdSimplex ℝ _) n (idChainInt_mem n))]

/-! ## §1. `Sd`/`D`/`Dₘ` preserve the integral subspace chains -/

/-- **`Sd` preserves the subspace chains** `C(A)` (integral). -/
theorem singularSdInt_mem_subspaceChainsInt {A : Set X} {n : ℕ}
    {c : SingularChainInt X n} (hc : c ∈ subspaceChainsInt A n) :
    singularSdInt X n c ∈ subspaceChainsInt A n := by
  obtain ⟨d, rfl⟩ := hc
  exact ⟨singularSdInt (sub A) n d, (singularSdInt_chainIncl A n d).symm⟩

/-- **`D` preserves subspace chains** `C(A)` (integral). -/
theorem singularDInt_mem_subspaceChainsInt {A : Set X} {n : ℕ}
    {c : SingularChainInt X n} (hc : c ∈ subspaceChainsInt A n) :
    singularDInt X n c ∈ subspaceChainsInt A (n + 1) := by
  obtain ⟨d, rfl⟩ := hc
  exact ⟨singularDInt (sub A) n d, (singularDInt_chainIncl A n d).symm⟩

/-- Iterating `Sd` keeps a subspace chain in the subspace (integral). -/
theorem singularSdInt_iterate_mem_subspaceChainsInt {A : Set X} {n : ℕ}
    {c : SingularChainInt X n} (hc : c ∈ subspaceChainsInt A n) (m : ℕ) :
    (⇑(singularSdInt X n))^[m] c ∈ subspaceChainsInt A n := by
  induction m with
  | zero => rwa [Function.iterate_zero_apply]
  | succ k ih => rw [Function.iterate_succ_apply']; exact singularSdInt_mem_subspaceChainsInt ih

/-- **`Dₘ` preserves subspace chains** (integral) — so the chain homotopy descends to `C(X)/C(A)`. -/
theorem iterHomotopyInt_mem_subspaceChainsInt {A : Set X} {n : ℕ}
    {c : SingularChainInt X n} (hc : c ∈ subspaceChainsInt A n) (m : ℕ) :
    iterHomotopyInt X n m c ∈ subspaceChainsInt A (n + 1) := by
  rw [iterHomotopyInt]
  exact Submodule.sum_mem _
    (fun i _ => singularSdInt_iterate_mem_subspaceChainsInt (singularDInt_mem_subspaceChainsInt hc) i)

/-! ## §2. `D`/`Dₘ` preserve the integral small chains -/

/-- **`D` preserves smallness** (integral). -/
theorem singularDInt_mem_smallChainsInt {n : ℕ} {𝒰 : Set (Set X)}
    {c : SingularChainInt X n} (hc : c ∈ smallChainsInt 𝒰 n) :
    singularDInt X n c ∈ smallChainsInt 𝒰 (n + 1) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨τ, hτ, rfl⟩
    rw [singularDInt_single]
    exact pushChainMInt_mem_smallChainsInt hτ
      (linHomotopyInt_mem_chainsInInt (convex_stdSimplex ℝ _) n (idChainInt_mem n))
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro a b _ _ ha hb; rw [map_add]; exact Submodule.add_mem _ ha hb
  · intro r a _ ha; rw [map_smul]; exact Submodule.smul_mem _ r ha

/-- The iterated homotopy `Dₘ` preserves smallness (integral). -/
theorem iterHomotopyInt_mem_smallChainsInt {n : ℕ} {𝒰 : Set (Set X)}
    {c : SingularChainInt X n} (hc : c ∈ smallChainsInt 𝒰 n) (m : ℕ) :
    iterHomotopyInt X n m c ∈ smallChainsInt 𝒰 (n + 1) := by
  rw [iterHomotopyInt]
  exact Submodule.sum_mem _
    (fun i _ => singularSdInt_iterate_mem_smallChainsInt (singularDInt_mem_smallChainsInt hc) i)

/-! ## §3. The two-cover decomposition and MV intersection identity (integral) -/

/-- **Lifting lemma** (integral): a subordinate single simplex is in `C(A)`. Reuses the geometric
`single_mem_subspaceChains_of_subordinate`-style bridge via `chainIncl`. -/
theorem single_mem_subspaceChainsInt_of_subordinate {A : Set X} {n : ℕ}
    {τ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))}
    (hτ : Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) ⊆ A) :
    Finsupp.single τ (1 : ℤ) ∈ subspaceChainsInt A n := by
  -- corestrict `τ` to `↥A`, as in the mod-2 `single_mem_subspaceChains_of_subordinate`
  have hmem : ∀ t, X.toSSetObjEquiv (op (SimplexCategory.mk n)) τ t ∈ A := fun t => hτ ⟨t, rfl⟩
  set g := X.toSSetObjEquiv (op (SimplexCategory.mk n)) τ with hg
  set σ' := ((sub A).toSSetObjEquiv (op (SimplexCategory.mk n))).symm
    (⟨fun t => ⟨g t, hmem t⟩, g.continuous.subtype_mk hmem⟩ :
      C(stdSimplex ℝ (Fin (n + 1)), sub A)) with hσ'
  have hincl : simplexIncl A n σ' = τ := by
    apply (X.toSSetObjEquiv (op (SimplexCategory.mk n))).injective
    rw [SingularExcision.toSSetObjEquiv_simplexIncl, hσ', Equiv.apply_symm_apply]
    rfl
  exact ⟨Finsupp.single σ' 1, by rw [chainIncl_single, hincl]⟩

/-- An included simplex `simplexIncl A τ'` has image inside `A`. -/
theorem range_simplexIncl_subsetInt (A : Set X) {n : ℕ}
    (τ' : (TopCat.toSSet.obj (sub A)).obj (op (SimplexCategory.mk n))) :
    Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) (simplexIncl A n τ')) ⊆ A :=
  SingularExcision.range_simplexIncl_subset A τ'

/-- Every support simplex of an integral subspace chain has image inside `S`. -/
theorem range_of_mem_subspaceChainsInt {S : Set X} {n : ℕ} {c : SingularChainInt X n}
    (hc : c ∈ subspaceChainsInt S n) {τ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk n))}
    (hτ : τ ∈ c.support) :
    Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) ⊆ S := by
  classical
  obtain ⟨d, rfl⟩ := hc
  rw [chainIncl, Finsupp.lmapDomain_apply] at hτ
  obtain ⟨τ', _, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hτ)
  exact range_simplexIncl_subsetInt S τ'

/-- A chain whose support simplices all have image in `S` is in `C(S)` (integral). -/
theorem mem_subspaceChainsInt_of_support {S : Set X} {n : ℕ} {c : SingularChainInt X n}
    (h : ∀ τ ∈ c.support, Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) ⊆ S) :
    c ∈ subspaceChainsInt S n := by
  classical
  rw [← Finsupp.sum_single c, Finsupp.sum]
  refine Submodule.sum_mem _ (fun τ hτ => ?_)
  rw [show Finsupp.single τ (c τ) = (c τ) • Finsupp.single τ (1 : ℤ) by
    rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
  exact Submodule.smul_mem _ _ (single_mem_subspaceChainsInt_of_subordinate (h τ hτ))

/-- **The two-cover decomposition** (integral): a chain small for `{A, B}` splits into `C(A) ⊔ C(B)`. -/
theorem smallChainsInt_two_le (A B : Set X) (n : ℕ) :
    smallChainsInt {A, B} n ≤ subspaceChainsInt A n ⊔ subspaceChainsInt B n := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨τ, ⟨U, hU, hsub⟩, rfl⟩
  rcases hU with rfl | rfl
  · exact Submodule.mem_sup_left (single_mem_subspaceChainsInt_of_subordinate hsub)
  · exact Submodule.mem_sup_right (single_mem_subspaceChainsInt_of_subordinate hsub)

/-- The subspace chains of a cover member are small (integral). -/
theorem subspaceChainsInt_le_smallChainsInt {A : Set X} {𝒰 : Set (Set X)} (hA : A ∈ 𝒰)
    (n : ℕ) : subspaceChainsInt A n ≤ smallChainsInt 𝒰 n := by
  classical
  rintro _ ⟨d, rfl⟩
  refine mem_smallChainsInt_of_support (fun τ hτ => ?_)
  rw [chainIncl, Finsupp.lmapDomain_apply] at hτ
  obtain ⟨τ', _, rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hτ)
  exact ⟨A, hA, range_simplexIncl_subsetInt A τ'⟩

/-- **The two-cover decomposition (equality)** `C^{A,B} = C(A) + C(B)` (integral). -/
theorem smallChainsInt_two_eq (A B : Set X) (n : ℕ) :
    smallChainsInt {A, B} n = subspaceChainsInt A n ⊔ subspaceChainsInt B n := by
  have hA : A ∈ ({A, B} : Set (Set X)) := Set.mem_insert _ _
  have hB : B ∈ ({A, B} : Set (Set X)) := Set.mem_insert_of_mem _ rfl
  refine le_antisymm (smallChainsInt_two_le A B n)
    (sup_le (subspaceChainsInt_le_smallChainsInt hA n) (subspaceChainsInt_le_smallChainsInt hB n))

/-- **The Mayer–Vietoris intersection identity** `C(A) ⊓ C(B) = C(A∩B)` (integral). -/
theorem subspaceChainsInt_inf (A B : Set X) (n : ℕ) :
    subspaceChainsInt A n ⊓ subspaceChainsInt B n = subspaceChainsInt (A ∩ B) n := by
  refine le_antisymm (fun c hc => ?_) (le_inf ?_ ?_)
  · refine mem_subspaceChainsInt_of_support (fun τ hτ => Set.subset_inter ?_ ?_)
    · exact range_of_mem_subspaceChainsInt hc.1 hτ
    · exact range_of_mem_subspaceChainsInt hc.2 hτ
  · exact fun c hc => mem_subspaceChainsInt_of_support
      (fun τ hτ => (range_of_mem_subspaceChainsInt hc hτ).trans Set.inter_subset_left)
  · exact fun c hc => mem_subspaceChainsInt_of_support
      (fun τ hτ => (range_of_mem_subspaceChainsInt hc hτ).trans Set.inter_subset_right)

/-! ## §4. The integral relative small-chains theorem -/

/-- **Relative small-chains, surjective half** (integral): a *relative* cycle `c` of `(X, A)`
(`∂c ∈ C(A)`) is relatively homologous to `Sdᵐ c`. From the SIGNED homotopy `∂Dₘ + Dₘ∂ = 1 − Sdᵐ`. -/
theorem relative_sub_singularSdInt_iterate_mem_relBoundariesInt {A : Set X} {n : ℕ}
    {c : SingularChainInt X (n + 1)} (hc : chainBoundary X n c ∈ subspaceChainsInt A n) (m : ℕ) :
    RelativeChainInt.mk A (n + 1) c - RelativeChainInt.mk A (n + 1) ((⇑(singularSdInt X (n + 1)))^[m] c)
      ∈ relBoundariesInt A (n + 1) := by
  refine ⟨RelativeChainInt.mk A (n + 2) (iterHomotopyInt X (n + 1) m c), ?_⟩
  rw [relBoundaryInt_mk]
  have hzero : RelativeChainInt.mk A (n + 1) (iterHomotopyInt X n m (chainBoundary X n c)) = 0 :=
    (RelativeChainInt.mk_eq_zero_iff A (n + 1) _).2 (iterHomotopyInt_mem_subspaceChainsInt hc m)
  -- ∂Dₘc = (c − Sdᵐc) − Dₘ∂c
  have hkey : chainBoundary X (n + 1) (iterHomotopyInt X (n + 1) m c)
      = (c - (⇑(singularSdInt X (n + 1)))^[m] c) - iterHomotopyInt X n m (chainBoundary X n c) := by
    rw [eq_sub_iff_add_eq]; exact iterHomotopyInt_chainHomotopy X m n c
  have hsub : ∀ x y : SingularChainInt X (n + 1),
      RelativeChainInt.mk A (n + 1) (x - y)
        = RelativeChainInt.mk A (n + 1) x - RelativeChainInt.mk A (n + 1) y := fun _ _ => rfl
  rw [hkey, hsub, hsub, hzero, sub_zero]

/-- **Relative small-chains, injective half** (integral): a *small* relative cycle `z` that is a
relative boundary `z ≡ ∂w (mod C(A))` is already a relative boundary by a *small* `w'`. -/
theorem relative_small_boundaryInt {A : Set X} {𝒰 : Set (Set X)}
    (hcov : (⋃ U ∈ 𝒰, interior U) = Set.univ) {n : ℕ} {z : SingularChainInt X (n + 1)}
    (hz_small : z ∈ smallChainsInt 𝒰 (n + 1)) (hz_rcyc : chainBoundary X n z ∈ subspaceChainsInt A n)
    {w : SingularChainInt X (n + 2)} (hw : z + chainBoundary X (n + 1) w ∈ subspaceChainsInt A (n + 1)) :
    ∃ w' ∈ smallChainsInt 𝒰 (n + 2), z + chainBoundary X (n + 1) w' ∈ subspaceChainsInt A (n + 1) := by
  obtain ⟨m, hm⟩ := exists_iterate_smallChainsInt hcov w
  refine ⟨(⇑(singularSdInt X (n + 2)))^[m] w - iterHomotopyInt X (n + 1) m z,
    Submodule.sub_mem _ hm (iterHomotopyInt_mem_smallChainsInt hz_small m), ?_⟩
  -- ∂Dₘz = (z − Sdᵐz) − Dₘ∂z
  have hsd : chainBoundary X (n + 1) (iterHomotopyInt X (n + 1) m z)
      = (z - (⇑(singularSdInt X (n + 1)))^[m] z) - iterHomotopyInt X n m (chainBoundary X n z) := by
    rw [eq_sub_iff_add_eq]; exact iterHomotopyInt_chainHomotopy X m n z
  have hsdw : (⇑(singularSdInt X (n + 1)))^[m] (z + chainBoundary X (n + 1) w)
      = (⇑(singularSdInt X (n + 1)))^[m] z + (⇑(singularSdInt X (n + 1)))^[m] (chainBoundary X (n + 1) w) := by
    rw [← Module.End.coe_pow, map_add]
  have key : z + chainBoundary X (n + 1)
        ((⇑(singularSdInt X (n + 2)))^[m] w - iterHomotopyInt X (n + 1) m z)
      = (⇑(singularSdInt X (n + 1)))^[m] (z + chainBoundary X (n + 1) w)
        + iterHomotopyInt X n m (chainBoundary X n z) := by
    rw [map_sub, singularSdInt_iterate_chainBoundary, hsd, hsdw]
    abel
  rw [key]
  exact Submodule.add_mem _ (singularSdInt_iterate_mem_subspaceChainsInt hw m)
    (iterHomotopyInt_mem_subspaceChainsInt hz_rcyc m)

/-! ## §5. The relative-chain inclusion `C(B, A∩B) → C(X, A)` (integral)

The relative part of the *source* pair `(B, A ∩ B)` viewed intrinsically as a pair
`(sub B, restr A B)`, where `restr A B := Subtype.val ⁻¹' A : Set (sub B)`. The geometric reflection
lemmas (`simplexIncl_range_subset_iff`, `range_toSSetObjEquiv_simplexIncl`) are coefficient-agnostic
and reused from `SingularExcisionIso`. -/

open SKEFTHawking.SingularExcisionIso (restr)

/-- **Chain-level reflection** (integral): `chainIncl B d` is supported in `A` iff `d` is supported in
`Subtype.val ⁻¹' A`. Makes `chainIncl B` a chain map of pairs `(sub B, restr A B) → (X, A)`. -/
theorem chainIncl_mem_subspaceChainsInt_iff (A B : Set X) {n : ℕ} (d : SingularChainInt (sub B) n) :
    chainIncl B n d ∈ subspaceChainsInt A n ↔ d ∈ subspaceChainsInt (Subtype.val ⁻¹' A) n := by
  classical
  have hd : chainIncl B n d = Finsupp.mapDomain (simplexIncl B n) d := by
    rw [chainIncl, Finsupp.lmapDomain_apply]
  constructor
  · intro h
    refine mem_subspaceChainsInt_of_support (fun τ' hτ' => ?_)
    rw [← SingularExcisionIso.simplexIncl_range_subset_iff A B τ']
    refine range_of_mem_subspaceChainsInt h ?_
    rw [Finsupp.mem_support_iff, hd, Finsupp.mapDomain_apply (simplexIncl_injective B n)]
    exact Finsupp.mem_support_iff.1 hτ'
  · intro h
    refine mem_subspaceChainsInt_of_support (fun σ hσ => ?_)
    rw [hd] at hσ
    obtain ⟨τ', hτ', rfl⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hσ)
    rw [SingularExcisionIso.simplexIncl_range_subset_iff A B τ']
    exact range_of_mem_subspaceChainsInt h hτ'

/-- Reflection through `A ∩ B` (integral): `chainIncl B d ∈ C(A ∩ B)` iff `d ∈ C(restr A B)`. -/
theorem chainIncl_mem_inter_iffInt (A B : Set X) {n : ℕ} (d : SingularChainInt (sub B) n) :
    chainIncl B n d ∈ subspaceChainsInt (A ∩ B) n ↔ d ∈ subspaceChainsInt (restr A B) n := by
  rw [chainIncl_mem_subspaceChainsInt_iff (A ∩ B) B d, SingularExcisionIso.restr_inter]

/-- The pushforward of relative chains `C_n(B, A ∩ B) → C_n(X, A)` induced by `chainIncl B`. -/
noncomputable def relChainInclInt (A B : Set X) (n : ℕ) :
    RelativeChainInt (restr A B) n →ₗ[ℤ] RelativeChainInt A n :=
  Submodule.mapQ (subspaceChainsInt (restr A B) n) (subspaceChainsInt A n) (chainIncl B n)
    (fun d hd => Submodule.mem_comap.2 ((chainIncl_mem_subspaceChainsInt_iff A B d).2 hd))

@[simp] theorem relChainInclInt_mk (A B : Set X) (n : ℕ) (c : SingularChainInt (sub B) n) :
    relChainInclInt A B n (RelativeChainInt.mk (restr A B) n c) =
      RelativeChainInt.mk A n (chainIncl B n c) := rfl

/-- `relChainInclInt` is a chain map: it commutes with the relative boundary. -/
theorem relBoundaryInt_relChainInclInt (A B : Set X) (n : ℕ)
    (c : RelativeChainInt (restr A B) (n + 1)) :
    relBoundaryInt A n (relChainInclInt A B (n + 1) c) =
      relChainInclInt A B n (relBoundaryInt (restr A B) n c) := by
  obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ c
  show relBoundaryInt A n (relChainInclInt A B (n + 1) (RelativeChainInt.mk _ (n + 1) c)) =
    relChainInclInt A B n (relBoundaryInt (restr A B) n (RelativeChainInt.mk _ (n + 1) c))
  rw [relChainInclInt_mk, relBoundaryInt_mk, relBoundaryInt_mk, relChainInclInt_mk,
    chainIncl_chainBoundary]

/-- `relChainInclInt` preserves relative cycles. -/
theorem relChainInclInt_mem_relCyclesInt (A B : Set X) (n : ℕ) (z : RelativeChainInt (restr A B) n)
    (hz : z ∈ relCyclesInt (restr A B) n) : relChainInclInt A B n z ∈ relCyclesInt A n := by
  cases n with
  | zero => exact Submodule.mem_top
  | succ m =>
    have hz' : relBoundaryInt (restr A B) m z = 0 := LinearMap.mem_ker.mp hz
    show relChainInclInt A B (m + 1) z ∈ LinearMap.ker (relBoundaryInt A m)
    rw [LinearMap.mem_ker, relBoundaryInt_relChainInclInt, hz', map_zero]

/-- `relChainInclInt` preserves relative boundaries. -/
theorem relChainInclInt_mem_relBoundariesInt (A B : Set X) (n : ℕ)
    (z : RelativeChainInt (restr A B) n) (hz : z ∈ relBoundariesInt (restr A B) n) :
    relChainInclInt A B n z ∈ relBoundariesInt A n := by
  obtain ⟨d, rfl⟩ := hz
  exact ⟨relChainInclInt A B (n + 1) d, relBoundaryInt_relChainInclInt A B n d⟩

/-! ## §6. The excision map on relative homology (integral) -/

/-- **The excision map** `Hₙ(B, A ∩ B; ℤ) → Hₙ(X, A; ℤ)` induced by `relChainInclInt`. -/
noncomputable def excisionMapInt (A B : Set X) (n : ℕ) :
    RelHomologyInt (restr A B) n →ₗ[ℤ] RelHomologyInt A n :=
  Submodule.mapQ _ _
    (LinearMap.restrict (relChainInclInt A B n)
      (fun z hz => relChainInclInt_mem_relCyclesInt A B n z hz))
    (fun z hz => by
      simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype,
        LinearMap.restrict_coe_apply] at hz ⊢
      exact relChainInclInt_mem_relBoundariesInt A B n _ hz)

@[simp] theorem excisionMapInt_mk (A B : Set X) (n : ℕ) (z : relCyclesInt (restr A B) n) :
    excisionMapInt A B n (RelHomologyInt.mk (restr A B) n z)
      = RelHomologyInt.mk A n ⟨relChainInclInt A B n (z : RelativeChainInt (restr A B) n),
          relChainInclInt_mem_relCyclesInt A B n z z.2⟩ := rfl

/-! ## §7. The excision isomorphism (integral) -/

/-- **Excision is injective** (positive degree, integral): the inclusion `(B, A ∩ B) ↪ (X, A)`
induces an injection on `H_{n+1}`. Uses `relative_small_boundaryInt` + the two-cover decomposition
+ the reflection lemma. Signed mirror of `SingularExcisionIso.excisionMap_injective`. -/
theorem excisionMapInt_injective (A B : Set X) (n : ℕ)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set X)), interior U) = Set.univ) :
    Function.Injective (excisionMapInt A B (n + 1)) := by
  rw [injective_iff_map_eq_zero]
  intro h hh
  obtain ⟨z', rfl⟩ := Submodule.Quotient.mk_surjective _ h
  obtain ⟨c', hc'⟩ := Submodule.Quotient.mk_surjective _ (z' : RelativeChainInt (restr A B) (n + 1))
  replace hc' : RelativeChainInt.mk (restr A B) (n + 1) c'
      = (z' : RelativeChainInt (restr A B) (n + 1)) := hc'
  have hz'cyc : relBoundaryInt (restr A B) n (z' : RelativeChainInt (restr A B) (n + 1)) = 0 :=
    LinearMap.mem_ker.mp z'.2
  have hc'_cyc : chainBoundary (sub B) n c' ∈ subspaceChainsInt (restr A B) n := by
    rw [← RelativeChainInt.mk_eq_zero_iff, ← relBoundaryInt_mk, hc', hz'cyc]
  rw [show (Submodule.Quotient.mk z' : RelHomologyInt (restr A B) (n + 1))
        = RelHomologyInt.mk (restr A B) (n + 1) z' from rfl, excisionMapInt_mk,
      RelHomologyInt.mk_eq_zero_iff] at hh
  have hval : relChainInclInt A B (n + 1) (z' : RelativeChainInt (restr A B) (n + 1))
      = RelativeChainInt.mk A (n + 1) (chainIncl B (n + 1) c') := by rw [← hc', relChainInclInt_mk]
  have hh2 : RelativeChainInt.mk A (n + 1) (chainIncl B (n + 1) c') ∈ relBoundariesInt A (n + 1) := by
    rw [← hval]; exact hh
  obtain ⟨wbar, hwbar⟩ := hh2
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ wbar
  replace hwbar : RelativeChainInt.mk A (n + 1) (chainBoundary X (n + 1) w)
      = RelativeChainInt.mk A (n + 1) (chainIncl B (n + 1) c') := hwbar
  -- (signed) `∂w − chainIncl B c' ∈ C(A)`; rewrite to `chainIncl B c' − ∂w ∈ C(A)` via neg-closure
  have hw_bound : chainIncl B (n + 1) c' - chainBoundary X (n + 1) w ∈ subspaceChainsInt A (n + 1) := by
    have hsub := (Submodule.Quotient.eq _).1 hwbar
    -- hsub : ∂w − chainIncl B c' ∈ C(A)
    have := Submodule.neg_mem _ hsub
    rwa [neg_sub] at this
  have hz_small : chainIncl B (n + 1) c' ∈ smallChainsInt ({A, B} : Set (Set X)) (n + 1) :=
    subspaceChainsInt_le_smallChainsInt (by simp) (n + 1) ⟨c', rfl⟩
  have hz_rcyc : chainBoundary X n (chainIncl B (n + 1) c') ∈ subspaceChainsInt A n := by
    rw [← chainIncl_chainBoundary]
    exact (chainIncl_mem_subspaceChainsInt_iff A B (chainBoundary (sub B) n c')).2 hc'_cyc
  -- apply the signed relative small-boundary with `w ↦ -w`
  have hw_bound' : chainIncl B (n + 1) c' + chainBoundary X (n + 1) (-w) ∈ subspaceChainsInt A (n + 1) := by
    rwa [map_neg, ← sub_eq_add_neg]
  obtain ⟨w', hw'_small, hw'_bound⟩ := relative_small_boundaryInt hcov hz_small hz_rcyc hw_bound'
  rw [smallChainsInt_two_eq] at hw'_small
  obtain ⟨wA, hwA, wB, hwB, hwAB⟩ := Submodule.mem_sup.mp hw'_small
  -- `chainIncl B c' + ∂wB` lies in both `C(A)` and `C(B)`, hence in `C(A ∩ B)`
  have hmemA : chainIncl B (n + 1) c' + chainBoundary X (n + 1) wB ∈ subspaceChainsInt A (n + 1) := by
    have h2 : chainIncl B (n + 1) c'
        + (chainBoundary X (n + 1) wA + chainBoundary X (n + 1) wB) ∈ subspaceChainsInt A (n + 1) := by
      rw [← map_add, hwAB]; exact hw'_bound
    have h1 : chainBoundary X (n + 1) wA ∈ subspaceChainsInt A (n + 1) :=
      chainBoundary_mem_subspaceChainsInt A (n + 1) wA hwA
    rw [show chainIncl B (n + 1) c' + chainBoundary X (n + 1) wB
        = (chainIncl B (n + 1) c'
            + (chainBoundary X (n + 1) wA + chainBoundary X (n + 1) wB))
          - chainBoundary X (n + 1) wA by abel]
    exact Submodule.sub_mem _ h2 h1
  have hmemB : chainIncl B (n + 1) c' + chainBoundary X (n + 1) wB ∈ subspaceChainsInt B (n + 1) :=
    Submodule.add_mem _ ⟨c', rfl⟩ (chainBoundary_mem_subspaceChainsInt B (n + 1) wB hwB)
  have hkey : chainIncl B (n + 1) c' + chainBoundary X (n + 1) wB
      ∈ subspaceChainsInt (A ∩ B) (n + 1) := by
    rw [← subspaceChainsInt_inf]; exact Submodule.mem_inf.2 ⟨hmemA, hmemB⟩
  -- pull `wB` back to `sub B` and reflect through `A ∩ B`
  obtain ⟨v, rfl⟩ := hwB
  rw [← chainIncl_chainBoundary, ← map_add, chainIncl_mem_inter_iffInt] at hkey
  -- `hkey : c' + ∂v ∈ C(restr A B)`, so `[c'] = [−∂v]` is a relative boundary
  refine (RelHomologyInt.mk_eq_zero_iff (restr A B) (n + 1) z').2 ?_
  refine ⟨RelativeChainInt.mk (restr A B) (n + 2) (-v), ?_⟩
  rw [relBoundaryInt_mk, ← hc']
  show RelativeChainInt.mk (restr A B) (n + 1) (chainBoundary (sub B) (n + 1) (-v))
      = RelativeChainInt.mk (restr A B) (n + 1) c'
  refine (Submodule.Quotient.eq (subspaceChainsInt (restr A B) (n + 1))).2 ?_
  -- ∂(−v) − c' = −(c' + ∂v) ∈ C(restr A B)
  have hneg : -(c' + chainBoundary (sub B) (n + 1) v) ∈ subspaceChainsInt (restr A B) (n + 1) :=
    Submodule.neg_mem _ hkey
  rw [map_neg,
    show -chainBoundary (sub B) (n + 1) v - c' = -(c' + chainBoundary (sub B) (n + 1) v) by abel]
  exact hneg

/-- **Excision is surjective** (positive degree, integral). Uses `relative_sub_singularSdInt_iterate_
mem_relBoundariesInt`: subdivide a relative cycle until `{A, B}`-small, drop the `C(A)` part, pull the
remaining `C(B)` part back to `sub B`. Signed mirror of `SingularExcisionIso.excisionMap_surjective`. -/
theorem excisionMapInt_surjective (A B : Set X) (n : ℕ)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set X)), interior U) = Set.univ) :
    Function.Surjective (excisionMapInt A B (n + 1)) := by
  intro h
  obtain ⟨zc, rfl⟩ := Submodule.Quotient.mk_surjective _ h
  obtain ⟨z, hz⟩ := Submodule.Quotient.mk_surjective _ (zc : RelativeChainInt A (n + 1))
  replace hz : RelativeChainInt.mk A (n + 1) z = (zc : RelativeChainInt A (n + 1)) := hz
  have hz_relcyc : RelativeChainInt.mk A (n + 1) z ∈ relCyclesInt A (n + 1) := by rw [hz]; exact zc.2
  have hz_cyc : chainBoundary X n z ∈ subspaceChainsInt A n := by
    rw [← RelativeChainInt.mk_eq_zero_iff, ← relBoundaryInt_mk, hz]
    exact LinearMap.mem_ker.mp zc.2
  obtain ⟨m, hsmall⟩ := exists_iterate_smallChainsInt hcov z
  rw [smallChainsInt_two_eq] at hsmall
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hsmall
  -- Sdᵐz = a + b, a ∈ C(A), b ∈ C(B); so [Sdᵐz] = [b] in C(X,A)
  have hSd_eq : RelativeChainInt.mk A (n + 1) ((⇑(singularSdInt X (n + 1)))^[m] z)
      = RelativeChainInt.mk A (n + 1) b := by
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [Submodule.Quotient.eq, show (⇑(singularSdInt X (n + 1)))^[m] z - b = a by rw [← hab]; abel]
    exact ha
  -- z − Sdᵐz is a relative boundary; so z − b is (via hSd_eq)
  have hrel : RelativeChainInt.mk A (n + 1) z - RelativeChainInt.mk A (n + 1) b
      ∈ relBoundariesInt A (n + 1) := by
    rw [← hSd_eq]; exact relative_sub_singularSdInt_iterate_mem_relBoundariesInt hz_cyc m
  have hb_cyc : RelativeChainInt.mk A (n + 1) b ∈ relCyclesInt A (n + 1) := by
    -- b = z − (z − b); z is a rel cycle, z − b is a rel boundary ⊆ rel cycles
    have hsum : RelativeChainInt.mk A (n + 1) z - RelativeChainInt.mk A (n + 1) b
        ∈ relCyclesInt A (n + 1) := relBoundariesInt_le_relCyclesInt A (n + 1) hrel
    rw [show RelativeChainInt.mk A (n + 1) b
          = RelativeChainInt.mk A (n + 1) z
            - (RelativeChainInt.mk A (n + 1) z - RelativeChainInt.mk A (n + 1) b) by abel]
    exact Submodule.sub_mem _ hz_relcyc hsum
  obtain ⟨b', rfl⟩ := hb
  have hb'_cyc : chainBoundary (sub B) n b' ∈ subspaceChainsInt (restr A B) n := by
    rw [← chainIncl_mem_inter_iffInt, chainIncl_chainBoundary, ← subspaceChainsInt_inf]
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · have hker : relBoundaryInt A n (RelativeChainInt.mk A (n + 1) (chainIncl B (n + 1) b')) = 0 :=
        LinearMap.mem_ker.mp hb_cyc
      rwa [relBoundaryInt_mk, RelativeChainInt.mk_eq_zero_iff] at hker
    · exact chainBoundary_mem_subspaceChainsInt B n (chainIncl B (n + 1) b') ⟨b', rfl⟩
  refine ⟨RelHomologyInt.mk (restr A B) (n + 1)
    ⟨RelativeChainInt.mk (restr A B) (n + 1) b', LinearMap.mem_ker.2 ?_⟩, ?_⟩
  · rw [relBoundaryInt_mk, RelativeChainInt.mk_eq_zero_iff]; exact hb'_cyc
  · rw [excisionMapInt_mk]
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk zc
    rw [Submodule.Quotient.eq]
    refine Submodule.mem_comap.2 ?_
    show RelativeChainInt.mk A (n + 1) (chainIncl B (n + 1) b') - (zc : RelativeChainInt A (n + 1))
        ∈ relBoundariesInt A (n + 1)
    rw [← hz]
    -- mk (chainIncl B b') = mk b (b = chainIncl B b'); (mk b − mk z) = −(mk z − mk b) ∈ rel boundaries
    have : RelativeChainInt.mk A (n + 1) (chainIncl B (n + 1) b') - RelativeChainInt.mk A (n + 1) z
        = -(RelativeChainInt.mk A (n + 1) z - RelativeChainInt.mk A (n + 1) (chainIncl B (n + 1) b')) := by
      abel
    rw [this]
    exact Submodule.neg_mem _ hrel

/-- **The excision isomorphism** `H_{n+1}(B, A ∩ B; ℤ) ≅ H_{n+1}(X, A; ℤ)` when the interiors of `A`
and `B` cover `X`. The inclusion of pairs `(B, A ∩ B) ↪ (X, A)` induces an isomorphism on relative ℤ
homology in every positive degree — signed singular excision, built from the integral relative
small-chains theorem. -/
noncomputable def excisionEquivInt (A B : Set X) (n : ℕ)
    (hcov : (⋃ U ∈ ({A, B} : Set (Set X)), interior U) = Set.univ) :
    RelHomologyInt (restr A B) (n + 1) ≃ₗ[ℤ] RelHomologyInt A (n + 1) :=
  LinearEquiv.ofBijective (excisionMapInt A B (n + 1))
    ⟨excisionMapInt_injective A B n hcov, excisionMapInt_surjective A B n hcov⟩

end SKEFTHawking.SingularExcisionIsoInt
