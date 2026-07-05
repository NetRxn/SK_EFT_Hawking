import Mathlib
import SKEFTHawking.SingularSphereHomologyInt
import SKEFTHawking.SingularLineMinusPoint

/-!
# Integral base case: reduced `H̃₀(ℝ¹∖0; ℤ) ≅ ℤ` and `H₁(S¹; ℤ) ≅ ℤ` (brick 14e, part 2)

The bottom of the integral sphere/local-homology induction. Signed mirror of `SingularH0` +
`SingularReducedH0` + `SingularDisjointUnion` + `SingularLineMinusPoint` over ℤ.

The one structural difference from mod-2: the base value is `ℤ`, not `ℤ/2`. Where the mod-2 file
gets `ker ε̄ ≅ ℤ/2` by a `finrank = 2 − 1 = 1` count over the *field* `ℤ/2`, over ℤ we identify
`ker(ε̄ : ℤ×ℤ → ℤ)` (the anti-diagonal `{(a, −a)}`) with `ℤ` *explicitly* — no field/finrank needed.

Delivers `H₁(S¹; ℤ) ≅ ℤ` (`circleH1EquivInt`), `Hₘ₊₁(Sᵐ⁺¹; ℤ) ≅ ℤ` (`topSphereIsoInt`), and the
headline `Homology (Sph 4) 3 ≃+ ℤ` = `H₃(S³; ℤ) ≅ ℤ`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite Metric
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)

namespace SKEFTHawking.SingularLineMinusPointInt

/-! ## §A. The integral augmentation `ε : C₀(X;ℤ) → ℤ` and `ε̄ : H₀(X;ℤ) → ℤ` -/

/-- The **integral augmentation** `ε : C₀(X;ℤ) → ℤ`, the sum of the coefficients. -/
noncomputable def augmentationInt (X : TopCat) : SingularChainInt X 0 →ₗ[ℤ] ℤ :=
  Finsupp.linearCombination ℤ (fun _ => 1)

@[simp] theorem augmentationInt_single (X : TopCat)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk 0))) (a : ℤ) :
    augmentationInt X (Finsupp.single σ a) = a := by
  rw [augmentationInt, Finsupp.linearCombination_single, smul_eq_mul, mul_one]

theorem augmentationInt_apply (X : TopCat) (z : SingularChainInt X 0) :
    augmentationInt X z = z.sum fun _ a => a := by
  rw [augmentationInt, Finsupp.linearCombination_apply]
  exact Finsupp.sum_congr fun _ _ => by rw [smul_eq_mul, mul_one]

/-- **The integral augmentation vanishes on boundaries**: `ε(∂c) = 0`. A 1-simplex's two `0`-faces
carry opposite signs `(+1, −1)` over ℤ, so they cancel. -/
theorem augmentationInt_chainBoundary (X : TopCat) (c : SingularChainInt X 1) :
    augmentationInt X (chainBoundary X 0 c) = 0 := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => simp only [map_add, h₁, h₂, add_zero]
  | single σ a =>
      rw [show Finsupp.single σ a = a • Finsupp.single σ (1 : ℤ) by
            rw [Finsupp.smul_single, smul_eq_mul, mul_one], map_smul, map_smul,
          chainBoundary_single, boundaryBasis, map_sum]
      simp only [map_zsmul, augmentationInt_single]
      rw [show (∑ i : Fin 2, ((-1 : ℤ) ^ (i : ℕ)) • (1 : ℤ)) = 0 from by decide, smul_zero]

theorem augmentationInt_surjective (X : TopCat)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk 0))) :
    Function.Surjective (augmentationInt X) :=
  fun a => ⟨Finsupp.single σ a, augmentationInt_single X σ a⟩

theorem augmentationInt_eq_zero_of_mem_boundaries (X : TopCat) (c : SingularChainInt X 0)
    (hc : c ∈ boundaries X 0) : augmentationInt X c = 0 := by
  obtain ⟨d, rfl⟩ := hc
  exact augmentationInt_chainBoundary X d

/-- **The integral augmentation on homology** `ε̄ : H₀(X;ℤ) → ℤ`. -/
noncomputable def augHInt (X : TopCat) : Homology X 0 →ₗ[ℤ] ℤ :=
  Submodule.liftQ _ ((augmentationInt X).comp (cycles X 0).subtype) (by
    rintro ⟨c, hcyc⟩ hc
    show augmentationInt X c = 0
    exact augmentationInt_eq_zero_of_mem_boundaries X c hc)

@[simp] theorem augHInt_mk (X : TopCat) (z : cycles X 0) :
    augHInt X (Homology.mk X 0 z) = augmentationInt X (z : SingularChainInt X 0) := rfl

theorem augHInt_surjective (X : TopCat)
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk 0))) :
    Function.Surjective (augHInt X) :=
  fun a => ⟨Homology.mk X 0 ⟨Finsupp.single σ a, Submodule.mem_top⟩, augmentationInt_single X σ a⟩

/-! ## §B. Reduced `H̃₀(U;ℤ) = 0` from a contraction (degree-0 prism, signed) -/

open SKEFTHawking.SingularHomotopyInvariance (slice constSimplex)
open SKEFTHawking.SingularPrism (prismSimplex endSimplex face_zero_prismSimplex_zero
  face_last_prismSimplex_last)
open SKEFTHawking.SingularHomotopyInvarianceInt (prismOpInt prismBasisInt endMapInt prismOpInt_single
  endMapInt_single endMapInt_eq_self_of_slice_id endMapInt_const_of_slice_const)
open SKEFTHawking.SingularCohomologyInt (face)

/-- **The integral degree-0 chain homotopy** `∂(P z) = end₁_#(z) − end₀_#(z)` on `C₀(X;ℤ)` (no `P∂`
term in degree 0; signed). The prism `1`-simplex of a `0`-simplex has its two faces `end₁` (sign `+1`)
and `end₀` (sign `−1`). -/
theorem prism_chainHomotopyInt_zero {X Y : TopCat} (H : C(↑X × unitInterval, ↑Y))
    (c : SingularChainInt X 0) :
    chainBoundary Y 0 (prismOpInt H 0 c) = endMapInt H 1 0 c - endMapInt H 0 0 c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => simp only [map_add]; rw [h₁, h₂]; abel
  | single σ a =>
      rw [show Finsupp.single σ a = a • Finsupp.single σ (1 : ℤ) by
            rw [Finsupp.smul_single, smul_eq_mul, mul_one]]
      simp only [map_smul, endMapInt_single, ← smul_sub]
      refine congrArg (a • ·) ?_
      rw [prismOpInt_single, one_smul, prismBasisInt, Fin.sum_univ_one]
      simp only [Fin.val_zero, pow_zero, one_smul]
      rw [chainBoundary_single, boundaryBasis, Fin.sum_univ_two,
        show face (0 : Fin 2) (prismSimplex H σ (0 : Fin 1)) = endSimplex H 1 σ from
            face_zero_prismSimplex_zero H σ,
        show face (1 : Fin 2) (prismSimplex H σ (0 : Fin 1)) = endSimplex H 0 σ from
            face_last_prismSimplex_last H σ]
      simp only [Fin.val_zero, Fin.val_one, pow_zero, pow_one, one_smul, neg_one_smul]
      rw [sub_eq_add_neg]

/-- **The integral constant pushforward** `(const_b)_#(z) = (∑ coeffs) · c_b`. -/
theorem mapChainInt_const {X : TopCat} (b : ↑X) {k : ℕ} (z : SingularChainInt X k) :
    mapChainInt (ContinuousMap.const ↑X b) k z
      = Finsupp.single (constSimplex b k) (z.sum fun _ a => a) := by
  induction z using Finsupp.induction_linear with
  | zero => simp
  | add z₁ z₂ h₁ h₂ =>
      rw [map_add, h₁, h₂, Finsupp.sum_add_index' (fun _ => rfl) (fun _ _ _ => rfl),
        Finsupp.single_add]
  | single σ a =>
      rw [mapChainInt_single, SingularHomotopyInvariance.mapSimplex_const,
        Finsupp.sum_single_index rfl]

/-- **Reduced `H̃₀ = 0` from a contraction** (integral): if `U` carries a contraction `H`
(`slice H 0 = id`, `slice H 1 = const_b`), every `0`-chain in `ker ε` is a boundary. Signed degree-0
prism: `∂(P z) = (const_b)_# z − z = ε(z)·c_b − z`, so on `ker ε`, `∂(P z) = −z`. -/
theorem augmentationInt_ker_le_boundaries_of_contraction {U : TopCat}
    (H : C(↑U × unitInterval, ↑U)) (b : ↑U) (h0 : slice H 0 = ContinuousMap.id ↑U)
    (h1 : slice H 1 = ContinuousMap.const ↑U b) (z : SingularChainInt U 0)
    (hz : augmentationInt U z = 0) : z ∈ boundaries U 0 := by
  refine ⟨-prismOpInt H 0 z, ?_⟩
  rw [map_neg, prism_chainHomotopyInt_zero,
    endMapInt_const_of_slice_const H 1 b h1 0 z, endMapInt_eq_self_of_slice_id H 0 h0,
    ← augmentationInt_apply, hz, zero_smul, zero_sub, neg_neg]

/-- **`ε̄ : H₀(U;ℤ) → ℤ` is injective for a contractible space** (kernel = reduced `H̃₀ = 0`). -/
theorem augHInt_injective_of_contraction {U : TopCat} (H : C(↑U × unitInterval, ↑U)) (b : ↑U)
    (h0 : slice H 0 = ContinuousMap.id ↑U) (h1 : slice H 1 = ContinuousMap.const ↑U b) :
    Function.Injective (augHInt U) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  intro x hx
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [LinearMap.mem_ker] at hx
  refine (Submodule.mem_bot _).mpr
    ((Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_comap.mpr ?_))
  exact augmentationInt_ker_le_boundaries_of_contraction H b h0 h1 (z : SingularChainInt U 0) hx

/-! ## §C. Reduced-`H̃₀` pair-LES isomorphisms (integral) -/

open SKEFTHawking.SingularSphereHomologyInt
  (exact_homIncl_homProjInt homProjInt_homIncl)

/-- **The integral augmentation is preserved by pushforward**: `ε_Y(f_# c) = ε_X(c)`. -/
theorem augmentationInt_mapChainInt {X Y : TopCat} (f : C(↑X, ↑Y)) (c : SingularChainInt X 0) :
    augmentationInt Y (mapChainInt f 0 c) = augmentationInt X c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | single σ a => rw [mapChainInt_single, augmentationInt_single, augmentationInt_single]

/-- **`ε̄` is natural** (integral): `ε̄_Y ∘ H₀(f) = ε̄_X`. -/
theorem augHInt_naturality {X Y : TopCat} (f : C(↑X, ↑Y)) (x : Homology X 0) :
    augHInt Y (Homology.mapInt f 0 x) = augHInt X x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  show augHInt Y (Homology.mapInt f 0 (Homology.mk X 0 z)) = augHInt X (Homology.mk X 0 z)
  rw [Homology.mapInt_mk, augHInt_mk, augHInt_mk, cyclesMapInt_coe]
  exact augmentationInt_mapChainInt f (z : SingularChainInt X 0)

/-- **Reduced-acyclicity transports backwards** (integral): `H₀(f)` injective + `Y` reduced-acyclic
⟹ `X` reduced-acyclic. -/
theorem augHInt_injective_of_map {X Y : TopCat} (f : C(↑X, ↑Y))
    (hf : Function.Injective (Homology.mapInt f 0)) (hY : Function.Injective (augHInt Y)) :
    Function.Injective (augHInt X) := by
  intro a b hab
  apply hf; apply hY
  rw [augHInt_naturality, augHInt_naturality]; exact hab

/-- The integral augmentation is preserved by the inclusion chain map. -/
theorem augmentationInt_chainIncl {X : TopCat} (S : Set ↑X) (c : SingularChainInt (sub S) 0) :
    augmentationInt X (chainIncl S 0 c) = augmentationInt (sub S) c := by
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | single τ a => rw [chainIncl_single, augmentationInt_single, augmentationInt_single]

/-- **`ε̄` along the inclusion** `i_* : H₀(S;ℤ) → H₀(X;ℤ)`: `ε̄_X ∘ i_* = ε̄_S`. -/
theorem augHInt_homIncl {X : TopCat} (S : Set ↑X) (y : Homology (sub S) 0) :
    augHInt X (homIncl S 0 y) = augHInt (sub S) y := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  show augHInt X (homIncl S 0 (Homology.mk (sub S) 0 z)) = augHInt (sub S) (Homology.mk (sub S) 0 z)
  rw [homIncl_mk, augHInt_mk, augHInt_mk]
  exact augmentationInt_chainIncl S (z : SingularChainInt (sub S) 0)

/-- **`i_* : H₀(S;ℤ) → H₀(X;ℤ)` is injective when `S` is reduced-acyclic**. -/
theorem homIncl_zero_injective_of_augHInt_injective {X : TopCat} (S : Set ↑X)
    (hS : Function.Injective (augHInt (sub S))) : Function.Injective (homIncl S 0) := by
  intro a b hab; apply hS; rw [← augHInt_homIncl, ← augHInt_homIncl, hab]

/-- **The bottom projection `j_* : H₁(X;ℤ) → H₁(X, S;ℤ)` is an iso when `S` is reduced-acyclic**. -/
theorem homProjInt_one_bijective_of_reduced_acyclic {X : TopCat} (S : Set ↑X)
    (hS1 : ∀ x : Homology (sub S) 1, x = 0) (hSaug : Function.Injective (augHInt (sub S))) :
    Function.Bijective (homProjInt S 1) := by
  have hincl1 : homIncl S 1 = 0 := by ext y; rw [LinearMap.zero_apply, hS1 y, map_zero]
  have hincl0_inj : Function.Injective (homIncl S 0) :=
    homIncl_zero_injective_of_augHInt_injective S hSaug
  have hconn0 : connectingInt S 0 = 0 := by
    apply LinearMap.ext; intro y
    rw [LinearMap.zero_apply]; apply hincl0_inj
    rw [map_zero, ← LinearMap.mem_ker,
      (SingularLocalHomologyInt.exact_connectingInt_homIncl S 0).linearMap_ker_eq]
    exact LinearMap.mem_range_self _ y
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, (exact_homIncl_homProjInt S 1).linearMap_ker_eq, hincl1,
      LinearMap.range_zero]
  · rw [← LinearMap.range_eq_top,
      ← (SingularLocalHomologyInt.exact_homProjInt_connectingInt S 0).linearMap_ker_eq, hconn0,
      LinearMap.ker_zero]

/-- **The bottom connecting map `δ : H₁(X,S;ℤ) → H₀(S;ℤ)` is injective when `H₁(X;ℤ) = 0`**. -/
theorem connectingInt_zero_injective_of_acyclic {X : TopCat} (S : Set ↑X)
    (hX1 : ∀ x : Homology X 1, x = 0) : Function.Injective (connectingInt S 0) := by
  have hproj1 : homProjInt S 1 = 0 := by ext x; rw [LinearMap.zero_apply, hX1 x, map_zero]
  rw [← LinearMap.ker_eq_bot,
    (SingularLocalHomologyInt.exact_homProjInt_connectingInt S 0).linearMap_ker_eq, hproj1,
    LinearMap.range_zero]

/-- **The bottom connecting map has range exactly reduced `H̃₀(S;ℤ) = ker ε̄_S`**, when `X` is
reduced-acyclic (`ε̄_X` injective). -/
theorem connectingInt_zero_range_of_augHInt_injective {X : TopCat} (S : Set ↑X)
    (hXaug : Function.Injective (augHInt X)) :
    LinearMap.range (connectingInt S 0) = LinearMap.ker (augHInt (sub S)) := by
  rw [← (SingularLocalHomologyInt.exact_connectingInt_homIncl S 0).linearMap_ker_eq]
  ext y
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  constructor
  · intro h; rw [← augHInt_homIncl, h, map_zero]
  · intro h; apply hXaug; rw [map_zero, augHInt_homIncl]; exact h

/-! ## §D. Degree-0 disjoint-union additivity and `ker ε̄ ≅ ℤ` (integral) -/

open SKEFTHawking.SingularExcisionIsoInt (single_mem_subspaceChainsInt_of_subordinate
  mem_subspaceChainsInt_of_support range_of_mem_subspaceChainsInt range_simplexIncl_subsetInt)
open SKEFTHawking.SingularRelativeHomologyMod2 (simplexIncl simplexIncl_injective)
open SKEFTHawking.SingularDisjointUnion (simplex_range_subset_or_compl range_realize_simplexIncl)

/-- **Every `k`-chain splits across a clopen partition** (integral): `Cₖ(X;ℤ) = Cₖ(U) ⊔ Cₖ(Uᶜ)`. -/
theorem subspaceChainsInt_sup_compl_eq_top {X : TopCat} {U : Set ↑X} (hU : IsClopen U) (k : ℕ) :
    subspaceChainsInt (S := U) k ⊔ subspaceChainsInt (S := Uᶜ) k = ⊤ := by
  rw [eq_top_iff]
  rintro c -
  induction c using Finsupp.induction_linear with
  | zero => exact Submodule.zero_mem _
  | add c₁ c₂ h₁ h₂ => exact Submodule.add_mem _ h₁ h₂
  | single σ a =>
      have hsmul : Finsupp.single σ a = a • Finsupp.single σ (1 : ℤ) := by
        rw [Finsupp.smul_single, smul_eq_mul, mul_one]
      rcases simplex_range_subset_or_compl hU σ with h | h
      · exact hsmul ▸ Submodule.mem_sup_left
          (Submodule.smul_mem _ a (single_mem_subspaceChainsInt_of_subordinate h))
      · exact hsmul ▸ Submodule.mem_sup_right
          (Submodule.smul_mem _ a (single_mem_subspaceChainsInt_of_subordinate h))

/-- **Disjoint supports** (integral): `Cₖ(U) ⊓ Cₖ(Uᶜ) = ⊥`. -/
theorem subspaceChainsInt_inf_compl_eq_bot {X : TopCat} {U : Set ↑X} (k : ℕ) :
    subspaceChainsInt (S := U) k ⊓ subspaceChainsInt (S := Uᶜ) k = ⊥ := by
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

/-- **The degree-0 additivity map** `H₀(U;ℤ) × H₀(Uᶜ;ℤ) → H₀(X;ℤ)`, `(a, b) ↦ i_*(a) + i_*(b)`. -/
noncomputable def splitH0Int {X : TopCat} (U : Set ↑X) :
    Homology (sub U) 0 × Homology (sub Uᶜ) 0 →ₗ[ℤ] Homology X 0 :=
  (homIncl U 0).coprod (homIncl Uᶜ 0)

/-- `splitH0Int` is **surjective**. -/
theorem splitH0Int_surjective {X : TopCat} {U : Set ↑X} (hU : IsClopen U) :
    Function.Surjective (splitH0Int U) := by
  intro x
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hz : (z : SingularChainInt X 0) ∈ subspaceChainsInt (S := U) 0 ⊔ subspaceChainsInt (S := Uᶜ) 0 := by
    rw [subspaceChainsInt_sup_compl_eq_top hU]; exact Submodule.mem_top
  rw [Submodule.mem_sup] at hz
  obtain ⟨_, ⟨zU, rfl⟩, _, ⟨zUc, rfl⟩, hsum⟩ := hz
  refine ⟨(Homology.mk (sub U) 0 ⟨zU, Submodule.mem_top⟩,
    Homology.mk (sub Uᶜ) 0 ⟨zUc, Submodule.mem_top⟩), ?_⟩
  show homIncl U 0 (Homology.mk (sub U) 0 _) + homIncl Uᶜ 0 (Homology.mk (sub Uᶜ) 0 _)
      = Homology.mk X 0 z
  rw [homIncl_mk, homIncl_mk,
    show z = (⟨_, Submodule.mem_top⟩ : cycles X 0) + ⟨_, Submodule.mem_top⟩ from Subtype.ext hsum.symm]
  rfl

/-- **The chain-level injectivity core** (integral): if `chainIncl U zU + chainIncl Uᶜ zUc` is a
boundary in `X`, each piece is a boundary in its own subspace. -/
theorem chainIncl_add_mem_boundaries_splitInt {X : TopCat} {U : Set ↑X} (hU : IsClopen U)
    (zU : SingularChainInt (sub U) 0) (zUc : SingularChainInt (sub Uᶜ) 0)
    (h : chainIncl U 0 zU + chainIncl Uᶜ 0 zUc ∈ boundaries X 0) :
    zU ∈ boundaries (sub U) 0 ∧ zUc ∈ boundaries (sub Uᶜ) 0 := by
  obtain ⟨w, hw⟩ := h
  have hwsplit : w ∈ subspaceChainsInt (S := U) 1 ⊔ subspaceChainsInt (S := Uᶜ) 1 := by
    rw [subspaceChainsInt_sup_compl_eq_top hU]; exact Submodule.mem_top
  rw [Submodule.mem_sup] at hwsplit
  obtain ⟨_, ⟨wU, rfl⟩, _, ⟨wUc, rfl⟩, hwsum⟩ := hwsplit
  rw [← hwsum, map_add, ← chainIncl_chainBoundary, ← chainIncl_chainBoundary] at hw
  set bU := chainBoundary (sub U) 0 wU
  set bUc := chainBoundary (sub Uᶜ) 0 wUc
  -- hw : chainIncl U bU + chainIncl Uᶜ bUc = chainIncl U zU + chainIncl Uᶜ zUc
  -- ⟹ chainIncl U (bU − zU) = chainIncl Uᶜ (zUc − bUc), lands in C(U) ⊓ C(Uᶜ) = ⊥
  have hkey : chainIncl U 0 (bU - zU) = chainIncl Uᶜ 0 (zUc - bUc) := by
    rw [map_sub, map_sub]; linear_combination (norm := abel) hw
  have hmemU : chainIncl U 0 (bU - zU) ∈ subspaceChainsInt (S := U) 0 ⊓ subspaceChainsInt (S := Uᶜ) 0 :=
    ⟨⟨_, rfl⟩, hkey ▸ ⟨_, rfl⟩⟩
  rw [subspaceChainsInt_inf_compl_eq_bot, Submodule.mem_bot] at hmemU
  have hzU : zU = bU :=
    (sub_eq_zero.mp (chainIncl_injective U 0 (hmemU.trans (map_zero _).symm))).symm
  have hzUc : zUc = bUc :=
    sub_eq_zero.mp ((hkey ▸ hmemU).trans (map_zero _).symm |> chainIncl_injective Uᶜ 0)
  exact ⟨⟨wU, hzU.symm⟩, ⟨wUc, hzUc.symm⟩⟩

/-- `splitH0Int` is **injective**. -/
theorem splitH0Int_injective {X : TopCat} {U : Set ↑X} (hU : IsClopen U) :
    Function.Injective (splitH0Int U) := by
  rw [← LinearMap.ker_eq_bot, eq_bot_iff]
  rintro ⟨a, b⟩ hab
  rw [LinearMap.mem_ker] at hab
  obtain ⟨zU, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨zUc, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  rw [show splitH0Int U (Submodule.Quotient.mk zU, Submodule.Quotient.mk zUc)
        = Homology.mk X 0 ⟨chainIncl U 0 (zU : SingularChainInt (sub U) 0)
            + chainIncl Uᶜ 0 (zUc : SingularChainInt (sub Uᶜ) 0), Submodule.mem_top⟩ from rfl] at hab
  have hab' : chainIncl U 0 (zU : SingularChainInt (sub U) 0)
      + chainIncl Uᶜ 0 (zUc : SingularChainInt (sub Uᶜ) 0) ∈ boundaries X 0 :=
    (Submodule.Quotient.mk_eq_zero ((boundaries X 0).submoduleOf (cycles X 0))).mp hab
  obtain ⟨hzU, hzUc⟩ := chainIncl_add_mem_boundaries_splitInt hU _ _ hab'
  rw [Submodule.mem_bot, Prod.ext_iff]
  exact ⟨(Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_comap.mpr hzU),
    (Submodule.Quotient.mk_eq_zero _).mpr (Submodule.mem_comap.mpr hzUc)⟩

/-- **Degree-0 disjoint-union additivity** (integral): `H₀(X;ℤ) ≅ H₀(U;ℤ) × H₀(Uᶜ;ℤ)`. -/
noncomputable def splitH0IntEquiv {X : TopCat} {U : Set ↑X} (hU : IsClopen U) :
    (Homology (sub U) 0 × Homology (sub Uᶜ) 0) ≃ₗ[ℤ] Homology X 0 :=
  LinearEquiv.ofBijective (splitH0Int U) ⟨splitH0Int_injective hU, splitH0Int_surjective hU⟩

/-- **Augmentation compatibility** (integral): under additivity, `ε̄_X (a, b) = ε̄_U a + ε̄_{Uᶜ} b`. -/
theorem augHInt_splitH0Int {X : TopCat} (U : Set ↑X)
    (p : Homology (sub U) 0 × Homology (sub Uᶜ) 0) :
    augHInt X (splitH0Int U p) = augHInt (sub U) p.1 + augHInt (sub Uᶜ) p.2 := by
  rw [splitH0Int, LinearMap.coprod_apply, map_add, augHInt_homIncl, augHInt_homIncl]

/-- The explicit iso `ker(ℤ × ℤ → ℤ, (a,b) ↦ a + b) ≅ ℤ`, `(a, −a) ↦ a`. Built with cheap term-mode
proofs (avoids the `Prod`-subtype `simp`/`ring` heartbeat wall). The anti-diagonal is the ℤ-analog of
the mod-2 finrank-`1` reduced-`H̃₀`. -/
noncomputable def kerSumLM_equiv_int :
    ↥(LinearMap.ker ((LinearMap.fst ℤ ℤ ℤ) + (LinearMap.snd ℤ ℤ ℤ))) ≃ₗ[ℤ] ℤ := by
  refine LinearEquiv.ofLinear
    ((LinearMap.fst ℤ ℤ ℤ).comp
      (LinearMap.ker ((LinearMap.fst ℤ ℤ ℤ) + (LinearMap.snd ℤ ℤ ℤ))).subtype)
    ({ toFun := fun a => ⟨(a, -a), ?_⟩
       map_add' := ?_
       map_smul' := ?_ }) ?_ ?_
  · show a + -a = 0; exact add_neg_cancel a
  · intro a b
    apply Subtype.ext
    rw [Submodule.coe_add]
    apply Prod.ext
    · show a + b = a + b; rfl
    · show -(a + b) = -a + -b; ring
  · intro r a
    apply Subtype.ext
    rw [SetLike.val_smul]
    apply Prod.ext
    · show r * a = r • a; rfl
    · show -(r * a) = r • (-a); rw [smul_neg, smul_eq_mul]
  · apply LinearMap.ext; intro a; rfl
  · apply LinearMap.ext
    rintro ⟨⟨a, b⟩, hab⟩
    apply Subtype.ext; apply Prod.ext
    · rfl
    · show -a = b
      have : a + b = 0 := hab
      omega

/-- **Reduced `H̃₀` of a two-piece clopen space is `ℤ`** (integral): if `X` splits as clopen `U ⊔ Uᶜ`
with each piece reduced-acyclic AND `H₀`-nonzero (`ε̄` bijective, e.g. contractible), then
`H̃₀(X) = ker ε̄_X ≅ ℤ`. Unlike the mod-2 finrank count, we identify the anti-diagonal
`{(a, −a) : ℤ × ℤ} ≅ ℤ` explicitly: transport `ker ε̄_X` across `H₀(X) ≅ H₀(U) × H₀(Uᶜ) ≅ ℤ × ℤ`
(each `ε̄` an iso) to `ker(ℤ × ℤ → ℤ, (a,b) ↦ a + b) = {(a, −a)}`, then `(a, −a) ↦ a`. -/
theorem augHInt_ker_iso_int {X : TopCat} {U : Set ↑X} (hU : IsClopen U)
    (hUbij : Function.Bijective (augHInt (sub U))) (hUcbij : Function.Bijective (augHInt (sub Uᶜ))) :
    Nonempty (↥(LinearMap.ker (augHInt X)) ≃ₗ[ℤ] ℤ) := by
  classical
  -- H₀(X) ≅ ℤ × ℤ via splitH0IntEquiv⁻¹ then (ε̄_U, ε̄_Uᶜ)
  let eU := LinearEquiv.ofBijective (augHInt (sub U)) hUbij
  let eUc := LinearEquiv.ofBijective (augHInt (sub Uᶜ)) hUcbij
  let e : Homology X 0 ≃ₗ[ℤ] ℤ × ℤ :=
    (splitH0IntEquiv hU).symm.trans (eU.prodCongr eUc)
  -- ε̄_X = (fst + snd) ∘ e
  have haug : ∀ x : Homology X 0, augHInt X x = (e x).1 + (e x).2 := by
    intro x
    obtain ⟨p, rfl⟩ := (splitH0IntEquiv hU).surjective x
    show augHInt X (splitH0IntEquiv hU p) = _
    rw [show (splitH0IntEquiv hU) p = splitH0Int U p from rfl, augHInt_splitH0Int]
    show _ = ((e (splitH0IntEquiv hU p)).1 + (e (splitH0IntEquiv hU p)).2)
    congr 1 <;>
      · show _ = _
        rw [show e (splitH0IntEquiv hU p) = (eU.prodCongr eUc) ((splitH0IntEquiv hU).symm (splitH0IntEquiv hU p))
              from rfl, (splitH0IntEquiv hU).symm_apply_apply]
        rfl
  -- transport ker ε̄_X to {(a,b) | a + b = 0}
  set sumLM : (ℤ × ℤ) →ₗ[ℤ] ℤ := (LinearMap.fst ℤ ℤ ℤ) + (LinearMap.snd ℤ ℤ ℤ) with hsumLM
  have hkerEq : Submodule.map (e : Homology X 0 →ₗ[ℤ] ℤ × ℤ) (LinearMap.ker (augHInt X))
      = LinearMap.ker sumLM := by
    ext p
    simp only [Submodule.mem_map, LinearMap.mem_ker]
    constructor
    · rintro ⟨x, hx, rfl⟩
      show (e x).1 + (e x).2 = 0
      rw [← haug]; exact hx
    · intro hp
      refine ⟨e.symm p, ?_, e.apply_symm_apply p⟩
      rw [haug, e.apply_symm_apply]
      show p.1 + p.2 = 0; exact hp
  -- ker ε̄_X ≅ ker sumLM
  let ekerX : ↥(LinearMap.ker (augHInt X)) ≃ₗ[ℤ] ↥(LinearMap.ker sumLM) :=
    (e.submoduleMap (LinearMap.ker (augHInt X))).trans (LinearEquiv.ofEq _ _ hkerEq)
  -- ker sumLM = {(a, −a)} ≅ ℤ via (a,−a) ↦ a
  exact ⟨ekerX.trans kerSumLM_equiv_int⟩

/-! ## §E. `augHInt` bijectivity transport + convex bijectivity + the `ℝ¹∖0` base -/

open SKEFTHawking.SingularSphereHomologyInt (Homology.mapInt_bijective_of_comp_id_all)

/-- **Reduced-acyclic-with-nonzero-`H₀` (`ε̄` bijective) transports across a homeomorphism** (integral). -/
theorem augHInt_bijective_of_homeo {X Y : TopCat} (f : C(↑X, ↑Y)) (g : C(↑Y, ↑X))
    (hgf : g.comp f = ContinuousMap.id ↑X) (hfg : f.comp g = ContinuousMap.id ↑Y)
    (hY : Function.Bijective (augHInt Y)) : Function.Bijective (augHInt X) := by
  have hf : Function.Bijective (Homology.mapInt f 0) :=
    Homology.mapInt_bijective_of_comp_id_all f g hgf hfg 0
  refine ⟨augHInt_injective_of_map f hf.injective hY.injective, fun t => ?_⟩
  obtain ⟨y, hy⟩ := hY.surjective t
  obtain ⟨x, hx⟩ := hf.surjective y
  exact ⟨x, by rw [← augHInt_naturality f, hx, hy]⟩

/-- A homeomorphism carries `ker ε̄` onto `ker ε̄` (integral). -/
theorem augHInt_ker_map_eq {X Y : TopCat} (f : C(↑X, ↑Y)) (g : C(↑Y, ↑X))
    (hgf : g.comp f = ContinuousMap.id ↑X) (hfg : f.comp g = ContinuousMap.id ↑Y) :
    Submodule.map (Homology.mapInt f 0) (LinearMap.ker (augHInt X)) = LinearMap.ker (augHInt Y) := by
  have hf := Homology.mapInt_bijective_of_comp_id_all f g hgf hfg 0
  ext y
  simp only [Submodule.mem_map, LinearMap.mem_ker]
  constructor
  · rintro ⟨x, hx, rfl⟩; rw [augHInt_naturality]; exact hx
  · intro hy
    obtain ⟨x, hx⟩ := hf.surjective y
    exact ⟨x, by rw [← augHInt_naturality f, hx]; exact hy, hx⟩

/-- **`ker ε̄` (reduced `H̃₀`) transports across a homeomorphism** (integral). -/
noncomputable def augHIntKerEquivOfHomeo {X Y : TopCat} (f : C(↑X, ↑Y)) (g : C(↑Y, ↑X))
    (hgf : g.comp f = ContinuousMap.id ↑X) (hfg : f.comp g = ContinuousMap.id ↑Y) :
    ↥(LinearMap.ker (augHInt X)) ≃ₗ[ℤ] ↥(LinearMap.ker (augHInt Y)) :=
  ((LinearEquiv.ofBijective (Homology.mapInt f 0)
        (Homology.mapInt_bijective_of_comp_id_all f g hgf hfg 0)).submoduleMap
      (LinearMap.ker (augHInt X))).trans
    (LinearEquiv.ofEq _ _ (augHInt_ker_map_eq f g hgf hfg))

/-- **A nonempty convex subset of a normed space is reduced-acyclic with nonzero `H₀`** (integral):
`ε̄` bijective (injective via the straight-line contraction; surjective since nonempty). -/
theorem convex_augHInt_bijective {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {C : Set E} (hC : Convex ℝ C) {p : E} (hp : p ∈ C) :
    Function.Bijective (augHInt (sub (X := TopCat.of E) C)) := by
  let hcont : C(↑(sub (X := TopCat.of E) C) × unitInterval, ↑(sub (X := TopCat.of E) C)) :=
    ⟨fun q => ⟨(1 - (q.2 : ℝ)) • (q.1 : E) + (q.2 : ℝ) • p,
        hC q.1.2 hp (by linarith [q.2.2.2]) q.2.2.1 (by ring)⟩, by fun_prop⟩
  refine ⟨augHInt_injective_of_contraction hcont ⟨p, hp⟩ ?_ ?_,
    augHInt_surjective (sub (X := TopCat.of E) C)
      (constSimplex (⟨p, hp⟩ : ↑(sub (X := TopCat.of E) C)) 0)⟩
  · refine ContinuousMap.ext fun x => Subtype.ext ?_
    show (1 - ((0 : unitInterval) : ℝ)) • (x : E) + ((0 : unitInterval) : ℝ) • p = (x : E)
    simp
  · refine ContinuousMap.ext fun x => Subtype.ext ?_
    show (1 - ((1 : unitInterval) : ℝ)) • (x : E) + ((1 : unitInterval) : ℝ) • p = p
    simp

/-! ## §F. `H̃₀(ℝ¹∖0; ℤ) ≅ ℤ`, `H₁(S¹; ℤ) ≅ ℤ`, and `H₃(S³; ℤ) ≅ ℤ` -/

open SKEFTHawking.SingularPuncturedRetract (Punc)
open SKEFTHawking.SingularLineMinusPoint
  (posSet posRay convex_posRay posFwd posBwd posBwd_comp_posFwd posFwd_comp_posBwd
    negFwd negBwd negBwd_comp_negFwd negFwd_comp_negBwd isClopen_posSet)

/-- **The positive arc of `ℝ¹∖0` is reduced-acyclic with nonzero `H₀`** (integral): homeomorphic to
the convex half-line `posRay`. -/
theorem augHInt_posSet_bijective : Function.Bijective (augHInt (sub posSet)) :=
  augHInt_bijective_of_homeo posFwd posBwd posBwd_comp_posFwd posFwd_comp_posBwd
    (convex_augHInt_bijective convex_posRay (p := EuclideanSpace.single 0 1)
      (by show (0:ℝ) < EuclideanSpace.single 0 (1:ℝ) 0; simp))

/-- **The negative arc is reduced-acyclic with nonzero `H₀`** (integral, antipodal). -/
theorem augHInt_posSetCompl_bijective : Function.Bijective (augHInt (sub posSetᶜ)) :=
  augHInt_bijective_of_homeo negFwd negBwd negBwd_comp_negFwd negFwd_comp_negBwd
    augHInt_posSet_bijective

/-- **`H̃₀(ℝ¹∖0; ℤ) ≅ ℤ`** — the concrete base value of the integral sphere/local-homology induction. -/
theorem augHInt_ker_punc1_iso_int :
    Nonempty (↥(LinearMap.ker (augHInt (Punc 1))) ≃ₗ[ℤ] ℤ) :=
  augHInt_ker_iso_int isClopen_posSet augHInt_posSet_bijective augHInt_posSetCompl_bijective

/-! ### The bottom sphere suspension `H₁(Sⁿ; ℤ) ≅ H̃₀(Sⁿ∖{v,-v}; ℤ)` -/

open SKEFTHawking.SingularSphereHomologyInt
open SKEFTHawking.SingularExcisionIsoInt (excisionEquivInt)
open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.SingularSphereAcyclic (Sph antipode ne_antipode polar_cover)

variable {n : ℕ} {v : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1}

/-- **`ℝⁿ` is reduced-acyclic** (integral): `ε̄ : H₀(ℝⁿ;ℤ) → ℤ` injective, via the straight-line
contraction (reused verbatim from `SingularEuclideanAcyclic`). -/
theorem eucl_augHInt_injective (m : ℕ) :
    Function.Injective (augHInt (SingularEuclideanAcyclic.Eucl m)) :=
  augHInt_injective_of_contraction (SingularEuclideanAcyclic.contraction m) 0
    (SingularEuclideanAcyclic.slice_contraction_zero m)
    (SingularEuclideanAcyclic.slice_contraction_one m)

/-- **The punctured sphere `Sⁿ∖{v}` is reduced-acyclic** (integral): `ε̄` injective, transported from
`ℝⁿ` reduced-acyclic across the stereographic homeo. -/
theorem punctured_sphere_augHInt_injective :
    Function.Injective (augHInt (SingularSphereAcyclic.Apunc n v)) :=
  augHInt_injective_of_map (SingularSphereAcyclic.stereoMap n v)
    (stereoMapInt_bijective_all (v := v) 0).injective (eucl_augHInt_injective n)

/-- The bottom projection `j_* : H₁(Sⁿ;ℤ) → H₁(Sⁿ, Sⁿ∖{v};ℤ)` is bijective (`Sⁿ∖{v}` reduced-acyclic). -/
theorem homProjInt_bottom_bijective :
    Function.Bijective (homProjInt ({v}ᶜ : Set ↑(Sph n)) 1) :=
  homProjInt_one_bijective_of_reduced_acyclic ({v}ᶜ : Set ↑(Sph n))
    (punctured_sphere_homology_trivialInt (v := v) 0) punctured_sphere_augHInt_injective

/-- **The bottom-degree sphere suspension map** `H₁(Sⁿ;ℤ) → H₀(Sⁿ∖{v,-v};ℤ)`. -/
noncomputable def bottomSuspMapInt (n : ℕ) (v : Metric.sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    Homology (Sph n) 1 →ₗ[ℤ]
      Homology (sub (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ))) 0 :=
  (connectingInt (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ)) 0).comp
    (((excisionEquivInt ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ) 0
          (polar_cover (ne_antipode v))).symm.toLinearMap).comp
      (homProjInt ({v}ᶜ : Set ↑(Sph n)) 1))

/-- **The bottom suspension is injective** (integral). -/
theorem bottomSuspMapInt_injective : Function.Injective (bottomSuspMapInt n v) := by
  rw [bottomSuspMapInt, LinearMap.coe_comp, LinearMap.coe_comp]
  exact (connectingInt_zero_injective_of_acyclic (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ))
    (punctured_sphere_homology_trivialInt (v := antipode v) 0)).comp
    (((excisionEquivInt ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ) 0
        (polar_cover (ne_antipode v))).symm.injective).comp homProjInt_bottom_bijective.injective)

/-- **The bottom suspension has range exactly `ker ε̄ = H̃₀(Sⁿ∖{v,-v};ℤ)`** (integral). -/
theorem bottomSuspMapInt_range :
    LinearMap.range (bottomSuspMapInt n v)
      = LinearMap.ker (augHInt (sub (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ)))) := by
  have hsurj : Function.Surjective ⇑(((excisionEquivInt ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ) 0
      (polar_cover (ne_antipode v))).symm.toLinearMap).comp (homProjInt ({v}ᶜ : Set ↑(Sph n)) 1)) := by
    rw [LinearMap.coe_comp]
    exact (excisionEquivInt ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ) 0
      (polar_cover (ne_antipode v))).symm.surjective.comp homProjInt_bottom_bijective.surjective
  rw [bottomSuspMapInt, LinearMap.range_comp, LinearMap.range_eq_top.mpr hsurj, Submodule.map_top]
  exact connectingInt_zero_range_of_augHInt_injective (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ))
    (punctured_sphere_augHInt_injective (v := antipode v))

/-- **The bottom sphere suspension iso** `H₁(Sⁿ;ℤ) ≅ H̃₀(Sⁿ∖{v,-v};ℤ) = ker ε̄` (integral). -/
noncomputable def bottomSuspEquivInt :
    Homology (Sph n) 1 ≃ₗ[ℤ]
      ↥(LinearMap.ker (augHInt (sub (restr ({v}ᶜ : Set ↑(Sph n)) ({antipode v}ᶜ))))) :=
  (LinearEquiv.ofInjective (bottomSuspMapInt n v) bottomSuspMapInt_injective).trans
    (LinearEquiv.ofEq _ _ bottomSuspMapInt_range)

/-! ### The base case `H₁(S¹; ℤ) ≅ ℤ` and the top `Hₙ(Sⁿ; ℤ) ≅ ℤ` -/

open SKEFTHawking.SingularSphereAcyclic
  (equatorMap equatorMapInv equatorMapInv_comp_equatorMap equatorMap_comp_equatorMapInv)
open SKEFTHawking.SingularSphereBottom (basePoint topSphereReduce)

/-- **`H₁(S¹; ℤ) ≅ ℤ`** — the base case of the integral sphere-homology induction. The bottom
suspension gives `H₁(S¹) ≅ H̃₀(equator)`; the equator `S¹∖{v,−v} ≃ ℝ¹∖0`, so
`H̃₀(equator) ≅ H̃₀(ℝ¹∖0) ≅ ℤ`. -/
noncomputable def circleH1EquivInt :
    Homology (Sph 1) 1 ≃ₗ[ℤ] ℤ :=
  (bottomSuspEquivInt (n := 1) (v := basePoint 1)).trans
    ((augHIntKerEquivOfHomeo (equatorMap (basePoint 1)) (equatorMapInv (basePoint 1))
          equatorMapInv_comp_equatorMap equatorMap_comp_equatorMapInv).trans
      augHInt_ker_punc1_iso_int.some)

/-- **`Hₘ₊₁(Sᵐ⁺¹; ℤ) ≅ ℤ`** — the top homology of every positive-dimensional sphere is `ℤ`
(`topSphereReduceInt` down to the circle, then `circleH1EquivInt`). -/
noncomputable def topSphereIsoInt (m : ℕ) :
    Homology (Sph (m + 1)) (m + 1) ≃ₗ[ℤ] ℤ :=
  (topSphereReduceInt m).trans circleH1EquivInt

/-- **`H₃(S³; ℤ) ≅ ℤ`** — the deliverable of brick 14e: `Homology (Sph 4) 3 ≃ₗ ℤ`
(`SingularPuncturedRetract.Sph 4` is the unit `S³ ⊂ ℝ⁴`). -/
noncomputable def H3S3IsoInt : Homology (Sph 3) 3 ≃ₗ[ℤ] ℤ :=
  topSphereIsoInt 2

end SKEFTHawking.SingularLineMinusPointInt
