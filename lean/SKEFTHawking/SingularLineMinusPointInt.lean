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

end SKEFTHawking.SingularLineMinusPointInt
