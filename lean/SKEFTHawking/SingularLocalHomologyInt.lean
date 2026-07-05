import Mathlib
import SKEFTHawking.SingularRelHomologyInt
import SKEFTHawking.SingularEuclideanSphereInt

/-!
# Integral local homology `Hₖ(ℝⁿ, ℝⁿ ∖ 0; ℤ)` and the pair-LES exactness

Completing the integral pair long-exact-sequence started in `SingularRelHomologyInt` (brick 12): the
three **exactness** lemmas at `Hₙ₊₁(X,S)`, `Hₙ(S)`, `Hₙ(X)`, mirroring the mod-2
`SingularPairLES.exact_*` (the proofs are module-generic — same `chainIncl`/`boundaryExtract`/
`relCycleToHom` infrastructure, over ℤ). Then, with `ℝⁿ` integrally acyclic
(`SingularEuclideanAcyclicInt`), the connecting map
`δ : Hⱼ₊₂(ℝⁿ, ℝⁿ∖0; ℤ) ≅ Hⱼ₊₁(ℝⁿ∖0; ℤ)` is an isomorphism — the integral mirror of the mod-2
`SingularLocalHomology.connecting_eucl_bijective`. Composed with the punctured retract
`ℝⁿ∖0 ≃ Sⁿ⁻¹` (`SingularPuncturedRetractInt`) this reduces integral local homology to sphere homology.
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)

namespace SKEFTHawking.SingularLocalHomologyInt

variable {X : TopCat} (S : Set X)

/-! ## §1. Pair-LES exactness (integral) -/

/-- **Exactness at `Hₙ₊₁(X,S;ℤ)`**: `ker δ = im j_*`. Integral mirror of
`SingularPairLES.exact_homProj_connecting`. -/
theorem exact_homProjInt_connectingInt (n : ℕ) :
    Function.Exact (homProjInt S (n + 1)) (connectingInt S n) := by
  intro y
  obtain ⟨c, rfl⟩ := relCycleToHom_surjective S n y
  rw [connectingInt_relCycleToHom, connectingLift_apply]
  constructor
  · intro h
    have hb : boundaryExtract S n c ∈ boundaries (sub S) n := by
      have h2 := (Submodule.Quotient.mk_eq_zero _).1 h
      rwa [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype] at h2
    obtain ⟨e, he⟩ := hb
    have hcyc : (c : SingularChainInt X (n + 1)) - chainIncl S (n + 1) e ∈ cycles X (n + 1) := by
      show _ ∈ LinearMap.ker (chainBoundary X n)
      rw [LinearMap.mem_ker, map_sub, ← chainIncl_boundaryExtract S n c, ← he,
        chainIncl_chainBoundary, sub_self]
    refine ⟨Homology.mk X (n + 1) ⟨_, hcyc⟩, ?_⟩
    rw [homProjInt_mk, relCycleToHom_apply]
    refine congrArg (RelHomologyInt.mk (S := S) (n + 1)) (Subtype.ext ?_)
    show RelativeChainInt.mk S (n + 1) ((c : SingularChainInt X (n + 1)) - chainIncl S (n + 1) e)
      = RelativeChainInt.mk S (n + 1) (c : SingularChainInt X (n + 1))
    rw [RelativeChainInt.mk, RelativeChainInt.mk]
    refine (Submodule.Quotient.eq _).2 ?_
    have hsub : ((c : SingularChainInt X (n + 1)) - chainIncl S (n + 1) e)
        - (c : SingularChainInt X (n + 1)) = -chainIncl S (n + 1) e := by abel
    rw [hsub]
    exact Submodule.neg_mem _ ⟨e, rfl⟩
  · rintro ⟨x, hx⟩
    rw [← connectingLift_apply, ← connectingInt_relCycleToHom, ← hx]
    exact connectingInt_homProjInt S n x

/-- **The complex property `i_* ∘ δ = 0`**: `i_*` kills the image of `δ`. -/
theorem homIncl_connectingInt (n : ℕ) (y : RelHomologyInt S (n + 1)) :
    homIncl S n (connectingInt S n y) = 0 := by
  obtain ⟨c, rfl⟩ := relCycleToHom_surjective S n y
  rw [connectingInt_relCycleToHom, connectingLift_apply, homIncl_mk]
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  show chainIncl S n (boundaryExtract S n c) ∈ boundaries X n
  rw [chainIncl_boundaryExtract]
  exact LinearMap.mem_range_self _ _

/-- **Exactness at `Hₙ(S;ℤ)`**: `ker i_* = im δ`. Integral mirror of
`SingularPairLES.exact_connecting_homIncl`. -/
theorem exact_connectingInt_homIncl (n : ℕ) :
    Function.Exact (connectingInt S n) (homIncl S n) := by
  intro w₀
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ w₀
  constructor
  · intro h
    have hb : chainIncl S n (w : SingularChainInt (sub S) n) ∈ boundaries X n := by
      have h2 : homIncl S n (Homology.mk (sub S) n w) = 0 := h
      rw [homIncl_mk] at h2
      have h3 := (Submodule.Quotient.mk_eq_zero _).1 h2
      rwa [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype] at h3
    obtain ⟨d, hd⟩ := hb
    have hdZ : d ∈ relCycleLift S n := by
      show chainBoundary X n d ∈ subspaceChainsInt S n
      rw [hd]; exact ⟨w, rfl⟩
    refine ⟨relCycleToHom S n ⟨d, hdZ⟩, ?_⟩
    rw [connectingInt_relCycleToHom, connectingLift_apply]
    have hbe : boundaryExtract S n ⟨d, hdZ⟩ = (w : SingularChainInt (sub S) n) := by
      apply chainIncl_injective S n
      rw [chainIncl_boundaryExtract]; exact hd
    exact congrArg (Homology.mk (sub S) n) (Subtype.ext hbe)
  · rintro ⟨y, hy⟩
    rw [← hy]
    exact homIncl_connectingInt S n y

/-! ## §2. The acyclic connecting isomorphism -/

/-- **The connecting map is an isomorphism when the ambient space is acyclic** (integral): if
`Hₙ₊₁(X;ℤ) = 0` and `Hₙ(X;ℤ) = 0`, the LES forces `δ : Hₙ₊₁(X,S;ℤ) → Hₙ(S;ℤ)` bijective. Integral
mirror of `SingularLocalHomology.connecting_bijective_of_acyclic`. -/
theorem connectingInt_bijective_of_acyclic (n : ℕ)
    (hX1 : ∀ x : Homology X (n + 1), x = 0) (hX0 : ∀ x : Homology X n, x = 0) :
    Function.Bijective (connectingInt S n) := by
  have hproj0 : homProjInt S (n + 1) = 0 := by
    ext x; rw [LinearMap.zero_apply, hX1 x, map_zero]
  have hincl0 : homIncl S n = 0 := by
    ext y; rw [LinearMap.zero_apply]; exact hX0 _
  refine ⟨?_, ?_⟩
  · rw [← LinearMap.ker_eq_bot, (exact_homProjInt_connectingInt S n).linearMap_ker_eq, hproj0,
      LinearMap.range_zero]
  · rw [← LinearMap.range_eq_top, ← (exact_connectingInt_homIncl S n).linearMap_ker_eq, hincl0,
      LinearMap.ker_zero]

/-! ## §3. Euclidean triviality and the local connecting isomorphism -/

/-- **Acyclicity is triviality of homology** (integral): if every `(n+1)`-cycle is a boundary then
`Hₙ₊₁(X; ℤ) = 0`. -/
theorem homology_trivial_of_acyclicInt {X : TopCat} {n : ℕ}
    (hac : ∀ z : SingularChainInt X (n + 1), chainBoundary X n z = 0 → z ∈ boundaries X (n + 1))
    (x : Homology X (n + 1)) : x = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
  exact Submodule.mem_comap.mpr (hac z z.2)

open SKEFTHawking.SingularEuclideanAcyclic (Eucl)

/-- `Hₖ₊₁(ℝⁿ; ℤ) = 0` (integral Euclidean triviality). -/
theorem eucl_homology_trivialInt (m k : ℕ) (x : Homology (Eucl m) (k + 1)) : x = 0 :=
  homology_trivial_of_acyclicInt
    (SingularEuclideanAcyclicInt.cycle_mem_boundariesInt m k) x

/-- **The integral local-homology connecting isomorphism `Hⱼ₊₂(ℝⁿ, ℝⁿ∖0; ℤ) ≅ Hⱼ₊₁(ℝⁿ∖0; ℤ)`**
(`n ≥ 1`): from `ℝⁿ` integrally acyclic, the pair-LES connecting map is bijective. Integral mirror of
`SingularLocalHomology.connecting_eucl_bijective`. Composed with the punctured retract
`ℝⁿ∖0 ≃ Sⁿ⁻¹` (`SingularPuncturedRetractInt.homology_mapInt_normalize_bijective`) this gives
`Hⱼ₊₂(ℝⁿ, ℝⁿ∖0; ℤ) ≅ Hⱼ₊₁(Sⁿ⁻¹; ℤ)` — the geometric input to the integral fundamental/local class. -/
theorem connectingInt_eucl_bijective (n j : ℕ) :
    Function.Bijective (connectingInt (X := Eucl n) {x | x ≠ 0} (j + 1)) :=
  connectingInt_bijective_of_acyclic (X := Eucl n) {x | x ≠ 0} (j + 1)
    (eucl_homology_trivialInt n (j + 1)) (eucl_homology_trivialInt n j)

/-! ## §4. The local homology reduces to sphere homology -/

open SKEFTHawking.SingularPuncturedRetract (Punc Sph normalize)
open SKEFTHawking.SingularPuncturedRetractInt
open SKEFTHawking.SingularFunctorialityInt

/-- **The integral local homology of `ℝⁿ` reduces to sphere homology**: the composite
`Hₙ(ℝⁿ, ℝⁿ∖0; ℤ) → Hₙ₋₁(ℝⁿ∖0; ℤ) → Hₙ₋₁(Sⁿ⁻¹; ℤ)` (connecting iso ∘ retract iso) is a bijection.
For `n = j + 2` this is `H_{j+2}(ℝⁿ, ℝⁿ∖0; ℤ) ≅ H_{j+1}(Sⁿ⁻¹; ℤ)`.

This is the geometric tower `H₄(ℝ⁴,ℝ⁴∖0;ℤ) ≅ H₃(ℝ⁴∖0;ℤ) ≅ H₃(S³;ℤ)` from the `IntLocalHomologyIso`
docstring, now GREEN except for the final `H₃(S³;ℤ) ≅ ℤ` (the integral sphere top class). The
`Homology (sub {x|x≠0})` and `Homology (Punc n)` are defeq at the `TopCat` level, so
`Homology.mapInt normalize` composes directly with `connectingInt`. -/
theorem localHomologyInt_reduces_to_sphere (n j : ℕ) :
    Function.Bijective
      ((Homology.mapInt (normalize (n := n)) (j + 1)).toFun ∘
        (connectingInt (X := SingularEuclideanAcyclic.Eucl n) {x | x ≠ 0} (j + 1))) :=
  Function.Bijective.comp (homology_mapInt_normalize_bijective n j)
    (connectingInt_eucl_bijective n j)

end SKEFTHawking.SingularLocalHomologyInt
