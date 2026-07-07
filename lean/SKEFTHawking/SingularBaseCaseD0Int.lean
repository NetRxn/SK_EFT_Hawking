/-
# Phase 5q.H (E1 CSC-PD tower) — the integral D⁰ base case (`hbaseConvG` discharge), part 1

The bottom-window (`D⁰`) chart-convex base case over ℤ — the integral mirror of `SingularBaseCaseD0`.
This part builds the **augmentation bridge** `augHInt (legW₀Int a) = ⟨a, [fundCycleW₀Int]⟩` (B4a) via the
cap–augmentation identity `augmentationInt (a ⌢ z) = ⟨a, z⟩`, and the stage-class identity
`[fundCycleW₀Int] = [z₀]` (B4b). Together they give the pairing form the B4c bijectivity assembly consumes.

Over ℤ the flip-pairing bijectivity (`relKroneckerHInt_flip_bijective_of_equiv`, later) rests on the
integral relative UCT free case (`relKroneckerHInt_bijective_of_free`) rather than the ℤ/2 UC vanishing —
the freeness (`SingularTopHomologyFreeUnionInt`) + projectivity (`relBoundariesInt_projective`) supply its
hypotheses at the good-compact stages.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.IntCapProductInt
import SKEFTHawking.SingularRelativeUCInt
import SKEFTHawking.SingularOpenDualityBotInt
import SKEFTHawking.SingularLocalDualityKBotInt
import SKEFTHawking.SingularLineMinusPointInt
import SKEFTHawking.SingularLocalDuality

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularOpenDualityBotInt
open SKEFTHawking.SingularOpenDualityCycleInt (fundCycleW fundCycleW_relHomologous)
open SKEFTHawking.SingularLocalDualityKBotInt
open SKEFTHawking.SingularRelativeUCInt
open SKEFTHawking.SingularLineMinusPointInt (augmentationInt augmentationInt_single augHInt augHInt_mk
  augmentationInt_chainIncl)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)

namespace SKEFTHawking.SingularBaseCaseD0Int

variable {X : TopCat}

/-- **A relative-cycle representative** (integral): an absolute `(k+1)`-chain `z` with `∂z` a subspace
chain projects to a relative `(k+1)`-cycle `[z] ∈ relCyclesInt S (k+1)`. Integral mirror of
`SingularLocalDuality.relMk_mem_relCycles`. -/
theorem relMk_mem_relCyclesInt_of_boundary (S : Set ↑X) {k : ℕ} (z : SingularChainInt X (k + 1))
    (hz : chainBoundary X k z ∈ subspaceChainsInt S k) :
    RelativeChainInt.mk S (k + 1) z ∈ relCyclesInt S (k + 1) := by
  show RelativeChainInt.mk S (k + 1) z ∈ LinearMap.ker (relBoundaryInt S k)
  rw [LinearMap.mem_ker, relBoundaryInt_mk]
  exact (RelativeChainInt.mk_eq_zero_iff S k _).mpr hz

/-- **The front `k`-face of a `k`-simplex is itself** (`q = 0`, integral cup): `frontIncl k 0 = 𝟙 [k]`,
so `frontFace (q := 0) σ = σ`. Coefficient-agnostic; the integral mirror of
`SingularLocalDuality.frontFace_zero` for `SingularCupInt.frontFace`. -/
theorem frontFaceInt_zero {k : ℕ}
    (σ : (TopCat.toSSet.obj X).obj (op (SimplexCategory.mk (k + 0)))) :
    frontFace (q := 0) σ = σ := by
  have hid : frontIncl k 0 = 𝟙 (SimplexCategory.mk k) := by
    apply SimplexCategory.Hom.ext
    apply OrderHom.ext
    funext i
    apply Fin.ext
    rfl
  show (TopCat.toSSet.obj X).map (frontIncl k 0).op σ = σ
  rw [hid]
  simp

/-- **The integral cap–augmentation identity** `ε(a ⌢ z) = ⟨a, z⟩` (`m = 0`). On a basis `k`-simplex `σ`,
`a ⌢ [σ] = a(σ)•[backₒ σ]` (`frontFace_zero`) and `ε` reads off `a(σ)`. Integral mirror of
`SingularLocalDuality.augmentation_cap`. -/
theorem augmentationInt_cap {k : ℕ} (a : SingularCochainInt X k) (z : SingularChainInt X (k + 0)) :
    augmentationInt X (capInt (m := 0) a z) = kronecker a z := by
  induction z using Finsupp.induction_linear with
  | zero => rw [map_zero, map_zero]; exact (map_zero (kroneckerₗ k a)).symm
  | add c d hc hd => rw [map_add, map_add, kronecker_add_right, hc, hd]
  | single σ s =>
      rw [capInt_single_smul, capBasisInt, frontFaceInt_zero,
        map_smul, map_smul, augmentationInt_single, kronecker_single]
      simp only [smul_eq_mul, mul_one]

/-- **The duality–pairing bridge** (integral, chain level): `ε(a ⌢ z) = ⟨a, [z]⟩` for a relative
`(k+1)`-cocycle `a`. `relKroneckerInt_mk` + `augmentationInt_cap`. -/
theorem augmentationInt_cap_eq_relKroneckerInt (S : Set ↑X) {k : ℕ}
    (a : LinearMap.ker (relCoboundaryIntₗ S (k + 1))) (z : SingularChainInt X (k + 1)) :
    augmentationInt X (capInt (m := 0) a.1.1 z)
      = relKroneckerInt S a.1 (RelativeChainInt.mk S (k + 1) z) := by
  rw [relKroneckerInt_mk]
  exact augmentationInt_cap a.1.1 z

variable [T2Space ↑X]

/-- **B4a: the integral `D⁰` augmentation bridge** — `augHInt (legW₀Int a) = ⟨a, [fundCycleW₀Int]⟩`.
The bottom duality leg, post-composed with the augmentation `ε̄`, is the relative Kronecker pairing
against the stage fundamental cycle. Integral mirror of `SingularBaseCaseD0.augH_legW₀_eq_relKroneckerH`. -/
theorem augH_legW₀_eq_relKroneckerHInt {k : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChainInt X (k + 0 + 1)) (hz₀ : chainBoundary X (k + 0) z₀ = 0)
    (K : CompactsIn W) (a : LinearMap.ker (relCoboundaryIntₗ ((↑K.1 : Set ↑X)ᶜ) (k + 1))) :
    augHInt (sub W) (legW₀Int hW z₀ hz₀ K (RelativeCohomologyInt.mk ((↑K.1 : Set ↑X)ᶜ) (k + 1) a))
      = relKroneckerHInt ((↑K.1 : Set ↑X)ᶜ) (RelativeCohomologyInt.mk ((↑K.1 : Set ↑X)ᶜ) (k + 1) a)
          (RelHomologyInt.mk ((↑K.1 : Set ↑X)ᶜ) (k + 1)
            ⟨RelativeChainInt.mk ((↑K.1 : Set ↑X)ᶜ) (k + 1) (fundCycleW₀Int hW z₀ hz₀ K),
              relMk_mem_relCyclesInt_of_boundary ((↑K.1 : Set ↑X)ᶜ) _
                (fundCycleW₀Int_boundary hW z₀ hz₀ K)⟩) := by
  rw [legW₀Int]
  -- `relativeDualityK₀Int_mk` fires only at default transparency (the `cohomGWInt`/`RelativeCohomologyInt`
  -- def-wrapper blocks reducible `rw`/`simp`); `erw` peels it.
  erw [relativeDualityK₀Int_mk]
  rw [augHInt_mk, ← augmentationInt_chainIncl, chainIncl_pullbackDualityIntₗ₀, relKroneckerHInt_mk_mk]
  exact augmentationInt_cap_eq_relKroneckerInt ((↑K.1 : Set ↑X)ᶜ) a (fundCycleW₀Int hW z₀ hz₀ K)

/-- **B4b: the stage class is the ambient fundamental class** (integral) — `[fundCycleW₀Int] = [z₀]` in
`H_{k+1}(M | K; ℤ)`. Over ℤ their difference is a relative boundary (`fundCycleW_relHomologous`, negated —
`neg_sub`/`neg_mem`, cleaner than the mod-2 `a-b=a+b` juggle). Integral mirror of
`SingularBaseCaseD0.fundCycleW₀_class_eq`. -/
theorem fundCycleW₀_class_eqInt {k : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChainInt X (k + 0 + 1)) (hz₀ : chainBoundary X (k + 0) z₀ = 0) (K : CompactsIn W) :
    RelHomologyInt.mk ((↑K.1 : Set ↑X)ᶜ) (k + 1)
        ⟨RelativeChainInt.mk ((↑K.1 : Set ↑X)ᶜ) (k + 1) (fundCycleW₀Int hW z₀ hz₀ K),
          relMk_mem_relCyclesInt_of_boundary ((↑K.1 : Set ↑X)ᶜ) _
            (fundCycleW₀Int_boundary hW z₀ hz₀ K)⟩
      = RelHomologyInt.mk ((↑K.1 : Set ↑X)ᶜ) (k + 1)
          ⟨RelativeChainInt.mk ((↑K.1 : Set ↑X)ᶜ) (k + 1) z₀,
            relMk_mem_relCyclesInt_of_boundary ((↑K.1 : Set ↑X)ᶜ) _ (by
              rw [show chainBoundary X k z₀ = 0 from hz₀]; exact Submodule.zero_mem _)⟩ := by
  refine (Submodule.Quotient.eq _).mpr (Submodule.mem_comap.mpr ?_)
  show RelativeChainInt.mk ((↑K.1 : Set ↑X)ᶜ) (k + 1) (fundCycleW₀Int hW z₀ hz₀ K)
      - RelativeChainInt.mk ((↑K.1 : Set ↑X)ᶜ) (k + 1) z₀
    ∈ relBoundariesInt ((↑K.1 : Set ↑X)ᶜ) (k + 1)
  have hhom := fundCycleW_relHomologous (k := k) (m := 0) hW z₀ hz₀ K
  -- `hhom : [z₀] - [fundCycleW] ∈ B`; negate (`neg_sub`) and collapse `fundCycleW₀Int = castChainInt rfl _`.
  have hneg := neg_mem hhom
  rw [neg_sub] at hneg
  convert hneg using 3
  rw [fundCycleW₀Int, SKEFTHawking.SingularOpenDualityMVConnSquareInt.castChainInt_eq]

/-! ## §4. The integral UC-flip: evaluation against a rank-1 generator is bijective -/

/-- **`dualEquivOfIsoZ E φ = φ g`** when `E g = 1` — the rank-1 dual iso is evaluation at the
`E`-generator `g = E.symm 1`. -/
theorem dualEquivOfIsoZ_apply {H : Type*} [AddCommGroup H] [Module ℤ H] (E : H ≃ₗ[ℤ] ℤ)
    {g : H} (hg : E g = 1) (φ : Module.Dual ℤ H) : dualEquivOfIsoZ E φ = φ g := by
  have hg' : g = E.symm 1 := by rw [← hg, E.symm_apply_apply]
  rw [dualEquivOfIsoZ, LinearEquiv.trans_apply, hg']
  rfl

omit [T2Space ↑X] in
/-- **The integral UC-flip is bijective** (the ℤ analogue of `relKroneckerH_flip_bijective_of_equiv`):
given a rank-1 iso `E : Hₘ₊₂(M,S;ℤ) ≃ ℤ` with generator `g` (`E g = 1`), and with `Hₘ₊₁(M,S;ℤ)` free
(so `Ext = 0`) and the relevant boundaries projective, the pairing `⟨·, g⟩ : Hᵐ⁺²(M,S;ℤ) → ℤ` is
bijective. It factors as `dualEquivOfIsoZ E ∘ relKronMapInt`, both bijective (the latter is the integral
relative UCT free case `relKroneckerHInt_bijective_of_free`). Over ℤ the freeness of `Hₘ₊₁` replaces the
ℤ/2 UC vanishing the mod-2 proof used — supplied by `SingularTopHomologyFreeUnionInt` at the stages. -/
theorem relKroneckerHInt_flip_bijective_of_equiv {S : Set ↑X} {M : ℕ}
    [Module.Free ℤ (RelHomologyInt S (M + 1))]
    [Module.Projective ℤ (relBoundariesInt S M)]
    [Module.Projective ℤ (relBoundariesInt S (M + 1))]
    (E : RelHomologyInt S (M + 2) ≃ₗ[ℤ] ℤ) {g : RelHomologyInt S (M + 2)} (hg : E g = 1) :
    Function.Bijective ⇑((relKroneckerHInt S (N := M + 1)).flip g) := by
  have hcomp : ⇑((relKroneckerHInt S (N := M + 1)).flip g)
      = (dualEquivOfIsoZ E) ∘ (relKronMapInt S (N := M + 1)) := by
    funext ω
    rw [LinearMap.flip_apply]
    exact (dualEquivOfIsoZ_apply E hg (relKronMapInt S ω)).symm
  rw [hcomp]
  exact (dualEquivOfIsoZ E).bijective.comp (relKroneckerHInt_bijective_of_free S)

end SKEFTHawking.SingularBaseCaseD0Int
