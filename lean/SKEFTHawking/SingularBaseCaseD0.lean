import Mathlib
import SKEFTHawking.SingularOpenDualityBot
import SKEFTHawking.SingularConnSquareCloseChainMapBot
import SKEFTHawking.SingularLocalDuality
import SKEFTHawking.SingularReducedH0

/-!
# Phase 5q.G (G1 PD-induction, base-case B4a/B4b) — the `D⁰` augmentation bridge

* `augH_legW₀_eq_relKroneckerH` (B4a): the augmentation of the ₀-family duality leg is the
  relative Kronecker pairing against the stage fundamental presentation —
  `augH (D⁰_K a) = ⟨a, [fundCycleW₀]⟩`. The subspace-valued companion of
  `augH_relativeDuality0_eq_relKroneckerH` (the "structural fact that makes `D_x` a PD iso"),
  through `legW₀_mk` / `augmentation_chainIncl` / `chainIncl_pullbackDualityₗ₀` /
  `augmentation_cap_eq_relKronecker`.
* `fundCycleW₀_class_eq` (B4b): the stage class `[fundCycleW₀] = [z₀]` in
  `H_{k+1}(M | K)` — the single-choice presentation is relatively homologous to the ambient
  fundamental cycle (`fundCycleW_relHomologous` at `(k, 0)`, with the `castChain rfl` collapse).

Together: `augH (D⁰_K a) = ⟨a, [z₀]⟩` — the pairing form the B4c bijectivity assembly consumes.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativePairing SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularOpenDualityBot SKEFTHawking.SingularLocalDualityKBot
open SKEFTHawking.SingularConnSquareCloseChainMapBot SKEFTHawking.SingularLocalDuality
open SKEFTHawking.SingularOpenDualityCycle SKEFTHawking.SingularReducedH0
open SKEFTHawking.SingularH0

namespace SKEFTHawking.SingularBaseCaseD0

variable {X : TopCat} [T2Space ↑X]

/-- **B4a: the `D⁰` augmentation bridge** — `augH (legW₀ a) = ⟨a, [fundCycleW₀]⟩`. -/
theorem augH_legW₀_eq_relKroneckerH {k : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChain X (k + 0 + 1)) (hz₀ : chainBoundary X (k + 0) z₀ = 0)
    (K : CompactsIn W) (a : LinearMap.ker (relCoboundaryₗ ((↑K.1 : Set ↑X)ᶜ) (k + 1))) :
    augH (sub W) (legW₀ hW z₀ hz₀ K (RelativeCohomology.mk ((↑K.1 : Set ↑X)ᶜ) (k + 1) a))
      = relKroneckerH ((↑K.1 : Set ↑X)ᶜ) (RelativeCohomology.mk ((↑K.1 : Set ↑X)ᶜ) (k + 1) a)
          (RelativeHomology.mk ((↑K.1 : Set ↑X)ᶜ) (k + 1)
            ⟨RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + 1) (fundCycleW₀ hW z₀ hz₀ K),
              relMk_mem_relCycles ((↑K.1 : Set ↑X)ᶜ) _ (fundCycleW₀_boundary hW z₀ hz₀ K)⟩) := by
  rw [legW₀_mk, augH_mk, ← augmentation_chainIncl,
    SKEFTHawking.SingularLocalDualityKBot.chainIncl_pullbackDualityₗ₀,
    relKroneckerH_mk_mk]
  exact augmentation_cap_eq_relKronecker ((↑K.1 : Set ↑X)ᶜ) a (fundCycleW₀ hW z₀ hz₀ K)

omit [T2Space ↑X] in
/-- ℤ/2 membership swap: `b + a ∈ B → a - b ∈ B` (fresh-budget helper for `fundCycleW₀_class_eq`). -/
private theorem mem_swap_sub {S : Set ↑X} {n : ℕ} (a b : RelativeChain S n)
    {B : Submodule (ZMod 2) (RelativeChain S n)} (h : b + a ∈ B) : a - b ∈ B := by
  rw [ZModModule.sub_eq_add, add_comm a b]
  exact h

/-- **B4b: the stage class is the ambient fundamental class** — `[fundCycleW₀] = [z₀]` in
`H_{k+1}(M | K)` (`ℤ/2`: their sum is a relative boundary, `fundCycleW_relHomologous`). -/
theorem fundCycleW₀_class_eq {k : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChain X (k + 0 + 1)) (hz₀ : chainBoundary X (k + 0) z₀ = 0)
    (K : CompactsIn W) :
    RelativeHomology.mk ((↑K.1 : Set ↑X)ᶜ) (k + 1)
        ⟨RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + 1) (fundCycleW₀ hW z₀ hz₀ K),
          relMk_mem_relCycles ((↑K.1 : Set ↑X)ᶜ) _ (fundCycleW₀_boundary hW z₀ hz₀ K)⟩
      = RelativeHomology.mk ((↑K.1 : Set ↑X)ᶜ) (k + 1)
          ⟨RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + 1) z₀,
            relMk_mem_relCycles ((↑K.1 : Set ↑X)ᶜ) _ (by
              rw [show chainBoundary X k z₀ = 0 from hz₀]; exact Submodule.zero_mem _)⟩ := by
  have hfund₀eq : fundCycleW₀ hW z₀ hz₀ K
      = fundCycleW (k := k) (m := 0) hW z₀ hz₀ K := by
    rw [fundCycleW₀, SingularOpenDualityMVConnSquare.castChain_eq]
  have hhom := fundCycleW_relHomologous (k := k) (m := 0) hW z₀ hz₀ K
  refine (Submodule.Quotient.eq _).mpr (Submodule.mem_comap.mpr ?_)
  show RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + 1) (fundCycleW₀ hW z₀ hz₀ K)
      - RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + 1) z₀
    ∈ relBoundaries ((↑K.1 : Set ↑X)ᶜ) (k + 1)
  have hhom' := hhom
  rw [← hfund₀eq] at hhom'
  exact mem_swap_sub _ _ hhom' 

omit [T2Space ↑X] in
/-- **The generic UC-flip**: if `H_{N+1}(M,S) ≅ ℤ/2` with `g` the generator, the Kronecker
pairing `⟨·, g⟩ : Hᴺ⁺¹(M,S) → ℤ/2` is bijective (the `manifoldLocalCohomologyIso` body pattern,
abstracted over the homology iso). Injectivity: `g` spans, so a class pairing to `0` with `g`
pairs to `0` with everything — relative UC kills it. Surjectivity: were the pairing zero, `g`
itself would die by the homology-side UC. -/
theorem relKroneckerH_flip_bijective_of_equiv {S : Set ↑X} {N : ℕ}
    (E : RelativeHomology S (N + 1) ≃ₗ[ZMod 2] ZMod 2)
    (g : RelativeHomology S (N + 1)) (hg : E g = 1) :
    Function.Bijective ⇑((relKroneckerH (X := X) S (N := N)).flip g) := by
  have hspan : ∀ β : RelativeHomology S (N + 1), (E β) • g = β := by
    intro β
    refine E.injective ?_
    rw [map_smul, hg, smul_eq_mul, mul_one]
  constructor
  · rw [injective_iff_map_eq_zero]
    intro ω hω
    rw [LinearMap.flip_apply] at hω
    refine SKEFTHawking.SingularRelativeUC.relCohomology_eq_zero_of_relKroneckerH
      (S := S) (N := N) ω (fun β => ?_)
    rw [← hspan β, map_smul, hω, smul_zero]
  · have hg_ne : g ≠ 0 := by
      intro h
      rw [h, map_zero] at hg
      exact one_ne_zero hg.symm
    have hΦne : ∃ ω, (relKroneckerH (X := X) S (N := N)).flip g ω ≠ 0 := by
      by_contra hall
      simp only [not_exists, not_not] at hall
      refine hg_ne (SKEFTHawking.SingularRelativeUC.relHomology_eq_zero_of_relKroneckerH
        (S := S) (N := N) g (fun ω => ?_))
      have := hall ω
      rwa [LinearMap.flip_apply] at this
    obtain ⟨ω₀, hω₀⟩ := hΦne
    have hz2 : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
    have hΦ1 : (relKroneckerH (X := X) S (N := N)).flip g ω₀ = 1 := hz2 _ hω₀
    intro y
    refine ⟨y • ω₀, ?_⟩
    have h1 : relKroneckerH (X := X) S (N := N) ω₀ g = 1 := hΦ1
    rw [map_smul, LinearMap.flip_apply, h1, smul_eq_mul, mul_one]

end SKEFTHawking.SingularBaseCaseD0
