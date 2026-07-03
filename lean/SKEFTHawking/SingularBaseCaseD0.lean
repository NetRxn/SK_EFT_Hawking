import Mathlib
import SKEFTHawking.SingularOpenDualityBot
import SKEFTHawking.SingularConnSquareCloseChainMapBot
import SKEFTHawking.SingularLocalDuality
import SKEFTHawking.SingularReducedH0
import SKEFTHawking.SingularChartBridge
import SKEFTHawking.SingularH0PathConnected
import SKEFTHawking.SingularConvexSubAcyclic
import SKEFTHawking.SingularFundamentalClassExist

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
open SKEFTHawking.SingularCompactlySupportedOpen
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

omit [T2Space ↑X] in
/-- **The stage restriction of a cycle class, in chain-`mk` form** (the glue between the
class-level `restrictHomologyToSet` and the B4a/B4b chain-level stage objects): for a cycle `z`,
`ρ_K [z] = [z]_{M|K}`. -/
theorem restrictHomologyToSet_mk {K : Set ↑X} {k : ℕ}
    (z : SingularChain X (k + 1)) (hz : z ∈ cycles X (k + 1))
    (hzb : chainBoundary X k z ∈ subspaceChains (Kᶜ) k) :
    SKEFTHawking.SingularFundamentalClass.restrictHomologyToSet K (k + 1)
        (Homology.mk X (k + 1) ⟨z, hz⟩)
      = RelativeHomology.mk (Kᶜ) (k + 1)
          ⟨RelativeChain.mk (Kᶜ) (k + 1) z, relMk_mem_relCycles (Kᶜ) z hzb⟩ := by
  rw [SKEFTHawking.SingularFundamentalClass.restrictHomologyToSet, LinearMap.comp_apply]
  erw [SingularRelativeMV.relIncl_mk]
  congr 1
  apply Subtype.ext
  simp [SingularRelativeFunctoriality.relCyclesMap]
  erw [show (↑((SingularRelativeEmpty.cyclesEmptyEquiv (k + 1)).symm ⟨z, hz⟩)
        : RelativeChain (∅ : Set ↑X) (k + 1)) = RelativeChain.mk ∅ (k + 1) z from rfl,
    SingularRelativeFunctoriality.relMapChain_mk, SingularFunctoriality.mapChain_id]

omit [T2Space ↑X] in
/-- Propositional set-congruence on relative homology (both `relIncl`s over a set equality;
NO raw defeq across set spellings — the `{x}ᶜ ↔ {y|y≠x}` seam killer). -/
private noncomputable def relHomologySetCongr {S T : Set ↑X} (hST : S ⊆ T) (hTS : T ⊆ S)
    (n : ℕ) : RelativeHomology S n ≃ₗ[ZMod 2] RelativeHomology T n :=
  LinearEquiv.ofLinear (SingularRelativeMV.relIncl hST n) (SingularRelativeMV.relIncl hTS n)
    (LinearMap.ext fun p =>
      SKEFTHawking.SingularFundamentalClass.relIncl_leftInverse hTS hST n p)
    (LinearMap.ext fun p =>
      SKEFTHawking.SingularFundamentalClass.relIncl_leftInverse hST hTS n p)

open SKEFTHawking.SingularChartBridge in
/-- The local iso at the `{x}ᶜ`-spelling (the seam paid ONCE, propositionally). -/
private noncomputable def localIsoCompl {m : ℕ} {M : Type} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] (x : M) :
    RelativeHomology (X := TopCat.of M) (({x} : Set M)ᶜ) (m + 2) ≃ₗ[ZMod 2] ZMod 2 :=
  (relHomologySetCongr (X := TopCat.of M)
    (fun y hy => by simpa using hy) (fun y hy => by simpa using hy) (m + 2)).trans
    (manifoldLocalIso x)

open SKEFTHawking.SingularChartBridge in
/-- Fresh-budget helper: a relative class equal to the local generator has
`localIsoCompl`-value `1` (the nonvanishing juggle, paid on its own heartbeat budget). -/
private theorem localIsoCompl_eq_one {m : ℕ} {M : Type} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] (x₀ : M)
    (g : RelativeHomology (X := TopCat.of M) (({x₀} : Set M)ᶜ) (m + 2))
    (hg : g = (manifoldLocalIso x₀).symm 1) :
    localIsoCompl x₀ g = 1 := by
  have hne : localIsoCompl x₀ g ≠ 0 := by
    intro h
    have hg0 : g = 0 := (LinearEquiv.map_eq_zero_iff _).mp h
    rw [hg] at hg0
    exact one_ne_zero (((manifoldLocalIso x₀).symm.map_eq_zero_iff).mp hg0)
  have hz2 : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  exact hz2 _ hne

open SKEFTHawking.SingularChartBridge in
/-- A point-stage class whose `D⁰`-image has augmentation `1` (fresh-budget; the seam crossed
only at the nonvanishing `Eq`). -/
private theorem exists_point_stage_hit {m : ℕ} {M : Type} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
    {W : Set ↑(TopCat.of M)} (hWo : IsOpen W) (x₀ : M) (hx₀W : x₀ ∈ W)
    (z₀ : SingularChain (TopCat.of M) (m + 1 + 0 + 1))
    (hz₀ : chainBoundary (TopCat.of M) (m + 1 + 0) z₀ = 0)
    (hcyc : z₀ ∈ cycles (TopCat.of M) (m + 2))
    (hloc : SKEFTHawking.SingularFundamentalClass.restrictHomologyToPoint
        (X := TopCat.of M) x₀ (m + 2) (Homology.mk (TopCat.of M) (m + 2) ⟨z₀, hcyc⟩)
      = (manifoldLocalIso x₀).symm 1) :
    ∃ β : CompactlySupportedCohomologyOpen (M := TopCat.of M) W (m + 1 + 1),
      augH (sub (X := TopCat.of M) W) (openDuality₀ (k := m + 1) (X := TopCat.of M) hWo z₀ hz₀ β) = 1 := by
  set Kx : SKEFTHawking.SingularCompactsInOpen.CompactsIn W :=
    ⟨⟨{x₀}, isCompact_singleton⟩, Set.singleton_subset_iff.mpr hx₀W⟩ with hKxdef
  have hzb : chainBoundary (TopCat.of M) (m + 1) z₀
      ∈ subspaceChains (({x₀} : Set M)ᶜ) (m + 1) := by
    rw [show chainBoundary (TopCat.of M) (m + 1) z₀ = 0 from hz₀]
    exact Submodule.zero_mem _
  -- The stage class is nonzero: it equals the local generator (hloc, seam crossed at Eq only).
  have hgcls := restrictHomologyToSet_mk (X := TopCat.of M) (K := ({x₀} : Set M)) z₀ hcyc hzb
  have hg_eq := hgcls.symm.trans hloc
  have hflip := relKroneckerH_flip_bijective_of_equiv (X := TopCat.of M)
    (S := (({x₀} : Set M)ᶜ)) (N := m + 1)
    (localIsoCompl x₀)
    _ (localIsoCompl_eq_one x₀ _ hg_eq)
  obtain ⟨ω₀, hω₀⟩ := hflip.surjective 1
  obtain ⟨a₀, rfl⟩ := Submodule.Quotient.mk_surjective _ ω₀
  refine ⟨Module.DirectLimit.of (ZMod 2)
    (SKEFTHawking.SingularCompactsInOpen.CompactsIn W)
    (cohomGW (M := TopCat.of M) W (m + 1 + 1)) (cohomFW (M := TopCat.of M) W (m + 1 + 1))
    Kx (Submodule.Quotient.mk a₀), ?_⟩
  exact (congrArg (fun t => augH (sub (X := TopCat.of M) W) t)
      (openDuality₀_of hWo z₀ hz₀ Kx (Submodule.Quotient.mk a₀))).trans
    ((augH_legW₀_eq_relKroneckerH hWo z₀ hz₀ Kx a₀).trans
      ((congrArg (fun t => relKroneckerH (X := TopCat.of M) ((↑Kx.1 : Set ↑(TopCat.of M))ᶜ)
          (RelativeCohomology.mk ((↑Kx.1 : Set ↑(TopCat.of M))ᶜ) (m + 1 + 1) a₀) t)
        (fundCycleW₀_class_eq hWo z₀ hz₀ Kx)).trans hω₀))

open SKEFTHawking.SingularChartBridge SKEFTHawking.SingularH0PathConnected in
/-- **B4c (surjectivity half)**: the `D⁰` duality of a chart-convex open is surjective. -/
theorem openDuality₀_surjective_of_chartConvex {m : ℕ} {M : Type} [TopologicalSpace M]
    [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
    {U : Set M} {V : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))}
    (e : ↥U ≃ₜ ↥V)
    {C : Set (EuclideanSpace ℝ (Fin (m + 2)))} (hCconv : Convex ℝ C) (hCne : C.Nonempty)
    (hCV : C ⊆ V)
    {W : Set M} (hWo : IsOpen W) (hWU : W ⊆ U)
    (hWe : ∀ u : ↥U, (u : M) ∈ W ↔ ((e u : ↑(SingularEuclideanAcyclic.Eucl (m + 2))) ∈ C))
    (z₀ : SingularChain (TopCat.of M) (m + 1 + 0 + 1))
    (hz₀ : chainBoundary (TopCat.of M) (m + 1 + 0) z₀ = 0)
    (hcyc : z₀ ∈ cycles (TopCat.of M) (m + 2))
    (hloc : ∀ x : M, SKEFTHawking.SingularFundamentalClass.restrictHomologyToPoint
        (X := TopCat.of M) x (m + 2) (Homology.mk (TopCat.of M) (m + 2) ⟨z₀, hcyc⟩)
      = (manifoldLocalIso x).symm 1) :
    Function.Surjective (openDuality₀ (k := m + 1) (X := TopCat.of M) hWo z₀ hz₀) := by
  obtain ⟨p₀, hp₀⟩ := hCne
  have hx₀W : ((e.symm ⟨p₀, hCV hp₀⟩ : ↥U) : M) ∈ W :=
    (hWe _).mpr (by rw [e.apply_symm_apply]; exact hp₀)
  obtain ⟨β, hβ⟩ := exists_point_stage_hit hWo _ hx₀W z₀ hz₀ hcyc (hloc _)
  haveI hpcsC : PathConnectedSpace
      ↑(sub (X := SingularEuclideanAcyclic.Eucl (m + 2)) C) :=
    isPathConnected_iff_pathConnectedSpace.mp (hCconv.isPathConnected ⟨p₀, hp₀⟩)
  haveI hpcsW : PathConnectedSpace ↑(sub W) := by
    have φ := SKEFTHawking.SingularConvexSubAcyclic.chartSubHomeo (M := TopCat.of M) e hCV hWU hWe
    exact φ.symm.surjective.pathConnectedSpace φ.symm.continuous
  have hauginj : Function.Injective (augH (sub (X := TopCat.of M) W)) := augH_injective
  intro y
  refine ⟨(augH (sub (X := TopCat.of M) W) y) • β, hauginj ?_⟩
  rw [map_smul, map_smul, hβ, smul_eq_mul, mul_one]

end SKEFTHawking.SingularBaseCaseD0