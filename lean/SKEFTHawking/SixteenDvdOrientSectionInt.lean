/-
# Phase 5q.H — the σ÷16 leg over an ARBITRARY `±1` orientation section (the `orient ≡ 1` weakening)

The round-5 leg chain (`sixteen_dvd_latticeSigInt` → … → `sixteen_dvd_latticeSig_sphere4`) consumed
its orientation input as `hloc : ∀ x, ρ_x [M] = (localIsoComplInt x).symm 1` — the `+1`-pinned
restriction at every point, obtained from an `IntOrientationData` via the normalisation
`h1 : orient ≡ 1`. That normalisation is CHOICE-SENSITIVE for Mathlib's sphere atlas (the pinned
generator's sign at `x` carries the orientation of the per-point `stdOrthonormalBasis` choice —
see `SphereFourOrientationDataInt`), so no `orient ≡ 1` datum is constructible at S⁴ and the
normalised leg can never fire there.

This module weakens the whole chain to an arbitrary `±1` section — mathematically free, because the
leg's PD tower uses `hloc` ONLY through `E g = 1` for the generic integral UC-flip
(`relKroneckerHInt_flip_bijective_of_equiv`, generic in `E`), and a `±1` sign conjugates into `E`
(`exists_equiv_apply_eq_one_of_apply`: replace `E` by `E.trans (LinearEquiv.neg ℤ)` where
`orient x = -1`). Concretely, primed `±`-section variants of:

* §1 `exists_point_stage_hitInt'` — the D⁰ point-stage hit (`ε̄(D⁰β) = 1` EXACTLY, sign absorbed);
* §2/§3/§4 `openDuality₀_surjective/injective/bijective_of_chartConvexInt'` — B4c halves;
* §5 `hbaseConvG_of_localGenInt'`, §6 `openDuality_univ_bij_of_hcoreGInt'`,
  §7 `sixteen_dvd_latticeSig_of_hcoreGInt'`, §8 `sixteen_dvd_latticeSigInt'` — the leg spine;
* §9 `exists_leg_data'` + `sixteen_dvd_latticeSig_of_orientationData'` — fed by ANY
  `IntOrientationData` (the `h1 : orient ≡ 1` binder is GONE);
* §10 `sixteen_dvd_latticeSig_of_orientation_spin_free'` — the Kronecker-free spin form, no `h1`.

The proofs are the round-5 proofs verbatim with the sign-conjugation patch at the two
`E`-consumption sites; all downstream objects (`(relKroneckerHInt …).flip g`, the cap-equiv chain,
the intersection form) never see `E`, only the bijectivity certificate.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/
`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularSixteenDvdUnconditionalInt
import SKEFTHawking.SixteenDvdKronFree

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularCompactlySupportedOpenInt
open SKEFTHawking.SingularOpenDualityBotInt
open SKEFTHawking.SingularLocalDualityKBotInt
open SKEFTHawking.SingularRelativeUCInt
open SKEFTHawking.SingularLineMinusPointInt (augHInt)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularBaseCaseD0Int
open SKEFTHawking.SingularOpenDualityMVConnSquareInt (castChainInt castChainInt_eq
  chainBoundary_castChainInt_eq_zero)
open SKEFTHawking.SingularPDWindowInt (HcoreG HbaseConvG pdWindowPInt_of_chartConvex pdWindowPInt_univ)
open SKEFTHawking.SingularOpenDualityInt
open SKEFTHawking.IntOrientationSection
open SKEFTHawking.SingularPD4Instances
open SKEFTHawking.PoincareDualityWu (wuClass2)
open SKEFTHawking.SingularAbsoluteUCInt (kronH2OfFree kronH2OfFree_apply)
open SKEFTHawking.SingularReducedGeneratorInt (intLocalHomologyIso_of_manifold')

namespace SKEFTHawking.SixteenDvdOrientSectionInt

/-! ## §0. The sign-conjugation helper and the oriented-generator bridge -/

/-- **A `±1` value of a rank-1 iso conjugates to `1`**: if `E g = s` with `s = ±1`, some iso `E'`
(namely `E` or `E.trans (LinearEquiv.neg ℤ)`) has `E' g = 1`. The whole `orient ≡ 1` weakening
reduces to this: the leg's UC-flip is generic in the iso, so the sign is absorbed into it. -/
theorem exists_equiv_apply_eq_one_of_apply {A : Type*} [AddCommGroup A] [Module ℤ A]
    (E : A ≃ₗ[ℤ] ℤ) {g : A} {s : ℤ} (hs : s = 1 ∨ s = -1) (hg : E g = s) :
    ∃ E' : A ≃ₗ[ℤ] ℤ, E' g = 1 := by
  rcases hs with rfl | rfl
  · exact ⟨E, hg⟩
  · exact ⟨E.trans (LinearEquiv.neg ℤ), by rw [LinearEquiv.trans_apply, hg]; norm_num⟩

variable {M : Type} [TopologicalSpace M] [T2Space M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]

/-- **The oriented local generator at sign `s` is `s •` the `localIsoComplInt` generator** — the
general-`s` form of `SixteenDvdOfOrientation.orientedLocalGenerator_one` (`localIsoComplInt` is
definitionally `manifoldLocalHomologyIsoInt`). The bridge from `IntOrientationData.restricts` to
the leg's `±`-section `hloc`. -/
theorem orientedLocalGenerator_smul_localIsoCompl (x : M) (s : ℤ) :
    orientedLocalGenerator x s = s • (localIsoComplInt x).symm 1 := by
  rw [orientedLocalGenerator, SKEFTHawking.SingularRelHomologyInt.localGenerator]
  rfl

/-! ## §1. The D⁰ point-stage hit over a `±1` sign -/

/-- **A point-stage class whose `D⁰`-image has augmentation `1`, over a `±1`-signed local
restriction** — `SingularBaseCaseD0Int.exists_point_stage_hitInt` with `hloc` weakened to
`ρ_{x₀}[z₀] = s • (localIsoComplInt x₀).symm 1`, `s = ±1`. The sign conjugates into the UC-flip's
iso; the conclusion still hits `1` EXACTLY. -/
theorem exists_point_stage_hitInt' (x₀ : M)
    [Module.Free ℤ (RelHomologyInt (X := TopCat.of M) (({x₀} : Set ↑(TopCat.of M))ᶜ) 3)]
    [Module.Projective ℤ (relBoundariesInt (X := TopCat.of M) (({x₀} : Set ↑(TopCat.of M))ᶜ) 2)]
    [Module.Projective ℤ (relBoundariesInt (X := TopCat.of M) (({x₀} : Set ↑(TopCat.of M))ᶜ) 3)]
    {W : Set ↑(TopCat.of M)} (hWo : IsOpen W) (hx₀W : (x₀ : ↑(TopCat.of M)) ∈ W)
    (z₀ : SingularChainInt (TopCat.of M) (2 + 1 + 0 + 1))
    (hz₀ : chainBoundary (TopCat.of M) (2 + 1 + 0) z₀ = 0)
    (hcyc : z₀ ∈ cycles (TopCat.of M) (2 + 2))
    {s : ℤ} (hs : s = 1 ∨ s = -1)
    (hloc : SKEFTHawking.IntOrientationSection.restrictHomologyToPointInt (X := TopCat.of M) x₀
        (2 + 2) (Homology.mk (TopCat.of M) (2 + 2) ⟨z₀, hcyc⟩)
      = s • (localIsoComplInt x₀).symm 1) :
    ∃ β : CompactlySupportedCohomologyOpenInt W (2 + 1 + 1),
      augHInt (sub W) (openDuality₀Int (k := 2 + 1) hWo z₀ hz₀ β) = 1 := by
  set Kx : CompactsIn W :=
    ⟨⟨{x₀}, isCompact_singleton⟩, Set.singleton_subset_iff.mpr hx₀W⟩ with hKxdef
  have hzb : chainBoundary (TopCat.of M) (2 + 1) z₀
      ∈ subspaceChainsInt (({x₀} : Set ↑(TopCat.of M))ᶜ) (2 + 1) := by
    rw [show chainBoundary (TopCat.of M) (2 + 1) z₀ = 0 from hz₀]
    exact Submodule.zero_mem _
  have hgcls := restrictHomologyToSet_mkInt (K := ({x₀} : Set ↑(TopCat.of M))) z₀ hcyc hzb
  have hg_eq : RelHomologyInt.mk (X := TopCat.of M) (({x₀} : Set ↑(TopCat.of M))ᶜ) (2 + 2)
        ⟨RelativeChainInt.mk (({x₀} : Set ↑(TopCat.of M))ᶜ) (2 + 2) z₀,
          relMk_mem_relCyclesInt_of_boundary (({x₀} : Set ↑(TopCat.of M))ᶜ) z₀ hzb⟩
      = s • (localIsoComplInt x₀).symm 1 := hgcls.symm.trans hloc
  have hEval : localIsoComplInt x₀ (RelHomologyInt.mk (X := TopCat.of M)
        (({x₀} : Set ↑(TopCat.of M))ᶜ) (2 + 2)
        ⟨RelativeChainInt.mk (({x₀} : Set ↑(TopCat.of M))ᶜ) (2 + 2) z₀,
          relMk_mem_relCyclesInt_of_boundary (({x₀} : Set ↑(TopCat.of M))ᶜ) z₀ hzb⟩) = s := by
    rw [hg_eq, map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
  obtain ⟨E', hE'⟩ := exists_equiv_apply_eq_one_of_apply (localIsoComplInt x₀) hs hEval
  have hflip := relKroneckerHInt_flip_bijective_of_equiv
    (S := (({x₀} : Set ↑(TopCat.of M))ᶜ)) (M := 2) E' hE'
  obtain ⟨ω₀, hω₀⟩ := hflip.surjective 1
  obtain ⟨a₀, rfl⟩ := Submodule.Quotient.mk_surjective _ ω₀
  refine ⟨Module.DirectLimit.of ℤ (CompactsIn W) (cohomGWInt W (2 + 1 + 1))
    (cohomFWInt W (2 + 1 + 1)) Kx (Submodule.Quotient.mk a₀), ?_⟩
  rw [LinearMap.flip_apply] at hω₀
  exact (congrArg (fun t => augHInt (sub W) t)
      (openDuality₀Int_of hWo z₀ hz₀ Kx (Submodule.Quotient.mk a₀))).trans
    ((augH_legW₀_eq_relKroneckerHInt hWo z₀ hz₀ Kx a₀).trans
      ((congrArg (fun t => relKroneckerHInt (({x₀} : Set ↑(TopCat.of M))ᶜ)
          (RelativeCohomologyInt.mk (({x₀} : Set ↑(TopCat.of M))ᶜ) (2 + 1 + 1) a₀) t)
        (fundCycleW₀_class_eqInt hWo z₀ hz₀ Kx)).trans hω₀))

/-! ## §2. B4c surjectivity over a `±1` section -/

/-- **B4c surjectivity over a `±1` section** — `openDuality₀_surjective_of_chartConvexInt` with the
per-point `hloc` weakened to `ρ_x[z₀] = orient x • (localIsoComplInt x).symm 1` for a `±1`-valued
section `orient`. -/
theorem openDuality₀_surjective_of_chartConvexInt'
    (hfree3 : ∀ x : M,
      Module.Free ℤ (RelHomologyInt (X := TopCat.of M) (({x} : Set ↑(TopCat.of M))ᶜ) 3))
    {U : Set ↑(TopCat.of M)} {V : Set ↑(SKEFTHawking.SingularEuclideanAcyclic.Eucl 4)} (e : ↥U ≃ₜ ↥V)
    {C : Set (EuclideanSpace ℝ (Fin 4))} (hCconv : Convex ℝ C) (hCne : C.Nonempty) (hCV : C ⊆ V)
    {W : Set ↑(TopCat.of M)} (hWo : IsOpen W) (hWU : W ⊆ U)
    (hWe : ∀ u : ↥U, (u : ↑(TopCat.of M)) ∈ W ↔
      ((e u : ↑(SKEFTHawking.SingularEuclideanAcyclic.Eucl 4)) ∈ C))
    (z₀ : SingularChainInt (TopCat.of M) (2 + 1 + 0 + 1))
    (hz₀ : chainBoundary (TopCat.of M) (2 + 1 + 0) z₀ = 0)
    (hcyc : z₀ ∈ cycles (TopCat.of M) (2 + 2))
    {orient : M → ℤ} (hunit : ∀ x, orient x = 1 ∨ orient x = -1)
    (hloc : ∀ x : M, SKEFTHawking.IntOrientationSection.restrictHomologyToPointInt
        (X := TopCat.of M) x (2 + 2) (Homology.mk (TopCat.of M) (2 + 2) ⟨z₀, hcyc⟩)
      = orient x • (localIsoComplInt x).symm 1) :
    Function.Surjective (openDuality₀Int (k := 2 + 1) hWo z₀ hz₀) := by
  obtain ⟨p₀, hp₀⟩ := hCne
  set x₀ : M := ((e.symm ⟨p₀, hCV hp₀⟩ : ↥U) : ↑(TopCat.of M)) with hx₀def
  have hx₀W : (x₀ : ↑(TopCat.of M)) ∈ W :=
    (hWe _).mpr (by rw [e.apply_symm_apply]; exact hp₀)
  haveI := hfree3 x₀
  haveI := SKEFTHawking.SingularRelBoundariesProjectiveInt.relBoundariesInt_projective
    (({x₀} : Set ↑(TopCat.of M))ᶜ) 2
  haveI := SKEFTHawking.SingularRelBoundariesProjectiveInt.relBoundariesInt_projective
    (({x₀} : Set ↑(TopCat.of M))ᶜ) 3
  obtain ⟨β, hβ⟩ := exists_point_stage_hitInt' x₀ hWo hx₀W z₀ hz₀ hcyc (hunit x₀) (hloc x₀)
  haveI hpcsC : PathConnectedSpace
      ↑(sub (X := SKEFTHawking.SingularEuclideanAcyclic.Eucl 4) C) :=
    isPathConnected_iff_pathConnectedSpace.mp (hCconv.isPathConnected ⟨p₀, hp₀⟩)
  haveI hpcsW : PathConnectedSpace ↑(sub W) := by
    have φ := SKEFTHawking.SingularConvexSubAcyclic.chartSubHomeo (M := TopCat.of M) e hCV hWU hWe
    exact φ.symm.surjective.pathConnectedSpace φ.symm.continuous
  have hauginj : Function.Injective (augHInt (sub (X := TopCat.of M) W)) :=
    SKEFTHawking.SingularH0PathConnectedInt.augHInt_injective_pathConnected
  intro y
  refine ⟨(augHInt (sub (X := TopCat.of M) W) y) • β, hauginj ?_⟩
  rw [map_smul, map_smul, hβ, smul_eq_mul, mul_one]

/-! ## §3. B4c injectivity over a `±1` section -/

/-- **B4c injectivity over a `±1` section** — `openDuality₀_injective_of_chartConvexInt` with `hloc`
weakened to the `±1`-section form; the stage iso `E` picks up the stage point's sign and is
conjugated back to a `1`-witness before feeding the generic UC-flip. -/
theorem openDuality₀_injective_of_chartConvexInt'
    {U : Set ↑(TopCat.of M)} {V : Set ↑(SKEFTHawking.SingularEuclideanAcyclic.Eucl 4)}
    (hU : IsOpen U) (hV : IsOpen V) (e : ↥U ≃ₜ ↥V)
    {C : Set (EuclideanSpace ℝ (Fin 4))} (hCconv : Convex ℝ C) (hCopen : IsOpen C)
    {p₀ : EuclideanSpace ℝ (Fin 4)} (hp₀ : p₀ ∈ C) (hCV : C ⊆ V)
    {W : Set ↑(TopCat.of M)} (hWo : IsOpen W) (hWU : W ⊆ U)
    (hWe : ∀ u : ↥U, (u : ↑(TopCat.of M)) ∈ W ↔
      ((e u : ↑(SKEFTHawking.SingularEuclideanAcyclic.Eucl 4)) ∈ C))
    (z₀ : SingularChainInt (TopCat.of M) (2 + 1 + 0 + 1))
    (hz₀ : chainBoundary (TopCat.of M) (2 + 1 + 0) z₀ = 0)
    (hcyc : z₀ ∈ cycles (TopCat.of M) (2 + 2))
    {orient : M → ℤ} (hunit : ∀ x, orient x = 1 ∨ orient x = -1)
    (hloc : ∀ x : M, SKEFTHawking.IntOrientationSection.restrictHomologyToPointInt
        (X := TopCat.of M) x (2 + 2) (Homology.mk (TopCat.of M) (2 + 2) ⟨z₀, hcyc⟩)
      = orient x • (localIsoComplInt x).symm 1) :
    Function.Injective (openDuality₀Int (k := 2 + 1) hWo z₀ hz₀) := by
  haveI : T2Space ↑(TopCat.of M) := inferInstanceAs (T2Space M)
  rw [injective_iff_map_eq_zero]
  intro α
  induction α using Module.DirectLimit.induction_on with
  | ih K ω =>
    intro hα0
    obtain ⟨K', C', hKK', hC'conv, hC'comp, hC'C, hp₀C', hcompat'⟩ :=
      SKEFTHawking.SingularCSCConvexChart.exists_chartConvex_stage_above
        (M := TopCat.of M) e hCconv hCopen hp₀ hCV hWU hWe K
    obtain ⟨a', ha'⟩ := Submodule.Quotient.mk_surjective _
      (cohomFWInt (M := TopCat.of M) W (2 + 1 + 1) K K' hKK' ω)
    have hs1 : Module.DirectLimit.of ℤ (SKEFTHawking.SingularCompactsInOpen.CompactsIn W)
          (cohomGWInt (M := TopCat.of M) W (2 + 1 + 1)) (cohomFWInt (M := TopCat.of M) W (2 + 1 + 1))
          K' (Submodule.Quotient.mk a')
        = Module.DirectLimit.of ℤ (SKEFTHawking.SingularCompactsInOpen.CompactsIn W)
          (cohomGWInt (M := TopCat.of M) W (2 + 1 + 1)) (cohomFWInt (M := TopCat.of M) W (2 + 1 + 1))
          K ω :=
      (congrArg (fun t => Module.DirectLimit.of ℤ (SKEFTHawking.SingularCompactsInOpen.CompactsIn W)
          (cohomGWInt (M := TopCat.of M) W (2 + 1 + 1)) (cohomFWInt (M := TopCat.of M) W (2 + 1 + 1))
          K' t) ha').trans (Module.DirectLimit.of_f (hij := hKK') (x := ω))
    have hs3 := (congrArg (fun t => augHInt (sub (X := TopCat.of M) W)
        (openDuality₀Int (k := 2 + 1) hWo z₀ hz₀ t)) hs1).trans
      ((congrArg (fun t => augHInt (sub (X := TopCat.of M) W) t) hα0).trans (map_zero _))
    have hzb' : chainBoundary (TopCat.of M) (2 + 1) z₀
        ∈ subspaceChainsInt ((↑K'.1 : Set ↑(TopCat.of M))ᶜ) (2 + 1) := by
      rw [show chainBoundary (TopCat.of M) (2 + 1) z₀ = 0 from hz₀]
      exact Submodule.zero_mem _
    have hs5 := (((congrArg (fun t => augHInt (sub (X := TopCat.of M) W) t)
        (openDuality₀Int_of hWo z₀ hz₀ K' (Submodule.Quotient.mk a'))).trans
      ((augH_legW₀_eq_relKroneckerHInt hWo z₀ hz₀ K' a').trans
        (congrArg (fun t => relKroneckerHInt ((↑K'.1 : Set ↑(TopCat.of M))ᶜ)
            (RelativeCohomologyInt.mk ((↑K'.1 : Set ↑(TopCat.of M))ᶜ) (2 + 1 + 1) a') t)
          (fundCycleW₀_class_eqInt hWo z₀ hz₀ K')))).symm).trans hs3
    -- the chart-convex point `x₀' ∈ K'` and the point-restriction stage iso `E`
    obtain ⟨x₀', hx₀'K'⟩ : ∃ y : M, (y : ↑(TopCat.of M)) ∈ (↑K'.1 : Set ↑(TopCat.of M)) :=
      ⟨((e.symm ⟨p₀, hCV (hC'C hp₀C')⟩ : ↥U) : ↑(TopCat.of M)),
        (hcompat' _).mp (by rw [e.apply_symm_apply]; exact hp₀C')⟩
    haveI := SKEFTHawking.SingularConvexStageIsoInt.free_stage3_convexChartInt hU hV e
      (K'.1.isCompact'.isClosed) (K'.2.trans hWU) hC'conv hC'comp (hC'C.trans hCV) hp₀C' hcompat'
    haveI := SKEFTHawking.SingularRelBoundariesProjectiveInt.relBoundariesInt_projective
      ((↑K'.1 : Set ↑(TopCat.of M))ᶜ) 2
    haveI := SKEFTHawking.SingularRelBoundariesProjectiveInt.relBoundariesInt_projective
      ((↑K'.1 : Set ↑(TopCat.of M))ᶜ) 3
    have hrtp : SKEFTHawking.IntOrientationSection.restrictToPointInt hx₀'K' (2 + 2)
          (RelHomologyInt.mk ((↑K'.1 : Set ↑(TopCat.of M))ᶜ) (2 + 2)
            ⟨RelativeChainInt.mk ((↑K'.1 : Set ↑(TopCat.of M))ᶜ) (2 + 2) z₀,
              relMk_mem_relCyclesInt_of_boundary ((↑K'.1 : Set ↑(TopCat.of M))ᶜ) z₀ hzb'⟩)
        = orient x₀' • (localIsoComplInt x₀').symm 1 := by
      rw [show RelHomologyInt.mk ((↑K'.1 : Set ↑(TopCat.of M))ᶜ) (2 + 2)
              ⟨RelativeChainInt.mk ((↑K'.1 : Set ↑(TopCat.of M))ᶜ) (2 + 2) z₀,
                relMk_mem_relCyclesInt_of_boundary ((↑K'.1 : Set ↑(TopCat.of M))ᶜ) z₀ hzb'⟩
            = restrictHomologyToSetInt (↑K'.1 : Set ↑(TopCat.of M)) (2 + 2)
                (Homology.mk (TopCat.of M) (2 + 2) ⟨z₀, hcyc⟩)
          from (restrictHomologyToSet_mkInt (K := (↑K'.1 : Set ↑(TopCat.of M))) z₀ hcyc hzb').symm,
        restrictToPoint_restrictHomologyToSetInt hx₀'K' (2 + 2) _, hloc x₀']
    set E := (LinearEquiv.ofBijective
        (SKEFTHawking.IntOrientationSection.restrictToPointInt hx₀'K' (2 + 2))
        (SKEFTHawking.SingularChartBallBijectiveInt.restrictToPointInt_convexChart_bijective
          (K'.1.isCompact'.isClosed) hU (K'.2.trans hWU) hC'conv hC'comp hV (hC'C.trans hCV)
          e hcompat' hx₀'K')).trans (localIsoComplInt x₀') with hEdef
    have hEgs : E (RelHomologyInt.mk ((↑K'.1 : Set ↑(TopCat.of M))ᶜ) (2 + 2)
        ⟨RelativeChainInt.mk ((↑K'.1 : Set ↑(TopCat.of M))ᶜ) (2 + 2) z₀,
          relMk_mem_relCyclesInt_of_boundary ((↑K'.1 : Set ↑(TopCat.of M))ᶜ) z₀ hzb'⟩)
        = orient x₀' := by
      rw [hEdef, LinearEquiv.trans_apply, LinearEquiv.ofBijective_apply, hrtp, map_smul,
        LinearEquiv.apply_symm_apply, smul_eq_mul, mul_one]
    obtain ⟨E', hE'1⟩ := exists_equiv_apply_eq_one_of_apply E (hunit x₀') hEgs
    have hE := relKroneckerHInt_flip_bijective_of_equiv
      (S := ((↑K'.1 : Set ↑(TopCat.of M))ᶜ)) (M := 2) E' hE'1
    have hmk0 : (Submodule.Quotient.mk a'
        : RelativeCohomologyInt ((↑K'.1 : Set ↑(TopCat.of M))ᶜ) (2 + 1 + 1)) = 0 :=
      hE.injective (hs5.trans (map_zero _).symm)
    exact hs1.symm.trans ((congrArg (fun t => Module.DirectLimit.of ℤ
        (SKEFTHawking.SingularCompactsInOpen.CompactsIn W)
        (cohomGWInt (M := TopCat.of M) W (2 + 1 + 1)) (cohomFWInt (M := TopCat.of M) W (2 + 1 + 1))
        K' t) hmk0).trans (map_zero _))

/-! ## §4. B4c bijectivity over a `±1` section (zero-posit) -/

/-- **B4c bijectivity over a `±1` section** — the SURJ + INJ halves, freeness discharged inline
exactly as in the round-5 `openDuality₀_bijective_of_chartConvexInt`. -/
theorem openDuality₀_bijective_of_chartConvexInt'
    {U : Set ↑(TopCat.of M)} {V : Set ↑(SKEFTHawking.SingularEuclideanAcyclic.Eucl 4)}
    (hU : IsOpen U) (hV : IsOpen V) (e : ↥U ≃ₜ ↥V)
    {C : Set (EuclideanSpace ℝ (Fin 4))} (hCconv : Convex ℝ C) (hCopen : IsOpen C)
    {p₀ : EuclideanSpace ℝ (Fin 4)} (hp₀ : p₀ ∈ C) (hCV : C ⊆ V)
    {W : Set ↑(TopCat.of M)} (hWo : IsOpen W) (hWU : W ⊆ U)
    (hWe : ∀ u : ↥U, (u : ↑(TopCat.of M)) ∈ W ↔
      ((e u : ↑(SKEFTHawking.SingularEuclideanAcyclic.Eucl 4)) ∈ C))
    (z₀ : SingularChainInt (TopCat.of M) (2 + 1 + 0 + 1))
    (hz₀ : chainBoundary (TopCat.of M) (2 + 1 + 0) z₀ = 0)
    (hcyc : z₀ ∈ cycles (TopCat.of M) (2 + 2))
    {orient : M → ℤ} (hunit : ∀ x, orient x = 1 ∨ orient x = -1)
    (hloc : ∀ x : M, SKEFTHawking.IntOrientationSection.restrictHomologyToPointInt
        (X := TopCat.of M) x (2 + 2) (Homology.mk (TopCat.of M) (2 + 2) ⟨z₀, hcyc⟩)
      = orient x • (localIsoComplInt x).symm 1) :
    Function.Bijective (openDuality₀Int (k := 2 + 1) hWo z₀ hz₀) :=
  ⟨openDuality₀_injective_of_chartConvexInt' hU hV e hCconv hCopen hp₀ hCV hWo hWU hWe
      z₀ hz₀ hcyc hunit hloc,
    openDuality₀_surjective_of_chartConvexInt'
      (fun x => SKEFTHawking.SingularLocalHomologyThreeInt.free_relHomologyThreeInt x)
      e hCconv ⟨p₀, hp₀⟩ hCV hWo hWU hWe z₀ hz₀ hcyc hunit hloc⟩

/-! ## §5–§8. The leg spine over a `±1` section -/

/-- **`hbaseConvG` over a `±1` section** — `hbaseConvG_of_localGenInt` with the weakened `hloc`. -/
theorem hbaseConvG_of_localGenInt'
    (zM : SingularChainInt (TopCat.of M) (1 + 0 + 3))
    (hzM : chainBoundary (TopCat.of M) (1 + 0 + 2) zM = 0)
    (hcyc : castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM
      ∈ cycles (TopCat.of M) (2 + 2))
    {orient : M → ℤ} (hunit : ∀ x, orient x = 1 ∨ orient x = -1)
    (hloc : ∀ x : M, SKEFTHawking.IntOrientationSection.restrictHomologyToPointInt
        (X := TopCat.of M) x (2 + 2)
        (Homology.mk (TopCat.of M) (2 + 2)
          ⟨castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM, hcyc⟩)
      = orient x • (localIsoComplInt x).symm 1) :
    HbaseConvG M zM hzM := by
  intro U' V' hU' hV' e' W hWo hWU' Cw hCwconv hCwopen pw hpw hCwV hWe'
  exact pdWindowPInt_of_chartConvex
    (fun S j => SKEFTHawking.SingularRelBoundariesProjectiveInt.relBoundariesInt_projective S j)
    hU' hV' e' hCwconv hCwopen hpw hCwV hWo hWU' hWe' zM hzM
    (openDuality₀_bijective_of_chartConvexInt'
      hU' hV' e' hCwconv hCwopen hpw hCwV hWo hWU' hWe'
      (castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM)
      (chainBoundary_castChainInt_eq_zero (by omega) (by omega) zM hzM) hcyc hunit hloc)

variable [CompactSpace M]

/-- **The `(2,1)`-window openDuality on `univ` is bijective over a `±1` section** —
`openDuality_univ_bij_of_hcoreGInt` with the weakened orientation input. -/
theorem openDuality_univ_bij_of_hcoreGInt'
    (zM : SingularChainInt (TopCat.of M) (1 + 0 + 3))
    (hzM : chainBoundary (TopCat.of M) (1 + 0 + 2) zM = 0)
    (hcoreG : HcoreG M zM hzM)
    (hcyc : castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM
      ∈ cycles (TopCat.of M) (2 + 2))
    {orient : M → ℤ} (hunit : ∀ x, orient x = 1 ∨ orient x = -1)
    (hloc : ∀ x : M, SKEFTHawking.IntOrientationSection.restrictHomologyToPointInt
        (X := TopCat.of M) x (2 + 2)
        (Homology.mk (TopCat.of M) (2 + 2)
          ⟨castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM, hcyc⟩)
      = orient x • (localIsoComplInt x).symm 1) :
    Function.Bijective
      (openDuality (k := 1 + 1) (m := 0 + 1)
        (isOpen_univ : IsOpen (Set.univ : Set ↑(TopCat.of M)))
        (castChainInt (show (1 : ℕ) + 0 + 3 = 1 + 1 + (0 + 1) + 1 by omega) zM)
        (chainBoundary_castChainInt_eq_zero (by omega) (by omega) zM hzM)) :=
  (pdWindowPInt_univ zM hzM hcoreG
    (hbaseConvG_of_localGenInt' zM hzM hcyc hunit hloc)
    isOpen_univ).1

/-- **The assembled integral σ÷16 leg over a `±1` section** — `sixteen_dvd_latticeSig_of_hcoreGInt`
with the weakened orientation input. -/
theorem sixteen_dvd_latticeSig_of_hcoreGInt'
    (zM : SingularChainInt (TopCat.of M) (1 + 0 + 3))
    (hzM : chainBoundary (TopCat.of M) (1 + 0 + 2) zM = 0)
    (hcoreG : HcoreG M zM hzM)
    (hcyc : castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM
      ∈ cycles (TopCat.of M) (2 + 2))
    {orient : M → ℤ} (hunit : ∀ x, orient x = 1 ∨ orient x = -1)
    (hloc : ∀ x : M, SKEFTHawking.IntOrientationSection.restrictHomologyToPointInt
        (X := TopCat.of M) x (2 + 2)
        (Homology.mk (TopCat.of M) (2 + 2)
          ⟨castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM, hcyc⟩)
      = orient x • (localIsoComplInt x).symm 1)
    (kron : Homology (TopCat.of M) 2 ≃ₗ[ℤ] Module.Dual ℤ (Cohomology (TopCat.of M) 2))
    (hkron : ∀ (h : Homology (TopCat.of M) 2) (b : Cohomology (TopCat.of M) 2),
      kron h b = kroneckerHInt 2 b h)
    (B : IntH2Basis (TopCat.of M))
    (D : SpinWuDatum (intFundamentalClassOfHomology (Homology.mk (TopCat.of M) (2 + 1 + 1)
        ⟨castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 1 by omega) zM,
          chainBoundary_castChainInt_eq_zero (b := 2 + 1) (by omega) (by omega) zM hzM⟩)))
    (htopo : (2 : ℤ) ∣ latticeSig (interMatrix (intFundamentalClassOfHomology
        (Homology.mk (TopCat.of M) (2 + 1 + 1)
          ⟨castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 1 by omega) zM,
            chainBoundary_castChainInt_eq_zero (b := 2 + 1) (by omega) (by omega) zM hzM⟩)) B) / 8) :
    (16 : ℤ) ∣ latticeSig (interMatrix (intFundamentalClassOfHomology
        (Homology.mk (TopCat.of M) (2 + 1 + 1)
          ⟨castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 1 by omega) zM,
            chainBoundary_castChainInt_eq_zero (b := 2 + 1) (by omega) (by omega) zM hzM⟩)) B) :=
  SKEFTHawking.SingularIntCapEquivAssembly.sixteen_dvd_latticeSig_of_capEquiv
    (isOpen_univ : IsOpen (Set.univ : Set ↑(TopCat.of M)))
    (castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 1 by omega) zM)
    (chainBoundary_castChainInt_eq_zero (b := 2 + 1) (by omega) (by omega) zM hzM)
    (openDuality_univ_bij_of_hcoreGInt' zM hzM hcoreG hcyc hunit hloc) kron hkron B D htopo

/-- **The integral σ÷16 leg, PD-input-free, over a `±1` section** — `sixteen_dvd_latticeSigInt`
with the weakened orientation input (`hcoreG` supplied intrinsically). -/
theorem sixteen_dvd_latticeSigInt'
    (zM : SingularChainInt (TopCat.of M) (1 + 0 + 3))
    (hzM : chainBoundary (TopCat.of M) (1 + 0 + 2) zM = 0)
    (hcyc : castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM
      ∈ cycles (TopCat.of M) (2 + 2))
    {orient : M → ℤ} (hunit : ∀ x, orient x = 1 ∨ orient x = -1)
    (hloc : ∀ x : M, SKEFTHawking.IntOrientationSection.restrictHomologyToPointInt
        (X := TopCat.of M) x (2 + 2)
        (Homology.mk (TopCat.of M) (2 + 2)
          ⟨castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM, hcyc⟩)
      = orient x • (localIsoComplInt x).symm 1)
    (kron : Homology (TopCat.of M) 2 ≃ₗ[ℤ] Module.Dual ℤ (Cohomology (TopCat.of M) 2))
    (hkron : ∀ (h : Homology (TopCat.of M) 2) (b : Cohomology (TopCat.of M) 2),
      kron h b = kroneckerHInt 2 b h)
    (B : IntH2Basis (TopCat.of M))
    (D : SpinWuDatum (intFundamentalClassOfHomology (Homology.mk (TopCat.of M) (2 + 1 + 1)
        ⟨castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 1 by omega) zM,
          chainBoundary_castChainInt_eq_zero (b := 2 + 1) (by omega) (by omega) zM hzM⟩)))
    (htopo : (2 : ℤ) ∣ latticeSig (interMatrix (intFundamentalClassOfHomology
        (Homology.mk (TopCat.of M) (2 + 1 + 1)
          ⟨castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 1 by omega) zM,
            chainBoundary_castChainInt_eq_zero (b := 2 + 1) (by omega) (by omega) zM hzM⟩)) B) / 8) :
    (16 : ℤ) ∣ latticeSig (interMatrix (intFundamentalClassOfHomology
        (Homology.mk (TopCat.of M) (2 + 1 + 1)
          ⟨castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 1 by omega) zM,
            chainBoundary_castChainInt_eq_zero (b := 2 + 1) (by omega) (by omega) zM hzM⟩)) B) :=
  sixteen_dvd_latticeSig_of_hcoreGInt' zM hzM
    (SKEFTHawking.SingularHcoreGDischargeInt.hcoreG_intrinsicInt zM hzM) hcyc hunit hloc
    kron hkron B D htopo

/-! ## §9–§10. The leg fed by ANY orientation datum (no `orient ≡ 1` binder) -/

variable [Nonempty M]

set_option linter.unusedVariables false in
/-- **The leg's fundamental-cycle data from ANY orientation datum** — `exists_leg_data` without the
`h1 : orient ≡ 1` normalisation: the local-generator property carries the datum's own `±1` section
(via `orientedLocalGenerator_smul_localIsoCompl`). -/
theorem exists_leg_data' (d : IntOrientationData M) :
    ∃ (zM : SingularChainInt (TopCat.of M) (1 + 0 + 3))
      (hzM : chainBoundary (TopCat.of M) (1 + 0 + 2) zM = 0)
      (hcyc : castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM
        ∈ cycles (TopCat.of M) (2 + 2)),
      (∀ x : M, SKEFTHawking.IntOrientationSection.restrictHomologyToPointInt
          (X := TopCat.of M) x (2 + 2)
          (Homology.mk (TopCat.of M) (2 + 2)
            ⟨castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM, hcyc⟩)
        = d.orient x • (localIsoComplInt x).symm 1)
      ∧ Homology.mk (TopCat.of M) (2 + 2)
          ⟨castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM, hcyc⟩
        = d.fundClass := by
  obtain ⟨zc, hzc⟩ := Submodule.Quotient.mk_surjective _ d.fundClass
  have hcast : castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega)
      (zc.1 : SingularChainInt (TopCat.of M) (1 + 0 + 3)) = zc.1 := by
    rw [castChainInt_eq]
  refine ⟨zc.1, LinearMap.mem_ker.mp zc.2, by rw [hcast]; exact zc.2, ?_, ?_⟩
  · intro x
    have hclass : Homology.mk (TopCat.of M) (2 + 2)
        ⟨castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zc.1,
          by rw [hcast]; exact zc.2⟩
        = d.fundClass :=
      (congrArg (Homology.mk (TopCat.of M) (2 + 2)) (Subtype.ext hcast)).trans hzc
    rw [hclass]
    have hres := d.restricts x
    rw [orientedLocalGenerator_smul_localIsoCompl] at hres
    exact hres
  · exact (congrArg (Homology.mk (TopCat.of M) (2 + 2)) (Subtype.ext hcast)).trans hzc

/-- **`16 ∣ σ` from ANY orientation datum** — `sixteen_dvd_latticeSig_of_orientationData` with the
`h1 : orient ≡ 1` binder GONE: the datum's own `±1` section threads the weakened leg. -/
theorem sixteen_dvd_latticeSig_of_orientationData' (d : IntOrientationData M)
    (kron : Homology (TopCat.of M) 2 ≃ₗ[ℤ] Module.Dual ℤ (Cohomology (TopCat.of M) 2))
    (hkron : ∀ (h : Homology (TopCat.of M) 2) (b : Cohomology (TopCat.of M) 2),
      kron h b = kroneckerHInt 2 b h)
    (B : IntH2Basis (TopCat.of M))
    (D : SpinWuDatum (intFundamentalClassOfHomology d.fundClass))
    (htopo : (2 : ℤ) ∣ latticeSig
      (interMatrix (intFundamentalClassOfHomology d.fundClass) B) / 8) :
    (16 : ℤ) ∣ latticeSig (interMatrix (intFundamentalClassOfHomology d.fundClass) B) := by
  obtain ⟨zM, hzM, hcyc, hloc, hclass⟩ := exists_leg_data' d
  have hcast' : castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 1 by omega) zM
      = castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 0 + 1 by omega) zM := by
    rw [castChainInt_eq]
  have hclass' : Homology.mk (TopCat.of M) (2 + 1 + 1)
      ⟨castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 1 by omega) zM,
        chainBoundary_castChainInt_eq_zero (b := 2 + 1) (by omega) (by omega) zM hzM⟩
      = d.fundClass :=
    (congrArg (Homology.mk (TopCat.of M) (2 + 2)) (Subtype.ext hcast')).trans hclass
  have hfc : intFundamentalClassOfHomology (Homology.mk (TopCat.of M) (2 + 1 + 1)
      ⟨castChainInt (show (1 : ℕ) + 0 + 3 = 2 + 1 + 1 by omega) zM,
        chainBoundary_castChainInt_eq_zero (b := 2 + 1) (by omega) (by omega) zM hzM⟩)
      = intFundamentalClassOfHomology d.fundClass :=
    congrArg intFundamentalClassOfHomology hclass'
  rw [← hfc] at D htopo ⊢
  exact sixteen_dvd_latticeSigInt' zM hzM hcyc d.orient_unit hloc kron hkron B D htopo

/-- **`16 ∣ σ` at a closed charted SPIN 4-manifold from ANY orientation datum — Kronecker binders
eliminated, `orient ≡ 1` binder eliminated.** The `±`-section mirror of
`SixteenDvdKronFree.sixteen_dvd_latticeSig_of_orientation_spin_free`: the spin-Wu datum from `hv2`
(`spinWuDatum_of_closed`, `h1`-free) and the Kronecker duality from the absolute integral UCT. -/
theorem sixteen_dvd_latticeSig_of_orientation_spin_free' (d : IntOrientationData M)
    [Module.Free ℤ (Homology (TopCat.of M) 1)]
    [Module.Projective ℤ (boundaries (TopCat.of M) 0)]
    [Module.Projective ℤ (boundaries (TopCat.of M) 1)]
    [Module.Free ℤ (Homology (TopCat.of M) 2)]
    [Module.Finite ℤ (Homology (TopCat.of M) 2)]
    (B : IntH2Basis (TopCat.of M))
    (hv2 : wuClass2 (poincareDual4Mid_of_closed (M := M)) = 0)
    (htopo : (2 : ℤ) ∣ latticeSig
      (interMatrix (intFundamentalClassOfHomology d.fundClass) B) / 8) :
    (16 : ℤ) ∣ latticeSig (interMatrix (intFundamentalClassOfHomology d.fundClass) B) :=
  sixteen_dvd_latticeSig_of_orientationData' d
    (kronH2OfFree (TopCat.of M)) (kronH2OfFree_apply (TopCat.of M)) B
    (SKEFTHawking.SpinWuDatumClosed.spinWuDatum_of_closed (intOrientationOfData d) hv2) htopo

end SKEFTHawking.SixteenDvdOrientSectionInt
