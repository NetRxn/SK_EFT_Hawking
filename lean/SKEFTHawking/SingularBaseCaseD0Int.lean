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
import SKEFTHawking.SingularLocalHomologyIsoInt
import SKEFTHawking.SingularGoodCompactUnionInt
import SKEFTHawking.SingularRelBoundariesProjectiveInt
import SKEFTHawking.SingularConvexSubAcyclic
import SKEFTHawking.SingularH0PathConnectedInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularCompactlySupportedOpenInt
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

/-! ## §5. The stage-restriction glue -/

/-- **Restriction of an absolute class to the local homology over a set** (integral)
`ρ_K : Hₙ(M;ℤ) → Hₙ(M | K;ℤ)`, the projection `homProjInt (Kᶜ)`. Integral mirror of
`SingularFundamentalClass.restrictHomologyToSet` (`restrictHomologyToPointInt`'s set analogue). -/
noncomputable def restrictHomologyToSetInt (K : Set ↑X) (n : ℕ) :
    Homology X n →ₗ[ℤ] RelHomologyInt (Kᶜ : Set ↑X) n :=
  homProjInt (Kᶜ : Set ↑X) n

omit [T2Space ↑X] in
/-- **The stage restriction of a cycle class, in chain-`mk` form** (integral): `ρ_K [z] = [z]_{M|K}`.
Integral mirror of `SingularBaseCaseD0.restrictHomologyToSet_mk`. -/
theorem restrictHomologyToSet_mkInt {K : Set ↑X} {k : ℕ}
    (z : SingularChainInt X (k + 1)) (hz : z ∈ cycles X (k + 1))
    (hzb : chainBoundary X k z ∈ subspaceChainsInt (Kᶜ : Set ↑X) k) :
    restrictHomologyToSetInt K (k + 1) (Homology.mk X (k + 1) ⟨z, hz⟩)
      = RelHomologyInt.mk (Kᶜ : Set ↑X) (k + 1)
          ⟨RelativeChainInt.mk (Kᶜ : Set ↑X) (k + 1) z,
            relMk_mem_relCyclesInt_of_boundary (Kᶜ : Set ↑X) z hzb⟩ := by
  rw [restrictHomologyToSetInt, homProjInt_mk]

/-! ## §6. The local iso at the `{x}ᶜ`-spelling -/

open SKEFTHawking.IntOrientationSection (relInclInt)

/-- **Propositional set-congruence on relative homology** (integral): both `relInclInt`s over a mutual
set inclusion, left/right inverse by `relInclInt_roundtrip`. The `{x}ᶜ = {y | y ≠ x}` seam killer (integral
mirror of `SingularConvexStageIso.relHomologySetCongr`). -/
noncomputable def relHomologySetCongrInt {S T : Set ↑X} (hST : S ⊆ T) (hTS : T ⊆ S) (n : ℕ) :
    RelHomologyInt S n ≃ₗ[ℤ] RelHomologyInt T n :=
  LinearEquiv.ofLinear (relInclInt hST n) (relInclInt hTS n)
    (LinearMap.ext fun p =>
      SKEFTHawking.SingularGoodCompactUnionInt.relInclInt_roundtrip hTS hST n p)
    (LinearMap.ext fun p =>
      SKEFTHawking.SingularGoodCompactUnionInt.relInclInt_roundtrip hST hTS n p)

/-- **The local homology iso at the `{x}ᶜ`-spelling** `H₄(M | x; ℤ) ≅ ℤ` — `manifoldLocalHomologyIsoInt`
transported across the `{x}ᶜ = {y | y ≠ x}` seam (paid once, propositionally). The `E` of the chart-convex
point stage. -/
noncomputable def localIsoComplInt {M : Type} [TopologicalSpace M] [T1Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] (x : M) :
    RelHomologyInt (X := TopCat.of M) (({x} : Set ↑(TopCat.of M))ᶜ) 4 ≃ₗ[ℤ] ℤ :=
  SKEFTHawking.SingularLocalHomologyIsoInt.manifoldLocalHomologyIsoInt x

/-- **The local-iso value of the generator is `1`** (integral, EXACT — no mod-2 `≠0⟹=1` juggle): if `g`
is the `localIsoComplInt`-generator (`g = E.symm 1`), then `E g = 1`. The flip's `hg` at the point stage. -/
theorem localIsoCompl_eq_oneInt {M : Type} [TopologicalSpace M] [T1Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] (x₀ : M)
    {g : RelHomologyInt (X := TopCat.of M) (({x₀} : Set ↑(TopCat.of M))ᶜ) 4}
    (hg : g = (localIsoComplInt x₀).symm 1) : localIsoComplInt x₀ g = 1 := by
  rw [hg, LinearEquiv.apply_symm_apply]

/-! ## §7. The point-stage hit (B4c surjectivity ingredient) -/

/-- **A point-stage class whose `D⁰`-image has augmentation `1`** (integral, `m = 2`): for a fundamental
cycle `z₀` restricting to the local generator at `x₀ ∈ W`, some compactly-supported cohomology class `β`
has `ε̄(D⁰_W β) = 1`. The `D⁰`-surjectivity witness. The flip's freeness prereqs `[Free H₃(M|x₀)]` +
`[Proj B₂/B₃]` are carried as instance hypotheses (`euclSourceIso` convention; dischargeable via
`H₃(ℝ⁴|0)=0` + Kaplansky). Integral mirror of `SingularBaseCaseD0.exists_point_stage_hit`. -/
theorem exists_point_stage_hitInt {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] (x₀ : M)
    [Module.Free ℤ (RelHomologyInt (X := TopCat.of M) (({x₀} : Set ↑(TopCat.of M))ᶜ) 3)]
    [Module.Projective ℤ (relBoundariesInt (X := TopCat.of M) (({x₀} : Set ↑(TopCat.of M))ᶜ) 2)]
    [Module.Projective ℤ (relBoundariesInt (X := TopCat.of M) (({x₀} : Set ↑(TopCat.of M))ᶜ) 3)]
    {W : Set ↑(TopCat.of M)} (hWo : IsOpen W) (hx₀W : (x₀ : ↑(TopCat.of M)) ∈ W)
    (z₀ : SingularChainInt (TopCat.of M) (2 + 1 + 0 + 1))
    (hz₀ : chainBoundary (TopCat.of M) (2 + 1 + 0) z₀ = 0)
    (hcyc : z₀ ∈ cycles (TopCat.of M) (2 + 2))
    (hloc : SKEFTHawking.IntOrientationSection.restrictHomologyToPointInt (X := TopCat.of M) x₀ (2 + 2)
        (Homology.mk (TopCat.of M) (2 + 2) ⟨z₀, hcyc⟩)
      = (localIsoComplInt x₀).symm 1) :
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
      = (localIsoComplInt x₀).symm 1 := hgcls.symm.trans hloc
  have hflip := relKroneckerHInt_flip_bijective_of_equiv
    (S := (({x₀} : Set ↑(TopCat.of M))ᶜ)) (M := 2)
    (localIsoComplInt x₀) (localIsoCompl_eq_oneInt x₀ hg_eq)
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

/-! ## §8. B4c surjectivity — the `D⁰` duality of a chart-convex open is surjective -/

/-- **B4c (surjectivity half)** (integral): the `D⁰` duality of a chart-convex open is surjective. Pick the
convex point `p₀`; `exists_point_stage_hitInt` gives a `β` with `ε̄(D⁰β) = 1`; since `sub W` is
path-connected (chart-homeomorphic to the convex `C`), `ε̄` is injective, so `y = ε̄(y)•β` maps under `D⁰`
to `y`. Carries the `∀ x, [Free H₃(M|x)]` freeness (`euclSourceIso` convention); the boundary
projectivities are discharged inline via Kaplansky. Integral mirror of
`SingularBaseCaseD0.openDuality₀_surjective_of_chartConvex`. -/
theorem openDuality₀_surjective_of_chartConvexInt {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
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
    (hloc : ∀ x : M, SKEFTHawking.IntOrientationSection.restrictHomologyToPointInt
        (X := TopCat.of M) x (2 + 2) (Homology.mk (TopCat.of M) (2 + 2) ⟨z₀, hcyc⟩)
      = (localIsoComplInt x).symm 1) :
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
  obtain ⟨β, hβ⟩ := exists_point_stage_hitInt x₀ hWo hx₀W z₀ hz₀ hcyc (hloc x₀)
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

end SKEFTHawking.SingularBaseCaseD0Int
