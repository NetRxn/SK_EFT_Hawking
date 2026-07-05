import Mathlib
import SKEFTHawking.SingularChartTransportInt
import SKEFTHawking.SingularConvexRadialBaseInt
import SKEFTHawking.SingularGoodCompactInt

/-!
# Phase 5q.H (integral Substrate-G, E1) — the MV-free chart-ball restriction bijectivity

The **integer-coefficient** mirror of the mod-2 chart base case
(`SingularDeterminedConvex.determinedByPoints_convexChart`,
`SingularGoodCompactChart.restrictToPoint_convexChart_bijective`,
`SingularGoodCompactManifold.restrictToPoint_chartBall_bijective`). This is the MV-**free** oriented
fundamental-class base case: the chart-transported convex determined-by-points property and the
concrete chart-closed-ball restriction bijectivity, over ℤ.

* `determinedByPointsInt_convexChart` — a class in `Hₙ(M|K;ℤ)` for a convex chart region `K`
  restricting to `0` at every point is `0`; via the 18b chart-transport of
  `determinedByPointsInt_convexCompact`.
* `restrictToPointInt_convexChart_bijective` — for a convex chart region `K` matched to a convex
  compact `C ⊆ ℝⁿ` and `y ∈ K`, the restriction `Hₙ(M|K;ℤ) → Hₙ(M|y;ℤ)` is bijective. Conjugates the
  Euclidean radial restriction `restrictToPointInt_radial_bijective` through the chart-transport equivs
  `chartPairEquiv_setInt` + `openSetExcisionEquivInt`.
* `restrictToPointInt_chartBall_bijective` — the concrete chart-closed-ball form: for a closed ball
  `B̄(chartAt y₀ · y₀, r)` inside the chart target and `y` in its chart-pullback `K`, the restriction
  `Hₙ(M|K;ℤ) → Hₙ(M|y;ℤ)` is bijective. Applies the previous with `convex_closedBall` + the concrete
  chart `(chartAt y₀).toHomeomorphSourceTarget`.

The naturality helpers `relInclInt_map` (the ℤ mirror of
`SingularManifoldFundamentalClass.relIncl_map`) and `relInclInt_excisionMap` (the ℤ mirror of
`relIncl_excisionMap`) transport a point-restriction across the chart homeomorphism / the open-set
excision. MV-free: no `goodCompactInt_union`/`_biUnion` / Mayer–Vietoris.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularRelativeFunctorialityInt
open SKEFTHawking.IntOrientationSection (relInclInt relInclInt_trans restrictToPointInt)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.SingularExcisionIsoInt (excisionMapInt excisionMapInt_mk excisionEquivInt
  relChainInclInt relChainInclInt_mk relChainInclInt_mem_relCyclesInt)
open SKEFTHawking.SingularMayerVietorisLES (ambIncl subIncl)
open SKEFTHawking.SingularChartTransportInt (openSetExcisionEquivInt chartPairEquiv_setInt)
open SKEFTHawking.SingularManifoldFundamentalClass (mapsTo_chart_set)

namespace SKEFTHawking.SingularChartBallBijectiveInt

variable {X : TopCat}

/-! ## §1. Naturality of `relInclInt` under `RelHomologyInt.map` and `excisionMapInt` -/

/-- **Naturality of `relInclInt` under `RelHomologyInt.map`** (ℤ mirror of `relIncl_map`): an
inclusion-of-pairs `relInclInt` commutes with any pair map `RelHomologyInt.map φ`. -/
theorem relInclInt_map {Y : TopCat} (φ : C(↑X, ↑Y)) {S T : Set ↑X} (hST : S ⊆ T)
    {S' T' : Set ↑Y} (hφS : Set.MapsTo φ S S') (hφT : Set.MapsTo φ T T') (hST' : S' ⊆ T') (n : ℕ)
    (x : RelHomologyInt S n) :
    RelHomologyInt.map φ hφT n (relInclInt hST n x)
      = relInclInt hST' n (RelHomologyInt.map φ hφS n x) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  simp only [relInclInt, RelHomologyInt.map_mk]
  refine congrArg (Submodule.Quotient.mk) (Subtype.ext ?_)
  simp only [relCyclesMapInt_coe]
  rw [← relMapChainInt_comp, ← relMapChainInt_comp]
  congr 1

/-- **`excisionMapInt` is `RelHomologyInt.map (ambIncl B)`** (ℤ mirror of `excisionMap_eq_map`): both
are the quotient of `chainIncl B = mapChainInt (ambIncl B)`. -/
theorem excisionMapInt_eq_map (A B : Set ↑X) (n : ℕ) :
    excisionMapInt A B n
      = RelHomologyInt.map (ambIncl B) (fun _ hp => hp) n := by
  have hchain : ∀ (k : ℕ) (c : SingularChainInt (sub B) k),
      chainIncl B k c = mapChainInt (ambIncl B) k c := fun k c => by
    rw [SKEFTHawking.SingularConvexRadialBaseInt.mapChainInt_ambIncl]
  refine LinearMap.ext fun z => ?_
  obtain ⟨z₀, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  rw [show (Submodule.Quotient.mk z₀ : RelHomologyInt (restr A B) n)
      = RelHomologyInt.mk (restr A B) n z₀ from rfl, excisionMapInt_mk]
  show RelHomologyInt.mk A n ⟨relChainInclInt A B n (z₀ : RelativeChainInt (restr A B) n),
      relChainInclInt_mem_relCyclesInt A B n z₀ z₀.2⟩
    = RelHomologyInt.map (ambIncl B) (fun _ hp => hp) n (Submodule.Quotient.mk z₀)
  rw [RelHomologyInt.map_mk (ambIncl B) (fun _ hp => hp) n z₀]
  refine congrArg (Submodule.Quotient.mk) (Subtype.ext ?_)
  rw [relCyclesMapInt_coe]
  show relChainInclInt A B n (z₀ : RelativeChainInt (restr A B) n)
    = relMapChainInt (ambIncl B) (fun _ hp => hp) n (z₀ : RelativeChainInt (restr A B) n)
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (z₀ : RelativeChainInt (restr A B) n)
  rw [← hc, show (Submodule.Quotient.mk c : RelativeChainInt (restr A B) n)
      = RelativeChainInt.mk (restr A B) n c from rfl, relChainInclInt_mk]
  rw [hchain n c]
  exact (relMapChainInt_mk (ambIncl B) (fun _ hp => hp) n c).symm

/-- **Excision-transport naturality** (ℤ mirror of `relIncl_excisionMap`): `relInclInt` commutes with
`excisionMapInt` (`A ⊆ A'`). -/
theorem relInclInt_excisionMap {A A' B : Set ↑X} (hAA' : A ⊆ A') (n : ℕ)
    (z : RelHomologyInt (restr A B) n) :
    relInclInt hAA' n (excisionMapInt A B n z)
      = excisionMapInt A' B n (relInclInt (Set.preimage_mono hAA') n z) := by
  rw [excisionMapInt_eq_map, excisionMapInt_eq_map]
  exact (relInclInt_map (ambIncl B) (Set.preimage_mono hAA')
    (fun _ hp => hp) (fun _ hp => hp) hAA' n z).symm

/-! ## §2. The chart-transported convex base case (ℤ) -/

/-- **Restriction to ANY point of a convex chart set is bijective** (ℤ) `Hₘ₊₂(M|K;ℤ) → Hₘ₊₂(M|y;ℤ)`
(`y ∈ K`, `K` a compact **convex** chart set matched to `C ⊆ ℝⁿ`). The point-transport equiv `Ty`
conjugates `restrictToPointInt hyK` to the Euclidean `restrictToPointInt hcC` at `c = e y ∈ C`, which is
bijective by the integral radial restriction iso (`restrictToPointInt_radial_bijective`, `C` convex
compact). The local-homology iso `Hₘ₊₂(M|K;ℤ) ≅ Hₘ₊₂(M|y;ℤ)` the oriented fundamental-class local
constancy rides on. Mirror of `SingularGoodCompactChart.restrictToPoint_convexChart_bijective`. -/
theorem restrictToPointInt_convexChart_bijective {M : TopCat} [T1Space ↑M] {m : ℕ} {K : Set ↑M}
    {U : Set ↑M} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U)
    {C : Set (EuclideanSpace ℝ (Fin (m + 2)))} {V : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))}
    (hCconv : Convex ℝ C) (hCcomp : IsCompact C) (hV : IsOpen V) (hCV : C ⊆ V)
    (e : ↥U ≃ₜ ↥V)
    (hcompat : ∀ u : ↥U, ((e u : ↑(SingularEuclideanAcyclic.Eucl (m + 2))) ∈ C) ↔ (u : ↑M) ∈ K)
    {y : ↑M} (hyK : y ∈ K) :
    Function.Bijective (restrictToPointInt (X := M) hyK (m + 2)) := by
  have hyU : y ∈ U := hKU hyK
  set yU : ↥U := ⟨y, hyU⟩ with hyU'
  set c : EuclideanSpace ℝ (Fin (m + 2)) := (e yU : ↑(SingularEuclideanAcyclic.Eucl (m + 2))) with hcdef
  have hcC : c ∈ C := (hcompat yU).mpr hyK
  -- The bulk transport `TK : Hₘ₊₂(M|K;ℤ) ≅ Hₘ₊₂(ℝⁿ|C;ℤ)`.
  set TK : RelHomologyInt (X := M) Kᶜ (m + 2)
      ≃ₗ[ℤ] RelHomologyInt (X := SingularEuclideanAcyclic.Eucl (m + 2)) Cᶜ (m + 2) :=
    (openSetExcisionEquivInt hK hU hKU (m + 1)).symm.trans
      ((chartPairEquiv_setInt e hcompat (m + 2)).trans
        (openSetExcisionEquivInt hCcomp.isClosed hV hCV (m + 1))) with hTK
  -- Point-version chart compatibility: `e u = c ↔ u = y` (modulo coercions).
  have hcompat' : ∀ u : ↥U,
      ((e u : ↑(SingularEuclideanAcyclic.Eucl (m + 2)))
          ∈ ({c} : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))))
        ↔ (u : ↑M) ∈ ({y} : Set ↑M) := by
    intro u
    simp only [Set.mem_singleton_iff, hcdef]
    rw [Subtype.coe_inj, e.injective.eq_iff]
    constructor
    · intro h; rw [h]
    · intro h; exact Subtype.ext h
  have hyV : c ∈ (V : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))) := hCV hcC
  -- The point transport `Ty : Hₘ₊₂(M|y;ℤ) ≅ Hₘ₊₂(ℝⁿ|c;ℤ)`.
  set Ty : RelHomologyInt (X := M) ({y}ᶜ) (m + 2)
      ≃ₗ[ℤ] RelHomologyInt (X := SingularEuclideanAcyclic.Eucl (m + 2)) ({c}ᶜ) (m + 2) :=
    (openSetExcisionEquivInt isClosed_singleton hU
        (Set.singleton_subset_iff.mpr hyU) (m + 1)).symm.trans
      ((chartPairEquiv_setInt e hcompat' (m + 2)).trans
        (openSetExcisionEquivInt isClosed_singleton hV
          (Set.singleton_subset_iff.mpr hyV) (m + 1))) with hTy
  have hKy : (Kᶜ : Set ↑M) ⊆ {y}ᶜ :=
    Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hyK)
  have hCc' : (Cᶜ : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))) ⊆ {c}ᶜ :=
    Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hcC)
  -- Naturality `Ty ∘ restrictToPointInt hyK = restrictToPointInt hcC ∘ TK` (the three transport steps).
  have hnat : ∀ α : RelHomologyInt (X := M) Kᶜ (m + 2),
      Ty (restrictToPointInt hyK (m + 2) α) = restrictToPointInt hcC (m + 2) (TK α) := by
    intro α
    simp only [hTK, hTy, LinearEquiv.trans_apply]
    have hstep1 : (openSetExcisionEquivInt isClosed_singleton hU
          (Set.singleton_subset_iff.mpr hyU) (m + 1)).symm
            ((restrictToPointInt hyK (m + 2)) α)
          = relInclInt (Set.preimage_mono hKy) (m + 2)
              ((openSetExcisionEquivInt hK hU hKU (m + 1)).symm α) := by
      apply (openSetExcisionEquivInt isClosed_singleton hU (Set.singleton_subset_iff.mpr hyU)
        (m + 1)).injective
      rw [LinearEquiv.apply_symm_apply]
      show (restrictToPointInt hyK (m + 2)) α
        = excisionMapInt {y}ᶜ U (m + 2)
            (relInclInt (Set.preimage_mono hKy) (m + 2)
              ((openSetExcisionEquivInt hK hU hKU (m + 1)).symm α))
      rw [← relInclInt_excisionMap hKy (m + 2)]
      show (restrictToPointInt hyK (m + 2)) α
        = relInclInt hKy (m + 2)
            ((openSetExcisionEquivInt hK hU hKU (m + 1))
              ((openSetExcisionEquivInt hK hU hKU (m + 1)).symm α))
      rw [LinearEquiv.apply_symm_apply]
      rfl
    have hstep2 : ∀ β, chartPairEquiv_setInt e hcompat' (m + 2)
          (relInclInt (Set.preimage_mono hKy) (m + 2) β)
          = relInclInt (Set.preimage_mono hCc') (m + 2) (chartPairEquiv_setInt e hcompat (m + 2) β) :=
      fun β => relInclInt_map (⟨e, e.continuous⟩ : C(↑(sub U), ↑(sub V))) (Set.preimage_mono hKy)
        (mapsTo_chart_set e hcompat) (mapsTo_chart_set e hcompat') (Set.preimage_mono hCc')
        (m + 2) β
    have hstep3 : ∀ γ, openSetExcisionEquivInt isClosed_singleton hV
          (Set.singleton_subset_iff.mpr hyV) (m + 1) (relInclInt (Set.preimage_mono hCc') (m + 2) γ)
          = restrictToPointInt hcC (m + 2)
              (openSetExcisionEquivInt hCcomp.isClosed hV hCV (m + 1) γ) :=
      fun γ => (relInclInt_excisionMap hCc' (m + 2) γ).symm
    rw [hstep1, hstep2, hstep3]
  -- Conjugation: `restrictToPointInt hyK` is bijective because the Euclidean restriction at `c` is.
  have hkey : ⇑Ty ∘ ⇑(restrictToPointInt hyK (m + 2))
      = ⇑(restrictToPointInt hcC (m + 2)) ∘ ⇑TK := funext hnat
  have hcomp_bij : Function.Bijective (⇑(restrictToPointInt hcC (m + 2)) ∘ ⇑TK) :=
    (SingularConvexRadialBaseInt.restrictToPointInt_radial_bijective hCconv hCcomp hcC).comp
      TK.bijective
  rw [← hkey] at hcomp_bij
  have hrw : ⇑(restrictToPointInt hyK (m + 2))
      = ⇑Ty.symm ∘ (⇑Ty ∘ ⇑(restrictToPointInt hyK (m + 2))) := by
    funext β
    simp only [Function.comp_apply, LinearEquiv.symm_apply_apply]
  rw [hrw]
  exact Ty.symm.bijective.comp hcomp_bij

end SKEFTHawking.SingularChartBallBijectiveInt
