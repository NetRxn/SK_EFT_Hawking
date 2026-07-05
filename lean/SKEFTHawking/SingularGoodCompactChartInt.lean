import Mathlib
import SKEFTHawking.SingularGoodCompactInt
import SKEFTHawking.SingularGoodCompactEuclideanInt
import SKEFTHawking.SingularChartTransportInt

/-!
# The integral "good compact" property transported through a chart (Hatcher step 4, ℤ) — brick 18e

The ℤ analog of the mod-2 `SingularGoodCompactChart`. A compact `K ⊆ M` contained in a chart domain
`U`, matched by a chart homeomorphism `e : U ≃ₜ V` to a compact `C ⊆ ℝⁿ` (`hcompat`), is
`goodCompactInt (m+2) K`. This transports the **arbitrary**-compact Euclidean result
`SingularGoodCompactEuclideanInt.goodCompactInt_eucl_compact` through the chart.

The transport rides on the integral naturality bridges built here (`§0`):

* `RelHomologyInt.map_compInt` — the homology-level functoriality `Hₙ(ψ∘φ) = Hₙ(ψ) ∘ Hₙ(φ)`;
* `relInclInt_mapInt` — naturality of `relInclInt` under `RelHomologyInt.map` (`φ ∘ id = id ∘ φ`);
* `mapChainInt_ambInclInt` + `excisionMapInt_eq_mapInt` — the excision map is `RelHomologyInt.map` of
  the subspace inclusion;
* `relInclInt_excisionMapInt` — `relInclInt` commutes with `excisionMapInt`.

Then `vanishAboveInt_chart` (verbatim excision transport of the high-degree half) and
`determinedByPointsInt_chart` (the degree-`n` half: the transport equiv `TK` carries per-point
restrictions, `hnat`), and `goodCompactInt_chart` (both halves).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeFunctorialityInt
open SKEFTHawking.SingularExcisionIsoInt
open SKEFTHawking.SingularChartTransportInt
open SKEFTHawking.IntOrientationSection (relInclInt relInclInt_trans restrictToPointInt)
open SKEFTHawking.SingularGoodCompactInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.SingularMayerVietorisLES (ambIncl mapSimplex_ambIncl)

namespace SKEFTHawking.SingularGoodCompactChartInt

variable {X : TopCat}

/-! ## §0. Integral naturality bridges (`relInclInt` vs `RelHomologyInt.map`/`excisionMapInt`) -/

/-- **Homology-level functoriality** `Hₙ(ψ∘φ) = Hₙ(ψ) ∘ Hₙ(φ)` (integral). -/
theorem RelHomologyInt.map_compInt {Y Z : TopCat} (φ : C(↑X, ↑Y)) (ψ : C(↑Y, ↑Z))
    {A : Set ↑X} {B : Set ↑Y} {D : Set ↑Z} (hAB : Set.MapsTo φ A B) (hBD : Set.MapsTo ψ B D)
    (n : ℕ) (x : RelHomologyInt A n) :
    RelHomologyInt.map ψ hBD n (RelHomologyInt.map φ hAB n x)
      = RelHomologyInt.map (ψ.comp φ) (hBD.comp hAB) n x := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [RelHomologyInt.map_mk, RelHomologyInt.map_mk, RelHomologyInt.map_mk]
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  simp only [relCyclesMapInt_coe]
  exact (relMapChainInt_comp φ hAB ψ hBD n (z : RelativeChainInt A n)).symm

/-- **Naturality of `relInclInt` under `RelHomologyInt.map`**: an inclusion-of-pairs commutes with any
pair map `RelHomologyInt.map φ` (both sides are `RelHomologyInt.map φ`, since `φ ∘ id = id ∘ φ`). -/
theorem relInclInt_mapInt {Y : TopCat} (φ : C(↑X, ↑Y)) {S T : Set ↑X} (hST : S ⊆ T)
    {S' T' : Set ↑Y} (hφS : Set.MapsTo φ S S') (hφT : Set.MapsTo φ T T') (hST' : S' ⊆ T') (n : ℕ)
    (x : RelHomologyInt S n) :
    RelHomologyInt.map φ hφT n (relInclInt hST n x)
      = relInclInt hST' n (RelHomologyInt.map φ hφS n x) := by
  show RelHomologyInt.map φ hφT n
        (RelHomologyInt.map (ContinuousMap.id ↑X) (fun _ hx => hST hx) n x)
      = RelHomologyInt.map (ContinuousMap.id ↑Y) (fun _ hx => hST' hx) n
        (RelHomologyInt.map φ hφS n x)
  rw [RelHomologyInt.map_compInt, RelHomologyInt.map_compInt]
  rfl

/-- **`mapChainInt (ambIncl S) = chainIncl S`** (integral) — the LES-side pushforward and the
`connecting`-side chain inclusion agree along `sub S ↪ X`. -/
theorem mapChainInt_ambInclInt (S : Set ↑X) (n : ℕ) :
    SingularFunctorialityInt.mapChainInt (ambIncl S) n = chainIncl S n := by
  refine LinearMap.ext fun c => ?_
  induction c using Finsupp.induction_linear with
  | zero => simp
  | add c₁ c₂ h₁ h₂ => rw [map_add, map_add, h₁, h₂]
  | single σ a =>
      rw [SingularFunctorialityInt.mapChainInt_single, chainIncl_single, mapSimplex_ambIncl]

/-- **The excision map is `RelHomologyInt.map` of the subspace inclusion** `Hₙ(B, A∩B; ℤ) → Hₙ(X, A; ℤ)`:
`excisionMapInt A B n = RelHomologyInt.map (ambIncl B)`. -/
theorem excisionMapInt_eq_mapInt (A B : Set ↑X) (n : ℕ) :
    excisionMapInt A B n
      = RelHomologyInt.map (ambIncl B) (fun _ hp => hp) n := by
  have hchain : relChainInclInt A B n
      = relMapChainInt (ambIncl B) (fun _ hp => hp) n := by
    refine LinearMap.ext fun c => ?_
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    show relChainInclInt A B n (RelativeChainInt.mk (restr A B) n c)
        = relMapChainInt (ambIncl B) (fun _ hp => hp) n (RelativeChainInt.mk (restr A B) n c)
    rw [relChainInclInt_mk, show relMapChainInt (ambIncl B) (fun _ hp => hp) n
        (RelativeChainInt.mk (restr A B) n c)
          = RelativeChainInt.mk A n (SingularFunctorialityInt.mapChainInt (ambIncl B) n c)
        from relMapChainInt_mk (ambIncl B) (fun _ hp => hp) n c, mapChainInt_ambInclInt]
  refine LinearMap.ext fun z => ?_
  obtain ⟨z₀, rfl⟩ := Submodule.Quotient.mk_surjective _ z
  change Submodule.Quotient.mk
      (⟨relChainInclInt A B n (z₀ : RelativeChainInt (restr A B) n),
        relChainInclInt_mem_relCyclesInt A B n z₀ z₀.2⟩ : relCyclesInt A n)
    = RelHomologyInt.map (ambIncl B) (fun _ hp => hp) n (Submodule.Quotient.mk z₀)
  rw [RelHomologyInt.map_mk]
  refine congrArg Submodule.Quotient.mk (Subtype.ext ?_)
  rw [relCyclesMapInt_coe]
  exact DFunLike.congr_fun hchain (z₀ : RelativeChainInt (restr A B) n)

/-- **Excision-transport naturality** (integral): `relInclInt` commutes with `excisionMapInt`
(`A ⊆ A'`). -/
theorem relInclInt_excisionMapInt {A A' B : Set ↑X} (hAA' : A ⊆ A') (n : ℕ)
    (z : RelHomologyInt (restr A B) n) :
    relInclInt hAA' n (excisionMapInt A B n z)
      = excisionMapInt A' B n (relInclInt (Set.preimage_mono hAA') n z) := by
  rw [excisionMapInt_eq_mapInt, excisionMapInt_eq_mapInt]
  exact (relInclInt_mapInt (ambIncl B) (Set.preimage_mono hAA')
    (fun _ hp => hp) (fun _ hp => hp) hAA' n z).symm

/-! ## §1. The high-degree vanishing half, transported through a chart -/

/-- **The high-degree vanishing half, transported through a chart** (ℤ): `Hᵢ(M | K; ℤ) = 0` for
`i > m+2`, for `K` a compact chart set matched to a compact `C ⊆ ℝⁿ`. Verbatim structure of
`SingularGoodCompactChart.vanishAbove_chart` with `vanishAboveInt_eucl_compact` closing the Euclidean
side. -/
theorem vanishAboveInt_chart {M : TopCat} {m : ℕ} {K : Set ↑M}
    {U : Set ↑M} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U)
    {C : Set (EuclideanSpace ℝ (Fin (m + 2)))} {V : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))}
    (hCcomp : IsCompact C) (hV : IsOpen V) (hCV : C ⊆ V)
    (e : ↥U ≃ₜ ↥V)
    (hcompat : ∀ u : ↥U, ((e u : ↑(SingularEuclideanAcyclic.Eucl (m + 2))) ∈ C) ↔ (u : ↑M) ∈ K) :
    vanishAboveInt (X := M) (m + 2) K := by
  intro i hi x
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 + 1 := ⟨i - 2, by omega⟩
  have e' := (openSetExcisionEquivInt hK hU hKU (k + 1)).symm.trans
    ((chartPairEquiv_setInt e hcompat (k + 1 + 1)).trans
      (openSetExcisionEquivInt hCcomp.isClosed hV hCV (k + 1)))
  exact e'.injective (by
    rw [map_zero]
    exact SingularGoodCompactEuclideanInt.vanishAboveInt_eucl_compact hCcomp (k + 1 + 1) (by omega)
      (e' x))

/-! ## §2. The degree-`n` half, transported through a chart -/

/-- **The degree-`n` half, transported through a chart** (ℤ): a class in `Hₘ₊₂(M | K; ℤ)` restricting
to `0` at every point of `K` is `0`, for `K` a compact chart set matched to a compact `C ⊆ ℝⁿ`. The
transport equiv `TK : Hₘ₊₂(M|K; ℤ) ≅ Hₘ₊₂(ℝⁿ|C; ℤ)` carries the per-point restriction
`restrictToPointInt hxK` to the Euclidean `restrictToPointInt hc` (`hnat`), so `TK α` restricts to `0`
at every point of `C` and is `0` by `determinedByPointsInt_eucl_compact`. -/
theorem determinedByPointsInt_chart {M : TopCat} [T1Space ↑M] {m : ℕ} {K : Set ↑M}
    {U : Set ↑M} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U)
    {C : Set (EuclideanSpace ℝ (Fin (m + 2)))} {V : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))}
    (hCcomp : IsCompact C) (hV : IsOpen V) (hCV : C ⊆ V)
    (e : ↥U ≃ₜ ↥V)
    (hcompat : ∀ u : ↥U, ((e u : ↑(SingularEuclideanAcyclic.Eucl (m + 2))) ∈ C) ↔ (u : ↑M) ∈ K) :
    determinedByPointsInt (X := M) (m + 2) K := by
  intro α hα
  set TK : RelHomologyInt (X := M) Kᶜ (m + 2)
      ≃ₗ[ℤ] RelHomologyInt (X := SingularEuclideanAcyclic.Eucl (m + 2)) Cᶜ (m + 2) :=
    (openSetExcisionEquivInt hK hU hKU (m + 1)).symm.trans
      ((chartPairEquiv_setInt e hcompat (m + 2)).trans
        (openSetExcisionEquivInt hCcomp.isClosed hV hCV (m + 1))) with hTK
  apply TK.injective
  rw [map_zero]
  refine SingularGoodCompactEuclideanInt.determinedByPointsInt_eucl_compact hCcomp (TK α)
    (fun c hc => ?_)
  -- The chart preimage `x₀` of `c`, and its `M`-point `xpt ∈ K`.
  have hcV : c ∈ (V : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))) := hCV hc
  set x₀ : ↥U := e.symm ⟨c, hcV⟩ with hx₀
  set xpt : ↑M := (x₀ : ↑M) with hxpt
  have hex₀ : e x₀ = ⟨c, hcV⟩ := by rw [hx₀, e.apply_symm_apply]
  have hexc : (e x₀ : ↑(SingularEuclideanAcyclic.Eucl (m + 2))) = c := by rw [hex₀]
  have hxK : xpt ∈ K := (hcompat x₀).mp (by rw [hexc]; exact hc)
  have hxptU : xpt ∈ U := x₀.2
  -- Point-version chart compatibility.
  have hcompat' : ∀ u : ↥U,
      ((e u : ↑(SingularEuclideanAcyclic.Eucl (m + 2)))
          ∈ ({c} : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))))
        ↔ (u : ↑M) ∈ ({xpt} : Set ↑M) := by
    intro u
    simp only [Set.mem_singleton_iff, hxpt]
    rw [← hexc, Subtype.coe_inj, e.injective.eq_iff, Subtype.coe_inj]
  -- The point-transport equiv `Tx`.
  set Tx : RelHomologyInt (X := M) ({xpt}ᶜ) (m + 2)
      ≃ₗ[ℤ] RelHomologyInt (X := SingularEuclideanAcyclic.Eucl (m + 2)) ({c}ᶜ) (m + 2) :=
    (openSetExcisionEquivInt isClosed_singleton hU
        (Set.singleton_subset_iff.mpr hxptU) (m + 1)).symm.trans
      ((chartPairEquiv_setInt e hcompat' (m + 2)).trans
        (openSetExcisionEquivInt isClosed_singleton hV
          (Set.singleton_subset_iff.mpr hcV) (m + 1))) with hTx
  have hKxpt : (Kᶜ : Set ↑M) ⊆ {xpt}ᶜ :=
    Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hxK)
  have hCc' : (Cᶜ : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))) ⊆ {c}ᶜ :=
    Set.compl_subset_compl.mpr (Set.singleton_subset_iff.mpr hc)
  -- Naturality: `Tx ∘ restrictToPointInt hxK = restrictToPointInt hc ∘ TK`.
  have hnat : Tx (restrictToPointInt hxK (m + 2) α) = restrictToPointInt hc (m + 2) (TK α) := by
    simp only [hTK, hTx, LinearEquiv.trans_apply]
    have hstep1 : (openSetExcisionEquivInt isClosed_singleton hU
          (Set.singleton_subset_iff.mpr hxptU) (m + 1)).symm
            ((restrictToPointInt hxK (m + 2)) α)
          = relInclInt (Set.preimage_mono hKxpt) (m + 2)
              ((openSetExcisionEquivInt hK hU hKU (m + 1)).symm α) := by
      apply (openSetExcisionEquivInt isClosed_singleton hU (Set.singleton_subset_iff.mpr hxptU)
        (m + 1)).injective
      rw [LinearEquiv.apply_symm_apply]
      show (restrictToPointInt hxK (m + 2)) α
        = excisionMapInt {xpt}ᶜ U (m + 2)
            (relInclInt (Set.preimage_mono hKxpt) (m + 2)
              ((openSetExcisionEquivInt hK hU hKU (m + 1)).symm α))
      rw [← relInclInt_excisionMapInt hKxpt (m + 2)]
      show (restrictToPointInt hxK (m + 2)) α
        = relInclInt hKxpt (m + 2)
            ((openSetExcisionEquivInt hK hU hKU (m + 1))
              ((openSetExcisionEquivInt hK hU hKU (m + 1)).symm α))
      rw [LinearEquiv.apply_symm_apply]
      rfl
    have hstep2 : ∀ β, chartPairEquiv_setInt e hcompat' (m + 2)
          (relInclInt (Set.preimage_mono hKxpt) (m + 2) β)
          = relInclInt (Set.preimage_mono hCc') (m + 2) (chartPairEquiv_setInt e hcompat (m + 2) β) :=
      fun β => relInclInt_mapInt (⟨e, e.continuous⟩ : C(↑(sub U), ↑(sub V))) (Set.preimage_mono hKxpt)
        (SingularManifoldFundamentalClass.mapsTo_chart_set e hcompat)
        (SingularManifoldFundamentalClass.mapsTo_chart_set e hcompat') (Set.preimage_mono hCc')
        (m + 2) β
    have hstep3 : ∀ γ, openSetExcisionEquivInt isClosed_singleton hV
          (Set.singleton_subset_iff.mpr hcV) (m + 1) (relInclInt (Set.preimage_mono hCc') (m + 2) γ)
          = restrictToPointInt hc (m + 2)
              (openSetExcisionEquivInt hCcomp.isClosed hV hCV (m + 1) γ) :=
      fun γ => (relInclInt_excisionMapInt hCc' (m + 2) γ).symm
    rw [hstep1, hstep2, hstep3]
  rw [← hnat, hα xpt hxK, map_zero]

/-- **A compact chart set is `goodCompactInt`** (Hatcher step 4 base case, ℤ): combine
`vanishAboveInt_chart` and `determinedByPointsInt_chart`. -/
theorem goodCompactInt_chart {M : TopCat} [T1Space ↑M] {m : ℕ} {K : Set ↑M}
    {U : Set ↑M} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U)
    {C : Set (EuclideanSpace ℝ (Fin (m + 2)))} {V : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))}
    (hCcomp : IsCompact C) (hV : IsOpen V) (hCV : C ⊆ V)
    (e : ↥U ≃ₜ ↥V)
    (hcompat : ∀ u : ↥U, ((e u : ↑(SingularEuclideanAcyclic.Eucl (m + 2))) ∈ C) ↔ (u : ↑M) ∈ K) :
    goodCompactInt (X := M) (m + 2) K :=
  ⟨vanishAboveInt_chart hK hU hKU hCcomp hV hCV e hcompat,
   determinedByPointsInt_chart hK hU hKU hCcomp hV hCV e hcompat⟩

end SKEFTHawking.SingularGoodCompactChartInt
