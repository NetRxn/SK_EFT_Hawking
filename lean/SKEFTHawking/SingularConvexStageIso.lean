import Mathlib
import SKEFTHawking.SingularChartBridge
import SKEFTHawking.SingularConvexRadialBase
import SKEFTHawking.SingularFundamentalClassExist

/-!
# Phase 5q.G (G1 PD-induction, B4c INJ substrate) — the chart-convex stage iso `Hₘ₊₂(M | K) ≅ ℤ/2`

The set-level analogue of `SingularChartBridge.chartLocalIso`: for a compact stage `K` of a
chart-convex open (the chart `e : U ≃ₜ V` carries `K` exactly onto a convex compact `C ∋ p₀`),
`H_{m+2}(M, M∖K) ≅ ℤ/2` by excising to the chart, transporting the pair through `e`, excising to
the model, restricting radially to `p₀` (`restrictToPoint_radial_bijective` — the `O`-based iso,
no `nhds 0` anchoring), and finishing with the translated local model.

The stage-iso input of the B4c `D⁰`-injectivity half (the UC-flip's `E`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularExcisionIso SKEFTHawking.SingularRelativeFunctoriality
open SKEFTHawking.SingularEuclideanAcyclic SKEFTHawking.SingularLocalModelChart
open SKEFTHawking.SingularRelativeMV

namespace SKEFTHawking.SingularConvexStageIso

/-- **Open-set excision** `Hₙ₊₁(V, V∖K) ≅ Hₙ₊₁(X, X∖K)`: for `K` closed inside an open `V`, the
relative homology of the pair at `K` only sees `V` (`excisionEquiv` at the cover `{X∖K, V}`; the
set-level generalization of `SingularChartBridge.openPointExcisionEquiv`). -/
noncomputable def openSetExcisionEquiv {X : TopCat} {K V : Set ↑X}
    (hK : IsClosed K) (hV : IsOpen V) (hKV : K ⊆ V) (n : ℕ) :
    RelativeHomology (restr (Kᶜ) V) (n + 1) ≃ₗ[ZMod 2] RelativeHomology (Kᶜ) (n + 1) :=
  excisionEquiv (Kᶜ) V n (by
    rw [Set.biUnion_pair, hK.isOpen_compl.interior_eq, hV.interior_eq, Set.eq_univ_iff_forall]
    intro x
    by_cases h : x ∈ K
    · exact Or.inr (hKV h)
    · exact Or.inl h)

/-- The chart homeo maps the pair `(U, U∖K)` to `(V, V∖C)` when it carries `K` exactly onto `C`. -/
theorem mapsTo_chart_stage {M : TopCat} {m : ℕ} {U : Set ↑M} {V : Set ↑(Eucl (m + 2))}
    (e : ↥U ≃ₜ ↥V) {KS : Set ↑M} {CS : Set ↑(Eucl (m + 2))}
    (hcompat : ∀ u : ↥U, ((e u : ↑(Eucl (m + 2))) ∈ CS) ↔ (u : ↑M) ∈ KS) :
    Set.MapsTo (⟨e, e.continuous⟩ : C(↑(sub U), ↑(sub V))) (restr (KSᶜ) U) (restr (CSᶜ) V) := by
  intro u hu
  simp only [restr, Set.mem_preimage, ContinuousMap.coe_mk, Set.mem_compl_iff] at hu ⊢
  exact fun hC => hu ((hcompat u).mp hC)

theorem mapsTo_chart_stage_symm {M : TopCat} {m : ℕ} {U : Set ↑M} {V : Set ↑(Eucl (m + 2))}
    (e : ↥U ≃ₜ ↥V) {KS : Set ↑M} {CS : Set ↑(Eucl (m + 2))}
    (hcompat : ∀ u : ↥U, ((e u : ↑(Eucl (m + 2))) ∈ CS) ↔ (u : ↑M) ∈ KS) :
    Set.MapsTo (⟨e.symm, e.symm.continuous⟩ : C(↑(sub V), ↑(sub U))) (restr (CSᶜ) V)
      (restr (KSᶜ) U) := by
  intro v hv
  simp only [restr, Set.mem_preimage, ContinuousMap.coe_mk, Set.mem_compl_iff] at hv ⊢
  intro hK
  apply hv
  have h := (hcompat (e.symm v)).mpr hK
  rwa [e.apply_symm_apply] at h

/-- **The chart-pair homeomorphism induces a relative-homology iso at a carried stage**
`Hₖ(U, U∖K) ≅ Hₖ(V, V∖C)` (the set-level `chartPairEquiv`). -/
noncomputable def chartStagePairEquiv {M : TopCat} {m : ℕ} {U : Set ↑M} {V : Set ↑(Eucl (m + 2))}
    (e : ↥U ≃ₜ ↥V) {KS : Set ↑M} {CS : Set ↑(Eucl (m + 2))}
    (hcompat : ∀ u : ↥U, ((e u : ↑(Eucl (m + 2))) ∈ CS) ↔ (u : ↑M) ∈ KS) (k : ℕ) :
    RelativeHomology (restr (KSᶜ) U) k ≃ₗ[ZMod 2] RelativeHomology (restr (CSᶜ) V) k :=
  LinearEquiv.ofBijective
    (RelativeHomology.map (⟨e, e.continuous⟩ : C(↑(sub U), ↑(sub V)))
      (mapsTo_chart_stage e hcompat) k)
    (RelativeHomology.map_bijective_of_comp_id (⟨e, e.continuous⟩ : C(↑(sub U), ↑(sub V)))
      (⟨e.symm, e.symm.continuous⟩ : C(↑(sub V), ↑(sub U)))
      (mapsTo_chart_stage e hcompat) (mapsTo_chart_stage_symm e hcompat)
      (ContinuousMap.ext fun v => e.symm_apply_apply v)
      (ContinuousMap.ext fun u => e.apply_symm_apply u) k)

/-- Propositional set-congruence on relative homology (both `relIncl`s over mutual inclusion; NO
raw defeq across set spellings — the `{x}ᶜ ↔ {y | y ≠ x}` seam killer, public twin of the
`SingularBaseCaseD0` private helper). -/
noncomputable def relHomologySetCongr {X : TopCat} {S T : Set ↑X} (hST : S ⊆ T) (hTS : T ⊆ S)
    (n : ℕ) : RelativeHomology S n ≃ₗ[ZMod 2] RelativeHomology T n :=
  LinearEquiv.ofLinear (relIncl hST n) (relIncl hTS n)
    (LinearMap.ext fun p =>
      SKEFTHawking.SingularFundamentalClass.relIncl_leftInverse hTS hST n p)
    (LinearMap.ext fun p =>
      SKEFTHawking.SingularFundamentalClass.relIncl_leftInverse hST hTS n p)

/-- `H_{m+2}(ℝᵐ⁺² | p) ≅ ℤ/2` at the `{p}ᶜ`-spelling (the seam to the `{y | y ≠ p}`-spelled
translated local model paid once, propositionally). -/
noncomputable def localHomologyAtPointIsoCompl (m : ℕ) (p : EuclideanSpace ℝ (Fin (m + 2))) :
    RelativeHomology (X := Eucl (m + 2)) (({p} : Set ↑(Eucl (m + 2)))ᶜ) (m + 2)
      ≃ₗ[ZMod 2] ZMod 2 :=
  (relHomologySetCongr (fun y hy => by simpa using hy) (fun y hy => by simpa using hy)
    (m + 2)).trans (localHomologyAtPointIso m p)

/-- **The chart-convex stage iso** `H_{m+2}(M | K) ≅ ℤ/2`: excise to the chart, transport the
pair, excise to the model, restrict radially to `p₀ ∈ C` (`restrictToPoint_radial_bijective` —
the arbitrary-basepoint radial iso, no `nhds 0` anchoring), and finish with the translated local
model. The UC-flip's `E` at a chart-convex-absorbed stage. -/
noncomputable def convexStageLocalIso {M : TopCat} {m : ℕ}
    {U : Set ↑M} {V : Set ↑(Eucl (m + 2))} (hU : IsOpen U) (hV : IsOpen V)
    (e : ↥U ≃ₜ ↥V)
    {KS : Set ↑M} (hKcl : IsClosed KS) (hKU : KS ⊆ U)
    {CS : Set ↑(Eucl (m + 2))} (hCconv : Convex ℝ CS) (hCcomp : IsCompact CS)
    {p₀ : EuclideanSpace ℝ (Fin (m + 2))} (hp₀ : p₀ ∈ CS) (hCV : CS ⊆ V)
    (hcompat : ∀ u : ↥U, ((e u : ↑(Eucl (m + 2))) ∈ CS) ↔ (u : ↑M) ∈ KS) :
    RelativeHomology (X := M) (KSᶜ) (m + 2) ≃ₗ[ZMod 2] ZMod 2 :=
  (openSetExcisionEquiv hKcl hU hKU (m + 1)).symm.trans
    ((chartStagePairEquiv e hcompat (m + 2)).trans
      ((openSetExcisionEquiv (X := Eucl (m + 2)) hCcomp.isClosed hV hCV (m + 1)).trans
        ((LinearEquiv.ofBijective
            (SKEFTHawking.SingularManifoldFundamentalClass.restrictToPoint
              (X := Eucl (m + 2)) hp₀ (m + 2))
            (SKEFTHawking.SingularConvexRadialBase.restrictToPoint_radial_bijective
              hCconv hCcomp hp₀)).trans
          (localHomologyAtPointIsoCompl m p₀))))

/-- Over `ℤ/2`, a linear iso to `ℤ/2` sends any nonzero vector to `1`. -/
theorem linearEquiv_zmod2_apply_eq_one {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (E : V ≃ₗ[ZMod 2] ZMod 2) {g : V} (hg : g ≠ 0) : E g = 1 := by
  have hne : E g ≠ 0 := fun h => hg ((LinearEquiv.map_eq_zero_iff _).mp h)
  have hz2 : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
  exact hz2 _ hne

end SKEFTHawking.SingularConvexStageIso
