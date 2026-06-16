import Mathlib
import SKEFTHawking.SingularLocalModelChart

/-!
# The chart↔excision bridge: `Hₙ(M, M∖x) ≅ ℤ/2`

The local homology of a manifold at a point equals that of `ℝⁿ` at a point. The engine is
**open-point excision** `Hₙ(V, V∖q) ≅ Hₙ(X, X∖q)` (excise `X∖V`), an instance of `excisionEquiv`
with the cover `{X∖q, V}`. Applied at the manifold (`X = M`, `V` a chart domain) and at the model
(`X = ℝⁿ`, `V` the chart image), plus the chart homeomorphism of pairs and `localHomologyAtPointIso`,
this gives `Hₙ(M, M∖x) ≅ ℤ/2` — the local generators that glue into the fundamental class `[M]`.
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularExcisionIso SKEFTHawking.SingularRelativeFunctoriality
open SKEFTHawking.SingularEuclideanAcyclic SKEFTHawking.SingularLocalModelChart

namespace SKEFTHawking.SingularChartBridge

/-- In a `T1` space the complement of a point is open. -/
theorem isOpen_ne_point {X : TopCat} [T1Space ↑X] (q : ↑X) : IsOpen {y : ↑X | y ≠ q} := by
  have h : {y : ↑X | y ≠ q} = {q}ᶜ := by ext y; simp
  rw [h]; exact isOpen_compl_singleton

/-- The open cover `{X ∖ q, V}` when `V` is open and `q ∈ V`. -/
theorem cover_ne_point_open {X : TopCat} [T1Space ↑X] {q : ↑X} {V : Set ↑X}
    (hV : IsOpen V) (hq : q ∈ V) :
    (⋃ U ∈ ({{y | y ≠ q}, V} : Set (Set ↑X)), interior U) = Set.univ := by
  rw [Set.biUnion_pair, (isOpen_ne_point q).interior_eq, hV.interior_eq, Set.eq_univ_iff_forall]
  intro x
  by_cases h : x = q
  · exact Or.inr (h ▸ hq)
  · exact Or.inl h

/-- **Open-point excision**: `Hₙ₊₁(V, V ∖ q) ≅ Hₙ₊₁(X, X ∖ q)` for `V` open with `q ∈ V` (`T1` space).
The relative homology of a pair at a point only sees an open neighborhood of the point. -/
noncomputable def openPointExcisionEquiv {X : TopCat} [T1Space ↑X] {q : ↑X} {V : Set ↑X}
    (hV : IsOpen V) (hq : q ∈ V) (n : ℕ) :
    RelativeHomology (restr {y | y ≠ q} V) (n + 1)
      ≃ₗ[ZMod 2] RelativeHomology {y | y ≠ q} (n + 1) :=
  excisionEquiv {y | y ≠ q} V n (cover_ne_point_open hV hq)

/-- The chart homeo maps the pair `(U, U∖x)` to `(V, V∖q)` (injective, sends `x` to `q`). -/
theorem mapsTo_chart {M : TopCat} {x : ↑M} {U : Set ↑M} (hx : x ∈ U) {m : ℕ}
    {q : ↑(Eucl (m + 2))} {V : Set ↑(Eucl (m + 2))} (e : ↥U ≃ₜ ↥V)
    (hex : (e ⟨x, hx⟩ : ↑(Eucl (m + 2))) = q) :
    Set.MapsTo (⟨e, e.continuous⟩ : C(↑(sub U), ↑(sub V))) (restr {y | y ≠ x} U)
      (restr {y | y ≠ q} V) := by
  intro u hu
  simp only [restr, Set.mem_preimage, Set.mem_setOf_eq, ContinuousMap.coe_mk] at hu ⊢
  intro hval
  exact hu (congrArg Subtype.val (e.injective (Subtype.ext (hval.trans hex.symm))))

theorem mapsTo_chart_symm {M : TopCat} {x : ↑M} {U : Set ↑M} (hx : x ∈ U) {m : ℕ}
    {q : ↑(Eucl (m + 2))} {V : Set ↑(Eucl (m + 2))} (e : ↥U ≃ₜ ↥V)
    (hex : (e ⟨x, hx⟩ : ↑(Eucl (m + 2))) = q) :
    Set.MapsTo (⟨e.symm, e.symm.continuous⟩ : C(↑(sub V), ↑(sub U))) (restr {y | y ≠ q} V)
      (restr {y | y ≠ x} U) := by
  intro v hv
  simp only [restr, Set.mem_preimage, Set.mem_setOf_eq, ContinuousMap.coe_mk] at hv ⊢
  intro hval
  apply hv
  have h2 : v = e ⟨x, hx⟩ := by rw [← (Subtype.ext hval : e.symm v = ⟨x, hx⟩), e.apply_symm_apply]
  rw [h2]; exact hex

/-- **The chart-pair homeomorphism induces a relative-homology iso** `Hₖ(U, U∖x) ≅ Hₖ(V, V∖q)`. -/
noncomputable def chartPairEquiv {M : TopCat} {x : ↑M} {U : Set ↑M} (hx : x ∈ U) {m : ℕ}
    {q : ↑(Eucl (m + 2))} {V : Set ↑(Eucl (m + 2))} (e : ↥U ≃ₜ ↥V)
    (hex : (e ⟨x, hx⟩ : ↑(Eucl (m + 2))) = q) (k : ℕ) :
    RelativeHomology (restr {y | y ≠ x} U) k ≃ₗ[ZMod 2] RelativeHomology (restr {y | y ≠ q} V) k :=
  LinearEquiv.ofBijective
    (RelativeHomology.map (⟨e, e.continuous⟩ : C(↑(sub U), ↑(sub V))) (mapsTo_chart hx e hex) k)
    (RelativeHomology.map_bijective_of_comp_id (⟨e, e.continuous⟩ : C(↑(sub U), ↑(sub V)))
      (⟨e.symm, e.symm.continuous⟩ : C(↑(sub V), ↑(sub U))) (mapsTo_chart hx e hex)
      (mapsTo_chart_symm hx e hex)
      (ContinuousMap.ext fun v => e.symm_apply_apply v)
      (ContinuousMap.ext fun u => e.apply_symm_apply u) k)

/-- **The chart↔excision bridge `Hₙ(M, M∖x) ≅ ℤ/2`** (`n = m + 2`): excise `M∖U` to a chart domain,
transport by the chart homeo of pairs to `(V, V∖q) ⊆ ℝⁿ`, excise `ℝⁿ∖V`, and apply the translated
local model. The local generator of the fundamental class. -/
noncomputable def chartLocalIso {M : TopCat} [T1Space ↑M] {x : ↑M} {U : Set ↑M} (hU : IsOpen U)
    (hx : x ∈ U) {m : ℕ} {q : ↑(Eucl (m + 2))} {V : Set ↑(Eucl (m + 2))} (hV : IsOpen V)
    (hq : q ∈ V) (e : ↥U ≃ₜ ↥V) (hex : (e ⟨x, hx⟩ : ↑(Eucl (m + 2))) = q) :
    RelativeHomology (X := M) {y | y ≠ x} (m + 2) ≃ₗ[ZMod 2] ZMod 2 :=
  (openPointExcisionEquiv hU hx (m + 1)).symm.trans
    ((chartPairEquiv hx e hex (m + 2)).trans
      ((openPointExcisionEquiv hV hq (m + 1)).trans (localHomologyAtPointIso m q)))

/-- **The local homology of a topological manifold is `ℤ/2`** at every point: for `M` a `T1`
topological manifold modeled on `ℝᵐ⁺²`, `Hₘ₊₂(M, M∖x) ≅ ℤ/2`. The chart `chartAt x` supplies the
homeomorphism of pairs `chartLocalIso` consumes. The per-point local generator of the fundamental
class `[M]`. -/
noncomputable def manifoldLocalIso {m : ℕ} {M : Type} [TopologicalSpace M] [T1Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] (x : M) :
    RelativeHomology (X := TopCat.of M) {y | y ≠ x} (m + 2) ≃ₗ[ZMod 2] ZMod 2 :=
  haveI : T1Space ↑(TopCat.of M) := inferInstanceAs (T1Space M)
  let c := chartAt (EuclideanSpace ℝ (Fin (m + 2))) x
  chartLocalIso (M := TopCat.of M) (x := x) (U := c.source) (V := c.target) (q := c x)
    c.open_source (mem_chart_source _ x) c.open_target (mem_chart_target _ x)
    c.toHomeomorphSourceTarget rfl

end SKEFTHawking.SingularChartBridge
