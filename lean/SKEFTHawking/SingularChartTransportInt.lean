import Mathlib
import SKEFTHawking.SingularLocalHomologyIsoInt
import SKEFTHawking.SingularExcisionIsoInt
import SKEFTHawking.SingularManifoldFundamentalClass

/-!
# Integral chart-transport equivalences for relative homology (brick 18b)

The set-level (as opposed to single-point) transport equivalences the oriented fundamental-class
chart-cover induction rides on, over ℤ:

* `openSetExcisionEquivInt` — open-set excision `Hₙ₊₁(V, V∖K; ℤ) ≅ Hₙ₊₁(X, X∖K; ℤ)` for `K` closed,
  `V` open, `K ⊆ V`. The set version of `SingularLocalHomologyIsoInt.openPointExcisionEquivInt`; a
  direct instance of the integral excision iso `excisionEquivInt` over the cover `{Kᶜ, V}`.
* `chartPairEquiv_setInt` — a chart homeomorphism `e : U ≃ₜ V` matching `K ⊆ U` with `C ⊆ V`
  (`e u ∈ C ↔ u ∈ K`) induces `Hₖ(U, U∖K; ℤ) ≅ Hₖ(V, V∖C; ℤ)`. The set version of
  `SingularLocalHomologyIsoInt.chartPairEquivInt`.

Both reuse the **coefficient-free** topology helpers of the mod-2 development
(`cover_compl_open`, `mapsTo_chart_set`, `mapsTo_chart_set_symm`) — those are pure `Set.MapsTo` /
open-cover facts, independent of the coefficient ring — composed with the integral relative-homology
functor `RelHomologyInt.map` and the integral excision iso `excisionEquivInt`. These transport the
Euclidean/convex good-compactness (brick 18-convex) through a chart to the manifold level; MV-free.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeFunctorialityInt
open SKEFTHawking.SingularFunctorialityInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.SingularExcisionIsoInt (excisionEquivInt)

namespace SKEFTHawking.SingularChartTransportInt

variable {X : TopCat}

/-- **Integral open-set excision**: `Hₙ₊₁(V, V∖K; ℤ) ≅ Hₙ₊₁(X, X∖K; ℤ)` for `K` closed, `V` open,
`K ⊆ V`. The relative homology of `(X, X∖K)` only sees an open neighbourhood of the compact support
`K`. The ℤ mirror of `SingularManifoldFundamentalClass.openSetExcisionEquiv`; a direct instance of
`excisionEquivInt` over the open cover `{Kᶜ, V}` (the cover fact `cover_compl_open` is coefficient-free
topology, reused as-is). -/
noncomputable def openSetExcisionEquivInt {K : Set ↑X} (hK : IsClosed K) {V : Set ↑X} (hV : IsOpen V)
    (hKV : K ⊆ V) (n : ℕ) :
    RelHomologyInt (restr Kᶜ V) (n + 1) ≃ₗ[ℤ] RelHomologyInt Kᶜ (n + 1) :=
  excisionEquivInt Kᶜ V n
    (SKEFTHawking.SingularManifoldFundamentalClass.cover_compl_open hK hV hKV)

variable {M : TopCat}

/-- **The chart-pair homeomorphism induces an integral relative-homology iso** `Hₖ(U, U∖K; ℤ) ≅
Hₖ(V, V∖C; ℤ)`, when `e : U ≃ₜ V` matches `K ⊆ U` with `C ⊆ V` (`e u ∈ C ↔ u ∈ K`). The ℤ mirror of
`SingularManifoldFundamentalClass.chartPairEquiv_set` and the set-level version of
`SingularLocalHomologyIsoInt.chartPairEquivInt`: `RelHomologyInt.map` of the chart homeo, bijective by
`RelHomologyInt.map_bijective_of_comp_id` on the mutually-inverse chart maps (the `Set.MapsTo` facts
`mapsTo_chart_set`/`_symm` are coefficient-free, reused from the mod-2 development). -/
noncomputable def chartPairEquiv_setInt {U : Set ↑M} {V : Set ↑X} {K : Set ↑M} {C : Set ↑X}
    (e : ↥U ≃ₜ ↥V) (hcompat : ∀ u : ↥U, ((e u : ↑X) ∈ C) ↔ (u : ↑M) ∈ K) (k : ℕ) :
    RelHomologyInt (restr Kᶜ U) k ≃ₗ[ℤ] RelHomologyInt (restr Cᶜ V) k :=
  LinearEquiv.ofBijective
    (RelHomologyInt.map (⟨e, e.continuous⟩ : C(↑(sub U), ↑(sub V)))
      (SKEFTHawking.SingularManifoldFundamentalClass.mapsTo_chart_set e hcompat) k)
    (RelHomologyInt.map_bijective_of_comp_id (⟨e, e.continuous⟩ : C(↑(sub U), ↑(sub V)))
      (⟨e.symm, e.symm.continuous⟩ : C(↑(sub V), ↑(sub U)))
      (SKEFTHawking.SingularManifoldFundamentalClass.mapsTo_chart_set e hcompat)
      (SKEFTHawking.SingularManifoldFundamentalClass.mapsTo_chart_set_symm e hcompat)
      (ContinuousMap.ext fun v => e.symm_apply_apply v)
      (ContinuousMap.ext fun u => e.apply_symm_apply u) k)

end SKEFTHawking.SingularChartTransportInt
