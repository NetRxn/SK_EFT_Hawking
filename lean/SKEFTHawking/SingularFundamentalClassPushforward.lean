import Mathlib
import SKEFTHawking.SingularFundamentalClassExist
import SKEFTHawking.SingularFunctoriality
import SKEFTHawking.SingularConvexStageIso

/-!
# Phase 5q.G (G3 F-ladder, F4) — the fundamental class pushes forward along homeomorphisms

`Hₘ₊₂(e)([M]) = [N]` for a homeomorphism `e : M ≃ₜ N` of closed charted manifolds. Route =
the point-restriction characterization: `[N]` is the *unique* class restricting to the local
generator at every point (uniqueness = the char-2 difference trick + the determined-by-points
property at `univ`, `goodCompact_univ.2` — no connectedness needed, so disjoint unions are
covered); the pushforward restricts at `e x` to the `RelativeHomology.map`-image of the local
generator at `x` (naturality of `restrictHomologyToPoint`, pure `RelativeHomology.map_comp`),
which is *nonzero* (the pair-map along a homeo is bijective) and hence *the* generator of
`Hₘ₊₂(N | e x) ≅ ℤ/2` (`linearEquiv_zmod2_apply_eq_one` — a 1-dim ℤ/2-space has one nonzero
element). Feeds F5 (PD-instance transport) and F6 (wuW2 homeo-invariance).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeMV SKEFTHawking.SingularRelativeEmpty
open SKEFTHawking.SingularRelativeFunctoriality SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularManifoldFundamentalClass SKEFTHawking.SingularFundamentalClass

namespace SKEFTHawking.SingularFundamentalClassPushforward

/-- **A top class vanishing at every point is zero** (the determined-by-points property at
`univ`, connectedness-free): the tail of `restrictHomologyToPoint_injective` extracted — works
for disconnected closed manifolds, where the clopen argument is unavailable. -/
theorem homology_eq_zero_of_forall_restrict_zero {m : ℕ} {M : Type} [TopologicalSpace M]
    [T2Space M] [CompactSpace M] [Nonempty M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] {α : Homology (TopCat.of M) (m + 2)}
    (hall : ∀ x : M, restrictHomologyToPoint (X := TopCat.of M) x (m + 2) α = 0) : α = 0 := by
  have hdet := (SingularGoodCompactManifold.goodCompact_univ (m := m) (M := M)).2
  have hβ0 : restrictHomologyToSet (X := TopCat.of M) (Set.univ : Set ↑(TopCat.of M)) (m + 2) α
      = 0 :=
    hdet (restrictHomologyToSet (Set.univ : Set ↑(TopCat.of M)) (m + 2) α)
      (fun x hx => by rw [restrictToPoint_restrictHomologyToSet hx (m + 2) α]; exact hall x)
  have huniv_empty : (Set.univ : Set ↑(TopCat.of M))ᶜ ⊆ (∅ : Set ↑(TopCat.of M)) :=
    Set.compl_univ.subset
  have hγ : (relHomologyEmptyEquiv (X := TopCat.of M) (m + 2)).symm α = 0 := by
    have hback : relIncl huniv_empty (m + 2)
        (restrictHomologyToSet (Set.univ : Set ↑(TopCat.of M)) (m + 2) α)
        = (relHomologyEmptyEquiv (X := TopCat.of M) (m + 2)).symm α := by
      show relIncl huniv_empty (m + 2)
          (relIncl (Set.empty_subset (Set.univ : Set ↑(TopCat.of M))ᶜ) (m + 2)
            ((relHomologyEmptyEquiv (X := TopCat.of M) (m + 2)).symm α))
        = (relHomologyEmptyEquiv (X := TopCat.of M) (m + 2)).symm α
      rw [relIncl_trans, relIncl, RelativeHomology.map_id]
      rfl
    rw [hβ0, map_zero] at hback
    exact hback.symm
  have hα := congrArg (relHomologyEmptyEquiv (X := TopCat.of M) (m + 2)) hγ
  rwa [LinearEquiv.apply_symm_apply, map_zero] at hα

/-- **Uniqueness of the fundamental class**: any class restricting to the local generator at
every point equals `[M]` — the char-2 difference trick on
`homology_eq_zero_of_forall_restrict_zero`. -/
theorem eq_fundamentalClass_of_restricts_generator {m : ℕ} {M : Type} [TopologicalSpace M]
    [T2Space M] [CompactSpace M] [Nonempty M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M] {α : Homology (TopCat.of M) (m + 2)}
    (h : ∀ x : M, restrictHomologyToPoint (X := TopCat.of M) x (m + 2) α
      = (SKEFTHawking.SingularChartBridge.manifoldLocalIso x).symm 1) :
    α = fundamentalClass (m := m) (M := M) := by
  have hsum : ∀ x : M, restrictHomologyToPoint (X := TopCat.of M) x (m + 2)
      (α + fundamentalClass (m := m) (M := M)) = 0 := by
    intro x
    rw [map_add, h x, fundamentalClass_restricts (m := m) x, ZModModule.add_self]
  have h0 := homology_eq_zero_of_forall_restrict_zero hsum
  have h1 := congrArg (· + fundamentalClass (m := m) (M := M)) h0
  simpa [add_assoc, ZModModule.add_self] using h1

/-- **Naturality of `relHomologyEmptyEquiv`**: the `(X,∅) → (Y,∅)` pair-map matches the absolute
map across the empty-pair identification — chain-level `mk`-pushes. -/
theorem emptyEquiv_naturality {X Y : TopCat} (φ : C(↑X, ↑Y)) (n : ℕ)
    (β : RelativeHomology (∅ : Set ↑X) n) :
    Homology.map φ n (relHomologyEmptyEquiv (X := X) n β)
      = relHomologyEmptyEquiv (X := Y) n
        (RelativeHomology.map φ (Set.mapsTo_empty ⇑φ ∅) n β) := by
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ β
  show Homology.map φ n (Homology.mk X n (cyclesEmptyEquiv n w))
      = Homology.mk Y n (cyclesEmptyEquiv n (relCyclesMap φ (Set.mapsTo_empty ⇑φ ∅) n w))
  rw [Homology.map_mk]
  refine congrArg _ (Subtype.ext ?_)
  rw [cyclesMap_coe, cyclesEmptyEquiv_coe, cyclesEmptyEquiv_coe, relCyclesMap_coe]
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (w : RelativeChain (∅ : Set ↑X) n)
  rw [show (Submodule.Quotient.mk c : RelativeChain (∅ : Set ↑X) n)
      = RelativeChain.mk (∅ : Set ↑X) n c from rfl] at hc
  rw [← hc, chainEmptyEquiv_mk, relMapChain_mk, chainEmptyEquiv_mk]

/-- **Naturality of the point restriction**: `ρ_{φ(x)} ∘ Hₙ(φ) = Hₙ(φ, pair) ∘ ρₓ` — both sides
are the pair-map `(X, ∅) → (Y, Y∖φ(x))`: `emptyEquiv_naturality` + the `relIncl_map` square. -/
theorem restrictHomologyToPoint_naturality {X Y : TopCat} (φ : C(↑X, ↑Y)) (x : ↑X)
    (hmt : Set.MapsTo φ ({x}ᶜ : Set ↑X) ({φ x}ᶜ : Set ↑Y)) (n : ℕ) (α : Homology X n) :
    restrictHomologyToPoint (X := Y) (φ x) n (Homology.map φ n α)
      = RelativeHomology.map φ hmt n (restrictHomologyToPoint (X := X) x n α) := by
  have hinner : (relHomologyEmptyEquiv (X := Y) n).symm (Homology.map φ n α)
      = RelativeHomology.map φ (Set.mapsTo_empty ⇑φ ∅) n
        ((relHomologyEmptyEquiv (X := X) n).symm α) := by
    rw [LinearEquiv.symm_apply_eq, ← emptyEquiv_naturality, LinearEquiv.apply_symm_apply]
  show relIncl (Set.empty_subset ({φ x}ᶜ : Set ↑Y)) n
      ((relHomologyEmptyEquiv (X := Y) n).symm (Homology.map φ n α))
    = RelativeHomology.map φ hmt n (relIncl (Set.empty_subset ({x}ᶜ : Set ↑X)) n
      ((relHomologyEmptyEquiv (X := X) n).symm α))
  rw [hinner, ← relIncl_map φ (Set.empty_subset ({x}ᶜ : Set ↑X)) (Set.mapsTo_empty ⇑φ ∅) hmt
    (Set.empty_subset ({φ x}ᶜ : Set ↑Y)) n]

/-- **F4 — the fundamental class pushes forward along a homeomorphism**:
`Hₘ₊₂(e)([M]) = [N]` for `e : M ≃ₜ N` (closed charted, possibly disconnected). -/
theorem fundamentalClass_map_homeo {m : ℕ} {M N : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) M]
    [TopologicalSpace N] [T2Space N] [CompactSpace N] [Nonempty N]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m + 2))) N] (e : M ≃ₜ N) :
    Homology.map (X := TopCat.of M) (Y := TopCat.of N) ⟨e, e.continuous⟩ (m + 2)
        (fundamentalClass (m := m) (M := M)) = fundamentalClass (m := m) (M := N) := by
  refine eq_fundamentalClass_of_restricts_generator (fun y => ?_)
  obtain ⟨x, rfl⟩ := e.surjective y
  have hmt : Set.MapsTo (⟨e, e.continuous⟩ : C(↑(TopCat.of M), ↑(TopCat.of N)))
      ({x}ᶜ : Set ↑(TopCat.of M)) ({e x}ᶜ : Set ↑(TopCat.of N)) :=
    fun z hz hez => hz (Set.mem_singleton_iff.mpr
      (e.injective (Set.mem_singleton_iff.mp hez)))
  have hmt' : Set.MapsTo (⟨e.symm, e.symm.continuous⟩ : C(↑(TopCat.of N), ↑(TopCat.of M)))
      ({e x}ᶜ : Set ↑(TopCat.of N)) ({x}ᶜ : Set ↑(TopCat.of M)) :=
    fun z hz hsz => hz (Set.mem_singleton_iff.mpr (by
      have h2 : e.symm z = x := Set.mem_singleton_iff.mp hsz
      rw [← h2, e.apply_symm_apply]))
  have hnat := restrictHomologyToPoint_naturality
    (⟨e, e.continuous⟩ : C(↑(TopCat.of M), ↑(TopCat.of N))) x hmt (m + 2)
    (fundamentalClass (m := m) (M := M))
  have hnat' : restrictHomologyToPoint (X := TopCat.of N) (e x) (m + 2)
      (Homology.map (X := TopCat.of M) (Y := TopCat.of N) ⟨e, e.continuous⟩ (m + 2)
        (fundamentalClass (m := m) (M := M)))
      = RelativeHomology.map (⟨e, e.continuous⟩ : C(↑(TopCat.of M), ↑(TopCat.of N))) hmt (m + 2)
        (restrictHomologyToPoint (X := TopCat.of M) x (m + 2)
          (fundamentalClass (m := m) (M := M))) := hnat
  rw [hnat', fundamentalClass_restricts (m := m) x]
  -- the image of the generator is nonzero, hence THE generator of `Hₘ₊₂(N|e x) ≅ ℤ/2`
  have hbij : Function.Bijective
      (RelativeHomology.map (⟨e, e.continuous⟩ : C(↑(TopCat.of M), ↑(TopCat.of N))) hmt
        (m + 2)) :=
    RelativeHomology.map_bijective_of_comp_id _ ⟨e.symm, e.symm.continuous⟩ hmt hmt'
      (by ext z; exact e.symm_apply_apply z) (by ext z; exact e.apply_symm_apply z) (m + 2)
  have hgen_ne : ((SKEFTHawking.SingularChartBridge.manifoldLocalIso x).symm 1 :
      RelativeHomology ({x}ᶜ : Set ↑(TopCat.of M)) (m + 2)) ≠ 0 := by
    intro h
    have h1 := congrArg (SKEFTHawking.SingularChartBridge.manifoldLocalIso x) h
    rw [LinearEquiv.apply_symm_apply, map_zero] at h1
    exact one_ne_zero h1
  have hv_ne : RelativeHomology.map (⟨e, e.continuous⟩ : C(↑(TopCat.of M), ↑(TopCat.of N)))
      hmt (m + 2) ((SKEFTHawking.SingularChartBridge.manifoldLocalIso x).symm 1) ≠ 0 :=
    fun h => hgen_ne (hbij.1 (by rw [h]; exact (map_zero _).symm))
  have h1 := SKEFTHawking.SingularConvexStageIso.linearEquiv_zmod2_apply_eq_one
    (SKEFTHawking.SingularChartBridge.manifoldLocalIso (e x)) hv_ne
  exact (LinearEquiv.eq_symm_apply _).mpr h1

end SKEFTHawking.SingularFundamentalClassPushforward
