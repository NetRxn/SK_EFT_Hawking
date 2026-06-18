import Mathlib
import SKEFTHawking.SingularPairLES
import SKEFTHawking.SingularRelativeMV
import SKEFTHawking.SingularChartBridge
import SKEFTHawking.SingularEuclideanAcyclic
import SKEFTHawking.SingularConvexComplementRetract
import SKEFTHawking.SingularSphereHighDegree

/-!
# Phase 5q.F (w₂-foundation, brick 6e) — toward the fundamental class `[M]`

Building `Hₙ(M; ℤ/2) ≅ ℤ/2` for a closed `n`-manifold (Hatcher Lemma 3.27) on this phase's hand-rolled
singular ℤ/2 homology. The engine is the relative Mayer–Vietoris LES (`SingularRelativeMV`); the local
input is `Hₙ(M | x) ≅ ℤ/2` (`SingularChartBridge.manifoldLocalIso`). This file collects the
pair-LES reductions and the compactness induction.

First brick: the **pair-LES connecting isomorphism for an acyclic ambient**
`Hₙ₊₁(X, A) ≅ Hₙ(A)` when `Hₙ₊₁(X) = Hₙ(X) = 0` — the reduction `Hₙ(ℝⁿ, ℝⁿ∖A) ≅ H̃ₙ₋₁(ℝⁿ∖A)` used in the
convex base case. Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularPairLES SKEFTHawking.SingularExcisionIso
open SKEFTHawking.SingularRelativeFunctoriality SKEFTHawking.SingularRelativeMV

namespace SKEFTHawking.SingularManifoldFundamentalClass

variable {X : TopCat}

/-- The open cover `{Kᶜ, V}` of `X` when `K` is closed, `V` open, and `K ⊆ V`. -/
theorem cover_compl_open {K : Set ↑X} (hK : IsClosed K) {V : Set ↑X} (hV : IsOpen V) (hKV : K ⊆ V) :
    (⋃ U ∈ ({Kᶜ, V} : Set (Set ↑X)), interior U) = Set.univ := by
  rw [Set.biUnion_pair, hK.isOpen_compl.interior_eq, hV.interior_eq, Set.eq_univ_iff_forall]
  intro x
  by_cases h : x ∈ K
  · exact Or.inr (hKV h)
  · exact Or.inl h

/-- **Open-set excision**: `Hₙ₊₁(V, V∖K) ≅ Hₙ₊₁(X, X∖K)` for `K` closed, `V` open, `K ⊆ V`. The
relative homology of `(X, X∖K)` only sees an open neighborhood of the compact `K` — the set version of
`openPointExcisionEquiv`. -/
noncomputable def openSetExcisionEquiv {K : Set ↑X} (hK : IsClosed K) {V : Set ↑X} (hV : IsOpen V)
    (hKV : K ⊆ V) (n : ℕ) :
    RelativeHomology (restr Kᶜ V) (n + 1) ≃ₗ[ZMod 2] RelativeHomology Kᶜ (n + 1) :=
  excisionEquiv Kᶜ V n (cover_compl_open hK hV hKV)

variable {M : TopCat}

/-- The chart homeo `e : U ≃ₜ V` maps `(U, U∖K) → (V, V∖C)` when `e` matches `K` with `C`
(`e u ∈ C ↔ u ∈ K`). -/
theorem mapsTo_chart_set {U : Set ↑M} {V : Set ↑X} {K : Set ↑M} {C : Set ↑X} (e : ↥U ≃ₜ ↥V)
    (hcompat : ∀ u : ↥U, ((e u : ↑X) ∈ C) ↔ (u : ↑M) ∈ K) :
    Set.MapsTo (⟨e, e.continuous⟩ : C(↑(sub U), ↑(sub V))) (restr Kᶜ U) (restr Cᶜ V) := by
  intro u hu
  simp only [restr, Set.mem_preimage, Set.mem_compl_iff, ContinuousMap.coe_mk] at hu ⊢
  exact fun hC => hu ((hcompat u).mp hC)

/-- The reverse chart map sends `(V, V∖C) → (U, U∖K)`. -/
theorem mapsTo_chart_set_symm {U : Set ↑M} {V : Set ↑X} {K : Set ↑M} {C : Set ↑X} (e : ↥U ≃ₜ ↥V)
    (hcompat : ∀ u : ↥U, ((e u : ↑X) ∈ C) ↔ (u : ↑M) ∈ K) :
    Set.MapsTo (⟨e.symm, e.symm.continuous⟩ : C(↑(sub V), ↑(sub U))) (restr Cᶜ V) (restr Kᶜ U) := by
  intro v hv
  simp only [restr, Set.mem_preimage, Set.mem_compl_iff, ContinuousMap.coe_mk] at hv ⊢
  intro hK
  exact hv (by rw [← e.apply_symm_apply v]; exact (hcompat (e.symm v)).mpr hK)

/-- **The chart-pair homeomorphism induces a relative-homology iso** `Hₖ(U, U∖K) ≅ Hₖ(V, V∖C)` (the
set version of `SingularChartBridge.chartPairEquiv`). -/
noncomputable def chartPairEquiv_set {U : Set ↑M} {V : Set ↑X} {K : Set ↑M} {C : Set ↑X}
    (e : ↥U ≃ₜ ↥V) (hcompat : ∀ u : ↥U, ((e u : ↑X) ∈ C) ↔ (u : ↑M) ∈ K) (k : ℕ) :
    RelativeHomology (restr Kᶜ U) k ≃ₗ[ZMod 2] RelativeHomology (restr Cᶜ V) k :=
  LinearEquiv.ofBijective
    (RelativeHomology.map (⟨e, e.continuous⟩ : C(↑(sub U), ↑(sub V))) (mapsTo_chart_set e hcompat) k)
    (RelativeHomology.map_bijective_of_comp_id (⟨e, e.continuous⟩ : C(↑(sub U), ↑(sub V)))
      (⟨e.symm, e.symm.continuous⟩ : C(↑(sub V), ↑(sub U))) (mapsTo_chart_set e hcompat)
      (mapsTo_chart_set_symm e hcompat)
      (ContinuousMap.ext fun v => e.symm_apply_apply v)
      (ContinuousMap.ext fun u => e.apply_symm_apply u) k)

/-- **The pair-LES connecting map is an isomorphism over an acyclic ambient**: if `Hₙ₊₁(X) = 0` and
`Hₙ(X) = 0`, then `δ : Hₙ₊₁(X, A) → Hₙ(A)` is bijective. (Injective: `ker δ = range j_* = 0` since
`Hₙ₊₁(X) = 0`. Surjective: `range δ = ker i_* = ⊤` since `Hₙ(X) = 0`.) The reduction
`Hₙ(ℝⁿ, ℝⁿ∖A) ≅ Hₙ₋₁(ℝⁿ∖A)`. -/
theorem connecting_bijective_of_acyclic (S : Set ↑X) (n : ℕ)
    (h1 : ∀ x : Homology X (n + 1), x = 0) (h0 : ∀ x : Homology X n, x = 0) :
    Function.Bijective (connecting S n) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, hy⟩ := (exact_homProj_connecting S n x).mp hx
    rw [← hy, h1 y, map_zero]
  · intro y
    exact (exact_connecting_homIncl S n y).mp (h0 _)

/-- The acyclic-ambient connecting isomorphism `Hₙ₊₁(X, A) ≃ₗ Hₙ(A)`. -/
noncomputable def connectingEquiv_of_acyclic (S : Set ↑X) (n : ℕ)
    (h1 : ∀ x : Homology X (n + 1), x = 0) (h0 : ∀ x : Homology X n, x = 0) :
    RelativeHomology S (n + 1) ≃ₗ[ZMod 2] Homology (sub S) n :=
  LinearEquiv.ofBijective (connecting S n) (connecting_bijective_of_acyclic S n h1 h0)

/-- **`ℝⁿ` is acyclic in positive degree**: `Hₖ₊₁(ℝⁿ; ℤ/2) = 0` (every cycle is a boundary, from the
straight-line contraction `SingularEuclideanAcyclic.cycle_mem_boundaries`). -/
theorem eucl_homology_zero (n k : ℕ) (x : Homology (SingularEuclideanAcyclic.Eucl n) (k + 1)) :
    x = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  refine (Submodule.Quotient.mk_eq_zero _).2 ?_
  rw [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype]
  exact SingularEuclideanAcyclic.cycle_mem_boundaries n k z (LinearMap.mem_ker.mp z.2)

/-- **The local relative homology of `ℝⁿ` rel a subset `A`** reduces to the subspace:
`Hₖ₊₂(ℝⁿ, A) ≅ Hₖ₊₁(A)` (the acyclic-ambient connecting iso, `n = m+2`). -/
noncomputable def euclRelHomologyEquiv (m : ℕ) (A : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2)))
    (k : ℕ) :
    RelativeHomology A (k + 1 + 1) ≃ₗ[ZMod 2] Homology (sub A) (k + 1) :=
  connectingEquiv_of_acyclic A (k + 1) (eucl_homology_zero (m + 2) (k + 1))
    (eucl_homology_zero (m + 2) k)

/-- **The local homology of `ℝⁿ` rel a compact convex `A`** is `ℤ/2`: `Hₘ₊₂(ℝⁿ, ℝⁿ∖A) ≅ ℤ/2`
(`n = m+2`, `0 ∈ interior A`). The convex base case of Hatcher 3.27 — assembled from the acyclic
connecting iso, the convex-complement radial retract (`ℝⁿ∖A ≃ ℝⁿ∖0`), and the punctured/sphere
local model (`normalize` + `topSphereIso`), exactly as `localHomologyIso` does for a point. -/
noncomputable def euclConvexLocalHomologyIso (m : ℕ)
    {A : Set (EuclideanSpace ℝ (Fin (m + 2)))} (hAc : Convex ℝ A) (hAcomp : IsCompact A)
    (hA0 : A ∈ nhds (0 : EuclideanSpace ℝ (Fin (m + 2)))) :
    RelativeHomology (X := SingularEuclideanAcyclic.Eucl (m + 2)) Aᶜ (m + 2) ≃ₗ[ZMod 2] ZMod 2 :=
  (euclRelHomologyEquiv m Aᶜ m).trans
    ((LinearEquiv.ofBijective _
        (SingularConvexComplementRetract.homology_map_inclMap_bijective hAc hAcomp hA0 m)).trans
      ((LinearEquiv.ofBijective _
          (SingularPuncturedRetract.homology_map_normalize_bijective (n := m + 2) m)).trans
        (SingularLineMinusPoint.topSphereIso m)))

/-- **High-degree vanishing of the convex local homology in `ℝⁿ`**: `Hᵢ(ℝⁿ, ℝⁿ∖A) = 0` for `i > n`
(`n = m+2`, `A` compact convex, `0 ∈ interior A`). Same retract chain as `euclConvexLocalHomologyIso`,
but landing in `Hᵢ₋₁(Sⁿ⁻¹) = 0` (`sphere_homology_high`) instead of the top `ℤ/2`. The other half of the
convex base case — `Hᵢ(M|K) = 0` away from the middle dimension. -/
theorem euclConvexLocalHomology_high (m : ℕ) {A : Set (EuclideanSpace ℝ (Fin (m + 2)))}
    (hAc : Convex ℝ A) (hAcomp : IsCompact A)
    (hA0 : A ∈ nhds (0 : EuclideanSpace ℝ (Fin (m + 2)))) (k : ℕ) (hk : m + 1 ≤ k)
    (x : RelativeHomology (X := SingularEuclideanAcyclic.Eucl (m + 2)) Aᶜ (k + 1 + 1)) : x = 0 := by
  have e := (euclRelHomologyEquiv m Aᶜ k).trans
    ((LinearEquiv.ofBijective _
        (SingularConvexComplementRetract.homology_map_inclMap_bijective hAc hAcomp hA0 k)).trans
      (LinearEquiv.ofBijective _
        (SingularPuncturedRetract.homology_map_normalize_bijective (n := m + 2) k)))
  exact e.injective (by
    rw [map_zero]
    exact SingularSphereHighDegree.sphere_homology_high (m + 1) (k + 1) (by omega) (e x))

/-- **The convex base case (Hatcher 3.27) in a manifold**: `Hₘ₊₂(M | K) = Hₘ₊₂(M, M∖K) ≅ ℤ/2` for `K`
a compact convex set in a chart, matched by the chart `e` with a compact convex `C ⊆ ℝⁿ` (`0 ∈ int C`).
Assembled from open-set excision (at `M` and at `ℝⁿ`), the chart-pair transport, and the Euclidean
convex local model. The base case the relative-MV compactness induction builds on. -/
noncomputable def manifoldConvexLocalHomologyIso {M : TopCat} {m : ℕ} {K : Set ↑M}
    {U : Set ↑M} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U)
    {C : Set (EuclideanSpace ℝ (Fin (m + 2)))} {V : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))}
    (hCconv : Convex ℝ C) (hCcomp : IsCompact C)
    (hC0 : C ∈ nhds (0 : EuclideanSpace ℝ (Fin (m + 2)))) (hV : IsOpen V) (hCV : C ⊆ V)
    (e : ↥U ≃ₜ ↥V)
    (hcompat : ∀ u : ↥U, ((e u : ↑(SingularEuclideanAcyclic.Eucl (m + 2))) ∈ C) ↔ (u : ↑M) ∈ K) :
    RelativeHomology (X := M) Kᶜ (m + 2) ≃ₗ[ZMod 2] ZMod 2 :=
  (openSetExcisionEquiv hK hU hKU (m + 1)).symm.trans
    ((chartPairEquiv_set e hcompat (m + 2)).trans
      ((openSetExcisionEquiv hCcomp.isClosed hV hCV (m + 1)).trans
        (euclConvexLocalHomologyIso m hCconv hCcomp hC0)))

/-- **High-degree vanishing of the convex local homology in a manifold**: `Hᵢ(M | K) = 0` for `i > n`
(`n = m+2`, `K` a compact convex chart set). Transported (open-set excision + chart-pair) to the
Euclidean `euclConvexLocalHomology_high`. The "`Hᵢ(M|K) = 0` for `i > n`" base case of the
relative-MV compactness induction. -/
theorem manifoldConvexLocalHomology_high {M : TopCat} {m : ℕ} {K : Set ↑M}
    {U : Set ↑M} (hK : IsClosed K) (hU : IsOpen U) (hKU : K ⊆ U)
    {C : Set (EuclideanSpace ℝ (Fin (m + 2)))} {V : Set ↑(SingularEuclideanAcyclic.Eucl (m + 2))}
    (hCconv : Convex ℝ C) (hCcomp : IsCompact C)
    (hC0 : C ∈ nhds (0 : EuclideanSpace ℝ (Fin (m + 2)))) (hV : IsOpen V) (hCV : C ⊆ V)
    (e : ↥U ≃ₜ ↥V)
    (hcompat : ∀ u : ↥U, ((e u : ↑(SingularEuclideanAcyclic.Eucl (m + 2))) ∈ C) ↔ (u : ↑M) ∈ K)
    (k : ℕ) (hk : m + 1 ≤ k)
    (x : RelativeHomology (X := M) Kᶜ (k + 1 + 1)) : x = 0 := by
  have e' := (openSetExcisionEquiv hK hU hKU (k + 1)).symm.trans
    ((chartPairEquiv_set e hcompat (k + 1 + 1)).trans
      (openSetExcisionEquiv hCcomp.isClosed hV hCV (k + 1)))
  exact e'.injective (by
    rw [map_zero]
    exact euclConvexLocalHomology_high m hCconv hCcomp hC0 k hk (e' x))

/-! ### The relative-MV gluing step of the compactness induction -/

/-- **MV gluing injectivity** (Hatcher 3.27): `Hₖ(M | A∪B) → Hₖ(M | A) ⊕ Hₖ(M | B)` is injective when
`Hₖ₊₁(M | A∩B) = 0` (the inductive hypothesis). In the `U = M∖A`, `V = M∖B` form: `relMvHomDiag` is
injective once `Hₖ₊₁(M, U∪V) = 0`, directly from the relative MV exactness `range δ = ker Δ_*`. -/
theorem relMvHomDiag_injective_of_acyclic {U V : Set ↑X} (hU : IsOpen U) (hV : IsOpen V) (k : ℕ)
    (h : ∀ x : RelativeHomology (U ∪ V) (k + 1), x = 0) :
    Function.Injective (relMvHomDiag U V k) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  obtain ⟨y, hy⟩ := (relMv_exact_connecting' U V hU hV k x).mp hx
  rw [← hy, h y, map_zero]

/-- **MV vanishing propagation** (the "`Hᵢ(M|K) = 0` for `i > n`" half of Hatcher 3.27): if both
`Hₖ₊₁(M | A) = 0` and `Hₖ₊₁(M | B) = 0`, and `Hₖ₊₂(M | A∩B) = 0`, then `Hₖ₊₁(M | A∪B) = 0`. In the
`U = M∖A`, `V = M∖B` form: `Hₖ₊₁(M, U∩V) = 0` follows because `relMvHomDiag` is injective (gluing) and
its target `Hₖ₊₁(M,U) ⊕ Hₖ₊₁(M,V)` vanishes. -/
theorem relInter_acyclic_of_acyclic {U V : Set ↑X} (hU : IsOpen U) (hV : IsOpen V) (k : ℕ)
    (hUV : ∀ x : RelativeHomology (U ∪ V) (k + 1 + 1), x = 0)
    (hU' : ∀ x : RelativeHomology U (k + 1), x = 0)
    (hV' : ∀ x : RelativeHomology V (k + 1), x = 0) :
    ∀ x : RelativeHomology (U ∩ V) (k + 1), x = 0 := by
  intro x
  have hinj := relMvHomDiag_injective_of_acyclic hU hV (k + 1) hUV
  refine (injective_iff_map_eq_zero _).mp hinj x ?_
  exact Prod.ext (hU' _) (hV' _)

end SKEFTHawking.SingularManifoldFundamentalClass
