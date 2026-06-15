/-
# Phase 5q.F (w₂-foundation, brick 6c-c7c.3): naturality of barycentric subdivision under linear maps

The affine subdivision `Sd = linSubdiv` is a **natural transformation** of the affine-chain functor on
`ℝ`-modules and linear maps: relabelling the vertices of a chain by a linear map `L : V →ₗ[ℝ] W`
(`mapVerts L = Finsupp.lmapDomain (L ∘ ·)`) commutes with `Sd` (and with `∂`, and with `cone`). This is
the algebraic core of the singular subdivision's chain-map property: the `i`-th facet inclusion
`Δⁿ⁻¹ ↪ Δⁿ` (`e_j ↦ e_{δ i j}`) is the restriction of the *linear* map `FunOnFinite.linearMap ℝ ℝ (δ i)`,
so `Sd (facet_i)_* = (facet_i)_* Sd`. Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularExcisionMod2

namespace SKEFTHawking.SingularSubdivisionNatural

open SKEFTHawking.SingularExcisionMod2

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [ContinuousAdd V] [ContinuousSMul ℝ V] [AddCommGroup W] [Module ℝ W] [TopologicalSpace W]
  [ContinuousAdd W] [ContinuousSMul ℝ W]

/-- **Vertex relabelling along a linear map** `L : V →ₗ[ℝ] W`: the `ℤ/2`-linear map on affine chains
`[v₀,…,vₙ] ↦ [L v₀,…,L vₙ]` (the `Finsupp` extension of post-composing each vertex-tuple with `L`). -/
noncomputable def mapVerts (L : V →ₗ[ℝ] W) (n : ℕ) :
    LinChain V n →ₗ[ZMod 2] LinChain W n :=
  Finsupp.lmapDomain (ZMod 2) (ZMod 2) (fun v => (L : V → W) ∘ v)

omit [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V] [TopologicalSpace W]
  [ContinuousAdd W] [ContinuousSMul ℝ W] in
theorem mapVerts_single (L : V →ₗ[ℝ] W) (n : ℕ) (v : Fin (n + 1) → V) (a : ZMod 2) :
    mapVerts L n (Finsupp.single v a) = Finsupp.single ((L : V → W) ∘ v) a := by
  rw [mapVerts, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]

omit [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V] [TopologicalSpace W]
  [ContinuousAdd W] [ContinuousSMul ℝ W] in
/-- A linear map carries a barycenter to the barycenter of the images (it commutes with the
convex-combination `(n+1)⁻¹ ∑`). -/
theorem map_barycenter (L : V →ₗ[ℝ] W) {n : ℕ} (v : Fin (n + 1) → V) :
    L (barycenter v) = barycenter ((L : V → W) ∘ v) := by
  rw [barycenter, barycenter, map_smul, map_sum]
  rfl

omit [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V] [TopologicalSpace W]
  [ContinuousAdd W] [ContinuousSMul ℝ W] in
/-- `mapVerts` commutes with `cone` (apex `b ↦ L b`). -/
theorem mapVerts_cone (L : V →ₗ[ℝ] W) (b : V) (n : ℕ) (c : LinChain V n) :
    mapVerts L (n + 1) (cone b n c) = cone (L b) n (mapVerts L n c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add, hc, hd]
  | single v a =>
    simp only [cone_single_smul, map_smul, mapVerts_single, Fin.comp_cons]

omit [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V] [TopologicalSpace W]
  [ContinuousAdd W] [ContinuousSMul ℝ W] in
/-- `mapVerts` commutes with the affine boundary `∂` (relabelling vertices commutes with dropping them). -/
theorem mapVerts_linBoundary (L : V →ₗ[ℝ] W) (n : ℕ) (c : LinChain V (n + 1)) :
    mapVerts L n (linBoundary n c) = linBoundary n (mapVerts L (n + 1) c) := by
  induction c using Finsupp.induction_linear with
  | zero => simp only [map_zero]
  | add c d hc hd => simp only [map_add, hc, hd]
  | single v a =>
    rw [linBoundary_single_smul, map_smul, mapVerts_single, linBoundary_single_smul, mapVerts,
      Finsupp.lmapDomain_apply, linBoundaryBasis, linBoundaryBasis, Finsupp.mapDomain_finset_sum]
    refine congrArg (a • ·) (Finset.sum_congr rfl fun i _ => ?_)
    rw [Finsupp.mapDomain_single]
    rfl

omit [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V] [TopologicalSpace W]
  [ContinuousAdd W] [ContinuousSMul ℝ W] in
/-- **The barycentric subdivision is natural under linear maps**: `Sd ∘ L_* = L_* ∘ Sd`. Induction on
degree, using `map_barycenter` (apex), `mapVerts_cone`, `mapVerts_linBoundary`. This is the facet-inclusion
naturality that powers the singular chain-map `∂Sd = Sd∂`. -/
theorem mapVerts_linSubdiv (L : V →ₗ[ℝ] W) :
    ∀ (n : ℕ) (c : LinChain V n), mapVerts L n (linSubdiv n c) = linSubdiv n (mapVerts L n c)
  | 0, c => by rw [linSubdiv_zero, linSubdiv_zero]
  | n + 1, c => by
    induction c using Finsupp.induction_linear with
    | zero => simp only [map_zero]
    | add c d hc hd => simp only [map_add, hc, hd]
    | single v a =>
      rw [linSubdiv_single_smul, map_smul, mapVerts_cone, map_barycenter, mapVerts_linSubdiv L n,
        mapVerts_linBoundary, mapVerts_single, ← linSubdiv_single_smul, mapVerts_single]

end SKEFTHawking.SingularSubdivisionNatural
