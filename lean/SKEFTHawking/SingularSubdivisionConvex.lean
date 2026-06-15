/-
# Phase 5q.F (w₂-foundation, brick 6c-c7c.2): the barycentric subdivision stays in a convex set

The affine subdivision engine (`SingularExcisionMod2`: `linSubdiv`, `linHomotopy`, `cone`, `barycenter`)
operates on `LinChain V n` for a topological `ℝ`-module `V`, with vertices ranging over *all* of `V`.
For the **singular** subdivision we must push the subdivision of the standard simplex `Δᴺ` along a
singular simplex `σ : Δᴺ → X`; this requires every vertex of every sub-simplex to lie in
`stdSimplex ℝ (Fin (N+1)) ⊆ (Fin (N+1) → ℝ)`, so that the affine sub-simplices (`affineSimplexStd`,
`SingularExcisionPushforward`) — which land in `Δᴺ` only by convexity — are defined.

This file proves that invariant once and for all: the submodule `chainsIn S n` of `n`-chains whose
basis simplices have all vertices in a set `S` is preserved by `cone` (apex in `S`), `linBoundary`
(faces drop vertices), and — for `S` **convex** — `linSubdiv` and `linHomotopy` (the new vertices are
barycenters, i.e. convex combinations, of old ones). Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularExcisionMod2

namespace SKEFTHawking.SingularSubdivisionConvex

open SKEFTHawking.SingularExcisionMod2

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [ContinuousAdd V] [ContinuousSMul ℝ V]

/-- The submodule of affine `n`-chains whose every basis simplex has **all vertices in `S`**: the
`ℤ/2`-span of the single-tuples `[v]` with `v j ∈ S` for all `j`. The carrier of the "stays in `S`"
invariant for barycentric subdivision. -/
noncomputable def chainsIn (S : Set V) (n : ℕ) : Submodule (ZMod 2) (LinChain V n) :=
  Submodule.span (ZMod 2)
    {c | ∃ v : Fin (n + 1) → V, (∀ j, v j ∈ S) ∧ c = Finsupp.single v 1}

omit [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V] in
/-- A single simplex with all vertices in `S` lies in `chainsIn S n`. -/
theorem single_mem_chainsIn {S : Set V} {n : ℕ} {v : Fin (n + 1) → V} (hv : ∀ j, v j ∈ S) :
    Finsupp.single v 1 ∈ chainsIn S n :=
  Submodule.subset_span ⟨v, hv, rfl⟩

omit [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V] in
/-- The barycenter of a simplex with vertices in a convex set `S` lies in `S` (it is the convex
combination with equal weights `(n+1)⁻¹`). -/
theorem barycenter_mem {S : Set V} (hS : Convex ℝ S) {n : ℕ} {v : Fin (n + 1) → V}
    (hv : ∀ j, v j ∈ S) : barycenter v ∈ S := by
  have hsum : ((n : ℝ) + 1)⁻¹ • ∑ i, v i = ∑ i : Fin (n + 1), ((n : ℝ) + 1)⁻¹ • v i := by
    rw [Finset.smul_sum]
  rw [barycenter, hsum]
  have hne : (n : ℝ) + 1 ≠ 0 := by positivity
  refine hS.sum_mem (fun i _ => ?_) ?_ (fun i _ => hv i)
  · positivity
  · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add,
      Nat.cast_one, mul_inv_cancel₀ hne]

omit [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V] in
/-- `cone` with apex `b ∈ S` preserves `chainsIn S` (it prepends `b` to each simplex). -/
theorem cone_mem_chainsIn {S : Set V} {n : ℕ} {b : V} (hb : b ∈ S) {c : LinChain V n}
    (hc : c ∈ chainsIn S n) : cone b n c ∈ chainsIn S (n + 1) := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨v, hv, rfl⟩
    rw [cone_single]
    refine single_mem_chainsIn (fun j => ?_)
    refine Fin.cases hb (fun k => hv k) j
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro a x _ hx; rw [map_smul]; exact Submodule.smul_mem _ a hx

omit [AddCommGroup V] [Module ℝ V] [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V] in
/-- `linBoundary` preserves `chainsIn S` (the faces of a simplex use a subset of its vertices). -/
theorem linBoundary_mem_chainsIn {S : Set V} {n : ℕ} {c : LinChain V (n + 1)}
    (hc : c ∈ chainsIn S (n + 1)) : linBoundary n c ∈ chainsIn S n := by
  refine Submodule.span_induction ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨v, hv, rfl⟩
    rw [linBoundary_single, linBoundaryBasis]
    refine Submodule.sum_mem _ (fun i _ => single_mem_chainsIn (fun j => ?_))
    exact hv (i.succAbove j)
  · rw [map_zero]; exact Submodule.zero_mem _
  · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
  · intro a x _ hx; rw [map_smul]; exact Submodule.smul_mem _ a hx

omit [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V] in
/-- **The barycentric subdivision stays in a convex set `S`**: if every vertex of `c` lies in the
convex set `S`, so does every vertex of `Sd c` (the new vertices are barycenters of faces of the
old simplices). By induction on degree, threading `barycenter_mem`, `cone_mem`, `linBoundary_mem`. -/
theorem linSubdiv_mem_chainsIn {S : Set V} (hS : Convex ℝ S) :
    ∀ (n : ℕ) {c : LinChain V n}, c ∈ chainsIn S n → linSubdiv n c ∈ chainsIn S n
  | 0, c, hc => by rw [linSubdiv_zero]; exact hc
  | n + 1, c, hc => by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hc
    · rintro _ ⟨v, hv, rfl⟩
      rw [linSubdiv_single]
      refine cone_mem_chainsIn (barycenter_mem hS hv) ?_
      exact linSubdiv_mem_chainsIn hS n
        (linBoundary_mem_chainsIn (single_mem_chainsIn hv))
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
    · intro a x _ hx; rw [map_smul]; exact Submodule.smul_mem _ a hx

omit [TopologicalSpace V] [ContinuousAdd V] [ContinuousSMul ℝ V] in
/-- **The subdivision chain homotopy `D` stays in a convex set `S`** (same barycentric mechanism as
`linSubdiv`). Needed to keep the singular homotopy's pushforward well-defined. -/
theorem linHomotopy_mem_chainsIn {S : Set V} (hS : Convex ℝ S) :
    ∀ (n : ℕ) {c : LinChain V n}, c ∈ chainsIn S n → linHomotopy n c ∈ chainsIn S (n + 1)
  | 0, c, hc => by rw [linHomotopy_zero_map]; exact Submodule.zero_mem _
  | n + 1, c, hc => by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hc
    · rintro _ ⟨v, hv, rfl⟩
      rw [linHomotopy_single_smul, one_smul]
      refine cone_mem_chainsIn (barycenter_mem hS hv) ?_
      refine Submodule.add_mem _ (single_mem_chainsIn hv) ?_
      exact linHomotopy_mem_chainsIn hS n
        (linBoundary_mem_chainsIn (single_mem_chainsIn hv))
    · rw [map_zero]; exact Submodule.zero_mem _
    · intro x y _ _ hx hy; rw [map_add]; exact Submodule.add_mem _ hx hy
    · intro a x _ hx; rw [map_smul]; exact Submodule.smul_mem _ a hx

end SKEFTHawking.SingularSubdivisionConvex
