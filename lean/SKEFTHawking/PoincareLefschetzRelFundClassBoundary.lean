/-
# Phase 5q.H (W-A.1d/1f) — the good-BOUNDARY-chart star-convexity data (Wall 1 sub-obligation (a))

The `∂W` analog of the interior chart data (`PoincareLefschetzRelFundClassGeom.interiorChartLocalIso`)
that feeds the boundary local-homology vanishing `boundaryPoint_localHomology_zero`. The predecessor's
finding: a *general* `ModelWithCorners` chart image is not convex, so the boundary vanishing needs a
chart whose image `V ⊆ ℝⁿ` is a metric **half-ball** — convex (hence star-convex at every point,
including the boundary `q`) with a **star-convex punctured slit** `V∖q` (star from any *interior*
center `c'`). This module banks the architecture-independent convexity geometry those two star-convex
hypotheses need:

* `starConvex_diff_of_interior` — a convex `C` minus a point `q ∉ interior C` is star-convex from any
  interior center `c' ∈ interior C` (the open segment from an interior point stays in the interior,
  which avoids the boundary point `q`). The genuinely-new *relative* geometry: it is exactly what
  makes the boundary-slit `V∖q` acyclic.
* `halfBall_convex` / `punctured_halfBall_starConvex` — the metric-half-ball instances (intersection of
  a closed metric ball with a convex half-space), packaged for `boundaryPoint_localHomology_zero`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClassGeom

namespace SKEFTHawking.PoincareLefschetzRelFundClassBoundary

/-! ## §1. A convex set minus a boundary point is star-convex from an interior center -/

/-- **A convex set minus a non-interior point is star-convex from any interior center.** If `C` is
convex, `c' ∈ interior C`, and `q ∉ interior C`, then `C \ {q}` is star-convex at `c'`. The open
segment from the interior point `c'` to any `y ∈ C` lands in `interior C`
(`Convex.openSegment_interior_self_subset_interior`), which avoids `q`; the two endpoints `c'`
(interior, `≠ q`) and `y` (`≠ q` on the slit) are also in `C \ {q}`. This is the acyclicity mechanism
for a punctured half-ball `V ∖ q` at a boundary point `q` (`q` lies on the flat face, hence not in the
interior of the half-ball). -/
theorem starConvex_diff_of_interior {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E]
    [IsTopologicalAddGroup E] [ContinuousConstSMul ℝ E] {C : Set E} (hC : Convex ℝ C)
    {c' : E} (hc' : c' ∈ interior C) {q : E} (hq : q ∉ interior C) :
    StarConvex ℝ c' (C \ {q}) := by
  rw [starConvex_iff_segment_subset]
  intro y hy
  have hyC : y ∈ C := hy.1
  have hyq : y ≠ q := fun h => hy.2 (by rw [h]; rfl)
  have hc'C : c' ∈ C := interior_subset hc'
  have hc'q : c' ≠ q := fun h => hq (h ▸ hc')
  rw [← insert_endpoints_openSegment]
  intro z hz
  simp only [Set.mem_insert_iff] at hz
  rcases hz with rfl | rfl | hzopen
  · exact ⟨hc'C, hc'q⟩
  · exact ⟨hyC, hyq⟩
  · have hzint : z ∈ interior C :=
      hC.openSegment_interior_self_subset_interior hc' hyC hzopen
    exact ⟨interior_subset hzint, fun h => hq (h ▸ hzint)⟩

/-! ## §2. Boundary vanishing from a convex chart image with `q` on its boundary

The clean reduction of the two star-convex hypotheses of
`PoincareLefschetzRelFundClassGeom.boundaryPoint_localHomology_zero` to the single natural condition
on the chart image: **`V` convex, the chart point `q` on its topological boundary (`q ∉ interior V`),
and `interior V` nonempty** (witnessed by an interior center `c'`). A metric half-ball at a boundary
point of a half-space-modeled `W` is exactly such a `V` (convex, `q` on the flat face, nonempty
interior). This absorbs `starConvex_diff_of_interior` (for the punctured slit) and
`Convex.starConvex` (for the whole `V`), leaving only the *convex chart extraction* geometry. -/

open SKEFTHawking.SingularEuclideanAcyclic (Eucl)
open SKEFTHawking.SingularRelativeHomologyMod2

/-- **Boundary-point local-homology vanishing from a convex chart** `Hₙ(W, W∖x) = 0`. At a point `x`
with a chart `e : U ≃ₜ V` (`U` open in `W ∋ x`, `V ⊆ ℝⁿ` **convex**, `e x = q` with `q` on the
topological boundary of `V`, i.e. `q ∉ interior V`) and a nonempty interior (`c' ∈ interior V`), the
pair-local homology at `x` vanishes. The two star-convex hypotheses of
`boundaryPoint_localHomology_zero` are supplied here: `V` is star-convex at `c'`
(`Convex.starConvex`), and `V ∖ q` is star-convex at `c'` (`starConvex_diff_of_interior`, since
`q ∉ interior V`). For a *boundary* point the half-space chart image is a convex half-ball with `q` on
its flat face — hence not interior — and nonempty interior; the interior center `c'` discharges both
witnesses. -/
theorem boundaryPoint_localHomology_zero_of_convex {W : TopCat} [T1Space ↑W] {m : ℕ}
    {x : ↑W} {U : Set ↑W} (hU : IsOpen U) (hx : x ∈ U)
    {q : ↑(Eucl (m + 2))} {V : Set ↑(Eucl (m + 2))} (hq : q ∈ V)
    (e : ↥U ≃ₜ ↥V) (hex : (e ⟨x, hx⟩ : ↑(Eucl (m + 2))) = q)
    (hVconv : Convex ℝ V) (hqbd : q ∉ interior V)
    {c' : EuclideanSpace ℝ (Fin (m + 2))} (hc'int : c' ∈ interior V)
    (α : RelativeHomology (X := W) ({x}ᶜ) (m + 2)) : α = 0 := by
  have hc'V : c' ∈ V := interior_subset hc'int
  have hc'q : c' ≠ q := fun h => hqbd (h ▸ hc'int)
  exact PoincareLefschetzRelFundClassGeom.boundaryPoint_localHomology_zero hU hx hq e hex
    (c := c') (hVconv.starConvex hc'V) hc'V
    (c' := c') (starConvex_diff_of_interior hVconv hc'int hqbd) ⟨hc'V, hc'q⟩ α

/-! ## §3. The interior-cover determination step (Wall 2 — `DeterminedByInteriorPoints`)

Wall 2's "interior chart-balls contribute the closed-case determination" mechanism, isolated as an
architecture-independent brick. A relative class `α ∈ Hₙ(W, S)` (`S := ∂W`) that restricts to `0` at
every interior point (`restrictBd = 0` on `Sᶜ`) already restricts to `0` on any **interior compact**
`K ⊆ Sᶜ` that is `determinedByPoints n K` (the closed-case degree-`n` half, `SingularGoodCompact`):
its image `relIncl(S ⊆ Kᶜ) α ∈ Hₙ(W, Kᶜ)` vanishes, because at each `y ∈ K` the closed-case
restriction `restrictToPoint` factors through the relative `restrictBd` (both are the single `relIncl`
over `S ⊆ {y}ᶜ`), which is `0` by hypothesis. Boundary chart-balls contribute nothing (their local
group is `0` — slice 2). What remains for the full wall is exactly the **collar-injectivity** residual:
that some interior compact family makes `relIncl(S ⊆ Kᶜ)` injective (Mathlib has no collar-neighbourhood
theorem; for a *product-boundary* `W = Σ × [0,1]` the collar `Σ × [0,ε)` is explicit). This module
banks the true, unconditional step and the exact conditional reduction to that residual. -/

open SKEFTHawking.SingularManifoldFundamentalClass SKEFTHawking.SingularRelativeMV
open SKEFTHawking.PoincareLefschetzRelFundClass

/-- **Interior-cover determination step**: a relative class `α ∈ Hₙ(W, S)` restricting to `0` at every
point off `S` (`restrictBd = 0` on `Sᶜ`) has `relIncl(S ⊆ Kᶜ) α = 0` for any interior compact
`K ⊆ Sᶜ` that is `determinedByPoints n K`. At each `y ∈ K` the closed-case restriction
`restrictToPoint` collapses (`relIncl_trans`) to the relative `restrictBd S (y∉S)`, which is `0` by
hypothesis, so `determinedByPoints n K` forces the image to vanish. The genuine reusable content of
Wall 2's interior step. -/
theorem relIncl_eq_zero_of_restrictBd_zero {X : TopCat} {S K : Set ↑X} (hKS : K ⊆ Sᶜ) {n : ℕ}
    (hdet : determinedByPoints (X := X) n K) {α : RelativeHomology S n}
    (hα : ∀ (x : ↑X) (hx : x ∉ S), restrictBd S hx n α = 0) :
    relIncl (Set.subset_compl_comm.mp hKS) n α = 0 := by
  refine hdet _ (fun y hy => ?_)
  have hyS : y ∉ S := hKS hy
  show restrictToPoint hy n (relIncl (Set.subset_compl_comm.mp hKS) n α) = 0
  rw [restrictToPoint, relIncl_trans]
  exact hα y hyS

/-- **Conditional reduction of Wall 2 (`DeterminedByInteriorPoints`) to the collar-injectivity
residual.** Given an interior compact `K ⊆ Sᶜ` with `determinedByPoints n K` **and** the injectivity
of `relIncl(S ⊆ Kᶜ)` (the collar residual — that pushing `Hₙ(W, S) → Hₙ(W, Kᶜ)` loses nothing), the
pair `(W, S)` is determined by its interior points. Modus ponens on `relIncl_eq_zero_of_restrictBd_zero`.
The hypothesis `hinj` is precisely the piece Mathlib's missing collar-neighbourhood theorem would
supply (explicit for a product-boundary cylinder). -/
theorem determinedByInteriorPoints_of_interiorInjective {X : TopCat} {S K : Set ↑X} (hKS : K ⊆ Sᶜ)
    {n : ℕ} (hdet : determinedByPoints (X := X) n K)
    (hinj : Function.Injective (relIncl (Set.subset_compl_comm.mp hKS) n)) :
    DeterminedByInteriorPoints S n := by
  intro α hα
  exact hinj (by rw [relIncl_eq_zero_of_restrictBd_zero hKS hdet hα, map_zero])

end SKEFTHawking.PoincareLefschetzRelFundClassBoundary
