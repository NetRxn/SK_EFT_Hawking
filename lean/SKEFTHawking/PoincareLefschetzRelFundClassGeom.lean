/-
# Phase 5q.H (W-A.1d) — the `[W,∂W]` geometric discharges (the named 1d slices)

The three geometric obligations named in `PoincareLefschetzRelFundClass.lean`'s docstring, plus the
concrete cylinder datum. All discharged on the project's genuine singular ℤ/2 (co)homology, reusing
the closed-case chart/excision/MV machinery (`SingularChartBridge`, `SingularManifoldFundamentalClass`,
`SingularFundamentalClassExist`) and the star-convex contraction tools (`SingularStarConvexSlit`).

* §1 — `homology_starConvexSub_eq_zero`: a **star-convex** subspace of `ℝⁿ` is acyclic (the
  `StarConvex` generalization of `SingularConvexSubAcyclic.homology_convexSub_eq_zero`, using
  `SingularStarConvexSlit.starConvexContraction`). The acyclicity of a punctured half-space's
  boundary-slit (`H∖q` at a boundary point `q` is star-convex from any interior center).
* §2 — `boundaryPoint_localHomology_zero`: the **boundary local-homology vanishing**
  `Hₙ(W, W∖x) = 0` at a boundary point, via a convex (⇒ acyclic) chart neighbourhood `V ⊆ ℝⁿ` with
  a star-convex punctured slit `V∖q`, transported by chart-excision and fed to the merged
  `localHomology_eq_zero_of_acyclic_puncture`. The genuinely-new *relative* content.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClass
import SKEFTHawking.SingularConvexSubAcyclic
import SKEFTHawking.SingularStarConvexSlit
import SKEFTHawking.SingularFundamentalClassExist

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularHomotopyInvariance
open SKEFTHawking.SingularEuclideanAcyclic (Eucl)
open SKEFTHawking.SingularStarConvexSlit
open SKEFTHawking.SingularExcisionIso (restr)

namespace SKEFTHawking.PoincareLefschetzRelFundClassGeom

/-! ## §1. A star-convex subspace of `ℝⁿ` is acyclic -/

/-- **A star-convex subspace is acyclic**: `H_{k+1}(sub C) = 0` for `C` star-convex at `p₀ ∈ C`. The
`StarConvex` generalization of `SingularConvexSubAcyclic.homology_convexSub_eq_zero` — the segment
only ever needs the one endpoint fixed at the star center, so the straight-line contraction
`SingularStarConvexSlit.starConvexContraction` kills positive homology exactly as in the convex case.
The half-space's punctured slit `H∖q` (boundary point `q`, star-convex from any interior center) is
the intended instance. -/
theorem homology_starConvexSub_eq_zero {n : ℕ} {C : Set (EuclideanSpace ℝ (Fin n))}
    {p₀ : EuclideanSpace ℝ (Fin n)} (hC : StarConvex ℝ p₀ C) (hp₀ : p₀ ∈ C) (k : ℕ)
    (x : Homology (sub (X := Eucl n) C) (k + 1)) : x = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [show (Submodule.Quotient.mk z : Homology _ (k + 1)) = Homology.mk _ (k + 1) z from rfl,
    SKEFTHawking.SingularCapHomology.Homology.mk_eq_zero]
  exact Submodule.mem_comap.mpr (by
    simpa using cycle_mem_boundaries_of_contraction (starConvexContraction hC) ⟨p₀, hp₀⟩
      (slice_starConvexContraction_zero hC) (slice_starConvexContraction_one hC hp₀)
      z.1 (LinearMap.mem_ker.mp z.2))

/-! ## §2. Boundary local-homology vanishing `Hₙ(W, W∖x) = 0`

At a **boundary** point `x` with a chart `e : U ≃ₜ V` onto an open `V ⊆ ℝⁿ`, the local homology
`Hₙ(W, W∖x)` transports (chart-excision) to the local homology at `q = e x` inside `sub V`; that
vanishes by the merged acyclic-puncture lemma once `V` is acyclic (convex ⇒ star-convex) and `V∖q`
is acyclic (star-convex from an interior center). The genuinely-new *relative* content. -/

/-- The subtype-of-subtype flattener `sub (restr A B) ≃ₜ sub A` for `A ⊆ B` — reassociates
`{p : sub B // p.val ∈ A}` with `{x // x ∈ A}` (`seamHomeo` + the `A ∩ B = A` set congruence). -/
noncomputable def flatSubHomeo {X : TopCat} {A B : Set ↑X} (hAB : A ⊆ B) :
    ↥(sub (restr A B)) ≃ₜ ↥(sub A) :=
  (SingularMayerVietorisLES.seamHomeo A B).trans
    (Homeomorph.setCongr (Set.inter_eq_self_of_subset_left hAB))

/-- **Vanishing transports across the flattener**: if `Hₙ(sub A) = 0` then `Hₙ(sub (restr A B)) = 0`
(`A ⊆ B`), via `flatSubHomeo` and homology functoriality. -/
theorem homology_restrSub_eq_zero {X : TopCat} {A B : Set ↑X} (hAB : A ⊆ B) (n : ℕ)
    (hac : ∀ y : Homology (sub A) n, y = 0) (y : Homology (sub (restr A B)) n) : y = 0 := by
  have hbij := Homology.map_bijective_of_comp_id_all
    (⟨flatSubHomeo hAB, (flatSubHomeo hAB).continuous⟩ : C(↑(sub (restr A B)), ↑(sub A)))
    (⟨(flatSubHomeo hAB).symm, (flatSubHomeo hAB).symm.continuous⟩ :
      C(↑(sub A), ↑(sub (restr A B))))
    (ContinuousMap.ext fun z => (flatSubHomeo hAB).symm_apply_apply z)
    (ContinuousMap.ext fun z => (flatSubHomeo hAB).apply_symm_apply z) n
  exact hbij.injective (by rw [map_zero]; exact hac _)

/-- **Boundary-point local-homology vanishing** `Hₙ(W, W∖x) = 0` (the `boundaryPoint_localHomology_zero`
obligation). At a point `x` with a chart `e : U ≃ₜ V` (`U` open in `W ∋ x`, `V ⊆ ℝⁿ`, `e x = q`)
whose image `V` is **star-convex** (at `c ∈ V`) and whose punctured image `V∖q` is **star-convex** (at
an interior center `c' ∈ V∖q`), the pair-local homology at `x` vanishes. For a *boundary* point the
chart image is a half-space neighbourhood (e.g. a half-ball, only *relatively* open in the half-space,
NOT open in `ℝⁿ`): convex (hence star-convex at any of its points, including the boundary `q`) with a
star-convex boundary-slit `V∖q` (star from any interior `c'`). Chart-excision
(`SingularChartBridge.openPointExcisionEquiv`, `chartPairEquiv`) identifies `Hₙ(W, W∖x)` with the local
homology at `q` inside `sub V`, then the merged
`PoincareLefschetzRelFundClass.localHomology_eq_zero_of_acyclic_puncture` fires. -/
theorem boundaryPoint_localHomology_zero {W : TopCat} [T1Space ↑W] {m : ℕ}
    {x : ↑W} {U : Set ↑W} (hU : IsOpen U) (hx : x ∈ U)
    {q : ↑(Eucl (m + 2))} {V : Set ↑(Eucl (m + 2))} (hq : q ∈ V)
    (e : ↥U ≃ₜ ↥V) (hex : (e ⟨x, hx⟩ : ↑(Eucl (m + 2))) = q)
    {c : EuclideanSpace ℝ (Fin (m + 2))} (hVstar : StarConvex ℝ c V) (hcV : c ∈ V)
    {c' : EuclideanSpace ℝ (Fin (m + 2))} (hVpunc : StarConvex ℝ c' (V \ {q}))
    (hc'V : c' ∈ V \ {q})
    (α : RelativeHomology (X := W) ({x}ᶜ) (m + 2)) : α = 0 := by
  set q' : ↥V := ⟨q, hq⟩ with hq'
  -- the chart-excision transport iso `Hₙ(W, W∖x) ≅ Hₙ(sub V, (sub V)∖q')`
  set Φ := (SingularChartBridge.openPointExcisionEquiv hU hx (m + 1)).symm.trans
    (SingularChartBridge.chartPairEquiv hx e hex (m + 2)) with hΦ
  -- the transported local homology vanishes (merged acyclic-puncture lemma)
  have hvanish : ∀ β : RelativeHomology (restr {y | y ≠ q} V) (m + 2), β = 0 := by
    have hset : restr {y | y ≠ q} V = ({q'}ᶜ : Set ↑(sub V)) := by
      ext p
      simp only [restr, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_compl_iff,
        Set.mem_singleton_iff, hq', Subtype.ext_iff]
    rw [hset]
    intro β
    refine PoincareLefschetzRelFundClass.localHomology_eq_zero_of_acyclic_puncture
      (Y := sub V) q' m (fun y => homology_starConvexSub_eq_zero hVstar hcV (m + 1) y)
      (fun y => homology_starConvexSub_eq_zero hVstar hcV m y) ?_ β
    -- `hpunct`: the puncture `(sub V)∖q'` is `sub (restr (V∖q) V)`, star-convex-acyclic
    have hset2 : ({q'}ᶜ : Set ↑(sub V)) = restr (V \ {q}) V := by
      ext p
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, restr, Set.mem_preimage,
        Set.mem_diff, hq', Subtype.ext_iff]
      exact ⟨fun h => ⟨p.2, h⟩, fun h => h.2⟩
    rw [hset2]
    exact fun y => homology_restrSub_eq_zero Set.diff_subset (m + 1)
      (fun z => homology_starConvexSub_eq_zero hVpunc hc'V m z) y
  have hΦα : Φ α = 0 := hvanish (Φ α)
  exact (LinearEquiv.map_eq_zero_iff Φ).mp hΦα

end SKEFTHawking.PoincareLefschetzRelFundClassGeom
