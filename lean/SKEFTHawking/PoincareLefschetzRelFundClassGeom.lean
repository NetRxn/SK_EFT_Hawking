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

/-! ## §3. Interior-point Euclidean chart extraction (`interiorPoint_hasEuclChart`)

At an **interior** point `x` of a charted manifold-with-boundary `(W, I : ModelWithCorners ℝ E H)`,
the extended chart `extChartAt I x` sends `x` into `interior (extChartAt I x).target` (open in `E`),
and restricts there to a homeomorphism `intChartHomeo` onto that open set. Composing with the model's
`toEuclidean : E ≃L EuclideanSpace ℝ (Fin (finrank E))` produces the open Euclidean chart
`SingularChartBridge.chartLocalIso` / `PoincareLefschetzRelFundClass.interiorLocalIso` consume — the
`gen` ingredient (interior local homology `≅ ℤ/2`) at every interior point of a concrete `W`. -/

section InteriorChart

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type} [TopologicalSpace H] {W : Type} [TopologicalSpace W] [ChartedSpace H W]
  (I : ModelWithCorners ℝ E H)

/-- The **open interior-chart source** at `x`: the chart source cut down to the preimage of the
interior of the chart target. Open, and it contains `x` when `x` is an interior point. -/
noncomputable def intChartU (x : W) : Set W :=
  (extChartAt I x).source ∩ (extChartAt I x) ⁻¹' interior (extChartAt I x).target

/-- The **open interior-chart image** at `x`: the interior of the chart target, open in `E`. -/
def intChartV (x : W) : Set E := interior (extChartAt I x).target

theorem isOpen_intChartV (x : W) : IsOpen (intChartV I x) := isOpen_interior

theorem isOpen_intChartU (x : W) : IsOpen (intChartU I x) :=
  (continuousOn_extChartAt x).isOpen_inter_preimage (isOpen_extChartAt_source x) isOpen_interior

theorem mem_intChartU (x : W) (hx : I.IsInteriorPoint x) : x ∈ intChartU I x :=
  ⟨mem_extChartAt_source x, I.isInteriorPoint_iff.mp hx⟩

theorem extChartAt_mem_intChartV (x : W) (hx : I.IsInteriorPoint x) :
    extChartAt I x x ∈ intChartV I x := I.isInteriorPoint_iff.mp hx

/-- **The interior chart homeomorphism** `intChartU ≃ₜ intChartV` at an interior point: the restriction
of `extChartAt I x` to the (open) interior-chart source, a homeomorphism onto the (open) interior of the
chart target. (Works at any point; interior-ness is only needed for `x ∈ intChartU`, `mem_intChartU`.) -/
noncomputable def intChartHomeo (x : W) :
    ↥(intChartU I x) ≃ₜ ↥(intChartV I x) where
  toFun u := ⟨extChartAt I x u, u.2.2⟩
  invFun v := ⟨(extChartAt I x).symm v,
    ⟨(extChartAt I x).map_target (interior_subset v.2), by
      rw [Set.mem_preimage, (extChartAt I x).right_inv (interior_subset v.2)]; exact v.2⟩⟩
  left_inv u := Subtype.ext ((extChartAt I x).left_inv u.2.1)
  right_inv v := Subtype.ext ((extChartAt I x).right_inv (interior_subset v.2))
  continuous_toFun :=
    Continuous.subtype_mk
      ((continuousOn_extChartAt x).comp_continuous continuous_subtype_val (fun u => u.2.1)) _
  continuous_invFun :=
    Continuous.subtype_mk
      ((continuousOn_extChartAt_symm x).comp_continuous continuous_subtype_val
        (fun v => interior_subset v.2)) _

@[simp] theorem intChartHomeo_apply (x : W) (u : ↥(intChartU I x)) :
    (intChartHomeo I x u : E) = extChartAt I x u := rfl

/-- **The interior local-homology iso `Hₙ(W, W∖x) ≅ ℤ/2` at an interior point** (the
`interiorPoint_hasEuclChart` obligation, delivering the local iso it feeds). Given a linear
homeomorphism `ε : E ≃L EuclideanSpace ℝ (Fin (m+2))` of the model vector space (e.g.
`ContinuousLinearEquiv.toEuclidean` composed with a `finrank = m+2` reindexing), the interior chart
`intChartHomeo` composed with `ε` is the open Euclidean chart around `x`, and
`PoincareLefschetzRelFundClass.interiorLocalIso` turns it into `Hₙ(W, W∖x) ≅ ℤ/2`. This is exactly the
`gen` ingredient of a `RelFundClassDatum` at the interior points of a concrete charted `W`. -/
noncomputable def interiorChartLocalIso [T1Space W] {m : ℕ}
    (ε : E ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 2))) (x : W) (hx : I.IsInteriorPoint x) :
    RelativeHomology (X := TopCat.of W) ({x}ᶜ) (m + 2) ≃ₗ[ZMod 2] ZMod 2 :=
  PoincareLefschetzRelFundClass.interiorLocalIso (X := TopCat.of W)
    (isOpen_intChartU I x) (mem_intChartU I x hx)
    ((ε.toHomeomorph.isOpen_image).mpr (isOpen_intChartV I x))
    (⟨extChartAt I x x, extChartAt_mem_intChartV I x hx, rfl⟩ :
      ε (extChartAt I x x) ∈ ε.toHomeomorph '' intChartV I x)
    ((intChartHomeo I x).trans (ε.toHomeomorph.image (intChartV I x)))
    rfl

end InteriorChart

end SKEFTHawking.PoincareLefschetzRelFundClassGeom
