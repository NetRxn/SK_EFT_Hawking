/-
# Phase 5q.H (#212) — THE BOUNDARY-FACE LOCAL-HOMOLOGY BRIDGE (degree-general), and its two models.

The named-but-unformalized lemma of the `capstone-binary-partition-detection-uninhabitable` record
("the kernel-encodable core = *boundary-face local homology vanishes*; formalizing the
boundary-local-homology lemma is itself a task"). This module lands it, in a **degree-general** form
and for the two model pieces of the surgery trace.

* §1 — `faceLocalHomology_zero_of_starConvexChart`: `H_{k+2}(W, W∖x) = 0` in **every** degree
  `k + 2`, at a point `x` carrying a chart `e : U ≃ₜ V` (`U` open in `W`) onto a **star-convex**
  `V ⊆ ℝⁿ` whose puncture `V∖q` is also star-convex. This decouples the degree from the chart
  dimension in `PoincareLefschetzRelFundClassGeom.boundaryPoint_localHomology_zero` (which fixes
  degree = chart dimension); the proof is the same chart-excision transport, since the star-convex
  acyclicity `homology_starConvexSub_eq_zero` is already degree-general.
* §2 — `closedBall_faceLocalHomology_zero`: the **disk model** `H_{k+2}(D^{n}, D^{n}∖x) = 0` at a
  point of the boundary sphere `‖x‖ = 1`. Chart: the identity on the whole ball; `V` = the closed
  ball (convex) and `V∖q` star-convex from the centre — the sole geometric input is that a segment
  from `0` reaches the unit sphere only at its far endpoint.
* §3 — `cylTopFace_localHomology_zero`: the **cylinder model**
  `H_{k+2}(M × [0,1], (M × [0,1])∖(p, t₀)) = 0` at a TOP-face point (`(t₀ : ℝ) = 1`), for `M` any
  charted `(m'+2)`-manifold. Chart: a chart ball of `M` at `p` crossed with the half-open end
  interval `(½, 1]`, carried into `ℝ^{m'+3}` by the canonical `EuclideanSpace` splitting
  (`cylEuclEquiv`). The punctured slit is star-convex from a point one notch inside the end face
  (`starConvex_endSlab_diff_singleton`).
* §4/§5 — the **vacuity attacks, run and defeated**. On the *same* ball and the *same* cylinder, in
  the *same* degree, the local homology is `ℤ/2` (resp. nonzero) at an INTERIOR point:
  `closedBall_interiorLocalIso` / `exists_ne_zero_closedBall_interiorLocalHomology` and
  `exists_ne_zero_cylInteriorLocalHomology`. So neither vanishing statement is about a module that is
  trivial anyway — the face hypotheses `‖x‖ = 1` and `(t₀ : ℝ) = 1` carry all the content.
* §6 — `localHomology_zero_of_homeo`: transport along a homeomorphism of ambient spaces (the
  delivery vehicle for pieces of a decomposition that are homeomorphic copies of the models).

Both vanishing models use *relatively* open half-space charts — `V` is deliberately NOT open in
`ℝⁿ`, which is exactly why the local homology vanishes instead of being `ℤ/2` (contrast
`SingularChartBridge.manifoldLocalIso` and §4/§5, whose charts ARE open).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClassGeom
import SKEFTHawking.PoincareLefschetzRelFundClassCylinder

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularEuclideanAcyclic (Eucl)
open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.PoincareLefschetzRelFundClassGeom
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder (cylW cylModel)

namespace SKEFTHawking.SingularFaceLocalHomologyVanish

noncomputable section

/-! ## §1. The degree-general boundary-face vanishing engine -/

/-- **BOUNDARY-FACE LOCAL HOMOLOGY VANISHES IN EVERY DEGREE.** At a point `x` of `W` carrying a
chart `e : U ≃ₜ V` (`U` open in `W` with `x ∈ U`, `e x = q`) whose image `V ⊆ ℝᵐ⁺²` is
**star-convex** and whose puncture `V ∖ {q}` is **star-convex** as well, the local homology
`H_{k+2}(W, W∖x)` vanishes for **every** `k`.

This is the degree-general form of
`PoincareLefschetzRelFundClassGeom.boundaryPoint_localHomology_zero`, which pins the degree to the
chart dimension `m + 2`. The generalisation is free: `chartPairEquiv` and `openPointExcisionEquiv`
are degree-general, and star-convex acyclicity (`homology_starConvexSub_eq_zero`) holds in every
positive degree — only the *chart dimension* `m + 2` is structural.

A **half-space** chart is the intended instance: convex (hence star-convex at any point, including
the face point `q` itself) with a star-convex slit `V∖q` seen from any point off the face. For an
*interior* point the puncture is a sphere and `H` is `ℤ/2` instead
(`SingularChartBridge.manifoldLocalIso`) — the hypothesis `hVpunc` is exactly what fails there. -/
theorem faceLocalHomology_zero_of_starConvexChart {W : TopCat} [T1Space ↑W] {m : ℕ}
    {x : ↑W} {U : Set ↑W} (hU : IsOpen U) (hx : x ∈ U)
    {q : ↑(Eucl (m + 2))} {V : Set ↑(Eucl (m + 2))} (hq : q ∈ V)
    (e : ↥U ≃ₜ ↥V) (hex : (e ⟨x, hx⟩ : ↑(Eucl (m + 2))) = q)
    {c : EuclideanSpace ℝ (Fin (m + 2))} (hVstar : StarConvex ℝ c V) (hcV : c ∈ V)
    {c' : EuclideanSpace ℝ (Fin (m + 2))} (hVpunc : StarConvex ℝ c' (V \ {q}))
    (hc'V : c' ∈ V \ {q}) (k : ℕ)
    (α : RelativeHomology (X := W) ({x}ᶜ) (k + 2)) : α = 0 := by
  set q' : ↥V := ⟨q, hq⟩ with hq'
  set Φ := (SingularChartBridge.openPointExcisionEquiv hU hx (k + 1)).symm.trans
    (SingularChartBridge.chartPairEquiv hx e hex (k + 2)) with hΦ
  have hvanish : ∀ β : RelativeHomology (restr {y | y ≠ q} V) (k + 2), β = 0 := by
    have hset : restr {y | y ≠ q} V = ({q'}ᶜ : Set ↑(sub V)) := by
      ext p
      simp only [restr, Set.mem_preimage, Set.mem_setOf_eq, Set.mem_compl_iff,
        Set.mem_singleton_iff, hq', Subtype.ext_iff]
    rw [hset]
    intro β
    refine PoincareLefschetzRelFundClass.localHomology_eq_zero_of_acyclic_puncture
      (Y := sub V) q' k (fun y => homology_starConvexSub_eq_zero hVstar hcV (k + 1) y)
      (fun y => homology_starConvexSub_eq_zero hVstar hcV k y) ?_ β
    have hset2 : ({q'}ᶜ : Set ↑(sub V)) = restr (V \ {q}) V := by
      ext p
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff, restr, Set.mem_preimage,
        Set.mem_diff, hq', Subtype.ext_iff]
      exact ⟨fun h => ⟨p.2, h⟩, fun h => h.2⟩
    rw [hset2]
    exact fun y => homology_restrSub_eq_zero Set.diff_subset (k + 1)
      (fun z => homology_starConvexSub_eq_zero hVpunc hc'V k z) y
  exact (LinearEquiv.map_eq_zero_iff Φ).mp (hvanish (Φ α))

/-! ## §2. The disk model — a boundary-sphere point of a closed ball -/

/-- **The punctured closed ball is star-convex from its centre when the puncture is on the unit
sphere.** The only geometric content of the disk model: a segment from `0` to a point of the ball
meets the unit sphere only at its far endpoint, so removing a unit-norm point leaves the radial
contraction intact. -/
theorem starConvex_closedBall_diff_singleton {n : ℕ}
    {q : EuclideanSpace ℝ (Fin n)} (hq : ‖q‖ = 1) :
    StarConvex ℝ 0 (Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1 \ {q}) := by
  intro y hy a b ha hb hab
  have hy1 : ‖y‖ ≤ 1 := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hy.1
  have hb1 : b ≤ 1 := by linarith
  have hval : a • (0 : EuclideanSpace ℝ (Fin n)) + b • y = b • y := by
    rw [smul_zero, zero_add]
  rw [hval]
  refine ⟨?_, ?_⟩
  · have : ‖b • y‖ = b * ‖y‖ := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
    simp only [Metric.mem_closedBall, dist_zero_right, this]
    nlinarith
  · intro hcon
    rw [Set.mem_singleton_iff] at hcon
    have hnorm : b * ‖y‖ = 1 := by
      rw [← hq, ← hcon, norm_smul, Real.norm_eq_abs, abs_of_nonneg hb]
    have hb' : b = 1 := by nlinarith
    exact hy.2 (by rw [← hcon, hb', one_smul]; exact rfl)

/-- **THE DISK MODEL — local homology vanishes at a boundary-sphere point, in every degree.**
`H_{k+2}(Dⁿ, Dⁿ∖x) = 0` for `x` in the boundary sphere `‖x‖ = 1` of the closed unit ball
`Dⁿ ⊆ ℝⁿ` (`n = m + 2`). The chart is the identity on the whole ball: `V` is the closed ball
(convex, hence star-convex at the centre) and `V∖q` is star-convex at the centre by
`starConvex_closedBall_diff_singleton`.

This is the handle side of the surgery trace: `D⁵ = NDisk 4` is `Metric.closedBall (0 : ℝ⁵) 1`, so
this fires verbatim at any attaching parameter lying on `S⁴ = ∂D⁵`. -/
theorem closedBall_faceLocalHomology_zero {m : ℕ}
    (x : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 2))) 1))
    (hx : ‖(x : EuclideanSpace ℝ (Fin (m + 2)))‖ = 1) (k : ℕ)
    (α : RelativeHomology
      (X := TopCat.of ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 2))) 1))
      ({x}ᶜ) (k + 2)) : α = 0 := by
  have h0 : (0 : EuclideanSpace ℝ (Fin (m + 2)))
      ∈ (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 2))) 1 : Set ↑(Eucl (m + 2))) := by
    simp
  have hqne : (x : EuclideanSpace ℝ (Fin (m + 2))) ≠ 0 := by
    intro hcon
    rw [hcon, norm_zero] at hx
    norm_num at hx
  refine faceLocalHomology_zero_of_starConvexChart
    (W := TopCat.of ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 2))) 1))
    (U := Set.univ) isOpen_univ (Set.mem_univ x)
    (q := (x : EuclideanSpace ℝ (Fin (m + 2))))
    (V := (Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 2))) 1 : Set ↑(Eucl (m + 2))))
    x.2 (Homeomorph.Set.univ _) rfl
    ((convex_closedBall _ _).starConvex h0) h0
    (starConvex_closedBall_diff_singleton hx) ⟨h0, fun hcon => hqne (Set.mem_singleton_iff.mp hcon).symm⟩
    k α

/-! ## §3. The cylinder model — a top-face point of `M × [0,1]` -/

/-- **A chart restricted to a subset of its target** — `↥(c.source ∩ c ⁻¹' D) ≃ₜ ↥D` for any
`D ⊆ c.target`. The chart-ball extractor: taking `D` a metric ball inside the target turns an
arbitrary chart into one with a **convex** image, which is what the star-convexity hypotheses of
`faceLocalHomology_zero_of_starConvexChart` need. -/
def chartBallHomeo {A B : Type} [TopologicalSpace A] [TopologicalSpace B]
    (c : OpenPartialHomeomorph A B) {D : Set B} (hD : D ⊆ c.target) :
    ↥(c.source ∩ c ⁻¹' D) ≃ₜ ↥D where
  toFun y := ⟨c (y : A), y.2.2⟩
  invFun w := ⟨c.symm (w : B), c.map_target (hD w.2), by
    simp only [Set.mem_preimage, c.right_inv (hD w.2)]; exact w.2⟩
  left_inv y := Subtype.ext (c.left_inv y.2.1)
  right_inv w := Subtype.ext (c.right_inv (hD w.2))
  continuous_toFun :=
    Continuous.subtype_mk ((c.continuousOn.mono Set.inter_subset_left).restrict) _
  continuous_invFun :=
    Continuous.subtype_mk ((c.continuousOn_symm.mono hD).restrict) _

/-- The **open top end** `(½, 1]` of the unit interval, as a subset of `↥(Icc 0 1)`. -/
def topEnd : Set (Set.Icc (0 : ℝ) 1) := {t | (1 : ℝ) / 2 < (t : ℝ)}

theorem isOpen_topEnd : IsOpen topEnd :=
  isOpen_Ioi.preimage (continuous_subtype_val (p := fun x : ℝ => x ∈ Set.Icc (0 : ℝ) 1))

/-- The top end of `↥(Icc 0 1)` is homeomorphic to the real half-open interval `Ioc (½) 1`. -/
def topEndHomeo : ↥topEnd ≃ₜ ↥(Set.Ioc (1 / 2 : ℝ) 1) where
  toFun t := ⟨((t : Set.Icc (0 : ℝ) 1) : ℝ), t.2, (t : Set.Icc (0 : ℝ) 1).2.2⟩
  invFun u := ⟨⟨(u : ℝ), le_of_lt (lt_trans (by norm_num) u.2.1), u.2.2⟩, u.2.1⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _

/-- The canonical line/`E¹` identification `ℝ ≃L E¹`. -/
def lineEquiv : ℝ ≃L[ℝ] EuclideanSpace ℝ (Fin 1) :=
  (ContinuousLinearEquiv.funUnique (Fin 1) ℝ ℝ).symm.trans (EuclideanSpace.equiv (Fin 1) ℝ).symm

/-- The **cylinder splitting** `E^{m'+2} × ℝ ≃L E^{m'+3}` — the canonical
`EuclideanSpace.finAddEquivProd` of `PoincareLefschetzRelFundClassCylinder.εcyl` with the interval
factor read as a line rather than as `E¹`. -/
def cylEuclEquiv (m' : ℕ) :
    (EuclideanSpace ℝ (Fin (m' + 2)) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (m' + 1 + 2)) :=
  ((ContinuousLinearEquiv.refl ℝ (EuclideanSpace ℝ (Fin (m' + 2)))).prodCongr lineEquiv).trans
    (SKEFTHawking.PoincareLefschetzRelFundClassCylinder.εcyl m')

/-- **Star-convexity transports along the cylinder splitting** (a linear equivalence carries a
star-convex set to a star-convex preimage-of-set, star centre included). Stated concretely to avoid
`LinearMap`-coercion friction. -/
theorem starConvex_preimage_cylEuclEquiv {m' : ℕ} (z : EuclideanSpace ℝ (Fin (m' + 2)) × ℝ)
    {T : Set (EuclideanSpace ℝ (Fin (m' + 2)) × ℝ)} (hT : StarConvex ℝ z T) :
    StarConvex ℝ (cylEuclEquiv m' z) (⇑(cylEuclEquiv m').symm ⁻¹' T) := by
  intro y hy a b ha hb hab
  simp only [Set.mem_preimage] at hy ⊢
  have hval : (cylEuclEquiv m').symm (a • cylEuclEquiv m' z + b • y)
      = a • z + b • (cylEuclEquiv m').symm y := by
    rw [map_add, map_smul, map_smul, ContinuousLinearEquiv.symm_apply_apply]
  rw [hval]
  exact hT hy ha hb hab

/-- **The punctured end-slab is star-convex from one notch inside the end face.** The geometric core
of the cylinder model: in `B × (½, 1]` the face point `(q₀, 1)` is extremal in the last coordinate,
so a segment starting at `(q₀, ¾)` reaches it only at its far endpoint. -/
theorem starConvex_endSlab_diff_singleton {m' : ℕ}
    (q₀ : EuclideanSpace ℝ (Fin (m' + 2))) {r : ℝ} (hr : 0 < r) :
    StarConvex ℝ (q₀, (3 : ℝ) / 4)
      ((Metric.ball q₀ r ×ˢ Set.Ioc (1 / 2 : ℝ) 1) \ {(q₀, (1 : ℝ))}) := by
  have hconv : Convex ℝ (Metric.ball q₀ r ×ˢ Set.Ioc (1 / 2 : ℝ) 1) :=
    (convex_ball q₀ r).prod (convex_Ioc _ _)
  have hcen : ((q₀, (3 : ℝ) / 4)) ∈ Metric.ball q₀ r ×ˢ Set.Ioc (1 / 2 : ℝ) 1 :=
    ⟨Metric.mem_ball_self hr, by norm_num, by norm_num⟩
  intro y hy a b ha hb hab
  refine ⟨hconv hcen hy.1 ha hb hab, ?_⟩
  intro hcon
  rw [Set.mem_singleton_iff] at hcon
  have hsnd : a * ((3 : ℝ) / 4) + b * y.2 = 1 := congrArg Prod.snd hcon
  have hy2 : y.2 ≤ 1 := hy.1.2.2
  have ha0 : a = 0 := by nlinarith
  have hb1 : b = 1 := by linarith
  refine hy.2 ?_
  rw [Set.mem_singleton_iff, ← hcon, ha0, hb1, one_smul, zero_smul, zero_add]

/-- **THE CYLINDER MODEL — local homology vanishes at a TOP-FACE point, in every degree.**
For `M` a charted `(m'+2)`-manifold and any `t₀` at the top of the interval (`(t₀ : ℝ) = 1`),
`H_{k+2}(M × [0,1], (M × [0,1]) ∖ (p, t₀)) = 0` for every `k`.

The chart is a **chart ball of `M` at `p` crossed with the end interval** `(½, 1]`, carried into
`ℝ^{m'+3}` by the canonical splitting `cylEuclEquiv`. Its image is convex (a ball times an interval)
and its puncture at the face point is star-convex from one notch inside
(`starConvex_endSlab_diff_singleton`), so `faceLocalHomology_zero_of_starConvexChart` fires.

This is the cylinder side of the surgery trace, and the formal content of the `#156` wall analysis:
a point of the *top face* `M × {⊤}` is a boundary point of the cylinder, so the cylinder's own local
homology there vanishes — it can carry no local class, in any degree. -/
theorem cylTopFace_localHomology_zero {m' : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M] [T1Space (cylW M)] (p : M)
    {t₀ : Set.Icc (0 : ℝ) 1} (ht₀ : (t₀ : ℝ) = 1) (k : ℕ)
    (α : RelativeHomology (X := TopCat.of (cylW M)) ({(p, t₀)}ᶜ) (k + 2)) : α = 0 := by
  haveI : T1Space ↑(TopCat.of (cylW M)) := inferInstanceAs (T1Space (cylW M))
  set c := chartAt (EuclideanSpace ℝ (Fin (m' + 2))) p with hcdef
  have hps : p ∈ c.source := mem_chart_source _ p
  have hq₀ : c p ∈ c.target := mem_chart_target _ p
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp c.open_target (c p) hq₀
  set q₀ : EuclideanSpace ℝ (Fin (m' + 2)) := c p with hq₀def
  set UM : Set M := c.source ∩ c ⁻¹' Metric.ball q₀ r with hUMdef
  have hpUM : p ∈ UM := ⟨hps, Metric.mem_ball_self hr⟩
  have hUMopen : IsOpen UM := c.isOpen_inter_preimage Metric.isOpen_ball
  set U : Set (cylW M) := UM ×ˢ topEnd with hUdef
  have hUopen : IsOpen U := hUMopen.prod isOpen_topEnd
  have hxU : ((p, t₀) : cylW M) ∈ U := ⟨hpUM, by
    show (1 : ℝ) / 2 < ((t₀ : Set.Icc (0 : ℝ) 1) : ℝ)
    rw [ht₀]; norm_num⟩
  -- the flat model of the chart: a ball times the end interval
  set Vraw : Set (EuclideanSpace ℝ (Fin (m' + 2)) × ℝ) :=
    Metric.ball q₀ r ×ˢ Set.Ioc (1 / 2 : ℝ) 1 with hVrawdef
  set V : Set (EuclideanSpace ℝ (Fin (m' + 1 + 2))) :=
    ⇑(cylEuclEquiv m').symm ⁻¹' Vraw with hVdef
  set qraw : EuclideanSpace ℝ (Fin (m' + 2)) × ℝ := (q₀, (1 : ℝ)) with hqrawdef
  have hqrawV : qraw ∈ Vraw := ⟨Metric.mem_ball_self hr, by norm_num, le_refl 1⟩
  have hcenV : ((q₀, (3 : ℝ) / 4)) ∈ Vraw := ⟨Metric.mem_ball_self hr, by norm_num, by norm_num⟩
  -- the chart homeomorphism `↥U ≃ₜ ↥V`
  set eU : ↥U ≃ₜ ↥Vraw :=
    (Homeomorph.Set.prod UM topEnd).trans
      (((chartBallHomeo c hball).prodCongr topEndHomeo).trans
        (Homeomorph.Set.prod (Metric.ball q₀ r) (Set.Ioc (1 / 2 : ℝ) 1)).symm) with heUdef
  set eV : ↥Vraw ≃ₜ ↥V :=
    (cylEuclEquiv m').toHomeomorph.subtype (fun w => by
      simp only [hVdef, Set.mem_preimage, ContinuousLinearEquiv.coe_toHomeomorph,
        ContinuousLinearEquiv.symm_apply_apply]) with heVdef
  -- the face point, and the fact that the chart sends it there
  have hex : ((eU.trans eV) ⟨((p, t₀) : cylW M), hxU⟩ : EuclideanSpace ℝ (Fin (m' + 1 + 2)))
      = cylEuclEquiv m' qraw := by
    show cylEuclEquiv m' (q₀, ((t₀ : Set.Icc (0 : ℝ) 1) : ℝ)) = cylEuclEquiv m' qraw
    rw [hqrawdef, ht₀]
  refine faceLocalHomology_zero_of_starConvexChart (W := TopCat.of (cylW M)) (U := U)
    hUopen hxU (q := cylEuclEquiv m' qraw) (V := V) ?_ (eU.trans eV) hex
    (c := cylEuclEquiv m' (q₀, (3 : ℝ) / 4)) ?_ ?_
    (c' := cylEuclEquiv m' (q₀, (3 : ℝ) / 4)) ?_ ?_ k α
  · show (cylEuclEquiv m').symm (cylEuclEquiv m' qraw) ∈ Vraw
    rw [ContinuousLinearEquiv.symm_apply_apply]; exact hqrawV
  · exact starConvex_preimage_cylEuclEquiv _
      (((convex_ball q₀ r).prod (convex_Ioc _ _)).starConvex hcenV)
  · show (cylEuclEquiv m').symm (cylEuclEquiv m' (q₀, (3 : ℝ) / 4)) ∈ Vraw
    rw [ContinuousLinearEquiv.symm_apply_apply]; exact hcenV
  · have hdiff : V \ {cylEuclEquiv m' qraw} = ⇑(cylEuclEquiv m').symm ⁻¹' (Vraw \ {qraw}) := by
      ext w
      simp only [hVdef, Set.mem_diff, Set.mem_preimage, Set.mem_singleton_iff]
      refine and_congr_right fun _ => ?_
      constructor
      · intro h hcon
        exact h (by rw [← hcon, ContinuousLinearEquiv.apply_symm_apply])
      · intro h hcon
        exact h (by rw [hcon, ContinuousLinearEquiv.symm_apply_apply])
    rw [hdiff]
    exact starConvex_preimage_cylEuclEquiv _ (starConvex_endSlab_diff_singleton q₀ hr)
  · refine ⟨?_, ?_⟩
    · show (cylEuclEquiv m').symm (cylEuclEquiv m' (q₀, (3 : ℝ) / 4)) ∈ Vraw
      rw [ContinuousLinearEquiv.symm_apply_apply]; exact hcenV
    · intro hcon
      rw [Set.mem_singleton_iff] at hcon
      have := congrArg Prod.snd ((cylEuclEquiv m').injective hcon)
      norm_num [hqrawdef] at this

/-! ## §4. NON-VACUITY — the same ball, at an INTERIOR point, has local homology `ℤ/2` -/

/-- The open part of the closed ball is (tautologically) the open ball. -/
def ballInteriorHomeo {n : ℕ} :
    ↥({v : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1) |
        ‖(v : EuclideanSpace ℝ (Fin n))‖ < 1})
      ≃ₜ ↥(Metric.ball (0 : EuclideanSpace ℝ (Fin n)) 1) where
  toFun v := ⟨((v : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin n)) 1)) :
      EuclideanSpace ℝ (Fin n)), by simpa only [Metric.mem_ball, dist_zero_right, Set.mem_setOf_eq] using v.2⟩
  invFun w := ⟨⟨(w : EuclideanSpace ℝ (Fin n)), by
      simpa only [Metric.mem_closedBall, dist_zero_right] using
        le_of_lt (by simpa only [Metric.mem_ball, dist_zero_right, Set.mem_setOf_eq] using w.2)⟩, by
      simpa only [Metric.mem_ball, dist_zero_right, Set.mem_setOf_eq] using w.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _

/-- **THE CONTRAST — at an INTERIOR point of the very same ball the local homology is `ℤ/2`.**
`H_{m+2}(Dⁿ, Dⁿ∖x) ≅ ℤ/2` for `‖x‖ < 1` (`n = m + 2`), from the open chart supplied by
`ballInteriorHomeo` fed to `SingularChartBridge.chartLocalIso`.

This is the **vacuity attack** on §2 run and defeated: `closedBall_faceLocalHomology_zero` is not a
statement about a module that is trivial anyway. On one and the same space, in one and the same
degree `m + 2`, the local homology is `ℤ/2` at an interior point and `0` at a boundary-sphere point.
The face hypothesis `‖x‖ = 1` is doing all the work. -/
def closedBall_interiorLocalIso {m : ℕ}
    (x : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 2))) 1))
    (hx : ‖(x : EuclideanSpace ℝ (Fin (m + 2)))‖ < 1) :
    RelativeHomology
      (X := TopCat.of ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 2))) 1))
      ({x}ᶜ) (m + 2) ≃ₗ[ZMod 2] ZMod 2 :=
  haveI : T1Space ↑(TopCat.of ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 2))) 1)) :=
    inferInstanceAs (T1Space ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 2))) 1))
  SingularChartBridge.chartLocalIso
    (M := TopCat.of ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 2))) 1)) (x := x)
    (U := {v | ‖(v : EuclideanSpace ℝ (Fin (m + 2)))‖ < 1})
    (isOpen_lt (continuous_norm.comp continuous_subtype_val) continuous_const) hx
    (q := (x : EuclideanSpace ℝ (Fin (m + 2))))
    (V := Metric.ball (0 : EuclideanSpace ℝ (Fin (m + 2))) 1) Metric.isOpen_ball
    (by simpa only [Metric.mem_ball, dist_zero_right] using hx) ballInteriorHomeo rfl

/-- **The interior local homology of the ball is NONZERO** — the explicit witness that makes the
boundary-face vanishing of §2 substantive rather than a statement about a trivial module. -/
theorem exists_ne_zero_closedBall_interiorLocalHomology {m : ℕ}
    (x : ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 2))) 1))
    (hx : ‖(x : EuclideanSpace ℝ (Fin (m + 2)))‖ < 1) :
    ∃ α : RelativeHomology
      (X := TopCat.of ↥(Metric.closedBall (0 : EuclideanSpace ℝ (Fin (m + 2))) 1))
      ({x}ᶜ) (m + 2), α ≠ 0 := by
  refine ⟨(closedBall_interiorLocalIso x hx).symm 1, fun hcon => ?_⟩
  have := congrArg (closedBall_interiorLocalIso x hx) hcon
  rw [LinearEquiv.apply_symm_apply, map_zero] at this
  exact one_ne_zero this

/-! ## §5. NON-VACUITY for the cylinder — an INTERIOR point of the same cylinder has `ℤ/2` -/

/-- The **open middle** `(0,1)` of the unit interval, as a subset of `↥(Icc 0 1)`. -/
def midEnd : Set (Set.Icc (0 : ℝ) 1) := {t | 0 < (t : ℝ) ∧ (t : ℝ) < 1}

theorem isOpen_midEnd : IsOpen midEnd :=
  isOpen_Ioo.preimage (continuous_subtype_val (p := fun x : ℝ => x ∈ Set.Icc (0 : ℝ) 1))

/-- The open middle of `↥(Icc 0 1)` is homeomorphic to the real open interval `Ioo 0 1`. -/
def midEndHomeo : ↥midEnd ≃ₜ ↥(Set.Ioo (0 : ℝ) 1) where
  toFun t := ⟨((t : Set.Icc (0 : ℝ) 1) : ℝ), t.2⟩
  invFun u := ⟨⟨(u : ℝ), le_of_lt u.2.1, le_of_lt u.2.2⟩, u.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun :=
    Continuous.subtype_mk (continuous_subtype_val.comp continuous_subtype_val) _
  continuous_invFun :=
    Continuous.subtype_mk (Continuous.subtype_mk continuous_subtype_val _) _

/-- **AN OPEN EUCLIDEAN CHART GIVES A NONZERO LOCAL CLASS.** The existence form of
`SingularChartBridge.chartLocalIso` (`H_{m+2}(W, W∖x) ≅ ℤ/2` at a point with a genuinely OPEN
Euclidean chart). Stated as an existence so downstream uses never have to unify against the heavy
chart iso. -/
theorem exists_ne_zero_localHomology_of_openChart {W : TopCat} [T1Space ↑W] {m : ℕ}
    {x : ↑W} {U : Set ↑W} (hU : IsOpen U) (hx : x ∈ U)
    {q : ↑(Eucl (m + 2))} {V : Set ↑(Eucl (m + 2))} (hV : IsOpen V) (hq : q ∈ V)
    (e : ↥U ≃ₜ ↥V) (hex : (e ⟨x, hx⟩ : ↑(Eucl (m + 2))) = q) :
    ∃ α : RelativeHomology (X := W) ({x}ᶜ) (m + 2), α ≠ 0 := by
  refine ⟨(SingularChartBridge.chartLocalIso hU hx hV hq e hex).symm 1, fun hcon => ?_⟩
  have h2 := congrArg (SingularChartBridge.chartLocalIso hU hx hV hq e hex) hcon
  rw [LinearEquiv.apply_symm_apply] at h2
  exact one_ne_zero (h2.trans (LinearEquiv.map_zero _))

/-- **THE CONTRAST — at an INTERIOR point of the very same cylinder the local homology is NONZERO.**
`H_{m'+3}(M × [0,1], (M × [0,1])∖(p, t₀)) ≠ 0` when `0 < t₀ < 1`. The construction is §3's, with the
end interval `(½, 1]` replaced by the OPEN `(0,1)`: the chart image is then genuinely open in
`ℝ^{m'+3}`, so `SingularChartBridge.chartLocalIso` gives `ℤ/2` rather than `0`.

This is the **vacuity attack** on §3 run and defeated. On one and the same cylinder, in one and the
same degree `m'+3`, the local homology is nonzero at an interior point and `0` at a top-face point;
the face hypothesis `(t₀ : ℝ) = 1` of `cylTopFace_localHomology_zero` is doing all the work. -/
theorem exists_ne_zero_cylInteriorLocalHomology {m' : ℕ} {M : Type} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M] [T1Space (cylW M)] (p : M)
    {t₀ : Set.Icc (0 : ℝ) 1} (ht₀ : 0 < (t₀ : ℝ)) (ht₁ : (t₀ : ℝ) < 1) :
    ∃ α : RelativeHomology (X := TopCat.of (cylW M)) ({((p, t₀) : cylW M)}ᶜ) (m' + 1 + 2),
      α ≠ 0 := by
  haveI : T1Space ↑(TopCat.of (cylW M)) := inferInstanceAs (T1Space (cylW M))
  set c := chartAt (EuclideanSpace ℝ (Fin (m' + 2))) p with hcdef
  have hps : p ∈ c.source := mem_chart_source _ p
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp c.open_target (c p) (mem_chart_target _ p)
  refine exists_ne_zero_localHomology_of_openChart (W := TopCat.of (cylW M))
    (U := (c.source ∩ c ⁻¹' Metric.ball (c p) r) ×ˢ midEnd)
    ((c.isOpen_inter_preimage Metric.isOpen_ball).prod isOpen_midEnd)
    (show ((p, t₀) : cylW M) ∈ (c.source ∩ c ⁻¹' Metric.ball (c p) r) ×ˢ midEnd from
      ⟨⟨hps, Metric.mem_ball_self hr⟩, ht₀, ht₁⟩)
    (q := cylEuclEquiv m' (c p, ((t₀ : Set.Icc (0 : ℝ) 1) : ℝ)))
    (V := ⇑(cylEuclEquiv m').symm ⁻¹' (Metric.ball (c p) r ×ˢ Set.Ioo (0 : ℝ) 1))
    ((Metric.isOpen_ball.prod isOpen_Ioo).preimage (cylEuclEquiv m').symm.continuous) ?_
    ((Homeomorph.Set.prod (c.source ∩ c ⁻¹' Metric.ball (c p) r) midEnd).trans
      (((chartBallHomeo c hball).prodCongr midEndHomeo).trans
        ((Homeomorph.Set.prod (Metric.ball (c p) r) (Set.Ioo (0 : ℝ) 1)).symm.trans
          ((cylEuclEquiv m').toHomeomorph.subtype (fun w => by
            simp only [Set.mem_preimage, ContinuousLinearEquiv.coe_toHomeomorph,
              ContinuousLinearEquiv.symm_apply_apply]))))) rfl
  show (cylEuclEquiv m').symm (cylEuclEquiv m' (c p, ((t₀ : Set.Icc (0 : ℝ) 1) : ℝ)))
    ∈ Metric.ball (c p) r ×ˢ Set.Ioo (0 : ℝ) 1
  rw [ContinuousLinearEquiv.symm_apply_apply]
  exact ⟨Metric.mem_ball_self hr, ht₀, ht₁⟩

/-! ## §6. Transport along a homeomorphism of ambient spaces -/

/-- **LOCAL HOMOLOGY TRANSPORTS ALONG A HOMEOMORPHISM.** If `h : X ≃ₜ Y` and the local homology of
`Y` at `h x` vanishes in degree `n`, so does the local homology of `X` at `x`. The delivery vehicle
for §2/§3: the two closed pieces of a surgery-trace carrier are homeomorphic images of the disk and
of the cylinder, so their intrinsic local homology at a seam point is computed by the models above. -/
theorem localHomology_zero_of_homeo {X Y : TopCat} (h : ↑X ≃ₜ ↑Y) {x : ↑X} (n : ℕ)
    (hY : ∀ β : RelativeHomology (X := Y) ({h x}ᶜ) n, β = 0)
    (α : RelativeHomology (X := X) ({x}ᶜ) n) : α = 0 := by
  have hmaps : Set.MapsTo (⟨h, h.continuous⟩ : C(↑X, ↑Y)) ({x}ᶜ) ({h x}ᶜ) := by
    intro y hy hcon
    exact hy (Set.mem_singleton_iff.mpr (h.injective (Set.mem_singleton_iff.mp hcon)))
  have hmaps' : Set.MapsTo (⟨h.symm, h.symm.continuous⟩ : C(↑Y, ↑X)) ({h x}ᶜ) ({x}ᶜ) := by
    intro w hw hcon
    have hval : h.symm w = x := Set.mem_singleton_iff.mp hcon
    exact hw (Set.mem_singleton_iff.mpr
      ((h.apply_symm_apply w).symm.trans (congrArg h hval)))
  have hbij := SingularRelativeFunctoriality.RelativeHomology.map_bijective_of_comp_id
    (⟨h, h.continuous⟩ : C(↑X, ↑Y)) (⟨h.symm, h.symm.continuous⟩ : C(↑Y, ↑X)) hmaps hmaps'
    (ContinuousMap.ext fun z => h.symm_apply_apply z)
    (ContinuousMap.ext fun z => h.apply_symm_apply z) n
  exact hbij.injective (by rw [map_zero]; exact hY _)

end

end SKEFTHawking.SingularFaceLocalHomologyVanish
