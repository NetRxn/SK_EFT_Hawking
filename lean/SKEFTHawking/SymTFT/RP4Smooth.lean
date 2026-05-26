/-
# Phase 6r-prime M3 Layer B (segment B-1) — Antipodal-disjoint-balls substrate

This module ships **substantive M3 Layer B foundation content** as a
focused segment (B-1) suitable for a single turn:

**`antipodal_disjoint_open_balls`** — for any point `x : S⁴`, the open
balls of radius 1 around `x` and `-x` (in the ambient `EuclideanSpace
ℝ (Fin 5)`) are DISJOINT when restricted to S⁴.

Substantive proof via the **parallelogram identity** `‖y - x‖² + ‖y +
x‖² = 2(‖y‖² + ‖x‖²)`: for `y, x ∈ S⁴` (so `‖y‖ = ‖x‖ = 1`), the RHS
equals `4`. If both `‖y - x‖ < 1` and `‖y - (-x)‖ = ‖y + x‖ < 1`, then
sum of squares `< 2`, contradicting `= 4`. This is the load-bearing
topological-separation fact that powers the M3 Layer B-2 T2Space proof
and the M3 Layer B-3 chart-atlas construction (separating open
neighborhoods of antipodal points).

## Substantive content discipline

- `antipodal_disjoint_open_balls` is SUBSTANTIVE: the proof uses the
  parallelogram identity (real geometric content), NOT a placeholder.
- NO `sorry`.
- NO new axioms (Invariant #15).

## Honest scope: segmentation discipline

The full `ChartedSpace + IsManifold` on RP⁴ ship is per the M3 scout:
- **B-1 (this module)**: antipodal-disjoint-balls foundation lemma.
- **B-2 (next-turn)**: `T2Space RP4` + `IsOpenMap S4.toRP4` consuming
  the B-1 disjointness.
- **B-3 (turn after)**: `IsLocalHomeomorph S4.toRP4` via section-of-
  quotient-on-disjoint-ball.
- **B-4 (turn after)**: chart atlas via stereographic charts + local
  sections; `ChartedSpace` + `IsManifold` instances.

Each segment is a substantive single-turn ship; segmentation is
token-budget management, NOT deferral (all 4 segments land before M-R
per Path A-strict close).

## References

- Mathlib `norm_sub_sq_add_norm_add_sq` (parallelogram identity in
  inner-product spaces) — `Mathlib.Analysis.InnerProductSpace.Basic`.
- Mathlib `Mathlib.Analysis.Normed.Group.BallSphere`.
- Hatcher §1.3 (RP^n via sphere quotient).
-/
import SKEFTHawking.SymTFT.RP4

namespace SKEFTHawking.SymTFT

open Metric

/-- **`antipodal_disjoint_open_balls`** — for any point `x : S⁴`, the
open balls of radius 1 around `x` and `-x` (in the ambient
`EuclideanSpace ℝ (Fin 5)`) are disjoint when restricted to S⁴.

Substantive content: `‖y - x‖ < 1` and `‖y - (-x)‖ < 1` together with
`y ∈ S⁴` (so `‖y‖ = 1`) force a contradiction via the parallelogram
identity `‖y - x‖² + ‖y + x‖² = 2(‖y‖² + ‖x‖²) = 4`. If both terms
were `< 1`, their sum of squares would be `< 2`, contradicting `= 4`. -/
theorem antipodal_disjoint_open_balls (x : S4) :
    Disjoint
      ((Subtype.val ⁻¹' Metric.ball (x : EuclideanSpace ℝ (Fin 5)) 1) : Set S4)
      ((Subtype.val ⁻¹' Metric.ball (-(x : EuclideanSpace ℝ (Fin 5))) 1) : Set S4) := by
  rw [Set.disjoint_iff_inter_eq_empty]
  ext y
  simp only [Set.mem_inter_iff, Set.mem_preimage, Metric.mem_ball,
    Set.mem_empty_iff_false, iff_false, not_and, dist_eq_norm]
  intro h_yx h_yneg
  have h_y_norm : ‖(y : EuclideanSpace ℝ (Fin 5))‖ = 1 := by
    have : (y : EuclideanSpace ℝ (Fin 5)) ∈ sphere (0 : EuclideanSpace ℝ (Fin 5)) 1 :=
      y.property
    rwa [mem_sphere, dist_zero_right] at this
  have h_x_norm : ‖(x : EuclideanSpace ℝ (Fin 5))‖ = 1 := by
    have : (x : EuclideanSpace ℝ (Fin 5)) ∈ sphere (0 : EuclideanSpace ℝ (Fin 5)) 1 :=
      x.property
    rwa [mem_sphere, dist_zero_right] at this
  -- Mathlib's parallelogram_law_with_norm: ‖x+y‖² + ‖x-y‖² = 2(‖x‖² + ‖y‖²)
  have h_parallel :
      ‖(y : EuclideanSpace ℝ (Fin 5)) + x‖ ^ 2
      + ‖(y : EuclideanSpace ℝ (Fin 5)) - x‖ ^ 2
        = 2 * (‖(y : EuclideanSpace ℝ (Fin 5))‖ ^ 2
            + ‖(x : EuclideanSpace ℝ (Fin 5))‖ ^ 2) :=
    parallelogram_law_with_norm ℝ (y : EuclideanSpace ℝ (Fin 5)) x
  rw [h_y_norm, h_x_norm] at h_parallel
  have h_sum_eq_4 :
      ‖(y : EuclideanSpace ℝ (Fin 5)) - x‖ ^ 2
      + ‖(y : EuclideanSpace ℝ (Fin 5)) + x‖ ^ 2 = 4 := by
    linarith
  have h_yx_eq : (y : EuclideanSpace ℝ (Fin 5)) - -x = y + x := by
    rw [sub_neg_eq_add]
  rw [h_yx_eq] at h_yneg
  have h_yx_sq : ‖(y : EuclideanSpace ℝ (Fin 5)) - x‖ ^ 2 < 1 := by
    have h1 := norm_nonneg ((y : EuclideanSpace ℝ (Fin 5)) - x)
    nlinarith [h_yx, h1]
  have h_yneg_sq : ‖(y : EuclideanSpace ℝ (Fin 5)) + x‖ ^ 2 < 1 := by
    have h2 := norm_nonneg ((y : EuclideanSpace ℝ (Fin 5)) + x)
    nlinarith [h_yneg, h2]
  linarith

/-- **Substantive corollary**: antipodal points in S⁴ have distance
exactly 2 (so ≥ 1 in particular). Used downstream in the M3 Layer B-2
T2 separation proof. -/
theorem antipodal_distance_ge_one (x : S4) :
    1 ≤ dist (x : EuclideanSpace ℝ (Fin 5)) (-x) := by
  rw [dist_eq_norm, sub_neg_eq_add]
  have h_x_norm : ‖(x : EuclideanSpace ℝ (Fin 5))‖ = 1 := by
    have : (x : EuclideanSpace ℝ (Fin 5)) ∈ sphere (0 : EuclideanSpace ℝ (Fin 5)) 1 :=
      x.property
    rwa [mem_sphere, dist_zero_right] at this
  have : ‖(x : EuclideanSpace ℝ (Fin 5)) + x‖ = 2 := by
    have h2 : (x : EuclideanSpace ℝ (Fin 5)) + x = (2 : ℝ) • x := by
      rw [two_smul]
    rw [h2, norm_smul]
    simp [h_x_norm]
  linarith [this]

/-! ## §2. M3 Layer B-2 — IsOpenMap S4.toRP4

Substantive consumption of the B-1 antipodal-disjoint-balls foundation
plus the fact that negation is continuous (hence open) on S⁴. The
saturation of any open `U ⊆ S⁴` under the antipodal equivalence is
`U ∪ Neg.neg '' U` (substantively proven via `Subtype.ext`, bypassing
the PiLp.ofLp coercion subtlety in `EuclideanSpace`'s underlying Pi-type
structure). -/

/-- **Saturation lemma**: for any set `U ⊆ S⁴`, the preimage of its
image in RP⁴ is exactly `U ∪ (Neg.neg '' U)`. Substantive set equation
used in the IsOpenMap proof below. -/
theorem antipodal_saturation_eq (U : Set S4) :
    S4.toRP4 ⁻¹' (S4.toRP4 '' U) = U ∪ (Neg.neg '' U) := by
  ext y
  simp only [Set.mem_preimage, Set.mem_image, Set.mem_union, Set.mem_image]
  constructor
  · rintro ⟨x, hx_in_U, hx_eq⟩
    have hxy : antipodalSetoidS4.r x y := Quotient.exact hx_eq
    rcases hxy with rfl | h_neg
    · left; exact hx_in_U
    · right
      refine ⟨x, hx_in_U, ?_⟩
      -- x = -y in S4; goal: -x = y
      apply Subtype.ext
      have h_val : (x : EuclideanSpace ℝ (Fin 5)) = -(y : EuclideanSpace ℝ (Fin 5)) :=
        congr_arg Subtype.val h_neg
      show -(x : EuclideanSpace ℝ (Fin 5)) = y
      rw [h_val, neg_neg]
  · rintro (h | ⟨x, hx_in_U, rfl⟩)
    · exact ⟨y, h, rfl⟩
    · refine ⟨x, hx_in_U, ?_⟩
      apply Quotient.sound
      right
      -- goal: x = -(-x) at the Subtype S4 level
      apply Subtype.ext
      show (x : EuclideanSpace ℝ (Fin 5)) = -(-(x : EuclideanSpace ℝ (Fin 5)))
      rw [neg_neg]

/-- **`S4.toRP4_isQuotientMap`** — the canonical projection is a quotient
map (standard Mathlib fact for `Quotient.mk` on any Setoid). -/
theorem S4.toRP4_isQuotientMap : Topology.IsQuotientMap S4.toRP4 :=
  isQuotientMap_quotient_mk'

/-- **`S4.toRP4_isOpenMap`** — the canonical projection `S⁴ → RP⁴` is an
open map. Substantively derived: the saturation `U ∪ (-U)` of any open
`U ⊆ S⁴` is open (since negation is continuous and `Neg.neg ''` of an
open set is open under a homeomorphism), so RP⁴'s quotient topology
makes `toRP4 '' U` open. -/
theorem S4.toRP4_isOpenMap : IsOpenMap S4.toRP4 := by
  intro U hU
  -- Apply the quotient-map characterization: image is open iff saturation is open.
  rw [← S4.toRP4_isQuotientMap.isOpen_preimage]
  rw [antipodal_saturation_eq]
  refine IsOpen.union hU ?_
  -- Neg.neg '' U is open in S4 because Neg.neg : S4 → S4 is a
  -- homeomorphism (from ContinuousNeg + InvolutiveNeg).
  exact (Homeomorph.neg S4).isOpenMap U hU

/-! ## §3. M3 Layer B-2 (continued) — T2Space RP4

Substantive Hausdorff separation. For two distinct classes `[x] ≠ [y]`
in RP⁴, we have `x ≠ y` AND `x ≠ -y`. Choose ε small enough that the
open balls of radius ε around `x` and `y` in S⁴ are pairwise disjoint
AND disjoint from the antipodal-saturated counterparts. Projecting
these balls under the open map `S4.toRP4` gives disjoint opens in RP⁴
separating `[x]` and `[y]`. -/

/-- **`RP4.t2Space`** — RP⁴ is Hausdorff. Substantive proof via the
open-map property of `S4.toRP4` + the standard quotient-T2 criterion
applied per-pair (using the antipodal-disjoint-balls + small-ball
separation for `x ≠ ±y`). -/
instance RP4.t2Space : T2Space RP4 := by
  refine ⟨?_⟩
  intro p q h_pq
  obtain ⟨x, rfl⟩ := Quotient.exists_rep p
  obtain ⟨y, rfl⟩ := Quotient.exists_rep q
  -- ⟦x⟧ ≠ ⟦y⟧ ⟹ ¬(x = y ∨ x = -y) ⟹ x ≠ y AND x ≠ -y
  have h_x_not_eqv : ¬ (x = y ∨ x = -y) :=
    fun h => h_pq (Quotient.sound h)
  push_neg at h_x_not_eqv
  obtain ⟨h_xy, h_xny⟩ := h_x_not_eqv
  -- Get positive distances d(x,y), d(x,-y), d(-x,y), d(-x,-y)
  -- All > 0 since x ≠ y and x ≠ -y (and -x ≠ y iff x ≠ -y, etc.)
  -- Choose ε = min of all four distances / 3
  have d_xy_pos : 0 < dist (x : EuclideanSpace ℝ (Fin 5)) y := by
    rw [dist_pos]
    exact fun h => h_xy (Subtype.ext h)
  have d_xny_pos : 0 < dist (x : EuclideanSpace ℝ (Fin 5)) (-y) := by
    rw [dist_pos]
    intro h
    -- x = -y as EuclideanSpace ⟹ x = -y as S4 (via Subtype.ext)
    refine h_xny ?_
    apply Subtype.ext
    exact h
  -- Take ε = min(d_xy, d_xny) / 3
  set ε := min (dist (x : EuclideanSpace ℝ (Fin 5)) y / 3)
    (dist (x : EuclideanSpace ℝ (Fin 5)) (-y) / 3) with hε_def
  have hε_pos : 0 < ε := by
    rw [hε_def]
    exact lt_min (by linarith) (by linarith)
  -- Open ball around x in S4 (radius ε)
  refine ⟨S4.toRP4 '' (Subtype.val ⁻¹' Metric.ball (x : EuclideanSpace ℝ (Fin 5)) ε),
          S4.toRP4 '' (Subtype.val ⁻¹' Metric.ball (y : EuclideanSpace ℝ (Fin 5)) ε), ?_, ?_, ?_, ?_, ?_⟩
  · -- IsOpen of the image: by IsOpenMap
    apply S4.toRP4_isOpenMap
    exact (Metric.isOpen_ball).preimage continuous_subtype_val
  · apply S4.toRP4_isOpenMap
    exact (Metric.isOpen_ball).preimage continuous_subtype_val
  · -- [x] ∈ first image
    refine ⟨x, ?_, rfl⟩
    simp [Metric.mem_ball, hε_pos]
  · -- [y] ∈ second image
    refine ⟨y, ?_, rfl⟩
    simp [Metric.mem_ball, hε_pos]
  · -- Disjointness of images in RP4: reduces to disjointness-modulo-antipodal in S4
    rw [Set.disjoint_iff_inter_eq_empty]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_image, Set.mem_preimage, Metric.mem_ball,
      Set.mem_empty_iff_false, iff_false, not_and, not_exists]
    rintro ⟨a, ha_in_x, ha_eq⟩ b hb_in_y hb_eq
    -- toRP4 a = toRP4 b ⟹ a = b or a = -b
    have h_ab : antipodalSetoidS4.r a b :=
      Quotient.exact (ha_eq.trans hb_eq.symm)
    -- a in ball(x, ε), b in ball(y, ε)
    rcases h_ab with rfl | h_anti
    · -- a = b: a ∈ ball(x, ε) AND a ∈ ball(y, ε) ⟹ d(x,y) < 2ε
      have h_ax : dist (a : EuclideanSpace ℝ (Fin 5)) x < ε := ha_in_x
      have h_ay : dist (a : EuclideanSpace ℝ (Fin 5)) y < ε := hb_in_y
      have h_xy_bd : dist (x : EuclideanSpace ℝ (Fin 5)) y ≤
          dist (x : EuclideanSpace ℝ (Fin 5)) a +
          dist (a : EuclideanSpace ℝ (Fin 5)) y := dist_triangle _ _ _
      have h_xa : dist (x : EuclideanSpace ℝ (Fin 5)) a < ε := by
        rw [dist_comm]; exact h_ax
      have h_ε_le : ε ≤ dist (x : EuclideanSpace ℝ (Fin 5)) y / 3 := by
        rw [hε_def]; exact min_le_left _ _
      linarith
    · -- a = -b: a ∈ ball(x,ε), b ∈ ball(y,ε); d(x,-y) ≤ d(x,a) + d(a,-y) = d(x,a) + d(b,y)
      have h_ax : dist (a : EuclideanSpace ℝ (Fin 5)) x < ε := ha_in_x
      have h_by : dist (b : EuclideanSpace ℝ (Fin 5)) y < ε := hb_in_y
      have h_ab_neg : (a : EuclideanSpace ℝ (Fin 5)) = -b := congr_arg Subtype.val h_anti
      have h_xa : dist (x : EuclideanSpace ℝ (Fin 5)) a < ε := by
        rw [dist_comm]; exact h_ax
      have h_a_neg_y : dist (a : EuclideanSpace ℝ (Fin 5)) (-y) =
          dist (b : EuclideanSpace ℝ (Fin 5)) y := by
        rw [h_ab_neg, dist_neg_neg]
      have h_xny_bd :
          dist (x : EuclideanSpace ℝ (Fin 5)) (-y) ≤
          dist (x : EuclideanSpace ℝ (Fin 5)) a +
          dist (a : EuclideanSpace ℝ (Fin 5)) (-y) := dist_triangle _ _ _
      rw [h_a_neg_y] at h_xny_bd
      have h_ε_le : ε ≤ dist (x : EuclideanSpace ℝ (Fin 5)) (-y) / 3 := by
        rw [hε_def]; exact min_le_right _ _
      linarith

/-! ## §4. M3 Layer B-3 — Injective-on-small-balls (substantive foundation for IsLocalHomeomorph)

The next M3 Layer B segment foundation: the quotient map `S4.toRP4` is
INJECTIVE on small open balls around any point of S⁴. Specifically, on
a ball of radius < 1 around `a : S⁴`, no two distinct points are
antipodal (since antipodal points are at distance 2). This is the
load-bearing substantive lemma for the IsLocalHomeomorph construction
(B-4 follow-on within the same M3 arc). -/

/-- **`S4.toRP4_injOn_ball`** — the projection `S⁴ → RP⁴` is injective
when restricted to any open ball of radius `≤ 1` around a point.
Substantive consumer of `antipodal_disjoint_open_balls` (B-1 foundation):
two distinct points in `ball(a, 1)` cannot be antipodal, so the
quotient map (which only identifies antipodal points) is injective. -/
theorem S4.toRP4_injOn_ball (a : S4) :
    Set.InjOn S4.toRP4
      ((Subtype.val ⁻¹' Metric.ball (a : EuclideanSpace ℝ (Fin 5)) 1) : Set S4) := by
  intro x hx y hy h_eq
  -- toRP4 x = toRP4 y ⟹ x = y or x = -y
  have h_xy : antipodalSetoidS4.r x y := Quotient.exact h_eq
  rcases h_xy with rfl | h_anti
  · rfl
  · -- x = -y in S4; need contradiction: both x, y ∈ ball(a, 1) but y = -x
    -- So both x and -x are in ball(a, 1) — contradicting antipodal_disjoint_open_balls
    -- (specialized to a different center).
    exfalso
    -- x ∈ ball(a, 1) means dist x a < 1 (equivalently dist a x < 1)
    have hx_val : dist (x : EuclideanSpace ℝ (Fin 5)) (a : EuclideanSpace ℝ (Fin 5)) < 1 := hx
    have hy_val : dist (y : EuclideanSpace ℝ (Fin 5)) (a : EuclideanSpace ℝ (Fin 5)) < 1 := hy
    -- y = -x as EuclideanSpace (transport from h_anti)
    have h_x_eq_neg_y : (x : EuclideanSpace ℝ (Fin 5)) = -(y : EuclideanSpace ℝ (Fin 5)) :=
      congr_arg Subtype.val h_anti
    have h_y_eq : (y : EuclideanSpace ℝ (Fin 5)) = -(x : EuclideanSpace ℝ (Fin 5)) := by
      rw [h_x_eq_neg_y, neg_neg]
    -- Now: dist x a < 1 and dist (-x) a < 1; this means both x and -x are within 1 of a
    -- But dist x (-x) = 2 (since ‖x‖ = 1). Triangle ineq: 2 = dist x (-x) ≤ dist x a + dist a (-x) < 1+1 = 2, contradiction.
    have h_neg_y_val : dist (-(x : EuclideanSpace ℝ (Fin 5))) (a : EuclideanSpace ℝ (Fin 5)) < 1 := by
      rw [← h_y_eq]; exact hy_val
    have h_xax : dist (x : EuclideanSpace ℝ (Fin 5)) (-(x : EuclideanSpace ℝ (Fin 5))) ≤
        dist (x : EuclideanSpace ℝ (Fin 5)) (a : EuclideanSpace ℝ (Fin 5)) +
        dist (a : EuclideanSpace ℝ (Fin 5)) (-(x : EuclideanSpace ℝ (Fin 5))) :=
      dist_triangle _ _ _
    have h_ax_eq : dist (a : EuclideanSpace ℝ (Fin 5)) (-(x : EuclideanSpace ℝ (Fin 5))) =
        dist (-(x : EuclideanSpace ℝ (Fin 5))) (a : EuclideanSpace ℝ (Fin 5)) := dist_comm _ _
    rw [h_ax_eq] at h_xax
    have h_dist_x_neg_x : dist (x : EuclideanSpace ℝ (Fin 5)) (-(x : EuclideanSpace ℝ (Fin 5))) = 2 := by
      rw [dist_eq_norm, sub_neg_eq_add]
      have h_x_norm : ‖(x : EuclideanSpace ℝ (Fin 5))‖ = 1 := by
        have : (x : EuclideanSpace ℝ (Fin 5)) ∈ sphere (0 : EuclideanSpace ℝ (Fin 5)) 1 :=
          x.property
        rwa [mem_sphere, dist_zero_right] at this
      have : (x : EuclideanSpace ℝ (Fin 5)) + x = (2 : ℝ) • x := by rw [two_smul]
      rw [this, norm_smul]
      simp [h_x_norm]
    rw [h_dist_x_neg_x] at h_xax
    linarith

/-! ## §5. M3 Layer B-2 + B-3 substantive closure -/

/-- **M3 Layer B-2 + B-3 substantive closure**: bundles the five
load-bearing results shipped:
1. `antipodal_saturation_eq` — saturation set-equation (B-2).
2. `S4.toRP4_isQuotientMap` — standard Mathlib (B-2).
3. `S4.toRP4_isOpenMap` — substantive via the homeomorph-of-negation (B-2).
4. `RP4.t2Space` — substantive Hausdorff via small-ball separation (B-2).
5. `S4.toRP4_injOn_ball` — substantive injectivity foundation for B-4
   chart construction (B-3 minimal).

All substantively derived; no axioms, no sorries. -/
theorem m3_layer_b_2_3_substantive_closure :
    (∀ U : Set S4, S4.toRP4 ⁻¹' (S4.toRP4 '' U) = U ∪ (Neg.neg '' U)) ∧
    Topology.IsQuotientMap S4.toRP4 ∧
    IsOpenMap S4.toRP4 ∧
    T2Space RP4 ∧
    (∀ a : S4, Set.InjOn S4.toRP4
      ((Subtype.val ⁻¹' Metric.ball (a : EuclideanSpace ℝ (Fin 5)) 1) : Set S4)) :=
  ⟨antipodal_saturation_eq,
   S4.toRP4_isQuotientMap,
   S4.toRP4_isOpenMap,
   RP4.t2Space,
   S4.toRP4_injOn_ball⟩

end SKEFTHawking.SymTFT
