/-
# Phase 5q.H — the Kummer K3 generator, K4′ (Route B): the punctured torus `T⁴°` (ROUND-BALL)

Continues `KummerInvolution.lean` (K2 = the involution `τ(w) = w⁻¹`, K3 = its 16 fixed points
`{±1}⁴`, both PROVEN there). Read `KummerK3Base.lean` §A first (the whole Kummer brick sequence) and
the **binding Route-B design doc** `docs/dev-loops/Phase5qH/KUMMER_K4K10_DESIGN.md`: the singular
orbifold quotient is NEVER formed — instead we **excise first, quotient free, weld bundles**. This
module ships the **K4′** brick (Wave K-I) plus the residual K2/K3 packaging that K4′–K6′ consume,
UNCONDITIONALLY (kernel-pure `{propext, Classical.choice, Quot.sound}`; no
`sorry`/`native_decide`/`maxHeartbeats`/axiom).

**THE ROUND-BALL EXCISION (the 2026-07-20 route-level fix).** The excised regions were originally the
sup-metric `Metric.ball c (1/2)` on `TorusFour = (S¹)⁴`. But `Prod.dist_eq = max`, so those balls are
**boxes**: their boundary `Metric.sphere c (1/2)` is a *cubical* `S³` with corners, blocking the smooth
manifold-with-boundary / collar chart. The fix: excise **round Euclidean balls in the centered chart**
`{t : ℝ⁴ ∣ ‖t‖ < ρ}` mapped in by `centeredChartParam c` (`chartBall`). In the chart the boundary is a
**round** `S³` (`‖t‖ = ρ`), and the `τ = −id` normal form (`centeredChartParam_involution`) makes the
boundary quotient EXACTLY `S³/±1 = ℝP³` on the nose (Design Risk #2). The pinned radius is **ρ = 1/2**
(`excisionRadius`); any `0 < ρ < π` with `2ρ ≤ 2` works — the 16 fixed points `{±1}⁴` are `≥ 2` apart
(`fixedSet_dist_ge`) and `dist(centeredChartParam c t, c) ≤ ‖t‖` (arc ≤ chord bound), so the round balls
sit inside the metric `1/2`-balls (`chartBall_subset_metricBall`) and stay pairwise disjoint; `ρ = 1/2 < π`
gives injectivity of the chart on the closed ball (`centeredChartParam_injOn`), which pins the boundary
sphere off the open ball.

**K2 packaging (extension).** `τ` as a **homeomorphism** (`torusFourInvolutionHomeo`) and a
**`C^ω` diffeomorphism** (`torusFourInvolutionDiffeo`) of `T⁴` — the group inverse of the compact
abelian Lie group `T⁴`, self-inverse and smooth both ways.

**K3 packaging (extension).** The 16 fixed points as an explicit **`Fintype`** with
**`Fintype.card = 16`** (`torusFourInvolution_fixedPoints_fintypeCard`), an explicit **`Finset`**
(`fixedFinset`, card 16), and the coordinatewise membership certificate `mem_fixedSet_iff`.

**K4′ — the round-punctured torus (the brick).**
- **Equivariant charts (`τ = −id` in-chart).** `circle_chart_involution` per factor,
  `centeredChartParam_involution` on `T⁴`: `τ (centeredChartParam c t) = centeredChartParam c (−t)`.
- **16 disjoint open `τ`-invariant round balls.** `chartBall c = centeredChartParam c '' {‖t‖ < ρ}`,
  open (`isOpen_chartBall`, since `centeredChartParam c` is an open map — `Circle.exp` is a covering
  map), `τ`-invariant (`chartBall_involution_mem_iff`; `τ = −id` in-chart preserves `‖t‖`), pairwise
  disjoint (`excisedBalls_pairwiseDisjoint`, via the metric containment + `fixedSet_dist_ge`).
- **`T⁴° := T⁴ ∖ excisedBalls`** (`puncturedTorus`), `τ`-invariant, `τ` FREE there
  (`involution_free_on_puncturedTorus` — `Fix(τ) ⊆ excisedBalls`).
- **Boundary spheres — round `S³/±1`.** `chartSphere c = centeredChartParam c '' {‖t‖ = ρ}` lies in
  `T⁴°` (`sphere_subset_puncturedTorus`, uses chart injectivity), `τ`-invariant
  (`chartSphere_involution_invariant`); in-chart `τ = −id`, so on `‖t‖ = ρ` it is the antipodal map,
  making `∂B_i / τ = S³/±1 = ℝP³` literal (the pinned presentation K5′/K6′a weld against).
-/
import Mathlib
import SKEFTHawking.KummerK3Base
import SKEFTHawking.KummerInvolution

namespace SKEFTHawking.KummerPuncturedTorus

open scoped Manifold ContDiff
open SKEFTHawking.KummerK3Base
open SKEFTHawking.KummerInvolution

/-! ## K2 packaging — `τ` as a homeomorphism / `C^ω` diffeomorphism of `T⁴` -/

/-- **`τ` as a homeomorphism** of `T⁴`: the topological-group inverse of `T⁴ = (S¹)⁴`
(`Homeomorph.inv`). Self-inverse, continuous both ways. -/
noncomputable def torusFourInvolutionHomeo : TorusFour ≃ₜ TorusFour := Homeomorph.inv TorusFour

@[simp] theorem torusFourInvolutionHomeo_apply (x : TorusFour) :
    torusFourInvolutionHomeo x = torusFourInvolution x := rfl

/-- **`τ` as a `C^ω` diffeomorphism** of `T⁴` on the product model — the Lie-group inverse, smooth in
both directions (`contMDiff_inv`, `T⁴` a Lie group by `torusFour_lieGroup`). This is the
smooth-structure-preserving self-map that descends to the free quotient `T⁴°/τ` (K5′). -/
noncomputable def torusFourInvolutionDiffeo :
    Diffeomorph ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1))))
      ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) TorusFour TorusFour ω where
  toEquiv := Equiv.inv TorusFour
  contMDiff_toFun := contMDiff_inv _ ω
  contMDiff_invFun := contMDiff_inv _ ω

@[simp] theorem torusFourInvolutionDiffeo_apply (x : TorusFour) :
    torusFourInvolutionDiffeo x = torusFourInvolution x := rfl

/-- The diffeomorphism is its own inverse (`τ² = id`), matching `torusFourInvolution_involutive`. -/
theorem torusFourInvolutionDiffeo_symm :
    torusFourInvolutionDiffeo.symm = torusFourInvolutionDiffeo := rfl

/-! ## K3 packaging — the 16 fixed points as an explicit `Fintype` / `Finset` -/

/-- The fixed set of `τ` as a `Set TorusFour` (the 16 points `{±1}⁴`, i.e. the 2-torsion of `T⁴`). -/
def fixedSet : Set TorusFour := {x | torusFourInvolution x = x}

/-- **Coordinatewise fixedness certificate**: `x` is `τ`-fixed iff every coordinate is a square-root of
unity (`∈ {1, negOne}`). The decidable per-coordinate membership description of the 16 fixed points. -/
theorem mem_fixedSet_iff (x : TorusFour) :
    torusFourInvolution x = x ↔
      (x.1 = 1 ∨ x.1 = negOne) ∧ (x.2.1 = 1 ∨ x.2.1 = negOne) ∧
        (x.2.2.1 = 1 ∨ x.2.2.1 = negOne) ∧ (x.2.2.2 = 1 ∨ x.2.2.2 = negOne) := by
  simp only [torusFourInvolution, Prod.ext_iff, circle_inv_self_iff]

/-- The per-factor square-root-of-unity subtype is finite (`= {1, negOne}`). -/
instance : Finite {z : Circle // z⁻¹ = z} := by
  have hfin : ({z : Circle | z⁻¹ = z}).Finite := by
    have hset : {z : Circle | z⁻¹ = z} = {1, negOne} := by ext z; simp [circle_inv_self_iff]
    rw [hset]; exact (Set.finite_singleton _).insert _
  exact hfin.to_subtype

/-- The 16 fixed points form a finite type (product of four finite per-factor 2-torsion subtypes,
through `fixedPointsEquiv`). -/
instance : Finite {x : TorusFour // torusFourInvolution x = x} :=
  Finite.of_equiv _ fixedPointsEquiv.symm

/-- The 16 fixed points as a `Fintype`. -/
noncomputable instance : Fintype {x : TorusFour // torusFourInvolution x = x} :=
  Fintype.ofFinite _

/-- **K3 falsifiable pin (Fintype form)**: `Fintype.card {x // τ x = x} = 16`, from the banked
`Nat.card = 16` (`torusFourInvolution_fixedPoints_card`). -/
theorem torusFourInvolution_fixedPoints_fintypeCard :
    Fintype.card {x : TorusFour // torusFourInvolution x = x} = 16 := by
  rw [← Nat.card_eq_fintype_card]
  exact torusFourInvolution_fixedPoints_card

/-- The 16 fixed points as an explicit `Finset TorusFour` — the image of `Finset.univ` on the
fixed-point subtype under the subtype embedding. -/
noncomputable def fixedFinset : Finset TorusFour :=
  (Finset.univ : Finset {x : TorusFour // torusFourInvolution x = x}).map
    (Function.Embedding.subtype _)

/-- Membership in `fixedFinset` is exactly `τ`-fixedness. -/
theorem mem_fixedFinset (x : TorusFour) : x ∈ fixedFinset ↔ torusFourInvolution x = x := by
  simp only [fixedFinset, Finset.mem_map, Finset.mem_univ, Function.Embedding.coe_subtype,
    true_and, Subtype.exists, exists_prop, exists_eq_right]

/-- **The explicit `Finset` of 16 fixed points has card 16.** -/
theorem fixedFinset_card : fixedFinset.card = 16 := by
  rw [fixedFinset, Finset.card_map, Finset.card_univ]
  exact torusFourInvolution_fixedPoints_fintypeCard

/-! ## K4′ — `τ` is an isometry of `T⁴` -/

/-- **Inversion is an isometry of the circle** (`z⁻¹ = z̄` on `S¹`, and conjugation preserves `dist`). -/
theorem circleInv_dist (z w : Circle) : dist z⁻¹ w⁻¹ = dist z w := by
  show dist (((z⁻¹ : Circle) : ℂ)) (((w⁻¹ : Circle) : ℂ)) = dist ((z : Circle) : ℂ) ((w : Circle) : ℂ)
  rw [Circle.coe_inv_eq_conj, Circle.coe_inv_eq_conj, Complex.dist_conj_conj]

/-- **`τ` is `dist`-preserving on `T⁴`** — componentwise inversion, each factor an isometry. -/
theorem torusFourInvolution_dist (x y : TorusFour) :
    dist (torusFourInvolution x) (torusFourInvolution y) = dist x y := by
  simp only [torusFourInvolution, Prod.dist_eq, circleInv_dist]

/-- **`τ` is an isometry of `T⁴`.** -/
theorem torusFourInvolution_isometry : Isometry torusFourInvolution :=
  Isometry.of_dist_eq torusFourInvolution_dist

/-- Distance to a **fixed** center is `τ`-invariant: `dist (τ x) c = dist x c` when `τ c = c`. -/
theorem dist_involution_fixed {c : TorusFour} (hc : torusFourInvolution c = c) (x : TorusFour) :
    dist (torusFourInvolution x) c = dist x c := by
  have : dist (torusFourInvolution x) c
      = dist (torusFourInvolution x) (torusFourInvolution c) := by rw [hc]
  rw [this, torusFourInvolution_dist]

/-! ## K4′ — minimum separation of the 16 fixed points -/

/-- `dist (1, negOne) = 2` on the circle (the two real points of `S¹`, at distance `‖1 − (−1)‖ = 2`). -/
theorem dist_one_negOne : dist (1 : Circle) negOne = 2 := by
  show dist ((1 : Circle) : ℂ) ((negOne : Circle) : ℂ) = 2
  rw [Circle.coe_one, coe_negOne, Complex.dist_eq]; norm_num

/-- Two distinct square-roots of unity on the circle are at distance exactly `2`. -/
theorem perFactor_dist_of_ne {a b : Circle} (ha : a = 1 ∨ a = negOne) (hb : b = 1 ∨ b = negOne)
    (hab : a ≠ b) : dist a b = 2 := by
  rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
  · exact absurd rfl hab
  · exact dist_one_negOne
  · rw [dist_comm]; exact dist_one_negOne
  · exact absurd rfl hab

/-- A per-coordinate distance bounds the product (sup-metric) distance from below. -/
theorem le_dist_c1 (x y : TorusFour) : dist x.1 y.1 ≤ dist x y := by
  rw [Prod.dist_eq]; exact le_max_left _ _

theorem le_dist_c2 (x y : TorusFour) : dist x.2.1 y.2.1 ≤ dist x y :=
  calc dist x.2.1 y.2.1 ≤ dist x.2 y.2 := by rw [Prod.dist_eq]; exact le_max_left _ _
    _ ≤ dist x y := by rw [Prod.dist_eq]; exact le_max_right _ _

theorem le_dist_c3 (x y : TorusFour) : dist x.2.2.1 y.2.2.1 ≤ dist x y :=
  calc dist x.2.2.1 y.2.2.1 ≤ dist x.2.2 y.2.2 := by rw [Prod.dist_eq]; exact le_max_left _ _
    _ ≤ dist x.2 y.2 := by rw [Prod.dist_eq]; exact le_max_right _ _
    _ ≤ dist x y := by rw [Prod.dist_eq]; exact le_max_right _ _

theorem le_dist_c4 (x y : TorusFour) : dist x.2.2.2 y.2.2.2 ≤ dist x y :=
  calc dist x.2.2.2 y.2.2.2 ≤ dist x.2.2 y.2.2 := by rw [Prod.dist_eq]; exact le_max_right _ _
    _ ≤ dist x.2 y.2 := by rw [Prod.dist_eq]; exact le_max_right _ _
    _ ≤ dist x y := by rw [Prod.dist_eq]; exact le_max_right _ _

/-- **Minimum separation of the 16 fixed points**: distinct points of `{±1}⁴` are at distance `≥ 2`
(they differ in some coordinate, where the two values `1, negOne` are `2` apart). The explicit
separation that makes the radius-`1/2` excised balls pairwise disjoint. -/
theorem fixedSet_dist_ge {c1 c2 : TorusFour} (h1 : c1 ∈ fixedSet) (h2 : c2 ∈ fixedSet)
    (hne : c1 ≠ c2) : 2 ≤ dist c1 c2 := by
  obtain ⟨a1, a2, a3, a4⟩ := (mem_fixedSet_iff c1).mp h1
  obtain ⟨b1, b2, b3, b4⟩ := (mem_fixedSet_iff c2).mp h2
  by_cases e1 : c1.1 = c2.1
  · by_cases e2 : c1.2.1 = c2.2.1
    · by_cases e3 : c1.2.2.1 = c2.2.2.1
      · have e4 : c1.2.2.2 ≠ c2.2.2.2 := fun e4 =>
          hne (Prod.ext e1 (Prod.ext e2 (Prod.ext e3 e4)))
        calc (2 : ℝ) = dist c1.2.2.2 c2.2.2.2 := (perFactor_dist_of_ne a4 b4 e4).symm
          _ ≤ dist c1 c2 := le_dist_c4 c1 c2
      · calc (2 : ℝ) = dist c1.2.2.1 c2.2.2.1 := (perFactor_dist_of_ne a3 b3 e3).symm
          _ ≤ dist c1 c2 := le_dist_c3 c1 c2
    · calc (2 : ℝ) = dist c1.2.1 c2.2.1 := (perFactor_dist_of_ne a2 b2 e2).symm
        _ ≤ dist c1 c2 := le_dist_c2 c1 c2
  · calc (2 : ℝ) = dist c1.1 c2.1 := (perFactor_dist_of_ne a1 b1 e1).symm
      _ ≤ dist c1 c2 := le_dist_c1 c1 c2

/-! ## K4′ — the equivariant centered charts (`τ = −id` in chart) -/

/-- **Per-factor equivariant chart**: on the circle, in the exp-chart centered at a square-root of
unity `c` (`c⁻¹ = c`), inversion is negation of the chart parameter — `(c · exp t)⁻¹ = c · exp (−t)`.
The local model that makes `S¹/τ` a half-circle, and `T⁴/τ` locally `cone(ℝP³)`. -/
theorem circle_chart_involution (c : Circle) (hc : c⁻¹ = c) (t : ℝ) :
    (c * Circle.exp t)⁻¹ = c * Circle.exp (-t) := by
  rw [mul_inv, hc, ← Circle.exp_neg]

/-- The `τ`-**centered chart parametrization** at `c ∈ T⁴`: `ℝ⁴ → T⁴`, `t ↦ c · exp(t)` per factor
(centered: `t = 0 ↦ c`). -/
noncomputable def centeredChartParam (c : TorusFour) : (ℝ × ℝ × ℝ × ℝ) → TorusFour :=
  fun t => (c.1 * Circle.exp t.1, c.2.1 * Circle.exp t.2.1,
            c.2.2.1 * Circle.exp t.2.2.1, c.2.2.2 * Circle.exp t.2.2.2)

/-- Negation ("`−id`") on the chart domain `ℝ⁴`. -/
def chartNeg : (ℝ × ℝ × ℝ × ℝ) → (ℝ × ℝ × ℝ × ℝ) := fun t => (-t.1, -t.2.1, -t.2.2.1, -t.2.2.2)

/-- The centered chart sends `0` to its center. -/
theorem centeredChartParam_zero (c : TorusFour) : centeredChartParam c 0 = c := by
  simp only [centeredChartParam, Prod.fst_zero, Prod.snd_zero, Circle.exp_zero, mul_one]

/-- **The equivariant-chart identity** (`τ = −id` in the centered chart): at a fixed point `c`,
`τ (centeredChartParam c t) = centeredChartParam c (−t)`. Conjugating `τ` by the centered chart yields
`−id` — the local normal form that presents `T⁴/τ` as `cone(ℝP³) = ℝ⁴/±1` at each fixed point, and the
boundary as the ANTIPODAL quotient `S³/±1` (Design Risk #2). -/
theorem centeredChartParam_involution (c : TorusFour) (hc : torusFourInvolution c = c)
    (t : ℝ × ℝ × ℝ × ℝ) :
    torusFourInvolution (centeredChartParam c t) = centeredChartParam c (chartNeg t) := by
  have h1 : c.1⁻¹ = c.1 := congrArg Prod.fst hc
  have h2 : c.2.1⁻¹ = c.2.1 := congrArg (Prod.fst ∘ Prod.snd) hc
  have h3 : c.2.2.1⁻¹ = c.2.2.1 := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hc
  have h4 : c.2.2.2⁻¹ = c.2.2.2 := congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) hc
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · exact circle_chart_involution c.1 h1 t.1
  · exact circle_chart_involution c.2.1 h2 t.2.1
  · exact circle_chart_involution c.2.2.1 h3 t.2.2.1
  · exact circle_chart_involution c.2.2.2 h4 t.2.2.2

/-- The composed form: on a fixed-point chart, `τ ∘ chart = chart ∘ (−id)`. -/
theorem centeredChartParam_involution_comp (c : TorusFour) (hc : torusFourInvolution c = c) :
    torusFourInvolution ∘ centeredChartParam c = centeredChartParam c ∘ chartNeg :=
  funext (centeredChartParam_involution c hc)

/-! ## K4′ — chart-domain Euclidean-norm machinery

The chart domain is `ℝ⁴ = ℝ × ℝ × ℝ × ℝ`. `sqNorm` is the squared **Euclidean** norm (NOT the product
sup-norm), so the round ball `{sqNorm < ρ²}` is genuinely round; its image under `centeredChartParam c`
is `chartBall c`, whose boundary is a round `S³` (the box-corner fix). -/

/-- `|u| < ρ` from `u² < ρ²` (with `0 < ρ`) — the sign-free Euclidean-coordinate bound. -/
theorem abs_lt_of_sq_lt_sq {u ρ : ℝ} (hρ : 0 < ρ) (h : u ^ 2 < ρ ^ 2) : |u| < ρ := by
  rw [← Real.sqrt_sq_eq_abs, show ρ = Real.sqrt (ρ ^ 2) from (Real.sqrt_sq hρ.le).symm]
  exact Real.sqrt_lt_sqrt (sq_nonneg u) h

/-- `|u| ≤ ρ` from `u² ≤ ρ²` (with `0 ≤ ρ`). -/
theorem abs_le_of_sq_le_sq {u ρ : ℝ} (hρ : 0 ≤ ρ) (h : u ^ 2 ≤ ρ ^ 2) : |u| ≤ ρ := by
  rw [← Real.sqrt_sq_eq_abs, show ρ = Real.sqrt (ρ ^ 2) from (Real.sqrt_sq hρ).symm]
  exact Real.sqrt_le_sqrt h

/-- The squared **Euclidean** norm of a chart coordinate `t : ℝ⁴`. -/
def sqNorm (t : ℝ × ℝ × ℝ × ℝ) : ℝ := t.1 ^ 2 + t.2.1 ^ 2 + t.2.2.1 ^ 2 + t.2.2.2 ^ 2

theorem sqNorm_nonneg (t : ℝ × ℝ × ℝ × ℝ) : 0 ≤ sqNorm t := by
  simp only [sqNorm]; positivity

theorem sqNorm_zero : sqNorm 0 = 0 := by simp [sqNorm]

/-- `‖·‖` (hence `sqNorm`) is invariant under the in-chart antipode `−id` (`chartNeg`). This is the
freeness input: `τ = −id` in-chart preserves the round balls/spheres. -/
theorem sqNorm_chartNeg (t : ℝ × ℝ × ℝ × ℝ) : sqNorm (chartNeg t) = sqNorm t := by
  simp only [sqNorm, chartNeg]; ring

theorem sqNorm_continuous : Continuous sqNorm := by unfold sqNorm; fun_prop

/-- The excision radius `ρ = 1/2`. Any `0 < ρ < π` with `2ρ ≤ 2` works: the 16 fixed points `{±1}⁴`
have minimum separation `2` (`fixedSet_dist_ge`) and `chartBall c ⊆ Metric.ball c ρ`, giving
pairwise-disjoint balls; `ρ < π` gives chart injectivity on the closed ball. -/
noncomputable def excisionRadius : ℝ := 1 / 2

theorem excisionRadius_pos : 0 < excisionRadius := by norm_num [excisionRadius]

/-- **Arc ≤ chord (per factor)**: `dist (c · exp s) c ≤ |s|` — the chart moves a point by at most the
arc length. (`‖exp(sI) − 1‖ ≤ |s|`, times the unit `‖c‖ = 1`.) -/
theorem circle_chartParam_dist_le (a : Circle) (s : ℝ) : dist (a * Circle.exp s) a ≤ |s| := by
  show dist ((↑(a * Circle.exp s) : ℂ)) (↑a) ≤ |s|
  rw [Complex.dist_eq, Circle.coe_mul, Circle.coe_exp]
  have hfac : (↑a : ℂ) * Complex.exp (↑s * Complex.I) - ↑a
      = ↑a * (Complex.exp (↑s * Complex.I) - 1) := by ring
  rw [hfac, norm_mul, Circle.norm_coe, one_mul, mul_comm (↑s : ℂ) Complex.I]
  calc ‖Complex.exp (Complex.I * ↑s) - 1‖ ≤ ‖s‖ := Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = |s| := Real.norm_eq_abs s

/-- **Per-factor chart injectivity on `[−1/2, 1/2]`**: `Circle.exp` is injective there (its period is
`2π > 1`), the input to the product chart injectivity. -/
theorem circle_exp_injOn_half {s s' : ℝ} (hs : |s| ≤ 1 / 2) (hs' : |s'| ≤ 1 / 2)
    (h : Circle.exp s = Circle.exp s') : s = s' := by
  have hc : Complex.exp (↑s * Complex.I) = Complex.exp (↑s' * Complex.I) := by
    rw [← Circle.coe_exp, ← Circle.coe_exp, h]
  rw [Complex.exp_eq_exp_iff_exists_int] at hc
  obtain ⟨n, hn⟩ := hc
  have hfac : (↑s : ℂ) * Complex.I = (↑s' + ↑n * (2 * ↑Real.pi)) * Complex.I := by rw [hn]; ring
  have hcC : (↑s : ℂ) = ↑s' + ↑n * (2 * ↑Real.pi) := mul_right_cancel₀ Complex.I_ne_zero hfac
  have hR : s = s' + (n : ℝ) * (2 * Real.pi) := by exact_mod_cast hcC
  have hpi : (2 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hdiff : |(n : ℝ) * (2 * Real.pi)| ≤ 1 := by
    have he : (n : ℝ) * (2 * Real.pi) = s - s' := by linarith [hR]
    rw [he]
    calc |s - s'| ≤ |s| + |s'| := abs_sub _ _
      _ ≤ 1 / 2 + 1 / 2 := by linarith [hs, hs']
      _ = 1 := by norm_num
  have hn0 : n = 0 := by
    by_contra hne
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have hz : (1 : ℤ) ≤ |n| := Int.one_le_abs (by exact_mod_cast hne)
      have hz' := (Int.cast_le (R := ℝ)).mpr hz
      rwa [Int.cast_abs, Int.cast_one] at hz'
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hdiff
    nlinarith [hdiff, h1, hpi]
  rw [hn0] at hR; simpa using hR

/-- **Product dist bound (open)**: `sqNorm t < ρ² ⟹ dist (centeredChartParam c t) c < ρ`. The sup-metric
distance is the max of the four per-factor arc-lengths, each `≤ |t.i| < ρ`. -/
theorem dist_centeredChartParam_lt (c : TorusFour) {t : ℝ × ℝ × ℝ × ℝ} {ρ : ℝ} (hρ : 0 < ρ)
    (h : sqNorm t < ρ ^ 2) : dist (centeredChartParam c t) c < ρ := by
  have b1 : |t.1| < ρ := abs_lt_of_sq_lt_sq hρ (by
    simp only [sqNorm] at h; nlinarith [sq_nonneg t.2.1, sq_nonneg t.2.2.1, sq_nonneg t.2.2.2])
  have b2 : |t.2.1| < ρ := abs_lt_of_sq_lt_sq hρ (by
    simp only [sqNorm] at h; nlinarith [sq_nonneg t.1, sq_nonneg t.2.2.1, sq_nonneg t.2.2.2])
  have b3 : |t.2.2.1| < ρ := abs_lt_of_sq_lt_sq hρ (by
    simp only [sqNorm] at h; nlinarith [sq_nonneg t.1, sq_nonneg t.2.1, sq_nonneg t.2.2.2])
  have b4 : |t.2.2.2| < ρ := abs_lt_of_sq_lt_sq hρ (by
    simp only [sqNorm] at h; nlinarith [sq_nonneg t.1, sq_nonneg t.2.1, sq_nonneg t.2.2.1])
  simp only [centeredChartParam, Prod.dist_eq]
  exact max_lt (lt_of_le_of_lt (circle_chartParam_dist_le _ _) b1)
    (max_lt (lt_of_le_of_lt (circle_chartParam_dist_le _ _) b2)
      (max_lt (lt_of_le_of_lt (circle_chartParam_dist_le _ _) b3)
        (lt_of_le_of_lt (circle_chartParam_dist_le _ _) b4)))

/-- **Product dist bound (closed)**: `sqNorm t ≤ ρ² ⟹ dist (centeredChartParam c t) c ≤ ρ`. -/
theorem dist_centeredChartParam_le (c : TorusFour) {t : ℝ × ℝ × ℝ × ℝ} {ρ : ℝ} (hρ : 0 ≤ ρ)
    (h : sqNorm t ≤ ρ ^ 2) : dist (centeredChartParam c t) c ≤ ρ := by
  have b1 : |t.1| ≤ ρ := abs_le_of_sq_le_sq hρ (by
    simp only [sqNorm] at h; nlinarith [sq_nonneg t.2.1, sq_nonneg t.2.2.1, sq_nonneg t.2.2.2])
  have b2 : |t.2.1| ≤ ρ := abs_le_of_sq_le_sq hρ (by
    simp only [sqNorm] at h; nlinarith [sq_nonneg t.1, sq_nonneg t.2.2.1, sq_nonneg t.2.2.2])
  have b3 : |t.2.2.1| ≤ ρ := abs_le_of_sq_le_sq hρ (by
    simp only [sqNorm] at h; nlinarith [sq_nonneg t.1, sq_nonneg t.2.1, sq_nonneg t.2.2.2])
  have b4 : |t.2.2.2| ≤ ρ := abs_le_of_sq_le_sq hρ (by
    simp only [sqNorm] at h; nlinarith [sq_nonneg t.1, sq_nonneg t.2.1, sq_nonneg t.2.2.1])
  simp only [centeredChartParam, Prod.dist_eq]
  exact max_le (le_trans (circle_chartParam_dist_le _ _) b1)
    (max_le (le_trans (circle_chartParam_dist_le _ _) b2)
      (max_le (le_trans (circle_chartParam_dist_le _ _) b3)
        (le_trans (circle_chartParam_dist_le _ _) b4)))

/-- **`centeredChartParam c` is continuous** — a product of `s ↦ c.i · Circle.exp s`, each a
composition of the continuous `Circle.exp` with left multiplication. -/
theorem continuous_centeredChartParam (c : TorusFour) : Continuous (centeredChartParam c) := by
  unfold centeredChartParam; fun_prop

/-- **`centeredChartParam c` is an open map** — it is `(left-translate) ∘ Circle.exp` per factor, and
`Circle.exp` is a covering map (`isLocalHomeomorph_circleExp`), hence open. This is what makes the round
`chartBall`/`chartSphere` genuine open/closed subsets of `T⁴` (so `T⁴°` is closed and compact). -/
theorem isOpenMap_centeredChartParam (c : TorusFour) : IsOpenMap (centeredChartParam c) := by
  have g : ∀ a : Circle, IsOpenMap (fun s : ℝ => a * Circle.exp s) :=
    fun a => (isOpenMap_mul_left a).comp isLocalHomeomorph_circleExp.isOpenMap
  have h : centeredChartParam c = Prod.map (fun s => c.1 * Circle.exp s)
      (Prod.map (fun s => c.2.1 * Circle.exp s)
        (Prod.map (fun s => c.2.2.1 * Circle.exp s) (fun s => c.2.2.2 * Circle.exp s))) := rfl
  rw [h]
  exact (g _).prodMap ((g _).prodMap ((g _).prodMap (g _)))

/-- **Product chart injectivity on the closed round ball `{sqNorm ≤ ρ²}` (`ρ = 1/2`).** Each coordinate
`|t.i| ≤ 1/2`, where `Circle.exp` is injective (`circle_exp_injOn_half`). Pins the boundary sphere off
the open ball (`sphere_subset_puncturedTorus`). -/
theorem centeredChartParam_injOn (c : TorusFour) :
    Set.InjOn (centeredChartParam c) {t | sqNorm t ≤ excisionRadius ^ 2} := by
  intro t ht t' ht' h
  rw [Set.mem_setOf_eq, show excisionRadius = (1 : ℝ) / 2 from rfl] at ht ht'
  have a1 : |t.1| ≤ 1 / 2 := abs_le_of_sq_le_sq (by norm_num) (by
    simp only [sqNorm] at ht; nlinarith [sq_nonneg t.2.1, sq_nonneg t.2.2.1, sq_nonneg t.2.2.2])
  have a2 : |t.2.1| ≤ 1 / 2 := abs_le_of_sq_le_sq (by norm_num) (by
    simp only [sqNorm] at ht; nlinarith [sq_nonneg t.1, sq_nonneg t.2.2.1, sq_nonneg t.2.2.2])
  have a3 : |t.2.2.1| ≤ 1 / 2 := abs_le_of_sq_le_sq (by norm_num) (by
    simp only [sqNorm] at ht; nlinarith [sq_nonneg t.1, sq_nonneg t.2.1, sq_nonneg t.2.2.2])
  have a4 : |t.2.2.2| ≤ 1 / 2 := abs_le_of_sq_le_sq (by norm_num) (by
    simp only [sqNorm] at ht; nlinarith [sq_nonneg t.1, sq_nonneg t.2.1, sq_nonneg t.2.2.1])
  have a1' : |t'.1| ≤ 1 / 2 := abs_le_of_sq_le_sq (by norm_num) (by
    simp only [sqNorm] at ht'; nlinarith [sq_nonneg t'.2.1, sq_nonneg t'.2.2.1, sq_nonneg t'.2.2.2])
  have a2' : |t'.2.1| ≤ 1 / 2 := abs_le_of_sq_le_sq (by norm_num) (by
    simp only [sqNorm] at ht'; nlinarith [sq_nonneg t'.1, sq_nonneg t'.2.2.1, sq_nonneg t'.2.2.2])
  have a3' : |t'.2.2.1| ≤ 1 / 2 := abs_le_of_sq_le_sq (by norm_num) (by
    simp only [sqNorm] at ht'; nlinarith [sq_nonneg t'.1, sq_nonneg t'.2.1, sq_nonneg t'.2.2.2])
  have a4' : |t'.2.2.2| ≤ 1 / 2 := abs_le_of_sq_le_sq (by norm_num) (by
    simp only [sqNorm] at ht'; nlinarith [sq_nonneg t'.1, sq_nonneg t'.2.1, sq_nonneg t'.2.2.1])
  simp only [centeredChartParam, Prod.mk.injEq] at h
  obtain ⟨e1, e2, e3, e4⟩ := h
  exact Prod.ext (circle_exp_injOn_half a1 a1' (mul_left_cancel e1))
    (Prod.ext (circle_exp_injOn_half a2 a2' (mul_left_cancel e2))
      (Prod.ext (circle_exp_injOn_half a3 a3' (mul_left_cancel e3))
        (circle_exp_injOn_half a4 a4' (mul_left_cancel e4))))

/-! ## K4′ — the round excised balls, the punctured torus, freeness -/

/-- **The `i`-th round excised open ball**: `centeredChartParam c '' {t : ℝ⁴ ∣ ‖t‖ < ρ}` — a round
Euclidean ball in the `τ = −id` centered chart at `c`, NOT a sup-metric box. -/
noncomputable def chartBall (c : TorusFour) : Set TorusFour :=
  centeredChartParam c '' {t | sqNorm t < excisionRadius ^ 2}

/-- **The `i`-th round boundary sphere**: `centeredChartParam c '' {t : ℝ⁴ ∣ ‖t‖ = ρ}` — a round `S³`
in the centered chart, on which `τ = −id` acts antipodally (`S³/±1 = ℝP³`, Design Risk #2). -/
noncomputable def chartSphere (c : TorusFour) : Set TorusFour :=
  centeredChartParam c '' {t | sqNorm t = excisionRadius ^ 2}

/-- **The 16 round excised open balls** (union over the 16 fixed points). -/
noncomputable def excisedBalls : Set TorusFour := ⋃ c ∈ fixedSet, chartBall c

/-- **The punctured torus `T⁴° := T⁴ ∖ (16 round balls)`** — the free locus of the `τ`-action. -/
noncomputable def puncturedTorus : Set TorusFour := (excisedBalls)ᶜ

/-- **A round ball sits inside the metric `ρ`-ball** (`dist(centeredChartParam c t, c) ≤ ‖t‖ < ρ`) — the
bridge that transports the metric fixed-point separation to round-ball disjointness. -/
theorem chartBall_subset_metricBall (c : TorusFour) :
    chartBall c ⊆ Metric.ball c excisionRadius := by
  rintro _ ⟨t, ht, rfl⟩
  rw [Metric.mem_ball]
  exact dist_centeredChartParam_lt c excisionRadius_pos ht

/-- A round ball sits inside the closed metric `ρ`-ball. -/
theorem chartBall_subset_metricClosedBall (c : TorusFour) :
    chartBall c ⊆ Metric.closedBall c excisionRadius := fun _ hx =>
  Metric.ball_subset_closedBall (chartBall_subset_metricBall c hx)

/-- A round boundary sphere sits inside the closed metric `ρ`-ball (`dist ≤ ‖t‖ = ρ`). -/
theorem chartSphere_subset_metricClosedBall (c : TorusFour) :
    chartSphere c ⊆ Metric.closedBall c excisionRadius := by
  rintro _ ⟨t, ht, rfl⟩
  rw [Metric.mem_closedBall]
  exact dist_centeredChartParam_le c excisionRadius_pos.le (le_of_eq ht)

/-- Each round ball is **open** (image of an open ball under the open map `centeredChartParam c`). -/
theorem isOpen_chartBall (c : TorusFour) : IsOpen (chartBall c) :=
  isOpenMap_centeredChartParam c _ (isOpen_lt sqNorm_continuous continuous_const)

/-- Each fixed point is the center of its round ball (`centeredChartParam c 0 = c`, `0 < ρ²`), hence
lies in the excised region. -/
theorem fixedSet_subset_excisedBalls : fixedSet ⊆ excisedBalls := fun c hc =>
  Set.mem_biUnion hc ⟨0, by
    rw [Set.mem_setOf_eq, sqNorm_zero, show excisionRadius = (1 : ℝ) / 2 from rfl]; norm_num,
    centeredChartParam_zero c⟩

/-- **Image-`τ`-invariance helper**: if `S ⊆ ℝ⁴` is `chartNeg`-invariant, then its `centeredChartParam`
image is `τ`-invariant (at a fixed center). Both `chartBall` and `chartSphere` invariance specialize. -/
theorem centeredChartParam_image_involution_mem {c : TorusFour}
    (hc : torusFourInvolution c = c) {S : Set (ℝ × ℝ × ℝ × ℝ)}
    (hS : ∀ t, chartNeg t ∈ S ↔ t ∈ S) (x : TorusFour) :
    torusFourInvolution x ∈ centeredChartParam c '' S ↔ x ∈ centeredChartParam c '' S := by
  constructor
  · rintro ⟨t, htS, ht⟩
    refine ⟨chartNeg t, (hS t).mpr htS, ?_⟩
    rw [← centeredChartParam_involution c hc t, ht]
    exact torusFourInvolution_involutive x
  · rintro ⟨t, htS, rfl⟩
    exact ⟨chartNeg t, (hS t).mpr htS, (centeredChartParam_involution c hc t).symm⟩

/-- **`τ`-invariance of a round ball** at a fixed center. -/
theorem chartBall_involution_mem_iff {c : TorusFour} (hc : torusFourInvolution c = c)
    (x : TorusFour) : torusFourInvolution x ∈ chartBall c ↔ x ∈ chartBall c :=
  centeredChartParam_image_involution_mem hc
    (fun t => by simp only [Set.mem_setOf_eq, sqNorm_chartNeg]) x

/-- **`τ`-invariance of the excised region** (union of round fixed-point balls). -/
theorem excisedBalls_involution_mem_iff (x : TorusFour) :
    torusFourInvolution x ∈ excisedBalls ↔ x ∈ excisedBalls := by
  simp only [excisedBalls, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨c, hc, hx⟩; exact ⟨c, hc, (chartBall_involution_mem_iff hc x).mp hx⟩
  · rintro ⟨c, hc, hx⟩; exact ⟨c, hc, (chartBall_involution_mem_iff hc x).mpr hx⟩

/-- **`τ`-invariance of the punctured torus**. -/
theorem puncturedTorus_involution_mem_iff (x : TorusFour) :
    torusFourInvolution x ∈ puncturedTorus ↔ x ∈ puncturedTorus := by
  simp only [puncturedTorus, Set.mem_compl_iff, excisedBalls_involution_mem_iff]

/-- `τ` maps `T⁴°` into `T⁴°`. -/
theorem involution_mapsTo_puncturedTorus :
    Set.MapsTo torusFourInvolution puncturedTorus puncturedTorus :=
  fun _ hx => (puncturedTorus_involution_mem_iff _).mpr hx

/-- **`τ` acts FREELY on `T⁴°`** — no fixed point survives excision (`Fix(τ) ⊆ excisedBalls`). This is
the K4′ freeness that lets K5′ form the quotient as an honest smooth manifold-with-boundary. -/
theorem involution_free_on_puncturedTorus :
    ∀ x ∈ puncturedTorus, torusFourInvolution x ≠ x := by
  intro x hx hfix
  exact hx (fixedSet_subset_excisedBalls hfix)

/-- **`τ` restricts to a (free) involution of `T⁴°`** — a bijection of the punctured torus onto itself. -/
theorem involution_bijOn_puncturedTorus :
    Set.BijOn torusFourInvolution puncturedTorus puncturedTorus :=
  ⟨involution_mapsTo_puncturedTorus,
    torusFourInvolution_involutive.injective.injOn,
    fun x hx => ⟨torusFourInvolution x, involution_mapsTo_puncturedTorus hx,
      torusFourInvolution_involutive x⟩⟩

/-! ## K4′ — pairwise disjointness of the round balls -/

/-- **The metric `1/2`-balls at the fixed points are pairwise disjoint** (`1/2 + 1/2 = 1 ≤ 2 ≤
dist c1 c2`). The round balls sit inside these (`chartBall_subset_metricBall`), so inherit disjointness. -/
theorem metricBall_disjoint {c1 c2 : TorusFour} (h1 : c1 ∈ fixedSet) (h2 : c2 ∈ fixedSet)
    (hne : c1 ≠ c2) :
    Disjoint (Metric.ball c1 excisionRadius) (Metric.ball c2 excisionRadius) := by
  apply Metric.ball_disjoint_ball
  calc excisionRadius + excisionRadius = 1 := by norm_num [excisionRadius]
    _ ≤ 2 := by norm_num
    _ ≤ dist c1 c2 := fixedSet_dist_ge h1 h2 hne

/-- **Two distinct round excised balls are disjoint** (each inside its metric `1/2`-ball). -/
theorem chartBall_disjoint {c1 c2 : TorusFour} (h1 : c1 ∈ fixedSet) (h2 : c2 ∈ fixedSet)
    (hne : c1 ≠ c2) : Disjoint (chartBall c1) (chartBall c2) :=
  (metricBall_disjoint h1 h2 hne).mono (chartBall_subset_metricBall c1)
    (chartBall_subset_metricBall c2)

/-- **The 16 round excised balls are a pairwise-disjoint family indexed by the fixed points.** -/
theorem excisedBalls_pairwiseDisjoint :
    fixedSet.PairwiseDisjoint (fun c => chartBall c) :=
  fun _ h1 _ h2 hne => chartBall_disjoint h1 h2 hne

/-! ## K4′ — the boundary spheres (round `S³/±1` presentation, Design Risk #2) -/

/-- **The round boundary spheres lie in `T⁴°`**: `chartSphere c ⊆ T⁴°`. A boundary point `x` is at
distance `≤ 1/2` from its own center `c` (so `≥ 3/2` from every OTHER fixed point, hence outside their
balls) and — by chart injectivity on the closed ball — is NOT in `c`'s own open ball. -/
theorem sphere_subset_puncturedTorus {c : TorusFour} (hc : c ∈ fixedSet) :
    chartSphere c ⊆ puncturedTorus := by
  rintro _ ⟨t, ht, rfl⟩
  rw [Set.mem_setOf_eq] at ht
  rw [puncturedTorus, Set.mem_compl_iff, excisedBalls, Set.mem_iUnion₂]
  rintro ⟨c', hc', hxc'⟩
  by_cases hcc : c' = c
  · rw [hcc] at hxc'
    obtain ⟨s, hs, hcs⟩ := hxc'
    rw [Set.mem_setOf_eq] at hs
    have hsmem : s ∈ {t | sqNorm t ≤ excisionRadius ^ 2} := by
      rw [Set.mem_setOf_eq]; exact le_of_lt hs
    have htmem : t ∈ {t | sqNorm t ≤ excisionRadius ^ 2} := by
      rw [Set.mem_setOf_eq]; exact le_of_eq ht
    have hst : s = t := centeredChartParam_injOn c hsmem htmem hcs
    rw [hst, ht] at hs
    exact lt_irrefl _ hs
  · have hxc'ball : dist (centeredChartParam c t) c' < excisionRadius := by
      rw [← Metric.mem_ball]; exact chartBall_subset_metricBall c' hxc'
    have hmemsph : centeredChartParam c t ∈ chartSphere c :=
      ⟨t, by rw [Set.mem_setOf_eq]; exact ht, rfl⟩
    have hxcball : dist (centeredChartParam c t) c ≤ excisionRadius := by
      rw [← Metric.mem_closedBall]; exact chartSphere_subset_metricClosedBall c hmemsph
    have hsep : (2 : ℝ) ≤ dist c c' := fixedSet_dist_ge hc hc' (fun h => hcc h.symm)
    have htri : dist c c' ≤ dist c (centeredChartParam c t) + dist (centeredChartParam c t) c' :=
      dist_triangle _ _ _
    rw [dist_comm c (centeredChartParam c t)] at htri
    rw [show excisionRadius = (1 : ℝ) / 2 from rfl] at hxc'ball hxcball
    linarith

/-- **`τ`-invariance of a round boundary sphere** at a fixed center (in-chart `τ = −id` preserves
`‖t‖ = ρ`). -/
theorem chartSphere_involution_invariant {c : TorusFour} (hc : torusFourInvolution c = c)
    (x : TorusFour) : torusFourInvolution x ∈ chartSphere c ↔ x ∈ chartSphere c :=
  centeredChartParam_image_involution_mem hc
    (fun t => by simp only [Set.mem_setOf_eq, sqNorm_chartNeg]) x

end SKEFTHawking.KummerPuncturedTorus
