/-
# Phase 5q.H — the Kummer K3 generator, K4′ (Route B): the punctured torus `T⁴°`

Continues `KummerInvolution.lean` (K2 = the involution `τ(w) = w⁻¹`, K3 = its 16 fixed points
`{±1}⁴`, both PROVEN there). Read `KummerK3Base.lean` §A first (the whole Kummer brick sequence) and
the **binding Route-B design doc** `docs/dev-loops/Phase5qH/KUMMER_K4K10_DESIGN.md`: the singular
orbifold quotient is NEVER formed — instead we **excise first, quotient free, weld bundles**. This
module ships the **K4′** brick (Wave K-I) plus the residual K2/K3 packaging that K4′–K6′ consume,
UNCONDITIONALLY (kernel-pure `{propext, Classical.choice, Quot.sound}`; no
`sorry`/`native_decide`/`maxHeartbeats`/axiom).

**K2 packaging (extension).** `τ` as a **homeomorphism** (`torusFourInvolutionHomeo`) and a
**`C^ω` diffeomorphism** (`torusFourInvolutionDiffeo`) of `T⁴` — the group inverse of the compact
abelian Lie group `T⁴`, self-inverse and smooth both ways. These give the structure-preserving self-map
K5′ needs to descend `τ` to the free quotient.

**K3 packaging (extension).** The 16 fixed points as an explicit **`Fintype`** with
**`Fintype.card = 16`** (`torusFourInvolution_fixedPoints_fintypeCard`, from the banked
`Nat.card = 16`), an explicit **`Finset`** (`fixedFinset`, card 16, decidable membership), and the
coordinatewise membership certificate `mem_fixedSet_iff` (`x` fixed ⟺ each coordinate `∈ {1, negOne}`).

**K4′ — the punctured torus (the brick).**
- **Equivariant charts (`τ = −id` in-chart).** In the exp-centered chart at a 2-torsion point `c`
  (`c⁻¹ = c`), inversion is negation: `τ (c · exp t) = c · exp (−t)` (`circle_chart_involution`
  per factor, `centeredChartParam_involution` on `T⁴`). This is the `τ = −id` fact that makes `T⁴/τ`
  locally `ℝ⁴/±1 = cone(ℝP³)` at each fixed point (consumed by K5′/K6′a).
- **16 disjoint open `τ`-invariant balls.** `excisedBalls = ⋃ c ∈ Fix(τ), ball c (1/2)`. `τ` is an
  **isometry** of `T⁴` (`torusFourInvolution_isometry`), each ball is centered at a fixed point hence
  `τ`-invariant (`ball_involution_mem_iff`); the 16 fixed points are the subgroup `{±1}⁴` with explicit
  minimum separation `dist ≥ 2` (`fixedSet_dist_ge`), so the radius-`1/2` balls are pairwise disjoint
  (`excisedBalls_pairwiseDisjoint`, via `Metric.ball_disjoint_ball`).
- **`T⁴° := T⁴ ∖ excisedBalls`** (`puncturedTorus`), `τ`-invariant (`puncturedTorus_involution_mem_iff`),
  with `τ` restricting to a **free** involution there (`involution_free_on_puncturedTorus`,
  `involution_bijOn_puncturedTorus`) — freeness is immediate: `Fix(τ) ⊆ excisedBalls`.
- **Boundary spheres — S³/±1 PRESENTATION (Design Risk #2, BINDING).** `∂B_i = sphere c (1/2) ≅ S³`
  lies in `T⁴°` (`sphere_subset_puncturedTorus`) and is `τ`-invariant (`sphere_involution_invariant`);
  `τ` is free on it. **The downstream `ℝP³` boundary of the free quotient MUST be presented as the
  antipodal quotient `∂B_i / τ = S³/±1`** (in the centered chart `τ = −id`, so on the sphere `‖t‖ = r`
  it is the antipodal map). K5′ and K6′a must both use this S³/±1 presentation (seam-match).

**Honest residual (the STRETCH, NOT shipped here).** Packaging `T⁴°` as a smooth
*manifold-with-boundary* (`∂ = 16 × S³`) via the surgery-foundation excision/chart stack is the deep
half of K4′; Mathlib has no "closed-ball complement is a manifold-with-boundary" lemma and the
project's excision machinery must be threaded through. This module ships `T⁴°` as a `τ`-invariant
subspace with the full free-action data (charts, disjoint invariant balls, freeness, invariant
boundary spheres); the `IsManifold`/`∂ = 16 × S³` certificate is the residual for the K4′ follow-up.
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

/-! ## K4′ — the excised balls, the punctured torus, freeness -/

/-- The excision radius `r = 1/2`. Any `0 < r < 1` works: the 16 fixed points `{±1}⁴` have minimum
separation `2` (`fixedSet_dist_ge`), so `2r = 1 < 2` gives pairwise-disjoint balls. -/
noncomputable def excisionRadius : ℝ := 1 / 2

theorem excisionRadius_pos : 0 < excisionRadius := by norm_num [excisionRadius]

/-- **The 16 excised open balls**: one radius-`1/2` ball around each of the 16 fixed points. -/
noncomputable def excisedBalls : Set TorusFour := ⋃ c ∈ fixedSet, Metric.ball c excisionRadius

/-- **The punctured torus `T⁴° := T⁴ ∖ (16 open balls)`** — the free locus of the `τ`-action. -/
noncomputable def puncturedTorus : Set TorusFour := (excisedBalls)ᶜ

/-- Each fixed point is the center of its excised ball, hence lies in the excised region. -/
theorem fixedSet_subset_excisedBalls : fixedSet ⊆ excisedBalls := fun _ hc =>
  Set.mem_biUnion hc (Metric.mem_ball_self excisionRadius_pos)

/-- **`τ`-invariance of a fixed-point ball**: `τ x ∈ ball c r ⟺ x ∈ ball c r` when `τ c = c`. -/
theorem ball_involution_mem_iff {c : TorusFour} (hc : torusFourInvolution c = c) (x : TorusFour) :
    torusFourInvolution x ∈ Metric.ball c excisionRadius ↔ x ∈ Metric.ball c excisionRadius := by
  simp only [Metric.mem_ball, dist_involution_fixed hc]

/-- **`τ`-invariance of the excised region** (union of fixed-point balls). -/
theorem excisedBalls_involution_mem_iff (x : TorusFour) :
    torusFourInvolution x ∈ excisedBalls ↔ x ∈ excisedBalls := by
  simp only [excisedBalls, Set.mem_iUnion, exists_prop]
  constructor
  · rintro ⟨c, hc, hx⟩; exact ⟨c, hc, (ball_involution_mem_iff hc x).mp hx⟩
  · rintro ⟨c, hc, hx⟩; exact ⟨c, hc, (ball_involution_mem_iff hc x).mpr hx⟩

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

/-! ## K4′ — minimum separation of the 16 fixed points, disjointness of the balls -/

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

/-- **The excised balls are pairwise disjoint** (`Metric.ball_disjoint_ball`: `1/2 + 1/2 = 1 ≤ 2 ≤
dist c1 c2`). -/
theorem excisedBalls_ball_disjoint {c1 c2 : TorusFour} (h1 : c1 ∈ fixedSet) (h2 : c2 ∈ fixedSet)
    (hne : c1 ≠ c2) :
    Disjoint (Metric.ball c1 excisionRadius) (Metric.ball c2 excisionRadius) := by
  apply Metric.ball_disjoint_ball
  calc excisionRadius + excisionRadius = 1 := by norm_num [excisionRadius]
    _ ≤ 2 := by norm_num
    _ ≤ dist c1 c2 := fixedSet_dist_ge h1 h2 hne

/-- **The 16 excised balls are a pairwise-disjoint family indexed by the fixed points.** -/
theorem excisedBalls_pairwiseDisjoint :
    fixedSet.PairwiseDisjoint (fun c => Metric.ball c excisionRadius) :=
  fun _ h1 _ h2 hne => excisedBalls_ball_disjoint h1 h2 hne

/-! ## K4′ — the boundary spheres (S³/±1 presentation, Design Risk #2) -/

/-- **The boundary spheres lie in `T⁴°`**: `∂B_i = sphere c (1/2) ⊆ T⁴°`. (A point at distance `1/2`
from a fixed point `c` is `≥ 3/2` from every other fixed point, hence outside every excised ball.) -/
theorem sphere_subset_puncturedTorus {c : TorusFour} (hc : c ∈ fixedSet) :
    Metric.sphere c excisionRadius ⊆ puncturedTorus := by
  intro x hx
  rw [Metric.mem_sphere] at hx
  rw [puncturedTorus, Set.mem_compl_iff, excisedBalls, Set.mem_iUnion₂]
  rintro ⟨c', hc', hxc'⟩
  rw [Metric.mem_ball] at hxc'
  by_cases hcc : c' = c
  · subst hcc; rw [hx] at hxc'; exact absurd hxc' (lt_irrefl _)
  · have hsep : (2 : ℝ) ≤ dist c c' := fixedSet_dist_ge hc hc' (fun h => hcc h.symm)
    have htri : dist c c' ≤ dist c x + dist x c' := dist_triangle c x c'
    rw [dist_comm c x, hx] at htri
    rw [show excisionRadius = (1 : ℝ) / 2 from rfl] at htri hxc'
    linarith

/-- **`τ`-invariance of a boundary sphere** at a fixed center. -/
theorem sphere_involution_invariant {c : TorusFour} (hc : torusFourInvolution c = c) (x : TorusFour) :
    torusFourInvolution x ∈ Metric.sphere c excisionRadius ↔
      x ∈ Metric.sphere c excisionRadius := by
  simp only [Metric.mem_sphere, dist_involution_fixed hc]

/-! ## K4′ — the equivariant centered charts (`τ = −id` in chart) -/

/-- **Per-factor equivariant chart**: on the circle, in the exp-chart centered at a square-root of
unity `c` (`c⁻¹ = c`), inversion is negation of the chart parameter — `(c · exp t)⁻¹ = c · exp (−t)`.
The local model that makes `S¹/τ` a half-circle with an `ℝP⁰`-type end, and `T⁴/τ` locally `cone(ℝP³)`. -/
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

end SKEFTHawking.KummerPuncturedTorus
