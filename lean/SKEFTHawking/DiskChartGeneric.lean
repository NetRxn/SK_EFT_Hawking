/-
# Phase 5q.H W-D — SURGERY WAVE 7: THE DIMENSION-GENERIC CLOSED-BALL ATLAS (D⁵ for the KT handle)

Wave 6 (`SingularSurgeryChartsConcrete.lean`) bottomed the Pin⁺ surgery-trace consumer at four named
inputs; the largest is the handle end `Ha` with an `H'`-atlas, where
`H' = KTModel = ModelProd (EuclideanSpace ℝ (Fin 4)) (EuclideanHalfSpace 1)`. The header's design of
record chose `Ha = D⁵` (a 2-handle of the 5-dimensional trace is a 5-ball abstractly): the closed
5-ball built with the same collar atlas as `DiskChart`'s `D³` is modelled on
`(𝓡 4).prod (𝓡∂ 1)` — model space **exactly `KTModel`, a single boundary face, NO corner**.

This module ships the **dimension-generic** closed-ball charted space — the direct `n`-dimensional
analogue of `DiskChart`/`DiskManifold`'s `D³` construction — and instantiates it at `n = 4` to deliver
`instChartedSpaceKTModelD5 : ChartedSpace KTModel D⁵`, the exact typeclass input wave 6's constructors
consume.

## Why generic (not a bespoke replay)

Mathlib provides a **global** instance
`ChartedSpace (EuclideanSpace ℝ (Fin n)) (sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1)`
(`Mathlib/Geometry/Manifold/Instances/Sphere.lean`, no `Fact` requirement — the finrank fact is
supplied internally). So the polar collar chart's stereographic factor resolves for an **arbitrary**
`n` with zero `Fact`-threading. Every other piece of the `D³` construction (radial clamp, direction
map, the `Eⁿ × ℝ ≅ E^{n+1}` coordinate iso) is dimension-agnostic. The whole atlas therefore
generalises verbatim; `D⁵ = NDisk 4` is a cheap instantiation, and every future `D^k` handle reuses
this module.

## What lands GREEN here

* `NDisk n` / `NSphere n` — the closed unit `(n+1)`-ball and unit `n`-sphere in `E^{n+1}`.
* `ballClamp` / `diskDir` / `assemble` / `splitLo` — the generic radial primitives.
* `diskInteriorChart n` / `diskCollarChart n u₀` — the interior + polar collar charts.
* `instChartedSpaceNDisk n : ChartedSpace (ModelProd (Eⁿ) (EuclideanHalfSpace 1)) (NDisk n)`.
* `D5` / `instChartedSpaceKTModelD5 : ChartedSpace KTModel D⁵` — the `n = 4` instantiation.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/
`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularSurgeryChartsConcrete

open Metric Set
open scoped Manifold

namespace SKEFTHawking.DiskChartGeneric

noncomputable section

variable (n : ℕ)

/-! ### §0. The generic closed ball and sphere -/

/-- **The closed unit `(n+1)`-ball** `D^{n+1} = closedBall(0,1) ⊆ E^{n+1}`. -/
abbrev NDisk : Type := closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-- **The unit `n`-sphere** `S^n = sphere(0,1) ⊆ E^{n+1}` — Mathlib's charted space on `Eⁿ`. -/
abbrev NSphere : Type := sphere (0 : EuclideanSpace ℝ (Fin (n + 1))) 1

/-! ### §1. The radial clamp onto the closed unit ball -/

/-- **The radial clamp onto the closed unit ball**: the identity on `D^{n+1}`, radial projection
outside — a closed-form total section of the inclusion `D^{n+1} ⊆ E^{n+1}`. -/
def ballClamp (w : EuclideanSpace ℝ (Fin (n + 1))) : NDisk n :=
  ⟨(max 1 ‖w‖)⁻¹ • w, by
    rw [mem_closedBall_zero_iff, norm_smul, norm_inv, Real.norm_eq_abs,
      abs_of_pos (lt_of_lt_of_le one_pos (le_max_left _ _))]
    exact inv_mul_le_one_of_le₀ (le_max_right _ _) (le_of_lt (lt_of_lt_of_le one_pos
      (le_max_left _ _)))⟩

theorem continuous_ballClamp : Continuous (ballClamp n) := by
  apply Continuous.subtype_mk
  exact ((continuous_const.max continuous_norm).inv₀
    (fun w => ne_of_gt (lt_of_lt_of_le one_pos (le_max_left _ _)))).smul continuous_id

/-- The clamp is the identity on the closed ball. -/
theorem ballClamp_coe_of_norm_le {n : ℕ} {w : EuclideanSpace ℝ (Fin (n + 1))} (h : ‖w‖ ≤ 1) :
    (ballClamp n w : EuclideanSpace ℝ (Fin (n + 1))) = w := by
  simp [ballClamp, max_eq_left h]

/-! ### §2. The direction map `D^{n+1}∖{0} → Sⁿ` -/

/-- **The direction of a disk point** (junk value at the centre): `v/‖v‖ ∈ Sⁿ` for `v ≠ 0`. -/
def diskDir (v : NDisk n) : NSphere n :=
  if h : (v : EuclideanSpace ℝ (Fin (n + 1))) = 0 then
    ⟨EuclideanSpace.single 0 1, by simp⟩
  else
    ⟨‖(v : EuclideanSpace ℝ (Fin (n + 1)))‖⁻¹ • (v : EuclideanSpace ℝ (Fin (n + 1))), by
      rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm]
      exact inv_mul_cancel₀ (norm_ne_zero_iff.mpr h)⟩

theorem diskDir_coe {n : ℕ} {v : NDisk n} (h : (v : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0) :
    (diskDir n v : EuclideanSpace ℝ (Fin (n + 1)))
      = ‖(v : EuclideanSpace ℝ (Fin (n + 1)))‖⁻¹ • (v : EuclideanSpace ℝ (Fin (n + 1))) := by
  rw [diskDir, dif_neg h]

/-- The direction of a positive multiple of a unit vector is that vector. -/
theorem diskDir_smul_unit {n : ℕ} {u : NSphere n} {r : ℝ} (hr : 0 < r) (hr1 : r ≤ 1) :
    diskDir n ⟨r • (u : EuclideanSpace ℝ (Fin (n + 1))), by
      rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs, abs_of_pos hr,
        mem_sphere_zero_iff_norm.mp u.2, mul_one]
      exact hr1⟩ = u := by
  have hu : ‖(u : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
  have hne : r • (u : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0 := by
    rw [smul_ne_zero_iff]
    exact ⟨ne_of_gt hr, fun h0 => by simp [h0] at hu⟩
  apply Subtype.ext
  rw [diskDir_coe hne]
  show ‖r • (u : EuclideanSpace ℝ (Fin (n + 1)))‖⁻¹ • (r • (u : EuclideanSpace ℝ (Fin (n + 1))))
    = (u : EuclideanSpace ℝ (Fin (n + 1)))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, hu, mul_one, smul_smul,
    inv_mul_cancel₀ (ne_of_gt hr), one_smul]

/-- `diskDir` is continuous away from the centre. -/
theorem continuousOn_diskDir :
    ContinuousOn (diskDir n) {v : NDisk n | (v : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0} := by
  rw [continuousOn_iff_continuous_restrict]
  apply Continuous.subtype_mk
  have hcont : Continuous fun v : {v : NDisk n | (v : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0} =>
      ((v.1 : NDisk n) : EuclideanSpace ℝ (Fin (n + 1))) :=
    continuous_subtype_val.comp continuous_subtype_val
  have h : Continuous fun v : {v : NDisk n | (v : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0} =>
      (‖((v.1 : NDisk n) : EuclideanSpace ℝ (Fin (n + 1)))‖⁻¹ •
        ((v.1 : NDisk n) : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin (n + 1))) :=
    (hcont.norm.inv₀ (fun v => norm_ne_zero_iff.mpr v.2)).smul hcont
  exact h.congr (fun v => (diskDir_coe v.2).symm)

/-! ### §3. The `Eⁿ × ℝ ≅ E^{n+1}` coordinate iso -/

/-- **Assemble** an `Eⁿ` block and a last coordinate into `E^{n+1}` (`Fin.snoc` under `WithLp.toLp`). -/
def assemble (a : EuclideanSpace ℝ (Fin n)) (s : ℝ) : EuclideanSpace ℝ (Fin (n + 1)) :=
  WithLp.toLp 2 (Fin.snoc (fun i => a.ofLp i) s)

@[simp] theorem assemble_ofLp (a : EuclideanSpace ℝ (Fin n)) (s : ℝ) (i : Fin (n + 1)) :
    (assemble n a s).ofLp i = (Fin.snoc (fun j => a.ofLp j) s : Fin (n + 1) → ℝ) i := rfl

theorem continuous_assemble :
    Continuous fun p : EuclideanSpace ℝ (Fin n) × ℝ => assemble n p.1 p.2 := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · simpa using continuous_snd
  -- v4.32: `simp` no longer unfolds `Function.comp`, so the `∘`-shaped term never reaches the
  -- goal's lambda form. `Function.comp_def` does it.
  · simpa [Function.comp_def] using
      ((PiLp.continuous_apply 2 (fun _ : Fin n => ℝ) j).comp continuous_fst)

/-- **Split** the first `n` coordinates of `E^{n+1}` into `Eⁿ`. -/
def splitLo (w : EuclideanSpace ℝ (Fin (n + 1))) : EuclideanSpace ℝ (Fin n) :=
  WithLp.toLp 2 (fun i => w.ofLp i.castSucc)

@[simp] theorem splitLo_ofLp (w : EuclideanSpace ℝ (Fin (n + 1))) (i : Fin n) :
    (splitLo n w).ofLp i = w.ofLp i.castSucc := rfl

theorem continuous_splitLo : Continuous (splitLo n) := by
  apply (PiLp.continuous_toLp 2 _).comp
  exact continuous_pi fun i => PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) i.castSucc

/-- The last coordinate of `assemble a s` is `s`. -/
@[simp] theorem assemble_ofLp_last (a : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
    (assemble n a s).ofLp (Fin.last n) = s := by
  rw [assemble_ofLp]; exact Fin.snoc_last _ _

/-- The lower coordinates of `assemble a s` are those of `a`. -/
@[simp] theorem assemble_ofLp_castSucc (a : EuclideanSpace ℝ (Fin n)) (s : ℝ) (j : Fin n) :
    (assemble n a s).ofLp j.castSucc = a.ofLp j := by
  rw [assemble_ofLp]; exact Fin.snoc_castSucc _ _ _

/-! ### §4. Round-trip lemmas for the coordinate iso -/

/-- `splitLo` is a left inverse of `assemble` in the first block. -/
theorem splitLo_assemble (a : EuclideanSpace ℝ (Fin n)) (s : ℝ) :
    splitLo n (assemble n a s) = a := by
  apply WithLp.ofLp_injective
  funext i
  rw [splitLo_ofLp, assemble_ofLp_castSucc]

/-- The full reconstruction: reassembling the low block and the last coordinate recovers `v`. -/
theorem assemble_splitLo (v : EuclideanSpace ℝ (Fin (n + 1))) :
    assemble n (splitLo n v) (v.ofLp (Fin.last n)) = v := by
  apply WithLp.ofLp_injective
  funext i
  refine Fin.lastCases ?_ (fun j => ?_) i
  · rw [assemble_ofLp_last]
  · rw [assemble_ofLp_castSucc, splitLo_ofLp]

/-- Half-space membership for the interior chart's target coordinate: for `v ∈ D^{n+1}` the translated
last coordinate `vₙ + 2` is nonnegative (indeed `≥ 1`). -/
theorem interior_last_add_two_nonneg (v : NDisk n) :
    (0 : ℝ) ≤ (v : EuclideanSpace ℝ (Fin (n + 1))).ofLp (Fin.last n) + 2 := by
  have h1 : ‖(v : EuclideanSpace ℝ (Fin (n + 1)))‖ ≤ 1 := mem_closedBall_zero_iff.mp v.2
  have h2 : ‖(v : EuclideanSpace ℝ (Fin (n + 1))).ofLp (Fin.last n)‖
      ≤ ‖(v : EuclideanSpace ℝ (Fin (n + 1)))‖ := PiLp.norm_apply_le _ _
  rw [Real.norm_eq_abs] at h2
  have h3 := (abs_le.mp (h2.trans h1)).1
  linarith

/-- On `E¹`, reassembling the single coordinate recovers the vector. -/
theorem toLp_ofLp_fin_one (x : EuclideanSpace ℝ (Fin 1)) :
    WithLp.toLp 2 (fun _ : Fin 1 => x.ofLp 0) = x := by
  apply WithLp.ofLp_injective
  funext i
  rw [Subsingleton.elim i 0]

/-! ### §5. The interior chart -/

/-- **The interior chart** of `D^{n+1}`: on the open ball `{‖v‖ < 1}`, the coordinate translation
`v ↦ (splitLo v, vₙ + 2)` landing in the interior of the half-space model. -/
def diskInteriorChart :
    OpenPartialHomeomorph (NDisk n)
      (ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace 1)) where
  source := {z : NDisk n | ‖(z : EuclideanSpace ℝ (Fin (n + 1)))‖ < 1}
  target := {p : ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace 1) |
    ‖assemble n p.1 ((p.2.val).ofLp 0 - 2)‖ < 1}
  toFun v := (splitLo n (v : EuclideanSpace ℝ (Fin (n + 1))),
    ⟨WithLp.toLp 2 (fun _ : Fin 1 => (v : EuclideanSpace ℝ (Fin (n + 1))).ofLp (Fin.last n) + 2),
      interior_last_add_two_nonneg n v⟩)
  invFun p := ballClamp n (assemble n p.1 ((p.2.val).ofLp 0 - 2))
  map_source' := by
    intro x hx
    change ‖assemble n (splitLo n (↑x : EuclideanSpace ℝ (Fin (n + 1))))
      ((↑x : EuclideanSpace ℝ (Fin (n + 1))).ofLp (Fin.last n) + 2 - 2)‖ < 1
    rw [add_sub_cancel_right, assemble_splitLo]
    exact hx
  map_target' := by
    intro p hp
    simp only [mem_setOf_eq] at hp ⊢
    rw [ballClamp_coe_of_norm_le (le_of_lt hp)]
    exact hp
  left_inv' := by
    intro x hx
    apply Subtype.ext
    show (↑(ballClamp n (assemble n (splitLo n (↑x : EuclideanSpace ℝ (Fin (n + 1))))
      ((↑x : EuclideanSpace ℝ (Fin (n + 1))).ofLp (Fin.last n) + 2 - 2))) :
        EuclideanSpace ℝ (Fin (n + 1)))
        = (↑x : EuclideanSpace ℝ (Fin (n + 1)))
    rw [add_sub_cancel_right, assemble_splitLo]
    exact ballClamp_coe_of_norm_le (le_of_lt hx)
  right_inv' := by
    intro p hp
    have hw : (↑(ballClamp n (assemble n p.1 (p.2.val.ofLp 0 - 2))) :
        EuclideanSpace ℝ (Fin (n + 1)))
        = assemble n p.1 (p.2.val.ofLp 0 - 2) :=
      ballClamp_coe_of_norm_le (le_of_lt hp)
    refine Prod.ext ?_ ?_
    · show splitLo n (↑(ballClamp n (assemble n p.1 (p.2.val.ofLp 0 - 2))) :
        EuclideanSpace ℝ (Fin (n + 1))) = p.1
      rw [hw, splitLo_assemble]
    · apply Subtype.ext
      show WithLp.toLp 2 (fun _ : Fin 1 =>
        (↑(ballClamp n (assemble n p.1 (p.2.val.ofLp 0 - 2))) :
          EuclideanSpace ℝ (Fin (n + 1))).ofLp (Fin.last n) + 2)
          = p.2.val
      rw [hw, assemble_ofLp_last, sub_add_cancel]
      exact toLp_ofLp_fin_one _
  open_source := isOpen_lt (by fun_prop) continuous_const
  open_target := by
    apply isOpen_lt _ continuous_const
    refine Continuous.norm (continuous_assemble n |>.comp (Continuous.prodMk continuous_fst ?_))
    exact ((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp
      (continuous_subtype_val.comp continuous_snd)).sub continuous_const
  continuousOn_toFun := by
    apply Continuous.continuousOn
    apply Continuous.prodMk
    · exact continuous_splitLo n |>.comp continuous_subtype_val
    · apply Continuous.subtype_mk
      apply (PiLp.continuous_toLp 2 _).comp
      apply continuous_pi
      intro _
      exact ((PiLp.continuous_apply 2 (fun _ : Fin (n + 1) => ℝ) (Fin.last n)).comp
        continuous_subtype_val).add continuous_const
  continuousOn_invFun := by
    apply Continuous.continuousOn
    refine continuous_ballClamp n |>.comp
      (continuous_assemble n |>.comp (Continuous.prodMk continuous_fst ?_))
    exact ((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp
      (continuous_subtype_val.comp continuous_snd)).sub continuous_const

/-! ### §6. The polar collar chart family -/

/-- Half-space membership for the collar chart's target coordinate: for `v ∈ D^{n+1}` the collar
coordinate `1 − ‖v‖` is nonnegative (it is `0` exactly on the boundary sphere). -/
theorem collar_one_sub_norm_nonneg (v : NDisk n) :
    (0 : ℝ) ≤ 1 - ‖(↑v : EuclideanSpace ℝ (Fin (n + 1)))‖ := by
  have := mem_closedBall_zero_iff.mp v.2
  linarith

/-- The collar chart's inverse lands in the closed ball: `max 0 (1−t) • u` (with `u ∈ Sⁿ`, `t ≥ 0`)
has norm `max 0 (1−t) ≤ 1`. -/
theorem collar_invFun_mem (u₀ : NSphere n)
    (p : ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace 1)) :
    (max 0 (1 - p.2.val.ofLp 0) •
      ((chartAt (EuclideanSpace ℝ (Fin n)) u₀).symm p.1 : EuclideanSpace ℝ (Fin (n + 1))))
      ∈ closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1 := by
  rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
    mem_sphere_zero_iff_norm.mp ((chartAt (EuclideanSpace ℝ (Fin n)) u₀).symm p.1).2, mul_one,
    abs_of_nonneg (le_max_left _ _)]
  have ht : (0 : ℝ) ≤ p.2.val.ofLp 0 := p.2.2
  exact max_le zero_le_one (by linarith)

/-- `diskDir` of a positive scalar multiple of a unit vector (any nonneg-ball membership proof) is
that unit vector — the proof-irrelevant reformulation of `diskDir_smul_unit`. -/
theorem diskDir_scaled {n : ℕ} (u : NSphere n) {c : ℝ} (hc : 0 < c) (hc1 : c ≤ 1)
    (h : c • (↑u : EuclideanSpace ℝ (Fin (n + 1)))
      ∈ closedBall (0 : EuclideanSpace ℝ (Fin (n + 1))) 1) :
    diskDir n ⟨c • (↑u : EuclideanSpace ℝ (Fin (n + 1))), h⟩ = u :=
  diskDir_smul_unit hc hc1

/-- The stereographic chart at any base point of `Sⁿ` has full target. -/
theorem chart_target_univ (u₀ : NSphere n) :
    (chartAt (EuclideanSpace ℝ (Fin n)) u₀).target = Set.univ := by
  haveI : Fact (Module.finrank ℝ (EuclideanSpace ℝ (Fin (n + 1))) = n + 1) :=
    ⟨finrank_euclideanSpace_fin⟩
  exact stereographic'_target _

/-- **The polar collar chart** of `D^{n+1}` at a base point `u₀ ∈ Sⁿ`: on the punctured ball with
direction in the `u₀`-stereographic chart's source, `v ↦ (chart_{Sⁿ}(v/‖v‖), 1 − ‖v‖)`. The
boundary sphere `‖v‖ = 1` lands on the half-space wall `t = 0`. -/
def diskCollarChart (u₀ : NSphere n) :
    OpenPartialHomeomorph (NDisk n)
      (ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace 1)) where
  source := {v : NDisk n | (↑v : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0 ∧
    diskDir n v ∈ (chartAt (EuclideanSpace ℝ (Fin n)) u₀).source}
  target := {p : ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace 1) |
    (p.2.val).ofLp 0 < 1}
  toFun v := (chartAt (EuclideanSpace ℝ (Fin n)) u₀ (diskDir n v),
    ⟨WithLp.toLp 2 (fun _ : Fin 1 => 1 - ‖(↑v : EuclideanSpace ℝ (Fin (n + 1)))‖),
      collar_one_sub_norm_nonneg n v⟩)
  invFun p := ⟨max 0 (1 - (p.2.val).ofLp 0) •
    ((chartAt (EuclideanSpace ℝ (Fin n)) u₀).symm p.1 : EuclideanSpace ℝ (Fin (n + 1))),
    collar_invFun_mem n u₀ p⟩
  map_source' := by
    intro v hv
    show (1 : ℝ) - ‖(↑v : EuclideanSpace ℝ (Fin (n + 1)))‖ < 1
    have : (0 : ℝ) < ‖(↑v : EuclideanSpace ℝ (Fin (n + 1)))‖ := norm_pos_iff.mpr hv.1
    linarith
  map_target' := by
    intro p hp
    simp only [mem_setOf_eq] at hp
    have ht : (0 : ℝ) ≤ p.2.val.ofLp 0 := p.2.2
    have hlt : (0 : ℝ) < 1 - p.2.val.ofLp 0 := by linarith
    have hc : (0 : ℝ) < max 0 (1 - p.2.val.ofLp 0) := lt_of_lt_of_le hlt (le_max_right _ _)
    have hc1 : max 0 (1 - p.2.val.ofLp 0) ≤ 1 := max_le zero_le_one (by linarith)
    refine ⟨?_, ?_⟩
    · show (max 0 (1 - p.2.val.ofLp 0) •
        ((chartAt (EuclideanSpace ℝ (Fin n)) u₀).symm p.1 : EuclideanSpace ℝ (Fin (n + 1)))) ≠ 0
      rw [smul_ne_zero_iff]
      refine ⟨ne_of_gt hc, ?_⟩
      rw [← norm_ne_zero_iff,
        mem_sphere_zero_iff_norm.mp ((chartAt (EuclideanSpace ℝ (Fin n)) u₀).symm p.1).2]
      norm_num
    · rw [diskDir_scaled _ hc hc1 (collar_invFun_mem n u₀ p)]
      exact (chartAt (EuclideanSpace ℝ (Fin n)) u₀).map_target
        (by rw [chart_target_univ]; exact Set.mem_univ p.1)
  left_inv' := by
    intro v hv
    apply Subtype.ext
    show max 0 (1 - (1 - ‖(↑v : EuclideanSpace ℝ (Fin (n + 1)))‖)) •
        ((chartAt (EuclideanSpace ℝ (Fin n)) u₀).symm
          (chartAt (EuclideanSpace ℝ (Fin n)) u₀ (diskDir n v)) : EuclideanSpace ℝ (Fin (n + 1)))
        = (↑v : EuclideanSpace ℝ (Fin (n + 1)))
    rw [(chartAt (EuclideanSpace ℝ (Fin n)) u₀).left_inv hv.2, sub_sub_cancel,
      max_eq_right (norm_nonneg _), diskDir_coe hv.1, smul_smul,
      mul_inv_cancel₀ (norm_ne_zero_iff.mpr hv.1), one_smul]
  right_inv' := by
    intro p hp
    simp only [mem_setOf_eq] at hp
    have ht : (0 : ℝ) ≤ p.2.val.ofLp 0 := p.2.2
    have hlt : (0 : ℝ) < 1 - p.2.val.ofLp 0 := by linarith
    have hc : (0 : ℝ) < max 0 (1 - p.2.val.ofLp 0) := lt_of_lt_of_le hlt (le_max_right _ _)
    have hc1 : max 0 (1 - p.2.val.ofLp 0) ≤ 1 := max_le zero_le_one (by linarith)
    have hmax : max 0 (1 - p.2.val.ofLp 0) = 1 - p.2.val.ofLp 0 := max_eq_right (le_of_lt hlt)
    have hnorm : ‖(max 0 (1 - p.2.val.ofLp 0) •
        ((chartAt (EuclideanSpace ℝ (Fin n)) u₀).symm p.1 : EuclideanSpace ℝ (Fin (n + 1))))‖
        = max 0 (1 - p.2.val.ofLp 0) := by
      rw [norm_smul, Real.norm_eq_abs,
        mem_sphere_zero_iff_norm.mp ((chartAt (EuclideanSpace ℝ (Fin n)) u₀).symm p.1).2, mul_one,
        abs_of_nonneg (le_max_left _ _)]
    refine Prod.ext ?_ ?_
    · show (chartAt (EuclideanSpace ℝ (Fin n)) u₀)
        (diskDir n ⟨max 0 (1 - p.2.val.ofLp 0) •
          ((chartAt (EuclideanSpace ℝ (Fin n)) u₀).symm p.1 : EuclideanSpace ℝ (Fin (n + 1))),
          collar_invFun_mem n u₀ p⟩) = p.1
      rw [diskDir_scaled _ hc hc1 (collar_invFun_mem n u₀ p)]
      exact (chartAt (EuclideanSpace ℝ (Fin n)) u₀).right_inv
        (by rw [chart_target_univ]; exact Set.mem_univ p.1)
    · apply Subtype.ext
      show WithLp.toLp 2 (fun _ : Fin 1 => 1 - ‖(max 0 (1 - p.2.val.ofLp 0) •
        ((chartAt (EuclideanSpace ℝ (Fin n)) u₀).symm p.1 : EuclideanSpace ℝ (Fin (n + 1))))‖)
          = p.2.val
      rw [hnorm, hmax, sub_sub_cancel]
      exact toLp_ofLp_fin_one _
  open_source := by
    have hU : IsOpen {v : NDisk n | (↑v : EuclideanSpace ℝ (Fin (n + 1))) ≠ 0} :=
      isOpen_compl_singleton.preimage continuous_subtype_val
    exact (continuousOn_diskDir n).isOpen_inter_preimage hU
      (chartAt (EuclideanSpace ℝ (Fin n)) u₀).open_source
  open_target := by
    apply isOpen_lt _ continuous_const
    exact (PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp
      (continuous_subtype_val.comp continuous_snd)
  continuousOn_toFun := by
    apply ContinuousOn.prodMk
    · exact (chartAt (EuclideanSpace ℝ (Fin n)) u₀).continuousOn.comp
        ((continuousOn_diskDir n).mono (fun v hv => hv.1)) (fun v hv => hv.2)
    · apply Continuous.continuousOn
      apply Continuous.subtype_mk
      apply (PiLp.continuous_toLp 2 _).comp
      apply continuous_pi
      intro _
      exact continuous_const.sub (continuous_norm.comp continuous_subtype_val)
  continuousOn_invFun := by
    have hsymm : Continuous fun x => (chartAt (EuclideanSpace ℝ (Fin n)) u₀).symm x := by
      have h := (chartAt (EuclideanSpace ℝ (Fin n)) u₀).continuousOn_symm
      rw [chart_target_univ] at h
      exact continuousOn_univ.mp h
    apply Continuous.continuousOn
    apply Continuous.subtype_mk
    -- v4.32: `Continuous.smul` now concludes a Pi-smul, so `apply` can no longer unify its
    -- conclusion `Continuous (?f • ?g)` against this pointwise `fun x => _ • _` goal. Supplying
    -- both arguments in one `exact` lets defeq do the matching.
    exact Continuous.smul
      (continuous_const.max (continuous_const.sub
        ((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp
          (continuous_subtype_val.comp continuous_snd))))
      (continuous_subtype_val.comp (hsymm.comp continuous_fst))

/-! ### §7. The charted-space structure on `D^{n+1}` -/

/-- **The closed unit `(n+1)`-ball is a charted space** on the half-space model
`ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace 1)` (`= (𝓡 n).prod (𝓡∂ 1)`): the atlas is
the single interior chart together with the polar collar chart family. The direct dimension-generic
analogue of `DiskChart.instChartedSpaceThreeDisk` (`n = 2`). -/
instance instChartedSpaceNDisk :
    ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin n)) (EuclideanHalfSpace 1)) (NDisk n) where
  atlas := insert (diskInteriorChart n) (Set.range (diskCollarChart n))
  chartAt v := if ‖(↑v : EuclideanSpace ℝ (Fin (n + 1)))‖ < 1 then diskInteriorChart n
    else diskCollarChart n (diskDir n v)
  mem_chart_source v := by
    by_cases h : ‖(↑v : EuclideanSpace ℝ (Fin (n + 1)))‖ < 1
    · rw [if_pos h]; exact h
    · rw [if_neg h]
      have hv1 : ‖(↑v : EuclideanSpace ℝ (Fin (n + 1)))‖ = 1 :=
        le_antisymm (mem_closedBall_zero_iff.mp v.2) (not_lt.mp h)
      refine ⟨?_, mem_chart_source (EuclideanSpace ℝ (Fin n)) (diskDir n v)⟩
      rw [← norm_ne_zero_iff, hv1]; norm_num
  chart_mem_atlas v := by
    by_cases h : ‖(↑v : EuclideanSpace ℝ (Fin (n + 1)))‖ < 1
    · rw [if_pos h]; exact Set.mem_insert _ _
    · rw [if_neg h]; exact Set.mem_insert_of_mem _ (Set.mem_range_self _)

end

/-! ### §8. The `n = 4` instantiation — `D⁵` charted on `KTModel` -/

open SKEFTHawking.SurgeryFoundation (KTModel)

/-- **The closed 5-ball** `D⁵ = closedBall(0,1) ⊆ E⁵`, presented as `NDisk 4` so its chart model is
`ModelProd (EuclideanSpace ℝ (Fin 4)) (EuclideanHalfSpace 1) = KTModel` on the nose. -/
abbrev D5 : Type := NDisk 4

/-- **`D⁵` is a charted space on `KTModel`** — the `n = 4` instantiation of the generic closed-ball
atlas. This is the handle-end atlas the Pin⁺ surgery-trace consumer (wave 6) takes as its
`[ChartedSpace KTModel Ha]` typeclass input, with `Ha = D⁵`, NO corner and NO re-association (the
header's design of record). -/
noncomputable instance instChartedSpaceKTModelD5 : ChartedSpace KTModel D5 :=
  instChartedSpaceNDisk 4

end SKEFTHawking.DiskChartGeneric
