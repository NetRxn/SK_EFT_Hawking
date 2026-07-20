/-
# Phase 5q.H — K4′′: the exterior-shell collar charts (the DiskChart adaptation)

The boundary of `T⁴° = T⁴ ∖ (16 round balls)` is 16 round `S³`s (`chartSphere c`, at chart-radius
`ρ = 1/2`). Near a boundary sphere the punctured torus is the **exterior** collar `{ρ ≤ ‖t‖}` of the
excised ball, in the centered chart `centeredChartParam c` (`KummerPuncturedTorus`). This module builds
the exterior-of-ball analogue of `DiskChartGeneric.diskCollarChart` — the collar chart of the shell onto
the half-space model, with radial coordinate `‖t‖ − ρ ≥ 0` (zero on the boundary sphere) in place of the
disk's `1 − ‖v‖`, and `S³` directions carried by the same stereographic atlas one dimension up from the
3-disk's `S²`.

## §A — the Euclidean exterior shell (this file's self-contained core)

`ExtShell = {t : E⁴ ∣ ρ ≤ ‖t‖}`, the closed exterior of the `ρ`-ball in `E⁴`, is a smooth
manifold-with-boundary on `ModelProd (EuclideanSpace ℝ (Fin 3)) (EuclideanHalfSpace 1) = (𝓡 3).prod (𝓡∂ 1)`,
its boundary the inner sphere `‖t‖ = ρ`. It is **cleaner** than the closed disk `NDisk`: there is no
centre (`‖t‖ ≥ ρ > 0`), so the direction map has no junk value, the collar inverse needs no `max`-clamp,
and the collar charts have target `univ` and cover `ExtShell` with **no interior chart** — the polar
collar family alone is the whole atlas.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.DiskChartGeneric
import SKEFTHawking.KummerChartedSpace

open Metric Set
open scoped Manifold

namespace SKEFTHawking.KummerShellChart

open SKEFTHawking.DiskChartGeneric (NSphere chart_target_univ)

noncomputable section

/-! ### §A.0. The closed exterior shell in `E⁴` -/

/-- **The closed exterior shell** `{t : E⁴ ∣ ρ ≤ ‖t‖}` at inner (excision) radius `ρ = 1/2`. The
punctured-torus side of a boundary sphere is a copy of this, transported by `centeredChartParam c`. -/
abbrev ExtShell : Type := {t : EuclideanSpace ℝ (Fin 4) // (1 : ℝ) / 2 ≤ ‖t‖}

/-- Every shell point has positive norm (`‖t‖ ≥ 1/2 > 0`) — no centre, hence no direction junk value. -/
theorem shell_norm_pos (v : ExtShell) : (0 : ℝ) < ‖(v : EuclideanSpace ℝ (Fin 4))‖ :=
  lt_of_lt_of_le (by norm_num) v.2

theorem shell_norm_ne_zero (v : ExtShell) : (v : EuclideanSpace ℝ (Fin 4)) ≠ 0 :=
  norm_ne_zero_iff.mp (ne_of_gt (shell_norm_pos v))

/-! ### §A.1. The direction map `ExtShell → S³` (no junk value) -/

/-- **The direction of a shell point**: `t/‖t‖ ∈ S³`. Total (no junk value), since `‖t‖ ≥ ρ > 0`. -/
def shellDir (v : ExtShell) : NSphere 3 :=
  ⟨‖(v : EuclideanSpace ℝ (Fin 4))‖⁻¹ • (v : EuclideanSpace ℝ (Fin 4)), by
    rw [mem_sphere_zero_iff_norm, norm_smul, norm_inv, norm_norm]
    exact inv_mul_cancel₀ (ne_of_gt (shell_norm_pos v))⟩

theorem shellDir_coe (v : ExtShell) :
    (shellDir v : EuclideanSpace ℝ (Fin 4))
      = ‖(v : EuclideanSpace ℝ (Fin 4))‖⁻¹ • (v : EuclideanSpace ℝ (Fin 4)) := rfl

/-- The direction of `(ρ + t) • u` (with `u ∈ S³`, `t ≥ 0`, so the scalar `> 0`) is `u`. -/
theorem shellDir_smul_unit (u : NSphere 3) {r : ℝ} (hr : (1 : ℝ) / 2 ≤ r)
    (h : (1 : ℝ) / 2 ≤ ‖r • (u : EuclideanSpace ℝ (Fin 4))‖) :
    shellDir ⟨r • (u : EuclideanSpace ℝ (Fin 4)), h⟩ = u := by
  have hu : ‖(u : EuclideanSpace ℝ (Fin 4))‖ = 1 := mem_sphere_zero_iff_norm.mp u.2
  have hrpos : (0 : ℝ) < r := lt_of_lt_of_le (by norm_num) hr
  apply Subtype.ext
  rw [shellDir_coe]
  show ‖r • (u : EuclideanSpace ℝ (Fin 4))‖⁻¹ • (r • (u : EuclideanSpace ℝ (Fin 4)))
    = (u : EuclideanSpace ℝ (Fin 4))
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hrpos, hu, mul_one, smul_smul,
    inv_mul_cancel₀ (ne_of_gt hrpos), one_smul]

/-- `shellDir` is continuous (`‖t‖ ≥ ρ > 0` everywhere, so `t ↦ ‖t‖⁻¹ • t` is continuous). -/
theorem continuous_shellDir : Continuous shellDir := by
  apply Continuous.subtype_mk
  exact ((continuous_norm.comp continuous_subtype_val).inv₀
    (fun v => ne_of_gt (shell_norm_pos v))).smul continuous_subtype_val

/-! ### §A.2. Half-space membership for the collar coordinates -/

/-- Half-space membership for the collar chart's radial coordinate: `‖t‖ − ρ ≥ 0` (zero on the boundary
sphere `‖t‖ = ρ`). -/
theorem collar_norm_sub_nonneg (v : ExtShell) :
    (0 : ℝ) ≤ ‖(v : EuclideanSpace ℝ (Fin 4))‖ - 1 / 2 := by
  have := v.2; linarith

/-- The collar chart's inverse lands in the exterior shell: `(ρ + t) • u` (with `u ∈ S³`, `t ≥ 0`) has
norm `ρ + t ≥ ρ`. -/
theorem collar_invFun_mem (u₀ : NSphere 3)
    (p : ModelProd (EuclideanSpace ℝ (Fin 3)) (EuclideanHalfSpace 1)) :
    (1 : ℝ) / 2 ≤ ‖((1 / 2 + p.2.val.ofLp 0) •
      ((chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm p.1 : EuclideanSpace ℝ (Fin 4)))‖ := by
  have ht : (0 : ℝ) ≤ p.2.val.ofLp 0 := p.2.2
  rw [norm_smul, Real.norm_eq_abs,
    mem_sphere_zero_iff_norm.mp ((chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm p.1).2, mul_one,
    abs_of_nonneg (by linarith)]
  linarith

/-- `shellDir` of a positive scalar multiple of a unit vector (any shell-membership proof) is that unit
vector — the proof-irrelevant reformulation of `shellDir_smul_unit`. -/
theorem shellDir_scaled (u : NSphere 3) {r : ℝ} (hr : (1 : ℝ) / 2 ≤ r)
    (h : (1 : ℝ) / 2 ≤ ‖r • (u : EuclideanSpace ℝ (Fin 4))‖) :
    shellDir ⟨r • (u : EuclideanSpace ℝ (Fin 4)), h⟩ = u :=
  shellDir_smul_unit u hr h

/-! ### §A.3. The polar collar chart family on the exterior shell -/

/-- **The polar collar chart** of `ExtShell` at a base point `u₀ ∈ S³`: on the cone `{v ∣ v/‖v‖ ∈
u₀-stereographic source}`, `v ↦ (chart_{S³}(v/‖v‖), ‖v‖ − ρ)`. The boundary sphere `‖v‖ = ρ` lands on
the half-space wall `t = 0`. Target is all of `E³ × HalfSpace¹` (no puncture, no clamp). -/
def shellCollarChart (u₀ : NSphere 3) :
    OpenPartialHomeomorph ExtShell
      (ModelProd (EuclideanSpace ℝ (Fin 3)) (EuclideanHalfSpace 1)) where
  source := {v : ExtShell | shellDir v ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) u₀).source}
  target := Set.univ
  toFun v := (chartAt (EuclideanSpace ℝ (Fin 3)) u₀ (shellDir v),
    ⟨WithLp.toLp 2 (fun _ : Fin 1 => ‖(v : EuclideanSpace ℝ (Fin 4))‖ - 1 / 2),
      collar_norm_sub_nonneg v⟩)
  invFun p := ⟨(1 / 2 + p.2.val.ofLp 0) •
    ((chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm p.1 : EuclideanSpace ℝ (Fin 4)),
    collar_invFun_mem u₀ p⟩
  map_source' := by intro v _; exact Set.mem_univ _
  map_target' := by
    intro p _
    have ht : (0 : ℝ) ≤ p.2.val.ofLp 0 := p.2.2
    have hr : (1 : ℝ) / 2 ≤ 1 / 2 + p.2.val.ofLp 0 := by linarith
    show shellDir ⟨(1 / 2 + p.2.val.ofLp 0) •
        ((chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm p.1 : EuclideanSpace ℝ (Fin 4)),
        collar_invFun_mem u₀ p⟩ ∈ (chartAt (EuclideanSpace ℝ (Fin 3)) u₀).source
    rw [shellDir_scaled _ hr (collar_invFun_mem u₀ p)]
    exact (chartAt (EuclideanSpace ℝ (Fin 3)) u₀).map_target
      (by rw [chart_target_univ]; exact Set.mem_univ p.1)
  left_inv' := by
    intro v hv
    apply Subtype.ext
    show (1 / 2 + (‖(v : EuclideanSpace ℝ (Fin 4))‖ - 1 / 2)) •
        ((chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm
          (chartAt (EuclideanSpace ℝ (Fin 3)) u₀ (shellDir v)) : EuclideanSpace ℝ (Fin 4))
        = (v : EuclideanSpace ℝ (Fin 4))
    rw [(chartAt (EuclideanSpace ℝ (Fin 3)) u₀).left_inv hv, add_sub_cancel, shellDir_coe, smul_smul,
      mul_inv_cancel₀ (ne_of_gt (shell_norm_pos v)), one_smul]
  right_inv' := by
    intro p _
    have ht : (0 : ℝ) ≤ p.2.val.ofLp 0 := p.2.2
    have hr : (1 : ℝ) / 2 ≤ 1 / 2 + p.2.val.ofLp 0 := by linarith
    have hnorm : ‖((1 / 2 + p.2.val.ofLp 0) •
        ((chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm p.1 : EuclideanSpace ℝ (Fin 4)))‖
        = 1 / 2 + p.2.val.ofLp 0 := by
      rw [norm_smul, Real.norm_eq_abs,
        mem_sphere_zero_iff_norm.mp ((chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm p.1).2, mul_one,
        abs_of_nonneg (by linarith)]
    refine Prod.ext ?_ ?_
    · show (chartAt (EuclideanSpace ℝ (Fin 3)) u₀)
        (shellDir ⟨(1 / 2 + p.2.val.ofLp 0) •
          ((chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm p.1 : EuclideanSpace ℝ (Fin 4)),
          collar_invFun_mem u₀ p⟩) = p.1
      rw [shellDir_scaled _ hr (collar_invFun_mem u₀ p)]
      exact (chartAt (EuclideanSpace ℝ (Fin 3)) u₀).right_inv
        (by rw [chart_target_univ]; exact Set.mem_univ p.1)
    · apply Subtype.ext
      show WithLp.toLp 2 (fun _ : Fin 1 => ‖((1 / 2 + p.2.val.ofLp 0) •
        ((chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm p.1 : EuclideanSpace ℝ (Fin 4)))‖ - 1 / 2)
          = p.2.val
      rw [hnorm, add_sub_cancel_left]
      exact DiskChartGeneric.toLp_ofLp_fin_one _
  open_source := by
    exact continuous_shellDir.isOpen_preimage _ (chartAt (EuclideanSpace ℝ (Fin 3)) u₀).open_source
  open_target := isOpen_univ
  continuousOn_toFun := by
    apply ContinuousOn.prodMk
    · exact (chartAt (EuclideanSpace ℝ (Fin 3)) u₀).continuousOn.comp
        continuous_shellDir.continuousOn (fun _ hv => hv)
    · apply Continuous.continuousOn
      apply Continuous.subtype_mk
      apply (PiLp.continuous_toLp 2 _).comp
      apply continuous_pi
      intro _
      exact (continuous_norm.comp continuous_subtype_val).sub continuous_const
  continuousOn_invFun := by
    have hsymm : Continuous fun x => (chartAt (EuclideanSpace ℝ (Fin 3)) u₀).symm x := by
      have h := (chartAt (EuclideanSpace ℝ (Fin 3)) u₀).continuousOn_symm
      rw [chart_target_univ] at h
      exact continuousOn_univ.mp h
    apply Continuous.continuousOn
    apply Continuous.subtype_mk
    apply Continuous.smul
    · exact continuous_const.add
        ((PiLp.continuous_apply 2 (fun _ : Fin 1 => ℝ) 0).comp
          (continuous_subtype_val.comp continuous_snd))
    · exact continuous_subtype_val.comp (hsymm.comp continuous_fst)

/-! ### §A.4. The charted-space structure on the exterior shell -/

/-- **The closed exterior shell is a charted space** on the half-space model
`ModelProd (EuclideanSpace ℝ (Fin 3)) (EuclideanHalfSpace 1)` (`= (𝓡 3).prod (𝓡∂ 1)`): the atlas is the
polar collar chart family alone — no interior chart is needed (there is no centre). The exterior-of-ball
analogue of `DiskChartGeneric.instChartedSpaceNDisk`, one dimension up (`S³`). -/
instance instChartedSpaceExtShell :
    ChartedSpace (ModelProd (EuclideanSpace ℝ (Fin 3)) (EuclideanHalfSpace 1)) ExtShell where
  atlas := Set.range shellCollarChart
  chartAt v := shellCollarChart (shellDir v)
  mem_chart_source v := mem_chart_source (EuclideanSpace ℝ (Fin 3)) (shellDir v)
  chart_mem_atlas _ := Set.mem_range_self _

/-! ### §B.0. The coordinate iso `ℝ⁴ = ℝ × ℝ × ℝ × ℝ ≅ E⁴`

`centeredChartParam c` (`KummerPuncturedTorus`) takes chart coordinates in the tuple `ℝ × ℝ × ℝ × ℝ`,
whereas the shell direction sphere `S³ ⊆ E⁴` lives in `EuclideanSpace ℝ (Fin 4)`. This block builds the
bridge: `toE4`/`ofE4` (mutually inverse, continuous) with `‖toE4 t‖ = √(sqNorm t)` (`sqNorm` = the
Euclidean square-norm of the tuple), so the round balls/spheres in tuple coordinates are round in `E⁴`. -/

open SKEFTHawking.KummerPuncturedTorus (sqNorm)

/-- Pack a chart tuple `ℝ × ℝ × ℝ × ℝ` into `E⁴ = EuclideanSpace ℝ (Fin 4)`. -/
def toE4 (t : ℝ × ℝ × ℝ × ℝ) : EuclideanSpace ℝ (Fin 4) :=
  WithLp.toLp 2 ![t.1, t.2.1, t.2.2.1, t.2.2.2]

/-- Unpack `E⁴` into a chart tuple `ℝ × ℝ × ℝ × ℝ`. -/
def ofE4 (w : EuclideanSpace ℝ (Fin 4)) : ℝ × ℝ × ℝ × ℝ :=
  (w.ofLp 0, w.ofLp 1, w.ofLp 2, w.ofLp 3)

/-- `‖toE4 t‖² = sqNorm t` — the tuple's Euclidean square-norm is carried faithfully into `E⁴`. -/
theorem norm_sq_toE4 (t : ℝ × ℝ × ℝ × ℝ) : ‖toE4 t‖ ^ 2 = sqNorm t := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  simp [toE4, sqNorm, Fin.sum_univ_four]

/-- `‖toE4 t‖ = √(sqNorm t)`. -/
theorem norm_toE4 (t : ℝ × ℝ × ℝ × ℝ) : ‖toE4 t‖ = Real.sqrt (sqNorm t) := by
  rw [← norm_sq_toE4, Real.sqrt_sq (norm_nonneg _)]

theorem continuous_toE4 : Continuous toE4 := by
  apply (PiLp.continuous_toLp 2 _).comp
  apply continuous_pi
  intro i
  fin_cases i <;> first
    | exact continuous_fst
    | exact continuous_fst.comp continuous_snd
    | exact continuous_fst.comp (continuous_snd.comp continuous_snd)
    | exact continuous_snd.comp (continuous_snd.comp continuous_snd)

theorem continuous_ofE4 : Continuous ofE4 := by
  apply Continuous.prodMk (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 0)
  apply Continuous.prodMk (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 1)
  exact Continuous.prodMk (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 2)
    (PiLp.continuous_apply 2 (fun _ : Fin 4 => ℝ) 3)

@[simp] theorem ofE4_toE4 (t : ℝ × ℝ × ℝ × ℝ) : ofE4 (toE4 t) = t := by
  simp only [ofE4, toE4, WithLp.ofLp_toLp, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three]

@[simp] theorem toE4_ofE4 (w : EuclideanSpace ℝ (Fin 4)) : toE4 (ofE4 w) = w := by
  apply WithLp.ofLp_injective
  funext i
  fin_cases i <;> rfl

theorem toE4_injective : Function.Injective toE4 :=
  Function.LeftInverse.injective ofE4_toE4

/-! ### §B.1. Extended chart injectivity beyond the excision radius

`centeredChartParam c` is injective on `{sqNorm ≤ ρ²}` (`ρ = 1/2`) — exactly the closed excision ball
(`KummerPuncturedTorus.centeredChartParam_injOn`). But `Circle.exp` is genuinely injective out to
`|s| < π`, so the chart is injective on a strictly larger ball. We push the bound to `|s| ≤ 3/4`
(`2·(3/4) = 3/2 < 2π`), giving injectivity on `{sqNorm ≤ (3/4)²}` — room for the **exterior** collar shell
`{ρ ≤ ‖t‖ < 3/4}` that lives on the punctured-torus side of the boundary sphere. -/

/-- **Per-factor chart injectivity on `[−3/4, 3/4]`** — the same period argument as `circle_exp_injOn_half`
one notch wider (`2·(3/4) = 3/2 < 2π`), the input to injectivity on the exterior collar shell. -/
theorem circle_exp_injOn_threeQuarters {s s' : ℝ} (hs : |s| ≤ 3 / 4) (hs' : |s'| ≤ 3 / 4)
    (h : Circle.exp s = Circle.exp s') : s = s' := by
  have hc : Complex.exp (↑s * Complex.I) = Complex.exp (↑s' * Complex.I) := by
    rw [← Circle.coe_exp, ← Circle.coe_exp, h]
  rw [Complex.exp_eq_exp_iff_exists_int] at hc
  obtain ⟨n, hn⟩ := hc
  have hfac : (↑s : ℂ) * Complex.I = (↑s' + ↑n * (2 * ↑Real.pi)) * Complex.I := by rw [hn]; ring
  have hcC : (↑s : ℂ) = ↑s' + ↑n * (2 * ↑Real.pi) := mul_right_cancel₀ Complex.I_ne_zero hfac
  have hR : s = s' + (n : ℝ) * (2 * Real.pi) := by exact_mod_cast hcC
  have hpi : (2 : ℝ) ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have hdiff : |(n : ℝ) * (2 * Real.pi)| ≤ 3 / 2 := by
    have he : (n : ℝ) * (2 * Real.pi) = s - s' := by linarith [hR]
    rw [he]
    calc |s - s'| ≤ |s| + |s'| := abs_sub _ _
      _ ≤ 3 / 4 + 3 / 4 := by linarith [hs, hs']
      _ = 3 / 2 := by norm_num
  have hn0 : n = 0 := by
    by_contra hne
    have h1 : (1 : ℝ) ≤ |(n : ℝ)| := by
      have hz : (1 : ℤ) ≤ |n| := Int.one_le_abs (by exact_mod_cast hne)
      have hz' := (Int.cast_le (R := ℝ)).mpr hz
      rwa [Int.cast_abs, Int.cast_one] at hz'
    rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)] at hdiff
    nlinarith [hdiff, h1, hpi]
  rw [hn0] at hR; simpa using hR

/-- The tuple square-norm of `ofE4 w` is `‖w‖²` — the bridge for transporting `sqNorm` bounds to `E⁴`. -/
theorem sqNorm_ofE4 (w : EuclideanSpace ℝ (Fin 4)) : sqNorm (ofE4 w) = ‖w‖ ^ 2 := by
  rw [← norm_sq_toE4, toE4_ofE4]

open SKEFTHawking.KummerPuncturedTorus (centeredChartParam excisionRadius)

/-- **Extended product chart injectivity on the closed ball `{sqNorm ≤ (3/4)²}`.** Each coordinate
`|t.i| ≤ 3/4`, where `Circle.exp` is injective (`circle_exp_injOn_threeQuarters`). This strictly
contains the closed excision ball `{sqNorm ≤ (1/2)²}`, giving the room the exterior collar shell needs. -/
theorem centeredChartParam_injOn_threeQuarters (c : SKEFTHawking.KummerK3Base.TorusFour) :
    Set.InjOn (centeredChartParam c) {t | sqNorm t ≤ (3 / 4) ^ 2} := by
  intro t ht t' ht' h
  rw [Set.mem_setOf_eq] at ht ht'
  have a1 : |t.1| ≤ 3 / 4 := SKEFTHawking.KummerPuncturedTorus.abs_le_of_sq_le_sq (by norm_num) (by
    simp only [sqNorm] at ht; nlinarith [sq_nonneg t.2.1, sq_nonneg t.2.2.1, sq_nonneg t.2.2.2])
  have a2 : |t.2.1| ≤ 3 / 4 := SKEFTHawking.KummerPuncturedTorus.abs_le_of_sq_le_sq (by norm_num) (by
    simp only [sqNorm] at ht; nlinarith [sq_nonneg t.1, sq_nonneg t.2.2.1, sq_nonneg t.2.2.2])
  have a3 : |t.2.2.1| ≤ 3 / 4 := SKEFTHawking.KummerPuncturedTorus.abs_le_of_sq_le_sq (by norm_num) (by
    simp only [sqNorm] at ht; nlinarith [sq_nonneg t.1, sq_nonneg t.2.1, sq_nonneg t.2.2.2])
  have a4 : |t.2.2.2| ≤ 3 / 4 := SKEFTHawking.KummerPuncturedTorus.abs_le_of_sq_le_sq (by norm_num) (by
    simp only [sqNorm] at ht; nlinarith [sq_nonneg t.1, sq_nonneg t.2.1, sq_nonneg t.2.2.1])
  have a1' : |t'.1| ≤ 3 / 4 := SKEFTHawking.KummerPuncturedTorus.abs_le_of_sq_le_sq (by norm_num) (by
    simp only [sqNorm] at ht'; nlinarith [sq_nonneg t'.2.1, sq_nonneg t'.2.2.1, sq_nonneg t'.2.2.2])
  have a2' : |t'.2.1| ≤ 3 / 4 := SKEFTHawking.KummerPuncturedTorus.abs_le_of_sq_le_sq (by norm_num) (by
    simp only [sqNorm] at ht'; nlinarith [sq_nonneg t'.1, sq_nonneg t'.2.2.1, sq_nonneg t'.2.2.2])
  have a3' : |t'.2.2.1| ≤ 3 / 4 := SKEFTHawking.KummerPuncturedTorus.abs_le_of_sq_le_sq (by norm_num) (by
    simp only [sqNorm] at ht'; nlinarith [sq_nonneg t'.1, sq_nonneg t'.2.1, sq_nonneg t'.2.2.2])
  have a4' : |t'.2.2.2| ≤ 3 / 4 := SKEFTHawking.KummerPuncturedTorus.abs_le_of_sq_le_sq (by norm_num) (by
    simp only [sqNorm] at ht'; nlinarith [sq_nonneg t'.1, sq_nonneg t'.2.1, sq_nonneg t'.2.2.1])
  simp only [centeredChartParam, Prod.mk.injEq] at h
  obtain ⟨e1, e2, e3, e4⟩ := h
  exact Prod.ext (circle_exp_injOn_threeQuarters a1 a1' (mul_left_cancel e1))
    (Prod.ext (circle_exp_injOn_threeQuarters a2 a2' (mul_left_cancel e2))
      (Prod.ext (circle_exp_injOn_threeQuarters a3 a3' (mul_left_cancel e3))
        (circle_exp_injOn_threeQuarters a4 a4' (mul_left_cancel e4))))

/-! ### §B.2. The extended round chart in `E⁴` coordinates

`centeredChartParam_openPartialHomeomorph` (`KummerChartedSpace`) is the round chart on the excision ball
`{sqNorm < ρ²}`. Here we bundle `ℝ⁴ ≅ E⁴` as a homeomorphism and push the round chart to the larger ball
`{w : E⁴ ∣ ‖w‖ < 3/4}` (using the extended injectivity of §B.1), landing in `E⁴` coordinates so the shell
direction sphere `S³ ⊆ E⁴` is directly available. This is the transport vehicle: its `‖w‖ ≥ ρ` part is the
punctured-torus side of a boundary sphere. -/

open SKEFTHawking.KummerK3Base (TorusFour)
open SKEFTHawking.KummerPuncturedTorus
  (continuous_centeredChartParam isOpenMap_centeredChartParam)

/-- **`ℝ⁴ = ℝ × ℝ × ℝ × ℝ ≅ E⁴`** as a homeomorphism (the coordinate iso of §B.0, bundled). -/
def homeoE4 : (ℝ × ℝ × ℝ × ℝ) ≃ₜ EuclideanSpace ℝ (Fin 4) where
  toFun := toE4
  invFun := ofE4
  left_inv := ofE4_toE4
  right_inv := toE4_ofE4
  continuous_toFun := continuous_toE4
  continuous_invFun := continuous_ofE4

theorem isOpenMap_ofE4 : IsOpenMap ofE4 := homeoE4.symm.isOpenMap

/-- **The extended round chart in `E⁴` coordinates** `centeredChartParamE4 c`: the `OpenPartialHomeomorph
E⁴ → T⁴`, `w ↦ centeredChartParam c (ofE4 w)`, on the open ball `{‖w‖ < 3/4}`. Genuine homeomorphism onto
its image (injective by the extended bound of §B.1, open by `isOpenMap_centeredChartParam`). Its `1/2 ≤ ‖w‖`
locus is the exterior collar shell on the punctured-torus side of `chartSphere c`. -/
noncomputable def centeredChartParamE4 (c : TorusFour) :
    OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 4)) TorusFour := by
  refine OpenPartialHomeomorph.ofContinuousOpenRestrict
    (Set.InjOn.toPartialEquiv (fun w => centeredChartParam c (ofE4 w))
      {w : EuclideanSpace ℝ (Fin 4) | ‖w‖ < 3 / 4} ?_) ?_ ?_ ?_
  · intro w hw w' hw' h
    have hle : ∀ {u : EuclideanSpace ℝ (Fin 4)}, ‖u‖ < 3 / 4 → sqNorm (ofE4 u) ≤ (3 / 4) ^ 2 := by
      intro u hu; rw [sqNorm_ofE4]; nlinarith [norm_nonneg u]
    have := centeredChartParam_injOn_threeQuarters c (hle hw) (hle hw') h
    have h2 : toE4 (ofE4 w) = toE4 (ofE4 w') := congrArg toE4 this
    rwa [toE4_ofE4, toE4_ofE4] at h2
  · exact ((continuous_centeredChartParam c).comp continuous_ofE4).continuousOn
  · exact ((isOpenMap_centeredChartParam c).comp isOpenMap_ofE4).restrict
      (isOpen_lt continuous_norm continuous_const)
  · exact isOpen_lt continuous_norm continuous_const

@[simp] theorem centeredChartParamE4_source (c : TorusFour) :
    (centeredChartParamE4 c).source = {w : EuclideanSpace ℝ (Fin 4) | ‖w‖ < 3 / 4} := rfl

@[simp] theorem centeredChartParamE4_apply (c : TorusFour) (w : EuclideanSpace ℝ (Fin 4)) :
    (centeredChartParamE4 c) w = centeredChartParam c (ofE4 w) := rfl

/-! ### §B.3. The exterior shell lands on the punctured-torus side (the geometric heart)

The transported exterior shell `{1/2 ≤ ‖w‖ < 3/4}` (image under `centeredChartParamE4 c`) lies in
`puncturedTorus`: it avoids `chartBall c` (by the extended injectivity — a shell point has `sqNorm ≥ 1/4`,
so it cannot be the image of an interior `sqNorm < 1/4` point) and avoids every other `chartBall c'` (by
the fixed-point separation `dist c c' ≥ 2`, since a shell point is within `3/4` of `c` and any point of
`chartBall c'` is within `1/2` of `c'`, and `3/4 + 1/2 < 2`). This is the exterior analogue of
`sphere_subset_puncturedTorus`, extended off the boundary sphere into the collar. -/

open SKEFTHawking.KummerPuncturedTorus
  (chartBall chartBall_subset_metricBall dist_centeredChartParam_lt fixedSet_dist_ge fixedSet
    sqNorm_nonneg excisedBalls puncturedTorus)

/-- **The exterior collar shell lies in `puncturedTorus`.** For `c` a fixed point and `1/2 ≤ ‖w‖ < 3/4`,
the point `centeredChartParam c (ofE4 w)` is on the punctured-torus side of the boundary sphere. -/
theorem shellImage_mem_puncturedTorus {c : TorusFour} (hc : c ∈ fixedSet)
    {w : EuclideanSpace ℝ (Fin 4)} (h1 : (1 : ℝ) / 2 ≤ ‖w‖) (h2 : ‖w‖ < 3 / 4) :
    centeredChartParam c (ofE4 w) ∈ SKEFTHawking.KummerPuncturedTorus.puncturedTorus := by
  have hsq : sqNorm (ofE4 w) = ‖w‖ ^ 2 := sqNorm_ofE4 w
  rw [SKEFTHawking.KummerPuncturedTorus.puncturedTorus, Set.mem_compl_iff,
    SKEFTHawking.KummerPuncturedTorus.excisedBalls, Set.mem_iUnion₂]
  rintro ⟨c', hc', hmem⟩
  by_cases hcc : c' = c
  · rw [hcc] at hmem
    -- shell point cannot lie in the excised ball `chartBall c` (extended injectivity)
    obtain ⟨t', ht', heq⟩ := hmem
    rw [Set.mem_setOf_eq, show SKEFTHawking.KummerPuncturedTorus.excisionRadius = (1 : ℝ) / 2 from rfl]
      at ht'
    have hofE4le : sqNorm (ofE4 w) ≤ (3 / 4) ^ 2 := by rw [hsq]; nlinarith [norm_nonneg w]
    have ht'le : sqNorm t' ≤ (3 / 4) ^ 2 := by nlinarith [sqNorm_nonneg t']
    have : ofE4 w = t' :=
      centeredChartParam_injOn_threeQuarters c hofE4le ht'le heq.symm
    rw [this] at hsq
    nlinarith [ht', hsq, h1, sq_nonneg (‖w‖ - 1 / 2)]
  · -- shell point at `c` cannot lie in a ball at a distinct fixed point `c'` (separation ≥ 2)
    have hdc : dist (centeredChartParam c (ofE4 w)) c < 3 / 4 :=
      dist_centeredChartParam_lt c (by norm_num) (by rw [hsq]; nlinarith [norm_nonneg w])
    have hdc' : dist (centeredChartParam c (ofE4 w)) c' < 1 / 2 := by
      have := chartBall_subset_metricBall c' hmem
      rwa [Metric.mem_ball, show SKEFTHawking.KummerPuncturedTorus.excisionRadius = (1 : ℝ) / 2 from
        rfl] at this
    have hsep : (2 : ℝ) ≤ dist c c' := fixedSet_dist_ge hc hc' (fun h => hcc h.symm)
    have htri : dist c c' ≤ dist c (centeredChartParam c (ofE4 w)) +
        dist (centeredChartParam c (ofE4 w)) c' := dist_triangle _ _ _
    rw [dist_comm c (centeredChartParam c (ofE4 w))] at htri
    linarith

/-! ### §B.4. The collar homeomorphism — the punctured-torus collar ≅ the Euclidean shell

Via `OpenPartialHomeomorph.homeomorphOfImageSubsetSource` on the extended round chart `centeredChartParamE4
c`, the Euclidean shell `shellSetE4 = {1/2 ≤ ‖w‖ < 3/4}` (a subset of the source ball, need **not** be open)
is carried homeomorphically onto the transported collar `collarSet c` of the boundary sphere `chartSphere
c`. This collar is **relatively open** in `puncturedTorus` and lies inside it (`shellImage_mem_puncturedTorus`):
it is the punctured-torus-side neighborhood of the boundary sphere. Composing this homeomorphism with the
inclusion `↥shellSetE4 ↪ ExtShell` and `shellCollarChart u₀` charts the collar onto the half-space model —
the boundary chart at each of the 16 spheres. -/

/-- **The Euclidean collar shell** `{w : E⁴ ∣ 1/2 ≤ ‖w‖ < 3/4}` — a subset of the extended round chart's
source ball, whose image is the punctured-torus collar of a boundary sphere. -/
def shellSetE4 : Set (EuclideanSpace ℝ (Fin 4)) := {w | (1 : ℝ) / 2 ≤ ‖w‖ ∧ ‖w‖ < 3 / 4}

theorem shellSetE4_subset_ExtShell : ∀ w ∈ shellSetE4, (1 : ℝ) / 2 ≤ ‖w‖ := fun _ hw => hw.1

theorem shellSetE4_subset_source (c : TorusFour) :
    shellSetE4 ⊆ (centeredChartParamE4 c).source := by
  intro w hw
  rw [centeredChartParamE4_source, Set.mem_setOf_eq]
  exact hw.2

/-- **The transported collar** `collarSet c := centeredChartParamE4 c '' shellSetE4` — the punctured-torus
neighborhood of the boundary sphere `chartSphere c`, on the exterior (punctured) side. -/
def collarSet (c : TorusFour) : Set TorusFour := (centeredChartParamE4 c) '' shellSetE4

/-- The transported collar lies inside `puncturedTorus` (via `shellImage_mem_puncturedTorus`). -/
theorem collarSet_subset_puncturedTorus {c : TorusFour} (hc : c ∈ fixedSet) :
    collarSet c ⊆ puncturedTorus := by
  rintro _ ⟨w, hw, rfl⟩
  exact shellImage_mem_puncturedTorus hc hw.1 hw.2

/-- **The collar homeomorphism** `↥shellSetE4 ≃ₜ ↥(collarSet c)`: the punctured-torus collar of the
boundary sphere `chartSphere c` is homeomorphic to the Euclidean exterior shell. The topological core of
the boundary chart, delivered by the extended round chart's `homeomorphOfImageSubsetSource`. -/
noncomputable def collarHomeo (c : TorusFour) : ↥shellSetE4 ≃ₜ ↥(collarSet c) :=
  (centeredChartParamE4 c).homeomorphOfImageSubsetSource (shellSetE4_subset_source c) rfl

/-! ### §C. STATUS — the K4′′ certificate

**GREEN here — deliverable (1) COMPLETE, deliverable (2) mathematical content + topological core:**

Deliverable (1) — **the exterior-shell collar charts** (§A):
- `shellCollarChart u₀` — the collar chart of `ExtShell = {t : E⁴ ∣ ρ ≤ ‖t‖}` onto `(𝓡 3).prod (𝓡∂ 1)`,
  `v ↦ (chart_{S³}(v/‖v‖), ‖v‖ − ρ)`; the exterior-of-ball analogue of `DiskChartGeneric.diskCollarChart`.
- `instChartedSpaceExtShell` — `ExtShell` is a manifold-with-boundary charted on the half-space model,
  the polar collar family alone (no interior chart: no centre).

Deliverable (2) — **the transport to the T⁴° side** (§B):
- `toE4`/`ofE4`/`homeoE4` — the coordinate iso `ℝ⁴ ≅ E⁴` (`sqNorm`-faithful).
- `circle_exp_injOn_threeQuarters`, `centeredChartParam_injOn_threeQuarters` — chart injectivity extended
  from the excision ball `{sqNorm ≤ ρ²}` to `{sqNorm ≤ (3/4)²}` (room for the exterior collar).
- `centeredChartParamE4 c` — the extended round chart as an `OpenPartialHomeomorph E⁴ → T⁴` on `{‖w‖ < 3/4}`.
- `shellImage_mem_puncturedTorus` — the geometric heart: the exterior shell lands on the punctured side.
- `collarHomeo c : ↥shellSetE4 ≃ₜ ↥(collarSet c)` — **each of the 16 boundary collars is homeomorphic to
  the Euclidean exterior shell**; `collarSet_subset_puncturedTorus` places the collar inside `T⁴°`.

**Residual (the point-set packaging, path now unblocked by `collarHomeo`):**
The full `ChartedSpace ((𝓡 3).prod (𝓡∂ 1)) (↥puncturedTorus)` needs two assembly steps, both reducible to
composition of the objects above:
1. **Boundary charts** — per `(c, u₀)`, the `OpenPartialHomeomorph (↥puncturedTorus) ((𝓡 3).prod (𝓡∂ 1))`
   with source `collarSet c` (relatively open in `T⁴°`), built by `OpenPartialHomeomorph.ofContinuousOpenRestrict`
   with forward map `shellCollarChart u₀ ∘ (↥shellSetE4 ↪ ExtShell) ∘ (collarHomeo c).symm ∘ val`. Its
   `IsOpenMap` requirement is now discharged by composition: `(collarHomeo c).symm` is a homeomorphism, the
   inclusion `↥shellSetE4 ↪ ExtShell` is an open embedding (`shellSetE4` is open in `ExtShell`), and
   `shellCollarChart u₀` is a chart — no bespoke subtype open-map argument remains.
2. **Interior charts** — the ambient `T⁴` product charts on `openPunctured` (`interior_chartedSpace`,
   `KummerChartedSpace`) reshaped `E⁴ ≅ E³ × (0,∞) ⊆ E³ × HalfSpace¹` into the boundary model's interior,
   glued to the boundary charts via the `chartAt` dispatch (interior vs the 16 collars).

The Q-side descent (deliverable 3) then follows: `shellCollarChart` is `τ`-equivariant (`τ = −id` preserves
`‖·‖` and antipodes directions), so it descends through `qmk` to the `ℝP³ × collar` charts on `FreeQuotient`
via the banked `qmk_localOpenPartialHomeomorph`/`isOpenEmbedding_qmk_sepBall`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom. -/

end

end SKEFTHawking.KummerShellChart
