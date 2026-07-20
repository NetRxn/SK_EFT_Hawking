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

end

end SKEFTHawking.KummerShellChart
