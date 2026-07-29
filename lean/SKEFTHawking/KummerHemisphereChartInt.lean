import Mathlib
import SKEFTHawking.KummerResolutionPiece
import SKEFTHawking.SingularFlatDiskChartVanishInt
import SKEFTHawking.SingularRelativeMVLESInt
import SKEFTHawking.KummerResolutionPieceH2

/-!
# The hemispheres of the zero section are flat 2-disks in 4-charts of `ResE`

This is the **geometric identification** that connects the abstract local-homology machinery
(`SingularFlatDiskChartVanishInt`, `SingularRelativeMVLESInt`) to the concrete Kummer resolution
piece `ResE` (`KummerResolutionPiece`).

`ResE` is two copies of `D² × D²` welded along the base equator by the Euler-number `−2` clutch
`(z, w) ↦ (z⁻¹, z² w)`. The zero section `S² = {w = 0}` is covered by the two closed hemispheres

* `hemi0 = {chart0 (z, 0) | ‖z‖ ≤ 1}` and `hemi1 = {chart1 (z, 0) | ‖z‖ ≤ 1}`,

which meet exactly in the equator circle. **Neither hemisphere lies inside a chart-image interior**:
its equator boundary is precisely where the two charts weld, so `chart0` alone cannot host it. The
module therefore builds an *extended* chart-0 — the chart-0 bidisk continued **across the weld** into
the annular part of chart 1 by the clutch — realised as a single continuous map

`F : ℝ⁴ ⊇ W → ResE`, `F(z, u) = chart0 (z, u)` for `‖z‖ ≤ 1`, `= chart1 (z⁻¹, z² u)` for `‖z‖ ≥ 1`

(the two branches agree on `‖z‖ = 1` by `chart_glue`). On the compact `W = {‖z‖ ≤ 3/2, ‖u‖ ≤ 1/4}`
`F` is continuous and injective into the Hausdorff `ResE`, hence a closed embedding; restricted to
the open `Wo = {‖z‖ < 3/2, ‖u‖ < 1/4}` its image `U` is open (a saturation computation in the
quotient), so `F : Wo ≃ₜ U` is a chart of `ResE` **containing the whole closed hemisphere** — which
in these coordinates is the flat 2-disk `{u = 0, ‖z‖ ≤ 1}`.

Rescaling by `1/2` puts the hemisphere on `flatDisk 4 2 (1/2)`, and
`SingularFlatDiskChartVanishInt.relHomology_flatDiskChart_four_eq_zero` then gives

`H₂(ResE | hemi) = H₃(ResE | hemi) = 0`,

the per-piece hypothesis set of `SingularRelativeMVLESInt.localMvDeltaEquivInt` at `n = 2`. The
second hemisphere is obtained for free from the **chart-swap involution** `swapE : ResE ≃ₜ ResE`
(the weld relation `glued` is symmetric), so no second chart has to be built.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.SingularEuclideanAcyclic (Eucl)
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularStarComplementRetractInt (flatDisk)

namespace SKEFTHawking.KummerHemisphereChartInt

/-! ## §1. `ℝ⁴ = ℂ × ℂ` coordinates -/

/-- The first complex coordinate of a point of `ℝ⁴`. -/
def zc (p : EuclideanSpace ℝ (Fin 4)) : ℂ := ⟨p 0, p 1⟩

/-- The second complex coordinate of a point of `ℝ⁴`. -/
def uc (p : EuclideanSpace ℝ (Fin 4)) : ℂ := ⟨p 2, p 3⟩

theorem normC_sq (z : ℂ) : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
  rw [Complex.norm_def, Real.sq_sqrt (Complex.normSq_nonneg _), Complex.normSq_apply]; ring

theorem continuous_zc : Continuous zc :=
  Complex.equivRealProdCLM.symm.continuous.comp
    (Continuous.prodMk (by fun_prop) (by fun_prop))

theorem continuous_uc : Continuous uc :=
  Complex.equivRealProdCLM.symm.continuous.comp
    (Continuous.prodMk (by fun_prop) (by fun_prop))

/-- The Euclidean norm of `ℝ⁴` splits as the two complex norms. -/
theorem norm_sq_split (p : EuclideanSpace ℝ (Fin 4)) : ‖p‖ ^ 2 = ‖zc p‖ ^ 2 + ‖uc p‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity), Fin.sum_univ_four, normC_sq, normC_sq]
  simp only [zc, uc, Real.norm_eq_abs, sq_abs]
  ring

/-- The two complex coordinates determine the point. -/
theorem ext4 {p q : EuclideanSpace ℝ (Fin 4)} (hz : zc p = zc q) (hu : uc p = uc q) : p = q := by
  have h0 : p 0 = q 0 := congrArg Complex.re hz
  have h1 : p 1 = q 1 := congrArg Complex.im hz
  have h2 : p 2 = q 2 := congrArg Complex.re hu
  have h3 : p 3 = q 3 := congrArg Complex.im hu
  ext i
  fin_cases i <;> assumption

theorem zc_smul (c : ℝ) (p : EuclideanSpace ℝ (Fin 4)) : zc (c • p) = (c : ℂ) * zc p := by
  apply Complex.ext <;> simp [zc]

theorem uc_smul (c : ℝ) (p : EuclideanSpace ℝ (Fin 4)) : uc (c • p) = (c : ℂ) * uc p := by
  apply Complex.ext <;> simp [uc]

/-- Membership in the closed flat 2-disk of `ℝ⁴`, in complex coordinates. -/
theorem mem_flatDisk_iff {r : ℝ} (p : EuclideanSpace ℝ (Fin 4)) :
    p ∈ flatDisk 4 2 r ↔ uc p = 0 ∧ ‖zc p‖ ≤ r := by
  constructor
  · rintro ⟨hn, hz⟩
    have h2 : p 2 = 0 := hz 2 (by norm_num)
    have h3 : p 3 = 0 := hz 3 (by norm_num)
    have hu : uc p = 0 := by apply Complex.ext <;> simp [uc, h2, h3]
    refine ⟨hu, ?_⟩
    have := norm_sq_split p
    rw [hu] at this
    simp only [norm_zero] at this
    nlinarith [norm_nonneg (zc p), norm_nonneg p, hn, this]
  · rintro ⟨hu, hz⟩
    have h2 : p 2 = 0 := congrArg Complex.re hu
    have h3 : p 3 = 0 := congrArg Complex.im hu
    refine ⟨?_, fun i hi => ?_⟩
    · have := norm_sq_split p
      rw [hu] at this
      simp only [norm_zero] at this
      nlinarith [norm_nonneg (zc p), norm_nonneg p, hz, this]
    · fin_cases i <;> simp_all

/-! ## §2. The clamped chart formulas -/

/-- `z` retracted into the closed unit disk (identity on the disk, radial elsewhere). -/
noncomputable def clampC (z : ℂ) : ℂ := ((max 1 ‖z‖ : ℝ) : ℂ)⁻¹ * z

/-- The continuous total extension of `z ↦ z⁻¹` that is correct outside the open unit disk. -/
noncomputable def invC (z : ℂ) : ℂ := ((max 1 (‖z‖ ^ 2) : ℝ) : ℂ)⁻¹ * (starRingEnd ℂ) z

theorem one_le_max_norm (z : ℂ) : (1 : ℝ) ≤ max 1 ‖z‖ := le_max_left _ _

theorem max_norm_pos (z : ℂ) : (0 : ℝ) < max 1 ‖z‖ :=
  lt_of_lt_of_le zero_lt_one (one_le_max_norm z)

theorem norm_clampC_le_one (z : ℂ) : ‖clampC z‖ ≤ 1 := by
  have hpos : (0 : ℝ) < max 1 ‖z‖ := max_norm_pos z
  rw [clampC, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos,
    inv_mul_le_iff₀ hpos, mul_one]
  exact le_max_right _ _

theorem clampC_of_le_one {z : ℂ} (h : ‖z‖ ≤ 1) : clampC z = z := by
  rw [clampC, max_eq_left h]
  norm_num

theorem continuous_clampC : Continuous clampC := by
  refine Continuous.mul (Continuous.inv₀ ?_ ?_) continuous_id
  · exact Complex.continuous_ofReal.comp (continuous_const.max continuous_norm)
  · exact fun z => Complex.ofReal_ne_zero.mpr (ne_of_gt (max_norm_pos z))

theorem norm_invC_le_one (z : ℂ) : ‖invC z‖ ≤ 1 := by
  have hpos : (0 : ℝ) < max 1 (‖z‖ ^ 2) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  rw [invC, norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos,
    RCLike.norm_conj, inv_mul_le_iff₀ hpos, mul_one]
  rcases le_or_gt ‖z‖ 1 with h | h
  · exact le_trans h (le_max_left _ _)
  · exact le_trans (by nlinarith [norm_nonneg z]) (le_max_right 1 (‖z‖ ^ 2))

theorem invC_of_one_le {z : ℂ} (h : 1 ≤ ‖z‖) : invC z = z⁻¹ := by
  have h1 : (1 : ℝ) ≤ ‖z‖ ^ 2 := by nlinarith
  rw [invC, max_eq_right h1]
  conv_rhs => rw [Complex.inv_def, Complex.normSq_eq_norm_sq]
  push_cast
  ring

theorem continuous_invC : Continuous invC := by
  refine Continuous.mul (Continuous.inv₀ ?_ ?_) Complex.continuous_conj
  · exact Complex.continuous_ofReal.comp (continuous_const.max (continuous_norm.pow 2))
  · exact fun z => Complex.ofReal_ne_zero.mpr
      (ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _)))

/-- The clutch commutes with the fiber clamp on the equator. -/
theorem clampC_mul_sq {z u : ℂ} (hz : ‖z‖ = 1) : clampC (z ^ 2 * u) = z ^ 2 * clampC u := by
  have hn : ‖z ^ 2 * u‖ = ‖u‖ := by rw [norm_mul, norm_pow, hz, one_pow, one_mul]
  rw [clampC, clampC, hn]
  ring

/-! ## §3. The extended chart `F` -/

/-- Chart-0 branch (clamped so it is total). -/
noncomputable def brA (p : EuclideanSpace ℝ (Fin 4)) : ResE :=
  chart0 (⟨clampC (zc p), norm_clampC_le_one _⟩, ⟨clampC (uc p), norm_clampC_le_one _⟩)

/-- Chart-1 branch (clamped so it is total): the clutch image of the chart-0 branch. -/
noncomputable def brB (p : EuclideanSpace ℝ (Fin 4)) : ResE :=
  chart1 (⟨invC (zc p), norm_invC_le_one _⟩,
    ⟨clampC ((zc p) ^ 2 * uc p), norm_clampC_le_one _⟩)

/-- **The extended chart-0 map** `ℝ⁴ → ResE`: chart 0 inside the base unit disk, continued across
the weld into chart 1 outside it. -/
noncomputable def F (p : EuclideanSpace ℝ (Fin 4)) : ResE :=
  if ‖zc p‖ ≤ 1 then brA p else brB p

theorem continuous_brA : Continuous brA :=
  continuous_chart0.comp (Continuous.prodMk
    ((continuous_clampC.comp continuous_zc).subtype_mk _)
    ((continuous_clampC.comp continuous_uc).subtype_mk _))

theorem continuous_brB : Continuous brB :=
  continuous_chart1.comp (Continuous.prodMk
    ((continuous_invC.comp continuous_zc).subtype_mk _)
    ((continuous_clampC.comp (((continuous_zc.pow 2).mul continuous_uc))).subtype_mk _))

/-- **The weld identity**: the two branches agree on the base equator. -/
theorem brA_eq_brB {p : EuclideanSpace ℝ (Fin 4)} (hz : ‖zc p‖ = 1) : brA p = brB p := by
  have hle : ‖zc p‖ ≤ 1 := le_of_eq hz
  have hq : ‖((⟨clampC (zc p), norm_clampC_le_one _⟩ : Disk),
      (⟨clampC (uc p), norm_clampC_le_one _⟩ : Disk)).1.1‖ = 1 := by
    show ‖clampC (zc p)‖ = 1
    rw [clampC_of_le_one hle, hz]
  rw [brA, chart_glue hq, brB]
  refine congrArg chart1 (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
  · show (clampC (zc p))⁻¹ = invC (zc p)
    rw [clampC_of_le_one hle, invC_of_one_le (le_of_eq hz.symm)]
  · show (clampC (zc p)) ^ 2 * clampC (uc p) = clampC ((zc p) ^ 2 * uc p)
    rw [clampC_of_le_one hle, clampC_mul_sq hz]

theorem continuous_F : Continuous F :=
  Continuous.if_le continuous_brA continuous_brB (continuous_norm.comp continuous_zc)
    continuous_const (fun _ h => brA_eq_brB h)

/-! ## §4. The chart domain, injectivity, and the embedding -/

/-- The **compact** chart domain: `‖z‖ ≤ 3/2`, `‖u‖ ≤ 1/4`. Large enough in the base direction to
contain the closed hemisphere `‖z‖ ≤ 1` **with room across the weld**; small enough in the fiber
direction that all clamps are inert. -/
def Wset : Set (EuclideanSpace ℝ (Fin 4)) := {p | ‖zc p‖ ≤ 3 / 2 ∧ ‖uc p‖ ≤ 1 / 4}

/-- The **open** chart domain. -/
def Wopen : Set (EuclideanSpace ℝ (Fin 4)) := {p | ‖zc p‖ < 3 / 2 ∧ ‖uc p‖ < 1 / 4}

theorem Wopen_subset_Wset : Wopen ⊆ Wset := fun _ h => ⟨le_of_lt h.1, le_of_lt h.2⟩

theorem isOpen_Wopen : IsOpen Wopen := by
  have h1 : IsOpen {p : EuclideanSpace ℝ (Fin 4) | ‖zc p‖ < 3 / 2} :=
    isOpen_lt (continuous_norm.comp continuous_zc) continuous_const
  have h2 : IsOpen {p : EuclideanSpace ℝ (Fin 4) | ‖uc p‖ < 1 / 4} :=
    isOpen_lt (continuous_norm.comp continuous_uc) continuous_const
  exact h1.inter h2

theorem isClosed_Wset : IsClosed Wset := by
  have h1 : IsClosed {p : EuclideanSpace ℝ (Fin 4) | ‖zc p‖ ≤ 3 / 2} :=
    isClosed_le (continuous_norm.comp continuous_zc) continuous_const
  have h2 : IsClosed {p : EuclideanSpace ℝ (Fin 4) | ‖uc p‖ ≤ 1 / 4} :=
    isClosed_le (continuous_norm.comp continuous_uc) continuous_const
  exact h1.inter h2

theorem isCompact_Wset : IsCompact Wset := by
  refine Metric.isCompact_of_isClosed_isBounded isClosed_Wset ?_
  refine (Metric.isBounded_closedBall (x := (0 : EuclideanSpace ℝ (Fin 4))) (r := 2)).subset
    (fun p hp => ?_)
  have hsq := norm_sq_split p
  have : ‖p‖ ^ 2 ≤ 4 := by nlinarith [norm_nonneg (zc p), norm_nonneg (uc p), hp.1, hp.2]
  simp only [Metric.mem_closedBall, dist_zero_right]
  nlinarith [norm_nonneg p]

/-- On `Wset` the fiber clamp is inert. -/
theorem clampC_uc {p : EuclideanSpace ℝ (Fin 4)} (hp : p ∈ Wset) : clampC (uc p) = uc p :=
  clampC_of_le_one (le_trans hp.2 (by norm_num))

/-- On `Wset` the twisted-fiber clamp is inert too. -/
theorem clampC_sq_mul {p : EuclideanSpace ℝ (Fin 4)} (hp : p ∈ Wset) :
    clampC ((zc p) ^ 2 * uc p) = (zc p) ^ 2 * uc p := by
  refine clampC_of_le_one ?_
  rw [norm_mul, norm_pow]
  nlinarith [norm_nonneg (zc p), norm_nonneg (uc p), hp.1, hp.2]

/-- Inside the base unit disk `F` **is** chart 0. -/
theorem F_inside {p : EuclideanSpace ℝ (Fin 4)} (hp : p ∈ Wset) (h : ‖zc p‖ ≤ 1) :
    F p = chart0 (⟨zc p, h⟩, ⟨uc p, le_trans hp.2 (by norm_num)⟩) := by
  rw [F, if_pos h, brA]
  exact congrArg chart0 (Prod.ext (Subtype.ext (clampC_of_le_one h)) (Subtype.ext (clampC_uc hp)))

/-- Outside it, `F` is chart 1 composed with the clutch. -/
theorem F_outside {p : EuclideanSpace ℝ (Fin 4)} (hp : p ∈ Wset) (h : 1 ≤ ‖zc p‖) :
    F p = chart1 (⟨(zc p)⁻¹, by rw [norm_inv]; exact inv_le_one_of_one_le₀ h⟩,
      ⟨(zc p) ^ 2 * uc p, by
        rw [norm_mul, norm_pow]
        nlinarith [norm_nonneg (zc p), norm_nonneg (uc p), hp.1, hp.2]⟩) := by
  have hb : F p = brB p := by
    rcases eq_or_lt_of_le h with heq | hlt
    · rw [F, if_pos (le_of_eq heq.symm), brA_eq_brB heq.symm]
    · rw [F, if_neg (not_le.mpr hlt)]
  rw [hb, brB]
  exact congrArg chart1
    (Prod.ext (Subtype.ext (invC_of_one_le h)) (Subtype.ext (clampC_sq_mul hp)))

theorem zc_ne_zero_of_one_le {p : EuclideanSpace ℝ (Fin 4)} (h : 1 ≤ ‖zc p‖) : zc p ≠ 0 := by
  intro h0
  rw [h0] at h
  simp at h
  linarith

/-- **`F` is injective on the chart domain.** The three genuinely different cases are: both points
inside the base unit disk (chart-0 injectivity), both outside (chart-1 injectivity plus invertibility
of the clutch), and one of each — which forces both onto the weld circle and so collapses. -/
theorem F_injOn : Set.InjOn F Wset := by
  intro p hp q hq hF
  rcases le_or_gt ‖zc p‖ 1 with hp1 | hp1 <;> rcases le_or_gt ‖zc q‖ 1 with hq1 | hq1
  · rw [F_inside hp hp1, F_inside hq hq1, chart0_inj_iff, Prod.ext_iff] at hF
    exact ext4 (congrArg Subtype.val hF.1) (congrArg Subtype.val hF.2)
  · rw [F_inside hp hp1, F_outside hq (le_of_lt hq1), chart0_eq_chart1_iff] at hF
    obtain ⟨hnorm, hfst, -⟩ := hF
    have hpz : ‖zc p‖ = 1 := hnorm
    have : (zc q)⁻¹ = (zc p)⁻¹ := hfst
    have hqz : zc q = zc p :=
      inv_injective this
    rw [hqz, hpz] at hq1
    exact absurd hq1 (lt_irrefl 1)
  · rw [F_outside hp (le_of_lt hp1), F_inside hq hq1, eq_comm, chart0_eq_chart1_iff] at hF
    obtain ⟨hnorm, hfst, -⟩ := hF
    have hqz : ‖zc q‖ = 1 := hnorm
    have hpz : zc p = zc q := inv_injective (hfst : (zc p)⁻¹ = (zc q)⁻¹)
    rw [hpz, hqz] at hp1
    exact absurd hp1 (lt_irrefl 1)
  · rw [F_outside hp (le_of_lt hp1), F_outside hq (le_of_lt hq1), chart1_inj_iff,
      Prod.ext_iff] at hF
    have hz : zc p = zc q := inv_injective (congrArg Subtype.val hF.1)
    have hu : (zc p) ^ 2 * uc p = (zc q) ^ 2 * uc q := congrArg Subtype.val hF.2
    rw [hz] at hu
    have hne : (zc q) ^ 2 ≠ 0 := pow_ne_zero 2 (zc_ne_zero_of_one_le (le_of_lt hq1))
    exact ext4 hz (mul_left_cancel₀ hne hu)

/-! ## §5. The chart image is open, and `F` is a chart -/

/-- The `ℝ⁴` point with prescribed complex coordinates. -/
def mk4 (z u : ℂ) : EuclideanSpace ℝ (Fin 4) := WithLp.toLp 2 ![z.re, z.im, u.re, u.im]

@[simp] theorem zc_mk4 (z u : ℂ) : zc (mk4 z u) = z := rfl

@[simp] theorem uc_mk4 (z u : ℂ) : uc (mk4 z u) = u := rfl

/-- The **chart image** — an open neighbourhood in `ResE` of the whole closed hemisphere. -/
def Uset : Set ResE := F '' Wopen

/-- Chart-0 points of the image are exactly those with small fiber: the base coordinate is
unconstrained, because `Wopen` reaches past the weld. -/
theorem mem_Uset_chart0 (p : ResChart) : chart0 p ∈ Uset ↔ ‖(p.2 : ℂ)‖ < 1 / 4 := by
  constructor
  · rintro ⟨x, hx, hxe⟩
    rcases le_or_gt ‖zc x‖ 1 with h | h
    · rw [F_inside (Wopen_subset_Wset hx) h, chart0_inj_iff] at hxe
      have : (p.2 : ℂ) = uc x := congrArg (fun r : ResChart => (r.2 : ℂ)) hxe.symm
      rw [this]; exact hx.2
    · exfalso
      rw [F_outside (Wopen_subset_Wset hx) (le_of_lt h), eq_comm, chart0_eq_chart1_iff] at hxe
      obtain ⟨hn, hf, -⟩ := hxe
      have hzx : zc x = (p.1 : ℂ) := inv_injective hf
      rw [hzx, hn] at h
      exact lt_irrefl 1 h
  · intro hp2
    have hz1 : ‖zc (mk4 (p.1 : ℂ) (p.2 : ℂ))‖ ≤ 1 := by rw [zc_mk4]; exact p.1.2
    have hmem : mk4 (p.1 : ℂ) (p.2 : ℂ) ∈ Wopen := by
      refine ⟨?_, ?_⟩
      · rw [zc_mk4]; exact lt_of_le_of_lt p.1.2 (by norm_num)
      · rw [uc_mk4]; exact hp2
    refine ⟨_, hmem, ?_⟩
    rw [F_inside (Wopen_subset_Wset hmem) hz1]
    exact congrArg chart0 (Prod.ext (Subtype.ext (zc_mk4 _ _)) (Subtype.ext (uc_mk4 _ _)))

/-- The chart-1 points of the image: the annular collar `2/3 < ‖w‖ ≤ 1` with a fiber bound that is
the clutch-transported version of `‖u‖ < 1/4`. -/
theorem mem_Uset_chart1 (q : ResChart) :
    chart1 q ∈ Uset ↔ 2 / 3 < ‖(q.1 : ℂ)‖ ∧ ‖(q.1 : ℂ)‖ ^ 2 * ‖(q.2 : ℂ)‖ < 1 / 4 := by
  constructor
  · rintro ⟨x, hx, hxe⟩
    have key : (q.1 : ℂ) = (zc x)⁻¹ ∧ (q.2 : ℂ) = (zc x) ^ 2 * uc x ∧ 1 ≤ ‖zc x‖ := by
      rcases le_or_gt ‖zc x‖ 1 with h | h
      · rw [F_inside (Wopen_subset_Wset hx) h, chart0_eq_chart1_iff] at hxe
        obtain ⟨hn, hf, hs⟩ := hxe
        exact ⟨hf, hs, le_of_eq hn.symm⟩
      · rw [F_outside (Wopen_subset_Wset hx) (le_of_lt h), chart1_inj_iff] at hxe
        refine ⟨(congrArg (fun r : ResChart => (r.1 : ℂ)) hxe).symm,
          (congrArg (fun r : ResChart => (r.2 : ℂ)) hxe).symm, le_of_lt h⟩
    obtain ⟨h1, h2, h3⟩ := key
    have hzpos : (0 : ℝ) < ‖zc x‖ := lt_of_lt_of_le zero_lt_one h3
    have hq1 : ‖(q.1 : ℂ)‖ = ‖zc x‖⁻¹ := by rw [h1, norm_inv]
    constructor
    · rw [hq1]
      rw [lt_inv_comm₀ (by norm_num) hzpos]
      calc ‖zc x‖ < 3 / 2 := hx.1
        _ = (2 / 3 : ℝ)⁻¹ := by norm_num
    · have hq2 : ‖(q.2 : ℂ)‖ = ‖zc x‖ ^ 2 * ‖uc x‖ := by rw [h2, norm_mul, norm_pow]
      rw [hq1, hq2, inv_pow]
      rw [← mul_assoc, inv_mul_cancel₀ (by positivity), one_mul]
      exact hx.2
  · rintro ⟨hb, hf⟩
    have hq1pos : (0 : ℝ) < ‖(q.1 : ℂ)‖ := lt_trans (by norm_num) hb
    have hq1ne : (q.1 : ℂ) ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hq1pos)
    set x : EuclideanSpace ℝ (Fin 4) := mk4 ((q.1 : ℂ)⁻¹) ((q.1 : ℂ) ^ 2 * (q.2 : ℂ)) with hxdef
    have hzx : zc x = (q.1 : ℂ)⁻¹ := by rw [hxdef, zc_mk4]
    have hux : uc x = (q.1 : ℂ) ^ 2 * (q.2 : ℂ) := by rw [hxdef, uc_mk4]
    have hnz : ‖zc x‖ = ‖(q.1 : ℂ)‖⁻¹ := by rw [hzx, norm_inv]
    have hone : 1 ≤ ‖zc x‖ := by
      rw [hnz, le_inv_comm₀ (by norm_num) hq1pos]
      simpa using q.1.2
    have hmem : x ∈ Wopen := by
      refine ⟨?_, ?_⟩
      · rw [hnz, inv_lt_comm₀ hq1pos (by norm_num)]
        calc (3 / 2 : ℝ)⁻¹ = 2 / 3 := by norm_num
          _ < ‖(q.1 : ℂ)‖ := hb
      · rw [hux, norm_mul, norm_pow]; exact hf
    refine ⟨x, hmem, ?_⟩
    rw [F_outside (Wopen_subset_Wset hmem) hone]
    refine congrArg chart1 (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
    · show (zc x)⁻¹ = (q.1 : ℂ)
      rw [hzx, inv_inv]
    · show (zc x) ^ 2 * uc x = (q.2 : ℂ)
      rw [hzx, hux, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hq1ne, one_pow, one_mul]

theorem isOpen_Uset : IsOpen Uset := by
  refine (isQuotientMap_quotient_mk' (s := resSetoid)).isOpen_preimage.mp ?_
  rw [isOpen_sum_iff]
  constructor
  · show IsOpen {p : ResChart | chart0 p ∈ Uset}
    have h : {p : ResChart | chart0 p ∈ Uset} = {p : ResChart | ‖(p.2 : ℂ)‖ < 1 / 4} := by
      ext p; exact mem_Uset_chart0 p
    rw [h]
    exact isOpen_lt (continuous_norm.comp (continuous_subtype_val.comp continuous_snd))
      continuous_const
  · show IsOpen {p : ResChart | chart1 p ∈ Uset}
    have h : {p : ResChart | chart1 p ∈ Uset}
        = {p : ResChart | 2 / 3 < ‖(p.1 : ℂ)‖} ∩
          {p : ResChart | ‖(p.1 : ℂ)‖ ^ 2 * ‖(p.2 : ℂ)‖ < 1 / 4} := by
      ext p; exact mem_Uset_chart1 p
    rw [h]
    refine IsOpen.inter (isOpen_lt continuous_const ?_) (isOpen_lt ?_ continuous_const)
    · exact continuous_norm.comp (continuous_subtype_val.comp continuous_fst)
    · exact ((continuous_norm.comp (continuous_subtype_val.comp continuous_fst)).pow 2).mul
        (continuous_norm.comp (continuous_subtype_val.comp continuous_snd))

theorem isEmbedding_F_Wset : Topology.IsEmbedding (fun x : ↥Wset => F ↑x) := by
  haveI : CompactSpace ↥Wset := isCompact_iff_compactSpace.mp isCompact_Wset
  exact (Continuous.isClosedEmbedding (continuous_F.comp continuous_subtype_val)
    (Set.injOn_iff_injective.mp F_injOn)).isEmbedding

theorem isEmbedding_F_Wopen : Topology.IsEmbedding (fun x : ↥Wopen => F ↑x) :=
  isEmbedding_F_Wset.comp (Topology.IsEmbedding.inclusion Wopen_subset_Wset)

/-- **The extended chart-0 homeomorphism** `Wopen ≃ₜ Uset`. -/
noncomputable def chartHomeo : ↥Wopen ≃ₜ ↥Uset :=
  isEmbedding_F_Wopen.toHomeomorph.trans
    (Homeomorph.setCongr (by rw [Uset, Set.image_eq_range]))

@[simp] theorem chartHomeo_coe (x : ↥Wopen) : ((chartHomeo x : ↥Uset) : ResE) = F ↑x := rfl

/-! ## §6. Rescaling onto `flatDisk 4 2 (1/2)` -/

/-- The rescaled chart target: `Wopen` shrunk by `1/2`, so the hemisphere lands on the radius-`1/2`
flat disk (`StarInBall` needs a radius strictly below `1`). -/
def Vset : Set (EuclideanSpace ℝ (Fin 4)) := {p | ‖zc p‖ < 3 / 4 ∧ ‖uc p‖ < 1 / 8}

theorem isOpen_Vset : IsOpen Vset :=
  (isOpen_lt (continuous_norm.comp continuous_zc) continuous_const).inter
    (isOpen_lt (continuous_norm.comp continuous_uc) continuous_const)

/-- Halving is a self-homeomorphism of `ℝ⁴`. -/
noncomputable def halve : EuclideanSpace ℝ (Fin 4) ≃ₜ EuclideanSpace ℝ (Fin 4) :=
  Homeomorph.smulOfNeZero (2⁻¹ : ℝ) (by norm_num)

@[simp] theorem halve_apply (p : EuclideanSpace ℝ (Fin 4)) : halve p = (2⁻¹ : ℝ) • p := rfl

theorem norm_zc_halve (p : EuclideanSpace ℝ (Fin 4)) : ‖zc (halve p)‖ = 2⁻¹ * ‖zc p‖ := by
  rw [halve_apply, zc_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  norm_num

theorem norm_uc_halve (p : EuclideanSpace ℝ (Fin 4)) : ‖uc (halve p)‖ = 2⁻¹ * ‖uc p‖ := by
  rw [halve_apply, uc_smul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  norm_num

theorem uc_halve_eq_zero_iff (p : EuclideanSpace ℝ (Fin 4)) : uc (halve p) = 0 ↔ uc p = 0 := by
  rw [halve_apply, uc_smul]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h2 | h2
    · exact absurd (Complex.ofReal_eq_zero.mp h2) (by norm_num)
    · exact h2
  · intro h; rw [h, mul_zero]

theorem halve_mem_Vset_iff (p : EuclideanSpace ℝ (Fin 4)) : p ∈ Wopen ↔ halve p ∈ Vset := by
  simp only [Wopen, Vset, Set.mem_setOf_eq, norm_zc_halve, norm_uc_halve]
  constructor
  · rintro ⟨h1, h2⟩; constructor <;> linarith
  · rintro ⟨h1, h2⟩; constructor <;> linarith

/-- **The rescaled chart** `Uset ≃ₜ Vset`. -/
noncomputable def chartHomeoV : ↥Uset ≃ₜ ↥Vset :=
  chartHomeo.symm.trans (halve.subtype halve_mem_Vset_iff)

theorem chartHomeoV_coe (u : ↥Uset) : ((chartHomeoV u : ↥Vset) : EuclideanSpace ℝ (Fin 4))
    = halve ↑(chartHomeo.symm u) := rfl

theorem flatDisk_subset_Vset : flatDisk 4 2 (1 / 2) ⊆ Vset := by
  intro p hp
  obtain ⟨hu, hz⟩ := (mem_flatDisk_iff p).mp hp
  refine ⟨by linarith, ?_⟩
  rw [hu, norm_zero]; norm_num

/-! ## §7. The hemispheres -/

/-- The **closed chart-0 hemisphere** of the zero section (`{w = 0, ‖z‖ ≤ 1}` in chart 0). -/
def hemi0 : Set ResE := Set.range (fun z : Disk => chart0 (zeroPt z))

/-- The **closed chart-1 hemisphere**. -/
def hemi1 : Set ResE := Set.range (fun z : Disk => chart1 (zeroPt z))

theorem isCompact_hemi0 : IsCompact hemi0 :=
  isCompact_range (continuous_chart0.comp (Continuous.prodMk continuous_id continuous_const))

theorem isCompact_hemi1 : IsCompact hemi1 :=
  isCompact_range (continuous_chart1.comp (Continuous.prodMk continuous_id continuous_const))

theorem isClosed_hemi0 : IsClosed hemi0 := isCompact_hemi0.isClosed

theorem isClosed_hemi1 : IsClosed hemi1 := isCompact_hemi1.isClosed

theorem hemi0_subset_Uset : hemi0 ⊆ Uset := by
  rintro _ ⟨z, rfl⟩
  refine (mem_Uset_chart0 (zeroPt z)).mpr ?_
  show ‖((zeroFiber : Disk) : ℂ)‖ < 1 / 4
  simp [zeroFiber]

/-- **The hemisphere is the flat 2-disk of the chart.** -/
theorem chartHomeoV_mem_flatDisk (u : ↥Uset) :
    ((chartHomeoV u : ↥Vset) : EuclideanSpace ℝ (Fin 4)) ∈ flatDisk 4 2 (1 / 2)
      ↔ (u : ResE) ∈ hemi0 := by
  set x : ↥Wopen := chartHomeo.symm u with hx
  have hux : (u : ResE) = F ↑x := by rw [hx, ← chartHomeo_coe, Homeomorph.apply_symm_apply]
  rw [chartHomeoV_coe, ← hx, mem_flatDisk_iff, norm_zc_halve]
  rw [uc_halve_eq_zero_iff, hux]
  constructor
  · rintro ⟨hu0, hz⟩
    have hzle : ‖zc (x : EuclideanSpace ℝ (Fin 4))‖ ≤ 1 := by linarith
    refine ⟨⟨zc (x : EuclideanSpace ℝ (Fin 4)), hzle⟩, ?_⟩
    show chart0 (zeroPt ⟨zc (x : EuclideanSpace ℝ (Fin 4)), hzle⟩) = F ↑x
    rw [F_inside (Wopen_subset_Wset x.2) hzle]
    -- v4.32: `simp` no longer delta-unfolds the plain def `zeroPt`, so `(zeroPt _).2` never
    -- reduces to `zeroFiber` and the `zeroFiber` rewrite has nothing to fire on. Name both.
    exact congrArg chart0 (Prod.ext rfl (Subtype.ext (by simpa [zeroPt, zeroFiber] using hu0.symm)))
  · rintro ⟨z, hz0⟩
    replace hz0 : chart0 (zeroPt z) = F ↑x := hz0
    rcases le_or_gt ‖zc (x : EuclideanSpace ℝ (Fin 4))‖ 1 with h | h
    · rw [F_inside (Wopen_subset_Wset x.2) h, chart0_inj_iff] at hz0
      have h1 : zc (x : EuclideanSpace ℝ (Fin 4)) = (z : ℂ) :=
        (congrArg (fun r : ResChart => (r.1 : ℂ)) hz0).symm
      have h2 : uc (x : EuclideanSpace ℝ (Fin 4)) = 0 := by
        have := (congrArg (fun r : ResChart => (r.2 : ℂ)) hz0).symm
        -- Same v4.32 `zeroPt` delta-unfolding gap as above.
        simpa [zeroPt, zeroFiber] using this
      refine ⟨h2, ?_⟩
      rw [h1]
      have := z.2
      linarith
    · exfalso
      rw [F_outside (Wopen_subset_Wset x.2) (le_of_lt h), chart0_eq_chart1_iff] at hz0
      obtain ⟨hn, hf, -⟩ := hz0
      have hzz : zc (x : EuclideanSpace ℝ (Fin 4)) = (z : ℂ) := inv_injective hf
      have hn' : ‖(z : ℂ)‖ = 1 := hn
      rw [hzz, hn'] at h
      exact lt_irrefl 1 h

/-! ## §8. The chart-0 hemisphere is locally-homologically invisible -/

/-- **`H₂(ResE | hemi0) = H₃(ResE | hemi0) = 0`.** The closed chart-0 hemisphere of the zero section
is a flat 2-disk in a 4-chart of `ResE`, so its local homology vanishes in the two degrees the
local-homology Mayer–Vietoris consumes at `n = 2`. -/
theorem relHomology_hemi0_eq_zero (j : ℕ) (hj : j ≤ 1)
    (x : RelHomologyInt (X := TopCat.of ResE) hemi0ᶜ (j + 2)) : x = 0 :=
  SingularFlatDiskChartVanishInt.relHomology_flatDiskChart_four_eq_zero
    (M := TopCat.of ResE) isClosed_hemi0 isOpen_Uset hemi0_subset_Uset isOpen_Vset
    flatDisk_subset_Vset chartHomeoV chartHomeoV_mem_flatDisk j hj x

/-! ## §9. The chart-swap involution, and the second hemisphere for free -/

/-- The weld relation is **symmetric in the two charts**: `glued p q` iff `glued q p`. This is what
makes the chart swap well defined, and it is exactly the involutivity of the clutch. -/
theorem glued_symm {p q : ResChart} (h : glued p q) : glued q p := by
  obtain ⟨h1, h2, h3⟩ := h
  have hp0 : (p.1 : ℂ) ≠ 0 := by
    refine norm_ne_zero_iff.mp ?_
    rw [h1]; norm_num
  refine ⟨?_, ?_, ?_⟩
  · rw [h2, norm_inv, h1, inv_one]
  · rw [h2, inv_inv]
  · rw [h2, h3, inv_pow, inv_mul_cancel_left₀ (pow_ne_zero 2 hp0)]

/-- **The chart-swap map** `ResE → ResE`: `chart0 p ↦ chart1 p`, `chart1 p ↦ chart0 p`. -/
def swapE : ResE → ResE :=
  Quotient.lift (Sum.elim chart1 chart0) (by
    rintro a b (rfl | hg)
    · rfl
    · cases a with
      | inl p =>
        cases b with
        | inl _ => exact (hg : False).elim
        | inr q => exact (chart0_eq_chart1_iff.mpr (glued_symm hg)).symm
      | inr q =>
        cases b with
        | inl p => exact chart0_eq_chart1_iff.mpr (glued_symm hg)
        | inr _ => exact (hg : False).elim)

@[simp] theorem swapE_chart0 (p : ResChart) : swapE (chart0 p) = chart1 p := rfl
@[simp] theorem swapE_chart1 (p : ResChart) : swapE (chart1 p) = chart0 p := rfl

theorem continuous_swapE : Continuous swapE :=
  Continuous.quotient_lift (Continuous.sumElim continuous_chart1 continuous_chart0) _

theorem swapE_involutive : Function.Involutive swapE := by
  intro y
  obtain ⟨a, rfl⟩ := Quotient.exists_rep y
  cases a with
  | inl p => rfl
  | inr p => rfl

/-- The chart swap as a self-homeomorphism of `ResE`. -/
def swapHomeo : ResE ≃ₜ ResE where
  toFun := swapE
  invFun := swapE
  left_inv := swapE_involutive
  right_inv := swapE_involutive
  continuous_toFun := continuous_swapE
  continuous_invFun := continuous_swapE

@[simp] theorem swapHomeo_apply (y : ResE) : swapHomeo y = swapE y := rfl

theorem hemi1_eq_preimage : hemi1 = swapE ⁻¹' hemi0 := by
  ext y
  constructor
  · rintro ⟨z, rfl⟩
    exact ⟨z, rfl⟩
  · rintro ⟨z, hz⟩
    replace hz : chart0 (zeroPt z) = swapE y := hz
    refine ⟨z, ?_⟩
    have h2 : swapE (chart0 (zeroPt z)) = swapE (swapE y) := congrArg swapE hz
    rw [swapE_involutive y, swapE_chart0] at h2
    exact h2

/-- The transported chart domain around the chart-1 hemisphere. -/
def Uset1 : Set ResE := swapE ⁻¹' Uset

theorem isOpen_Uset1 : IsOpen Uset1 := isOpen_Uset.preimage continuous_swapE

theorem hemi1_subset_Uset1 : hemi1 ⊆ Uset1 := by
  rw [hemi1_eq_preimage]
  exact fun _ hy => hemi0_subset_Uset hy

/-- **The chart-1 hemisphere chart**, obtained from the chart-0 one by the swap. -/
noncomputable def chartHomeoV1 : ↥Uset1 ≃ₜ ↥Vset :=
  (swapHomeo.subtype (p := fun y => y ∈ Uset1) (q := fun y => y ∈ Uset)
    (fun _ => Iff.rfl)).trans chartHomeoV

theorem chartHomeoV1_mem_flatDisk (u : ↥Uset1) :
    ((chartHomeoV1 u : ↥Vset) : EuclideanSpace ℝ (Fin 4)) ∈ flatDisk 4 2 (1 / 2)
      ↔ (u : ResE) ∈ hemi1 := by
  rw [hemi1_eq_preimage]
  exact chartHomeoV_mem_flatDisk _

/-- **`H₂(ResE | hemi1) = H₃(ResE | hemi1) = 0`** — the swapped twin of `relHomology_hemi0_eq_zero`.
No second chart had to be built: `swapHomeo` transports the chart-0 one. -/
theorem relHomology_hemi1_eq_zero (j : ℕ) (hj : j ≤ 1)
    (x : RelHomologyInt (X := TopCat.of ResE) hemi1ᶜ (j + 2)) : x = 0 :=
  SingularFlatDiskChartVanishInt.relHomology_flatDiskChart_four_eq_zero
    (M := TopCat.of ResE) isClosed_hemi1 isOpen_Uset1 hemi1_subset_Uset1 isOpen_Vset
    flatDisk_subset_Vset chartHomeoV1 chartHomeoV1_mem_flatDisk j hj x

/-! ## §10. The Mayer–Vietoris assembly: `H₃(ResE | equator) ≅ H₂(ResE | S²)` -/

/-- The **equator circle** of the zero section — the weld locus of the two hemispheres. -/
def equatorE : Set ResE := {y | ∃ z : Disk, ‖(z : ℂ)‖ = 1 ∧ y = chart0 (zeroPt z)}

/-- The two hemispheres **cover the zero section**. -/
theorem hemi_union : hemi0 ∪ hemi1 = zeroLocus := by
  ext y
  constructor
  · rintro (⟨z, hz⟩ | ⟨z, hz⟩)
    · exact ⟨z, Or.inl hz.symm⟩
    · exact ⟨z, Or.inr hz.symm⟩
  · rintro ⟨z, hz | hz⟩
    · exact Or.inl ⟨z, hz.symm⟩
    · exact Or.inr ⟨z, hz.symm⟩

/-- The two hemispheres **meet exactly in the equator**. -/
theorem hemi_inter : hemi0 ∩ hemi1 = equatorE := by
  ext y
  constructor
  · rintro ⟨⟨z, hz⟩, ⟨z', hz'⟩⟩
    replace hz : chart0 (zeroPt z) = y := hz
    replace hz' : chart1 (zeroPt z') = y := hz'
    have hglue : glued (zeroPt z) (zeroPt z') :=
      chart0_eq_chart1_iff.mp (hz.trans hz'.symm)
    exact ⟨z, hglue.1, hz.symm⟩
  · rintro ⟨z, hz1, rfl⟩
    refine ⟨⟨z, rfl⟩, ?_⟩
    have hzz : ‖((zeroPt z).1 : ℂ)‖ = 1 := hz1
    refine ⟨⟨(z : ℂ)⁻¹, by rw [norm_inv, hz1, inv_one]⟩, ?_⟩
    rw [chart_glue hzz]
    refine congrArg chart1 (Prod.ext rfl (Subtype.ext ?_))
    show ((zeroFiber : Disk) : ℂ) = ((z : ℂ) ^ 2 * ((zeroFiber : Disk) : ℂ))
    simp [zeroFiber]

/-- **`H₃(ResE | equator) ≅ H₂(ResE | S²)`** — the local-homology Mayer–Vietoris step of Hatcher's
Lemma 3.36, now *concrete* for the Kummer resolution piece: the two closed hemispheres of the zero
section are flat 2-disks in 4-charts (§7–§9), so both vanishing hypotheses hold in degrees `2` and
`3`, and the connecting map is an isomorphism from the local homology of their intersection (the
equator circle) to that of their union (the whole embedded `S²`). -/
noncomputable def localMvEquatorEquiv :
    RelHomologyInt (X := TopCat.of ResE) equatorEᶜ 3 ≃ₗ[ℤ]
      RelHomologyInt (X := TopCat.of ResE) zeroLocusᶜ 2 :=
  ((SingularRelativeMVLESInt.relHomologyIntCongr (X := TopCat.of ResE)
      (show (equatorEᶜ : Set ResE) = (hemi0 ∩ hemi1)ᶜ by rw [hemi_inter]) 3).trans
    (SingularRelativeMVLESInt.localMvDeltaEquivInt (X := TopCat.of ResE) hemi0 hemi1
      isClosed_hemi0.isOpen_compl isClosed_hemi1.isOpen_compl 2
      (relHomology_hemi0_eq_zero 0 (by norm_num))
      (relHomology_hemi1_eq_zero 0 (by norm_num))
      (relHomology_hemi0_eq_zero 1 (by norm_num))
      (relHomology_hemi1_eq_zero 1 (by norm_num)))).trans
    (SingularRelativeMVLESInt.relHomologyIntCongr (X := TopCat.of ResE)
      (show ((hemi0 ∪ hemi1)ᶜ : Set ResE) = zeroLocusᶜ by rw [hemi_union]) 2)

/-- The zero section's image is the locus the MV step computes: `zeroLocus = range zeroSection`, so
`localMvEquatorEquiv` really is `H₃(ResE | equator) ≅ H₂(ResE | S²)` for the **embedded** `S²`. -/
theorem zeroLocus_eq_range_zeroSection : zeroLocus = Set.range zeroSection :=
  range_zeroSection_eq_zeroLocus.symm

end SKEFTHawking.KummerHemisphereChartInt
