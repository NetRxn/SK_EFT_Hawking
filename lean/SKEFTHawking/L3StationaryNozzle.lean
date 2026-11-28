import Mathlib
import SKEFTHawking.AcousticMetric

/-!
# The local stationary Laval-nozzle throat

The fluid equations below are the stationary constant-sound-speed equations
(4.1) and (4.4) of Balbinot, Fagnocchi and Fabbri (gr-qc/0405098v2).
The four-dimensional geometry is the effective transverse lift of their
Painlevé–Gullstrand block.
-/

namespace SKEFTHawking.L3StationaryNozzle

open Filter Set
open scoped Topology
open AcousticMetric

noncomputable section

/-- The longitudinal PG coordinates and two Euclidean transverse coordinates. -/
abbrev Axis := Fin 2 ⊕ Fin 2

abbrev timeAxis : Axis := .inl 0
abbrev axialAxis : Axis := .inl 1
abbrev transverseAxis : Axis := .inr 0

/-- The transverse lift with positive conformal factor `f`. -/
def liftMetric (v c f : ℝ) : Matrix Axis Axis ℝ :=
  Matrix.fromBlocks (acousticMetric v c (f * c)) 0 0 (f • (1 : Matrix (Fin 2) (Fin 2) ℝ))

/-- The inverse of the transverse lift. -/
def liftInverse (v c f : ℝ) : Matrix Axis Axis ℝ :=
  Matrix.fromBlocks (acousticMetricInv v c (f * c)) 0 0
    (f⁻¹ • (1 : Matrix (Fin 2) (Fin 2) ℝ))

theorem lift_inverse (v c f : ℝ) (hc : c ≠ 0) (hf : f ≠ 0) :
    liftMetric v c f * liftInverse v c f = 1 := by
  rw [liftMetric, liftInverse, Matrix.fromBlocks_multiply]
  simp [acousticMetric_inv_correct v c (f * c) hc (mul_ne_zero hf hc),
    smul_smul, hf]

/-- The coordinate time vector. -/
def timeVector (i : Axis) : ℝ := if i = timeAxis then 1 else 0

/-- The coordinate covector `dz`. -/
def axialCovector (i : Axis) : ℝ := if i = axialAxis then 1 else 0

/-- The null hypersurface in the laboratory coordinates. -/
def sonicSurface : Set (Axis → ℝ) := {q | q axialAxis = 0}

/-- A spatial cut of the null hypersurface at fixed laboratory time. -/
def sonicCut (t : ℝ) : Set (Axis → ℝ) := sonicSurface ∩ {q | q timeAxis = t}

theorem sonic_normal (c f : ℝ) (hc : c ≠ 0) (hf : f ≠ 0) (i : Axis) :
    liftMetric (-c) c f i timeAxis = (f * c) * axialCovector i ∧
    liftInverse (-c) c f i axialAxis = (f * c)⁻¹ * timeVector i := by
  rcases i with i | i <;> fin_cases i <;>
    norm_num [liftMetric, liftInverse, acousticMetric, acousticMetricInv, axialCovector,
      timeVector, timeAxis, axialAxis, hc, hf] <;> (try field_simp) <;> simp

/-- Time-independent lift in the coordinates `(t,z,y,x)`, allowing transverse variation in y. -/
def stationaryMetric (c : ℝ) (v f : ℝ → ℝ → ℝ) (q : Axis → ℝ) : Matrix Axis Axis ℝ :=
  liftMetric (v (q axialAxis) (q transverseAxis)) c (f (q axialAxis) (q transverseAxis))

/-- The squared norm of the time translation field. -/
def timeNorm (c : ℝ) (v f : ℝ → ℝ → ℝ) (z y : ℝ) : ℝ :=
  f z y * ((v z y) ^ 2 - c ^ 2)

theorem stationaryMetric_timeNorm (c : ℝ) (hc : c ≠ 0) (v f : ℝ → ℝ → ℝ)
    (q : Axis → ℝ) :
    stationaryMetric c v f q timeAxis timeAxis =
      timeNorm c v f (q axialAxis) (q transverseAxis) := by
  simp [stationaryMetric, liftMetric, acousticMetric, timeNorm, timeAxis, hc]

/-- The stationary Christoffel column `Γ^i_tt = -g^{ij}∂_j(g_tt)/2`.
The t and x partial derivatives are identically zero. -/
def stationaryColumn (c : ℝ) (v f : ℝ → ℝ → ℝ) (z y : ℝ) (i : Axis) : ℝ :=
  let gInv := liftInverse (v z y) c (f z y)
  show ℝ from -(gInv i axialAxis * deriv (fun z' ↦ timeNorm c v f z' y) z +
    gInv i transverseAxis * deriv (timeNorm c v f z) y) / 2

theorem stationary_nonaffinity (c : ℝ) (hc : c ≠ 0) (v f : ℝ → ℝ → ℝ)
    (y s : ℝ) (hf : f 0 y ≠ 0) (hsonic : ∀ y', v 0 y' = -c)
    (hvz : HasDerivAt (fun z ↦ v z y) s 0) (hfz : DifferentiableAt ℝ (fun z ↦ f z y) 0)
    (i : Axis) :
    stationaryColumn c v f 0 y i = s * timeVector i := by
  have hz : HasDerivAt (fun z ↦ timeNorm c v f z y) (-2 * f 0 y * c * s) 0 := by
    convert hfz.hasDerivAt.mul ((hvz.pow 2).sub_const (c ^ 2)) using 1 <;>
      first | rfl | (simp only [Pi.pow_apply, hsonic y]; ring)
  have hy : deriv (timeNorm c v f 0) y = 0 := by
    have h : timeNorm c v f 0 = fun _ ↦ 0 := by
      funext y'
      simp [timeNorm, hsonic]
    rw [h, deriv_const]
  simp only [stationaryColumn, hz.deriv, hy, mul_zero, add_zero, hsonic y,
    (sonic_normal c (f 0 y) hc hf i).2]
  field_simp

/-- Source acceleration normalization, with `s` measured in laboratory time. -/
def sourceAcceleration (c s : ℝ) : ℝ := c * s

/-- Source inverse-length normalization (Balbinot et al., Eq. (4.17)). -/
def sourceInverseLength (c s : ℝ) : ℝ := sourceAcceleration c s / c ^ 2

/-- Under constant rescaling of the generator, its connection column scales quadratically. -/
theorem normalized_nonaffinity (c s : ℝ) (hc : c ≠ 0) (i : Axis) :
    c⁻¹ ^ 2 * (s * timeVector i) = (s / c) * (c⁻¹ * timeVector i) ∧
    sourceInverseLength c s = s / c := by
  constructor
  · field_simp
  · unfold sourceInverseLength sourceAcceleration
    field_simp

/-- Transverse variation changes the nonaffinity of this geometric control. -/
theorem transverse_control (c : ℝ) (hc : c ≠ 0) (y : ℝ) (i : Axis) :
    stationaryColumn c (fun z y ↦ -c + (1 + y ^ 2) * z) (fun _ _ ↦ 1) 0 y i =
      (1 + y ^ 2) * timeVector i := by
  apply stationary_nonaffinity c hc _ _ y _ one_ne_zero
  · simp
  · simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (1 + y ^ 2)).const_add (-c)
  · fun_prop

theorem transverse_control_distinct (c : ℝ) (hc : c ≠ 0) :
    stationaryColumn c (fun z y ↦ -c + (1 + y ^ 2) * z) (fun _ _ ↦ 1) 0 0 timeAxis = 1 ∧
    stationaryColumn c (fun z y ↦ -c + (1 + y ^ 2) * z) (fun _ _ ↦ 1) 0 1 timeAxis = 2 := by
  constructor <;> rw [transverse_control c hc] <;> norm_num [timeVector]

/-- A local analytic inverse with the derivative and both the needed point and germ identities. -/
private theorem analytic_inverse {g : ℝ → ℝ} {x d : ℝ} (hg : AnalyticAt ℝ g x)
    (hd : HasDerivAt g d x) (hd0 : d ≠ 0) :
    ∃ j : ℝ → ℝ, AnalyticAt ℝ j (g x) ∧ j (g x) = x ∧ HasDerivAt j d⁻¹ (g x) ∧
      (∀ᶠ y in 𝓝 (g x), g (j y) = y) := by
  have hn : deriv g x ≠ 0 := hd.deriv ▸ hd0
  let j := HasStrictDerivAt.localInverse g (deriv g x) x hg.hasStrictDerivAt hn
  refine ⟨j, hg.analyticAt_localInverse hn, ?_, ?_, ?_⟩
  · have h : (fun z ↦ j (g z)) =ᶠ[𝓝 x] id :=
      hg.hasStrictDerivAt.eventually_left_inverse hn
    exact h.eq_of_nhds
  · simpa only [j, hd.deriv] using (hg.hasStrictDerivAt.to_localInverse hn).hasDerivAt
  · exact hg.hasStrictDerivAt.eventually_right_inverse hn

private def profileExp (w : ℝ) : ℝ := Real.exp ((w ^ 2 - 1) / 2)

/-- The normalized area ratio minus one as a function of normalized speed. -/
def areaProfile (w : ℝ) : ℝ := profileExp w / w - 1

private theorem profileExp_hasDerivAt (w : ℝ) :
    HasDerivAt profileExp (profileExp w * w) w := by
  have hd : HasDerivAt (fun x : ℝ ↦ (x ^ 2 - 1) / 2) w w := by
    convert (((hasDerivAt_id w).pow 2).sub_const 1).div_const 2 using 1 <;>
      first | rfl | simp
  exact (Real.hasDerivAt_exp _).comp w hd

private theorem areaProfile_hasDerivAt (w : ℝ) (hw : w ≠ 0) :
    HasDerivAt areaProfile (profileExp w - profileExp w / w ^ 2) w := by
  convert (((profileExp_hasDerivAt w).div (hasDerivAt_id w) hw).sub_const 1) using 1 <;>
    first | rfl | simp only [id_eq]; field_simp

private theorem areaProfile_at_one : areaProfile 1 = 0 := by
  norm_num [areaProfile, profileExp]

private theorem areaProfile_analytic : AnalyticAt ℝ areaProfile 1 := by
  have h : AnalyticAt ℝ (fun w : ℝ ↦ (w ^ 2 - 1) / 2) 1 := by fun_prop
  apply ((h.rexp.div analyticAt_id one_ne_zero).sub
    (analyticAt_const : AnalyticAt ℝ (fun _ : ℝ ↦ (1 : ℝ)) 1)).congr
  exact Filter.Eventually.of_forall (fun w ↦ rfl)

private theorem areaProfile_deriv_one : deriv areaProfile 1 = 0 := by
  rw [(areaProfile_hasDerivAt 1 one_ne_zero).deriv]
  norm_num

private theorem areaProfile_second_one : iteratedDeriv 2 areaProfile 1 = 2 := by
  have he : deriv areaProfile =ᶠ[𝓝 (1 : ℝ)] fun w ↦ profileExp w - profileExp w / w ^ 2 := by
    filter_upwards [continuousAt_id.eventually_ne (one_ne_zero : (1 : ℝ) ≠ 0)] with w hw
    exact (areaProfile_hasDerivAt w hw).deriv
  have hd : HasDerivAt (fun w ↦ profileExp w - profileExp w / w ^ 2) 2 1 := by
    convert (profileExp_hasDerivAt 1).sub
      ((profileExp_hasDerivAt 1).div ((hasDerivAt_id (1 : ℝ)).pow 2) (by norm_num)) using 1 <;>
      first | rfl | norm_num [profileExp]
  rw [show (2 : ℕ) = 1 + 1 by decide, iteratedDeriv_succ, iteratedDeriv_one,
    he.deriv_eq, hd.deriv]

/-- First and second derivatives of a local quadratic factor at its zero. -/
private theorem quadratic_factor_jet {u a : ℝ → ℝ} {x : ℝ} (h0 : u x = 0)
    (hu : ContDiffAt ℝ 2 u x) (ha : ContDiffAt ℝ 2 a x) :
    deriv (fun z ↦ (u z * u z) * a z) x = 0 ∧
    iteratedDeriv 2 (fun z ↦ (u z * u z) * a z) x = 2 * deriv u x ^ 2 * a x := by
  have hdu := (hu.differentiableAt (by norm_num)).hasDerivAt
  have hda := (ha.differentiableAt (by norm_num)).hasDerivAt
  have hd0 : deriv (u * u) x = 0 := by
    rw [(hdu.mul hdu).deriv]
    simp [h0]
  have hd2 : iteratedDeriv 2 (u * u) x = 2 * deriv u x ^ 2 := by
    rw [iteratedDeriv_mul (n := 2) hu hu]
    norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, h0]
    ring
  constructor
  · change deriv ((u * u) * a) x = 0
    rw [((hdu.mul hdu).mul hda).deriv]
    simp [h0]
  · change iteratedDeriv 2 ((u * u) * a) x = _
    rw [iteratedDeriv_mul (n := 2) (f := u * u) (hu.mul hu) ha]
    norm_num [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_one, h0, hd0, hd2]

/-- The divided profile extends analytically across the sonic point with value one. -/
private theorem areaProfile_factor :
    ∃ a : ℝ → ℝ, AnalyticAt ℝ a 1 ∧ a 1 = 1 ∧
      (areaProfile =ᶠ[𝓝 (1 : ℝ)] fun w ↦ ((w - 1) * (w - 1)) * a w) := by
  have hlo : (2 : ℕ∞) ≤ analyticOrderAt areaProfile 1 := by
    apply (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero areaProfile_analytic).2
    intro i hi
    interval_cases i
    · simpa only [iteratedDeriv_zero] using areaProfile_at_one
    · simpa only [iteratedDeriv_one] using areaProfile_deriv_one
  have hhi : ¬ (3 : ℕ∞) ≤ analyticOrderAt areaProfile 1 := by
    intro h
    have h2 := (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero
      areaProfile_analytic).1 h 2 (by decide)
    rw [areaProfile_second_one] at h2
    norm_num at h2
  have ho : analyticOrderAt areaProfile 1 = (2 : ℕ∞) :=
    le_antisymm ((ENat.lt_add_one_iff (by norm_num : (2 : ℕ∞) ≠ ⊤)).1 (lt_of_not_ge hhi)) hlo
  obtain ⟨a, ha, _, hfact⟩ := areaProfile_analytic.analyticOrderAt_eq_natCast.1 ho
  have hh : areaProfile =ᶠ[𝓝 (1 : ℝ)] fun w ↦ ((w - 1) * (w - 1)) * a w := by
    filter_upwards [hfact] with w hw
    simpa only [pow_two, smul_eq_mul] using hw
  refine ⟨a, ha, ?_, hh⟩
  have hjet := (quadratic_factor_jet (u := fun w : ℝ ↦ w - 1) (by norm_num)
    (by fun_prop) ha.contDiffAt).2
  have hdu : deriv (fun w : ℝ ↦ w - 1) 1 = 1 := ((hasDerivAt_id 1).sub_const 1).deriv
  rw [← hh.iteratedDeriv_eq 2, areaProfile_second_one, hdu] at hjet
  linarith

private theorem positive_analytic_root {a : ℝ → ℝ} (ha : AnalyticAt ℝ a 1)
    (ha1 : a 1 = 1) :
    ∃ r : ℝ → ℝ, AnalyticAt ℝ r 1 ∧ r 1 = 1 ∧
      ∀ᶠ w in 𝓝 (1 : ℝ), 0 < r w ∧ r w ^ 2 = a w := by
  obtain ⟨j, hj, hj1, _, hsq⟩ := analytic_inverse (g := fun x : ℝ ↦ x ^ 2)
    (x := 1) (d := 2) (by fun_prop)
    (by convert (hasDerivAt_id (1 : ℝ)).pow 2 using 1 <;> first | rfl | norm_num) (by norm_num)
  simp only [one_pow] at hj hj1 hsq
  let r := j ∘ a
  have hr : AnalyticAt ℝ r 1 := hj.comp_of_eq ha ha1
  have hr1 : r 1 = 1 := by simp [r, ha1, hj1]
  have ht : Tendsto a (𝓝 1) (𝓝 1) := by
    have h : Tendsto a (𝓝 1) (𝓝 (a 1)) := ha.continuousAt
    rwa [ha1] at h
  refine ⟨r, hr, hr1, ?_⟩
  have hpos : ∀ᶠ w in 𝓝 (1 : ℝ), 0 < r w :=
    hr.continuousAt (show Ioi (0 : ℝ) ∈ 𝓝 (r 1) from Ioi_mem_nhds (by simp [hr1]))
  exact hpos.and (ht.eventually hsq)

/-- Local analytic speed on the oriented transonic branch. -/
private theorem normalized_speed (p : ℝ) (hp : 0 < p) :
    ∃ w : ℝ → ℝ, AnalyticAt ℝ w 0 ∧ w 0 = 1 ∧ HasDerivAt w (-p) 0 ∧
      ∀ᶠ z in 𝓝 (0 : ℝ), 0 < w z ∧ areaProfile (w z) = (p * z) ^ 2 ∧
        (z < 0 → 1 < w z) ∧ (0 < z → w z < 1) := by
  obtain ⟨a, ha, ha1, hf⟩ := areaProfile_factor
  obtain ⟨r, hr, hr1, hrsq⟩ := positive_analytic_root ha ha1
  let M : ℝ → ℝ := fun w ↦ (w - 1) * r w
  have hM : AnalyticAt ℝ M 1 := by
    exact (show AnalyticAt ℝ (fun w : ℝ ↦ w - 1) 1 by fun_prop).mul hr
  have hM0 : M 1 = 0 := by simp [M]
  have hM' : HasDerivAt M 1 1 := by
    simpa [M, hr1] using ((hasDerivAt_id (1 : ℝ)).sub_const 1).fun_mul
      hr.hasStrictDerivAt.hasDerivAt
  obtain ⟨j, hj, hj0, hj', hjinv⟩ := analytic_inverse hM hM' one_ne_zero
  rw [hM0] at hj hj0 hj' hjinv
  let u : ℝ → ℝ := fun z ↦ -p * z
  let w := j ∘ u
  have hu : AnalyticAt ℝ u 0 := by dsimp [u]; fun_prop
  have hu0 : u 0 = 0 := by simp [u]
  have hw : AnalyticAt ℝ w 0 := hj.comp_of_eq hu hu0
  have hw0 : w 0 = 1 := by simp [w, hu0, hj0]
  have hu' : HasDerivAt u (-p) 0 := by
    simpa [u] using ((hasDerivAt_id (0 : ℝ)).const_mul (-p))
  have hw' : HasDerivAt w (-p) 0 := by
    simpa [w, hu0] using (show HasDerivAt j (1 : ℝ) (u 0) by simpa [hu0] using hj').comp 0 hu'
  have hut : Tendsto u (𝓝 0) (𝓝 0) := by
    have h : Tendsto u (𝓝 0) (𝓝 (u 0)) := hu.continuousAt
    rwa [hu0] at h
  have hwt : Tendsto w (𝓝 0) (𝓝 1) := by
    have h : Tendsto w (𝓝 0) (𝓝 (w 0)) := hw.continuousAt
    rwa [hw0] at h
  have hwpos : ∀ᶠ z in 𝓝 (0 : ℝ), 0 < w z :=
    hwt (show Ioi (0 : ℝ) ∈ 𝓝 (1 : ℝ) from Ioi_mem_nhds zero_lt_one)
  refine ⟨w, hw, hw0, hw', ?_⟩
  filter_upwards [hwpos, hwt.eventually hf, hwt.eventually hrsq, hut.eventually hjinv]
    with z hzpos hzf hzr hzi
  change M (w z) = -p * z at hzi
  have hs : (w z - 1) * r (w z) = -p * z := hzi
  refine ⟨hzpos, ?_, ?_, ?_⟩
  · calc
      areaProfile (w z) = (w z - 1) * (w z - 1) * a (w z) := hzf
      _ = ((w z - 1) * r (w z)) ^ 2 := by rw [← hzr.2]; ring
      _ = (p * z) ^ 2 := by rw [hs]; ring
  · intro hz
    have hprod : 0 < (w z - 1) * r (w z) := by
      rw [hs]
      exact mul_pos_of_neg_of_neg (neg_lt_zero.mpr hp) hz
    exact sub_pos.mp (pos_of_mul_pos_left hprod hzr.1.le)
  · intro hz
    have hprod : (w z - 1) * r (w z) < 0 := by
      rw [hs]
      exact mul_neg_of_neg_of_pos (neg_lt_zero.mpr hp) hz
    exact sub_neg.mp (neg_of_mul_neg_left hprod hzr.1.le)

/-- The positive quadratic waist has an analytic stationary transonic solution. -/
theorem analytic_transonic_nozzle (c A₀ β ρ₀ : ℝ) (hc : 0 < c) (hA : 0 < A₀)
    (hβ : 0 < β) (hρ : 0 < ρ₀) :
    ∃ v ρ : ℝ → ℝ, AnalyticAt ℝ v 0 ∧ AnalyticAt ℝ ρ 0 ∧ v 0 = -c ∧
      HasDerivAt v (c * Real.sqrt (β / A₀)) 0 ∧
      ∀ᶠ z in 𝓝 (0 : ℝ), 0 < ρ z ∧ v z < 0 ∧
        (A₀ + β * z ^ 2) * ρ z * v z = -(A₀ * ρ₀ * c * Real.exp (-(1 / 2))) ∧
        v z ^ 2 / 2 + c ^ 2 * Real.log (ρ z / ρ₀) = 0 ∧
        (z < 0 → v z < -c) ∧ (0 < z → -c < v z) := by
  let p := Real.sqrt (β / A₀)
  have hp : 0 < p := Real.sqrt_pos.2 (div_pos hβ hA)
  have hp2 : p ^ 2 = β / A₀ := Real.sq_sqrt (div_nonneg hβ.le hA.le)
  obtain ⟨w, hw, hw0, hw', hwe⟩ := normalized_speed p hp
  let v : ℝ → ℝ := fun z ↦ -c * w z
  let ρ : ℝ → ℝ := fun z ↦ ρ₀ * Real.exp (-(w z ^ 2) / 2)
  have hv : AnalyticAt ℝ v 0 := analyticAt_const.mul hw
  have harg : AnalyticAt ℝ (fun z ↦ -(w z ^ 2) / 2) 0 :=
    ((hw.pow 2).neg.div analyticAt_const (by norm_num : (2 : ℝ) ≠ 0))
  have hρan : AnalyticAt ℝ ρ 0 := analyticAt_const.mul harg.rexp
  have hv' : HasDerivAt v (c * p) 0 := (hw'.const_mul (-c)).congr_deriv (by ring)
  refine ⟨v, ρ, hv, hρan, by simp [v, hw0], hv', ?_⟩
  filter_upwards [hwe] with z hz
  have hquot : profileExp (w z) / w z = 1 + (p * z) ^ 2 := by
    have h := hz.2.1
    unfold areaProfile at h
    linarith
  have hm := (div_eq_iff hz.1.ne').mp hquot
  have hflux : (A₀ + β * z ^ 2) * w z = A₀ * profileExp (w z) := by
    calc
      (A₀ + β * z ^ 2) * w z = A₀ * (1 + (p * z) ^ 2) * w z := by
        rw [mul_pow, hp2]
        field_simp
      _ = A₀ * profileExp (w z) := by rw [mul_assoc, ← hm]
  have hexp : profileExp (w z) * Real.exp (-(w z ^ 2) / 2) = Real.exp (-(1 / 2)) := by
    rw [profileExp, ← Real.exp_add]
    congr 1
    ring
  have hratio : ρ z / ρ₀ = Real.exp (-(w z ^ 2) / 2) := by dsimp [ρ]; field_simp
  refine ⟨mul_pos hρ (Real.exp_pos _), mul_neg_of_neg_of_pos (neg_lt_zero.mpr hc) hz.1,
    ?_, ?_, ?_, ?_⟩
  · dsimp [v, ρ]
    calc
      (A₀ + β * z ^ 2) * (ρ₀ * Real.exp (-(w z ^ 2) / 2)) * (-c * w z) =
          - (ρ₀ * c * ((A₀ + β * z ^ 2) * w z) * Real.exp (-(w z ^ 2) / 2)) := by ring
      _ = -(A₀ * ρ₀ * c * Real.exp (-(1 / 2))) := by
        rw [hflux, ← hexp]
        ring
  · rw [hratio, Real.log_exp]
    dsimp [v]
    ring
  · intro h
    simpa [v] using mul_lt_mul_of_neg_left (hz.2.2.1 h) (neg_lt_zero.mpr hc)
  · intro h
    simpa [v] using mul_lt_mul_of_neg_left (hz.2.2.2 h) (neg_lt_zero.mpr hc)

/-- The general sonic-throat identities follow from the stationary fluid laws. -/
theorem throat_identities (A ρ v : ℝ → ℝ) (c ρ₀ D : ℝ) (hc : 0 < c) (hρ₀ : 0 < ρ₀)
    (hv : ContDiffAt ℝ 2 v 0) (hsonic : v 0 = -c)
    (hlaws : ∀ᶠ z in 𝓝 (0 : ℝ), 0 < A z ∧ 0 < ρ z ∧ A z * ρ z * v z = D ∧
      v z ^ 2 / 2 + c ^ 2 * Real.log (ρ z / ρ₀) = 0) :
    deriv A 0 = 0 ∧ iteratedDeriv 2 A 0 = 2 * A 0 * (deriv v 0 / c) ^ 2 := by
  let w : ℝ → ℝ := fun z ↦ -v z / c
  have hw0 : w 0 = 1 := by simp [w, hsonic, hc.ne']
  have hw : ContDiffAt ℝ 2 w 0 := hv.neg.div_const c
  have hwt : Tendsto w (𝓝 0) (𝓝 1) := by
    have h : Tendsto w (𝓝 0) (𝓝 (w 0)) := hw.continuousAt
    rwa [hw0] at h
  have hwpos : ∀ᶠ z in 𝓝 (0 : ℝ), 0 < w z :=
    hwt (show Ioi (0 : ℝ) ∈ 𝓝 (1 : ℝ) from Ioi_mem_nhds zero_lt_one)
  have hvw (z : ℝ) : v z = -c * w z := by dsimp [w]; field_simp
  have hrho : ∀ᶠ z in 𝓝 (0 : ℝ), ρ z = ρ₀ * Real.exp (-(w z ^ 2) / 2) := by
    filter_upwards [hlaws] with z hz
    have hlog : Real.log (ρ z / ρ₀) = -(w z ^ 2) / 2 := by
      apply mul_left_cancel₀ (pow_ne_zero 2 hc.ne')
      have hb := hz.2.2.2
      rw [hvw z] at hb
      linarith only [hb, show c ^ 2 * (-(w z ^ 2) / 2) = -((-c * w z) ^ 2 / 2) by ring]
    have h := congrArg Real.exp hlog
    rw [Real.exp_log (div_pos hz.2.1 hρ₀)] at h
    exact (div_eq_iff hρ₀.ne').mp h |>.trans (mul_comm _ _)
  have hlaws0 := hlaws.self_of_nhds
  have hA0 : A 0 ≠ 0 := hlaws0.1.ne'
  have hD : D = -(A 0 * ρ₀ * c * Real.exp (-(1 / 2))) := by
    rw [← hlaws0.2.2.1, hrho.self_of_nhds, hw0, hsonic]
    ring_nf
  obtain ⟨a, ha, ha1, hf⟩ := areaProfile_factor
  let u : ℝ → ℝ := fun z ↦ w z - 1
  let aw := a ∘ w
  have he : A =ᶠ[𝓝 (0 : ℝ)] fun z ↦ A 0 + A 0 * ((u z * u z) * aw z) := by
    filter_upwards [hlaws, hrho, hwpos, hwt.eventually hf] with z hz hρ hwz hzfactor
    have hflux := hz.2.2.1
    rw [hρ, hvw z, hD] at hflux
    have hflux' : (A z * w z) * Real.exp (-(w z ^ 2) / 2) =
        A 0 * Real.exp (-(1 / 2)) := by
      apply mul_left_cancel₀ (mul_ne_zero (neg_ne_zero.mpr hρ₀.ne') hc.ne')
      linear_combination hflux
    have hexp : profileExp (w z) * Real.exp (-(w z ^ 2) / 2) = Real.exp (-(1 / 2)) := by
      rw [profileExp, ← Real.exp_add]
      congr 1
      ring
    have hratio : A z / A 0 = profileExp (w z) / w z := by
      have h : A z * w z = A 0 * profileExp (w z) := by
        apply mul_right_cancel₀ (Real.exp_ne_zero (-(w z ^ 2) / 2))
        rw [hflux', mul_assoc, hexp]
      field_simp
      linear_combination h
    have hp : A z / A 0 - 1 = (u z * u z) * aw z := by
      rw [hratio]
      exact hzfactor
    field_simp at hp
    linear_combination hp
  have hu : ContDiffAt ℝ 2 u 0 := hw.sub contDiffAt_const
  have hau : ContDiffAt ℝ 2 aw 0 :=
    ContDiffAt.comp 0 (by rw [hw0]; exact ha.contDiffAt) hw
  have hj := quadratic_factor_jet (u := u) (a := aw) (by simp [u, hw0]) hu hau
  have hvd := (hv.differentiableAt (by norm_num)).hasDerivAt
  have hud : deriv u 0 = -deriv v 0 / c := ((hvd.neg.div_const c).sub_const 1).deriv
  have haw0 : aw 0 = 1 := by simp [aw, hw0, ha1]
  constructor
  · rw [he.deriv_eq]
    have hp : HasDerivAt (fun z ↦ (u z * u z) * aw z) 0 0 := by
      simpa only [hj.1] using
        ((hu.mul hu |>.mul hau).differentiableAt (by norm_num)).hasDerivAt
    simpa using ((hp.const_mul (A 0)).const_add (A 0)).deriv
  · rw [he.iteratedDeriv_eq 2, iteratedDeriv_const_add (by decide), iteratedDeriv_const_mul_field,
      hj.2, haw0, hud]
    ring

/-- The magnitude of the throat slope for a positive quadratic waist. -/
theorem quadratic_throat_slope (v ρ : ℝ → ℝ) (c A₀ β ρ₀ D : ℝ)
    (hc : 0 < c) (hA : 0 < A₀) (hβ : 0 < β) (hρ₀ : 0 < ρ₀)
    (hv : ContDiffAt ℝ 2 v 0) (hsonic : v 0 = -c)
    (hlaws : ∀ᶠ z in 𝓝 (0 : ℝ), 0 < ρ z ∧ (A₀ + β * z ^ 2) * ρ z * v z = D ∧
      v z ^ 2 / 2 + c ^ 2 * Real.log (ρ z / ρ₀) = 0) :
    |deriv v 0| = c * Real.sqrt (β / A₀) := by
  let A : ℝ → ℝ := fun z ↦ A₀ + β * z ^ 2
  have h := (throat_identities A ρ v c ρ₀ D hc hρ₀ hv hsonic (by
    filter_upwards [hlaws] with z hz
    exact ⟨add_pos_of_pos_of_nonneg hA (mul_nonneg hβ.le (sq_nonneg z)), hz⟩)).2
  have hA2 : iteratedDeriv 2 A 0 = 2 * β := by
    have h' : deriv A = fun z ↦ β * (2 * z) := by
      funext z
      simp [A]
    rw [show (2 : ℕ) = 1 + 1 by decide, iteratedDeriv_succ, iteratedDeriv_one, h']
    simp [mul_comm]
  rw [hA2, show A 0 = A₀ by simp [A]] at h
  have hsq : deriv v 0 ^ 2 = c ^ 2 * (β / A₀) := by
    field_simp
    field_simp at h
    linear_combination -h
  calc
    |deriv v 0| = Real.sqrt (deriv v 0 ^ 2) := (Real.sqrt_sq_eq_abs _).symm
    _ = c * Real.sqrt (β / A₀) := by
      rw [hsq, Real.sqrt_mul (sq_nonneg c), Real.sqrt_sq_eq_abs, abs_of_pos hc]

theorem lift_det (v c f : ℝ) (hc : c ≠ 0) : (liftMetric v c f).det = -c ^ 2 * f ^ 4 := by
  rw [liftMetric, Matrix.det_fromBlocks_zero₁₂, acousticMetric_det v c _ hc,
    Matrix.det_smul, Matrix.det_one, Fintype.card_fin, mul_one]
  ring

/-- The invertible triangular change of frame in the PG quadratic form. -/
def pgFrame (v c : ℝ) (hc : c ≠ 0) : (Axis → ℝ) ≃ₗ[ℝ] (Axis → ℝ) where
  toFun X := Sum.elim ![c * X timeAxis, X axialAxis - v * X timeAxis] (fun i ↦ X (.inr i))
  invFun X := Sum.elim ![X timeAxis / c, X axialAxis + v * (X timeAxis / c)]
    (fun i ↦ X (.inr i))
  left_inv X := by
    funext i
    rcases i with i | i
    · fin_cases i <;> simp [timeAxis, axialAxis, hc]
    · rfl
  right_inv X := by
    funext i
    rcases i with i | i
    · fin_cases i <;> simp [timeAxis, axialAxis]; field_simp
    · rfl
  map_add' X Y := by
    funext i
    rcases i with i | i
    · fin_cases i <;> simp [timeAxis, axialAxis] <;> ring
    · rfl
  map_smul' r X := by
    funext i
    rcases i with i | i
    · fin_cases i <;> simp [timeAxis, axialAxis] <;> ring
    · rfl

/-- The Lorentzian quadratic form is diagonal in the PG frame. -/
theorem lift_lorentzian_form (v c f : ℝ) (hc : c ≠ 0) (X : Axis → ℝ) :
    (∑ i, ∑ j, X i * liftMetric v c f i j * X j) =
      f * (-(pgFrame v c hc X timeAxis) ^ 2 + (pgFrame v c hc X axialAxis) ^ 2 +
        (pgFrame v c hc X transverseAxis) ^ 2 + (pgFrame v c hc X (.inr 1)) ^ 2) := by
  simp [Fintype.sum_sum_type, Fin.sum_univ_two, liftMetric, acousticMetric, pgFrame,
    timeAxis, axialAxis, transverseAxis, hc]
  ring

/-- Time translations preserve the metric components in this chart. -/
theorem stationary_time_translation (c : ℝ) (v f : ℝ → ℝ → ℝ) (q : Axis → ℝ) (δ : ℝ) :
    stationaryMetric c v f (q + δ • timeVector) = stationaryMetric c v f q := by
  simp [stationaryMetric, timeVector, timeAxis, axialAxis, transverseAxis]

theorem time_tangent_to_surface (q : Axis → ℝ) (δ : ℝ) :
    q + δ • timeVector ∈ sonicSurface ↔ q ∈ sonicSurface := by
  simp [sonicSurface, timeVector, timeAxis, axialAxis]

theorem timeVector_ne_zero : timeVector ≠ 0 := by
  intro h
  have ht := congrFun h timeAxis
  simp [timeVector] at ht

/-- Coordinate partial derivative of a scalar in the chart. -/
def coordPartial (F : (Axis → ℝ) → ℝ) (q : Axis → ℝ) (j : Axis) : ℝ :=
  deriv (fun r ↦ F (Function.update q j r)) (q j)

/-- Full coordinate expression for the time-time Christoffel column. -/
def christoffelTT (c : ℝ) (v f : ℝ → ℝ → ℝ) (q : Axis → ℝ) (i : Axis) : ℝ :=
  let g := stationaryMetric c v f
  let gi := liftInverse (v (q axialAxis) (q transverseAxis)) c (f (q axialAxis) (q transverseAxis))
  (∑ j, gi i j * (coordPartial (fun q' ↦ g q' j timeAxis) q timeAxis +
    coordPartial (fun q' ↦ g q' timeAxis j) q timeAxis -
    coordPartial (fun q' ↦ g q' timeAxis timeAxis) q j)) / 2

theorem time_partial_metric (c : ℝ) (v f : ℝ → ℝ → ℝ) (q : Axis → ℝ) (i j : Axis) :
    coordPartial (fun q' ↦ stationaryMetric c v f q' i j) q timeAxis = 0 := by
  simp [coordPartial, stationaryMetric, timeAxis, axialAxis, transverseAxis, Function.update]

theorem christoffelTT_eq_stationary (c : ℝ) (hc : c ≠ 0) (v f : ℝ → ℝ → ℝ)
    (q : Axis → ℝ) (i : Axis) :
    christoffelTT c v f q i = stationaryColumn c v f (q axialAxis) (q transverseAxis) i := by
  simp only [christoffelTT, time_partial_metric, zero_add, zero_sub, stationaryColumn]
  rw [Fintype.sum_sum_type, Fin.sum_univ_two, Fin.sum_univ_two]
  simp [coordPartial, stationaryMetric_timeNorm c hc, Function.update, timeAxis, axialAxis,
    transverseAxis]
  ring

theorem sonicCut_iff (q : Axis → ℝ) (t : ℝ) :
    q ∈ sonicCut t ↔ q axialAxis = 0 ∧ q timeAxis = t := Iff.rfl

/-- The fixed-time cut carries only the positive transverse quadratic form. -/
theorem lift_cut_form (v c f : ℝ) (hc : c ≠ 0) (X : Axis → ℝ)
    (ht : X timeAxis = 0) (hz : X axialAxis = 0) :
    (∑ i, ∑ j, X i * liftMetric v c f i j * X j) =
      f * (X transverseAxis ^ 2 + X (.inr 1) ^ 2) := by
  rw [lift_lorentzian_form v c f hc]
  simp [pgFrame, ht, hz, timeAxis, axialAxis, transverseAxis]

/-- Coordinate data for the stationary Killing horizon and its null normal. -/
structure LocalHorizon (c : ℝ) (v f : ℝ → ℝ → ℝ) (s : ℝ → ℝ) : Prop where
  timeTranslation : ∀ (q : Axis → ℝ) (δ : ℝ),
    stationaryMetric c v f (q + δ • timeVector) = stationaryMetric c v f q
  tangent : ∀ (q : Axis → ℝ) (δ : ℝ), q + δ • timeVector ∈ sonicSurface ↔ q ∈ sonicSurface
  generatorNonzero : timeVector ≠ 0
  normal : ∀ q ∈ sonicSurface, ∀ i,
    stationaryMetric c v f q i timeAxis = (f 0 (q transverseAxis) * c) * axialCovector i
  raisedNormal : ∀ q ∈ sonicSurface, ∀ i,
    liftInverse (v (q axialAxis) (q transverseAxis)) c (f (q axialAxis) (q transverseAxis))
      i axialAxis = (f 0 (q transverseAxis) * c)⁻¹ * timeVector i
  nullNormal : ∀ q ∈ sonicSurface,
    liftInverse (v (q axialAxis) (q transverseAxis)) c (f (q axialAxis) (q transverseAxis))
      axialAxis axialAxis = 0
  connection : ∀ q ∈ sonicSurface, ∀ i, christoffelTT c v f q i =
    s (q transverseAxis) * timeVector i

theorem local_horizon (c : ℝ) (hc : c ≠ 0) (v f : ℝ → ℝ → ℝ) (s : ℝ → ℝ)
    (hf : ∀ y, 0 < f 0 y) (hsonic : ∀ y, v 0 y = -c)
    (hvz : ∀ y, HasDerivAt (fun z ↦ v z y) (s y) 0)
    (hfz : ∀ y, DifferentiableAt ℝ (fun z ↦ f z y) 0) :
    LocalHorizon c v f s := by
  refine ⟨stationary_time_translation c v f, time_tangent_to_surface, timeVector_ne_zero,
    ?_, ?_, ?_, ?_⟩
  · intro q hq i
    have hz : q axialAxis = 0 := hq
    simpa only [stationaryMetric, hz, hsonic] using
      (sonic_normal c (f 0 (q transverseAxis)) hc (hf _).ne' i).1
  · intro q hq i
    have hz : q axialAxis = 0 := hq
    simpa only [hz, hsonic] using
      (sonic_normal c (f 0 (q transverseAxis)) hc (hf _).ne' i).2
  · intro q hq
    have hz : q axialAxis = 0 := hq
    simp [hz, hsonic, (sonic_normal c (f 0 (q transverseAxis)) hc (hf _).ne' axialAxis).2,
      timeVector, timeAxis, axialAxis]
  · intro q hq i
    have hz : q axialAxis = 0 := hq
    rw [christoffelTT_eq_stationary c hc, hz]
    exact stationary_nonaffinity c hc v f _ _ (hf _).ne' hsonic (hvz _) (hfz _) i

/-- The adverse metric is itself a local Killing horizon with variable nonaffinity. -/
theorem transverse_control_horizon (c : ℝ) (hc : 0 < c) :
    LocalHorizon c (fun z y ↦ -c + (1 + y ^ 2) * z) (fun _ _ ↦ 1) (fun y ↦ 1 + y ^ 2) := by
  apply local_horizon c hc.ne'
  · intro y
    exact zero_lt_one
  · simp
  · intro y
    simpa using ((hasDerivAt_id (0 : ℝ)).const_mul (1 + y ^ 2)).const_add (-c)
  · intro y
    fun_prop

/-- The components of the lifted metric are analytic at every point of the sonic surface. -/
theorem lift_component_analytic (c : ℝ) (hc : c ≠ 0) (v f : ℝ → ℝ)
    (hv : AnalyticAt ℝ v 0) (hf : AnalyticAt ℝ f 0)
    (q : Axis → ℝ) (hq : q ∈ sonicSurface) (i j : Axis) :
    AnalyticAt ℝ (fun x ↦ stationaryMetric c (fun z _ ↦ v z) (fun z _ ↦ f z) x i j) q := by
  have hz : q axialAxis = 0 := hq
  have hπ : AnalyticAt ℝ (fun x : Axis → ℝ ↦ x axialAxis) q :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Axis ↦ ℝ) axialAxis).analyticAt q
  have hvπ : AnalyticAt ℝ (fun x : Axis → ℝ ↦ v (x axialAxis)) q :=
    hv.comp_of_eq hπ hz
  have hfπ : AnalyticAt ℝ (fun x : Axis → ℝ ↦ f (x axialAxis)) q :=
    hf.comp_of_eq hπ hz
  rcases i with i | i <;> rcases j with j | j <;> fin_cases i <;> fin_cases j <;>
    simp [stationaryMetric, liftMetric, acousticMetric, hc]
  all_goals first
    | exact analyticAt_const
    | exact hfπ
    | exact (hfπ.fun_mul hvπ).neg
    | exact hfπ.fun_mul ((hvπ.fun_pow 2).fun_sub analyticAt_const)

/-- The full coordinate connection of the adverse metric is nonconstant along the horizon. -/
theorem transverse_control_not_constant (c : ℝ) (hc : 0 < c) :
    ¬ ∃ κ : ℝ, ∀ q ∈ sonicSurface, ∀ i,
      christoffelTT c (fun z y ↦ -c + (1 + y ^ 2) * z) (fun _ _ ↦ 1) q i =
        κ * timeVector i := by
  rintro ⟨κ, hκ⟩
  let q₀ : Axis → ℝ := 0
  let q₁ : Axis → ℝ := fun i ↦ if i = transverseAxis then 1 else 0
  have hh := transverse_control_horizon c hc
  have hq₀ : q₀ ∈ sonicSurface := rfl
  have hq₁ : q₁ ∈ sonicSurface := by simp [q₁, sonicSurface, axialAxis, transverseAxis]
  have h₀ := (hh.connection q₀ hq₀ timeAxis).symm.trans (hκ q₀ hq₀ timeAxis)
  have h₁ := (hh.connection q₁ hq₁ timeAxis).symm.trans (hκ q₁ hq₁ timeAxis)
  norm_num [q₀, q₁, timeVector] at h₀ h₁
  linarith

/-- The analytic stationary fluid solution together with its transverse horizon geometry. -/
theorem analytic_nozzle_horizon (c A₀ β ρ₀ : ℝ) (hc : 0 < c) (hA : 0 < A₀)
    (hβ : 0 < β) (hρ : 0 < ρ₀) :
    ∃ v ρ : ℝ → ℝ, AnalyticAt ℝ v 0 ∧ AnalyticAt ℝ ρ 0 ∧ v 0 = -c ∧
      HasDerivAt v (c * Real.sqrt (β / A₀)) 0 ∧
      (∀ᶠ z in 𝓝 (0 : ℝ), 0 < ρ z ∧ v z < 0 ∧
        (A₀ + β * z ^ 2) * ρ z * v z = -(A₀ * ρ₀ * c * Real.exp (-(1 / 2))) ∧
        v z ^ 2 / 2 + c ^ 2 * Real.log (ρ z / ρ₀) = 0 ∧
        (z < 0 → v z < -c) ∧ (0 < z → -c < v z)) ∧
      LocalHorizon c (fun z _ ↦ v z) (fun z _ ↦ ρ z / c) (fun _ ↦ c * Real.sqrt (β / A₀)) ∧
      (∀ q ∈ sonicSurface, ∀ i j, AnalyticAt ℝ
        (fun x ↦ stationaryMetric c (fun z _ ↦ v z) (fun z _ ↦ ρ z / c) x i j) q) ∧
      (∀ q ∈ sonicSurface, ∀ i,
        c⁻¹ ^ 2 * christoffelTT c (fun z _ ↦ v z) (fun z _ ↦ ρ z / c) q i =
          Real.sqrt (β / A₀) * (c⁻¹ * timeVector i)) ∧
      sourceAcceleration c (c * Real.sqrt (β / A₀)) = c ^ 2 * Real.sqrt (β / A₀) ∧
      sourceInverseLength c (c * Real.sqrt (β / A₀)) = Real.sqrt (β / A₀) := by
  obtain ⟨v, ρ, hv, hρan, hsonic, hvz, hlaws⟩ := analytic_transonic_nozzle c A₀ β ρ₀ hc hA hβ hρ
  have hh : LocalHorizon c (fun z _ ↦ v z) (fun z _ ↦ ρ z / c)
      (fun _ ↦ c * Real.sqrt (β / A₀)) := by
    apply local_horizon c hc.ne'
    · intro y
      exact div_pos hlaws.self_of_nhds.1 hc
    · exact fun _ ↦ hsonic
    · exact fun _ ↦ hvz
    · exact fun _ ↦ hρan.differentiableAt.div_const c
  refine ⟨v, ρ, hv, hρan, hsonic, hvz, hlaws, hh, ?_, ?_, by unfold sourceAcceleration; ring, ?_⟩
  · exact fun q hq i j ↦ lift_component_analytic c hc.ne' v (fun z ↦ ρ z / c)
      hv hρan.div_const q hq i j
  · intro q hq i
    rw [hh.connection q hq i]
    have hn := (normalized_nonaffinity c (c * Real.sqrt (β / A₀)) hc.ne' i).1
    simpa [hc.ne'] using hn
  · simpa [hc.ne'] using
      (normalized_nonaffinity c (c * Real.sqrt (β / A₀)) hc.ne' timeAxis).2

end

end SKEFTHawking.L3StationaryNozzle
