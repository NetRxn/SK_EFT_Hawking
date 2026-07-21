/-
# Phase 5q.H — the chart-1 neighbourhood is acyclic, and its boundary part is a solid torus

`KummerBasePushRetractInt.kummerK3_b2_target_of_chartNbhd1` reduced the `H₂(K3;ℤ) ≅ ℤ²²` headline to
**two ordinary homotopy facts at a single threshold** `r`:

1. `H₂(chartNbhd1 r; ℤ) = 0` and `H₁(chartNbhd1 r; ℤ) = 0`;
2. `H₁(∂E ∩ chartNbhd1 r; ℤ)` cyclic.

This module proves both, unconditionally, for every `0 < r < 1`.

## The engine: the two GLOBAL chart-1 coordinates

`E` is glued from two `D² × D²` charts by `clutch (z,w) = (z⁻¹, z²w)`. The *chart-1 fiber*
coordinate

> `fibC1 (chart0 (z,w)) = z²·w`,   `fibC1 (chart1 (ζ,v)) = v`

is **globally defined on all of `E`** — the transition is exactly `z²·w`, so the two chart formulas
agree on the weld with no case split. The *chart-1 base* coordinate `ζ = z⁻¹` is not global (it blows
up at `z = 0`), but its **guarded** form `ginv r z = conj z / max(‖z‖, r)²` is: it is continuous
everywhere, equals `z⁻¹` on `‖z‖ ≥ r`, and on the weld locus `‖z‖ = 1` it is literally `z⁻¹`
regardless of `r`, so it descends through the quotient with no hypothesis at all.

Together they give a continuous `Ψ = (baseC1 r, fibC1) : E → ℂ × ℂ` which restricts to a
**homeomorphism of `chartNbhd1 r` onto the explicit model**

> `Model r = {(ζ,w) | ‖ζ‖·r < 1 ∧ ‖w‖ ≤ 1 ∧ ‖w‖·‖ζ‖² ≤ 1}`,

the extended base disk of radius `1/r` carrying the `𝒪(−2)` disk bundle in its chart-1
trivialization. The inverse `Θ` is the only case split in the module — `chart1` over `‖ζ‖ ≤ 1`,
`chart0` over `‖ζ‖ ≥ 1` — glued by `Continuous.if_le` (the two branches agree on `‖ζ‖ = 1` *by the
weld*), with radial clamps making both branches total.

`Model r` is **star-shaped about the origin** (`s·(ζ,w)` scales the third condition by `s³`), so it
is contractible and integrally acyclic in every positive degree; the boundary model
`BdryModel r = {‖ζ‖·r < 1 ∧ ‖w‖·max(1,‖ζ‖²) = 1}` deformation-retracts onto the fiber circle
`{0} × S¹` by shrinking `ζ` and renormalizing the fiber, so its `H₁` is cyclic (`≅ ℤ`, via the banked
`circleH1EquivInt`).

## Output

* `homology_chartNbhd1_eq_zero` : `Hₖ₊₁(chartNbhd1 r; ℤ) = 0` for `0 < r < 1` — fact 1.
* `bdryRegion_h1_cyclic` : `H₁(∂E ∩ chartNbhd1 r; ℤ)` is cyclic — fact 2.
* `kummerK3_b2_target_unconditional` : **`H₂(K3;ℤ) ≅ ℤ²²`, with no hypotheses left.**

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.KummerBasePushRetractInt
import SKEFTHawking.KummerHomologyT4

open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularFunctorialityInt (Homology.mapInt
  Homology.mapInt_bijective_of_homotopyEquiv)
open SKEFTHawking.SingularSphereHomologyInt (Homology.mapInt_bijective_of_comp_id_all)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularHomotopyInvariance (slice)
open SKEFTHawking.SingularHomotopyInvarianceInt (cycle_mem_boundaries_of_contractionInt)
open SKEFTHawking.SingularRelativeTripleSurjInt (cyclic_of_surjective)
open SKEFTHawking.SingularSphereAcyclic (Sph)
open SKEFTHawking.SingularLineMinusPointInt (circleH1EquivInt)
open SKEFTHawking.KummerHomologyT4 (complexEuclidLI)
open SKEFTHawking.KummerResolutionPiece (ResE ResChart Disk boundaryE chart0 chart1 glued
  chart0_inj_iff chart1_inj_iff chart0_eq_chart1_iff continuous_chart0 continuous_chart1 resSetoid)
open SKEFTHawking.KummerWeldFiberFlow (fiberNorm fiberNorm_eq_one_iff)
open SKEFTHawking.KummerPairTransportInt (ResEtop)
open SKEFTHawking.KummerChartNbhdInt (deepChart0 chartNbhd1)
open SKEFTHawking.KummerCollarRegionRetractInt (BdryRegion)
open SKEFTHawking.KummerBasePushRetractInt (Chart1NbhdTop)

namespace SKEFTHawking.KummerChart1NbhdAcyclicInt

noncomputable section

/-! ## §1. The chart-1 fiber coordinate — global, no guard -/

/-- The chart-1 fiber coordinate at the chart level: `z²·w` on chart 0, `v` on chart 1. -/
def fibSum : ResChart ⊕ ResChart → ℂ
  | Sum.inl p => (p.1 : ℂ) ^ 2 * (p.2 : ℂ)
  | Sum.inr q => (q.2 : ℂ)

/-- **The chart-1 fiber coordinate respects the weld** — because the weld's fiber component is
*literally* `z²·w`. No hypothesis, no case analysis on norms. -/
theorem fibSum_respects {a b : ResChart ⊕ ResChart}
    (h : SKEFTHawking.KummerResolutionPiece.resRel a b) : fibSum a = fibSum b := by
  rcases h with rfl | hg
  · rfl
  · cases a with
    | inl p =>
      cases b with
      | inl _ => exact (hg : False).elim
      | inr q => exact ((hg : glued p q).2.2).symm
    | inr q =>
      cases b with
      | inr _ => exact (hg : False).elim
      | inl p => exact (hg : glued p q).2.2

/-- **The global chart-1 fiber coordinate `w' : E → ℂ`.** -/
def fibC1 : ResE → ℂ := Quotient.lift fibSum (fun _ _ h => fibSum_respects h)

@[simp] theorem fibC1_chart0 (p : ResChart) : fibC1 (chart0 p) = (p.1 : ℂ) ^ 2 * (p.2 : ℂ) := rfl

@[simp] theorem fibC1_chart1 (q : ResChart) : fibC1 (chart1 q) = (q.2 : ℂ) := rfl

theorem continuous_fibSum : Continuous fibSum := by
  have h : fibSum = Sum.elim (fun p : ResChart => (p.1 : ℂ) ^ 2 * (p.2 : ℂ))
      (fun q : ResChart => (q.2 : ℂ)) := by
    funext a; cases a <;> rfl
  rw [h]
  exact (((continuous_subtype_val.comp continuous_fst).pow 2).mul
    (continuous_subtype_val.comp continuous_snd)).sumElim
      (continuous_subtype_val.comp continuous_snd)

theorem continuous_fibC1 : Continuous fibC1 :=
  (isQuotientMap_quotient_mk' (s := resSetoid)).continuous_iff.mpr continuous_fibSum

/-! ## §2. The guarded chart-1 base coordinate -/

/-- The guard radius, clamped into `[0,1]` so that the weld computation needs no hypothesis. -/
def rc (r : ℝ) : ℝ := max 0 (min r 1)

theorem rc_nonneg (r : ℝ) : 0 ≤ rc r := le_max_left _ _

theorem rc_le_one (r : ℝ) : rc r ≤ 1 := max_le zero_le_one (min_le_right _ _)

theorem rc_pos {r : ℝ} (hr : 0 < r) : 0 < rc r :=
  lt_max_of_lt_right (lt_min hr zero_lt_one)

theorem rc_eq {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) : rc r = r := by
  unfold rc; rw [min_eq_left hr1, max_eq_right hr0]

/-- **The guarded inverse** `conj z / max(‖z‖, rc r)²`: continuous everywhere, equal to `z⁻¹`
whenever `‖z‖ ≥ rc r`, and — the load-bearing point — equal to `z⁻¹` on the weld locus `‖z‖ = 1`
for *every* `r`, because `rc r ≤ 1`. -/
def ginv (r : ℝ) (z : ℂ) : ℂ :=
  (starRingEnd ℂ) z / (((max ‖z‖ (rc r)) ^ 2 : ℝ) : ℂ)

/-- `conj z / ‖z‖² = z⁻¹` — the algebraic core of every guarded inverse in this module. -/
theorem conj_div_normSq {z : ℂ} (hz0 : z ≠ 0) :
    (starRingEnd ℂ) z / ((‖z‖ ^ 2 : ℝ) : ℂ) = z⁻¹ := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  refine eq_inv_of_mul_eq_one_left ?_
  rw [div_mul_eq_mul_div, mul_comm ((starRingEnd ℂ) z) z, Complex.mul_conj,
    Complex.normSq_eq_norm_sq]
  exact div_self (by exact_mod_cast pow_ne_zero 2 hn)

theorem ginv_eq_inv {r : ℝ} {z : ℂ} (hz : rc r ≤ ‖z‖) (hz0 : z ≠ 0) : ginv r z = z⁻¹ := by
  have hmax : max ‖z‖ (rc r) = ‖z‖ := max_eq_left hz
  unfold ginv
  rw [hmax]
  exact conj_div_normSq hz0

theorem ginv_of_norm_one {r : ℝ} {z : ℂ} (hz : ‖z‖ = 1) : ginv r z = z⁻¹ :=
  ginv_eq_inv (by rw [hz]; exact rc_le_one r) (by rw [← norm_ne_zero_iff, hz]; norm_num)

theorem continuous_ginv {r : ℝ} (hr : 0 < r) : Continuous (ginv r) := by
  have hden : Continuous (fun z : ℂ => (((max ‖z‖ (rc r)) ^ 2 : ℝ) : ℂ)) :=
    Complex.continuous_ofReal.comp ((continuous_norm.max continuous_const).pow 2)
  refine Complex.continuous_conj.div hden (fun z => ?_)
  have h0 : 0 < max ‖z‖ (rc r) := lt_of_lt_of_le (rc_pos hr) (le_max_right _ _)
  exact_mod_cast (by positivity : ((max ‖z‖ (rc r)) ^ 2 : ℝ) ≠ 0)

/-- The chart-1 base coordinate at the chart level. -/
def baseSum (r : ℝ) : ResChart ⊕ ResChart → ℂ
  | Sum.inl p => ginv r (p.1 : ℂ)
  | Sum.inr q => (q.1 : ℂ)

theorem baseSum_respects {r : ℝ} {a b : ResChart ⊕ ResChart}
    (h : SKEFTHawking.KummerResolutionPiece.resRel a b) : baseSum r a = baseSum r b := by
  rcases h with rfl | hg
  · rfl
  · cases a with
    | inl p =>
      cases b with
      | inl _ => exact (hg : False).elim
      | inr q =>
        obtain ⟨hz, hq1, -⟩ := (hg : glued p q)
        show ginv r (p.1 : ℂ) = (q.1 : ℂ)
        rw [ginv_of_norm_one hz, hq1]
    | inr q =>
      cases b with
      | inr _ => exact (hg : False).elim
      | inl p =>
        obtain ⟨hz, hq1, -⟩ := (hg : glued p q)
        show (q.1 : ℂ) = ginv r (p.1 : ℂ)
        rw [ginv_of_norm_one hz, hq1]

/-- **The global (guarded) chart-1 base coordinate `ζ : E → ℂ`.** -/
def baseC1 (r : ℝ) : ResE → ℂ := Quotient.lift (baseSum r) (fun _ _ h => baseSum_respects h)

@[simp] theorem baseC1_chart0 (r : ℝ) (p : ResChart) :
    baseC1 r (chart0 p) = ginv r (p.1 : ℂ) := rfl

@[simp] theorem baseC1_chart1 (r : ℝ) (q : ResChart) : baseC1 r (chart1 q) = (q.1 : ℂ) := rfl

theorem continuous_baseSum {r : ℝ} (hr : 0 < r) : Continuous (baseSum r) := by
  have h : baseSum r = Sum.elim (fun p : ResChart => ginv r (p.1 : ℂ))
      (fun q : ResChart => (q.1 : ℂ)) := by
    funext a; cases a <;> rfl
  rw [h]
  exact ((continuous_ginv hr).comp (continuous_subtype_val.comp continuous_fst)).sumElim
    (continuous_subtype_val.comp continuous_fst)

theorem continuous_baseC1 {r : ℝ} (hr : 0 < r) : Continuous (baseC1 r) :=
  (isQuotientMap_quotient_mk' (s := resSetoid)).continuous_iff.mpr (continuous_baseSum hr)

/-- **The chart-1 coordinate map `Ψ = (ζ, w') : E → ℂ × ℂ`.** -/
def psiRaw (r : ℝ) (x : ResE) : ℂ × ℂ := (baseC1 r x, fibC1 x)

theorem continuous_psiRaw {r : ℝ} (hr : 0 < r) : Continuous (psiRaw r) :=
  (continuous_baseC1 hr).prodMk continuous_fibC1

/-! ## §3. The explicit model and the inverse map `Θ` -/

/-- The plane `ℂ × ℂ` as an ambient space. -/
abbrev CCtop : TopCat := TopCat.of (ℂ × ℂ)

/-- **The chart-1 model of `chartNbhd1 r`**: the `𝒪(−2)` disk bundle over the extended base disk of
radius `1/r`, written in the chart-1 trivialization. The third condition `‖w‖·‖ζ‖² ≤ 1` is the
chart-0 disk condition transported through the clutch. -/
def Model (r : ℝ) : Set (ℂ × ℂ) :=
  {p | ‖p.1‖ * r < 1 ∧ ‖p.2‖ ≤ 1 ∧ ‖p.2‖ * ‖p.1‖ ^ 2 ≤ 1}

/-- **The chart-1 model of `∂E ∩ chartNbhd1 r`**: the circle bundle over the same disk — a solid
torus. The fiber radius is `min(1, ‖ζ‖⁻²)`, written multiplicatively. -/
def BdryModel (r : ℝ) : Set (ℂ × ℂ) :=
  {p | ‖p.1‖ * r < 1 ∧ ‖p.2‖ * max 1 (‖p.1‖ ^ 2) = 1}

theorem BdryModel_subset_Model (r : ℝ) : BdryModel r ⊆ Model r := by
  rintro p ⟨h1, h2⟩
  have hm : (1 : ℝ) ≤ max 1 (‖p.1‖ ^ 2) := le_max_left _ _
  have hm2 : ‖p.1‖ ^ 2 ≤ max 1 (‖p.1‖ ^ 2) := le_max_right _ _
  have hw : (0 : ℝ) ≤ ‖p.2‖ := norm_nonneg _
  exact ⟨h1, by nlinarith, by nlinarith⟩

/-- The clamping denominator is positive. -/
theorem clamp_den_pos (c : ℂ) : (0 : ℝ) < max 1 ‖c‖ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)

/-- **Radial clamp into the closed unit disk** — the identity wherever `‖c‖ ≤ 1`. -/
def clampD (c : ℂ) : Disk :=
  ⟨c / ((max 1 ‖c‖ : ℝ) : ℂ), by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (clamp_den_pos c)]
    exact div_le_one_of_le₀ (le_max_right _ _) (clamp_den_pos c).le⟩

@[simp] theorem clampD_coe (c : ℂ) : ((clampD c : Disk) : ℂ) = c / ((max 1 ‖c‖ : ℝ) : ℂ) := rfl

theorem clampD_eq {c : ℂ} (hc : ‖c‖ ≤ 1) : ((clampD c : Disk) : ℂ) = c := by
  rw [clampD_coe, max_eq_left hc]
  norm_num

theorem continuous_clampD : Continuous clampD := by
  refine Continuous.subtype_mk (continuous_id.div ?_ (fun c => ?_)) _
  · exact Complex.continuous_ofReal.comp (continuous_const.max continuous_norm)
  · exact_mod_cast (clamp_den_pos c).ne'

/-- **Guarded inverse landing in the closed unit disk** — equals `c⁻¹` wherever `‖c‖ ≥ 1`. -/
def invD (c : ℂ) : Disk :=
  ⟨(starRingEnd ℂ) c / ((max 1 (‖c‖ ^ 2) : ℝ) : ℂ), by
    have hpos : (0 : ℝ) < max 1 (‖c‖ ^ 2) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    have hle : ‖c‖ ≤ max 1 (‖c‖ ^ 2) := by
      rcases le_total ‖c‖ 1 with h | h
      · exact le_trans h (le_max_left _ _)
      · exact le_trans (by nlinarith) (le_max_right _ _)
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos, RCLike.norm_conj]
    exact div_le_one_of_le₀ hle hpos.le⟩

@[simp] theorem invD_coe (c : ℂ) :
    ((invD c : Disk) : ℂ) = (starRingEnd ℂ) c / ((max 1 (‖c‖ ^ 2) : ℝ) : ℂ) := rfl

theorem invD_eq {c : ℂ} (hc : 1 ≤ ‖c‖) : ((invD c : Disk) : ℂ) = c⁻¹ := by
  have hc0 : c ≠ 0 := by rw [← norm_ne_zero_iff]; intro h; rw [h] at hc; linarith
  rw [invD_coe, max_eq_right (by nlinarith)]
  exact conj_div_normSq hc0

theorem continuous_invD : Continuous invD := by
  refine Continuous.subtype_mk (Complex.continuous_conj.div ?_ (fun c => ?_)) _
  · exact Complex.continuous_ofReal.comp (continuous_const.max (continuous_norm.pow 2))
  · have hpos : (0 : ℝ) < max 1 (‖c‖ ^ 2) := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
    exact_mod_cast hpos.ne'

/-- The chart-1 branch of `Θ` (used over `‖ζ‖ ≤ 1`). -/
def thetaA (p : ℂ × ℂ) : ResE := chart1 (clampD p.1, clampD p.2)

/-- The chart-0 branch of `Θ` (used over `‖ζ‖ ≥ 1`): base `ζ⁻¹`, fiber `ζ²·w`. -/
def thetaB (p : ℂ × ℂ) : ResE := chart0 (invD p.1, clampD (p.1 ^ 2 * p.2))

/-- **The two branches agree on the seam `‖ζ‖ = 1` — by the weld.** This is the one place where the
`𝒪(−2)` clutch enters the construction of `Θ`, and it is exactly `chart0_eq_chart1_iff`. -/
theorem thetaA_eq_thetaB {p : ℂ × ℂ} (h : ‖p.1‖ = 1) : thetaA p = thetaB p := by
  have h0 : p.1 ≠ 0 := by rw [← norm_ne_zero_iff, h]; norm_num
  have hinv : ((invD p.1 : Disk) : ℂ) = (p.1)⁻¹ := invD_eq h.ge
  have hnorm : ‖p.1 ^ 2 * p.2‖ = ‖p.2‖ := by
    rw [norm_mul, norm_pow, h, one_pow, one_mul]
  refine (chart0_eq_chart1_iff.mpr ⟨?_, ?_, ?_⟩).symm
  · rw [hinv, norm_inv, h, inv_one]
  · rw [hinv, inv_inv, clampD_eq h.le]
  · rw [hinv, clampD_coe, clampD_coe, hnorm]
    field_simp

/-- **The inverse map `Θ : ℂ × ℂ → E`** — `chart1` over the unit disk, `chart0` outside it. -/
def thetaRaw (p : ℂ × ℂ) : ResE := if ‖p.1‖ ≤ 1 then thetaA p else thetaB p

theorem thetaRaw_of_le {p : ℂ × ℂ} (h : ‖p.1‖ ≤ 1) : thetaRaw p = thetaA p := if_pos h

theorem thetaRaw_of_ge {p : ℂ × ℂ} (h : 1 ≤ ‖p.1‖) : thetaRaw p = thetaB p := by
  unfold thetaRaw
  split
  · next hle => exact thetaA_eq_thetaB (le_antisymm hle h)
  · rfl

theorem continuous_thetaA : Continuous thetaA :=
  continuous_chart1.comp ((continuous_clampD.comp continuous_fst).prodMk
    (continuous_clampD.comp continuous_snd))

theorem continuous_thetaB : Continuous thetaB :=
  continuous_chart0.comp ((continuous_invD.comp continuous_fst).prodMk
    (continuous_clampD.comp ((continuous_fst.pow 2).mul continuous_snd)))

theorem continuous_thetaRaw : Continuous thetaRaw :=
  Continuous.if_le continuous_thetaA continuous_thetaB (continuous_fst.norm) continuous_const
    (fun _ h => thetaA_eq_thetaB h)

/-! ## §4. `Ψ` and `Θ` are mutually inverse between `chartNbhd1 r` and `Model r` -/

theorem Model.fst_lt {r : ℝ} {p : ℂ × ℂ} (hp : p ∈ Model r) : ‖p.1‖ * r < 1 := hp.1

theorem Model.snd_le {r : ℝ} {p : ℂ × ℂ} (hp : p ∈ Model r) : ‖p.2‖ ≤ 1 := hp.2.1

theorem Model.mul_le {r : ℝ} {p : ℂ × ℂ} (hp : p ∈ Model r) : ‖p.2‖ * ‖p.1‖ ^ 2 ≤ 1 := hp.2.2

/-- On the far side of the seam the model's fiber datum is already in the disk. -/
theorem model_fiber_norm_le {r : ℝ} {p : ℂ × ℂ} (hp : p ∈ Model r) : ‖p.1 ^ 2 * p.2‖ ≤ 1 := by
  rw [norm_mul, norm_pow, mul_comm]
  exact Model.mul_le hp

/-- **`Θ` lands in the chart-1 neighbourhood.** Over the unit disk it produces a chart-1 point (never
deep in chart 0, since a weld forces base norm `1 > r`); outside it the chart-0 base norm is
`1/‖ζ‖ > r`, precisely the model's first condition. -/
theorem theta_mem_chartNbhd1 {r : ℝ} (hr1 : r < 1) {p : ℂ × ℂ} (hp : p ∈ Model r) :
    thetaRaw p ∈ chartNbhd1 r := by
  rcases le_total ‖p.1‖ 1 with h | h
  · rw [thetaRaw_of_le h]
    rintro ⟨p', hp', hmk⟩
    have hmk' : chart0 p' = chart1 (clampD p.1, clampD p.2) := hmk
    obtain ⟨hseam, -, -⟩ := chart0_eq_chart1_iff.mp hmk'
    have hle : ‖((p'.1 : Disk) : ℂ)‖ ≤ r := hp'
    rw [hseam] at hle
    linarith
  · rw [thetaRaw_of_ge h]
    rintro ⟨p', hp', hmk⟩
    have hmk' : chart0 p' = chart0 (invD p.1, clampD (p.1 ^ 2 * p.2)) := hmk
    have heq : p' = (invD p.1, clampD (p.1 ^ 2 * p.2)) := chart0_inj_iff.mp hmk'
    have hle : ‖((p'.1 : Disk) : ℂ)‖ ≤ r := hp'
    rw [heq] at hle
    have hbase : ‖((invD p.1 : Disk) : ℂ)‖ = ‖p.1‖⁻¹ := by
      rw [invD_eq h, norm_inv]
    rw [show ‖((((invD p.1, clampD (p.1 ^ 2 * p.2)) : ResChart).1 : Disk) : ℂ)‖
        = ‖((invD p.1 : Disk) : ℂ)‖ from rfl, hbase] at hle
    have h0 : (0 : ℝ) < ‖p.1‖ := lt_of_lt_of_le zero_lt_one h
    have := Model.fst_lt hp
    rw [inv_le_iff_one_le_mul₀ h0] at hle
    nlinarith

/-- **`Ψ` lands in the model.** -/
theorem psi_mem_Model {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {x : ResE} (hx : x ∈ chartNbhd1 r) :
    psiRaw r x ∈ Model r := by
  induction x using Quotient.ind with
  | _ a =>
    cases a with
    | inl p =>
      have hgt : r < ‖((p.1 : Disk) : ℂ)‖ := by
        by_contra hcon
        exact hx ⟨p, le_of_not_gt hcon, rfl⟩
      have h0 : ((p.1 : Disk) : ℂ) ≠ 0 := by
        rw [← norm_ne_zero_iff]; intro h; rw [h] at hgt; linarith
      have hbase : baseC1 r (chart0 p) = ((p.1 : Disk) : ℂ)⁻¹ :=
        ginv_eq_inv (by rw [rc_eq hr0 hr1.le]; exact hgt.le) h0
      have hb1 : ‖((p.1 : Disk) : ℂ)‖ ≤ 1 := p.1.2
      have hf1 : ‖((p.2 : Disk) : ℂ)‖ ≤ 1 := p.2.2
      have hfnorm : ‖fibC1 (chart0 p)‖ = ‖((p.1 : Disk) : ℂ)‖ ^ 2 * ‖((p.2 : Disk) : ℂ)‖ := by
        rw [fibC1_chart0, norm_mul, norm_pow]
      have hbnorm : ‖baseC1 r (chart0 p)‖ = ‖((p.1 : Disk) : ℂ)‖⁻¹ := by
        rw [hbase, norm_inv]
      have hpos : (0 : ℝ) < ‖((p.1 : Disk) : ℂ)‖ := lt_of_le_of_lt hr0 hgt
      refine ⟨?_, ?_, ?_⟩
      · show ‖baseC1 r (chart0 p)‖ * r < 1
        rw [hbnorm, inv_mul_lt_iff₀ hpos, mul_one]
        exact hgt
      · show ‖fibC1 (chart0 p)‖ ≤ 1
        rw [hfnorm]
        nlinarith [norm_nonneg ((p.1 : Disk) : ℂ), norm_nonneg ((p.2 : Disk) : ℂ)]
      · show ‖fibC1 (chart0 p)‖ * ‖baseC1 r (chart0 p)‖ ^ 2 ≤ 1
        rw [hfnorm, hbnorm, inv_pow]
        rw [mul_inv_le_iff₀ (by positivity), one_mul]
        nlinarith
    | inr q =>
      have hb1 : ‖((q.1 : Disk) : ℂ)‖ ≤ 1 := q.1.2
      have hf1 : ‖((q.2 : Disk) : ℂ)‖ ≤ 1 := q.2.2
      refine ⟨?_, ?_, ?_⟩
      · show ‖baseC1 r (chart1 q)‖ * r < 1
        rw [baseC1_chart1]
        nlinarith [norm_nonneg ((q.1 : Disk) : ℂ)]
      · show ‖fibC1 (chart1 q)‖ ≤ 1
        rw [fibC1_chart1]; exact hf1
      · show ‖fibC1 (chart1 q)‖ * ‖baseC1 r (chart1 q)‖ ^ 2 ≤ 1
        rw [fibC1_chart1, baseC1_chart1]
        nlinarith [norm_nonneg ((q.1 : Disk) : ℂ), norm_nonneg ((q.2 : Disk) : ℂ)]

/-- **`Ψ ∘ Θ = id` on the model.** -/
theorem psi_theta {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r ≤ 1) {p : ℂ × ℂ} (hp : p ∈ Model r) :
    psiRaw r (thetaRaw p) = p := by
  rcases le_total ‖p.1‖ 1 with h | h
  · rw [thetaRaw_of_le h]
    show (baseC1 r (chart1 _), fibC1 (chart1 _)) = p
    rw [baseC1_chart1, fibC1_chart1, clampD_coe, clampD_coe, max_eq_left h,
      max_eq_left (Model.snd_le hp)]
    norm_num
  · have hpos : (0 : ℝ) < ‖p.1‖ := lt_of_lt_of_le zero_lt_one h
    have h0 : p.1 ≠ 0 := norm_ne_zero_iff.mp hpos.ne'
    have hinv : ((invD p.1 : Disk) : ℂ) = (p.1)⁻¹ := invD_eq h
    have hclamp : ((clampD (p.1 ^ 2 * p.2) : Disk) : ℂ) = p.1 ^ 2 * p.2 :=
      clampD_eq (model_fiber_norm_le hp)
    have hbase : ‖((invD p.1 : Disk) : ℂ)‖ = ‖p.1‖⁻¹ := by rw [hinv, norm_inv]
    have hrle : rc r ≤ ‖((invD p.1 : Disk) : ℂ)‖ := by
      rw [hbase, rc_eq hr0 hr1, inv_eq_one_div, le_div_iff₀ hpos]
      nlinarith [Model.fst_lt hp]
    rw [thetaRaw_of_ge h]
    show (baseC1 r (chart0 _), fibC1 (chart0 _)) = p
    rw [baseC1_chart0, fibC1_chart0]
    rw [ginv_eq_inv hrle (by rw [hinv]; exact inv_ne_zero h0), hinv, inv_inv, hclamp]
    refine Prod.ext rfl ?_
    show (p.1)⁻¹ ^ 2 * (p.1 ^ 2 * p.2) = p.2
    field_simp

/-- **`Θ ∘ Ψ = id` on the chart-1 neighbourhood.** -/
theorem theta_psi {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {x : ResE} (hx : x ∈ chartNbhd1 r) :
    thetaRaw (psiRaw r x) = x := by
  induction x using Quotient.ind with
  | _ a =>
    cases a with
    | inl p =>
      have hgt : r < ‖((p.1 : Disk) : ℂ)‖ := by
        by_contra hcon
        exact hx ⟨p, le_of_not_gt hcon, rfl⟩
      have h0 : ((p.1 : Disk) : ℂ) ≠ 0 := by
        rw [← norm_ne_zero_iff]; intro h; rw [h] at hgt; linarith
      have hpos : (0 : ℝ) < ‖((p.1 : Disk) : ℂ)‖ := lt_of_le_of_lt hr0 hgt
      have hbase : baseC1 r (chart0 p) = ((p.1 : Disk) : ℂ)⁻¹ :=
        ginv_eq_inv (by rw [rc_eq hr0 hr1.le]; exact hgt.le) h0
      show thetaRaw (psiRaw r (chart0 p)) = chart0 p
      have hpsi : psiRaw r (chart0 p)
          = (((p.1 : Disk) : ℂ)⁻¹, ((p.1 : Disk) : ℂ) ^ 2 * ((p.2 : Disk) : ℂ)) := by
        show (baseC1 r (chart0 p), fibC1 (chart0 p)) = _
        rw [hbase, fibC1_chart0]
      rw [hpsi]
      have hge : (1 : ℝ) ≤ ‖((p.1 : Disk) : ℂ)⁻¹‖ := by
        rw [norm_inv, one_le_inv_iff₀]
        exact ⟨hpos, p.1.2⟩
      rw [thetaRaw_of_ge hge]
      show chart0 (invD ((p.1 : Disk) : ℂ)⁻¹,
        clampD ((((p.1 : Disk) : ℂ)⁻¹) ^ 2 * (((p.1 : Disk) : ℂ) ^ 2 * ((p.2 : Disk) : ℂ))))
          = chart0 p
      refine congrArg chart0 (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
      · rw [invD_eq hge, inv_inv]
      · have hfib : (((p.1 : Disk) : ℂ)⁻¹) ^ 2 * (((p.1 : Disk) : ℂ) ^ 2 * ((p.2 : Disk) : ℂ))
            = ((p.2 : Disk) : ℂ) := by field_simp
        rw [hfib, clampD_eq p.2.2]
    | inr q =>
      show thetaRaw (psiRaw r (chart1 q)) = chart1 q
      have hpsi : psiRaw r (chart1 q) = (((q.1 : Disk) : ℂ), ((q.2 : Disk) : ℂ)) := rfl
      rw [hpsi, thetaRaw_of_le q.1.2]
      show chart1 (clampD ((q.1 : Disk) : ℂ), clampD ((q.2 : Disk) : ℂ)) = chart1 q
      exact congrArg chart1 (Prod.ext (Subtype.ext (clampD_eq q.1.2))
        (Subtype.ext (clampD_eq q.2.2)))

/-! ## §5. `chartNbhd1 r` is acyclic -/

/-- `Θ`, as a continuous map of the model onto the chart-1 neighbourhood. -/
def ThetaMap {r : ℝ} (hr1 : r < 1) : C(↑(sub (X := CCtop) (Model r)), ↑(Chart1NbhdTop r)) where
  toFun p := ⟨thetaRaw (p : ℂ × ℂ), theta_mem_chartNbhd1 hr1 p.2⟩
  continuous_toFun := (continuous_thetaRaw.comp continuous_subtype_val).subtype_mk _

/-- `Ψ`, as a continuous map of the chart-1 neighbourhood onto the model. -/
def PsiMap {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    C(↑(Chart1NbhdTop r), ↑(sub (X := CCtop) (Model r))) where
  toFun x := ⟨psiRaw r (x : ResE), psi_mem_Model hr0.le hr1 x.2⟩
  continuous_toFun := ((continuous_psiRaw hr0).comp continuous_subtype_val).subtype_mk _

/-- **`Θ` is a homeomorphism of the model onto `chartNbhd1 r`** — at the level of homology, an
isomorphism in every degree. -/
theorem mapInt_ThetaMap_bijective {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) :
    Function.Bijective (Homology.mapInt (ThetaMap hr1) n) :=
  Homology.mapInt_bijective_of_comp_id_all (ThetaMap hr1) (PsiMap hr0 hr1)
    (ContinuousMap.ext fun p => Subtype.ext (psi_theta hr0.le hr1.le p.2))
    (ContinuousMap.ext fun x => Subtype.ext (theta_psi hr0.le hr1 x.2)) n

/-- Real scaling of a model point, written multiplicatively in `ℂ` (no `ℝ`-module instances
needed on the ambient product). -/
def scale (s : ℝ) (p : ℂ × ℂ) : ℂ × ℂ := ((s : ℂ) * p.1, (s : ℂ) * p.2)

@[simp] theorem scale_one (p : ℂ × ℂ) : scale 1 p = p := by
  simp [scale]

@[simp] theorem scale_zero (p : ℂ × ℂ) : scale 0 p = 0 := by
  simp [scale]

theorem norm_scale_fst {s : ℝ} (hs : 0 ≤ s) (p : ℂ × ℂ) : ‖(scale s p).1‖ = s * ‖p.1‖ := by
  rw [show (scale s p).1 = (s : ℂ) * p.1 from rfl, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hs]

theorem norm_scale_snd {s : ℝ} (hs : 0 ≤ s) (p : ℂ × ℂ) : ‖(scale s p).2‖ = s * ‖p.2‖ := by
  rw [show (scale s p).2 = (s : ℂ) * p.2 from rfl, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hs]

theorem continuous_scale : Continuous (fun q : ℝ × (ℂ × ℂ) => scale q.1 q.2) :=
  ((Complex.continuous_ofReal.comp continuous_fst).mul
    (continuous_fst.comp continuous_snd)).prodMk
    ((Complex.continuous_ofReal.comp continuous_fst).mul (continuous_snd.comp continuous_snd))

/-- **The model is star-shaped about the origin**: scaling by `s ∈ [0,1]` scales the first two
conditions by `s` and the third by `s³`. -/
theorem model_scale_mem {r : ℝ} (hr : 0 ≤ r) {p : ℂ × ℂ} (hp : p ∈ Model r) {s : ℝ} (hs0 : 0 ≤ s)
    (hs1 : s ≤ 1) : scale s p ∈ Model r := by
  have hz : (0 : ℝ) ≤ ‖p.1‖ := norm_nonneg _
  have hw : (0 : ℝ) ≤ ‖p.2‖ := norm_nonneg _
  have e1 := norm_scale_fst hs0 p
  have e2 := norm_scale_snd hs0 p
  have h1 := Model.fst_lt hp
  have h2 := Model.snd_le hp
  have h3 := Model.mul_le hp
  refine ⟨?_, ?_, ?_⟩
  · show ‖(scale s p).1‖ * r < 1
    rw [e1]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (mul_nonneg hz hr)]
  · show ‖(scale s p).2‖ ≤ 1
    rw [e2]; nlinarith
  · show ‖(scale s p).2‖ * ‖(scale s p).1‖ ^ 2 ≤ 1
    rw [e1, e2]
    have hcube : s ^ 3 ≤ 1 := pow_le_one₀ hs0 hs1
    have hprod : (0 : ℝ) ≤ ‖p.2‖ * ‖p.1‖ ^ 2 := mul_nonneg hw (sq_nonneg _)
    nlinarith [pow_nonneg hs0 3]

theorem model_zero_mem (r : ℝ) : (0 : ℂ × ℂ) ∈ Model r := by
  refine ⟨?_, ?_, ?_⟩ <;> simp

/-- **The straight-line contraction of the model to the origin.** -/
def modelContraction {r : ℝ} (hr : 0 ≤ r) :
    C(↑(sub (X := CCtop) (Model r)) × unitInterval, ↑(sub (X := CCtop) (Model r))) where
  toFun q := ⟨scale (1 - (q.2 : ℝ)) (q.1 : ℂ × ℂ),
    model_scale_mem hr q.1.2 (by have := q.2.2.2; linarith) (by have := q.2.2.1; linarith)⟩
  continuous_toFun :=
    (continuous_scale.comp ((continuous_const.sub (continuous_subtype_val.comp continuous_snd)).prodMk
      (continuous_subtype_val.comp continuous_fst))).subtype_mk _

theorem slice_modelContraction_zero {r : ℝ} (hr : 0 ≤ r) :
    slice (modelContraction hr) 0 = ContinuousMap.id _ := by
  refine ContinuousMap.ext fun p => Subtype.ext ?_
  show scale (1 - ((0 : unitInterval) : ℝ)) (p : ℂ × ℂ) = (p : ℂ × ℂ)
  rw [show ((0 : unitInterval) : ℝ) = 0 from rfl, sub_zero, scale_one]

theorem slice_modelContraction_one {r : ℝ} (hr : 0 ≤ r) :
    slice (modelContraction hr) 1 = ContinuousMap.const _ ⟨(0 : ℂ × ℂ), model_zero_mem r⟩ := by
  refine ContinuousMap.ext fun p => Subtype.ext ?_
  show scale (1 - ((1 : unitInterval) : ℝ)) (p : ℂ × ℂ) = (0 : ℂ × ℂ)
  rw [show ((1 : unitInterval) : ℝ) = 1 from rfl, sub_self, scale_zero]

/-- **The model is integrally acyclic in every positive degree.** -/
theorem homology_Model_eq_zero {r : ℝ} (hr : 0 ≤ r) (k : ℕ)
    (x : Homology (sub (X := CCtop) (Model r)) (k + 1)) : x = 0 := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [show (Submodule.Quotient.mk z : Homology _ (k + 1)) = Homology.mk _ (k + 1) z from rfl,
    SKEFTHawking.SingularCohomologyInt.Homology.mk_eq_zero]
  exact Submodule.mem_comap.mpr (by
    simpa using cycle_mem_boundaries_of_contractionInt (modelContraction hr)
      ⟨(0 : ℂ × ℂ), model_zero_mem r⟩ (slice_modelContraction_zero hr)
      (slice_modelContraction_one hr) z.1 (LinearMap.mem_ker.mp z.2))

/-- **FACT 1 — the chart-1 neighbourhood is acyclic**: `Hₖ₊₁(chartNbhd1 r; ℤ) = 0` for every
`0 < r < 1`. The chart-1 neighbourhood is the `𝒪(−2)` disk bundle over a disk, and in the chart-1
trivialization it is literally a star-shaped subset of `ℂ²`. -/
theorem homology_chartNbhd1_eq_zero {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (k : ℕ)
    (x : Homology (Chart1NbhdTop r) (k + 1)) : x = 0 := by
  obtain ⟨y, rfl⟩ := (mapInt_ThetaMap_bijective hr0 hr1 (k + 1)).2 x
  rw [homology_Model_eq_zero hr0.le k y, map_zero]

/-! ## §6. The boundary part is a solid torus -/

theorem BdryModel.fst_lt {r : ℝ} {p : ℂ × ℂ} (hp : p ∈ BdryModel r) : ‖p.1‖ * r < 1 := hp.1

theorem BdryModel.fib {r : ℝ} {p : ℂ × ℂ} (hp : p ∈ BdryModel r) :
    ‖p.2‖ * max 1 (‖p.1‖ ^ 2) = 1 := hp.2

/-- `Θ` carries the boundary model into `∂E` — the fiber radius is `1` in whichever chart the point
lands in. -/
theorem theta_mem_boundaryE {r : ℝ} {p : ℂ × ℂ} (hp : p ∈ BdryModel r) :
    thetaRaw p ∈ boundaryE := by
  refine fiberNorm_eq_one_iff.mp ?_
  rcases le_total ‖p.1‖ 1 with h | h
  · have hmax : max 1 (‖p.1‖ ^ 2) = 1 :=
      max_eq_left (by nlinarith [norm_nonneg p.1])
    have hw : ‖p.2‖ = 1 := by have := BdryModel.fib hp; rwa [hmax, mul_one] at this
    rw [thetaRaw_of_le h]
    show ‖((clampD p.2 : Disk) : ℂ)‖ = 1
    rw [clampD_eq hw.le]; exact hw
  · have hmax : max 1 (‖p.1‖ ^ 2) = ‖p.1‖ ^ 2 := max_eq_right (by nlinarith)
    have hw : ‖p.2‖ * ‖p.1‖ ^ 2 = 1 := by have := BdryModel.fib hp; rwa [hmax] at this
    have hnorm : ‖p.1 ^ 2 * p.2‖ = 1 := by
      rw [norm_mul, norm_pow, mul_comm]; exact hw
    rw [thetaRaw_of_ge h]
    show ‖((clampD (p.1 ^ 2 * p.2) : Disk) : ℂ)‖ = 1
    rw [clampD_eq hnorm.le]; exact hnorm

/-- `Ψ` carries `∂E ∩ chartNbhd1 r` into the boundary model. -/
theorem psi_mem_BdryModel {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) {x : ResE}
    (hb : x ∈ boundaryE) (hx : x ∈ chartNbhd1 r) : psiRaw r x ∈ BdryModel r := by
  have hfn : fiberNorm x = 1 := fiberNorm_eq_one_iff.mpr hb
  refine ⟨(psi_mem_Model hr0.le hr1 hx).1, ?_⟩
  clear hb
  induction x using Quotient.ind with
  | _ a =>
    cases a with
    | inl p =>
      have hgt : r < ‖((p.1 : Disk) : ℂ)‖ := by
        by_contra hcon
        exact hx ⟨p, le_of_not_gt hcon, rfl⟩
      have hpos : (0 : ℝ) < ‖((p.1 : Disk) : ℂ)‖ := lt_trans hr0 hgt
      have h0 : ((p.1 : Disk) : ℂ) ≠ 0 := norm_ne_zero_iff.mp hpos.ne'
      have hbase : baseC1 r (chart0 p) = ((p.1 : Disk) : ℂ)⁻¹ :=
        ginv_eq_inv (by rw [rc_eq hr0.le hr1.le]; exact hgt.le) h0
      have hw : ‖((p.2 : Disk) : ℂ)‖ = 1 := hfn
      have hinvge : (1 : ℝ) ≤ ‖((p.1 : Disk) : ℂ)‖⁻¹ := one_le_inv_iff₀.mpr ⟨hpos, p.1.2⟩
      show ‖fibC1 (chart0 p)‖ * max 1 (‖baseC1 r (chart0 p)‖ ^ 2) = 1
      rw [fibC1_chart0, hbase, norm_mul, norm_pow, norm_inv, hw, mul_one,
        max_eq_right (one_le_pow₀ hinvge)]
      field_simp
    | inr q =>
      have hw : ‖((q.2 : Disk) : ℂ)‖ = 1 := hfn
      show ‖fibC1 (chart1 q)‖ * max 1 (‖baseC1 r (chart1 q)‖ ^ 2) = 1
      rw [fibC1_chart1, baseC1_chart1, hw,
        max_eq_left (by nlinarith [norm_nonneg ((q.1 : Disk) : ℂ), q.1.2]), mul_one]

/-- `Θ` as a continuous map of the boundary model onto `∂E ∩ chartNbhd1 r`. -/
def ThetaBdry {r : ℝ} (hr1 : r < 1) :
    C(↑(sub (X := CCtop) (BdryModel r)), ↑(BdryRegion (chartNbhd1 r))) where
  toFun p := ⟨thetaRaw (p : ℂ × ℂ), Set.mem_inter (theta_mem_boundaryE p.2)
    (theta_mem_chartNbhd1 hr1 (BdryModel_subset_Model r p.2))⟩
  continuous_toFun := (continuous_thetaRaw.comp continuous_subtype_val).subtype_mk _

/-- `Ψ` as a continuous map of `∂E ∩ chartNbhd1 r` onto the boundary model. -/
def PsiBdry {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    C(↑(BdryRegion (chartNbhd1 r)), ↑(sub (X := CCtop) (BdryModel r))) where
  toFun x := ⟨psiRaw r (x : ResE), psi_mem_BdryModel hr0 hr1 x.2.1 x.2.2⟩
  continuous_toFun := ((continuous_psiRaw hr0).comp continuous_subtype_val).subtype_mk _

theorem mapInt_ThetaBdry_bijective {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) (n : ℕ) :
    Function.Bijective (Homology.mapInt (ThetaBdry hr1) n) :=
  Homology.mapInt_bijective_of_comp_id_all (ThetaBdry hr1) (PsiBdry hr0 hr1)
    (ContinuousMap.ext fun p =>
      Subtype.ext (psi_theta hr0.le hr1.le (BdryModel_subset_Model r p.2)))
    (ContinuousMap.ext fun x => Subtype.ext (theta_psi hr0.le hr1 x.2.2)) n

/-- **The fiber circle over the chart-1 origin** — the core of the solid torus. -/
def Circ : Set (ℂ × ℂ) := {p | p.1 = 0 ∧ ‖p.2‖ = 1}

theorem circ_subset_BdryModel (r : ℝ) : Circ ⊆ BdryModel r := by
  rintro p ⟨h1, h2⟩
  constructor
  · show ‖p.1‖ * r < 1
    rw [h1]; simp
  · show ‖p.2‖ * max 1 (‖p.1‖ ^ 2) = 1
    rw [h1, h2]; simp

/-- The fiber renormalization factor accompanying the base shrink `ζ ↦ s·ζ`. -/
def bdryScale (p : ℂ × ℂ) (s : ℝ) : ℝ :=
  max 1 (‖p.1‖ ^ 2) / max 1 (‖(s : ℂ) * p.1‖ ^ 2)

theorem max_one_pos (c : ℂ) : (0 : ℝ) < max 1 (‖c‖ ^ 2) :=
  lt_of_lt_of_le zero_lt_one (le_max_left _ _)

theorem bdryScale_pos (p : ℂ × ℂ) (s : ℝ) : 0 < bdryScale p s :=
  div_pos (max_one_pos p.1) (max_one_pos _)

/-- **The base shrink with fiber renormalization** — the deformation retraction of the solid torus
onto its core circle. -/
def bdryFlow (p : ℂ × ℂ) (s : ℝ) : ℂ × ℂ :=
  ((s : ℂ) * p.1, ((bdryScale p s : ℝ) : ℂ) * p.2)

theorem bdryFlow_mem {r : ℝ} (hr : 0 ≤ r) {p : ℂ × ℂ} (hp : p ∈ BdryModel r) {s : ℝ}
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) : bdryFlow p s ∈ BdryModel r := by
  have hz : (0 : ℝ) ≤ ‖p.1‖ := norm_nonneg _
  have e1 : ‖(bdryFlow p s).1‖ = s * ‖p.1‖ := by
    rw [show (bdryFlow p s).1 = (s : ℂ) * p.1 from rfl, norm_mul, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hs0]
  constructor
  · show ‖(bdryFlow p s).1‖ * r < 1
    rw [e1]
    nlinarith [mul_nonneg (sub_nonneg.mpr hs1) (mul_nonneg hz hr), BdryModel.fst_lt hp]
  · show ‖(bdryFlow p s).2‖ * max 1 (‖(bdryFlow p s).1‖ ^ 2) = 1
    have hM' : (0 : ℝ) < max 1 (‖(s : ℂ) * p.1‖ ^ 2) := max_one_pos _
    have hfst : (bdryFlow p s).1 = (s : ℂ) * p.1 := rfl
    have e2 : ‖(bdryFlow p s).2‖ = bdryScale p s * ‖p.2‖ := by
      rw [show (bdryFlow p s).2 = ((bdryScale p s : ℝ) : ℂ) * p.2 from rfl, norm_mul,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos (bdryScale_pos p s)]
    rw [e2, hfst, bdryScale, div_mul_eq_mul_div, div_mul_eq_mul_div,
      mul_div_assoc, div_self hM'.ne', mul_one]
    rw [mul_comm (max 1 (‖p.1‖ ^ 2)) ‖p.2‖]
    exact BdryModel.fib hp

theorem bdryFlow_one (p : ℂ × ℂ) : bdryFlow p 1 = p := by
  have h : ((1 : ℝ) : ℂ) * p.1 = p.1 := by push_cast; ring
  have hs : bdryScale p 1 = 1 := by
    rw [bdryScale, h]
    exact div_self (max_one_pos p.1).ne'
  refine Prod.ext ?_ ?_
  · exact h
  · show ((bdryScale p 1 : ℝ) : ℂ) * p.2 = p.2
    rw [hs]; push_cast; ring

theorem bdryFlow_zero_of_circ {p : ℂ × ℂ} (hp : p ∈ Circ) : bdryFlow p 0 = p := by
  have h1 : p.1 = 0 := hp.1
  have h : ((0 : ℝ) : ℂ) * p.1 = p.1 := by rw [h1]; ring
  have hs : bdryScale p 0 = 1 := by
    rw [bdryScale, h, h1]
    norm_num
  refine Prod.ext h ?_
  show ((bdryScale p 0 : ℝ) : ℂ) * p.2 = p.2
  rw [hs]; push_cast; ring

theorem bdryFlow_zero_mem_circ {r : ℝ} {p : ℂ × ℂ} (hp : p ∈ BdryModel r) :
    bdryFlow p 0 ∈ Circ := by
  have h1 : ((0 : ℝ) : ℂ) * p.1 = 0 := by push_cast; ring
  refine ⟨h1, ?_⟩
  have hM' : max 1 (‖((0 : ℝ) : ℂ) * p.1‖ ^ 2) = 1 := by rw [h1]; norm_num
  have hs : bdryScale p 0 = max 1 (‖p.1‖ ^ 2) := by rw [bdryScale, hM', div_one]
  show ‖((bdryScale p 0 : ℝ) : ℂ) * p.2‖ = 1
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (bdryScale_pos p 0), hs]
  rw [mul_comm]
  exact BdryModel.fib hp

theorem continuous_bdryFlow : Continuous (fun q : (ℂ × ℂ) × ℝ => bdryFlow q.1 q.2) := by
  have hbase : Continuous (fun q : (ℂ × ℂ) × ℝ => ((q.2 : ℝ) : ℂ) * q.1.1) :=
    (Complex.continuous_ofReal.comp continuous_snd).mul (continuous_fst.comp continuous_fst)
  have hnum : Continuous (fun q : (ℂ × ℂ) × ℝ => max 1 (‖q.1.1‖ ^ 2)) :=
    continuous_const.max (((continuous_fst.comp continuous_fst).norm).pow 2)
  have hden : Continuous (fun q : (ℂ × ℂ) × ℝ => max 1 (‖((q.2 : ℝ) : ℂ) * q.1.1‖ ^ 2)) :=
    continuous_const.max ((hbase.norm).pow 2)
  refine hbase.prodMk ?_
  refine ((Complex.continuous_ofReal.comp (hnum.div hden (fun q => (max_one_pos _).ne'))).mul
    (continuous_snd.comp continuous_fst))

/-- The retraction of the solid torus onto its core circle. -/
def bdryRetrMap {r : ℝ} (_hr : 0 < r) :
    C(↑(sub (X := CCtop) (BdryModel r)), ↑(sub (X := CCtop) Circ)) where
  toFun p := ⟨bdryFlow (p : ℂ × ℂ) 0, bdryFlow_zero_mem_circ p.2⟩
  continuous_toFun :=
    ((continuous_bdryFlow.comp (continuous_subtype_val.prodMk continuous_const))).subtype_mk _

/-- The inclusion of the core circle. -/
def bdryInclMap (r : ℝ) :
    C(↑(sub (X := CCtop) Circ), ↑(sub (X := CCtop) (BdryModel r))) where
  toFun p := ⟨(p : ℂ × ℂ), circ_subset_BdryModel r p.2⟩
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The retracting homotopy inside the solid torus. -/
def bdryHomotopy {r : ℝ} (hr : 0 < r) :
    C(↑(sub (X := CCtop) (BdryModel r)) × unitInterval,
      ↑(sub (X := CCtop) (BdryModel r))) where
  toFun q := ⟨bdryFlow (q.1 : ℂ × ℂ) (q.2 : ℝ),
    bdryFlow_mem hr.le q.1.2 q.2.2.1 q.2.2.2⟩
  continuous_toFun :=
    ((continuous_bdryFlow.comp ((continuous_subtype_val.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)))).subtype_mk _

/-- The constant homotopy on the core circle. -/
def circConstHomotopy :
    C(↑(sub (X := CCtop) Circ) × unitInterval, ↑(sub (X := CCtop) Circ)) :=
  ⟨fun q => q.1, continuous_fst⟩

theorem mapInt_bdryRetrMap_bijective {r : ℝ} (hr : 0 < r) (n : ℕ) :
    Function.Bijective (Homology.mapInt (bdryRetrMap hr) (n + 1)) :=
  Homology.mapInt_bijective_of_homotopyEquiv (bdryRetrMap hr) (bdryInclMap r)
    (bdryHomotopy hr)
    (ContinuousMap.ext fun _ => Subtype.ext rfl)
    (ContinuousMap.ext fun _ => Subtype.ext (bdryFlow_one _))
    circConstHomotopy
    (ContinuousMap.ext fun p => Subtype.ext (bdryFlow_zero_of_circ p.2).symm)
    (ContinuousMap.ext fun _ => Subtype.ext rfl) n

/-! ### The core circle is `S¹` -/

def circToSph : C(↑(sub (X := CCtop) Circ), ↑(Sph 1)) where
  toFun p := ⟨complexEuclidLI ((p : ℂ × ℂ).2), by
    rw [mem_sphere_zero_iff_norm, complexEuclidLI.norm_map]; exact p.2.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact complexEuclidLI.continuous.comp (continuous_snd.comp continuous_subtype_val)

def sphToCirc : C(↑(Sph 1), ↑(sub (X := CCtop) Circ)) where
  toFun w := ⟨((0 : ℂ), complexEuclidLI.symm (w : EuclideanSpace ℝ (Fin 2))), rfl, by
    rw [complexEuclidLI.symm.norm_map]; exact mem_sphere_zero_iff_norm.mp w.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_const.prodMk
      (complexEuclidLI.symm.continuous.comp continuous_subtype_val)

theorem sphToCirc_circToSph (p : ↑(sub (X := CCtop) Circ)) : sphToCirc (circToSph p) = p := by
  refine Subtype.ext (Prod.ext p.2.1.symm ?_)
  show complexEuclidLI.symm (complexEuclidLI ((p : ℂ × ℂ).2)) = (p : ℂ × ℂ).2
  exact complexEuclidLI.symm_apply_apply _

theorem circToSph_sphToCirc (w : ↑(Sph 1)) : circToSph (sphToCirc w) = w := by
  refine Subtype.ext ?_
  show complexEuclidLI (complexEuclidLI.symm (w : EuclideanSpace ℝ (Fin 2)))
      = (w : EuclideanSpace ℝ (Fin 2))
  exact complexEuclidLI.apply_symm_apply _

theorem mapInt_circToSph_bijective (n : ℕ) :
    Function.Bijective (Homology.mapInt circToSph n) :=
  Homology.mapInt_bijective_of_comp_id_all circToSph sphToCirc
    (ContinuousMap.ext sphToCirc_circToSph)
    (ContinuousMap.ext circToSph_sphToCirc) n

/-- **`H₁` of the core circle is `ℤ`** — the banked `circleH1EquivInt`, transported. -/
def circH1Equiv : Homology (sub (X := CCtop) Circ) 1 ≃ₗ[ℤ] ℤ :=
  (LinearEquiv.ofBijective _ (mapInt_circToSph_bijective 1)).trans circleH1EquivInt

theorem circ_h1_cyclic (x : Homology (sub (X := CCtop) Circ) 1) :
    ∃ k : ℤ, x = k • circH1Equiv.symm 1 := by
  refine ⟨circH1Equiv x, ?_⟩
  rw [← map_zsmul, smul_eq_mul, mul_one, LinearEquiv.symm_apply_apply]

/-- **`H₁` of the boundary model is cyclic.** -/
theorem bdryModel_h1_cyclic {r : ℝ} (hr : 0 < r) :
    ∃ a : Homology (sub (X := CCtop) (BdryModel r)) 1,
      ∀ x : Homology (sub (X := CCtop) (BdryModel r)) 1, ∃ k : ℤ, x = k • a := by
  set e : Homology (sub (X := CCtop) (BdryModel r)) 1 ≃ₗ[ℤ] Homology (sub (X := CCtop) Circ) 1 :=
    LinearEquiv.ofBijective _ (mapInt_bdryRetrMap_bijective hr 0) with he
  exact ⟨e.symm (circH1Equiv.symm 1),
    cyclic_of_surjective e.symm.toLinearMap e.symm.surjective circ_h1_cyclic⟩

/-- **FACT 2 — the boundary part of the chart-1 neighbourhood is a solid torus**, so its `H₁` is
cyclic. -/
theorem bdryRegion_h1_cyclic {r : ℝ} (hr0 : 0 < r) (hr1 : r < 1) :
    ∃ a : Homology (BdryRegion (chartNbhd1 r)) 1,
      ∀ x : Homology (BdryRegion (chartNbhd1 r)) 1, ∃ k : ℤ, x = k • a := by
  obtain ⟨a, ha⟩ := bdryModel_h1_cyclic hr0
  exact ⟨Homology.mapInt (ThetaBdry hr1) 1 a,
    cyclic_of_surjective (Homology.mapInt (ThetaBdry hr1) 1)
      (mapInt_ThetaBdry_bijective hr0 hr1 1).2 ha⟩

/-! ## §7. The headline, unconditional -/

/-- **`H₂(K3;ℤ) ≅ ℤ²²` — UNCONDITIONALLY.**

`KummerBasePushRetractInt.kummerK3_b2_target_of_chartNbhd1` left exactly two ordinary homotopy
facts at the single threshold `r` (admissible at `r' = 1/4`, `r = 3/8`, by
`quarter_threshold_admissible`): acyclicity of `chartNbhd1 r` in degrees `1, 2`
(`homology_chartNbhd1_eq_zero`) and cyclicity of `H₁(∂E ∩ chartNbhd1 r; ℤ)`
(`bdryRegion_h1_cyclic`). Both are discharged above, so the `b₂ = 22` target carries **no
hypotheses**. -/
theorem kummerK3_b2_target_unconditional :
    SKEFTHawking.KummerK7Opener.kummerK3_b2_target :=
  SKEFTHawking.KummerBasePushRetractInt.kummerK3_b2_target_of_chartNbhd1
    (r := 3 / 8) (r' := 1 / 4) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)
    (homology_chartNbhd1_eq_zero (by norm_num) (by norm_num) 1)
    (homology_chartNbhd1_eq_zero (by norm_num) (by norm_num) 0)
    (bdryRegion_h1_cyclic (by norm_num) (by norm_num))

end

end SKEFTHawking.KummerChart1NbhdAcyclicInt
