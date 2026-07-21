/-
# Phase 5q.H — the BASE-radial push, and the removal of the second threshold

The two-threshold excision (`KummerSplitBChart1ExcisionInt`) had to retain the *larger* chart-1
neighbourhood `chartNbhd1 r'` (`r' < r`) to dodge the corner where `‖base‖ = r` meets
`fiberNorm = 1/2`. That leaves the residual frontier phrased at the auxiliary threshold `r'`. This
module removes it: the retained piece deformation-retracts onto the honest chart-1 neighbourhood
`chartNbhd1 r`.

## The push

The retraction is a **base**-radial push, mirroring the banked fiber flow `resFlow`:

> `basePush (chart0 (z, w), t) = chart0 ((1 + (1 - t)(1 - ‖z‖)) · z, w)`, chart-1 points fixed.

Three facts make it work and make it cheap:

* **Seam compatibility.** At `‖z‖ = 1` the factor is `1`, so the push is the identity on the weld
  locus at every time — that is exactly what lets it descend through the quotient, and it is why the
  chart-1 branch can simply be the identity.
* **It stays in the disk.** The radius at `t` is `s + (1-t)s(1-s) ≤ 2s - s² ≤ 1`, with equality only
  at `s = 1`. No clamping, no `max`/`min`, no case split.
* **It is monotone and lands past `r`.** The radius never decreases, and at `t = 0` it is
  `ψ(s) = s(2 - s)`, strictly increasing on `[0,1]`. So a point with `‖z‖ > r'` ends with radius
  `> ψ(r') = r'(2 - r')`; the standing hypothesis `r < r'(2 - r')` then puts it inside
  `chartNbhd1 r`.

Because the push moves only the **base** coordinate it preserves `outerE` and `∂E` (fiber
conditions) exactly as `resFlow` preserved `chartNbhd1` (base conditions) — the two flows are
complementary, and together they reduce the whole residual frontier to a single threshold.

## Output

* `chart1PieceHomologyEquiv` : `Hₙ₊₁(chartNbhd1 r' ∩ splitBOpen r; ℤ) ≅ Hₙ₊₁(chartNbhd1 r; ℤ)`
* `bdryRegionHomologyEquiv` : `Hₙ₊₁(∂E ∩ chartNbhd1 r'; ℤ) ≅ Hₙ₊₁(∂E ∩ chartNbhd1 r; ℤ)`
* `kummerK3_b2_target_of_chartNbhd1` : the `H₂(K3;ℤ) ≅ ℤ²²` headline on **two** facts at a single
  threshold — acyclicity of `chartNbhd1 r` in degrees `1, 2`, and cyclicity of
  `H₁(∂E ∩ chartNbhd1 r; ℤ)`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.KummerCollarRegionRetractInt

open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularFunctorialityInt (Homology.mapInt
  Homology.mapInt_bijective_of_homotopyEquiv)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularHomotopyInvariance (slice)
open SKEFTHawking.SingularRelativeTripleSurjInt (cyclic_of_surjective)
open SKEFTHawking.KummerResolutionPiece (ResE ResChart Disk boundaryE chart0 chart1
  chart0_inj_iff chart0_eq_chart1_iff continuous_chart0 continuous_chart1 resSetoid)
open SKEFTHawking.KummerPairTransportInt (ResEtop)
open SKEFTHawking.KummerPieceCollarInt (outerE)
open SKEFTHawking.KummerChartNbhdInt (deepChart0 chartNbhd1 splitBOpen)
open SKEFTHawking.KummerSplitBChart1ExcisionInt (chart1Piece)
open SKEFTHawking.KummerCollarRegionRetractInt (BdryRegion kummerK3_b2_target_of_chart1_bdry)

namespace SKEFTHawking.KummerBasePushRetractInt

noncomputable section

/-! ## §1. The base-radial push on a disk -/

/-- The push factor at time `t` for a base coordinate of norm `s`. It is `1` at `t = 1` (identity)
and `2 - s` at `t = 0` (the full push), and it is `1` whenever `s = 1` — the seam. -/
def pushFactor (t : unitInterval) (s : ℝ) : ℝ := 1 + (1 - (t : ℝ)) * (1 - s)

theorem pushFactor_nonneg (t : unitInterval) {s : ℝ} (hs : s ≤ 1) : 0 ≤ pushFactor t s := by
  have h1 : (0 : ℝ) ≤ 1 - (t : ℝ) := by have := t.2.2; linarith
  have h2 : (0 : ℝ) ≤ 1 - s := by linarith
  have := mul_nonneg h1 h2
  unfold pushFactor
  linarith

theorem one_le_pushFactor (t : unitInterval) {s : ℝ} (hs : s ≤ 1) : 1 ≤ pushFactor t s := by
  have h1 : (0 : ℝ) ≤ 1 - (t : ℝ) := by have := t.2.2; linarith
  have h2 : (0 : ℝ) ≤ 1 - s := by linarith
  have := mul_nonneg h1 h2
  unfold pushFactor
  linarith

theorem pushFactor_one (s : ℝ) : pushFactor 1 s = 1 := by
  unfold pushFactor
  have : ((1 : unitInterval) : ℝ) = 1 := rfl
  rw [this]
  ring

theorem pushFactor_of_norm_one (t : unitInterval) : pushFactor t 1 = 1 := by
  unfold pushFactor; ring

/-- The pushed radius stays in `[0,1]`: `s + (1-t)·s·(1-s) ≤ 2s - s² ≤ 1`. -/
theorem pushFactor_mul_le_one (t : unitInterval) {s : ℝ} (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    pushFactor t s * s ≤ 1 := by
  have ht0 : (0 : ℝ) ≤ (t : ℝ) := t.2.1
  have ht1 : (1 : ℝ) - (t : ℝ) ≤ 1 := by linarith
  have hstep : pushFactor t s * s ≤ 2 * s - s ^ 2 := by
    unfold pushFactor
    nlinarith [mul_nonneg hs0 (by linarith : (0 : ℝ) ≤ 1 - s)]
  nlinarith [sq_nonneg (s - 1)]

/-- **The base push on the base disk.** -/
def pushDisk (t : unitInterval) (z : Disk) : Disk :=
  ⟨(pushFactor t ‖(z : ℂ)‖ : ℂ) * (z : ℂ), by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (pushFactor_nonneg t z.2)]
    exact pushFactor_mul_le_one t (norm_nonneg _) z.2⟩

@[simp] theorem pushDisk_coe (t : unitInterval) (z : Disk) :
    ((pushDisk t z : Disk) : ℂ) = (pushFactor t ‖(z : ℂ)‖ : ℂ) * (z : ℂ) := rfl

theorem norm_pushDisk (t : unitInterval) (z : Disk) :
    ‖((pushDisk t z : Disk) : ℂ)‖ = pushFactor t ‖(z : ℂ)‖ * ‖(z : ℂ)‖ := by
  rw [pushDisk_coe, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pushFactor_nonneg t z.2)]

/-- The push never decreases the base radius. -/
theorem norm_le_norm_pushDisk (t : unitInterval) (z : Disk) :
    ‖(z : ℂ)‖ ≤ ‖((pushDisk t z : Disk) : ℂ)‖ := by
  rw [norm_pushDisk]
  nlinarith [one_le_pushFactor t z.2, norm_nonneg (z : ℂ)]

/-- At `t = 1` the push is the identity. -/
theorem pushDisk_one (z : Disk) : pushDisk 1 z = z := by
  refine Subtype.ext ?_
  rw [pushDisk_coe, pushFactor_one]
  simp

/-- **Seam compatibility**: on the base equator the push is the identity at every time. -/
theorem pushDisk_of_norm_one {z : Disk} (hz : ‖(z : ℂ)‖ = 1) (t : unitInterval) :
    pushDisk t z = z := by
  refine Subtype.ext ?_
  rw [pushDisk_coe, hz, pushFactor_of_norm_one]
  simp

/-- At `t = 0` the radius is `ψ(s) = s(2 - s)`. -/
theorem norm_pushDisk_zero (z : Disk) :
    ‖((pushDisk 0 z : Disk) : ℂ)‖ = ‖(z : ℂ)‖ * (2 - ‖(z : ℂ)‖) := by
  rw [norm_pushDisk]
  have h : ((0 : unitInterval) : ℝ) = 0 := rfl
  unfold pushFactor
  rw [h]
  ring

/-- `ψ(s) = s(2 - s)` is strictly increasing on `[0, 1]`. -/
theorem psi_lt_psi {a b : ℝ} (_ha : 0 ≤ a) (hab : a < b) (hb : b ≤ 1) :
    a * (2 - a) < b * (2 - b) := by nlinarith

theorem continuous_pushDisk :
    Continuous (fun p : unitInterval × Disk => pushDisk p.1 p.2) := by
  refine Continuous.subtype_mk ?_ _
  refine Continuous.mul ?_ (continuous_subtype_val.comp continuous_snd)
  refine Complex.continuous_ofReal.comp ?_
  unfold pushFactor
  exact continuous_const.add
    ((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).mul
      (continuous_const.sub
        (continuous_norm.comp (continuous_subtype_val.comp continuous_snd))))

/-! ## §2. The push descends to `E` -/

/-- The push at the level of the two-chart disjoint union: chart 0 is pushed in the base, chart 1 is
fixed. -/
def pushSum : ResChart ⊕ ResChart → unitInterval → ResE
  | Sum.inl p => fun t => chart0 (pushDisk t p.1, p.2)
  | Sum.inr q => fun _ => chart1 q

/-- **The push respects the weld.** A weld forces base norm `1`, where the push is the identity. -/
theorem pushSum_respects (t : unitInterval) {a b : ResChart ⊕ ResChart}
    (h : SKEFTHawking.KummerResolutionPiece.resRel a b) : pushSum a t = pushSum b t := by
  rcases h with rfl | hg
  · rfl
  · cases a with
    | inl p =>
      cases b with
      | inl _ => exact (hg : False).elim
      | inr q =>
        have hglue : SKEFTHawking.KummerResolutionPiece.glued p q := hg
        show chart0 (pushDisk t p.1, p.2) = chart1 q
        rw [pushDisk_of_norm_one hglue.1 t]
        exact chart0_eq_chart1_iff.mpr hglue
    | inr q =>
      cases b with
      | inr _ => exact (hg : False).elim
      | inl p =>
        have hglue : SKEFTHawking.KummerResolutionPiece.glued p q := hg
        show chart1 q = chart0 (pushDisk t p.1, p.2)
        rw [pushDisk_of_norm_one hglue.1 t]
        exact (chart0_eq_chart1_iff.mpr hglue).symm

/-- **The base push on `E`.** -/
def basePush : ResE × unitInterval → ResE :=
  fun p => Quotient.liftOn p.1 (fun a => pushSum a p.2) (fun _ _ h => pushSum_respects p.2 h)

@[simp] theorem basePush_chart0 (p : ResChart) (t : unitInterval) :
    basePush (chart0 p, t) = chart0 (pushDisk t p.1, p.2) := rfl

@[simp] theorem basePush_chart1 (q : ResChart) (t : unitInterval) :
    basePush (chart1 q, t) = chart1 q := rfl

theorem continuous_pushSum :
    Continuous (fun p : (ResChart ⊕ ResChart) × unitInterval => pushSum p.1 p.2) := by
  have hg0 : Continuous (fun q : ResChart × unitInterval =>
      chart0 (pushDisk q.2 q.1.1, q.1.2)) :=
    continuous_chart0.comp (Continuous.prodMk
      (continuous_pushDisk.comp
        (Continuous.prodMk continuous_snd (continuous_fst.comp continuous_fst)))
      (continuous_snd.comp continuous_fst))
  have hg1 : Continuous (fun q : ResChart × unitInterval => chart1 q.1) :=
    continuous_chart1.comp continuous_fst
  have hcongr : (fun p : (ResChart ⊕ ResChart) × unitInterval => pushSum p.1 p.2)
      = (Sum.elim (fun q : ResChart × unitInterval => chart0 (pushDisk q.2 q.1.1, q.1.2))
          (fun q : ResChart × unitInterval => chart1 q.1))
        ∘ Homeomorph.sumProdDistrib := by
    funext p
    obtain ⟨a, t⟩ := p
    cases a with
    | inl q => rfl
    | inr q => rfl
  rw [hcongr]
  exact (hg0.sumElim hg1).comp Homeomorph.sumProdDistrib.continuous

theorem continuous_basePush : Continuous basePush := by
  have hq : Topology.IsQuotientMap (Quotient.mk resSetoid) := isQuotientMap_quotient_mk'
  exact hq.continuous_lift_prod_left continuous_pushSum

/-- **`basePush(·, 1) = id`.** -/
theorem basePush_one (x : ResE) : basePush (x, 1) = x := by
  induction x using Quotient.ind with
  | _ a =>
    cases a with
    | inl p =>
      show chart0 (pushDisk 1 p.1, p.2) = chart0 p
      exact congrArg chart0 (Prod.ext (pushDisk_one p.1) rfl)
    | inr q => rfl

/-! ## §3. Invariance properties -/

/-- The push does not change the fiber coordinate, so it preserves every fiber condition — in
particular `outerE` and `∂E`. -/
theorem basePush_mem_outerE {x : ResE} (hx : x ∈ outerE) (t : unitInterval) :
    basePush (x, t) ∈ outerE := by
  induction x using Quotient.ind with
  | _ a =>
    cases a with
    | inl p =>
      show (1 : ℝ) / 2 ≤ ‖((p.2 : Disk) : ℂ)‖
      exact hx
    | inr q => exact hx

theorem basePush_mem_boundaryE {x : ResE} (hx : x ∈ boundaryE) (t : unitInterval) :
    basePush (x, t) ∈ boundaryE := by
  obtain ⟨p, hp, rfl | rfl⟩ := hx
  · exact ⟨(pushDisk t p.1, p.2), hp, Or.inl rfl⟩
  · exact ⟨p, hp, Or.inr rfl⟩

/-- The push only increases the base radius, so it preserves every chart-1 neighbourhood. -/
theorem basePush_mem_chartNbhd1 {s : ℝ} (hs : s < 1) {x : ResE} (hx : x ∈ chartNbhd1 s)
    (t : unitInterval) : basePush (x, t) ∈ chartNbhd1 s := by
  intro hmem
  refine hx ?_
  induction x using Quotient.ind with
  | _ a =>
    cases a with
    | inl p =>
      obtain ⟨p', hp', hmk⟩ := hmem
      have hmk' : chart0 p' = chart0 (pushDisk t p.1, p.2) := hmk
      have heq : p' = (pushDisk t p.1, p.2) := chart0_inj_iff.mp hmk'
      have hle : ‖((p'.1 : Disk) : ℂ)‖ ≤ s := hp'
      rw [heq] at hle
      refine ⟨p, ?_, rfl⟩
      show ‖((p.1 : Disk) : ℂ)‖ ≤ s
      exact le_trans (norm_le_norm_pushDisk t p.1) hle
    | inr q =>
      exfalso
      obtain ⟨p', hp', hmk⟩ := hmem
      have hmk' : chart0 p' = chart1 q := hmk
      obtain ⟨hseam, -, -⟩ := chart0_eq_chart1_iff.mp hmk'
      have hle : ‖((p'.1 : Disk) : ℂ)‖ ≤ s := hp'
      rw [hseam] at hle
      linarith

/-- **The landing property.** At `t = 0` a point outside the deep chart-0 disk of radius `r'` has
base radius `> r'(2 - r')`; the hypothesis `r < r'(2 - r')` puts it inside `chartNbhd1 r`. -/
theorem basePush_zero_mem_chartNbhd1 {r r' : ℝ} (hr'0 : 0 ≤ r') (_hr'1 : r' < 1)
    (hpsi : r < r' * (2 - r')) {x : ResE} (hx : x ∈ chartNbhd1 r') :
    basePush (x, 0) ∈ chartNbhd1 r := by
  intro hmem
  induction x using Quotient.ind with
  | _ a =>
    cases a with
    | inl p =>
      obtain ⟨p', hp', hmk⟩ := hmem
      have hmk' : chart0 p' = chart0 (pushDisk 0 p.1, p.2) := hmk
      have heq : p' = (pushDisk 0 p.1, p.2) := chart0_inj_iff.mp hmk'
      have hle : ‖((p'.1 : Disk) : ℂ)‖ ≤ r := hp'
      rw [heq] at hle
      -- `x ∈ chartNbhd1 r'` forces `‖p.1‖ > r'`
      have hgt : r' < ‖((p.1 : Disk) : ℂ)‖ := by
        by_contra hcon
        exact hx ⟨p, le_of_not_gt hcon, rfl⟩
      have hzero : ‖((pushDisk 0 p.1 : Disk) : ℂ)‖
          = ‖((p.1 : Disk) : ℂ)‖ * (2 - ‖((p.1 : Disk) : ℂ)‖) := norm_pushDisk_zero p.1
      rw [hzero] at hle
      have := psi_lt_psi hr'0 hgt p.1.2
      linarith
    | inr q =>
      obtain ⟨p', hp', hmk⟩ := hmem
      have hmk' : chart0 p' = chart1 q := hmk
      obtain ⟨hseam, -, -⟩ := chart0_eq_chart1_iff.mp hmk'
      have hle : ‖((p'.1 : Disk) : ℂ)‖ ≤ r := hp'
      rw [hseam] at hle
      have : r' * (2 - r') ≤ 1 := by nlinarith [sq_nonneg (r' - 1)]
      linarith

theorem chartNbhd1_mono {a b : ℝ} (hab : a ≤ b) : chartNbhd1 b ⊆ chartNbhd1 a := by
  intro y hy hmem
  obtain ⟨p, hp, rfl⟩ := hmem
  refine hy ⟨p, ?_, rfl⟩
  show ‖((p.1 : Disk) : ℂ)‖ ≤ b
  exact le_trans hp hab

/-- The push preserves the retained chart-1 piece: `splitBOpen r = outerE ∪ chartNbhd1 r` is a union
of an `outerE`-condition and a `chartNbhd1`-condition, both preserved. -/
theorem basePush_mem_chart1Piece {r r' : ℝ} (hr1 : r < 1) (hr'1 : r' < 1)
    {x : ResE} (hx : x ∈ chart1Piece r r') (t : unitInterval) :
    basePush (x, t) ∈ chart1Piece r r' := by
  refine ⟨basePush_mem_chartNbhd1 hr'1 hx.1 t, ?_⟩
  rcases hx.2 with hout | hnb
  · exact Or.inl (basePush_mem_outerE hout t)
  · exact Or.inr (basePush_mem_chartNbhd1 hr1 hnb t)

theorem chartNbhd1_subset_chart1Piece {r r' : ℝ} (hr' : r' ≤ r) :
    chartNbhd1 r ⊆ chart1Piece r r' :=
  fun _ hy => ⟨chartNbhd1_mono hr' hy, Or.inr hy⟩

/-! ## §4. The retained piece retracts onto `chartNbhd1 r` -/

variable (r r' : ℝ)

/-- The retained chart-1 piece as a space. -/
abbrev Chart1PieceTop : TopCat := sub (X := ResEtop) (chart1Piece r r')

/-- The chart-1 neighbourhood at the single threshold, as a space. -/
abbrev Chart1NbhdTop : TopCat := sub (X := ResEtop) (chartNbhd1 r)

variable {r r'}

/-- The retraction of the retained piece onto `chartNbhd1 r`. -/
def pieceRetr (hr'0 : 0 ≤ r') (hr'1 : r' < 1) (hpsi : r < r' * (2 - r')) :
    C(↑(Chart1PieceTop r r'), ↑(Chart1NbhdTop r)) where
  toFun e := ⟨basePush (e.1, 0), basePush_zero_mem_chartNbhd1 hr'0 hr'1 hpsi e.2.1⟩
  continuous_toFun :=
    (continuous_basePush.comp (continuous_subtype_val.prodMk continuous_const)).subtype_mk _

/-- The inclusion `chartNbhd1 r ↪ chart1Piece r r'`. -/
def pieceIncl (hr' : r' ≤ r) : C(↑(Chart1NbhdTop r), ↑(Chart1PieceTop r r')) :=
  ⟨fun b => ⟨b.1, chartNbhd1_subset_chart1Piece hr' b.2⟩, continuous_subtype_val.subtype_mk _⟩

/-- The push homotopy inside the retained piece. -/
def pieceHomotopy (hr1 : r < 1) (hr'1 : r' < 1) :
    C(↑(Chart1PieceTop r r') × unitInterval, ↑(Chart1PieceTop r r')) where
  toFun p := ⟨basePush (p.1.1, p.2), basePush_mem_chart1Piece hr1 hr'1 p.1.2 p.2⟩
  continuous_toFun :=
    (continuous_basePush.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).subtype_mk _

/-- The push homotopy inside `chartNbhd1 r`. -/
def nbhdHomotopy (hr1 : r < 1) :
    C(↑(Chart1NbhdTop r) × unitInterval, ↑(Chart1NbhdTop r)) where
  toFun p := ⟨basePush (p.1.1, p.2), basePush_mem_chartNbhd1 hr1 p.1.2 p.2⟩
  continuous_toFun :=
    (continuous_basePush.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).subtype_mk _

theorem mapInt_pieceRetr_bijective (hr1 : r < 1) (hr'0 : 0 ≤ r') (hr'1 : r' < 1)
    (hr' : r' ≤ r) (hpsi : r < r' * (2 - r')) (n : ℕ) :
    Function.Bijective (Homology.mapInt (X := Chart1PieceTop r r') (Y := Chart1NbhdTop r)
      (pieceRetr hr'0 hr'1 hpsi) (n + 1)) :=
  Homology.mapInt_bijective_of_homotopyEquiv (pieceRetr hr'0 hr'1 hpsi) (pieceIncl hr')
    (pieceHomotopy hr1 hr'1)
    (ContinuousMap.ext fun _ => Subtype.ext rfl)
    (ContinuousMap.ext fun e => Subtype.ext (basePush_one e.1))
    (nbhdHomotopy hr1)
    (ContinuousMap.ext fun _ => Subtype.ext rfl)
    (ContinuousMap.ext fun b => Subtype.ext (basePush_one b.1)) n

/-- **`Hₙ₊₁(chartNbhd1 r' ∩ splitBOpen r; ℤ) ≅ Hₙ₊₁(chartNbhd1 r; ℤ)`** — the second threshold is
homologically invisible. -/
def chart1PieceHomologyEquiv (hr1 : r < 1) (hr'0 : 0 ≤ r') (hr'1 : r' < 1) (hr' : r' ≤ r)
    (hpsi : r < r' * (2 - r')) (n : ℕ) :
    Homology (Chart1PieceTop r r') (n + 1) ≃ₗ[ℤ] Homology (Chart1NbhdTop r) (n + 1) :=
  LinearEquiv.ofBijective _ (mapInt_pieceRetr_bijective hr1 hr'0 hr'1 hr' hpsi n)

/-! ## §5. The same for the boundary regions -/

def bdryRetr (hr'0 : 0 ≤ r') (hr'1 : r' < 1) (hpsi : r < r' * (2 - r')) :
    C(↑(BdryRegion (chartNbhd1 r')), ↑(BdryRegion (chartNbhd1 r))) where
  toFun e := ⟨basePush (e.1, 0), basePush_mem_boundaryE e.2.1 0,
    basePush_zero_mem_chartNbhd1 hr'0 hr'1 hpsi e.2.2⟩
  continuous_toFun :=
    (continuous_basePush.comp (continuous_subtype_val.prodMk continuous_const)).subtype_mk _

def bdryIncl (hr' : r' ≤ r) :
    C(↑(BdryRegion (chartNbhd1 r)), ↑(BdryRegion (chartNbhd1 r'))) :=
  ⟨fun b => ⟨b.1, b.2.1, chartNbhd1_mono hr' b.2.2⟩, continuous_subtype_val.subtype_mk _⟩

def bdryHomotopy (hs : r' < 1) :
    C(↑(BdryRegion (chartNbhd1 r')) × unitInterval, ↑(BdryRegion (chartNbhd1 r'))) where
  toFun p := ⟨basePush (p.1.1, p.2), basePush_mem_boundaryE p.1.2.1 p.2,
    basePush_mem_chartNbhd1 hs p.1.2.2 p.2⟩
  continuous_toFun :=
    (continuous_basePush.comp
      ((continuous_subtype_val.comp continuous_fst).prodMk continuous_snd)).subtype_mk _

theorem mapInt_bdryRetr_bijective (hr1 : r < 1) (hr'0 : 0 ≤ r') (hr'1 : r' < 1)
    (hr' : r' ≤ r) (hpsi : r < r' * (2 - r')) (n : ℕ) :
    Function.Bijective (Homology.mapInt (X := BdryRegion (chartNbhd1 r'))
      (Y := BdryRegion (chartNbhd1 r)) (bdryRetr hr'0 hr'1 hpsi) (n + 1)) :=
  Homology.mapInt_bijective_of_homotopyEquiv (bdryRetr hr'0 hr'1 hpsi) (bdryIncl hr')
    (bdryHomotopy hr'1)
    (ContinuousMap.ext fun _ => Subtype.ext rfl)
    (ContinuousMap.ext fun e => Subtype.ext (basePush_one e.1))
    (bdryHomotopy hr1)
    (ContinuousMap.ext fun _ => Subtype.ext rfl)
    (ContinuousMap.ext fun b => Subtype.ext (basePush_one b.1)) n

/-- **`Hₙ₊₁(∂E ∩ chartNbhd1 r'; ℤ) ≅ Hₙ₊₁(∂E ∩ chartNbhd1 r; ℤ)`.** -/
def bdryRegionHomologyEquiv (hr1 : r < 1) (hr'0 : 0 ≤ r') (hr'1 : r' < 1) (hr' : r' ≤ r)
    (hpsi : r < r' * (2 - r')) (n : ℕ) :
    Homology (BdryRegion (chartNbhd1 r')) (n + 1)
      ≃ₗ[ℤ] Homology (BdryRegion (chartNbhd1 r)) (n + 1) :=
  LinearEquiv.ofBijective _ (mapInt_bdryRetr_bijective hr1 hr'0 hr'1 hr' hpsi n)

/-! ## §6. The headline at a SINGLE threshold -/

/-- **The `H₂(K3;ℤ) ≅ ℤ²²` headline on two facts at one threshold.**

With `0 < r' < r < r'(2 - r')` (e.g. `r' = 1/4`, `r = 3/8`), it follows from

* `H₂(chartNbhd1 r; ℤ) = 0` and `H₁(chartNbhd1 r; ℤ) = 0` — the chart-1 neighbourhood, a
  `D² × D²` chart region fattened slightly past the base equator, is acyclic; and
* `H₁(∂E ∩ chartNbhd1 r; ℤ)` cyclic — the part of the boundary lens space `∂E ≅ ℝP³` lying over
  that base disk is a solid torus.

The auxiliary threshold `r'`, which the corner-dodging excision forced, has been retracted away by
the base push; it survives only as the numerical side condition relating the two radii. -/
theorem kummerK3_b2_target_of_chartNbhd1 {r r' : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (hr'0 : 0 ≤ r')
    (hr'1 : r' < 1) (hr' : r' < r) (hpsi : r < r' * (2 - r'))
    (h2 : ∀ x : Homology (Chart1NbhdTop r) 2, x = 0)
    (h1 : ∀ x : Homology (Chart1NbhdTop r) 1, x = 0)
    (hbdry : ∃ a : Homology (BdryRegion (chartNbhd1 r)) 1,
      ∀ x : Homology (BdryRegion (chartNbhd1 r)) 1, ∃ k : ℤ, x = k • a) :
    SKEFTHawking.KummerK7Opener.kummerK3_b2_target := by
  refine kummerK3_b2_target_of_chart1_bdry hr0 hr1 hr'1 hr' ?_ ?_ ?_
  · intro x
    refine (chart1PieceHomologyEquiv hr1 hr'0 hr'1 (le_of_lt hr') hpsi 1).injective ?_
    rw [map_zero]
    exact h2 _
  · intro x
    refine (chart1PieceHomologyEquiv hr1 hr'0 hr'1 (le_of_lt hr') hpsi 0).injective ?_
    rw [map_zero]
    exact h1 _
  · obtain ⟨a, hgen⟩ := hbdry
    exact ⟨(bdryRegionHomologyEquiv hr1 hr'0 hr'1 (le_of_lt hr') hpsi 0).symm a,
      cyclic_of_surjective
        (bdryRegionHomologyEquiv hr1 hr'0 hr'1 (le_of_lt hr') hpsi 0).symm.toLinearMap
        (bdryRegionHomologyEquiv hr1 hr'0 hr'1 (le_of_lt hr') hpsi 0).symm.surjective hgen⟩

/-- **The side condition is satisfiable** — `r' = 1/4`, `r = 3/8` meet every hypothesis of
`kummerK3_b2_target_of_chartNbhd1`, so the reduction is not vacuous on its numerics. -/
theorem quarter_threshold_admissible :
    (0 : ℝ) ≤ 3 / 8 ∧ (3 : ℝ) / 8 < 1 ∧ (0 : ℝ) ≤ 1 / 4 ∧ (1 : ℝ) / 4 < 1 ∧
      (1 : ℝ) / 4 < 3 / 8 ∧ (3 : ℝ) / 8 < (1 / 4) * (2 - 1 / 4) := by
  norm_num

end

end SKEFTHawking.KummerBasePushRetractInt
