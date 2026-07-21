/-
# Phase 5q.H — K6′b Leg 19: the E-SIDE SEAM PARAMETRIZATION IN CHART COORDINATES

The two open weld-atlas transition classes (1,3) and (2,3) compare an *interior* chart of a weld
piece with the *seam* chart. On the E side the comparison needs one explicit identity: what the seam
parametrization `seamParam c : ℝP³ × (−1/8,1/2) → K3` looks like when its value is read in an
E-interior chart.

**§1 — the collar bookkeeping (chart-free).** On the `E` half of the double collar the parameter is
just the complement of the fiber radius:

    seamParam c (mkRP3 σ, 1 − t) = weldMk (inr (c, deform (bdryMap σ, t))) ,   0 ≤ t ≤ 1 .

**§2 — the fiber-scaled boundary point, per chart.** `deform (bdryMap σ, t)` is the boundary point
of `σ` pushed to fiber radius `t`, and in each of the three E-interior charts it is the *product*
`(β, t·ζ)` of the boundary datum with the scaling `t` (`deform_bdryMap_chart0` /
`_chart1` / `annulusTrivFun_deform_bdryMap`) — the chart-level product statement of
`KummerSeamCollarSmooth`, now on the interior charts rather than the collar charts.

**§3 — the section closes the loop.** Feeding `KummerSeamSectionAt`'s based section into §1–§2
produces, for *any* fiber phase, an explicit `(r, v) ∈ ℝP³ × (−1/8,1/2)` whose seam-parametrization
value is a prescribed collar-band point of the `c`-th E-interior copy
(`seamParam_eq_weldMk_chart0`). The `ℝP³` coordinate `r = mkRP3 (seamPointAt …)` is an explicitly
`C^k` function of the chart coordinates, which is exactly the direction
`KummerSeamSmooth.contMDiff_bdryMapRP3` does not supply.

**§4, §5 — the other two branches are the SAME section.** `hopf1 (swap x) = hopf0 x` is definitional,
so the `chart1` hemisphere is served by the *swapped* section point `seamPointAt1` — no second
inversion (`seamParam_eq_weldMk_chart1`). And `seamAnnulusFiber_eq` shows the unified equatorial
fiber coordinate is `ζ = (β/‖β‖)·u`, i.e. the `regDir` twist that `annulusTriv` applies is exactly
the unit part of the base coordinate; so the equatorial branch is the chart-0 section at the
*rotated* fiber phase `u = ζ·‖β‖/β` (`seamParam_eq_weldMk_annulus`). One section, three branches.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerSeamSectionAt
import SKEFTHawking.KummerSeamChart
import SKEFTHawking.KummerEIntChartCoord

namespace SKEFTHawking.KummerSeamCollarCoord

open Set Topology
open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerResolutionPieceBoundary
open SKEFTHawking.KummerWeldFiberFlow
open SKEFTHawking.KummerWeld
open SKEFTHawking.KummerSeamSmooth
open SKEFTHawking.KummerSeamSection
open SKEFTHawking.KummerSeamSectionAt
open SKEFTHawking.KummerSeamCollarE (eCollar)
open SKEFTHawking.KummerSeamDoubleCollar
open SKEFTHawking.KummerSeamChart

noncomputable section

/-! ## §1. The `E` half of the double collar, chart-free -/

/-- **The `E`-half collar bookkeeping.** On the `E` side the seam parameter is `1 − t`, where `t` is
the fiber radius the boundary point is pushed to. -/
theorem seamParam_eq_weldMk (c : EIndex) (σ : S3) {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hv : (1 - t) ∈ openParam) :
    seamParam c (mkRP3 σ, ⟨1 - t, hv⟩)
      = weldMk (Sum.inr (c, deform (bdryMap σ, ⟨t, ht0, ht1⟩))) := by
  have hnn : (0 : ℝ) ≤ ((toDbl ⟨1 - t, hv⟩ : ↥dblParam) : ℝ) := by
    show (0 : ℝ) ≤ 1 - t; linarith
  have hE : clampE (toDbl ⟨1 - t, hv⟩) = (⟨t, ht0, ht1⟩ : unitInterval) := by
    apply Subtype.ext
    rw [clampE_coe]
    show 1 - max (1 - t) 0 = t
    rw [max_eq_left (by linarith)]
    ring
  show dblCollar c (mkRP3 σ, toDbl ⟨1 - t, hv⟩) = _
  rw [dblCollar_of_nonneg c hnn]
  show weldMk (Sum.inr (c, eCollar (mkRP3 σ, clampE (toDbl ⟨1 - t, hv⟩)))) = _
  rw [hE]
  rfl

/-! ## §2. The fiber-scaled boundary point in the three E-interior charts -/

/-- **Chart-0 branch** — on the chart-0 hemisphere the fiber-scaled boundary point is
`chart0 (β, t·u)` with `(β, u) = hopf0 σ`. -/
theorem deform_bdryMap_chart0 {σ : S3} (h : ‖(σ : ℂ × ℂ).1‖ ≤ ‖(σ : ℂ × ℂ).2‖) (t : unitInterval) :
    deform (bdryMap σ, t)
      = chart0 ((hopfChart0 h).1, scaleDisk t (hopfChart0 h).2) := by
  rw [bdryMap_eq_chart0 h]
  rfl

/-- **Chart-1 branch.** -/
theorem deform_bdryMap_chart1 {σ : S3} (h : ¬ ‖(σ : ℂ × ℂ).1‖ ≤ ‖(σ : ℂ × ℂ).2‖)
    (t : unitInterval) :
    deform (bdryMap σ, t)
      = chart1 ((hopfChart1 h).1, scaleDisk t (hopfChart1 h).2) := by
  rw [bdryMap_eq_chart1 h]
  rfl

/-- **Equatorial branch** — in the annulus trivialization the fiber-scaled boundary point is the
product `(seamAnnulusBase σ, t · seamAnnulusFiberD σ)`. -/
theorem annulusTrivFun_deform_bdryMap {σ : S3} (hq : (σ : ℂ × ℂ) ∈ nearEquator)
    (t : unitInterval) :
    annulusTrivFun (deform (bdryMap σ, t))
      = (seamAnnulusBase (σ : ℂ × ℂ), scaleDisk t (seamAnnulusFiberD (σ : ℂ × ℂ))) := by
  rw [SKEFTHawking.KummerSeamCollarSmooth.annulusTrivFun_deform, annulusTrivFun_bdryMap σ hq]

/-! ## §3. Feeding in the based section: an explicit seam preimage of a collar-band point -/

/-- The unit fiber direction of a nonzero fiber coordinate. -/
def fiberDir (w : ℂ) : ℂ := w / ((‖w‖ : ℝ) : ℂ)

theorem norm_fiberDir {w : ℂ} (hw : w ≠ 0) : ‖fiberDir w‖ = 1 := by
  have hn : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
  rw [fiberDir, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self hn]

theorem scaleDisk_fiberDir {w : ℂ} (hw : w ≠ 0) (hw1 : ‖w‖ ≤ 1) :
    ((scaleDisk ⟨‖w‖, norm_nonneg w, hw1⟩ ⟨fiberDir w, le_of_eq (norm_fiberDir hw)⟩ : Disk) : ℂ)
      = w := by
  have hn : ((‖w‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr hw
  show ((‖w‖ : ℝ) : ℂ) * fiberDir w = w
  rw [fiberDir]
  field_simp

/-- **THE CHART-0 SEAM PREIMAGE.** Every collar-band point of the `c`-th E-interior copy presented
in chart-0 coordinates `(z, w)` with `1/2 < ‖w‖ ≤ 1` is the seam-parametrization value of the
explicit pair `(mkRP3 (seamPointAt …), 1 − ‖w‖)` — for *every* fiber phase, since the based section
of `KummerSeamSectionAt` has no branch obstruction. -/
theorem seamParam_eq_weldMk_chart0 (c : EIndex) {m : ℂ} (hm : ‖m‖ = 1) {z w : ℂ}
    (hz : ‖z‖ ≤ 1) (hw0 : w ≠ 0) (hw1 : 1 / 2 < ‖w‖) (hw2 : ‖w‖ ≤ 1)
    (h : (z, fiberDir w) ∈ seamDomAt m) :
    seamParam c (mkRP3 (seamPointAt hm h),
        ⟨1 - ‖w‖, by
          constructor
          · show -(1 / 8 : ℝ) < 1 - ‖w‖; linarith
          · show 1 - ‖w‖ < 1 / 2; linarith⟩)
      = weldMk (Sum.inr (c, chart0 (⟨z, hz⟩, ⟨w, hw2⟩))) := by
  have hu : ‖fiberDir w‖ = 1 := norm_fiberDir hw0
  have hle : ‖((seamPointAt hm h : S3) : ℂ × ℂ).1‖ ≤ ‖((seamPointAt hm h : S3) : ℂ × ℂ).2‖ :=
    norm_seamSectionAt_fst_le hm hz h
  have hbdry : bdryMap (seamPointAt hm h) = chart0 (⟨z, hz⟩, ⟨fiberDir w, le_of_eq hu⟩) :=
    bdryMap_seamPointAt hm hz hu h
  rw [seamParam_eq_weldMk c (seamPointAt hm h) (norm_nonneg w) hw2, hbdry]
  refine congrArg (fun x : ResE => weldMk (Sum.inr (c, x))) ?_
  show chart0 ((⟨z, hz⟩ : Disk), scaleDisk ⟨‖w‖, norm_nonneg w, hw2⟩
    (⟨fiberDir w, le_of_eq hu⟩ : Disk)) = _
  exact congrArg chart0 (Prod.ext rfl (Subtype.ext (scaleDisk_fiberDir hw0 hw2)))

/-! ## §4. The `chart1` branch — the SAME section, swapped -/

/-- **`hopf1` is `hopf0` after a swap** — the two hemisphere formulas of the Hopf boundary map are
one formula read on the two orderings of `ℂ²`. -/
theorem hopf1_swap (x : ℂ × ℂ) : hopf1 (Prod.swap x) = hopf0 x := rfl

/-- The strict form of the hemisphere inequality for the based section — strict exactly when the
base coordinate is strictly inside the unit disk. -/
theorem norm_seamSectionAt_fst_lt {m : ℂ} (hm : ‖m‖ = 1) {q : ℂ × ℂ} (hβ : ‖q.1‖ < 1)
    (h : q ∈ seamDomAt m) : ‖(seamSectionAt m q).1‖ < ‖(seamSectionAt m q).2‖ := by
  rw [norm_seamSectionAt_fst hm q, norm_seamSectionAt_snd hm q,
    norm_seamSection0_fst (q := (q.1, q.2 / m ^ 2)) h,
    norm_seamSection0_snd (q := (q.1, q.2 / m ^ 2)) h]
  have hρ := seamRho_pos q.1
  nlinarith

/-- The swapped section point, for the `chart1` hemisphere. -/
def seamPointAt1 {m : ℂ} (hm : ‖m‖ = 1) {q : ℂ × ℂ} (h : q ∈ seamDomAt m) : S3 :=
  ⟨Prod.swap (seamSectionAt m q), by
    have h1 := seamSectionAt_mem hm h
    show ‖(seamSectionAt m q).2‖ ^ 2 + ‖(seamSectionAt m q).1‖ ^ 2 = 1
    linarith⟩

theorem bdryMap_seamPointAt1 {m : ℂ} (hm : ‖m‖ = 1) {q : ℂ × ℂ} (hβ : ‖q.1‖ < 1) (hu : ‖q.2‖ = 1)
    (h : q ∈ seamDomAt m) :
    bdryMap (seamPointAt1 hm h) = chart1 (⟨q.1, le_of_lt hβ⟩, ⟨q.2, le_of_eq hu⟩) := by
  have hlt : ‖(seamSectionAt m q).1‖ < ‖(seamSectionAt m q).2‖ :=
    norm_seamSectionAt_fst_lt hm hβ h
  have hnle : ¬ ‖((seamPointAt1 hm h : S3) : ℂ × ℂ).1‖ ≤ ‖((seamPointAt1 hm h : S3) : ℂ × ℂ).2‖ :=
    not_le.mpr hlt
  rw [bdryMap_eq_chart1 hnle]
  refine congrArg chart1 (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
  · rw [hopfChart1_fst_coe]
    show (hopf1 (Prod.swap (seamSectionAt m q))).1 = q.1
    rw [hopf1_swap]
    exact congrArg Prod.fst (hopf0_seamSectionAt hm hu h)
  · rw [hopfChart1_snd_coe]
    show (hopf1 (Prod.swap (seamSectionAt m q))).2 = q.2
    rw [hopf1_swap]
    exact congrArg Prod.snd (hopf0_seamSectionAt hm hu h)

/-- **THE CHART-1 SEAM PREIMAGE.** -/
theorem seamParam_eq_weldMk_chart1 (c : EIndex) {m : ℂ} (hm : ‖m‖ = 1) {z w : ℂ}
    (hz : ‖z‖ < 1) (hw0 : w ≠ 0) (hw1 : 1 / 2 < ‖w‖) (hw2 : ‖w‖ ≤ 1)
    (h : (z, fiberDir w) ∈ seamDomAt m) :
    seamParam c (mkRP3 (seamPointAt1 hm h),
        ⟨1 - ‖w‖, by
          constructor
          · show -(1 / 8 : ℝ) < 1 - ‖w‖; linarith
          · show 1 - ‖w‖ < 1 / 2; linarith⟩)
      = weldMk (Sum.inr (c, chart1 (⟨z, le_of_lt hz⟩, ⟨w, hw2⟩))) := by
  have hu : ‖fiberDir w‖ = 1 := norm_fiberDir hw0
  have hbdry : bdryMap (seamPointAt1 hm h)
      = chart1 (⟨z, le_of_lt hz⟩, ⟨fiberDir w, le_of_eq hu⟩) :=
    bdryMap_seamPointAt1 hm hz hu h
  rw [seamParam_eq_weldMk c (seamPointAt1 hm h) (norm_nonneg w) hw2, hbdry]
  refine congrArg (fun x : ResE => weldMk (Sum.inr (c, x))) ?_
  show chart1 ((⟨z, le_of_lt hz⟩ : Disk), scaleDisk ⟨‖w‖, norm_nonneg w, hw2⟩
    (⟨fiberDir w, le_of_eq hu⟩ : Disk)) = _
  exact congrArg chart1 (Prod.ext rfl (Subtype.ext (scaleDisk_fiberDir hw0 hw2)))

/-! ## §5. The equatorial branch — the SAME section, at a rotated fiber phase -/

/-- **The unified annulus fiber coordinate in Hopf chart-0 terms**: `ζ = (β/‖β‖)·u`. The `regDir`
twist that `annulusTriv` applies is exactly the unit part of the base coordinate. -/
theorem seamAnnulusFiber_eq {x : ℂ × ℂ} (ha : x.1 ≠ 0) (hb : x.2 ≠ 0) :
    seamAnnulusFiber x
      = ((hopf0 x).1 / ((‖(hopf0 x).1‖ : ℝ) : ℂ)) * (hopf0 x).2 := by
  have hna : ((‖x.1‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr ha
  have hnb : ((‖x.2‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hb
  have hnorm : ((‖x.1 / x.2‖ : ℝ) : ℂ) = ((‖x.1‖ : ℝ) : ℂ) / ((‖x.2‖ : ℝ) : ℂ) := by
    rw [norm_div]; push_cast; ring
  rw [hopf0_fst, hopf0_snd, hnorm, seamAnnulusFiber, Complex.ofReal_mul]
  field_simp

/-- **THE EQUATORIAL SEAM PREIMAGE, boundary half** — the based section at the rotated fiber phase
`u = ζ·‖β‖/β` realises a prescribed annulus datum `(β, ζ)`. -/
theorem annulusTrivFun_bdryMap_seamPointAt {m : ℂ} (hm : ‖m‖ = 1) {β ζ : ℂ} (hβ0 : β ≠ 0)
    (hζ : ‖ζ‖ = 1)
    (h : (β, ζ * ((‖β‖ : ℝ) : ℂ) / β) ∈ seamDomAt m)
    (hne : ((seamPointAt hm h : S3) : ℂ × ℂ) ∈ nearEquator) :
    annulusTrivFun (bdryMap (seamPointAt hm h)) = (β, ⟨ζ, le_of_eq hζ⟩) := by
  have hnβ : ((‖β‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hβ0
  have hu : ‖ζ * ((‖β‖ : ℝ) : ℂ) / β‖ = 1 := by
    rw [norm_div, norm_mul, hζ, one_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_norm, div_self (norm_ne_zero_iff.mpr hβ0)]
  have hhopf : hopf0 ((seamPointAt hm h : S3) : ℂ × ℂ) = (β, ζ * ((‖β‖ : ℝ) : ℂ) / β) :=
    hopf0_seamSectionAt hm hu h
  have ha := nearEquator_fst_ne_zero hne
  have hb := nearEquator_snd_ne_zero hne
  rw [annulusTrivFun_bdryMap _ hne]
  refine Prod.ext ?_ (Subtype.ext ?_)
  · show seamAnnulusBase ((seamPointAt hm h : S3) : ℂ × ℂ) = β
    rw [show seamAnnulusBase ((seamPointAt hm h : S3) : ℂ × ℂ)
        = (hopf0 ((seamPointAt hm h : S3) : ℂ × ℂ)).1 from (hopf0_fst _).symm, hhopf]
  · show seamAnnulusFiber ((seamPointAt hm h : S3) : ℂ × ℂ) = ζ
    rw [seamAnnulusFiber_eq ha hb, hhopf]
    show β / ((‖β‖ : ℝ) : ℂ) * (ζ * ((‖β‖ : ℝ) : ℂ) / β) = ζ
    field_simp

/-- A near-equator boundary point lies in the annulus region (its base coordinate has modulus
`> 1/2` on either hemisphere). -/
theorem bdryMap_mem_annulusRegion {σ : S3} (hne : (σ : ℂ × ℂ) ∈ nearEquator) :
    bdryMap σ ∈ annulusRegion := by
  by_cases h : ‖(σ : ℂ × ℂ).1‖ ≤ ‖(σ : ℂ × ℂ).2‖
  · exact Or.inl ⟨hopfChart0 h, half_lt_norm_hopfChart0_fst hne h, (bdryMap_eq_chart0 h).symm⟩
  · exact Or.inr ⟨hopfChart1 h, half_lt_norm_hopfChart1_fst hne h, (bdryMap_eq_chart1 h).symm⟩

/-- **THE EQUATORIAL SEAM PREIMAGE.** -/
theorem seamParam_eq_weldMk_annulus (c : EIndex) {m : ℂ} (hm : ‖m‖ = 1) {x : ResE}
    (hx : x ∈ annulusRegion) (hβ0 : (annulusTrivFun x).1 ≠ 0)
    (hζ0 : ((annulusTrivFun x).2 : ℂ) ≠ 0)
    (hζ1 : 1 / 2 < ‖((annulusTrivFun x).2 : ℂ)‖)
    (h : ((annulusTrivFun x).1,
        fiberDir ((annulusTrivFun x).2 : ℂ) * ((‖(annulusTrivFun x).1‖ : ℝ) : ℂ)
          / (annulusTrivFun x).1) ∈ seamDomAt m)
    (hne : ((seamPointAt hm h : S3) : ℂ × ℂ) ∈ nearEquator) :
    seamParam c (mkRP3 (seamPointAt hm h),
        ⟨1 - ‖((annulusTrivFun x).2 : ℂ)‖, by
          have h2 := (annulusTrivFun x).2.2
          constructor
          · show -(1 / 8 : ℝ) < 1 - ‖((annulusTrivFun x).2 : ℂ)‖; linarith
          · show 1 - ‖((annulusTrivFun x).2 : ℂ)‖ < 1 / 2; linarith⟩)
      = weldMk (Sum.inr (c, x)) := by
  set ζ : ℂ := ((annulusTrivFun x).2 : ℂ) with hζdef
  have hζ2 : ‖ζ‖ ≤ 1 := (annulusTrivFun x).2.2
  set t : unitInterval := ⟨‖ζ‖, norm_nonneg ζ, hζ2⟩ with htdef
  have hbdry : annulusTrivFun (bdryMap (seamPointAt hm h))
      = ((annulusTrivFun x).1, ⟨fiberDir ζ, le_of_eq (norm_fiberDir hζ0)⟩) :=
    annulusTrivFun_bdryMap_seamPointAt hm hβ0 (norm_fiberDir hζ0) h hne
  have hbdryReg : bdryMap (seamPointAt hm h) ∈ annulusRegion := bdryMap_mem_annulusRegion hne
  have hdefReg : deform (bdryMap (seamPointAt hm h), t) ∈ annulusRegion :=
    SKEFTHawking.KummerSeamCollarSmooth.deform_mem_annulusRegion hbdryReg t
  have hval : annulusTrivFun (deform (bdryMap (seamPointAt hm h), t)) = annulusTrivFun x := by
    rw [SKEFTHawking.KummerSeamCollarSmooth.annulusTrivFun_deform, hbdry]
    refine Prod.ext rfl (Subtype.ext ?_)
    show ((‖ζ‖ : ℝ) : ℂ) * fiberDir ζ = ζ
    have hn : ((‖ζ‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.mpr hζ0
    rw [fiberDir]; field_simp
  have hEq : deform (bdryMap (seamPointAt hm h), t) = x :=
    calc deform (bdryMap (seamPointAt hm h), t)
        = annulusTrivInv (annulusTrivFun (deform (bdryMap (seamPointAt hm h), t))) :=
          (annulusTriv_left_inv hdefReg).symm
      _ = annulusTrivInv (annulusTrivFun x) := by rw [hval]
      _ = x := annulusTriv_left_inv hx
  rw [seamParam_eq_weldMk c (seamPointAt hm h) (norm_nonneg ζ) hζ2, hEq]

end

end SKEFTHawking.KummerSeamCollarCoord
