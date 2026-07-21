/-
# Phase 5q.H — K6′b Leg 5: the E-side of the seam has a genuine product collar `ℝP³ × [1/2, 1]`

The third (and last) chart family of the Kummer weld atlas is the **seam double collar** — a
neighbourhood of the welded seam charted by gluing the `Q`-side boundary collar to the `E`-side
boundary collar across `bdryMapRP3`. This module builds the **E half** of that double collar, as a
concrete product structure rather than an abstract "collar exists" claim.

**The construction.** The banked fiber-scaling deformation `KummerResolutionPiece.deform` scales the
disk-bundle fiber, and the banked `KummerWeldFiberFlow.fiberNorm` reads the fiber radius off
chart-independently. Compose them at the boundary: `eCollar (r, t) := deform (bdryMapRP3 r, t)`.
Then `fiberNorm (eCollar (r, t)) = t` exactly (§2), so the second coordinate IS the collar's radial
parameter — no auxiliary retraction is needed.

**What makes it a collar and not merely a parametrization** is §1: `deform (·, t)` is **injective**
for every `t ≠ 0` (`deform_injective`). This is new — `KummerResolutionPiece` §9 banks only that the
deformation is continuous and its two endpoint slices, never that the intermediate slices are
embeddings. The proof unwinds the weld: same-chart representatives cancel the scalar `t` off the
fiber, and the cross-chart case cancels it off the clutch identity `w' = z² w`, recovering `glued`
at scale `1` from `glued` at scale `t`.

**The payoff (§4)**: `eCollarHomeo : ℝP³ × [1/2, 1] ≃ₜ {x : E ∣ 1/2 ≤ fiberNorm x}`. Compact source,
Hausdorff target (`instT2SpaceResE`), continuous bijection — so the E-side collar region is
*literally* a product, with `{1} ↔ ∂E = seam` and `{1/2}` the inner collar face used by the K7
thickening (`KummerK7MVAssembly.eOuterCarrier`).

**Residual (sharply named).** The Q-side collar (`qCollarHomeo`) and the glue of the two halves
across `bdryMapRP3` — the actual chart family 3/3 — are NOT built here. What is built here is the
E half of it, plus the general slice-injectivity of `deform` that half rests on.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerWeldQInterior

namespace SKEFTHawking.KummerSeamCollarE

open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerWeldFiberFlow

noncomputable section

/-! ## §1. The intermediate slices of the fiber-scaling deformation are injective -/

/-- **Every nonzero slice of the fiber-scaling deformation is injective.** `KummerResolutionPiece`
§9 banks continuity and the two endpoint slices of `deform`; this is the missing structural fact
that the *intermediate* slices are embeddings, which is what turns "scale the boundary inwards"
into a genuine collar.

Cancelling `t` is legitimate in all three cases: same-chart representatives cancel it off the fiber
coordinate; the cross-chart case cancels it off the clutch identity `w' = z² · w`, so `glued` at
scale `t` forces `glued` at scale `1`. -/
theorem deform_injective {t : unitInterval} (ht : (t : ℝ) ≠ 0) {x y : ResE}
    (h : deform (x, t) = deform (y, t)) : x = y := by
  have htc : ((t : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ht
  induction x using Quotient.ind with | _ a =>
  induction y using Quotient.ind with | _ b =>
  cases a with
  | inl p =>
    cases b with
    | inl q =>
      have hpq : (p.1, scaleDisk t p.2) = (q.1, scaleDisk t q.2) := chart0_inj_iff.mp h
      have h1 : p.1 = q.1 := (Prod.ext_iff.mp hpq).1
      have h2 : ((t : ℝ) : ℂ) * (p.2 : ℂ) = ((t : ℝ) : ℂ) * (q.2 : ℂ) :=
        congrArg (fun r : ResChart => (r.2 : ℂ)) hpq
      exact congrArg chart0 (Prod.ext h1 (Subtype.ext (mul_left_cancel₀ htc h2)))
    | inr q =>
      obtain ⟨hz, hq1, hq2⟩ := chart0_eq_chart1_iff.mp h
      show chart0 p = chart1 q
      refine chart0_eq_chart1_iff.mpr ⟨hz, hq1, ?_⟩
      refine mul_left_cancel₀ htc ?_
      calc ((t : ℝ) : ℂ) * (q.2 : ℂ) = (p.1 : ℂ) ^ 2 * (((t : ℝ) : ℂ) * (p.2 : ℂ)) := hq2
        _ = ((t : ℝ) : ℂ) * ((p.1 : ℂ) ^ 2 * (p.2 : ℂ)) := by ring
  | inr p =>
    cases b with
    | inl q =>
      obtain ⟨hz, hq1, hq2⟩ := chart0_eq_chart1_iff.mp h.symm
      show chart1 p = chart0 q
      refine ((chart0_eq_chart1_iff (p := q) (q := p)).mpr ⟨hz, hq1, ?_⟩).symm
      refine mul_left_cancel₀ htc ?_
      calc ((t : ℝ) : ℂ) * (p.2 : ℂ) = (q.1 : ℂ) ^ 2 * (((t : ℝ) : ℂ) * (q.2 : ℂ)) := hq2
        _ = ((t : ℝ) : ℂ) * ((q.1 : ℂ) ^ 2 * (q.2 : ℂ)) := by ring
    | inr q =>
      have hpq : (p.1, scaleDisk t p.2) = (q.1, scaleDisk t q.2) := chart1_inj_iff.mp h
      have h1 : p.1 = q.1 := (Prod.ext_iff.mp hpq).1
      have h2 : ((t : ℝ) : ℂ) * (p.2 : ℂ) = ((t : ℝ) : ℂ) * (q.2 : ℂ) :=
        congrArg (fun r : ResChart => (r.2 : ℂ)) hpq
      exact congrArg chart1 (Prod.ext h1 (Subtype.ext (mul_left_cancel₀ htc h2)))

/-! ## §2. The deformation scales the fiber norm exactly -/

/-- **The fiber norm scales exactly**: `fiberNorm (deform (x, t)) = t · fiberNorm x`. The radial
bookkeeping law that makes the collar parameter readable off the ambient space. -/
theorem fiberNorm_deform (x : ResE) (t : unitInterval) :
    fiberNorm (deform (x, t)) = (t : ℝ) * fiberNorm x := by
  induction x using Quotient.ind with | _ a =>
  cases a with
  | inl p =>
    show ‖((t : ℝ) : ℂ) * (p.2 : ℂ)‖ = (t : ℝ) * ‖(p.2 : ℂ)‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (unitInterval.nonneg t)]
  | inr p =>
    show ‖((t : ℝ) : ℂ) * (p.2 : ℂ)‖ = (t : ℝ) * ‖(p.2 : ℂ)‖
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (unitInterval.nonneg t)]

/-! ## §3. The E-side collar map `ℝP³ × [0,1] → E` -/

/-- **The E-side collar map** `(r, t) ↦ deform (bdryMapRP3 r, t)` — push the seam point `r` inwards
to fiber radius `t`. -/
def eCollar (p : RP3 × unitInterval) : ResE := deform (bdryMapRP3 p.1, p.2)

theorem continuous_eCollar : Continuous eCollar :=
  continuous_deform.comp ((continuous_bdryMapRP3.comp continuous_fst).prodMk continuous_snd)

/-- **The collar parameter IS the fiber radius**: `fiberNorm (eCollar (r, t)) = t`. (Uses
`fiberNorm_bdryMapRP3 : fiberNorm (bdryMapRP3 r) = 1`.) -/
@[simp] theorem fiberNorm_eCollar (p : RP3 × unitInterval) : fiberNorm (eCollar p) = (p.2 : ℝ) := by
  rw [eCollar, fiberNorm_deform, fiberNorm_bdryMapRP3, mul_one]

/-- **The `t = 1` face of the collar is the seam** — `eCollar (r, 1) = bdryMapRP3 r`. -/
@[simp] theorem eCollar_one (r : RP3) : eCollar (r, 1) = bdryMapRP3 r := deform_one _

/-- **The collar map is injective away from the zero section** — two collar points with the same
image have the same radius (`fiberNorm_eCollar`) and, after cancelling it (`deform_injective`), the
same seam point (`bdryMapRP3_injective`). -/
theorem eCollar_injOn {p q : RP3 × unitInterval} (hp : (p.2 : ℝ) ≠ 0) (h : eCollar p = eCollar q) :
    p = q := by
  obtain ⟨r, t⟩ := p
  obtain ⟨r', t'⟩ := q
  have ht : (t : ℝ) = (t' : ℝ) := by
    rw [← fiberNorm_eCollar (r, t), ← fiberNorm_eCollar (r', t'), h]
  have ht' : t = t' := Subtype.ext ht
  subst ht'
  exact Prod.ext (bdryMapRP3_injective (deform_injective hp h)) rfl

/-- **Chart-level unscaling** — a nonzero fiber coordinate is its norm times a unit vector. -/
theorem exists_unit_scale {z : ℂ} (hz : z ≠ 0) :
    ∃ w : Disk, ‖(w : ℂ)‖ = 1 ∧ ((‖z‖ : ℝ) : ℂ) * (w : ℂ) = z := by
  have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
  have hnc : ((‖z‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hn
  have hnorm : ‖z / ((‖z‖ : ℝ) : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self hn]
  exact ⟨⟨z / ((‖z‖ : ℝ) : ℂ), le_of_eq hnorm⟩, hnorm, by
    show ((‖z‖ : ℝ) : ℂ) * (z / ((‖z‖ : ℝ) : ℂ)) = z
    field_simp⟩

/-- **The collar map is onto the positive-radius locus** — every point of `E` with fiber radius
`t > 0` is the seam point of its fiber pushed in to radius `t`. Combined with `eCollar_injOn` this
says the collar map parametrizes `E ∖ (zero section)` as `ℝP³ × (0, 1]`. -/
theorem eCollar_surjOn {x : ResE} (hx : 0 < fiberNorm x) :
    ∃ p : RP3 × unitInterval, eCollar p = x ∧ ((p.2 : ℝ)) = fiberNorm x := by
  obtain ⟨a, rfl⟩ := Quotient.exists_rep x
  set t : unitInterval := ⟨fiberNorm (Quotient.mk resSetoid a), hx.le,
    fiberNorm_le_one _⟩ with htdef
  have key : ∃ y : ResE, y ∈ boundaryE ∧ deform (y, t) = Quotient.mk resSetoid a := by
    cases a with
    | inl p =>
      have hnz : (p.2 : ℂ) ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hx)
      obtain ⟨w, hw1, hw2⟩ := exists_unit_scale hnz
      exact ⟨chart0 (p.1, w), ⟨(p.1, w), hw1, Or.inl rfl⟩,
        congrArg chart0 (Prod.ext rfl (Subtype.ext hw2))⟩
    | inr p =>
      have hnz : (p.2 : ℂ) ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hx)
      obtain ⟨w, hw1, hw2⟩ := exists_unit_scale hnz
      exact ⟨chart1 (p.1, w), ⟨(p.1, w), hw1, Or.inr rfl⟩,
        congrArg chart1 (Prod.ext rfl (Subtype.ext hw2))⟩
  obtain ⟨y, hy, hyx⟩ := key
  obtain ⟨r, hr⟩ : y ∈ Set.range bdryMapRP3 := by rw [range_bdryMapRP3_eq_boundaryE]; exact hy
  exact ⟨(r, t), by rw [eCollar, hr]; exact hyx, rfl⟩

/-! ## §4. THE E-SIDE COLLAR IS A PRODUCT — `ℝP³ × [1/2, 1] ≃ₜ {1/2 ≤ fiberNorm}` -/

/-- The collar's radial parameter range `[1/2, 1] ⊂ [0, 1]`. -/
def collarParam : Set unitInterval := {t : unitInterval | 1 / 2 ≤ (t : ℝ)}

theorem isClosed_collarParam : IsClosed collarParam :=
  isClosed_le continuous_const continuous_subtype_val

instance instCompactSpaceCollarParam : CompactSpace ↥collarParam :=
  isCompact_iff_compactSpace.mp isClosed_collarParam.isCompact

/-- **The E-side collar region** of the seam — the outer half of the disk bundle's fibers. This is
exactly the fiber condition of `KummerK7MVAssembly.eOuterCarrier`, whose weld image `eOuter` is the
K7 collar-thickening of the seam. -/
def eCollarSet : Set ResE := {x : ResE | 1 / 2 ≤ fiberNorm x}

/-- The collar map restricted to the collar region, as a map of subtypes. -/
def eCollarRestrict (p : RP3 × ↥collarParam) : ↥eCollarSet :=
  ⟨eCollar (p.1, p.2.1), by
    show 1 / 2 ≤ fiberNorm (eCollar (p.1, p.2.1))
    rw [fiberNorm_eCollar]
    exact p.2.2⟩

theorem continuous_eCollarRestrict : Continuous eCollarRestrict :=
  Continuous.subtype_mk
    (continuous_eCollar.comp (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))) _

theorem bijective_eCollarRestrict : Function.Bijective eCollarRestrict := by
  constructor
  · rintro ⟨r, t⟩ ⟨r', t'⟩ h
    have hpos : (0 : ℝ) < (t.1 : ℝ) := lt_of_lt_of_le (by norm_num) t.2
    have heq : eCollar (r, t.1) = eCollar (r', t'.1) := congrArg Subtype.val h
    have := eCollar_injOn (p := (r, t.1)) (q := (r', t'.1)) (ne_of_gt hpos) heq
    exact Prod.ext (Prod.ext_iff.mp this).1 (Subtype.ext (Prod.ext_iff.mp this).2)
  · rintro ⟨x, hx⟩
    have hpos : 0 < fiberNorm x := lt_of_lt_of_le (by norm_num) hx
    obtain ⟨⟨r, t⟩, hrt, htv⟩ := eCollar_surjOn hpos
    refine ⟨(r, ⟨t, ?_⟩), Subtype.ext hrt⟩
    show 1 / 2 ≤ (t : ℝ)
    rw [htv]; exact hx

/-- **THE E-SIDE OF THE SEAM IS A PRODUCT COLLAR** `ℝP³ × [1/2, 1] ≃ₜ {x ∣ 1/2 ≤ fiberNorm x}`,
with the `t = 1` face carried onto the seam `∂E` (`eCollar_one`). Continuous bijection from a
compact space to a Hausdorff one (`instT2SpaceResE`), so a homeomorphism.

This is the **E half of the seam double collar** — the third chart family of the weld atlas glues
this to the `Q`-side collar across `bdryMapRP3` (whose smoothness is
`KummerSeamSmooth.contMDiff_bdryMapRP3`). -/
def eCollarHomeo : (RP3 × ↥collarParam) ≃ₜ ↥eCollarSet :=
  Continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ bijective_eCollarRestrict)
    continuous_eCollarRestrict

@[simp] theorem eCollarHomeo_apply (p : RP3 × ↥collarParam) :
    (eCollarHomeo p : ResE) = eCollar (p.1, p.2.1) := rfl

/-- **The collar's outer face is exactly the seam** — the `t = 1` slice of the product collar is
`∂E = range bdryMapRP3`, the welded seam. -/
theorem eCollarHomeo_one_face (r : RP3) :
    (eCollarHomeo (r, ⟨1, by show (1:ℝ)/2 ≤ (1:ℝ); norm_num⟩) : ResE) = bdryMapRP3 r :=
  eCollar_one r

end

end SKEFTHawking.KummerSeamCollarE
