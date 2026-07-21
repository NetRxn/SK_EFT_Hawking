/-
# Phase 5q.H — K6′b Leg 16: A SMOOTH LOCAL SECTION OF THE SEAM BOUNDARY MAP

The two remaining weld-atlas transition classes, (1,3) and (2,3), need the collar identification in
**both** directions. `KummerSeamSmooth.contMDiff_bdryMapRP3` (plus the chart-level product formula
of `KummerSeamCollarSmooth`) gives the direction `ℝP³ → ∂E`. This module builds the *other*
direction locally: an **explicit smooth right inverse** of the chart-0 boundary coordinates.

**The obstruction, named.** In chart-0 coordinates the boundary map is the Hopf-type formula
`hopf0 (a, b) = (a/b, (b/‖b‖)²)` (`KummerSeamSmooth.hopf0`). Inverting it means taking a **square
root of the fiber phase** — which is exactly why the reverse direction is not a formal consequence
of the forward one, and why it is only ever *locally* defined (the two square roots differ by a
sign; that sign ambiguity is precisely the `S³ → ℝP³` double cover).

**The resolution (§1).** On the unit circle minus `−1` there is an explicit smooth square root

    phaseSqrt u = (1 + u) / ‖1 + u‖ ,

since `u = e^{iθ}` with `|θ| < π` gives `1 + u = 2cos(θ/2)·e^{iθ/2}`. The identity
`phaseSqrt u ^ 2 = u` is proved from `‖1+u‖² = (1+u)(1 + u⁻¹) = (1+u)²/u`, using
`conj u = u⁻¹` on the unit circle.

**The section (§2, §3).**

    seamSection0 (β, u) = ρ(β) · (β · s(u), s(u)),   ρ(β) = (1 + ‖β‖²)^(−1/2),  s = phaseSqrt

lands on `S³` (`seamSection0_mem`), inverts the Hopf coordinates (`hopf0_seamSection0`), is smooth
wherever `1 + u ≠ 0` (`contDiffOn_seamSection0` — note `ρ` is smooth *globally*, since `‖β‖²` is),
and satisfies the section identity

    bdryMap (seamPoint0 (β,u)) = chart0 (β, u)     (`bdryMap_seamPoint0`, for `‖β‖ ≤ 1`, `‖u‖ = 1`).

**Residual (sharply named).** What is NOT here: the chart-1 and equatorial-annulus analogues, the
descent of the section through `mkRP3` into the stereographic `ℝP³` atlas of `KummerRP3Smooth`, and
therefore the transition classes themselves. This module supplies the piece that had no substrate
at all; the rest is composition with already-built layers.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerSeamSmooth

namespace SKEFTHawking.KummerSeamSection

open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerSeamSmooth

noncomputable section

variable {k : WithTop ℕ∞}

/-! ## §1. A smooth local square root of a unit complex number -/

/-- **The principal phase square root** `s(u) = (1 + u)/‖1 + u‖`. For `‖u‖ = 1` and `u ≠ −1` this is
the unit complex number with `s(u)² = u` (writing `u = e^{iθ}` with `|θ| < π`,
`1 + u = 2cos(θ/2) e^{iθ/2}`). It is smooth wherever `1 + u ≠ 0`. -/
def phaseSqrt (u : ℂ) : ℂ := (1 + u) / ((‖1 + u‖ : ℝ) : ℂ)

theorem norm_phaseSqrt {u : ℂ} (h : 1 + u ≠ 0) : ‖phaseSqrt u‖ = 1 := by
  have hn : ‖1 + u‖ ≠ 0 := norm_ne_zero_iff.mpr h
  rw [phaseSqrt, norm_div, Complex.norm_real, Real.norm_eq_abs, abs_norm, div_self hn]

theorem phaseSqrt_ne_zero {u : ℂ} (h : 1 + u ≠ 0) : phaseSqrt u ≠ 0 :=
  norm_ne_zero_iff.mp (by rw [norm_phaseSqrt h]; norm_num)

/-- **The square-root identity.** On the unit circle minus `−1`, `phaseSqrt` squares to the
identity: `‖1 + u‖² = (1+u)·conj(1+u) = (1+u)(1 + u⁻¹) = (1+u)²/u`. -/
theorem phaseSqrt_sq {u : ℂ} (hu : ‖u‖ = 1) (h : 1 + u ≠ 0) : phaseSqrt u ^ 2 = u := by
  have hune : u ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hu; norm_num at hu
  have hconj : (starRingEnd ℂ) u = u⁻¹ := (Complex.inv_eq_conj hu).symm
  have hsq : ((‖1 + u‖ : ℝ) : ℂ) ^ 2 = (1 + u) ^ 2 / u := by
    have h1 : ((‖1 + u‖ : ℝ) : ℂ) ^ 2 = (1 + u) * (starRingEnd ℂ) (1 + u) := by
      rw [Complex.mul_conj, ← Complex.sq_norm]
      norm_cast
    rw [h1, map_add, map_one, hconj]
    field_simp
    ring
  have hn : ((‖1 + u‖ : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr h
  rw [phaseSqrt, div_pow, hsq]
  field_simp

theorem contDiffOn_phaseSqrt : ContDiffOn ℝ k phaseSqrt {u : ℂ | 1 + u ≠ 0} := by
  have h1 : ContDiffOn ℝ k (fun u : ℂ => 1 + u) {u : ℂ | 1 + u ≠ 0} :=
    (contDiff_const.add contDiff_id).contDiffOn
  have hinv : ContDiffOn ℝ k (fun u : ℂ => (‖1 + u‖)⁻¹) {u : ℂ | 1 + u ≠ 0} :=
    (h1.norm ℝ (fun u hu => hu)).inv (fun u hu => norm_ne_zero_iff.mpr hu)
  refine (hinv.smul h1).congr ?_
  intro u hu
  simp only [Pi.smul_apply']
  rw [phaseSqrt, div_eq_inv_mul, ← Complex.ofReal_inv]
  norm_cast

/-! ## §2. The explicit smooth section of the chart-0 boundary coordinates -/

/-- The `S³` radial normalization `ρ(β) = (1 + ‖β‖²)^(−1/2)`. -/
def seamRho (β : ℂ) : ℝ := 1 / Real.sqrt (1 + ‖β‖ ^ 2)

theorem seamRho_pos (β : ℂ) : 0 < seamRho β := by
  have h : (0 : ℝ) < 1 + ‖β‖ ^ 2 := by positivity
  exact div_pos one_pos (Real.sqrt_pos.mpr h)

theorem seamRho_sq (β : ℂ) : seamRho β ^ 2 * (1 + ‖β‖ ^ 2) = 1 := by
  have h : (0 : ℝ) < 1 + ‖β‖ ^ 2 := by positivity
  rw [seamRho, div_pow, one_pow, Real.sq_sqrt h.le]
  field_simp

/-- **THE SECTION.** `seamSection0 (β, u) = ρ(β) · (β · s(u), s(u))` — the point of `S³` whose Hopf
chart-0 coordinates are `(β, u)`. -/
def seamSection0 (q : ℂ × ℂ) : ℂ × ℂ :=
  (((seamRho q.1 : ℝ) : ℂ) * (q.1 * phaseSqrt q.2), ((seamRho q.1 : ℝ) : ℂ) * phaseSqrt q.2)

theorem norm_seamSection0_fst {q : ℂ × ℂ} (h : 1 + q.2 ≠ 0) :
    ‖(seamSection0 q).1‖ = seamRho q.1 * ‖q.1‖ := by
  rw [seamSection0]
  show ‖((seamRho q.1 : ℝ) : ℂ) * (q.1 * phaseSqrt q.2)‖ = _
  rw [norm_mul, norm_mul, norm_phaseSqrt h, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (seamRho_pos q.1)]

theorem norm_seamSection0_snd {q : ℂ × ℂ} (h : 1 + q.2 ≠ 0) :
    ‖(seamSection0 q).2‖ = seamRho q.1 := by
  rw [seamSection0]
  show ‖((seamRho q.1 : ℝ) : ℂ) * phaseSqrt q.2‖ = _
  rw [norm_mul, norm_phaseSqrt h, mul_one, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (seamRho_pos q.1)]

/-- **The section lands on `S³`.** -/
theorem seamSection0_mem {q : ℂ × ℂ} (h : 1 + q.2 ≠ 0) :
    ‖(seamSection0 q).1‖ ^ 2 + ‖(seamSection0 q).2‖ ^ 2 = 1 := by
  rw [norm_seamSection0_fst h, norm_seamSection0_snd h, mul_pow, ← seamRho_sq q.1]
  ring

/-- The `S³` point cut out by the section. -/
def seamPoint0 {q : ℂ × ℂ} (h : 1 + q.2 ≠ 0) : S3 := ⟨seamSection0 q, seamSection0_mem h⟩

/-- **The section inverts the Hopf chart-0 coordinates.** -/
theorem hopf0_seamSection0 {q : ℂ × ℂ} (hu : ‖q.2‖ = 1) (h : 1 + q.2 ≠ 0) :
    hopf0 (seamSection0 q) = q := by
  have hs : phaseSqrt q.2 ≠ 0 := phaseSqrt_ne_zero h
  have hρ : ((seamRho q.1 : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (seamRho_pos q.1)
  refine Prod.ext ?_ ?_
  · rw [hopf0_fst, seamSection0]
    show ((seamRho q.1 : ℝ) : ℂ) * (q.1 * phaseSqrt q.2) / (((seamRho q.1 : ℝ) : ℂ)
      * phaseSqrt q.2) = q.1
    field_simp
  · rw [hopf0_snd, norm_seamSection0_snd h, seamSection0]
    show (((seamRho q.1 : ℝ) : ℂ) * phaseSqrt q.2 / ((seamRho q.1 : ℝ) : ℂ)) ^ 2 = q.2
    rw [mul_comm, mul_div_assoc, div_self hρ, mul_one, phaseSqrt_sq hu h]

theorem contDiff_seamRho : ContDiff ℝ k seamRho :=
  contDiff_const.div ((contDiff_const.add (contDiff_norm_sq ℝ)).sqrt (fun _ => by positivity))
    (fun _ => Real.sqrt_ne_zero'.mpr (by positivity))

theorem contDiffOn_seamSection0 :
    ContDiffOn ℝ k seamSection0 {q : ℂ × ℂ | 1 + q.2 ≠ 0} := by
  have hρ : ContDiffOn ℝ k (fun q : ℂ × ℂ => ((seamRho q.1 : ℝ) : ℂ))
      {q : ℂ × ℂ | 1 + q.2 ≠ 0} :=
    (Complex.ofRealCLM.contDiff.comp (contDiff_seamRho.comp contDiff_fst)).contDiffOn
  have hs : ContDiffOn ℝ k (fun q : ℂ × ℂ => phaseSqrt q.2) {q : ℂ × ℂ | 1 + q.2 ≠ 0} :=
    contDiffOn_phaseSqrt.comp contDiff_snd.contDiffOn (fun q hq => hq)
  exact (hρ.mul (contDiff_fst.contDiffOn.mul hs)).prodMk (hρ.mul hs)

/-! ## §3. The section is a genuine right inverse of the boundary map -/

theorem norm_seamSection0_fst_le {q : ℂ × ℂ} (hβ : ‖q.1‖ ≤ 1) (h : 1 + q.2 ≠ 0) :
    ‖(seamSection0 q).1‖ ≤ ‖(seamSection0 q).2‖ := by
  rw [norm_seamSection0_fst h, norm_seamSection0_snd h]
  nlinarith [seamRho_pos q.1]

/-- **THE SECTION IDENTITY.** `bdryMap` carries the explicit `S³` point `seamPoint0 (β, u)` to the
chart-0 boundary point with base `β` and unit fiber `u`. Together with `contDiffOn_seamSection0`
this is a *smooth local right inverse* of the seam parametrization in chart-0 coordinates — the
piece the thickened-collar transition classes need in the direction that
`KummerSeamSmooth.contMDiff_bdryMapRP3` does not supply. -/
theorem bdryMap_seamPoint0 {q : ℂ × ℂ} (hβ : ‖q.1‖ ≤ 1) (hu : ‖q.2‖ = 1) (h : 1 + q.2 ≠ 0) :
    bdryMap (seamPoint0 h) = chart0 (⟨q.1, hβ⟩, ⟨q.2, le_of_eq hu⟩) := by
  have hle : ‖((seamPoint0 h : S3) : ℂ × ℂ).1‖ ≤ ‖((seamPoint0 h : S3) : ℂ × ℂ).2‖ :=
    norm_seamSection0_fst_le hβ h
  rw [bdryMap_eq_chart0 hle]
  refine congrArg chart0 (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
  · rw [hopfChart0_fst_coe]
    exact congrArg Prod.fst (hopf0_seamSection0 hu h)
  · rw [hopfChart0_snd_coe]
    exact congrArg Prod.snd (hopf0_seamSection0 hu h)

end

end SKEFTHawking.KummerSeamSection
