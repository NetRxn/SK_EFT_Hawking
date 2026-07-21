/-
# Phase 5q.H — K6′b Leg 17: the BASED smooth section of the seam boundary map

`KummerSeamSection` built one explicit smooth right inverse of the chart-0 boundary map, resting on
the principal phase square root `phaseSqrt u = (1+u)/‖1+u‖`. That branch is undefined at `u = −1`,
so a *single* section cannot cover the whole seam. This module removes the restriction with a
**one-parameter family of branches**, indexed by the square root `m` at the base point:

    phaseSqrtAt m u = m · phaseSqrt (u / m²) ,      (phaseSqrtAt m (m²) = m)

which is smooth on `{u ∣ u ≠ −m²}` — the antipode of the base value. Since every unit `u₀` has a
square root (`exists_sq_eq_of_norm_one`), **every** point of the seam has a smooth local section
through it, with no branch obstruction anywhere. The section is

    seamSectionAt m q = m • seamSection0 (q.1, q.2 / m²)

(a *unit* rescaling of the principal section at a rotated fiber phase), so every property of §2–§3
of `KummerSeamSection` transfers by the two scaling laws `hopf0_smul_unit` and `norm` invariance —
no second geometric argument.

**Why the sign is free.** `seamSectionAt (−m) = −seamSectionAt m`: the two square roots of `m²`
give antipodal `S³` points, hence the *same* `ℝP³` point (`mkRP3_seamPointAt_neg`). So a local
section can always be normalised to land in whichever hemisphere a given `ℝP³` chart needs.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.KummerSeamSection

namespace SKEFTHawking.KummerSeamSectionAt

open SKEFTHawking.KummerResolutionPiece
open SKEFTHawking.KummerSeamSmooth
open SKEFTHawking.KummerSeamSection

noncomputable section

variable {k : WithTop ℕ∞}

/-! ## §1. Unit rescaling laws for the Hopf chart-0 coordinates -/

/-- Scaling both `ℂ` coordinates by a unit leaves the affine base coordinate alone and multiplies
the squared fiber phase by `m²`. -/
theorem hopf0_smul_unit {m : ℂ} (hm : ‖m‖ = 1) (x : ℂ × ℂ) :
    hopf0 (m * x.1, m * x.2) = ((hopf0 x).1, m ^ 2 * (hopf0 x).2) := by
  have hm0 : m ≠ 0 := by
    intro h; rw [h, norm_zero] at hm; norm_num at hm
  refine Prod.ext ?_ ?_
  · rw [hopf0_fst, hopf0_fst]
    by_cases hx : x.2 = 0
    · rw [hx, mul_zero]; simp
    · show m * x.1 / (m * x.2) = x.1 / x.2
      rw [mul_div_mul_left _ _ hm0]
  · rw [hopf0_snd, hopf0_snd]
    show ((m * x.2) / ((‖m * x.2‖ : ℝ) : ℂ)) ^ 2 = m ^ 2 * (x.2 / ((‖x.2‖ : ℝ) : ℂ)) ^ 2
    rw [norm_mul, hm, one_mul, mul_div_assoc, mul_pow]

/-- Every unit complex number has a unit square root — the fact that removes the branch
obstruction. -/
theorem exists_sq_eq_of_norm_one {u : ℂ} (hu : ‖u‖ = 1) : ∃ m : ℂ, ‖m‖ = 1 ∧ m ^ 2 = u := by
  by_cases h : 1 + u = 0
  · refine ⟨Complex.I * phaseSqrt (-u), ?_, ?_⟩
    · have hnu : ‖(-u : ℂ)‖ = 1 := by rwa [norm_neg]
      have hne : 1 + (-u) ≠ 0 := by
        intro hc
        rw [show (1 : ℂ) + -u = 1 - u by ring] at hc
        have hu1 : u = 1 := by linear_combination -hc
        rw [hu1] at h; norm_num at h
      rw [norm_mul, Complex.norm_I, one_mul, norm_phaseSqrt hne]
    · have hnu : ‖(-u : ℂ)‖ = 1 := by rwa [norm_neg]
      have hne : 1 + (-u) ≠ 0 := by
        intro hc
        rw [show (1 : ℂ) + -u = 1 - u by ring] at hc
        have hu1 : u = 1 := by linear_combination -hc
        rw [hu1] at h; norm_num at h
      rw [mul_pow, Complex.I_sq, phaseSqrt_sq hnu hne]
      ring
  · exact ⟨phaseSqrt u, norm_phaseSqrt h, phaseSqrt_sq hu h⟩

/-! ## §2. The based phase square root -/

/-- **The based phase square root.** `phaseSqrtAt m u` is the branch of `√u` normalised so that it
takes the value `m` at `u = m²`; it is smooth on the complement of `−m²`. -/
def phaseSqrtAt (m u : ℂ) : ℂ := m * phaseSqrt (u / m ^ 2)

/-- The smooth domain of the `m`-branch: everything but the antipode `−m²` of the base value. -/
def seamDomAt (m : ℂ) : Set (ℂ × ℂ) := {q : ℂ × ℂ | 1 + q.2 / m ^ 2 ≠ 0}

theorem isOpen_seamDomAt (m : ℂ) : IsOpen (seamDomAt m) := by
  refine IsOpen.preimage (f := fun q : ℂ × ℂ => 1 + q.2 / m ^ 2) ?_ isOpen_compl_singleton
  exact continuous_const.add (continuous_snd.div_const _)

theorem mem_seamDomAt_iff {m : ℂ} {q : ℂ × ℂ} : q ∈ seamDomAt m ↔ 1 + q.2 / m ^ 2 ≠ 0 := Iff.rfl

/-- **The base value is always in the smooth domain** — `1 + m²/m² = 2 ≠ 0`. -/
theorem mem_seamDomAt_base {m : ℂ} (hm : ‖m‖ = 1) (β : ℂ) : (β, m ^ 2) ∈ seamDomAt m := by
  have hm0 : m ≠ 0 := by
    intro h; rw [h, norm_zero] at hm; norm_num at hm
  have hsq : (m : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ hm0
  show (1 : ℂ) + m ^ 2 / m ^ 2 ≠ 0
  rw [div_self hsq]
  norm_num

theorem norm_phaseSqrtAt {m u : ℂ} (hm : ‖m‖ = 1) (h : 1 + u / m ^ 2 ≠ 0) :
    ‖phaseSqrtAt m u‖ = 1 := by
  rw [phaseSqrtAt, norm_mul, hm, one_mul, norm_phaseSqrt h]

theorem phaseSqrtAt_sq {m u : ℂ} (hm : ‖m‖ = 1) (hu : ‖u‖ = 1) (h : 1 + u / m ^ 2 ≠ 0) :
    phaseSqrtAt m u ^ 2 = u := by
  have hm0 : m ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hm; norm_num at hm
  have hsq : (m : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ hm0
  have hnorm : ‖u / m ^ 2‖ = 1 := by
    rw [norm_div, hu, norm_pow, hm, one_pow, div_one]
  rw [phaseSqrtAt, mul_pow, phaseSqrt_sq hnorm h]
  field_simp

/-- The branch takes the value `m` at the base point `m²`. -/
theorem phaseSqrtAt_base {m : ℂ} (hm : ‖m‖ = 1) : phaseSqrtAt m (m ^ 2) = m := by
  have hm0 : m ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hm; norm_num at hm
  have hsq : (m : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ hm0
  rw [phaseSqrtAt, div_self hsq, phaseSqrt]
  norm_num

/-! ## §3. The based section -/

/-- **THE BASED SECTION.** A unit rescaling of the principal section at a rotated fiber phase:
`seamSectionAt m q = m · seamSection0 (q.1, q.2/m²)`. -/
def seamSectionAt (m : ℂ) (q : ℂ × ℂ) : ℂ × ℂ :=
  (m * (seamSection0 (q.1, q.2 / m ^ 2)).1, m * (seamSection0 (q.1, q.2 / m ^ 2)).2)

theorem seamSectionAt_one (q : ℂ × ℂ) : seamSectionAt 1 q = seamSection0 q := by
  refine Prod.ext ?_ ?_ <;>
    simp only [seamSectionAt, one_pow, div_one, one_mul, Prod.mk.eta]

theorem norm_seamSectionAt_fst {m : ℂ} (hm : ‖m‖ = 1) (q : ℂ × ℂ) :
    ‖(seamSectionAt m q).1‖ = ‖(seamSection0 (q.1, q.2 / m ^ 2)).1‖ := by
  show ‖m * (seamSection0 (q.1, q.2 / m ^ 2)).1‖ = _
  rw [norm_mul, hm, one_mul]

theorem norm_seamSectionAt_snd {m : ℂ} (hm : ‖m‖ = 1) (q : ℂ × ℂ) :
    ‖(seamSectionAt m q).2‖ = ‖(seamSection0 (q.1, q.2 / m ^ 2)).2‖ := by
  show ‖m * (seamSection0 (q.1, q.2 / m ^ 2)).2‖ = _
  rw [norm_mul, hm, one_mul]

/-- **The based section lands on `S³`.** -/
theorem seamSectionAt_mem {m : ℂ} (hm : ‖m‖ = 1) {q : ℂ × ℂ} (h : q ∈ seamDomAt m) :
    ‖(seamSectionAt m q).1‖ ^ 2 + ‖(seamSectionAt m q).2‖ ^ 2 = 1 := by
  rw [norm_seamSectionAt_fst hm q, norm_seamSectionAt_snd hm q]
  exact seamSection0_mem (q := (q.1, q.2 / m ^ 2)) h

/-- The `S³` point cut out by the based section. -/
def seamPointAt {m : ℂ} (hm : ‖m‖ = 1) {q : ℂ × ℂ} (h : q ∈ seamDomAt m) : S3 :=
  ⟨seamSectionAt m q, seamSectionAt_mem hm h⟩

@[simp] theorem seamPointAt_coe {m : ℂ} (hm : ‖m‖ = 1) {q : ℂ × ℂ} (h : q ∈ seamDomAt m) :
    ((seamPointAt hm h : S3) : ℂ × ℂ) = seamSectionAt m q := rfl

/-- **The based section inverts the Hopf chart-0 coordinates.** -/
theorem hopf0_seamSectionAt {m : ℂ} (hm : ‖m‖ = 1) {q : ℂ × ℂ} (hu : ‖q.2‖ = 1)
    (h : q ∈ seamDomAt m) : hopf0 (seamSectionAt m q) = q := by
  have hm0 : m ≠ 0 := by
    intro h0; rw [h0, norm_zero] at hm; norm_num at hm
  have hsq : (m : ℂ) ^ 2 ≠ 0 := pow_ne_zero _ hm0
  have hnorm : ‖q.2 / m ^ 2‖ = 1 := by
    rw [norm_div, hu, norm_pow, hm, one_pow, div_one]
  have hbase : hopf0 (seamSection0 (q.1, q.2 / m ^ 2)) = (q.1, q.2 / m ^ 2) :=
    hopf0_seamSection0 (q := (q.1, q.2 / m ^ 2)) hnorm h
  have hstep : hopf0 (seamSectionAt m q)
      = ((hopf0 (seamSection0 (q.1, q.2 / m ^ 2))).1,
         m ^ 2 * (hopf0 (seamSection0 (q.1, q.2 / m ^ 2))).2) :=
    hopf0_smul_unit hm (seamSection0 (q.1, q.2 / m ^ 2))
  rw [hstep, hbase]
  refine Prod.ext rfl ?_
  show m ^ 2 * (q.2 / m ^ 2) = q.2
  field_simp

theorem norm_seamSectionAt_fst_le {m : ℂ} (hm : ‖m‖ = 1) {q : ℂ × ℂ} (hβ : ‖q.1‖ ≤ 1)
    (h : q ∈ seamDomAt m) : ‖(seamSectionAt m q).1‖ ≤ ‖(seamSectionAt m q).2‖ := by
  rw [norm_seamSectionAt_fst hm q, norm_seamSectionAt_snd hm q]
  exact norm_seamSection0_fst_le (q := (q.1, q.2 / m ^ 2)) hβ h

/-- **THE BASED SECTION IDENTITY** — the boundary map carries the based section point to the
chart-0 boundary point with base `q.1` and unit fiber `q.2`, at *every* fiber phase (the `m`-branch
covers every point of the seam). -/
theorem bdryMap_seamPointAt {m : ℂ} (hm : ‖m‖ = 1) {q : ℂ × ℂ} (hβ : ‖q.1‖ ≤ 1) (hu : ‖q.2‖ = 1)
    (h : q ∈ seamDomAt m) :
    bdryMap (seamPointAt hm h) = chart0 (⟨q.1, hβ⟩, ⟨q.2, le_of_eq hu⟩) := by
  have hle : ‖((seamPointAt hm h : S3) : ℂ × ℂ).1‖ ≤ ‖((seamPointAt hm h : S3) : ℂ × ℂ).2‖ :=
    norm_seamSectionAt_fst_le hm hβ h
  rw [bdryMap_eq_chart0 hle]
  refine congrArg chart0 (Prod.ext (Subtype.ext ?_) (Subtype.ext ?_))
  · rw [hopfChart0_fst_coe]
    exact congrArg Prod.fst (hopf0_seamSectionAt hm hu h)
  · rw [hopfChart0_snd_coe]
    exact congrArg Prod.snd (hopf0_seamSectionAt hm hu h)

/-! ## §4. Smoothness, and the free sign -/

theorem contDiffOn_seamSectionAt (m : ℂ) : ContDiffOn ℝ k (seamSectionAt m) (seamDomAt m) := by
  have hrot : ContDiff ℝ k (fun q : ℂ × ℂ => (q.1, q.2 / m ^ 2)) :=
    contDiff_fst.prodMk (contDiff_snd.div_const _)
  have hmaps : ∀ q ∈ seamDomAt m,
      (fun q : ℂ × ℂ => (q.1, q.2 / m ^ 2)) q ∈ {r : ℂ × ℂ | 1 + r.2 ≠ 0} := fun q hq => hq
  have hcomp : ContDiffOn ℝ k (fun q : ℂ × ℂ => seamSection0 (q.1, q.2 / m ^ 2)) (seamDomAt m) :=
    contDiffOn_seamSection0.comp hrot.contDiffOn hmaps
  exact ((contDiff_const.contDiffOn).mul hcomp.fst).prodMk ((contDiff_const.contDiffOn).mul hcomp.snd)

/-- **The two square roots of the base value give antipodal section points** — hence the *same*
point of `ℝP³`. This is what makes the branch choice free: a local section can be normalised into
whichever hemisphere a given `ℝP³` chart needs. -/
theorem seamSectionAt_neg (m : ℂ) (q : ℂ × ℂ) :
    seamSectionAt (-m) q = (-(seamSectionAt m q).1, -(seamSectionAt m q).2) := by
  refine Prod.ext ?_ ?_ <;>
  · show -m * _ = -(m * _)
    rw [neg_sq]
    ring

theorem mem_seamDomAt_neg (m : ℂ) (q : ℂ × ℂ) : q ∈ seamDomAt (-m) ↔ q ∈ seamDomAt m := by
  show (1 : ℂ) + q.2 / (-m) ^ 2 ≠ 0 ↔ (1 : ℂ) + q.2 / m ^ 2 ≠ 0
  rw [neg_sq]

theorem seamPointAt_neg {m : ℂ} (hm : ‖m‖ = 1) (hm' : ‖(-m)‖ = 1) {q : ℂ × ℂ}
    (h : q ∈ seamDomAt m) (h' : q ∈ seamDomAt (-m)) :
    seamPointAt hm' h' = negS3 (seamPointAt hm h) :=
  Subtype.ext (seamSectionAt_neg m q)

/-- **The branch sign is invisible in `ℝP³`.** -/
theorem mkRP3_seamPointAt_neg {m : ℂ} (hm : ‖m‖ = 1) (hm' : ‖(-m)‖ = 1) {q : ℂ × ℂ}
    (h : q ∈ seamDomAt m) (h' : q ∈ seamDomAt (-m)) :
    mkRP3 (seamPointAt hm' h') = mkRP3 (seamPointAt hm h) := by
  rw [seamPointAt_neg hm hm' h h', mkRP3_neg]

end

end SKEFTHawking.KummerSeamSectionAt
