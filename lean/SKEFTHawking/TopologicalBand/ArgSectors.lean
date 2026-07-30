import Mathlib
import SKEFTHawking.TopologicalBand.PrincipalBranch

/-!
# A rational-enclosure `arg` sector calculus (Phase 6ED, Wave 3 — promoted)

Model-independent machinery for placing `Complex.arg` of an explicitly-known complex number into a
`2π`-window **without evaluating any transcendental**. Built on `Complex.tan_arg` and `Real.arctan`
monotonicity, so every side-condition is a radical-free comparison of the number's real and
imaginary parts.

This is the observation that makes concrete FHS lattice-Chern computations tractable:
`latticeChern` is `−∑ branchIndex (rawCurl)`, a sum of **integers**, so the invariant is carried by
*which window* each raw curl falls in — a **bounding** problem, not an evaluation problem.

* `arg_eq_arctan_of_re_pos`, `arg_lt_of_slope`, `lt_arg_of_slope` — the slope-to-`arg` bridge.
* `arg_cell_A`/`_B`/`_C`/`_D` — the four sectors `[0, π/6)`, `(−π/6, 0]`, `(π/4, π/2)`,
  `(−π/2, −π/3)`, each certified by radical-free inequalities on `Re` and `Im`.
* `abs_arg_lt_pi_div_four` — the narrow sector, from `|Im z| < Re z`.
* `branchIndex_eq_zero_of` / `branchIndex_eq_one_of` — window placement for `PrincipalBranch`.

**Promoted out of `GrapheneBand.HaldaneWitness` on 2026-07-29.** Nothing here mentions graphene,
the honeycomb lattice, or any particular `d`-field; a square-lattice (QWZ) spike needs exactly this
calculus and must not have to import a graphene module to get it.
-/

namespace SKEFTHawking.TopologicalBand

open Complex Real

/-! ## Rational-enclosure `arg` sectors -/

/-- For `Re z > 0` the argument is the `arctan` of the slope. -/
theorem arg_eq_arctan_of_re_pos {z : ℂ} (h : 0 < z.re) : z.arg = Real.arctan (z.im / z.re) := by
  have habs : |z.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl h)
  rw [abs_lt] at habs
  rw [← Complex.tan_arg, Real.arctan_tan (by linarith [habs.1]) habs.2]

/-- Upper `arg` bound from a slope bound, at a reference angle `a` with known tangent. -/
theorem arg_lt_of_slope {z : ℂ} {a c : ℝ} (hre : 0 < z.re) (hta : Real.tan a = c)
    (ha1 : -(Real.pi / 2) < a) (ha2 : a < Real.pi / 2) (h : z.im < c * z.re) : z.arg < a := by
  rw [arg_eq_arctan_of_re_pos hre, ← Real.arctan_tan ha1 ha2, hta]
  exact Real.arctan_lt_arctan_iff.mpr ((div_lt_iff₀ hre).mpr h)

/-- Lower `arg` bound from a slope bound. -/
theorem lt_arg_of_slope {z : ℂ} {a c : ℝ} (hre : 0 < z.re) (hta : Real.tan a = c)
    (ha1 : -(Real.pi / 2) < a) (ha2 : a < Real.pi / 2) (h : c * z.re < z.im) : a < z.arg := by
  rw [arg_eq_arctan_of_re_pos hre, ← Real.arctan_tan ha1 ha2, hta]
  exact Real.arctan_lt_arctan_iff.mpr ((lt_div_iff₀ hre).mpr h)

theorem tan_neg_pi_div_six : Real.tan (-(Real.pi / 6)) = -(1 / Real.sqrt 3) := by
  rw [Real.tan_neg, Real.tan_pi_div_six]

theorem tan_neg_pi_div_three : Real.tan (-(Real.pi / 3)) = -Real.sqrt 3 := by
  rw [Real.tan_neg, Real.tan_pi_div_three]

theorem tan_neg_pi_div_four : Real.tan (-(Real.pi / 4)) = -1 := by
  rw [Real.tan_neg, Real.tan_pi_div_four]

/-- **Sector A** — `arg z ∈ [0, π/6)`: positive real part, non-negative imaginary part, slope
below `tan (π/6) = 1/√3` (stated as the radical-free `√3 · Im z < Re z`). -/
theorem arg_cell_A {z : ℂ} (hre : 0 < z.re) (him : 0 ≤ z.im) (h : Real.sqrt 3 * z.im < z.re) :
    0 ≤ z.arg ∧ z.arg < Real.pi / 6 := by
  have hpi := Real.pi_pos
  have h3 : (0:ℝ) < Real.sqrt 3 := by positivity
  refine ⟨Complex.arg_nonneg_iff.mpr him, arg_lt_of_slope hre Real.tan_pi_div_six (by linarith) (by linarith) ?_⟩
  rw [one_div, inv_mul_eq_div, lt_div_iff₀ h3]
  linarith [h]

/-- **Sector B** — `arg z ∈ (−π/6, 0]`. -/
theorem arg_cell_B {z : ℂ} (hre : 0 < z.re) (him : z.im ≤ 0) (h : -z.re < Real.sqrt 3 * z.im) :
    -(Real.pi / 6) < z.arg ∧ z.arg ≤ 0 := by
  have hpi := Real.pi_pos
  have h3 : (0:ℝ) < Real.sqrt 3 := by positivity
  refine ⟨lt_arg_of_slope hre tan_neg_pi_div_six (by linarith) (by linarith) ?_, ?_⟩
  · rw [neg_mul, one_div, inv_mul_eq_div, neg_lt, lt_div_iff₀ h3]
    nlinarith [h]
  · rw [arg_eq_arctan_of_re_pos hre, Real.arctan_le_zero]
    exact div_nonpos_of_nonpos_of_nonneg him hre.le

/-- **Sector C** — `arg z ∈ (π/4, π/2)`, certified by the radical-free `Re z < Im z`.

The two large-argument sectors are deliberately *asymmetric*: `π/4` on the positive side and `π/3`
on the negative side (sector D). Those are the widest thresholds the Haldane plaquette arithmetic
below tolerates — widening D to `π/4` as well would push the winding plaquette's bracket onto the
boundary of its `2π` window. Stating C at `π/4` keeps its side-condition free of `√3`, which is
what makes the two tightest links (`Re ≈ 0.39`) provable by rational enclosure alone. -/
theorem arg_cell_C {z : ℂ} (hre : 0 < z.re) (h : z.re < z.im) :
    Real.pi / 4 < z.arg ∧ z.arg < Real.pi / 2 := by
  have hpi := Real.pi_pos
  refine ⟨lt_arg_of_slope hre Real.tan_pi_div_four (by linarith) (by linarith) (by linarith), ?_⟩
  have habs : |z.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  exact (abs_lt.mp habs).2

/-- **Sector D** — `arg z ∈ (−π/2, −π/3)`. -/
theorem arg_cell_D {z : ℂ} (hre : 0 < z.re) (h : z.im < -(Real.sqrt 3 * z.re)) :
    -(Real.pi / 2) < z.arg ∧ z.arg < -(Real.pi / 3) := by
  have hpi := Real.pi_pos
  refine ⟨?_, arg_lt_of_slope hre tan_neg_pi_div_three (by linarith) (by linarith) (by linarith)⟩
  have habs : |z.arg| < Real.pi / 2 := Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl hre)
  linarith [(abs_lt.mp habs).1]

/-- **Narrow sector** — `|arg z| < π/4` from `|Im z| < Re z`. -/
theorem abs_arg_lt_pi_div_four {z : ℂ} (hre : 0 < z.re) (h : |z.im| < z.re) :
    |z.arg| < Real.pi / 4 := by
  have hpi := Real.pi_pos
  rw [abs_lt] at h ⊢
  constructor
  · refine lt_arg_of_slope hre tan_neg_pi_div_four (by linarith) (by linarith) ?_
    linarith [h.1]
  · refine arg_lt_of_slope hre Real.tan_pi_div_four (by linarith) (by linarith) ?_
    linarith [h.2]

/-! ## Branch-index placement from bounds -/

theorem branchIndex_eq_zero_of {t : ℝ} (h1 : -Real.pi < t) (h2 : t ≤ Real.pi) :
    branchIndex t = 0 := by
  rw [branchIndex, toIocDiv_eq_iff, Set.mem_Ioc]
  simp only [zero_zsmul, sub_zero]
  exact ⟨h1, by linarith⟩

theorem branchIndex_eq_one_of {t : ℝ} (h1 : Real.pi < t) (h2 : t ≤ 3 * Real.pi) :
    branchIndex t = 1 := by
  rw [branchIndex, toIocDiv_eq_iff, Set.mem_Ioc]
  simp only [one_zsmul]
  exact ⟨by linarith, by linarith⟩

end SKEFTHawking.TopologicalBand
