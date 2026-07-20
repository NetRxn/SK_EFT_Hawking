import Mathlib

/-!
# D11-FHS kill-fast spike — principal-branch / `Complex.arg` feasibility gate

Spike goal: determine whether the Fukui–Hatsugai–Suzuki lattice-Chern **branch-correction**
mechanism (`fieldStrength_decomp`) is formalizable with the pinned Mathlib `Complex.arg`
+ `toIocMod`/`toIocDiv` machinery, kernel-pure.
-/

open Complex Real

namespace SKEFTHawking.TopologicalBand

noncomputable def principal (θ : ℝ) : ℝ := toIocMod Real.two_pi_pos (-Real.pi) θ

noncomputable def branchIndex (θ : ℝ) : ℤ := toIocDiv Real.two_pi_pos (-Real.pi) θ

/-- Branch decomposition: any angle is its principal representative plus an integer number
of full turns. This is the definitional `toIocMod`/`toIocDiv` identity. -/
theorem principal_add_branch (θ : ℝ) :
    principal θ + (2 * Real.pi) * (branchIndex θ : ℝ) = θ := by
  unfold principal branchIndex
  have h := toIocMod_add_toIocDiv_zsmul Real.two_pi_pos (-Real.pi) θ
  rw [zsmul_eq_mul] at h
  linarith

/-- The principal representative lands in `(-π, π]`. -/
theorem principal_mem_Ioc (θ : ℝ) : principal θ ∈ Set.Ioc (-Real.pi) Real.pi := by
  unfold principal
  have h := toIocMod_mem_Ioc Real.two_pi_pos (-Real.pi) θ
  rwa [show -Real.pi + 2 * Real.pi = Real.pi by ring] at h

/-- **Decisive spike lemma.** `arg` of a product is the principal reduction of the sum of args. -/
theorem arg_mul_eq_principal_add (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) :
    Complex.arg (z * w) = principal (Complex.arg z + Complex.arg w) := by
  unfold principal
  rw [← arg_coe_angle_toReal_eq_arg (z * w), arg_mul_coe_angle hz hw,
    ← Real.Angle.coe_add, Real.Angle.toReal_coe]

/-- **`fieldStrength_decomp` primitive.** The branch-correction integer of a single product. -/
theorem arg_mul_branch_correction (z w : ℂ) (hz : z ≠ 0) (hw : w ≠ 0) :
    Complex.arg z + Complex.arg w - Complex.arg (z * w)
      = (2 * Real.pi) * (branchIndex (Complex.arg z + Complex.arg w) : ℝ) := by
  have h := principal_add_branch (Complex.arg z + Complex.arg w)
  rw [← arg_mul_eq_principal_add z w hz hw] at h
  linarith

/-- `Real.Angle`-level additivity of `arg` over the FHS plaquette product
`a · b · c⁻¹ · d⁻¹` (the four oriented links around one plaquette). -/
theorem argCoe_plaquette (a b c d : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    (↑(Complex.arg (a * b * c⁻¹ * d⁻¹)) : Real.Angle)
      = ↑(Complex.arg a) + ↑(Complex.arg b) - ↑(Complex.arg c) - ↑(Complex.arg d) := by
  rw [arg_mul_coe_angle (mul_ne_zero (mul_ne_zero ha hb) (inv_ne_zero hc)) (inv_ne_zero hd),
    arg_mul_coe_angle (mul_ne_zero ha hb) (inv_ne_zero hc), arg_mul_coe_angle ha hb,
    arg_inv_coe_angle, arg_inv_coe_angle]
  abel

/-- **The FHS plaquette-curl principal reduction** — the substantive spike target.
`arg` of the plaquette product is the principal reduction of the raw lattice curl
`A(a) + A(b) − A(c) − A(d)`. This is exactly the shape the FHS lattice field strength
consumes: `plaquetteArg = principal (rawCurl)`, whence integrality follows by torus
telescoping (a downstream finite-`Finset` argument outside this spike). -/
theorem arg_plaquette_eq_principal_rawCurl (a b c d : ℂ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    Complex.arg (a * b * c⁻¹ * d⁻¹)
      = principal (Complex.arg a + Complex.arg b - Complex.arg c - Complex.arg d) := by
  have hcoe : (↑(Complex.arg (a * b * c⁻¹ * d⁻¹)) : Real.Angle)
      = ↑(Complex.arg a + Complex.arg b - Complex.arg c - Complex.arg d) := by
    rw [argCoe_plaquette a b c d ha hb hc hd, Real.Angle.coe_sub, Real.Angle.coe_sub,
      Real.Angle.coe_add]
  unfold principal
  rw [← arg_coe_angle_toReal_eq_arg (a * b * c⁻¹ * d⁻¹), hcoe, Real.Angle.toReal_coe]

end SKEFTHawking.TopologicalBand
