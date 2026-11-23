import SKEFTHawking.MolecularHamiltonian
import Mathlib.MeasureTheory.Function.L2Space

/-!
# Full positive angular-frequency port bath

The carrier is vector-valued L² on positive Lebesgue angular frequency, with arbitrary
complete complex Hilbert port fiber. The multiplier is ω itself (angular frequency,
not energy ℏω). Its domain is the actual maximal square-integrable multiplication graph.
This file concerns the free bath only; it does not construct couplings or a detector.
-/

noncomputable section

open MeasureTheory Set
open scoped InnerProductSpace ComplexConjugate

namespace SKEFTHawking.DKMBootstrap.PolaritonPortBath

/-- Full continuum measure, with no frequency truncation. -/
def frequencyMeasure : Measure ℝ := volume.restrict (Ioi 0)

/-- The port fiber need not be scalar or finite dimensional. -/
abbrev Bath (E : Type*) [NormedAddCommGroup E] := Lp E 2 frequencyMeasure

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- Multiplication of the chosen L² representative by physical angular frequency. -/
def weighted (u : Bath E) (ω : ℝ) : E := (ω : ℂ) • u ω

/-- Maximal multiplication domain, expressed on the actual L² representative. -/
def domain : Submodule ℂ (Bath E) where
  carrier := {u | MemLp (weighted u) 2 frequencyMeasure}
  zero_mem' := by
    apply MemLp.zero.ae_eq
    filter_upwards [Lp.coeFn_zero E 2 frequencyMeasure] with ω hω
    change (0 : E) = (ω : ℂ) • (0 : Bath E) ω
    rw [hω, Pi.zero_apply, smul_zero]
  add_mem' := by
    intro u v hu hv
    apply (hu.add hv).ae_eq
    filter_upwards [Lp.coeFn_add u v] with ω hω
    change (ω : ℂ) • u ω + (ω : ℂ) • v ω = (ω : ℂ) • (u + v) ω
    rw [hω, Pi.add_apply, smul_add]
  smul_mem' := by
    intro c u hu
    apply (hu.const_smul c).ae_eq
    filter_upwards [Lp.coeFn_smul c u] with ω hω
    change c • ((ω : ℂ) • u ω) = (ω : ℂ) • (c • u) ω
    rw [hω, Pi.smul_apply, smul_comm]

/-- Actual output L² class, not an abstract graph witness. -/
def omega : Bath E →ₗ.[ℂ] Bath E where
  domain := domain
  toFun :=
    { toFun := fun u ↦ u.property.toLp (weighted u.val)
      map_add' := by
        intro u v
        apply Lp.ext
        filter_upwards [(u + v).property.coeFn_toLp, u.property.coeFn_toLp,
          v.property.coeFn_toLp, Lp.coeFn_add u.val v.val,
          Lp.coeFn_add (u.property.toLp (weighted u.val))
            (v.property.toLp (weighted v.val))] with ω huv hu hv ha hb
        change (u + v).property.toLp (weighted (u + v).val) ω =
          (u.property.toLp (weighted u.val) + v.property.toLp (weighted v.val)) ω
        rw [huv, hb]
        change (ω : ℂ) • ((u.val + v.val) ω) =
          u.property.toLp (weighted u.val) ω + v.property.toLp (weighted v.val) ω
        rw [ha, Pi.add_apply, hu, hv]
        exact smul_add _ _ _
      map_smul' := by
        intro c u
        apply Lp.ext
        filter_upwards [(c • u).property.coeFn_toLp, u.property.coeFn_toLp,
          Lp.coeFn_smul c u.val, Lp.coeFn_smul c (u.property.toLp (weighted u.val))]
          with ω hcu hu ha hb
        change (c • u).property.toLp (weighted (c • u).val) ω =
          (c • u.property.toLp (weighted u.val)) ω
        rw [hcu, hb]
        change (ω : ℂ) • (c • u.val) ω = c • u.property.toLp (weighted u.val) ω
        rw [ha, Pi.smul_apply, hu]
        exact smul_comm _ _ _ }

/-- Exact maximal-domain characterization. -/
theorem mem_domain_iff (u : Bath E) :
    u ∈ (omega (E := E)).domain ↔ MemLp (fun ω : ℝ ↦ (ω : ℂ) • u ω) 2
      frequencyMeasure := Iff.rfl

/-- Frequency multiplication holds almost everywhere on the actual output class. -/
theorem omega_ae (u : (omega (E := E)).domain) :
    (omega u : ℝ → E) =ᵐ[frequencyMeasure] fun ω ↦ (ω : ℂ) • (u.val : Bath E) ω :=
  u.property.coeFn_toLp

/-- Real scalar multiplication is symmetric in any complex Hilbert fiber. -/
theorem real_smul_inner (ω : ℝ) (x y : E) :
    ⟪(ω : ℂ) • x, y⟫_ℂ = ⟪x, (ω : ℂ) • y⟫_ℂ := by
  rw [inner_smul_left, inner_smul_right, Complex.conj_ofReal]

/-- Symmetry on the full maximal graph, proved through the actual L² integral. -/
theorem omega_symmetric : DFT.IsSymmetricPMap (omega (E := E)) := by
  intro u v
  simp only [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [omega_ae u, omega_ae v] with ω hu hv
  rw [hu, hv, real_smul_inner]

/-- Inverse of the shift Ω − iμ, retaining the physical angular-frequency sign. -/
def inverseSymbol (μ ω : ℝ) : ℂ := ((ω : ℂ) - Complex.I * (μ : ℂ))⁻¹

private theorem shift_im (μ ω : ℝ) :
    ((ω : ℂ) - Complex.I * (μ : ℂ)).im = -μ := by simp

/-- Every nonzero imaginary shift is separated from the real frequency axis. -/
theorem shift_norm_lower (μ ω : ℝ) :
    |μ| ≤ ‖(ω : ℂ) - Complex.I * (μ : ℂ)‖ := by
  simpa only [shift_im, abs_neg] using
    Complex.abs_im_le_norm ((ω : ℂ) - Complex.I * (μ : ℂ))

private theorem shift_ne_zero {μ : ℝ} (hμ : μ ≠ 0) (ω : ℝ) :
    (ω : ℂ) - Complex.I * (μ : ℂ) ≠ 0 := by
  intro h
  have := congrArg Complex.im h
  simp only [shift_im, Complex.zero_im, neg_eq_zero] at this
  exact hμ this

/-- Uniform resolvent multiplier bound on the full frequency half-line. -/
theorem inverseSymbol_norm_le {μ : ℝ} (hμ : μ ≠ 0) (ω : ℝ) :
    ‖inverseSymbol μ ω‖ ≤ |μ|⁻¹ := by
  rw [inverseSymbol, norm_inv]
  exact (inv_le_inv₀ (lt_of_lt_of_le (abs_pos.mpr hμ) (shift_norm_lower μ ω))
    (abs_pos.mpr hμ)).mpr (shift_norm_lower μ ω)

/-- The weighted inverse is bounded by one, ensuring membership in the maximal domain. -/
theorem weighted_inverseSymbol_norm_le {μ : ℝ} (hμ : μ ≠ 0) (ω : ℝ) :
    ‖(ω : ℂ) * inverseSymbol μ ω‖ ≤ 1 := by
  rw [norm_mul, inverseSymbol, norm_inv, ← div_eq_mul_inv]
  apply (div_le_one (norm_pos_iff.mpr (shift_ne_zero hμ ω))).mpr
  have h := Complex.abs_re_le_norm ((ω : ℂ) - Complex.I * (μ : ℂ))
  simpa using h

private theorem inverseSymbol_measurable (μ : ℝ) : Measurable (inverseSymbol μ) := by
  unfold inverseSymbol
  fun_prop

private theorem bounded_smul_memLp (a : ℝ → ℂ) (ha : Measurable a) (C : ℝ)
    (hC : ∀ ω, ‖a ω‖ ≤ C) (u : Bath E) :
    MemLp (fun ω ↦ a ω • u ω) 2 frequencyMeasure := by
  apply (Lp.memLp u).of_le_mul (c := C) (ha.aestronglyMeasurable.smul (Lp.aestronglyMeasurable u))
  exact Filter.Eventually.of_forall fun ω ↦ by
    change ‖a ω • u ω‖ ≤ C * ‖u ω‖
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right (hC ω) (norm_nonneg _)

/-- Actual L² preimage obtained by multiplying each port amplitude by (ω − iμ)⁻¹. -/
def shiftedPreimage (μ : ℝ) (hμ : μ ≠ 0) (u : Bath E) : Bath E :=
  (bounded_smul_memLp (inverseSymbol μ) (inverseSymbol_measurable μ) (|μ|⁻¹)
    (inverseSymbol_norm_le hμ) u).toLp (fun ω ↦ inverseSymbol μ ω • u ω)

/-- Almost-everywhere formula for the shifted preimage. -/
theorem shiftedPreimage_ae (μ : ℝ) (hμ : μ ≠ 0) (u : Bath E) :
    (shiftedPreimage μ hμ u : ℝ → E) =ᵐ[frequencyMeasure]
      fun ω ↦ inverseSymbol μ ω • u ω := MemLp.coeFn_toLp _

/-- The weighted multiplier bound puts the actual preimage in the maximal graph. -/
theorem shiftedPreimage_mem_domain (μ : ℝ) (hμ : μ ≠ 0) (u : Bath E) :
    shiftedPreimage μ hμ u ∈ (omega (E := E)).domain := by
  have h := bounded_smul_memLp (fun ω ↦ (ω : ℂ) * inverseSymbol μ ω)
    (Complex.measurable_ofReal.mul (inverseSymbol_measurable μ)) 1
    (weighted_inverseSymbol_norm_le hμ) u
  apply h.ae_eq
  filter_upwards [shiftedPreimage_ae μ hμ u] with ω hω
  change ((ω : ℂ) * inverseSymbol μ ω) • u ω =
    (ω : ℂ) • shiftedPreimage μ hμ u ω
  rw [hω, mul_smul]

/-- Genuine surjectivity of Ω − iμ, for every nonzero real μ. -/
theorem omega_shift_surjective (μ : ℝ) (hμ : μ ≠ 0) (u : Bath E) :
    ∃ x : (omega (E := E)).domain,
      omega x - (Complex.I * (μ : ℂ)) • (x.val : Bath E) = u := by
  let x : (omega (E := E)).domain :=
    ⟨shiftedPreimage μ hμ u, shiftedPreimage_mem_domain μ hμ u⟩
  refine ⟨x, Lp.ext ?_⟩
  filter_upwards [Lp.coeFn_sub (omega x) ((Complex.I * (μ : ℂ)) • x.val),
    Lp.coeFn_smul (Complex.I * (μ : ℂ)) x.val, omega_ae x,
    shiftedPreimage_ae μ hμ u] with ω hsub hsmul hΩ hx
  change (omega x - (Complex.I * (μ : ℂ)) • x.val) ω = u ω
  rw [hsub, Pi.sub_apply, hsmul, Pi.smul_apply, hΩ]
  change (ω : ℂ) • shiftedPreimage μ hμ u ω -
    (Complex.I * (μ : ℂ)) • shiftedPreimage μ hμ u ω = u ω
  rw [hx, ← sub_smul, smul_smul, inverseSymbol,
    mul_inv_cancel₀ (shift_ne_zero hμ ω), one_smul]

/-- The actual L² resolvent obeys the same 1/|μ| bound as its scalar symbol. -/
theorem shiftedPreimage_norm_le (μ : ℝ) (hμ : μ ≠ 0) (u : Bath E) :
    ‖shiftedPreimage μ hμ u‖ ≤ |μ|⁻¹ * ‖u‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [shiftedPreimage_ae μ hμ u] with ω hω
  rw [hω, norm_smul]
  exact mul_le_mul_of_nonneg_right (inverseSymbol_norm_le hμ ω) (norm_nonneg _)

/-- The positive-frequency restriction makes the maximal bath operator nonnegative. -/
theorem omega_nonnegative (u : (omega (E := E)).domain) :
    0 ≤ (⟪(u.val : Bath E), omega u⟫_ℂ).re := by
  change 0 ≤ RCLike.re (⟪(u.val : Bath E), omega u⟫_ℂ)
  rw [L2.inner_def, ← integral_re (L2.integrable_inner (𝕜 := ℂ) u.val (omega u))]
  apply integral_nonneg_of_ae
  have hpos : ∀ᵐ ω ∂frequencyMeasure, 0 < ω := ae_restrict_mem measurableSet_Ioi
  filter_upwards [omega_ae u, hpos] with ω hω hpos
  change 0 ≤ (⟪(u.val : Bath E) ω, omega u ω⟫_ℂ).re
  rw [hω, inner_smul_right, Complex.mul_re]
  simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  exact mul_nonneg hpos.le (inner_self_nonneg (𝕜 := ℂ))

variable [CompleteSpace E]

/-- Actual density: an orthogonal vector is a shifted output; its imaginary pairing
with its preimage forces that preimage, and hence the vector itself, to vanish. -/
theorem omega_dense_domain : Dense ((omega (E := E)).domain : Set (Bath E)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top,
    Submodule.topologicalClosure_eq_top_iff, Submodule.eq_bot_iff]
  intro y hy
  obtain ⟨x, hx⟩ := omega_shift_surjective 1 one_ne_zero y
  have hxy : ⟪(x.val : Bath E), y⟫_ℂ = 0 :=
    (Submodule.mem_orthogonal _ _).mp hy x.val x.property
  have him : (⟪x.val, omega x⟫_ℂ).im = 0 := by
    rw [← omega_symmetric x x]
    exact omega_symmetric.inner_self_im_eq_zero x
  rw [← hx, inner_sub_right, inner_smul_right] at hxy
  have hnorm : ‖(x.val : Bath E)‖ ^ 2 = 0 := by
    have hi := congrArg Complex.im hxy
    simp only [Complex.ofReal_one, mul_one, Complex.sub_im, Complex.I_mul_im,
      Complex.zero_im, him] at hi
    have hre : (⟪(x.val : Bath E), x.val⟫_ℂ).re = ‖(x.val : Bath E)‖ ^ 2 :=
      inner_self_eq_norm_sq (𝕜 := ℂ) x.val
    linarith
  have hx0 : (x.val : Bath E) = 0 := norm_eq_zero.mp (sq_eq_zero_iff.mp hnorm)
  have hΩ0 : omega x = 0 := by
    have hxsub : x = 0 := Subtype.ext hx0
    rw [hxsub, LinearPMap.map_zero]
  rw [hΩ0, hx0, smul_zero, sub_zero] at hx
  exact hx.symm

/-- The full maximal positive angular-frequency bath operator is self-adjoint. -/
theorem omega_selfAdjoint : IsSelfAdjoint (omega (E := E)) := by
  apply omega_symmetric.isSelfAdjoint_of_surjective omega_dense_domain (μ := 1)
  · exact omega_shift_surjective 1 one_ne_zero
  · intro z
    obtain ⟨x, hx⟩ := omega_shift_surjective (-1) (neg_ne_zero.mpr one_ne_zero) z
    refine ⟨x, ?_⟩
    simpa using hx

end SKEFTHawking.DKMBootstrap.PolaritonPortBath
