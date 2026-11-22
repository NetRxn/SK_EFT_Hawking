import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.MeasureTheory.Group.Integral

/-! Vector Bochner construction of a bounded receiver.

Only continuity of each vector orbit is required; no operator norm continuity or
operator-valued Bochner integrability is assumed. The unitary specialization uses the actual
conjugation `V t ∘ A ∘ V (-t)`. Translation, generator-domain differentiation, and transfer to
a physical density/current correlator are separate obligations.
-/

noncomputable section

open MeasureTheory

namespace SKEFTHawking.DKMBootstrap.ReceiverIntegral

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H]

/-- A uniformly bounded family with continuous vector orbits. -/
structure BoundedStrongOrbit (H : Type*) [NormedAddCommGroup H] [NormedSpace ℂ H] where
  map : ℝ → H →L[ℂ] H
  bound : ℝ
  bound_nonneg : 0 ≤ bound
  continuous : ∀ x, Continuous (fun t ↦ map t x)
  norm_le : ∀ t x, ‖map t x‖ ≤ bound * ‖x‖

namespace BoundedStrongOrbit

variable (O : BoundedStrongOrbit H) {h : ℝ → ℝ} (hh : Integrable h)

include hh in
/-- Strong continuity on each vector suffices for the weighted vector's measurability. -/
theorem weighted_aestronglyMeasurable (x : H) :
    AEStronglyMeasurable (fun t ↦ h t • O.map t x) :=
  hh.aestronglyMeasurable.smul (O.continuous x).aestronglyMeasurable

/-- Pointwise domination by the actual absolute weight. -/
theorem weighted_norm_le (x : H) (t : ℝ) :
    ‖h t • O.map t x‖ ≤ |h t| * (O.bound * ‖x‖) := by
  rw [norm_smul, Real.norm_eq_abs]
  exact mul_le_mul_of_nonneg_left (O.norm_le t x) (abs_nonneg _)

include hh in
/-- Integrability is established by scalar domination before defining the receiver integral. -/
theorem weighted_integrable (x : H) : Integrable (fun t ↦ h t • O.map t x) := by
  refine (hh.norm.mul_const (O.bound * ‖x‖)).mono
    (O.weighted_aestronglyMeasurable hh x) ?_
  filter_upwards [] with t
  simpa only [Real.norm_eq_abs, abs_mul, abs_abs,
    abs_of_nonneg (mul_nonneg O.bound_nonneg (norm_nonneg x))] using
    O.weighted_norm_le (h := h) x t

include hh in
/-- The norm estimate for the vector integral, with its integrability witness explicit. -/
theorem integral_norm_le (x : H) :
    ‖∫ t, h t • O.map t x‖ ≤ (O.bound * ∫ t, |h t|) * ‖x‖ := by
  have hi := O.weighted_integrable hh x
  calc
    ‖∫ t, h t • O.map t x‖ ≤ ∫ t, ‖h t • O.map t x‖ :=
      norm_integral_le_integral_norm _
    _ ≤ ∫ t, |h t| * (O.bound * ‖x‖) :=
      integral_mono hi.norm (hh.norm.mul_const _) (O.weighted_norm_le x)
    _ = (O.bound * ∫ t, |h t|) * ‖x‖ := by
      rw [integral_mul_const]
      ring

/-- The complex linear map is defined by vector integrals, whose integrability was proved above. -/
def receiverLinear [CompleteSpace H] : H →ₗ[ℂ] H where
  toFun x := ∫ t, h t • O.map t x
  map_add' x y := by
    simp only [map_add, smul_add]
    exact integral_add (O.weighted_integrable hh x) (O.weighted_integrable hh y)
  map_smul' c x := by
    simp only [map_smul, RingHom.id_apply]
    simp_rw [smul_comm (h _) c]
    exact integral_smul c _

variable [CompleteSpace H]

/-- The actual bounded receiver, obtained from complex linearity and the vector integral bound. -/
def receiver : H →L[ℂ] H :=
  (O.receiverLinear hh).mkContinuous (O.bound * ∫ t, |h t|) (O.integral_norm_le hh)

@[simp] theorem receiver_apply (x : H) :
    O.receiver hh x = ∫ t, h t • O.map t x := rfl

/-- The uniform orbit bound times the L1 norm of the weight controls the operator norm. -/
theorem receiver_norm_le : ‖O.receiver hh‖ ≤ O.bound * ∫ t, |h t| := by
  apply LinearMap.mkContinuous_norm_le
  exact mul_nonneg O.bound_nonneg (integral_nonneg (fun t ↦ abs_nonneg (h t)))

/-- A normalized weight recovers a constant orbit. -/
theorem receiver_eq_of_constant (A : H →L[ℂ] H) (hA : ∀ t, O.map t = A)
    (hnormalized : ∫ t, h t = 1) : O.receiver hh = A := by
  ext x
  simp only [receiver_apply, hA]
  rw [integral_smul_const, hnormalized, one_smul]

end BoundedStrongOrbit

/-- Strongly continuous isometries act continuously on a varying continuous vector.
The proof splits the distance into a fixed-vector orbit term and an isometric vector term. -/
theorem continuous_unitary_variable (V : ℝ → H ≃ₗᵢ[ℂ] H)
    (hV : ∀ x, Continuous (fun t ↦ V t x)) {f : ℝ → H} (hf : Continuous f) :
    Continuous (fun t ↦ V t (f t)) := by
  apply continuous_iff_continuousAt.mpr
  intro t₀
  rw [Metric.continuousAt_iff]
  intro ε hε
  obtain ⟨δ₁, hδ₁, h₁⟩ := Metric.continuousAt_iff.mp hf.continuousAt (ε / 2) (by linarith)
  obtain ⟨δ₂, hδ₂, h₂⟩ :=
    Metric.continuousAt_iff.mp (hV (f t₀)).continuousAt (ε / 2) (by linarith)
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_⟩
  intro t ht
  have hv := h₁ (lt_of_lt_of_le ht (min_le_left _ _))
  have ho := h₂ (lt_of_lt_of_le ht (min_le_right _ _))
  calc
    dist (V t (f t)) (V t₀ (f t₀)) ≤
        dist (V t (f t)) (V t (f t₀)) + dist (V t (f t₀)) (V t₀ (f t₀)) :=
      dist_triangle _ _ _
    _ = dist (f t) (f t₀) + dist (V t (f t₀)) (V t₀ (f t₀)) := by
      rw [(V t).dist_map]
    _ < ε := by linarith

/-- Embed the actual conjugation orbit, using only strong continuity and isometry.
For a unitary group, `V (-t)` is its inverse; no group law is needed for this bound. -/
def unitaryOrbit (V : ℝ → H ≃ₗᵢ[ℂ] H) (hV : ∀ x, Continuous (fun t ↦ V t x))
    (A : H →L[ℂ] H) : BoundedStrongOrbit H where
  map t := (V t).toContinuousLinearEquiv.toContinuousLinearMap |>.comp
    (A.comp (V (-t)).toContinuousLinearEquiv.toContinuousLinearMap)
  bound := ‖A‖
  bound_nonneg := norm_nonneg A
  continuous x := continuous_unitary_variable V hV
    (A.continuous.comp ((hV x).comp continuous_neg))
  norm_le t x := by
    change ‖V t (A (V (-t) x))‖ ≤ ‖A‖ * ‖x‖
    rw [(V t).norm_map]
    simpa only [(V (-t)).norm_map] using A.le_opNorm (V (-t) x)

variable [CompleteSpace H]

/-- The bounded receiver for the actual unitary conjugation orbit and an integrable real weight. -/
def unitaryReceiver (V : ℝ → H ≃ₗᵢ[ℂ] H)
    (hV : ∀ x, Continuous (fun t ↦ V t x)) (A : H →L[ℂ] H)
    {h : ℝ → ℝ} (hh : Integrable h) : H →L[ℂ] H :=
  (unitaryOrbit V hV A).receiver hh

@[simp] theorem unitaryReceiver_apply (V : ℝ → H ≃ₗᵢ[ℂ] H)
    (hV : ∀ x, Continuous (fun t ↦ V t x)) (A : H →L[ℂ] H)
    {h : ℝ → ℝ} (hh : Integrable h) (x : H) :
    unitaryReceiver V hV A hh x = ∫ t, h t • V t (A (V (-t) x)) := rfl

omit [CompleteSpace H] in
/-- The actual conjugation integrand is integrable for every vector. -/
theorem unitaryReceiver_integrable (V : ℝ → H ≃ₗᵢ[ℂ] H)
    (hV : ∀ x, Continuous (fun t ↦ V t x)) (A : H →L[ℂ] H)
    {h : ℝ → ℝ} (hh : Integrable h) (x : H) :
    Integrable (fun t ↦ h t • V t (A (V (-t) x))) :=
  (unitaryOrbit V hV A).weighted_integrable hh x

/-- The conjugation receiver has the expected L1 operator norm bound. -/
theorem unitaryReceiver_norm_le (V : ℝ → H ≃ₗᵢ[ℂ] H)
    (hV : ∀ x, Continuous (fun t ↦ V t x)) (A : H →L[ℂ] H)
    {h : ℝ → ℝ} (hh : Integrable h) :
    ‖unitaryReceiver V hV A hh‖ ≤ ‖A‖ * ∫ t, |h t| :=
  (unitaryOrbit V hV A).receiver_norm_le hh

/-- Any conjugation-invariant bounded observable is recovered by a normalized weight. -/
theorem unitaryReceiver_eq_of_invariant (V : ℝ → H ≃ₗᵢ[ℂ] H)
    (hV : ∀ x, Continuous (fun t ↦ V t x)) (A : H →L[ℂ] H)
    {h : ℝ → ℝ} (hh : Integrable h) (hnormalized : ∫ t, h t = 1)
    (hA : ∀ t x, V t (A (V (-t) x)) = A x) : unitaryReceiver V hV A hh = A := by
  apply (unitaryOrbit V hV A).receiver_eq_of_constant hh A _ hnormalized
  intro t
  ext x
  exact hA t x

/-- The identity unitary dynamics give a concrete constant-orbit control for every bounded `A`. -/
theorem unitaryReceiver_identity (A : H →L[ℂ] H) {h : ℝ → ℝ} (hh : Integrable h)
    (hnormalized : ∫ t, h t = 1) :
    unitaryReceiver (fun _ ↦ LinearIsometryEquiv.refl ℂ H)
      (fun _ ↦ continuous_const) A hh = A := by
  apply unitaryReceiver_eq_of_invariant _ _ A hh hnormalized
  intro t x
  rfl


namespace BoundedStrongOrbit

variable (O : BoundedStrongOrbit H)

/-- Additivity in the actual integrable real weight. -/
theorem receiver_add {h k : ℝ → ℝ} (hh : Integrable h) (hk : Integrable k) :
    O.receiver (hh.add hk) = O.receiver hh + O.receiver hk := by
  ext x
  simp only [receiver_apply, Pi.add_apply, add_smul, add_apply]
  exact integral_add (O.weighted_integrable hh x) (O.weighted_integrable hk x)

/-- Subtraction in the weight is subtraction of bounded receivers. -/
theorem receiver_sub {h k : ℝ → ℝ} (hh : Integrable h) (hk : Integrable k) :
    O.receiver (hh.sub hk) = O.receiver hh - O.receiver hk := by
  ext x
  simp only [receiver_apply, Pi.sub_apply, sub_smul, sub_apply]
  exact integral_sub (O.weighted_integrable hh x) (O.weighted_integrable hk x)

/-- Real scalar linearity in the weight. -/
theorem receiver_smul {h : ℝ → ℝ} (hh : Integrable h) (c : ℝ) :
    O.receiver (hh.smul c) = c • O.receiver hh := by
  ext x
  simp only [receiver_apply, Pi.smul_apply, smul_eq_mul, mul_smul,
    smul_apply]
  exact integral_smul c _

/-- Finite sums of integrable weights give finite sums of receivers. -/
theorem receiver_finsetSum {ι : Type*} (S : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i, Integrable (f i)) :
    O.receiver (integrable_finsetSum S (fun i _ ↦ hf i)) =
      ∑ i ∈ S, O.receiver (hf i) := by
  ext x
  simp only [receiver_apply, Finset.sum_smul, sum_apply]
  exact integral_finsetSum S (fun i _ ↦ O.weighted_integrable (hf i) x)

/-- The receiver is Lipschitz in the scalar L1 distance between integrable weights. -/
theorem receiver_sub_norm_le {h k : ℝ → ℝ} (hh : Integrable h) (hk : Integrable k) :
    ‖O.receiver hh - O.receiver hk‖ ≤ O.bound * ∫ t, |h t - k t| := by
  rw [← O.receiver_sub hh hk]
  exact O.receiver_norm_le (hh.sub hk)

/-- Transfer a supplied scalar L1 remainder bound to the operator norm.
This theorem does not establish the scalar remainder or any generator-domain applicability. -/
theorem receiver_sub_norm_le_of_l1 {h k : ℝ → ℝ} (hh : Integrable h) (hk : Integrable k)
    {R : ℝ} (hR : (∫ t, |h t - k t|) ≤ R) :
    ‖O.receiver hh - O.receiver hk‖ ≤ O.bound * R :=
  (O.receiver_sub_norm_le hh hk).trans (mul_le_mul_of_nonneg_left hR O.bound_nonneg)

end BoundedStrongOrbit

omit [CompleteSpace H] in
/-- Lebesgue translation invariance preserves integrability of the actual shifted weight. -/
theorem integrable_weight_translate {h : ℝ → ℝ} (hh : Integrable h) (s : ℝ) :
    Integrable (fun t ↦ h (t - s)) := by
  simpa only [sub_eq_add_neg] using hh.comp_add_right (-s)

/-- Exact conjugation covariance for a strongly continuous isometric group.
The group composition law is an explicit pointwise premise; operator norm continuity is absent. -/
theorem unitaryReceiver_covariance (V : ℝ → H ≃ₗᵢ[ℂ] H)
    (hV : ∀ x, Continuous (fun t ↦ V t x))
    (hgroup : ∀ s t x, V (s + t) x = V s (V t x)) (A : H →L[ℂ] H)
    {h : ℝ → ℝ} (hh : Integrable h) (s : ℝ) (x : H) :
    V s (unitaryReceiver V hV A hh (V (-s) x)) =
      unitaryReceiver V hV A (integrable_weight_translate hh s) x := by
  rw [unitaryReceiver_apply, unitaryReceiver_apply]
  calc
    V s (∫ t, h t • V t (A (V (-t) (V (-s) x)))) =
        ∫ t, V s (h t • V t (A (V (-t) (V (-s) x)))) :=
      ((V s).toContinuousLinearEquiv.toContinuousLinearMap.integral_comp_comm
        (unitaryReceiver_integrable V hV A hh (V (-s) x))).symm
    _ = ∫ t, h t • V (t + s) (A (V (-(t + s)) x)) := by
      apply integral_congr_ae
      filter_upwards [] with t
      simp only [← Complex.coe_smul]
      rw [map_smul, ← hgroup, ← hgroup]
      have hsum : -t + -s = -(s + t) := by ring
      rw [hsum, add_comm s t]
    _ = ∫ t, h (t - s) • V t (A (V (-t) x)) := by
      simpa only [add_sub_cancel_right] using
        (integral_add_right_eq_self (fun t ↦ h (t - s) • V t (A (V (-t) x))) s)

/-- Covariance transfers any supplied L1 approximation of the shifted weight to the receiver.
A Taylor polynomial may be supplied as `p`; its scalar remainder is a premise, not proved here. -/
theorem unitaryReceiver_covariance_remainder (V : ℝ → H ≃ₗᵢ[ℂ] H)
    (hV : ∀ x, Continuous (fun t ↦ V t x))
    (hgroup : ∀ s t x, V (s + t) x = V s (V t x)) (A : H →L[ℂ] H)
    {h p : ℝ → ℝ} (hh : Integrable h) (hp : Integrable p) (s : ℝ)
    {R : ℝ} (hR : (∫ t, |h (t - s) - p t|) ≤ R) :
    ‖((V s).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((unitaryReceiver V hV A hh).comp
          (V (-s)).toContinuousLinearEquiv.toContinuousLinearMap)) -
      unitaryReceiver V hV A hp‖ ≤ ‖A‖ * R := by
  have hcov : (V s).toContinuousLinearEquiv.toContinuousLinearMap.comp
      ((unitaryReceiver V hV A hh).comp
        (V (-s)).toContinuousLinearEquiv.toContinuousLinearMap) =
      unitaryReceiver V hV A (integrable_weight_translate hh s) := by
    ext x
    exact unitaryReceiver_covariance V hV hgroup A hh s x
  rw [hcov]
  exact (unitaryOrbit V hV A).receiver_sub_norm_le_of_l1
    (integrable_weight_translate hh s) hp hR

/-- An explicit finite Taylor-weight estimate from a supplied scalar L1 remainder.
The caller supplies integrable derivative weights `d` and the scalar remainder inequality;
no derivative identification, scalar Taylor theorem, or physical generator claim is asserted. -/
theorem unitaryReceiver_covariance_taylor (V : ℝ → H ≃ₗᵢ[ℂ] H)
    (hV : ∀ x, Continuous (fun t ↦ V t x))
    (hgroup : ∀ s t x, V (s + t) x = V s (V t x)) (A : H →L[ℂ] H)
    {h : ℝ → ℝ} (hh : Integrable h) (s : ℝ) (n : ℕ)
    (d : Fin n → ℝ → ℝ) (hd : ∀ i, Integrable (d i))
    {R : ℝ} (hR : (∫ t, |h (t - s) -
      ∑ i : Fin n, ((-s) ^ (i : ℕ) / (i : ℕ).factorial) * d i t|) ≤ R) :
    ‖((V s).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((unitaryReceiver V hV A hh).comp
          (V (-s)).toContinuousLinearEquiv.toContinuousLinearMap)) -
      ∑ i : Fin n, ((-s) ^ (i : ℕ) / (i : ℕ).factorial) •
        unitaryReceiver V hV A (hd i)‖ ≤ ‖A‖ * R := by
  let c : Fin n → ℝ := fun i ↦ (-s) ^ (i : ℕ) / (i : ℕ).factorial
  have hp : Integrable (fun t ↦ ∑ i : Fin n, c i * d i t) :=
    integrable_finsetSum Finset.univ (fun i _ ↦ (hd i).const_mul (c i))
  have hlin : unitaryReceiver V hV A hp =
      ∑ i : Fin n, c i • unitaryReceiver V hV A (hd i) := by
    change (unitaryOrbit V hV A).receiver hp = _
    rw [(unitaryOrbit V hV A).receiver_finsetSum Finset.univ
      (fun i t ↦ c i * d i t) (fun i ↦ (hd i).const_mul (c i))]
    apply Finset.sum_congr rfl
    intro i _
    exact (unitaryOrbit V hV A).receiver_smul (hd i) (c i)
  change ‖_ - ∑ i : Fin n, c i • unitaryReceiver V hV A (hd i)‖ ≤ _
  rw [← hlin]
  exact unitaryReceiver_covariance_remainder V hV hgroup A hh hp s hR

end SKEFTHawking.DKMBootstrap.ReceiverIntegral
