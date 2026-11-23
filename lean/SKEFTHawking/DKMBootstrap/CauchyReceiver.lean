import SKEFTHawking.DKMBootstrap.ReceiverKernel
import SKEFTHawking.DKMBootstrap.ReceiverIntegral
import SKEFTHawking.DKMBootstrap.ReceiverCommutator
import SKEFTHawking.DKMBootstrap.Predicates

/-!
# Cauchy receiver on a unitary group with an identified forward derivative

The weights are the actual iterated derivatives of the normalized Cauchy kernel.
Their vector Bochner integrals define `B_j = receiverOrder ... j`. The proved scalar
Taylor estimate gives a quantitative covariance remainder and the orbit derivative `-B_(j + 1)`.

For a self-adjoint partial operator `K`, the forward derivative `i K v` on its existing
domain is an explicit premise. The weak-to-strong bridge derives domain preservation;
it is not assumed. The bounded maps `T_j = i^j B_j` then satisfy the genuine ordinary
bracket recurrence and `‖T_j‖ ≤ ‖A‖ j! / τ^j`.

For nonzero `B_0`, the actual bracket norms satisfy `HasOperatorGrowthBound` with prefactor
`‖B_0‖` and positive rate `max(1, ‖A‖ / ‖B_0‖) / τ`. When `B_0 = 0`, the actual bracket
recurrence and density of the self-adjoint domain force every `T_j` to vanish, giving a
positive rate in that case too. This is an ideal bilateral receiver result. Physical group
and detector identification, spatial locality, microscopic state/density hypotheses,
calibration, finite-acquisition transfer, and physical transport remain separate obligations.
-/

noncomputable section
open scoped NNReal
open MeasureTheory
namespace SKEFTHawking.DKMBootstrap.CauchyReceiver

open ReceiverIntegral ReceiverCommutator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
variable (V : ℝ → H ≃ₗᵢ[ℂ] H) (hV : ∀ x, Continuous (fun t ↦ V t x))
variable (A : H →L[ℂ] H) (τ : ℝ≥0) (hτ : 0 < τ)

/-- The actual Cauchy derivative weight, integrated against the unitary conjugation orbit. -/
def receiverOrder (j : ℕ) : H →L[ℂ] H :=
  unitaryReceiver V hV A (receiverKernel_iteratedDeriv_integrable τ hτ j)

include hV hτ in
omit [CompleteSpace H] in
/-- The defining vector integrand is integrable before evaluating the receiver. -/
theorem receiverOrder_integrable (j : ℕ) (x : H) :
    Integrable (fun t ↦ iteratedDeriv j (receiverKernel τ) t • V t (A (V (-t) x))) :=
  unitaryReceiver_integrable V hV A (receiverKernel_iteratedDeriv_integrable τ hτ j) x

/-- Expose the vector Bochner integral underlying the bounded map. -/
theorem receiverOrder_apply (j : ℕ) (x : H) :
    receiverOrder V hV A τ hτ j x =
      ∫ t, iteratedDeriv j (receiverKernel τ) t • V t (A (V (-t) x)) := rfl

/-- Actual Cauchy derivative L¹ control yields an all-order bound with the input norm. -/
theorem receiverOrder_norm_le (j : ℕ) :
    ‖receiverOrder V hV A τ hτ j‖ ≤ ‖A‖ * ((j.factorial : ℝ) / (τ : ℝ) ^ j) := by
  unfold receiverOrder
  exact (unitaryReceiver_norm_le V hV A
    (receiverKernel_iteratedDeriv_integrable τ hτ j)).trans
    (mul_le_mul_of_nonneg_left (receiverKernel_iteratedDeriv_integral_abs_le τ hτ j)
      (norm_nonneg A))

/-- The scalar Cauchy Taylor bound gives an operator norm covariance remainder.
The sign comes from translation of the weight by `t - s`. -/
theorem receiverOrder_covariance_remainder
    (hgroup : ∀ s t x, V (s + t) x = V s (V t x)) (j : ℕ) (s : ℝ)
    (hs : |s| ≤ (τ : ℝ)) :
    ‖(V s).toContinuousLinearEquiv.toContinuousLinearMap.comp
        ((receiverOrder V hV A τ hτ j).comp
          (V (-s)).toContinuousLinearEquiv.toContinuousLinearMap) -
      (receiverOrder V hV A τ hτ j - s • receiverOrder V hV A τ hτ (j + 1))‖ ≤
      ‖A‖ * (3 * |s| ^ 2 * (((j + 2).factorial : ℝ) / (τ : ℝ) ^ (j + 2))) := by
  let h : ℝ → ℝ := iteratedDeriv j (receiverKernel τ)
  let k : ℝ → ℝ := iteratedDeriv (j + 1) (receiverKernel τ)
  have hh : Integrable h := receiverKernel_iteratedDeriv_integrable τ hτ j
  have hk : Integrable k := receiverKernel_iteratedDeriv_integrable τ hτ (j + 1)
  have hp : Integrable (fun t ↦ h t - s * k t) := hh.sub (hk.const_mul s)
  have hscalar : (∫ t, |h (t - s) - (h t - s * k t)|) ≤
      3 * |s| ^ 2 * (((j + 2).factorial : ℝ) / (τ : ℝ) ^ (j + 2)) := by
    convert receiverKernel_taylor_remainder_integral_abs_le τ hτ j s hs using 1
    congr 1
    ext t
    congr 1
    ring
  have hweights : unitaryReceiver V hV A hp =
      receiverOrder V hV A τ hτ j - s • receiverOrder V hV A τ hτ (j + 1) := by
    change (unitaryOrbit V hV A).receiver hp = _
    rw [(unitaryOrbit V hV A).receiver_sub hh (hk.const_mul s),
      (unitaryOrbit V hV A).receiver_smul hk s]
    rfl
  rw [← hweights]
  exact unitaryReceiver_covariance_remainder V hV hgroup A hh hp s hscalar

/-- Evaluate the covariance remainder at any vector, retaining its norm factor. -/
theorem receiverOrder_quadratic
    (hgroup : ∀ s t x, V (s + t) x = V s (V t x)) (j : ℕ) (s : ℝ)
    (hs : |s| ≤ (τ : ℝ)) (x : H) :
    ‖V s (receiverOrder V hV A τ hτ j (V (-s) x)) -
      receiverOrder V hV A τ hτ j x +
        s • receiverOrder V hV A τ hτ (j + 1) x‖ ≤
      (‖A‖ * (3 * (((j + 2).factorial : ℝ) / (τ : ℝ) ^ (j + 2))) * ‖x‖) * |s| ^ 2 := by
  let Q := (V s).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((receiverOrder V hV A τ hτ j).comp
      (V (-s)).toContinuousLinearEquiv.toContinuousLinearMap) -
      (receiverOrder V hV A τ hτ j - s • receiverOrder V hV A τ hτ (j + 1))
  have hq : ‖Q‖ ≤ ‖A‖ *
      (3 * |s| ^ 2 * (((j + 2).factorial : ℝ) / (τ : ℝ) ^ (j + 2))) := by
    exact receiverOrder_covariance_remainder V hV A τ hτ hgroup j s hs
  have hv := (Q.le_opNorm x).trans (mul_le_mul_of_nonneg_right hq (norm_nonneg x))
  have heval : Q x = V s (receiverOrder V hV A τ hτ j (V (-s) x)) -
      receiverOrder V hV A τ hτ j x +
        s • receiverOrder V hV A τ hτ (j + 1) x := by
    change V s (receiverOrder V hV A τ hτ j (V (-s) x)) -
      (receiverOrder V hV A τ hτ j x -
        s • receiverOrder V hV A τ hτ (j + 1) x) = _
    abel
  rw [heval] at hv
  calc
    _ ≤ _ := hv
    _ = _ := by ring

/-- The local quadratic remainder proves the actual vector orbit derivative at zero. -/
theorem receiverOrder_orbit_derivative
    (hgroup : ∀ s t x, V (s + t) x = V s (V t x)) (j : ℕ) (x : H) :
    HasDerivAt (fun s : ℝ ↦ V s (receiverOrder V hV A τ hτ j (V (-s) x)))
      (-receiverOrder V hV A τ hτ (j + 1) x) 0 := by
  apply hasDerivAt_of_quadratic_remainder _ _
    (‖A‖ * (3 * (((j + 2).factorial : ℝ) / (τ : ℝ) ^ (j + 2))) * ‖x‖) (τ : ℝ)
    (by exact_mod_cast hτ)
  intro s hs
  simpa [group_zero_apply V hgroup, smul_neg, sub_neg_eq_add] using
    receiverOrder_quadratic V hV A τ hτ hgroup j s hs x

variable (hgroup : ∀ s t x, V (s + t) x = V s (V t x))
variable (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K)
variable (hgen : ∀ v : K.domain,
    HasDerivAt (fun s : ℝ ↦ V s (v : H)) (Complex.I • K v) 0)

include hgroup hK hgen in
/-- Derive membership in the actual domain and its generator action from the two derivatives. -/
theorem receiverOrder_domain_action (j : ℕ) (v : K.domain) :
    ∃ hv : receiverOrder V hV A τ hτ j (v : H) ∈ K.domain,
      K ⟨receiverOrder V hV A τ hτ j (v : H), hv⟩ =
        receiverOrder V hV A τ hτ j (K v) +
          Complex.I • receiverOrder V hV A τ hτ (j + 1) (v : H) :=
  domain_of_group_derivatives K hK
    (receiverOrder V hV A τ hτ j) (receiverOrder V hV A τ hτ (j + 1))
    V hgroup hgen
    (fun w ↦ receiverOrder_orbit_derivative V hV A τ hτ hgroup j (w : H)) v

/-- Bounded representatives of the iterated bracket. The recurrence is proved below. -/
def commutatorOrder (j : ℕ) : H →L[ℂ] H :=
  Complex.I ^ j • receiverOrder V hV A τ hτ j

/-- The order-zero bracket representative is the smoothed observable itself. -/
@[simp] theorem commutatorOrder_zero :
    commutatorOrder V hV A τ hτ 0 = receiverOrder V hV A τ hτ 0 := by
  simp [commutatorOrder]

/-- The unit-modulus powers of `i` retain the input-norm factorial estimate. -/
theorem commutatorOrder_norm_le (j : ℕ) :
    ‖commutatorOrder V hV A τ hτ j‖ ≤ ‖A‖ * ((j.factorial : ℝ) / (τ : ℝ) ^ j) := by
  simpa only [commutatorOrder, norm_smul, norm_pow, Complex.norm_I, one_pow, one_mul] using
    receiverOrder_norm_le V hV A τ hτ j

include hgroup hK hgen in
/-- Domain membership and the ordinary bracket recurrence are derived for every order. -/
theorem commutatorOrder_domain_recurrence (j : ℕ) (v : K.domain) :
    ∃ hv : commutatorOrder V hV A τ hτ j (v : H) ∈ K.domain,
      K ⟨commutatorOrder V hV A τ hτ j (v : H), hv⟩ -
        commutatorOrder V hV A τ hτ j (K v) =
          commutatorOrder V hV A τ hτ (j + 1) (v : H) := by
  obtain ⟨hv, hact⟩ := receiverOrder_domain_action V hV A τ hτ hgroup K hK hgen j v
  let w : K.domain := ⟨receiverOrder V hV A τ hτ j (v : H), hv⟩
  refine ⟨K.domain.smul_mem (Complex.I ^ j) hv, ?_⟩
  change K ((Complex.I ^ j) • w) -
    (Complex.I ^ j) • receiverOrder V hV A τ hτ j (K v) = _
  rw [K.map_smul]
  change (Complex.I ^ j) • K ⟨_, hv⟩ - _ = _
  rw [hact, smul_add, add_sub_cancel_left, ← mul_smul, ← pow_succ]
  rfl

/-- For nonzero output, absorb the input/output norm ratio into an explicit rate.
Order zero uses the actual identity `T₀ = B₀`; positive orders use the input-norm estimate. -/
theorem commutatorOrder_hasOperatorGrowthBound_of_norm_pos
    (hB : 0 < ‖receiverOrder V hV A τ hτ 0‖) :
    HasOperatorGrowthBound (fun j ↦ ‖commutatorOrder V hV A τ hτ j‖)
      (max 1 (‖A‖ / ‖receiverOrder V hV A τ hτ 0‖) / (τ : ℝ))
      ‖receiverOrder V hV A τ hτ 0‖ := by
  let b := ‖receiverOrder V hV A τ hτ 0‖
  let r := max 1 (‖A‖ / b)
  have hr : 1 ≤ r := le_max_left _ _
  have hr0 : 0 ≤ r := le_trans zero_le_one hr
  have hA : ‖A‖ ≤ r * b := (div_le_iff₀ hB).mp (le_max_right _ _)
  intro j
  cases j with
  | zero => simp
  | succ k =>
    have hrpow : r ≤ r ^ (k + 1) := by
      calc
        r = 1 * r := (one_mul r).symm
        _ ≤ r ^ k * r := mul_le_mul_of_nonneg_right
          (one_le_pow₀ hr) hr0
        _ = r ^ (k + 1) := (pow_succ r k).symm
    have hApow : ‖A‖ ≤ r ^ (k + 1) * b :=
      hA.trans (mul_le_mul_of_nonneg_right hrpow (norm_nonneg _))
    calc
      ‖commutatorOrder V hV A τ hτ (k + 1)‖ ≤
          ‖A‖ * (((k + 1).factorial : ℝ) / (τ : ℝ) ^ (k + 1)) :=
        commutatorOrder_norm_le V hV A τ hτ (k + 1)
      _ ≤ (r ^ (k + 1) * b) *
          (((k + 1).factorial : ℝ) / (τ : ℝ) ^ (k + 1)) :=
        mul_le_mul_of_nonneg_right hApow (by positivity)
      _ = ((k + 1).factorial : ℝ) * (r / (τ : ℝ)) ^ (k + 1) * b := by
        rw [div_pow]
        ring

include hgroup hK hgen in
/-- Zero smoothed output forces the actual brackets to vanish: the recurrence gives
zero on `K.domain` at each successor, and continuity extends it from that dense domain. -/
theorem commutatorOrder_eq_zero_of_receiverOrder_zero
    (hB : receiverOrder V hV A τ hτ 0 = 0) (j : ℕ) :
    commutatorOrder V hV A τ hτ j = 0 := by
  induction j with
  | zero => simpa using hB
  | succ j ih =>
    have hon (x : H) (hx : x ∈ K.domain) :
        commutatorOrder V hV A τ hτ (j + 1) x = 0 := by
      obtain ⟨hv, hrec⟩ :=
        commutatorOrder_domain_recurrence V hV A τ hτ hgroup K hK hgen j ⟨x, hx⟩
      have hz : (⟨commutatorOrder V hV A τ hτ j x, hv⟩ : K.domain) = 0 := by
        apply Subtype.ext
        simp [ih]
      rw [hz, K.map_zero, ih] at hrec
      simpa using hrec.symm
    have heq := (commutatorOrder V hV A τ hτ (j + 1)).continuous.ext_on
      hK.dense_domain continuous_const hon
    ext x
    exact congrFun heq x

include hgroup hK hgen in
/-- The actual ideal receiver brackets satisfy the existing output-normalized F3 predicate
at a positive rate, including zero output without division by its norm. -/
theorem commutatorOrder_hasOperatorGrowthBound :
    ∃ ε : ℝ, 0 < ε ∧
      HasOperatorGrowthBound (fun j ↦ ‖commutatorOrder V hV A τ hτ j‖) ε
        ‖receiverOrder V hV A τ hτ 0‖ := by
  have hτR : 0 < (τ : ℝ) := by exact_mod_cast hτ
  by_cases hB : receiverOrder V hV A τ hτ 0 = 0
  · refine ⟨1 / (τ : ℝ), div_pos zero_lt_one hτR, ?_⟩
    intro j
    dsimp only
    rw [commutatorOrder_eq_zero_of_receiverOrder_zero V hV A τ hτ hgroup K hK hgen hB j,
      hB, norm_zero, mul_zero]
  · have hBpos : 0 < ‖receiverOrder V hV A τ hτ 0‖ := norm_pos_iff.mpr hB
    refine ⟨max 1 (‖A‖ / ‖receiverOrder V hV A τ hτ 0‖) / (τ : ℝ),
      div_pos (lt_of_lt_of_le zero_lt_one (le_max_left _ _)) hτR, ?_⟩
    exact commutatorOrder_hasOperatorGrowthBound_of_norm_pos V hV A τ hτ hBpos

end SKEFTHawking.DKMBootstrap.CauchyReceiver
