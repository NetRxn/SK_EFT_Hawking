import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Calculus
import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! A conditional weak-to-strong commutator interface for an actual self-adjoint partial operator.

The weak identity implies domain preservation and identifies the strong bracket on that domain.
The weak identity is derived below from two explicit real derivatives for a given isometric
group. Instantiating those derivatives for the Cauchy receiver and identifying a physical
generator or finite observation window require separate arguments.
-/

noncomputable section

open scoped ComplexConjugate

namespace SKEFTHawking.DKMBootstrap.ReceiverCommutator

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

omit [CompleteSpace H] in
private theorem same_value {K J : H →ₗ.[ℂ] H} (h : K = J) (v : H)
    (hK : v ∈ K.domain) (hJ : v ∈ J.domain) :
    K ⟨v, hK⟩ = J ⟨v, hJ⟩ := by
  subst J
  rfl

/-- A bounded weak commutator for a self-adjoint partial operator preserves
its domain. The receiver-orbit argument must supply the weak identity. -/
theorem domain_of_weak_commutator (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K)
    (B C : H →L[ℂ] H)
    (hweak : ∀ u v : K.domain,
      inner ℂ (K u) (B (v : H)) =
        inner ℂ (u : H) (B (K v) + Complex.I • C (v : H)))
    (v : K.domain) :
    ∃ hv : B (v : H) ∈ K.domain,
      K ⟨B (v : H), hv⟩ = B (K v) + Complex.I • C (v : H) := by
  let y := B (v : H)
  let w := B (K v) + Complex.I • C (v : H)
  have hw (u : K.domain) : inner ℂ w (u : H) = inner ℂ y (K u) := by
    simpa only [inner_conj_symm] using congrArg (starRingEnd ℂ) (hweak u v).symm
  have hy : y ∈ (LinearPMap.adjoint K).domain :=
    LinearPMap.mem_adjoint_domain_of_exists y ⟨w, hw⟩
  have ha : (LinearPMap.adjoint K) ⟨y, hy⟩ = w :=
    LinearPMap.adjoint_apply_eq hK.dense_domain ⟨y, hy⟩ hw
  have hadj : LinearPMap.adjoint K = K := LinearPMap.isSelfAdjoint_def.mp hK
  have hdom : y ∈ K.domain := hadj ▸ hy
  exact ⟨hdom, (same_value hadj y hy hdom).symm.trans ha⟩

variable (K : H →ₗ.[ℂ] H) (hK : IsSelfAdjoint K) (B C : H →L[ℂ] H)
  (hweak : ∀ u v : K.domain,
    inner ℂ (K u) (B (v : H)) =
      inner ℂ (u : H) (B (K v) + Complex.I • C (v : H)))

/-- Restrict `B` to a linear endomorphism of the actual operator domain.
Domain membership is derived from the weak identity through the partial adjoint. -/
def domainLift : K.domain →ₗ[ℂ] K.domain where
  toFun v := ⟨B (v : H), (domain_of_weak_commutator K hK B C hweak v).choose⟩
  map_add' u v := Subtype.ext (B.map_add (u : H) (v : H))
  map_smul' a v := Subtype.ext (B.map_smul a (v : H))

@[simp]
theorem coe_domainLift (v : K.domain) :
    (domainLift K hK B C hweak v : H) = B (v : H) := rfl

/-- The partial operator acts on the derived domain lift as prescribed by the weak form. -/
theorem domainLift_action (v : K.domain) :
    K (domainLift K hK B C hweak v) = B (K v) + Complex.I • C (v : H) :=
  (domain_of_weak_commutator K hK B C hweak v).choose_spec

include hK hweak in
/-- On the actual domain, the strong bracket agrees with the bounded operator `i C`.
The result holds for every proof of the derived membership, without a chosen lift. -/
theorem strong_commutator_action (v : K.domain) (hv : B (v : H) ∈ K.domain) :
    K ⟨B (v : H), hv⟩ - B (K v) = Complex.I • C (v : H) := by
  have ha : K ⟨B (v : H), hv⟩ = B (K v) + Complex.I • C (v : H) :=
    (domain_of_weak_commutator K hK B C hweak v).choose_spec
  rw [ha, add_sub_cancel_left]

include hK hweak in
/-- The strong bracket on the dense operator domain has the ambient bound supplied by `C`. -/
theorem strong_commutator_bound (v : K.domain) (hv : B (v : H) ∈ K.domain) :
    ‖K ⟨B (v : H), hv⟩ - B (K v)‖ ≤ ‖C‖ * ‖(v : H)‖ := by
  rw [strong_commutator_action K hK B C hweak v hv]
  simpa only [norm_smul, Complex.norm_I, one_mul] using C.le_opNorm (v : H)

section Generator

variable (V : ℝ → H ≃ₗᵢ[ℂ] H)
  (hgroup : ∀ s t x, V (s + t) x = V s (V t x))

include hgroup in
omit [CompleteSpace H] in
/-- The group law and surjectivity force the zero-time isometry to be the identity. -/
theorem group_zero_apply (x : H) : V 0 x = x := by
  obtain ⟨y, rfl⟩ := (V 0).surjective x
  exact (hgroup 0 0 y).symm.trans (by simp)

include hgroup in
omit [CompleteSpace H] in
/-- The negative-time isometry cancels the positive-time isometry. -/
theorem group_neg_apply (s : ℝ) (x : H) : V (-s) (V s x) = x := by
  rw [← hgroup, neg_add_cancel, group_zero_apply V hgroup]

include hgroup in
omit [CompleteSpace H] in
/-- Move the left conjugating isometry across the pairing without any domain assumption. -/
theorem conjugation_pairing (B : H →L[ℂ] H) (s : ℝ) (u v : H) :
    inner ℂ u (V s (B (V (-s) v))) = inner ℂ (V (-s) u) (B (V (-s) v)) := by
  rw [← (V (-s)).inner_map_map u (V s (B (V (-s) v))),
    group_neg_apply V hgroup]

omit [CompleteSpace H] in
/-- Reversing real time negates the explicitly given forward vector derivative on `D(K)`. -/
theorem hasDerivAt_group_neg (K : H →ₗ.[ℂ] H)
    (hgen : ∀ v : K.domain,
      HasDerivAt (fun s : ℝ ↦ V s (v : H)) (Complex.I • K v) 0)
    (v : K.domain) :
    HasDerivAt (fun s : ℝ ↦ V (-s) (v : H)) (-(Complex.I • K v)) 0 := by
  simpa only [Function.comp_def, neg_one_smul] using
    (hgen v).scomp_of_eq (0 : ℝ) (hasDerivAt_neg (x := (0 : ℝ))) neg_zero.symm

include hgroup in
omit [CompleteSpace H] in
/-- Two real derivatives of the same matrix element give the weak bracket with sign `+i C`.
The group-to-operator derivative is explicit; `B v ∈ D(K)` is not presumed. -/
theorem weak_commutator_of_group_derivatives (K : H →ₗ.[ℂ] H) (B C : H →L[ℂ] H)
    (hgen : ∀ v : K.domain,
      HasDerivAt (fun s : ℝ ↦ V s (v : H)) (Complex.I • K v) 0)
    (horbit : ∀ v : K.domain,
      HasDerivAt (fun s : ℝ ↦ V s (B (V (-s) (v : H)))) (-C (v : H)) 0)
    (u v : K.domain) :
    inner ℂ (K u) (B (v : H)) =
      inner ℂ (u : H) (B (K v) + Complex.I • C (v : H)) := by
  have hu := hasDerivAt_group_neg V K hgen u
  have hv := hasDerivAt_group_neg V K hgen v
  have hB : HasDerivAt (fun s : ℝ ↦ B (V (-s) (v : H)))
      (B (-(Complex.I • K v))) 0 :=
    ((B.restrictScalars ℝ).hasFDerivAt).comp_hasDerivAt 0 hv
  have hr := hu.inner ℂ hB
  have hl := (hasDerivAt_const (0 : ℝ) (u : H)).inner ℂ (horbit v)
  have hp : (fun s : ℝ ↦ inner ℂ (u : H) (V s (B (V (-s) (v : H))))) =
      (fun s : ℝ ↦ inner ℂ (V (-s) (u : H)) (B (V (-s) (v : H)))) := by
    funext s
    exact conjugation_pairing V hgroup B s u v
  rw [hp] at hl
  have he := hl.unique hr
  simp only [neg_zero, group_zero_apply V hgroup, inner_neg_right, inner_zero_left,
    add_zero, map_neg, map_smul, inner_smul_right, inner_neg_left, inner_smul_left,
    Complex.conj_I] at he
  simp only [inner_add_right, inner_smul_right]
  apply mul_left_cancel₀ Complex.I_ne_zero
  calc
    Complex.I * inner ℂ (K u) (B (v : H)) =
        Complex.I * inner ℂ (u : H) (B (K v)) - inner ℂ (u : H) (C (v : H)) := by
      linear_combination -he
    _ = Complex.I * (inner ℂ (u : H) (B (K v)) +
        Complex.I * inner ℂ (u : H) (C (v : H))) := by
      simp [mul_add, ← mul_assoc, sub_eq_add_neg]

variable (hgen : ∀ v : K.domain,
    HasDerivAt (fun s : ℝ ↦ V s (v : H)) (Complex.I • K v) 0)
  (horbit : ∀ v : K.domain,
    HasDerivAt (fun s : ℝ ↦ V s (B (V (-s) (v : H)))) (-C (v : H)) 0)

include hgroup hK hgen horbit in
/-- The two group derivatives imply actual domain preservation and the generator action. -/
theorem domain_of_group_derivatives (v : K.domain) :
    ∃ hv : B (v : H) ∈ K.domain,
      K ⟨B (v : H), hv⟩ = B (K v) + Complex.I • C (v : H) :=
  domain_of_weak_commutator K hK B C
    (weak_commutator_of_group_derivatives V hgroup K B C hgen horbit) v

include hgroup hK hgen horbit in
/-- The derived domain membership gives the strong bracket for any membership witness. -/
theorem strong_commutator_action_of_group_derivatives (v : K.domain)
    (hv : B (v : H) ∈ K.domain) :
    K ⟨B (v : H), hv⟩ - B (K v) = Complex.I • C (v : H) :=
  strong_commutator_action K hK B C
    (weak_commutator_of_group_derivatives V hgroup K B C hgen horbit) v hv

include hgroup hK hgen horbit in
/-- The strong bracket derived from the real group derivatives has the ambient `C` bound. -/
theorem strong_commutator_bound_of_group_derivatives (v : K.domain)
    (hv : B (v : H) ∈ K.domain) :
    ‖K ⟨B (v : H), hv⟩ - B (K v)‖ ≤ ‖C‖ * ‖(v : H)‖ :=
  strong_commutator_bound K hK B C
    (weak_commutator_of_group_derivatives V hgroup K B C hgen horbit) v hv

end Generator

/-- A local quadratic vector remainder supplies a real derivative at zero.
This can be applied after evaluating an operator covariance estimate at a fixed vector. -/
theorem hasDerivAt_of_quadratic_remainder {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℝ → E) (f' : E) (L τ : ℝ)
    (hτ : 0 < τ)
    (hR : ∀ s : ℝ, |s| ≤ τ → ‖f s - f 0 - s • f'‖ ≤ L * |s| ^ 2) :
    HasDerivAt f f' 0 := by
  rw [hasDerivAt_iff_isLittleO_nhds_zero]
  have hO : (fun s : ℝ ↦ f s - f 0 - s • f') =O[nhds 0] (fun s ↦ s ^ 2) := by
    apply Asymptotics.IsBigO.of_bound L
    have ht : ∀ᶠ s : ℝ in nhds 0, |s| < τ := by
      change {s : ℝ | |s| < τ} ∈ nhds (0 : ℝ)
      simpa only [Metric.ball, Real.dist_eq, sub_zero] using Metric.ball_mem_nhds (0 : ℝ) hτ
    filter_upwards [ht] with s hs
    simpa only [norm_pow, Real.norm_eq_abs] using hR s hs.le
  simpa only [zero_add, pow_one] using
    hO.trans_isLittleO (Asymptotics.isLittleO_pow_pow (𝕜 := ℝ) (m := 1) (n := 2)
      (by decide))

end SKEFTHawking.DKMBootstrap.ReceiverCommutator
