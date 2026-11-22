import Mathlib.Analysis.InnerProductSpace.LinearPMap

/-! A conditional weak-to-strong commutator interface for an actual self-adjoint partial operator.

The weak identity implies domain preservation and identifies the strong bracket on that domain.
Establishing the weak identity for a Cauchy receiver orbit, finite observation windows, or a
physical generator requires separate arguments.
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

end SKEFTHawking.DKMBootstrap.ReceiverCommutator
