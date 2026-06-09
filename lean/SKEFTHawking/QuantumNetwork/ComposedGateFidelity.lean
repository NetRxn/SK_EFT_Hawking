import SKEFTHawking.QuantumNetwork.CoherenceFidelity
import SKEFTHawking.QuantumNetwork.GateFidelityBridge

/-!
# Composed average-gate-fidelity / diamond-distance bound (Phase 6AN, Wave 3)

A realized physical gate is modelled as the coherence-limited channel composed after an explicit
control/gate-error channel: `Φ_realized = Φ_coh ∘ Φ_ctrl`. This file makes the **composition error
budget** explicit as a function of the device parameters `(t_gate, T₁, T₂, ε_ctrl)`:

* `diamondDist_coherenceChannel_le` — the coherence-limited diamond error is bounded in closed form
  by `γ(t,T₁) + p(t,T₂) = (1 − e^{−t/T₁}) + (1 − e^{−t/T₂})/2`. This is possible because the
  coherence channel `coherenceKraus γ p = 𝒜_γ ∘ 𝒟_p` is *itself* a composition of amplitude damping
  and dephasing (Wave 1 composition + the exact named-channel diamond distances
  `diamondDist_ampDamp_eq = γ`, `diamondDist_dephasing_eq = p`).
* `diamondDist_coherence_after_control_le` — the **composed bound**: for any control channel with
  diamond distance `≤ ε_ctrl` from its ideal, the realized gate's worst-case error satisfies
  `‖Φ_realized − Φ_ideal‖_◇ ≤ γ(t,T₁) + p(t,T₂) + ε_ctrl` (Wave 1 applied at the outer composition).
* `sqrtFidelity_coherence_after_control_ge` — the fidelity reading: every stabilized input–output
  square-root fidelity of the realized gate is `≥ 1 − (γ + p + ε_ctrl)` (via the shipped
  Fuchs–van de Graaf diamond→fidelity bridge `sqrtFidelity_output_ge_one_sub_diamondDist`).
* Two worked regimes (`*_coherence_binds`, `*_control_binds`) exhibit the two operating points where,
  respectively, the coherence term and the control term is the binding contribution.

The coherence term's average-gate-fidelity reading is the 6AK.1 closed form
`avgGateFidelity (coherenceChannel t T₁ T₂) = ½ + ⅙e^{−t/T₁} + ⅓e^{−t/(2T₁)−t/T₂}`
(`avgGateFidelity_coherenceChannel`); the point of this wave is that the coherence ceiling alone is
non-binding once control error dominates, and the composed bound is the one that constrains the
realizable gate.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix

/-- **Coherence-limited diamond error, closed form.** Since `coherenceChannel t T₁ T₂` is amplitude
damping (`γ = cohGamma t T₁`) composed after dephasing (`p = cohP t T₂`), Wave-1 subadditivity plus
the exact named-channel diamond distances give
`diamondDist (coherenceChannel t T₁ T₂) (id ∘ id) ≤ cohGamma t T₁ + cohP t T₂`. -/
theorem diamondDist_coherenceChannel_le {t T1 T2 : ℝ} (ht : 0 ≤ t) (hT1 : 0 < T1) (hT2 : 0 < T2) :
    diamondDist (coherenceChannel t T1 T2) (composeKraus (idKrausPad 1 2) (idKrausPad 1 2))
      ≤ cohGamma t T1 + cohP t T2 := by
  have h := diamondDist_composeKraus_le
    (isKrausChannel_ampDampKraus (cohGamma_nonneg ht hT1) cohGamma_le_one)
    (isKrausChannel_idKrausPad 1 2)
    (isKrausChannel_dephasingKraus (cohP_nonneg ht hT2) cohP_le_one)
    (isKrausChannel_idKrausPad 1 2)
  rw [diamondDist_ampDamp_eq (cohGamma_nonneg ht hT1) cohGamma_le_one,
    diamondDist_dephasing_eq (cohP_nonneg ht hT2) cohP_le_one] at h
  exact h

variable {c : ℕ} {ctrl ctrlId : Fin c → Matrix (Fin 2) (Fin 2) ℂ}

/-- **Composed gate error budget (coherence ⊕ control).** Model the realized gate as the
coherence-limited channel composed after a control-error channel `ctrl` whose diamond distance from
its ideal `ctrlId` is at most `ε`. The realized gate's worst-case (diamond) error is bounded by the
sum of the coherence and control contributions:
`‖Φ_coh ∘ Φ_ctrl − id ∘ id ∘ id‖_◇ ≤ (cohGamma t T₁ + cohP t T₂) + ε`. -/
theorem diamondDist_coherence_after_control_le {t T1 T2 ε : ℝ}
    (ht : 0 ≤ t) (hT1 : 0 < T1) (hT2 : 0 < T2)
    (hctrl : IsKrausChannel ctrl) (hctrlId : IsKrausChannel ctrlId)
    (hε : diamondDist ctrl ctrlId ≤ ε) :
    diamondDist (composeKraus (coherenceChannel t T1 T2) ctrl)
        (composeKraus (composeKraus (idKrausPad 1 2) (idKrausPad 1 2)) ctrlId)
      ≤ cohGamma t T1 + cohP t T2 + ε := by
  have hcomp := diamondDist_composeKraus_le
    (isKrausChannel_coherenceChannel ht hT1 hT2)
    (isKrausChannel_composeKraus (isKrausChannel_idKrausPad 1 2) (isKrausChannel_idKrausPad 1 2))
    hctrl hctrlId
  exact hcomp.trans (add_le_add (diamondDist_coherenceChannel_le ht hT1 hT2) hε)

/-- **Fidelity reading of the composed budget.** Every stabilized input–output square-root fidelity
of the realized gate is at least `1 − (cohGamma t T₁ + cohP t T₂ + ε)`. Diamond→fidelity via the
shipped Fuchs–van de Graaf bridge `sqrtFidelity_output_ge_one_sub_diamondDist`. -/
theorem sqrtFidelity_coherence_after_control_ge {t T1 T2 ε : ℝ}
    (ht : 0 ≤ t) (hT1 : 0 < T1) (hT2 : 0 < T2)
    (hctrl : IsKrausChannel ctrl) (hctrlId : IsKrausChannel ctrlId)
    (hε : diamondDist ctrl ctrlId ≤ ε)
    {ρ : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ} (hρ : IsDensityOperator ρ) :
    1 - (cohGamma t T1 + cohP t T2 + ε)
      ≤ sqrtFidelity
          (krausMap_isDensityOperator (isKrausChannel_tensorKraus
            (isKrausChannel_composeKraus (isKrausChannel_coherenceChannel ht hT1 hT2) hctrl)) hρ).1
          (krausMap_isDensityOperator (isKrausChannel_tensorKraus
            (isKrausChannel_composeKraus (isKrausChannel_composeKraus
              (isKrausChannel_idKrausPad 1 2) (isKrausChannel_idKrausPad 1 2)) hctrlId)) hρ).1 := by
  have hbr := sqrtFidelity_output_ge_one_sub_diamondDist
    (isKrausChannel_composeKraus (isKrausChannel_coherenceChannel ht hT1 hT2) hctrl)
    (isKrausChannel_composeKraus (isKrausChannel_composeKraus
      (isKrausChannel_idKrausPad 1 2) (isKrausChannel_idKrausPad 1 2)) hctrlId) hρ
  have hb := diamondDist_coherence_after_control_le ht hT1 hT2 hctrl hctrlId hε
  linarith

/-! ## Worked operating regimes -/

/-- `exp (-1) < 1/2`, hence `cohGamma 1 1 > 1/2` — used to exhibit the coherence-binding regime. -/
theorem cohGamma_one_one_gt_half : (1 : ℝ) / 2 < cohGamma 1 1 := by
  have he : Real.exp (-1 / 1) < 1 / 2 := by
    rw [neg_div, div_one, Real.exp_neg]
    rw [show (1 : ℝ) / 2 = (2 : ℝ)⁻¹ by norm_num]
    exact inv_strictAnti₀ (by norm_num) (by linarith [Real.add_one_lt_exp (x := (1 : ℝ)) one_ne_zero])
  unfold cohGamma; linarith

/-- **Coherence-binding regime.** At `t = T₁ = T₂ = 1` with a control channel of diamond error
`≤ 1/100`, the coherence contribution exceeds the control contribution
(`cohGamma 1 1 + cohP 1 1 > 1/2 > 1/100`): coherence is the binding term, yet the composed budget
still bounds the realized error. -/
theorem diamondDist_coherence_after_control_le_coherence_binds
    (hctrl : IsKrausChannel ctrl) (hctrlId : IsKrausChannel ctrlId)
    (hε : diamondDist ctrl ctrlId ≤ 1 / 100) :
    diamondDist (composeKraus (coherenceChannel 1 1 1) ctrl)
        (composeKraus (composeKraus (idKrausPad 1 2) (idKrausPad 1 2)) ctrlId)
      ≤ cohGamma 1 1 + cohP 1 1 + 1 / 100
      ∧ (1 : ℝ) / 100 < cohGamma 1 1 + cohP 1 1 :=
  ⟨diamondDist_coherence_after_control_le (by norm_num) (by norm_num) (by norm_num)
      hctrl hctrlId hε,
    by have := cohGamma_one_one_gt_half; have := cohP_nonneg (t := 1) (T2 := 1) (by norm_num)
        (by norm_num); linarith⟩

/-- **Control-binding regime.** For a zero-duration gate (`t = 0`), the coherence channel is exactly
the identity (`cohGamma 0 T₁ = cohP 0 T₂ = 0`), so the entire realized error is the control
contribution: the composed budget collapses to `≤ ε`, and control is the binding term. -/
theorem diamondDist_coherence_after_control_le_control_binds {ε : ℝ}
    (hctrl : IsKrausChannel ctrl) (hctrlId : IsKrausChannel ctrlId)
    (hε : diamondDist ctrl ctrlId ≤ ε) (hε0 : 0 ≤ ε) :
    diamondDist (composeKraus (coherenceChannel 0 1 1) ctrl)
        (composeKraus (composeKraus (idKrausPad 1 2) (idKrausPad 1 2)) ctrlId)
      ≤ ε
      ∧ cohGamma 0 1 + cohP 0 1 ≤ ε := by
  have hz : cohGamma 0 1 + cohP 0 1 = 0 := by
    simp [cohGamma, cohP]
  refine ⟨?_, by rw [hz]; exact hε0⟩
  have h := diamondDist_coherence_after_control_le (t := 0) (T1 := 1) (T2 := 1) (ε := ε)
    (by norm_num) (by norm_num) (by norm_num) hctrl hctrlId hε
  rwa [hz, zero_add] at h

end SKEFTHawking.QuantumNetwork
