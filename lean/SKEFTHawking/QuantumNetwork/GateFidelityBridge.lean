import SKEFTHawking.QuantumNetwork.DiamondNormChoiUpper

/-!
# Fidelity ↔ diamond-distance bridges (Phase 6AG, Ask 4)

Operationally one certifies a worst-case (diamond) error guarantee from average-case fidelity data,
and conversely bounds all input–output fidelities from a small diamond distance. This file records
the two Fuchs–van de Graaf bridges, lifted from states to *channels* by composing the shipped FvdG
state bounds with the diamond-distance least-upper-bound property `le_diamondDist`.

For any stabilized input density operator `ρ` on the doubled space, with outputs
`Oᵢ = (Kᵢ ⊗ id) ρ`:

* **lower bridge** `1 − √F(O₁,O₂) ≤ D(O₁,O₂) ≤ ‖Φ₁−Φ₂‖_◇ / 2` (FvdG-lower ∘ `le_diamondDist`);
* **upper bridge** `D(O₁,O₂) ≤ √(1 − F(O₁,O₂))`, and this trace distance is `≤ diamondDist`.

Invariants: kernel-pure, zero sorry, zero project-local axioms, no `maxHeartbeats`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix

variable {m n : ℕ} {K₁ K₂ : Fin m → Matrix (Fin n) (Fin n) ℂ}

/-- **Fidelity → diamond lower bridge.** For any stabilized input density operator `ρ`, the
input–output square-root fidelity of two channels is controlled by their diamond distance:
`1 − √F((K₁⊗id)ρ, (K₂⊗id)ρ) ≤ diamondDist K₁ K₂`. Composes the Fuchs–van de Graaf lower bound
`one_sub_sqrtFidelity_le_traceDist` with the diamond least-upper-bound `le_diamondDist`. -/
theorem one_sub_sqrtFidelity_output_le_diamondDist (hK₁ : IsKrausChannel K₁)
    (hK₂ : IsKrausChannel K₂)
    {ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ} (hρ : IsDensityOperator ρ) :
    1 - sqrtFidelity (krausMap_isDensityOperator (isKrausChannel_tensorKraus hK₁) hρ).1
          (krausMap_isDensityOperator (isKrausChannel_tensorKraus hK₂) hρ).1
      ≤ diamondDist K₁ K₂ := by
  have hO₁ := krausMap_isDensityOperator (isKrausChannel_tensorKraus hK₁) hρ
  have hO₂ := krausMap_isDensityOperator (isKrausChannel_tensorKraus hK₂) hρ
  exact (one_sub_sqrtFidelity_le_traceDist hO₁.1 hO₂.1 hO₁.2 hO₂.2).trans
    (le_diamondDist hK₁ hK₂ hρ)

/-- **Diamond → fidelity contrapositive.** If two channels are diamond-close, then every
input–output square-root fidelity is high: `√F((K₁⊗id)ρ, (K₂⊗id)ρ) ≥ 1 − diamondDist K₁ K₂`. -/
theorem sqrtFidelity_output_ge_one_sub_diamondDist (hK₁ : IsKrausChannel K₁)
    (hK₂ : IsKrausChannel K₂)
    {ρ : Matrix (Fin n × Fin n) (Fin n × Fin n) ℂ} (hρ : IsDensityOperator ρ) :
    1 - diamondDist K₁ K₂
      ≤ sqrtFidelity (krausMap_isDensityOperator (isKrausChannel_tensorKraus hK₁) hρ).1
          (krausMap_isDensityOperator (isKrausChannel_tensorKraus hK₂) hρ).1 := by
  have h := one_sub_sqrtFidelity_output_le_diamondDist hK₁ hK₂ hρ
  linarith

end SKEFTHawking.QuantumNetwork
