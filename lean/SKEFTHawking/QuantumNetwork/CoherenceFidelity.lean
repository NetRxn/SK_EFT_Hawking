import SKEFTHawking.QuantumNetwork.GateFidelity
import SKEFTHawking.QuantumNetwork.DiamondBudget

/-!
# Coherence-limited average gate fidelity (Phase 6AK, Wave 6AK.1)

A qubit gate of duration `t` on hardware with relaxation time `T₁` and dephasing time `T₂` is
modelled by the **coherence channel** `Φ_t = 𝒜_γ ∘ 𝒟_p`, the amplitude-damping channel with
`γ = 1 − e^{−t/T₁}` composed after the dephasing channel with `p = (1 − e^{−t/T₂})/2`. We compute
its entanglement fidelity and average gate fidelity in closed form. The remarkable structure: both
collapse to a **sum of decaying exponentials**,

`F_e(Φ_t)   = ¼ (1 + e^{−t/T₁} + 2 e^{−t/(2T₁) − t/T₂})`,
`F_avg(Φ_t) = ½ + ⅙ e^{−t/T₁} + ⅓ e^{−t/(2T₁) − t/T₂}`,

via the general identity `avgGateFidelity_eq : F_avg = (d·F_e + 1)/(d+1)` (Phase 6AG). Each term is
antitone in `t`, so `F_avg(Φ_t)` decreases monotonically from `1` at `t = 0` to the floor `½` as
`t → ∞`.

**Scope (what is and is not proven).** Every theorem here is an *exact equality (or its consequence)
for the specific model channel* `Φ_t = 𝒜_γ ∘ 𝒟_p` with the stated `γ(t,T₁)`, `p(t,T₂)`. Reading
`F_avg(Φ_t)` as an *upper bound on a physical gate's* average fidelity is a separate modelling
assumption — namely that the realised noise is at least as strong as the coherence-limited model
(`𝒜_γ ∘ 𝒟_p` is the best case) — and is **not** part of any theorem below. The Lean-verified asset is
the closed form and its monotonicity for the model channel; the "physical-gate ceiling" reading is a
stated assumption layered on top. (Convention: dephasing `𝒟_p` is applied first, then amplitude
damping `𝒜_γ`; `γ = 1 − e^{−t/T₁}`, `p = (1 − e^{−t/T₂})/2`.)

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix

/-- The **coherence channel** Kraus operators `Φ_{γ,p} = 𝒜_γ ∘ 𝒟_p`: amplitude damping with
parameter `γ` composed after dephasing with parameter `p` (four Kraus operators `Aⱼ Dᵢ`). -/
noncomputable def coherenceKraus (γ p : ℝ) : Fin (2 * 2) → Matrix (Fin 2) (Fin 2) ℂ :=
  composeKraus (ampDampKraus γ) (dephasingKraus p)

/-- The coherence channel is CPTP for `γ, p ∈ [0,1]`. -/
theorem isKrausChannel_coherenceKraus {γ p : ℝ} (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : IsKrausChannel (coherenceKraus γ p) :=
  isKrausChannel_composeKraus (isKrausChannel_ampDampKraus hγ0 hγ1)
    (isKrausChannel_dephasingKraus hp0 hp1)

/-- **Exact entanglement fidelity of the coherence channel.** Contracting the four Kraus traces
gives `F_e = ¼ ((1−p)(1+√(1−γ))² + p(1−√(1−γ))²)`. -/
theorem entanglementFidelity_coherenceKraus {γ p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    entanglementFidelity (coherenceKraus γ p)
      = ((1 - p) * (1 + Real.sqrt (1 - γ)) ^ 2 + p * (1 - Real.sqrt (1 - γ)) ^ 2) / 4 := by
  simp only [entanglementFidelity, coherenceKraus, composeKraus]
  rw [finProdFinEquiv.symm.sum_comp
      (fun q : Fin 2 × Fin 2 =>
        Complex.normSq (Matrix.trace (ampDampKraus γ q.1 * dephasingKraus p q.2))),
    Fintype.sum_prod_type]
  simp only [Fin.sum_univ_two]
  have h00 : (ampDampKraus γ 0 * dephasingKraus p 0).trace
      = ((Real.sqrt (1 - p) * (1 + Real.sqrt (1 - γ)) : ℝ) : ℂ) := by
    rw [show dephasingKraus p 0 = (Real.sqrt (1 - p) : ℂ) • 1 from rfl, Matrix.mul_smul,
      Matrix.mul_one, Matrix.trace_smul, Matrix.trace_fin_two]
    simp [ampDampKraus]
  have h01 : (ampDampKraus γ 0 * dephasingKraus p 1).trace
      = ((Real.sqrt p * (1 - Real.sqrt (1 - γ)) : ℝ) : ℂ) := by
    rw [show dephasingKraus p 1 = (Real.sqrt p : ℂ) • pauliZ from rfl, Matrix.mul_smul,
      Matrix.trace_smul, Matrix.trace_fin_two]
    simp [ampDampKraus, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]; tauto
  have h10 : (ampDampKraus γ 1 * dephasingKraus p 0).trace = (0 : ℂ) := by
    rw [show dephasingKraus p 0 = (Real.sqrt (1 - p) : ℂ) • 1 from rfl, Matrix.mul_smul,
      Matrix.mul_one, Matrix.trace_smul, Matrix.trace_fin_two]
    simp [ampDampKraus]
  have h11 : (ampDampKraus γ 1 * dephasingKraus p 1).trace = (0 : ℂ) := by
    rw [show dephasingKraus p 1 = (Real.sqrt p : ℂ) • pauliZ from rfl, Matrix.mul_smul,
      Matrix.trace_smul, Matrix.trace_fin_two]
    simp [ampDampKraus, pauliZ, Matrix.mul_apply, Fin.sum_univ_two]
  rw [h00, h01, h10, h11]
  simp only [map_zero, Complex.normSq_ofReal]
  have e1 : Real.sqrt (1 - p) * Real.sqrt (1 - p) = 1 - p := Real.mul_self_sqrt (by linarith)
  have e2 : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0
  push_cast
  linear_combination ((1 + Real.sqrt (1 - γ)) ^ 2 / 4) * e1 + ((1 - Real.sqrt (1 - γ)) ^ 2 / 4) * e2

/-! ## Time-dependent coherence channel -/

/-- Amplitude-damping weight at gate duration `t` with relaxation time `T₁`: `γ = 1 − e^{−t/T₁}`. -/
noncomputable def cohGamma (t T1 : ℝ) : ℝ := 1 - Real.exp (-t / T1)

/-- Dephasing weight at gate duration `t` with dephasing time `T₂`: `p = (1 − e^{−t/T₂})/2`. -/
noncomputable def cohP (t T2 : ℝ) : ℝ := (1 - Real.exp (-t / T2)) / 2

/-- The **coherence channel at gate duration `t`**: amplitude damping (`γ = 1 − e^{−t/T₁}`) composed
after dephasing (`p = (1 − e^{−t/T₂})/2`). -/
noncomputable def coherenceChannel (t T1 T2 : ℝ) : Fin (2 * 2) → Matrix (Fin 2) (Fin 2) ℂ :=
  coherenceKraus (cohGamma t T1) (cohP t T2)

theorem exp_neg_div_le_one {t T : ℝ} (ht : 0 ≤ t) (hT : 0 < T) : Real.exp (-t / T) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hT.le

theorem cohGamma_nonneg {t T1 : ℝ} (ht : 0 ≤ t) (hT1 : 0 < T1) : 0 ≤ cohGamma t T1 := by
  have := exp_neg_div_le_one ht hT1; unfold cohGamma; linarith

theorem cohGamma_le_one {t T1 : ℝ} : cohGamma t T1 ≤ 1 := by
  have := (Real.exp_pos (-t / T1)).le; unfold cohGamma; linarith

theorem cohP_nonneg {t T2 : ℝ} (ht : 0 ≤ t) (hT2 : 0 < T2) : 0 ≤ cohP t T2 := by
  have := exp_neg_div_le_one ht hT2; unfold cohP; linarith

theorem cohP_le_one {t T2 : ℝ} : cohP t T2 ≤ 1 := by
  have := (Real.exp_pos (-t / T2)).le; unfold cohP; linarith

/-- The coherence channel is CPTP for `0 ≤ t`, `0 < T₁`, `0 < T₂`. -/
theorem isKrausChannel_coherenceChannel {t T1 T2 : ℝ} (ht : 0 ≤ t) (hT1 : 0 < T1) (hT2 : 0 < T2) :
    IsKrausChannel (coherenceChannel t T1 T2) :=
  isKrausChannel_coherenceKraus (cohGamma_nonneg ht hT1) cohGamma_le_one (cohP_nonneg ht hT2)
    cohP_le_one

/-- `√(1 − γ(t)) = e^{−t/(2T₁)}` — the relaxation weight enters the fidelity through its square root. -/
theorem sqrt_one_sub_cohGamma (t T1 : ℝ) :
    Real.sqrt (1 - cohGamma t T1) = Real.exp (-t / (2 * T1)) := by
  have h : (1 : ℝ) - cohGamma t T1 = Real.exp (-t / T1) := by unfold cohGamma; ring
  rw [h, ← Real.exp_half]; congr 1; ring

/-- **Exact entanglement fidelity of the time-dependent coherence channel** — a sum of decaying
exponentials: `F_e(Φ_t) = ¼(1 + e^{−t/T₁} + 2 e^{−t/(2T₁) − t/T₂})`. -/
theorem entanglementFidelity_coherenceChannel {t T1 T2 : ℝ} (ht : 0 ≤ t) (hT2 : 0 < T2) :
    entanglementFidelity (coherenceChannel t T1 T2)
      = (1 + Real.exp (-t / T1) + 2 * Real.exp (-t / (2 * T1) - t / T2)) / 4 := by
  rw [coherenceChannel,
    entanglementFidelity_coherenceKraus (cohP_nonneg ht hT2) cohP_le_one,
    sqrt_one_sub_cohGamma]
  have hE2 : Real.exp (-t / (2 * T1)) * Real.exp (-t / (2 * T1)) = Real.exp (-t / T1) := by
    rw [← Real.exp_add]; congr 1; ring
  have hEu : Real.exp (-t / (2 * T1)) * Real.exp (-t / T2)
      = Real.exp (-t / (2 * T1) - t / T2) := by rw [← Real.exp_add]; congr 1; ring
  unfold cohP
  linear_combination (1 / 4 : ℝ) * hE2 + (1 / 2 : ℝ) * hEu

/-- **Exact average gate fidelity of the time-dependent coherence channel** — a sum of decaying
exponentials with floor `½`: `F_avg(Φ_t) = ½ + ⅙ e^{−t/T₁} + ⅓ e^{−t/(2T₁) − t/T₂}`. This is an exact
equality for the model channel `Φ_t = 𝒜_γ ∘ 𝒟_p`; see the module header on what is (and is not) implied
about a physical gate. -/
theorem avgGateFidelity_coherenceChannel {t T1 T2 : ℝ} (ht : 0 ≤ t) (hT1 : 0 < T1) (hT2 : 0 < T2) :
    avgGateFidelity (coherenceChannel t T1 T2)
      = 1 / 2 + (1 / 6) * Real.exp (-t / T1) + (1 / 3) * Real.exp (-t / (2 * T1) - t / T2) := by
  rw [avgGateFidelity_eq _ (isKrausChannel_coherenceChannel ht hT1 hT2),
    entanglementFidelity_coherenceChannel ht hT2]
  ring

/-! ## Monotone decay and endpoints of the model channel's average gate fidelity -/

/-- **The model channel's average gate fidelity is monotone decreasing in gate duration `t`** (each
exponential term is antitone). Interpreting this as an upper bound on a physical gate's fidelity is the
modelling assumption noted in the module header — it is not part of this theorem. -/
theorem avgGateFidelity_coherenceChannel_antitone {T1 T2 : ℝ} (hT1 : 0 < T1) (hT2 : 0 < T2)
    {t t' : ℝ} (ht : 0 ≤ t) (htt : t ≤ t') :
    avgGateFidelity (coherenceChannel t' T1 T2) ≤ avgGateFidelity (coherenceChannel t T1 T2) := by
  have ht' : 0 ≤ t' := le_trans ht htt
  rw [avgGateFidelity_coherenceChannel ht hT1 hT2, avgGateFidelity_coherenceChannel ht' hT1 hT2]
  have hA : Real.exp (-t' / T1) ≤ Real.exp (-t / T1) := by
    apply Real.exp_le_exp.mpr; rw [neg_div, neg_div]
    exact neg_le_neg ((div_le_div_iff_of_pos_right hT1).mpr htt)
  have hB : Real.exp (-t' / (2 * T1) - t' / T2) ≤ Real.exp (-t / (2 * T1) - t / T2) := by
    apply Real.exp_le_exp.mpr
    have h1 : -t' / (2 * T1) ≤ -t / (2 * T1) :=
      (div_le_div_iff_of_pos_right (by linarith : (0 : ℝ) < 2 * T1)).mpr (neg_le_neg htt)
    have h2 : t / T2 ≤ t' / T2 := (div_le_div_iff_of_pos_right hT2).mpr htt
    linarith
  linarith

/-- **Floor:** the model channel's average gate fidelity never drops below `½` (the fully-decohered
qubit value). -/
theorem avgGateFidelity_coherenceChannel_ge_half {t T1 T2 : ℝ} (ht : 0 ≤ t) (hT1 : 0 < T1)
    (hT2 : 0 < T2) : 1 / 2 ≤ avgGateFidelity (coherenceChannel t T1 T2) := by
  rw [avgGateFidelity_coherenceChannel ht hT1 hT2]
  have h1 := (Real.exp_pos (-t / T1)).le
  have h2 := (Real.exp_pos (-t / (2 * T1) - t / T2)).le
  linarith

/-- **Ceiling:** the model channel's average gate fidelity never exceeds `1` (the zero-duration
value). -/
theorem avgGateFidelity_coherenceChannel_le_one {t T1 T2 : ℝ} (ht : 0 ≤ t) (hT1 : 0 < T1)
    (hT2 : 0 < T2) : avgGateFidelity (coherenceChannel t T1 T2) ≤ 1 := by
  rw [avgGateFidelity_coherenceChannel ht hT1 hT2]
  have h1 := exp_neg_div_le_one ht hT1
  have h2 : Real.exp (-t / (2 * T1) - t / T2) ≤ 1 := by
    rw [Real.exp_le_one_iff]
    have e1 : -t / (2 * T1) ≤ 0 := by
      rw [neg_div]; exact neg_nonpos.mpr (div_nonneg ht (by linarith))
    have e2 : 0 ≤ t / T2 := div_nonneg ht hT2.le
    linarith
  linarith

end SKEFTHawking.QuantumNetwork
