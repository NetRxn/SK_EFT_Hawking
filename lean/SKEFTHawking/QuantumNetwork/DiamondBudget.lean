import SKEFTHawking.QuantumNetwork.NamedChannelDiamondExact

/-!
# Diamond-norm network error budget (Phase 6AH, Wave 6AH.3)

The worst-case (diamond) analogue of the trace-distance chain bound. Channel composition in the
Kraus representation `composeKraus L K` (Kraus operators `Lⱼ Kᵢ`) realises `Φ_L ∘ Φ_K`, and the
diamond distance is contractive under composition with a fixed CPTP channel. Telescoping gives the
N-segment **error budget**: the worst-case end-to-end error of a composed channel network is bounded
by the sum of the per-segment diamond errors.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; no project-local axioms;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder Kronecker

variable {ι : Type*} [Fintype ι] [DecidableEq ι] {a b : ℕ}

/-- **Channel composition in the Kraus representation.** The Kraus operators of `Φ_L ∘ Φ_K` are the
products `Lⱼ Kᵢ` (indexed by `Fin b × Fin a ≃ Fin (b·a)`). -/
noncomputable def composeKraus (L : Fin b → Matrix ι ι ℂ) (K : Fin a → Matrix ι ι ℂ) :
    Fin (b * a) → Matrix ι ι ℂ :=
  fun idx => L (finProdFinEquiv.symm idx).1 * K (finProdFinEquiv.symm idx).2

/-- **`composeKraus` realises channel composition:** `krausMap (L∘K) = krausMap L ∘ krausMap K`. -/
theorem krausMap_composeKraus (L : Fin b → Matrix ι ι ℂ) (K : Fin a → Matrix ι ι ℂ)
    (ρ : Matrix ι ι ℂ) :
    krausMap (composeKraus L K) ρ = krausMap L (krausMap K ρ) := by
  unfold krausMap composeKraus
  rw [finProdFinEquiv.symm.sum_comp
    (fun p : Fin b × Fin a => L p.1 * K p.2 * ρ * (L p.1 * K p.2)ᴴ), Fintype.sum_prod_type]
  simp only [Matrix.mul_sum, Matrix.sum_mul]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.conjTranspose_mul]; noncomm_ring

/-- The composition of two CPTP channels is CPTP. -/
theorem isKrausChannel_composeKraus {L : Fin b → Matrix ι ι ℂ} {K : Fin a → Matrix ι ι ℂ}
    (hL : IsKrausChannel L) (hK : IsKrausChannel K) : IsKrausChannel (composeKraus L K) := by
  unfold IsKrausChannel composeKraus at *
  rw [finProdFinEquiv.symm.sum_comp (fun p : Fin b × Fin a => (L p.1 * K p.2)ᴴ * (L p.1 * K p.2)),
    Fintype.sum_prod_type]
  have hcol : ∀ i : Fin a, ∑ j, (L j * K i)ᴴ * (L j * K i) = (K i)ᴴ * (K i) := by
    intro i
    simp_rw [Matrix.conjTranspose_mul, show ∀ j, (K i)ᴴ * (L j)ᴴ * (L j * K i)
      = (K i)ᴴ * ((L j)ᴴ * L j) * K i from fun j => by simp only [Matrix.mul_assoc]]
    rw [← Finset.sum_mul, ← Matrix.mul_sum, hL, Matrix.mul_one]
  rw [Finset.sum_comm]; simp_rw [hcol]; exact hK

/-! ## Diamond data processing and the composition error budget -/

section Diamond
variable {n : ℕ}

/-- Tensoring distributes over composition: `(L∘K)⊗id = (L⊗id)∘(K⊗id)`, since `(A⊗1)(B⊗1)=(AB)⊗1`. -/
theorem tensorKraus_composeKraus (L : Fin b → Matrix (Fin n) (Fin n) ℂ)
    (K : Fin a → Matrix (Fin n) (Fin n) ℂ) :
    tensorKraus (composeKraus L K) = composeKraus (tensorKraus L) (tensorKraus K) := by
  funext idx
  simp only [tensorKraus, composeKraus]
  rw [← Matrix.mul_kronecker_mul, Matrix.one_mul]

/-- **Diamond data processing (pre-channel fixed).** Composing with a fixed CPTP channel `L` on the
output contracts the diamond distance: `diamondDist(L∘K₁, L∘K₂) ≤ diamondDist(K₁, K₂)`. -/
theorem diamondDist_composeKraus_left {L : Fin b → Matrix (Fin n) (Fin n) ℂ}
    {K₁ K₂ : Fin a → Matrix (Fin n) (Fin n) ℂ}
    (hL : IsKrausChannel L) (hK₁ : IsKrausChannel K₁) (hK₂ : IsKrausChannel K₂) :
    diamondDist (composeKraus L K₁) (composeKraus L K₂) ≤ diamondDist K₁ K₂ := by
  apply Real.sSup_le _ diamondDist_nonneg
  rintro d ⟨ρ, hρ, rfl⟩
  rw [tensorKraus_composeKraus, tensorKraus_composeKraus, krausMap_composeKraus,
    krausMap_composeKraus]
  calc _ ≤ traceDist (krausMap (tensorKraus K₁) ρ) (krausMap (tensorKraus K₂) ρ) :=
        traceDist_krausMap_le (isKrausChannel_tensorKraus hL)
          (krausMap_isDensityOperator (isKrausChannel_tensorKraus hK₁) hρ).1.isHermitian
          (krausMap_isDensityOperator (isKrausChannel_tensorKraus hK₂) hρ).1.isHermitian
    _ ≤ diamondDist K₁ K₂ := le_diamondDist hK₁ hK₂ hρ

/-- **Diamond data processing (post-channel fixed).** Pre-composing with a fixed CPTP channel `K`
contracts: `diamondDist(L₁∘K, L₂∘K) ≤ diamondDist(L₁, L₂)`. -/
theorem diamondDist_composeKraus_right {L₁ L₂ : Fin b → Matrix (Fin n) (Fin n) ℂ}
    {K : Fin a → Matrix (Fin n) (Fin n) ℂ}
    (hL₁ : IsKrausChannel L₁) (hL₂ : IsKrausChannel L₂) (hK : IsKrausChannel K) :
    diamondDist (composeKraus L₁ K) (composeKraus L₂ K) ≤ diamondDist L₁ L₂ := by
  apply Real.sSup_le _ diamondDist_nonneg
  rintro d ⟨ρ, hρ, rfl⟩
  rw [tensorKraus_composeKraus, tensorKraus_composeKraus, krausMap_composeKraus,
    krausMap_composeKraus]
  exact le_diamondDist hL₁ hL₂ (krausMap_isDensityOperator (isKrausChannel_tensorKraus hK) hρ)

/-- **Diamond sub-additivity under composition (the error budget for one stage):**
`‖Φ_{L₁}∘Φ_{K₁} − Φ_{L₂}∘Φ_{K₂}‖_◇ ≤ ‖Φ_{L₁}−Φ_{L₂}‖_◇ + ‖Φ_{K₁}−Φ_{K₂}‖_◇`. Triangle plus the two
data-processing inequalities; iterating gives the N-segment worst-case error budget
`total ≤ ∑ per-segment diamond errors`. -/
theorem diamondDist_composeKraus_le {L₁ L₂ : Fin b → Matrix (Fin n) (Fin n) ℂ}
    {K₁ K₂ : Fin a → Matrix (Fin n) (Fin n) ℂ}
    (hL₁ : IsKrausChannel L₁) (hL₂ : IsKrausChannel L₂) (hK₁ : IsKrausChannel K₁)
    (hK₂ : IsKrausChannel K₂) :
    diamondDist (composeKraus L₁ K₁) (composeKraus L₂ K₂)
      ≤ diamondDist L₁ L₂ + diamondDist K₁ K₂ :=
  calc diamondDist (composeKraus L₁ K₁) (composeKraus L₂ K₂)
      ≤ diamondDist (composeKraus L₁ K₁) (composeKraus L₂ K₁)
        + diamondDist (composeKraus L₂ K₁) (composeKraus L₂ K₂) :=
        diamondDist_triangle (isKrausChannel_composeKraus hL₁ hK₁)
          (isKrausChannel_composeKraus hL₂ hK₁) (isKrausChannel_composeKraus hL₂ hK₂)
    _ ≤ diamondDist L₁ L₂ + diamondDist K₁ K₂ :=
        add_le_add (diamondDist_composeKraus_right hL₁ hL₂ hK₁)
          (diamondDist_composeKraus_left hL₂ hK₁ hK₂)

/-- **Worked 2-stage diamond error budget (named channels).** A concrete instance of
`diamondDist_composeKraus_le`: a depolarizing channel (strength `p`) followed by a dephasing
channel (strength `γ`), compared against the ideal `id ∘ id` pipeline. Since the per-stage diamond
distances from the identity are *exactly* `γ` (`diamondDist_dephasing_eq`) and `p`
(`diamondDist_depolarizing_eq`), the composed worst-case (diamond) error is bounded by their sum
`γ + p` — the composition error budget made fully explicit on physical noise channels. -/
theorem diamondDist_dephasing_after_depolarizing_le {γ p : ℝ}
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    diamondDist (composeKraus (dephasingKraus γ) (depolarizingKraus p))
        (composeKraus (idKrausPad 1 2) (idKrausPad 3 2)) ≤ γ + p := by
  have h := diamondDist_composeKraus_le (isKrausChannel_dephasingKraus hγ0 hγ1)
    (isKrausChannel_idKrausPad 1 2) (isKrausChannel_depolarizingKraus hp0 hp1)
    (isKrausChannel_idKrausPad 3 2)
  rwa [diamondDist_dephasing_eq hγ0 hγ1, diamondDist_depolarizing_eq hp0 hp1] at h

end Diamond

end SKEFTHawking.QuantumNetwork
