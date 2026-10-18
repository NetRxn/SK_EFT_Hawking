import SKEFTHawking.FinitePositiveKernelTransfer
import SKEFTHawking.QuantumNetwork.FidelityBounds

/-! Stationary finite Kraus channels acting on the reconstructed observable quotient.
The Schwarz remainder derives contraction before descent. Singular stationary
states are allowed; weighted detailed balance is a separate symmetry hypothesis. -/
noncomputable section
open Matrix
open scoped ComplexOrder InnerProductSpace
namespace SKEFTHawking.FinitePositiveKernel.GibbsObservable.Channel
open SKEFTHawking.QuantumNetwork
variable {n : Type*} [Fintype n] [DecidableEq n] {m : ℕ}

/-- The actual Heisenberg action dual to the existing Schrödinger Kraus map. -/
def heisenberg (V : Fin m → Matrix n n ℂ) (X : Matrix n n ℂ) : Matrix n n ℂ :=
  ∑ i, (V i)ᴴ * X * V i

theorem heisenberg_add (V : Fin m → Matrix n n ℂ) (X Y : Matrix n n ℂ) :
    heisenberg V (X + Y) = heisenberg V X + heisenberg V Y := by
  simp [heisenberg, mul_add, add_mul, Finset.sum_add_distrib]

theorem heisenberg_smul (V : Fin m → Matrix n n ℂ) (c : ℂ) (X : Matrix n n ℂ) :
    heisenberg V (c • X) = c • heisenberg V X := by
  simp [heisenberg, Finset.smul_sum]

def heisenbergLinear (V : Fin m → Matrix n n ℂ) :
    Matrix n n ℂ →ₗ[ℂ] Matrix n n ℂ where
  toFun := heisenberg V
  map_add' := heisenberg_add V
  map_smul' := heisenberg_smul V

omit [DecidableEq n] in
theorem heisenberg_star (V : Fin m → Matrix n n ℂ) (X : Matrix n n ℂ) :
    heisenberg V Xᴴ = (heisenberg V X)ᴴ := by
  simp [heisenberg, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul, mul_assoc]

theorem heisenberg_one (V : Fin m → Matrix n n ℂ) (hV : IsKrausChannel V) :
    heisenberg V 1 = 1 := by
  simpa [heisenberg, IsKrausChannel] using hV

omit [DecidableEq n] in
/-- The exact finite trace-duality identity fixes the direction of the channel action. -/
theorem trace_duality (V : Fin m → Matrix n n ℂ) (ρ X : Matrix n n ℂ) :
    (ρ * heisenberg V X).trace = (krausMap V ρ * X).trace := by
  simp only [heisenberg, krausMap, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro i _
  calc
    (ρ * ((V i)ᴴ * X * V i)).trace = (V i * (ρ * (V i)ᴴ) * X).trace := by
      simpa only [mul_assoc] using Matrix.trace_mul_cycle' ρ ((V i)ᴴ * X) (V i)
    _ = (V i * ρ * (V i)ᴴ * X).trace := by rw [mul_assoc (V i) ρ]

/-- The Kraus Stinespring remainder is an explicit matrix, not an assumed inequality. -/
def schwarzRemainder (V : Fin m → Matrix n n ℂ) (X : Matrix n n ℂ) (i : Fin m) :
    Matrix n n ℂ := X * V i - V i * heisenberg V X

theorem schwarz_term (V : Fin m → Matrix n n ℂ) (X : Matrix n n ℂ) (i : Fin m) : (schwarzRemainder V X i)ᴴ * schwarzRemainder V X i =
    (V i)ᴴ * (Xᴴ * X) * V i - ((V i)ᴴ * Xᴴ * V i) * heisenberg V X -
    (heisenberg V X)ᴴ * ((V i)ᴴ * X * V i) +
    (heisenberg V X)ᴴ * ((V i)ᴴ * V i) * heisenberg V X := by
  simp only [schwarzRemainder, Matrix.conjTranspose_sub, Matrix.conjTranspose_mul]
  noncomm_ring

theorem schwarz_remainder_identity (V : Fin m → Matrix n n ℂ) (hV : IsKrausChannel V)
    (X : Matrix n n ℂ) :
    ∑ i, (schwarzRemainder V X i)ᴴ * schwarzRemainder V X i =
      heisenberg V (Xᴴ * X) - (heisenberg V X)ᴴ * heisenberg V X := by
  simp_rw [schwarz_term]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  simp only [← Matrix.sum_mul, ← Matrix.mul_sum]
  change heisenberg V (Xᴴ * X) - heisenberg V Xᴴ * heisenberg V X -
    (heisenberg V X)ᴴ * heisenberg V X +
    (heisenberg V X)ᴴ * (∑ i, (V i)ᴴ * V i) * heisenberg V X = _
  rw [heisenberg_star]
  rw [hV, mul_one]
  abel

/-- Kadison–Schwarz follows from a finite sum of positive squares. -/
theorem schwarz_positive (V : Fin m → Matrix n n ℂ) (hV : IsKrausChannel V)
    (X : Matrix n n ℂ) :
    (heisenberg V (Xᴴ * X) - (heisenberg V X)ᴴ * heisenberg V X).PosSemidef := by
  rw [← schwarz_remainder_identity V hV X]
  exact Matrix.posSemidef_sum _ (fun i _ => Matrix.posSemidef_conjTranspose_mul_self _)

/-- Stationarity converts the Schwarz defect into weighted observable energy decrease. -/
theorem weighted_energy_le (V : Fin m → Matrix n n ℂ) (hV : IsKrausChannel V)
    {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef) (hstationary : krausMap V ρ = ρ)
    (X : Matrix n n ℂ) :
    (heisenberg V X * ρ * (heisenberg V X)ᴴ).trace.re ≤ (X * ρ * Xᴴ).trace.re := by
  have hp := (trace_mul_nonneg hρ (schwarz_positive V hV X)).1
  rw [Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re, trace_duality, hstationary] at hp
  have htrace (Y : Matrix n n ℂ) : (ρ * (Yᴴ * Y)).trace = (Y * ρ * Yᴴ).trace :=
    (Matrix.trace_mul_cycle' ρ Yᴴ Y).trans (by rw [← mul_assoc])
  rw [htrace, htrace] at hp
  exact sub_nonneg.mp hp

section Quotient
variable {ρ : Matrix n n ℂ} (hρ : ρ.PosSemidef)

/-- Actual Heisenberg action on matrix-unit coefficients, prior to quotienting. -/
def coefficientAction (V : Fin m → Matrix n n ℂ) :
    Coefficients (gram_posSemidef hρ) →ₗ[ℂ] Coefficients (gram_posSemidef hρ) :=
  (synthEquiv hρ).symm.toLinearMap.comp ((heisenbergLinear V).comp (synthEquiv hρ).toLinearMap)

theorem synth_coefficientAction (V : Fin m → Matrix n n ℂ)
    (c : Coefficients (gram_posSemidef hρ)) :
    synth (coefficientAction hρ V c) = heisenberg V (synth c) :=
  (synthEquiv hρ).apply_symm_apply _

/-- Energy contraction is derived from Kraus normalization and stationarity. -/
theorem coefficient_energy_le (V : Fin m → Matrix n n ℂ) (hV : IsKrausChannel V)
    (hstationary : krausMap V ρ = ρ) (c : Coefficients (gram_posSemidef hρ)) :
    (pairing (gram ρ) (coefficientAction hρ V c) (coefficientAction hρ V c)).re ≤
      (pairing (gram ρ) c c).re := by
  rw [pairing_gram hρ, pairing_gram hρ, synth_coefficientAction]
  exact weighted_energy_le V hV hρ hstationary (synth c)

/-- A stationary quantum channel descends to a contraction on the actual Gram quotient. -/
def quotientChannel (V : Fin m → Matrix n n ℂ) (hV : IsKrausChannel V)
    (hstationary : krausMap V ρ = ρ) : Space (gram ρ) (gram_posSemidef hρ) →L[ℂ]
      Space (gram ρ) (gram_posSemidef hρ) :=
  descendContraction (gram_posSemidef hρ) (coefficientAction hρ V)
    (coefficient_energy_le hρ V hV hstationary)

theorem quotientChannel_observable (V : Fin m → Matrix n n ℂ) (hV : IsKrausChannel V)
    (hstationary : krausMap V ρ = ρ) (X : Matrix n n ℂ) :
    quotientChannel hρ V hV hstationary (observable hρ X) = observable hρ (heisenberg V X) := by
  change descend _ _ _ (mk _ _ _) = _
  rw [descend_mk]
  apply congrArg (mk _ _)
  change (synthEquiv hρ).symm (heisenberg V (synth (fun p => X p.1 p.2))) = _
  rw [synth_flat]
  rfl

theorem quotientChannel_norm_le (V : Fin m → Matrix n n ℂ) (hV : IsKrausChannel V)
    (hstationary : krausMap V ρ = ρ) (z : Space (gram ρ) (gram_posSemidef hρ)) :
    ‖quotientChannel hρ V hV hstationary z‖ ≤ ‖z‖ :=
  descend_norm_le _ _ (coefficient_energy_le hρ V hV hstationary) z

/-- Weighted detailed balance is a concrete trace identity for the actual channel. -/
def DetailedBalance (ρ : Matrix n n ℂ) (V : Fin m → Matrix n n ℂ) : Prop :=
  ∀ X Y, (Y * ρ * (heisenberg V X)ᴴ).trace = (heisenberg V Y * ρ * Xᴴ).trace

theorem quotientChannel_symmetric (V : Fin m → Matrix n n ℂ) (hV : IsKrausChannel V)
    (hstationary : krausMap V ρ = ρ) (hDB : DetailedBalance ρ V) :
    (quotientChannel hρ V hV hstationary).IsSymmetric := by
  intro z w
  obtain ⟨X, rfl⟩ := observable_surjective hρ z
  obtain ⟨Y, rfl⟩ := observable_surjective hρ w
  change ⟪quotientChannel hρ V hV hstationary (observable hρ X), observable hρ Y⟫_ℂ =
    ⟪observable hρ X, quotientChannel hρ V hV hstationary (observable hρ Y)⟫_ℂ
  rw [quotientChannel_observable, quotientChannel_observable, inner_observable, inner_observable]
  exact hDB X Y

theorem quotientChannel_selfAdjoint (V : Fin m → Matrix n n ℂ) (hV : IsKrausChannel V)
    (hstationary : krausMap V ρ = ρ) (hDB : DetailedBalance ρ V) :
    IsSelfAdjoint (quotientChannel hρ V hV hstationary) :=
  (quotientChannel_symmetric hρ V hV hstationary hDB).isSelfAdjoint

/-- Algebraic powers represent repeated applications of the actual channel. -/
theorem quotientChannel_pow_observable (V : Fin m → Matrix n n ℂ) (hV : IsKrausChannel V)
    (hstationary : krausMap V ρ = ρ) (k : ℕ) (X : Matrix n n ℂ) :
    (quotientChannel hρ V hV hstationary ^ k) (observable hρ X) =
      observable hρ ((heisenberg V)^[k] X) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [pow_succ', mul_apply_eq_comp, ih, quotientChannel_observable,
      Function.iterate_succ_apply']

/-- Laziness averages the identity and channel; it does not assume Hilbert positivity. -/
def lazyChannel (V : Fin m → Matrix n n ℂ) (hV : IsKrausChannel V)
    (hstationary : krausMap V ρ = ρ) : Space (gram ρ) (gram_posSemidef hρ) →L[ℂ]
      Space (gram ρ) (gram_posSemidef hρ) :=
  (1/2 : ℂ) • (ContinuousLinearMap.id ℂ _ + quotientChannel hρ V hV hstationary)

theorem lazyChannel_apply (V : Fin m → Matrix n n ℂ) (hV : IsKrausChannel V)
    (hstationary : krausMap V ρ = ρ) (z : Space (gram ρ) (gram_posSemidef hρ)) :
    lazyChannel hρ V hV hstationary z =
      (1/2 : ℂ) • (z + quotientChannel hρ V hV hstationary z) := rfl

theorem lazyChannel_observable (V : Fin m → Matrix n n ℂ) (hV : IsKrausChannel V)
    (hstationary : krausMap V ρ = ρ) (X : Matrix n n ℂ) :
    lazyChannel hρ V hV hstationary (observable hρ X) =
      observable hρ ((1/2 : ℂ) • (X + heisenberg V X)) := by
  rw [lazyChannel_apply, quotientChannel_observable, observable_smul]
  exact congrArg (fun z => (1/2 : ℂ) • z) ((observableLinear hρ).map_add X _).symm

theorem lazyChannel_norm_le (V : Fin m → Matrix n n ℂ) (hV : IsKrausChannel V)
    (hstationary : krausMap V ρ = ρ) (z : Space (gram ρ) (gram_posSemidef hρ)) :
    ‖lazyChannel hρ V hV hstationary z‖ ≤ ‖z‖ := by
  rw [lazyChannel_apply, norm_smul]
  have htriangle := norm_add_le z (quotientChannel hρ V hV hstationary z)
  have hcontract := quotientChannel_norm_le hρ V hV hstationary z
  norm_num
  linarith

theorem lazyChannel_symmetric (V : Fin m → Matrix n n ℂ) (hV : IsKrausChannel V)
    (hstationary : krausMap V ρ = ρ) (hDB : DetailedBalance ρ V) :
    (lazyChannel hρ V hV hstationary).IsSymmetric := by
  have hid : (LinearMap.id : Space (gram ρ) (gram_posSemidef hρ) →ₗ[ℂ] _).IsSymmetric :=
    fun _ _ => rfl
  exact LinearMap.IsSymmetric.smul (by norm_num [map_ofNat])
    (hid.add (quotientChannel_symmetric hρ V hV hstationary hDB))

/-- Symmetry and the derived contraction bound prove positivity of the lazy channel. -/
theorem lazyChannel_positive (V : Fin m → Matrix n n ℂ) (hV : IsKrausChannel V)
    (hstationary : krausMap V ρ = ρ) (hDB : DetailedBalance ρ V) :
    (lazyChannel hρ V hV hstationary).IsPositive := by
  refine ⟨lazyChannel_symmetric hρ V hV hstationary hDB, ?_⟩
  intro z
  change 0 ≤ (⟪lazyChannel hρ V hV hstationary z, z⟫_ℂ).re
  have hcs := re_inner_le_norm (𝕜 := ℂ) (-(quotientChannel hρ V hV hstationary z)) z
  simp only [inner_neg_left, map_neg, norm_neg] at hcs
  change -(⟪quotientChannel hρ V hV hstationary z, z⟫_ℂ).re ≤ _ at hcs
  have hcontract := mul_le_mul_of_nonneg_right
    (quotientChannel_norm_le hρ V hV hstationary z) (norm_nonneg z)
  have hself := norm_sq_eq_re_inner (𝕜 := ℂ) z
  rw [lazyChannel_apply, inner_smul_left, inner_add_left]
  norm_num [Complex.mul_re, Complex.add_re, ← Complex.ofReal_pow]
  change ‖z‖ ^ 2 = (⟪z, z⟫_ℂ).re at hself
  nlinarith

theorem lazyChannel_selfAdjoint (V : Fin m → Matrix n n ℂ) (hV : IsKrausChannel V)
    (hstationary : krausMap V ρ = ρ) (hDB : DetailedBalance ρ V) :
    IsSelfAdjoint (lazyChannel hρ V hV hstationary) :=
  (lazyChannel_positive hρ V hV hstationary hDB).isSelfAdjoint

end Quotient
end SKEFTHawking.FinitePositiveKernel.GibbsObservable.Channel
