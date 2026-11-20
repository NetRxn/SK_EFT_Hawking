import SKEFTHawking.QuantumNetwork.FiniteAdaptiveKrausRealization
import SKEFTHawking.QuantumNetwork.FiniteThreeLevelHistoryReadout

/-!
# Faithful reversal of an entire adaptive qutrit strategy

The reversed operations are defined before normalization. Their completeness is
equivalent to stationarity of the whole strategy at the existing nontracial state.
This is a global complete-leaf instrument, not a local causal reversal or CP inverse.

Observable transfer is conditional on preservation of the accessible range and
an actual coefficient intertwiner. Selfadjointness additionally requires
`K*C=Cᴴ*K`, positivity requires `(K*C).PosSemidef`, and contraction requires
`(K-Cᴴ*K*C).PosSemidef`. These conditions do not identify an inserted chronology.
The weighted metric is distinct from operational trace distance. No continuum,
physical gap, calibrated clock, or computational advantage is asserted.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteThreeLevelStationaryStrategyReflection
open Matrix FiniteInterventionProcess
open scoped BigOperators ComplexOrder Kronecker
open FiniteThreeLevelPositiveHistory (Q MatQ rhoN R Rinv Gamma Phi Psi form)
open FiniteAdaptiveKrausRealization (joint unJoint recodeInstrument recodeStep recodeTree
  recodeHistory historyEquiv)

variable {o n : ℕ}

noncomputable def branch (T : Tree Q Unit o n) (h : History o n) (X : MatQ) : MatQ :=
  FiniteAdaptiveKrausRealization.unJoint (run Q Unit o T h (FiniteAdaptiveKrausRealization.joint X))

noncomputable def effect (T : Tree Q Unit o n) (h : History o n) : MatQ :=
  FiniteAdaptiveKrausRealization.unJoint (FiniteAdaptiveKrausRealization.leafEffect T h)

noncomputable def branchDual (T : Tree Q Unit o n) (h : History o n) (Y : MatQ) : MatQ :=
  ∑ z, (FiniteAdaptiveKrausRealization.systemPathKraus T h z)ᴴ * Y * FiniteAdaptiveKrausRealization.systemPathKraus T h z

theorem branch_path (T : Tree Q Unit o n) (h : History o n) (X : MatQ) :
    branch T h X = ∑ z, FiniteAdaptiveKrausRealization.systemPathKraus T h z * X * (FiniteAdaptiveKrausRealization.systemPathKraus T h z)ᴴ :=
  FiniteAdaptiveKrausRealization.system_run_eq_pathKraus T h X

theorem effect_path (T : Tree Q Unit o n) (h : History o n) :
    effect T h = ∑ z, (FiniteAdaptiveKrausRealization.systemPathKraus T h z)ᴴ * FiniteAdaptiveKrausRealization.systemPathKraus T h z :=
  FiniteAdaptiveKrausRealization.system_leafEffect T h

theorem branchDual_one (T : Tree Q Unit o n) (h : History o n) :
    branchDual T h 1 = effect T h := by simp [branchDual, effect_path]

theorem effect_sum (T : Tree Q Unit o n) : ∑ h, effect T h = 1 := by
  simp_rw [effect_path]
  exact FiniteAdaptiveKrausRealization.system_path_complete T

theorem effect_posSemidef (T : Tree Q Unit o n) (h : History o n) :
    (effect T h).PosSemidef := by
  rw [effect_path]
  apply Matrix.posSemidef_sum
  intro z _
  exact Matrix.posSemidef_conjTranspose_mul_self _

theorem effect_adjoint (T : Tree Q Unit o n) (h : History o n) :
    (effect T h)ᴴ = effect T h := (effect_posSemidef T h).isHermitian

theorem branch_trace_duality (T : Tree Q Unit o n) (h : History o n) (Y X : MatQ) :
    (Y * branch T h X).trace = (branchDual T h Y * X).trace := by
  rw [branch_path]
  simp only [branchDual, Matrix.mul_sum, Matrix.sum_mul, Matrix.trace_sum]
  apply Finset.sum_congr rfl
  intro z _
  simpa only [Matrix.mul_assoc] using
    Matrix.trace_mul_comm (Y * FiniteAdaptiveKrausRealization.systemPathKraus T h z * X) (FiniteAdaptiveKrausRealization.systemPathKraus T h z)ᴴ

theorem branch_trace (T : Tree Q Unit o n) (h : History o n) (X : MatQ) :
    (branch T h X).trace = (effect T h * X).trace := by
  simpa [branchDual_one] using branch_trace_duality T h 1 X

def Stationary (T : Tree Q Unit o n) : Prop := (∑ h, branch T h rhoN) = rhoN

noncomputable def inverseGamma (X : MatQ) : MatQ := Rinv * X * Rinv

theorem inverseGamma_rho : inverseGamma rhoN = 1 := by
  rw [inverseGamma, ← FiniteThreeLevelPositiveHistory.R_square]
  simp only [← Matrix.mul_assoc, FiniteThreeLevelPositiveHistory.Rinv_mul, Matrix.one_mul, FiniteThreeLevelPositiveHistory.R_mul_inv]

/-- Raw reversed Kraus operators exist without assuming stationarity. -/
noncomputable def reverseKraus (T : Tree Q Unit o n) (h : History o n)
    (z : FiniteAdaptiveKrausRealization.Path T h) : MatQ := R * (FiniteAdaptiveKrausRealization.systemPathKraus T h z)ᴴ * Rinv

noncomputable def reverseBranch (T : Tree Q Unit o n) (h : History o n) (X : MatQ) : MatQ :=
  ∑ z, reverseKraus T h z * X * (reverseKraus T h z)ᴴ

theorem reverseBranch_eq_Gamma_dual (T : Tree Q Unit o n) (h : History o n) (X : MatQ) :
    reverseBranch T h X = Gamma (branchDual T h (inverseGamma X)) := by
  simp only [reverseBranch, reverseKraus, branchDual, inverseGamma, Gamma,
    Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    FiniteThreeLevelPositiveHistory.R_adjoint, FiniteThreeLevelHistoryReadout.Rinv_adjoint,
    Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_assoc]

theorem reverseBranch_rho (T : Tree Q Unit o n) (h : History o n) :
    reverseBranch T h rhoN = Gamma (effect T h) := by
  rw [reverseBranch_eq_Gamma_dual, inverseGamma_rho, branchDual_one]

theorem reverseKraus_gram (T : Tree Q Unit o n) (h : History o n) (z : FiniteAdaptiveKrausRealization.Path T h) :
    (reverseKraus T h z)ᴴ * reverseKraus T h z =
      Rinv * (FiniteAdaptiveKrausRealization.systemPathKraus T h z * rhoN * (FiniteAdaptiveKrausRealization.systemPathKraus T h z)ᴴ) * Rinv := by
  simp only [reverseKraus, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    FiniteThreeLevelPositiveHistory.R_adjoint, FiniteThreeLevelHistoryReadout.Rinv_adjoint]
  rw [← FiniteThreeLevelPositiveHistory.R_square]
  noncomm_ring

theorem reverse_complete_formula (T : Tree Q Unit o n) :
    (∑ h, ∑ z, (reverseKraus T h z)ᴴ * reverseKraus T h z) =
      Rinv * (∑ h, branch T h rhoN) * Rinv := by
  simp_rw [reverseKraus_gram, branch_path]
  simp only [Matrix.mul_sum, Matrix.sum_mul]

/-- Necessity and sufficiency concern the aggregate strategy, including feedback. -/
theorem reverse_normalized_iff (T : Tree Q Unit o n) :
    (∑ h, ∑ z, (reverseKraus T h z)ᴴ * reverseKraus T h z) = 1 ↔ Stationary T := by
  rw [reverse_complete_formula]
  constructor
  · intro he
    have hc := congrArg (fun X : MatQ => R * X * R) he
    simpa only [Matrix.mul_assoc, ← Matrix.mul_assoc R Rinv,
      FiniteThreeLevelPositiveHistory.R_mul_inv, Matrix.one_mul,
      FiniteThreeLevelPositiveHistory.Rinv_mul, Matrix.mul_one,
      FiniteThreeLevelPositiveHistory.R_square, Stationary] using hc
  · intro he
    change (∑ h, branch T h rhoN) = rhoN at he
    rw [he]
    exact inverseGamma_rho

theorem reverse_stationary (T : Tree Q Unit o n) :
    (∑ h, reverseBranch T h rhoN) = rhoN := by
  simp_rw [reverseBranch_rho, Gamma]
  rw [← Matrix.sum_mul, ← Matrix.mul_sum, effect_sum]
  simpa using FiniteThreeLevelPositiveHistory.R_square

/-- Reversal is involutive on Kraus operators, not inversion under channel composition. -/
theorem reverseKraus_involution (T : Tree Q Unit o n) (h : History o n) (z : FiniteAdaptiveKrausRealization.Path T h) :
    R * (reverseKraus T h z)ᴴ * Rinv = FiniteAdaptiveKrausRealization.systemPathKraus T h z := by
  simp only [reverseKraus, Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose,
    FiniteThreeLevelPositiveHistory.R_adjoint, FiniteThreeLevelHistoryReadout.Rinv_adjoint, ← Matrix.mul_assoc, FiniteThreeLevelPositiveHistory.R_mul_inv, Matrix.one_mul]
  simp only [Matrix.mul_assoc, FiniteThreeLevelPositiveHistory.R_mul_inv, Matrix.mul_one]

theorem reverseBranch_posSemidef (T : Tree Q Unit o n) (h : History o n)
    {X : MatQ} (hX : X.PosSemidef) : (reverseBranch T h X).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro z _
  exact hX.mul_mul_conjTranspose_same _

/-- Explicit finite spectator Kraus lifts also preserve positivity before normalization. -/
theorem reverseBranch_spectator_posSemidef (T : Tree Q Unit o n) (h : History o n)
    (F : Type*) [Fintype F] [DecidableEq F]
    {X : Matrix (Q × F) (Q × F) ℂ} (hX : X.PosSemidef) :
    (∑ z, (reverseKraus T h z ⊗ₖ (1 : Matrix F F ℂ)) * X *
      (reverseKraus T h z ⊗ₖ (1 : Matrix F F ℂ))ᴴ).PosSemidef := by
  apply Matrix.posSemidef_sum
  intro z _
  exact hX.mul_mul_conjTranspose_same _

noncomputable def reversePadded (T : Tree Q Unit o n) (h : History o n)
    (z : FiniteAdaptiveKrausRealization.TotalPath T) : MatQ :=
  if z.1 = h then reverseKraus T z.1 z.2 else 0

theorem reversePadded_branch (T : Tree Q Unit o n) (h : History o n) (X : MatQ) :
    (∑ z, reversePadded T h z * X * (reversePadded T h z)ᴴ) = reverseBranch T h X := by
  change (∑ z : Sigma (FiniteAdaptiveKrausRealization.Path T), _) = _
  rw [Fintype.sum_sigma]
  simp [reversePadded, reverseBranch]

theorem reversePadded_complete (T : Tree Q Unit o n) (h : History o n) :
    (∑ z, (reversePadded T h z)ᴴ * reversePadded T h z) =
      ∑ z, (reverseKraus T h z)ᴴ * reverseKraus T h z := by
  change (∑ z : Sigma (FiniteAdaptiveKrausRealization.Path T), _) = _
  rw [Fintype.sum_sigma]
  simp [reversePadded]

/-- Stationarity is the only extra assumption permitting the normalized global reverse. -/
noncomputable def reverseInstrument (T : Tree Q Unit o n) (hT : Stationary T) :
    FiniteInstrument Q (Fintype.card (History o n)) where
  count := Fintype.card (FiniteAdaptiveKrausRealization.TotalPath T)
  operators a z := reversePadded T (FiniteAdaptiveKrausRealization.historyEquiv o n a)
    (FiniteAdaptiveKrausRealization.pathEquiv T z)
  normalized := by
    let eH := FiniteAdaptiveKrausRealization.historyEquiv o n
    let eP := FiniteAdaptiveKrausRealization.pathEquiv T
    have hr : ∀ a, (∑ z, (reversePadded T (eH a) (eP z))ᴴ * reversePadded T (eH a) (eP z)) =
        ∑ z, (reverseKraus T (eH a) z)ᴴ * reverseKraus T (eH a) z := by
      intro a
      rw [eP.sum_comp (fun z => (reversePadded T (eH a) z)ᴴ * reversePadded T (eH a) z),
        reversePadded_complete]
    change (∑ a, ∑ z, (reversePadded T (eH a) (eP z))ᴴ * reversePadded T (eH a) (eP z)) = 1
    simp_rw [hr]
    rw [eH.sum_comp (fun h => ∑ z, (reverseKraus T h z)ᴴ * reverseKraus T h z)]
    exact (reverse_normalized_iff T).mpr hT

theorem reverseInstrument_branch (T : Tree Q Unit o n) (hT : Stationary T)
    (a : Fin (Fintype.card (History o n))) (X : MatQ) :
    (reverseInstrument T hT).branch a X =
      reverseBranch T (FiniteAdaptiveKrausRealization.historyEquiv o n a) X := by
  change (∑ z, reversePadded T (FiniteAdaptiveKrausRealization.historyEquiv o n a)
      (FiniteAdaptiveKrausRealization.pathEquiv T z) * X *
      (reversePadded T (FiniteAdaptiveKrausRealization.historyEquiv o n a)
        (FiniteAdaptiveKrausRealization.pathEquiv T z))ᴴ) = _
  rw [(FiniteAdaptiveKrausRealization.pathEquiv T).sum_comp
    (fun z => reversePadded T (FiniteAdaptiveKrausRealization.historyEquiv o n a) z * X *
      (reversePadded T (FiniteAdaptiveKrausRealization.historyEquiv o n a) z)ᴴ), reversePadded_branch]

def pairedArity (o n : ℕ) : ℕ := 1 + Fintype.card (History o n) + o

def reverseLabel (o n : ℕ) : Fin (Fintype.card (History o n)) ↪ Fin (pairedArity o n) where
  toFun a := ⟨1+a.val, by have := a.isLt; unfold pairedArity; omega⟩
  inj' := by intro a b h; apply Fin.ext; have := congrArg Fin.val h; simp only at this; omega

def originalLabel (o n : ℕ) : Fin o ↪ Fin (pairedArity o n) where
  toFun a := ⟨1+Fintype.card (History o n)+a.val, by have := a.isLt; unfold pairedArity; omega⟩
  inj' := by intro a b h; apply Fin.ext; have := congrArg Fin.val h; simp only at this; omega

def resetLabel (o n : ℕ) : Fin 1 ↪ Fin (pairedArity o n) where
  toFun _ := ⟨0, by unfold pairedArity; omega⟩
  inj' := fun _ _ _ => Subsingleton.elim _ _

noncomputable def resetStep (o n : ℕ) (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) :
    Step Q Unit (pairedArity o n) where
  count := _
  evolution k := GibbsMultilevelReflection.joint (FiniteThreeLevelPositiveHistory.channel q k)
  normalized := GibbsMultilevelReflection.joint_normalized _
    (FiniteThreeLevelPositiveHistory.channel_normalized hq hq1)
  instrument := recodeInstrument FiniteInstrument.identity (resetLabel o n)

theorem recoded_instrument_branch {k m : ℕ} (I : FiniteInstrument Q k) (e : Fin k ↪ Fin m)
    (a : Fin k) (X : MatQ) : (recodeInstrument I e).branch (e a) X = I.branch a X := by
  simp only [FiniteInstrument.branch, krausMap, recodeInstrument,
    FiniteAdaptiveKrausRealization.recodeKraus_image]
  rfl

theorem localStep_joint {k : ℕ} (I : FiniteInstrument Q k) (a : Fin k) (X : MatQ) :
    (localStep Q Unit k I).branch Q Unit k a (joint X) = joint (I.branch a X) := by
  rw [localStep_branch]
  exact GibbsMultilevelReflection.joint_kraus _ _

theorem resetStep_branch (o n : ℕ) (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1) (X : MatQ) :
    (resetStep o n q hq hq1).branch Q Unit _ (resetLabel o n 0) (joint X) = joint (Phi q X) := by
  change ((recodeInstrument FiniteInstrument.identity (resetLabel o n)).lift Unit).branch _
    (krausMap (fun k => GibbsMultilevelReflection.joint (FiniteThreeLevelPositiveHistory.channel q k))
      (GibbsMultilevelReflection.joint X)) = _
  rw [GibbsMultilevelReflection.joint_kraus, FiniteThreeLevelPositiveHistory.channel_state hq hq1]
  change krausMap (fun k => GibbsMultilevelReflection.joint
    ((recodeInstrument FiniteInstrument.identity (resetLabel o n)).operators (resetLabel o n 0) k))
      (GibbsMultilevelReflection.joint (Phi q X)) = _
  rw [GibbsMultilevelReflection.joint_kraus]
  change joint ((recodeInstrument FiniteInstrument.identity (resetLabel o n)).branch _ (Phi q X)) = _
  rw [recoded_instrument_branch, FiniteInstrument.identity_branch]

theorem resetStep_invalid (o n : ℕ) (q : ℝ) (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (b : Fin (pairedArity o n)) (hb : b ≠ resetLabel o n 0)
    (X : Matrix (Q × Unit) (Q × Unit) ℂ) :
    (resetStep o n q hq hq1).branch Q Unit _ b X = 0 := by
  have hn : b ∉ Set.range (resetLabel o n) := by
    rintro ⟨a,rfl⟩
    exact hb (congrArg (resetLabel o n) (Subsingleton.elim a 0))
  simp [Step.branch, resetStep, FiniteInstrument.lift, FiniteInstrument.branch, krausMap,
    recodeInstrument, FiniteAdaptiveKrausRealization.recodeKraus_invalid _ _ b hn]

/-- The actual uniform-arity chronology: global reverse, central reset, original feedback tree. -/
noncomputable def pairedTree (T : Tree Q Unit o n) (ho : 0 < o) (hT : Stationary T)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) : Tree Q Unit (pairedArity o n) (n+2) :=
  .node (recodeStep (localStep Q Unit _ (reverseInstrument T hT)) (reverseLabel o n)) (fun _ =>
    .node (resetStep o n (p*p) (mul_nonneg hp hp) (by nlinarith)) (fun _ =>
      recodeTree (originalLabel o n) ⟨0,ho⟩ T))

noncomputable def pairedHistory (u v : History o n) : History (pairedArity o n) (n+2) :=
  (reverseLabel o n ((historyEquiv o n).symm u), resetLabel o n 0,
    recodeHistory (originalLabel o n) v)

theorem pairedHistory_injective : Function.Injective
    (fun uv : History o n × History o n => pairedHistory uv.1 uv.2) := by
  intro ⟨u,v⟩ ⟨u',v'⟩ he
  have h := Prod.mk.inj he
  apply Prod.ext
  · exact (historyEquiv o n).symm.injective ((reverseLabel o n).injective h.1)
  · exact FiniteAdaptiveKrausRealization.recodeHistory_injective (originalLabel o n) n
      (Prod.mk.inj h.2).2

theorem paired_run (T : Tree Q Unit o n) (ho : 0 < o) (hT : Stationary T)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (u v : History o n) (X : MatQ) :
    unJoint (run Q Unit _ (pairedTree T ho hT p hp hp1) (pairedHistory u v) (joint X)) =
      branch T v (Phi (p*p) (reverseBranch T u X)) := by
  simp only [pairedTree, pairedHistory, run, FiniteAdaptiveKrausRealization.recodeStep_branch,
    localStep_joint, reverseInstrument_branch, Equiv.apply_symm_apply, resetStep_branch]
  rw [FiniteAdaptiveKrausRealization.recode_run]
  rfl

theorem paired_invalid_zero (T : Tree Q Unit o n) (ho : 0 < o) (hT : Stationary T)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (h : History (pairedArity o n) (n+2))
    (hh : h ∉ Set.range (fun uv : History o n × History o n => pairedHistory uv.1 uv.2))
    (X : Matrix (Q × Unit) (Q × Unit) ℂ) :
    run Q Unit _ (pairedTree T ho hT p hp hp1) h X = 0 := by
  rcases h with ⟨a,b,v⟩
  by_cases ha : a ∈ Set.range (reverseLabel o n)
  · obtain ⟨a,rfl⟩ := ha
    by_cases hb : b = resetLabel o n 0
    · subst b
      have hv : v ∉ Set.range (@recodeHistory o (pairedArity o n) (originalLabel o n) n) := by
        rintro ⟨v',rfl⟩
        apply hh
        refine ⟨(historyEquiv o n a,v'), ?_⟩
        simp only [pairedHistory, Equiv.symm_apply_apply]
      simp only [pairedTree, run]
      exact FiniteAdaptiveKrausRealization.recode_invalid_zero _ _ _ _ hv _
    · simp only [pairedTree, run]
      rw [resetStep_invalid o n _ _ _ b hb, run_zero]
  · simp only [pairedTree, run]
    rw [FiniteAdaptiveKrausRealization.recodeStep_invalid _ _ a ha, Step.branch_zero, run_zero]

/-- The encoded leaves exhaust the actual process; invalid labels contribute zero. -/
theorem paired_encoded_sum (T : Tree Q Unit o n) (ho : 0 < o) (hT : Stationary T)
    (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (X : Matrix (Q × Unit) (Q × Unit) ℂ) :
    (∑ uv : History o n × History o n,
      run Q Unit _ (pairedTree T ho hT p hp hp1) (pairedHistory uv.1 uv.2) X) =
    ∑ h, run Q Unit _ (pairedTree T ho hT p hp hp1) h X := by
  exact Fintype.sum_of_injective _ pairedHistory_injective _ _
    (fun h hh => paired_invalid_zero T ho hT p hp hp1 h hh X) (fun _ => rfl)

/-- Consistency with the existing arity-fifteen complex event evaluator. -/
theorem effect_event_complex_trace {n : ℕ} (T : Tree Q Unit 15 n)
    (h : History 15 n) (X : MatQ) :
    (joint (effect T h) * joint X).trace =
      ∑ g, ((if g = h then 1 else 0 : ℝ) : ℂ) *
        (run Q Unit 15 T g (joint X)).trace := by
  rw [effect_path, FiniteAdaptiveKrausRealization.system_leafEffect_event]
  exact FiniteThreeLevelHistoryTransfer.qutrit_effect_complex_trace T _ _

section Kernel
variable (T : Tree Q Unit o n) (ho : 0 < o) (hT : Stationary T)
variable (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)

/-- The kernel is defined by the actual normalized chronological process weight. -/
noncomputable def kernel (u v : History o n) : ℂ :=
  (weight Q Unit _ (pairedTree T ho hT p hp hp1) (pairedHistory u v) (joint rhoN) : ℂ)

theorem actual_complex_trace (u v : History o n) :
    (run Q Unit _ (pairedTree T ho hT p hp hp1) (pairedHistory u v) (joint rhoN)).trace =
      (effect T v * Phi (p*p) (Gamma (effect T u))).trace := by
  rw [← FiniteAdaptiveKrausRealization.unJoint_trace, paired_run, reverseBranch_rho, branch_trace]

theorem kernel_complex_trace (u v : History o n) :
    kernel T ho hT p hp hp1 u v = (effect T v * Phi (p*p) (Gamma (effect T u))).trace := by
  unfold kernel weight
  rw [actual_complex_trace]
  apply FiniteThreeLevelPositiveHistory.hermitian_product_real _ _ (effect_adjoint T v)
  rw [FiniteThreeLevelPositiveHistory.Phi_Gamma, FiniteThreeLevelPositiveHistory.Gamma_adjoint,
    FiniteThreeLevelPositiveHistory.Psi_adjoint, effect_adjoint]

theorem kernel_form (u v : History o n) :
    kernel T ho hT p hp hp1 u v = form (Psi p (effect T u)) (Psi p (effect T v)) := by
  rw [kernel_complex_trace, FiniteThreeLevelPositiveHistory.central_split]
  simp only [form, FiniteThreeLevelPositiveHistory.Psi_adjoint, effect_adjoint,
    Gamma, Matrix.mul_assoc]

noncomputable def synthesis (f : History o n → ℂ) : MatQ := ∑ h, f h • Psi p (effect T h)

noncomputable def synthesisLinear : (History o n → ℂ) →ₗ[ℂ] MatQ where
  toFun := synthesis T p
  map_add' f g := by simp [synthesis, Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c f := by simp [synthesis, Pi.smul_apply, Finset.smul_sum, smul_smul]

theorem synthesis_single (h : History o n) : synthesis T p (Pi.single h 1) = Psi p (effect T h) := by
  classical
  simp [synthesis, Pi.single_apply]

theorem feature_synthesis (f : History o n → ℂ) :
    FiniteThreeLevelPositiveHistory.feature (synthesis T p f) =
      ∑ h, f h • FiniteThreeLevelPositiveHistory.feature (Psi p (effect T h)) := by
  simp only [FiniteThreeLevelPositiveHistory.feature, synthesis,
    Matrix.mul_sum, Matrix.sum_mul, mul_smul_comm, smul_mul_assoc]

local instance : NormedAddCommGroup MatQ := Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one
local instance : InnerProductSpace ℂ MatQ := Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

theorem kernel_gram : kernel T ho hT p hp hp1 =
    Matrix.gram ℂ (fun h => FiniteThreeLevelPositiveHistory.feature (Psi p (effect T h))) := by
  ext u v
  rw [kernel_form, ← FiniteThreeLevelPositiveHistory.feature_gram]
  change (FiniteThreeLevelPositiveHistory.feature (Psi p (effect T v)) *
    (FiniteThreeLevelPositiveHistory.feature (Psi p (effect T u)))ᴴ).trace =
    (FiniteThreeLevelPositiveHistory.feature (Psi p (effect T v)) * 1 *
    (FiniteThreeLevelPositiveHistory.feature (Psi p (effect T u)))ᴴ).trace
  simp

theorem kernel_posSemidef : Matrix.PosSemidef (kernel T ho hT p hp hp1) := by
  rw [kernel_gram]
  exact Matrix.posSemidef_gram ℂ _

theorem pairing_synthesis (f g : History o n → ℂ) :
    FinitePositiveKernel.pairing (kernel T ho hT p hp hp1) f g =
      form (synthesis T p f) (synthesis T p g) := by
  rw [kernel_gram]
  unfold FinitePositiveKernel.pairing
  rw [Matrix.star_dotProduct_gram_mulVec, ← feature_synthesis, ← feature_synthesis]
  change (FiniteThreeLevelPositiveHistory.feature (synthesis T p g) * 1 *
    (FiniteThreeLevelPositiveHistory.feature (synthesis T p f))ᴴ).trace = _
  simpa using FiniteThreeLevelPositiveHistory.feature_gram (synthesis T p f) (synthesis T p g)

/-- The exact accessible observables, equipped below with the sandwiched metric. -/
noncomputable def accessible : Submodule ℂ MatQ :=
  Submodule.span ℂ (Set.range (fun h => Psi p (effect T h)))

theorem synthesis_range : (synthesisLinear T p).range = accessible T p := by
  apply le_antisymm
  · rintro A ⟨f,rfl⟩
    change (∑ h, f h • Psi p (effect T h)) ∈ accessible T p
    exact Submodule.sum_mem _ (fun h _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨h,rfl⟩))
  · apply Submodule.span_le.mpr
    rintro A ⟨h,rfl⟩
    exact ⟨Pi.single h 1, synthesis_single T p h⟩

open FinitePositiveKernel
open scoped InnerProductSpace
local notation "K" => kernel T ho hT p hp hp1
local notation "hK" => kernel_posSemidef T ho hT p hp hp1

abbrev Reconstructed := Space K hK

theorem null_iff (f : History o n → ℂ) : mk K hK f = 0 ↔ synthesis T p f = 0 := by
  rw [mk_eq_zero_iff, pairing_synthesis, FiniteThreeLevelPositiveHistory.form_self_zero_iff]

noncomputable def coefficientSynthesis : Coefficients hK →ₗ[ℂ] MatQ := synthesisLinear T p

theorem synthesis_null : nullSpace K hK ≤ (coefficientSynthesis T ho hT p hp hp1).ker := by
  intro f hf
  change synthesis T p f = 0
  apply (null_iff T ho hT p hp hp1 f).mp
  rw [mk_eq_zero_iff]
  exact (mem_nullSpace_iff _ _ f).mp hf

noncomputable def coordinates : Reconstructed T ho hT p hp hp1 →ₗ[ℂ] MatQ :=
  ((nullSpace K hK).liftQ (coefficientSynthesis T ho hT p hp hp1)
    (synthesis_null T ho hT p hp hp1)).comp (quotientEquiv K hK).symm.toLinearMap

theorem coordinates_mk (f : History o n → ℂ) :
    coordinates T ho hT p hp hp1 (mk K hK f) = synthesis T p f := by
  rw [← quotientEquiv_mk hK f]
  simp only [coordinates, LinearMap.comp_apply, LinearEquiv.coe_coe,
    LinearEquiv.symm_apply_apply, Submodule.liftQ_apply]
  rfl

theorem coordinates_injective : Function.Injective (coordinates T ho hT p hp hp1) := by
  intro z w hz
  obtain ⟨f,rfl⟩ := mk_surjective K hK z
  obtain ⟨g,rfl⟩ := mk_surjective K hK w
  rw [coordinates_mk, coordinates_mk] at hz
  apply (mk_eq_mk_iff K hK f g).mpr
  rw [pairing_synthesis]
  have he : synthesis T p (f-g) = 0 :=
    (synthesisLinear T p).map_sub f g |>.trans (sub_eq_zero.mpr hz)
  simp [he, form]

theorem coordinates_range : (coordinates T ho hT p hp hp1).range = accessible T p := by
  rw [← synthesis_range]
  ext A
  constructor
  · rintro ⟨z,rfl⟩
    obtain ⟨f,rfl⟩ := mk_surjective K hK z
    exact ⟨f, (coordinates_mk T ho hT p hp hp1 f).symm⟩
  · rintro ⟨f,rfl⟩
    exact ⟨mk K hK f, coordinates_mk T ho hT p hp hp1 f⟩

theorem coordinates_inner (z w : Reconstructed T ho hT p hp hp1) :
    ⟪z,w⟫_ℂ = form (coordinates T ho hT p hp hp1 z) (coordinates T ho hT p hp hp1 w) := by
  obtain ⟨f,rfl⟩ := mk_surjective K hK z
  obtain ⟨g,rfl⟩ := mk_surjective K hK w
  rw [inner_mk, coordinates_mk, coordinates_mk, pairing_synthesis]

/-- Only the Q4 feature is isometric into the ordinary Hilbert-Schmidt matrix space. -/
noncomputable def embedding : Reconstructed T ho hT p hp hp1 →ₗᵢ[ℂ] MatQ :=
  (FiniteThreeLevelPositiveHistory.featureLinear.comp (coordinates T ho hT p hp hp1)).isometryOfInner (by
    intro z w
    rw [coordinates_inner T ho hT p hp hp1]
    change (FiniteThreeLevelPositiveHistory.feature (coordinates T ho hT p hp hp1 w) * 1 *
      (FiniteThreeLevelPositiveHistory.feature (coordinates T ho hT p hp hp1 z))ᴴ).trace = _
    simpa using FiniteThreeLevelPositiveHistory.feature_gram
      (coordinates T ho hT p hp hp1 z) (coordinates T ho hT p hp hp1 w))

theorem embedding_range : (embedding T ho hT p hp hp1).range =
    (accessible T p).map FiniteThreeLevelPositiveHistory.featureLinear := by
  change (FiniteThreeLevelPositiveHistory.featureLinear.comp (coordinates T ho hT p hp hp1)).range = _
  rw [LinearMap.range_comp, coordinates_range]

noncomputable def rangeEquiv : Reconstructed T ho hT p hp hp1 ≃ₗᵢ[ℂ]
    (embedding T ho hT p hp hp1).range := (embedding T ho hT p hp hp1).equivRange

theorem synthesis_constant : synthesis T p (fun _ => 1) = 1 := by
  simp only [synthesis, one_smul]
  rw [← FiniteThreeLevelPositiveHistory.Psi_sum, effect_sum,
    FiniteThreeLevelPositiveHistory.Psi_unital]

theorem one_mem_accessible : (1 : MatQ) ∈ accessible T p := by
  rw [← synthesis_range]
  exact ⟨fun _ => 1, synthesis_constant T p⟩

def effectSpan : Submodule ℂ MatQ := Submodule.span ℂ (Set.range (effect T))

theorem accessible_one : accessible T 1 = effectSpan T := by
  simp only [accessible, FiniteThreeLevelPositiveHistory.Psi_one, effectSpan]

theorem inversePsi_Psi (hpos : 0 < p) (A : MatQ) :
    FiniteThreeLevelPositiveHistory.inversePsi p (Psi p A) = A := by
  have hi : Function.Injective (FiniteThreeLevelPositiveHistory.PsiLinear p) :=
    (LinearMap.injective_iff_surjective (f := FiniteThreeLevelPositiveHistory.PsiLinear p)).mpr
      (fun B => ⟨FiniteThreeLevelPositiveHistory.inversePsi p B,
        FiniteThreeLevelPositiveHistory.Psi_inverse hpos B⟩)
  apply hi
  exact FiniteThreeLevelPositiveHistory.Psi_inverse hpos (Psi p A)

theorem range_positive_eq_effect_span (hpos : 0 < p) : accessible T p = effectSpan T := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro A ⟨h,rfl⟩
    have hI : (1 : MatQ) ∈ effectSpan T := by
      rw [← accessible_one]
      exact one_mem_accessible T 1
    exact Submodule.add_mem _
      (Submodule.smul_mem _ _ (Submodule.subset_span ⟨h,rfl⟩))
      (Submodule.smul_mem _ _ (Submodule.smul_mem _ _ hI))
  · apply Submodule.span_le.mpr
    rintro A ⟨h,rfl⟩
    rw [← inversePsi_Psi p hpos (effect T h)]
    have hM : Psi p (effect T h) ∈ accessible T p := Submodule.subset_span ⟨h,rfl⟩
    have hI := one_mem_accessible T p
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ hI)
      (Submodule.smul_mem _ _ (Submodule.sub_mem _ hM (Submodule.smul_mem _ _ hI)))

theorem full_range_iff (hpos : 0 < p) :
    (coordinates T ho hT p hp hp1).range = ⊤ ↔ effectSpan T = ⊤ := by
  rw [coordinates_range, range_positive_eq_effect_span T p hpos]

theorem reconstructed_finrank : Module.finrank ℂ (Reconstructed T ho hT p hp hp1) =
    Module.finrank ℂ (accessible T p) := by
  rw [← coordinates_range T ho hT p hp hp1]
  exact (LinearMap.finrank_range_of_inj (coordinates_injective T ho hT p hp hp1)).symm

theorem reconstructed_finrank_le : Module.finrank ℂ (Reconstructed T ho hT p hp hp1) ≤ 9 := by
  rw [reconstructed_finrank]
  exact (Submodule.finrank_le (accessible T p)).trans_eq (by
    simpa using Module.finrank_matrix ℂ ℂ Q Q)

theorem full_finrank_iff (hpos : 0 < p) :
    Module.finrank ℂ (Reconstructed T ho hT p hp hp1) = 9 ↔ effectSpan T = ⊤ := by
  rw [reconstructed_finrank, range_positive_eq_effect_span T p hpos]
  constructor
  · intro h
    apply Submodule.eq_top_of_finrank_eq
    rw [h]
    symm
    simpa using Module.finrank_matrix ℂ ℂ Q Q
  · intro h
    rw [h, finrank_top]
    simpa using Module.finrank_matrix ℂ ℂ Q Q

theorem reset_range : accessible T 0 = Submodule.span ℂ {(1 : MatQ)} := by
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro A ⟨h,rfl⟩
    change Psi 0 (effect T h) ∈ Submodule.span ℂ {(1 : MatQ)}
    rw [FiniteThreeLevelPositiveHistory.Psi_zero]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton _))
  · apply Submodule.span_le.mpr
    intro A hA
    rw [Set.mem_singleton_iff] at hA
    subst A
    exact one_mem_accessible T 0

theorem reset_finrank : Module.finrank ℂ
    (Reconstructed T ho hT 0 (by norm_num) (by norm_num)) = 1 := by
  rw [reconstructed_finrank, reset_range]
  exact finrank_span_singleton (one_ne_zero : (1 : MatQ) ≠ 0)

def mass (h : History o n) : ℝ := (rhoN * effect T h).trace.re

theorem mass_complex (h : History o n) : (mass T h : ℂ) = (rhoN * effect T h).trace :=
  FiniteThreeLevelPositiveHistory.hermitian_product_real _ _
    FiniteThreeLevelPositiveHistory.rhoN_adjoint (effect_adjoint T h)

theorem mass_sum : ∑ h, mass T h = 1 := by
  have he : (∑ h, (rhoN * effect T h).trace) = 1 := by
    rw [← Matrix.trace_sum, ← Matrix.mul_sum, effect_sum, Matrix.mul_one,
      FiniteThreeLevelPositiveHistory.rhoN_trace]
  simpa only [mass, Complex.re_sum, Complex.one_re] using congrArg Complex.re he

theorem kernel_nonnegative (u v : History o n) : 0 ≤ kernel T ho hT p hp hp1 u v := by
  change (0 : ℂ) ≤ ((weight Q Unit _ (pairedTree T ho hT p hp hp1)
    (pairedHistory u v) (joint rhoN) : ℝ) : ℂ)
  exact_mod_cast weight_nonneg Q Unit _ (pairedTree T ho hT p hp hp1)
    (pairedHistory u v) (FiniteThreeLevelPositiveHistory.rhoN_density.1.kronecker
      (Matrix.PosSemidef.one : (1 : Matrix Unit Unit ℂ).PosSemidef))

theorem kernel_real (u v : History o n) : (kernel T ho hT p hp hp1 u v).im = 0 :=
  Complex.ofReal_im _

theorem kernel_encoded_full_trace :
    (∑ u, ∑ v, kernel T ho hT p hp hp1 u v) =
      ∑ h, (run Q Unit _ (pairedTree T ho hT p hp hp1) h (joint rhoN)).trace := by
  simp_rw [kernel_complex_trace, ← actual_complex_trace T ho hT p hp hp1]
  have he := congrArg Matrix.trace (paired_encoded_sum T ho hT p hp hp1 (joint rhoN))
  simpa only [Matrix.trace_sum, Fintype.sum_prod_type] using he

theorem kernel_normalized : ∑ u, ∑ v, kernel T ho hT p hp hp1 u v = 1 := by
  rw [kernel_encoded_full_trace, sum_trace, FiniteAdaptiveKrausRealization.joint_trace,
    FiniteThreeLevelPositiveHistory.rhoN_trace]

theorem kernel_row_sum (u : History o n) :
    (∑ v, kernel T ho hT p hp hp1 u v) = (mass T u : ℂ) := by
  simp_rw [kernel_complex_trace]
  rw [← Matrix.trace_sum, ← Matrix.sum_mul, effect_sum, Matrix.one_mul,
    FiniteThreeLevelPositiveHistory.Phi_Gamma, FiniteThreeLevelPositiveHistory.Gamma_trace,
    FiniteThreeLevelPositiveHistory.Psi_mean, mass_complex]

theorem kernel_column_sum (v : History o n) :
    (∑ u, kernel T ho hT p hp hp1 u v) = (mass T v : ℂ) := by
  simp_rw [kernel_complex_trace]
  rw [← Matrix.trace_sum, ← Matrix.mul_sum, ← FiniteThreeLevelPositiveHistory.Phi_sum,
    ← FiniteThreeLevelPositiveHistory.Gamma_sum, effect_sum,
    FiniteThreeLevelPositiveHistory.Gamma_one]
  have hs : Phi (p*p) rhoN = rhoN := by
    simp [Phi, FiniteThreeLevelPositiveHistory.rhoN_trace, ← add_smul]
  rw [hs, Matrix.trace_mul_comm, mass_complex]

theorem reset_synthesis (f : History o n → ℂ) :
    synthesis T 0 f = (∑ h, f h * (mass T h : ℂ)) • (1 : MatQ) := by
  simp only [synthesis, FiniteThreeLevelPositiveHistory.Psi_zero,
    ← mass_complex, smul_smul, Finset.sum_smul]

theorem reset_kernel (u v : History o n) :
    kernel T ho hT 0 (by norm_num) (by norm_num) u v = (mass T u : ℂ) * (mass T v : ℂ) := by
  rw [kernel_complex_trace]
  simp only [zero_mul, FiniteThreeLevelPositiveHistory.Phi_zero, mul_smul_comm,
    Matrix.trace_smul, FiniteThreeLevelPositiveHistory.Gamma_trace, smul_eq_mul]
  rw [Matrix.trace_mul_comm (effect T v) rhoN, mass_complex, mass_complex]

/-- On the physical retention interval, full matrix reconstruction needs both conditions. -/
theorem full_finrank_physical_iff :
    Module.finrank ℂ (Reconstructed T ho hT p hp hp1) = 9 ↔
      0 < p ∧ effectSpan T = ⊤ := by
  constructor
  · intro hr
    have hpos : 0 < p := by
      by_contra hn
      have hz : p = 0 := le_antisymm (le_of_not_gt hn) hp
      subst p
      have hc := reset_finrank T ho hT
      omega
    exact ⟨hpos, (full_finrank_iff T ho hT p hp hp1 hpos).mp hr⟩
  · rintro ⟨hpos,hs⟩
    exact (full_finrank_iff T ho hT p hp hp1 hpos).mpr hs

def fullCoordinateEquiv (hpos : 0 < p) (hspan : effectSpan T = ⊤) :
    Reconstructed T ho hT p hp hp1 ≃ₗ[ℂ] MatQ :=
  LinearEquiv.ofBijective (coordinates T ho hT p hp hp1)
    ⟨coordinates_injective T ho hT p hp hp1,
      LinearMap.range_eq_top.mp ((full_range_iff T ho hT p hp hp1 hpos).mpr hspan)⟩

/-- Full trace readout is transported only after the actual effect span is proved full. -/
theorem full_trace_evaluation (hpos : 0 < p) (hspan : effectSpan T = ⊤) (X A : MatQ) :
    ⟪(fullCoordinateEquiv T ho hT p hp hp1 hpos hspan).symm
        (FiniteThreeLevelHistoryReadout.dualState X),
      (fullCoordinateEquiv T ho hT p hp hp1 hpos hspan).symm A⟫_ℂ = (A * X).trace := by
  rw [coordinates_inner]
  change form ((fullCoordinateEquiv T ho hT p hp hp1 hpos hspan)
    ((fullCoordinateEquiv T ho hT p hp hp1 hpos hspan).symm
      (FiniteThreeLevelHistoryReadout.dualState X)))
    ((fullCoordinateEquiv T ho hT p hp hp1 hpos hspan)
      ((fullCoordinateEquiv T ho hT p hp hp1 hpos hspan).symm A)) = _
  rw [LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply,
    FiniteThreeLevelHistoryReadout.dualState_form]

end Kernel


/-- Outcome padding preserves each valid leaf effect exactly. -/
theorem recoded_effect {m : ℕ} (T : Tree Q Unit o n) (e : Fin o ↪ Fin m)
    (a₀ : Fin o) (h : History o n) :
    effect (recodeTree e a₀ T) (recodeHistory e h) = effect T h := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  rw [← branch_trace, ← branch_trace]
  unfold branch
  rw [FiniteAdaptiveKrausRealization.recode_run]

theorem recoded_invalid_effect {m : ℕ} (T : Tree Q Unit o n) (e : Fin o ↪ Fin m)
    (a₀ : Fin o) (h : History m n) (hh : h ∉ Set.range (@recodeHistory o m e n)) :
    effect (recodeTree e a₀ T) h = 0 := by
  apply Matrix.ext_iff_trace_mul_right.mpr
  intro X
  rw [← branch_trace]
  unfold branch
  rw [FiniteAdaptiveKrausRealization.recode_invalid_zero e a₀ T h hh]
  have hz : unJoint (0 : Matrix (Q × Unit) (Q × Unit) ℂ) = 0 := rfl
  rw [hz]
  simp

/-- Arbitrarily many padded zero leaves add no accessible observable directions. -/
theorem recoded_accessible {m : ℕ} (T : Tree Q Unit o n) (e : Fin o ↪ Fin m)
    (a₀ : Fin o) (p : ℝ) :
    accessible (recodeTree e a₀ T) p = accessible T p := by
  classical
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro A ⟨h,rfl⟩
    change Psi p (effect (recodeTree e a₀ T) h) ∈ accessible T p
    by_cases hh : h ∈ Set.range (@recodeHistory o m e n)
    · obtain ⟨g,rfl⟩ := hh
      rw [recoded_effect]
      exact Submodule.subset_span ⟨g,rfl⟩
    · rw [recoded_invalid_effect T e a₀ h hh]
      simp [Psi]
  · apply Submodule.span_le.mpr
    rintro A ⟨h,rfl⟩
    change Psi p (effect T h) ∈ accessible (recodeTree e a₀ T) p
    rw [← recoded_effect T e a₀ h]
    exact Submodule.subset_span ⟨recodeHistory e h,rfl⟩

end SKEFTHawking.QuantumNetwork.FiniteThreeLevelStationaryStrategyReflection

#check Nat
