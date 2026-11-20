import SKEFTHawking.QuantumNetwork.FiniteThreeLevelStationaryStrategyReflection
import Mathlib.Algebra.Module.Projective

/-!
# Exact observable transfer on stationary strategy ranges

Exact coefficient lifts are characterized by invariance of the actual synthesis
range. Their action on the existing null quotient is independent of the lift.
Physical insertion and positivity are separate obligations.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteThreeLevelStationaryStrategyTransfer
open Matrix FiniteInterventionProcess FiniteThreeLevelStationaryStrategyReflection
open FiniteThreeLevelPositiveHistory (Q MatQ Psi Phi Gamma rhoN form)
open FinitePositiveKernel
open scoped BigOperators ComplexOrder InnerProductSpace

variable {o n : ℕ} (T : Tree Q Unit o n) (p : ℝ)

/-- Invariance refers to the actual accessible observable range. -/
def Invariant (O : MatQ →ₗ[ℂ] MatQ) : Prop :=
  ∀ A ∈ accessible T p, O A ∈ accessible T p

/-- Column-oriented exact intertwining, with no positivity assumption. -/
def ExactLift (O : MatQ →ₗ[ℂ] MatQ)
    (C : (History o n → ℂ) →ₗ[ℂ] (History o n → ℂ)) : Prop :=
  (synthesisLinear T p).comp C = O.comp (synthesisLinear T p)

theorem exactLift_apply {O : MatQ →ₗ[ℂ] MatQ}
    {C : (History o n → ℂ) →ₗ[ℂ] (History o n → ℂ)}
    (hC : ExactLift T p O C) (f : History o n → ℂ) :
    synthesis T p (C f) = O (synthesis T p f) :=
  LinearMap.congr_fun hC f

/-- A linear section of the range restriction supplies the lift; conversely an
exact lift makes every accessible observable's image accessible. -/
theorem invariant_iff_exists_exactLift (O : MatQ →ₗ[ℂ] MatQ) :
    Invariant T p O ↔ ∃ C, ExactLift T p O C := by
  constructor
  · intro hO
    let S := synthesisLinear T p
    obtain ⟨σ, hσ⟩ := S.rangeRestrict.exists_rightInverse_of_surjective
      S.range_rangeRestrict
    let R : (History o n → ℂ) →ₗ[ℂ] S.range :=
      (O.comp S).codRestrict S.range (by
        intro f
        rw [synthesis_range]
        exact hO (S f) (by rw [← synthesis_range]; exact ⟨f, rfl⟩))
    refine ⟨σ.comp R, ?_⟩
    apply LinearMap.ext
    intro f
    have he := congrArg Subtype.val (LinearMap.congr_fun hσ (R f))
    exact he
  · rintro ⟨C, hC⟩ A hA
    rw [← synthesis_range] at hA ⊢
    obtain ⟨f, rfl⟩ := hA
    exact ⟨C f, exactLift_apply T p hC f⟩

def chosenLift (O : MatQ →ₗ[ℂ] MatQ) (hO : Invariant T p O) :
    (History o n → ℂ) →ₗ[ℂ] (History o n → ℂ) :=
  Classical.choose ((invariant_iff_exists_exactLift T p O).mp hO)

theorem chosenLift_exact (O : MatQ →ₗ[ℂ] MatQ) (hO : Invariant T p O) :
    ExactLift T p O (chosenLift T p O hO) :=
  Classical.choose_spec ((invariant_iff_exists_exactLift T p O).mp hO)

theorem invariant_id : Invariant T p LinearMap.id := fun _ hA => hA

theorem invariant_comp {O P : MatQ →ₗ[ℂ] MatQ}
    (hO : Invariant T p O) (hP : Invariant T p P) :
    Invariant T p (O.comp P) := fun A hA => hO (P A) (hP A hA)

variable (ho : 0 < o) (hT : Stationary T) (hp : 0 ≤ p) (hp1 : p ≤ 1)
/-- Matrix-typed view of the existing chronological kernel. -/
def kernelMatrix : Matrix (History o n) (History o n) ℂ := kernel T ho hT p hp hp1
local notation "K" => kernel T ho hT p hp hp1
local notation "hK" => kernel_posSemidef T ho hT p hp hp1

theorem exactLift_nullPreserving {O : MatQ →ₗ[ℂ] MatQ}
    {C : (History o n → ℂ) →ₗ[ℂ] (History o n → ℂ)}
    (hC : ExactLift T p O C) : NullPreserving hK C := by
  intro f hf
  apply (mem_nullSpace_iff K hK _).mpr
  apply (mk_eq_zero_iff K hK _).mp
  apply (null_iff T ho hT p hp hp1 _).mpr
  have hf0 := (mk_eq_zero_iff K hK f).mpr ((mem_nullSpace_iff K hK f).mp hf)
  exact (exactLift_apply T p hC f).trans
    ((congrArg O ((null_iff T ho hT p hp hp1 f).mp hf0)).trans O.map_zero)

def transferOfLift {O : MatQ →ₗ[ℂ] MatQ}
    {C : (History o n → ℂ) →ₗ[ℂ] (History o n → ℂ)}
    (hC : ExactLift T p O C) :
    Reconstructed T ho hT p hp hp1 →ₗ[ℂ] Reconstructed T ho hT p hp hp1 :=
  descend hK C (exactLift_nullPreserving T p ho hT hp hp1 hC)

theorem coordinates_transferOfLift {O : MatQ →ₗ[ℂ] MatQ}
    {C : (History o n → ℂ) →ₗ[ℂ] (History o n → ℂ)}
    (hC : ExactLift T p O C) (z : Reconstructed T ho hT p hp hp1) :
    coordinates T ho hT p hp hp1 (transferOfLift T p ho hT hp hp1 hC z) =
      O (coordinates T ho hT p hp hp1 z) := by
  obtain ⟨f, rfl⟩ := mk_surjective K hK z
  rw [transferOfLift, descend_mk, coordinates_mk, coordinates_mk]
  exact exactLift_apply T p hC f

theorem transferOfLift_independent {O : MatQ →ₗ[ℂ] MatQ}
    {C D : (History o n → ℂ) →ₗ[ℂ] (History o n → ℂ)}
    (hC : ExactLift T p O C) (hD : ExactLift T p O D) :
    transferOfLift T p ho hT hp hp1 hC = transferOfLift T p ho hT hp hp1 hD := by
  ext z
  apply coordinates_injective T ho hT p hp hp1
  rw [coordinates_transferOfLift, coordinates_transferOfLift]

def transfer (O : MatQ →ₗ[ℂ] MatQ) (hO : Invariant T p O) :
    Reconstructed T ho hT p hp hp1 →ₗ[ℂ] Reconstructed T ho hT p hp hp1 :=
  transferOfLift T p ho hT hp hp1 (chosenLift_exact T p O hO)

theorem coordinates_transfer (O : MatQ →ₗ[ℂ] MatQ) (hO : Invariant T p O)
    (z : Reconstructed T ho hT p hp hp1) :
    coordinates T ho hT p hp hp1 (transfer T p ho hT hp hp1 O hO z) =
      O (coordinates T ho hT p hp hp1 z) :=
  coordinates_transferOfLift T p ho hT hp hp1 _ z

theorem transfer_id : transfer T p ho hT hp hp1 LinearMap.id (invariant_id T p) =
    LinearMap.id := by
  ext z
  apply coordinates_injective T ho hT p hp hp1
  rw [coordinates_transfer]
  rfl

theorem transfer_comp {O P : MatQ →ₗ[ℂ] MatQ}
    (hO : Invariant T p O) (hP : Invariant T p P) :
    transfer T p ho hT hp hp1 (O.comp P) (invariant_comp T p hO hP) =
      (transfer T p ho hT hp hp1 O hO).comp (transfer T p ho hT hp hp1 P hP) := by
  ext z
  apply coordinates_injective T ho hT p hp hp1
  simp only [LinearMap.comp_apply, coordinates_transfer]

/-- An exact coordinate action necessarily preserves the actual accessible range. -/
theorem invariant_of_coordinates {O : MatQ →ₗ[ℂ] MatQ}
    (F : Reconstructed T ho hT p hp hp1 →ₗ[ℂ] Reconstructed T ho hT p hp hp1)
    (hF : ∀ z, coordinates T ho hT p hp hp1 (F z) = O (coordinates T ho hT p hp hp1 z)) :
    Invariant T p O := by
  intro A hA
  rw [← coordinates_range T ho hT p hp hp1] at hA ⊢
  obtain ⟨z,rfl⟩ := hA
  exact ⟨F z, hF z⟩

/-- Scalar central reset preserves every unital complex-linear evolution. -/
theorem reset_range_invariant (O : MatQ →ₗ[ℂ] MatQ) (hO : O 1 = 1) :
    Invariant T 0 O := by
  intro A hA
  rw [reset_range] at hA ⊢
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hA
  rw [map_smul, hO]
  exact Submodule.smul_mem _ c (Submodule.subset_span (Set.mem_singleton _))

section Weighted
local notation "KM" => kernelMatrix T p ho hT hp hp1

theorem pairing_exactLift {O : MatQ →ₗ[ℂ] MatQ}
    {C : Matrix (History o n) (History o n) ℂ}
    (hC : ExactLift T p O C.mulVecLin) (f g : History o n → ℂ) :
    pairing (KM * C) f g = form (synthesis T p f) (O (synthesis T p g)) := by
  have he := exactLift_apply T p hC g
  change synthesis T p (C *ᵥ g) = O (synthesis T p g) at he
  rw [← he, ← pairing_synthesis T ho hT p hp hp1]
  change star f ⬝ᵥ (KM * C) *ᵥ g = star f ⬝ᵥ KM *ᵥ (C *ᵥ g)
  rw [Matrix.mulVec_mulVec]

theorem weighted_adjoint {O P : MatQ →ₗ[ℂ] MatQ}
    {C D : Matrix (History o n) (History o n) ℂ}
    (hC : ExactLift T p O C.mulVecLin) (hD : ExactLift T p P D.mulVecLin)
    (hadj : ∀ A ∈ accessible T p, ∀ B ∈ accessible T p, form (O A) B = form A (P B)) :
    Cᴴ * KM = KM * D := by
  classical
  have hs (f : History o n → ℂ) : synthesis T p f ∈ accessible T p := by
    rw [← synthesis_range]; exact ⟨f, rfl⟩
  have he (f g : History o n → ℂ) : pairing (Cᴴ * KM) f g = pairing (KM * D) f g := by
    rw [pairing_exactLift T p ho hT hp hp1 hD]
    have hc := exactLift_apply T p hC f
    change synthesis T p (C *ᵥ f) = O (synthesis T p f) at hc
    rw [← hadj _ (hs f) _ (hs g), ← hc, ← pairing_synthesis T ho hT p hp hp1]
    simp only [pairing, star_mulVec, dotProduct_mulVec, vecMul_vecMul, kernelMatrix]
  ext i j
  have hij := he (Pi.single i 1) (Pi.single j 1)
  simpa [pairing, Matrix.mulVec, dotProduct, Pi.single_apply] using hij

/-- Complex PSD explicitly includes the vanishing imaginary quadratic part. -/
theorem weighted_positive_iff {O : MatQ →ₗ[ℂ] MatQ}
    {C : Matrix (History o n) (History o n) ℂ}
    (hC : ExactLift T p O C.mulVecLin) :
    (KM * C).PosSemidef ↔ KM * C = Cᴴ * KM ∧
      ∀ A ∈ accessible T p, 0 ≤ (form A (O A)).re ∧ (form A (O A)).im = 0 := by
  constructor
  · intro h
    refine ⟨weightedSymmetry_of_positive hK C h, ?_⟩
    intro A hA
    rw [← synthesis_range] at hA
    obtain ⟨f, rfl⟩ := hA
    have hn := h.dotProduct_mulVec_nonneg f
    change 0 ≤ pairing (KM * C) f f at hn
    rw [pairing_exactLift T p ho hT hp hp1 hC] at hn
    exact ⟨hn.1, hn.2.symm⟩
  · rintro ⟨hs, hn⟩
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · change (KM * C)ᴴ = KM * C
      have hk : KMᴴ = KM := (kernel_posSemidef T ho hT p hp hp1).isHermitian.eq
      rw [Matrix.conjTranspose_mul, hk]
      exact hs.symm
    · intro f
      change 0 ≤ pairing (KM * C) f f
      rw [pairing_exactLift T p ho hT hp hp1 hC]
      have hf : synthesis T p f ∈ accessible T p := by
        rw [← synthesis_range]; exact ⟨f, rfl⟩
      exact ⟨(hn _ hf).1, (hn _ hf).2.symm⟩

theorem transfer_norm_le {O : MatQ →ₗ[ℂ] MatQ} (hO : Invariant T p O)
    (hE : ∀ A ∈ accessible T p, (form (O A) (O A)).re ≤ (form A A).re)
    (z : Reconstructed T ho hT p hp hp1) :
    ‖transfer T p ho hT hp hp1 O hO z‖ ≤ ‖z‖ := by
  have hz : coordinates T ho hT p hp hp1 z ∈ accessible T p := by
    rw [← coordinates_range T ho hT p hp hp1]; exact ⟨z, rfl⟩
  have he := hE _ hz
  rw [← coordinates_transfer T p ho hT hp hp1 O hO z,
    ← coordinates_inner T ho hT p hp hp1, ← coordinates_inner T ho hT p hp hp1] at he
  have hzsq := norm_sq_eq_re_inner (𝕜 := ℂ) z
  have htsq := norm_sq_eq_re_inner (𝕜 := ℂ) (transfer T p ho hT hp hp1 O hO z)
  change ‖z‖ ^ 2 = (⟪z, z⟫_ℂ).re at hzsq
  change ‖transfer T p ho hT hp hp1 O hO z‖ ^ 2 =
    (⟪transfer T p ho hT hp hp1 O hO z, transfer T p ho hT hp hp1 O hO z⟫_ℂ).re at htsq
  nlinarith [norm_nonneg z, norm_nonneg (transfer T p ho hT hp hp1 O hO z)]

theorem defect_positive_iff {O : MatQ →ₗ[ℂ] MatQ}
    {C : Matrix (History o n) (History o n) ℂ}
    (hC : ExactLift T p O C.mulVecLin) :
    (KM - Cᴴ * KM * C).PosSemidef ↔
      ∀ A ∈ accessible T p, (form (O A) (O A)).re ≤ (form A A).re := by
  have he (f : History o n → ℂ) :
      pairing (KM - Cᴴ * KM * C) f f =
        form (synthesis T p f) (synthesis T p f) -
        form (O (synthesis T p f)) (O (synthesis T p f)) := by
    have hc := exactLift_apply T p hC f
    change synthesis T p (C *ᵥ f) = O (synthesis T p f) at hc
    rw [← hc, ← pairing_synthesis T ho hT p hp hp1,
      ← pairing_synthesis T ho hT p hp hp1, pairing_mulVec]
    simp only [pairing, Matrix.sub_mulVec, dotProduct_sub, kernelMatrix]
  constructor
  · intro hd A hA
    rw [← synthesis_range] at hA
    obtain ⟨f, rfl⟩ := hA
    have hn := (hd.dotProduct_mulVec_nonneg f).1
    change 0 ≤ (pairing (KM - Cᴴ * KM * C) f f).re at hn
    rw [he, Complex.sub_re] at hn
    exact sub_nonneg.mp hn
  · intro hE
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · exact (kernel_posSemidef T ho hT p hp hp1).isHermitian.sub
        (Matrix.isHermitian_conjTranspose_mul_mul C
          (kernel_posSemidef T ho hT p hp hp1).isHermitian)
    · intro f
      change 0 ≤ pairing (KM - Cᴴ * KM * C) f f
      have hf : synthesis T p f ∈ accessible T p := by
        rw [← synthesis_range]; exact ⟨f, rfl⟩
      have h0 := (kernel_posSemidef T ho hT p hp hp1).dotProduct_mulVec_nonneg f
      have h1 := (kernel_posSemidef T ho hT p hp hp1).dotProduct_mulVec_nonneg (C *ᵥ f)
      change 0 ≤ pairing K f f at h0
      change 0 ≤ pairing K (C *ᵥ f) (C *ᵥ f) at h1
      rw [pairing_synthesis] at h0 h1
      have hc := exactLift_apply T p hC f
      change synthesis T p (C *ᵥ f) = O (synthesis T p f) at hc
      rw [hc] at h1
      rw [he]
      exact ⟨by simpa only [Complex.sub_re, Complex.zero_re, sub_nonneg] using hE _ hf,
        by simp only [Complex.sub_im, ← h0.2, ← h1.2, sub_self, Complex.zero_im]⟩

theorem transferOfLift_positive {O : MatQ →ₗ[ℂ] MatQ}
    {C : Matrix (History o n) (History o n) ℂ}
    (hC : ExactLift T p O C.mulVecLin) (hpos : (KM * C).PosSemidef) :
    (transferOfLift T p ho hT hp hp1 hC).toContinuousLinearMap.IsPositive := by
  have he : (transferOfLift T p ho hT hp hp1 hC).toContinuousLinearMap =
      positiveMatrixTransfer hK C hpos := by
    ext z
    obtain ⟨f, rfl⟩ := mk_surjective K hK z
    change descend hK C.mulVecLin _ (mk K hK f) = _
    rw [descend_mk, positiveMatrixTransfer_mk]
    rfl
  rw [he]
  exact positiveMatrixTransfer_positive hK C hpos

end Weighted

section Insertion
open FiniteAdaptiveKrausRealization (joint unJoint recodeInstrument recodeStep recodeTree
  recodeHistory historyEquiv)
open FinitePositiveKernel.GibbsObservable
variable {m : ℕ} (L : Fin m → MatQ) (hL : IsKrausChannel L)

/-- The inserted channel follows the original central reset. The instrument
retains the single reset label, including all the other zero outcomes. -/
def insertedStep (o n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) :
    Step Q Unit (pairedArity o n) where
  count := _
  evolution k := GibbsMultilevelReflection.joint
    (composeKraus L (FiniteThreeLevelPositiveHistory.channel (p*p)) k)
  normalized := GibbsMultilevelReflection.joint_normalized _
    (isKrausChannel_composeKraus hL
      (FiniteThreeLevelPositiveHistory.channel_normalized (mul_nonneg hp hp) (by nlinarith)))
  instrument := recodeInstrument FiniteInstrument.identity (resetLabel o n)

theorem insertedStep_branch (o n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1) (X : MatQ) :
    (insertedStep L hL o n p hp hp1).branch Q Unit _ (resetLabel o n 0) (joint X) =
      joint (krausMap L (Phi (p*p) X)) := by
  change ((recodeInstrument FiniteInstrument.identity (resetLabel o n)).lift Unit).branch _
    (krausMap (fun k => GibbsMultilevelReflection.joint
      (composeKraus L (FiniteThreeLevelPositiveHistory.channel (p*p)) k))
      (GibbsMultilevelReflection.joint X)) = _
  rw [GibbsMultilevelReflection.joint_kraus, krausMap_composeKraus,
    FiniteThreeLevelPositiveHistory.channel_state (mul_nonneg hp hp) (by nlinarith)]
  change krausMap (fun k => GibbsMultilevelReflection.joint
    ((recodeInstrument FiniteInstrument.identity (resetLabel o n)).operators (resetLabel o n 0) k))
      (GibbsMultilevelReflection.joint (krausMap L (Phi (p*p) X))) = _
  rw [GibbsMultilevelReflection.joint_kraus]
  change joint ((recodeInstrument FiniteInstrument.identity (resetLabel o n)).branch _ _) = _
  rw [recoded_instrument_branch, FiniteInstrument.identity_branch]

theorem insertedStep_invalid (o n : ℕ) (p : ℝ) (hp : 0 ≤ p) (hp1 : p ≤ 1)
    (b : Fin (pairedArity o n)) (hb : b ≠ resetLabel o n 0)
    (X : Matrix (Q × Unit) (Q × Unit) ℂ) :
    (insertedStep L hL o n p hp hp1).branch Q Unit _ b X = 0 := by
  have hn : b ∉ Set.range (resetLabel o n) := by
    rintro ⟨a,rfl⟩
    exact hb (congrArg (resetLabel o n) (Subsingleton.elim a 0))
  simp [Step.branch, insertedStep, FiniteInstrument.lift, FiniteInstrument.branch, krausMap,
    recodeInstrument, FiniteAdaptiveKrausRealization.recodeKraus_invalid _ _ b hn]

/-- An independently normalized physical chronology, before its weight kernel. -/
def insertedTree : Tree Q Unit (pairedArity o n) (n+2) :=
  .node (recodeStep (localStep Q Unit _ (reverseInstrument T hT)) (reverseLabel o n)) (fun _ =>
    .node (insertedStep L hL o n p hp hp1) (fun _ =>
      recodeTree (originalLabel o n) ⟨0,ho⟩ T))

/-- The actual real history weight, embedded into complex coefficients. -/
def insertedKernel (u v : History o n) : ℂ :=
  (weight Q Unit _ (insertedTree T p ho hT hp hp1 L hL)
    (pairedHistory u v) (joint rhoN) : ℂ)

theorem inserted_run (u v : History o n) (X : MatQ) :
    unJoint (run Q Unit _ (insertedTree T p ho hT hp hp1 L hL)
      (pairedHistory u v) (joint X)) =
      branch T v (krausMap L (Phi (p*p) (reverseBranch T u X))) := by
  simp only [insertedTree, pairedHistory, run, FiniteAdaptiveKrausRealization.recodeStep_branch,
    localStep_joint, reverseInstrument_branch, Equiv.apply_symm_apply, insertedStep_branch]
  rw [FiniteAdaptiveKrausRealization.recode_run]
  rfl

theorem inserted_invalid_zero (h : History (pairedArity o n) (n+2))
    (hh : h ∉ Set.range (fun uv : History o n × History o n => pairedHistory uv.1 uv.2))
    (X : Matrix (Q × Unit) (Q × Unit) ℂ) :
    run Q Unit _ (insertedTree T p ho hT hp hp1 L hL) h X = 0 := by
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
      simp only [insertedTree, run]
      exact FiniteAdaptiveKrausRealization.recode_invalid_zero _ _ _ _ hv _
    · simp only [insertedTree, run]
      rw [insertedStep_invalid L hL o n _ _ _ b hb, run_zero]
  · simp only [insertedTree, run]
    rw [FiniteAdaptiveKrausRealization.recodeStep_invalid _ _ a ha, Step.branch_zero, run_zero]

theorem inserted_encoded_sum (X : Matrix (Q × Unit) (Q × Unit) ℂ) :
    (∑ uv : History o n × History o n,
      run Q Unit _ (insertedTree T p ho hT hp hp1 L hL) (pairedHistory uv.1 uv.2) X) =
    ∑ h, run Q Unit _ (insertedTree T p ho hT hp hp1 L hL) h X := by
  exact Fintype.sum_of_injective _ pairedHistory_injective _ _
    (fun h hh => inserted_invalid_zero T p ho hT hp hp1 L hL h hh X) (fun _ => rfl)

theorem inserted_complex_trace (u v : History o n) :
    (run Q Unit _ (insertedTree T p ho hT hp hp1 L hL)
      (pairedHistory u v) (joint rhoN)).trace =
      (effect T v * krausMap L (Phi (p*p) (Gamma (effect T u)))).trace := by
  rw [← FiniteAdaptiveKrausRealization.unJoint_trace, inserted_run, reverseBranch_rho, branch_trace]

theorem insertedKernel_trace (u v : History o n) :
    insertedKernel T p ho hT hp hp1 L hL u v =
      (effect T v * krausMap L (Phi (p*p) (Gamma (effect T u)))).trace := by
  unfold insertedKernel weight
  rw [inserted_complex_trace]
  apply FiniteThreeLevelPositiveHistory.hermitian_product_real _ _ (effect_adjoint T v)
  have he : (Phi (p*p) (Gamma (effect T u)))ᴴ = Phi (p*p) (Gamma (effect T u)) := by
    rw [FiniteThreeLevelPositiveHistory.Phi_Gamma, FiniteThreeLevelPositiveHistory.Gamma_adjoint,
      FiniteThreeLevelPositiveHistory.Psi_adjoint, effect_adjoint]
  simp only [krausMap, Matrix.conjTranspose_sum, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose, he, Matrix.mul_assoc]

theorem inserted_probabilities :
    (∀ h, 0 ≤ weight Q Unit _ (insertedTree T p ho hT hp hp1 L hL) h (joint rhoN)) ∧
    (∑ h, weight Q Unit _ (insertedTree T p ho hT hp hp1 L hL) h (joint rhoN)) = 1 :=
  normalized_weights Q Unit _ _ FiniteThreeLevelPositiveHistory.joint_density

theorem insertedKernel_real (u v : History o n) :
    (insertedKernel T p ho hT hp hp1 L hL u v).im = 0 := rfl

theorem insertedKernel_nonnegative (u v : History o n) :
    0 ≤ (insertedKernel T p ho hT hp hp1 L hL u v).re :=
  (inserted_probabilities T p ho hT hp hp1 L hL).1 _

theorem insertedKernel_normalized :
    ∑ u, ∑ v, insertedKernel T p ho hT hp hp1 L hL u v = 1 := by
  simp_rw [insertedKernel_trace, ← inserted_complex_trace T p ho hT hp hp1 L hL]
  have he := congrArg Matrix.trace (inserted_encoded_sum T p ho hT hp hp1 L hL (joint rhoN))
  rw [Matrix.trace_sum, Matrix.trace_sum] at he
  rw [Fintype.sum_prod_type] at he
  rw [he, sum_trace, FiniteAdaptiveKrausRealization.joint_trace,
    FiniteThreeLevelPositiveHistory.rhoN_trace]

/-- Physical insertion needs commutation for this form identity, but does not
need accessible-range invariance. -/
theorem insertedKernel_form
    (hcomm : ∀ A, Channel.heisenberg L (Psi p A) = Psi p (Channel.heisenberg L A))
    (u v : History o n) :
    insertedKernel T p ho hT hp hp1 L hL u v =
      form (Psi p (effect T u)) (Channel.heisenberg L (Psi p (effect T v))) := by
  rw [insertedKernel_trace, Matrix.trace_mul_comm, ← Channel.trace_duality, Matrix.trace_mul_comm,
    FiniteThreeLevelPositiveHistory.central_split, ← hcomm]
  rw [form, FiniteThreeLevelPositiveHistory.Psi_adjoint, effect_adjoint]
  simp only [Gamma, Matrix.mul_assoc]

theorem insertedKernel_row_sum (u : History o n) :
    (∑ v, insertedKernel T p ho hT hp hp1 L hL u v) = (mass T u : ℂ) := by
  simp_rw [insertedKernel_trace]
  rw [← Matrix.trace_sum, ← Matrix.sum_mul, effect_sum, Matrix.one_mul]
  have ht (X : MatQ) : (krausMap L X).trace = X.trace := by
    simpa only [Channel.heisenberg_one L hL, Matrix.mul_one] using
      (Channel.trace_duality L X 1).symm
  rw [ht, FiniteThreeLevelPositiveHistory.Phi_Gamma,
    FiniteThreeLevelPositiveHistory.Gamma_trace, FiniteThreeLevelPositiveHistory.Psi_mean,
    mass_complex]

/-- The original column marginal additionally uses stationarity of the inserted channel. -/
theorem insertedKernel_column_sum (hstat : krausMap L rhoN = rhoN) (v : History o n) :
    (∑ u, insertedKernel T p ho hT hp hp1 L hL u v) = (mass T v : ℂ) := by
  simp_rw [insertedKernel_trace]
  rw [← Matrix.trace_sum, ← Matrix.mul_sum, ← FiniteThreeLevelHistoryTransfer.kraus_sum,
    ← FiniteThreeLevelPositiveHistory.Phi_sum, ← FiniteThreeLevelPositiveHistory.Gamma_sum,
    effect_sum, FiniteThreeLevelPositiveHistory.Gamma_one]
  have hs : Phi (p*p) rhoN = rhoN := by
    simp [Phi, FiniteThreeLevelPositiveHistory.rhoN_trace, ← add_smul]
  rw [hs, hstat, Matrix.trace_mul_comm, mass_complex]

/-- The form identity becomes `K C` only with an exact coefficient lift. -/
theorem insertedKernel_eq_mul
    (hcomm : ∀ A, Channel.heisenberg L (Psi p A) = Psi p (Channel.heisenberg L A))
    (C : Matrix (History o n) (History o n) ℂ)
    (hC : ExactLift T p (Channel.heisenbergLinear L) C.mulVecLin) :
    (insertedKernel T p ho hT hp hp1 L hL : Matrix (History o n) (History o n) ℂ) =
      kernelMatrix T p ho hT hp hp1 * C := by
  classical
  ext u v
  rw [insertedKernel_form T p ho hT hp hp1 L hL hcomm]
  have he := exactLift_apply T p hC (Pi.single v 1)
  rw [synthesis_single] at he
  change synthesis T p (C *ᵥ Pi.single v 1) = Channel.heisenberg L (Psi p (effect T v)) at he
  rw [← he, ← synthesis_single T p u, ← pairing_synthesis T ho hT p hp hp1]
  simp [pairing, Matrix.mulVec, dotProduct, Pi.single_apply, Matrix.mul_apply, kernelMatrix]

theorem insertedKernel_pairing
    (hcomm : ∀ A, Channel.heisenberg L (Psi p A) = Psi p (Channel.heisenberg L A))
    (C : Matrix (History o n) (History o n) ℂ)
    (hC : ExactLift T p (Channel.heisenbergLinear L) C.mulVecLin)
    (f g : History o n → ℂ) :
    pairing (insertedKernel T p ho hT hp hp1 L hL) f g =
      ⟪mk K hK f, transferOfLift T p ho hT hp hp1 hC (mk K hK g)⟫_ℂ := by
  rw [insertedKernel_eq_mul T p ho hT hp hp1 L hL hcomm C hC,
    transferOfLift, descend_mk, inner_mk]
  change star f ⬝ᵥ (kernelMatrix T p ho hT hp hp1 * C) *ᵥ g =
    star f ⬝ᵥ kernelMatrix T p ho hT hp hp1 *ᵥ (C *ᵥ g)
  rw [Matrix.mulVec_mulVec]

theorem inserted_pairing_form
    (hcomm : ∀ A, Channel.heisenberg L (Psi p A) = Psi p (Channel.heisenberg L A))
    (f g : History o n → ℂ) :
    pairing (insertedKernel T p ho hT hp hp1 L hL) f g =
      form (synthesis T p f) (Channel.heisenberg L (synthesis T p g)) := by
  have he (A : MatQ) : Channel.heisenberg L A = Channel.heisenbergLinear L A := rfl
  simp_rw [he]
  simp only [synthesis, map_sum, map_smul,
    FiniteThreeLevelHistoryTransfer.form_sum_left,
    FiniteThreeLevelHistoryTransfer.form_sum_right,
    FiniteThreeLevelPositiveHistory.form_smul, pairing, Matrix.mulVec, dotProduct,
    Finset.mul_sum, Pi.star_apply]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro u _
  apply Finset.sum_congr rfl
  intro v _
  rw [insertedKernel_form T p ho hT hp hp1 L hL hcomm]
  rw [he]
  ring

end Insertion

section Reset
open FiniteThreeLevelHistoryTransfer (mean meanLinear)

def average : (History o n → ℂ) →ₗ[ℂ] ℂ where
  toFun f := ∑ h, (mass T h : ℂ) * f h
  map_add' f g := by simp [mul_add, Finset.sum_add_distrib]
  map_smul' c f := by simp [Finset.mul_sum, mul_left_comm]

theorem average_one : average T (fun _ => 1) = 1 := by
  simp only [average, LinearMap.coe_mk, AddHom.coe_mk, mul_one,
    ← Complex.ofReal_sum, mass_sum, Complex.ofReal_one]

theorem synthesis_mean (f : History o n → ℂ) : mean (synthesis T p f) = average T f := by
  change meanLinear (∑ h, f h • Psi p (effect T h)) = _
  rw [map_sum]
  simp only [map_smul]
  change (∑ h, f h * mean (Psi p (effect T h))) = _
  simp_rw [FiniteThreeLevelHistoryTransfer.mean_Psi]
  simp only [mean, ← mass_complex]
  exact Finset.sum_congr rfl (fun _ _ => mul_comm _ _)

def resetCoefficients (a : ℝ) : (History o n → ℂ) →ₗ[ℂ] (History o n → ℂ) where
  toFun f i := (a : ℂ) * f i + (1 - (a : ℂ)) * average T f
  map_add' f g := by ext i; simp only [map_add, Pi.add_apply]; ring
  map_smul' c f := by ext i; simp only [map_smul, Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

def resetMatrix (a : ℝ) : Matrix (History o n) (History o n) ℂ :=
  fun i j => (a : ℂ) * (if i = j then 1 else 0) + (1 - (a : ℂ)) * (mass T j : ℂ)

theorem resetMatrix_mulVec (a : ℝ) (f : History o n → ℂ) :
    resetMatrix T a *ᵥ f = resetCoefficients T a f := by
  classical
  ext i
  simp [resetMatrix, resetCoefficients, average, Matrix.mulVec, dotProduct,
    add_mul, Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

theorem resetCoefficients_average (a : ℝ) (f : History o n → ℂ) :
    average T (resetCoefficients T a f) = average T f := by
  have he : resetCoefficients T a f = (a : ℂ) • f +
      ((1 - (a : ℂ)) * average T f) • (fun _ => 1) := by
    ext i; simp [resetCoefficients]
  rw [he, map_add, map_smul, map_smul, average_one]
  simp only [smul_eq_mul, mul_one]
  ring

theorem resetCoefficients_comp (a b : ℝ) :
    (resetCoefficients T a).comp (resetCoefficients T b) = resetCoefficients T (a*b) := by
  apply LinearMap.ext
  intro f
  funext i
  change (a : ℂ) * ((b : ℂ) * f i + (1 - (b : ℂ)) * average T f) +
    (1 - (a : ℂ)) * average T (resetCoefficients T b f) = _
  rw [resetCoefficients_average]
  simp only [resetCoefficients, LinearMap.coe_mk, AddHom.coe_mk, Complex.ofReal_mul]
  ring

theorem resetCoefficients_exact (a : ℝ) :
    ExactLift T p (FiniteThreeLevelPositiveHistory.PsiLinear a) (resetCoefficients T a) := by
  apply LinearMap.ext
  intro f
  apply Matrix.ext
  intro i j
  have he : resetCoefficients T a f = (a : ℂ) • f +
      ((1 - (a : ℂ)) * average T f) • (fun _ => 1) := by
    ext k; simp [resetCoefficients]
  have hs : synthesis T p (resetCoefficients T a f) = Psi a (synthesis T p f) := by
    change synthesisLinear T p (resetCoefficients T a f) = _
    rw [he, map_add, map_smul, map_smul]
    change (a : ℂ) • synthesis T p f +
      ((1 - (a : ℂ)) * average T f) • synthesis T p (fun _ => 1) = _
    rw [synthesis_constant]
    simp only [Psi, ← smul_smul, ← synthesis_mean T p f, mean]
  exact congrFun (congrFun hs i) j

theorem reset_invariant (a : ℝ) : Invariant T p (FiniteThreeLevelPositiveHistory.PsiLinear a) :=
  (invariant_iff_exists_exactLift T p _).mpr ⟨_, resetCoefficients_exact T p a⟩

def resetTransfer (a : ℝ) :
    Reconstructed T ho hT p hp hp1 →ₗ[ℂ] Reconstructed T ho hT p hp hp1 :=
  transfer T p ho hT hp hp1 (FiniteThreeLevelPositiveHistory.PsiLinear a) (reset_invariant T p a)

theorem coordinates_resetTransfer (a : ℝ) (z : Reconstructed T ho hT p hp hp1) :
    coordinates T ho hT p hp hp1 (resetTransfer T p ho hT hp hp1 a z) =
      Psi a (coordinates T ho hT p hp hp1 z) :=
  coordinates_transfer T p ho hT hp hp1 _ _ z

theorem resetTransfer_comp (a b : ℝ) :
    (resetTransfer T p ho hT hp hp1 a).comp (resetTransfer T p ho hT hp hp1 b) =
      resetTransfer T p ho hT hp hp1 (a*b) := by
  ext z
  apply coordinates_injective T ho hT p hp hp1
  simp only [LinearMap.comp_apply, coordinates_resetTransfer,
    FiniteThreeLevelPositiveHistory.Psi_comp]

theorem resetTransfer_one : resetTransfer T p ho hT hp hp1 1 = LinearMap.id := by
  ext z
  apply coordinates_injective T ho hT p hp hp1
  rw [coordinates_resetTransfer, FiniteThreeLevelPositiveHistory.Psi_one]
  rfl

theorem resetTransfer_zero_idempotent :
    (resetTransfer T p ho hT hp hp1 0).comp (resetTransfer T p ho hT hp hp1 0) =
      resetTransfer T p ho hT hp hp1 0 := by
  rw [resetTransfer_comp, zero_mul]

theorem resetTransfer_symmetric (a : ℝ) (z w : Reconstructed T ho hT p hp hp1) :
    ⟪resetTransfer T p ho hT hp hp1 a z, w⟫_ℂ =
      ⟪z, resetTransfer T p ho hT hp hp1 a w⟫_ℂ := by
  rw [coordinates_inner, coordinates_inner, coordinates_resetTransfer, coordinates_resetTransfer]
  exact (FiniteThreeLevelPositiveHistory.form_Psi_symmetric a _ _).symm

local notation "P₀" => resetTransfer T p ho hT hp hp1 0

theorem scalar_orthogonal (z : Reconstructed T ho hT p hp hp1) :
    ⟪P₀ z, z - P₀ z⟫_ℂ = 0 := by
  have hi := LinearMap.congr_fun (resetTransfer_zero_idempotent T p ho hT hp hp1) z
  change P₀ (P₀ z) = P₀ z at hi
  have hs := resetTransfer_symmetric T p ho hT hp hp1 0 (P₀ z) z
  rw [hi] at hs
  rw [inner_sub_right, hs, sub_self]

theorem scalar_pythagoras (z : Reconstructed T ho hT p hp hp1) :
    ‖z‖ ^ 2 = ‖P₀ z‖ ^ 2 + ‖z - P₀ z‖ ^ 2 := by
  have he := norm_add_sq (𝕜 := ℂ) (P₀ z) (z - P₀ z)
  rw [scalar_orthogonal] at he
  have hz : P₀ z + (z - P₀ z) = z := by abel
  simpa only [hz, map_zero, mul_zero, add_zero] using he

theorem resetTransfer_split (a : ℝ) (z : Reconstructed T ho hT p hp hp1) :
    resetTransfer T p ho hT hp hp1 a z = P₀ z + (a : ℂ) • (z - P₀ z) := by
  apply coordinates_injective T ho hT p hp hp1
  rw [map_add, map_smul, map_sub, coordinates_resetTransfer, coordinates_resetTransfer]
  simp only [Psi, Complex.ofReal_zero, zero_smul, sub_zero, one_smul]
  module

theorem reset_norm_sq (a : ℝ) (z : Reconstructed T ho hT p hp hp1) :
    ‖resetTransfer T p ho hT hp hp1 a z‖ ^ 2 =
      ‖P₀ z‖ ^ 2 + a^2 * ‖z - P₀ z‖ ^ 2 := by
  rw [resetTransfer_split, norm_add_sq (𝕜 := ℂ), inner_smul_right, scalar_orthogonal]
  simp only [mul_zero, map_zero, add_zero, norm_smul, Complex.norm_real, Real.norm_eq_abs,
    mul_pow, sq_abs]

theorem scalar_positive : (P₀).toContinuousLinearMap.IsPositive := by
  refine ⟨resetTransfer_symmetric T p ho hT hp hp1 0, ?_⟩
  intro z
  have ho := scalar_orthogonal T p ho hT hp hp1 z
  rw [inner_sub_right, sub_eq_zero] at ho
  change 0 ≤ (⟪P₀ z,z⟫_ℂ).re
  rw [ho]
  exact inner_self_nonneg (𝕜 := ℂ) (x := P₀ z)

theorem reset_positive (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (resetTransfer T p ho hT hp hp1 a).toContinuousLinearMap.IsPositive := by
  have he : (resetTransfer T p ho hT hp hp1 a).toContinuousLinearMap =
      (1 - (a : ℂ)) • (P₀).toContinuousLinearMap +
        (a : ℂ) • (1 : Reconstructed T ho hT p hp hp1 →L[ℂ] Reconstructed T ho hT p hp hp1) := by
    ext z
    change resetTransfer T p ho hT hp hp1 a z = (1 - (a : ℂ)) • P₀ z + (a : ℂ) • z
    rw [resetTransfer_split]
    module
  rw [he]
  exact ((scalar_positive T p ho hT hp hp1).smul_of_nonneg
    (by exact_mod_cast sub_nonneg.mpr ha1)).add
    (ContinuousLinearMap.isPositive_one.smul_of_nonneg (by exact_mod_cast ha))

theorem resetMatrix_exact (a : ℝ) :
    ExactLift T p (FiniteThreeLevelPositiveHistory.PsiLinear a) (resetMatrix T a).mulVecLin := by
  have he : (resetMatrix T a).mulVecLin = resetCoefficients T a := by
    apply LinearMap.ext
    intro f
    exact resetMatrix_mulVec T a f
  rw [he]
  exact resetCoefficients_exact T p a

theorem resetMatrix_comp (a b : ℝ) : resetMatrix T a * resetMatrix T b = resetMatrix T (a*b) := by
  classical
  have he (f : History o n → ℂ) :
      (resetMatrix T a * resetMatrix T b) *ᵥ f = resetMatrix T (a*b) *ᵥ f := by
    rw [← Matrix.mulVec_mulVec, resetMatrix_mulVec, resetMatrix_mulVec, resetMatrix_mulVec]
    exact LinearMap.congr_fun (resetCoefficients_comp T a b) f
  ext i j
  simpa [Matrix.mulVec, dotProduct, Pi.single_apply] using congrFun (he (Pi.single j 1)) i

def massKernel : Matrix (History o n) (History o n) ℂ :=
  fun i j => (mass T i : ℂ) * (mass T j : ℂ)

theorem kernel_mul_reset (a : ℝ) :
    kernelMatrix T p ho hT hp hp1 * resetMatrix T a =
      (a : ℂ) • kernelMatrix T p ho hT hp hp1 + (1 - (a : ℂ)) • massKernel T := by
  classical
  ext i j
  simp only [Matrix.mul_apply, resetMatrix, mul_add, Finset.sum_add_distrib]
  have he : (∑ x, kernelMatrix T p ho hT hp hp1 i x *
      ((a : ℂ) * if x = j then 1 else 0)) = (a : ℂ) * kernelMatrix T p ho hT hp hp1 i j := by
    simp [mul_ite, mul_comm]
  rw [he, ← Finset.sum_mul]
  change _ + (∑ x, kernel T ho hT p hp hp1 i x) * _ = _
  rw [kernel_row_sum]
  simp only [Matrix.add_apply, Matrix.smul_apply, massKernel, smul_eq_mul]
  ring

theorem reset_weighted_adjoint (a : ℝ) :
    (resetMatrix T a)ᴴ * kernelMatrix T p ho hT hp hp1 =
      kernelMatrix T p ho hT hp hp1 * resetMatrix T a := by
  apply weighted_adjoint T p ho hT hp hp1 (resetMatrix_exact T p a)
    (resetMatrix_exact T p a)
  intro A _ B _
  exact (FiniteThreeLevelPositiveHistory.form_Psi_symmetric a A B).symm

/-- The defect uses the square of the old-space retention. -/
theorem reset_defect (a : ℝ) :
    kernelMatrix T p ho hT hp hp1 -
      (resetMatrix T a)ᴴ * kernelMatrix T p ho hT hp hp1 * resetMatrix T a =
    (1 - (a : ℂ)^2) • (kernelMatrix T p ho hT hp hp1 - massKernel T) := by
  rw [reset_weighted_adjoint, Matrix.mul_assoc, resetMatrix_comp, kernel_mul_reset]
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul,
    Complex.ofReal_mul]
  ring

include ho hT hp hp1 in
theorem reset_energy_le (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (A : MatQ) (hA : A ∈ accessible T p) :
    (form (Psi a A) (Psi a A)).re ≤ (form A A).re := by
  rw [← coordinates_range T ho hT p hp hp1] at hA
  obtain ⟨z, rfl⟩ := hA
  rw [← coordinates_resetTransfer T p ho hT hp hp1 a z,
    ← coordinates_inner, ← coordinates_inner]
  have hz := norm_sq_eq_re_inner (𝕜 := ℂ) z
  have ht := norm_sq_eq_re_inner (𝕜 := ℂ) (resetTransfer T p ho hT hp hp1 a z)
  change ‖z‖ ^ 2 = (⟪z,z⟫_ℂ).re at hz
  change ‖resetTransfer T p ho hT hp hp1 a z‖ ^ 2 =
    (⟪resetTransfer T p ho hT hp hp1 a z,resetTransfer T p ho hT hp hp1 a z⟫_ℂ).re at ht
  rw [← hz, ← ht, reset_norm_sq, scalar_pythagoras T p ho hT hp hp1 z]
  have ha2 : a^2 ≤ 1 := by nlinarith
  nlinarith [sq_nonneg ‖z - P₀ z‖]

/-- Centering the actual chronological Gram kernel preserves complex PSD. -/
theorem centeredKernel_posSemidef :
    (kernelMatrix T p ho hT hp hp1 - massKernel T).PosSemidef := by
  have hd := (defect_positive_iff T p ho hT hp hp1 (resetMatrix_exact T p 0)).mpr
    (reset_energy_le T p ho hT hp hp1 0 (by norm_num) (by norm_num))
  rw [reset_defect] at hd
  simpa only [Complex.ofReal_zero, zero_pow (by decide : 2 ≠ 0), sub_zero, one_smul] using hd

theorem reset_inserted_eq_original (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    insertedKernel T p ho hT hp hp1 (FiniteThreeLevelPositiveHistory.channel a)
      (FiniteThreeLevelPositiveHistory.channel_normalized ha ha1) =
    kernel T ho hT (p * Real.sqrt a) (mul_nonneg hp (Real.sqrt_nonneg a))
      (mul_le_one₀ hp1 (Real.sqrt_nonneg a) (Real.sqrt_le_one.mpr ha1)) := by
  ext u v
  rw [insertedKernel_trace, kernel_complex_trace,
    FiniteThreeLevelPositiveHistory.channel_state ha ha1]
  simp only [FiniteThreeLevelPositiveHistory.Phi_Gamma, FiniteThreeLevelPositiveHistory.Psi_comp]
  have he : a * (p*p) = (p * Real.sqrt a) * (p * Real.sqrt a) := by
    nlinarith [Real.sq_sqrt ha]
  rw [he]

theorem scaled_synthesis (b : ℝ) (f : History o n → ℂ) :
    synthesis T (p*b) f = Psi b (synthesis T p f) := by
  simp only [synthesis, FiniteThreeLevelPositiveHistory.Psi_sum,
    FiniteThreeLevelPositiveHistory.Psi_smul, FiniteThreeLevelPositiveHistory.Psi_comp]
  rw [mul_comm p b]

theorem scaled_null (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (f : Coefficients hK) (hf : f ∈ nullSpace K hK) :
    FiniteThreeLevelHistoryTransfer.coefficientIdentity hK
      (kernel_posSemidef T ho hT (p*b) (mul_nonneg hp hb) (mul_le_one₀ hp1 hb hb1)) f ∈
      nullSpace (kernel T ho hT (p*b) (mul_nonneg hp hb) (mul_le_one₀ hp1 hb hb1))
        (kernel_posSemidef T ho hT (p*b) (mul_nonneg hp hb) (mul_le_one₀ hp1 hb hb1)) := by
  apply (mem_nullSpace_iff _ _ _).mpr
  change pairing (kernel T ho hT (p*b) (mul_nonneg hp hb) (mul_le_one₀ hp1 hb hb1)) f f = 0
  rw [pairing_synthesis, scaled_synthesis]
  have hz := (null_iff T ho hT p hp hp1 f).mp
    ((mk_eq_zero_iff K hK f).mpr ((mem_nullSpace_iff K hK f).mp hf))
  rw [hz]
  simp [Psi, form]

/-- Same literal history coefficients into the quotient with scaled retention. -/
def sameHistory (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1) :
    Reconstructed T ho hT p hp hp1 →ₗ[ℂ]
      Reconstructed T ho hT (p*b) (mul_nonneg hp hb) (mul_le_one₀ hp1 hb hb1) :=
  FiniteThreeLevelHistoryTransfer.quotientTransport hK
    (kernel_posSemidef T ho hT (p*b) (mul_nonneg hp hb) (mul_le_one₀ hp1 hb hb1))
    (scaled_null T p ho hT hp hp1 b hb hb1)

theorem sameHistory_mk (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1) (f : History o n → ℂ) :
    sameHistory T p ho hT hp hp1 b hb hb1 (mk K hK f) =
      mk (kernel T ho hT (p*b) (mul_nonneg hp hb) (mul_le_one₀ hp1 hb hb1))
        (kernel_posSemidef T ho hT (p*b) (mul_nonneg hp hb) (mul_le_one₀ hp1 hb hb1)) f :=
  FiniteThreeLevelHistoryTransfer.quotientTransport_mk hK _ _ f

theorem sameHistory_norm (b : ℝ) (hb : 0 ≤ b) (hb1 : b ≤ 1)
    (z : Reconstructed T ho hT p hp hp1) :
    ‖sameHistory T p ho hT hp hp1 b hb hb1 z‖ = ‖resetTransfer T p ho hT hp hp1 b z‖ := by
  apply FiniteThreeLevelHistoryTransfer.quotientTransport_norm hK _ _
    (resetTransfer T p ho hT hp hp1 b).toContinuousLinearMap _ z
  intro f
  rw [pairing_synthesis, scaled_synthesis]
  have he := coordinates_inner T ho hT p hp hp1
    (resetTransfer T p ho hT hp hp1 b (mk K hK f))
    (resetTransfer T p ho hT hp hp1 b (mk K hK f))
  simp only [coordinates_resetTransfer, coordinates_mk] at he
  exact he.symm

theorem sameHistory_sqrt_norm_sq (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (z : Reconstructed T ho hT p hp hp1) :
    ‖sameHistory T p ho hT hp hp1 (Real.sqrt a) (Real.sqrt_nonneg a)
      (Real.sqrt_le_one.mpr ha1) z‖ ^ 2 = ‖P₀ z‖ ^ 2 + a * ‖z - P₀ z‖ ^ 2 := by
  rw [sameHistory_norm, reset_norm_sq, Real.sq_sqrt ha]

theorem reset_sameHistory_strict_iff (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (z : Reconstructed T ho hT p hp hp1) :
    ‖resetTransfer T p ho hT hp hp1 a z‖ <
      ‖sameHistory T p ho hT hp hp1 (Real.sqrt a) (Real.sqrt_nonneg a)
        (Real.sqrt_le_one.mpr ha1.le) z‖ ↔ z - P₀ z ≠ 0 := by
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), reset_norm_sq, sameHistory_sqrt_norm_sq]
  · constructor
    · intro hs hz
      simp [hz] at hs
    · intro hz
      have hn : 0 < ‖z - P₀ z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
      have ha2 : a^2 < a := by nlinarith
      exact add_lt_add_right (mul_lt_mul_of_pos_right ha2 hn) _
  · exact ha.le
  · exact ha1.le

theorem scaled_rank_positive (b : ℝ) (hb : 0 < b) (hb1 : b ≤ 1) :
    Module.finrank ℂ (Reconstructed T ho hT (p*b) (mul_nonneg hp hb.le)
      (mul_le_one₀ hp1 hb.le hb1)) =
    Module.finrank ℂ (Reconstructed T ho hT p hp hp1) := by
  rw [reconstructed_finrank, reconstructed_finrank]
  by_cases hp0 : p = 0
  · have he : accessible T (p*b) = accessible T p := by rw [hp0, zero_mul]
    rw [he]
  · rw [range_positive_eq_effect_span _ _ (mul_pos (lt_of_le_of_ne hp (Ne.symm hp0)) hb),
      range_positive_eq_effect_span _ _ (lt_of_le_of_ne hp (Ne.symm hp0))]

theorem scaled_rank_zero :
    Module.finrank ℂ (Reconstructed T ho hT (p*0) (by positivity) (by simp)) = 1 := by
  rw [reconstructed_finrank]
  have he : accessible T (p*0) = Submodule.span ℂ {(1 : MatQ)} := by
    rw [mul_zero, reset_range]
  rw [he]
  exact finrank_span_singleton (one_ne_zero : (1 : MatQ) ≠ 0)

/-- Complete reset drops rank precisely when the original range is nonscalar. -/
theorem reset_rank_drop_iff :
    Module.finrank ℂ (Reconstructed T ho hT 0 (by norm_num) (by norm_num)) <
      Module.finrank ℂ (Reconstructed T ho hT p hp hp1) ↔
    1 < Module.finrank ℂ (accessible T p) := by
  rw [reset_finrank, reconstructed_finrank]

theorem scalar_of_rank_one
    (hr : Module.finrank ℂ (accessible T p) = 1) :
    accessible T p = Submodule.span ℂ {(1 : MatQ)} := by
  symm
  apply Submodule.eq_of_le_of_finrank_eq
  · apply Submodule.span_le.mpr
    intro A hA
    rw [Set.mem_singleton_iff.mp hA]
    exact one_mem_accessible T p
  · rw [hr, finrank_span_singleton (one_ne_zero : (1 : MatQ) ≠ 0)]

theorem resetTransfer_eq_id_of_scalar
    (hs : accessible T p = Submodule.span ℂ {(1 : MatQ)}) (a : ℝ) :
    resetTransfer T p ho hT hp hp1 a = LinearMap.id := by
  ext z
  apply coordinates_injective T ho hT p hp hp1
  rw [coordinates_resetTransfer]
  have hz : coordinates T ho hT p hp hp1 z ∈ accessible T p := by
    rw [← coordinates_range T ho hT p hp hp1]; exact ⟨z,rfl⟩
  rw [hs] at hz
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hz
  change Psi a (coordinates T ho hT p hp hp1 z) = coordinates T ho hT p hp hp1 z
  rw [← hc, FiniteThreeLevelPositiveHistory.Psi_smul,
    FiniteThreeLevelPositiveHistory.Psi_unital]

theorem rank_one_no_center
    (hr : Module.finrank ℂ (accessible T p) = 1)
    (z : Reconstructed T ho hT p hp hp1) : z - P₀ z = 0 := by
  rw [resetTransfer_eq_id_of_scalar T p ho hT hp hp1 (scalar_of_rank_one T p hr)]
  exact sub_self z

theorem reset_endpoint_no_decay (a : ℝ) :
    resetTransfer T 0 ho hT (by norm_num) (by norm_num) a = LinearMap.id :=
  resetTransfer_eq_id_of_scalar T 0 ho hT (by norm_num) (by norm_num) (reset_range T) a

theorem resetInserted_positive (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    Matrix.PosSemidef (insertedKernel T p ho hT hp hp1
      (FiniteThreeLevelPositiveHistory.channel a)
      (FiniteThreeLevelPositiveHistory.channel_normalized ha ha1)) := by
  rw [reset_inserted_eq_original T p ho hT hp hp1 a ha ha1]
  exact kernel_posSemidef T ho hT _ _ _

abbrev ResetInsertedSpace (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :=
  Space (insertedKernel T p ho hT hp hp1 (FiniteThreeLevelPositiveHistory.channel a)
    (FiniteThreeLevelPositiveHistory.channel_normalized ha ha1))
      (resetInserted_positive T p ho hT hp hp1 a ha ha1)

theorem resetInserted_rank_positive (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    Module.finrank ℂ (ResetInsertedSpace T p ho hT hp hp1 a ha.le ha1) =
      Module.finrank ℂ (Reconstructed T ho hT p hp hp1) := by
  rw [FiniteThreeLevelHistoryTransfer.space_finrank_congr _ _
    (reset_inserted_eq_original T p ho hT hp hp1 a ha.le ha1)]
  exact scaled_rank_positive T p ho hT hp hp1 (Real.sqrt a) (Real.sqrt_pos.mpr ha)
    (Real.sqrt_le_one.mpr ha1)

theorem resetInserted_rank_zero :
    Module.finrank ℂ (ResetInsertedSpace T p ho hT hp hp1 0 (by norm_num) (by norm_num)) = 1 := by
  rw [FiniteThreeLevelHistoryTransfer.space_finrank_congr _ _
    (reset_inserted_eq_original T p ho hT hp hp1 0 (by norm_num) (by norm_num))]
  change Module.finrank ℂ (Reconstructed T ho hT (p * Real.sqrt 0) _ _) = 1
  rw [reconstructed_finrank]
  have he : accessible T (p * Real.sqrt 0) = accessible T 0 := by rw [Real.sqrt_zero, mul_zero]
  rw [he, reset_range]
  exact finrank_span_singleton (one_ne_zero : (1 : MatQ) ≠ 0)

theorem resetInserted_strict_rank_drop_iff :
    Module.finrank ℂ (ResetInsertedSpace T p ho hT hp hp1 0 (by norm_num) (by norm_num)) <
      Module.finrank ℂ (Reconstructed T ho hT p hp hp1) ↔
    1 < Module.finrank ℂ (accessible T p) := by
  rw [resetInserted_rank_zero, reconstructed_finrank]

/-- Equality transports the existing quotient, including its metric. -/
private def kernelEquality (KM LM : Matrix (History o n) (History o n) ℂ)
    (hk : KM.PosSemidef) (hl : LM.PosSemidef) (he : KM = LM) :
    Space KM hk ≃ₗᵢ[ℂ] Space LM hl := by
  have hn : ∀ f : Coefficients hk, f ∈ nullSpace KM hk →
      FiniteThreeLevelHistoryTransfer.coefficientIdentity hk hl f ∈ nullSpace LM hl := by
    subst LM
    exact fun _ hf => hf
  let F : Space KM hk →ₗᵢ[ℂ] Space LM hl :=
    { toLinearMap := FiniteThreeLevelHistoryTransfer.quotientTransport hk hl hn
      norm_map' := by
        intro z
        apply FiniteThreeLevelHistoryTransfer.quotientTransport_norm hk hl hn
          (ContinuousLinearMap.id ℂ _) _ z
        intro f
        rw [ContinuousLinearMap.id_apply, inner_mk, he] }
  exact LinearIsometryEquiv.ofSurjective F (by
    intro z
    obtain ⟨f,rfl⟩ := mk_surjective LM hl z
    exact ⟨mk KM hk f, FiniteThreeLevelHistoryTransfer.quotientTransport_mk hk hl hn f⟩)

private theorem kernelEquality_mk (KM LM : Matrix (History o n) (History o n) ℂ)
    (hk : KM.PosSemidef) (hl : LM.PosSemidef) (he : KM = LM) (f : History o n → ℂ) :
    kernelEquality KM LM hk hl he (mk KM hk f) = mk LM hl f := by
  exact FiniteThreeLevelHistoryTransfer.quotientTransport_mk hk hl _ f

def resetKernelIdentification (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    ResetInsertedSpace T p ho hT hp hp1 a ha ha1 ≃ₗᵢ[ℂ]
      Reconstructed T ho hT (p * Real.sqrt a) (mul_nonneg hp (Real.sqrt_nonneg a))
        (mul_le_one₀ hp1 (Real.sqrt_nonneg a) (Real.sqrt_le_one.mpr ha1)) :=
  kernelEquality _ _ _ _ (reset_inserted_eq_original T p ho hT hp hp1 a ha ha1)

theorem resetKernelIdentification_mk (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (f : History o n → ℂ) :
    resetKernelIdentification T p ho hT hp hp1 a ha ha1
      (mk (insertedKernel T p ho hT hp hp1 (FiniteThreeLevelPositiveHistory.channel a)
        (FiniteThreeLevelPositiveHistory.channel_normalized ha ha1))
        (resetInserted_positive T p ho hT hp hp1 a ha ha1) f) =
      mk (kernel T ho hT (p * Real.sqrt a) (mul_nonneg hp (Real.sqrt_nonneg a))
        (mul_le_one₀ hp1 (Real.sqrt_nonneg a) (Real.sqrt_le_one.mpr ha1))) _ f :=
  kernelEquality_mk _ _ _ _ (reset_inserted_eq_original T p ho hT hp hp1 a ha ha1) f

theorem resetInserted_one :
    insertedKernel T p ho hT hp hp1 (FiniteThreeLevelPositiveHistory.channel 1)
      (FiniteThreeLevelPositiveHistory.channel_normalized (by norm_num) (by norm_num)) = K := by
  ext u v
  rw [insertedKernel_trace, FiniteThreeLevelPositiveHistory.channel_state (by norm_num) (by norm_num),
    FiniteThreeLevelPositiveHistory.Phi_one, kernel_complex_trace]

theorem resetInserted_zero :
    insertedKernel T p ho hT hp hp1 (FiniteThreeLevelPositiveHistory.channel 0)
      (FiniteThreeLevelPositiveHistory.channel_normalized (by norm_num) (by norm_num)) =
    kernel T ho hT 0 (by norm_num) (by norm_num) := by
  ext u v
  rw [insertedKernel_trace, FiniteThreeLevelPositiveHistory.channel_state (by norm_num) (by norm_num),
    kernel_complex_trace, FiniteThreeLevelPositiveHistory.Phi_Gamma,
    FiniteThreeLevelPositiveHistory.Phi_Gamma, FiniteThreeLevelPositiveHistory.Phi_Gamma,
    FiniteThreeLevelPositiveHistory.Psi_comp, zero_mul, zero_mul]

/-- At unit retention the actual inserted quotient is canonically the old one. -/
def resetUnitIdentification :
    ResetInsertedSpace T p ho hT hp hp1 1 (by norm_num) (by norm_num) ≃ₗᵢ[ℂ]
      Reconstructed T ho hT p hp hp1 :=
  kernelEquality _ _ _ _ (resetInserted_one T p ho hT hp hp1)

theorem resetUnitIdentification_mk (f : History o n → ℂ) :
    resetUnitIdentification T p ho hT hp hp1
      (mk (insertedKernel T p ho hT hp hp1 (FiniteThreeLevelPositiveHistory.channel 1)
        (FiniteThreeLevelPositiveHistory.channel_normalized (by norm_num) (by norm_num)))
        (resetInserted_positive T p ho hT hp hp1 1 (by norm_num) (by norm_num)) f) = mk K hK f :=
  kernelEquality_mk _ _ _ _ (resetInserted_one T p ho hT hp hp1) f

def resetZeroIdentification :
    ResetInsertedSpace T p ho hT hp hp1 0 (by norm_num) (by norm_num) ≃ₗᵢ[ℂ]
      Reconstructed T ho hT 0 (by norm_num) (by norm_num) :=
  kernelEquality _ _ _ _ (resetInserted_zero T p ho hT hp hp1)

theorem resetZeroIdentification_mk (f : History o n → ℂ) :
    resetZeroIdentification T p ho hT hp hp1
      (mk (insertedKernel T p ho hT hp hp1 (FiniteThreeLevelPositiveHistory.channel 0)
        (FiniteThreeLevelPositiveHistory.channel_normalized (by norm_num) (by norm_num)))
        (resetInserted_positive T p ho hT hp hp1 0 (by norm_num) (by norm_num)) f) =
      mk (kernel T ho hT 0 (by norm_num) (by norm_num)) _ f :=
  kernelEquality_mk _ _ _ _ (resetInserted_zero T p ho hT hp hp1) f

/-- Literal coefficients transported into the actual inserted-kernel quotient. -/
def resetSameHistory (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    Reconstructed T ho hT p hp hp1 →ₗ[ℂ] ResetInsertedSpace T p ho hT hp hp1 a ha ha1 :=
  (resetKernelIdentification T p ho hT hp hp1 a ha ha1).symm.toLinearEquiv.toLinearMap.comp
    (sameHistory T p ho hT hp hp1 (Real.sqrt a) (Real.sqrt_nonneg a) (Real.sqrt_le_one.mpr ha1))

theorem resetSameHistory_mk (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (f : History o n → ℂ) :
    resetSameHistory T p ho hT hp hp1 a ha ha1 (mk K hK f) =
      mk (insertedKernel T p ho hT hp hp1 (FiniteThreeLevelPositiveHistory.channel a)
        (FiniteThreeLevelPositiveHistory.channel_normalized ha ha1))
        (resetInserted_positive T p ho hT hp hp1 a ha ha1) f := by
  apply (resetKernelIdentification T p ho hT hp hp1 a ha ha1).injective
  change resetKernelIdentification T p ho hT hp hp1 a ha ha1
    ((resetKernelIdentification T p ho hT hp hp1 a ha ha1).symm
      (sameHistory T p ho hT hp hp1 (Real.sqrt a) (Real.sqrt_nonneg a)
        (Real.sqrt_le_one.mpr ha1) (mk K hK f))) = _
  rw [LinearIsometryEquiv.apply_symm_apply, sameHistory_mk, resetKernelIdentification_mk]

theorem resetSameHistory_norm_sq (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (z : Reconstructed T ho hT p hp hp1) :
    ‖resetSameHistory T p ho hT hp hp1 a ha ha1 z‖ ^ 2 =
      ‖P₀ z‖ ^ 2 + a * ‖z - P₀ z‖ ^ 2 := by
  change ‖(resetKernelIdentification T p ho hT hp hp1 a ha ha1).symm
    (sameHistory T p ho hT hp hp1 (Real.sqrt a) (Real.sqrt_nonneg a)
      (Real.sqrt_le_one.mpr ha1) z)‖ ^ 2 = _
  rw [LinearIsometryEquiv.norm_map]
  exact sameHistory_sqrt_norm_sq T p ho hT hp hp1 a ha ha1 z

theorem resetSameHistory_strict_iff (a : ℝ) (ha : 0 < a) (ha1 : a < 1)
    (z : Reconstructed T ho hT p hp hp1) :
    ‖resetTransfer T p ho hT hp hp1 a z‖ <
      ‖resetSameHistory T p ho hT hp hp1 a ha.le ha1.le z‖ ↔ z - P₀ z ≠ 0 := by
  change ‖resetTransfer T p ho hT hp hp1 a z‖ <
    ‖(resetKernelIdentification T p ho hT hp hp1 a ha.le ha1.le).symm
      (sameHistory T p ho hT hp hp1 (Real.sqrt a) (Real.sqrt_nonneg a)
        (Real.sqrt_le_one.mpr ha1.le) z)‖ ↔ _
  rw [LinearIsometryEquiv.norm_map]
  exact reset_sameHistory_strict_iff T p ho hT hp hp1 a ha ha1 z

theorem resetSameHistory_one_mk (f : History o n → ℂ) :
    resetUnitIdentification T p ho hT hp hp1
      (resetSameHistory T p ho hT hp hp1 1 (by norm_num) (by norm_num) (mk K hK f)) =
        mk K hK f := by
  exact (congrArg (resetUnitIdentification T p ho hT hp hp1)
    (resetSameHistory_mk T p ho hT hp hp1 1 (by norm_num) (by norm_num) f)).trans
      (resetUnitIdentification_mk T p ho hT hp hp1 f)

theorem resetSameHistory_one (z : Reconstructed T ho hT p hp hp1) :
    resetUnitIdentification T p ho hT hp hp1
      (resetSameHistory T p ho hT hp hp1 1 (by norm_num) (by norm_num) z) = z := by
  obtain ⟨f,rfl⟩ := mk_surjective K hK z
  exact resetSameHistory_one_mk T p ho hT hp hp1 f

end Reset

section Phase
open FiniteThreeLevelHistoryTransfer (rotate rotate_form rotate_group rotate_zero rotate_Psi
  rotate_mean rotate_one)
variable (ω : Q → ℝ) (hω : ∀ t : ℝ, Invariant T p (rotate ω t))

/-- All-real range invariance is explicit for the group and its inverse. -/
def phaseOperator (t : ℝ) :
    Reconstructed T ho hT p hp hp1 →L[ℂ] Reconstructed T ho hT p hp hp1 :=
  (transfer T p ho hT hp hp1 (rotate ω t) (hω t)).toContinuousLinearMap

theorem phase_coordinates (t : ℝ) (z : Reconstructed T ho hT p hp hp1) :
    coordinates T ho hT p hp hp1 (phaseOperator T p ho hT hp hp1 ω hω t z) =
      rotate ω t (coordinates T ho hT p hp hp1 z) :=
  coordinates_transfer T p ho hT hp hp1 _ _ z

theorem phase_inner (t : ℝ) (z w : Reconstructed T ho hT p hp hp1) :
    ⟪phaseOperator T p ho hT hp hp1 ω hω t z,
      phaseOperator T p ho hT hp hp1 ω hω t w⟫_ℂ = ⟪z,w⟫_ℂ := by
  rw [coordinates_inner, coordinates_inner, phase_coordinates, phase_coordinates, rotate_form]

def phaseIsometry (t : ℝ) :
    Reconstructed T ho hT p hp hp1 →ₗᵢ[ℂ] Reconstructed T ho hT p hp hp1 :=
  (phaseOperator T p ho hT hp hp1 ω hω t).toLinearMap.isometryOfInner
    (phase_inner T p ho hT hp hp1 ω hω t)

theorem phase_norm (t : ℝ) (z : Reconstructed T ho hT p hp hp1) :
    ‖phaseOperator T p ho hT hp hp1 ω hω t z‖ = ‖z‖ :=
  (phaseIsometry T p ho hT hp hp1 ω hω t).norm_map z

theorem phase_group (s t : ℝ) (z : Reconstructed T ho hT p hp hp1) :
    phaseOperator T p ho hT hp hp1 ω hω s (phaseOperator T p ho hT hp hp1 ω hω t z) =
      phaseOperator T p ho hT hp hp1 ω hω (s+t) z := by
  apply coordinates_injective T ho hT p hp hp1
  rw [phase_coordinates, phase_coordinates, phase_coordinates, rotate_group]

theorem phase_zero (z : Reconstructed T ho hT p hp hp1) :
    phaseOperator T p ho hT hp hp1 ω hω 0 z = z := by
  apply coordinates_injective T ho hT p hp hp1
  rw [phase_coordinates, rotate_zero]

theorem phase_inverse (t : ℝ) (z : Reconstructed T ho hT p hp hp1) :
    phaseOperator T p ho hT hp hp1 ω hω (-t) (phaseOperator T p ho hT hp hp1 ω hω t z) = z := by
  rw [phase_group, neg_add_cancel, phase_zero]

local notation "P₀" => resetTransfer T p ho hT hp hp1 0

theorem phase_scalar (t : ℝ) (z : Reconstructed T ho hT p hp hp1) :
    phaseOperator T p ho hT hp hp1 ω hω t (P₀ z) = P₀ z := by
  apply coordinates_injective T ho hT p hp hp1
  rw [phase_coordinates, coordinates_resetTransfer]
  simp only [FiniteThreeLevelPositiveHistory.Psi_zero, map_smul, rotate_one]

theorem scalar_phase (t : ℝ) (z : Reconstructed T ho hT p hp hp1) :
    P₀ (phaseOperator T p ho hT hp hp1 ω hω t z) = P₀ z := by
  apply coordinates_injective T ho hT p hp hp1
  rw [coordinates_resetTransfer, coordinates_resetTransfer, phase_coordinates]
  simp only [FiniteThreeLevelPositiveHistory.Psi_zero]
  rw [show (rhoN * rotate ω t (coordinates T ho hT p hp hp1 z)).trace =
    (rhoN * coordinates T ho hT p hp hp1 z).trace from rotate_mean ω t _]

theorem phase_reset_commute (a t : ℝ) (z : Reconstructed T ho hT p hp hp1) :
    phaseOperator T p ho hT hp hp1 ω hω t (resetTransfer T p ho hT hp hp1 a z) =
      resetTransfer T p ho hT hp hp1 a (phaseOperator T p ho hT hp hp1 ω hω t z) := by
  apply coordinates_injective T ho hT p hp hp1
  rw [phase_coordinates, coordinates_resetTransfer, coordinates_resetTransfer, phase_coordinates, rotate_Psi]

theorem phase_adjoint_inner (t : ℝ) (z w : Reconstructed T ho hT p hp hp1) :
    ⟪phaseOperator T p ho hT hp hp1 ω hω t z,w⟫_ℂ =
      ⟪z,phaseOperator T p ho hT hp hp1 ω hω (-t) w⟫_ℂ := by
  have he := phase_inner T p ho hT hp hp1 ω hω t z
    (phaseOperator T p ho hT hp hp1 ω hω (-t) w)
  rw [phase_group, add_neg_cancel, phase_zero] at he
  exact he

theorem phase_adjoint (t : ℝ) :
    (phaseOperator T p ho hT hp hp1 ω hω t).adjoint =
      phaseOperator T p ho hT hp hp1 ω hω (-t) := by
  ext z
  apply ext_inner_left ℂ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact phase_adjoint_inner T p ho hT hp hp1 ω hω t w z

/-- Operational retention and all-real phase parameters remain independent. -/
def pulseTransfer (a t : ℝ) :
    Reconstructed T ho hT p hp hp1 →L[ℂ] Reconstructed T ho hT p hp hp1 :=
  (phaseOperator T p ho hT hp hp1 ω hω t).comp
    (resetTransfer T p ho hT hp hp1 a).toContinuousLinearMap

theorem pulse_coordinates (a t : ℝ) (z : Reconstructed T ho hT p hp hp1) :
    coordinates T ho hT p hp hp1 (pulseTransfer T p ho hT hp hp1 ω hω a t z) =
      rotate ω t (Psi a (coordinates T ho hT p hp hp1 z)) := by
  change coordinates T ho hT p hp hp1
    (phaseOperator T p ho hT hp hp1 ω hω t (resetTransfer T p ho hT hp hp1 a z)) = _
  rw [phase_coordinates, coordinates_resetTransfer]

theorem pulse_split (a t : ℝ) (z : Reconstructed T ho hT p hp hp1) :
    pulseTransfer T p ho hT hp hp1 ω hω a t z = P₀ z +
      (a : ℂ) • phaseOperator T p ho hT hp hp1 ω hω t (z - P₀ z) := by
  change phaseOperator T p ho hT hp hp1 ω hω t (resetTransfer T p ho hT hp hp1 a z) = _
  rw [resetTransfer_split, map_add, map_smul, phase_scalar]

theorem pulse_composition (a b s t : ℝ) (z : Reconstructed T ho hT p hp hp1) :
    pulseTransfer T p ho hT hp hp1 ω hω a s (pulseTransfer T p ho hT hp hp1 ω hω b t z) =
      pulseTransfer T p ho hT hp hp1 ω hω (a*b) (s+t) z := by
  apply coordinates_injective T ho hT p hp hp1
  rw [pulse_coordinates, pulse_coordinates, pulse_coordinates, ← rotate_Psi, rotate_group,
    FiniteThreeLevelPositiveHistory.Psi_comp]

theorem pulse_adjoint_inner (a t : ℝ) (z w : Reconstructed T ho hT p hp hp1) :
    ⟪pulseTransfer T p ho hT hp hp1 ω hω a t z,w⟫_ℂ =
      ⟪z,pulseTransfer T p ho hT hp hp1 ω hω a (-t) w⟫_ℂ := by
  change ⟪phaseOperator T p ho hT hp hp1 ω hω t
    (resetTransfer T p ho hT hp hp1 a z),w⟫_ℂ =
    ⟪z,phaseOperator T p ho hT hp hp1 ω hω (-t) (resetTransfer T p ho hT hp hp1 a w)⟫_ℂ
  rw [phase_adjoint_inner, phase_reset_commute]
  exact resetTransfer_symmetric T p ho hT hp hp1 a z _

theorem pulse_adjoint (a t : ℝ) : (pulseTransfer T p ho hT hp hp1 ω hω a t).adjoint =
    pulseTransfer T p ho hT hp hp1 ω hω a (-t) := by
  ext z
  apply ext_inner_left ℂ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_right, pulse_adjoint_inner]

theorem pulse_normal (a t : ℝ) :
    (pulseTransfer T p ho hT hp hp1 ω hω a t).adjoint.comp
      (pulseTransfer T p ho hT hp hp1 ω hω a t) =
    (pulseTransfer T p ho hT hp hp1 ω hω a t).comp
      (pulseTransfer T p ho hT hp hp1 ω hω a t).adjoint := by
  rw [pulse_adjoint]
  ext z
  simp only [ContinuousLinearMap.comp_apply, pulse_composition, neg_add_cancel, add_neg_cancel]

theorem pulse_norm_sq (a t : ℝ) (z : Reconstructed T ho hT p hp hp1) :
    ‖pulseTransfer T p ho hT hp hp1 ω hω a t z‖ ^ 2 =
      ‖P₀ z‖ ^ 2 + a^2 * ‖z - P₀ z‖ ^ 2 := by
  change ‖phaseOperator T p ho hT hp hp1 ω hω t (resetTransfer T p ho hT hp hp1 a z)‖ ^ 2 = _
  rw [phase_norm, reset_norm_sq]

theorem phase_selfadjoint_iff_square (t : ℝ) :
    IsSelfAdjoint (phaseOperator T p ho hT hp hp1 ω hω t) ↔
      ∀ z, phaseOperator T p ho hT hp hp1 ω hω t
        (phaseOperator T p ho hT hp hp1 ω hω t z) = z := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', phase_adjoint]
  constructor
  · intro he z
    have hi := phase_inverse T p ho hT hp hp1 ω hω t z
    rwa [he] at hi
  · intro hs
    ext z
    have he := congrArg (phaseOperator T p ho hT hp hp1 ω hω (-t)) (hs z)
    rw [phase_inverse] at he
    exact he.symm

/-- The square criterion is local to the centered range; scalar coordinates are fixed. -/
theorem phase_square_iff_centered (t : ℝ) :
    (∀ z, phaseOperator T p ho hT hp hp1 ω hω t
      (phaseOperator T p ho hT hp hp1 ω hω t z) = z) ↔
    ∀ z, P₀ z = 0 → phaseOperator T p ho hT hp hp1 ω hω t
      (phaseOperator T p ho hT hp hp1 ω hω t z) = z := by
  constructor
  · intro h z _; exact h z
  · intro h z
    have hc : P₀ (z - P₀ z) = 0 := by
      rw [map_sub]
      have hi := LinearMap.congr_fun (resetTransfer_zero_idempotent T p ho hT hp hp1) z
      change P₀ (P₀ z) = P₀ z at hi
      rw [hi, sub_self]
    have he := h (z - P₀ z) hc
    simp only [map_sub, phase_scalar] at he
    exact sub_left_injective he

theorem phase_eq_id_iff_centered (t : ℝ) :
    (∀ z, phaseOperator T p ho hT hp hp1 ω hω t z = z) ↔
    ∀ z, P₀ z = 0 → phaseOperator T p ho hT hp hp1 ω hω t z = z := by
  constructor
  · intro h z _; exact h z
  · intro h z
    have hc : P₀ (z - P₀ z) = 0 := by
      rw [map_sub]
      have hi := LinearMap.congr_fun (resetTransfer_zero_idempotent T p ho hT hp hp1) z
      change P₀ (P₀ z) = P₀ z at hi
      rw [hi, sub_self]
    have he := h (z - P₀ z) hc
    simp only [map_sub, phase_scalar] at he
    exact sub_left_injective he

/-- Cancellation here is algebraic on the quotient and asserts no physical inverse channel. -/
theorem pulse_selfadjoint_iff_phase (a t : ℝ) (ha : a ≠ 0) :
    IsSelfAdjoint (pulseTransfer T p ho hT hp hp1 ω hω a t) ↔
      IsSelfAdjoint (phaseOperator T p ho hT hp hp1 ω hω t) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', pulse_adjoint,
    ContinuousLinearMap.isSelfAdjoint_iff', phase_adjoint]
  constructor
  · intro he
    ext z
    have hz := DFunLike.congr_fun he
      (resetTransfer T p ho hT hp hp1 a⁻¹ z)
    change phaseOperator T p ho hT hp hp1 ω hω (-t)
      (resetTransfer T p ho hT hp hp1 a (resetTransfer T p ho hT hp hp1 a⁻¹ z)) =
      phaseOperator T p ho hT hp hp1 ω hω t
      (resetTransfer T p ho hT hp hp1 a (resetTransfer T p ho hT hp hp1 a⁻¹ z)) at hz
    have hr := LinearMap.congr_fun (resetTransfer_comp T p ho hT hp hp1 a a⁻¹) z
    change resetTransfer T p ho hT hp hp1 a (resetTransfer T p ho hT hp hp1 a⁻¹ z) = _ at hr
    rw [mul_inv_cancel₀ ha, resetTransfer_one] at hr
    change resetTransfer T p ho hT hp hp1 a (resetTransfer T p ho hT hp hp1 a⁻¹ z) = z at hr
    rwa [hr] at hz
  · intro he
    simp only [pulseTransfer, he]

theorem pulse_centered_norm (a t : ℝ) (z : Reconstructed T ho hT p hp hp1) :
    ‖pulseTransfer T p ho hT hp hp1 ω hω a t z - P₀ z‖ = |a| * ‖z - P₀ z‖ := by
  rw [pulse_split, add_sub_cancel_left, norm_smul, phase_norm,
    Complex.norm_real, Real.norm_eq_abs]

theorem pulse_centered_norm_bound (a t : ℝ) :
    ‖pulseTransfer T p ho hT hp hp1 ω hω a t - (P₀).toContinuousLinearMap‖ ≤ |a| := by
  apply ContinuousLinearMap.opNorm_le_bound _ (abs_nonneg a)
  intro z
  change ‖pulseTransfer T p ho hT hp hp1 ω hω a t z - P₀ z‖ ≤ |a| * ‖z‖
  rw [pulse_centered_norm]
  have hz := scalar_pythagoras T p ho hT hp hp1 z
  have hn : ‖z - P₀ z‖ ≤ ‖z‖ := by
    nlinarith [sq_nonneg ‖P₀ z‖, norm_nonneg z, norm_nonneg (z - P₀ z)]
  exact mul_le_mul_of_nonneg_left hn (abs_nonneg a)

/-- Sharp norm requires a genuine nonzero centered vector. -/
theorem pulse_centered_operator_norm (a t : ℝ)
    (hne : ∃ z : Reconstructed T ho hT p hp hp1, P₀ z = 0 ∧ z ≠ 0) :
    ‖pulseTransfer T p ho hT hp hp1 ω hω a t - (P₀).toContinuousLinearMap‖ = |a| := by
  apply le_antisymm (pulse_centered_norm_bound T p ho hT hp hp1 ω hω a t)
  obtain ⟨z,hz,hnz⟩ := hne
  have he := (pulseTransfer T p ho hT hp hp1 ω hω a t - (P₀).toContinuousLinearMap).le_opNorm z
  change ‖pulseTransfer T p ho hT hp hp1 ω hω a t z - P₀ z‖ ≤ _ at he
  rw [pulse_centered_norm, hz, sub_zero] at he
  exact (mul_le_mul_iff_left₀ (norm_pos_iff.mpr hnz)).mp he

theorem pulse_centered_operator_norm_zero (a t : ℝ)
    (hzero : ∀ z : Reconstructed T ho hT p hp hp1, P₀ z = 0 → z = 0) :
    ‖pulseTransfer T p ho hT hp hp1 ω hω a t - (P₀).toContinuousLinearMap‖ = 0 := by
  have he : pulseTransfer T p ho hT hp hp1 ω hω a t - (P₀).toContinuousLinearMap = 0 := by
    ext z
    have hc : P₀ (z - P₀ z) = 0 := by
      rw [map_sub]
      have hi := LinearMap.congr_fun (resetTransfer_zero_idempotent T p ho hT hp hp1) z
      change P₀ (P₀ z) = P₀ z at hi
      rw [hi, sub_self]
    change pulseTransfer T p ho hT hp hp1 ω hω a t z - P₀ z = 0
    rw [pulse_split, hzero _ hc, map_zero, smul_zero, add_zero, sub_self]
  rw [he, norm_zero]

/-- A positive unitary restriction is the identity. The argument tests the
negative eigendirection `z - U z` after symmetry has forced `U² = id`. -/
theorem pulse_positive_iff_phase_fixed (a t : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (pulseTransfer T p ho hT hp hp1 ω hω a t).IsPositive ↔
      ∀ z, phaseOperator T p ho hT hp hp1 ω hω t z = z := by
  constructor
  · intro hpos z
    have hs := (pulse_selfadjoint_iff_phase T p ho hT hp hp1 ω hω a t ha.ne').mp
      hpos.isSelfAdjoint
    have hsq := (phase_selfadjoint_iff_square T p ho hT hp hp1 ω hω t).mp hs
    let y := z - phaseOperator T p ho hT hp hp1 ω hω t z
    have hpy : P₀ y = 0 := by
      dsimp [y]
      rw [map_sub, scalar_phase, sub_self]
    have huy : phaseOperator T p ho hT hp hp1 ω hω t y = -y := by
      dsimp [y]
      rw [map_sub, hsq]
      abel
    have hty : pulseTransfer T p ho hT hp hp1 ω hω a t y = -(a : ℂ) • y := by
      rw [pulse_split, hpy, sub_zero, zero_add, huy, smul_neg, neg_smul]
    have hn := hpos.re_inner_nonneg_left y
    change 0 ≤ (⟪pulseTransfer T p ho hT hp hp1 ω hω a t y,y⟫_ℂ).re at hn
    rw [hty, inner_smul_left] at hn
    simp only [map_neg, Complex.conj_ofReal, neg_mul, Complex.neg_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hn
    have hy : 0 ≤ (⟪y,y⟫_ℂ).re := inner_self_nonneg (𝕜 := ℂ) (x := y)
    have hy0 : ‖y‖ ^ 2 = 0 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
      change (⟪y,y⟫_ℂ).re = 0
      nlinarith
    have hyz : y = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg y])
    exact (sub_eq_zero.mp hyz).symm
  · intro hfix
    have he : pulseTransfer T p ho hT hp hp1 ω hω a t =
        (resetTransfer T p ho hT hp hp1 a).toContinuousLinearMap := by
      ext z
      exact hfix (resetTransfer T p ho hT hp hp1 a z)
    rw [he]
    exact reset_positive T p ho hT hp hp1 a ha.le ha1

open scoped Matrix.Norms.L2Operator

/-- Finite dimensionality makes the exact coordinate range closed. -/
theorem accessible_closed : IsClosed (accessible T p : Set MatQ) :=
  (accessible T p).closed_of_finiteDimensional

/-- A continuous extension of the inverse coordinates, used only on the actual
range or its differentiated all-real orbit. -/
def coordinateRecovery : MatQ →L[ℂ] Reconstructed T ho hT p hp hp1 :=
  (coordinates T ho hT p hp hp1).leftInverse.toContinuousLinearMap

theorem recovery_coordinates (z : Reconstructed T ho hT p hp hp1) :
    coordinateRecovery T p ho hT hp hp1 (coordinates T ho hT p hp hp1 z) = z :=
  LinearMap.leftInverse_apply_of_inj
    (LinearMap.ker_eq_bot.mpr (coordinates_injective T ho hT p hp hp1)) z

def generator (γ : ℝ) :
    Reconstructed T ho hT p hp hp1 →L[ℂ] Reconstructed T ho hT p hp hp1 :=
  (coordinateRecovery T p ho hT hp hp1).comp
    ((FiniteThreeLevelHistoryTransfer.generatorMatrix ω γ).comp
      (coordinates T ho hT p hp hp1)).toContinuousLinearMap

theorem pulse_recovery (γ t : ℝ) (z : Reconstructed T ho hT p hp hp1) :
    pulseTransfer T p ho hT hp hp1 ω hω (Real.exp (-γ*t)) t z =
      coordinateRecovery T p ho hT hp hp1
        (FiniteThreeLevelHistoryTransfer.matrixOrbit ω γ t (coordinates T ho hT p hp hp1 z)) := by
  rw [← recovery_coordinates T p ho hT hp hp1
    (pulseTransfer T p ho hT hp hp1 ω hω (Real.exp (-γ*t)) t z), pulse_coordinates]
  rfl

/-- Differentiation uses the continuous finite-dimensional inverse extension;
the entire orbit has exact coordinates in the invariant range. -/
theorem orbit_hasDerivAt (γ t : ℝ) (z : Reconstructed T ho hT p hp hp1) :
    HasDerivAt (fun s : ℝ => pulseTransfer T p ho hT hp hp1 ω hω (Real.exp (-γ*s)) s z)
      (generator T p ho hT hp hp1 ω γ
        (pulseTransfer T p ho hT hp hp1 ω hω (Real.exp (-γ*t)) t z)) t := by
  have hd := ((coordinateRecovery T p ho hT hp hp1).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t
    (FiniteThreeLevelHistoryTransfer.matrixOrbit_hasDerivAt ω γ t
      (coordinates T ho hT p hp hp1 z))
  simp only [pulse_recovery]
  convert hd using 1
  · rfl
  · change coordinateRecovery T p ho hT hp hp1
      (FiniteThreeLevelHistoryTransfer.generatorMatrix ω γ
        (coordinates T ho hT p hp hp1
          (coordinateRecovery T p ho hT hp hp1
            (FiniteThreeLevelHistoryTransfer.matrixOrbit ω γ t
              (coordinates T ho hT p hp hp1 z))))) = _
    rw [← pulse_recovery T p ho hT hp hp1 ω hω γ t z, pulse_coordinates]
    rfl

theorem thermal_zero (γ : ℝ) (z : Reconstructed T ho hT p hp hp1) :
    pulseTransfer T p ho hT hp hp1 ω hω (Real.exp (-γ*0)) 0 z = z := by
  apply coordinates_injective T ho hT p hp hp1
  rw [pulse_coordinates, rotate_zero]
  simp only [mul_zero, Real.exp_zero, FiniteThreeLevelPositiveHistory.Psi_one]

include hω in
/-- Uniqueness of the ambient derivative proves that the generator stays in the
closed accessible range; no generator-invariance premise is assumed. -/
theorem generator_coordinates (γ : ℝ) (z : Reconstructed T ho hT p hp hp1) :
    coordinates T ho hT p hp hp1 (generator T p ho hT hp hp1 ω γ z) =
      FiniteThreeLevelHistoryTransfer.generatorMatrix ω γ (coordinates T ho hT p hp hp1 z) := by
  have hd := (((coordinates T ho hT p hp hp1).toContinuousLinearMap).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt 0
    (orbit_hasDerivAt T p ho hT hp hp1 ω hω γ 0 z)
  have hm := FiniteThreeLevelHistoryTransfer.matrixOrbit_hasDerivAt ω γ 0
    (coordinates T ho hT p hp hp1 z)
  have hfun : (fun s : ℝ => coordinates T ho hT p hp hp1
      (pulseTransfer T p ho hT hp hp1 ω hω (Real.exp (-γ*s)) s z)) =
      (fun s => FiniteThreeLevelHistoryTransfer.matrixOrbit ω γ s
        (coordinates T ho hT p hp hp1 z)) := by
    funext s
    exact pulse_coordinates T p ho hT hp hp1 ω hω _ _ z
  change HasDerivAt (fun s : ℝ => coordinates T ho hT p hp hp1
      (pulseTransfer T p ho hT hp hp1 ω hω (Real.exp (-γ*s)) s z))
      (coordinates T ho hT p hp hp1 (generator T p ho hT hp hp1 ω γ
        (pulseTransfer T p ho hT hp hp1 ω hω (Real.exp (-γ*0)) 0 z))) 0 at hd
  rw [thermal_zero, hfun] at hd
  have he := hd.unique hm
  simpa only [FiniteThreeLevelHistoryTransfer.matrixOrbit, rotate_zero, mul_zero,
    Real.exp_zero, FiniteThreeLevelPositiveHistory.Psi_one] using he

include ho hT hp hp1 hω in
theorem generator_invariant (γ : ℝ) :
    Invariant T p (FiniteThreeLevelHistoryTransfer.generatorMatrix ω γ) :=
  invariant_of_coordinates T p ho hT hp hp1
    (generator T p ho hT hp hp1 ω γ).toLinearMap
    (generator_coordinates T p ho hT hp hp1 ω hω γ)

theorem physical_right_derivative (γ : ℝ) (z : Reconstructed T ho hT p hp hp1) :
    HasDerivWithinAt
      (fun t : ℝ => pulseTransfer T p ho hT hp hp1 ω hω (Real.exp (-γ*t)) t z)
      (generator T p ho hT hp hp1 ω γ z) (Set.Ici 0) 0 := by
  have hd := (orbit_hasDerivAt T p ho hT hp hp1 ω hω γ 0 z).hasDerivWithinAt (s := Set.Ici 0)
  rwa [thermal_zero] at hd

end Phase

section PhysicalInsertion
open FinitePositiveKernel.GibbsObservable
open FiniteThreeLevelHistoryTransfer (rotate pulseResetKraus pulseReset_normalized
  pulseReset_observable pulseReset_commutes)

/-- The kernel is the weight of the already defined normalized inserted tree. -/
def pulseKernel (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ) :
    Matrix (History o n) (History o n) ℂ :=
  insertedKernel T p ho hT hp hp1 (pulseResetKraus a ω t)
    (pulseReset_normalized a ha ha1 ω t)

theorem pulseKernel_form (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ)
    (u v : History o n) :
    pulseKernel T p ho hT hp hp1 a ha ha1 ω t u v =
      form (Psi p (effect T u)) (rotate ω t (Psi a (Psi p (effect T v)))) := by
  rw [pulseKernel, insertedKernel_form T p ho hT hp hp1 _ _
    (pulseReset_commutes a ha ha1 ω t p), pulseReset_observable a ha ha1]

theorem pulseKernel_pairing (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ)
    (f g : History o n → ℂ) :
    pairing (pulseKernel T p ho hT hp hp1 a ha ha1 ω t) f g =
      form (synthesis T p f) (rotate ω t (Psi a (synthesis T p g))) := by
  rw [pulseKernel, inserted_pairing_form T p ho hT hp hp1 _ _
    (pulseReset_commutes a ha ha1 ω t p), pulseReset_observable a ha ha1]

theorem pulseKernel_old_inner (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ)
    (hω : ∀ t : ℝ, Invariant T p (rotate ω t)) (t : ℝ) (f g : History o n → ℂ) :
    pairing (pulseKernel T p ho hT hp hp1 a ha ha1 ω t) f g =
      ⟪mk K hK f, pulseTransfer T p ho hT hp hp1 ω hω a t (mk K hK g)⟫_ℂ := by
  rw [pulseKernel_pairing, coordinates_inner, pulse_coordinates, coordinates_mk, coordinates_mk]

theorem pulseKernel_hermitian_iff (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ)
    (hω : ∀ t : ℝ, Invariant T p (rotate ω t)) (t : ℝ) :
    (pulseKernel T p ho hT hp hp1 a ha ha1 ω t).IsHermitian ↔
      IsSelfAdjoint (pulseTransfer T p ho hT hp hp1 ω hω a t) := by
  classical
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  constructor
  · intro hh z w
    obtain ⟨f,rfl⟩ := mk_surjective K hK z
    obtain ⟨g,rfl⟩ := mk_surjective K hK w
    change ⟪pulseTransfer T p ho hT hp hp1 ω hω a t (mk K hK f), mk K hK g⟫_ℂ =
      ⟪mk K hK f, pulseTransfer T p ho hT hp hp1 ω hω a t (mk K hK g)⟫_ℂ
    rw [← inner_conj_symm, ← pulseKernel_old_inner T p ho hT hp hp1 a ha ha1 ω hω t,
      ← pulseKernel_old_inner T p ho hT hp hp1 a ha ha1 ω hω t]
    change star (star g ⬝ᵥ (pulseKernel T p ho hT hp hp1 a ha ha1 ω t *ᵥ f)) = _
    rw [← star_dotProduct, star_mulVec, hh.eq]
    exact (dotProduct_mulVec (star f) (pulseKernel T p ho hT hp hp1 a ha ha1 ω t) g).symm
  · intro hs
    apply Matrix.IsHermitian.ext
    intro u v
    have he := hs (mk K hK (Pi.single u 1)) (mk K hK (Pi.single v 1))
    change ⟪pulseTransfer T p ho hT hp hp1 ω hω a t (mk K hK (Pi.single u 1)),
      mk K hK (Pi.single v 1)⟫_ℂ =
      ⟪mk K hK (Pi.single u 1),pulseTransfer T p ho hT hp hp1 ω hω a t
        (mk K hK (Pi.single v 1))⟫_ℂ at he
    rw [← inner_conj_symm, ← pulseKernel_old_inner T p ho hT hp hp1 a ha ha1 ω hω t,
      ← pulseKernel_old_inner T p ho hT hp hp1 a ha ha1 ω hω t] at he
    simpa [pairing, Matrix.mulVec, dotProduct, Pi.single_apply] using he

theorem pulseKernel_positive_iff_operator (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ)
    (hω : ∀ t : ℝ, Invariant T p (rotate ω t)) (t : ℝ) :
    (pulseKernel T p ho hT hp hp1 a ha ha1 ω t).PosSemidef ↔
      (pulseTransfer T p ho hT hp hp1 ω hω a t).IsPositive := by
  constructor
  · intro hk
    refine ⟨((pulseKernel_hermitian_iff T p ho hT hp hp1 a ha ha1 ω hω t).mp
      hk.isHermitian).isSymmetric, ?_⟩
    intro z
    obtain ⟨f,rfl⟩ := mk_surjective K hK z
    have hn := (hk.dotProduct_mulVec_nonneg f).1
    change 0 ≤ (pairing (pulseKernel T p ho hT hp hp1 a ha ha1 ω t) f f).re at hn
    rw [pulseKernel_old_inner T p ho hT hp hp1 a ha ha1 ω hω t] at hn
    change 0 ≤ (⟪pulseTransfer T p ho hT hp hp1 ω hω a t (mk K hK f), mk K hK f⟫_ℂ).re
    rw [← inner_conj_symm, Complex.conj_re]
    exact hn
  · intro ht
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · exact (pulseKernel_hermitian_iff T p ho hT hp hp1 a ha ha1 ω hω t).mpr ht.isSelfAdjoint
    · intro f
      change 0 ≤ pairing (pulseKernel T p ho hT hp hp1 a ha ha1 ω t) f f
      rw [pulseKernel_old_inner T p ho hT hp hp1 a ha ha1 ω hω t]
      exact ht.inner_nonneg_right _

/-- Hermiticity is determined on the actual centered range, including vacuous scalar cases. -/
theorem pulseKernel_hermitian_iff_centered_square
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (ω : Q → ℝ)
    (hω : ∀ t : ℝ, Invariant T p (rotate ω t)) (t : ℝ) :
    (pulseKernel T p ho hT hp hp1 a ha.le ha1 ω t).IsHermitian ↔
      ∀ z, resetTransfer T p ho hT hp hp1 0 z = 0 →
        phaseOperator T p ho hT hp hp1 ω hω t
          (phaseOperator T p ho hT hp hp1 ω hω t z) = z := by
  rw [pulseKernel_hermitian_iff T p ho hT hp hp1 a ha.le ha1 ω hω t,
    pulse_selfadjoint_iff_phase T p ho hT hp hp1 ω hω a t ha.ne',
    phase_selfadjoint_iff_square, phase_square_iff_centered]

theorem pulseKernel_positive_iff_centered_fixed
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (ω : Q → ℝ)
    (hω : ∀ t : ℝ, Invariant T p (rotate ω t)) (t : ℝ) :
    (pulseKernel T p ho hT hp hp1 a ha.le ha1 ω t).PosSemidef ↔
      ∀ z, resetTransfer T p ho hT hp hp1 0 z = 0 →
        phaseOperator T p ho hT hp hp1 ω hω t z = z := by
  rw [pulseKernel_positive_iff_operator T p ho hT hp hp1 a ha.le ha1 ω hω t,
    pulse_positive_iff_phase_fixed T p ho hT hp hp1 ω hω a t ha ha1,
    phase_eq_id_iff_centered]

theorem pulse_stationary (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ) :
    krausMap (pulseResetKraus a ω t) rhoN = rhoN := by
  rw [FiniteThreeLevelHistoryTransfer.pulseReset_state a ha ha1]
  have he : Phi a rhoN = rhoN := by
    simp only [Phi, FiniteThreeLevelPositiveHistory.rhoN_trace, one_smul]
    module
  rw [he]
  exact FiniteThreeLevelHistoryTransfer.rotate_diagonal ω (-t) _

theorem pulseKernel_eq_reset_of_fixed (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (ω : Q → ℝ) (t : ℝ)
    (hfix : ∀ A ∈ accessible T p, rotate ω t A = A) :
    pulseKernel T p ho hT hp hp1 a ha ha1 ω t =
      kernel T ho hT (p * Real.sqrt a) (mul_nonneg hp (Real.sqrt_nonneg a))
        (mul_le_one₀ hp1 (Real.sqrt_nonneg a) (Real.sqrt_le_one.mpr ha1)) := by
  rw [← reset_inserted_eq_original T p ho hT hp hp1 a ha ha1]
  ext u v
  rw [pulseKernel_form]
  have hm : Psi p (effect T v) ∈ accessible T p := Submodule.subset_span ⟨v,rfl⟩
  have hma : Psi a (Psi p (effect T v)) ∈ accessible T p := reset_invariant T p a _ hm
  rw [hfix _ hma]
  rw [insertedKernel_form T p ho hT hp hp1 _ _ (by
    intro A
    simp only [FiniteThreeLevelPositiveHistory.channel_observable ha ha1,
      FiniteThreeLevelPositiveHistory.Psi_comp]
    rw [mul_comm a p]), FiniteThreeLevelPositiveHistory.channel_observable ha ha1]

theorem pulseKernel_positive_of_fixed (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (ω : Q → ℝ) (t : ℝ)
    (hfix : ∀ A ∈ accessible T p, rotate ω t A = A) :
    (pulseKernel T p ho hT hp hp1 a ha ha1 ω t).PosSemidef := by
  rw [pulseKernel_eq_reset_of_fixed T p ho hT hp hp1 a ha ha1 ω t hfix]
  exact kernel_posSemidef T ho hT _ _ _

theorem pulseKernel_zero (ω : Q → ℝ) (t : ℝ) :
    pulseKernel T p ho hT hp hp1 0 (by norm_num) (by norm_num) ω t = massKernel T := by
  ext u v
  rw [pulseKernel_form, FiniteThreeLevelPositiveHistory.Psi_zero,
    map_smul, FiniteThreeLevelHistoryTransfer.rotate_one]
  have he := pulseKernel_form T p ho hT hp hp1 0 (by norm_num) (by norm_num)
    ω 0 u v
  rw [FiniteThreeLevelHistoryTransfer.rotate_zero] at he
  rw [← FiniteThreeLevelPositiveHistory.Psi_zero, ← he,
    pulseKernel_eq_reset_of_fixed T p ho hT hp hp1 0 (by norm_num) (by norm_num)
      ω 0 (fun A _ => FiniteThreeLevelHistoryTransfer.rotate_zero ω A)]
  simpa only [Real.sqrt_zero, mul_zero, massKernel] using reset_kernel T ho hT u v

theorem pulseKernel_column (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ)
    (v : History o n) :
    (∑ u, pulseKernel T p ho hT hp hp1 a ha ha1 ω t u v) = (mass T v : ℂ) :=
  insertedKernel_column_sum T p ho hT hp hp1 _ _ (pulse_stationary a ha ha1 ω t) v

def thermalKernel (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    Matrix (History o n) (History o n) ℂ :=
  insertedKernel T p ho hT hp hp1 (FiniteThreeLevelThermalPhase.channelKraus b ℏ γ t)
    (FiniteThreeLevelThermalPhase.channel_normalized b ℏ γ t hγ ht)

/-- Equality follows from the actual state-channel action on every complex input. -/
theorem thermalKernel_eq_pulse (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    thermalKernel T p ho hT hp hp1 b ℏ γ t hγ ht =
      pulseKernel T p ho hT hp hp1 (Real.exp (-γ*t)) (Real.exp_pos _).le
        (GibbsReset.exp_rate_le_one γ t hγ ht) (FiniteThreeLevelThermalPhase.frequencies b ℏ) t := by
  ext u v
  simp only [thermalKernel, pulseKernel, insertedKernel_trace,
    FiniteThreeLevelHistoryTransfer.thermal_state_pulse b ℏ γ t hγ ht]

theorem thermalKernel_column (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (v : History o n) :
    (∑ u, thermalKernel T p ho hT hp hp1 b ℏ γ t hγ ht u v) = (mass T v : ℂ) :=
  insertedKernel_column_sum T p ho hT hp hp1 _ _
    (FiniteThreeLevelThermalPhase.channel_stationary b ℏ γ t hγ ht) v

theorem thermal_coordinates (b ℏ γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (hω : ∀ s : ℝ, Invariant T p (rotate (FiniteThreeLevelThermalPhase.frequencies b ℏ) s))
    (z : Reconstructed T ho hT p hp hp1) :
    coordinates T ho hT p hp hp1
      (pulseTransfer T p ho hT hp hp1 (FiniteThreeLevelThermalPhase.frequencies b ℏ)
        hω (Real.exp (-γ*t)) t z) =
    Channel.heisenberg (FiniteThreeLevelThermalPhase.channelKraus b ℏ γ t)
      (coordinates T ho hT p hp hp1 z) := by
  rw [pulse_coordinates, FiniteThreeLevelHistoryTransfer.thermal_observable_matrix b ℏ γ t hγ ht]

theorem thermal_generator_sign (b ℏ γ : ℝ)
    (hω : ∀ s : ℝ, Invariant T p (rotate (FiniteThreeLevelThermalPhase.frequencies b ℏ) s))
    (z : Reconstructed T ho hT p hp hp1) :
    coordinates T ho hT p hp hp1
      (generator T p ho hT hp hp1 (FiniteThreeLevelThermalPhase.frequencies b ℏ) γ z) =
    Complex.I • (FiniteThreeLevelThermalPhase.scaledH b ℏ * coordinates T ho hT p hp hp1 z -
      coordinates T ho hT p hp hp1 z * FiniteThreeLevelThermalPhase.scaledH b ℏ) +
      (γ : ℂ) • (FiniteThreeLevelHistoryTransfer.mean (coordinates T ho hT p hp hp1 z) • 1 -
        coordinates T ho hT p hp hp1 z) := by
  rw [generator_coordinates T p ho hT hp hp1 _ hω,
    FiniteThreeLevelHistoryTransfer.observable_generator_actual]
  rfl

theorem thermal_generator_duality (b ℏ γ : ℝ) (hγ : 0 ≤ γ)
    (hω : ∀ s : ℝ, Invariant T p (rotate (FiniteThreeLevelThermalPhase.frequencies b ℏ) s))
    (z : Reconstructed T ho hT p hp hp1) (X : MatQ) :
    (coordinates T ho hT p hp hp1
      (generator T p ho hT hp hp1 (FiniteThreeLevelThermalPhase.frequencies b ℏ) γ z) * X).trace =
    (coordinates T ho hT p hp hp1 z * OpenSystems.lindbladGenerator
      (FiniteThreeLevelThermalPhase.scaledH b ℏ) (FiniteThreeLevelThermalPhase.jumps γ) X).trace := by
  rw [generator_coordinates T p ho hT hp hp1 _ hω]
  exact FiniteThreeLevelHistoryTransfer.generator_trace_duality b ℏ γ hγ _ X

end PhysicalInsertion

section FullRangeControls
open FiniteThreeLevelHistoryTransfer (rotate multiplier)
open FiniteThreeLevelPositiveHistory (E metricWeight)

theorem pulseKernel_unit_pairing (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ)
    {i j : Q} (hij : i ≠ j) (f : History o n → ℂ) (hf : synthesis T p f = E i j) :
    pairing (pulseKernel T p ho hT hp hp1 a ha ha1 ω t) f f =
      ((a * metricWeight i j : ℝ) : ℂ) * multiplier ω t i j := by
  rw [pulseKernel_pairing, hf]
  have he := FiniteThreeLevelHistoryTransfer.observable_unit a ω t 1 hij
  simp only [one_smul, mul_one] at he
  rw [he, FiniteThreeLevelHistoryTransfer.form_smul_right,
    FiniteThreeLevelPositiveHistory.matrixUnit_form]
  simp only [Complex.ofReal_mul]
  ring

/-- Ambient multiplier criteria require a proof of the entire accessible range. -/
theorem full_hermitian_necessary (hfull : accessible T p = ⊤)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ)
    (hk : (pulseKernel T p ho hT hp hp1 a ha.le ha1 ω t).IsHermitian) :
    ∀ i j, (multiplier ω t i j).im = 0 := by
  intro i j
  by_cases hij : i = j
  · subst j
    rw [FiniteThreeLevelHistoryTransfer.multiplier_diag]
    rfl
  · have hm : E i j ∈ (synthesisLinear T p).range := by
      rw [synthesis_range, hfull]; exact Submodule.mem_top
    obtain ⟨f,hf⟩ := hm
    have he := FiniteThreeLevelHistoryTransfer.hermitian_pairing_conj hk f f
    rw [pulseKernel_unit_pairing T p ho hT hp hp1 a ha.le ha1 ω t hij f hf] at he
    have hi := congrArg Complex.im he
    simp only [Complex.star_def, Complex.conj_im, Complex.mul_im, Complex.ofReal_im,
      Complex.ofReal_re, zero_mul, add_zero] at hi
    have hc := mul_pos ha (FiniteThreeLevelHistoryTransfer.metricWeight_positive i j)
    nlinarith

theorem ambient_hermitian_sufficient (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (ω : Q → ℝ) (t : ℝ) (hreal : ∀ i j, (multiplier ω t i j).im = 0) :
    (pulseKernel T p ho hT hp hp1 a ha ha1 ω t).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro u v
  rw [pulseKernel_form, pulseKernel_form, FiniteThreeLevelHistoryTransfer.form_conj,
    FiniteThreeLevelHistoryTransfer.rotate_form_adjoint,
    ← FiniteThreeLevelPositiveHistory.form_Psi_symmetric,
    ← FiniteThreeLevelHistoryTransfer.rotate_Psi,
    FiniteThreeLevelHistoryTransfer.rotate_reverse_of_real ω t hreal]

theorem full_positive_necessary (hfull : accessible T p = ⊤)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ)
    (hk : (pulseKernel T p ho hT hp hp1 a ha.le ha1 ω t).PosSemidef) :
    ∀ i j, multiplier ω t i j = 1 := by
  intro i j
  by_cases hij : i = j
  · subst j; exact FiniteThreeLevelHistoryTransfer.multiplier_diag ω t i
  · have hi := full_hermitian_necessary T p ho hT hp hp1 hfull a ha ha1 ω t hk.isHermitian i j
    have hm : E i j ∈ (synthesisLinear T p).range := by
      rw [synthesis_range, hfull]; exact Submodule.mem_top
    obtain ⟨f,hf⟩ := hm
    have hn := (hk.dotProduct_mulVec_nonneg f).1
    change 0 ≤ (pairing (pulseKernel T p ho hT hp hp1 a ha.le ha1 ω t) f f).re at hn
    rw [pulseKernel_unit_pairing T p ho hT hp hp1 a ha.le ha1 ω t hij f hf] at hn
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hn
    have hc := mul_pos ha (FiniteThreeLevelHistoryTransfer.metricWeight_positive i j)
    have hr : 0 ≤ (multiplier ω t i j).re := by nlinarith
    have he : multiplier ω t i j = ((multiplier ω t i j).re : ℂ) := by
      apply Complex.ext <;> simp [hi]
    have hn1 := FiniteThreeLevelHistoryTransfer.multiplier_norm ω t i j
    rw [he, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr] at hn1
    rw [he, hn1, Complex.ofReal_one]

theorem ambient_positive_sufficient (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (ω : Q → ℝ) (t : ℝ) (hone : ∀ i j, multiplier ω t i j = 1) :
    (pulseKernel T p ho hT hp hp1 a ha ha1 ω t).PosSemidef := by
  apply pulseKernel_positive_of_fixed T p ho hT hp hp1 a ha ha1 ω t
  intro A _
  ext i j
  rw [FiniteThreeLevelHistoryTransfer.rotate_entry]
  change multiplier ω t i j * A i j = A i j
  rw [hone, one_mul]

theorem full_pulse_hermitian_iff (hfull : accessible T p = ⊤)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ) :
    (pulseKernel T p ho hT hp hp1 a ha.le ha1 ω t).IsHermitian ↔
      ∀ i j, (multiplier ω t i j).im = 0 :=
  ⟨full_hermitian_necessary T p ho hT hp hp1 hfull a ha ha1 ω t,
    ambient_hermitian_sufficient T p ho hT hp hp1 a ha.le ha1 ω t⟩

theorem full_pulse_positive_iff (hfull : accessible T p = ⊤)
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) (ω : Q → ℝ) (t : ℝ) :
    (pulseKernel T p ho hT hp hp1 a ha.le ha1 ω t).PosSemidef ↔
      ∀ i j, multiplier ω t i j = 1 :=
  ⟨full_positive_necessary T p ho hT hp hp1 hfull a ha ha1 ω t,
    ambient_positive_sufficient T p ho hT hp hp1 a ha.le ha1 ω t⟩

end FullRangeControls

section PhysicalDerivative
open scoped Matrix.Norms.L2Operator
open FinitePositiveKernel.GibbsObservable
open FiniteThreeLevelHistoryTransfer (rotate)

/-- Only the nonnegative-time restriction is identified with a normalized
physical channel. The ambient algebraic formula supplies no negative-time channel claim. -/
theorem actual_thermal_right_derivative (b ℏ γ : ℝ) (hγ : 0 ≤ γ)
    (hω : ∀ s : ℝ, Invariant T p (rotate (FiniteThreeLevelThermalPhase.frequencies b ℏ) s))
    (z : Reconstructed T ho hT p hp hp1) :
    HasDerivWithinAt
      (fun t : ℝ => coordinateRecovery T p ho hT hp hp1
        (Channel.heisenberg (FiniteThreeLevelThermalPhase.channelKraus b ℏ γ t)
          (coordinates T ho hT p hp hp1 z)))
      (generator T p ho hT hp hp1 (FiniteThreeLevelThermalPhase.frequencies b ℏ) γ z)
      (Set.Ici 0) 0 := by
  apply (physical_right_derivative T p ho hT hp hp1 _ hω γ z).congr_of_mem
  · intro t ht
    rw [← thermal_coordinates T p ho hT hp hp1 b ℏ γ t hγ ht hω z, recovery_coordinates]
  · change (0 : ℝ) ≤ 0
    exact le_rfl

end PhysicalDerivative

section Modular
open FiniteThreeLevelHistoryTransfer (rotate)
open FiniteThreeLevelThermalPhase (thermalH frequencies thermalH_hermitian)

/-- This linear map evaluates the independently defined Gibbs modular action. -/
def modularLinear (b s : ℝ) : MatQ →ₗ[ℂ] MatQ where
  toFun := FiniteGibbsClock.modular (thermalH_hermitian b) b s
  map_add' := FiniteGibbsClock.modular_add (thermalH_hermitian b) b s
  map_smul' := FiniteGibbsClock.modular_smul (thermalH_hermitian b) b s

theorem modular_eq_rotate (b ℏ s : ℝ) (hℏ : 0 < ℏ) (A : MatQ) :
    modularLinear b s A = rotate (frequencies b ℏ) (-b * ℏ * s) A := by
  change FiniteGibbsClock.modular (thermalH_hermitian b) b s A = _
  rw [FiniteGibbsClock.modular_eq_heisenberg _ b s ℏ hℏ]
  have he := FiniteThreeLevelThermalPhase.phase_physical b ℏ (b * ℏ * s) hℏ A
  simpa only [FiniteThreeLevelThermalPhase.phase, rotate, LinearMap.coe_mk,
    AddHom.coe_mk, neg_mul, neg_neg] using he.symm

theorem modular_invariant (b ℏ s : ℝ) (hℏ : 0 < ℏ)
    (hω : ∀ t : ℝ, Invariant T p (rotate (frequencies b ℏ) t)) :
    Invariant T p (modularLinear b s) := by
  intro A hA
  rw [modular_eq_rotate b ℏ s hℏ]
  exact hω _ A hA

/-- Parameter comparison on the actual strategy quotient, not a second
full-matrix reconstruction and not an elapsed-time calibration. -/
theorem modular_strategy_coordinates (b ℏ s : ℝ) (hℏ : 0 < ℏ)
    (hω : ∀ t : ℝ, Invariant T p (rotate (frequencies b ℏ) t))
    (z : Reconstructed T ho hT p hp hp1) :
    coordinates T ho hT p hp hp1
      (transfer T p ho hT hp hp1 (modularLinear b s) (modular_invariant T p b ℏ s hℏ hω) z) =
    rotate (frequencies b ℏ) (-b * ℏ * s) (coordinates T ho hT p hp hp1 z) := by
  rw [coordinates_transfer, modular_eq_rotate b ℏ s hℏ]

/-- Equal equilibrium states coexist with different energy gaps. -/
theorem equilibrium_does_not_select_gap {b c : ℝ} (hb : 0 < b) (hc : 0 < c) (hne : b ≠ c) :
    FiniteGibbsClock.gibbs (thermalH b) b = FiniteGibbsClock.gibbs (thermalH c) c ∧
      FiniteThreeLevelThermalPhase.energies b 1 ≠ FiniteThreeLevelThermalPhase.energies c 1 :=
  ⟨FiniteThreeLevelThermalPhase.gibbs_two_scales hb hc,
    FiniteThreeLevelThermalPhase.gap_scales_ne hb hc hne⟩

end Modular

section EndpointConsumers
open FiniteThreeLevelHistoryTransfer (mean meanLinear rotate)
open FinitePositiveKernel.GibbsObservable

/-- The centered physical range is the accessible range intersected with the mean kernel. -/
def centeredRange : Submodule ℂ MatQ := accessible T p ⊓ meanLinear.ker

theorem centered_coordinates_iff (z : Reconstructed T ho hT p hp hp1) :
    resetTransfer T p ho hT hp hp1 0 z = 0 ↔
      mean (coordinates T ho hT p hp hp1 z) = 0 := by
  constructor
  · intro hz
    have he := congrArg (coordinates T ho hT p hp hp1) hz
    rw [coordinates_resetTransfer, map_zero, FiniteThreeLevelPositiveHistory.Psi_zero] at he
    have hm := congrArg mean he
    change meanLinear (_ • (1 : MatQ)) = meanLinear 0 at hm
    rw [map_smul, map_zero] at hm
    simpa only [meanLinear, LinearMap.coe_mk, AddHom.coe_mk, mean,
      Matrix.mul_one, FiniteThreeLevelPositiveHistory.rhoN_trace, smul_eq_mul, mul_one] using hm
  · intro hm
    apply coordinates_injective T ho hT p hp hp1
    rw [coordinates_resetTransfer, map_zero, FiniteThreeLevelPositiveHistory.Psi_zero]
    change mean (coordinates T ho hT p hp hp1 z) • (1 : MatQ) = 0
    rw [hm, zero_smul]

theorem centeredRange_coordinates :
    ∀ A, A ∈ centeredRange T p ↔ ∃ z : Reconstructed T ho hT p hp hp1,
      resetTransfer T p ho hT hp hp1 0 z = 0 ∧ coordinates T ho hT p hp hp1 z = A := by
  intro A
  constructor
  · rintro ⟨hA,hm⟩
    rw [← coordinates_range T ho hT p hp hp1] at hA
    obtain ⟨z,rfl⟩ := hA
    exact ⟨z,(centered_coordinates_iff T p ho hT hp hp1 z).mpr hm,rfl⟩
  · rintro ⟨z,hz,rfl⟩
    refine ⟨?_,(centered_coordinates_iff T p ho hT hp hp1 z).mp hz⟩
    rw [← coordinates_range T ho hT p hp hp1]
    exact ⟨z,rfl⟩

theorem phase_fixed_of_scalar (hs : accessible T p = Submodule.span ℂ {(1 : MatQ)})
    (ω : Q → ℝ) (t : ℝ) (A : MatQ) (hA : A ∈ accessible T p) : rotate ω t A = A := by
  rw [hs] at hA
  obtain ⟨c,rfl⟩ := Submodule.mem_span_singleton.mp hA
  rw [map_smul, FiniteThreeLevelHistoryTransfer.rotate_one]

theorem centeredRange_eq_bot_iff : centeredRange T p = ⊥ ↔
    ∀ z : Reconstructed T ho hT p hp hp1, resetTransfer T p ho hT hp hp1 0 z = 0 → z = 0 := by
  constructor
  · intro hb z hz
    have hm := (centeredRange_coordinates T p ho hT hp hp1 _).mpr ⟨z,hz,rfl⟩
    rw [hb, Submodule.mem_bot] at hm
    apply coordinates_injective T ho hT p hp hp1
    simpa only [map_zero] using hm
  · intro hz
    apply le_antisymm _ bot_le
    intro A hA
    obtain ⟨z,hz0,rfl⟩ := (centeredRange_coordinates T p ho hT hp hp1 A).mp hA
    rw [hz z hz0, map_zero]
    exact Submodule.zero_mem _

/-- The sharp operator norm is stated on the physical centered range, with its
zero-dimensional exception explicit. -/
theorem pulse_centered_norm_of_range (ω : Q → ℝ) (hω : ∀ t, Invariant T p (rotate ω t))
    (a t : ℝ) (ha : 0 ≤ a) (hne : centeredRange T p ≠ ⊥) :
    ‖pulseTransfer T p ho hT hp hp1 ω hω a t -
      (resetTransfer T p ho hT hp hp1 0).toContinuousLinearMap‖ = a := by
  have hw : ∃ z : Reconstructed T ho hT p hp hp1,
      resetTransfer T p ho hT hp hp1 0 z = 0 ∧ z ≠ 0 := by
    classical
    by_contra hn
    apply hne
    apply (centeredRange_eq_bot_iff T p ho hT hp hp1).mpr
    intro z hz
    by_contra hz0
    exact hn ⟨z,hz,hz0⟩
  rw [pulse_centered_operator_norm T p ho hT hp hp1 ω hω a t hw, abs_of_nonneg ha]

theorem pulse_centered_norm_of_zero_range (ω : Q → ℝ)
    (hω : ∀ t, Invariant T p (rotate ω t)) (a t : ℝ) (hz : centeredRange T p = ⊥) :
    ‖pulseTransfer T p ho hT hp hp1 ω hω a t -
      (resetTransfer T p ho hT hp hp1 0).toContinuousLinearMap‖ = 0 :=
  pulse_centered_operator_norm_zero T p ho hT hp hp1 ω hω a t
    ((centeredRange_eq_bot_iff T p ho hT hp hp1).mp hz)

theorem pulseKernel_hermitian_iff_on_range (ω : Q → ℝ)
    (hω : ∀ t, Invariant T p (rotate ω t)) (a t : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (pulseKernel T p ho hT hp hp1 a ha.le ha1 ω t).IsHermitian ↔
      ∀ A ∈ centeredRange T p, rotate ω t (rotate ω t A) = A := by
  rw [pulseKernel_hermitian_iff_centered_square T p ho hT hp hp1 a ha ha1 ω hω t]
  constructor
  · intro h A hA
    obtain ⟨z,hz,rfl⟩ := (centeredRange_coordinates T p ho hT hp hp1 A).mp hA
    have he := congrArg (coordinates T ho hT p hp hp1) (h z hz)
    simpa only [phase_coordinates] using he
  · intro h z hz
    apply coordinates_injective T ho hT p hp hp1
    rw [phase_coordinates, phase_coordinates]
    exact h _ ((centeredRange_coordinates T p ho hT hp hp1 _).mpr ⟨z,hz,rfl⟩)

theorem pulseKernel_positive_iff_on_range (ω : Q → ℝ)
    (hω : ∀ t, Invariant T p (rotate ω t)) (a t : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (pulseKernel T p ho hT hp hp1 a ha.le ha1 ω t).PosSemidef ↔
      ∀ A ∈ centeredRange T p, rotate ω t A = A := by
  rw [pulseKernel_positive_iff_centered_fixed T p ho hT hp hp1 a ha ha1 ω hω t]
  constructor
  · intro h A hA
    obtain ⟨z,hz,rfl⟩ := (centeredRange_coordinates T p ho hT hp hp1 A).mp hA
    have he := congrArg (coordinates T ho hT p hp hp1) (h z hz)
    simpa only [phase_coordinates] using he
  · intro h z hz
    apply coordinates_injective T ho hT p hp hp1
    rw [phase_coordinates]
    exact h _ ((centeredRange_coordinates T p ho hT hp hp1 _).mpr ⟨z,hz,rfl⟩)

theorem rotate_centered_mem (ω : Q → ℝ) (t : ℝ) (hω : Invariant T p (rotate ω t))
    (A : MatQ) (hA : A ∈ centeredRange T p) : rotate ω t A ∈ centeredRange T p := by
  refine ⟨hω A hA.1, ?_⟩
  change mean (rotate ω t A) = 0
  rw [FiniteThreeLevelHistoryTransfer.rotate_mean]
  exact hA.2

/-- Weighted selfadjointness of the unitary on the actual centered range is
equivalent to its square being the identity there. -/
theorem centered_phase_symmetric_iff_square (ω : Q → ℝ) (t : ℝ)
    (hω : Invariant T p (rotate ω t)) :
    (∀ A ∈ centeredRange T p, ∀ B ∈ centeredRange T p,
      form (rotate ω t A) B = form A (rotate ω t B)) ↔
    ∀ A ∈ centeredRange T p, rotate ω t (rotate ω t A) = A := by
  constructor
  · intro hs A hA
    have hUA := rotate_centered_mem T p ω t hω A hA
    have hUUA := rotate_centered_mem T p ω t hω _ hUA
    let B := rotate ω t (rotate ω t A) - A
    have hB : B ∈ centeredRange T p := Submodule.sub_mem _ hUUA hA
    have he := hs (rotate ω t A) hUA B hB
    rw [FiniteThreeLevelHistoryTransfer.rotate_form] at he
    have hz : form B B = 0 := by
      change form (rotate ω t (rotate ω t A) - A) B = 0
      simp only [form, Matrix.conjTranspose_sub, mul_sub, sub_mul, Matrix.trace_sub] at he ⊢
      exact sub_eq_zero.mpr he
    exact sub_eq_zero.mp ((FiniteThreeLevelPositiveHistory.form_self_zero_iff B).mp hz)
  · intro hs A _ B hB
    calc
      form (rotate ω t A) B = form (rotate ω t A) (rotate ω t (rotate ω t B)) :=
        congrArg (form (rotate ω t A)) (hs B hB).symm
      _ = form A (rotate ω t B) := FiniteThreeLevelHistoryTransfer.rotate_form ω t A _

theorem pulseKernel_hermitian_iff_centered_symmetric (ω : Q → ℝ)
    (hω : ∀ t, Invariant T p (rotate ω t)) (a t : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (pulseKernel T p ho hT hp hp1 a ha.le ha1 ω t).IsHermitian ↔
    ∀ A ∈ centeredRange T p, ∀ B ∈ centeredRange T p,
      form (rotate ω t A) B = form A (rotate ω t B) := by
  rw [pulseKernel_hermitian_iff_on_range T p ho hT hp hp1 ω hω a t ha ha1,
    centered_phase_symmetric_iff_square T p ω t (hω t)]

theorem pulse_identity_of_scalar (hs : accessible T p = Submodule.span ℂ {(1 : MatQ)})
    (ω : Q → ℝ) (hω : ∀ t, Invariant T p (rotate ω t)) (a t : ℝ)
    (z : Reconstructed T ho hT p hp hp1) : pulseTransfer T p ho hT hp hp1 ω hω a t z = z := by
  apply coordinates_injective T ho hT p hp hp1
  rw [pulse_coordinates]
  have hz : coordinates T ho hT p hp hp1 z ∈ accessible T p := by
    rw [← coordinates_range T ho hT p hp hp1]; exact ⟨z,rfl⟩
  rw [← coordinates_resetTransfer T p ho hT hp hp1 a z,
    resetTransfer_eq_id_of_scalar T p ho hT hp hp1 hs]
  exact phase_fixed_of_scalar T p hs ω t _ hz

theorem pulseKernel_zero_positive (ω : Q → ℝ) (t : ℝ) :
    (pulseKernel T p ho hT hp hp1 0 (by norm_num) (by norm_num) ω t).PosSemidef := by
  rw [pulseKernel_zero]
  have he : massKernel T = kernel T ho hT 0 (by norm_num) (by norm_num) := by
    ext u v
    exact (reset_kernel T ho hT u v).symm
  rw [he]
  exact kernel_posSemidef T ho hT 0 (by norm_num) (by norm_num)

/-- Strict physical damping is visible precisely on a nonzero centered component. -/
theorem thermal_norm_strict_iff (ω : Q → ℝ) (hω : ∀ t, Invariant T p (rotate ω t))
    (γ t : ℝ) (hγ : 0 < γ) (ht : 0 < t) (z : Reconstructed T ho hT p hp hp1) :
    ‖pulseTransfer T p ho hT hp hp1 ω hω (Real.exp (-γ*t)) t z‖ < ‖z‖ ↔
      z - resetTransfer T p ho hT hp hp1 0 z ≠ 0 := by
  rw [← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _), pulse_norm_sq,
    scalar_pythagoras T p ho hT hp hp1 z]
  have ha : Real.exp (-γ*t) < 1 := Real.exp_lt_one_iff.mpr (by nlinarith)
  have ha0 := Real.exp_pos (-γ*t)
  constructor
  · intro h hz
    simp [hz] at h
  · intro hz
    have hn := sq_pos_of_pos (norm_pos_iff.mpr hz)
    nlinarith [mul_pos (by nlinarith : 0 < 1 - Real.exp (-γ*t)^2) hn]

theorem thermal_zero_rate (ω : Q → ℝ) (hω : ∀ t, Invariant T p (rotate ω t))
    (t : ℝ) (z : Reconstructed T ho hT p hp hp1) :
    pulseTransfer T p ho hT hp hp1 ω hω (Real.exp (-(0:ℝ)*t)) t z =
      phaseOperator T p ho hT hp hp1 ω hω t z := by
  simp only [neg_zero, zero_mul, Real.exp_zero, pulseTransfer,
    ContinuousLinearMap.comp_apply, resetTransfer_one]
  rfl

theorem scalar_phase_invariant (hs : accessible T p = Submodule.span ℂ {(1 : MatQ)})
    (ω : Q → ℝ) (t : ℝ) : Invariant T p (rotate ω t) := by
  intro A hA
  rw [phase_fixed_of_scalar T p hs ω t A hA]
  exact hA

theorem reset_endpoint_pulse_identity (ω : Q → ℝ) (a t : ℝ)
    (z : Reconstructed T ho hT 0 (by norm_num) (by norm_num)) :
    pulseTransfer T 0 ho hT (by norm_num) (by norm_num) ω
      (fun s => scalar_phase_invariant T 0 (reset_range T) ω s) a t z = z :=
  pulse_identity_of_scalar T 0 ho hT (by norm_num) (by norm_num) (reset_range T) ω _ a t z

theorem reset_endpoint_pulse_positive (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1)
    (ω : Q → ℝ) (t : ℝ) :
    (pulseKernel T 0 ho hT (by norm_num) (by norm_num) a ha ha1 ω t).PosSemidef :=
  pulseKernel_positive_of_fixed T 0 ho hT (by norm_num) (by norm_num) a ha ha1 ω t
    (phase_fixed_of_scalar T 0 (reset_range T) ω t)

/-- Positive finite damping time separates the thermal orbit from its unitary part
exactly where the strategy retains a centered component. -/
theorem thermal_ne_phase (ω : Q → ℝ) (hω : ∀ t, Invariant T p (rotate ω t))
    (γ t : ℝ) (hγ : 0 < γ) (ht : 0 < t) (z : Reconstructed T ho hT p hp hp1)
    (hz : z - resetTransfer T p ho hT hp hp1 0 z ≠ 0) :
    pulseTransfer T p ho hT hp hp1 ω hω (Real.exp (-γ*t)) t z ≠
      phaseOperator T p ho hT hp hp1 ω hω t z := by
  intro he
  have hn := (thermal_norm_strict_iff T p ho hT hp hp1 ω hω γ t hγ ht z).mpr hz
  rw [he, phase_norm] at hn
  exact lt_irrefl _ hn

/-- The physical retention is positive at every finite allowed time; no finite
exponential parameter realizes complete operational reset. -/
theorem physical_retention (γ t : ℝ) (hγ : 0 ≤ γ) (ht : 0 ≤ t) :
    Real.exp (-γ*t) ∈ Set.Ioc (0 : ℝ) 1 :=
  ⟨Real.exp_pos _, GibbsReset.exp_rate_le_one γ t hγ ht⟩

theorem thermal_physical_coordinates (b ℏ γ t : ℝ) (hℏ : 0 < ℏ)
    (hγ : 0 ≤ γ) (ht : 0 ≤ t)
    (hω : ∀ s, Invariant T p (rotate (FiniteThreeLevelThermalPhase.frequencies b ℏ) s))
    (z : Reconstructed T ho hT p hp hp1) :
    coordinates T ho hT p hp hp1
      (pulseTransfer T p ho hT hp hp1 (FiniteThreeLevelThermalPhase.frequencies b ℏ)
        hω (Real.exp (-γ*t)) t z) =
    FiniteGibbsClock.heisenberg (FiniteThreeLevelThermalPhase.thermalH b) ℏ t
      (Channel.heisenberg (FiniteThreeLevelPositiveHistory.channel (Real.exp (-γ*t)))
        (coordinates T ho hT p hp hp1 z)) := by
  rw [pulse_coordinates, FiniteThreeLevelPositiveHistory.channel_observable
    (physical_retention γ t hγ ht).1.le (physical_retention γ t hγ ht).2]
  have he := FiniteThreeLevelThermalPhase.phase_physical b ℏ (-t) hℏ
    (Psi (Real.exp (-γ*t)) (coordinates T ho hT p hp hp1 z))
  simpa only [FiniteThreeLevelThermalPhase.phase, rotate, LinearMap.coe_mk,
    AddHom.coe_mk, neg_neg] using he

theorem modular_at_physical_parameter (b ℏ t : ℝ) (hb : 0 < b) (hℏ : 0 < ℏ)
    (hω : ∀ s, Invariant T p (rotate (FiniteThreeLevelThermalPhase.frequencies b ℏ) s))
    (z : Reconstructed T ho hT p hp hp1) :
    transfer T p ho hT hp hp1 (modularLinear b (-t / (b*ℏ)))
      (modular_invariant T p b ℏ _ hℏ hω) z =
    phaseOperator T p ho hT hp hp1 (FiniteThreeLevelThermalPhase.frequencies b ℏ) hω t z := by
  apply coordinates_injective T ho hT p hp hp1
  rw [modular_strategy_coordinates T p ho hT hp hp1 b ℏ _ hℏ hω, phase_coordinates]
  have he : -b * ℏ * (-t / (b*ℏ)) = t := by field_simp
  rw [he]

/-- This physical comparison consumes the independently defined Gibbs state
and keeps the nonzero-center condition on dissipative separation. -/
theorem physical_thermal_ne_modular (b ℏ γ t : ℝ) (hb : 0 < b) (hℏ : 0 < ℏ)
    (hγ : 0 < γ) (ht : 0 < t)
    (hω : ∀ s, Invariant T p (rotate (FiniteThreeLevelThermalPhase.frequencies b ℏ) s))
    (z : Reconstructed T ho hT p hp hp1)
    (hz : z - resetTransfer T p ho hT hp hp1 0 z ≠ 0) :
    FiniteGibbsClock.gibbs (FiniteThreeLevelThermalPhase.thermalH b) b = rhoN ∧
    pulseTransfer T p ho hT hp hp1 (FiniteThreeLevelThermalPhase.frequencies b ℏ)
      hω (Real.exp (-γ*t)) t z ≠
    transfer T p ho hT hp hp1 (modularLinear b (-t / (b*ℏ)))
      (modular_invariant T p b ℏ _ hℏ hω) z := by
  refine ⟨FiniteThreeLevelThermalPhase.gibbs_thermal hb, ?_⟩
  rw [modular_at_physical_parameter T p ho hT hp hp1 b ℏ t hb hℏ hω]
  exact thermal_ne_phase T p ho hT hp hp1 _ hω γ t hγ ht z hz

/-- Scalar strategies erase the unitary modular action as well as dissipation. -/
theorem modular_identity_of_scalar (hs : accessible T p = Submodule.span ℂ {(1 : MatQ)})
    (b ℏ s : ℝ) (hℏ : 0 < ℏ) (z : Reconstructed T ho hT p hp hp1) :
    transfer T p ho hT hp hp1 (modularLinear b s)
      (modular_invariant T p b ℏ s hℏ (scalar_phase_invariant T p hs _)) z = z := by
  apply coordinates_injective T ho hT p hp hp1
  rw [modular_strategy_coordinates T p ho hT hp hp1 b ℏ s hℏ
    (scalar_phase_invariant T p hs _)]
  apply phase_fixed_of_scalar T p hs
  rw [← coordinates_range T ho hT p hp hp1]
  exact ⟨z,rfl⟩

end EndpointConsumers


section FixedTime
open FiniteThreeLevelHistoryTransfer (rotate rotate_inverse rotate_group rotate_zero rotate_form
  rotate_mean rotate_one rotate_Psi)

/-- Restriction of the actual phase to its invariant finite-dimensional range. -/
def phaseRange (ω : Q → ℝ) (t : ℝ) (ht : Invariant T p (rotate ω t)) :
    accessible T p →ₗ[ℂ] accessible T p :=
  ((rotate ω t).comp (accessible T p).subtype).codRestrict (accessible T p)
    (fun A => ht A A.property)

theorem phaseRange_injective (ω : Q → ℝ) (t : ℝ)
    (ht : Invariant T p (rotate ω t)) : Function.Injective (phaseRange T p ω t ht) := by
  intro A B h
  apply Subtype.ext
  have he := congrArg (fun C : accessible T p => rotate ω (-t) C.val) h
  change rotate ω (-t) (rotate ω t A.val) = rotate ω (-t) (rotate ω t B.val) at he
  simpa only [rotate_inverse] using he

/-- Finite dimension is essential: injectivity of the restricted endomorphism
implies onto the same actual accessible range. -/
theorem phaseRange_surjective (ω : Q → ℝ) (t : ℝ)
    (ht : Invariant T p (rotate ω t)) : Function.Surjective (phaseRange T p ω t ht) :=
  LinearMap.surjective_of_injective (phaseRange_injective T p ω t ht)

/-- Negative-time invariance follows from the selected-time hypothesis alone. -/
theorem phase_negative_invariant (ω : Q → ℝ) (t : ℝ)
    (ht : Invariant T p (rotate ω t)) : Invariant T p (rotate ω (-t)) := by
  intro A hA
  obtain ⟨B,hB⟩ := phaseRange_surjective T p ω t ht ⟨A,hA⟩
  have he := congrArg (fun C : accessible T p => rotate ω (-t) C.val) hB
  change rotate ω (-t) (rotate ω t B.val) = rotate ω (-t) A at he
  rw [rotate_inverse] at he
  exact he ▸ B.property

theorem phaseRange_inverse (ω : Q → ℝ) (t : ℝ)
    (ht : Invariant T p (rotate ω t)) (A : accessible T p) :
    phaseRange T p ω (-t) (phase_negative_invariant T p ω t ht)
      (phaseRange T p ω t ht A) = A := by
  apply Subtype.ext
  exact rotate_inverse ω t A.val

theorem phaseRange_right_inverse (ω : Q → ℝ) (t : ℝ)
    (ht : Invariant T p (rotate ω t)) (A : accessible T p) :
    phaseRange T p ω t ht
      (phaseRange T p ω (-t) (phase_negative_invariant T p ω t ht) A) = A := by
  apply Subtype.ext
  change rotate ω t (rotate ω (-t) A.val) = A.val
  rw [rotate_group, add_neg_cancel, rotate_zero]

end FixedTime

namespace Pointwise
open FiniteThreeLevelHistoryTransfer (rotate rotate_form rotate_group rotate_zero rotate_Psi
  rotate_mean rotate_one)
variable (ω : Q → ℝ) (t : ℝ) (hω : Invariant T p (rotate ω t))

/-- Exact selected-time descent through S1; no all-real family is assumed. -/
def phaseOperator :
    Reconstructed T ho hT p hp hp1 →L[ℂ] Reconstructed T ho hT p hp hp1 :=
  (transfer T p ho hT hp hp1 (rotate ω t) hω).toContinuousLinearMap

theorem phase_coordinates (z : Reconstructed T ho hT p hp hp1) :
    coordinates T ho hT p hp hp1 (phaseOperator T p ho hT hp hp1 ω t hω z) =
      rotate ω t (coordinates T ho hT p hp hp1 z) :=
  coordinates_transfer T p ho hT hp hp1 _ _ z

theorem phase_inner (z w : Reconstructed T ho hT p hp hp1) :
    ⟪phaseOperator T p ho hT hp hp1 ω t hω z,
      phaseOperator T p ho hT hp hp1 ω t hω w⟫_ℂ = ⟪z,w⟫_ℂ := by
  rw [coordinates_inner, coordinates_inner, phase_coordinates, phase_coordinates, rotate_form]

def phaseIsometry :
    Reconstructed T ho hT p hp hp1 →ₗᵢ[ℂ] Reconstructed T ho hT p hp hp1 :=
  (phaseOperator T p ho hT hp hp1 ω t hω).toLinearMap.isometryOfInner
    (phase_inner T p ho hT hp hp1 ω t hω)

theorem phase_norm (z : Reconstructed T ho hT p hp hp1) :
    ‖phaseOperator T p ho hT hp hp1 ω t hω z‖ = ‖z‖ :=
  (phaseIsometry T p ho hT hp hp1 ω t hω).norm_map z

theorem phase_inverse (z : Reconstructed T ho hT p hp hp1) :
    phaseOperator T p ho hT hp hp1 ω (-t) (phase_negative_invariant T p ω t hω)
      (phaseOperator T p ho hT hp hp1 ω t hω z) = z := by
  apply coordinates_injective T ho hT p hp hp1
  rw [phase_coordinates, phase_coordinates, FiniteThreeLevelHistoryTransfer.rotate_inverse]

local notation "P₀" => resetTransfer T p ho hT hp hp1 0

theorem phase_scalar (z : Reconstructed T ho hT p hp hp1) :
    phaseOperator T p ho hT hp hp1 ω t hω (P₀ z) = P₀ z := by
  apply coordinates_injective T ho hT p hp hp1
  rw [phase_coordinates, coordinates_resetTransfer]
  simp only [FiniteThreeLevelPositiveHistory.Psi_zero, map_smul, rotate_one]

theorem scalar_phase (z : Reconstructed T ho hT p hp hp1) :
    P₀ (phaseOperator T p ho hT hp hp1 ω t hω z) = P₀ z := by
  apply coordinates_injective T ho hT p hp hp1
  rw [coordinates_resetTransfer, coordinates_resetTransfer, phase_coordinates]
  simp only [FiniteThreeLevelPositiveHistory.Psi_zero]
  rw [show (rhoN * rotate ω t (coordinates T ho hT p hp hp1 z)).trace =
    (rhoN * coordinates T ho hT p hp hp1 z).trace from rotate_mean ω t _]

theorem phase_reset_commute (a : ℝ) (z : Reconstructed T ho hT p hp hp1) :
    phaseOperator T p ho hT hp hp1 ω t hω (resetTransfer T p ho hT hp hp1 a z) =
      resetTransfer T p ho hT hp hp1 a (phaseOperator T p ho hT hp hp1 ω t hω z) := by
  apply coordinates_injective T ho hT p hp hp1
  rw [phase_coordinates, coordinates_resetTransfer, coordinates_resetTransfer, phase_coordinates, rotate_Psi]

theorem phase_adjoint_inner (z w : Reconstructed T ho hT p hp hp1) :
    ⟪phaseOperator T p ho hT hp hp1 ω t hω z,w⟫_ℂ =
      ⟪z,phaseOperator T p ho hT hp hp1 ω (-t)
        (phase_negative_invariant T p ω t hω) w⟫_ℂ := by
  rw [coordinates_inner, coordinates_inner, phase_coordinates, phase_coordinates]
  exact FiniteThreeLevelHistoryTransfer.rotate_form_adjoint ω t _ _

theorem phase_adjoint :
    (phaseOperator T p ho hT hp hp1 ω t hω).adjoint =
      phaseOperator T p ho hT hp hp1 ω (-t) (phase_negative_invariant T p ω t hω) := by
  ext z
  apply ext_inner_left ℂ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact phase_adjoint_inner T p ho hT hp hp1 ω t hω w z

def pulseTransfer (a : ℝ) :
    Reconstructed T ho hT p hp hp1 →L[ℂ] Reconstructed T ho hT p hp hp1 :=
  (phaseOperator T p ho hT hp hp1 ω t hω).comp
    (resetTransfer T p ho hT hp hp1 a).toContinuousLinearMap

theorem pulse_coordinates (a : ℝ) (z : Reconstructed T ho hT p hp hp1) :
    coordinates T ho hT p hp hp1 (pulseTransfer T p ho hT hp hp1 ω t hω a z) =
      rotate ω t (Psi a (coordinates T ho hT p hp hp1 z)) := by
  change coordinates T ho hT p hp hp1
    (phaseOperator T p ho hT hp hp1 ω t hω (resetTransfer T p ho hT hp hp1 a z)) = _
  rw [phase_coordinates, coordinates_resetTransfer]

theorem pulse_split (a : ℝ) (z : Reconstructed T ho hT p hp hp1) :
    pulseTransfer T p ho hT hp hp1 ω t hω a z = P₀ z +
      (a : ℂ) • phaseOperator T p ho hT hp hp1 ω t hω (z - P₀ z) := by
  change phaseOperator T p ho hT hp hp1 ω t hω (resetTransfer T p ho hT hp hp1 a z) = _
  rw [resetTransfer_split, map_add, map_smul, phase_scalar]

theorem pulse_adjoint_inner (a : ℝ) (z w : Reconstructed T ho hT p hp hp1) :
    ⟪pulseTransfer T p ho hT hp hp1 ω t hω a z,w⟫_ℂ =
      ⟪z,pulseTransfer T p ho hT hp hp1 ω (-t) (phase_negative_invariant T p ω t hω) a w⟫_ℂ := by
  change ⟪phaseOperator T p ho hT hp hp1 ω t hω
    (resetTransfer T p ho hT hp hp1 a z),w⟫_ℂ =
    ⟪z,phaseOperator T p ho hT hp hp1 ω (-t) (phase_negative_invariant T p ω t hω) (resetTransfer T p ho hT hp hp1 a w)⟫_ℂ
  rw [phase_adjoint_inner, phase_reset_commute]
  exact resetTransfer_symmetric T p ho hT hp hp1 a z _

theorem pulse_adjoint (a : ℝ) : (pulseTransfer T p ho hT hp hp1 ω t hω a).adjoint =
    pulseTransfer T p ho hT hp hp1 ω (-t) (phase_negative_invariant T p ω t hω) a := by
  ext z
  apply ext_inner_left ℂ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_right, pulse_adjoint_inner]

theorem pulse_norm_sq (a : ℝ) (z : Reconstructed T ho hT p hp hp1) :
    ‖pulseTransfer T p ho hT hp hp1 ω t hω a z‖ ^ 2 =
      ‖P₀ z‖ ^ 2 + a^2 * ‖z - P₀ z‖ ^ 2 := by
  change ‖phaseOperator T p ho hT hp hp1 ω t hω (resetTransfer T p ho hT hp hp1 a z)‖ ^ 2 = _
  rw [phase_norm, reset_norm_sq]

theorem phase_selfadjoint_iff_square :
    IsSelfAdjoint (phaseOperator T p ho hT hp hp1 ω t hω) ↔
      ∀ z, phaseOperator T p ho hT hp hp1 ω t hω
        (phaseOperator T p ho hT hp hp1 ω t hω z) = z := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', phase_adjoint]
  constructor
  · intro he z
    have hi := phase_inverse T p ho hT hp hp1 ω t hω z
    rwa [he] at hi
  · intro hs
    ext z
    have he := congrArg (phaseOperator T p ho hT hp hp1 ω (-t) (phase_negative_invariant T p ω t hω)) (hs z)
    rw [phase_inverse] at he
    exact he.symm

theorem phase_square_iff_centered :
    (∀ z, phaseOperator T p ho hT hp hp1 ω t hω
      (phaseOperator T p ho hT hp hp1 ω t hω z) = z) ↔
    ∀ z, P₀ z = 0 → phaseOperator T p ho hT hp hp1 ω t hω
      (phaseOperator T p ho hT hp hp1 ω t hω z) = z := by
  constructor
  · intro h z _; exact h z
  · intro h z
    have hc : P₀ (z - P₀ z) = 0 := by
      rw [map_sub]
      have hi := LinearMap.congr_fun (resetTransfer_zero_idempotent T p ho hT hp hp1) z
      change P₀ (P₀ z) = P₀ z at hi
      rw [hi, sub_self]
    have he := h (z - P₀ z) hc
    simp only [map_sub, phase_scalar] at he
    exact sub_left_injective he

theorem phase_eq_id_iff_centered :
    (∀ z, phaseOperator T p ho hT hp hp1 ω t hω z = z) ↔
    ∀ z, P₀ z = 0 → phaseOperator T p ho hT hp hp1 ω t hω z = z := by
  constructor
  · intro h z _; exact h z
  · intro h z
    have hc : P₀ (z - P₀ z) = 0 := by
      rw [map_sub]
      have hi := LinearMap.congr_fun (resetTransfer_zero_idempotent T p ho hT hp hp1) z
      change P₀ (P₀ z) = P₀ z at hi
      rw [hi, sub_self]
    have he := h (z - P₀ z) hc
    simp only [map_sub, phase_scalar] at he
    exact sub_left_injective he

theorem pulse_selfadjoint_iff_phase (a : ℝ) (ha : a ≠ 0) :
    IsSelfAdjoint (pulseTransfer T p ho hT hp hp1 ω t hω a) ↔
      IsSelfAdjoint (phaseOperator T p ho hT hp hp1 ω t hω) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff', pulse_adjoint,
    ContinuousLinearMap.isSelfAdjoint_iff', phase_adjoint]
  constructor
  · intro he
    ext z
    have hz := DFunLike.congr_fun he
      (resetTransfer T p ho hT hp hp1 a⁻¹ z)
    change phaseOperator T p ho hT hp hp1 ω (-t) (phase_negative_invariant T p ω t hω)
      (resetTransfer T p ho hT hp hp1 a (resetTransfer T p ho hT hp hp1 a⁻¹ z)) =
      phaseOperator T p ho hT hp hp1 ω t hω
      (resetTransfer T p ho hT hp hp1 a (resetTransfer T p ho hT hp hp1 a⁻¹ z)) at hz
    have hr := LinearMap.congr_fun (resetTransfer_comp T p ho hT hp hp1 a a⁻¹) z
    change resetTransfer T p ho hT hp hp1 a (resetTransfer T p ho hT hp hp1 a⁻¹ z) = _ at hr
    rw [mul_inv_cancel₀ ha, resetTransfer_one] at hr
    change resetTransfer T p ho hT hp hp1 a (resetTransfer T p ho hT hp hp1 a⁻¹ z) = z at hr
    rwa [hr] at hz
  · intro he
    simp only [pulseTransfer, he]

theorem pulse_positive_iff_phase_fixed (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (pulseTransfer T p ho hT hp hp1 ω t hω a).IsPositive ↔
      ∀ z, phaseOperator T p ho hT hp hp1 ω t hω z = z := by
  constructor
  · intro hpos z
    have hs := (pulse_selfadjoint_iff_phase T p ho hT hp hp1 ω t hω a ha.ne').mp
      hpos.isSelfAdjoint
    have hsq := (phase_selfadjoint_iff_square T p ho hT hp hp1 ω t hω).mp hs
    let y := z - phaseOperator T p ho hT hp hp1 ω t hω z
    have hpy : P₀ y = 0 := by
      dsimp [y]
      rw [map_sub, scalar_phase, sub_self]
    have huy : phaseOperator T p ho hT hp hp1 ω t hω y = -y := by
      dsimp [y]
      rw [map_sub, hsq]
      abel
    have hty : pulseTransfer T p ho hT hp hp1 ω t hω a y = -(a : ℂ) • y := by
      rw [pulse_split, hpy, sub_zero, zero_add, huy, smul_neg, neg_smul]
    have hn := hpos.re_inner_nonneg_left y
    change 0 ≤ (⟪pulseTransfer T p ho hT hp hp1 ω t hω a y,y⟫_ℂ).re at hn
    rw [hty, inner_smul_left] at hn
    simp only [map_neg, Complex.conj_ofReal, neg_mul, Complex.neg_re,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] at hn
    have hy : 0 ≤ (⟪y,y⟫_ℂ).re := inner_self_nonneg (𝕜 := ℂ) (x := y)
    have hy0 : ‖y‖ ^ 2 = 0 := by
      rw [norm_sq_eq_re_inner (𝕜 := ℂ)]
      change (⟪y,y⟫_ℂ).re = 0
      nlinarith
    have hyz : y = 0 := norm_eq_zero.mp (by nlinarith [norm_nonneg y])
    exact (sub_eq_zero.mp hyz).symm
  · intro hfix
    have he : pulseTransfer T p ho hT hp hp1 ω t hω a =
        (resetTransfer T p ho hT hp hp1 a).toContinuousLinearMap := by
      ext z
      exact hfix (resetTransfer T p ho hT hp hp1 a z)
    rw [he]
    exact reset_positive T p ho hT hp hp1 a ha.le ha1

theorem pulseKernel_old_inner (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) (f g : History o n → ℂ) :
    pairing (pulseKernel T p ho hT hp hp1 a ha ha1 ω t) f g =
      ⟪mk K hK f, pulseTransfer T p ho hT hp hp1 ω t hω a (mk K hK g)⟫_ℂ := by
  rw [pulseKernel_pairing, coordinates_inner, pulse_coordinates, coordinates_mk, coordinates_mk]

theorem pulseKernel_hermitian_iff (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (pulseKernel T p ho hT hp hp1 a ha ha1 ω t).IsHermitian ↔
      IsSelfAdjoint (pulseTransfer T p ho hT hp hp1 ω t hω a) := by
  classical
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  constructor
  · intro hh z w
    obtain ⟨f,rfl⟩ := mk_surjective K hK z
    obtain ⟨g,rfl⟩ := mk_surjective K hK w
    change ⟪pulseTransfer T p ho hT hp hp1 ω t hω a (mk K hK f), mk K hK g⟫_ℂ =
      ⟪mk K hK f, pulseTransfer T p ho hT hp hp1 ω t hω a (mk K hK g)⟫_ℂ
    rw [← inner_conj_symm, ← pulseKernel_old_inner T p ho hT hp hp1 ω t hω a ha ha1,
      ← pulseKernel_old_inner T p ho hT hp hp1 ω t hω a ha ha1]
    change star (star g ⬝ᵥ (pulseKernel T p ho hT hp hp1 a ha ha1 ω t *ᵥ f)) = _
    rw [← star_dotProduct, star_mulVec, hh.eq]
    exact (dotProduct_mulVec (star f) (pulseKernel T p ho hT hp hp1 a ha ha1 ω t) g).symm
  · intro hs
    apply Matrix.IsHermitian.ext
    intro u v
    have he := hs (mk K hK (Pi.single u 1)) (mk K hK (Pi.single v 1))
    change ⟪pulseTransfer T p ho hT hp hp1 ω t hω a (mk K hK (Pi.single u 1)),
      mk K hK (Pi.single v 1)⟫_ℂ =
      ⟪mk K hK (Pi.single u 1),pulseTransfer T p ho hT hp hp1 ω t hω a
        (mk K hK (Pi.single v 1))⟫_ℂ at he
    rw [← inner_conj_symm, ← pulseKernel_old_inner T p ho hT hp hp1 ω t hω a ha ha1,
      ← pulseKernel_old_inner T p ho hT hp hp1 ω t hω a ha ha1] at he
    simpa [pairing, Matrix.mulVec, dotProduct, Pi.single_apply] using he

theorem pulseKernel_positive_iff_operator (a : ℝ) (ha : 0 ≤ a) (ha1 : a ≤ 1) :
    (pulseKernel T p ho hT hp hp1 a ha ha1 ω t).PosSemidef ↔
      (pulseTransfer T p ho hT hp hp1 ω t hω a).IsPositive := by
  constructor
  · intro hk
    refine ⟨((pulseKernel_hermitian_iff T p ho hT hp hp1 ω t hω a ha ha1).mp
      hk.isHermitian).isSymmetric, ?_⟩
    intro z
    obtain ⟨f,rfl⟩ := mk_surjective K hK z
    have hn := (hk.dotProduct_mulVec_nonneg f).1
    change 0 ≤ (pairing (pulseKernel T p ho hT hp hp1 a ha ha1 ω t) f f).re at hn
    rw [pulseKernel_old_inner T p ho hT hp hp1 ω t hω a ha ha1] at hn
    change 0 ≤ (⟪pulseTransfer T p ho hT hp hp1 ω t hω a (mk K hK f), mk K hK f⟫_ℂ).re
    rw [← inner_conj_symm, Complex.conj_re]
    exact hn
  · intro ht
    apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    · exact (pulseKernel_hermitian_iff T p ho hT hp hp1 ω t hω a ha ha1).mpr ht.isSelfAdjoint
    · intro f
      change 0 ≤ pairing (pulseKernel T p ho hT hp hp1 a ha ha1 ω t) f f
      rw [pulseKernel_old_inner T p ho hT hp hp1 ω t hω a ha ha1]
      exact ht.inner_nonneg_right _

theorem pulseKernel_hermitian_iff_centered_square
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (pulseKernel T p ho hT hp hp1 a ha.le ha1 ω t).IsHermitian ↔
      ∀ z, resetTransfer T p ho hT hp hp1 0 z = 0 →
        phaseOperator T p ho hT hp hp1 ω t hω
          (phaseOperator T p ho hT hp hp1 ω t hω z) = z := by
  rw [pulseKernel_hermitian_iff T p ho hT hp hp1 ω t hω a ha.le ha1,
    pulse_selfadjoint_iff_phase T p ho hT hp hp1 ω t hω a ha.ne',
    phase_selfadjoint_iff_square, phase_square_iff_centered]

theorem pulseKernel_positive_iff_centered_fixed
    (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (pulseKernel T p ho hT hp hp1 a ha.le ha1 ω t).PosSemidef ↔
      ∀ z, resetTransfer T p ho hT hp hp1 0 z = 0 →
        phaseOperator T p ho hT hp hp1 ω t hω z = z := by
  rw [pulseKernel_positive_iff_operator T p ho hT hp hp1 ω t hω a ha.le ha1,
    pulse_positive_iff_phase_fixed T p ho hT hp hp1 ω t hω a ha ha1,
    phase_eq_id_iff_centered]

include hω in
theorem pulseKernel_hermitian_iff_on_range (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (pulseKernel T p ho hT hp hp1 a ha.le ha1 ω t).IsHermitian ↔
      ∀ A ∈ centeredRange T p, rotate ω t (rotate ω t A) = A := by
  rw [pulseKernel_hermitian_iff_centered_square T p ho hT hp hp1 ω t hω a ha ha1]
  constructor
  · intro h A hA
    obtain ⟨z,hz,rfl⟩ := (centeredRange_coordinates T p ho hT hp hp1 A).mp hA
    have he := congrArg (coordinates T ho hT p hp hp1) (h z hz)
    simpa only [phase_coordinates] using he
  · intro h z hz
    apply coordinates_injective T ho hT p hp hp1
    rw [phase_coordinates, phase_coordinates]
    exact h _ ((centeredRange_coordinates T p ho hT hp hp1 _).mpr ⟨z,hz,rfl⟩)

include hω in
theorem pulseKernel_positive_iff_on_range (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (pulseKernel T p ho hT hp hp1 a ha.le ha1 ω t).PosSemidef ↔
      ∀ A ∈ centeredRange T p, rotate ω t A = A := by
  rw [pulseKernel_positive_iff_centered_fixed T p ho hT hp hp1 ω t hω a ha ha1]
  constructor
  · intro h A hA
    obtain ⟨z,hz,rfl⟩ := (centeredRange_coordinates T p ho hT hp hp1 A).mp hA
    have he := congrArg (coordinates T ho hT p hp hp1) (h z hz)
    simpa only [phase_coordinates] using he
  · intro h z hz
    apply coordinates_injective T ho hT p hp hp1
    rw [phase_coordinates]
    exact h _ ((centeredRange_coordinates T p ho hT hp hp1 _).mpr ⟨z,hz,rfl⟩)

include hω in
theorem pulseKernel_hermitian_iff_centered_symmetric (a : ℝ) (ha : 0 < a) (ha1 : a ≤ 1) :
    (pulseKernel T p ho hT hp hp1 a ha.le ha1 ω t).IsHermitian ↔
    ∀ A ∈ centeredRange T p, ∀ B ∈ centeredRange T p,
      form (rotate ω t A) B = form A (rotate ω t B) := by
  rw [pulseKernel_hermitian_iff_on_range T p ho hT hp hp1 ω t hω a ha ha1,
    centered_phase_symmetric_iff_square T p ω t hω]

/-- The selected-time construction agrees with the established all-real API
whenever that stronger hypothesis is available. -/
theorem phase_all_real (hAll : ∀ s, Invariant T p (rotate ω s)) :
    phaseOperator T p ho hT hp hp1 ω t hω =
      FiniteThreeLevelStationaryStrategyTransfer.phaseOperator T p ho hT hp hp1 ω hAll t := by
  ext z
  apply coordinates_injective T ho hT p hp hp1
  rw [phase_coordinates, FiniteThreeLevelStationaryStrategyTransfer.phase_coordinates]

theorem pulse_all_real (hAll : ∀ s, Invariant T p (rotate ω s)) (a : ℝ) :
    pulseTransfer T p ho hT hp hp1 ω t hω a =
      FiniteThreeLevelStationaryStrategyTransfer.pulseTransfer T p ho hT hp hp1 ω hAll a t := by
  ext z
  apply coordinates_injective T ho hT p hp hp1
  rw [pulse_coordinates, FiniteThreeLevelStationaryStrategyTransfer.pulse_coordinates]

end Pointwise

end SKEFTHawking.QuantumNetwork.FiniteThreeLevelStationaryStrategyTransfer

#check Nat
