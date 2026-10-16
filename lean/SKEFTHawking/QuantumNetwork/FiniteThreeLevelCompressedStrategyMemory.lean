import SKEFTHawking.QuantumNetwork.FiniteThreeLevelStationaryStrategyTransfer
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Sandwiched compression on actual stationary strategy ranges

The projection is conjugated through the existing faithful feature map.
Its transfer acts on the existing history quotient; it is not a physical channel.
-/
noncomputable section
namespace SKEFTHawking.QuantumNetwork.FiniteThreeLevelCompressedStrategyMemory
open Matrix FiniteInterventionProcess FiniteThreeLevelStationaryStrategyReflection
open FiniteThreeLevelStationaryStrategyTransfer
open FiniteThreeLevelPositiveHistory (Q MatQ Psi form feature featureLinear)
open FiniteThreeLevelHistoryTransfer (mean rotate)
open FinitePositiveKernel (mk pairing)
open scoped BigOperators ComplexOrder InnerProductSpace

local instance : NormedAddCommGroup MatQ := Matrix.toMatrixNormedAddCommGroup 1 Matrix.PosDef.one
local instance : InnerProductSpace ℂ MatQ := Matrix.toMatrixInnerProductSpace 1 Matrix.PosSemidef.one

def featureEquiv : MatQ ≃ₗ[ℂ] MatQ :=
  LinearEquiv.ofBijective featureLinear
    ⟨FiniteThreeLevelPositiveHistory.feature_injective,
      FiniteThreeLevelPositiveHistory.feature_surjective⟩

theorem feature_inner (A B : MatQ) : ⟪feature A, feature B⟫_ℂ = form A B := by
  change (feature B * 1 * (feature A)ᴴ).trace = _
  simpa using FiniteThreeLevelPositiveHistory.feature_gram A B

variable {o n : ℕ} (T : Tree Q Unit o n) (p : ℝ)

def featureRange : Submodule ℂ MatQ := (accessible T p).map featureLinear

/-- The actual feature-conjugated weighted projection, without an assumed decomposition. -/
def projection : MatQ →ₗ[ℂ] MatQ where
  toFun A := featureEquiv.symm ((featureRange T p).starProjection (featureLinear A))
  map_add' A B := by
    simp only [map_add]
  map_smul' z A := by
    simp only [map_smul, RingHom.id_apply]

def hiddenProjection : MatQ →ₗ[ℂ] MatQ := LinearMap.id - projection T p

theorem feature_projection (A : MatQ) :
    feature (projection T p A) = (featureRange T p).starProjection (feature A) :=
  featureEquiv.apply_symm_apply _

theorem projection_mem (A : MatQ) : projection T p A ∈ accessible T p := by
  have h := (featureRange T p).starProjection_apply_mem (feature A)
  rw [← feature_projection T p A] at h
  obtain ⟨B, hB, he⟩ := h
  exact (FiniteThreeLevelPositiveHistory.feature_injective he) ▸ hB

theorem projection_fixed {A : MatQ} (hA : A ∈ accessible T p) :
    projection T p A = A := by
  apply FiniteThreeLevelPositiveHistory.feature_injective
  rw [feature_projection]
  exact Submodule.starProjection_eq_self_iff.mpr ⟨A, hA, rfl⟩

theorem projection_idempotent (A : MatQ) :
    projection T p (projection T p A) = projection T p A :=
  projection_fixed T p (projection_mem T p A)

theorem projection_range : (projection T p).range = accessible T p := by
  apply le_antisymm
  · rintro A ⟨B, rfl⟩
    exact projection_mem T p B
  · intro A hA
    exact ⟨A, projection_fixed T p hA⟩

theorem feature_hiddenProjection (A : MatQ) :
    feature (hiddenProjection T p A) =
      feature A - (featureRange T p).starProjection (feature A) := by
  change featureLinear (A - projection T p A) = _
  rw [map_sub]
  exact congrArg (feature A - ·) (feature_projection T p A)

theorem projection_orthogonal (A B : MatQ) (hB : B ∈ accessible T p) :
    form (hiddenProjection T p A) B = 0 := by
  rw [← feature_inner, feature_hiddenProjection]
  exact Submodule.starProjection_inner_eq_zero _ _ ⟨B, hB, rfl⟩

theorem projection_symmetric (A B : MatQ) :
    form (projection T p A) B = form A (projection T p B) := by
  rw [← feature_inner, ← feature_inner, feature_projection, feature_projection]
  exact (featureRange T p).inner_starProjection_left_eq_right _ _

theorem form_projection_right {A : MatQ} (hA : A ∈ accessible T p) (B : MatQ) :
    form A (projection T p B) = form A B := by
  rw [← projection_symmetric, projection_fixed T p hA]

theorem projection_eq_of_pairings (A B : MatQ) (hB : B ∈ accessible T p)
    (h : ∀ C ∈ accessible T p, form C B = form C A) : projection T p A = B := by
  apply sub_eq_zero.mp
  apply (FiniteThreeLevelPositiveHistory.form_self_zero_iff _).mp
  have hz := (accessible T p).sub_mem (projection_mem T p A) hB
  have hp := form_projection_right T p hz A
  have hb := h _ hz
  have hs (X Y Z : MatQ) : form X (Y-Z) = form X Y - form X Z := by
    simp [form, sub_mul, Matrix.trace_sub]
  rw [hs, hp, hb, sub_self]

theorem projection_pythagoras (A : MatQ) :
    ‖feature A‖ ^ 2 =
      ‖feature (projection T p A)‖ ^ 2 + ‖feature (hiddenProjection T p A)‖ ^ 2 := by
  rw [feature_projection, feature_hiddenProjection]
  simpa only [Submodule.starProjection_orthogonal_val] using
    (Submodule.norm_sq_eq_add_norm_sq_starProjection (feature A) (featureRange T p))

theorem projection_contraction (A : MatQ) :
    ‖feature (projection T p A)‖ ≤ ‖feature A‖ := by
  rw [feature_projection]
  exact (featureRange T p).norm_starProjection_apply_le _

theorem projection_one : projection T p 1 = 1 :=
  projection_fixed T p (one_mem_accessible T p)

theorem form_one_left (A : MatQ) : form 1 A = mean A := by
  simp only [form, Matrix.conjTranspose_one, Matrix.mul_one]
  rw [Matrix.mul_assoc, FiniteThreeLevelPositiveHistory.R_square, Matrix.trace_mul_comm]
  rfl

theorem projection_mean (A : MatQ) : mean (projection T p A) = mean A := by
  rw [← form_one_left, form_projection_right T p (one_mem_accessible T p), form_one_left]

theorem projection_full (h : accessible T p = ⊤) : projection T p = LinearMap.id := by
  apply LinearMap.ext
  intro A
  exact projection_fixed T p (by rw [h]; trivial)

theorem compressed_invariant (O : MatQ →ₗ[ℂ] MatQ) :
    Invariant T p ((projection T p).comp O) := fun A _ => projection_mem T p (O A)

variable (ho : 0 < o) (hT : Stationary T) (hp : 0 ≤ p) (hp1 : p ≤ 1)

def compression (O : MatQ →ₗ[ℂ] MatQ) :
    Reconstructed T ho hT p hp hp1 →ₗ[ℂ] Reconstructed T ho hT p hp hp1 :=
  transfer T p ho hT hp hp1 ((projection T p).comp O) (compressed_invariant T p O)

theorem coordinates_compression (O : MatQ →ₗ[ℂ] MatQ)
    (z : Reconstructed T ho hT p hp hp1) :
    coordinates T ho hT p hp hp1 (compression T p ho hT hp hp1 O z) =
      projection T p (O (coordinates T ho hT p hp hp1 z)) :=
  coordinates_transfer T p ho hT hp hp1 _ _ z

theorem coordinates_mem (z : Reconstructed T ho hT p hp hp1) :
    coordinates T ho hT p hp hp1 z ∈ accessible T p := by
  rw [← coordinates_range T ho hT p hp hp1]
  exact ⟨z, rfl⟩

theorem compression_exact (O : MatQ →ₗ[ℂ] MatQ) (hO : Invariant T p O) :
    compression T p ho hT hp hp1 O = transfer T p ho hT hp hp1 O hO := by
  ext z
  apply coordinates_injective T ho hT p hp hp1
  rw [coordinates_compression, coordinates_transfer]
  exact projection_fixed T p (hO _ (coordinates_mem T p ho hT hp hp1 z))

theorem compression_choice_independent (O : MatQ →ₗ[ℂ] MatQ)
    {C : (History o n → ℂ) →ₗ[ℂ] (History o n → ℂ)}
    (hC : ExactLift T p ((projection T p).comp O) C) :
    transferOfLift T p ho hT hp hp1 hC = compression T p ho hT hp hp1 O :=
  transferOfLift_independent T p ho hT hp hp1 hC
    (chosenLift_exact T p _ (compressed_invariant T p O))

/-- Scalar ranges give identity for every unital ambient map. -/
theorem compression_scalar (hs : accessible T p = Submodule.span ℂ {(1 : MatQ)})
    (O : MatQ →ₗ[ℂ] MatQ) (hO : O 1 = 1) :
    compression T p ho hT hp hp1 O = LinearMap.id := by
  apply LinearMap.ext
  intro z
  apply coordinates_injective T ho hT p hp hp1
  rw [coordinates_compression]
  have hz := coordinates_mem T p ho hT hp hp1 z
  rw [hs, Submodule.mem_span_singleton] at hz
  obtain ⟨c, hc⟩ := hz
  change projection T p (O (coordinates T ho hT p hp hp1 z)) =
    coordinates T ho hT p hp hp1 z
  rw [← hc, map_smul, hO, map_smul, projection_one]

theorem projection_scalar (hs : accessible T p = Submodule.span ℂ {(1 : MatQ)}) (A : MatQ) :
    projection T p A = mean A • 1 := by
  have hm := projection_mem T p A
  rw [hs, Submodule.mem_span_singleton] at hm
  obtain ⟨a,ha⟩ := hm
  have hmean := projection_mean T p A
  rw [← ha] at hmean
  change FiniteThreeLevelHistoryTransfer.meanLinear (a • 1) = mean A at hmean
  rw [map_smul] at hmean
  change a * mean 1 = mean A at hmean
  rw [FiniteThreeLevelHistoryTransfer.mean_one, mul_one] at hmean
  rw [← ha, hmean]

theorem compression_reset (O : MatQ →ₗ[ℂ] MatQ) (hO : O 1 = 1) :
    compression T 0 ho hT (by norm_num) (by norm_num) O = LinearMap.id :=
  compression_scalar T 0 ho hT _ _ (reset_range T) O hO

open FinitePositiveKernel.GibbsObservable

/-- Actual normalized insertion, represented on the old quotient without O-invariance. -/
theorem inserted_pairing_compression {m : ℕ} (L : Fin m → MatQ) (hL : IsKrausChannel L)
    (hcomm : ∀ A, Channel.heisenberg L (Psi p A) = Psi p (Channel.heisenberg L A))
    (f g : History o n → ℂ) :
    pairing (insertedKernel T p ho hT hp hp1 L hL) f g =
      ⟪mk (kernel T ho hT p hp hp1) (kernel_posSemidef T ho hT p hp hp1) f,
        compression T p ho hT hp hp1 (Channel.heisenbergLinear L)
          (mk (kernel T ho hT p hp hp1) (kernel_posSemidef T ho hT p hp hp1) g)⟫_ℂ := by
  rw [inserted_pairing_form T p ho hT hp hp1 L hL hcomm,
    coordinates_inner, coordinates_compression, coordinates_mk, coordinates_mk]
  symm
  apply form_projection_right
  rw [← synthesis_range]
  exact ⟨f, rfl⟩

theorem projection_hidden (A : MatQ) : projection T p (hiddenProjection T p A) = 0 := by
  change projection T p (A - projection T p A) = 0
  rw [map_sub, projection_idempotent, sub_self]

theorem hidden_fixed_zero {A : MatQ} (hA : A ∈ accessible T p) :
    hiddenProjection T p A = 0 := by
  change A - projection T p A = 0
  rw [projection_fixed T p hA, sub_self]

/-- Composition is rightmost first; the returning hidden term has a plus sign. -/
theorem composition_defect (U V : MatQ →ₗ[ℂ] MatQ) :
    (projection T p).comp (U.comp (V.comp (projection T p))) -
      (projection T p).comp (U.comp ((projection T p).comp (V.comp (projection T p)))) =
      (projection T p).comp (U.comp ((hiddenProjection T p).comp (V.comp (projection T p)))) := by
  apply LinearMap.ext
  intro A
  change projection T p (U (V (projection T p A))) -
    projection T p (U (projection T p (V (projection T p A)))) =
    projection T p (U (V (projection T p A) - projection T p (V (projection T p A))))
  rw [map_sub, map_sub]

theorem coordinates_compression_defect (U V : MatQ →ₗ[ℂ] MatQ)
    (z : Reconstructed T ho hT p hp hp1) :
    coordinates T ho hT p hp hp1
      (compression T p ho hT hp hp1 (U.comp V) z -
        compression T p ho hT hp hp1 U (compression T p ho hT hp hp1 V z)) =
    projection T p (U (hiddenProjection T p (V (coordinates T ho hT p hp hp1 z)))) := by
  rw [map_sub, coordinates_compression, coordinates_compression, coordinates_compression]
  change projection T p (U (V _)) - projection T p (U (projection T p (V _))) =
    projection T p (U (V _ - projection T p (V _)))
  rw [map_sub, map_sub]

theorem compression_comp_of_invariant (U V : MatQ →ₗ[ℂ] MatQ)
    (hV : Invariant T p V) :
    compression T p ho hT hp hp1 (U.comp V) =
      (compression T p ho hT hp hp1 U).comp (compression T p ho hT hp hp1 V) := by
  apply LinearMap.ext
  intro z
  apply coordinates_injective T ho hT p hp hp1
  change coordinates T ho hT p hp hp1 (compression T p ho hT hp hp1 (U.comp V) z) =
    coordinates T ho hT p hp hp1
      (compression T p ho hT hp hp1 U (compression T p ho hT hp hp1 V z))
  rw [coordinates_compression, coordinates_compression, coordinates_compression,
    projection_fixed T p (hV _ (coordinates_mem T p ho hT hp hp1 z))]
  rfl

def compressedPhase (ω : Q → ℝ) (t : ℝ) :
    Reconstructed T ho hT p hp hp1 →L[ℂ] Reconstructed T ho hT p hp hp1 :=
  (compression T p ho hT hp hp1 (rotate ω t)).toContinuousLinearMap

theorem compressedPhase_adjoint_inner (ω : Q → ℝ) (t : ℝ)
    (z w : Reconstructed T ho hT p hp hp1) :
    ⟪compressedPhase T p ho hT hp hp1 ω t z, w⟫_ℂ =
      ⟪z, compressedPhase T p ho hT hp hp1 ω (-t) w⟫_ℂ := by
  change ⟪compression T p ho hT hp hp1 (rotate ω t) z, w⟫_ℂ =
    ⟪z, compression T p ho hT hp hp1 (rotate ω (-t)) w⟫_ℂ
  rw [coordinates_inner, coordinates_inner, coordinates_compression, coordinates_compression,
    projection_symmetric, projection_fixed T p (coordinates_mem T p ho hT hp hp1 w),
    form_projection_right T p (coordinates_mem T p ho hT hp hp1 z),
    FiniteThreeLevelHistoryTransfer.rotate_form_adjoint]

theorem compressedPhase_adjoint (ω : Q → ℝ) (t : ℝ) :
    (compressedPhase T p ho hT hp hp1 ω t).adjoint =
      compressedPhase T p ho hT hp hp1 ω (-t) := by
  ext z
  apply ext_inner_left ℂ
  intro w
  rw [ContinuousLinearMap.adjoint_inner_right]
  exact compressedPhase_adjoint_inner T p ho hT hp hp1 ω t w z

theorem form_hidden_pair (A B : MatQ) :
    form (hiddenProjection T p A) (hiddenProjection T p B) =
      form A B - form (projection T p A) (projection T p B) := by
  rw [← feature_inner, ← feature_inner, ← feature_inner]
  change ⟪featureLinear (A - projection T p A), featureLinear (B - projection T p B)⟫_ℂ =
    ⟪feature A, feature B⟫_ℂ - ⟪feature (projection T p A), feature (projection T p B)⟫_ℂ
  rw [map_sub, map_sub, inner_sub_left, inner_sub_right, inner_sub_right]
  have h (X Y : MatQ) : ⟪featureLinear X, featureLinear Y⟫_ℂ = form X Y :=
    feature_inner X Y
  rw [h, h, h, h, feature_inner, feature_inner]
  simp only [projection_symmetric, projection_idempotent]
  ring

theorem feature_rotate_norm (ω : Q → ℝ) (t : ℝ) (A : MatQ) :
    ‖feature (rotate ω t A)‖ = ‖feature A‖ := by
  have h : ‖feature (rotate ω t A)‖ ^ 2 = ‖feature A‖ ^ 2 := by
    rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ),
      feature_inner, feature_inner, FiniteThreeLevelHistoryTransfer.rotate_form]
  nlinarith [norm_nonneg (feature (rotate ω t A)), norm_nonneg (feature A)]

theorem coordinate_feature_norm (z : Reconstructed T ho hT p hp hp1) :
    ‖feature (coordinates T ho hT p hp hp1 z)‖ = ‖z‖ :=
  (embedding T ho hT p hp hp1).norm_map z

theorem compressedPhase_norm_le (ω : Q → ℝ) (t : ℝ) :
    ‖compressedPhase T p ho hT hp hp1 ω t‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  rw [one_mul, ← coordinate_feature_norm T p ho hT hp hp1]
  change ‖feature (coordinates T ho hT p hp hp1
    (compression T p ho hT hp hp1 (rotate ω t) z))‖ ≤ ‖z‖
  rw [coordinates_compression]
  calc
    _ ≤ ‖feature (rotate ω t (coordinates T ho hT p hp hp1 z))‖ :=
      projection_contraction T p _
    _ = ‖z‖ := by rw [feature_rotate_norm, coordinate_feature_norm]

/-- The feature-valued leakage uses the correct weighted metric. -/
def leakage (ω : Q → ℝ) (t : ℝ) :
    Reconstructed T ho hT p hp hp1 →ₗ[ℂ] MatQ :=
  featureLinear.comp ((hiddenProjection T p).comp
    ((rotate ω t).comp (coordinates T ho hT p hp hp1)))

theorem inverse_defect_pairing (ω : Q → ℝ) (t : ℝ)
    (z w : Reconstructed T ho hT p hp hp1) :
    ⟪z, w - compressedPhase T p ho hT hp hp1 ω (-t)
      (compressedPhase T p ho hT hp hp1 ω t w)⟫_ℂ =
      ⟪leakage T p ho hT hp hp1 ω t z, leakage T p ho hT hp hp1 ω t w⟫_ℂ := by
  rw [inner_sub_right, ← compressedPhase_adjoint_inner]
  change ⟪z,w⟫_ℂ -
    ⟪compression T p ho hT hp hp1 (rotate ω t) z,
      compression T p ho hT hp hp1 (rotate ω t) w⟫_ℂ =
    ⟪feature (hiddenProjection T p (rotate ω t (coordinates T ho hT p hp hp1 z))),
      feature (hiddenProjection T p (rotate ω t (coordinates T ho hT p hp hp1 w)))⟫_ℂ
  rw [feature_inner, form_hidden_pair, FiniteThreeLevelHistoryTransfer.rotate_form,
    coordinates_inner, coordinates_inner, coordinates_compression, coordinates_compression]

theorem inverse_defect_quadratic (ω : Q → ℝ) (t : ℝ)
    (z : Reconstructed T ho hT p hp hp1) :
    (⟪z, z - compressedPhase T p ho hT hp hp1 ω (-t)
      (compressedPhase T p ho hT hp hp1 ω t z)⟫_ℂ).re =
      ‖leakage T p ho hT hp hp1 ω t z‖ ^ 2 := by
  rw [inverse_defect_pairing, norm_sq_eq_re_inner (𝕜 := ℂ)]
  rfl

local instance : TopologicalSpace MatQ :=
  PseudoMetricSpace.toUniformSpace.toTopologicalSpace (α := MatQ)

/-- Feature-valued leakage, continuous in the actual quotient norm. -/
def leakageContinuous (ω : Q → ℝ) (t : ℝ) :
    Reconstructed T ho hT p hp hp1 →L[ℂ] MatQ :=
  (leakage T p ho hT hp hp1 ω t).toContinuousLinearMap

theorem inverse_defect_operator (ω : Q → ℝ) (t : ℝ) :
    ContinuousLinearMap.id ℂ _ -
      (compressedPhase T p ho hT hp hp1 ω (-t)).comp
        (compressedPhase T p ho hT hp hp1 ω t) =
    (leakageContinuous T p ho hT hp hp1 ω t).adjoint.comp
      (leakageContinuous T p ho hT hp hp1 ω t) := by
  ext w
  apply ext_inner_left ℂ
  intro z
  change ⟪z, w - compressedPhase T p ho hT hp hp1 ω (-t)
    (compressedPhase T p ho hT hp hp1 ω t w)⟫_ℂ = _
  rw [inverse_defect_pairing, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.adjoint_inner_right]
  rfl

theorem inverse_defect_nonzero_iff (ω : Q → ℝ) (t : ℝ) :
    ContinuousLinearMap.id ℂ _ -
      (compressedPhase T p ho hT hp hp1 ω (-t)).comp
        (compressedPhase T p ho hT hp hp1 ω t) ≠ 0 ↔
    ∃ z, hiddenProjection T p (rotate ω t (coordinates T ho hT p hp hp1 z)) ≠ 0 := by
  constructor
  · intro hn
    by_contra h
    push Not at h
    apply hn
    ext z
    apply ext_inner_left ℂ
    intro w
    change ⟪w, z - compressedPhase T p ho hT hp hp1 ω (-t)
      (compressedPhase T p ho hT hp hp1 ω t z)⟫_ℂ = ⟪w, 0⟫_ℂ
    rw [inverse_defect_pairing]
    change ⟪feature (hiddenProjection T p (rotate ω t (coordinates T ho hT p hp hp1 w))),
      feature (hiddenProjection T p (rotate ω t (coordinates T ho hT p hp hp1 z)))⟫_ℂ = _
    rw [h z]
    change ⟪_, featureLinear 0⟫_ℂ = _
    simp only [map_zero, inner_zero_right]
  · rintro ⟨z,hz⟩ he
    have hv := congrArg (fun M => M z) he
    have hq := inverse_defect_quadratic T p ho hT hp hp1 ω t z
    change z - compressedPhase T p ho hT hp hp1 ω (-t)
      (compressedPhase T p ho hT hp hp1 ω t z) = 0 at hv
    rw [hv, inner_zero_right, Complex.zero_re] at hq
    have hl : leakage T p ho hT hp hp1 ω t z = 0 :=
      norm_eq_zero.mp (by nlinarith [norm_nonneg (leakage T p ho hT hp hp1 ω t z)])
    apply hz
    apply FiniteThreeLevelPositiveHistory.feature_injective
    exact hl.trans (map_zero featureLinear).symm

theorem phase_group (ω : Q → ℝ) (t s : ℝ) :
    rotate ω (t+s) = (rotate ω t).comp (rotate ω s) := by
  apply LinearMap.ext
  intro A
  exact (FiniteThreeLevelHistoryTransfer.rotate_group ω t s A).symm

theorem phase_composition_defect (ω : Q → ℝ) (t s : ℝ)
    (z : Reconstructed T ho hT p hp hp1) :
    coordinates T ho hT p hp hp1
      (compressedPhase T p ho hT hp hp1 ω (t+s) z -
        compressedPhase T p ho hT hp hp1 ω t (compressedPhase T p ho hT hp hp1 ω s z)) =
      projection T p (rotate ω t (hiddenProjection T p
        (rotate ω s (coordinates T ho hT p hp hp1 z)))) := by
  change coordinates T ho hT p hp hp1
    (compression T p ho hT hp hp1 (rotate ω (t+s)) z -
      compression T p ho hT hp hp1 (rotate ω t)
        (compression T p ho hT hp hp1 (rotate ω s) z)) = _
  rw [phase_group]
  exact coordinates_compression_defect T p ho hT hp hp1 _ _ z

/-- Negative parameters here belong only to the algebraic unitary phase group. -/
theorem phase_comp_of_invariant (ω : Q → ℝ) (t s : ℝ) (hV : Invariant T p (rotate ω s)) :
    compressedPhase T p ho hT hp hp1 ω (t+s) =
      (compressedPhase T p ho hT hp hp1 ω t).comp (compressedPhase T p ho hT hp hp1 ω s) := by
  apply ContinuousLinearMap.ext
  intro z
  change compression T p ho hT hp hp1 (rotate ω (t+s)) z =
    compression T p ho hT hp hp1 (rotate ω t) (compression T p ho hT hp hp1 (rotate ω s) z)
  rw [phase_group, compression_comp_of_invariant T p ho hT hp hp1 _ _ hV]
  rfl

theorem compression_full (hfull : accessible T p = ⊤) (O : MatQ →ₗ[ℂ] MatQ) :
    compression T p ho hT hp hp1 O =
      transfer T p ho hT hp hp1 O (by intro A _; rw [hfull]; trivial) :=
  compression_exact T p ho hT hp hp1 O _

theorem compression_full_comp (hfull : accessible T p = ⊤) (U V : MatQ →ₗ[ℂ] MatQ) :
    compression T p ho hT hp hp1 (U.comp V) =
      (compression T p ho hT hp hp1 U).comp (compression T p ho hT hp hp1 V) :=
  compression_comp_of_invariant T p ho hT hp hp1 U V (by intro A _; rw [hfull]; trivial)

theorem compression_scalar_comp (hs : accessible T p = Submodule.span ℂ {(1 : MatQ)})
    (U V : MatQ →ₗ[ℂ] MatQ) (hU : U 1 = 1) (hV : V 1 = 1) :
    compression T p ho hT hp hp1 (U.comp V) =
      (compression T p ho hT hp hp1 U).comp (compression T p ho hT hp hp1 V) := by
  rw [compression_scalar T p ho hT hp hp1 hs U hU,
    compression_scalar T p ho hT hp hp1 hs V hV,
    compression_scalar T p ho hT hp hp1 hs (U.comp V) (by simp [hU, hV])]
  rfl

/-- Retained and hidden maps have actual, proved subspace codomains. -/
def retained : MatQ →ₗ[ℂ] accessible T p :=
  (projection T p).codRestrict _ (projection_mem T p)

def hidden : MatQ →ₗ[ℂ] (projection T p).ker :=
  (hiddenProjection T p).codRestrict _ (projection_hidden T p)

def blockA (U : MatQ →ₗ[ℂ] MatQ) : accessible T p →ₗ[ℂ] accessible T p :=
  (retained T p).comp (U.comp (accessible T p).subtype)

def blockB (U : MatQ →ₗ[ℂ] MatQ) : (projection T p).ker →ₗ[ℂ] accessible T p :=
  (retained T p).comp (U.comp (projection T p).ker.subtype)

def blockC (U : MatQ →ₗ[ℂ] MatQ) : accessible T p →ₗ[ℂ] (projection T p).ker :=
  (hidden T p).comp (U.comp (accessible T p).subtype)

def blockD (U : MatQ →ₗ[ℂ] MatQ) : (projection T p).ker →ₗ[ℂ] (projection T p).ker :=
  (hidden T p).comp (U.comp (projection T p).ker.subtype)

def visibleOrbit (U : MatQ →ₗ[ℂ] MatQ) (x : MatQ) (k : ℕ) : accessible T p :=
  retained T p ((U ^ k) x)

def hiddenOrbit (U : MatQ →ₗ[ℂ] MatQ) (x : MatQ) (k : ℕ) : (projection T p).ker :=
  hidden T p ((U ^ k) x)

theorem split_observable (x : MatQ) :
    (retained T p x : MatQ) + (hidden T p x : MatQ) = x := by
  change projection T p x + (x - projection T p x) = x
  abel

theorem visible_coupled (U : MatQ →ₗ[ℂ] MatQ) (x : MatQ) (k : ℕ) :
    visibleOrbit T p U x (k+1) =
      blockA T p U (visibleOrbit T p U x k) + blockB T p U (hiddenOrbit T p U x k) := by
  apply Subtype.ext
  change projection T p ((U ^ (k+1)) x) =
    projection T p (U (projection T p ((U ^ k) x))) +
      projection T p (U (hiddenProjection T p ((U ^ k) x)))
  rw [pow_succ', Module.End.mul_apply, ← map_add, ← map_add]
  change projection T p (U ((U ^ k) x)) =
    projection T p (U ((retained T p ((U ^ k) x) : MatQ) + hidden T p ((U ^ k) x)))
  rw [split_observable]

theorem hidden_coupled (U : MatQ →ₗ[ℂ] MatQ) (x : MatQ) (k : ℕ) :
    hiddenOrbit T p U x (k+1) =
      blockC T p U (visibleOrbit T p U x k) + blockD T p U (hiddenOrbit T p U x k) := by
  apply Subtype.ext
  change hiddenProjection T p ((U ^ (k+1)) x) =
    hiddenProjection T p (U (projection T p ((U ^ k) x))) +
      hiddenProjection T p (U (hiddenProjection T p ((U ^ k) x)))
  rw [pow_succ', Module.End.mul_apply, ← map_add, ← map_add]
  change hiddenProjection T p (U ((U ^ k) x)) =
    hiddenProjection T p (U ((retained T p ((U ^ k) x) : MatQ) + hidden T p ((U ^ k) x)))
  rw [split_observable]

/-- Elimination is an induction on the derived coupled equations, including k=0. -/
theorem hidden_elimination (U : MatQ →ₗ[ℂ] MatQ) (x : MatQ) (k : ℕ) :
    hiddenOrbit T p U x k =
      (blockD T p U ^ k) (hidden T p x) +
        ∑ j ∈ Finset.range k, (blockD T p U ^ (k-1-j))
          (blockC T p U (visibleOrbit T p U x j)) := by
  induction k with
  | zero => simp [hiddenOrbit]
  | succ k ih =>
    rw [hidden_coupled, ih, map_add, map_sum, Finset.sum_range_succ]
    have hs : ∑ j ∈ Finset.range k,
        blockD T p U ((blockD T p U ^ (k-1-j))
          (blockC T p U (visibleOrbit T p U x j))) =
        ∑ j ∈ Finset.range k, (blockD T p U ^ (k+1-1-j))
          (blockC T p U (visibleOrbit T p U x j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have he : k+1-1-j = (k-1-j)+1 := by
        have := Finset.mem_range.mp hj
        omega
      rw [he, pow_succ', Module.End.mul_apply]
    rw [hs, pow_succ', Module.End.mul_apply]
    simp only [Nat.add_sub_cancel, Nat.sub_self, pow_zero, Module.End.one_apply]
    abel

/-- Actual block kernels; finite-dimensional realization does not imply finite lag. -/
def memoryKernel (U : MatQ →ₗ[ℂ] MatQ) (k : ℕ) :
    accessible T p →ₗ[ℂ] accessible T p :=
  (blockB T p U).comp ((blockD T p U ^ k).comp (blockC T p U))

theorem visible_memory (U : MatQ →ₗ[ℂ] MatQ) (x : MatQ) (k : ℕ) :
    visibleOrbit T p U x (k+1) =
      blockA T p U (visibleOrbit T p U x k) +
      blockB T p U ((blockD T p U ^ k) (hidden T p x)) +
      ∑ j ∈ Finset.range k, memoryKernel T p U (k-1-j) (visibleOrbit T p U x j) := by
  rw [visible_coupled, hidden_elimination, map_add, map_sum]
  simp only [memoryKernel, LinearMap.comp_apply]
  abel

theorem hidden_initial_accessible (x : MatQ) (hx : x ∈ accessible T p) :
    hidden T p x = 0 := by
  apply Subtype.ext
  exact hidden_fixed_zero T p hx

theorem memoryKernel_zero (U : MatQ →ₗ[ℂ] MatQ) (x : accessible T p) :
    (memoryKernel T p U 0 x : MatQ) =
      projection T p (U (U x)) - projection T p (U (projection T p (U x))) := by
  simp only [memoryKernel, pow_zero, LinearMap.comp_apply, Module.End.one_apply]
  change projection T p (U (hiddenProjection T p (U x))) = _
  change projection T p (U (U x - projection T p (U x))) = _
  rw [map_sub, map_sub]

end SKEFTHawking.QuantumNetwork.FiniteThreeLevelCompressedStrategyMemory
