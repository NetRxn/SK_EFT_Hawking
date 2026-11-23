import SKEFTHawking.DKMBootstrap.BECPeriodicCommutator
import SKEFTHawking.DKMBootstrap.BECInteriorCommutator
import Physlib.QuantumMechanics.Operators.SpectralTheory.SelfAdjoint
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts
import Mathlib.Analysis.Calculus.Deriv.Star

/-!
# Spatial reflection and periodic parity kinetic cores

Reflection is complex-linear pullback by negation on the circle with normalized Haar
measure. The finite Fourier domain and kinetic action below are the actual domain and
action of `BECPeriodicCommutator`. Both closed parity Hilbert spaces have dense projected
Fourier cores on which the kinetic is essentially self-adjoint. Parity refers to this
periodic Hilbert space. The physical half-interval unitary transports these closures to
self-adjoint wall kinetics on interval Lebesgue L². Actual compact interior tests enter
both wall domains, with action minus a times the ordinary second derivative, through
smooth reflected lifts and an adjoint argument. The operator cores used here are the
finite Fourier parity cores. Bounded potentials and interacting Fock Hamiltonians remain
separate constructions.
-/

noncomputable section
open Complex MeasureTheory
namespace SKEFTHawking.DKMBootstrap.BECWallParity
open BECPeriodicCommutator

variable (L : ℝ) [Fact (0 < L)]

/-- Geometric reflection preserves normalized Haar measure. -/
theorem neg_measurePreserving :
    MeasurePreserving (fun x : AddCircle L ↦ -x)
      AddCircle.haarAddCircle AddCircle.haarAddCircle :=
  Measure.measurePreserving_neg _

/-- Complex-linear spatial pullback, with full ambient L² norm preservation. -/
def reflection : ModeSpace L →ₗᵢ[ℂ] ModeSpace L :=
  Lp.compMeasurePreservingₗᵢ ℂ _ (neg_measurePreserving L)

theorem reflection_ae (u : ModeSpace L) :
    (reflection L u : AddCircle L → ℂ) =ᵐ[AddCircle.haarAddCircle]
      (fun x ↦ u (-x)) :=
  Lp.coeFn_compMeasurePreserving u (neg_measurePreserving L)

@[simp] theorem reflection_norm (u : ModeSpace L) : ‖reflection L u‖ = ‖u‖ :=
  (reflection L).norm_map u

@[simp] theorem reflection_involution (u : ModeSpace L) :
    reflection L (reflection L u) = u := by
  apply Lp.ext
  have h := (neg_measurePreserving L).quasiMeasurePreserving.ae_eq (reflection_ae L u)
  filter_upwards [reflection_ae L (reflection L u), h] with x hx hh
  exact hx.trans (by simpa using hh)

/-- Bundled unitary spatial involution; no amplitude conjugation is used. -/
def reflectionEquiv : ModeSpace L ≃ₗᵢ[ℂ] ModeSpace L :=
  LinearIsometryEquiv.ofSurjective (reflection L)
    (fun u ↦ ⟨reflection L u, reflection_involution L u⟩)

omit [Fact (0 < L)] in
/-- The spatial character identity exchanges the signed Fourier indices. -/
theorem fourier_reflection (n : ℤ) (x : AddCircle L) :
    fourier n (-x) = fourier (-n) x := by
  simp only [fourier_apply, smul_neg, neg_smul]

@[simp] theorem reflection_mode (n : ℤ) :
    reflection L (mode L n) = mode L (-n) := by
  apply Lp.ext
  have h := (neg_measurePreserving L).quasiMeasurePreserving.ae_eq
    (coeFn_fourierLp 2 n)
  filter_upwards [reflection_ae L (mode L n), h, coeFn_fourierLp 2 (-n)]
    with x hr hn hm
  exact hr.trans (hn.trans ((fourier_reflection L n x).trans hm.symm))

/-- Reflection preserves the existing finite Fourier core. -/
theorem reflection_mem_trigDomain {u : ModeSpace L} (hu : u ∈ trigDomain L) :
    reflection L u ∈ trigDomain L := by
  rw [trigDomain_eq_span] at hu ⊢
  induction hu using Submodule.span_induction with
  | mem u hu =>
    obtain ⟨n, rfl⟩ := hu
    rw [reflection_mode]
    exact Submodule.subset_span ⟨-n, rfl⟩
  | zero => simp
  | add u v _ _ hu hv => simpa using (Submodule.add_mem _ hu hv)
  | smul b u _ hu => simpa using (Submodule.smul_mem _ b hu)

/-- Restriction of geometric reflection to the actual invariant core. -/
def coreReflection : trigDomain L →ₗ[ℂ] trigDomain L :=
  ((reflection L).toLinearMap.comp (trigDomain L).subtype).codRestrict
    (trigDomain L) (fun u ↦ reflection_mem_trigDomain L u.2)

@[simp] theorem coe_coreReflection (u : trigDomain L) :
    (coreReflection L u : ModeSpace L) = reflection L (u : ModeSpace L) := rfl

@[simp] theorem coreReflection_mode (n : ℤ) :
    coreReflection L (domainMode L n) = domainMode L (-n) := by
  apply Subtype.ext
  simp

/-- The existing kinetic commutes with spatial reflection on its actual finite domain. -/
theorem kinetic_coreReflection (c : ℝ) (u : trigDomain L) :
    kinetic L c (coreReflection L u) = coreReflection L (kinetic L c u) := by
  obtain ⟨v, rfl⟩ := (trigEquiv L).surjective u
  induction v using Finsupp.induction_linear with
  | zero => simp
  | add v w hv hw => simp only [map_add, hv, hw]
  | single n b =>
    have hs : trigEquiv L (Finsupp.single n b) = b • domainMode L n := by
      rw [domainMode, ← map_smul]
      simp
    simp only [hs, map_smul, coreReflection_mode, kinetic_domainMode, Int.cast_neg,
      neg_sq]

/-- Closed eigenspace of the actual spatial reflection. -/
def paritySpace (σ : ℂ) : Submodule ℂ (ModeSpace L) :=
  ((reflection L).toContinuousLinearMap - σ • ContinuousLinearMap.id ℂ (ModeSpace L)).ker

@[simp] theorem mem_paritySpace (σ : ℂ) (u : ModeSpace L) :
    u ∈ paritySpace L σ ↔ reflection L u = σ • u := by
  simp [paritySpace, sub_eq_zero]

theorem paritySpace_closed (σ : ℂ) : IsClosed (paritySpace L σ : Set (ModeSpace L)) :=
  ContinuousLinearMap.isClosed_ker _

instance paritySpace_complete (σ : ℂ) : CompleteSpace (paritySpace L σ) := by
  haveI := paritySpace_closed L σ
  exact IsClosed.completeSpace_coe

/-- The ambient parity projection `(I + σ R)/2`, for signs satisfying `σ² = 1`. -/
def projection (σ : ℂ) : ModeSpace L →L[ℂ] ModeSpace L :=
  (1 / 2 : ℂ) • (ContinuousLinearMap.id ℂ (ModeSpace L) +
    σ • (reflection L).toContinuousLinearMap)

theorem projection_apply (σ : ℂ) (u : ModeSpace L) :
    projection L σ u = (1 / 2 : ℂ) • (u + σ • reflection L u) := rfl

theorem projection_mem (σ : ℂ) (hσ : σ ^ 2 = 1) (u : ModeSpace L) :
    projection L σ u ∈ paritySpace L σ := by
  rw [mem_paritySpace, projection_apply]
  simp only [map_smul, map_add, reflection_involution]
  have hs : σ * σ = 1 := by simpa only [pow_two] using hσ
  simp only [smul_add, smul_smul]
  rw [show σ * (1 / 2 * σ) = (1 / 2 : ℂ) by linear_combination (1 / 2 : ℂ) * hs]
  module

theorem projection_eq_self (σ : ℂ) (hσ : σ ^ 2 = 1) (u : paritySpace L σ) :
    projection L σ (u : ModeSpace L) = u := by
  have hu := (mem_paritySpace L σ u).mp u.2
  rw [projection_apply, hu, smul_smul, ← pow_two, hσ, one_smul]
  module

theorem projection_idempotent (σ : ℂ) (hσ : σ ^ 2 = 1) (u : ModeSpace L) :
    projection L σ (projection L σ u) = projection L σ u :=
  projection_eq_self L σ hσ ⟨_, projection_mem L σ hσ u⟩

theorem projection_range (σ : ℂ) (hσ : σ ^ 2 = 1) :
    (projection L σ).toLinearMap.range = paritySpace L σ := by
  apply le_antisymm
  · rintro _ ⟨u, rfl⟩
    exact projection_mem L σ hσ u
  · intro u hu
    exact ⟨u, projection_eq_self L σ hσ ⟨u, hu⟩⟩

/-- Projection valued in the closed parity Hilbert space. -/
def projectionInto (σ : ℂ) (hσ : σ ^ 2 = 1) :
    ModeSpace L →L[ℂ] paritySpace L σ :=
  (projection L σ).codRestrict _ (projection_mem L σ hσ)

theorem projectionInto_surjective (σ : ℂ) (hσ : σ ^ 2 = 1) :
    Function.Surjective (projectionInto L σ hσ) := by
  intro u
  exact ⟨u, Subtype.ext (projection_eq_self L σ hσ u)⟩

/-- Finite Fourier vectors in the parity Hilbert space, with the ambient domain unchanged. -/
def parityCore (σ : ℂ) : Submodule ℂ (paritySpace L σ) :=
  (trigDomain L).comap (paritySpace L σ).subtype

theorem projection_mem_trigDomain (σ : ℂ) (u : trigDomain L) :
    projection L σ (u : ModeSpace L) ∈ trigDomain L := by
  rw [projection_apply]
  exact Submodule.smul_mem _ _ (Submodule.add_mem _ u.2
    (Submodule.smul_mem _ _ (reflection_mem_trigDomain L u.2)))

/-- The finite parity core is exactly the projected existing finite Fourier core. -/
theorem parityCore_eq_projected (σ : ℂ) (hσ : σ ^ 2 = 1) :
    parityCore L σ = (trigDomain L).map (projectionInto L σ hσ).toLinearMap := by
  apply le_antisymm
  · intro u hu
    exact ⟨u, hu, Subtype.ext (projection_eq_self L σ hσ u)⟩
  · rintro u ⟨v, hv, rfl⟩
    exact projection_mem_trigDomain L σ ⟨v, hv⟩

/-- Density is in the closed parity carrier, rather than in ambient L². -/
theorem parityCore_dense (σ : ℂ) (hσ : σ ^ 2 = 1) :
    (parityCore L σ).topologicalClosure = ⊤ := by
  rw [parityCore_eq_projected L σ hσ]
  exact (projectionInto_surjective L σ hσ).denseRange.topologicalClosure_map_submodule
    (trigDomain_dense L)

/-- The constant mode is a nonzero even vector. -/
theorem even_witness : mode L 0 ∈ paritySpace L 1 ∧ mode L 0 ≠ 0 := by
  constructor
  · simp
  · intro h
    have hn := mode_normalized L 0
    rw [h, norm_zero] at hn
    exact zero_ne_one hn

/-- The signed pair of actual Fourier modes is a nonzero odd vector. -/
theorem odd_witness :
    mode L 1 - mode L (-1) ∈ paritySpace L (-1) ∧
      mode L 1 - mode L (-1) ≠ 0 := by
  constructor
  · simp only [mem_paritySpace, map_sub, reflection_mode, neg_neg, neg_smul, one_smul]
    abel
  · intro h
    have he := sub_eq_zero.mp h
    have hi := congrArg (fun u : ModeSpace L ↦ inner ℂ (mode L 1) u) he
    rw [orthonormal_iff_ite.mp (modes_orthonormal L),
      orthonormal_iff_ite.mp (modes_orthonormal L)] at hi
    norm_num at hi

/-- The odd and even carriers are genuinely different subspaces of the same L² space. -/
theorem paritySpaces_distinct : paritySpace L 1 ≠ paritySpace L (-1) := by
  intro h
  have ho : mode L 0 ∈ paritySpace L (-1) := h ▸ (even_witness L).1
  have he := (mem_paritySpace L (-1) (mode L 0)).mp ho
  simp only [reflection_mode, neg_zero, neg_smul, one_smul] at he
  have hz : mode L 0 = 0 := by
    have ht : (2 : ℂ) • mode L 0 = 0 := by
      rw [two_smul]
      nth_rw 1 [he]
      exact neg_add_cancel _
    exact (smul_eq_zero.mp ht).resolve_left (by norm_num)
  exact (even_witness L).2 hz

/-- Core projection constructed from the already proved invariant reflection. -/
def coreProjection (σ : ℂ) : trigDomain L →ₗ[ℂ] trigDomain L :=
  (1 / 2 : ℂ) • (LinearMap.id + σ • coreReflection L)

@[simp] theorem coe_coreProjection (σ : ℂ) (u : trigDomain L) :
    (coreProjection L σ u : ModeSpace L) = projection L σ (u : ModeSpace L) := rfl

theorem kinetic_coreProjection (c : ℝ) (σ : ℂ) (u : trigDomain L) :
    kinetic L c (coreProjection L σ u) = coreProjection L σ (kinetic L c u) := by
  simp only [coreProjection, LinearMap.smul_apply, LinearMap.add_apply, LinearMap.id_apply,
    map_smul, map_add, kinetic_coreReflection]

theorem kinetic_mem_paritySpace (c : ℝ) (σ : ℂ) (u : trigDomain L)
    (hu : (u : ModeSpace L) ∈ paritySpace L σ) :
    (kinetic L c u : ModeSpace L) ∈ paritySpace L σ := by
  have hr : coreReflection L u = σ • u := by
    apply Subtype.ext
    exact (mem_paritySpace L σ u).mp hu
  rw [mem_paritySpace, ← coe_coreReflection, ← kinetic_coreReflection, hr, map_smul]
  rfl

/-- Inclusion of finite parity vectors into the original finite Fourier domain. -/
def coreInclusion (σ : ℂ) : parityCore L σ →ₗ[ℂ] trigDomain L where
  toFun u := ⟨u.1.1, u.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- The parity operator uses the existing kinetic, restricted to the actual common domain. -/
def parityKinetic (c : ℝ) (σ : ℂ) : parityCore L σ →ₗ[ℂ] paritySpace L σ :=
  (((trigDomain L).subtype.comp (kinetic L c)).comp (coreInclusion L σ)).codRestrict
    (paritySpace L σ) (fun u ↦ kinetic_mem_paritySpace L c σ _ u.1.2)

@[simp] theorem coe_parityKinetic (c : ℝ) (σ : ℂ) (u : parityCore L σ) :
    (parityKinetic L c σ u : ModeSpace L) =
      (kinetic L c (coreInclusion L σ u) : ModeSpace L) := rfl

/-- The partial unbounded kinetic on the closed parity Hilbert carrier. -/
def parityPMap (c : ℝ) (σ : ℂ) : paritySpace L σ →ₗ.[ℂ] paritySpace L σ where
  domain := parityCore L σ
  toFun := parityKinetic L c σ

theorem parityPMap_symmetric (c : ℝ) (σ : ℂ) :
    DFT.IsSymmetricPMap (parityPMap L c σ) := by
  intro u v
  exact kineticPMap_symmetric L c (coreInclusion L σ u) (coreInclusion L σ v)

theorem parityPMap_dense (c : ℝ) (σ : ℂ) (hσ : σ ^ 2 = 1) :
    Dense ((parityPMap L c σ).domain : Set (paritySpace L σ)) :=
  Submodule.dense_iff_topologicalClosure_eq_top.mpr (parityCore_dense L σ hσ)

/-- Projection commutes with the actual imaginary shifted kinetic on the Fourier core. -/
theorem shiftedKinetic_coreProjection (c μ : ℝ) (σ : ℂ) (u : trigDomain L) :
    shiftedKinetic L c μ (coreProjection L σ u) =
      projection L σ (shiftedKinetic L c μ u) := by
  simp only [shiftedKinetic, LinearMap.sub_apply, LinearMap.comp_apply,
    LinearMap.smul_apply, Submodule.subtype_apply, kinetic_coreProjection,
    coe_coreProjection, map_sub, map_smul]

/-- Project finite preimages for the existing shifted kinetic into the parity core. -/
theorem parity_shifted_preimage (c μ : ℝ) (hμ : μ ≠ 0) (σ : ℂ) (hσ : σ ^ 2 = 1)
    (v : parityCore L σ) :
    ∃ u : (parityPMap L c σ).domain,
      parityPMap L c σ u - (Complex.I * (μ : ℂ)) • (u : paritySpace L σ) = v := by
  obtain ⟨x, hx⟩ := trigDomain_le_shiftedKinetic_range L c μ hμ v.2
  let u : parityCore L σ :=
    ⟨projectionInto L σ hσ (x : ModeSpace L), projection_mem_trigDomain L σ x⟩
  refine ⟨u, Subtype.ext ?_⟩
  change shiftedKinetic L c μ (coreProjection L σ x) = (v.1 : ModeSpace L)
  rw [shiftedKinetic_coreProjection, hx]
  exact projection_eq_self L σ hσ v.1

theorem parityPMap_dense_shifted_range (c μ : ℝ) (hμ : μ ≠ 0)
    (σ : ℂ) (hσ : σ ^ 2 = 1) :
    Dense {w : paritySpace L σ | ∃ u : (parityPMap L c σ).domain,
      parityPMap L c σ u - (Complex.I * (μ : ℂ)) • (u : paritySpace L σ) = w} := by
  apply (parityPMap_dense L c σ hσ).mono
  intro w hw
  exact parity_shifted_preimage L c μ hμ σ hσ ⟨w, hw⟩

/-- Essential self-adjointness in either periodic parity carrier, on its finite Fourier core. -/
theorem parityPMap_closure_selfAdjoint (c : ℝ) (σ : ℂ) (hσ : σ ^ 2 = 1) :
    IsSelfAdjoint (parityPMap L c σ).closure :=
  DFT.isSelfAdjoint_closure_of_dense_range (parityPMap_symmetric L c σ)
    (parityPMap_dense L c σ hσ) one_ne_zero
    (parityPMap_dense_shifted_range L c 1 one_ne_zero σ hσ)
    (parityPMap_dense_shifted_range L c (-1) (by norm_num) σ hσ)

theorem even_closure_selfAdjoint (c : ℝ) :
    IsSelfAdjoint (parityPMap L c 1).closure :=
  parityPMap_closure_selfAdjoint L c 1 (by norm_num)

theorem odd_closure_selfAdjoint (c : ℝ) :
    IsSelfAdjoint (parityPMap L c (-1)).closure :=
  parityPMap_closure_selfAdjoint L c (-1) (by norm_num)

/-- The original finite parity domain is an operator core of the closure. -/
theorem parityPMap_closure_hasCore (c : ℝ) (σ : ℂ) :
    (parityPMap L c σ).closure.HasCore (parityCore L σ) :=
  (parityPMap L c σ).closureHasCore

/-- Projected actual Fourier character, as a vector of the finite parity domain. -/
def parityMode (σ : ℂ) (hσ : σ ^ 2 = 1) (n : ℤ) : parityCore L σ :=
  ⟨projectionInto L σ hσ (mode L n), by
    change projection L σ (mode L n) ∈ trigDomain L
    simpa only [coe_domainMode] using projection_mem_trigDomain L σ (domainMode L n)⟩

/-- The paired eigenvectors are built from the actual `±n` Haar L² characters. -/
theorem coe_parityMode (σ : ℂ) (hσ : σ ^ 2 = 1) (n : ℤ) :
    ((parityMode L σ hσ n : paritySpace L σ) : ModeSpace L) =
      (1 / 2 : ℂ) • (mode L n + σ • mode L (-n)) := by
  change projection L σ (mode L n) = _
  rw [projection_apply, reflection_mode]

theorem parityKinetic_parityMode (c : ℝ) (σ : ℂ) (hσ : σ ^ 2 = 1) (n : ℤ) :
    parityKinetic L c σ (parityMode L σ hσ n) =
      ((c : ℂ) * (n : ℂ)^2) • (parityMode L σ hσ n : paritySpace L σ) := by
  apply Subtype.ext
  have hc : coreInclusion L σ (parityMode L σ hσ n) =
      coreProjection L σ (domainMode L n) := by
    apply Subtype.ext
    change projection L σ (mode L n) = projection L σ (domainMode L n : ModeSpace L)
    rw [coe_domainMode]
  rw [coe_parityKinetic, hc, kinetic_coreProjection, kinetic_domainMode, map_smul]
  simp only [Submodule.coe_smul, coe_coreProjection, coe_domainMode, coe_parityMode,
    projection_apply, reflection_mode]

/-- Every nonzero signed index gives a nonzero parity vector in both sectors. -/
theorem parityMode_ne_zero (σ : ℂ) (hσ : σ ^ 2 = 1) {n : ℤ} (hn : n ≠ 0) :
    parityMode L σ hσ n ≠ 0 := by
  intro hz
  have hi := congrArg
    (fun u : parityCore L σ ↦ inner ℂ (mode L n) ((u : paritySpace L σ) : ModeSpace L)) hz
  rw [coe_parityMode] at hi
  have hne : n ≠ -n := by omega
  simp only [inner_smul_right, inner_add_right,
    orthonormal_iff_ite.mp (modes_orthonormal L), hne, ↓reduceIte,
    mul_zero, add_zero, mul_one, ZeroMemClass.coe_zero, inner_zero_right] at hi
  norm_num at hi

/-- The zero mode is retained by even projection. -/
theorem even_projection_zero_mode : projection L 1 (mode L 0) = mode L 0 := by
  rw [projection_apply, reflection_mode]
  simp only [neg_zero, one_smul]
  module

/-- The odd projection removes the zero mode. -/
theorem odd_projection_zero_mode : projection L (-1) (mode L 0) = 0 := by
  rw [projection_apply, reflection_mode]
  simp

/-- Canonical finite-core inclusion in the parity closure domain. -/
def parityClosureCore (c : ℝ) (σ : ℂ) (u : parityCore L σ) :
    (parityPMap L c σ).closure.domain :=
  ⟨u, (parityPMap L c σ).le_closure.1 u.2⟩

/-- Closing the parity kinetic preserves the existing ambient kinetic action exactly. -/
theorem parityClosure_apply_core (c : ℝ) (σ : ℂ) (u : parityCore L σ) :
    ((parityPMap L c σ).closure (parityClosureCore L c σ u) : ModeSpace L) =
      (kinetic L c (coreInclusion L σ u) : ModeSpace L) := by
  have h := ((parityPMap L c σ).le_closure.2
    (x := u) (y := parityClosureCore L c σ u) rfl).symm
  exact congrArg (fun v : paritySpace L σ ↦ (v : ModeSpace L)) h

/-- The parity closures retain the actual second-derivative action on their Fourier cores.
This statement uses normalized circle Haar measure, without an interval identification. -/
theorem parityClosure_eq_neg_second_deriv_ae (a : ℝ) (σ : ℂ) (u : parityCore L σ) :
    ∀ᵐ z : AddCircle L ∂AddCircle.haarAddCircle, ∀ x : ℝ, (x : AddCircle L) = z →
      (((parityPMap L (scale L a) σ).closure
        (parityClosureCore L (scale L a) σ u) : ModeSpace L) : AddCircle L → ℂ) z =
        -(a : ℂ) * deriv (deriv (representativeLift L (coreInclusion L σ u))) x := by
  rw [parityClosure_apply_core]
  exact kinetic_eq_neg_second_deriv_ae L a (coreInclusion L σ u)

section PhysicalVolume

variable (T : ℝ) [Fact (0 < T)]

/-- Physical periodic Lebesgue L², with period `T` (not the wall interval length). -/
abbrev VolumeSpace := Lp ℂ 2 (volume : Measure (AddCircle T))

/-- The scalar relating physical volume to normalized Haar is strictly positive. -/
theorem volumeScalar_pos : 0 < ENNReal.ofReal T := by
  exact ENNReal.ofReal_pos.mpr (Fact.out : 0 < T)

/-- The actual circle volume, without replacing it by a normalized surrogate. -/
theorem volume_eq_period_smul_haar :
    (volume : Measure (AddCircle T)) = ENNReal.ofReal T • AddCircle.haarAddCircle :=
  AddCircle.volume_eq_smul_haarAddCircle

/-- Nonzero rescaling preserves precisely the null sets used by both L² quotients. -/
theorem volume_ae_eq_haar :
    ae (volume : Measure (AddCircle T)) = ae AddCircle.haarAddCircle := by
  rw [volume_eq_period_smul_haar,
    Measure.ae_ennreal_smul_measure_eq (ne_of_gt (volumeScalar_pos T))]

/-- Retain representatives while changing to actual physical volume. Norms scale by `√T`. -/
def retainVolume : ModeSpace T →ₗ[ℂ] VolumeSpace T where
  toFun u := (Lp.memLp u).of_haarAddCircle.toLp u
  map_add' u v := by
    apply Lp.ext
    have h := Lp.coeFn_add u v
    rw [← volume_ae_eq_haar T] at h
    filter_upwards [(Lp.memLp (u + v)).of_haarAddCircle.coeFn_toLp,
      (Lp.memLp u).of_haarAddCircle.coeFn_toLp,
      (Lp.memLp v).of_haarAddCircle.coeFn_toLp, h,
      Lp.coeFn_add ((Lp.memLp u).of_haarAddCircle.toLp u)
        ((Lp.memLp v).of_haarAddCircle.toLp v)] with x huv hu hv ha hb
    simp only [Pi.add_apply] at ha hb
    rw [huv, ha, hb, hu, hv]
  map_smul' b u := by
    apply Lp.ext
    have h := Lp.coeFn_smul b u
    rw [← volume_ae_eq_haar T] at h
    filter_upwards [(Lp.memLp (b • u)).of_haarAddCircle.coeFn_toLp,
      (Lp.memLp u).of_haarAddCircle.coeFn_toLp, h,
      Lp.coeFn_smul b ((Lp.memLp u).of_haarAddCircle.toLp u)] with x hbu hu ha hb
    simp only [Pi.smul_apply, RingHom.id_apply] at ha hb ⊢
    rw [hbu, ha, hb, hu]

theorem retainVolume_ae (u : ModeSpace T) :
    (retainVolume T u : AddCircle T → ℂ) =ᵐ[volume] u :=
  (Lp.memLp u).of_haarAddCircle.coeFn_toLp

/-- The reverse change of measure also retains the actual representative. -/
def retainHaar (u : VolumeSpace T) : ModeSpace T :=
  (Lp.memLp u).haarAddCircle.toLp u

theorem retainHaar_ae (u : VolumeSpace T) :
    (retainHaar T u : AddCircle T → ℂ) =ᵐ[AddCircle.haarAddCircle] u :=
  (Lp.memLp u).haarAddCircle.coeFn_toLp

@[simp] theorem retainHaar_retainVolume (u : ModeSpace T) :
    retainHaar T (retainVolume T u) = u := by
  apply Lp.ext
  have h := retainVolume_ae T u
  rw [volume_ae_eq_haar T] at h
  exact (retainHaar_ae T _).trans h

@[simp] theorem retainVolume_retainHaar (u : VolumeSpace T) :
    retainVolume T (retainHaar T u) = u := by
  apply Lp.ext
  have h := retainHaar_ae T u
  rw [← volume_ae_eq_haar T] at h
  exact (retainVolume_ae T _).trans h

/-- The unnormalized change of measure is an actual complex linear equivalence. -/
def retainVolumeEquiv : ModeSpace T ≃ₗ[ℂ] VolumeSpace T :=
  { retainVolume T with
    invFun := retainHaar T
    left_inv := retainHaar_retainVolume T
    right_inv := retainVolume_retainHaar T }

/-- Retaining a representative multiplies its norm by the square root of physical period. -/
theorem retainVolume_norm (u : ModeSpace T) :
    ‖retainVolume T u‖ = Real.sqrt T * ‖u‖ := by
  rw [Lp.norm_def, eLpNorm_congr_ae (retainVolume_ae T u), volume_eq_period_smul_haar,
    eLpNorm_smul_measure_of_ne_zero (ne_of_gt (volumeScalar_pos T))]
  simp only [smul_eq_mul, ENNReal.toReal_mul, ← ENNReal.toReal_rpow,
    ENNReal.toReal_ofReal (le_of_lt (Fact.out : 0 < T)), ← Lp.norm_def]
  norm_num [Real.sqrt_eq_rpow]

/-- Haar-to-volume isometry: the retained representative is multiplied by `T⁻¹/²`. -/
def volumeIsometry : ModeSpace T →ₗᵢ[ℂ] VolumeSpace T where
  toLinearMap := ((Real.sqrt T)⁻¹ : ℂ) • retainVolume T
  norm_map' u := by
    simp only [LinearMap.smul_apply, norm_smul, retainVolume_norm, norm_inv,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg T)]
    rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (Fact.out : 0 < T))),
      one_mul]

theorem volumeIsometry_surjective : Function.Surjective (volumeIsometry T) := by
  intro u
  refine ⟨retainHaar T ((Real.sqrt T : ℂ) • u), ?_⟩
  change ((Real.sqrt T)⁻¹ : ℂ) • retainVolume T _ = u
  rw [retainVolume_retainHaar, smul_smul]
  simp [Real.sqrt_ne_zero'.mpr (Fact.out : 0 < T)]

/-- Surjective complex linear isometry between actual Haar and physical Lebesgue L². -/
def volumeUnitary : ModeSpace T ≃ₗᵢ[ℂ] VolumeSpace T :=
  LinearIsometryEquiv.ofSurjective (volumeIsometry T) (volumeIsometry_surjective T)

theorem volumeUnitary_ae (u : ModeSpace T) :
    (volumeUnitary T u : AddCircle T → ℂ) =ᵐ[volume]
      (fun x ↦ ((Real.sqrt T)⁻¹ : ℂ) * u x) := by
  change (((Real.sqrt T)⁻¹ : ℂ) • retainVolume T u : VolumeSpace T) =ᵐ[volume] _
  filter_upwards [Lp.coeFn_smul ((Real.sqrt T)⁻¹ : ℂ) (retainVolume T u),
    retainVolume_ae T u] with x hs hu
  simpa only [Pi.smul_apply, smul_eq_mul, hu] using hs

/-- The unscaled Fourier character in actual physical volume L². -/
def volumeCharacter (n : ℤ) : VolumeSpace T :=
  ContinuousMap.toLp 2 volume ℂ (fourier n)

/-- Fourier normalization is `1/√T` on the actual period-`T` volume carrier. -/
theorem volumeUnitary_mode (n : ℤ) :
    volumeUnitary T (mode T n) = ((Real.sqrt T)⁻¹ : ℂ) • volumeCharacter T n := by
  apply Lp.ext
  have hn := coeFn_fourierLp (T := T) 2 n
  rw [← volume_ae_eq_haar T] at hn
  filter_upwards [volumeUnitary_ae T (mode T n), hn,
    Lp.coeFn_smul ((Real.sqrt T)⁻¹ : ℂ) (volumeCharacter T n),
    ContinuousMap.coeFn_toLp (p := 2) (𝕜 := ℂ) volume (fourier n)] with x hu hn hs hc
  change (volumeCharacter T n : AddCircle T → ℂ) x = fourier n x at hc
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  rw [hu, hn, hs, hc]

theorem normalized_volumeCharacters :
    Orthonormal ℂ (fun n : ℤ ↦ ((Real.sqrt T)⁻¹ : ℂ) • volumeCharacter T n) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [← volumeUnitary_mode, ← volumeUnitary_mode, (volumeUnitary T).inner_map_map]
  exact orthonormal_iff_ite.mp (modes_orthonormal T) i j

/-- Actual periodic self-adjoint kinetic, carried into physical Lebesgue volume L². -/
def volumeKinetic (c : ℝ) : VolumeSpace T →ₗ.[ℂ] VolumeSpace T :=
  (kineticPMap T c).closure.unitaryConj (volumeUnitary T)

theorem volumeKinetic_selfAdjoint (c : ℝ) : IsSelfAdjoint (volumeKinetic T c) :=
  LinearPMap.unitaryConj_isSelfAdjoint (volumeUnitary T)
    (kineticPMap_closure_selfAdjoint T c)

/-- Exact carrying map on the full accepted periodic closure domain. -/
def volumeKineticDomain (c : ℝ) (u : (kineticPMap T c).closure.domain) :
    (volumeKinetic T c).domain :=
  ⟨volumeUnitary T (u : ModeSpace T),
    LinearPMap.map_mem_unitaryConj_domain (volumeUnitary T) _ u⟩

theorem volumeKinetic_apply (c : ℝ) (u : (kineticPMap T c).closure.domain) :
    volumeKinetic T c (volumeKineticDomain T c u) =
      volumeUnitary T ((kineticPMap T c).closure u) :=
  LinearPMap.unitaryConj_apply_map (volumeUnitary T) _ u

/-- The carried kinetic retains the actual minus-second-derivative action on the core. -/
theorem volumeKinetic_core_ae (a : ℝ) (u : trigDomain T) :
    ∀ᵐ z : AddCircle T ∂volume, ∀ x : ℝ, (x : AddCircle T) = z →
      (volumeKinetic T (scale T a)
        (volumeKineticDomain T (scale T a) (closureCore T (scale T a) u))
          : AddCircle T → ℂ) z =
        ((Real.sqrt T)⁻¹ : ℂ) *
          (-(a : ℂ) * deriv (deriv (representativeLift T u)) x) := by
  rw [volumeKinetic_apply]
  have h := kineticPMap_closure_eq_neg_second_deriv_ae T a u
  rw [← volume_ae_eq_haar T] at h
  filter_upwards [volumeUnitary_ae T ((kineticPMap T (scale T a)).closure
    (closureCore T (scale T a) u)), h] with z hu hz
  intro x hx
  rw [hu, hz x hx]

/-- Bounded cosine multiplication transported by the actual volume unitary. -/
def volumeCosineMultiplier : VolumeSpace T →L[ℂ] VolumeSpace T :=
  (volumeUnitary T).toContinuousLinearEquiv.toContinuousLinearMap.comp
    ((cosineMultiplier T).comp
      (volumeUnitary T).symm.toContinuousLinearEquiv.toContinuousLinearMap)

@[simp] theorem volumeCosineMultiplier_map (u : ModeSpace T) :
    volumeCosineMultiplier T (volumeUnitary T u) =
      volumeUnitary T (cosineMultiplier T u) := by
  simp [volumeCosineMultiplier]

/-- The transported bounded operator is actual multiplication by the same cosine. -/
theorem volumeCosineMultiplier_ae (u : VolumeSpace T) :
    (volumeCosineMultiplier T u : AddCircle T → ℂ) =ᵐ[volume]
      (fun x ↦ cosine T x * u x) := by
  obtain ⟨v, rfl⟩ := (volumeUnitary T).surjective u
  rw [volumeCosineMultiplier_map]
  have h := cosineMultiplier_ae T v
  rw [← volume_ae_eq_haar T] at h
  filter_upwards [volumeUnitary_ae T (cosineMultiplier T v),
    volumeUnitary_ae T v, h] with x hc hv hm
  rw [hc, hv, hm]
  ring

/-- The entire actual common domain of the periodic bracket carries to physical volume. -/
theorem volumeCosineMultiplier_mem (c : ℝ) (u : (kineticPMap T c).closure.domain)
    (hu : cosineMultiplier T (u : ModeSpace T) ∈ (kineticPMap T c).closure.domain) :
    volumeCosineMultiplier T (volumeKineticDomain T c u : VolumeSpace T) ∈
      (volumeKinetic T c).domain := by
  change volumeCosineMultiplier T (volumeUnitary T (u : ModeSpace T)) ∈ _
  rw [volumeCosineMultiplier_map]
  exact LinearPMap.map_mem_unitaryConj_domain (volumeUnitary T) _ ⟨_, hu⟩

/-- Exact transport of the accepted closure bracket, on its full common domain. -/
theorem volume_bracket_map (c : ℝ) (u : (kineticPMap T c).closure.domain)
    (hu : cosineMultiplier T (u : ModeSpace T) ∈ (kineticPMap T c).closure.domain) :
    volumeKinetic T c
        ⟨volumeCosineMultiplier T (volumeKineticDomain T c u : VolumeSpace T),
          volumeCosineMultiplier_mem T c u hu⟩ -
      volumeCosineMultiplier T (volumeKinetic T c (volumeKineticDomain T c u)) =
        volumeUnitary T ((kineticPMap T c).closure ⟨cosineMultiplier T u, hu⟩ -
          cosineMultiplier T ((kineticPMap T c).closure u)) := by
  have he : (⟨volumeCosineMultiplier T (volumeKineticDomain T c u : VolumeSpace T),
      volumeCosineMultiplier_mem T c u hu⟩ : (volumeKinetic T c).domain) =
      volumeKineticDomain T c ⟨cosineMultiplier T u, hu⟩ := by
    apply Subtype.ext
    exact volumeCosineMultiplier_map T u
  rw [he, volumeKinetic_apply, volumeKinetic_apply, volumeCosineMultiplier_map, map_sub]

/-- Physical-volume normalization cannot create a bounded extension of the closure bracket. -/
theorem no_bounded_volume_bracket_extension {c : ℝ} (hc : 0 < c) :
    ¬ ∃ B : VolumeSpace T →L[ℂ] VolumeSpace T,
      ∀ v : (volumeKinetic T c).domain,
      ∀ hv : volumeCosineMultiplier T (v : VolumeSpace T) ∈ (volumeKinetic T c).domain,
        B (v : VolumeSpace T) = volumeKinetic T c
          ⟨volumeCosineMultiplier T (v : VolumeSpace T), hv⟩ -
            volumeCosineMultiplier T (volumeKinetic T c v) := by
  rintro ⟨B, hB⟩
  apply no_bounded_closure_bracket_extension T hc
  refine ⟨(volumeUnitary T).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
    (B.comp (volumeUnitary T).toContinuousLinearEquiv.toContinuousLinearMap), ?_⟩
  intro u hu
  have h := hB (volumeKineticDomain T c u) (volumeCosineMultiplier_mem T c u hu)
  rw [volume_bracket_map T c u hu] at h
  exact congrArg (volumeUnitary T).symm h |>.trans ((volumeUnitary T).symm_apply_apply _)

end PhysicalVolume

section HalfInterval

open scoped ENNReal

variable (T : ℝ) [Fact (0 < T)]

/-- The physical wall interval has length `L = T/2`; the periodic carrier has period `T`. -/
abbrev HalfSpace := Lp ℂ 2 (volume.restrict (Set.Ioo 0 (T / 2)))

theorem halfInterval_measure_le_cell :
    volume.restrict (Set.Ioo 0 (T / 2)) ≤
      volume.restrict (Set.Ioc 0 (0 + T)) := by
  apply Measure.restrict_mono_set
  intro x hx
  exact ⟨hx.1, by linarith [hx.2, (Fact.out : 0 < T)]⟩

/-- Pulling back volume-null sets to the actual positive half-period is legitimate. -/
theorem ae_half_of_volume {P : AddCircle T → Prop} (h : ∀ᵐ z ∂volume, P z) :
    ∀ᵐ x : ℝ ∂volume.restrict (Set.Ioo 0 (T / 2)), P (x : AddCircle T) :=
  (AddCircle.measurePreserving_mk T 0).quasiMeasurePreserving.ae h |>.filter_mono
    (ae_mono (halfInterval_measure_le_cell T))

/-- Actual restriction of a periodic volume L² representative is square integrable. -/
theorem half_memLp (u : VolumeSpace T) :
    MemLp (fun x : ℝ ↦ u (x : AddCircle T)) 2
      (volume.restrict (Set.Ioo 0 (T / 2))) :=
  ((Lp.memLp u).comp_measurePreserving (AddCircle.measurePreserving_mk T 0)).mono_measure
    (halfInterval_measure_le_cell T)

/-- Restriction to `(0,L)`, `L=T/2`, on actual Lebesgue L² quotients. No wall domain asserted. -/
def halfRestriction : VolumeSpace T →ₗ[ℂ] HalfSpace T where
  toFun u := (half_memLp T u).toLp (fun x : ℝ ↦ u (x : AddCircle T))
  map_add' u v := by
    apply Lp.ext
    have h := ae_half_of_volume T (Lp.coeFn_add u v)
    filter_upwards [(half_memLp T (u + v)).coeFn_toLp,
      (half_memLp T u).coeFn_toLp, (half_memLp T v).coeFn_toLp, h,
      Lp.coeFn_add ((half_memLp T u).toLp _) ((half_memLp T v).toLp _)]
      with x huv hu hv ha hb
    simp only [Pi.add_apply] at ha hb
    rw [huv, ha, hb, hu, hv]
  map_smul' b u := by
    apply Lp.ext
    have h := ae_half_of_volume T (Lp.coeFn_smul b u)
    filter_upwards [(half_memLp T (b • u)).coeFn_toLp, (half_memLp T u).coeFn_toLp,
      h, Lp.coeFn_smul b ((half_memLp T u).toLp _)] with x hbu hu ha hb
    simp only [Pi.smul_apply, RingHom.id_apply] at ha hb ⊢
    rw [hbu, ha, hb, hu]

theorem halfRestriction_ae (u : VolumeSpace T) :
    (halfRestriction T u : ℝ → ℂ) =ᵐ[volume.restrict (Set.Ioo 0 (T / 2))]
      (fun x ↦ u (x : AddCircle T)) :=
  (half_memLp T u).coeFn_toLp

/-- The accepted Haar parity equality becomes the actual odd/even relation on the half cell. -/
theorem parity_half_ae (σ : ℂ) (u : paritySpace T σ) :
    ∀ᵐ x : ℝ ∂volume.restrict (Set.Ioo 0 (T / 2)),
      u.1 ((-x : ℝ) : AddCircle T) = σ * u.1 (x : AddCircle T) := by
  have h := reflection_ae T (u : ModeSpace T)
  rw [(mem_paritySpace T σ u).mp u.2] at h
  have hs := Lp.coeFn_smul σ (u : ModeSpace T)
  have hp : ∀ᵐ z ∂AddCircle.haarAddCircle, u.1 (-z) = σ * u.1 z := by
    filter_upwards [h, hs] with z hz hsz
    exact hz.symm.trans hsz
  rw [← volume_ae_eq_haar T] at hp
  simpa only [AddCircle.coe_neg] using ae_half_of_volume T hp

/-- Haar parity restriction at the physical `L⁻¹/²` scale.
The norm identity and explicit odd/even inverse are proved below. -/
def parityHalfRestriction (σ : ℂ) : paritySpace T σ →ₗ[ℂ] HalfSpace T :=
  ((Real.sqrt (T / 2))⁻¹ : ℂ) •
    ((halfRestriction T).comp ((retainVolume T).comp (paritySpace T σ).subtype))

theorem parityHalfRestriction_ae (σ : ℂ) (u : paritySpace T σ) :
    (parityHalfRestriction T σ u : ℝ → ℂ) =ᵐ[volume.restrict (Set.Ioo 0 (T / 2))]
      (fun x ↦ ((Real.sqrt (T / 2))⁻¹ : ℂ) * u.1 (x : AddCircle T)) := by
  have h := ae_half_of_volume T (retainVolume_ae T (u : ModeSpace T))
  filter_upwards [h, halfRestriction_ae T (retainVolume T (u : ModeSpace T)),
    Lp.coeFn_smul ((Real.sqrt (T / 2))⁻¹ : ℂ)
      (halfRestriction T (retainVolume T (u : ModeSpace T)))] with x hu hr hs
  change (((Real.sqrt (T / 2))⁻¹ : ℂ) •
    halfRestriction T (retainVolume T (u : ModeSpace T)) : HalfSpace T) x = _
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  rw [hs, hr, hu]

/-- The two open half-cells exhaust a physical period up to null endpoints. -/
theorem volume_lintegral_halves (F : AddCircle T → ℝ≥0∞) :
    (∫⁻ z, F z) =
      (∫⁻ x in Set.Ioo (-(T / 2)) 0, F (x : AddCircle T)) +
      ∫⁻ x in Set.Ioo 0 (T / 2), F (x : AddCircle T) := by
  have hT : 0 < T := Fact.out
  have hc : -(T / 2) + T = T / 2 := by ring
  rw [← AddCircle.lintegral_preimage T (-(T / 2)) F, hc,
    ← Set.Ioc_union_Ioc_eq_Ioc (by linarith : -(T / 2) ≤ 0) (by linarith : 0 ≤ T / 2),
    lintegral_union measurableSet_Ioc (Set.Ioc_disjoint_Ioc_of_le le_rfl)]
  rw [← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := -(T / 2)) (b := 0)),
    ← Measure.restrict_congr_set (Ioo_ae_eq_Ioc (a := 0) (b := T / 2))]

omit [Fact (0 < T)] in
/-- Lebesgue reflection exchanges the actual open half-cells, including their measures. -/
theorem half_lintegral_neg (f : ℝ → ℝ≥0∞) :
    (∫⁻ x in Set.Ioo (-(T / 2)) 0, f x) =
      ∫⁻ x in Set.Ioo 0 (T / 2), f (-x) := by
  have hp : (Neg.neg : ℝ → ℝ) ⁻¹' Set.Ioo (-(T / 2)) 0 = Set.Ioo 0 (T / 2) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_Ioo]
    constructor <;> intro h <;> constructor <;> linarith [h.1, h.2]
  have h := (Measure.measurePreserving_neg (volume : Measure ℝ)).restrict_preimage
    (measurableSet_Ioo (a := -(T / 2)) (b := 0))
  rw [hp] at h
  exact (h.lintegral_comp_emb (Homeomorph.neg ℝ).measurableEmbedding f).symm

/-- A sign with square one has unit complex norm. -/
theorem paritySign_norm (σ : ℂ) (hσ : σ ^ 2 = 1) : ‖σ‖ = 1 := by
  have h : ‖σ‖ ^ 2 = 1 := by rw [← norm_pow, hσ, norm_one]
  nlinarith [norm_nonneg σ]

/-- Physical full-period mass is twice the positive-half mass, by actual parity. -/
theorem parity_volume_mass (σ : ℂ) (hσ : σ ^ 2 = 1) (u : paritySpace T σ) :
    (∫⁻ z : AddCircle T, ‖u.1 z‖ₑ ^ 2) =
      2 * ∫⁻ x in Set.Ioo 0 (T / 2), ‖u.1 (x : AddCircle T)‖ₑ ^ 2 := by
  rw [volume_lintegral_halves T, half_lintegral_neg T]
  have hh : (∫⁻ x in Set.Ioo 0 (T / 2), ‖u.1 ((-x : ℝ) : AddCircle T)‖ₑ ^ 2) =
      ∫⁻ x in Set.Ioo 0 (T / 2), ‖u.1 (x : AddCircle T)‖ₑ ^ 2 := by
    apply lintegral_congr_ae
    filter_upwards [parity_half_ae T σ u] with x hx
    rw [hx, enorm_mul, ← ofReal_norm σ, paritySign_norm σ hσ]
    simp
  rw [hh, two_mul]

/-- Squared L² norm as physical square mass; this applies to both actual measures. -/
theorem lp_norm_sq_mass {α : Type*} [MeasurableSpace α] {μ : Measure α} (u : Lp ℂ 2 μ) :
    ‖u‖ ^ 2 = (∫⁻ x, ‖u x‖ₑ ^ 2 ∂μ).toReal := by
  have h := congrArg (RCLike.re : ℂ → ℝ) (L2.integral_inner_eq_sq_eLpNorm (𝕜 := ℂ) u)
  change RCLike.re (inner ℂ u u) = _ at h
  simpa only [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow, RCLike.ofReal_re,
    ENNReal.rpow_two, enorm_eq_nnnorm] using h

/-- The unscaled restriction has exactly `T/2` times the Haar squared norm. -/
theorem halfRestriction_parity_norm_sq (σ : ℂ) (hσ : σ ^ 2 = 1)
    (u : paritySpace T σ) :
    ‖halfRestriction T (retainVolume T (u : ModeSpace T))‖ ^ 2 =
      (T / 2) * ‖u‖ ^ 2 := by
  have hf : ‖retainVolume T (u : ModeSpace T)‖ ^ 2 =
      (∫⁻ z : AddCircle T, ‖u.1 z‖ₑ ^ 2).toReal := by
    rw [lp_norm_sq_mass]
    congr 1
    exact lintegral_congr_ae ((retainVolume_ae T (u : ModeSpace T)).fun_comp
      (fun z : ℂ ↦ ‖z‖ₑ ^ 2))
  have hh : ‖halfRestriction T (retainVolume T (u : ModeSpace T))‖ ^ 2 =
      (∫⁻ x in Set.Ioo 0 (T / 2), ‖u.1 (x : AddCircle T)‖ₑ ^ 2).toReal := by
    rw [lp_norm_sq_mass]
    congr 1
    apply lintegral_congr_ae
    filter_upwards [halfRestriction_ae T (retainVolume T (u : ModeSpace T)),
      ae_half_of_volume T (retainVolume_ae T (u : ModeSpace T))] with x hx hu
    rw [hx, hu]
  rw [parity_volume_mass T σ hσ u, ENNReal.toReal_mul] at hf
  norm_num only [ENNReal.toReal_ofNat] at hf
  rw [retainVolume_norm, mul_pow, Real.sq_sqrt (le_of_lt (Fact.out : 0 < T))] at hf
  change _ = (T / 2) * ‖(u : ModeSpace T)‖ ^ 2
  linarith

/-- The physical half-interval restriction preserves the actual Haar parity norm. -/
theorem parityHalfRestriction_norm (σ : ℂ) (hσ : σ ^ 2 = 1)
    (u : paritySpace T σ) : ‖parityHalfRestriction T σ u‖ = ‖u‖ := by
  have hn := halfRestriction_parity_norm_sq T σ hσ u
  have hs : 0 < Real.sqrt (T / 2) := Real.sqrt_pos.mpr (by linarith [(Fact.out : 0 < T)])
  have he : ‖halfRestriction T (retainVolume T (u : ModeSpace T))‖ =
      Real.sqrt (T / 2) * ‖u‖ := by
    have hsq := Real.sq_sqrt (le_of_lt (show 0 < T / 2 by linarith [(Fact.out : 0 < T)]))
    apply (sq_eq_sq₀ (norm_nonneg _) (mul_nonneg hs.le (norm_nonneg u))).mp
    rw [mul_pow, hsq]
    exact hn
  change ‖((Real.sqrt (T / 2))⁻¹ : ℂ) •
    halfRestriction T (retainVolume T (u : ModeSpace T))‖ = _
  rw [norm_smul, he]
  simp only [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Real.sqrt_nonneg _)]
  rw [← mul_assoc, inv_mul_cancel₀ (ne_of_gt hs), one_mul]

/-- Isometric physical realization of the closed even or odd parity carrier. -/
def halfIsometry (σ : ℂ) (hσ : σ ^ 2 = 1) : paritySpace T σ →ₗᵢ[ℂ] HalfSpace T where
  toLinearMap := parityHalfRestriction T σ
  norm_map' := parityHalfRestriction_norm T σ hσ

/-- Zero extension on the physical cell, followed by the actual periodic lift. -/
def halfZeroLift (g : HalfSpace T) : VolumeSpace T :=
  (((memLp_indicator_iff_restrict measurableSet_Ioo).mpr (Lp.memLp g)).restrict
    (Set.Ioc (-(T / 2)) (-(T / 2) + T))).memLp_liftIoc.toLp
      (AddCircle.liftIoc T (-(T / 2)) ((Set.Ioo 0 (T / 2)).indicator g))

/-- The zero lift changes measure by retaining its representative, without rescaling. -/
def halfZeroHaar (g : HalfSpace T) : ModeSpace T := retainHaar T (halfZeroLift T g)

theorem halfZeroHaar_ae (g : HalfSpace T) :
    (halfZeroHaar T g : AddCircle T → ℂ) =ᵐ[volume]
      AddCircle.liftIoc T (-(T / 2)) ((Set.Ioo 0 (T / 2)).indicator g) := by
  have hh := retainHaar_ae T (halfZeroLift T g)
  rw [← volume_ae_eq_haar T] at hh
  exact hh.trans (MemLp.coeFn_toLp _)

/-- The lifted zero extension is the input on the positive half and zero on its reflection. -/
theorem halfZeroHaar_half_ae (g : HalfSpace T) :
    ∀ᵐ x : ℝ ∂volume.restrict (Set.Ioo 0 (T / 2)),
      halfZeroHaar T g (x : AddCircle T) = g x ∧
        halfZeroHaar T g ((-x : ℝ) : AddCircle T) = 0 := by
  have hn := (Measure.measurePreserving_neg
    (volume : Measure (AddCircle T))).quasiMeasurePreserving.ae_eq
    (halfZeroHaar_ae T g)
  filter_upwards [ae_half_of_volume T (halfZeroHaar_ae T g),
    ae_half_of_volume T hn, ae_restrict_mem measurableSet_Ioo] with x hx hnx hmem
  have hT : 0 < T := Fact.out
  have hc : x ∈ Set.Ioc (-(T / 2)) (-(T / 2) + T) :=
    ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
  have hnc : -x ∈ Set.Ioc (-(T / 2)) (-(T / 2) + T) :=
    ⟨by linarith [hmem.2], by linarith [hmem.1]⟩
  have hnm : -x ∉ Set.Ioo 0 (T / 2) := by
    intro h
    linarith [h.1, hmem.1]
  constructor
  · rw [hx, AddCircle.liftIoc_coe_apply hc, Set.indicator_of_mem hmem]
  · simpa only [Function.comp_apply, ← AddCircle.coe_neg, AddCircle.liftIoc_coe_apply hnc,
      Set.indicator_of_notMem hnm] using hnx

/-- The actual spatial projection acts on representatives by `(v(x) + σ v(-x))/2`. -/
theorem projection_ae (σ : ℂ) (v : ModeSpace T) :
    (projection T σ v : AddCircle T → ℂ) =ᵐ[AddCircle.haarAddCircle]
      (fun z ↦ (1 / 2 : ℂ) * (v z + σ * v (-z))) := by
  change (((1 / 2 : ℂ) • (v + σ • reflection T v) : ModeSpace T) :
    AddCircle T → ℂ) =ᵐ[AddCircle.haarAddCircle] _
  filter_upwards [Lp.coeFn_smul (1 / 2 : ℂ) (v + σ • reflection T v),
    Lp.coeFn_add v (σ • reflection T v), Lp.coeFn_smul σ (reflection T v),
    reflection_ae T v] with z hs ha ht hr
  simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply] at hs ha ht
  rw [hs, ha, ht, hr]

/-- Projecting the zero lift recovers precisely half of the input on the physical half-cell. -/
theorem halfRestriction_projection_zeroLift (σ : ℂ) (g : HalfSpace T) :
    halfRestriction T (retainVolume T (projection T σ (halfZeroHaar T g))) =
      (1 / 2 : ℂ) • g := by
  apply Lp.ext
  have hp := projection_ae T σ (halfZeroHaar T g)
  rw [← volume_ae_eq_haar T] at hp
  filter_upwards [halfRestriction_ae T (retainVolume T (projection T σ (halfZeroHaar T g))),
    ae_half_of_volume T (retainVolume_ae T (projection T σ (halfZeroHaar T g))),
    ae_half_of_volume T hp, halfZeroHaar_half_ae T g,
    Lp.coeFn_smul (1 / 2 : ℂ) g] with x hh hv hp hz hs
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  rw [hh, hv, hp, ← AddCircle.coe_neg, hz.1, hz.2, mul_zero, add_zero, hs]

/-- A concrete onto witness: scale the parity projection of the actual zero extension. -/
def halfExtension (σ : ℂ) (hσ : σ ^ 2 = 1) (g : HalfSpace T) : paritySpace T σ :=
  (2 * (Real.sqrt (T / 2) : ℂ)) •
    ⟨projection T σ (halfZeroHaar T g), projection_mem T σ hσ _⟩

@[simp] theorem halfIsometry_halfExtension (σ : ℂ) (hσ : σ ^ 2 = 1) (g : HalfSpace T) :
    halfIsometry T σ hσ (halfExtension T σ hσ g) = g := by
  change parityHalfRestriction T σ ((2 * (Real.sqrt (T / 2) : ℂ)) •
    ⟨projection T σ (halfZeroHaar T g), projection_mem T σ hσ _⟩) = g
  rw [map_smul]
  change (2 * (Real.sqrt (T / 2) : ℂ)) • (((Real.sqrt (T / 2))⁻¹ : ℂ) •
    halfRestriction T (retainVolume T (projection T σ (halfZeroHaar T g)))) = g
  rw [halfRestriction_projection_zeroLift, smul_smul, smul_smul]
  have hs : (Real.sqrt (T / 2) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr
      (show 0 < T / 2 by linarith [(Fact.out : 0 < T)]))
  have hc : 2 * (Real.sqrt (T / 2) : ℂ) * (Real.sqrt (T / 2) : ℂ)⁻¹ * (1 / 2) = 1 := by
    field_simp
  rw [hc, one_smul]

theorem halfIsometry_surjective (σ : ℂ) (hσ : σ ^ 2 = 1) :
    Function.Surjective (halfIsometry T σ hσ) :=
  fun g ↦ ⟨halfExtension T σ hσ g, halfIsometry_halfExtension T σ hσ g⟩

/-- The genuine parity-to-physical-interval unitary, with explicit projected extension. -/
def halfUnitary (σ : ℂ) (hσ : σ ^ 2 = 1) : paritySpace T σ ≃ₗᵢ[ℂ] HalfSpace T :=
  LinearIsometryEquiv.ofSurjective (halfIsometry T σ hσ) (halfIsometry_surjective T σ hσ)

/-- The inverse unitary is the explicit scaled projected zero extension. -/
theorem halfUnitary_symm_apply (σ : ℂ) (hσ : σ ^ 2 = 1) (g : HalfSpace T) :
    (halfUnitary T σ hσ).symm g = halfExtension T σ hσ g := by
  apply (halfUnitary T σ hσ).injective
  rw [(halfUnitary T σ hσ).apply_symm_apply]
  exact (halfIsometry_halfExtension T σ hσ g).symm

theorem halfUnitary_ae (σ : ℂ) (hσ : σ ^ 2 = 1) (u : paritySpace T σ) :
    (halfUnitary T σ hσ u : ℝ → ℂ) =ᵐ[volume.restrict (Set.Ioo 0 (T / 2))]
      (fun x ↦ ((Real.sqrt (T / 2))⁻¹ : ℂ) * u.1 (x : AddCircle T)) :=
  parityHalfRestriction_ae T σ u

/-- The self-adjoint parity closure transported to the actual physical interval L². -/
def halfKinetic (c : ℝ) (σ : ℂ) (hσ : σ ^ 2 = 1) : HalfSpace T →ₗ.[ℂ] HalfSpace T :=
  (parityPMap T c σ).closure.unitaryConj (halfUnitary T σ hσ)

theorem halfKinetic_selfAdjoint (c : ℝ) (σ : ℂ) (hσ : σ ^ 2 = 1) :
    IsSelfAdjoint (halfKinetic T c σ hσ) :=
  LinearPMap.unitaryConj_isSelfAdjoint (halfUnitary T σ hσ)
    (parityPMap_closure_selfAdjoint T c σ hσ)

/-- Canonical transport of the entire accepted parity closure domain. -/
def halfKineticDomain (c : ℝ) (σ : ℂ) (hσ : σ ^ 2 = 1)
    (u : (parityPMap T c σ).closure.domain) : (halfKinetic T c σ hσ).domain :=
  ⟨halfUnitary T σ hσ (u : paritySpace T σ),
    LinearPMap.map_mem_unitaryConj_domain (halfUnitary T σ hσ) _ u⟩

theorem halfKinetic_apply (c : ℝ) (σ : ℂ) (hσ : σ ^ 2 = 1)
    (u : (parityPMap T c σ).closure.domain) :
    halfKinetic T c σ hσ (halfKineticDomain T c σ hσ u) =
      halfUnitary T σ hσ ((parityPMap T c σ).closure u) :=
  LinearPMap.unitaryConj_apply_map (halfUnitary T σ hσ) _ u

/-- Physical interval action on the transported finite Fourier parity core. -/
theorem halfKinetic_core_ae (a : ℝ) (σ : ℂ) (hσ : σ ^ 2 = 1)
    (u : parityCore T σ) :
    ∀ᵐ x : ℝ ∂volume.restrict (Set.Ioo 0 (T / 2)),
      (halfKinetic T (scale T a) σ hσ
        (halfKineticDomain T (scale T a) σ hσ (parityClosureCore T (scale T a) σ u))
          : ℝ → ℂ) x =
        ((Real.sqrt (T / 2))⁻¹ : ℂ) *
          (-(a : ℂ) * deriv (deriv (representativeLift T (coreInclusion T σ u))) x) := by
  rw [halfKinetic_apply]
  have hd := parityClosure_eq_neg_second_deriv_ae T a σ u
  rw [← volume_ae_eq_haar T] at hd
  filter_upwards [halfUnitary_ae T σ hσ ((parityPMap T (scale T a) σ).closure
    (parityClosureCore T (scale T a) σ u)), ae_half_of_volume T hd] with x hu hd
  rw [hu, hd x rfl]

omit [Fact (0 < T)] in
/-- The doubled period gives the physical interval kinetic scale `a(π/L)²`, `L=T/2`. -/
theorem halfKinetic_scale (a : ℝ) : scale T a = a * (Real.pi / (T / 2)) ^ 2 := by
  unfold scale
  congr 2
  ring

end HalfInterval

section CompactInterior

open BECInteriorCommutator
open scoped ContDiff ComplexConjugate

variable (T : ℝ) [Fact (0 < T)]

/-- Smooth reflection of an actual compact interior test; there is no piecewise join. -/
def reflectedTest (σ : ℂ) (ψ : Domain 0 (T / 2)) (x : ℝ) : ℂ :=
  ψ x + σ * ψ (-x)

omit [Fact (0 < T)] in
theorem reflectedTest_smooth (σ : ℂ) (ψ : Domain 0 (T / 2)) :
    ContDiff ℝ ∞ (reflectedTest T σ ψ) :=
  ψ.contDiff.add (contDiff_const.mul (ψ.contDiff.comp contDiff_neg))

omit [Fact (0 < T)] in
/-- Reflection preserves compact support of the actual full-line test. -/
theorem reflectedTest_hasCompactSupport (σ : ℂ) (ψ : Domain 0 (T / 2)) :
    HasCompactSupport (reflectedTest T σ ψ) := by
  have hn : HasCompactSupport (fun x : ℝ ↦ ψ (-x)) :=
    ψ.hasCompactSupport.comp_homeomorph (Homeomorph.neg ℝ)
  have hs : HasCompactSupport (fun x : ℝ ↦ σ * ψ (-x)) :=
    hn.comp_left (mul_zero σ)
  unfold reflectedTest
  simpa only [Pi.add_def] using ψ.hasCompactSupport.add hs

omit [Fact (0 < T)] in
/-- Reflection reverses the first real derivative. -/
theorem reflectedTest_deriv (σ : ℂ) (ψ : Domain 0 (T / 2)) :
    deriv (reflectedTest T σ ψ) = reflectedTest T (-σ) (D ψ) := by
  funext x
  have h := (ψ.contDiff.differentiable (by simp)).differentiableAt (x := x)
  have hn := (ψ.contDiff.differentiable (by simp)).differentiableAt (x := -x)
  change deriv (fun y ↦ ψ y + σ * ψ (-y)) x = deriv ψ x + (-σ) * deriv ψ (-x)
  simpa only [Pi.add_def, Function.comp_def, neg_smul, one_smul, mul_neg, neg_mul] using
    ((h.hasDerivAt).add ((hn.hasDerivAt.scomp x (hasDerivAt_neg x)).const_mul σ)).deriv

omit [Fact (0 < T)] in
/-- Twice differentiating restores the same parity, on the actual derivative test. -/
theorem reflectedTest_deriv2 (σ : ℂ) (ψ : Domain 0 (T / 2)) :
    deriv (deriv (reflectedTest T σ ψ)) = reflectedTest T σ (D (D ψ)) := by
  rw [reflectedTest_deriv, reflectedTest_deriv, neg_neg]

omit [Fact (0 < T)] in
theorem reflectedTest_parity (σ : ℂ) (hσ : σ ^ 2 = 1)
    (ψ : Domain 0 (T / 2)) (x : ℝ) :
    reflectedTest T σ ψ (-x) = σ * reflectedTest T σ ψ x := by
  simp only [reflectedTest, neg_neg]
  have hs : σ * σ = 1 := by simpa [pow_two] using hσ
  calc
    ψ (-x) + σ * ψ x = σ * ψ x + (σ * σ) * ψ (-x) := by rw [hs]; ring
    _ = σ * (ψ x + σ * ψ (-x)) := by ring

omit [Fact (0 < T)] in
/-- On the positive half the reflected summand vanishes by the actual support condition. -/
theorem reflectedTest_half (σ : ℂ) (ψ : Domain 0 (T / 2)) {x : ℝ} (hx : 0 ≤ x) :
    reflectedTest T σ ψ x = ψ x := by
  have hn : ψ (-x) = 0 := zero_of_not_mem ψ (by intro h; linarith [h.1])
  simp only [reflectedTest, hn, mul_zero, add_zero]

/-- Both endpoints of the centered cell are outside the reflected compact support. -/
theorem reflectedTest_endpoints (σ : ℂ) (ψ : Domain 0 (T / 2)) :
    reflectedTest T σ ψ (-(T / 2)) = 0 ∧ reflectedTest T σ ψ (T / 2) = 0 := by
  have hp : 0 < T := Fact.out
  have hn : ψ (-(T / 2)) = 0 := zero_of_not_mem ψ (by intro h; linarith [h.1])
  have he : ψ (T / 2) = 0 := (endpoint_data ψ).2.1
  simp [reflectedTest, hn, he]

omit [Fact (0 < T)] in
/-- All the reflected jets vanish near the seam, inherited from compact interior support. -/
theorem reflectedTest_eventually_zero (σ : ℂ) (ψ : Domain 0 (T / 2)) {x : ℝ}
    (hx : x ∉ Set.Ioo 0 (T / 2)) (hnx : -x ∉ Set.Ioo 0 (T / 2)) :
    reflectedTest T σ ψ =ᶠ[nhds x] 0 := by
  have hn := (eventually_zero_of_not_mem ψ hnx).comp_tendsto
    (continuous_neg.continuousAt (x := x))
  filter_upwards [eventually_zero_of_not_mem ψ hx, hn] with y hy hny
  change ψ (-y) = 0 at hny
  simp [reflectedTest, hy, hny]

/-- The reflected support lies strictly inside the centered period cell. -/
theorem reflectedTest_tsupport (σ : ℂ) (ψ : Domain 0 (T / 2)) :
    tsupport (reflectedTest T σ ψ) ⊆ Set.Ioo (-(T / 2)) (T / 2) := by
  intro x hx
  by_contra hn
  have hp : 0 < T := Fact.out
  have h0 : x ∉ Set.Ioo 0 (T / 2) := by
    intro h
    exact hn ⟨by linarith [h.1], h.2⟩
  have h1 : -x ∉ Set.Ioo 0 (T / 2) := by
    intro h
    exact hn ⟨by linarith [h.2], by linarith [h.1]⟩
  exact (notMem_tsupport_iff_eventuallyEq.mpr
    (reflectedTest_eventually_zero T σ ψ h0 h1)) hx

omit [Fact (0 < T)] in
/-- The test and its first two genuine reflected derivatives vanish near either seam. -/
theorem reflectedTest_eventually_zero_derivatives (σ : ℂ) (ψ : Domain 0 (T / 2)) {x : ℝ}
    (hx : x ∉ Set.Ioo 0 (T / 2)) (hnx : -x ∉ Set.Ioo 0 (T / 2)) :
    ∀ᶠ y in nhds x, reflectedTest T σ ψ y = 0 ∧
      deriv (reflectedTest T σ ψ) y = 0 ∧ deriv (deriv (reflectedTest T σ ψ)) y = 0 := by
  filter_upwards [reflectedTest_eventually_zero T σ ψ hx hnx,
    reflectedTest_eventually_zero T (-σ) (D ψ) hx hnx,
    reflectedTest_eventually_zero T σ (D (D ψ)) hx hnx] with y h0 h1 h2
  exact ⟨h0, by simpa only [reflectedTest_deriv, Pi.zero_apply] using h1,
    by simpa only [reflectedTest_deriv2, Pi.zero_apply] using h2⟩

/-- Actual periodic circle representative, with the physical √L normalization. -/
def compactLift (σ : ℂ) (ψ : Domain 0 (T / 2)) : AddCircle T → ℂ :=
  fun z ↦ (Real.sqrt (T / 2) : ℂ) *
    AddCircle.liftIoc T (-(T / 2)) (reflectedTest T σ ψ) z

theorem compactLift_continuous (σ : ℂ) (ψ : Domain 0 (T / 2)) :
    Continuous (compactLift T σ ψ) := by
  apply continuous_const.mul
  apply AddCircle.liftIoc_continuous
  · convert (reflectedTest_endpoints T σ ψ).1.trans
      (reflectedTest_endpoints T σ ψ).2.symm using 1
    congr 1
    ring
  · exact (reflectedTest_smooth T σ ψ).continuous.continuousOn

/-- The representative agrees on the closed cell, including the identified zero endpoints. -/
theorem compactLift_coe (σ : ℂ) (ψ : Domain 0 (T / 2)) {x : ℝ}
    (hx : x ∈ Set.Icc (-(T / 2)) (T / 2)) :
    compactLift T σ ψ (x : AddCircle T) =
      (Real.sqrt (T / 2) : ℂ) * reflectedTest T σ ψ x := by
  unfold compactLift
  congr 1
  by_cases he : x = -(T / 2)
  · subst x
    rw [← AddCircle.coe_add_period T (-(T / 2))]
    rw [AddCircle.liftIoc_coe_apply (by
      constructor <;> linarith [(Fact.out : 0 < T)])]
    have h : -(T / 2) + T = T / 2 := by ring
    rw [h, (reflectedTest_endpoints T σ ψ).1, (reflectedTest_endpoints T σ ψ).2]
  · exact AddCircle.liftIoc_coe_apply ⟨lt_of_le_of_ne hx.1 (Ne.symm he), by linarith [hx.2]⟩

/-- Around every point strictly inside the cell the lift is the smooth reflected function. -/
theorem compactLift_eventually_eq (σ : ℂ) (ψ : Domain 0 (T / 2)) {x : ℝ}
    (hx : x ∈ Set.Ioo (-(T / 2)) (T / 2)) :
    (fun y : ℝ ↦ compactLift T σ ψ (y : AddCircle T)) =ᶠ[nhds x]
      (fun y ↦ (Real.sqrt (T / 2) : ℂ) * reflectedTest T σ ψ y) := by
  filter_upwards [isOpen_Ioo.mem_nhds hx] with y hy
  exact compactLift_coe T σ ψ ⟨hy.1.le, hy.2.le⟩

/-- The periodic representative is zero on a full real neighborhood of its seam. -/
theorem compactLift_seam_eventually_zero (σ : ℂ) (ψ : Domain 0 (T / 2)) :
    (fun y : ℝ ↦ compactLift T σ ψ (y : AddCircle T)) =ᶠ[nhds (T / 2)] 0 := by
  have hp : 0 < T := Fact.out
  have hz := eventually_zero_of_not_mem ψ (x := T / 2) (by simp)
  have hr : (fun y : ℝ ↦ ψ (T - y)) =ᶠ[nhds (T / 2)] 0 := by
    have ht : Filter.Tendsto (fun y : ℝ ↦ T - y) (nhds (T / 2)) (nhds (T / 2)) := by
      have ht := (show Continuous (fun y : ℝ ↦ T - y) from
        continuous_const.sub continuous_id).continuousAt (x := T / 2)
      simpa only [ContinuousAt, show T - T / 2 = T / 2 by ring] using ht
    exact hz.comp_tendsto ht
  filter_upwards [hz, hr, isOpen_Ioo.mem_nhds
    (show T / 2 ∈ Set.Ioo 0 T by constructor <;> linarith)] with y hy hry hb
  change ψ y = 0 at hy
  change ψ (T - y) = 0 at hry
  change compactLift T σ ψ (y : AddCircle T) = 0
  by_cases he : y ≤ T / 2
  · rw [compactLift_coe T σ ψ ⟨by linarith [hb.1], he⟩,
      reflectedTest_half T σ ψ hb.1.le, hy, mul_zero]
  · have hc : ((y - T : ℝ) : AddCircle T) = (y : AddCircle T) := by
      simp only [AddCircle.coe_sub, AddCircle.coe_period, sub_zero]
    rw [← hc, compactLift_coe T σ ψ ⟨by linarith, by linarith [hb.2]⟩]
    have hn : ψ (y - T) = 0 := zero_of_not_mem ψ (by intro h; linarith [h.1, hb.2])
    simp only [reflectedTest, hn, neg_sub, hry, mul_zero, add_zero]

/-- The actual real pullback of the circle lift is globally smooth, including the seam. -/
theorem compactLift_real_smooth (σ : ℂ) (ψ : Domain 0 (T / 2)) :
    ContDiff ℝ ∞ (fun x : ℝ ↦ compactLift T σ ψ (x : AddCircle T)) := by
  apply contDiff_iff_contDiffAt.mpr
  intro x
  let y := AddCircle.equivIoc T (-(T / 2)) (x : AddCircle T)
  have hy : (y : ℝ) ∈ Set.Ioc (-(T / 2)) (T / 2) :=
    ⟨y.prop.1, by linarith [y.prop.2]⟩
  have hs : ContDiffAt ℝ ∞ (fun t : ℝ ↦ compactLift T σ ψ (t : AddCircle T)) y := by
    by_cases he : (y : ℝ) = T / 2
    · rw [he]
      exact contDiffAt_const.congr_of_eventuallyEq (compactLift_seam_eventually_zero T σ ψ)
    · exact (contDiff_const.mul (reflectedTest_smooth T σ ψ)).contDiffAt.congr_of_eventuallyEq
        (compactLift_eventually_eq T σ ψ ⟨hy.1, lt_of_le_of_ne hy.2 he⟩)
  have ht : ContDiffAt ℝ ∞ (fun t : ℝ ↦ t + ((y : ℝ) - x)) x :=
    (contDiff_id.add contDiff_const).contDiffAt
  have he : x + ((y : ℝ) - x) = y := by ring
  rw [← he] at hs
  have h := hs.comp x ht
  convert h using 1
  funext t
  have hc : ((y : ℝ) : AddCircle T) = (x : AddCircle T) := AddCircle.coe_equivIoc
  simp only [Function.comp_def, AddCircle.coe_add, AddCircle.coe_sub, hc, sub_self, add_zero]

theorem compactLift_parity (σ : ℂ) (hσ : σ ^ 2 = 1)
    (ψ : Domain 0 (T / 2)) (z : AddCircle T) :
    compactLift T σ ψ (-z) = σ * compactLift T σ ψ z := by
  let x := AddCircle.equivIoc T (-(T / 2)) z
  have hx : (x : ℝ) ∈ Set.Icc (-(T / 2)) (T / 2) :=
    ⟨x.prop.1.le, by linarith [x.prop.2]⟩
  have hn : -(x : ℝ) ∈ Set.Icc (-(T / 2)) (T / 2) := by
    constructor <;> linarith [hx.1, hx.2]
  have hz : ((x : ℝ) : AddCircle T) = z := AddCircle.coe_equivIoc
  rw [← hz, ← AddCircle.coe_neg, compactLift_coe T σ ψ hn,
    compactLift_coe T σ ψ hx, reflectedTest_parity T σ hσ]
  ring

/-- The continuous reflected compact representative as an actual Haar L² vector. -/
def compactL2 (σ : ℂ) (ψ : Domain 0 (T / 2)) : ModeSpace T :=
  ContinuousMap.toLp 2 AddCircle.haarAddCircle ℂ
    ⟨compactLift T σ ψ, compactLift_continuous T σ ψ⟩

theorem compactL2_ae (σ : ℂ) (ψ : Domain 0 (T / 2)) :
    (compactL2 T σ ψ : AddCircle T → ℂ) =ᵐ[AddCircle.haarAddCircle] compactLift T σ ψ :=
  ContinuousMap.coeFn_toLp _ _

/-- Pointwise parity descends to the true closed parity Hilbert subspace. -/
theorem compactL2_mem_parity (σ : ℂ) (hσ : σ ^ 2 = 1) (ψ : Domain 0 (T / 2)) :
    compactL2 T σ ψ ∈ paritySpace T σ := by
  rw [mem_paritySpace]
  apply Lp.ext
  have hn := (neg_measurePreserving T).quasiMeasurePreserving.ae_eq (compactL2_ae T σ ψ)
  filter_upwards [reflection_ae T (compactL2 T σ ψ), hn,
    compactL2_ae T σ ψ, Lp.coeFn_smul σ (compactL2 T σ ψ)] with z hr hn hz hs
  simp only [Pi.smul_apply, smul_eq_mul] at hs
  dsimp only [Function.comp_def] at hn
  rw [hr, hn, hs, hz]
  exact compactLift_parity T σ hσ ψ z

/-- The actual reflected compact vector in the closed parity space, without a core claim. -/
def compactParity (σ : ℂ) (hσ : σ ^ 2 = 1) (ψ : Domain 0 (T / 2)) : paritySpace T σ :=
  ⟨compactL2 T σ ψ, compactL2_mem_parity T σ hσ ψ⟩

/-- The established half-unitary sends this smooth lift to the original interval test. -/
theorem halfUnitary_compactParity (σ : ℂ) (hσ : σ ^ 2 = 1) (ψ : Domain 0 (T / 2)) :
    halfUnitary T σ hσ (compactParity T σ hσ ψ) = toIntervalL2 ψ := by
  apply Lp.ext
  have ha := compactL2_ae T σ ψ
  rw [← volume_ae_eq_haar T] at ha
  filter_upwards [halfUnitary_ae T σ hσ (compactParity T σ hσ ψ),
    ae_half_of_volume T ha, toIntervalL2_ae ψ,
    ae_restrict_mem (μ := (volume : Measure ℝ)) measurableSet_Ioo] with x hu hx hψ hm
  rw [hu]
  change ((Real.sqrt (T / 2))⁻¹ : ℂ) * (compactL2 T σ ψ) (x : AddCircle T) = _
  rw [hx, compactLift_coe T σ ψ ⟨by linarith [hm.1, (Fact.out : 0 < T)], hm.2.le⟩,
    reflectedTest_half T σ ψ hm.1.le, hψ]
  have hs : (Real.sqrt (T / 2) : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (Real.sqrt_pos.mpr
      (show 0 < T / 2 by linarith [(Fact.out : 0 < T)]))
  simp only [← mul_assoc, inv_mul_cancel₀ hs, one_mul]

/-- Explicit identification with the accepted inverse, on actual interval L² classes. -/
theorem halfUnitary_symm_compact (σ : ℂ) (hσ : σ ^ 2 = 1) (ψ : Domain 0 (T / 2)) :
    (halfUnitary T σ hσ).symm (toIntervalL2 ψ) = compactParity T σ hσ ψ := by
  apply (halfUnitary T σ hσ).injective
  rw [(halfUnitary T σ hσ).apply_symm_apply, halfUnitary_compactParity]

omit [Fact (0 < T)] in
/-- Finite Fourier representatives are smooth in the actual real coordinate. -/
theorem trigLift_smooth (v : ℤ →₀ ℂ) : ContDiff ℝ ∞ (trigLift T v) := by
  unfold trigLift trigPolynomial
  simp only [Finsupp.sum, ContinuousMap.coe_sum, ContinuousMap.coe_smul,
    Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  apply ContDiff.sum
  intro n hn
  simp only [fourier_coe_apply]
  have hor : ContDiff ℝ ∞ (fun x : ℝ ↦ (x : ℂ)) := Complex.ofRealCLM.contDiff
  exact contDiff_const.mul (((contDiff_const.mul hor).div_const _).cexp)

/-- Two genuine integrations by parts; only the compact test and its derivative
vanish at the endpoints. The Fourier test has no imposed zero boundary data. -/
theorem reflectedTest_green (σ : ℂ) (ψ : Domain 0 (T / 2))
    {f : ℝ → ℂ} (hf : ContDiff ℝ ∞ f) :
    (∫ x in -(T / 2)..T / 2,
      conj (deriv (deriv f) x) * reflectedTest T σ ψ x) =
    ∫ x in -(T / 2)..T / 2,
      conj (f x) * reflectedTest T σ (D (D ψ)) x := by
  let g := reflectedTest T σ ψ
  have hg : ContDiff ℝ ∞ g := reflectedTest_smooth T σ ψ
  have hf1 : ContDiff ℝ ∞ (deriv f) := hf.deriv'
  have hf2 : ContDiff ℝ ∞ (deriv (deriv f)) := hf1.deriv'
  have hg1 : ContDiff ℝ ∞ (deriv g) := hg.deriv'
  have hg2 : ContDiff ℝ ∞ (deriv (deriv g)) := hg1.deriv'
  have hd (x : ℝ) : HasDerivAt (fun y ↦ conj (f y)) (conj (deriv f x)) x :=
    ((hf.differentiable (by simp)).differentiableAt.hasDerivAt).star
  have hdd (x : ℝ) : HasDerivAt (fun y ↦ conj (deriv f y))
      (conj (deriv (deriv f) x)) x :=
    ((hf1.differentiable (by simp)).differentiableAt.hasDerivAt).star
  have h0 := reflectedTest_endpoints T σ ψ
  have h1 : deriv g (-(T / 2)) = 0 ∧ deriv g (T / 2) = 0 := by
    simpa only [g, reflectedTest_deriv] using reflectedTest_endpoints T (-σ) (D ψ)
  have hi₁ := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := -(T / 2)) (b := T / 2)
    (u := fun x ↦ conj (deriv f x)) (v := g)
    (u' := fun x ↦ conj (deriv (deriv f) x)) (v' := deriv g)
    (Complex.continuous_conj.comp hf1.continuous).continuousOn hg.continuous.continuousOn
    (fun x _ ↦ hdd x) (fun x _ ↦ (hg.differentiable (by simp)).differentiableAt.hasDerivAt)
    ((Complex.continuous_conj.comp hf2.continuous).intervalIntegrable _ _)
    (hg1.continuous.intervalIntegrable _ _)
  have hi₂ := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := -(T / 2)) (b := T / 2)
    (u := fun x ↦ conj (f x)) (v := deriv g)
    (u' := fun x ↦ conj (deriv f x)) (v' := deriv (deriv g))
    (Complex.continuous_conj.comp hf.continuous).continuousOn
    hg1.continuous.continuousOn (fun x _ ↦ hd x)
    (fun x _ ↦ (hg1.differentiable (by simp)).differentiableAt.hasDerivAt)
    ((Complex.continuous_conj.comp hf1.continuous).intervalIntegrable _ _)
    (hg2.continuous.intervalIntegrable _ _)
  change g (-(T / 2)) = 0 ∧ g (T / 2) = 0 at h0
  simp only [h0.1, h0.2, h1.1, h1.2, mul_zero, sub_zero, zero_sub] at hi₁ hi₂
  rw [hi₁, neg_neg] at hi₂
  simpa only [g, reflectedTest_deriv2] using hi₂.symm

/-- Actual L² inner products are normalized physical cell integrals of representatives. -/
theorem inner_eq_cell (u v : ModeSpace T) (f g : AddCircle T → ℂ)
    (hu : (u : AddCircle T → ℂ) =ᵐ[AddCircle.haarAddCircle] f)
    (hv : (v : AddCircle T → ℂ) =ᵐ[AddCircle.haarAddCircle] g) :
    inner ℂ u v = (T⁻¹ : ℂ) *
      ∫ x in -(T / 2)..T / 2, conj (f (x : AddCircle T)) * g (x : AddCircle T) := by
  rw [L2.inner_def]
  have he : (fun z ↦ inner ℂ (u z) (v z)) =ᵐ[AddCircle.haarAddCircle]
      (fun z ↦ conj (f z) * g z) := by
    filter_upwards [hu, hv] with z hz hw
    simp only [hz, hw, RCLike.inner_apply, mul_comm]
  rw [integral_congr_ae he, AddCircle.integral_haarAddCircle,
    ← AddCircle.intervalIntegral_preimage T (-(T / 2))]
  rw [show -(T / 2) + T = T / 2 by ring]
  simp only [Complex.real_smul, Complex.ofReal_inv]

/-- The actual spectral kinetic satisfies the weak second-derivative identity against
any compact interior test, before restricting to either parity sector. -/
theorem kinetic_compact_weak (a : ℝ) (σ : ℂ) (ψ : Domain 0 (T / 2))
    (u : trigDomain T) :
    inner ℂ (BECPeriodicCommutator.kinetic T (scale T a) u : ModeSpace T)
        (compactL2 T σ ψ) =
      inner ℂ (u : ModeSpace T) (-(a : ℂ) • compactL2 T σ (D (D ψ))) := by
  obtain ⟨v, rfl⟩ := (trigEquiv T).surjective u
  let k : C(AddCircle T, ℂ) :=
    v.sum (fun n b ↦ b • (((scale T a : ℂ) * (n : ℂ)^2) • fourier n))
  rw [inner_smul_right]
  rw [inner_eq_cell T _ _ k (compactLift T σ ψ)
    (kinetic_polynomial_ae T (scale T a) v) (compactL2_ae T σ ψ)]
  rw [coe_trigEquiv]
  rw [inner_eq_cell T _ _ (trigPolynomial T v) (compactLift T σ (D (D ψ)))
    (trigPolynomial_ae T v) (compactL2_ae T σ (D (D ψ)))]
  have hp : -(T / 2) ≤ T / 2 := by linarith [(Fact.out : 0 < T)]
  have hleft :
      (∫ x in -(T / 2)..T / 2,
        conj (k (x : AddCircle T)) * compactLift T σ ψ (x : AddCircle T)) =
      (-(a : ℂ) * (Real.sqrt (T / 2) : ℂ)) *
        ∫ x in -(T / 2)..T / 2,
          conj (deriv (deriv (trigLift T v)) x) * reflectedTest T σ ψ x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hp] at hx
    dsimp only
    rw [compactLift_coe T σ ψ hx, show k (x : AddCircle T) =
      -(a : ℂ) * deriv (deriv (trigLift T v)) x from
        kinetic_polynomial_eq_neg_second_deriv T a v x]
    simp only [map_mul, map_neg, Complex.conj_ofReal]
    ring
  have hright :
      (∫ x in -(T / 2)..T / 2,
        conj (trigPolynomial T v (x : AddCircle T)) *
          compactLift T σ (D (D ψ)) (x : AddCircle T)) =
      (Real.sqrt (T / 2) : ℂ) *
        ∫ x in -(T / 2)..T / 2,
          conj (trigLift T v x) * reflectedTest T σ (D (D ψ)) x := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro x hx
    rw [Set.uIcc_of_le hp] at hx
    dsimp only
    rw [compactLift_coe T σ (D (D ψ)) hx]
    unfold trigLift
    ring
  rw [hleft, hright, reflectedTest_green T σ ψ (trigLift_smooth T v)]
  ring

/-- The weak identity in the actual parity Hilbert space uses the accepted finite
Fourier operator domain, with the compact lift as the adjoint-domain candidate. -/
theorem parity_compact_weak (a : ℝ) (σ : ℂ) (hσ : σ ^ 2 = 1)
    (ψ : Domain 0 (T / 2)) (u : parityCore T σ) :
    inner ℂ (parityPMap T (scale T a) σ u) (compactParity T σ hσ ψ) =
      inner ℂ (u : paritySpace T σ) (-(a : ℂ) • compactParity T σ hσ (D (D ψ))) :=
  kinetic_compact_weak T a σ ψ (coreInclusion T σ u)

/-- Essential self-adjointness identifies the adjoint of the actual finite parity
operator with the already constructed self-adjoint closure. -/
theorem parityPMap_adjoint_eq_closure (c : ℝ) (σ : ℂ) (hσ : σ ^ 2 = 1) :
    (parityPMap T c σ).adjoint = (parityPMap T c σ).closure := by
  have hu : (parityPMap T c σ).IsUnbounded :=
    LinearPMap.isUnbounded_of_dense_of_isSymmetric (parityPMap_dense T c σ hσ)
      (parityPMap_symmetric T c σ)
  exact hu.adjoint_closure_eq_adjoint.symm.trans
    (LinearPMap.isSelfAdjoint_def.mp (parityPMap_closure_selfAdjoint T c σ hσ))

/-- The conjugate-first Hilbert convention supplies the actual adjoint witness. -/
theorem compact_adjoint_witness (a : ℝ) (σ : ℂ) (hσ : σ ^ 2 = 1)
    (ψ : Domain 0 (T / 2)) (u : (parityPMap T (scale T a) σ).domain) :
    inner ℂ (-(a : ℂ) • compactParity T σ hσ (D (D ψ))) (u : paritySpace T σ) =
      inner ℂ (compactParity T σ hσ ψ) (parityPMap T (scale T a) σ u) := by
  simpa only [inner_conj_symm] using
    congrArg (starRingEnd ℂ) (parity_compact_weak T a σ hσ ψ u).symm

/-- Every actual compact interior test belongs to the true parity closure domain. -/
theorem compactParity_mem_closure (a : ℝ) (σ : ℂ) (hσ : σ ^ 2 = 1)
    (ψ : Domain 0 (T / 2)) :
    compactParity T σ hσ ψ ∈ (parityPMap T (scale T a) σ).closure.domain := by
  rw [← parityPMap_adjoint_eq_closure T (scale T a) σ hσ]
  exact LinearPMap.mem_adjoint_domain_of_exists _
    ⟨-(a : ℂ) • compactParity T σ hσ (D (D ψ)), compact_adjoint_witness T a σ hσ ψ⟩

/-- Compact tests as elements of the actual closure domain; no assertion that they are a core. -/
def compactParityDomain (a : ℝ) (σ : ℂ) (hσ : σ ^ 2 = 1) (ψ : Domain 0 (T / 2)) :
    (parityPMap T (scale T a) σ).closure.domain :=
  ⟨compactParity T σ hσ ψ, compactParity_mem_closure T a σ hσ ψ⟩

/-- Adjoint uniqueness computes the actual self-adjoint closure action on compact tests. -/
theorem parityClosure_compact_apply (a : ℝ) (σ : ℂ) (hσ : σ ^ 2 = 1)
    (ψ : Domain 0 (T / 2)) :
    (parityPMap T (scale T a) σ).closure (compactParityDomain T a σ hσ ψ) =
      -(a : ℂ) • compactParity T σ hσ (D (D ψ)) := by
  have he := parityPMap_adjoint_eq_closure T (scale T a) σ hσ
  have hw := LinearPMap.adjoint_apply_eq (parityPMap_dense T (scale T a) σ hσ)
    (⟨compactParity T σ hσ ψ,
      he.symm ▸ compactParity_mem_closure T a σ hσ ψ⟩ :
        (parityPMap T (scale T a) σ).adjoint.domain)
    (compact_adjoint_witness T a σ hσ ψ)
  exact (he.le.2 (x := ⟨compactParity T σ hσ ψ,
    he.symm ▸ compactParity_mem_closure T a σ hσ ψ⟩)
    (y := compactParityDomain T a σ hσ ψ) rfl).symm.trans hw

/-- Actual physical interval compact tests enter both transported self-adjoint wall domains. -/
theorem compact_mem_halfKinetic (a : ℝ) (σ : ℂ) (hσ : σ ^ 2 = 1)
    (ψ : Domain 0 (T / 2)) :
    toIntervalL2 ψ ∈ (halfKinetic T (scale T a) σ hσ).domain := by
  rw [← halfUnitary_compactParity T σ hσ ψ]
  exact LinearPMap.map_mem_unitaryConj_domain (halfUnitary T σ hσ) _
    (compactParityDomain T a σ hσ ψ)

/-- The original interval test with its proved membership in the actual wall domain. -/
def compactWallDomain (a : ℝ) (σ : ℂ) (hσ : σ ^ 2 = 1) (ψ : Domain 0 (T / 2)) :
    (halfKinetic T (scale T a) σ hσ).domain :=
  ⟨toIntervalL2 ψ, compact_mem_halfKinetic T a σ hσ ψ⟩

/-- The self-adjoint wall kinetic acts as minus a times the genuine second derivative
on the original compact test, in actual interval Lebesgue L². -/
theorem halfKinetic_compact_apply (a : ℝ) (σ : ℂ) (hσ : σ ^ 2 = 1)
    (ψ : Domain 0 (T / 2)) :
    halfKinetic T (scale T a) σ hσ (compactWallDomain T a σ hσ ψ) =
      toIntervalL2 (-(a : ℂ) • D (D ψ)) := by
  have he : compactWallDomain T a σ hσ ψ =
      halfKineticDomain T (scale T a) σ hσ (compactParityDomain T a σ hσ ψ) := by
    apply Subtype.ext
    exact (halfUnitary_compactParity T σ hσ ψ).symm
  rw [he, halfKinetic_apply, parityClosure_compact_apply, map_smul,
    halfUnitary_compactParity, map_smul]

/-- The same action stated on actual representatives almost everywhere. -/
theorem halfKinetic_compact_ae (a : ℝ) (σ : ℂ) (hσ : σ ^ 2 = 1)
    (ψ : Domain 0 (T / 2)) :
    ∀ᵐ x : ℝ ∂volume.restrict (Set.Ioo 0 (T / 2)),
      (halfKinetic T (scale T a) σ hσ (compactWallDomain T a σ hσ ψ) : ℝ → ℂ) x =
        -(a : ℂ) * deriv (deriv ψ) x := by
  rw [halfKinetic_compact_apply]
  exact toIntervalL2_ae (-(a : ℂ) • D (D ψ))

/-- Both genuine wall realizations contain each original compact interior test. -/
theorem compact_mem_both_wall_domains (a : ℝ) (ψ : Domain 0 (T / 2)) :
    toIntervalL2 ψ ∈ (halfKinetic T (scale T a) 1 (by norm_num)).domain ∧
      toIntervalL2 ψ ∈ (halfKinetic T (scale T a) (-1) (by norm_num)).domain :=
  ⟨compact_mem_halfKinetic T a 1 (by norm_num) ψ,
    compact_mem_halfKinetic T a (-1) (by norm_num) ψ⟩

end CompactInterior

end SKEFTHawking.DKMBootstrap.BECWallParity
