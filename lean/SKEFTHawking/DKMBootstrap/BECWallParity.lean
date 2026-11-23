import SKEFTHawking.DKMBootstrap.BECPeriodicCommutator

/-!
# Spatial reflection and periodic parity kinetic cores

Reflection is complex-linear pullback by negation on the circle with normalized Haar
measure. The finite Fourier domain and kinetic action below are the actual domain and
action of `BECPeriodicCommutator`. Both closed parity Hilbert spaces have dense projected
Fourier cores on which the kinetic is essentially self-adjoint. Parity refers to this
periodic Hilbert space.
Identifying it with physical interval Lebesgue L², proving compact-interior domain
membership, and constructing wall or interacting Fock Hamiltonians require further work.
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

end SKEFTHawking.DKMBootstrap.BECWallParity
