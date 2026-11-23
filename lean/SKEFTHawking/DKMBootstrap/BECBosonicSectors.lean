import SKEFTHawking.DKMBootstrap.BECInteriorCommutator
import Mathlib.MeasureTheory.Constructions.Pi

/-!
# Bosonic configuration carriers on an interval

The measure is the finite product of the restricted Lebesgue measure used by
`BECInteriorCommutator.IntervalHilbert`. It is not probability normalized.
Coordinate permutations induce actual complex linear isometric equivalences on L²;
their common fixed space is a closed Hilbert subspace. At particle number one,
evaluation and constant extension identify this sector with the existing interval L².

This checkpoint constructs carriers only. It assumes no Hamiltonian, pair interaction,
Fock graph, thermal state, or physical transport conclusion. The moving wall-operator
module is deliberately not a dependency.
-/

noncomputable section

open MeasureTheory Set

namespace SKEFTHawking.DKMBootstrap.BECBosonicSectors

/-- The existing one-particle measure, without a mass rescaling. -/
def intervalMeasure (l r : ℝ) : Measure ℝ := volume.restrict (Ioo l r)

/-- Ambient configurations; the measure restricts every coordinate to the interval. -/
abbrev Configuration (N : ℕ) := Fin N → ℝ

/-- Actual product of the one-particle restricted Lebesgue measures. -/
def configurationMeasure (l r : ℝ) (N : ℕ) : Measure (Configuration N) :=
  Measure.pi (fun _ : Fin N ↦ intervalMeasure l r)

instance (l r : ℝ) : IsFiniteMeasure (intervalMeasure l r) := by
  unfold intervalMeasure
  infer_instance

/-- Product restriction agrees with restriction of ambient product Lebesgue measure. -/
theorem configurationMeasure_eq_restrict (l r : ℝ) (N : ℕ) :
    configurationMeasure l r N =
      (Measure.pi (fun _ : Fin N ↦ (volume : Measure ℝ))).restrict
        (Set.univ.pi (fun _ ↦ Ioo l r)) :=
  (Measure.restrict_pi_pi (fun _ : Fin N ↦ (volume : Measure ℝ))
    (fun _ ↦ Ioo l r)).symm

/-- The total mass retains the physical interval length in every coordinate. -/
theorem configurationMeasure_univ (l r : ℝ) (N : ℕ) :
    configurationMeasure l r N Set.univ = ENNReal.ofReal (r - l) ^ N := by
  simp [configurationMeasure, Measure.pi_univ, intervalMeasure, Real.volume_Ioo]

/-- Full configuration L², before imposing bosonic symmetry. -/
abbrev ConfigurationHilbert (l r : ℝ) (N : ℕ) := Lp ℂ 2 (configurationMeasure l r N)

section Pullback

variable {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
  {μ : Measure α} {ν : Measure β}

/-- Pullback and inverse pullback really cancel on L² classes. -/
private theorem pullback_inverse (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν)
    (ψ : Lp ℂ 2 μ) :
    Lp.compMeasurePreserving e he
      (Lp.compMeasurePreserving e.symm (he.symm e) ψ) = ψ := by
  rw [← Lp.compMeasurePreserving_comp_apply]
  have h : (e.symm ∘ e : α → α) = id := funext e.symm_apply_apply
  simpa only [h] using Lp.compMeasurePreserving_id_apply ψ

/-- A measure-preserving measurable equivalence gives an onto complex L² unitary. -/
def pullbackUnitary (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν) :
    Lp ℂ 2 ν ≃ₗᵢ[ℂ] Lp ℂ 2 μ :=
  LinearIsometryEquiv.ofSurjective (Lp.compMeasurePreservingₗᵢ ℂ e he)
    (fun ψ ↦ ⟨Lp.compMeasurePreserving e.symm (he.symm e) ψ,
      pullback_inverse e he ψ⟩)

theorem pullbackUnitary_ae (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν)
    (ψ : Lp ℂ 2 ν) :
    (pullbackUnitary e he ψ : α → ℂ) =ᵐ[μ] fun x ↦ ψ (e x) :=
  Lp.coeFn_compMeasurePreserving ψ he

theorem pullbackUnitary_symm_apply (e : α ≃ᵐ β) (he : MeasurePreserving e μ ν)
    (ψ : Lp ℂ 2 μ) :
    (pullbackUnitary e he).symm ψ = pullbackUnitary e.symm (he.symm e) ψ := by
  apply (pullbackUnitary e he).injective
  exact ((pullbackUnitary e he).apply_symm_apply ψ).trans
    (pullback_inverse e he ψ).symm

end Pullback

/-- Geometric left action: `(reindex σ x) i = x (σ⁻¹ i)`. -/
def reindex {N : ℕ} (σ : Equiv.Perm (Fin N)) : Configuration N ≃ᵐ Configuration N :=
  MeasurableEquiv.piCongrLeft (fun _ : Fin N ↦ ℝ) σ

theorem reindex_apply {N : ℕ} (σ : Equiv.Perm (Fin N)) (x : Configuration N)
    (i : Fin N) : reindex σ x i = x (σ.symm i) := by
  simp [reindex, MeasurableEquiv.piCongrLeft, Equiv.piCongrLeft_apply]

theorem reindex_mul {N : ℕ} (σ τ : Equiv.Perm (Fin N)) (x : Configuration N) :
    reindex (σ * τ) x = reindex σ (reindex τ x) := by
  ext i
  simp only [reindex_apply]
  rfl

theorem reindex_measurePreserving (l r : ℝ) {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    MeasurePreserving (reindex σ) (configurationMeasure l r N)
      (configurationMeasure l r N) :=
  measurePreserving_piCongrLeft (fun _ : Fin N ↦ intervalMeasure l r) σ

/-- Inverse geometric pullback, giving the usual left action on wave functions. -/
def permutationUnitary (l r : ℝ) {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    ConfigurationHilbert l r N ≃ₗᵢ[ℂ] ConfigurationHilbert l r N :=
  pullbackUnitary (reindex σ).symm ((reindex_measurePreserving l r σ).symm _)

/-- The unitary acts by actual coordinate precomposition, modulo the product measure. -/
theorem permutationUnitary_ae (l r : ℝ) {N : ℕ} (σ : Equiv.Perm (Fin N))
    (ψ : ConfigurationHilbert l r N) :
    (permutationUnitary l r σ ψ : Configuration N → ℂ) =ᵐ[configurationMeasure l r N]
      fun x ↦ ψ (fun i ↦ x (σ i)) :=
  pullbackUnitary_ae _ _ ψ

theorem permutationUnitary_one (l r : ℝ) {N : ℕ}
    (ψ : ConfigurationHilbert l r N) : permutationUnitary l r 1 ψ = ψ := by
  change Lp.compMeasurePreserving _ _ ψ = ψ
  have h : ((reindex (1 : Equiv.Perm (Fin N))).symm : Configuration N →
      Configuration N) = id := rfl
  simpa only [h] using Lp.compMeasurePreserving_id_apply ψ

theorem permutationUnitary_mul (l r : ℝ) {N : ℕ} (σ τ : Equiv.Perm (Fin N))
    (ψ : ConfigurationHilbert l r N) :
    permutationUnitary l r (σ * τ) ψ =
      permutationUnitary l r σ (permutationUnitary l r τ ψ) := by
  change Lp.compMeasurePreserving _ _ ψ =
    Lp.compMeasurePreserving _ _ (Lp.compMeasurePreserving _ _ ψ)
  rw [← Lp.compMeasurePreserving_comp_apply]
  rfl

/-- Each fixed space is the closed kernel of the continuous operator `Uσ - I`. -/
def permutationFixedSpace (l r : ℝ) {N : ℕ} (σ : Equiv.Perm (Fin N)) :
    ClosedSubmodule ℂ (ConfigurationHilbert l r N) :=
  let A := (permutationUnitary l r σ).toLinearIsometry.toContinuousLinearMap -
    ContinuousLinearMap.id ℂ (ConfigurationHilbert l r N)
  ⟨A.ker, A.isClosed_ker⟩

/-- The bosonic sector is the intersection of all permutation fixed spaces. -/
def bosonicSubspace (l r : ℝ) (N : ℕ) : ClosedSubmodule ℂ (ConfigurationHilbert l r N) :=
  ⨅ σ : Equiv.Perm (Fin N), permutationFixedSpace l r σ

theorem mem_bosonicSubspace_iff (l r : ℝ) {N : ℕ}
    (ψ : ConfigurationHilbert l r N) :
    ψ ∈ bosonicSubspace l r N ↔ ∀ σ, permutationUnitary l r σ ψ = ψ := by
  simp [bosonicSubspace, ClosedSubmodule.mem_iInf, permutationFixedSpace, sub_eq_zero]

/-- Fixed L² classes are exactly wave functions symmetric almost everywhere. -/
theorem mem_bosonicSubspace_iff_ae (l r : ℝ) {N : ℕ}
    (ψ : ConfigurationHilbert l r N) :
    ψ ∈ bosonicSubspace l r N ↔ ∀ σ : Equiv.Perm (Fin N),
      (fun x ↦ ψ (fun i ↦ x (σ i))) =ᵐ[configurationMeasure l r N]
        (ψ : Configuration N → ℂ) := by
  rw [mem_bosonicSubspace_iff]
  constructor
  · intro h σ
    exact (permutationUnitary_ae l r σ ψ).symm.trans
      (Filter.EventuallyEq.of_eq (congrArg
        (fun u : ConfigurationHilbert l r N ↦ (u : Configuration N → ℂ)) (h σ)))
  · intro h σ
    exact Lp.ext ((permutationUnitary_ae l r σ ψ).trans (h σ))

/-- Closedness is in the actual L² norm topology. -/
theorem bosonicSubspace_isClosed (l r : ℝ) (N : ℕ) :
    IsClosed (bosonicSubspace l r N : Set (ConfigurationHilbert l r N)) :=
  (bosonicSubspace l r N).isClosed

/-- The inherited inner product is the product-measure L² inner product. -/
abbrev BosonicHilbert (l r : ℝ) (N : ℕ) := (bosonicSubspace l r N).toSubmodule

instance (l r : ℝ) (N : ℕ) : CompleteSpace (BosonicHilbert l r N) :=
  (bosonicSubspace_isClosed l r N).completeSpace_coe

instance (l r : ℝ) (N : ℕ) : InnerProductSpace ℂ (BosonicHilbert l r N) :=
  inferInstanceAs (InnerProductSpace ℂ (bosonicSubspace l r N).toSubmodule)

/-- At N=1 evaluation is a measurable equivalence, with constant extension as inverse. -/
def oneParticleEvaluation : Configuration 1 ≃ᵐ ℝ :=
  MeasurableEquiv.piUnique (fun _ : Fin 1 ↦ ℝ)

theorem oneParticleEvaluation_apply (x : Configuration 1) :
    oneParticleEvaluation x = x 0 := rfl

theorem oneParticleEvaluation_symm_apply (x : ℝ) :
    oneParticleEvaluation.symm x = fun _ ↦ x := by
  ext i
  rfl

/-- Evaluation preserves the restricted Lebesgue measure exactly, including its mass. -/
theorem oneParticleEvaluation_measurePreserving (l r : ℝ) :
    MeasurePreserving oneParticleEvaluation (configurationMeasure l r 1)
      (intervalMeasure l r) :=
  measurePreserving_piUnique (fun _ : Fin 1 ↦ intervalMeasure l r)

/-- Constant extension is the reverse measure-preserving map, with no normalization. -/
theorem oneParticleExtension_measurePreserving (l r : ℝ) :
    MeasurePreserving (fun x : ℝ ↦ (fun _ : Fin 1 ↦ x)) (intervalMeasure l r)
      (configurationMeasure l r 1) :=
  (oneParticleEvaluation_measurePreserving l r).symm oneParticleEvaluation

/-- Actual onto unitary from the existing interval carrier to full one-particle L². -/
def intervalConfigurationUnitary (l r : ℝ) :
    BECInteriorCommutator.IntervalHilbert l r ≃ₗᵢ[ℂ] ConfigurationHilbert l r 1 :=
  pullbackUnitary oneParticleEvaluation (oneParticleEvaluation_measurePreserving l r)

theorem intervalConfigurationUnitary_ae (l r : ℝ)
    (ψ : BECInteriorCommutator.IntervalHilbert l r) :
    (intervalConfigurationUnitary l r ψ : Configuration 1 → ℂ)
      =ᵐ[configurationMeasure l r 1] fun x ↦ ψ (x 0) :=
  pullbackUnitary_ae _ _ ψ

theorem intervalConfigurationUnitary_symm_ae (l r : ℝ)
    (ψ : ConfigurationHilbert l r 1) :
    ((intervalConfigurationUnitary l r).symm ψ : ℝ → ℂ)
      =ᵐ[intervalMeasure l r] fun x ↦ ψ (fun _ ↦ x) := by
  rw [intervalConfigurationUnitary, pullbackUnitary_symm_apply]
  exact pullbackUnitary_ae _ _ ψ

/-- There is no symmetry constraint at N=1: every permutation is the identity. -/
theorem bosonicSubspace_one_eq_top (l r : ℝ) :
    (bosonicSubspace l r 1).toSubmodule = ⊤ := by
  apply top_unique
  intro ψ _
  apply (mem_bosonicSubspace_iff l r ψ).mpr
  intro σ
  have hσ : σ = 1 := Subsingleton.elim _ _
  rw [hσ, permutationUnitary_one]

/-- Inclusion of the one-particle bosonic sector is itself an onto unitary. -/
def bosonicOneInclusion (l r : ℝ) :
    BosonicHilbert l r 1 ≃ₗᵢ[ℂ] ConfigurationHilbert l r 1 :=
  LinearIsometryEquiv.ofTop _ _ (bosonicSubspace_one_eq_top l r)

/-- The requested N=1 identification with the existing physical interval Hilbert space. -/
def intervalBosonicUnitary (l r : ℝ) :
    BECInteriorCommutator.IntervalHilbert l r ≃ₗᵢ[ℂ] BosonicHilbert l r 1 :=
  (intervalConfigurationUnitary l r).trans (bosonicOneInclusion l r).symm

theorem intervalBosonicUnitary_coe (l r : ℝ)
    (ψ : BECInteriorCommutator.IntervalHilbert l r) :
    (intervalBosonicUnitary l r ψ : ConfigurationHilbert l r 1) =
      intervalConfigurationUnitary l r ψ := by
  exact (bosonicOneInclusion l r).apply_symm_apply _

/-- Forward representatives are evaluation pullbacks on the actual product measure. -/
theorem intervalBosonicUnitary_ae (l r : ℝ)
    (ψ : BECInteriorCommutator.IntervalHilbert l r) :
    ((intervalBosonicUnitary l r ψ : ConfigurationHilbert l r 1) : Configuration 1 → ℂ)
      =ᵐ[configurationMeasure l r 1] fun x ↦ ψ (x 0) := by
  rw [intervalBosonicUnitary_coe]
  exact intervalConfigurationUnitary_ae l r ψ

/-- The inverse representatives are constant-extension pullbacks on interval volume. -/
theorem intervalBosonicUnitary_symm_ae (l r : ℝ) (ψ : BosonicHilbert l r 1) :
    ((intervalBosonicUnitary l r).symm ψ : ℝ → ℂ) =ᵐ[intervalMeasure l r]
      fun x ↦ (ψ : ConfigurationHilbert l r 1) (fun _ ↦ x) :=
  intervalConfigurationUnitary_symm_ae l r ψ

theorem intervalBosonicUnitary_left_inverse (l r : ℝ)
    (ψ : BECInteriorCommutator.IntervalHilbert l r) :
    (intervalBosonicUnitary l r).symm (intervalBosonicUnitary l r ψ) = ψ :=
  (intervalBosonicUnitary l r).symm_apply_apply ψ

theorem intervalBosonicUnitary_right_inverse (l r : ℝ) (ψ : BosonicHilbert l r 1) :
    intervalBosonicUnitary l r ((intervalBosonicUnitary l r).symm ψ) = ψ :=
  (intervalBosonicUnitary l r).apply_symm_apply ψ

/-- Every bosonic one-particle vector is reached, with no extra hypothesis. -/
theorem intervalBosonicUnitary_surjective (l r : ℝ) :
    Function.Surjective (intervalBosonicUnitary l r) :=
  (intervalBosonicUnitary l r).surjective

theorem intervalBosonicUnitary_norm (l r : ℝ)
    (ψ : BECInteriorCommutator.IntervalHilbert l r) :
    ‖intervalBosonicUnitary l r ψ‖ = ‖ψ‖ :=
  (intervalBosonicUnitary l r).norm_map ψ

theorem intervalBosonicUnitary_unit_norm_iff (l r : ℝ)
    (ψ : BECInteriorCommutator.IntervalHilbert l r) :
    ‖intervalBosonicUnitary l r ψ‖ = 1 ↔ ‖ψ‖ = 1 := by
  rw [intervalBosonicUnitary_norm]

theorem intervalBosonicUnitary_inner (l r : ℝ)
    (ψ φ : BECInteriorCommutator.IntervalHilbert l r) :
    inner ℂ (intervalBosonicUnitary l r ψ) (intervalBosonicUnitary l r φ) =
      inner ℂ ψ φ :=
  (intervalBosonicUnitary l r).inner_map_map ψ φ

end SKEFTHawking.DKMBootstrap.BECBosonicSectors
