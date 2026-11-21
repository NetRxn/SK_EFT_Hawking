import SKEFTHawking.ADW.QuaternionSU2Sphere
import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
/-!
# Normalized quaternion sphere measure

The Euclidean unit sphere carries Mathlib's surface measure from radial cones.
Normalizing this measure and transporting it through the original quaternion
coordinates gives the normalized SU(2) Haar measure used by the Dirac integral.
-/

set_option autoImplicit false

open MeasureTheory Set Metric
open scoped Pointwise ENNReal
namespace SKEFTHawking.ADW.QuaternionSU2Sphere
open FiniteGrassmannCoframe FiniteGrassmannDiracBerezin
noncomputable section
private theorem measurable_leftOnSphere (A : SU2) : Measurable (leftOnSphere A) :=
  ((leftIsometry A).continuous.comp continuous_subtype_val).subtype_mk
    (fun x : UnitSphere ↦ (leftOnSphere A x).property) |>.measurable

private theorem preimage_sphereCone (A : SU2) (s : Set UnitSphere) :
    leftIsometry A ⁻¹' (Ioo (0 : ℝ) 1 • (Subtype.val '' s)) =
      Ioo (0 : ℝ) 1 • (Subtype.val '' (leftOnSphere A ⁻¹' s)) := by
  ext x
  constructor
  · rintro ⟨r, hr, y, ⟨u, hu, rfl⟩, h⟩
    let v := leftOnSphere A⁻¹ u
    have hv : leftOnSphere A v = u := by
      rw [show leftOnSphere A v = leftOnSphere A (leftOnSphere A⁻¹ u) from rfl,
        ← leftOnSphere_mul, mul_inv_cancel, leftOnSphere_one]
    refine ⟨r, hr, v.val, ⟨v, ?_, rfl⟩, ?_⟩
    · show leftOnSphere A v ∈ s
      rwa [hv]
    · apply (leftIsometry A).injective
      rw [LinearIsometryEquiv.map_smul]
      change r • (leftOnSphere A v).val = leftIsometry A x
      rwa [hv]
  · rintro ⟨r, hr, y, ⟨v, hv, rfl⟩, h⟩
    refine ⟨r, hr, (leftOnSphere A v).val, ⟨leftOnSphere A v, hv, rfl⟩, ?_⟩
    change r • leftIsometry A v.val = leftIsometry A x
    rw [← LinearIsometryEquiv.map_smul]
    exact congrArg (leftIsometry A) h

/-- The orthogonal left action preserves the Euclidean cone measure on the sphere. -/
theorem map_leftOnSphere_toSphere (A : SU2) :
    Measure.map (leftOnSphere A) (volume : Measure Coordinates).toSphere =
      (volume : Measure Coordinates).toSphere := by
  have hvol := (leftIsometry A).measurePreserving
  have hme : MeasurableEmbedding (leftIsometry A) :=
    (leftIsometry A).toHomeomorph.measurableEmbedding
  ext s hs
  rw [Measure.map_apply (measurable_leftOnSphere A) hs,
    Measure.toSphere_apply' _ (measurable_leftOnSphere A hs), Measure.toSphere_apply' _ hs,
    ← preimage_sphereCone A s, ← hme.map_apply, hvol.map_eq]

/-- Euclidean sphere surface measure divided by its total mass. -/
def normalizedSphere : Measure UnitSphere :=
  ((volume : Measure Coordinates).toSphere univ)⁻¹ •
    (volume : Measure Coordinates).toSphere

instance normalizedSphere_probability : IsProbabilityMeasure normalizedSphere := by
  let μ := (volume : Measure Coordinates).toSphere
  have h0 : μ univ ≠ 0 := fun h ↦
    (Measure.toSphere_ne_zero volume) (Measure.measure_univ_eq_zero.mp h)
  have ht : μ univ ≠ ∞ := (IsFiniteMeasure.measure_univ_lt_top (μ := μ)).ne
  constructor
  exact ENNReal.inv_mul_cancel h0 ht

/-- Normalizing the sphere's total mass preserves orthogonal left invariance. -/
theorem map_leftOnSphere_normalizedSphere (A : SU2) :
    Measure.map (leftOnSphere A) normalizedSphere = normalizedSphere := by
  rw [normalizedSphere, Measure.map_smul, map_leftOnSphere_toSphere]

/-- Quaternion coordinates identify normalized Euclidean sphere measure with
the original normalized SU(2) Haar measure. -/
theorem measurePreserving_sphereHomeomorphSU2 :
    MeasurePreserving sphereHomeomorphSU2 normalizedSphere su2Haar := by
  let μ := Measure.map sphereHomeomorphSU2 normalizedSphere
  have hQ : Measurable sphereHomeomorphSU2 := sphereHomeomorphSU2.measurable
  letI : IsProbabilityMeasure μ := by
    constructor
    change (Measure.map sphereHomeomorphSU2 normalizedSphere) univ = 1
    rw [Measure.map_apply hQ MeasurableSet.univ, preimage_univ, measure_univ]
  letI : μ.IsMulLeftInvariant := ⟨fun A ↦ by
    change Measure.map (fun U ↦ A * U) (Measure.map sphereHomeomorphSU2 normalizedSphere) =
      Measure.map sphereHomeomorphSU2 normalizedSphere
    have hcomp : (fun U : SU2 ↦ A * U) ∘ sphereHomeomorphSU2 =
        sphereHomeomorphSU2 ∘ leftOnSphere A := by
      funext x
      exact (sphereHomeomorphSU2_left A x).symm
    rw [Measure.map_map (measurable_const_mul A) hQ, hcomp,
      ← Measure.map_map hQ (measurable_leftOnSphere A), map_leftOnSphere_normalizedSphere]⟩
  letI : su2Haar.IsHaarMeasure := by
    unfold su2Haar
    infer_instance
  have hscale := Measure.isMulInvariant_eq_smul_of_compactSpace μ su2Haar
  have hmass := congrArg (fun ν : Measure SU2 ↦ ν univ) hscale
  simp only [measure_univ, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul, mul_one] at hmass
  have hscalar : μ.haarScalarFactor su2Haar = 1 := by
    exact_mod_cast hmass.symm
  refine ⟨hQ, ?_⟩
  change μ = su2Haar
  rw [hscale, hscalar, one_smul]

end

end SKEFTHawking.ADW.QuaternionSU2Sphere
