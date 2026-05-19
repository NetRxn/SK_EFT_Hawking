/-
Phase 6p Wave 2c.4a-R4.2.d.R5.4 Layer Cartan-C: matrix exponential
is a local diffeomorphism at 0.

## What this module ships

Application of Mathlib's normed-space Inverse Function Theorem
(`HasStrictFDerivAt.toOpenPartialHomeomorph`) to the matrix exponential
on `Matrix (Fin 2) (Fin 2) ℂ` at 0.

**Tier 1 substrate (this commit, ~100 LoC)**:

  - `expAmbient_hasStrictFDerivAt_zero` : the matrix exp on `Matrix (Fin 2)
    (Fin 2) ℂ` has strict Fréchet derivative `id` at 0.
    (Direct alias of Mathlib's `hasStrictFDerivAt_exp_zero` for the
    `𝔸 = Matrix (Fin 2) (Fin 2) ℂ` instance.)

  - `expAmbient_map_nhds_zero` : `map exp (𝓝 0) = 𝓝 1` — IMAGE of a
    neighborhood of 0 in `Matrix _ _ ℂ` under matrix exp is a
    neighborhood of 1 in `Matrix _ _ ℂ`.
    Via `HasStrictFDerivAt.map_nhds_eq_of_equiv` (Mathlib).

  - `expAmbient_image_contains_nhds_one` : the image of any neighborhood
    of 0 contains a neighborhood of 1 in `Matrix _ _ ℂ`. Consumer-friendly
    form of the previous theorem.

**Mathlib4 substrate leveraged**:
  - `hasStrictFDerivAt_exp_zero` (from `Mathlib.Analysis.SpecialFunctions.Exponential`)
  - `HasStrictFDerivAt.map_nhds_eq_of_equiv` (from
    `Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv`)
  - `ContinuousLinearEquiv.refl` (identity continuous linear equiv)

**Architectural significance**: this is the IFT-derived foundation for
the AccPt → interior closure bridge. Combined with shipped
`exp_mem_unitaryGroup` (Cartan-B) and shipped D.3.i.1 iteration sequence,
the resulting "exp maps small nbhd of 0 in 𝔰𝔲(2) to a nbhd of 1
intersected with unitaryGroup" gives the substrate for closing
`1 ∈ interior(closure H_Fib)` in Cartan-D.

**Pipeline Invariant compliance**:
  - #10 (no `maxHeartbeats`): RESPECTED.
  - #15 (no new project-local axioms): RESPECTED.
  - ADR-003 (zero sorry): RESPECTED.
-/

import Mathlib
import SKEFTHawking.FKLW.SU2MatrixExp

set_option autoImplicit false

namespace SKEFTHawking.FKLW.SU2LocalDiffeo

open Matrix Complex NormedSpace Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## §1. exp has identity Fréchet derivative at 0

Direct alias of Mathlib's `hasStrictFDerivAt_exp_zero` for the
`Matrix (Fin 2) (Fin 2) ℂ` instance. The derivative is `(1 : Matrix _ →L[ℝ] Matrix _)`,
which coincides with `ContinuousLinearEquiv.refl ℝ _` (the identity equivalence). -/

/-- **`NormedSpace.exp` on `Matrix (Fin 2) (Fin 2) ℂ` has strict Fréchet
derivative `id` at 0**.

Direct specialization of Mathlib's `hasStrictFDerivAt_exp_zero`
(in `Mathlib.Analysis.SpecialFunctions.Exponential`) to the
`Matrix (Fin 2) (Fin 2) ℂ` normed algebra. -/
theorem expAmbient_hasStrictFDerivAt_zero :
    HasStrictFDerivAt (NormedSpace.exp : Matrix (Fin 2) (Fin 2) ℂ →
                                          Matrix (Fin 2) (Fin 2) ℂ)
      (1 : Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ) 0 :=
  hasStrictFDerivAt_exp_zero

/-- **`NormedSpace.exp` on `Matrix (Fin 2) (Fin 2) ℂ` has strict Fréchet
derivative `ContinuousLinearEquiv.refl` at 0** — equivalent form using the
identity equivalence (which the IFT API requires). -/
theorem expAmbient_hasStrictFDerivAt_zero_equiv :
    HasStrictFDerivAt
      (NormedSpace.exp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
      ((ContinuousLinearEquiv.refl ℝ (Matrix (Fin 2) (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ →L[ℝ] Matrix (Fin 2) (Fin 2) ℂ) 0 :=
  expAmbient_hasStrictFDerivAt_zero

/-! ## §2. exp maps nbhd(0) to nbhd(1) — the IFT consequence

The standard normed-space IFT consequence: since exp has invertible
derivative at 0 (the identity is invertible), exp is a local
homeomorphism at 0. In particular, `map exp (𝓝 0) = 𝓝 (exp 0) = 𝓝 1`.
-/

/-- **exp maps nbhd(0) to nbhd(1)** in `Matrix (Fin 2) (Fin 2) ℂ`.

Application of `HasStrictFDerivAt.map_nhds_eq_of_equiv` (Mathlib IFT
consequence). The derivative at 0 is `1 = (ContinuousLinearEquiv.refl _).toCLM`,
which is an equivalence. -/
theorem expAmbient_map_nhds_zero :
    Filter.map (NormedSpace.exp : Matrix (Fin 2) (Fin 2) ℂ →
                                    Matrix (Fin 2) (Fin 2) ℂ)
      (nhds (0 : Matrix (Fin 2) (Fin 2) ℂ)) =
        nhds (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  have h_map : Filter.map
      (NormedSpace.exp : Matrix (Fin 2) (Fin 2) ℂ → Matrix (Fin 2) (Fin 2) ℂ)
      (nhds (0 : Matrix (Fin 2) (Fin 2) ℂ)) =
      nhds (NormedSpace.exp (0 : Matrix (Fin 2) (Fin 2) ℂ)) :=
    expAmbient_hasStrictFDerivAt_zero_equiv.map_nhds_eq_of_equiv
  rw [h_map, NormedSpace.exp_zero]

/-! ## §3. Consumer-friendly: image of any nbhd(0) contains nbhd(1)

For downstream consumers, often the more useful form is: "the image
of any neighborhood of 0 under exp contains a neighborhood of 1." This
follows from `map_nhds_eq_of_equiv` by definition of `Filter.map`.
-/

/-- **Image of nbhd(0) under exp contains a nbhd(1)**.

Derives from `expAmbient_map_nhds_zero` via the standard `Filter.map`
characterization: `V ∈ map f F ↔ f ⁻¹' V ∈ F`, so `exp ⁻¹' V ⊆ U` for
some `U ∈ 𝓝 0` for every `V ∈ 𝓝 1`. The image form requires only that
`exp '' U ⊇ V ∩ exp '' U` (trivially), giving the containment.

Concretely: by `expAmbient_map_nhds_zero`, `exp '' U ∈ 𝓝 1` for every
`U ∈ 𝓝 0`, via the fact that `exp '' (exp ⁻¹' V) = V` (when surjective
onto the image, which the IFT-derived local-homeo gives us). -/
theorem expAmbient_image_nhds_zero_subset_nhds_one
    {U : Set (Matrix (Fin 2) (Fin 2) ℂ)} (hU : U ∈ nhds (0 : Matrix _ _ ℂ)) :
    ∃ V ∈ nhds (1 : Matrix (Fin 2) (Fin 2) ℂ),
        V ⊆ (NormedSpace.exp : Matrix _ _ ℂ → Matrix _ _ ℂ) '' U := by
  -- IFT gives an open partial homeomorphism φ with φ = exp on source
  -- containing 0. Take V := φ '' (U ∩ φ.source).
  let φ := expAmbient_hasStrictFDerivAt_zero_equiv.toOpenPartialHomeomorph
    (NormedSpace.exp : Matrix _ _ ℂ → Matrix _ _ ℂ)
  have h_zero_source : (0 : Matrix _ _ ℂ) ∈ φ.source :=
    expAmbient_hasStrictFDerivAt_zero_equiv.mem_toOpenPartialHomeomorph_source
  have hU' : U ∩ φ.source ∈ nhds (0 : Matrix _ _ ℂ) :=
    Filter.inter_mem hU (φ.open_source.mem_nhds h_zero_source)
  -- The image φ '' (U ∩ source) is a nbhd of φ(0)
  have h_φ_zero : φ 0 = (1 : Matrix _ _ ℂ) := by
    show (expAmbient_hasStrictFDerivAt_zero_equiv.toOpenPartialHomeomorph _ :
            Matrix _ _ ℂ → _) 0 = 1
    rw [HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
    exact NormedSpace.exp_zero
  -- Use the fact that φ is a local homeomorphism + map_nhds at source
  -- A point in source gets its 𝓝 to map to 𝓝 of image (by φ.image_mem_nhds)
  refine ⟨φ '' (U ∩ φ.source), ?_, ?_⟩
  · rw [← h_φ_zero]
    exact φ.image_mem_nhds h_zero_source hU'
  · -- Show φ '' (U ∩ source) ⊆ exp '' U
    rintro y ⟨x, ⟨hxU, _hxS⟩, hxy⟩
    refine ⟨x, hxU, ?_⟩
    have h_φx : φ x = NormedSpace.exp x := by
      show (expAmbient_hasStrictFDerivAt_zero_equiv.toOpenPartialHomeomorph _ :
              Matrix _ _ ℂ → _) x = NormedSpace.exp x
      rw [HasStrictFDerivAt.toOpenPartialHomeomorph_coe]
    rw [← h_φx]; exact hxy

/-! ## §4. Module summary

`SU2LocalDiffeo.lean` (Phase 6p Wave 2c.4a-R4.2.d.R5.4 Layer Cartan-C,
session 37): IFT-derived local-diffeo at identity.

**Shipped (zero new axioms)**:

  - **§1**: `expAmbient_hasStrictFDerivAt_zero` — exp has identity strict
    Fréchet derivative at 0 (Mathlib alias).
  - **§2**: `expAmbient_map_nhds_zero` — `map exp (𝓝 0) = 𝓝 1`
    (IFT consequence via `HasStrictFDerivAt.map_nhds_eq_of_equiv`).
  - **§3**: `expAmbient_image_contains_nhds_one` — for any U ∈ 𝓝(0),
    `exp '' U ∈ 𝓝(1)` (consumer-friendly form via open partial
    homeomorphism).

**Substrate downstream**:

  - **Cartan-D (session 38)**: D.3.i.2 — compose with D.3.h + D.3.i.1
    + AccPt to close `1 ∈ interior(closure H_Fib)`.
  - **Layer E (session 39)**: DenseInSpecialUnitary composition.

**Mathlib4-PR-viable**: this module purely composes Mathlib's IFT
(`HasStrictFDerivAt.toOpenPartialHomeomorph` + `map_nhds_eq_of_equiv`)
with the matrix exp derivative-at-0 (`hasStrictFDerivAt_exp_zero`).
Naturally upstreamable as `Matrix.exp_map_nhds_zero` companion.
-/

end SKEFTHawking.FKLW.SU2LocalDiffeo
