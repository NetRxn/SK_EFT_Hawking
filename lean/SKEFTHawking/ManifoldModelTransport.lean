/-
Copyright (c) 2026 SK_EFT_Hawking contributors. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib.Geometry.Manifold.IsManifold.Basic
import Mathlib.Geometry.Manifold.Instances.Real
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Model transport for boundaryless manifolds

A charted space / manifold structure modelled on a normed space `E` transports along a
**continuous linear equivalence** `φ : E ≃L[ℝ] F` to one modelled on `F`.

This is the generic, `M`-polymorphic version of the `reshapeModel` conjugation banked in
`KummerResolutionPieceBoundary` (§P): there the reassembly `𝓔² × (𝓔¹ × HS¹) ≃ₜ 𝓔³ × HS¹` was
threaded by hand through each transition proof; here we prove the conjugation **once**, at the
level of the whole `ChartedSpace` / `IsManifold` structure, so a manifold built on whichever
Euclidean-factor decomposition its charts naturally produce can be delivered on the flat model
`𝓡 n` that downstream consumers (`StrMfd`, `CharPairWProviderPerOp`) demand.

## Main definitions

* `SKEFTHawking.ManifoldModelTransport.modelChart φ` — the global chart `E → F` given by `φ`,
  as an `OpenPartialHomeomorph` with `source = univ`.
* `SKEFTHawking.ManifoldModelTransport.transportedChartedSpace φ M` — `ChartedSpace F M`
  obtained from `ChartedSpace E M` by post-composing every chart with `φ`.

## Main results

* `SKEFTHawking.ManifoldModelTransport.mem_contDiffGroupoid_conj` — the conjugate
  `φ⁻¹ ≫ₕ g ≫ₕ φ` of a `C^n` coordinate change `g` on `E` is a `C^n` coordinate change on `F`.
* `SKEFTHawking.ManifoldModelTransport.isManifold_transport` — **the transport theorem**:
  `IsManifold 𝓘(ℝ, E) n M → IsManifold 𝓘(ℝ, F) n M` (with the transported charted space).

## The concrete `𝓔³ × ℝ ≃L 𝓔⁴` instance

* `SKEFTHawking.ManifoldModelTransport.prodRealEquivEuclidean` — `𝓔ⁿ × ℝ ≃L[ℝ] 𝓔⁽ⁿ⁺¹⁾`.
* `SKEFTHawking.ManifoldModelTransport.isManifold_R4_of_prodReal` — the packaged
  `IsManifold ((𝓡 3).prod 𝓘(ℝ, ℝ)) n M → IsManifold (𝓡 4) n M` step.
-/

noncomputable section

open Set Topology
open scoped Manifold

namespace SKEFTHawking.ManifoldModelTransport

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-! ## §A. The global model chart -/

/-- The global chart `E → F` induced by a continuous linear equivalence, as an
`OpenPartialHomeomorph` with `source = univ` and `target = univ`. -/
def modelChart (φ : E ≃L[ℝ] F) : OpenPartialHomeomorph E F :=
  φ.toHomeomorph.toOpenPartialHomeomorph

@[simp] theorem modelChart_source (φ : E ≃L[ℝ] F) : (modelChart φ).source = univ := rfl

@[simp] theorem modelChart_target (φ : E ≃L[ℝ] F) : (modelChart φ).target = univ := rfl

@[simp] theorem modelChart_apply (φ : E ≃L[ℝ] F) (x : E) : modelChart φ x = φ x := rfl

@[simp] theorem modelChart_symm_apply (φ : E ≃L[ℝ] F) (y : F) :
    (modelChart φ).symm y = φ.symm y := rfl

/-- `E` is a (single-chart) charted space over `F` via `φ`. -/
@[reducible] def modelChartedSpace (φ : E ≃L[ℝ] F) : ChartedSpace F E :=
  (modelChart φ).singletonChartedSpace (modelChart_source φ)

/-- **The transported charted space.** Every chart of `M` (modelled on `E`) is post-composed with
the global model chart `φ`, giving an atlas modelled on `F`. -/
@[reducible] def transportedChartedSpace (φ : E ≃L[ℝ] F) (M : Type*) [TopologicalSpace M]
    [ChartedSpace E M] : ChartedSpace F M :=
  letI := modelChartedSpace φ
  ChartedSpace.comp F E M

/-! ## §B. Membership in the `C^n` groupoid for self-models -/

variable {n : WithTop ℕ∞}

/-- For a **self-model** `𝓘(ℝ, F)` the `contDiffGroupoid` membership condition is literally
`ContDiffOn` of the map on its source and of its inverse on its target: the model map and its
inverse are the identity and `range 𝓘(ℝ, F) = univ`. -/
theorem mem_contDiffGroupoid_self {g : OpenPartialHomeomorph F F} :
    g ∈ contDiffGroupoid n 𝓘(ℝ, F) ↔
      ContDiffOn ℝ n g g.source ∧ ContDiffOn ℝ n g.symm g.target := by
  rw [contDiffGroupoid, mem_groupoid_of_pregroupoid]
  simp only [contDiffPregroupoid, mfld_simps]

/-- **The conjugation lemma.** If `g` is a `C^n` coordinate change of `E`, then its `φ`-conjugate
`φ⁻¹ ≫ₕ g ≫ₕ φ` is a `C^n` coordinate change of `F`. -/
theorem mem_contDiffGroupoid_conj (φ : E ≃L[ℝ] F) {g : OpenPartialHomeomorph E E}
    (hg : g ∈ contDiffGroupoid n 𝓘(ℝ, E)) :
    ((modelChart φ).symm.trans g).trans (modelChart φ) ∈ contDiffGroupoid n 𝓘(ℝ, F) := by
  rw [mem_contDiffGroupoid_self] at hg ⊢
  obtain ⟨hg1, hg2⟩ := hg
  constructor
  · have h1 : ContDiffOn ℝ n (fun y : F => g (φ.symm y)) (φ.symm ⁻¹' g.source) :=
      hg1.comp (φ.symm.contDiff.contDiffOn) (fun y hy => hy)
    have h2 : ContDiffOn ℝ n (fun y : F => φ (g (φ.symm y))) (φ.symm ⁻¹' g.source) :=
      φ.contDiff.comp_contDiffOn h1
    refine h2.congr_mono (fun y hy => rfl) ?_
    intro y hy
    simpa [modelChart] using hy
  · have h1 : ContDiffOn ℝ n (fun y : F => g.symm (φ.symm y)) (φ.symm ⁻¹' g.target) :=
      hg2.comp (φ.symm.contDiff.contDiffOn) (fun y hy => hy)
    have h2 : ContDiffOn ℝ n (fun y : F => φ (g.symm (φ.symm y))) (φ.symm ⁻¹' g.target) :=
      φ.contDiff.comp_contDiffOn h1
    refine h2.congr_mono (fun y hy => rfl) ?_
    intro y hy
    simpa [modelChart] using hy

/-! ## §C. The transport theorem -/

variable (M : Type*) [TopologicalSpace M] [ChartedSpace E M]

/-- **THE MODEL TRANSPORT.** A `C^n` manifold modelled on the self-model `𝓘(ℝ, E)` is a `C^n`
manifold modelled on `𝓘(ℝ, F)` for the transported charted space, for any continuous linear
equivalence `φ : E ≃L[ℝ] F`. -/
theorem isManifold_transport (φ : E ≃L[ℝ] F) [IsManifold 𝓘(ℝ, E) n M] :
    letI := transportedChartedSpace φ M
    IsManifold 𝓘(ℝ, F) n M := by
  letI := transportedChartedSpace φ M
  haveI : HasGroupoid M (contDiffGroupoid n 𝓘(ℝ, F)) := by
    refine ⟨?_⟩
    rintro f f' ⟨e, he, c, hc, rfl⟩ ⟨e', he', c', hc', rfl⟩
    have hcφ : c = modelChart φ := by
      simpa [modelChartedSpace] using
        (OpenPartialHomeomorph.singletonChartedSpace_mem_atlas_eq _ (modelChart_source φ) _ hc)
    have hcφ' : c' = modelChart φ := by
      simpa [modelChartedSpace] using
        (OpenPartialHomeomorph.singletonChartedSpace_mem_atlas_eq _ (modelChart_source φ) _ hc')
    subst hcφ; subst hcφ'
    have hcomp : (e.trans (modelChart φ)).symm.trans (e'.trans (modelChart φ))
        = ((modelChart φ).symm.trans (e.symm.trans e')).trans (modelChart φ) := by
      rw [OpenPartialHomeomorph.trans_symm_eq_symm_trans_symm]
      rw [OpenPartialHomeomorph.trans_assoc, OpenPartialHomeomorph.trans_assoc,
        ← OpenPartialHomeomorph.trans_assoc e.symm e' (modelChart φ)]
    rw [hcomp]
    exact mem_contDiffGroupoid_conj φ (StructureGroupoid.compatible _ he he')
  exact IsManifold.mk' _ _ _

/-! ## §D. The concrete `𝓔ⁿ × ℝ ≃L 𝓔⁽ⁿ⁺¹⁾` reshape -/

/-- `(Fin n → ℝ) × ℝ ≃ₗ[ℝ] (Fin (n+1) → ℝ)` — append the extra real coordinate last (`Fin.snoc`).

Built by hand on **plain** pi types rather than through `EuclideanSpace.finAddEquivProd`: that
`abbrev` is `[RCLike 𝕜]`-parameterised, so its normed instances elaborate through
`RCLike.toDenselyNormedField`, which does not unify with the direct `ℝ` instance path — the
resulting `≃L` is unusable against a hand-written `ℝ`-typed signature. -/
def snocLinearEquiv (n : ℕ) : ((Fin n → ℝ) × ℝ) ≃ₗ[ℝ] (Fin (n + 1) → ℝ) where
  toFun q := Fin.snoc q.1 q.2
  map_add' q r := by funext i; refine Fin.lastCases ?_ ?_ i <;> simp
  map_smul' c q := by funext i; refine Fin.lastCases ?_ ?_ i <;> simp
  invFun v := (fun i => v i.castSucc, v (Fin.last n))
  left_inv q := by
    refine Prod.ext ?_ ?_
    · funext i; simp
    · simp
  right_inv v := by funext i; refine Fin.lastCases ?_ ?_ i <;> simp

/-- `snocLinearEquiv` as a continuous linear equivalence. -/
def snocContinuousLinearEquiv (n : ℕ) : ((Fin n → ℝ) × ℝ) ≃L[ℝ] (Fin (n + 1) → ℝ) where
  toLinearEquiv := snocLinearEquiv n
  continuous_toFun := by
    refine continuous_pi fun i => ?_
    refine Fin.lastCases ?_ ?_ i
    · simpa [snocLinearEquiv] using continuous_snd
    · intro j; simpa [snocLinearEquiv] using (continuous_apply j).comp continuous_fst
  continuous_invFun :=
    Continuous.prodMk (continuous_pi fun i => continuous_apply _) (continuous_apply _)

/-- **The model reshape** `𝓔ⁿ × ℝ ≃L[ℝ] 𝓔⁽ⁿ⁺¹⁾`: append the extra real coordinate as the last
Euclidean coordinate. The generic, linear analogue of `KummerResolutionPieceBoundary.reshapeModel`
(which merges `𝓔² × 𝓔¹` into `𝓔³` keeping a half-space factor); here both sides are boundaryless,
so the reshape is a *continuous linear* equivalence and the whole conjugation is available. -/
def prodRealEquivEuclidean (n : ℕ) :
    (EuclideanSpace ℝ (Fin n) × ℝ) ≃L[ℝ] EuclideanSpace ℝ (Fin (n + 1)) :=
  (((PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin n => ℝ)).prodCongr
      (ContinuousLinearEquiv.refl ℝ ℝ)).trans (snocContinuousLinearEquiv n)).trans
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin (n + 1) => ℝ)).symm

/-- **The equivalence certificate for the briefed model.** The brief names the intermediate model
`(𝓡 3).prod 𝓘(ℝ, ℝ)`; we work with `𝓘(ℝ, 𝓔³ × ℝ)`. These are *the same model with corners* —
`ModelProd` is only a type tag (`ModelProd H H' := H × H'`, deliberately semireducible so that
instance search does not confuse a product manifold with a product of charted spaces). Working on
the untagged product is what lets ordinary `NormedSpace` instance resolution fire on the model
space, which the tagged form blocks. -/
theorem model_prod3Real_eq : (𝓡 3).prod 𝓘(ℝ, ℝ) = 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × ℝ) :=
  modelWithCornersSelf_prod.symm

/-- **The mission's transport step**, packaged at the briefed models: a `C^n` manifold charted on
`𝓔³ × ℝ` — the model that every `𝓔³ × [interval]` chart family produces natively, and which
`model_prod3Real_eq` identifies with the briefed `(𝓡 3).prod 𝓘(ℝ, ℝ)` — is a `C^n` manifold charted
on the flat `𝓡 4` that downstream `StrMfd` consumers demand. -/
theorem isManifold_R4_of_prodReal (N : Type*) [TopologicalSpace N]
    [ChartedSpace (EuclideanSpace ℝ (Fin 3) × ℝ) N]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin 3) × ℝ) n N] :
    letI := transportedChartedSpace (prodRealEquivEuclidean 3) N
    IsManifold (𝓡 4) n N :=
  isManifold_transport N (prodRealEquivEuclidean 3)

end SKEFTHawking.ManifoldModelTransport
