import Mathlib
import SKEFTHawking.PinPlusTangentialData
import SKEFTHawking.SingularWuTransport
import SKEFTHawking.SingularWuSum

/-!
# Phase 5q.G (G3-3b) — the faithful Pin⁺ tangential datum: the `w₂`-certified grade

The faithful refinement of `pinPlusData`: a structure on `s` is a Pin⁺ grade **together with the
`w₂`-certificate of the underlying manifold** —
`Mfd s := {g : PinPlusGrade // PinPlusCert I s}` where `PinPlusCert I s` says the singular Wu
class of `s.M` vanishes (`wuW2 = 0` on the genuine PD instances, quantified over the `T2Space`
and `Nonempty` instances Mathlib's `SingularManifold` does not bundle — vacuous on the empty
manifold). A structure *exists* only on Pin⁺-admissible (w₂ = 0) manifolds: the carrier is
faithful to the geometry, unlike `pinPlusData`'s manifold-blind grade.

The op-transport obligations are exactly the F-ladder:
* `sumStr` — `PinPlusCert.sum`: the ⊔-criterion `wuW2_sum_eq_zero_iff` (F7d) for two nonempty
  pieces, the homeo-invariance `wuW2_pullback` (F6) through `Homeomorph.sumEmpty/emptySum` when
  one piece is empty, vacuity when both are.
* all grade equations — verbatim `pinPlusData` (the certificate rides along).

`revStr ⟨g, c⟩ := ⟨-g, c⟩` stays genuinely non-trivial (`pinPlusFaithfulData_revStr_nontrivial`),
so the 2-torsion no-go does not apply to the faithful carrier either.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularCohomologyFunctoriality
open SKEFTHawking.PoincareDualityWu SKEFTHawking.PoincareDualityWuFormula
open SKEFTHawking.SingularPD4Instances SKEFTHawking.SingularWuTransport
open SKEFTHawking.SingularWuSum SKEFTHawking.SingularCochainGlue
open SKEFTHawking.TangentialDataBordism SKEFTHawking.PinPlusTangentialData
open SKEFTHawking.BordismTheory SKEFTHawking.CellularCohomologyMod2

namespace SKEFTHawking.PinPlusFaithfulData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- **The Pin⁺ admissibility certificate**: the singular Wu class `w₂` of the underlying closed
charted 4-manifold vanishes, on the genuine PD instances. Quantified over the `T2Space` and
`Nonempty` instances (not bundled by `SingularManifold`) — vacuously true on the empty manifold. -/
def PinPlusCert (I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))) [I.Boundaryless]
    (s : SingularManifold PUnit ⊤ I) : Prop :=
  ∀ [T2Space s.M] [Nonempty s.M],
    wuW2 (poincareDual4Mid_of_closed (M := s.M)) (poincareDual4Lo_of_closed (M := s.M)) = 0

variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]

/-- The empty manifold is (vacuously) certified. -/
theorem pinPlusCert_empty : PinPlusCert I (emptySM : SingularManifold PUnit ⊤ I) := by
  intro _ hne
  exact absurd hne (not_nonempty_iff.mpr inferInstance)

/-- **The certificate is closed under disjoint union** — the F-ladder in action: `wuW2_sum_eq_zero_iff`
(F7d) for two nonempty pieces; `wuW2_pullback` (F6) along `Homeomorph.sumEmpty/emptySum` when one
piece is empty; vacuous when both are. -/
theorem PinPlusCert.sum {s t : SingularManifold PUnit ⊤ I}
    (hs : PinPlusCert I s) (ht : PinPlusCert I t) : PinPlusCert I (s.sum t) := by
  intro hT2 hne
  haveI hT2' : T2Space (s.M ⊕ t.M) := hT2
  haveI hne' : Nonempty (s.M ⊕ t.M) := hne
  haveI : T2Space s.M := (Topology.IsEmbedding.inl (X := s.M) (Y := t.M)).t2Space
  haveI : T2Space t.M := (Topology.IsEmbedding.inr (X := s.M) (Y := t.M)).t2Space
  rcases isEmpty_or_nonempty s.M with hes | hnes
  · rcases isEmpty_or_nonempty t.M with het | hnet
    · -- both empty: contradicts `Nonempty (s.M ⊕ t.M)`
      exact absurd hne' (by rw [not_nonempty_iff]; infer_instance)
    · -- `s` empty: transport `ht` along `t.M ≃ₜ s.M ⊕ t.M`
      have h := wuW2_pullback (M := t.M) (N := s.M ⊕ t.M)
        (Homeomorph.emptySum (Y := s.M) (X := t.M)).symm
      rw [ht] at h
      have h2 : (cohomologyHomeoEquiv (X := TopCat.of t.M) (Y := TopCat.of (s.M ⊕ t.M))
          (Homeomorph.emptySum (Y := s.M) (X := t.M)).symm 2)
          (wuW2 (poincareDual4Mid_of_closed (M := s.M ⊕ t.M))
            (poincareDual4Lo_of_closed (M := s.M ⊕ t.M))) = 0 := h
      exact (LinearEquiv.map_eq_zero_iff _).mp h2
  · rcases isEmpty_or_nonempty t.M with het | hnet
    · -- `t` empty: transport `hs` along `s.M ≃ₜ s.M ⊕ t.M`
      have h := wuW2_pullback (M := s.M) (N := s.M ⊕ t.M)
        (Homeomorph.sumEmpty (X := s.M) (Y := t.M)).symm
      rw [hs] at h
      have h2 : (cohomologyHomeoEquiv (X := TopCat.of s.M) (Y := TopCat.of (s.M ⊕ t.M))
          (Homeomorph.sumEmpty (X := s.M) (Y := t.M)).symm 2)
          (wuW2 (poincareDual4Mid_of_closed (M := s.M ⊕ t.M))
            (poincareDual4Lo_of_closed (M := s.M ⊕ t.M))) = 0 := h
      exact (LinearEquiv.map_eq_zero_iff _).mp h2
    · -- both nonempty: the F7d ⊔-criterion
      exact (wuW2_sum_eq_zero_iff (M := s.M) (N := t.M)).mpr ⟨hs, ht⟩

/-- **The faithful Pin⁺ tangential datum**: `Mfd s := {g : PinPlusGrade // PinPlusCert I s}` —
the grade plus the manifold's `w₂`-certificate; `Bor` is the ABK-invariance constraint; all
grade equations are `pinPlusData`'s, with the certificate transported by the F-ladder. -/
noncomputable def pinPlusFaithfulData (I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2))))
    [I.Boundaryless] : TangentialData PUnit ⊤ I where
  Mfd := fun s => {_g : PinPlusGrade // PinPlusCert I s}
  Bor := fun _ σ τ => PLift (σ.1.abk = τ.1.abk)
  emptyStr := ⟨0, pinPlusCert_empty⟩
  sumStr := fun σ τ => ⟨σ.1 + τ.1, PinPlusCert.sum σ.2 τ.2⟩
  cylBor := fun _ => ⟨rfl⟩
  addBor := fun h₁ h₂ => ⟨by rw [PinPlusGrade.abk_add, PinPlusGrade.abk_add, h₁.down, h₂.down]⟩
  symmBor := fun h => ⟨h.down.symm⟩
  commBor := fun σ τ => ⟨by simp [add_comm]⟩
  assocBor := fun σ τ ρ => ⟨by simp [add_assoc]⟩
  unitBor := fun σ => ⟨by simp⟩
  revStr := fun σ => ⟨-σ.1, σ.2⟩
  revBor := fun h => ⟨by rw [PinPlusGrade.abk_neg, PinPlusGrade.abk_neg, h.down]⟩
  negBor := fun σ =>
    ⟨show ((-σ.1) + σ.1).abk = (0 : PinPlusGrade).abk by
      rw [PinPlusGrade.abk_add, PinPlusGrade.abk_neg, PinPlusGrade.abk_zero, neg_add_cancel]⟩

/-- The faithful conjugation is genuinely non-trivial — on the (vacuously certified) empty
manifold, `revStr ⟨(1,0), _⟩ ≠ ⟨(1,0), _⟩` (`−1 ≠ 1` in `ZMod 16`); the 2-torsion no-go does not
apply to the faithful carrier. -/
theorem pinPlusFaithfulData_revStr_nontrivial :
    ∃ (s : SingularManifold PUnit ⊤ I) (σ : (pinPlusFaithfulData I).Mfd s),
      (pinPlusFaithfulData I).revStr σ ≠ σ := by
  refine ⟨emptySM, ⟨((1 : ZMod 16), (0 : Cohomology (RPComplex 1) 1)), pinPlusCert_empty⟩, ?_⟩
  intro h
  have h1 : (-((1 : ZMod 16), (0 : Cohomology (RPComplex 1) 1)) :
      ZMod 16 × Cohomology (RPComplex 1) 1) = ((1 : ZMod 16), 0) := congrArg Subtype.val h
  have : (-1 : ZMod 16) = 1 := congrArg Prod.fst h1
  exact absurd this (by decide)

/-- The no-go's hypothesis fails for the faithful datum too. -/
theorem pinPlusFaithfulData_not_revStr_trivial :
    ¬ (∀ {s : SingularManifold PUnit ⊤ I} (σ : (pinPlusFaithfulData I).Mfd s),
        (pinPlusFaithfulData I).revStr σ = σ) := by
  intro htriv
  obtain ⟨s, σ, hσ⟩ := pinPlusFaithfulData_revStr_nontrivial (I := I)
  exact hσ (htriv σ)

end SKEFTHawking.PinPlusFaithfulData
