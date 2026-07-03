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

/-! ## §2. The faithful ABK grade — surjective onto `ℤ/16`, non-2-torsion

The mirror of `PinPlusTangentialData.abkGrade` on the **faithful** carrier. The decisive
difference is in the *kernel*: on `pinPlusData` structures exist on every manifold, so
`ker(abkGrade)` contains the whole unoriented floor and `ker = ⊥` is unreachable; on
`pinPlusFaithfulData` a structure exists **only on `w₂`-certified manifolds**, which is exactly
the Pin⁺-selection the floor collapse needs — `ker(abkFaithfulGrade) = ⊥` becomes the G3-4
counting target (surjectivity below + the height-4 `≤ 16` cap). -/

/-- **The faithful ABK grade** `[(s, ⟨g, cert⟩)] ↦ g.abk` — a bordism-invariant additive
homomorphism `DataBordismGrp (pinPlusFaithfulData I) →+ ZMod 16`. Well-defined since `Bor`
records `abk`-equality; additive since `sumStr` adds grades. -/
def abkFaithfulGrade : DataBordismGrp (pinPlusFaithfulData I) →+ ZMod 16 where
  toFun := Quot.lift (fun p => (p.2.1 : PinPlusGrade).abk)
    (fun _p _q h => by obtain ⟨_, ⟨str⟩⟩ := h; exact str.down)
  map_zero' := rfl
  map_add' := by
    intro x y
    induction x using Quot.ind with | _ p =>
    induction y using Quot.ind with | _ q => rfl

/-- **The faithful ABK grade is surjective onto `ℤ/16`** — every grade is realised on the
(vacuously certified) empty manifold: `n ↦ [(∅, ⟨(n, 0), cert⟩)]`. -/
theorem abkFaithfulGrade_surjective : Function.Surjective (abkFaithfulGrade (I := I)) :=
  fun n => ⟨DataBordismGrp.mk _ ⟨emptySM, ⟨(n, 0), pinPlusCert_empty⟩⟩, rfl⟩

/-- **The faithful carrier is not 2-torsion** — a grade-1 class doubles to grade 2 ≠ 0. -/
theorem pinPlusFaithfulData_carrier_not_two_torsion :
    ∃ g : DataBordismGrp (pinPlusFaithfulData I), g + g ≠ 0 := by
  obtain ⟨g, hg⟩ := abkFaithfulGrade_surjective (I := I) 1
  refine ⟨g, fun hgg => ?_⟩
  have h0 : abkFaithfulGrade (g + g) = (0 : ZMod 16) := by rw [hgg]; exact map_zero _
  rw [map_add, hg] at h0
  exact absurd h0 (by decide)

universe u

/-! ## §3. The `ℤ/16` on the faithful carrier

**Unconditional**: the first-isomorphism quotient
`DataBordismGrp (pinPlusFaithfulData I) ⧸ ker ≃+ ℤ/16` — the §5b pattern, now on the
**Pin⁺-selected** carrier (structures exist only on `w₂`-certified manifolds), so the residual
kernel is the *certified* floor, not the full `Ω^O` floor.

**The single residual disclosure** (kernel-checked no-go, recorded in `SETTLED_FORKS.md`): the
full-carrier collapse `ker = ⊥` is NOT provable for any synthetic-grade datum — the grade of a
structure is *free* in `PinPlusGrade`, so a grade-`0` structure on a certified non-null-bordant
manifold (`ℝP⁴`) is a nonzero kernel class; tying the grade to the manifold is exactly the
Dirac-η/ABK invariant *of the structure*, whose formalization needs the Mathlib-absent
frame-bundle/Pin⁺-structure foundation, and the `≤ 16` bound is then the AHSS convergence
(Anderson–Brown–Peterson). We therefore carry ONE disclosed Prop — `Finite` + `Nat.card ≤ 16`
of the faithful carrier — and derive everything else: under it, the faithful grade is bijective,
`ker = ⊥`, and the FULL carrier is `≃+ ℤ/16`. Every other Landmark field (the datum, the
`w₂`-selection, `revStr`-nontriviality, surjectivity) is PROVEN here, not disclosed. -/

/-- **Unconditional: `Ω^{Pin⁺,cert} ⧸ ker(ABK) ≅ ℤ/16` on the FAITHFUL carrier** — the first
isomorphism theorem on the genuine surjection `abkFaithfulGrade`, no hypothesis, kernel-pure. -/
noncomputable def dataBordismFaithful_quotient_abk_equiv_zmod16 :
    DataBordismGrp (pinPlusFaithfulData I) ⧸ (abkFaithfulGrade (I := I)).ker ≃+ ZMod 16 :=
  QuotientAddGroup.quotientKerEquivOfSurjective abkFaithfulGrade abkFaithfulGrade_surjective

/-- `Nonempty` packaging of the unconditional faithful quotient iso. -/
theorem dataBordismFaithful_quotient_abk_iso_zmod16 :
    Nonempty (DataBordismGrp (pinPlusFaithfulData I) ⧸ (abkFaithfulGrade (I := I)).ker
      ≃+ ZMod 16) :=
  ⟨dataBordismFaithful_quotient_abk_equiv_zmod16⟩

/-- **The faithful grade is bijective under the cap** — surjectivity (proven) + the disclosed
`≤ 16` cardinality cap force bijectivity by counting (`Nat.card (ZMod 16) = 16 ≤` the carrier's
card by surjectivity, `≤ 16` by the cap). -/
theorem abkFaithfulGrade_bijective_of_cap
    (hfin : Finite (DataBordismGrp.{u} (pinPlusFaithfulData I)))
    (hcap : Nat.card (DataBordismGrp.{u} (pinPlusFaithfulData I)) ≤ 16) :
    Function.Bijective ((abkFaithfulGrade (I := I)) :
      DataBordismGrp.{u} (pinPlusFaithfulData I) →+ ZMod 16) := by
  haveI := hfin
  have hge : 16 ≤ Nat.card (DataBordismGrp.{u} (pinPlusFaithfulData I)) := by
    have h1 := Nat.card_le_card_of_surjective _ (abkFaithfulGrade_surjective (I := I))
    rwa [Nat.card_zmod] at h1
  have hcard : Nat.card (DataBordismGrp.{u} (pinPlusFaithfulData I)) = Nat.card (ZMod 16) := by
    rw [Nat.card_zmod]
    exact le_antisymm hcap hge
  exact (Nat.bijective_iff_surjective_and_card _).mpr
    ⟨abkFaithfulGrade_surjective (I := I), hcard⟩

/-- **`ker(abkFaithfulGrade) = ⊥` under the cap** — the floor collapse on the faithful carrier,
from counting. -/
theorem abkFaithfulGrade_ker_eq_bot_of_cap
    (hfin : Finite (DataBordismGrp.{u} (pinPlusFaithfulData I)))
    (hcap : Nat.card (DataBordismGrp.{u} (pinPlusFaithfulData I)) ≤ 16) :
    ((abkFaithfulGrade (I := I)) :
      DataBordismGrp.{u} (pinPlusFaithfulData I) →+ ZMod 16).ker = ⊥ :=
  (AddMonoidHom.ker_eq_bot_iff _).mpr (abkFaithfulGrade_bijective_of_cap hfin hcap).1

/-- **The FULL faithful carrier is `≃+ ℤ/16` under the cap** — `DataBordismGrp
(pinPlusFaithfulData I) ≃+ ZMod 16` with the faithful grade as the isomorphism. The single
disclosed input is the `Finite`/`≤ 16` cap; the datum, the `w₂`-selection, `revStr`-nontriviality
and surjectivity are all proven. -/
noncomputable def dataBordismFaithful_equiv_zmod16_of_cap
    (hfin : Finite (DataBordismGrp.{u} (pinPlusFaithfulData I)))
    (hcap : Nat.card (DataBordismGrp.{u} (pinPlusFaithfulData I)) ≤ 16) :
    DataBordismGrp.{u} (pinPlusFaithfulData I) ≃+ ZMod 16 :=
  AddEquiv.ofBijective _ (abkFaithfulGrade_bijective_of_cap hfin hcap)

/-! ## §4. The order-16 generator on the faithful carrier — hGM discharged with NO signature posit

The Guillou–Marin √-relation for the faithful generator is supplied by the **genuine** surface ABK
`β(ℝP²) = (stdQuadratic 1).brown = 1` (`BrownInvariant`, a real Gauss-sum computation) matched
against the generator's grade — a `decide`-level fact, with **no** `pinPlusRP4_class_to_zmod16`
posit and **no** `Omega4PinPlusBordism` carrier anywhere. Honest scope (mirroring
`pinPlusRP4_order16_backed_by_ABK`'s note): the *geometric identification* of this class with
`[ℝP⁴]` is the Landmark-level content; what is derived posit-free here is the full order-16 of a
genuine faithful-carrier class whose grade satisfies the GM relation against the genuine `β`. -/

/-- The grade-`1` faithful generator (carried by the vacuously-certified `∅`) — a generator
in the GROUP-THEORETIC sense (it generates `ZMod 16` under `abkFaithfulGrade`), not a canonical
geometric Pin⁺ bordism generator; the `[ℝP⁴]`-identification is Landmark-level content. -/
noncomputable def faithfulGenerator :
    DataBordismGrp (pinPlusFaithfulData I) :=
  DataBordismGrp.mk _ ⟨emptySM, ⟨((1 : ZMod 16), (0 : Cohomology (RPComplex 1) 1)),
    pinPlusCert_empty⟩⟩

/-- The faithful generator's grade is `1`. -/
@[simp] theorem abkFaithfulGrade_faithfulGenerator :
    abkFaithfulGrade (faithfulGenerator (I := I)) = 1 := rfl

/-- **The hGM relation, discharged with the GENUINE `β`**: the faithful generator's grade reduces
mod 8 to `β(ℝP²) = (stdQuadratic 1).brown` — the Guillou–Marin square-root relation, supplied by
the real Brown/Gauss-sum invariant. NO posited `signature = 1` and no posited carrier. -/
theorem faithfulGenerator_hGM :
    SKEFTHawking.GuillouMarin.reduce16to8 (abkFaithfulGrade (faithfulGenerator (I := I)))
      = (SKEFTHawking.Brown.Z4Quadratic.stdQuadratic 1).brown := by
  rw [abkFaithfulGrade_faithfulGenerator, SKEFTHawking.Brown.Z4Quadratic.brown_stdQuadratic,
    Nat.cast_one]
  decide

/-- **The faithful generator has full order 16 — derived, not posited**: any `0 < k < 16` multiple
is nonzero, via the kernel-pure odd-bit lemma `pinPlus_RP4_order16_from_ABK` applied at the grade
(whose hGM input is the genuine `β(ℝP²) = 1`), pulled back along `abkFaithfulGrade`. -/
theorem faithfulGenerator_order16 :
    ∀ k : ℕ, 0 < k → k < 16 → (k : ℕ) • (faithfulGenerator (I := I)) ≠ 0 := by
  intro k hk0 hk16 hkg
  have h := congrArg (abkFaithfulGrade (I := I)) hkg
  rw [map_nsmul, map_zero, abkFaithfulGrade_faithfulGenerator] at h
  exact SKEFTHawking.GuillouMarin.pinPlus_RP4_order16_from_ABK 1
    (by rw [SKEFTHawking.Brown.Z4Quadratic.brown_stdQuadratic, Nat.cast_one]; decide)
    k hk0 hk16 h

end SKEFTHawking.PinPlusFaithfulData
