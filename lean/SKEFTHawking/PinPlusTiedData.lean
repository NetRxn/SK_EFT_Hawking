import Mathlib
import SKEFTHawking.PinPlusFaithfulData
import SKEFTHawking.SingularSWNumber

/-!
# Phase 5q.G (B-arc, B2) — the parity-TIED Pin⁺ datum: the grade constrained by `w₁⁴`

The structure-tied refinement of `pinPlusFaithfulData` (the B-arc checkpoint authorized by the
user toward the fully-unconditional program): a structure on `s` is a grade **whose mod-2
parity equals the manifold's Stiefel–Whitney number `w₁⁴[s.M]`** (`SingularSWNumber`), with the
Hausdorff-ness carried as a **structure field** (structures simply do not exist on non-`T2`
manifolds — the design that survives the ⊔-op case analysis; the two failure modes of naive
tying are recorded in the lab notebook push 119 and `SETTLED_FORKS`-adjacent notes).

What the tie buys over the free-grade datum:
* the `synthetic-grade-ker-bot-nogo` witness dies at this datum's level: a grade-`0` structure
  on an `ℝP⁴`-like manifold (`w₁⁴ = 1`) is **unpopulatable** (`tie` forces odd parity);
* on the empty manifold the tie's *equation* (not a vacuous ∀) forces **even** grades — the
  `(∅, grade-1)` pathology of the vacuous-quantified design is excluded;
* consequently the tied grade's surjectivity onto ODD classes is exactly the geometric
  realization question (a `w₁⁴ = 1` manifold in the singular tower — the B4 arc), surfacing
  the geometry where it belongs.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularCohomologyFunctoriality
open SKEFTHawking.PoincareDualityWu SKEFTHawking.PoincareDualityWuFormula
open SKEFTHawking.SingularPD4Instances SKEFTHawking.SingularWuTransport
open SKEFTHawking.SingularWuSum SKEFTHawking.SingularCochainGlue
open SKEFTHawking.TangentialDataBordism SKEFTHawking.PinPlusTangentialData
open SKEFTHawking.BordismTheory SKEFTHawking.CellularCohomologyMod2
open SKEFTHawking.PinPlusFaithfulData SKEFTHawking.SingularSWNumber

namespace SKEFTHawking.PinPlusTiedData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- The mod-2 reduction `ZMod 16 →+* ZMod 2` (the grade's parity). -/
def reduce16to2 : ZMod 16 →+* ZMod 2 := ZMod.castHom (by norm_num) (ZMod 2)

variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]

/-- `w₁⁴` totalized over the `Nonempty` gap (Hausdorff-ness supplied as a witness): the genuine
`swNumberW14` on nonempty manifolds, `0` on the empty one. -/
noncomputable def swTotalNe (s : SingularManifold PUnit ⊤ I) (h2 : T2Space s.M) : ZMod 2 :=
  letI := h2
  letI := Classical.dec (Nonempty s.M)
  if h : Nonempty s.M then
    letI := h
    swNumberW14 s.M
  else 0

omit [I.Boundaryless] in
/-- On an empty carrier the totalized `w₁⁴` is `0`. -/
theorem swTotalNe_of_isEmpty {s : SingularManifold PUnit ⊤ I} (h2 : T2Space s.M)
    [IsEmpty s.M] : swTotalNe s h2 = 0 := by
  rw [swTotalNe]
  exact dif_neg (not_nonempty_iff.mpr inferInstance)

omit [I.Boundaryless] in
/-- Hausdorff-ness of a disjoint union from witnessed components. -/
theorem t2_sum {s t : SingularManifold PUnit ⊤ I} (h2s : T2Space s.M) (h2t : T2Space t.M) :
    T2Space (s.sum t).M := by
  haveI := h2s
  haveI := h2t
  exact inferInstanceAs (T2Space (s.M ⊕ t.M))

omit [I.Boundaryless] in
/-- **The totalized `w₁⁴` is ⊔-additive** — the four `Nonempty`-cases: both live (B1
additivity), one empty (B1 homeo-invariance along `sumEmpty`/`emptySum`), both empty. -/
theorem swTotalNe_sum {s t : SingularManifold PUnit ⊤ I} (h2s : T2Space s.M)
    (h2t : T2Space t.M) :
    swTotalNe s h2s + swTotalNe t h2t = swTotalNe (s.sum t) (t2_sum h2s h2t) := by
  haveI := h2s
  haveI := h2t
  rcases isEmpty_or_nonempty s.M with hes | hnes
  · rcases isEmpty_or_nonempty t.M with het | hnet
    · haveI : IsEmpty (s.sum t).M :=
        inferInstanceAs (IsEmpty (s.M ⊕ t.M))
      rw [swTotalNe_of_isEmpty, swTotalNe_of_isEmpty, swTotalNe_of_isEmpty
          (s := s.sum t), add_zero]
    · haveI hne' : Nonempty (s.sum t).M := ⟨Sum.inr hnet.some⟩
      rw [swTotalNe_of_isEmpty, zero_add]
      show swTotalNe t h2t = swTotalNe (s.sum t) _
      haveI := t2_sum h2s h2t
      rw [swTotalNe, dif_pos hnet, swTotalNe, dif_pos hne']
      exact swNumberW14_homeo_invariant (Homeomorph.emptySum (Y := s.M) (X := t.M)).symm
  · rcases isEmpty_or_nonempty t.M with het | hnet
    · haveI hne' : Nonempty (s.sum t).M := ⟨Sum.inl hnes.some⟩
      rw [swTotalNe_of_isEmpty (h2 := h2t), add_zero]
      show swTotalNe s h2s = swTotalNe (s.sum t) _
      haveI := t2_sum h2s h2t
      rw [swTotalNe, dif_pos hnes, swTotalNe, dif_pos hne']
      exact swNumberW14_homeo_invariant (Homeomorph.sumEmpty (X := s.M) (Y := t.M)).symm
    · haveI hne' : Nonempty (s.sum t).M := ⟨Sum.inl hnes.some⟩
      rw [swTotalNe, dif_pos hnes, swTotalNe, dif_pos hnet, swTotalNe, dif_pos hne']
      exact (swNumberW14_sum (M := s.M) (N := t.M)).symm

/-- **A tied Pin⁺ structure**: a grade, the Hausdorff witness (a *field* — no structure exists
on a non-`T2` carrier), the `w₂`-certificate, and the **parity tie** `parity(grade) = w₁⁴`. -/
structure TiedStr (I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2))))
    [I.Boundaryless] (s : SingularManifold PUnit ⊤ I) : Type where
  /-- The ABK/`H¹`-torsor grade. -/
  grade : PinPlusGrade
  /-- The carrier is Hausdorff — witnessed, not assumed. -/
  t2 : T2Space s.M
  /-- The `w₂ = 0` admissibility certificate. -/
  cert : PinPlusCert I s
  /-- **The parity tie**: the grade's mod-2 class is the manifold's `w₁⁴`. -/
  tie : reduce16to2 grade.abk = swTotalNe s t2

/-- **The parity-tied Pin⁺ tangential datum** — `pinPlusFaithfulData` with the grade's parity
constrained by the genuine `w₁⁴`. The ⊔/homeo/reversal obligations are the `swTotalNe`
transport laws; the grade equations are verbatim. -/
noncomputable def pinPlusTiedData (I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2))))
    [I.Boundaryless] : TangentialData PUnit ⊤ I where
  Mfd := fun s => TiedStr I s
  Bor := fun _ σ τ => PLift (σ.grade.abk = τ.grade.abk)
  emptyStr :=
    { grade := 0
      t2 := ⟨fun x => x.elim⟩
      cert := pinPlusCert_empty
      tie := by rw [PinPlusGrade.abk_zero, map_zero, swTotalNe_of_isEmpty] }
  sumStr := fun {s t} σ τ =>
    { grade := σ.grade + τ.grade
      t2 := t2_sum σ.t2 τ.t2
      cert := PinPlusCert.sum σ.cert τ.cert
      tie := by
        rw [PinPlusGrade.abk_add, map_add, σ.tie, τ.tie]
        exact swTotalNe_sum σ.t2 τ.t2 }
  cylBor := fun _ => ⟨rfl⟩
  addBor := fun h₁ h₂ =>
    ⟨by rw [PinPlusGrade.abk_add, PinPlusGrade.abk_add, h₁.down, h₂.down]⟩
  symmBor := fun h => ⟨h.down.symm⟩
  commBor := fun σ τ => ⟨by simp [add_comm]⟩
  assocBor := fun σ τ ρ => ⟨by simp [add_assoc]⟩
  unitBor := fun σ => ⟨by simp⟩
  revStr := fun σ =>
    { grade := -σ.grade
      t2 := σ.t2
      cert := σ.cert
      tie := by
        rw [PinPlusGrade.abk_neg, map_neg, CharTwo.neg_eq]
        exact σ.tie }
  revBor := fun h => ⟨by rw [PinPlusGrade.abk_neg, PinPlusGrade.abk_neg, h.down]⟩
  negBor := fun σ =>
    ⟨show ((-σ.grade) + σ.grade).abk = (0 : PinPlusGrade).abk by
      rw [PinPlusGrade.abk_add, PinPlusGrade.abk_neg, PinPlusGrade.abk_zero, neg_add_cancel]⟩

/-- **The tied ABK grade** — the bordism-invariant additive `→+ ZMod 16` on the tied carrier. -/
def abkTiedGrade : DataBordismGrp (pinPlusTiedData I) →+ ZMod 16 where
  toFun := Quot.lift (fun p => p.2.grade.abk)
    (fun _p _q h => by obtain ⟨_, ⟨str⟩⟩ := h; exact str.down)
  map_zero' := rfl
  map_add' := by
    intro x y
    induction x using Quot.ind with | _ p =>
    induction y using Quot.ind with | _ q => rfl

/-- **Every even grade is realised** (on the empty manifold — the tie forces evenness there,
and every even class is `2k`): the tied grade's image contains the even subgroup. Odd classes
are exactly the `w₁⁴ = 1` realization question (B4). -/
theorem abkTiedGrade_hits_even (k : ZMod 16) :
    ∃ g : DataBordismGrp (pinPlusTiedData I), abkTiedGrade g = 2 * k := by
  refine ⟨DataBordismGrp.mk _ ⟨emptySM,
    { grade := (2 * k, 0)
      t2 := ⟨fun x => x.elim⟩
      cert := pinPlusCert_empty
      tie := ?_ }⟩, rfl⟩
  rw [swTotalNe_of_isEmpty]
  show reduce16to2 (2 * k) = 0
  rw [map_mul, show (reduce16to2 2 : ZMod 2) = 0 from by decide, zero_mul]

/-! ## §2. The tied quotient — `ℤ/16` up to the odd-realization question

The first isomorphism theorem gives the tied carrier's ABK quotient as the grade's **range**;
the range contains the even subgroup (realised on `∅`), and it is ALL of `ZMod 16` as soon as
ONE odd class is realised (the odds are a single coset of the evens) — which is exactly the
`w₁⁴ = 1` realization question (B4): the geometry, isolated to one witness. -/

universe u

/-- **The tied first isomorphism**: `DataBordismGrp (pinPlusTiedData I) ⧸ ker ≃+ range` —
unconditional. -/
noncomputable def dataBordismTied_quotient_equiv_range :
    DataBordismGrp (pinPlusTiedData I) ⧸ (abkTiedGrade (I := I)).ker
      ≃+ (abkTiedGrade (I := I)).range :=
  QuotientAddGroup.quotientKerEquivRange (abkTiedGrade (I := I))

/-- The even subgroup is in the tied grade's range. -/
theorem even_mem_abkTiedGrade_range (k : ZMod 16) :
    2 * k ∈ (abkTiedGrade (I := I)).range := by
  obtain ⟨g, hg⟩ := abkTiedGrade_hits_even (I := I) k
  exact ⟨g, hg⟩

/-- **One odd witness closes the range**: if any class has an odd grade, the range is all of
`ZMod 16` — the odds form a single coset of the evens, and the evens are realised on `∅`. -/
theorem abkTiedGrade_range_top_of_odd
    (h : ∃ g : DataBordismGrp.{u} (pinPlusTiedData I), reduce16to2 (abkTiedGrade g) = 1) :
    ((abkTiedGrade (I := I)) :
      DataBordismGrp.{u} (pinPlusTiedData I) →+ ZMod 16).range = ⊤ := by
  obtain ⟨g₀, hodd⟩ := h
  rw [AddSubgroup.eq_top_iff']
  intro x
  rcases (by decide : ∀ p : ZMod 2, p = 0 ∨ p = 1) (reduce16to2 x) with hx | hx
  · -- x even: x = 2 * k for some k (kernel of reduce16to2 = the even subgroup)
    obtain ⟨k, hk⟩ : ∃ k : ZMod 16, x = 2 * k := by
      revert hx; revert x; decide
    exact hk ▸ even_mem_abkTiedGrade_range k
  · -- x odd: x - abk(g₀) is even, so x = abk(g₀) + even ∈ range
    obtain ⟨k, hk⟩ : ∃ k : ZMod 16, x - abkTiedGrade g₀ = 2 * k := by
      have hdiff : reduce16to2 (x - abkTiedGrade g₀) = 0 := by
        rw [map_sub, hx, hodd, sub_self]
      revert hdiff; generalize x - abkTiedGrade g₀ = y; revert y; decide
    obtain ⟨gk, hgk⟩ := abkTiedGrade_hits_even (I := I) k
    refine AddMonoidHom.mem_range.mpr ⟨g₀ + gk, ?_⟩
    rw [map_add, hgk, ← hk, add_comm, sub_add_cancel]

/-- **The tied quotient is `ℤ/16` given one odd realization** — the B-arc checkpoint form: the
whole `ℤ/16` on the parity-tied carrier, with the geometry isolated to a single `w₁⁴ = 1`
witness (the B4 arc; e.g. `ℝP⁴` in the singular tower). -/
noncomputable def dataBordismTied_quotient_equiv_zmod16_of_odd
    (h : ∃ g : DataBordismGrp.{u} (pinPlusTiedData I), reduce16to2 (abkTiedGrade g) = 1) :
    (DataBordismGrp.{u} (pinPlusTiedData I) ⧸
      ((abkTiedGrade (I := I)) :
        DataBordismGrp.{u} (pinPlusTiedData I) →+ ZMod 16).ker) ≃+ ZMod 16 :=
  QuotientAddGroup.quotientKerEquivOfSurjective (abkTiedGrade (I := I))
    (by
      intro x
      have hrange := abkTiedGrade_range_top_of_odd h
      have : x ∈ (abkTiedGrade (I := I)).range := hrange ▸ AddSubgroup.mem_top x
      exact AddMonoidHom.mem_range.mp this)

end SKEFTHawking.PinPlusTiedData
