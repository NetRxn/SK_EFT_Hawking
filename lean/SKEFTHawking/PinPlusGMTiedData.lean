import Mathlib
import SKEFTHawking.PinPlusGMData
import SKEFTHawking.PinPlusTiedData
import SKEFTHawking.GuillouMarinBridge

/-!
# Phase 5q.H (H6-a) — the TIED Guillou–Marin carrier: a ℤ/16 grade with the mod-8 part COMPUTED

The free-`q` carrier `pinPlusGMData` (H3–H5) cannot support `ker = ⊥` — its grade is free per manifold, so
the `synthetic-grade-ker-bot-nogo` applies (a grade-0 structure on non-null-bordant `ℝP⁴` is a nonzero
kernel class). Moreover `abkGM8 : → ZMod 8` can NEVER have `ker = ⊥` (the `ZMod 16` "8"-class is always in
its kernel). So H6 targets the ℤ/16 GRADE, and this module builds the honest **tied** carrier for it:

`GMTiedStr s := { t2, cert (= PinPlusCertK, reused), q : Z4Quadratic (Fin rank), grade16 : ZMod 16,
  hcoh : reduce16to8 grade16 = q.brown,   -- the mod-8 part is the COMPUTED surface Brown invariant (§9.1)
  htie : reduce16to2 grade16 = swTotalNe s t2 }`   -- the odd bit's parity tied to w₁⁴ (kills the ℝP⁴ grade-0 witness)

The mod-8 part of `grade16` is COMPUTED from the enhancement (`hcoh`); the **odd bit** is the disclosed
content the H6 Smith-LES / H8 Rokhlin input pins (`η(σ)=0 ⟹ bounds`). `abkGMTied16 := grade16 : →+ ZMod 16`.
`ker = ⊥` is H6-b/H8 (given the Smith-LES toolkit + the Rokhlin ABK-completeness Prop). Kernel-pure.
-/

open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.TangentialDataBordism SKEFTHawking.BordismTheory
open SKEFTHawking.PinPlusFaithfulData SKEFTHawking.PinPlusTiedData
open SKEFTHawking.GuillouMarin

namespace SKEFTHawking.PinPlusGMTiedData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}

/-- **A tied Guillou–Marin structure on `s`**: the Hausdorff witness, the `w₂`-certificate, a
characteristic-surface enhancement `q`, and a `ZMod 16` grade whose **mod-8 part is the computed surface
Brown invariant** (`hcoh`) and whose **parity is tied to `w₁⁴`** (`htie`, killing the `ℝP⁴` grade-0
witness). The odd bit of `grade16` is the disclosed H6/H8 content. -/
structure GMTiedStr (I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))) [I.Boundaryless]
    (s : SingularManifold PUnit k I) : Type where
  /-- The carrier is Hausdorff — witnessed. -/
  t2 : T2Space s.M
  /-- The `w₂ = 0` admissibility certificate. -/
  cert : PinPlusCertK I s
  /-- The rank of the characteristic surface's `H₁(·;ℤ/2)`. -/
  rank : ℕ
  /-- The `ZMod 4`-quadratic enhancement. -/
  q : Z4Quadratic (Fin rank)
  /-- The `ZMod 16` Pin⁺ grade. -/
  grade16 : ZMod 16
  /-- **The mod-8 part is COMPUTED**: `grade16` reduces mod 8 to the surface Brown invariant `q.brown`. -/
  hcoh : reduce16to8 grade16 = q.brown
  /-- **The parity tie**: `grade16` reduces mod 2 to `w₁⁴` (kills the `ℝP⁴` grade-0 witness). -/
  htie : reduce16to2 grade16 = swTotalNe s t2

variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]

/-- **The tied Guillou–Marin tangential datum** — `Mfd s := GMTiedStr I s`, `Bor` records `grade16`-equality
(the ℤ/16 grade), the mod-8 part computed from `q`. -/
noncomputable def pinPlusGMTiedData (I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2))))
    [I.Boundaryless] : TangentialData PUnit k I where
  Mfd := fun s => GMTiedStr I s
  Bor := fun _ σ τ => PLift (σ.grade16 = τ.grade16)
  emptyStr :=
    { t2 := ⟨fun x => x.elim⟩
      cert := pinPlusCertK_empty
      rank := 0
      q := stdQuadratic 0
      grade16 := 0
      hcoh := by rw [map_zero, brown_stdQuadratic, Nat.cast_zero]
      htie := by rw [map_zero, swTotalNe_of_isEmpty] }
  sumStr := fun {s t} σ τ =>
    { t2 := t2_sum σ.t2 τ.t2
      cert := PinPlusCertK.sum σ.cert τ.cert
      rank := σ.rank + τ.rank
      q := (orthSum σ.q τ.q).reindex finSumFinEquiv
      grade16 := σ.grade16 + τ.grade16
      hcoh := by rw [map_add, σ.hcoh, τ.hcoh, reindex_brown, brown_orthSum]
      htie := by rw [map_add, σ.htie, τ.htie]; exact swTotalNe_sum σ.t2 τ.t2 }
  cylBor := fun _ => ⟨rfl⟩
  addBor := fun h₁ h₂ => ⟨congrArg₂ (· + ·) h₁.down h₂.down⟩
  symmBor := fun h => ⟨h.down.symm⟩
  commBor := fun σ τ => ⟨add_comm _ _⟩
  assocBor := fun σ τ ρ => ⟨add_assoc _ _ _⟩
  unitBor := fun σ => ⟨add_zero _⟩
  revStr := fun σ =>
    { t2 := σ.t2
      cert := σ.cert
      rank := σ.rank
      q := neg σ.q
      grade16 := -σ.grade16
      hcoh := by rw [map_neg, σ.hcoh, brown_neg]
      htie := by rw [map_neg, σ.htie, CharTwo.neg_eq] }
  revBor := fun h => ⟨congrArg Neg.neg h.down⟩
  negBor := fun σ => ⟨neg_add_cancel _⟩

/-- **The tied Guillou–Marin ℤ/16 grade** — the bordism-invariant additive `→+ ZMod 16`, with the mod-8
part computed from the enhancement (`hcoh`). Well-defined since `Bor` records `grade16`-equality. -/
def abkGMTied16 : DataBordismGrp (pinPlusGMTiedData (E := E) (k := k) I) →+ ZMod 16 where
  toFun := Quot.lift (fun p => p.2.grade16)
    (fun _p _q h => by obtain ⟨_, ⟨str⟩⟩ := h; exact str.down)
  map_zero' := rfl
  map_add' := by
    intro x y
    induction x using Quot.ind with | _ p =>
    induction y using Quot.ind with | _ q => rfl

universe u

/-- **Every even ℤ/16 grade is realised** on the (vacuously certified) empty manifold, with the enhancement
`q` chosen so `hcoh` holds (`brown` is surjective) and `htie` vacuous (parity 0 = `w₁⁴(∅)`). -/
theorem abkGMTied16_hits_even (m : ZMod 16) :
    ∃ g : DataBordismGrp (pinPlusGMTiedData (E := E) (k := k) I),
      abkGMTied16 (E := E) (k := k) (I := I) g = 2 * m := by
  obtain ⟨j, hj⟩ := brown_stdQuadratic_surjective (reduce16to8 (2 * m))
  refine ⟨DataBordismGrp.mk _ ⟨emptySM,
    { t2 := ⟨fun x => x.elim⟩, cert := pinPlusCertK_empty, rank := j, q := stdQuadratic j,
      grade16 := 2 * m, hcoh := hj.symm, htie := ?_ }⟩, rfl⟩
  rw [swTotalNe_of_isEmpty]
  show reduce16to2 (2 * m) = 0
  rw [map_mul, show (reduce16to2 2 : ZMod 2) = 0 from by decide, zero_mul]

/-- The even subgroup is in the tied GM grade's range. -/
theorem even_mem_abkGMTied16_range (m : ZMod 16) :
    2 * m ∈ (abkGMTied16 (E := E) (k := k) (I := I)).range := abkGMTied16_hits_even m

/-- **One odd witness closes the range**: if any class has an odd `grade16`, `abkGMTied16` is surjective
onto `ZMod 16` (the odds are a single coset of the evens, which are realised on `∅`). -/
theorem abkGMTied16_range_top_of_odd
    (h : ∃ g : DataBordismGrp.{u} (pinPlusGMTiedData (E := E) (k := k) I),
      reduce16to2 (abkGMTied16 g) = 1) :
    ((abkGMTied16 (E := E) (k := k) (I := I)) :
      DataBordismGrp.{u} (pinPlusGMTiedData (E := E) (k := k) I) →+ ZMod 16).range = ⊤ := by
  obtain ⟨g₀, hodd⟩ := h
  rw [AddSubgroup.eq_top_iff']
  intro x
  rcases (by decide : ∀ p : ZMod 2, p = 0 ∨ p = 1) (reduce16to2 x) with hx | hx
  · obtain ⟨k', hk⟩ : ∃ k' : ZMod 16, x = 2 * k' := by revert hx; revert x; decide
    exact hk ▸ even_mem_abkGMTied16_range k'
  · obtain ⟨k', hk⟩ : ∃ k' : ZMod 16, x - abkGMTied16 g₀ = 2 * k' := by
      have hdiff : reduce16to2 (x - abkGMTied16 g₀) = 0 := by rw [map_sub, hx, hodd, sub_self]
      revert hdiff; generalize x - abkGMTied16 g₀ = y; revert y; decide
    obtain ⟨gk, hgk⟩ := abkGMTied16_hits_even (E := E) (k := k) (I := I) k'
    refine AddMonoidHom.mem_range.mpr ⟨g₀ + gk, ?_⟩
    rw [map_add, hgk, ← hk, add_comm, sub_add_cancel]

end SKEFTHawking.PinPlusGMTiedData
