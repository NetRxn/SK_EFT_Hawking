import Mathlib
import SKEFTHawking.BrownInvariant
import SKEFTHawking.PinPlusTiedData

/-!
# Phase 5q.H (H3 enhancement algebra) — reindexing a `ZMod 4`-quadratic form along a domain equivalence

The first 5q.H enhancement-algebra brick toward the Guillou–Marin carrier `pinPlusGMData`. The carrier's
`sumStr` composes two characteristic-surface enhancements by `orthSum` (over `Fin m ⊕ Fin n`) but the
carrier fixes the enhancement domain to a single `Fin (m+n)`; `Z4Quadratic.reindex` transports the form
along `Fin m ⊕ Fin n ≃ Fin (m+n)`, and `reindex_brown` shows the Brown invariant is unchanged (the Gauss
sum is invariant under a domain bijection, and `Fintype.card` is preserved by the equivalence).

Kernel-pure `{propext, Classical.choice, Quot.sound}` — pure `Z4Quadratic` algebra over `BrownInvariant`.
-/

open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic

namespace SKEFTHawking.Brown.Z4Quadratic

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **Reindexing a `ZMod 4`-quadratic form along a domain equivalence** `e : ι ≃ κ`. The form on
`κ → ZMod 2` is `x ↦ Q.q (x ∘ e)`; all axioms transport, since `x ↦ x ∘ e` is a bijection of
`κ → ZMod 2` with `ι → ZMod 2`. -/
def reindex (Q : Z4Quadratic ι) (e : ι ≃ κ) : Z4Quadratic κ where
  q := fun x => Q.q (fun i => x (e i))
  B := fun x y => Q.B (fun i => x (e i)) (fun i => y (e i))
  refine' := fun x y => Q.refine' _ _
  B_add_left := fun x y z => Q.B_add_left _ _ _
  B_symm := fun x y => Q.B_symm _ _
  nondeg := fun x hx => by
    have h0 : (fun i => x (e i)) = 0 := Q.nondeg _ (fun y => by
      have := hx (fun k => y (e.symm k))
      simpa [Equiv.apply_symm_apply] using this)
    funext k
    have := congrFun h0 (e.symm k)
    simpa [Equiv.apply_symm_apply] using this

/-- The Gauss sum is invariant under reindexing (a domain bijection permutes the sum). -/
lemma gaussSum4_reindex (Q : Z4Quadratic ι) (e : ι ≃ κ) :
    gaussSum4 (Q.reindex e).q = gaussSum4 Q.q :=
  (Fintype.sum_equiv (Equiv.arrowCongr e (Equiv.refl (ZMod 2)))
    (fun x' => zeta4 (Q.q x')) (fun x => zeta4 ((Q.reindex e).q x))
    (fun x' => by simp [reindex, Equiv.arrowCongr_apply, Equiv.symm_apply_apply])).symm

/-- The Brown-phase unit is invariant under reindexing. -/
lemma brownUnit_reindex (Q : Z4Quadratic ι) (e : ι ≃ κ) :
    (Q.reindex e).brownUnit = Q.brownUnit := by
  have hcard : Fintype.card κ = Fintype.card ι := (Fintype.card_congr e).symm
  have h := (Q.reindex e).gaussSum4_eq_brownUnit
  rw [gaussSum4_reindex, Q.gaussSum4_eq_brownUnit, hcard] at h
  exact (zeta4_mul_pow_right_inj h).symm

/-- **The Brown invariant is invariant under reindexing** — the enhancement's ABK value depends only on
the isometry class of the form, not on the chosen basis/index of `H₁(Σ;ℤ/2)`. -/
@[simp] lemma reindex_brown (Q : Z4Quadratic ι) (e : ι ≃ κ) :
    (Q.reindex e).brown = Q.brown := by
  have hcard : Fintype.card κ = Fintype.card ι := (Fintype.card_congr e).symm
  simp only [brown, brownUnit_reindex, hcard]

/-! ## Negation of a `ZMod 4`-quadratic form (structure reversal `q ↦ -q`, `β ↦ -β`)

The characteristic-surface enhancement of the reversed Pin⁻ structure is `-q`; its Brown invariant
negates (`β(-q) = -β(q)`, the ABK reflection). Needed by the GM carrier's `revStr`/`negBor`. -/

/-- `-embed2 b = embed2 b` in `ZMod 4` (the image `{0,2}` is 2-torsion). -/
lemma neg_embed2 (b : ZMod 2) : -(embed2 b) = embed2 b := by revert b; decide

/-- **Negation of a `ZMod 4`-quadratic form**: `q ↦ -q`, keeping the same polar form `B`. Valid since
`-embed2 = embed2`, so `(-q)` still refines `B`. -/
def neg (Q : Z4Quadratic ι) : Z4Quadratic ι where
  q := fun x => -(Q.q x)
  B := Q.B
  refine' := fun x y => by
    show -(Q.q (x + y)) = -(Q.q x) + -(Q.q y) + embed2 (Q.B x y)
    rw [Q.refine', neg_add, neg_add, neg_embed2]
  B_add_left := Q.B_add_left
  B_symm := Q.B_symm
  nondeg := Q.nondeg

/-- `zeta4` powers: `zeta4 a ^ n = zeta4 (n · a)` (the `ζ₄` character is a monoid hom). -/
lemma zeta4_pow (a : ZMod 4) (n : ℕ) : zeta4 a ^ n = zeta4 ((n : ZMod 4) * a) := by
  induction n with
  | zero => simp [zeta4]
  | succ k ih =>
    rw [pow_succ, ih, ← zeta4_add]
    congr 1
    push_cast; ring

/-- The Gauss sum of the negated form is the complex conjugate. -/
lemma gaussSum4_neg (Q : Z4Quadratic ι) : gaussSum4 (neg Q).q = star (gaussSum4 Q.q) := by
  rw [star_gaussSum4]; rfl

/-- `1 - I = ζ₄(3) · (1 + I)` in `ℤ[i]`. -/
lemma one_sub_I_eq : (1 - I) = zeta4 3 * (1 + I) := by decide

/-- The Brown-phase unit of the negated form: `brownUnit(-Q) = -brownUnit(Q) + 3·dim`. -/
lemma brownUnit_neg (Q : Z4Quadratic ι) :
    (neg Q).brownUnit = -Q.brownUnit + 3 * (Fintype.card ι : ZMod 4) := by
  have h := (neg Q).gaussSum4_eq_brownUnit
  rw [gaussSum4_neg, Q.gaussSum4_eq_brownUnit] at h
  -- h : star (zeta4 bU * (1+I)^card) = zeta4 ((neg Q).brownUnit) * (1+I)^card
  have hs1 : star (1 + I : GaussianInt) = 1 - I := by decide
  have hstar : star (zeta4 Q.brownUnit * (1 + I) ^ Fintype.card ι)
      = zeta4 (-Q.brownUnit + 3 * (Fintype.card ι : ZMod 4)) * (1 + I) ^ Fintype.card ι := by
    rw [star_mul', star_pow, star_zeta4, hs1, one_sub_I_eq, mul_pow, zeta4_pow, ← mul_assoc,
      ← zeta4_add]
    congr 2
    ring
  rw [hstar] at h
  exact (zeta4_mul_pow_right_inj h).symm

/-- **The Brown invariant negates under form negation** — `β(-q) = -β(q)`, the ABK reflection
`ABK(σ̄) = -ABK(σ)`. -/
@[simp] lemma brown_neg (Q : Z4Quadratic ι) : (neg Q).brown = - Q.brown := by
  have hc : ((Fintype.card ι : ℕ) : ZMod 4)
      = (ZMod.castHom (by norm_num : (4 : ℕ) ∣ 8) (ZMod 4)) ((Fintype.card ι : ℕ) : ZMod 8) :=
    (map_natCast _ _).symm
  unfold brown
  rw [brownUnit_neg, hc]
  generalize Q.brownUnit = bU
  generalize ((Fintype.card ι : ℕ) : ZMod 8) = d
  revert bU d; decide

end SKEFTHawking.Brown.Z4Quadratic

/-! ## The Guillou–Marin carrier `pinPlusGMData` and the COMPUTED mod-8 grade `abkGM8`

The 5q.H carrier whose grade is **computed from an enhancement** (a genuine Brown/Gauss-sum invariant),
rather than assigned as a free ℤ/16 tag like the faithful carrier's grade. **Honest scope (mirroring the
faithful carrier):** the enhancement `q : Z4Quadratic (Fin rank)` is *carried structure data* — for a
general `s` it is NOT derived from `s.M`'s actual characteristic surface; it is geometrically grounded only
at the ℝP⁴ witness (`PinPlusGMWitness.rp4GMStr`, `q := stdQuadratic 1`), exactly as the faithful carrier's
grade is a free tag whose `[ℝP⁴]` identification is Landmark-level. What is genuine here is that `abkGM8`
is computed **from `q`** through the real `brown` Gauss-sum algebra (with honest additive/reindex/negation
laws), NOT that `q` is computed from `s`. Per roadmap §9.1 the surface package computes the Pin⁺ invariant
only **mod 8** (`doubleBrown q` is even in `ZMod 16`); the odd bit / full `ZMod 16` is assembled at the
Smith-LES level (H6), not carried here. So the carrier grade is `abkGM8 := q.brown : ZMod 8`.

Mirrors `PinPlusTiedData`, but `revStr` negates the enhancement (`q ↦ neg q`, `β ↦ -β`) and `sumStr`
composes by `orthSum` reindexed to `Fin (m+n)`. `Bor := PLift (Brown-equality)` (the §4-H4
invariance-by-structure; inhabitation proven per-construction). Kernel-pure. β-sign: GL/FK.
-/

open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.TangentialDataBordism SKEFTHawking.BordismTheory
open SKEFTHawking.PinPlusFaithfulData SKEFTHawking.PinPlusTiedData

namespace SKEFTHawking.PinPlusGMData

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}

/-- **A Guillou–Marin structure on `s`**: the Hausdorff witness, the `w₂`-admissibility certificate
(the k-generic `PinPlusCertK`, reused from the tied carrier), and a characteristic-surface enhancement
`q` — carried structure data on `Fin rank` (intended as the surface's `H₁(·;ℤ/2)` basis; geometrically
grounded only at the ℝP⁴ witness, not derived from `s` in general). The mod-8 grade is `q.brown`,
computed **from `q`** via the `brown` Gauss-sum algebra. -/
structure GMStr (I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))) [I.Boundaryless]
    (s : SingularManifold PUnit k I) : Type where
  /-- The carrier is Hausdorff — witnessed, not assumed. -/
  t2 : T2Space s.M
  /-- The `w₂ = 0` admissibility certificate (k-generic, reused from the tied carrier). -/
  cert : PinPlusCertK I s
  /-- The rank of the characteristic surface's `H₁(·;ℤ/2)`. -/
  rank : ℕ
  /-- The `ZMod 4`-quadratic enhancement on the surface's `H₁`. -/
  q : Z4Quadratic (Fin rank)

variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]

/-- **The Guillou–Marin tangential datum** — `Mfd s := GMStr I s`, with the grade computed from the
carried enhancement `q`'s Brown value (grounded geometrically at the ℝP⁴ witness; carried data for a
general `s`). `Bor` records Brown-equality (the §4-H4 invariance-by-structure). k-generic (like
`pinPlusTiedData`), so the k = 0 ℝP⁴ witness instantiates it. -/
noncomputable def pinPlusGMData (I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2))))
    [I.Boundaryless] : TangentialData PUnit k I where
  Mfd := fun s => GMStr I s
  Bor := fun _ σ τ => PLift (σ.q.brown = τ.q.brown)
  emptyStr :=
    { t2 := ⟨fun x => x.elim⟩
      cert := pinPlusCertK_empty
      rank := 0
      q := stdQuadratic 0 }
  sumStr := fun {s t} σ τ =>
    { t2 := t2_sum σ.t2 τ.t2
      cert := PinPlusCertK.sum σ.cert τ.cert
      rank := σ.rank + τ.rank
      q := (orthSum σ.q τ.q).reindex finSumFinEquiv }
  cylBor := fun _ => ⟨rfl⟩
  addBor := fun h₁ h₂ => ⟨by simp only [reindex_brown, brown_orthSum]; rw [h₁.down, h₂.down]⟩
  symmBor := fun h => ⟨h.down.symm⟩
  commBor := fun σ τ => ⟨by simp only [reindex_brown, brown_orthSum]; ring⟩
  assocBor := fun σ τ ρ => ⟨by simp only [reindex_brown, brown_orthSum]; ring⟩
  unitBor := fun σ => ⟨by
    simp only [reindex_brown, brown_orthSum, brown_stdQuadratic, Nat.cast_zero, add_zero]⟩
  revStr := fun σ => { σ with q := neg σ.q }
  revBor := fun h => ⟨by simp only [brown_neg]; rw [h.down]⟩
  negBor := fun σ => ⟨by
    simp only [reindex_brown, brown_orthSum, brown_neg, brown_stdQuadratic, Nat.cast_zero,
      neg_add_cancel]⟩

/-- **The computed mod-8 Guillou–Marin grade** — the bordism-invariant additive `→+ ZMod 8`, COMPUTED
from the enhancement's Brown value (not a carried tag). Well-defined since `Bor` records Brown-equality;
additive since `sumStr` is `orthSum` (`brown_orthSum`, reindex-invariant). -/
noncomputable def abkGM8 : DataBordismGrp (pinPlusGMData (E := E) (k := k) I) →+ ZMod 8 where
  toFun := Quot.lift (fun p => p.2.q.brown)
    (fun _p _q h => by obtain ⟨_, ⟨str⟩⟩ := h; exact str.down)
  map_zero' := by show (stdQuadratic 0).brown = 0; rw [brown_stdQuadratic, Nat.cast_zero]
  map_add' := by
    intro x y
    induction x using Quot.ind with | _ p =>
    induction y using Quot.ind with | _ q =>
    show ((orthSum p.2.q q.2.q).reindex finSumFinEquiv).brown = p.2.q.brown + q.2.q.brown
    rw [reindex_brown, brown_orthSum]

/-- **The computed GM grade is surjective onto `ZMod 8`** — every mod-8 Brown value is realised on the
(vacuously certified) empty manifold by a standard enhancement `stdQuadratic g` (`brown` is surjective).
This is the mod-8 fullness (per §9.1 the surface computes only mod 8; the odd bit is H6). -/
theorem abkGM8_surjective : Function.Surjective (abkGM8 (E := E) (k := k) (I := I)) := by
  intro b
  obtain ⟨g, hg⟩ := brown_stdQuadratic_surjective b
  exact ⟨DataBordismGrp.mk _ ⟨emptySM, ⟨⟨fun x => x.elim⟩, pinPlusCertK_empty, g, stdQuadratic g⟩⟩, hg⟩

/-- **Unconditional first isomorphism on the GM carrier**: `DataBordismGrp (pinPlusGMData) ⧸ ker(abkGM8)
≃+ ZMod 8` — the mod-8 quotient, computed-not-carried, no hypothesis. (The full `ZMod 16` with the odd
bit is the H6 Smith-LES target.) -/
noncomputable def dataBordismGM_quotient_abk8_equiv_zmod8 :
    DataBordismGrp (pinPlusGMData (E := E) (k := k) I) ⧸ (abkGM8 (E := E) (k := k) (I := I)).ker
      ≃+ ZMod 8 :=
  QuotientAddGroup.quotientKerEquivOfSurjective abkGM8 abkGM8_surjective

end SKEFTHawking.PinPlusGMData
