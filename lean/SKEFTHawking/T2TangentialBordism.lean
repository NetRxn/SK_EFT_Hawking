/-
# Phase 5q.H (N1 repair) — the Hausdorff-refined structured bordism substrate

**The repaired carrier.** `NonHausdorffBordismCollapse.lean` proves the T2-less `Bordism` relation
degenerates (grade-0 collapse through the bug-eyed cylinder), so the phase's completeness node
`hbound` was vacuous AS STATED. This module builds the repair:

* `T2TangentialData` — a `TangentialData` whose structures certify Hausdorff-ness of their carrier
  (`t2Str`; the tied GM structures already carry this as `GMTiedStr.t2`).
* `IsT2DataBordant` — the structured cobordism relation **with `T2Space W` required** on the
  bordism manifold. Compact + charted-on-`E⁵` + T2 ⟹ `W` is a genuine (metrizable) topological
  bordism manifold, so the relation is honest bordism; the bug-eyed collapse is excluded
  (`tripleBordism_not_t2`).
* `T2DataBordismGrp` — the bordism group of the refined relation; all group-law bordisms
  (cylinders, disjoint unions, doublings) have T2 total spaces when the pieces do, so the
  `AddCommGroup` structure replays verbatim.
* `pinPlusGMTiedT2Data` / `abkGMTied16T2` — the tied Guillou–Marin carrier on the refined
  relation, with the ℤ/16 grade and its UNCONDITIONAL surjectivity (the ℝP⁴ odd generator and the
  even empty-manifold realizations transport verbatim).
* `omega4PinPlusGMTiedT2_equiv_zmod16_of_grade0_bounds` — **the RESTATED keystone door**: the
  genuine geometric completeness node of the phase is now
  `hboundT2 : ∀ x : T2DataBordismGrp (pinPlusGMTiedT2Data (k := 0) (𝓡 4)), abkGMTied16T2 x = 0 → x = 0`
  — grade-0 tied classes bound through HAUSDORFF bordisms. This is the honest `[W,∂W]`-completeness
  content (KT §5 / Thom-detection), NOT dischargeable by the non-Hausdorff exploit.

⚠ Smoothness caveat for the eventual discharge (record, not proven here): at `k = 0` the honest
relation is *topological* bordism, where `Ω₄^{Pin⁺,TOP} ≠ ℤ/16` (Kirby–Siebenmann phenomena — the
E₈-manifold carries a grade-0 tied structure but does not bound topologically). The genuine ℤ/16
target needs the smooth (`k ≥ 1`) instantiation of this carrier; the tied witness tower currently
realizes ℝP⁴ at `k = 0` only. Both the T2 field (this module) and the smoothness lift are needed
for literature-grade fidelity — flagged for the lead/operator.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no sorry/axiom/native_decide/maxHeartbeats.
-/
import Mathlib
import SKEFTHawking.TangentialDataBordism
import SKEFTHawking.PinPlusGMTiedData
import SKEFTHawking.PinPlusGMWitness

namespace SKEFTHawking.T2TangentialBordism

open scoped Manifold
open SKEFTHawking.TangentialDataBordism SKEFTHawking.BordismTheory

/-! ## §1. Hausdorff-certified tangential data and the refined relation -/

/-- A tangential-structure datum whose structures certify that their carrier manifold is
Hausdorff. (The tied Pin⁺/GM structures already carry this: `GMTiedStr.t2`.) -/
structure T2TangentialData.{u, v} (X : Type*) [TopologicalSpace X] (k : WithTop ℕ∞)
    {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    extends TangentialData.{u, v} X k I where
  /-- Every structured carrier is Hausdorff. -/
  t2Str : ∀ {s : SingularManifold.{u} X k I}, Mfd s → T2Space s.M

variable {X : Type*} [TopologicalSpace X] {k : WithTop ℕ∞}
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- **The Hausdorff-refined structured cobordism relation**: as `IsDataBordant`, but the bordism
manifold `W` must be Hausdorff. Compact + T2 + charted ⟹ `W` is a genuine bordism manifold; the
non-Hausdorff collapse (`NonHausdorffBordismCollapse`) is excluded. -/
def IsT2DataBordant.{u, v} (ξ : T2TangentialData.{u, v} X k I)
    (p q : StrMfd ξ.toTangentialData) : Prop :=
  ∃ b : Bordism.{u} (I.prod (𝓡∂ 1)) p.1 q.1, T2Space b.W ∧ Nonempty (ξ.Bor b p.2 q.2)

/-- The Hausdorff-refined structured bordism group. -/
def T2DataBordismGrp.{u, v} (ξ : T2TangentialData.{u, v} X k I) : Type _ :=
  Quot (IsT2DataBordant ξ)

/-- The class of a structured manifold in the refined group. -/
def T2DataBordismGrp.mk.{u, v} (ξ : T2TangentialData.{u, v} X k I) (p : StrMfd ξ.toTangentialData) :
    T2DataBordismGrp ξ :=
  Quot.mk _ p

theorem T2DataBordismGrp.mk_eq_of_bordant.{u, v} (ξ : T2TangentialData.{u, v} X k I)
    {p q : StrMfd ξ.toTangentialData} (h : IsT2DataBordant ξ p q) :
    T2DataBordismGrp.mk ξ p = T2DataBordismGrp.mk ξ q :=
  Quot.sound h

/-! ## §2. The group structure — every group-law bordism has a T2 total space -/

/-- Disjoint union on refined classes (the congruence bordisms are cylinders and sums of T2
spaces, hence T2). -/
noncomputable def T2DataBordismGrp.add.{u, v} (ξ : T2TangentialData.{u, v} X k I)
    (x y : T2DataBordismGrp ξ) : T2DataBordismGrp ξ :=
  Quot.lift₂ (fun p q => T2DataBordismGrp.mk ξ ⟨p.1.sum q.1, ξ.sumStr p.2 q.2⟩)
    (fun p _q _q' h => by
      obtain ⟨b, hT2, ⟨str⟩⟩ := h
      refine mk_eq_of_bordant ξ ⟨Bordism.add (reflCylinder p.1) b, ?_,
        ⟨ξ.addBor (ξ.cylBor p.2) str⟩⟩
      haveI := ξ.t2Str p.2
      haveI : T2Space b.W := hT2
      exact inferInstanceAs (T2Space ((p.1.M × Set.Icc (0 : ℝ) 1) ⊕ b.W)))
    (fun _p _p' q h => by
      obtain ⟨b, hT2, ⟨str⟩⟩ := h
      refine mk_eq_of_bordant ξ ⟨Bordism.add b (reflCylinder q.1), ?_,
        ⟨ξ.addBor str (ξ.cylBor q.2)⟩⟩
      haveI := ξ.t2Str q.2
      haveI : T2Space b.W := hT2
      exact inferInstanceAs (T2Space (b.W ⊕ (q.1.M × Set.Icc (0 : ℝ) 1))))
    x y

@[simp] theorem T2DataBordismGrp.add_mk.{u, v} (ξ : T2TangentialData.{u, v} X k I)
    (p q : StrMfd ξ.toTangentialData) :
    T2DataBordismGrp.add ξ (T2DataBordismGrp.mk ξ p) (T2DataBordismGrp.mk ξ q) =
      T2DataBordismGrp.mk ξ ⟨p.1.sum q.1, ξ.sumStr p.2 q.2⟩ :=
  rfl

theorem T2DataBordismGrp.add_comm.{u, v} (ξ : T2TangentialData.{u, v} X k I)
    (x y : T2DataBordismGrp ξ) : add ξ x y = add ξ y x := by
  induction x using Quot.ind with | _ p =>
  induction y using Quot.ind with | _ q =>
  refine mk_eq_of_bordant ξ
    ⟨mapCylinder (Diffeomorph.sumComm I p.1.M k q.1.M)
      (by funext z; rcases z with z | z <;> rfl), ?_, ⟨ξ.commBor p.2 q.2⟩⟩
  haveI := ξ.t2Str p.2
  haveI := ξ.t2Str q.2
  exact inferInstanceAs (T2Space ((p.1.M ⊕ q.1.M) × Set.Icc (0 : ℝ) 1))

theorem T2DataBordismGrp.add_assoc.{u, v} (ξ : T2TangentialData.{u, v} X k I)
    (x y z : T2DataBordismGrp ξ) : add ξ (add ξ x y) z = add ξ x (add ξ y z) := by
  induction x using Quot.ind with | _ p =>
  induction y using Quot.ind with | _ q =>
  induction z using Quot.ind with | _ r =>
  refine mk_eq_of_bordant ξ
    ⟨mapCylinder (Diffeomorph.sumAssoc I p.1.M k q.1.M r.1.M)
      (by funext w; rcases w with (w | w) | w <;> rfl), ?_, ⟨ξ.assocBor p.2 q.2 r.2⟩⟩
  haveI := ξ.t2Str p.2
  haveI := ξ.t2Str q.2
  haveI := ξ.t2Str r.2
  exact inferInstanceAs (T2Space (((p.1.M ⊕ q.1.M) ⊕ r.1.M) × Set.Icc (0 : ℝ) 1))

/-- The zero class: the empty manifold (vacuously Hausdorff). -/
noncomputable def T2DataBordismGrp.zero.{u, v} (ξ : T2TangentialData.{u, v} X k I) :
    T2DataBordismGrp ξ :=
  T2DataBordismGrp.mk ξ ⟨emptySM, ξ.emptyStr⟩

theorem T2DataBordismGrp.add_zero.{u, v} (ξ : T2TangentialData.{u, v} X k I)
    (x : T2DataBordismGrp ξ) : add ξ x (zero ξ) = x := by
  induction x using Quot.ind with | _ p =>
  refine mk_eq_of_bordant ξ
    ⟨mapCylinder (Diffeomorph.sumEmpty I p.1.M k (M' := emptySM.M))
      (by funext z; cases z with | inl m => rfl | inr e => exact (IsEmpty.false e).elim),
     ?_, ⟨ξ.unitBor p.2⟩⟩
  haveI := ξ.t2Str p.2
  haveI : T2Space (emptySM (X := X) (k := k) (I := I)).M := ⟨fun x => isEmptyElim x⟩
  exact inferInstanceAs (T2Space ((p.1.M ⊕ emptySM.M) × Set.Icc (0 : ℝ) 1))

theorem T2DataBordismGrp.zero_add.{u, v} (ξ : T2TangentialData.{u, v} X k I)
    (x : T2DataBordismGrp ξ) : add ξ (zero ξ) x = x := by
  rw [T2DataBordismGrp.add_comm ξ]; exact add_zero ξ x

/-- Negation = structure reversal (the same `W`, which is T2 when the witness's was). -/
noncomputable def T2DataBordismGrp.neg.{u, v} (ξ : T2TangentialData.{u, v} X k I)
    (x : T2DataBordismGrp ξ) : T2DataBordismGrp ξ :=
  Quot.lift (fun p => T2DataBordismGrp.mk ξ ⟨p.1, ξ.revStr p.2⟩)
    (fun _p _q h => by
      obtain ⟨b, hT2, ⟨str⟩⟩ := h
      exact mk_eq_of_bordant ξ ⟨b, hT2, ⟨ξ.revBor str⟩⟩) x

@[simp] theorem T2DataBordismGrp.neg_mk.{u, v} (ξ : T2TangentialData.{u, v} X k I)
    (p : StrMfd ξ.toTangentialData) :
    T2DataBordismGrp.neg ξ (T2DataBordismGrp.mk ξ p)
      = T2DataBordismGrp.mk ξ ⟨p.1, ξ.revStr p.2⟩ :=
  rfl

noncomputable instance (ξ : T2TangentialData X k I) : Zero (T2DataBordismGrp ξ) :=
  ⟨T2DataBordismGrp.zero ξ⟩
noncomputable instance (ξ : T2TangentialData X k I) : Add (T2DataBordismGrp ξ) :=
  ⟨T2DataBordismGrp.add ξ⟩
noncomputable instance (ξ : T2TangentialData X k I) : Neg (T2DataBordismGrp ξ) :=
  ⟨T2DataBordismGrp.neg ξ⟩

/-- **The Hausdorff-refined structured bordism group is an additive commutative group** — every
group-law bordism (cylinder, disjoint union, doubling) has a T2 total space when the structured
pieces do, so the whole `DataBordismGrp` group structure replays on the honest relation. -/
noncomputable instance (ξ : T2TangentialData X k I) : AddCommGroup (T2DataBordismGrp ξ) where
  add := (· + ·)
  zero := 0
  neg := (- ·)
  add_assoc := T2DataBordismGrp.add_assoc ξ
  zero_add := T2DataBordismGrp.zero_add ξ
  add_zero := T2DataBordismGrp.add_zero ξ
  add_comm := T2DataBordismGrp.add_comm ξ
  neg_add_cancel := fun x => by
    induction x using Quot.ind with | _ p =>
    refine T2DataBordismGrp.mk_eq_of_bordant ξ ⟨doublingBordism p.1, ?_, ⟨ξ.negBor p.2⟩⟩
    haveI := ξ.t2Str p.2
    exact inferInstanceAs (T2Space (p.1.M × Set.Icc (0 : ℝ) 1))
  nsmul := nsmulRec
  nsmul_zero := fun _ => rfl
  nsmul_succ := fun _ _ => rfl
  zsmul := zsmulRec
  zsmul_zero' := fun _ => rfl
  zsmul_succ' := fun _ _ => rfl
  zsmul_neg' := fun _ _ => rfl

end SKEFTHawking.T2TangentialBordism

/-! ## §3. The tied Guillou–Marin carrier on the HONEST relation -/

namespace SKEFTHawking.PinPlusGMTiedT2

open scoped Manifold
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.TangentialDataBordism SKEFTHawking.BordismTheory
open SKEFTHawking.PinPlusFaithfulData SKEFTHawking.PinPlusTiedData
open SKEFTHawking.GuillouMarin SKEFTHawking.PinPlusGMTiedData
open SKEFTHawking.T2TangentialBordism SKEFTHawking.PinPlusGMWitness

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]

/-- **The tied Guillou–Marin datum, Hausdorff-certified** — `pinPlusGMTiedData` with the
`GMTiedStr.t2` field surfaced as the `t2Str` certificate. -/
noncomputable def pinPlusGMTiedT2Data (I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2))))
    [I.Boundaryless] : T2TangentialData PUnit k I where
  toTangentialData := pinPlusGMTiedData I
  t2Str := fun σ => σ.t2

/-- **The tied ℤ/16 grade on the honest carrier** — the bordism-invariant `→+ ZMod 16` (the
refined relation still records grade equality along its `Bor` witnesses). -/
def abkGMTied16T2 :
    T2DataBordismGrp (pinPlusGMTiedT2Data (E := E) (k := k) I) →+ ZMod 16 where
  toFun := Quot.lift (fun p => p.2.grade16)
    (fun _p _q h => by obtain ⟨_, _, ⟨str⟩⟩ := h; exact str.down)
  map_zero' := rfl
  map_add' := by
    intro x y
    induction x using Quot.ind with | _ p =>
    induction y using Quot.ind with | _ q => rfl

/-- Every even grade is realised on the (vacuously Hausdorff-bordant) empty manifold. -/
theorem abkGMTied16T2_hits_even (m : ZMod 16) :
    ∃ g : T2DataBordismGrp (pinPlusGMTiedT2Data (E := E) (k := k) I),
      abkGMTied16T2 (E := E) (k := k) (I := I) g = 2 * m := by
  obtain ⟨j, hj⟩ := brown_stdQuadratic_surjective (reduce16to8 (2 * m))
  refine ⟨T2DataBordismGrp.mk _ ⟨emptySM,
    { t2 := ⟨fun x => x.elim⟩, cert := pinPlusCertK_empty, rank := j, q := stdQuadratic j,
      grade16 := 2 * m, hcoh := hj.symm, htie := ?_ }⟩, rfl⟩
  rw [swTotalNe_of_isEmpty]
  show reduce16to2 (2 * m) = 0
  rw [map_mul, show (reduce16to2 2 : ZMod 2) = 0 from by decide, zero_mul]

universe u

/-- One odd witness closes the range (verbatim transport of the coset argument). -/
theorem abkGMTied16T2_range_top_of_odd
    (h : ∃ g : T2DataBordismGrp.{u} (pinPlusGMTiedT2Data (E := E) (k := k) I),
      reduce16to2 (abkGMTied16T2 g) = 1) :
    ((abkGMTied16T2 (E := E) (k := k) (I := I)) :
      T2DataBordismGrp.{u} (pinPlusGMTiedT2Data (E := E) (k := k) I) →+ ZMod 16).range = ⊤ := by
  obtain ⟨g₀, hodd⟩ := h
  rw [AddSubgroup.eq_top_iff']
  intro x
  rcases (by decide : ∀ p : ZMod 2, p = 0 ∨ p = 1) (reduce16to2 x) with hx | hx
  · obtain ⟨k', hk⟩ : ∃ k' : ZMod 16, x = 2 * k' := by revert hx; revert x; decide
    obtain ⟨g, hg⟩ := abkGMTied16T2_hits_even (E := E) (k := k) (I := I) k'
    exact hk ▸ AddMonoidHom.mem_range.mpr ⟨g, hg⟩
  · obtain ⟨k', hk⟩ : ∃ k' : ZMod 16, x - abkGMTied16T2 g₀ = 2 * k' := by
      have hdiff : reduce16to2 (x - abkGMTied16T2 g₀) = 0 := by rw [map_sub, hx, hodd, sub_self]
      revert hdiff; generalize x - abkGMTied16T2 g₀ = y; revert y; decide
    obtain ⟨gk, hgk⟩ := abkGMTied16T2_hits_even (E := E) (k := k) (I := I) k'
    refine AddMonoidHom.mem_range.mpr ⟨g₀ + gk, ?_⟩
    rw [map_add, hgk, ← hk, add_comm, sub_add_cancel]

/-- The ℝP⁴ class on the honest tied carrier (grade `1` — the odd order-16 generator). -/
noncomputable def rp4GMTiedT2Class :
    T2DataBordismGrp (pinPlusGMTiedT2Data (k := 0) (𝓡 4)) :=
  T2DataBordismGrp.mk _ ⟨SKEFTHawking.RP4Witness.rp4SM, rp4GMTiedStr⟩

theorem abkGMTied16T2_rp4 :
    abkGMTied16T2 (k := 0) (I := 𝓡 4) rp4GMTiedT2Class = 1 := rfl

theorem abkGMTied16T2_rp4_odd :
    reduce16to2 (abkGMTied16T2 (k := 0) (I := 𝓡 4) rp4GMTiedT2Class) = 1 := by
  rw [abkGMTied16T2_rp4]; decide

/-- **The tied grade is SURJECTIVE on the honest carrier** — the ℝP⁴ odd generator + the even
empty realizations, exactly as on the degenerate carrier (surjectivity never needed the collapse). -/
theorem abkGMTied16T2_surjective :
    Function.Surjective (abkGMTied16T2 (k := 0) (I := 𝓡 4)) :=
  AddMonoidHom.range_eq_top.mp
    (abkGMTied16T2_range_top_of_odd ⟨rp4GMTiedT2Class, abkGMTied16T2_rp4_odd⟩)

/-- **THE RESTATED KEYSTONE DOOR (the phase's genuine completeness node).** On the
Hausdorff-refined tied GM carrier, `Ω₄^{Pin⁺} ≅ ℤ/16` follows from the single geometric Prop

  `hboundT2 : ∀ x, abkGMTied16T2 x = 0 → x = 0`

— every grade-`0` tied class bounds through a HAUSDORFF (i.e. genuine) bordism. Unlike the
superseded T2-less `hbound` (vacuously true — `NonHausdorffBordismCollapse`), this is the honest
KT §5 / Thom-detection completeness content: the `[W,∂W]` + surgery geometric substrate.
(Smoothness caveat in the module docstring: the ℤ/16 fidelity target ultimately needs the smooth
instantiation; at `k = 0` the honest topological group differs by Kirby–Siebenmann classes.) -/
theorem omega4PinPlusGMTiedT2_equiv_zmod16_of_grade0_bounds
    (hboundT2 : ∀ x : T2DataBordismGrp.{u} (pinPlusGMTiedT2Data (k := 0) (𝓡 4)),
        abkGMTied16T2 (k := 0) (I := 𝓡 4) x = 0 → x = 0) :
    Nonempty (T2DataBordismGrp.{u} (pinPlusGMTiedT2Data (k := 0) (𝓡 4)) ≃+ ZMod 16) :=
  ⟨AddEquiv.ofBijective (abkGMTied16T2 (k := 0) (I := 𝓡 4))
    ⟨(injective_iff_map_eq_zero _).mpr hboundT2, abkGMTied16T2_surjective⟩⟩

/-- **The refined carrier surjects onto the T2-less one** (the refined relation is finer), so the
repair loses nothing that was honestly there: every degenerate-carrier class lifts. -/
noncomputable def toDataBordismGrp :
    T2DataBordismGrp (pinPlusGMTiedT2Data (E := E) (k := k) I)
      →+ DataBordismGrp (pinPlusGMTiedData (E := E) (k := k) I) where
  toFun := Quot.lift (fun p => DataBordismGrp.mk (pinPlusGMTiedData (E := E) (k := k) I) p)
    (fun _p _q h => by
      obtain ⟨b, _, hstr⟩ := h
      exact DataBordismGrp.mk_eq_of_bordant _ ⟨b, hstr⟩)
  map_zero' := rfl
  map_add' := by
    intro x y
    induction x using Quot.ind with | _ p =>
    induction y using Quot.ind with | _ q => rfl

theorem toDataBordismGrp_surjective :
    Function.Surjective (toDataBordismGrp (E := E) (k := k) (I := I)) := by
  intro x
  induction x using Quot.ind with | _ p =>
  exact ⟨T2DataBordismGrp.mk _ p, rfl⟩

end SKEFTHawking.PinPlusGMTiedT2
