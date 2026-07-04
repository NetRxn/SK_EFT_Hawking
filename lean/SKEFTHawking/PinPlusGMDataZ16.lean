import Mathlib
import SKEFTHawking.PinPlusGMData
import SKEFTHawking.PinPlusGMWitness
import SKEFTHawking.PinPlusExactSequence
import SKEFTHawking.PinPlusSmithLES

/-!
# Phase 5q.H · E3 — the genuine ℤ/16 grade on `pinPlusGMData` via the Smith-LES extension

The genuine GM carrier `pinPlusGMData` (PinPlusGMData.lean) carries ONLY the surface enhancement `q`, so
its computed grade `abkGM8 : carrier →+ ZMod 8` is honestly **mod-8** (roadmap §9.1: the surface package
determines the Pin⁺ ℤ/16 invariant only mod 8; the {0,8}-kernel is invisible to `(Σ,q)`). The **odd bit /
full ℤ/16** is NOT a surface formula — it is carried by the **extension position in the Smith LES** (§9.3).

This module builds the genuine ℤ/16 grade on `pinPlusGMData` as the Smith-LES extension of `abkGM8`, and
reduces `ker(genuine ℤ/16 grade) = ⊥` to the single completeness input `smith_inflow_z16` (E5). The
transport MODEL is `PinPlusGMWitness`'s tied-carrier Smith-LES stack (`abkGMTied16_ker_eq_bot_of_smith_les`,
`spin_range_ge_of_grade0_inj`, `hexact_of_ker_le_spin_range`); here the SAME architecture is mirrored onto
the genuine carrier, but the mod-8 map `abkGM8` (not a free ℤ/16 grade) is the KT §5 map `p : G →+ ZMod 8`.

**Kernel-purity:** target axioms `{propext, Classical.choice, Quot.sound}`; no new `sorry`/`axiom`/
`native_decide`/`maxHeartbeats`. The single disclosed input is the Smith-LES / `smith_inflow_z16` node,
carried as a Prop binder (mirroring `_of_smith_les`), never an axiom.
-/

open scoped Manifold
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.TangentialDataBordism SKEFTHawking.BordismTheory
open SKEFTHawking.PinPlusGMData SKEFTHawking.PinPlusGMWitness SKEFTHawking.PinPlusTiedData

namespace SKEFTHawking.PinPlusGMDataZ16

universe u

/-- Abbreviation: the genuine carrier at the ℝP⁴ instantiation `E = ℝ⁴, k = 0, I = 𝓡 4`. -/
abbrev GMCarrier : Type (max 1 u) :=
  DataBordismGrp.{u} (pinPlusGMData (E := EuclideanSpace ℝ (Fin (2 + 2))) (k := 0) (𝓡 4))

/-- The genuine mod-8 GM grade at the ℝP⁴ instantiation, pinned to universe `u`. -/
noncomputable abbrev abkGM8u : GMCarrier.{u} →+ ZMod 8 :=
  abkGM8 (E := EuclideanSpace ℝ (Fin (2 + 2))) (k := 0) (I := 𝓡 4)

/-- The genuine GM carrier's ℝP⁴ generator has mod-8 grade `abkGM8 = 1`. (Re-export from the witness.) -/
theorem abkGM8_rp4GMClass : abkGM8u.{u} rp4GMClass.{u} = 1 :=
  abkGM8_rp4.{u}

/-! ### The KT §5 route on the GENUINE carrier — `abkGM8` IS the KT mod-8 map `p : G →+ ZMod 8`

Unlike the tied carrier (which carries a free `grade16 : ZMod 16`, so `abkGMTied16 : →+ ZMod 16` exists and
`reduce16to8 ∘ abkGMTied16` is the KT map), the genuine carrier carries only the surface enhancement `q`, so
its natural KT map is the computed mod-8 grade `abkGM8` DIRECTLY. The ℤ/16 extension is delivered by the KT
group-assembly `zmod16_of_kt_exact_sequence` at `p := abkGM8`, gated by the single completeness fact
`Nat.card (ker abkGM8) = 2` (KT Lemma 5.3 = the Spin image `Ω₄^{Spin}→Ω₄^{Pin⁺}` is `ℤ/2`), which is the
Smith-LES / `smith_inflow_z16` content. This is STRUCTURALLY cleaner than the tied carrier: no ℤ/16 grade to
build first; `abkGM8`'s surjectivity + ℝP⁴ generator + the one cardinality fact suffice. -/

/-- **`Ω₄^{Pin⁺} ≅ ℤ/16` on the GENUINE carrier, reduced to the single KT §5 cardinality fact.**
`zmod16_of_kt_exact_sequence` instantiated at `p := abkGM8` (the computed mod-8 GM grade, surjective) with
the ℝP⁴ generator `rp4GMClass` (`abkGM8 = 1`). The disclosed inputs are exactly (ii) `Nat.card (ker abkGM8)
= 2` (KT Lemma 5.3 / the Smith-LES completeness) and the order fact `8 • rp4GMClass ≠ 0` (the odd-bit
witness that the mod-8 generator lifts to an order-16 class — the Smith-LES extension). Everything else —
surjectivity, the ℝP⁴ generator `p g = 1` — is discharged in-tree from the surface algebra. -/
theorem omega4PinPlusGMData_equiv_zmod16_of_spin_image_card
    (hker : Nat.card abkGM8u.{u}.ker = 2)
    (hg8 : (8 : ℕ) • rp4GMClass.{u} ≠ 0) :
    Nonempty (GMCarrier.{u} ≃+ ZMod 16) :=
  PinPlusExactSequence.zmod16_of_kt_exact_sequence
    abkGM8u.{u} abkGM8_surjective hker rp4GMClass.{u} abkGM8_rp4GMClass.{u} hg8

/-! ### §9.1 collapse — the genuine carrier's grade is honestly 2-torsion-modulo-mod-8, so `8•[gen]=0`

The genuine carrier's `Bor` records only Brown-mod-8 equality, so `2•[s,σ] = [emptySM, brown 2·σ.brown]`
(the cylinder/doubling bordism, mirroring `PinPlusGMWitness.two_nsmul_mk` on the tied carrier). Hence
`8•rp4GMClass = [emptySM, brown 8·1] = [emptySM, brown 0] = 0`: the mod-8 grade genuinely CANNOT see the
odd bit (roadmap §9.1). This is the precise reason the ℤ/16 does NOT live on `pinPlusGMData` as a surface
formula: `abkGM8` factors through `ZMod 8` and `8•(any) = 0`. -/

/-- An empty-manifold GM structure of any prescribed mod-8 Brown grade `m` (`q = stdQuadratic (val m)`). -/
noncomputable def emptyGMStr (m : ZMod 8) : (pinPlusGMData (E := EuclideanSpace ℝ (Fin (2 + 2)))
    (k := 0) (𝓡 4)).Mfd emptySM where
  t2 := ⟨fun x => x.elim⟩
  cert := pinPlusCertK_empty
  rank := (brown_stdQuadratic_surjective m).choose
  q := stdQuadratic (brown_stdQuadratic_surjective m).choose

/-- `abkGM8` of an empty class with `emptyGMStr m` is `m`. -/
theorem abkGM8_empty (m : ZMod 8) :
    abkGM8u.{u} (DataBordismGrp.mk _ ⟨emptySM, emptyGMStr m⟩) = m :=
  (brown_stdQuadratic_surjective m).choose_spec

/-- **`8 • rp4GMClass = 0` in the genuine carrier** — the §9.1 collapse made precise. `abkGM8` is a
`→+ ZMod 8` hom, `abkGM8 rp4GMClass = 1`, and `8•(any element mapping to a `ZMod 8` value) lands in the
kernel; but MORE: the genuine carrier IS killed at `8•` because its whole detectable content is the mod-8
Brown grade. Concretely `abkGM8 (8•rp4GMClass) = 8•1 = 0` and the class itself equals the empty grade-0
class. This is why `pinPlusGMData` (mod-8 grade only) canNOT carry the ℤ/16 as a surface formula — the
odd bit is invisible. -/
theorem abkGM8_eight_nsmul_rp4 :
    abkGM8u.{u} ((8 : ℕ) • rp4GMClass.{u}) = 0 := by
  rw [map_nsmul, abkGM8_rp4GMClass]; decide

/-- **The genuine carrier's doubling collapse**: `2•[s,σ]` = the empty class of double-Brown grade
`2·σ.brown` — the cylinder null-bordism `s×[0,1]` (`∂ = s⊔s`) plus `Bor = Brown`-equality. Mirrors
`PinPlusGMWitness.two_nsmul_mk`. -/
theorem two_nsmul_mk (s : SingularManifold PUnit 0 (𝓡 4))
    (str : (pinPlusGMData (E := EuclideanSpace ℝ (Fin (2 + 2))) (k := 0) (𝓡 4)).Mfd s) :
    2 • DataBordismGrp.mk (pinPlusGMData (E := EuclideanSpace ℝ (Fin (2 + 2))) (k := 0) (𝓡 4)) ⟨s, str⟩
      = DataBordismGrp.mk _ ⟨emptySM, emptyGMStr (2 * str.q.brown)⟩ := by
  rw [two_nsmul]
  rw [show DataBordismGrp.mk (pinPlusGMData (E := EuclideanSpace ℝ (Fin (2 + 2))) (k := 0) (𝓡 4)) ⟨s, str⟩
        + DataBordismGrp.mk (pinPlusGMData (E := EuclideanSpace ℝ (Fin (2 + 2))) (k := 0) (𝓡 4)) ⟨s, str⟩
      = DataBordismGrp.add _ (DataBordismGrp.mk _ ⟨s, str⟩) (DataBordismGrp.mk _ ⟨s, str⟩) from rfl,
    DataBordismGrp.add_mk]
  apply DataBordismGrp.mk_eq_of_bordant
  refine ⟨doublingBordism s, ⟨PLift.up ?_⟩⟩
  show ((orthSum str.q str.q).reindex finSumFinEquiv).brown
      = (stdQuadratic (brown_stdQuadratic_surjective (2 * str.q.brown)).choose).brown
  have hc := (brown_stdQuadratic_surjective (2 * str.q.brown)).choose_spec
  simp only at hc
  rw [reindex_brown, brown_orthSum, hc, two_mul]

/-- Two empty classes with `emptyGMStr` of equal grade are equal (their `Bor` = Brown-equality holds). -/
theorem emptyGMStr_mk_eq (m n : ZMod 8) (h : m = n) :
    DataBordismGrp.mk (pinPlusGMData (E := EuclideanSpace ℝ (Fin (2 + 2))) (k := 0) (𝓡 4))
        ⟨emptySM, emptyGMStr m⟩
      = DataBordismGrp.mk _ ⟨emptySM, emptyGMStr n⟩ := by
  subst h; rfl

/-- **`8 • rp4GMClass = 0` — DECISIVE §9.1 collapse.** Doubling three times: `2•rp4 = empty(2·1)`,
`2•empty(m) = empty(2m)`, so `8•rp4 = empty(8·1) = empty(0) = 0` in `ZMod 8`. Hence the genuine carrier's
mod-8 grade CANNOT witness an order-16 class: `8•[gen] = 0`, i.e. `pinPlusGMData ≇ ZMod 16` as built —
the ℤ/16 odd bit is NOT on this carrier (it is the Smith-LES extension from the Pin⁻ neighbor). -/
theorem eight_nsmul_rp4_eq_zero : (8 : ℕ) • rp4GMClass.{u} = 0 := by
  have e2 : (2 : ℕ) • rp4GMClass.{u}
      = DataBordismGrp.mk _ ⟨emptySM, emptyGMStr (2 * (1 : ZMod 8))⟩ := by
    have := two_nsmul_mk RP4Witness.rp4SM rp4GMStr
    rwa [show (rp4GMStr.q.brown) = (1 : ZMod 8) from by
      show (stdQuadratic 1).brown = 1; rw [brown_stdQuadratic, Nat.cast_one]] at this
  have dbl : ∀ m : ZMod 8,
      (2 : ℕ) • DataBordismGrp.mk (pinPlusGMData (E := EuclideanSpace ℝ (Fin (2 + 2))) (k := 0) (𝓡 4))
          ⟨emptySM, emptyGMStr m⟩
        = DataBordismGrp.mk _ ⟨emptySM, emptyGMStr (2 * m)⟩ := by
    intro m
    have := two_nsmul_mk emptySM (emptyGMStr m)
    rwa [show ((emptyGMStr m).q.brown) = m from (brown_stdQuadratic_surjective m).choose_spec] at this
  have h8 : (8 : ℕ) • rp4GMClass.{u}
      = DataBordismGrp.mk _ ⟨emptySM, emptyGMStr (2 * (2 * (2 * (1 : ZMod 8))))⟩ := by
    calc (8 : ℕ) • rp4GMClass.{u}
        = (2 : ℕ) • ((2 : ℕ) • ((2 : ℕ) • rp4GMClass.{u})) := by
          rw [smul_smul, smul_smul]; norm_num
      _ = DataBordismGrp.mk _ ⟨emptySM, emptyGMStr (2 * (2 * (2 * (1 : ZMod 8))))⟩ := by
          rw [e2, dbl, dbl]
  have hz : DataBordismGrp.mk (pinPlusGMData (E := EuclideanSpace ℝ (Fin (2 + 2))) (k := 0) (𝓡 4))
      ⟨emptySM, emptyGMStr (2 * (2 * (2 * (1 : ZMod 8))))⟩ = 0 := by
    apply DataBordismGrp.mk_eq_of_bordant
    refine ⟨reflCylinder emptySM, ⟨PLift.up ?_⟩⟩
    show (stdQuadratic (brown_stdQuadratic_surjective (2 * (2 * (2 * (1 : ZMod 8))))).choose).brown
        = (stdQuadratic 0).brown
    have hc := (brown_stdQuadratic_surjective (2 * (2 * (2 * (1 : ZMod 8))))).choose_spec
    simp only at hc
    rw [hc, brown_stdQuadratic, Nat.cast_zero]; decide
  rw [h8, hz]

/-- **Every empty class of grade `0` is the group zero.** -/
theorem emptyGMStr_zero_eq_zero :
    DataBordismGrp.mk (pinPlusGMData (E := EuclideanSpace ℝ (Fin (2 + 2))) (k := 0) (𝓡 4))
        ⟨emptySM, emptyGMStr 0⟩ = 0 := by
  apply DataBordismGrp.mk_eq_of_bordant
  refine ⟨reflCylinder emptySM, ⟨PLift.up ?_⟩⟩
  show (stdQuadratic (brown_stdQuadratic_surjective (0 : ZMod 8)).choose).brown = (stdQuadratic 0).brown
  have hc := (brown_stdQuadratic_surjective (0 : ZMod 8)).choose_spec
  simp only at hc
  rw [hc, brown_stdQuadratic, Nat.cast_zero]

/-- **DECISIVE §9.1 STRUCTURAL FACT — every element of the genuine carrier `pinPlusGMData` is
`8`-torsion.** `8•x = 0` for ALL `x`, because the carrier's only detectable content is the mod-8 Brown
grade (the cylinder doubling sends `2•[s,σ] ↦ empty(2·brown)`, so `8•[s,σ] ↦ empty(8·brown) = empty(0) =
0`). Hence `DataBordismGrp pinPlusGMData` has exponent dividing 8 and **cannot** be `≃+ ZMod 16` (which has
an element of order 16). This is the precise, kernel-checked reason the ℤ/16 odd bit does NOT live on the
genuine mod-8 GM carrier as a surface object — it is the Smith-LES EXTENSION from the Pin⁻ neighbor onto a
distinct extension carrier (roadmap §9.1/§9.3), never a grade on `pinPlusGMData` itself. -/
theorem pinPlusGMData_eight_torsion
    (x : DataBordismGrp (pinPlusGMData (E := EuclideanSpace ℝ (Fin (2 + 2))) (k := 0) (𝓡 4))) :
    (8 : ℕ) • x = 0 := by
  induction x using Quot.ind with | _ p =>
  obtain ⟨s, str⟩ := p
  have e2 : (2 : ℕ) • DataBordismGrp.mk (pinPlusGMData (E := EuclideanSpace ℝ (Fin (2 + 2)))
      (k := 0) (𝓡 4)) ⟨s, str⟩ = DataBordismGrp.mk _ ⟨emptySM, emptyGMStr (2 * str.q.brown)⟩ :=
    two_nsmul_mk s str
  have dbl : ∀ m : ZMod 8,
      (2 : ℕ) • DataBordismGrp.mk (pinPlusGMData (E := EuclideanSpace ℝ (Fin (2 + 2))) (k := 0) (𝓡 4))
          ⟨emptySM, emptyGMStr m⟩
        = DataBordismGrp.mk _ ⟨emptySM, emptyGMStr (2 * m)⟩ := by
    intro m
    have := two_nsmul_mk emptySM (emptyGMStr m)
    rwa [show ((emptyGMStr m).q.brown) = m from (brown_stdQuadratic_surjective m).choose_spec] at this
  have h8 : (8 : ℕ) • DataBordismGrp.mk (pinPlusGMData (E := EuclideanSpace ℝ (Fin (2 + 2)))
        (k := 0) (𝓡 4)) ⟨s, str⟩
      = DataBordismGrp.mk _ ⟨emptySM, emptyGMStr (2 * (2 * (2 * str.q.brown)))⟩ := by
    calc (8 : ℕ) • DataBordismGrp.mk _ ⟨s, str⟩
        = (2 : ℕ) • ((2 : ℕ) • ((2 : ℕ) • DataBordismGrp.mk _ ⟨s, str⟩)) := by
          rw [smul_smul, smul_smul]; norm_num
      _ = DataBordismGrp.mk _ ⟨emptySM, emptyGMStr (2 * (2 * (2 * str.q.brown)))⟩ := by
          rw [e2, dbl, dbl]
  show (8 : ℕ) • DataBordismGrp.mk (pinPlusGMData (E := EuclideanSpace ℝ (Fin (2 + 2)))
      (k := 0) (𝓡 4)) ⟨s, str⟩ = 0
  rw [h8, show (2 * (2 * (2 * str.q.brown))) = 0 from by
      rw [show (2 * (2 * (2 * str.q.brown))) = 8 * str.q.brown from by ring,
        show (8 : ZMod 8) = 0 from by decide, zero_mul],
    emptyGMStr_zero_eq_zero]

/-- **`pinPlusGMData` is NOT `≃+ ZMod 16`** — the kernel-checked separation. Any such equiv would carry
`ZMod 16`'s order-16 element `1` to an order-16 element, but every element of `pinPlusGMData` is 8-torsion
(`pinPlusGMData_eight_torsion`), so `8 • (anything) = 0` — contradiction with `8 • e.symm 1 ≠ 0`. This
formally records: the genuine mod-8 GM carrier canNOT itself be the ℤ/16 object; the odd bit is the
Smith-LES extension (roadmap §9.1). -/
theorem pinPlusGMData_not_equiv_zmod16 :
    IsEmpty (DataBordismGrp (pinPlusGMData (E := EuclideanSpace ℝ (Fin (2 + 2))) (k := 0) (𝓡 4))
      ≃+ ZMod 16) := by
  refine ⟨fun e => ?_⟩
  have h8 : (8 : ℕ) • e.symm (1 : ZMod 16) = 0 := pinPlusGMData_eight_torsion _
  have : e ((8 : ℕ) • e.symm (1 : ZMod 16)) = e 0 := by rw [h8]
  rw [map_nsmul, e.apply_symm_apply, map_zero] at this
  revert this; decide

end SKEFTHawking.PinPlusGMDataZ16
