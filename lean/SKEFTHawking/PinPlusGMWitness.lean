import Mathlib
import SKEFTHawking.PinPlusGMData
import SKEFTHawking.PinPlusGMTiedData
import SKEFTHawking.RP4Unconditional

/-!
# Phase 5q.H (H3 witness) — the ℝP⁴ Guillou–Marin structure and its COMPUTED mod-8 invariant

The geometric grounding of the GM carrier `pinPlusGMData`: ℝP⁴ carries a GM structure whose
characteristic surface is ℝP² (rank-1 `H₁(ℝP²;ℤ/2)`), with the canonical enhancement `stdQuadratic 1`.
Its computed mod-8 grade is `abkGM8 [ℝP⁴] = β(ℝP²) = (stdQuadratic 1).brown = 1` — **odd**, computed from
the genuine surface enhancement, not a carried tag. The `w₂ = 0` certificate is `rp4_hcert` (RP4 tower).

This is the ℝP⁴ witness the mod-8 surjectivity/fullness ultimately grounds on, and (with the odd value)
the input the H6 Smith-LES lifts to the full `ZMod 16` order-16 generator. Kernel-pure.
-/

open scoped Manifold
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.TangentialDataBordism SKEFTHawking.BordismTheory
open SKEFTHawking.PinPlusGMData SKEFTHawking.PinPlusTiedData SKEFTHawking.PinPlusGMTiedData
open SKEFTHawking.GuillouMarin SKEFTHawking.SingularSWNumber
open SKEFTHawking.RP4PointSet SKEFTHawking.RP4Witness SKEFTHawking.RP4Unconditional

namespace SKEFTHawking.PinPlusGMWitness

/-- **The ℝP⁴ Guillou–Marin structure**: characteristic surface ℝP² (`rank = 1`), enhancement
`stdQuadratic 1`; the `w₂`-certificate is `rp4_hcert`. -/
noncomputable def rp4GMStr : GMStr (𝓡 4) rp4SM where
  t2 := inferInstanceAs (T2Space RP4)
  cert := rp4_hcert
  rank := 1
  q := stdQuadratic 1

/-- The ℝP⁴ class in the GM carrier `DataBordismGrp (pinPlusGMData (k := 0) (𝓡 4))`. -/
noncomputable def rp4GMClass : DataBordismGrp (pinPlusGMData (k := 0) (𝓡 4)) :=
  DataBordismGrp.mk _ ⟨rp4SM, rp4GMStr⟩

/-- **The computed mod-8 GM invariant of ℝP⁴ is `1`** (odd) — `β(ℝP²)`, computed from the genuine
characteristic-surface enhancement `stdQuadratic 1`, NOT a carried tag. The odd value is what the H6
Smith-LES lifts to the full `ZMod 16` order-16 generator. -/
theorem abkGM8_rp4 : abkGM8 (k := 0) (I := 𝓡 4) rp4GMClass = 1 := by
  show (stdQuadratic 1).brown = 1
  rw [brown_stdQuadratic, Nat.cast_one]

/-! ### H5 comparison — the GM and tied carriers agree on the ℝP⁴ generator

Per §9.1 the GM surface package computes the invariant only **mod 8**; the tied carrier carries the full
(free) `ZMod 16` grade. So the carriers are comparable at the **mod-8** level, and the meaningful,
buildable comparison is the generator cross-check: both give the ℝP⁴ generator, and the GM mod-8 invariant
is the mod-8 reduction of the tied `ZMod 16` grade. (A *total* structure-morphism `GM → Tied` is NOT
buildable — the GM enhancement `q` is free, so its parity need not match the tied `tie = w₁⁴`, the same
free-grade obstruction as `synthetic-grade-ker-bot-nogo`; full subsumption of the tied capstone is the H7
job, once the GM carrier gains its own `ZMod 16` via the H6 Smith-LES.) -/

/-- The tied ℝP⁴ class (5q.G bedrock: grade `(1,0)`, w₁⁴ = 1). -/
noncomputable def rp4TiedClass : DataBordismGrp (pinPlusTiedData (k := 0) (𝓡 4)) :=
  DataBordismGrp.mk _ ⟨rp4SM, rp4TiedStr rp4_hcert rp4_htie⟩

/-- The tied ℝP⁴ grade is `1 ∈ ZMod 16`. -/
theorem abkTiedGrade_rp4 : abkTiedGrade (I := 𝓡 4) (k := 0) rp4TiedClass = 1 := rfl

/-- **GM ↔ tied agreement on the ℝP⁴ generator** — the computed GM mod-8 invariant `abkGM8[ℝP⁴] = 1`
is exactly the mod-8 reduction of the tied `ZMod 16` grade `abkTiedGrade[ℝP⁴] = 1`. The live cross-check
(risk-register #2): the ℝP⁴ witness's ABK comes out the generator on both carriers, consistently. -/
theorem gm_tied_agree_rp4 :
    reduce16to8 (abkTiedGrade (I := 𝓡 4) (k := 0) rp4TiedClass)
      = abkGM8 (k := 0) (I := 𝓡 4) rp4GMClass := by
  rw [abkTiedGrade_rp4, abkGM8_rp4]; decide

/-! ### H6-a — the ℝP⁴ witness on the TIED GM carrier (an odd order-16 generator)

`rp4GMTiedStr` carries `grade16 = 1` with the mod-8 part computed (`hcoh`: `reduce16to8 1 = β(ℝP²) = 1`)
and the parity tied to `w₁⁴[ℝP⁴] = 1` (`htie`, discharged from `rp4_htie` exactly as `rp4TiedStr`). Its
grade is `1 ∈ ZMod 16` — ODD, so it is the order-16 generator the H6 injectivity / H7 capstone need. -/

/-- **The ℝP⁴ tied Guillou–Marin structure** — `grade16 = 1`, enhancement `stdQuadratic 1`, cert `rp4_hcert`;
the mod-8 part computed (`hcoh`) and the parity tied to `w₁⁴` (`htie`). -/
noncomputable def rp4GMTiedStr : GMTiedStr (𝓡 4) rp4SM where
  t2 := inferInstanceAs (T2Space RP4)
  cert := rp4_hcert
  rank := 1
  q := stdQuadratic 1
  grade16 := 1
  hcoh := by rw [brown_stdQuadratic, Nat.cast_one]; decide
  htie := by
    rw [swTotalNe, dif_pos (inferInstanceAs (Nonempty RP4))]
    show reduce16to2 (1 : ZMod 16) = swNumberW14 RP4
    rw [rp4_htie]; decide

/-- The ℝP⁴ class in the tied GM carrier. -/
noncomputable def rp4GMTiedClass : DataBordismGrp (pinPlusGMTiedData (k := 0) (𝓡 4)) :=
  DataBordismGrp.mk _ ⟨rp4SM, rp4GMTiedStr⟩

/-- **The tied ℤ/16 GM grade of ℝP⁴ is `1`** — the odd order-16 generator (mod-8 part computed from the
ℝP² Brown invariant; the odd bit `1` is the H6/H8-content value on the generator). -/
theorem abkGMTied16_rp4 : abkGMTied16 (k := 0) (I := 𝓡 4) rp4GMTiedClass = 1 := rfl

/-- **The ℝP⁴ tied grade is ODD** — `reduce16to2 (abkGMTied16 [ℝP⁴]) = 1`, so it has additive order 16
(the surjectivity / order-16 input for H6–H7). -/
theorem abkGMTied16_rp4_odd :
    reduce16to2 (abkGMTied16 (k := 0) (I := 𝓡 4) rp4GMTiedClass) = 1 := by
  rw [abkGMTied16_rp4]; decide

/-- **The tied GM ℤ/16 grade is SURJECTIVE onto `ZMod 16`** — the ℝP⁴ odd generator closes the range
(the evens are realised on `∅`). This is the FULL `ZMod 16` fullness on the tied carrier (stronger than
`abkGM8`'s mod-8 surjectivity): the H6 surjectivity + order-16 input. -/
theorem abkGMTied16_surjective : Function.Surjective (abkGMTied16 (k := 0) (I := 𝓡 4)) :=
  AddMonoidHom.range_eq_top.mp
    (abkGMTied16_range_top_of_odd ⟨rp4GMTiedClass, abkGMTied16_rp4_odd⟩)

/-- **Unconditional first isomorphism on the tied GM carrier**: `DataBordismGrp (pinPlusGMTiedData) ⧸
ker(abkGMTied16) ≃+ ZMod 16` — the full `ZMod 16` quotient (mod-8 part computed, odd generator geometric).
The residual `ker` (⟹ the full-carrier `≃+ ZMod 16`, H7) is the H6-b/H8 Smith-LES + Rokhlin summit. -/
noncomputable def dataBordismGMTied_quotient_equiv_zmod16 :
    DataBordismGrp (pinPlusGMTiedData (k := 0) (𝓡 4)) ⧸ (abkGMTied16 (k := 0) (I := 𝓡 4)).ker
      ≃+ ZMod 16 :=
  QuotientAddGroup.quotientKerEquivOfSurjective abkGMTied16 abkGMTied16_surjective

/-! ### H6-a — the injectivity reduction (unconditional GIVEN the ABK-completeness cap)

`ker abkGMTied16 = ⊥` reduces to a `card ≤ 16` cap by counting: surjectivity (proven) + `card ≤ 16` force
bijectivity. The `card ≤ 16` cap is the ONE disclosed input — the ABK-completeness `η(σ)=0 ⟹ bounds`
(`synthetic-grade-ker-bot-nogo` discharge plan #2). Per §9.3 (ROUTE LOCK) it is discharged at **H8 via the
SMITH-LES** (the Pin⁻ neighbor `Ω₆^{Pin⁻} ≅ ℤ/16` transported through the geometric Smith map), NOT the
AHSS/height cap the faithful carrier used. This mirrors `PinPlusFaithfulData.abkFaithfulGrade_bijective_of_cap`
but on the COMPUTED-grade tied GM carrier. -/

universe u

/-- **Bijective under the cap** — surjectivity (proven) + `Nat.card ≤ 16` force bijectivity by counting. -/
theorem abkGMTied16_bijective_of_cap
    (hfin : Finite (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4))))
    (hcap : Nat.card (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4))) ≤ 16) :
    Function.Bijective ((abkGMTied16 (k := 0) (I := 𝓡 4)) :
      DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) →+ ZMod 16) := by
  haveI := hfin
  have hge : 16 ≤ Nat.card (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4))) := by
    have h1 := Nat.card_le_card_of_surjective _ (abkGMTied16_surjective)
    rwa [Nat.card_zmod] at h1
  have hcard : Nat.card (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)))
      = Nat.card (ZMod 16) := by rw [Nat.card_zmod]; exact le_antisymm hcap hge
  exact (Nat.bijective_iff_surjective_and_card _).mpr ⟨abkGMTied16_surjective, hcard⟩

/-- **`ker abkGMTied16 = ⊥` under the cap** — the injectivity, from counting (surjective + `card ≤ 16`). -/
theorem abkGMTied16_ker_eq_bot_of_cap
    (hfin : Finite (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4))))
    (hcap : Nat.card (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4))) ≤ 16) :
    ((abkGMTied16 (k := 0) (I := 𝓡 4)) :
      DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) →+ ZMod 16).ker = ⊥ :=
  (AddMonoidHom.ker_eq_bot_iff _).mpr (abkGMTied16_bijective_of_cap hfin hcap).1

/-- **The FULL tied GM carrier is `≃+ ZMod 16` under the cap** — `omega4PinPlusGMTied_equiv_zmod16_of_cap`,
the literature-grade statement modulo the single disclosed ABK-completeness cap (→ H8 Smith-LES/Rokhlin).
Invariant computed (mod-8 via `hcoh`), generator geometric (`rp4GMTiedStr`), NO quotient-by-kernel. -/
noncomputable def omega4PinPlusGMTied_equiv_zmod16_of_cap
    (hfin : Finite (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4))))
    (hcap : Nat.card (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4))) ≤ 16) :
    DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) ≃+ ZMod 16 :=
  AddEquiv.ofBijective _ (abkGMTied16_bijective_of_cap hfin hcap)

end SKEFTHawking.PinPlusGMWitness
