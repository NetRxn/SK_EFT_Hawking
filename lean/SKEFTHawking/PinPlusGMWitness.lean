import Mathlib
import SKEFTHawking.PinPlusGMData
import SKEFTHawking.PinPlusGMTiedData
import SKEFTHawking.RP4Unconditional
import SKEFTHawking.PinPlusSmithLES
import SKEFTHawking.PinPlusExactSequence

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

/-! ### H8 — routing the cap through the Smith-LES (reduce it to the Rokhlin node)

Per §9.3 (ROUTE LOCK) the cap `{Finite + card ≤ 16}` is NOT the AHSS/height cap — it is supplied by the
Smith-LES: a carrier iso `carrier ≃+ ZMod 16` (transported from the Pin⁻ neighbor `Ω₆^{Pin⁻} ≅ ZMod 16`
through the geometric zero-locus Smith map, `PinPlusSmithLES.pinPlus_zmod16_of_smith_les`) gives `Finite`
+ `card ≤ 16` at once. So `ker abkGMTied16 = ⊥` + the COMPUTED-grade iso follow from **one** input:
`Nonempty (carrier ≃+ ZMod 16)`, i.e. the neighbor `≅ ZMod 16` = the pre-existing tracked Rokhlin node
`hyp:rokhlin_sigma_mod_16` (its irreducible `2 ∣ σ/8` factor). No new debt; the disclosed surface is the
single existing node, its discharge the live 5q.B `16 ∣ σ` workstream (or Matsumoto). -/

/-- **The cap is supplied by any carrier iso `carrier ≃+ ZMod 16`** — `Finite` (transport of `ZMod 16`'s
finiteness) + `Nat.card ≤ 16` (card is iso-invariant). The Smith-LES provides such an iso from the Rokhlin
neighbor. -/
theorem cap_of_carrier_iso_zmod16
    (h : Nonempty (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) ≃+ ZMod 16)) :
    Finite (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4))) ∧
      Nat.card (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4))) ≤ 16 := by
  obtain ⟨e⟩ := h
  haveI : Finite (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4))) :=
    Finite.of_equiv _ e.toEquiv.symm
  exact ⟨inferInstance, by rw [Nat.card_congr e.toEquiv, Nat.card_zmod]⟩

/-- **`ker abkGMTied16 = ⊥` GIVEN a Smith-LES carrier iso** — the COMPUTED grade `abkGMTied16` is the
isomorphism (surjective + the Smith-LES cardinality ⟹ bijective), so its kernel is `⊥`. The single input
is `Nonempty (carrier ≃+ ZMod 16)` = the Rokhlin node (H8 / 5q.B). -/
theorem abkGMTied16_ker_eq_bot_of_smith_les
    (h : Nonempty (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) ≃+ ZMod 16)) :
    ((abkGMTied16 (k := 0) (I := 𝓡 4)) :
      DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) →+ ZMod 16).ker = ⊥ :=
  let ⟨hfin, hcap⟩ := cap_of_carrier_iso_zmod16 h
  abkGMTied16_ker_eq_bot_of_cap hfin hcap

/-- **The full COMPUTED-grade iso GIVEN the Smith-LES carrier iso** — `DataBordismGrp (pinPlusGMTiedData)
≃+ ZMod 16` **via `abkGMTied16`** (invariant computed, generator geometric, no quotient-by-kernel), with
the sole input the Rokhlin-node carrier iso. When `hyp:rokhlin_sigma_mod_16` lands in-tree (5q.B / Matsumoto)
this becomes binder-free. -/
noncomputable def omega4PinPlusGMTied_equiv_zmod16_of_smith_les
    (h : Nonempty (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) ≃+ ZMod 16)) :
    DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) ≃+ ZMod 16 :=
  let ⟨hfin, hcap⟩ := cap_of_carrier_iso_zmod16 h
  omega4PinPlusGMTied_equiv_zmod16_of_cap hfin hcap

/-- **§9.3 Smith-LES form of the tied GM capstone** — the locked injectivity architecture. Re-expresses the
disclosed carrier-iso input in the Smith-LES form: given the geometric codim-2 Smith map `sm : A →+ carrier`
from a Pin⁻ neighbor `A = Ω₆^{Pin⁻}`, its LES exactness at both ends (`0 → A →ˢᵐ carrier → 0`, the twisted-spin
vanishings `Ω_{5,6}^{Spin}(ℝP¹,σ)=0` — the pre-authorized Smith-LES toolkit Props), and the neighbor iso
`A ≃+ ZMod 16` (the ABP-1969 spectral input `hyp:smith_inflow_z16`, the atlas keystone), the full
COMPUTED-grade tied GM carrier is `≃+ ZMod 16`. This is the roadmap §9.3 endpoint: the disclosed input is now
carried solely by the neighbor iso + the geometric exactness, matching the locked architecture. -/
noncomputable def omega4PinPlusGMTied_equiv_zmod16_via_smith_les_neighbor
    {A : Type u} [AddCommGroup A]
    (sm : A →+ DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)))
    (hL : Function.Exact (0 : PUnit →+ A) sm)
    (hR : Function.Exact sm (0 : DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) →+ PUnit))
    (hA : Nonempty (A ≃+ ZMod 16)) :
    DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) ≃+ ZMod 16 :=
  omega4PinPlusGMTied_equiv_zmod16_of_smith_les
    (PinPlusSmithLES.pinPlus_zmod16_of_smith_les sm hL hR hA)

/-- **KT §5 form of the tied capstone — the disclosed input reduced to a SINGLE cardinality fact.**
Instantiates `PinPlusExactSequence.zmod16_of_kt_exact_sequence` (Kirby–Taylor LMS-151 Thm 5.2) at the
tied GM carrier with `p = reduce16to8 ∘ abkGMTied16 : carrier →+ ZMod 8` (the mod-8 GM package the route
lock says `[∩w₁²]` lives at). Three of the four KT §5 facts discharge FROM THE GRADE — (i) `p` surjective
(composite of surjections), (iii) `p[ℝP⁴] = 1`, (iv) `8•[ℝP⁴] ≠ 0` (its grade is `8•1 = 8 ≠ 0` in ℤ/16).
The **sole** remaining disclosed input is (ii) `Nat.card (ker p) = 2` = KT **Lemma 5.3** (the Spin image
`Ω₄^{Spin} → Ω₄^{Pin⁺}` is `ℤ/2`), page-traced in `KT_LMS_Section5_completeness_proof_extracted.md`. -/
theorem omega4PinPlusGMTied_equiv_zmod16_of_spin_image_card
    (hker : Nat.card ((reduce16to8.toAddMonoidHom.comp
        (abkGMTied16 (k := 0) (I := 𝓡 4) :
          DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) →+ ZMod 16)).ker) = 2) :
    Nonempty (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) ≃+ ZMod 16) := by
  refine PinPlusExactSequence.zmod16_of_kt_exact_sequence
    (reduce16to8.toAddMonoidHom.comp (abkGMTied16 (k := 0) (I := 𝓡 4) :
      DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) →+ ZMod 16)) ?_ hker
    rp4GMTiedClass ?_ ?_
  · have h8 : Function.Surjective (reduce16to8 : ZMod 16 → ZMod 8) :=
      ZMod.castHom_surjective (by norm_num)
    exact h8.comp abkGMTied16_surjective
  · show reduce16to8 (abkGMTied16 (k := 0) (I := 𝓡 4) rp4GMTiedClass) = 1
    rw [abkGMTied16_rp4]; rfl
  · intro h
    have hc := congrArg (abkGMTied16 (k := 0) (I := 𝓡 4)) h
    rw [map_nsmul, abkGMTied16_rp4, map_zero] at hc
    revert hc; decide

/-- **The complete KT-route capstone — full strength modulo the two granular §5 geometric facts.**
Threads `PinPlusExactSequence.spin_image_card_two` + the KT §5 exact-sequence exactness + the carrier
instantiation into `DataBordismGrp(pinPlusGMTiedData) ≃+ ZMod 16`. The disclosed input is now exactly the two
individually-standard Kirby–Taylor §5 geometric facts, each page-traced:
* `s : ℤ →+ carrier` with `hs : ∀ n, s n = 0 ↔ 2 ∣ n` — the forgetful `Ω₄^{Spin}≅ℤ → Ω₄^{Pin⁺}` with kernel
  the Pin⁺-bounding classes `2ℤ` (KT **Lemma 5.3**: `sig(Kummer)=16`, bounds iff `sig ÷ 32`);
* `hexact` — the KT §5 exact-sequence exactness `ker [∩w₁²] = image(Spin→Pin⁺)`.
Everything else (surjectivity, the ℝP⁴ generator, the ψ-witness, the order-16 / Lagrange algebra) is already
discharged in-tree. -/
theorem omega4PinPlusGMTied_equiv_zmod16_via_kt_lemma53
    (s : ℤ →+ DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)))
    (hs : ∀ n : ℤ, s n = 0 ↔ (2 : ℤ) ∣ n)
    (hexact : (reduce16to8.toAddMonoidHom.comp
        (abkGMTied16 (k := 0) (I := 𝓡 4) :
          DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) →+ ZMod 16)).ker = s.range) :
    Nonempty (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) ≃+ ZMod 16) := by
  apply omega4PinPlusGMTied_equiv_zmod16_of_spin_image_card
  rw [hexact]
  exact SKEFTHawking.PinPlusExactSequence.spin_image_card_two s hs

/-! ### `hs` DISCHARGED in-tree — the emptySM Spin map (refutes "no in-tree `s` works") -/

/-- The empty-manifold `GMTiedStr` of grade `8` (the Spin generator's grade; `q = stdQuadratic 0`, `w₁⁴=0`). -/
noncomputable def str8 : (pinPlusGMTiedData (k := 0) (𝓡 4)).Mfd emptySM where
  t2 := ⟨fun x => x.elim⟩
  cert := pinPlusCertK_empty
  rank := 0
  q := stdQuadratic 0
  grade16 := 8
  hcoh := by rw [brown_stdQuadratic, Nat.cast_zero]; decide
  htie := by rw [swTotalNe_of_isEmpty]; decide

/-- The grade-`8` empty class — the image of the Spin generator (`[Kummer]=8`). -/
noncomputable def g8 : DataBordismGrp (pinPlusGMTiedData (k := 0) (𝓡 4)) :=
  DataBordismGrp.mk _ ⟨emptySM, str8⟩

theorem abkGMTied16_g8 : abkGMTied16 (k := 0) (I := 𝓡 4) g8 = 8 := rfl

/-- **`g8` is 2-torsion** — the neg=self trick (like `brown_even_two_torsion`): `-g8 = [emptySM, grade -8]`,
and `-8 = 8` in `ZMod 16` on the same manifold, so `-g8 = g8` (`Bor` checks only `grade16`) ⟹ `2•g8 = 0`. -/
theorem two_nsmul_g8 : (2 : ℕ) • g8 = 0 := by
  have hneg : -g8 = g8 := by
    apply DataBordismGrp.mk_eq_of_bordant
    refine ⟨reflCylinder emptySM, ⟨PLift.up ?_⟩⟩
    show (-(8 : ZMod 16)) = 8
    decide
  rw [two_nsmul]
  nth_rewrite 1 [← hneg]
  exact neg_add_cancel g8

/-- `g8 ≠ 0` (its grade is `8 ≠ 0`) and hence has additive order exactly `2`. -/
theorem addOrderOf_g8 : addOrderOf g8 = 2 := by
  have hne : g8 ≠ 0 := fun h => by
    have h8 := abkGMTied16_g8; rw [h, map_zero] at h8; exact absurd h8 (by decide)
  rcases (Nat.dvd_prime Nat.prime_two).mp (addOrderOf_dvd_of_nsmul_eq_zero two_nsmul_g8) with h | h
  · have hg : g8 = 0 := by
      have := h ▸ addOrderOf_nsmul_eq_zero g8; rwa [one_nsmul] at this
    exact absurd hg hne
  · exact h

/-- **`hs` DISCHARGED in-tree** (refutes "no in-tree `s` discharges `hs`"): the Spin map
`s := n ↦ n•g8` (the image of `Ω₄^{Spin}≅ℤ`, `s 1 = [Kummer]` of grade 8) has kernel exactly `2ℤ`,
purely from `g8` being 2-torsion (grade `8 = −8` on the empty manifold) — no completeness needed. -/
theorem g8_zmultiples_ker (n : ℤ) :
    (zmultiplesHom (DataBordismGrp (pinPlusGMTiedData (k := 0) (𝓡 4))) g8) n = 0 ↔ (2 : ℤ) ∣ n := by
  rw [zmultiplesHom_apply, ← addOrderOf_dvd_iff_zsmul_eq_zero, addOrderOf_g8]
  norm_num

/-- **The ⊆ half of the KT §5 exactness `hexact`, proven in-tree.** The Spin image `s.range` (with
`s := n ↦ n•g8`) sits inside `ker(reduce16to8 ∘ abkGMTied16)`: every `n•g8` has grade `8n`, and
`reduce16to8 8 = 0` in `ZMod 8`, so its mod-8 GM grade vanishes. This is the algebraically-forced inclusion
`image(Ω₄^{Spin}) ⊆ ker[∩w₁²]` — half of the sole remaining KT input `hexact` for
`omega4PinPlusGMTied_equiv_zmod16_via_kt_lemma53`; only the reverse (⊇, the completeness/Rokhlin depth)
remains disclosed. Cf. the congruence-level form `GMRokhlin.gmrelation_add_spin`. -/
theorem spin_range_le_ker_reduce :
    (zmultiplesHom (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4))) g8).range ≤
      (reduce16to8.toAddMonoidHom.comp (abkGMTied16 (k := 0) (I := 𝓡 4) :
        DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) →+ ZMod 16)).ker := by
  rintro _ ⟨n, rfl⟩
  simp only [AddMonoidHom.mem_ker, AddMonoidHom.comp_apply, RingHom.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_coe, zmultiplesHom_apply, map_zsmul, abkGMTied16_g8]
  rw [show (reduce16to8 (8 : ZMod 16) = 0) from by decide, zsmul_zero]

/-- **The KT §5 exactness `hexact` reduced to its ⊇ half.** Combining the in-tree ⊆ inclusion
(`spin_range_le_ker_reduce`) with the reverse `hle`, the full exact-sequence equality
`ker[∩w₁²] = image(Spin)` holds. So the disclosed content of `hexact` is now the SINGLE inclusion
`ker ⊆ s.range` (the completeness/Rokhlin depth), not a two-sided equality. -/
theorem hexact_of_ker_le_spin_range
    (hle : (reduce16to8.toAddMonoidHom.comp (abkGMTied16 (k := 0) (I := 𝓡 4) :
              DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) →+ ZMod 16)).ker ≤
           (zmultiplesHom (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4))) g8).range) :
    (reduce16to8.toAddMonoidHom.comp (abkGMTied16 (k := 0) (I := 𝓡 4) :
        DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) →+ ZMod 16)).ker
      = (zmultiplesHom (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4))) g8).range :=
  le_antisymm hle spin_range_le_ker_reduce

/-- **`Ω₄^{Pin⁺} ≅ ℤ/16` reduced to the SINGLE inclusion `ker[∩w₁²] ⊆ image(Spin)`.** The sharpest KT-route
form of the tied GM capstone: everything — surjectivity, the ℝP⁴ generator, the Spin map `s := n•g8` with its
kernel `hs` (`g8_zmultiples_ker`), and the ⊆ half of exactness (`spin_range_le_ker_reduce`) — is discharged
in-tree; the sole remaining geometric input is the one inclusion `hle : ker(reduce16to8 ∘ abkGMTied16) ⊆
(n ↦ n•g8).range`, i.e. the completeness (Rokhlin/ABK) depth that a class of mod-8 GM grade `0` lies in the
Spin image. -/
theorem omega4PinPlusGMTied_equiv_zmod16_of_ker_le_spin_range
    (hle : (reduce16to8.toAddMonoidHom.comp (abkGMTied16 (k := 0) (I := 𝓡 4) :
              DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) →+ ZMod 16)).ker ≤
           (zmultiplesHom (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4))) g8).range) :
    Nonempty (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) ≃+ ZMod 16) :=
  omega4PinPlusGMTied_equiv_zmod16_via_kt_lemma53
    (zmultiplesHom _ g8) g8_zmultiples_ker (hexact_of_ker_le_spin_range hle)

/-! ### The cylinder null-bordism: `2•(any class) = an empty class` (`s⊔s` bounds `s×[0,1]`) -/

/-- An empty-manifold structure of any **even** grade `m` (`q` chosen so `hcoh` holds; `htie` needs `m` even). -/
noncomputable def emptyGMTiedStr (m : ZMod 16) (h : reduce16to2 m = 0) :
    (pinPlusGMTiedData (k := 0) (𝓡 4)).Mfd emptySM where
  t2 := ⟨fun x => x.elim⟩
  cert := pinPlusCertK_empty
  rank := (brown_stdQuadratic_surjective (reduce16to8 m)).choose
  q := stdQuadratic (brown_stdQuadratic_surjective (reduce16to8 m)).choose
  grade16 := m
  hcoh := (brown_stdQuadratic_surjective (reduce16to8 m)).choose_spec.symm
  htie := by rw [swTotalNe_of_isEmpty]; exact h

/-- **The cylinder null-bordism** (`s×[0,1]` has `∂ = s⊔s`, so `s⊔s ~ ∅`): since `Bor` checks only the grade,
`2•[s,str] = [emptySM, 2·grade]` for EVERY structured manifold. So `2•(carrier)` lands in the empty subgroup. -/
theorem two_nsmul_mk (s : SingularManifold PUnit 0 (𝓡 4))
    (str : (pinPlusGMTiedData (k := 0) (𝓡 4)).Mfd s) :
    2 • DataBordismGrp.mk (pinPlusGMTiedData (k := 0) (𝓡 4)) ⟨s, str⟩
      = DataBordismGrp.mk _ ⟨emptySM, emptyGMTiedStr (2 * str.grade16)
          (by rw [map_mul, show (reduce16to2 2 : ZMod 2) = 0 from by decide, zero_mul])⟩ := by
  rw [two_nsmul]
  rw [show DataBordismGrp.mk (pinPlusGMTiedData (k := 0) (𝓡 4)) ⟨s, str⟩
        + DataBordismGrp.mk (pinPlusGMTiedData (k := 0) (𝓡 4)) ⟨s, str⟩
      = DataBordismGrp.add _ (DataBordismGrp.mk _ ⟨s, str⟩) (DataBordismGrp.mk _ ⟨s, str⟩) from rfl,
    DataBordismGrp.add_mk]
  apply DataBordismGrp.mk_eq_of_bordant
  refine ⟨doublingBordism s, ⟨PLift.up ?_⟩⟩
  show str.grade16 + str.grade16 = 2 * str.grade16
  ring

/-- **The completeness capstone reduced to the single geometric node.** From the one geometric fact
"every grade-`0` Pin⁺ class bounds" (`hbound` — the `w₂=0` cert + Wu `w₄=Sq²(w₁²)=w₁⁴` making a Pin⁺
4-manifold's only SW number `w₁⁴=0`, so it is null-bordant; this is the pre-authorized Rokhlin/ABK node),
`abkGMTied16` is injective, so with its surjectivity the tied GM carrier is `≃+ ZMod 16`. The whole
algebra above (`hs` via `g8`, the cylinder `two_nsmul_mk`) plus this single node give the full result. -/
theorem omega4PinPlusGMTied_equiv_zmod16_of_grade0_bounds
    (hbound : ∀ x : DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)),
        (abkGMTied16 (k := 0) (I := 𝓡 4)) x = 0 → x = 0) :
    Nonempty (DataBordismGrp.{u} (pinPlusGMTiedData (k := 0) (𝓡 4)) ≃+ ZMod 16) :=
  ⟨AddEquiv.ofBijective (abkGMTied16 (k := 0) (I := 𝓡 4))
    ⟨(injective_iff_map_eq_zero _).mpr hbound, abkGMTied16_surjective⟩⟩

end SKEFTHawking.PinPlusGMWitness
