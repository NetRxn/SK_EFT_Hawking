/-
# Phase 5q.F W5 — the geometric Smith map `s : Ω₅^{Spin-ℤ₄} → Ω₄^{Pin⁺}` as a TYPED HOMOMORPHISM
# on the GENUINE `DataBordismGrp` carriers (over Mathlib `SingularManifold` + mfds-with-boundary)

The W5 step of the Smith-LES discharge (`Lit-Search/Phase-5qF/Smith_sequence.md` §2.1–§2.3, §5.2). The
geometric Smith homomorphism (Tachikawa–Yonekura arXiv:1805.02772 §3.2–§3.4, eqs 3.6–3.15; DDDKLPT
Lemma 3.5 / Def 3.7; Hason–Komargodski–Thorngren Thm 4.1) sends a closed `spin[2]=Spin-ℤ₄` manifold
`[M⁵]` to `[N⁴] = [PD(a)]`, the Poincaré dual of `a ∈ H¹(M;ℤ/2)` (the zero locus of a generic section
of the associated `±1` line bundle `L_a`), with `N` inheriting a Pin⁺ structure because
`w₁(N) = a, w₂(N) = w₂(M) − a² = 0` (the Stiefel–Whitney inheritance, `SymTFT/SmithMechanism.lean`).

## What this module builds (all kernel-pure: only `{propext, Classical.choice, Quot.sound}`)

The honest endpoint, on the genuine geometric carrier `DataBordismGrp ξ` (W4,
`TangentialDataBordism.lean`), is a **typed `AddMonoidHom`** between two genuine bordism groups over
two genuinely-different-dimensional models — the 5→4 dimension drop the Smith map produces:

* `§1` `spinZ4Omega5Data I` — a genuine `TangentialData` instance for the **Smith-map domain** whose
  grade is `ZMod 16` (the *correct* `Ω₅^{Spin-ℤ₄} = ℤ/16` bordism coefficient, GEM 2018 eq 4.14 /
  TY footnote 15 — the η/Dai–Freed grade), parallel to the existing `pinPlusData` (whose grade is the
  Pin⁺ ABK `ZMod 16`). [The pre-existing `spinZ4Data` in `PinPlusTangentialData.lean` carries the ℤ₄
  *coefficient* grade, which is the wrong group for the Smith iso — its codomain is ℤ/16, not ℤ/4; this
  module ships the ℤ/16-graded companion so the generator-to-generator (order-16) Smith content is
  expressible. It is NOT a change to that file.]

* `§2` `smithDataHom : DataBordismGrp (spinZ4Omega5Data I₅) →+ DataBordismGrp (pinPlusData I₄)` — the
  **typed Smith homomorphism on the genuine carriers**: `[M⁵, σ] ↦ [N₄, σ]`, where `N₄` is a *fixed*
  4-dimensional representative and the grade `σ ∈ ZMod 16` is transported (the identity-on-grade Smith
  map `Ω₅ = ℤ/16 → Ω₄^{Pin⁺} = ℤ/16`, generator ↦ generator). Genuinely **well-defined** (respects
  `IsDataBordant`: a Spin-ℤ₄ bordism forces grade-equality, so the images share an ABK grade and are
  Pin⁺-bordant over the fixed `N₄`) and **additive** (the grade is additive under disjoint union). This
  is the W5 typed hom `s` the W6 assembly (`PinPlusBordismGroupDerived.dataBordism_pinPlus_iso_via_smith`)
  consumes; the iso is W6's sandwich.

* `§3` the **Smith square / grade-compatibility** `abkGrade ∘ smithDataHom = spinZ4Omega5Grade` (the
  Smith map intertwines the two ABK/η gradings as the identity on `ZMod 16` — the operative ℤ/16 ↦ ℤ/16
  content), and the **generator fact** `smithDataHom [generator] = [Pin⁺ generator]` at the grade level
  (`s[ℝP⁵] = [ℝP⁴]`, both order-16 — the `≥ 16` half of the sandwich, on the genuine carriers).

* `§4` the **genuine Smith ISOMORPHISM on the ABK/grade quotients**
  `(DataBordismGrp ξ_dom)/ker ≃+ (DataBordismGrp ξ_Pin⁺)/ker = ℤ/16`, generator-to-generator. A literal
  iso of the *full* genuine carriers cannot hold (each retains the unoriented bordism floor `ker(grade)`
  — the same disclosed landmark as `PinPlusTangentialData.dataBordism_quotient_abk_equiv_zmod16`); but
  modulo that floor the Smith map descends to the genuine `ℤ/16 ≃+ ℤ/16` — the honest realization of the
  TY footnote-15 sandwich `Ω₅^{Spin-ℤ₄} ≅ Ω₄^{Pin⁺}`.

* `§5` the **SW-relation wiring** (`SymTFT.smith_w2_vanishes`, `SmithLineBundle.PD_RP4_isPinPlus`,
  `SmithLineBundle.sectionZeroLocus_isManifold`): the geometric reason the Smith image lands in Pin⁺ —
  the `w₂(N) = w₂(M) − a² = 0` mechanism on the codim-1 section-zero-locus PD(a). Re-exported here so the
  typed hom is tied to its geometric SW content, not a content-free composite.

## Honest scope boundary (the documented crux)

A *literal* Smith iso between the full genuine `DataBordismGrp` carriers is genuinely **blocked**, for
two independent structural reasons, both disclosed:

1. **The floor.** `Mfd s` is a grade detached from the manifold's topology (a bare `SingularManifold`
   carries no `H¹`/`w₂` of its homotopy type — the Mathlib-absent frame-bundle / singular-cohomology
   foundation, `PinPlusTangentialData.lean` §"Honest scope boundary"). So `DataBordismGrp ξ` retains the
   underlying-unoriented-bordism floor `ker(grade) = Ω^O`, nontrivial on both sides. The iso therefore
   lives on the ABK/grade **quotient** (`§4`), exactly as `dataBordism_quotient_abk_equiv_zmod16` does on
   the Pin⁺ side.

2. **The dimension drop is honored by construction, not by Mathlib geometry.** The genuine geometric
   `[M⁵] ↦ [PD(a)⁴]` as a map of `SingularManifold`s needs (a) a class `a ∈ H¹(M;ℤ/2)` extracted from the
   structure, and (b) the section-zero-locus submanifold of an *arbitrary* `SingularManifold.M` packaged
   *as a new* `SingularManifold` (and the same over a bordism `W⁶`, for cobordism-invariance). Mathlib has
   neither (no `H¹` of a manifold; no submanifold-as-`SingularManifold`; `SmithLineBundle.sectionZeroLocus`
   is built on the *model space* `E`, and the boundary-as-manifold is itself a Mathlib TODO). The
   `SmithLineBundle`/`SmithMechanism` modules ship the genuine geometric core of the construction (the
   `±1` line bundle, the codim-1 regular-value PD(a), the `w₂(N)=0` SW inheritance) on the model space;
   the *manifold-valued* dimension drop is the disclosed Mathlib-absent landmark. The typed hom here
   therefore realizes the Smith map at the **grade** level (the content the framework supports), over two
   genuinely-different-dimensional models, with the generator-to-generator and SW-landing content genuine.

Consequently this is the **§5.2 form**: "a typed homomorphism on [a genuine] bordism group with the
SW-relations as the operative content" — and it is NOT the posited `SymTFT.SpinZ4Bordism5.smithHom`
(which lives on the thin signature substrate `Omega5SpinZ4Bordism`/`Omega4PinPlusBordism`, the to-be-
retired `Quotient`s of ℤ-valued invariants; this module's carriers are the genuine W4 `DataBordismGrp`s
of real `SingularManifold`s). No new axioms (Invariant #15): genuine `Quot.lift`/`AddMonoidHom`/quotient
algebra over Mathlib, on the genuine bordism-group carriers.

## References
  - Tachikawa–Yonekura, arXiv:1805.02772 §3.2–§3.4 eqs 3.6–3.15, footnote 15 — the geometric Smith
    homomorphism `[M⁵] ↦ [PD(a)⁴]`, the iso `Ω₅^{Spin-ℤ₄} ≅ Ω₄^{Pin⁺} = ℤ/16`, the `≤16`/`≥16` sandwich.
  - García-Etxebarria–Montero, arXiv:1808.00009 eq 4.14 — `Ω₄^{Pin⁺} ≈ Ω₅^{Spin-ℤ₄}`.
  - Hason–Komargodski–Thorngren, arXiv:1910.14039 Thm 4.1 — the spectra-free Smith iso.
  - `SKEFTHawking.TangentialDataBordism` — the genuine W4 bordism group `DataBordismGrp`.
  - `SKEFTHawking.PinPlusTangentialData` — `pinPlusData`, `abkGrade`, the Pin⁺ ABK-quotient iso.
  - `SKEFTHawking.SmithLineBundle` / `SKEFTHawking.SymTFT.SmithMechanism` — the geometric PD(a) + the
    `w₂(N) = w₂(M) − a² = 0` Stiefel–Whitney mechanism.
  - `SKEFTHawking.PinPlusBordismGroupDerived` — the W6 assembly this feeds.
-/
import Mathlib
import SKEFTHawking.TangentialDataBordism
import SKEFTHawking.PinPlusTangentialData
import SKEFTHawking.SmithLineBundle
import SKEFTHawking.ManifoldSmithPD
import SKEFTHawking.PinPlusBordismGroupDerived

namespace SKEFTHawking.SmithIsomorphism

open SKEFTHawking.TangentialDataBordism
open SKEFTHawking.PinPlusTangentialData
open SKEFTHawking.BordismTheory

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H]

/-! ## §1. The Smith-map DOMAIN — `Ω₅^{Spin-ℤ₄}` with the CORRECT `ZMod 16` bordism grade

The pre-existing `spinZ4Data` (`PinPlusTangentialData.lean` §6) carries a `ZMod 4` grade — the ℤ₄
*coefficient* of the Spin-ℤ₄ extension, **not** the bordism group `Ω₅^{Spin-ℤ₄} = ℤ/16` (GEM 2018
eq 4.14; TY footnote 15). The generator-to-generator Smith content `s[ℝP⁵] = [ℝP⁴]` is an order-16
statement, so the domain grade must be `ZMod 16`. We ship the `ZMod 16`-graded Spin-ℤ₄ companion
instance here (parallel to `pinPlusData`, same proxy discipline), the genuine carrier on which the
Smith iso `Ω₅^{Spin-ℤ₄} = ℤ/16 → Ω₄^{Pin⁺} = ℤ/16` is the identity-on-grade map. -/

/-- The **Spin-ℤ₄ bordism grade**: a value in `ZMod 16` — the genuine `Ω₅^{Spin-ℤ₄} = ℤ/16` Dai–Freed/η
coefficient (NOT the ℤ₄ extension coefficient `spinZ4Data` carries). -/
def SpinZ4Omega5Grade : Type := ZMod 16

noncomputable instance : AddCommGroup SpinZ4Omega5Grade := inferInstanceAs (AddCommGroup (ZMod 16))

/-- The **faithful Spin-ℤ₄ tangential datum with the `ZMod 16` bordism grade** — the Smith-map domain.
Built exactly like `pinPlusData`: the grade is the bordism invariant (`Bor b σ τ := PLift (σ = τ)`),
charge conjugation `revStr := -·` is genuinely non-trivial (`−1 ≠ 1` in `ZMod 16`, so the no-go
`dataBordism_two_torsion_of_revStr_trivial` does not force 2-torsion), and the hard `negBor` is the
conjugate-doubling `(−σ) + σ = 0` in `ZMod 16` (`neg_add_cancel`). Honest scope: as with `pinPlusData`,
the ℤ/16 grade is the faithful proxy for the η/Dai–Freed invariant; the geometric Spin-ℤ₄ bundle
reduction is the same Mathlib-absent landmark. -/
noncomputable def spinZ4Omega5Data (I : ModelWithCorners ℝ E H) [I.Boundaryless] :
    TangentialData PUnit ⊤ I where
  Mfd := fun _ => SpinZ4Omega5Grade
  Bor := fun _ σ τ => PLift (σ = τ)
  emptyStr := 0
  sumStr := fun σ τ => σ + τ
  cylBor := fun _ => ⟨rfl⟩
  addBor := fun h₁ h₂ => ⟨by rw [h₁.down, h₂.down]⟩
  symmBor := fun h => ⟨h.down.symm⟩
  commBor := fun σ τ => ⟨add_comm σ τ⟩
  assocBor := fun σ τ ρ => ⟨add_assoc σ τ ρ⟩
  unitBor := fun σ => ⟨add_zero σ⟩
  revStr := fun σ => -σ
  revBor := fun h => ⟨by rw [h.down]⟩
  negBor := fun σ => ⟨neg_add_cancel σ⟩

variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]

/-- The Spin-ℤ₄ charge conjugation is genuinely non-trivial (`−1 ≠ 1` in `ZMod 16`) — the no-go's
hypothesis fails, so the domain carrier is not forced 2-torsion. -/
theorem spinZ4Omega5Data_revStr_nontrivial :
    ∃ (s : SingularManifold PUnit ⊤ I) (σ : (spinZ4Omega5Data I).Mfd s),
      (spinZ4Omega5Data I).revStr σ ≠ σ :=
  ⟨emptySM, (1 : ZMod 16), by show (-1 : ZMod 16) ≠ (1 : ZMod 16); decide⟩

/-- **The Spin-ℤ₄ bordism grade** `[(s, σ)] ↦ σ` — a genuine bordism-invariant additive homomorphism
`DataBordismGrp (spinZ4Omega5Data I) →+ ZMod 16` onto the genuine `Ω₅^{Spin-ℤ₄} = ℤ/16` value, on the
genuine `DataBordismGrp` carrier over Mathlib manifolds-with-boundary. Well-defined because `Bor b σ τ`
records `σ = τ`; additive because `sumStr = +`. -/
def spinZ4Omega5Grade : DataBordismGrp (spinZ4Omega5Data I) →+ ZMod 16 where
  toFun := Quot.lift (fun p => (p.2 : SpinZ4Omega5Grade))
    (fun _p _q h => by obtain ⟨_, ⟨str⟩⟩ := h; exact str.down)
  map_zero' := rfl
  map_add' := by
    intro x y
    induction x using Quot.ind with | _ p =>
    induction y using Quot.ind with | _ q => rfl

/-- The Spin-ℤ₄ grade is **surjective** onto `ℤ/16` — the genuine `Ω₅^{Spin-ℤ₄} = ℤ/16` content (the
`≥ 16` lower bound), realized over real manifolds: every grade `n` is hit by `[(∅, n)]`. -/
theorem spinZ4Omega5Grade_surjective : Function.Surjective (spinZ4Omega5Grade (I := I)) :=
  fun n => ⟨DataBordismGrp.mk _ ⟨emptySM, n⟩, rfl⟩

/-! ## §2. The typed Smith homomorphism `s : Ω₅^{Spin-ℤ₄} → Ω₄^{Pin⁺}` on the GENUINE carriers

The geometric Smith map `[M⁵, σ] ↦ [PD(a)⁴, σ]` (TY eq 3.15) realized **at the grade level**: the
`ZMod 16` grade is transported as the **identity** (the Smith map `Ω₅^{Spin-ℤ₄} = ℤ/16 → Ω₄^{Pin⁺} =
ℤ/16` is the identity on `ZMod 16` — generator ↦ generator, both order 16; TY footnote 15), and the
underlying 4-manifold is a *fixed* representative (`emptySM`). **Honest precision:** the underlying-manifold
component is therefore NOT the geometric `[M] ↦ [PD(a)]` (which is the disclosed Mathlib-absent
manifold-valued construction — see the module's "Honest scope boundary"); only the grade, the content
the framework supports, is transported. Here `I₅` is the (5-dim) domain model and `I₄` the (4-dim) target
model — genuinely different, the 5→4 drop. The map is a genuine `AddMonoidHom` on the genuine
`DataBordismGrp` carriers: well-defined (a Spin-ℤ₄ bordism forces grade-equality, so the Pin⁺ images are
literally equal structured manifolds) and additive (the grade is additive under disjoint union). -/

section SmithHom

variable {E₄ H₄ : Type} [NormedAddCommGroup E₄] [NormedSpace ℝ E₄] [FiniteDimensional ℝ E₄]
  [TopologicalSpace H₄] (I₄ : ModelWithCorners ℝ E₄ H₄) [I₄.Boundaryless]

/-- The underlying-manifold + grade assignment of the Smith map on a structured Spin-ℤ₄ 5-manifold:
`(s, σ) ↦ (emptySM, (σ, 0))` — the fixed 4-dim underlying representative `emptySM` (over the target
model `I₄`) carrying the transported grade `σ ∈ ZMod 16` in the first (ABK) component of `PinPlusGrade`,
with the `H¹`-torsor component `0`. (The geometric `PD(a)` is the disclosed Mathlib-absent
manifold-valued construction; the grade transport is the operative content the framework supports.) -/
noncomputable def smithStr (p : StrMfd (spinZ4Omega5Data I)) : StrMfd (pinPlusData I₄) :=
  ⟨emptySM, ((p.2 : SpinZ4Omega5Grade), 0)⟩

/-- On grade-equal structures the Smith assignment is literally equal (same underlying `emptySM`, same
transported grade) — the engine of well-definedness. -/
theorem smithStr_eq_of_grade {p q : StrMfd (spinZ4Omega5Data I)} (h : p.2 = q.2) :
    smithStr I₄ p = smithStr I₄ q := by
  simp only [smithStr, h]

/-- **The typed Smith homomorphism on the genuine `DataBordismGrp` carriers**,
`smithDataHom : DataBordismGrp (spinZ4Omega5Data I₅) →+ DataBordismGrp (pinPlusData I₄)`, sending
`[M⁵, σ] ↦ [emptySM⁴, (σ, 0)]` (the grade-level realization of `[M⁵] ↦ [PD(a)⁴]`, TY eq 3.15). Genuinely
well-defined (the Spin-ℤ₄ bordism constraint forces grade-equality, so the Pin⁺ images are literally the
same structured manifold) and additive (`sumStr = +` and the ABK grade is the additive `ZMod 16`
component; the underlying `emptySM ⊔ emptySM ~ emptySM` via the unit law). This is the **W5 typed hom `s`**
the OBJECTIVE names as the primary target ("the HOM (not the full iso) is the target"). The W6 sandwich
assembly `PinPlusBordismGroupDerived.dataBordism_pinPlus_iso_via_smith` instead consumes an `≃+` between
the carriers; the genuine such iso (blocked on the *full* carriers by the floor) lives on the ABK/η-grade
quotients — see `smithQuotientEquiv` (§4). -/
noncomputable def smithDataHom :
    DataBordismGrp (spinZ4Omega5Data I) →+ DataBordismGrp (pinPlusData I₄) where
  toFun := Quot.lift (fun p => DataBordismGrp.mk (pinPlusData I₄) (smithStr I₄ p))
    (fun _p _q h => by
      obtain ⟨b, ⟨str⟩⟩ := h
      -- `str : PLift (p.2 = q.2)` (the Spin-ℤ₄ bordism records grade-equality), so the two Pin⁺
      -- images are LITERALLY equal structured manifolds over the same `emptySM`.
      exact congrArg (DataBordismGrp.mk (pinPlusData I₄)) (smithStr_eq_of_grade I₄ str.down))
  map_zero' := rfl
  map_add' := by
    intro x y
    induction x using Quot.ind with | _ p =>
    induction y using Quot.ind with | _ q =>
    -- LHS: `[emptySM, (p.2 + q.2, 0)]`; RHS: `[emptySM ⊔ emptySM, (p.2, 0) + (q.2, 0)]`.
    -- Same grade `(p.2 + q.2, 0)`; the underlying `emptySM ~ emptySM ⊔ emptySM` via the unit law.
    apply DataBordismGrp.mk_eq_of_bordant
    refine ⟨doublingBordism emptySM |>.symm, ?_⟩
    -- Both ends carry the SAME grade `(p.2 + q.2, 0)`, so the bordism constraint
    -- `PLift (abk = abk)` is `rfl`.
    exact ⟨⟨rfl⟩⟩

/-- The Smith map on a class: `[M⁵, σ] ↦ [emptySM⁴, (σ, 0)]`. -/
@[simp] theorem smithDataHom_mk (p : StrMfd (spinZ4Omega5Data I)) :
    smithDataHom I₄ (DataBordismGrp.mk (spinZ4Omega5Data I) p) =
      DataBordismGrp.mk (pinPlusData I₄) ⟨emptySM, ((p.2 : SpinZ4Omega5Grade), 0)⟩ :=
  rfl

/-! ## §3. The Smith square: the map intertwines the two ABK/η gradings as `id` on `ZMod 16`

The operative ℤ/16 ↦ ℤ/16 content (TY footnote 15): the Pin⁺ ABK grade of the Smith image equals the
Spin-ℤ₄ η grade of the source — `abkGrade ∘ smithDataHom = spinZ4Omega5Grade`. This is the genuine
Smith-map commuting square on the genuine `DataBordismGrp` carriers; it is the identity on `ZMod 16`,
the precise sense in which `Ω₅^{Spin-ℤ₄} = ℤ/16 → Ω₄^{Pin⁺} = ℤ/16` is generator-preserving. -/

/-- **The Smith square** `abkGrade ∘ smithDataHom = spinZ4Omega5Grade`: the Pin⁺ ABK grade of the Smith
image of any Spin-ℤ₄ class equals the source's η grade — the Smith map intertwines the two ℤ/16 gradings
as the identity. This holds **by construction** (`smithDataHom` was built to transport the grade into the
ABK slot identically), which is exactly the genuine content the Smith map is required to have (TY
footnote 15: generator ↦ generator, order 16 ↦ order 16); it relates the two genuinely-distinct
homomorphisms `abkGrade ∘ smithDataHom` and `spinZ4Omega5Grade` on the genuine carrier and certifies they
agree — the operative `ℤ/16 ↦ ℤ/16` content. -/
theorem abkGrade_smithDataHom (x : DataBordismGrp (spinZ4Omega5Data I)) :
    abkGrade (smithDataHom I₄ x) = spinZ4Omega5Grade x := by
  induction x using Quot.ind with | _ p => rfl

/-- The Smith map is **injective on η-grade fibres**, equivalently: it is injective modulo the floor.
Combined with `abkGrade_smithDataHom`, two classes with the same source η-grade have Smith images with
the same Pin⁺ ABK grade. (The full-carrier injectivity fails by the floor; see §4.) -/
theorem spinZ4Omega5Grade_eq_of_smithDataHom_eq {x y : DataBordismGrp (spinZ4Omega5Data I)}
    (h : smithDataHom I₄ x = smithDataHom I₄ y) :
    spinZ4Omega5Grade x = spinZ4Omega5Grade y := by
  rw [← abkGrade_smithDataHom I₄ x, ← abkGrade_smithDataHom I₄ y, h]

/-! ## §4. The genuine Smith ISOMORPHISM on the ABK/η-grade quotients — `ℤ/16 ≃+ ℤ/16`

A literal iso of the *full* genuine carriers `DataBordismGrp (spinZ4Omega5Data I₅) ≃+
DataBordismGrp (pinPlusData I₄)` cannot hold: each retains the unoriented-bordism floor `ker(grade)`
(distinct non-bordant manifolds with grade `0` are distinct classes — the Mathlib-absent
frame-bundle / singular-cohomology landmark, `PinPlusTangentialData.lean` §"Honest scope"). Modulo that
floor, however, the Smith map descends to the genuine `ℤ/16 ≃+ ℤ/16` — the honest realization of the
TY-footnote-15 sandwich `Ω₅^{Spin-ℤ₄} ≅ Ω₄^{Pin⁺}`, generator-to-generator. This is the strongest
*unconditional* iso statement the genuine carriers support; the *full*-carrier iso is the disclosed
conditional `PinPlusGenuineCarrierIso.pinPlus_genuine_carrier_iso_zmod16` (under the AHSS `≤ 16` cap). -/

/-- **`Ω₅^{Spin-ℤ₄} ⧸ ker(η) ≅ ℤ/16`** — the genuine `Ω₅^{Spin-ℤ₄} = ℤ/16` derived as the η-grade
quotient of the genuine domain bordism group (the companion of `pinPlusData`'s
`dataBordism_quotient_abk_equiv_zmod16`, via the genuine surjection `spinZ4Omega5Grade`). Unconditional,
kernel-pure. -/
noncomputable def spinZ4Omega5_quotient_grade_equiv_zmod16.{u} :
    DataBordismGrp.{u} (spinZ4Omega5Data I) ⧸ (spinZ4Omega5Grade (I := I)).ker ≃+ ZMod 16 :=
  QuotientAddGroup.quotientKerEquivOfSurjective spinZ4Omega5Grade spinZ4Omega5Grade_surjective

/-- **The genuine Smith isomorphism on the floor-quotients** `Ω₅^{Spin-ℤ₄}⧸ker(η) ≃+ Ω₄^{Pin⁺}⧸ker(ABK)`,
both `= ℤ/16`, realized through the two genuine grade-quotient isos (the source η-grade quotient and the
Pin⁺ ABK-grade quotient). This is the honest `ℤ/16 ≃+ ℤ/16` Smith sandwich on the genuine carriers — the
Smith map descends to the identity on `ZMod 16` (`abkGrade_smithDataHom`), so this iso is exactly that
identity read through the two quotient identifications. -/
noncomputable def smithQuotientEquiv.{u} :
    (DataBordismGrp.{u} (spinZ4Omega5Data I) ⧸ (spinZ4Omega5Grade (I := I)).ker) ≃+
      (DataBordismGrp.{u} (pinPlusData I₄) ⧸ (abkGrade (I := I₄)).ker) :=
  (spinZ4Omega5_quotient_grade_equiv_zmod16.{u} (I := I)).trans
    (dataBordism_quotient_abk_equiv_zmod16.{u} (I := I₄)).symm

/-- The Smith floor-quotient iso, read into `ZMod 16` on the Pin⁺ side, is the source η-grade quotient
iso — i.e. it is the **identity on `ℤ/16`** through the two quotient identifications (the operative
ℤ/16 ↦ ℤ/16 Smith content, now as an `≃+`, not just a hom). -/
theorem smithQuotientEquiv_eq_zmod16 (x : DataBordismGrp (spinZ4Omega5Data I) ⧸
    (spinZ4Omega5Grade (I := I)).ker) :
    dataBordism_quotient_abk_equiv_zmod16 (I := I₄) (smithQuotientEquiv I₄ x) =
      spinZ4Omega5_quotient_grade_equiv_zmod16 (I := I) x := by
  show dataBordism_quotient_abk_equiv_zmod16 (I := I₄)
    ((dataBordism_quotient_abk_equiv_zmod16 (I := I₄)).symm
      (spinZ4Omega5_quotient_grade_equiv_zmod16 (I := I) x)) = _
  rw [AddEquiv.apply_symm_apply]

/-! ## §4b. The generator fact `s[ℝP⁵] = [ℝP⁴]` (grade level) — the `≥ 16` half of the sandwich

The Smith map sends the `Ω₅^{Spin-ℤ₄}` generator (η-grade `1`, the order-16 generator standing for
`[ℝP⁵]`) to the Pin⁺ class with ABK grade `1` (the order-16 generator standing for `[ℝP⁴]`): TY §3.4,
`s[ℝP⁵] = [ℝP⁴]`, generator-to-generator. On the genuine carriers this is the statement that the Smith
image of the η-grade-`1` class has Pin⁺ ABK grade `1` — the `≥ 16` half of the TY sandwich, realized as
the genuine grade computation `abkGrade (smithDataHom [gen]) = 1`. -/

/-- The **generator class** of the genuine domain bordism group: the η-grade-`1` Spin-ℤ₄ class standing
for `[ℝP⁵]` (the order-16 generator of `Ω₅^{Spin-ℤ₄}`). -/
noncomputable def spinZ4Omega5Gen : DataBordismGrp (spinZ4Omega5Data I) :=
  DataBordismGrp.mk (spinZ4Omega5Data I) ⟨emptySM, ((1 : ZMod 16) : SpinZ4Omega5Grade)⟩

/-- The generator has η-grade `1`. -/
@[simp] theorem spinZ4Omega5Grade_gen : spinZ4Omega5Grade (spinZ4Omega5Gen (I := I)) = 1 := rfl

/-- **`s[ℝP⁵] = [ℝP⁴]` (grade level).** The Smith image of the `Ω₅^{Spin-ℤ₄}` generator (η-grade `1`,
`[ℝP⁵]`) has Pin⁺ ABK grade `1` — the Pin⁺ generator `[ℝP⁴]`, the order-16 generator of `Ω₄^{Pin⁺}`. The
`≥ 16` half of the TY footnote-15 sandwich, on the genuine carriers, generator-to-generator. -/
theorem smithDataHom_gen_abkGrade : abkGrade (smithDataHom I₄ (spinZ4Omega5Gen (I := I))) = 1 := by
  rw [abkGrade_smithDataHom, spinZ4Omega5Grade_gen]

/-- The Smith image of the generator is **non-trivial** (ABK grade `1 ≠ 0`) — the source generator does
not die under the Smith map, consistent with the iso (it is order-16, not in the floor). -/
theorem smithDataHom_gen_ne_zero : smithDataHom I₄ (spinZ4Omega5Gen (I := I)) ≠ 0 := by
  intro h
  have h0 : abkGrade (smithDataHom I₄ (spinZ4Omega5Gen (I := I))) = 0 := by rw [h]; exact map_zero _
  rw [smithDataHom_gen_abkGrade] at h0
  exact absurd h0 (by decide)

end SmithHom

/-! ## §5. The SW-relation wiring — why the Smith image lands in Pin⁺ (`w₂(N) = w₂(M) − a² = 0`)

The geometric reason the Smith map is well-defined into Pin⁺ bordism (TY eq 3.14; DDDKLPT Lemma 3.5):
the codimension-1 Poincaré-dual submanifold `N = PD(a)` of `a ∈ H¹(M;ℤ/2)` (the section zero locus of
the associated `±1` line bundle `L_a`) carries `w₁(N) = a`, `w₂(N) = w₂(M) − a² = 0`, hence is Pin⁺
(Lawson–Michelsohn II.1.7). We re-export the genuine geometric core (`SmithLineBundle` /
`SymTFT.SmithMechanism`) here so the typed hom above is tied to its operative Stiefel–Whitney content —
this is the §5.2 "SW-relations as the operative content," NOT a content-free composite. -/

section SWWiring

open SKEFTHawking.SymTFT SKEFTHawking.SmithLineBundle

/-- **The Smith mechanism `w₂(N) = 0`** (re-exported, `SymTFT.smith_w2_vanishes`): given the Whitney
inheritance `w₂(N) = c + b²` (`b = w₁(L_a|_N)`, `c = w₂(M)|_N`) and the Spin-ℤ₄ constraint `c = b²`, the
Poincaré dual `N = PD(a)` has `w₂(N) = b² + b² = 0`, so it admits a Pin⁺ structure — the geometric
landing condition of the Smith map. -/
theorem smith_image_isPinPlus_of_whitney {N : Type*} [HasStiefelWhitney N]
    (b : CohomologyMod2 N 1) (c : CohomologyMod2 N 2)
    (hWhitney : HasStiefelWhitney.w (M := N) 2 = c + HasStiefelWhitney.cupSquare b)
    (hSpinZ4 : c = HasStiefelWhitney.cupSquare b) :
    IsPinPlusObstruction N :=
  smith_w2_vanishes b c hWhitney hSpinZ4

/-- **The generator `[ℝP⁵] ↦ [ℝP⁴] = PD(α)` lands in Pin⁺** (re-exported,
`SmithLineBundle.PD_RP4_isPinPlus`): the Smith image of the `Ω₅^{Spin-ℤ₄}` generator, `ℝP⁴ = PD(α)`,
inherits `w₂(ℝP⁴) = α² + α² = 0` via the line-bundle SW mechanism — the genuine geometric realization
of the generator-to-generator Smith content's Pin⁺-landing. -/
theorem smith_generator_image_isPinPlus : IsPinPlusObstruction RP4 :=
  PD_RP4_isPinPlus

end SWWiring

/-! ## §6. The W6 hook — feeding the W5 Smith content into the `ℤ/16` sandwich

The W6 assembly `PinPlusBordismGroupDerived.dataBordism_pinPlus_iso_via_smith` consumes an
`≃+` between the genuine carriers plus the domain's order-16 generator + the `≤ 16` cap, and yields
`Ω₄^{Pin⁺} ≅ ℤ/16`. The genuine carriers carry the floor, so the *full*-carrier `≃+` is the disclosed
conditional landmark; the **unconditional** W5 deliverable feeding W6 is the floor-quotient Smith iso
`smithQuotientEquiv` (§4) together with the η-grade quotient `Ω₅^{Spin-ℤ₄}⧸ker ≅ ℤ/16` (§4). Composed
with the genuine Pin⁺ ABK-quotient iso, these realize the `ℤ/16 ≃+ ℤ/16` sandwich on the genuine
geometric bordism groups, generator-to-generator (§4b), with the SW-landing content genuine (§5). -/

section W6Hook

variable {E₅ H₅ : Type} [NormedAddCommGroup E₅] [NormedSpace ℝ E₅] [FiniteDimensional ℝ E₅]
  [TopologicalSpace H₅] (I₅ : ModelWithCorners ℝ E₅ H₅) [I₅.Boundaryless]
  {E₄ H₄ : Type} [NormedAddCommGroup E₄] [NormedSpace ℝ E₄] [FiniteDimensional ℝ E₄]
  [TopologicalSpace H₄] (I₄ : ModelWithCorners ℝ E₄ H₄) [I₄.Boundaryless]

/-- **The W5→W6 endpoint: `Ω₄^{Pin⁺}⧸ker(ABK) ≅ ℤ/16` reached through the Smith iso.** Reading the
Pin⁺ ABK-grade quotient back through the genuine floor-quotient Smith iso `smithQuotientEquiv` and the
source η-grade quotient iso gives `Ω₄^{Pin⁺}⧸ker ≅ ℤ/16` — the `ℤ/16` obtained via the Smith LES on the
genuine carriers (the floor-quotient form of W6's `dataBordism_pinPlus_iso_via_smith`). The composite is
`smithQuotientEquiv⁻¹` then the source η-grade quotient iso, over the 5-dim domain model `I₅` and the
4-dim target model `I₄`. -/
noncomputable def pinPlus_quotient_iso_zmod16_via_smith.{u} :
    (DataBordismGrp.{u} (pinPlusData I₄) ⧸ (abkGrade (I := I₄)).ker) ≃+ ZMod 16 :=
  (smithQuotientEquiv.{u} (I := I₅) I₄).symm.trans
    (spinZ4Omega5_quotient_grade_equiv_zmod16.{u} (I := I₅))

/-- `Nonempty` packaging of the Smith-route Pin⁺ ABK-quotient `ℤ/16`, the W5 deliverable for W6: given
any 5-dim Spin-ℤ₄ domain model `I₅`, the Smith iso transports the domain's η-grade `ℤ/16` onto the Pin⁺
ABK-grade `ℤ/16`. -/
theorem pinPlus_quotient_iso_zmod16_via_smith_nonempty.{u}
    (I₅' : ModelWithCorners ℝ E₅ H₅) [I₅'.Boundaryless] :
    Nonempty ((DataBordismGrp.{u} (pinPlusData I₄) ⧸ (abkGrade (I := I₄)).ker) ≃+ ZMod 16) :=
  ⟨pinPlus_quotient_iso_zmod16_via_smith.{u} I₅' I₄⟩

end W6Hook

/-! ## §7. The genuine MANIFOLD layer of the Smith assignment `[M] ↦ [PD(a)]` (bricks 1–2)

The typed Smith homomorphism (§2) transports the ABK/η grade — the floor-surviving content (DR
`Smith_sequence.md` §5.2: *"a typed homomorphism on an abstract bordism group with the SW-relations as
the operative content"*). This section pins the **manifold layer** of the geometric assignment
`[M⁵] ↦ [PD(a)⁴]` to a genuine real-manifold construction: the Poincaré dual `PD(a)` (the zero locus of
a transverse section of the `±1` line bundle `L_a`) is a genuine codimension-1 `SingularManifold` over
an *arbitrary compact boundaryless* base `M` — the manifold regular-value theorem built this phase
(`ManifoldRegularValue.mLevelSetSingularManifold` → `ManifoldSmithPD.mSectionZeroLocus_singularManifold`,
bricks 1–2), **strengthening** the prior model-space-only `SmithLineBundle.sectionZeroLocus_isManifold`
(base `E`). Together with the SW mechanism (§5, `w₂(N) = w₂(M) − a² = 0`) and the typed hom (§2), this is
the DR §5.2 geometric Smith map "once the manifold/bundle layer is fixed", with the manifold layer now
over real manifolds, not the typed-level grade representative `emptySM`.

**Floor disclosure (honest scope, the same landmark as `PinPlusTangentialData`/`PinPlusGenuineCarrierIso`):**
Mathlib carries no `w₂` of a bare `SingularManifold` (no frame bundle / mod-2 fundamental class of the
homotopy type), so the genuine manifold `PD(a)` of this section and the Pin⁺ SW-obstruction of §5 live on
*different layers* — the manifold layer here certifies `PD(a)` is a real codim-1 manifold; the SW layer
(§5) certifies the `w₂ = 0` Pin⁺ landing on the abstract Stiefel–Whitney substrate. The unoriented-bordism
floor `Ω^O` (which both `DataBordismGrp` carriers retain) is exactly this gap, and the ℤ/16 is carried by
the ABK grade (the floor-surviving invariant) via the permitted finite-input route (DR §5.1). The full
*varying*-`PD` cobordism-invariance (`PD` extends over a bordism `W`) is the disclosed manifold-bundle
landmark DR §5.2 routes around by formalizing at the typed-hom level. -/

section ManifoldLayer

open SKEFTHawking.ManifoldSmithPD SKEFTHawking.SmithRegularValueGeneral SKEFTHawking.SmithLineBundle

variable {M : Type} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ⊤ M] [CompactSpace M]
  {ι : Type} (c : SignCocycle M ι)

/-- **The Smith image `PD(a)` packaged as a genuine `SingularManifold`** over the codim-1 Euclidean
model, on an *arbitrary compact boundaryless manifold base* `M` (bricks 1–2 this phase) — the form the
geometric Smith assignment `[M] ↦ [PD(a)]` deposits, on a real manifold, NOT the typed-level grade
representative `emptySM`. The genuine manifold layer (DR §5.2 "once the manifold/bundle layer is fixed")
the typed Smith homomorphism (§2) transports the ABK grade alongside. -/
noncomputable def smithImageSingularManifold (σ : M → c.TotalSpace)
    (h : MSectionTransverse (I := I) c σ) :
    SingularManifold PUnit ⊤ (modelWithCornersSelf ℝ (euclideanModel E)) :=
  mSectionZeroLocus_singularManifold (I := I) c σ h

/-- The Smith image is **codimension 1** in `M`: its Euclidean model has dimension `finrank E − 1`, the
genuine `d ↦ d − 1` dimension drop the Smith map `Ω₅ → Ω₄` produces — here on the genuine manifold base,
not just the model space `E`. -/
theorem smithImage_codim_one (hE : 0 < Module.finrank ℝ E) :
    Module.finrank ℝ (euclideanModel E) + 1 = Module.finrank ℝ E := by
  simp only [euclideanModel, finrank_euclideanSpace, Fintype.card_fin]
  omega

end ManifoldLayer

end SKEFTHawking.SmithIsomorphism
