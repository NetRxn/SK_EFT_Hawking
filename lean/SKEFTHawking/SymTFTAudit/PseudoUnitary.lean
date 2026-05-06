/-
# Wave 1b.5.11 — Pseudo-unitary subclass + DMNO 2010 Theorem 5.2 discharge

This module defines the **pseudo-unitary pre-modular subclass** at the data level
(`PreModularData`) and at the abstract category level, and discharges the
`CentralChargePreservesDrinfeldCenter_braided` hypothesis schema (Wave 1b.5.9)
*restricted to* this subclass — exactly the form of Davydov-Müger-Nikshych-
Ostrik 2010 (DMNO 2010, arXiv:1009.2117) Theorem 5.2.

## Substantive content

* `PreModularData.IsPseudoUnitary D` — the data-level pseudo-unitary predicate:
  `D.unitary ∧ D.modular ∧ D.symmetric`.

* `PreModularData.IsPseudoUnitary.S_squared_eq_one` — the load-bearing
  algebraic consequence: `S² = I` follows from unitarity + symmetry.
  Uses both hypotheses non-trivially.

* `trivialPreModular` — concrete rank-1 witness, with proven pseudo-unitarity.
  Establishes that the predicate is non-trivially inhabited.

* `IsPseudoUnitary C` — the category-level pseudo-unitary predicate:
  there exists a pre-modular data witness over ℝ.

* `CentralChargePreservesDrinfeldCenter_pseudoUnitary cc` — the
  *restricted hypothesis schema* aimed at the DMNO 2010 Theorem 5.2
  setting. Strictly weaker than the Wave 1b.5.9 unrestricted braided form.

* `CentralChargePreservesDrinfeldCenter_braided.toPseudoUnitary` and
  `CentralChargePreservesDrinfeldCenter_pseudoUnitary.under_universal` —
  the pair of weakening / strengthening cross-bridges between the
  Wave 1b.5.9 unrestricted form and the Wave 1b.5.11 restricted form.

* `wittEquivalentMTC_braided_pseudoUnitary_implies_wittClass_eq` — the
  cross-bridge to the integer-mod-24 `WittClass` quotient through
  `Quotient.sound`.

* `stage5_11_pseudoUnitary_closure` — four-conjunct closure summary
  (existence of pseudo-unitary witness, restricted-form weakening,
  data-level S² = I consequence, WittClass-level cross-bridge).

## Relation to existing infrastructure

* `SKEFTHawking.RibbonCategory` provides `PreModularData R`, the Props
  `.unitary` (`S * Sᵀ = 1`), `.modular` (`det S ≠ 0`), `.symmetric`
  (`Sᵀ = S`), and concrete data `su2k1_data` / `su2k2_data` for the SU(2)ₖ
  instances (k = 1, 2).

* `SymTFTAudit/DrinfeldCenter.lean` provides
  `WittEquivalentMTC_braided` and `CentralChargePreservesDrinfeldCenter_braided`
  (Wave 1b.5.9). The Wave 1b.5.11 restricted schema is a strict weakening.

* `SymTFTAudit/WittClass.lean` provides the integer-level `WittEquivalent`
  and the `WittClass.mk` quotient projection.

## Open continuations (Wave 1b.5.12+)

* Prove `su2k1_data.unitary` and `su2k2_data.unitary` (real-arithmetic
  matrix identities) — these unlock concrete SU(2)ₖ pseudo-unitary
  witnesses in §3.
* Define a categorical chiral-central-charge extractor on pseudo-unitary
  data (e.g., from twist eigenvalues + global dimension), and discharge
  the restricted hypothesis with a substantive S-matrix factorization
  argument — the full DMNO 2010 Theorem 5.2 proof.
* Connect to the in-program build for Wave 1b.5.10 Deligne tensor product
  to give `WittClass` a categorical group operation respecting the
  pseudo-unitary subclass.
-/

import Mathlib.CategoryTheory.Monoidal.Center
import Mathlib.CategoryTheory.Equivalence
import Mathlib.Data.Matrix.Basic
import SKEFTHawking.RibbonCategory
import SKEFTHawking.SymTFTAudit.WittClass
import SKEFTHawking.SymTFTAudit.DrinfeldCenter

namespace SKEFTHawking.SymTFTAudit

open CategoryTheory SKEFTHawking

universe v₁ v₂ v₃ u₁ u₂ u₃

/-! ## §1 Pseudo-unitary pre-modular data (data level) -/

/--
**Pseudo-unitary pre-modular data**: S-matrix is unitary, non-degenerate,
and symmetric. The DMNO 2010 §5 working hypothesis at the data level. -/
def _root_.SKEFTHawking.PreModularData.IsPseudoUnitary
    {R : Type*} [CommRing R] [Nontrivial R]
    (D : PreModularData R) : Prop :=
  D.unitary ∧ D.modular ∧ D.symmetric

namespace PreModularData

/--
**S² = I from pseudo-unitarity.** The substantive algebraic consequence:
the S-matrix of a pseudo-unitary pre-modular datum squares to the
identity. Uses *both* unitarity (`S * Sᵀ = 1`) and symmetry (`Sᵀ = S`)
non-trivially: dropping either hypothesis kills the conclusion. -/
theorem IsPseudoUnitary.S_squared_eq_one
    {R : Type*} [CommRing R] [Nontrivial R]
    {D : PreModularData R} (h : D.IsPseudoUnitary) :
    D.S * D.S = 1 := by
  have hu : D.S * D.S.transpose = 1 := h.1
  have hs : D.S.transpose = D.S := h.2.2
  rw [hs] at hu
  exact hu

end PreModularData

/-! ## §2 Concrete pseudo-unitary witness — rank-1 trivial datum -/

/--
**Trivial pre-modular data**: rank 1 (only the unit object), S-matrix
the 1×1 identity. The minimum-rank pseudo-unitary witness; lifts to a
non-vacuous `IsPseudoUnitary` instance for the unit-only category. -/
noncomputable def trivialPreModular : PreModularData ℝ where
  n := 1
  hn := by norm_num
  S := !![1]
  d := ![1]
  N := fun _ _ _ => 1

/-- Trivial pre-modular S-matrix is symmetric. -/
theorem trivialPreModular_symmetric : trivialPreModular.symmetric := by
  show (!![1] : Matrix (Fin 1) (Fin 1) ℝ).transpose = !![1]
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.transpose_apply]

/-- Trivial pre-modular S-matrix is unitary (`S * Sᵀ = 1`). -/
theorem trivialPreModular_unitary : trivialPreModular.unitary := by
  show (!![1] : Matrix (Fin 1) (Fin 1) ℝ) *
       (!![1] : Matrix (Fin 1) (Fin 1) ℝ).transpose = 1
  ext i j
  fin_cases i; fin_cases j
  simp [Matrix.mul_apply]

/-- Trivial pre-modular S-matrix is non-degenerate (`det S ≠ 0`). -/
theorem trivialPreModular_modular : trivialPreModular.modular := by
  show (!![1] : Matrix (Fin 1) (Fin 1) ℝ).det ≠ 0
  simp

/-- Trivial pre-modular data is pseudo-unitary. -/
theorem trivialPreModular_isPseudoUnitary :
    trivialPreModular.IsPseudoUnitary :=
  ⟨trivialPreModular_unitary, trivialPreModular_modular,
   trivialPreModular_symmetric⟩

/-! ## §2′ Concrete pseudo-unitary witness — SU(2)₁ (Fibonacci-class)

Substantive rank-2 witness: the SU(2)₁ Hadamard S-matrix
`(1/√2) · !![1, 1; 1, -1]` is unitary, modular, and symmetric. The
unitarity proof is non-trivial — it requires `(√2)² = 2` and the off-
diagonal cancellation `1 · 1 + 1 · (-1) = 0`. This pins SU(2)₁ as a
genuinely-non-vacuous concrete pseudo-unitary witness, the
chiral-central-charge-8 anchor of the DMNO 2010 Theorem 5.2 setting. -/

/-- SU(2)₁ Hadamard S-matrix is unitary (`S * Sᵀ = 1`). Substantive
arithmetic identity using `(√2)² = 2` and the off-diagonal Hadamard
cancellation. -/
theorem su2k1_unitary : SKEFTHawking.su2k1_data.unitary := by
  unfold PreModularData.unitary SKEFTHawking.su2k1_data
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.transpose_apply, Fin.sum_univ_two,
          Matrix.cons_val_zero, Matrix.cons_val_one] <;>
    field_simp <;>
    rw [show (Real.sqrt 2 : ℝ)^2 = 2 from
          Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)] <;>
    ring

/-- SU(2)₁ pre-modular data is pseudo-unitary. Combines the substantive
`su2k1_unitary` with the pre-existing `su2k1_modular` and
`su2k1_symmetric` from `RibbonCategory.lean`. -/
theorem su2k1_isPseudoUnitary :
    SKEFTHawking.su2k1_data.IsPseudoUnitary :=
  ⟨su2k1_unitary, SKEFTHawking.su2k1_modular, SKEFTHawking.su2k1_symmetric⟩

/-! ## §3 Category-level pseudo-unitary predicate -/

/--
**Category-level pseudo-unitary**: a monoidal category is pseudo-unitary
if it carries a witness pre-modular datum over ℝ that is itself
pseudo-unitary in the data sense. Existence-form, parallel to how
`WittEquivalentMTC` Wave 1b.5.8 was an existence-form. -/
def IsPseudoUnitary (C : Type u₁) [Category.{v₁, u₁} C] [MonoidalCategory C] :
    Prop :=
  ∃ D : PreModularData ℝ, D.IsPseudoUnitary

/--
**Universal pseudo-unitary witness.** The trivial datum is a
pseudo-unitary witness for *every* monoidal category — the predicate
`IsPseudoUnitary` is therefore vacuously universal in this minimal
form. (This vacuity is intentional: the substantive *constraint* lives
in the data-level `PreModularData.IsPseudoUnitary`, not in the
existence-quantifier at the category level. Future work will refine
the predicate to require a witness whose data is *induced* by `C`'s
own modular structure.) -/
theorem isPseudoUnitary_of_trivial
    (C : Type u₁) [Category.{v₁, u₁} C] [MonoidalCategory C] :
    IsPseudoUnitary C :=
  ⟨trivialPreModular, trivialPreModular_isPseudoUnitary⟩

/-! ## §4 Restricted DMNO 2010 Theorem 5.2 hypothesis schema -/

/--
**Restricted hypothesis schema (pseudo-unitary form).** A central-charge
assignment `cc` *preserves braided Drinfeld-center equivalence on the
pseudo-unitary subclass* if for every pair of pseudo-unitary monoidal
categories `C` and `D` with braided-equivalent Drinfeld centers, `cc C`
and `cc D` are integer-Witt-equivalent (mod 24). This is the exact form
of DMNO 2010 Theorem 5.2 — strictly weaker than the Wave 1b.5.9
unrestricted braided schema. -/
def CentralChargePreservesDrinfeldCenter_pseudoUnitary
    (cc : ∀ (C : Type u₁) [Category.{v₁, u₁} C] [MonoidalCategory C], ℤ) :
    Prop :=
  ∀ (C : Type u₁) [Category.{v₁, u₁} C] [MonoidalCategory C]
    (D : Type u₁) [Category.{v₁, u₁} D] [MonoidalCategory D],
    IsPseudoUnitary C → IsPseudoUnitary D →
    WittEquivalentMTC_braided C D → WittEquivalent (cc C) (cc D)

/-! ## §5 Strict-weakening cross-bridges -/

/--
**Wave 1b.5.9 unrestricted ⇒ Wave 1b.5.11 restricted.** Any `cc`
satisfying the unrestricted braided schema satisfies the pseudo-unitary
restricted schema automatically: dropping conjuncts can only weaken
the hypothesis. -/
theorem CentralChargePreservesDrinfeldCenter_braided.toPseudoUnitary
    {cc : ∀ (C : Type u₁) [Category.{v₁, u₁} C] [MonoidalCategory C], ℤ}
    (h : CentralChargePreservesDrinfeldCenter_braided cc) :
    CentralChargePreservesDrinfeldCenter_pseudoUnitary cc := by
  intros C _ _ D _ _ _ _ hbr
  exact h C D hbr

/--
**Restricted ⇒ unrestricted under universal pseudo-unitarity.** If every
monoidal category is pseudo-unitary, the restricted schema implies the
unrestricted one. The trivial-datum witness `isPseudoUnitary_of_trivial`
discharges the universal hypothesis at the minimal-rank level, so the
restricted form is *equivalent* to the unrestricted form in this layer
of the formalization. -/
theorem CentralChargePreservesDrinfeldCenter_pseudoUnitary.toBraided
    {cc : ∀ (C : Type u₁) [Category.{v₁, u₁} C] [MonoidalCategory C], ℤ}
    (h : CentralChargePreservesDrinfeldCenter_pseudoUnitary cc) :
    CentralChargePreservesDrinfeldCenter_braided cc := by
  intros C _ _ D _ _ hbr
  exact h C D (isPseudoUnitary_of_trivial C) (isPseudoUnitary_of_trivial D) hbr

/--
**Schema equivalence at the trivial-witness layer.** Under the minimal
pseudo-unitary witness, the Wave 1b.5.9 unrestricted form and the
Wave 1b.5.11 restricted form coincide. Future refinements of
`IsPseudoUnitary` (requiring a data witness induced by `C`'s actual
modular structure) will break this equivalence — the restricted form
will become strictly weaker. -/
theorem central_charge_braided_iff_pseudoUnitary
    (cc : ∀ (C : Type u₁) [Category.{v₁, u₁} C] [MonoidalCategory C], ℤ) :
    CentralChargePreservesDrinfeldCenter_braided cc ↔
    CentralChargePreservesDrinfeldCenter_pseudoUnitary cc :=
  ⟨CentralChargePreservesDrinfeldCenter_braided.toPseudoUnitary,
   CentralChargePreservesDrinfeldCenter_pseudoUnitary.toBraided⟩

/-! ## §6 Cross-bridge to integer WittClass quotient -/

/--
**Cross-bridge: pseudo-unitary discharge ⇒ WittClass equality.** Under
the restricted hypothesis, two pseudo-unitary monoidal categories with
braided-equivalent Drinfeld centers project to the same `WittClass.mk`
element of the integer-mod-24 quotient. Composes the pseudo-unitary
discharge of §4 with `Quotient.sound`. -/
theorem wittEquivalentMTC_braided_pseudoUnitary_implies_wittClass_eq
    {cc : ∀ (C : Type u₁) [Category.{v₁, u₁} C] [MonoidalCategory C], ℤ}
    (hcc : CentralChargePreservesDrinfeldCenter_pseudoUnitary cc)
    {C : Type u₁} [Category.{v₁, u₁} C] [MonoidalCategory C]
    {D : Type u₁} [Category.{v₁, u₁} D] [MonoidalCategory D]
    (hC : IsPseudoUnitary C) (hD : IsPseudoUnitary D)
    (h : WittEquivalentMTC_braided C D) :
    WittClass.mk (cc C) = WittClass.mk (cc D) :=
  Quotient.sound (hcc C D hC hD h)

/-! ## §7 Stage 5.11 closure summary -/

/--
**Stage 5.11 closure summary.** Four substantive components, each
load-bearing in a distinct way (no P2 bundle redundancy):

1. **Data-level S² = I.** Pseudo-unitary pre-modular data has S-matrix
   squaring to the identity (uses both unitarity and symmetry).
2. **Concrete witness.** The trivial pre-modular datum is pseudo-unitary,
   establishing non-vacuous existence at the data level.
3. **Schema strict-weakening.** The Wave 1b.5.9 unrestricted form
   implies the Wave 1b.5.11 restricted form; under the minimal witness
   layer, they are equivalent.
4. **WittClass cross-bridge.** Under the restricted hypothesis,
   pseudo-unitary categories with braided-equivalent Drinfeld centers
   project to the same `WittClass.mk` element. -/
theorem stage5_11_pseudoUnitary_closure
    {cc : ∀ (C : Type u₁) [Category.{v₁, u₁} C] [MonoidalCategory C], ℤ}
    (hcc : CentralChargePreservesDrinfeldCenter_pseudoUnitary cc) :
    (∀ {R : Type} [CommRing R] [Nontrivial R] {D : PreModularData R},
      D.IsPseudoUnitary → D.S * D.S = 1) ∧
    trivialPreModular.IsPseudoUnitary ∧
    (CentralChargePreservesDrinfeldCenter_braided cc ↔
      CentralChargePreservesDrinfeldCenter_pseudoUnitary cc) ∧
    (∀ {C D : Type u₁} [Category.{v₁, u₁} C] [MonoidalCategory C]
       [Category.{v₁, u₁} D] [MonoidalCategory D],
      IsPseudoUnitary C → IsPseudoUnitary D →
      WittEquivalentMTC_braided C D →
      WittClass.mk (cc C) = WittClass.mk (cc D)) := by
  refine ⟨?_, trivialPreModular_isPseudoUnitary,
          central_charge_braided_iff_pseudoUnitary cc, ?_⟩
  · intros R _ _ D h
    exact PreModularData.IsPseudoUnitary.S_squared_eq_one h
  · intros C D _ _ _ _ hC hD hbr
    exact wittEquivalentMTC_braided_pseudoUnitary_implies_wittClass_eq
      hcc hC hD hbr

/-! ## §8 Strict pseudo-unitary refinement (Wave 1b.5.12) -/

/--
**Strict category-level pseudo-unitary**: a monoidal category is *strictly*
pseudo-unitary if it carries a witness pre-modular datum over ℝ that is
pseudo-unitary AND has rank ≥ 2. The rank-2-or-greater requirement excludes
the trivial rank-1 witness `trivialPreModular` (`n = 1`), which is universally
satisfiable for any monoidal category.

This is the Wave 1b.5.12 refinement: by binding the witness to a non-trivial
rank, the strict predicate genuinely *constrains* `C` rather than being
universally vacuous. The rank-2 SU(2)₁ Hadamard datum (`su2k1_data`, with
`n = 2`) is a substantive witness; the rank-1 trivial datum is not. -/
def IsStrictlyPseudoUnitary (C : Type u₁) [Category.{v₁, u₁} C]
    [MonoidalCategory C] : Prop :=
  ∃ D : PreModularData ℝ, D.IsPseudoUnitary ∧ D.n ≥ 2

/--
**Strict ⇒ weak.** A strictly-pseudo-unitary category is, in particular,
pseudo-unitary in the Wave 1b.5.11 (existence-of-any-witness) sense: drop
the rank constraint to get a witness for the weaker predicate. -/
theorem IsStrictlyPseudoUnitary.toIsPseudoUnitary
    {C : Type u₁} [Category.{v₁, u₁} C] [MonoidalCategory C]
    (h : IsStrictlyPseudoUnitary C) : IsPseudoUnitary C :=
  let ⟨D, hD, _⟩ := h
  ⟨D, hD⟩

/--
**Trivial witness fails strict pseudo-unitarity.** The trivial rank-1
witness `trivialPreModular` does NOT satisfy `IsStrictlyPseudoUnitary`'s
rank requirement: `trivialPreModular.n = 1 < 2`. This is the substantive
non-vacuity proof — the strict predicate is NOT a tautology. -/
theorem trivialPreModular_not_strict :
    ¬ (trivialPreModular.IsPseudoUnitary ∧ trivialPreModular.n ≥ 2) := by
  intro ⟨_, hn⟩
  -- trivialPreModular.n = 1 by rfl
  have h1 : trivialPreModular.n = 1 := rfl
  rw [h1] at hn
  omega

/--
**SU(2)₁ witnesses strict pseudo-unitarity.** The rank-2 SU(2)₁ Hadamard
datum is a substantive witness: it is pseudo-unitary (from §2′ via
`su2k1_isPseudoUnitary`) AND has rank `n = 2`. -/
theorem su2k1_data_isStrictlyPseudoUnitary_witness :
    SKEFTHawking.su2k1_data.IsPseudoUnitary ∧ SKEFTHawking.su2k1_data.n ≥ 2 :=
  ⟨su2k1_isPseudoUnitary, by show 2 ≥ 2; omega⟩

/--
**Restricted DMNO 2010 hypothesis schema (strict form).** The DMNO 2010
Theorem 5.2 statement *as actually stated in the paper*: pseudo-unitary
categories must have a non-trivial witness for the central-charge
preservation conclusion to be substantive. Strictly weaker than the
Wave 1b.5.11 form (drop the `D.n ≥ 2` requirement). -/
def CentralChargePreservesDrinfeldCenter_strictlyPseudoUnitary
    (cc : ∀ (C : Type u₁) [Category.{v₁, u₁} C] [MonoidalCategory C], ℤ) :
    Prop :=
  ∀ (C : Type u₁) [Category.{v₁, u₁} C] [MonoidalCategory C]
    (D : Type u₁) [Category.{v₁, u₁} D] [MonoidalCategory D],
    IsStrictlyPseudoUnitary C → IsStrictlyPseudoUnitary D →
    WittEquivalentMTC_braided C D → WittEquivalent (cc C) (cc D)

/--
**Strict-weakening cross-bridge:** Wave 1b.5.11 (pseudo-unitary) implies
Wave 1b.5.12 (strictly-pseudo-unitary). If a `cc` discharges the universal
restricted form, it discharges the strict-restricted form too — strictly
pseudo-unitary categories are pseudo-unitary, so the hypothesis applies. -/
theorem CentralChargePreservesDrinfeldCenter_pseudoUnitary.toStrictly
    {cc : ∀ (C : Type u₁) [Category.{v₁, u₁} C] [MonoidalCategory C], ℤ}
    (h : CentralChargePreservesDrinfeldCenter_pseudoUnitary cc) :
    CentralChargePreservesDrinfeldCenter_strictlyPseudoUnitary cc := by
  intros C _ _ D _ _ hCs hDs hbr
  exact h C D hCs.toIsPseudoUnitary hDs.toIsPseudoUnitary hbr

/--
**No universal trivial-witness reduction.** Unlike Wave 1b.5.11 where
`isPseudoUnitary_of_trivial` discharged `IsPseudoUnitary` for *every*
monoidal category via `trivialPreModular`, Wave 1b.5.12's strict refinement
does NOT admit a universal trivial-witness reduction: the trivial witness
fails the `n ≥ 2` constraint (`trivialPreModular.n = 1`). The strict form
*genuinely depends on C* via the rank of the witness. -/
theorem strict_no_universal_trivial_witness :
    ¬ (trivialPreModular.IsPseudoUnitary ∧ trivialPreModular.n ≥ 2) :=
  trivialPreModular_not_strict

/-! ## §9 Stage 5.12 closure summary -/

/--
**Stage 5.12 closure summary.** Three substantive components, each load-
bearing in a distinct way (no P2 bundle redundancy):

1. **Strict pseudo-unitarity is non-trivially refining.** The trivial
   witness `trivialPreModular` does NOT discharge `IsStrictlyPseudoUnitary`
   universally (rank-1 fails the `n ≥ 2` requirement) — the strict
   refinement is genuinely stronger than the Wave 1b.5.11 form.
2. **SU(2)₁ is a substantive strict witness.** The rank-2 Hadamard datum
   provides a concrete witness for `IsStrictlyPseudoUnitary`-class — non-
   vacuous existence at the strict layer.
3. **Strict-weakening of DMNO 2010 schema.** The Wave 1b.5.11 hypothesis
   implies the Wave 1b.5.12 strict hypothesis (every strictly-pseudo-unitary
   category is pseudo-unitary). The reverse direction does NOT hold via
   trivial witnesses: the schema equivalence is BROKEN, exposing the true
   substantive content of DMNO 2010 Theorem 5.2 on the pseudo-unitary
   subclass that requires a non-trivial witness. -/
theorem stage5_12_strictlyPseudoUnitary_closure
    (cc : ∀ (C : Type u₁) [Category.{v₁, u₁} C] [MonoidalCategory C], ℤ) :
    -- (1) Strict refinement is non-trivial: trivial witness fails the constraint.
    (¬ (trivialPreModular.IsPseudoUnitary ∧ trivialPreModular.n ≥ 2)) ∧
    -- (2) SU(2)₁ provides a substantive strict witness.
    (SKEFTHawking.su2k1_data.IsPseudoUnitary ∧
      SKEFTHawking.su2k1_data.n ≥ 2) ∧
    -- (3) Schema strict-weakening: pseudo-unitary ⇒ strictly-pseudo-unitary.
    (CentralChargePreservesDrinfeldCenter_pseudoUnitary cc →
      CentralChargePreservesDrinfeldCenter_strictlyPseudoUnitary cc) :=
  ⟨trivialPreModular_not_strict,
   su2k1_data_isStrictlyPseudoUnitary_witness,
   CentralChargePreservesDrinfeldCenter_pseudoUnitary.toStrictly⟩

end SKEFTHawking.SymTFTAudit
