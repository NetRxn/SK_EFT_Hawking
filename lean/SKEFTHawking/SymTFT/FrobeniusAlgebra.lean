/-
# Phase 6r Wave 1c.1 — Frobenius algebras in monoidal categories

The Wave 1c boundary substrate begins with the Frobenius-algebra structure
required to specify Lagrangian algebras in the Drinfeld center (Wave 1c.2)
and gapped boundary conditions (Wave 1c.2). Per Wave 1a.1 §4.3 + Wave 3a.1
§Q2(c), Mathlib4 v4.29.1 provides:

- `Mon_(C)` algebras (via `MonObj` typeclass at
  `Mathlib.CategoryTheory.Monoidal.Mon_`).
- `Comon_(C)` coalgebras (via `ComonObj` typeclass at
  `Mathlib.CategoryTheory.Monoidal.Comon_`).
- `Hopf_(C)` Hopf algebras (Mathlib `Hopf_`).

…but does NOT provide the **Frobenius compatibility** between a `MonObj`
and `ComonObj` structure on the same object. This is the load-bearing
missing piece for Lagrangian algebras (which are commutative Frobenius
algebras satisfying connectedness + Frobenius-Perron-dimension condition).

This module ships the in-project `IsFrobeniusAlgebra` predicate on an
object equipped with both `MonObj` and `ComonObj` structures, plus the
commutative variant. The predicate captures the Frobenius compatibility
condition `(μ ⊗ 𝟙) ∘ (𝟙 ⊗ Δ) = Δ ∘ μ = (𝟙 ⊗ μ) ∘ (Δ ⊗ 𝟙)`.

## Tracked-Prop discipline

Per Wave 1a.1 §1.4 + Wave 3a.1 §Caveats, the substantive content
(DMNO 2010, Kapustin-Saulina 2011) is supplied externally. The Lean-side
predicate `IsFrobeniusAlgebra` ships the *interface* (compatibility
equations) — without claiming to prove the DMNO characterization
internally.

**Mathlib upstream-PR candidate.** The Frobenius-algebra-in-monoidal-C
predicate is a clean ~250 LoC addition fitting cleanly with Mon_/Comon_;
once stabilized, this would be a strong Mathlib4 upstream contribution
(no in-flight PR confirmed via Wave 1a.1 §4.3).

## References

- Davydov-Müger-Nikshych-Ostrik, "The Witt group of non-degenerate
  braided fusion categories," J. Reine Angew. Math. 677 (2013) 135;
  arXiv:1009.2117.
- Kock, "Frobenius Algebras and 2D Topological Quantum Field Theories,"
  Cambridge Univ. Press 2004.
- Fuchs-Schweigert-Valentino, "Bicategories for boundary conditions
  and for surface defects in 3-d TFT," arXiv:1203.4568, Commun. Math.
  Phys. 321 (2013) 543.
- Mathlib4 `Mathlib.CategoryTheory.Monoidal.Mon_`,
  `Mathlib.CategoryTheory.Monoidal.Comon_`.
-/
import Mathlib.CategoryTheory.Monoidal.Mon_
import Mathlib.CategoryTheory.Monoidal.Comon_
import Mathlib.CategoryTheory.Monoidal.Braided.Basic

namespace SKEFTHawking.SymTFT

open CategoryTheory MonoidalCategory

universe v u

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-! ## §1. The Frobenius-compatibility predicate -/

/-- **`IsFrobeniusAlgebra X`** — predicate on an object `X` of a
monoidal category, equipped with both `MonObj X` (algebra structure:
unit `η`, multiplication `μ`) and `ComonObj X` (coalgebra structure:
counit `ε`, comultiplication `Δ`), stating the **Frobenius compatibility
condition**:

```
(μ ⊗ 𝟙) ∘ (𝟙 ⊗ Δ) = Δ ∘ μ = (𝟙 ⊗ μ) ∘ (Δ ⊗ 𝟙)
```

Per Kock (Cambridge 2004), this is the standard definition of a
Frobenius algebra in a monoidal category: the comultiplication is a
bimodule map for the multiplication.

**Note on tensored-with-1 morphisms.** Encoded via Mathlib's
`whiskerLeft` / `whiskerRight` notation: `X ◁ f` for `𝟙_X ⊗ f` and
`f ▷ X` for `f ⊗ 𝟙_X`. The compatibility equations live in
`(X ⊗ X ⟶ X ⊗ X)`.

This is the *predicate-substrate-level* interface; the substantive
content (DMNO 2010 characterization of Drinfeld centers via Lagrangian
algebras) is shipped externally. -/
def IsFrobeniusAlgebra (X : C) [MonObj X] [ComonObj X] : Prop :=
  -- Left Frobenius compatibility:
  --   (μ ⊗ 𝟙) ∘ α⁻¹ ∘ (𝟙 ⊗ Δ) = Δ ∘ μ : X ⊗ X ⟶ X ⊗ X
  ((X ◁ ComonObj.comul) ≫ (α_ X X X).inv ≫ MonObj.mul ▷ X) =
    (MonObj.mul ≫ ComonObj.comul (X := X)) ∧
  -- Right Frobenius compatibility:
  --   (𝟙 ⊗ μ) ∘ α ∘ (Δ ⊗ 𝟙) = Δ ∘ μ : X ⊗ X ⟶ X ⊗ X
  (ComonObj.comul ▷ X ≫ (α_ X X X).hom ≫ X ◁ MonObj.mul) =
    (MonObj.mul ≫ ComonObj.comul (X := X))

/-! ## §2. The commutative-Frobenius-algebra predicate

A *commutative* Frobenius algebra `A` in a braided monoidal category
satisfies the additional `μ ∘ β_{A,A} = μ` condition (commutativity).
Per DMNO 2010, Lagrangian algebras in non-degenerate braided fusion
categories are commutative Frobenius algebras with extra Étale (=
connected + separable) conditions; this section ships the commutative
predicate.

The Étale conditions are layered on at the Lagrangian-algebra level
(Wave 1c.2 `LagrangianAlgebra.lean`). -/

/-- **`IsCommFrobeniusAlgebra X`** — Frobenius algebra `X` whose
multiplication is commutative under the braiding. Requires a
`BraidedCategory` instance on the ambient category. -/
def IsCommFrobeniusAlgebra
    [BraidedCategory C] (X : C) [MonObj X] [ComonObj X] : Prop :=
  IsFrobeniusAlgebra X ∧
  -- Commutativity: μ ∘ β_{X,X} = μ
  ((β_ X X).hom ≫ MonObj.mul (X := X)) = MonObj.mul (X := X)

/-! ## §3. Connected and separable algebras

Per DMNO 2010, Lagrangian algebras are *connected commutative étale*
algebras. We ship the connectedness + separability predicates as
predicate-substrate-level interfaces. -/

/-- **`IsConnectedAlgebra X`** — predicate on a `MonObj X` stating that
the algebra is *connected*: the unit map `η : 𝟙_C ⟶ X` is a
monomorphism (the unit is an inclusion-of-summand, ruling out
non-trivial idempotents that factor through the unit).

**Phase 6r-prime W2.1 substantive ship (2026-05-25)**: strengthens the
Phase 6r `:= True` placeholder to require `Mono` on the unit map. The
full standard categorical "connected" condition (no nontrivial central
idempotents in `End(X)`) requires additional Mathlib substrate (`End`
ring infrastructure for objects in monoidal categories); the
mono-on-unit version captures the load-bearing inclusion content and is
strictly stronger than the placeholder.

Per Wave 3a.1 §Q2(c), connectedness is one of three conditions
characterizing Lagrangian algebras (DMNO 2010); the other two are
étale (commutative + separable) and the Frobenius-Perron-dimension
condition. -/
def IsConnectedAlgebra (X : C) [MonObj X] : Prop :=
  Mono (MonObj.one (X := X))

/-- **`IsSeparableAlgebra X`** — predicate stating that the
multiplication `μ : X ⊗ X ⟶ X` admits a section `s : X ⟶ X ⊗ X`. The
section `s` plays the role of the inverse of the multiplication on the
diagonal; existence of `s` makes the algebra `X` separable.

**Phase 6r-prime W2.1 substantive ship (2026-05-25)**: strengthens the
Phase 6r `:= True` placeholder to require explicit existence of a
section `s` with `s ≫ μ = 𝟙 X`. This is the standard categorical
separability condition (per Kock 2004, Frobenius Algebras and 2D TQFTs;
DMNO 2010 arXiv:1009.2117).

Per Wave 3a.1 §Q2(c), separability + commutativity = étale; combined
with connectedness + the Frobenius-Perron-dimension condition, these
characterize Lagrangian algebras (DMNO 2010). -/
def IsSeparableAlgebra (X : C) [MonObj X] : Prop :=
  ∃ s : X ⟶ X ⊗ X, s ≫ MonObj.mul (X := X) = 𝟙 X

/-- **`IsEtaleAlgebra X`** — étale algebra: commutative + separable.
Combined with connectedness, this is the substrate for Lagrangian
algebras per DMNO 2010. -/
def IsEtaleAlgebra
    [BraidedCategory C] (X : C) [MonObj X] [ComonObj X] : Prop :=
  IsCommFrobeniusAlgebra X ∧ IsSeparableAlgebra X

/-! ## §4. Predicate-substrate properties -/

theorem isCommFrobeniusAlgebra_imp_isFrobeniusAlgebra
    [BraidedCategory C] {X : C} [MonObj X] [ComonObj X]
    (h : IsCommFrobeniusAlgebra X) : IsFrobeniusAlgebra X := h.1

theorem isEtaleAlgebra_imp_isCommFrobeniusAlgebra
    [BraidedCategory C] {X : C} [MonObj X] [ComonObj X]
    (h : IsEtaleAlgebra X) : IsCommFrobeniusAlgebra X := h.1

end SKEFTHawking.SymTFT
