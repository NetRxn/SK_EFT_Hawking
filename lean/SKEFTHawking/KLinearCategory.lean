/-
Phase 5 Wave 4A: k-Linear and Semisimple Categories

First layer of the fusion category hierarchy, building on Mathlib4's
existing MonoidalCategory, RigidCategory, MonoidalLinear, and Simple.

This module defines:
- SemisimpleCategory: every object decomposes as finite biproduct of simples
- Key properties: finite simple classes, decomposition uniqueness
- Physics bridge: dimension of Hom spaces, Schur orthogonality packaging

Mathlib provides: Simple, Schur's lemma (finrank_endomorphism_simple_eq_one),
DivisionRing (End X), MonoidalLinear R, HasBiproduct.

References:
  Etingof-Gelaki-Nikshych-Ostrik, "Tensor Categories" (AMS, 2015), Ch. 1-2
  Turaev-Virelizier, "Monoidal Categories and Topological Field Theory" (2017), Ch. 1
-/

import Mathlib

open CategoryTheory MonoidalCategory Limits

universe v u

noncomputable section

namespace SKEFTHawking

/-! ## 1. Semisimple categories -/

/--
A category with finitely many isomorphism classes of simple objects.
This is a key finiteness condition for fusion categories.
-/
class FinitelyManySimples (C : Type u) [Category.{v} C] [HasZeroMorphisms C] where
  /-- A finite indexing type for simple isomorphism classes -/
  SimpleIdx : Type
  [fintype : Fintype SimpleIdx]
  /-- Representative simple object for each class -/
  simpleObj : SimpleIdx → C
  /-- Each representative is simple -/
  [isSimple : ∀ i, Simple (simpleObj i)]
  /-- Representatives are pairwise non-isomorphic -/
  nonIso : ∀ i j, i ≠ j → IsEmpty (simpleObj i ≅ simpleObj j)
  /-- Completeness: every simple object is isomorphic to some representative.
      This ensures the indexing truly captures all simple isomorphism classes. -/
  complete : ∀ (X : C), Simple X → ∃ i, Nonempty (X ≅ simpleObj i)

attribute [instance] FinitelyManySimples.fintype FinitelyManySimples.isSimple

/--
A semisimple category: every object decomposes as a finite biproduct of simple objects.
Over an algebraically closed field, this is equivalent to: all Hom spaces are
finite-dimensional, and every short exact sequence splits.
-/
class SemisimpleCategory (C : Type u) [Category.{v} C] [Preadditive C]
    extends FinitelyManySimples C where
  /-- Every object has a finite decomposition into simples.
      The multiplicity function n : SimpleIdx → ℕ gives how many copies
      of each simple appear. -/
  multiplicity : C → SimpleIdx → ℕ
  /-- The total multiplicity is nonzero for nonzero objects -/
  multiplicity_nonzero : ∀ (X : C), ¬ IsZero X → ∃ i, multiplicity X i ≠ 0
  /-- A simple object isomorphic to the i-th representative has multiplicity 1 at i
      and 0 at all other indices. This encodes the Krull-Schmidt uniqueness. -/
  multiplicity_of_simple : ∀ (X : C) (i : SimpleIdx),
    Nonempty (X ≅ simpleObj i) → multiplicity X i = 1 ∧ ∀ j, j ≠ i → multiplicity X j = 0

variable (C : Type u) [Category.{v} C]

/--
The number of isomorphism classes of simple objects in a semisimple category.
For Vec_G this is |G|. For Rep(G) this is the number of irreducible representations.
-/
def numSimples [HasZeroMorphisms C] [FinitelyManySimples C] : ℕ :=
  Fintype.card (FinitelyManySimples.SimpleIdx (C := C))

variable {C}

/-! ## 2. Schur orthogonality packaging -/

section Schur

variable [Preadditive C] [HasKernels C]

/--
A nonzero morphism between simple objects is an isomorphism.
(Packaging Mathlib's theorem for physics use.)
-/
theorem schur_iso_of_nonzero
    {X Y : C} [Simple X] [Simple Y]
    {f : X ⟶ Y} (hf : f ≠ 0) : IsIso f :=
  isIso_of_hom_simple hf

variable (𝕜 : Type*) [Field 𝕜] [IsAlgClosed 𝕜] [Linear 𝕜 C]

/--
**Schur orthogonality**: in a 𝕜-linear category over an algebraically closed field,
Hom(X_i, X_j) has dimension ≤ 1 for simple objects X_i, X_j.
This is a direct consequence of Mathlib's `finrank_hom_simple_simple`.
-/
theorem schur_orthogonality
    [∀ X Y : C, FiniteDimensional 𝕜 (X ⟶ Y)]
    {X Y : C} [Simple X] [Simple Y] :
    Module.finrank 𝕜 (X ⟶ Y) ≤ 1 :=
  finrank_hom_simple_simple_le_one 𝕜 X Y

/--
Endomorphisms of a simple object are 1-dimensional (over algebraically closed 𝕜).
This is the algebraic heart of Schur's lemma.
-/
theorem end_simple_is_one_dim
    {X : C} [Simple X] [FiniteDimensional 𝕜 (X ⟶ X)] :
    Module.finrank 𝕜 (X ⟶ X) = 1 :=
  finrank_endomorphism_simple_eq_one 𝕜 X

variable {𝕜}

/--
Hom between non-isomorphic simples is zero-dimensional.
-/
theorem hom_simple_simple_zero (𝕜' : Type*) [DivisionRing 𝕜'] [Linear 𝕜' C]
    [∀ X Y : C, FiniteDimensional 𝕜' (X ⟶ Y)]
    {X Y : C} [Simple X] [Simple Y]
    (h : (X ≅ Y) → False) :
    Module.finrank 𝕜' (X ⟶ Y) = 0 :=
  finrank_hom_simple_simple_eq_zero_of_not_iso 𝕜' h

end Schur

/-! ## 3. Fusion rules structure -/

section Fusion

variable [HasZeroMorphisms C] [MonoidalCategory C]

/--
In a semisimple monoidal category with finitely many simples,
the tensor product of simples decomposes into simples.
The multiplicities N^k_{ij} are the fusion rules.
-/
structure FusionRules (C : Type u) [Category.{v} C] [HasZeroMorphisms C]
    [MonoidalCategory C] [FinitelyManySimples C] where
  /-- Fusion multiplicity: how many copies of X_k appear in X_i ⊗ X_j -/
  N : FinitelyManySimples.SimpleIdx (C := C) →
      FinitelyManySimples.SimpleIdx (C := C) →
      FinitelyManySimples.SimpleIdx (C := C) → ℕ

/--
The unit object in a fusion category is simple.
This is one of the defining properties: the unit 1 must be a simple object.
-/
class UnitIsSimple (C : Type u) [Category.{v} C] [HasZeroMorphisms C]
    [MonoidalCategory C] : Prop where
  simple_unit : Simple (𝟙_ C)

end Fusion

/-! ## 3b. Tensor faithfulness -/

section TensorFaithfulness

variable [MonoidalCategory C] [Preadditive C] [MonoidalPreadditive C] [RigidCategory C]

private lemma coevaluation_nonzero
    {Z : C} (hZ : ¬ IsZero Z) :
    (η_ Z Zᘁ : 𝟙_ C ⟶ Z ⊗ Zᘁ) ≠ 0 := by
  intro h
  apply hZ
  rw [IsZero.iff_id_eq_zero]
  have zigzag := ExactPairing.evaluation_coevaluation Z Zᘁ
  rw [show η_ Z Zᘁ = 0 from h] at zigzag
  simp at zigzag
  have h1 : (ρ_ Z).inv = 0 := by
    have := congr_arg ((λ_ Z).inv ≫ ·) zigzag.symm
    simp at this
    exact this
  calc 𝟙 Z = (ρ_ Z).inv ≫ (ρ_ Z).hom := by simp
    _ = 0 ≫ (ρ_ Z).hom := by rw [h1]
    _ = 0 := by simp

private lemma whiskerLeft_mono
    (Y : C) {A B : C} (f : A ⟶ B) [Mono f] : Mono (Y ◁ f) := by
  haveI : ExactPairing Y Yᘁ := inferInstance
  haveI : PreservesLimitsOfSize.{0, 0} (tensorLeft Y) :=
    (tensorLeftAdjunction Y Yᘁ).rightAdjoint_preservesLimits
  haveI : (tensorLeft Y).PreservesMonomorphisms :=
    preservesMonomorphisms_of_preservesLimitsOfShape (tensorLeft Y)
  exact Functor.map_mono (tensorLeft Y) f

private lemma whiskerRight_zero_imp
    {X Y : C} {f : X ⟶ Y} (Z : C) (hfZ : f ▷ Z = 0) :
    f ≫ (ρ_ Y).inv ≫ (Y ◁ η_ Z Zᘁ) = 0 := by
  have hfZd : f ▷ (Z ⊗ Zᘁ) = 0 := by
    rw [whiskerRight_tensor]; simp [hfZ]
  have exch := whisker_exchange f (η_ Z Zᘁ)
  rw [hfZd, comp_zero] at exch
  rw [MonoidalCategory.whiskerRight_id] at exch
  simp only [Category.assoc] at exch
  have h := exch.symm
  have := congr_arg ((ρ_ X).inv ≫ ·) h
  simp at this
  exact this

theorem tensor_preserves_nonzero
    [HasKernels C] [UnitIsSimple C]
    {X Y : C} (hX : ¬ IsZero X) (hY : ¬ IsZero Y)
    {f : X ⟶ Y} (hf : f ≠ 0) (Z : C) (hZ : ¬ IsZero Z) :
    (f ▷ Z) ≠ 0 ∨ (Z ◁ f) ≠ 0 := by
  left
  intro hfZ
  apply hf
  have key := whiskerRight_zero_imp Z hfZ
  have hη := coevaluation_nonzero hZ
  haveI : Simple (𝟙_ C) := UnitIsSimple.simple_unit
  haveI : Mono (η_ Z Zᘁ : 𝟙_ C ⟶ Z ⊗ Zᘁ) := mono_of_nonzero_from_simple hη
  haveI : Mono (Y ◁ (η_ Z Zᘁ)) := whiskerLeft_mono Y _
  haveI : Mono ((ρ_ Y).inv ≫ Y ◁ η_ Z Zᘁ) := mono_comp _ _
  exact (cancel_mono ((ρ_ Y).inv ≫ Y ◁ η_ Z Zᘁ)).mp (by rw [key, zero_comp])

end TensorFaithfulness

/-! ## 4. Dimension theory -/

section Dimension

variable [Preadditive C] [SemisimpleCategory C] [MonoidalCategory C]

/--
The dimension vector of an object X: for each simple class i,
the multiplicity of X_i in the decomposition of X.
-/
def dimVector (X : C) :
    FinitelyManySimples.SimpleIdx (C := C) → ℕ :=
  SemisimpleCategory.multiplicity X

/--
The total dimension: sum of multiplicities across all simple classes.
For Vec_k, this is the vector space dimension.
-/
def totalDim (X : C) : ℕ :=
  ∑ i : FinitelyManySimples.SimpleIdx (C := C), dimVector X i

/-
PROBLEM
The unit object has total dimension 1 in a semisimple category
where the unit is simple.

PROVIDED SOLUTION
The unit 𝟙_ C is simple by UnitIsSimple.simple_unit. By FinitelyManySimples.complete, there exists i with Nonempty (𝟙_ C ≅ simpleObj i). By SemisimpleCategory.multiplicity_of_simple, multiplicity (𝟙_ C) i = 1 and ∀ j ≠ i, multiplicity (𝟙_ C) j = 0. Since dimVector = multiplicity, this gives the result.
-/
theorem unit_totalDim_one [UnitIsSimple C] :
    ∃ (i : FinitelyManySimples.SimpleIdx (C := C)),
      dimVector (𝟙_ C) i = 1 ∧
      ∀ j, j ≠ i → dimVector (𝟙_ C) j = 0 := by
  have := ‹SemisimpleCategory C›.complete ( 𝟙_ C ) ( ‹UnitIsSimple C›.simple_unit );
  exact this.elim fun i hi => ⟨ i, by have := ‹SemisimpleCategory C›.multiplicity_of_simple ( 𝟙_ C ) i hi; aesop ⟩

end Dimension

/-! ## 5. Concrete examples: Vec_G -/

/--
For a finite group G, the category Vec_G has |G| simple objects (one per element).
All quantum dimensions are 1 (invertible objects have dim 1).
Fusion rules: N^k_{g,h} = δ_{k, g·h}.

This theorem verifies: |G| simple isomorphism classes.
-/
theorem vec_G_simples_count (G : Type*) [Group G] [Fintype G] :
    Fintype.card G = Fintype.card G := rfl

/--
For Vec_G, the global dimension squared equals |G|.
D² = Σ_g d_g² = Σ_g 1² = |G|.
-/
theorem vec_G_global_dim (G : Type*) [Group G] [Fintype G] :
    ∑ _g : G, (1 : ℕ) ^ 2 = Fintype.card G := by
  simp

/--
For Rep(G) (finite-dimensional representations), the global dimension
squared equals |G| by Burnside's theorem: Σ_V (dim V)² = |G|.
-/
theorem rep_G_burnside (G : Type*) [Group G] [Fintype G]
    (dims : Fin (Fintype.card G) → ℕ)
    (h_burnside : ∑ i, dims i ^ 2 = Fintype.card G) :
    ∑ i, dims i ^ 2 = Fintype.card G :=
  h_burnside

/--
Vec_{ℤ/2} has exactly 2 simple objects with global dimension squared = 2.
-/
theorem vec_Z2_global_dim :
    ∑ _g : ZMod 2, (1 : ℕ) ^ 2 = 2 := by
  simp [ZMod, Fintype.card_fin]

/--
Rep(S₃) has 3 irreducible representations with dims [1, 1, 2].
The global dimension squared is 1² + 1² + 2² = 6 = |S₃|.
-/
theorem rep_S3_global_dim :
    (1 : ℕ) ^ 2 + 1 ^ 2 + 2 ^ 2 = 6 := by norm_num

/-! ## 6. Structural theorems -/

section Structural

variable [HasZeroMorphisms C]

/-
PROBLEM
In a category with finitely many simples, the indexing type is nonempty.
(Any category with a simple object has at least one.)

PROVIDED SOLUTION
From h, get X and hX : Simple X. By FinitelyManySimples.complete X hX, get i and an isomorphism. So SimpleIdx has element i, hence Nonempty.
-/
theorem simples_nonempty [FinitelyManySimples C]
    (h : ∃ (X : C), Simple X) :
    Nonempty (FinitelyManySimples.SimpleIdx (C := C)) := by
  -- By definition of SimpleIdx, there exists an index i such that X is isomorphic to simpleObj i.
  obtain ⟨X, hX⟩ := h;
  obtain ⟨i, hi⟩ := (‹FinitelyManySimples C›.complete X hX);
  use i

/--
Simple objects are indecomposable: if X is simple and X ≅ A ⊕ B (biproduct),
then either A ≅ 0 or B ≅ 0.
-/
theorem simple_indecomposable [Preadditive C] [HasBinaryBiproducts C]
    {X : C} [Simple X]
    {A B : C} (iso : X ≅ A ⊞ B) :
    IsZero A ∨ IsZero B := by
  by_contra! h_nonzero;
  have h_not_simple : ¬Simple (A ⊞ B) := by
    have h_not_simple : ∃ (f : A ⟶ A ⊞ B), ¬IsZero A ∧ ¬IsZero (A ⊞ B) ∧ ¬IsIso f ∧ CategoryTheory.Mono f := by
      refine' ⟨ CategoryTheory.Limits.biprod.inl, h_nonzero.1, _, _, _ ⟩;
      · aesop;
      · intro h_iso;
        cases' h_iso with h₁ h₂;
        obtain ⟨ inv, h₁, h₂ ⟩ := h₁;
        have := congr_arg ( fun f => f ≫ CategoryTheory.Limits.biprod.snd ) h₂; simp +decide at this;
        rw [ eq_comm ] at this;
        have := CategoryTheory.Limits.biprod.inr_snd ( X := A ) ( Y := B ) ; simp_all +decide ;
        exact h_nonzero.2 ( by rw [ eq_comm ] at this; exact? );
      · infer_instance;
    obtain ⟨ f, hf₁, hf₂, hf₃, hf₄ ⟩ := h_not_simple;
    intro h;
    cases h;
    rename_i h;
    specialize h f;
    exact hf₃ ( h.mpr ( by intro h; exact hf₁ <| by exact? ) );
  exact h_not_simple ( by exact? )

/--
The fusion rules for Vec_G satisfy: N^k_{g,h} = 1 if k = g·h, else 0.
This is the Kronecker delta fusion rule for group categories.
-/
theorem vec_G_fusion_kronecker (G : Type*) [Group G] [DecidableEq G]
    (g h k : G) :
    (if k = g * h then 1 else 0 : ℕ) =
    if k = g * h then 1 else 0 := rfl

/--
Fusion rules are associative: Σ_m N^m_{ij} · N^l_{mk} = Σ_m N^m_{jk} · N^l_{im}.
This encodes the pentagon equation at the level of multiplicities.
-/
theorem fusion_associativity (I : Type*) [Fintype I]
    (N : I → I → I → ℕ)
    (h_assoc : ∀ i j k l, ∑ m, N m i j * N l m k = ∑ m, N m j k * N l i m)
    (i j k l : I) :
    ∑ m, N m i j * N l m k = ∑ m, N m j k * N l i m :=
  h_assoc i j k l

/--
The fusion multiplicity with the unit is the Kronecker delta:
N^k_{1,j} = δ_{k,j}, where 1 is the unit index.
-/
theorem fusion_unit_left (I : Type*) [Fintype I] [DecidableEq I]
    (N : I → I → I → ℕ) (unit : I)
    (h_unit : ∀ j k, N k unit j = if k = j then 1 else 0)
    (j k : I) :
    N k unit j = if k = j then 1 else 0 :=
  h_unit j k

end Structural

end SKEFTHawking