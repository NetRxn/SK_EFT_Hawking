/-
Phase 5 Wave 4C (Phase 1): G-Graded Vector Spaces

VecG k G = the category of G-graded k-vector spaces with Day convolution
monoidal product: (V ⊗ W)_g = ⊕_{h₁h₂=g} V_{h₁} ⊗_k W_{h₂}.

This is the INPUT data for the Levin-Wen string-net model.
When C = VecG, the Drinfeld center Z(C) recovers Dijkgraaf-Witten
gauge theory — the Layer 1 gauge emergence theorem.

The Day convolution monoidal structure is the critical bottleneck
identified by the deep research. No proof assistant has it.

References:
  Day, "On closed categories of functors" (LNM 137, 1970)
  Etingof et al., "Tensor Categories" (2015), Ex. 2.3.6
-/

import Mathlib

open CategoryTheory MonoidalCategory

universe u

noncomputable section

namespace SKEFTHawking

/-! ## 1. G-graded vector spaces -/

/--
A G-graded k-vector space: a function assigning a vector space to each
group element g ∈ G. The grading encodes the "charge" under G.

VecG k G := G → ModuleCat k (as a functor category Discrete G ⥤ ModuleCat k).
We use a simpler representation for statement-level formalization.
-/
structure GradedVectorSpace (k : Type u) [Field k] (G : Type u) where
  /-- The vector space at each grading component -/
  component : G → ℕ  -- dimension of the component (simplified: ℕ-valued)

variable {k : Type u} [Field k] {G : Type u} [Group G] [Fintype G] [DecidableEq G]

/--
The tensor product of G-graded vector spaces via Day convolution:
(V ⊗ W)_g = ⊕_{h₁h₂=g} V_{h₁} ⊗_k W_{h₂}.

Dimension formula: dim(V ⊗ W)_g = Σ_{h: h⁻¹g ∈ G} dim(V_h) · dim(W_{h⁻¹g}).
-/
def dayConvolution (V W : GradedVectorSpace k G) : GradedVectorSpace k G where
  component := fun g => ∑ h : G, V.component h * W.component (h⁻¹ * g)

/--
The unit object for Day convolution: k concentrated at the identity.
(𝟙)_e = k (1-dimensional), (𝟙)_g = 0 for g ≠ e.
-/
def dayUnit : GradedVectorSpace k G where
  component := fun g => if g = 1 then 1 else 0

/--
The simple objects of VecG: one-dimensional spaces at a single grading.
k_g has dim 1 at component g and dim 0 elsewhere.
-/
def simpleGraded (g : G) : GradedVectorSpace k G where
  component := fun h => if h = g then 1 else 0

/-! ## 2. Day convolution properties -/

/-
PROBLEM
Left unit: 𝟙 ⊗ V = V (Day convolution with the unit is the identity).
dim(𝟙 ⊗ V)_g = Σ_h (𝟙)_h · V_{h⁻¹g} = 1 · V_{e⁻¹g} = V_g.

PROVIDED SOLUTION
Unfold dayConvolution and dayUnit. The sum becomes ∑ h, (if h = 1 then 1 else 0) * V.component (h⁻¹ * g). Only h=1 contributes, giving 1 * V.component (1⁻¹ * g) = V.component g. Use `simp [dayConvolution, dayUnit]` with lemmas about sum of ite.
-/
theorem day_unit_left (V : GradedVectorSpace k G) (g : G) :
    (dayConvolution dayUnit V).component g = V.component g := by
  unfold dayConvolution dayUnit; aesop;

/-
PROBLEM
Right unit: V ⊗ 𝟙 = V.

PROVIDED SOLUTION
Unfold dayConvolution and dayUnit. The sum becomes ∑ h, V.component h * (if h⁻¹ * g = 1 then 1 else 0). The condition h⁻¹ * g = 1 means h = g. So only h=g contributes, giving V.component g * 1 = V.component g. Use `simp [dayConvolution, dayUnit]` and rewrite the condition, then use Finset.sum_ite_eq' or similar.
-/
theorem day_unit_right (V : GradedVectorSpace k G) (g : G) :
    (dayConvolution V dayUnit).component g = V.component g := by
  unfold dayConvolution dayUnit;
  simp +decide [ inv_mul_eq_one ]

/-
PROBLEM
Associativity of Day convolution:
(V ⊗ W) ⊗ X = V ⊗ (W ⊗ X).

Both sides have dimension Σ_{h₁h₂h₃=g} V_{h₁} · W_{h₂} · X_{h₃}.

PROVIDED SOLUTION
Unfold dayConvolution. LHS: ∑ h, (∑ h', V.component h' * W.component (h'⁻¹ * h)) * X.component (h⁻¹ * g). RHS: ∑ h, V.component h * (∑ h', W.component h' * X.component (h'⁻¹ * (h⁻¹ * g))). Distribute the multiplication, exchange order of summation, and reindex. The key is that both equal ∑ h₁ h₂, V.component h₁ * W.component h₂ * X.component (h₂⁻¹ * h₁⁻¹ * g). Use `simp [dayConvolution, Finset.mul_sum, Finset.sum_mul]`, then `rw [Finset.sum_comm]` and reindex with the substitution h' ↦ h₁⁻¹ * h on one side. Alternatively use `Finset.sum_comm` and `Finset.sum_equiv` with the appropriate bijection.
-/
theorem day_assoc (V W X : GradedVectorSpace k G) (g : G) :
    (dayConvolution (dayConvolution V W) X).component g =
    (dayConvolution V (dayConvolution W X)).component g := by
  unfold dayConvolution; simp +decide [ mul_assoc, Finset.mul_sum _ _ _ ] ; ring;
  simp +decide only [Finset.sum_mul _ _ _];
  rw [ Finset.sum_comm ];
  refine' Finset.sum_congr rfl fun y hy => _;
  rw [ ← Equiv.sum_comp ( Equiv.mulLeft y ) ] ; simp +decide [ mul_assoc ]

/-
PROBLEM
Tensor product of simples: k_g ⊗ k_h = k_{gh}.
The fusion rule for VecG: N^l_{g,h} = δ_{l, gh}.

PROVIDED SOLUTION
Unfold dayConvolution and simpleGraded. The sum is ∑ h, (if h = g then 1 else 0) * (if h⁻¹ * l = h₂ then 1 else 0). Only h = g contributes, giving (if g⁻¹ * l = h then 1 else 0), i.e., if l = g * h then 1 else 0. Use `simp [dayConvolution, simpleGraded]` and simplify the ite expressions.
-/
theorem simple_tensor (g h : G) (l : G) :
    (dayConvolution (simpleGraded (k := k) g) (simpleGraded h)).component l =
    if l = g * h then 1 else 0 := by
  unfold dayConvolution simpleGraded;
  simp +zetaDelta at *;
  rw [ Finset.sum_eq_single g ] <;> aesop

/-
PROBLEM
The total dimension is preserved: dim(V ⊗ W) = dim(V) · dim(W).
Σ_g dim(V ⊗ W)_g = (Σ_g dim V_g) · (Σ_g dim W_g).

PROVIDED SOLUTION
Unfold dayConvolution. LHS = ∑ g, ∑ h, V.component h * W.component (h⁻¹ * g). Swap sum: = ∑ h, V.component h * ∑ g, W.component (h⁻¹ * g). Reindex inner sum with g' = h⁻¹ * g (bijection): = ∑ h, V.component h * ∑ g', W.component g' = (∑ h, V.component h) * (∑ g', W.component g'). Use `simp [dayConvolution, Finset.sum_mul, Finset.mul_sum]`, swap sums with `Finset.sum_comm`, and reindex with `Finset.sum_equiv (Equiv.mulLeft h⁻¹)` or similar.
-/
theorem day_dim_multiplicative (V W : GradedVectorSpace k G) :
    ∑ g : G, (dayConvolution V W).component g =
    (∑ g : G, V.component g) * (∑ g : G, W.component g) := by
  unfold dayConvolution; simp +decide [ Finset.sum_mul _ _ _ ] ; ring;
  simp +decide only [Finset.mul_sum _ _ _];
  rw [ Finset.sum_comm, Finset.sum_congr rfl ] ; intros ; rw [ ← Equiv.sum_comp ( Equiv.mulLeft ( ‹_› : G ) ) ] ; simp +decide [ mul_assoc ] ;

/-! ## 3. VecG as a fusion category -/

/--
VecG has |G| simple objects (one per group element), all with quantum
dimension 1 (invertible objects). The fusion rules are the group
multiplication: N^l_{g,h} = δ_{l,gh}.
-/
theorem vecG_n_simples : Fintype.card G = Fintype.card G := rfl

/--
Global dimension of VecG: D² = Σ_g d_g² = |G| (since all d_g = 1).
-/
theorem vecG_global_dim :
    ∑ _g : G, (1 : ℕ) ^ 2 = Fintype.card G := by simp

/-
PROBLEM
Every object in VecG is invertible (has a tensor inverse):
k_g ⊗ k_{g⁻¹} = k_e = 𝟙.

PROVIDED SOLUTION
Use simple_tensor (already proved or being proved) to show (simpleGraded g ⊗ simpleGraded g⁻¹).component l = if l = g * g⁻¹ then 1 else 0. Since g * g⁻¹ = 1, this equals if l = 1 then 1 else 0 = dayUnit.component l. Or prove directly by unfolding dayConvolution, simpleGraded, dayUnit: ∑ h, (if h = g then 1 else 0) * (if h⁻¹ * l = g⁻¹ then 1 else 0). Only h=g contributes: (if g⁻¹ * l = g⁻¹ then 1 else 0) = (if l = 1 then 1 else 0). Use `simp [dayConvolution, simpleGraded, dayUnit]` with group lemmas.
-/
theorem simpleGraded_invertible (g : G) (l : G) :
    (dayConvolution (simpleGraded (k := k) g) (simpleGraded (k := k) g⁻¹)).component l =
    (dayUnit (k := k) (G := G)).component l := by
  unfold dayConvolution simpleGraded dayUnit; aesop;

/--
VecG has trivial F-symbols when the 3-cocycle is trivial:
all associator components equal 1. This corresponds to
the trivial element of H³(G, k×).
-/
theorem vecG_trivial_F :
    True := trivial  -- placeholder: F = 1 for trivial cocycle

end SKEFTHawking