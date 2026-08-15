/-
Phase 5q.T Wave T2: A(1) as a genuine `Ring` / `Algebra (ZMod 2)`

`A1Ring.lean` holds eight 8×8 matrices over F₂ — the left-regular-representation matrices
of the Milnor basis `e₀ … e₇` of A(1) = ⟨Sq¹, Sq²⟩ — together with multiplication facts
proven by `decide`. Those matrices are *about* A(1); they are not A(1). Nothing there is a
`Ring`, so nothing there can be fed to Mathlib's module, `Hom`, or `Ext` machinery, and the
statement "dim Hom_{A(1)}(P, F₂) = rank P" could not even be typed.

This module builds the algebra itself, as the F₂-span of those eight matrices inside
`Matrix (Fin 8) (Fin 8) F₂`:

  * `A1Span`  — the F₂-submodule spanned by `Lmat`.
  * `A1sub`   — the same set as a `Subalgebra F2 (Matrix Idx Idx F2)`. Closure under
                multiplication is `Lmat_mul_expand` (the structure constants, kernel-checked
                in `A1Ring.lean`). Being a subalgebra of a matrix algebra, it inherits
                `Ring`, `Algebra F2`, associativity and distributivity from Mathlib —
                nothing is re-axiomatised here.
  * `A1_finrank : Module.finrank F2 A1sub = 8` — via an explicit linear equivalence with
                `Fin 8 → F2` given by reading off column 0 (`x ↦ x · e₀`). This is what
                pins A1sub to *the* 8-dimensional A(1) rather than to some sub-thing of it.
  * `A1_noncommutative` — `Sq¹·Sq² ≠ Sq²·Sq¹` inside the algebra. Recorded because it is
                the fact that rules out Mathlib's `CommRing`-only change-of-rings functor
                `ModuleCat.extendScalars` for this algebra (see `ChangeOfRings.lean`).
  * `aug : A1sub →ₐ[F2] F2` — the augmentation, an honest `AlgHom`; `aug_Lmat` shows it
                kills every non-unit basis element, i.e. the augmentation ideal is the span
                of `e₁ … e₇`.
  * `trivialA1Module` — F₂ as the trivial A(1)-module, `a • x = ε(a)·x`. This is the target
                module of the Ext computation, and it is what makes `Hom_{A(1)}(−, F₂)`
                type-check at all.
  * `finrank_hom_free`, `hom_free_A1_finrank` — `dim_{F₂} Hom_{A(1)}(A(1)^r, F₂) = r`.
                The genuine form of what `ChangeOfRings.hom_tensor_adjunction_dim` used to
                assert as `rank = rank := rfl`.

Everything here is kernel-pure: axiom set `{propext, Classical.choice, Quot.sound}`.

Roadmap: docs/roadmaps/Phase5qT_ExtSubstantiation_Roadmap.md (Wave T2).
-/

import Mathlib
import SKEFTHawking.A1Ring

namespace SKEFTHawking.A1

/-! ## 1. The span of the left-regular-representation matrices -/

/-- The F₂-span of the eight left-regular-representation matrices `Lmat e₀ … Lmat e₇`. -/
def A1Span : Submodule F2 (Matrix Idx Idx F2) := Submodule.span F2 (Set.range Lmat)

theorem Lmat_mem (a : Idx) : Lmat a ∈ A1Span := Submodule.subset_span ⟨a, rfl⟩

theorem one_mem_A1Span : (1 : Matrix Idx Idx F2) ∈ A1Span := by
  rw [← Lmat_zero_eq_one]; exact Lmat_mem 0

/-- Closure under multiplication — the content is `Lmat_mul_expand`, the structure
    constants of A(1) in the Milnor basis. -/
theorem mul_mem_A1Span : ∀ x ∈ A1Span, ∀ y ∈ A1Span, x * y ∈ A1Span := by
  have key : A1Span * A1Span ≤ A1Span := by
    rw [A1Span, Submodule.span_mul_span, Submodule.span_le]
    rintro z ⟨x, ⟨i, rfl⟩, y, ⟨j, rfl⟩, rfl⟩
    show Lmat i * Lmat j ∈ A1Span
    rw [Lmat_mul_expand]
    exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Lmat_mem k)
  intro x hx y hy
  exact key (Submodule.mul_mem_mul hx hy)

/-! ## 2. A(1) as a genuine algebra -/

/-- **A(1) = ⟨Sq¹, Sq²⟩ as a genuine `Ring` and `Algebra (ZMod 2)`**, realised as the
    subalgebra of `Matrix (Fin 8) (Fin 8) F₂` spanned by the left-regular-representation
    matrices of the Milnor basis. Ring and algebra axioms are inherited from the ambient
    matrix algebra; nothing is postulated. -/
def A1sub : Subalgebra F2 (Matrix Idx Idx F2) :=
  A1Span.toSubalgebra one_mem_A1Span (fun x y hx hy => mul_mem_A1Span x hx y hy)

theorem mem_A1sub_iff {M : Matrix Idx Idx F2} : M ∈ A1sub ↔ M ∈ A1Span := Iff.rfl

/-- The Milnor basis elements, as elements of the algebra. -/
def e (a : Idx) : A1sub := ⟨Lmat a, Lmat_mem a⟩

/-- `Sq¹ · Sq² ≠ Sq² · Sq¹` **inside the algebra**: A(1) is genuinely noncommutative.
    This is the fact that forces the noncommutative branch of Mathlib's change-of-rings
    API (`ModuleCat.restrictCoextendScalarsAdj`, `[Ring R] [Ring S]`) and rules out the
    `CommRing`-only `ModuleCat.extendScalars` / `extendRestrictScalarsAdj`. -/
theorem A1_noncommutative : e 1 * e 2 ≠ e 2 * e 1 := by
  intro h
  have : L1 * L2 = L2 * L1 := congrArg Subtype.val h
  revert this
  decide

/-- Sq¹ squares to zero in the algebra (the fundamental Adem relation). -/
theorem e1_sq : e 1 * e 1 = 0 := by
  apply Subtype.ext
  show L1 * L1 = 0
  decide

/-- Sq² · Sq² = Sq(1,1) in the algebra. -/
theorem e2_sq : e 2 * e 2 = e 5 := by
  apply Subtype.ext
  show L2 * L2 = L5
  decide

/-! ## 3. Dimension: A(1) is 8-dimensional over F₂

The linear equivalence is "act on the unit": `x ↦ (x · e₀)`, which in the left-regular
representation is column 0 of the matrix. `Lmat_col0` says column 0 of `Lmat a` is the
`a`-th standard basis vector, which is exactly why this is a bijection. -/

/-- Read off column 0 of a matrix — i.e. evaluate the operator at the unit `e₀`. -/
def coeffL : Matrix Idx Idx F2 →ₗ[F2] (Idx → F2) where
  toFun M := fun k => M k 0
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

/-- Assemble a matrix from a coefficient vector in the Milnor basis. -/
def ofCoeff : (Idx → F2) →ₗ[F2] Matrix Idx Idx F2 where
  toFun v := ∑ a, v a • Lmat a
  map_add' u v := by simp [add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp [Finset.smul_sum, smul_smul]

theorem ofCoeff_mem (v : Idx → F2) : ofCoeff v ∈ A1Span := by
  show ∑ a, v a • Lmat a ∈ A1Span
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Lmat_mem k)

theorem coeffL_ofCoeff (v : Idx → F2) : coeffL (ofCoeff v) = v := by
  funext k
  simp only [coeffL, ofCoeff, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply,
    Matrix.smul_apply, smul_eq_mul, Lmat_col0]
  simp [Finset.sum_ite_eq]

theorem ofCoeff_coeffL : ∀ M ∈ A1Span, ofCoeff (coeffL M) = M := by
  intro M hM
  induction hM using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      simp only [coeffL, ofCoeff, LinearMap.coe_mk, AddHom.coe_mk, Lmat_col0]
      simp
  | zero => simp
  | add x y _ _ hx hy => rw [map_add, map_add, hx, hy]
  | smul c x _ hx => rw [map_smul, map_smul, hx]

/-- A(1) ≃ F₂⁸ as F₂-vector spaces, by evaluation at the unit. -/
noncomputable def A1equiv : A1sub ≃ₗ[F2] (Idx → F2) where
  toFun M := coeffL M.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun v := ⟨ofCoeff v, ofCoeff_mem v⟩
  left_inv := by rintro ⟨M, hM⟩; exact Subtype.ext (ofCoeff_coeffL M hM)
  right_inv := coeffL_ofCoeff

/-- **A(1) has F₂-dimension 8** — the Milnor basis `e₀ … e₇` really is a basis. -/
theorem A1_finrank : Module.finrank F2 A1sub = 8 := by
  rw [A1equiv.finrank_eq, Module.finrank_pi F2]
  simp

/-! ## 4. The augmentation, and F₂ as the trivial A(1)-module -/

/-- Row 0 of `Lmat a` is supported at column 0, and only for the unit `a = e₀`:
    `e₀` occurs in `e a · e k` only when both are the unit. Connectivity of the grading. -/
theorem Lmat_row0 : ∀ a k : Idx,
    Lmat a 0 k = (if a = 0 then 1 else 0) * (if k = 0 then 1 else 0) := by decide

/-- Row 0 of an element of A(1) is concentrated in column 0 — the connectivity of the
    graded algebra: `e₀` occurs in `a · e_k` only when `a = e₀` and `k = 0`. -/
theorem row0_concentrated :
    ∀ M ∈ A1Span, ∀ k : Idx, M 0 k = M 0 0 * (if k = 0 then 1 else 0) := by
  intro M hM
  induction hM using Submodule.span_induction with
  | mem x hx => obtain ⟨a, rfl⟩ := hx; intro k; rw [Lmat_row0, Lmat_row0]; simp
  | zero => intro k; simp
  | add x y _ _ hx hy =>
      intro k; rw [Matrix.add_apply, Matrix.add_apply, hx k, hy k, ← add_mul]
  | smul c x _ hx =>
      intro k
      rw [Matrix.smul_apply, Matrix.smul_apply, hx k, smul_eq_mul, smul_eq_mul, mul_assoc]

theorem aug_mul_aux (M N : Matrix Idx Idx F2) (hM : M ∈ A1Span) :
    (M * N) 0 0 = M 0 0 * N 0 0 := by
  simp only [Matrix.mul_apply]
  rw [Finset.sum_congr rfl (fun k _ => by rw [row0_concentrated M hM k])]
  simp

/-- **The augmentation ε : A(1) →ₐ[F₂] F₂**, a genuine algebra homomorphism (multiplicativity
    is `aug_mul_aux`, which is where the connectivity of A(1) is used). -/
def aug : A1sub →ₐ[F2] F2 where
  toFun M := M.1 0 0
  map_one' := rfl
  map_mul' M N := aug_mul_aux M.1 N.1 M.2
  map_zero' := rfl
  map_add' _ _ := rfl
  commutes' c := by
    show (algebraMap F2 (Matrix Idx Idx F2) c) 0 0 = c
    simp [Matrix.algebraMap_matrix_apply]

/-- ε kills every non-unit Milnor basis element: the augmentation ideal is `⟨e₁ … e₇⟩`.
    This is the precise sense in which the resolution's differentials are "minimal". -/
theorem aug_e (a : Idx) : aug (e a) = if a = 0 then 1 else 0 := by
  show Lmat a 0 0 = _
  rw [Lmat_row0]; simp

/-- **F₂ as the trivial A(1)-module**, `a • x = ε(a)·x`. Scoped, so it does not leak a
    `Module A1sub F2` instance outside this namespace. -/
scoped instance trivialA1Module : Module A1sub F2 := Module.compHom F2 (aug : A1sub →+* F2)

theorem trivial_smul (a : A1sub) (x : F2) : a • x = aug a * x := rfl

scoped instance : SMulCommClass A1sub F2 F2 where
  smul_comm a c x := by show aug a * (c * x) = c * (aug a * x); ring

/-! ## 5. `Hom` out of a free module

This is the honest content of what `ChangeOfRings.hom_tensor_adjunction_dim` used to state
as `rank = rank := rfl`. -/

/-- **`dim_{F₂} Hom_A(A^r, F₂) = r` for ANY ring `A` acting on `F₂`** (in particular, for
    any augmented F₂-algebra, acting through its augmentation).

    Stated at this generality on purpose: it is one half of the change-of-rings claim of
    `ChangeOfRings.lean`. For a free A(1)-module `P = A(1)^r` the induced module
    `A ⊗_{A(1)} P` is the free `A`-module `A^r`, so this single lemma gives the F₂-dimension
    of BOTH `Hom_{A(1)}(P, F₂)` and `Hom_A(A ⊗_{A(1)} P, F₂)` — both are `r`.
    (What it does *not* give is the identification `A ⊗_{A(1)} A(1)^r ≅ A^r` itself: Mathlib
    has no balanced tensor product over a noncommutative base ring, so that object cannot
    currently be *stated*. See `ChangeOfRings.lean` §2 and the Phase 5q.T findings.) -/
theorem finrank_hom_free {A : Type*} [Ring A] [Module A F2] [SMulCommClass A F2 F2]
    (r : ℕ) : Module.finrank F2 ((Fin r → A) →ₗ[A] F2) = r := by
  have h : ((Fin r → A) →ₗ[A] F2) ≃ₗ[F2] (Fin r → F2) :=
    (LinearMap.lsum A (fun _ : Fin r => A) F2).symm.trans
      (LinearEquiv.piCongrRight fun _ => LinearMap.ringLmapEquivSelf A F2 F2)
  rw [h.finrank_eq, Module.finrank_pi F2]
  simp

/-- **dim_{F₂} Hom_{A(1)}(A(1)^r, F₂) = r.**

    A free A(1)-module of rank `r` has an `r`-dimensional space of maps to the trivial
    module — the statement that turns the resolution's ranks `1,2,2,2,3,4` into cochain-group
    dimensions, and the genuine replacement for the former
    `hom_tensor_adjunction_dim (rank : ℕ) : rank = rank := rfl`. -/
theorem hom_free_A1_finrank (r : ℕ) :
    Module.finrank F2 ((Fin r → A1sub) →ₗ[A1sub] F2) = r :=
  finrank_hom_free r

/-- Master statement for Wave T2: A(1) is a genuine 8-dimensional noncommutative
    F₂-algebra with an augmentation, and `Hom_{A(1)}(A(1)^r, F₂)` has dimension `r`. -/
theorem a1_is_a_genuine_algebra :
    Module.finrank F2 A1sub = 8
    ∧ e 1 * e 2 ≠ e 2 * e 1
    ∧ e 1 * e 1 = 0
    ∧ (∀ a : Idx, aug (e a) = if a = 0 then 1 else 0)
    ∧ (∀ r : ℕ, Module.finrank F2 ((Fin r → A1sub) →ₗ[A1sub] F2) = r) :=
  ⟨A1_finrank, A1_noncommutative, e1_sq, aug_e, hom_free_A1_finrank⟩

end SKEFTHawking.A1
