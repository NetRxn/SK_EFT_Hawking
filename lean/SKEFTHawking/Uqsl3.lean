/-
Phase 5i Wave 1: U_q(sl₃) — First Rank-2 Quantum Group in a Proof Assistant

Defines the Drinfeld-Jimbo quantum group U_q(sl₃) as a quotient of the free
algebra on 8 generators by 21 Chevalley relations, using Mathlib's
FreeAlgebra and RingQuot. Cartan matrix A₂ = [[2,−1],[−1,2]].

Same architecture as Uqsl2.lean, extended to rank 2. ZERO axioms.
No existing formalization of U_q(sl_N) for N ≥ 3 in any proof assistant.

References:
  Drinfeld, Proc. ICM 1986; Jimbo, Lett. Math. Phys. 11, 247 (1986)
  Kassel, "Quantum Groups" (Springer, 1995), Ch. VI §3
  Lit-Search/Phase-5j/U_q(sl_3) complete technical specification...
-/

import Mathlib
import SKEFTHawking.QNumber

open LaurentPolynomial

universe u

noncomputable section

namespace SKEFTHawking

variable (k : Type u) [CommRing k]

/-! ## 1. Generators -/

/--
The 8 generators of U_q(sl₃): raising (E₁,E₂), lowering (F₁,F₂),
and Cartan elements (K₁,K₁⁻¹,K₂,K₂⁻¹) for simple roots α₁, α₂.
-/
inductive Uqsl3Gen : Type
  | E1 | E2 | F1 | F2 | K1 | K1inv | K2 | K2inv
  deriving DecidableEq

open Uqsl3Gen

/-! ## 2. Chevalley Relations (21 total) -/

-- Helper: embed a Laurent polynomial as a scalar in the free algebra
private abbrev scal3 (r : LaurentPolynomial k) :
    FreeAlgebra (LaurentPolynomial k) Uqsl3Gen :=
  algebraMap (LaurentPolynomial k) (FreeAlgebra (LaurentPolynomial k) Uqsl3Gen) r

-- Helper: embed a generator
private abbrev g3 (x : Uqsl3Gen) : FreeAlgebra (LaurentPolynomial k) Uqsl3Gen :=
  FreeAlgebra.ι (LaurentPolynomial k) x

/--
The 21 Chevalley relations for U_q(sl₃).
Cartan matrix: A = [[2,−1],[−1,2]] (type A₂, simply-laced, d_i = 1).

Groups:
  I.   K-invertibility (R1-R4): K_i K_i⁻¹ = K_i⁻¹ K_i = 1
  II.  K-commutativity (R5): K₁ K₂ = K₂ K₁
  III. K-E conjugation (R6-R9): K_i E_j = q^{A_{ij}} E_j K_i
  IV.  K-F conjugation (R10-R13): K_i F_j = q^{−A_{ij}} F_j K_i
  V.   E-F commutation (R14-R17): (q−q⁻¹)[E_i,F_j] = δ_{ij}(K_i−K_i⁻¹)
  VI.  Quantum Serre E (R18-R19): E_i²E_j − [2]_q E_iE_jE_i + E_jE_i² = 0
  VII. Quantum Serre F (R20-R21): F_i²F_j − [2]_q F_iF_jF_i + F_jF_i² = 0

All relations in denominator-free form.
-/
inductive ChevalleyRelSl3 :
    FreeAlgebra (LaurentPolynomial k) Uqsl3Gen →
    FreeAlgebra (LaurentPolynomial k) Uqsl3Gen → Prop
  -- Group I: K-invertibility (4 relations)
  | K1K1inv : ChevalleyRelSl3 (g3 k K1 * g3 k K1inv) 1
  | K1invK1 : ChevalleyRelSl3 (g3 k K1inv * g3 k K1) 1
  | K2K2inv : ChevalleyRelSl3 (g3 k K2 * g3 k K2inv) 1
  | K2invK2 : ChevalleyRelSl3 (g3 k K2inv * g3 k K2) 1
  -- Group II: K-commutativity (1 relation)
  | K1K2 : ChevalleyRelSl3 (g3 k K1 * g3 k K2) (g3 k K2 * g3 k K1)
  -- Group III: K-E conjugation (4 relations)
  -- K_i E_j = q^{A_{ij}} E_j K_i
  | K1E1 : ChevalleyRelSl3
      (g3 k K1 * g3 k E1)
      (scal3 k (T 2) * g3 k E1 * g3 k K1)              -- A₁₁ = 2
  | K1E2 : ChevalleyRelSl3
      (g3 k K1 * g3 k E2)
      (scal3 k (T (-1)) * g3 k E2 * g3 k K1)            -- A₁₂ = −1
  | K2E1 : ChevalleyRelSl3
      (g3 k K2 * g3 k E1)
      (scal3 k (T (-1)) * g3 k E1 * g3 k K2)            -- A₂₁ = −1
  | K2E2 : ChevalleyRelSl3
      (g3 k K2 * g3 k E2)
      (scal3 k (T 2) * g3 k E2 * g3 k K2)               -- A₂₂ = 2
  -- Group IV: K-F conjugation (4 relations)
  -- K_i F_j = q^{−A_{ij}} F_j K_i
  | K1F1 : ChevalleyRelSl3
      (g3 k K1 * g3 k F1)
      (scal3 k (T (-2)) * g3 k F1 * g3 k K1)            -- −A₁₁ = −2
  | K1F2 : ChevalleyRelSl3
      (g3 k K1 * g3 k F2)
      (scal3 k (T 1) * g3 k F2 * g3 k K1)               -- −A₁₂ = 1
  | K2F1 : ChevalleyRelSl3
      (g3 k K2 * g3 k F1)
      (scal3 k (T 1) * g3 k F1 * g3 k K2)               -- −A₂₁ = 1
  | K2F2 : ChevalleyRelSl3
      (g3 k K2 * g3 k F2)
      (scal3 k (T (-2)) * g3 k F2 * g3 k K2)            -- −A₂₂ = −2
  -- Group V: E-F commutation (4 relations, denominator-free)
  -- (q − q⁻¹)(E_i F_j − F_j E_i) = δ_{ij}(K_i − K_i⁻¹)
  | EF11 : ChevalleyRelSl3
      (scal3 k (T 1 - T (-1)) * (g3 k E1 * g3 k F1 - g3 k F1 * g3 k E1))
      (g3 k K1 - g3 k K1inv)
  | EF22 : ChevalleyRelSl3
      (scal3 k (T 1 - T (-1)) * (g3 k E2 * g3 k F2 - g3 k F2 * g3 k E2))
      (g3 k K2 - g3 k K2inv)
  | E1F2comm : ChevalleyRelSl3 (g3 k E1 * g3 k F2) (g3 k F2 * g3 k E1)
  | E2F1comm : ChevalleyRelSl3 (g3 k E2 * g3 k F1) (g3 k F1 * g3 k E2)
  -- Group VI: Quantum Serre for E (2 relations)
  -- E_i² E_j − [2]_q E_i E_j E_i + E_j E_i² = 0
  -- Rewritten: E_i² E_j + E_j E_i² = [2]_q E_i E_j E_i
  | SerreE12 : ChevalleyRelSl3
      (g3 k E1 * g3 k E1 * g3 k E2 + g3 k E2 * g3 k E1 * g3 k E1)
      (scal3 k (T 1 + T (-1)) * g3 k E1 * g3 k E2 * g3 k E1)
  | SerreE21 : ChevalleyRelSl3
      (g3 k E2 * g3 k E2 * g3 k E1 + g3 k E1 * g3 k E2 * g3 k E2)
      (scal3 k (T 1 + T (-1)) * g3 k E2 * g3 k E1 * g3 k E2)
  -- Group VII: Quantum Serre for F (2 relations)
  | SerreF12 : ChevalleyRelSl3
      (g3 k F1 * g3 k F1 * g3 k F2 + g3 k F2 * g3 k F1 * g3 k F1)
      (scal3 k (T 1 + T (-1)) * g3 k F1 * g3 k F2 * g3 k F1)
  | SerreF21 : ChevalleyRelSl3
      (g3 k F2 * g3 k F2 * g3 k F1 + g3 k F1 * g3 k F2 * g3 k F2)
      (scal3 k (T 1 + T (-1)) * g3 k F2 * g3 k F1 * g3 k F2)

/-! ## 3. The Quantum Group -/

/--
**U_q(sl₃): the Drinfeld-Jimbo quantum group of type A₂.**

Defined as RingQuot of FreeAlgebra by ChevalleyRelSl3. This is the FIRST
definition of a rank-2 quantum group in any proof assistant. Zero axioms.

Cartan matrix A = [[2,−1],[−1,2]]. 8 generators, 21 relations.
Ring and Algebra (LaurentPolynomial k) instances are automatic from RingQuot.
-/
abbrev Uqsl3 := RingQuot (ChevalleyRelSl3 k)

/-- The quotient map. -/
noncomputable def uqsl3Mk :
    FreeAlgebra (LaurentPolynomial k) Uqsl3Gen →ₐ[LaurentPolynomial k] Uqsl3 k :=
  RingQuot.mkAlgHom _ (ChevalleyRelSl3 k)

/-! ## 4. Named Generators -/

noncomputable def uq3E1 : Uqsl3 k := uqsl3Mk k (g3 k E1)
noncomputable def uq3E2 : Uqsl3 k := uqsl3Mk k (g3 k E2)
noncomputable def uq3F1 : Uqsl3 k := uqsl3Mk k (g3 k F1)
noncomputable def uq3F2 : Uqsl3 k := uqsl3Mk k (g3 k F2)
noncomputable def uq3K1 : Uqsl3 k := uqsl3Mk k (g3 k K1)
noncomputable def uq3K1inv : Uqsl3 k := uqsl3Mk k (g3 k K1inv)
noncomputable def uq3K2 : Uqsl3 k := uqsl3Mk k (g3 k K2)
noncomputable def uq3K2inv : Uqsl3 k := uqsl3Mk k (g3 k K2inv)

/-! ## 5. Relations in U_q(sl₃)

All 21 Chevalley relations hold by RingQuot.mkAlgHom_rel.
Group I (K-invertibility) and II (K-commutativity) are proved directly.
Groups III-VII use the same map_mul + AlgHom.commutes pattern.
-/

-- Group I: K-invertibility (4 theorems)
theorem uq3_K1_mul_K1inv : uq3K1 k * uq3K1inv k = 1 := by
  show uqsl3Mk k (g3 k K1) * uqsl3Mk k (g3 k K1inv) = 1
  rw [← map_mul, ← map_one (uqsl3Mk k)]
  exact RingQuot.mkAlgHom_rel _ ChevalleyRelSl3.K1K1inv

theorem uq3_K1inv_mul_K1 : uq3K1inv k * uq3K1 k = 1 := by
  show uqsl3Mk k (g3 k K1inv) * uqsl3Mk k (g3 k K1) = 1
  rw [← map_mul, ← map_one (uqsl3Mk k)]
  exact RingQuot.mkAlgHom_rel _ ChevalleyRelSl3.K1invK1

theorem uq3_K2_mul_K2inv : uq3K2 k * uq3K2inv k = 1 := by
  show uqsl3Mk k (g3 k K2) * uqsl3Mk k (g3 k K2inv) = 1
  rw [← map_mul, ← map_one (uqsl3Mk k)]
  exact RingQuot.mkAlgHom_rel _ ChevalleyRelSl3.K2K2inv

theorem uq3_K2inv_mul_K2 : uq3K2inv k * uq3K2 k = 1 := by
  show uqsl3Mk k (g3 k K2inv) * uqsl3Mk k (g3 k K2) = 1
  rw [← map_mul, ← map_one (uqsl3Mk k)]
  exact RingQuot.mkAlgHom_rel _ ChevalleyRelSl3.K2invK2

/-- K₁ is invertible with inverse K₁⁻¹. -/
noncomputable def uq3K1_unit : (Uqsl3 k)ˣ where
  val := uq3K1 k
  inv := uq3K1inv k
  val_inv := uq3_K1_mul_K1inv k
  inv_val := uq3_K1inv_mul_K1 k

/-- K₂ is invertible with inverse K₂⁻¹. -/
noncomputable def uq3K2_unit : (Uqsl3 k)ˣ where
  val := uq3K2 k
  inv := uq3K2inv k
  val_inv := uq3_K2_mul_K2inv k
  inv_val := uq3_K2inv_mul_K2 k

-- Group II: K-commutativity (1 theorem)
theorem uq3_K1K2_comm : uq3K1 k * uq3K2 k = uq3K2 k * uq3K1 k := by
  show uqsl3Mk k (g3 k K1) * uqsl3Mk k (g3 k K2) =
    uqsl3Mk k (g3 k K2) * uqsl3Mk k (g3 k K1)
  rw [← map_mul, ← map_mul]
  exact RingQuot.mkAlgHom_rel _ ChevalleyRelSl3.K1K2

-- Group III: K-E conjugation (4 theorems)

/-- K₁E₁ = q²E₁K₁ (A₁₁ = 2). -/
theorem uq3_K1E1 : uq3K1 k * uq3E1 k =
    (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2)) * uq3E1 k * uq3K1 k := by
  have h := RingQuot.mkAlgHom_rel (LaurentPolynomial k) (ChevalleyRelSl3.K1E1 (k := k))
  simp only [map_mul] at h
  unfold uq3K1 uq3E1 uqsl3Mk
  rwa [AlgHom.commutes] at h

/-- K₁E₂ = q⁻¹E₂K₁ (A₁₂ = −1). -/
theorem uq3_K1E2 : uq3K1 k * uq3E2 k =
    (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1))) * uq3E2 k * uq3K1 k := by
  have h := RingQuot.mkAlgHom_rel (LaurentPolynomial k) (ChevalleyRelSl3.K1E2 (k := k))
  simp only [map_mul] at h
  unfold uq3K1 uq3E2 uqsl3Mk
  rwa [AlgHom.commutes] at h

/-- K₂E₁ = q⁻¹E₁K₂ (A₂₁ = −1). -/
theorem uq3_K2E1 : uq3K2 k * uq3E1 k =
    (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-1))) * uq3E1 k * uq3K2 k := by
  have h := RingQuot.mkAlgHom_rel (LaurentPolynomial k) (ChevalleyRelSl3.K2E1 (k := k))
  simp only [map_mul] at h
  unfold uq3K2 uq3E1 uqsl3Mk
  rwa [AlgHom.commutes] at h

/-- K₂E₂ = q²E₂K₂ (A₂₂ = 2). -/
theorem uq3_K2E2 : uq3K2 k * uq3E2 k =
    (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 2)) * uq3E2 k * uq3K2 k := by
  have h := RingQuot.mkAlgHom_rel (LaurentPolynomial k) (ChevalleyRelSl3.K2E2 (k := k))
  simp only [map_mul] at h
  unfold uq3K2 uq3E2 uqsl3Mk
  rwa [AlgHom.commutes] at h

-- Group IV: K-F conjugation (4 theorems)

/-- K₁F₁ = q⁻²F₁K₁ (−A₁₁ = −2).

PROVIDED SOLUTION: Same pattern as K-E relations. -/
theorem uq3_K1F1 : uq3K1 k * uq3F1 k =
    (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-2))) * uq3F1 k * uq3K1 k := by
  have h := RingQuot.mkAlgHom_rel (LaurentPolynomial k) (ChevalleyRelSl3.K1F1 (k := k))
  simp only [map_mul] at h
  unfold uq3K1 uq3F1 uqsl3Mk
  rwa [AlgHom.commutes] at h

/-- K₁F₂ = qF₂K₁ (−A₁₂ = 1). -/
theorem uq3_K1F2 : uq3K1 k * uq3F2 k =
    (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 1)) * uq3F2 k * uq3K1 k := by
  have h := RingQuot.mkAlgHom_rel (LaurentPolynomial k) (ChevalleyRelSl3.K1F2 (k := k))
  simp only [map_mul] at h
  unfold uq3K1 uq3F2 uqsl3Mk
  rwa [AlgHom.commutes] at h

/-- K₂F₁ = qF₁K₂ (−A₂₁ = 1). -/
theorem uq3_K2F1 : uq3K2 k * uq3F1 k =
    (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 1)) * uq3F1 k * uq3K2 k := by
  have h := RingQuot.mkAlgHom_rel (LaurentPolynomial k) (ChevalleyRelSl3.K2F1 (k := k))
  simp only [map_mul] at h
  unfold uq3K2 uq3F1 uqsl3Mk
  rwa [AlgHom.commutes] at h

/-- K₂F₂ = q⁻²F₂K₂ (−A₂₂ = −2). -/
theorem uq3_K2F2 : uq3K2 k * uq3F2 k =
    (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T (-2))) * uq3F2 k * uq3K2 k := by
  have h := RingQuot.mkAlgHom_rel (LaurentPolynomial k) (ChevalleyRelSl3.K2F2 (k := k))
  simp only [map_mul] at h
  unfold uq3K2 uq3F2 uqsl3Mk
  rwa [AlgHom.commutes] at h

-- Group V: E-F commutation (4 theorems)

/-- (q−q⁻¹)(E₁F₁ − F₁E₁) = K₁ − K₁⁻¹ (quantum Serre for root 1).

PROVIDED SOLUTION: Same approach as Uqsl2.uq_serre. Use map_sub + AlgHom.commutes. -/
theorem uq3_EF11 :
    (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 1 - T (-1))) *
      (uq3E1 k * uq3F1 k - uq3F1 k * uq3E1 k) =
    uq3K1 k - uq3K1inv k := by
  unfold uq3E1 uq3F1 uq3K1 uq3K1inv uqsl3Mk
  rw [map_sub (algebraMap (LaurentPolynomial k) (Uqsl3 k))]
  have h := RingQuot.mkAlgHom_rel (LaurentPolynomial k) (ChevalleyRelSl3.EF11 (k := k))
  simp only [map_mul, map_sub, AlgHom.commutes] at h
  exact h

/-- (q−q⁻¹)(E₂F₂ − F₂E₂) = K₂ − K₂⁻¹ (quantum Serre for root 2).

PROVIDED SOLUTION: Identical to EF11 with index swap. -/
theorem uq3_EF22 :
    (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 1 - T (-1))) *
      (uq3E2 k * uq3F2 k - uq3F2 k * uq3E2 k) =
    uq3K2 k - uq3K2inv k := by
  unfold uq3E2 uq3F2 uq3K2 uq3K2inv uqsl3Mk
  rw [map_sub (algebraMap (LaurentPolynomial k) (Uqsl3 k))]
  have h := RingQuot.mkAlgHom_rel (LaurentPolynomial k) (ChevalleyRelSl3.EF22 (k := k))
  simp only [map_mul, map_sub, AlgHom.commutes] at h
  exact h

/-- E₁F₂ = F₂E₁ (cross-root commutation: [E₁,F₂] = 0).

PROVIDED SOLUTION: Direct from mkAlgHom_rel + map_mul. -/
theorem uq3_E1F2_comm : uq3E1 k * uq3F2 k = uq3F2 k * uq3E1 k := by
  show uqsl3Mk k (g3 k E1) * uqsl3Mk k (g3 k F2) =
    uqsl3Mk k (g3 k F2) * uqsl3Mk k (g3 k E1)
  rw [← map_mul, ← map_mul]
  exact RingQuot.mkAlgHom_rel _ ChevalleyRelSl3.E1F2comm

/-- E₂F₁ = F₁E₂ (cross-root commutation: [E₂,F₁] = 0). -/
theorem uq3_E2F1_comm : uq3E2 k * uq3F1 k = uq3F1 k * uq3E2 k := by
  show uqsl3Mk k (g3 k E2) * uqsl3Mk k (g3 k F1) =
    uqsl3Mk k (g3 k F1) * uqsl3Mk k (g3 k E2)
  rw [← map_mul, ← map_mul]
  exact RingQuot.mkAlgHom_rel _ ChevalleyRelSl3.E2F1comm

-- Groups VI-VII: Quantum Serre relations (4 theorems)
-- These involve cubic terms and the [2]_q coefficient.

/-- Quantum Serre relation for E₁,E₂:
    E₁²E₂ − [2]_q E₁E₂E₁ + E₂E₁² = 0.

PROVIDED SOLUTION: Apply mkAlgHom_rel for SerreE12. The relation is stated as
LHS = RHS where LHS = E₁²E₂ + E₂E₁² and RHS = [2]_q · E₁E₂E₁.
Use map_mul + map_add + AlgHom.commutes to convert. -/
theorem uq3_SerreE12 :
    uq3E1 k * uq3E1 k * uq3E2 k + uq3E2 k * uq3E1 k * uq3E1 k =
    (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 1 + T (-1))) *
      uq3E1 k * uq3E2 k * uq3E1 k := by
  unfold uq3E1 uq3E2 uqsl3Mk
  have h := RingQuot.mkAlgHom_rel (LaurentPolynomial k) (ChevalleyRelSl3.SerreE12 (k := k))
  simp only [map_mul, map_add, AlgHom.commutes] at h ⊢
  exact h

/-- Quantum Serre relation for E₂,E₁:
    E₂²E₁ − [2]_q E₂E₁E₂ + E₁E₂² = 0. -/
theorem uq3_SerreE21 :
    uq3E2 k * uq3E2 k * uq3E1 k + uq3E1 k * uq3E2 k * uq3E2 k =
    (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 1 + T (-1))) *
      uq3E2 k * uq3E1 k * uq3E2 k := by
  unfold uq3E1 uq3E2 uqsl3Mk
  have h := RingQuot.mkAlgHom_rel (LaurentPolynomial k) (ChevalleyRelSl3.SerreE21 (k := k))
  simp only [map_mul, map_add, AlgHom.commutes] at h ⊢
  exact h

/-- Quantum Serre relation for F₁,F₂:
    F₁²F₂ − [2]_q F₁F₂F₁ + F₂F₁² = 0. -/
theorem uq3_SerreF12 :
    uq3F1 k * uq3F1 k * uq3F2 k + uq3F2 k * uq3F1 k * uq3F1 k =
    (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 1 + T (-1))) *
      uq3F1 k * uq3F2 k * uq3F1 k := by
  unfold uq3F1 uq3F2 uqsl3Mk
  have h := RingQuot.mkAlgHom_rel (LaurentPolynomial k) (ChevalleyRelSl3.SerreF12 (k := k))
  simp only [map_mul, map_add, AlgHom.commutes] at h ⊢
  exact h

/-- Quantum Serre relation for F₂,F₁:
    F₂²F₁ − [2]_q F₂F₁F₂ + F₁F₂² = 0. -/
theorem uq3_SerreF21 :
    uq3F2 k * uq3F2 k * uq3F1 k + uq3F1 k * uq3F2 k * uq3F2 k =
    (algebraMap (LaurentPolynomial k) (Uqsl3 k) (T 1 + T (-1))) *
      uq3F2 k * uq3F1 k * uq3F2 k := by
  unfold uq3F1 uq3F2 uqsl3Mk
  have h := RingQuot.mkAlgHom_rel (LaurentPolynomial k) (ChevalleyRelSl3.SerreF21 (k := k))
  simp only [map_mul, map_add, AlgHom.commutes] at h ⊢
  exact h

/-! ## 6. Module Summary -/

/--
Uqsl3 module: the Drinfeld-Jimbo quantum group U_q(sl₃) of type A₂.
  - Defined via FreeAlgebra + RingQuot (ZERO axioms)
  - First rank-2 quantum group definition in any proof assistant
  - 8 generators: E₁, E₂, F₁, F₂, K₁, K₁⁻¹, K₂, K₂⁻¹
  - 21 Chevalley relations from Cartan matrix A = [[2,−1],[−1,2]]
  - K₁K₁⁻¹ = K₂K₂⁻¹ = 1 PROVED
  - K₁K₂ = K₂K₁ PROVED
  - K-E and K-F conjugation (8 relations) PROVED
  - E-F commutation (4 relations) PROVED
  - Quantum Serre (4 relations) PROVED via simp [map_mul, map_add, AlgHom.commutes]
  - Ring and Algebra instances automatic from RingQuot
-/
theorem uqsl3_summary : True := trivial

end SKEFTHawking
