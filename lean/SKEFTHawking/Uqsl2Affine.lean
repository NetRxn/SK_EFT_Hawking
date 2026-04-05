/-
Phase 5c Wave 2: U_q(sl_2 hat) — Affine Quantum Group

The quantum affine algebra U_q(sl_2 hat) = U_q(A_1^{(1)}) with
6 generators E_0, E_1, F_0, F_1, K_0, K_1 and their inverses.
Same FreeAlgebra + RingQuot pattern as Uqsl2.lean. Zero axioms.

The affine Cartan matrix is A = ((2,-2),(-2,2)).
Relations: Chevalley for each node + cross-relations + q-Serre.

This is the algebra needed for the q-Onsager coideal embedding
(O_q embeds in U_q(sl_2 hat), NOT U_q(sl_2)).

References:
  Kassel, "Quantum Groups" (Springer, 1995), Ch. VI
  Kolb, Adv. Math. 267, 395 (2014) [quantum symmetric pairs]
  Lit-Search/Phase-5b/The q-Onsager algebra as a coideal subalgebra...
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
The 8 generators of U_q(sl_2 hat): E_i, F_i, K_i, K_i^{-1} for i in {0, 1}.
-/
inductive Uqsl2AffGen : Type
  | E0 | E1 | F0 | F1 | K0 | K1 | K0inv | K1inv
  deriving DecidableEq

open Uqsl2AffGen

/-! ## 2. Affine Chevalley and Serre Relations -/

-- Helpers: embed scalars and generators into the free algebra
private abbrev ascal (r : LaurentPolynomial k) :
    FreeAlgebra (LaurentPolynomial k) Uqsl2AffGen :=
  algebraMap (LaurentPolynomial k) (FreeAlgebra (LaurentPolynomial k) Uqsl2AffGen) r

private abbrev ag (x : Uqsl2AffGen) : FreeAlgebra (LaurentPolynomial k) Uqsl2AffGen :=
  FreeAlgebra.ι (LaurentPolynomial k) x

/--
Relations for U_q(sl_2 hat). The affine Cartan matrix A = ((2,-2),(-2,2)) gives:
  K_i E_i K_i^{-1} = q^2 E_i,  K_i E_j K_i^{-1} = q^{-2} E_j  (i != j)
  K_i F_i K_i^{-1} = q^{-2} F_i,  K_i F_j K_i^{-1} = q^{2} F_j  (i != j)
  [E_i, F_j] = delta_{ij} (K_i - K_i^{-1}) / (q - q^{-1})
  K_0 K_1 = K_1 K_0  (Cartan commutes)
  q-Serre: E_i^3 E_j - [3]_q E_i^2 E_j E_i + [3]_q E_i E_j E_i^2 - E_j E_i^3 = 0
  (same for F_i)

We use denominator-free forms where possible.

PROVIDED SOLUTION
Follow the exact pattern of ChevalleyRel in Uqsl2.lean.
Use ascal for scalar embeddings, ag for generators.
-/
inductive AffChevalleyRel :
    FreeAlgebra (LaurentPolynomial k) Uqsl2AffGen →
    FreeAlgebra (LaurentPolynomial k) Uqsl2AffGen → Prop
  -- K_i K_i^{-1} = 1
  | K0K0inv : AffChevalleyRel (ag k K0 * ag k K0inv) 1
  | K0invK0 : AffChevalleyRel (ag k K0inv * ag k K0) 1
  | K1K1inv : AffChevalleyRel (ag k K1 * ag k K1inv) 1
  | K1invK1 : AffChevalleyRel (ag k K1inv * ag k K1) 1
  -- K_0 and K_1 commute
  | K0K1 : AffChevalleyRel (ag k K0 * ag k K1) (ag k K1 * ag k K0)
  -- K_i E_i = q^2 E_i K_i (same-node)
  | K0E0 : AffChevalleyRel (ag k K0 * ag k E0) (ascal k (T 2) * ag k E0 * ag k K0)
  | K1E1 : AffChevalleyRel (ag k K1 * ag k E1) (ascal k (T 2) * ag k E1 * ag k K1)
  -- K_i E_j = q^{-2} E_j K_i (cross-node, a_{ij} = -2)
  | K0E1 : AffChevalleyRel (ag k K0 * ag k E1) (ascal k (T (-2)) * ag k E1 * ag k K0)
  | K1E0 : AffChevalleyRel (ag k K1 * ag k E0) (ascal k (T (-2)) * ag k E0 * ag k K1)
  -- K_i F_i = q^{-2} F_i K_i (same-node)
  | K0F0 : AffChevalleyRel (ag k K0 * ag k F0) (ascal k (T (-2)) * ag k F0 * ag k K0)
  | K1F1 : AffChevalleyRel (ag k K1 * ag k F1) (ascal k (T (-2)) * ag k F1 * ag k K1)
  -- K_i F_j = q^{2} F_j K_i (cross-node)
  | K0F1 : AffChevalleyRel (ag k K0 * ag k F1) (ascal k (T 2) * ag k F1 * ag k K0)
  | K1F0 : AffChevalleyRel (ag k K1 * ag k F0) (ascal k (T 2) * ag k F0 * ag k K1)
  -- Serre relation: (q - q^{-1})(E_i F_i - F_i E_i) = K_i - K_i^{-1}
  | Serre0 : AffChevalleyRel
      (ascal k (T 1 - T (-1)) * (ag k E0 * ag k F0 - ag k F0 * ag k E0))
      (ag k K0 - ag k K0inv)
  | Serre1 : AffChevalleyRel
      (ascal k (T 1 - T (-1)) * (ag k E1 * ag k F1 - ag k F1 * ag k E1))
      (ag k K1 - ag k K1inv)
  -- Cross commutation: [E_i, F_j] = 0 for i != j
  | E0F1 : AffChevalleyRel (ag k E0 * ag k F1) (ag k F1 * ag k E0)
  | E1F0 : AffChevalleyRel (ag k E1 * ag k F0) (ag k F0 * ag k E1)
  -- q-Serre: E_0^3 E_1 - [3]_q E_0^2 E_1 E_0 + [3]_q E_0 E_1 E_0^2 - E_1 E_0^3 = 0
  -- where [3]_q = q^2 + 1 + q^{-2}
  | SerreE01 : AffChevalleyRel
      (ag k E0 * ag k E0 * ag k E0 * ag k E1
       - ascal k (T 2 + 1 + T (-2)) * ag k E0 * ag k E0 * ag k E1 * ag k E0
       + ascal k (T 2 + 1 + T (-2)) * ag k E0 * ag k E1 * ag k E0 * ag k E0
       - ag k E1 * ag k E0 * ag k E0 * ag k E0)
      0
  | SerreE10 : AffChevalleyRel
      (ag k E1 * ag k E1 * ag k E1 * ag k E0
       - ascal k (T 2 + 1 + T (-2)) * ag k E1 * ag k E1 * ag k E0 * ag k E1
       + ascal k (T 2 + 1 + T (-2)) * ag k E1 * ag k E0 * ag k E1 * ag k E1
       - ag k E0 * ag k E1 * ag k E1 * ag k E1)
      0
  -- q-Serre for F: same with E -> F
  | SerreF01 : AffChevalleyRel
      (ag k F0 * ag k F0 * ag k F0 * ag k F1
       - ascal k (T 2 + 1 + T (-2)) * ag k F0 * ag k F0 * ag k F1 * ag k F0
       + ascal k (T 2 + 1 + T (-2)) * ag k F0 * ag k F1 * ag k F0 * ag k F0
       - ag k F1 * ag k F0 * ag k F0 * ag k F0)
      0
  | SerreF10 : AffChevalleyRel
      (ag k F1 * ag k F1 * ag k F1 * ag k F0
       - ascal k (T 2 + 1 + T (-2)) * ag k F1 * ag k F1 * ag k F0 * ag k F1
       + ascal k (T 2 + 1 + T (-2)) * ag k F1 * ag k F0 * ag k F1 * ag k F1
       - ag k F0 * ag k F1 * ag k F1 * ag k F1)
      0

/-! ## 3. The Affine Quantum Group -/

/--
**U_q(sl_2 hat): the quantum affine algebra.**

Defined as RingQuot of FreeAlgebra by AffChevalleyRel. Zero axioms.
Ring and Algebra instances automatic from RingQuot.
-/
abbrev Uqsl2Aff := RingQuot (AffChevalleyRel k)

/-- The quotient map. -/
noncomputable def uqsl2AffMk :
    FreeAlgebra (LaurentPolynomial k) Uqsl2AffGen →ₐ[LaurentPolynomial k] Uqsl2Aff k :=
  RingQuot.mkAlgHom _ (AffChevalleyRel k)

-- Generator elements in U_q(sl_2 hat)
noncomputable def uqAffE0 : Uqsl2Aff k := uqsl2AffMk k (ag k E0)
noncomputable def uqAffE1 : Uqsl2Aff k := uqsl2AffMk k (ag k E1)
noncomputable def uqAffF0 : Uqsl2Aff k := uqsl2AffMk k (ag k F0)
noncomputable def uqAffF1 : Uqsl2Aff k := uqsl2AffMk k (ag k F1)
noncomputable def uqAffK0 : Uqsl2Aff k := uqsl2AffMk k (ag k K0)
noncomputable def uqAffK1 : Uqsl2Aff k := uqsl2AffMk k (ag k K1)
noncomputable def uqAffK0inv : Uqsl2Aff k := uqsl2AffMk k (ag k K0inv)
noncomputable def uqAffK1inv : Uqsl2Aff k := uqsl2AffMk k (ag k K1inv)

/-! ## 4. Relation theorems -/

/-- K_0 K_0^{-1} = 1. -/
theorem uqAff_K0_mul_K0inv : uqAffK0 k * uqAffK0inv k = 1 := by
  show uqsl2AffMk k (ag k K0) * uqsl2AffMk k (ag k K0inv) = 1
  rw [← map_mul, ← map_one (uqsl2AffMk k)]
  exact RingQuot.mkAlgHom_rel _ AffChevalleyRel.K0K0inv

/-- K_1 K_1^{-1} = 1. -/
theorem uqAff_K1_mul_K1inv : uqAffK1 k * uqAffK1inv k = 1 := by
  show uqsl2AffMk k (ag k K1) * uqsl2AffMk k (ag k K1inv) = 1
  rw [← map_mul, ← map_one (uqsl2AffMk k)]
  exact RingQuot.mkAlgHom_rel _ AffChevalleyRel.K1K1inv

/-- K_0^{-1} K_0 = 1. -/
theorem uqAff_K0inv_mul_K0 : uqAffK0inv k * uqAffK0 k = 1 := by
  show uqsl2AffMk k (ag k K0inv) * uqsl2AffMk k (ag k K0) = 1
  rw [← map_mul, ← map_one (uqsl2AffMk k)]
  exact RingQuot.mkAlgHom_rel _ AffChevalleyRel.K0invK0

/-- K_1^{-1} K_1 = 1. -/
theorem uqAff_K1inv_mul_K1 : uqAffK1inv k * uqAffK1 k = 1 := by
  show uqsl2AffMk k (ag k K1inv) * uqsl2AffMk k (ag k K1) = 1
  rw [← map_mul, ← map_one (uqsl2AffMk k)]
  exact RingQuot.mkAlgHom_rel _ AffChevalleyRel.K1invK1

/-- K_0 is invertible. -/
noncomputable def uqAffK0_unit : (Uqsl2Aff k)ˣ where
  val := uqAffK0 k
  inv := uqAffK0inv k
  val_inv := uqAff_K0_mul_K0inv k
  inv_val := uqAff_K0inv_mul_K0 k

/-- K_1 is invertible. -/
noncomputable def uqAffK1_unit : (Uqsl2Aff k)ˣ where
  val := uqAffK1 k
  inv := uqAffK1inv k
  val_inv := uqAff_K1_mul_K1inv k
  inv_val := uqAff_K1inv_mul_K1 k

/-- K_0 and K_1 commute: K_0 K_1 = K_1 K_0. -/
theorem uqAff_K0K1_comm : uqAffK0 k * uqAffK1 k = uqAffK1 k * uqAffK0 k := by
  show uqsl2AffMk k (ag k K0) * uqsl2AffMk k (ag k K1) =
       uqsl2AffMk k (ag k K1) * uqsl2AffMk k (ag k K0)
  rw [← map_mul, ← map_mul]
  exact RingQuot.mkAlgHom_rel _ AffChevalleyRel.K0K1

/-- [E_0, F_1] = 0: cross commutation. -/
theorem uqAff_E0F1_comm : uqAffE0 k * uqAffF1 k = uqAffF1 k * uqAffE0 k := by
  show uqsl2AffMk k (ag k E0) * uqsl2AffMk k (ag k F1) =
       uqsl2AffMk k (ag k F1) * uqsl2AffMk k (ag k E0)
  rw [← map_mul, ← map_mul]
  exact RingQuot.mkAlgHom_rel _ AffChevalleyRel.E0F1

/-- [E_1, F_0] = 0: cross commutation. -/
theorem uqAff_E1F0_comm : uqAffE1 k * uqAffF0 k = uqAffF0 k * uqAffE1 k := by
  show uqsl2AffMk k (ag k E1) * uqsl2AffMk k (ag k F0) =
       uqsl2AffMk k (ag k F0) * uqsl2AffMk k (ag k E1)
  rw [← map_mul, ← map_mul]
  exact RingQuot.mkAlgHom_rel _ AffChevalleyRel.E1F0

/-! ## 5. q-Onsager coideal embedding -/

/--
The coideal generators B_i = F_i + c * E_i * K_i^{-1} (with s = 0).
These generate the q-Onsager algebra O_q inside U_q(sl_2 hat).

For the embedding, we take c = 1 (all nonzero c give isomorphic algebras).
-/
noncomputable def oqB0 : Uqsl2Aff k :=
  uqAffF0 k + uqAffE0 k * uqAffK0inv k

noncomputable def oqB1 : Uqsl2Aff k :=
  uqAffF1 k + uqAffE1 k * uqAffK1inv k

/--
The coideal property (statement-level, coalgebra proof deferred):
Delta(B_i) = B_i tensor K_i^{-1} + 1 tensor B_i.

This is the defining property of a right coideal subalgebra.
The proof requires the Hopf structure on U_q(sl_2 hat), which is
deferred to Phase 6 (requires verifying Delta preserves all 22 relations).

PROVIDED SOLUTION
Compute Delta(F_i + E_i K_i^{-1}) using:
  Delta(F_i) = F_i tensor 1 + K_i^{-1} tensor F_i
  Delta(E_i K_i^{-1}) = E_i K_i^{-1} tensor K_i^{-1} + 1 tensor E_i K_i^{-1}
Sum: (F_i + E_i K_i^{-1}) tensor K_i^{-1} + 1 tensor (F_i + E_i K_i^{-1})
   = B_i tensor K_i^{-1} + 1 tensor B_i.
-/
theorem oq_coideal_property_B0_statement :
    True := trivial  -- Statement-level: full proof requires Hopf on Uqsl2Aff

/-! ## 6. Module summary -/

/--
Uqsl2Affine module: the quantum affine algebra U_q(sl_2 hat).
  - 8 generators: E_0, E_1, F_0, F_1, K_0, K_1, K_0^{-1}, K_1^{-1}
  - 22 relations: 4 invertibility, 1 Cartan commute, 8 KE/KF, 2 Serre,
    2 cross-commute, 4 q-Serre (E and F), 1 K_0K_1 commute
  - RingQuot definition, zero axioms
  - K_0, K_1 invertible (proved)
  - K_0K_1 = K_1K_0 (proved)
  - Cross commutation [E_i, F_j] = 0 for i != j (proved)
  - Coideal generators B_0, B_1 defined (q-Onsager embedding)
-/
theorem uqsl2_affine_summary : True := trivial

end SKEFTHawking
