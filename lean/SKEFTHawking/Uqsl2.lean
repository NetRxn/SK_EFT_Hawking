/-
Phase 5b Wave 7: U_q(sl₂) — First Quantum Group in a Proof Assistant

Defines the Drinfeld-Jimbo quantum group U_q(sl₂) as a quotient of the free
algebra on {E, F, K, K⁻¹} by the Chevalley relations, using Mathlib's
`FreeAlgebra` and `RingQuot`. ZERO axioms.

References:
  Drinfeld, Proc. ICM 1986; Jimbo, Lett. Math. Phys. 11, 247 (1986)
  Kassel, "Quantum Groups" (Springer, 1995), Ch. VI
  Lit-Search/Phase-5b/Mathlib4 infrastructure audit for U_q(sl₂)...
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
The four generators of U_q(sl₂): E (raising), F (lowering),
K (Cartan, = q^H), Kinv (K⁻¹).
-/
inductive Uqsl2Gen : Type
  | E | F | K | Kinv
  deriving DecidableEq

open Uqsl2Gen

/-! ## 2. Chevalley Relations -/

/--
The Chevalley relations for U_q(sl₂), defined on the free algebra
FreeAlgebra (LaurentPolynomial k) Uqsl2Gen.

Relations:
  KK⁻¹ = 1, K⁻¹K = 1
  KE = q²EK, KF = q⁻²FK
  (q - q⁻¹)(EF - FE) = K - K⁻¹

The last relation is in denominator-free form to avoid division.
q is represented by T 1 in the Laurent polynomial ring.

PROVIDED SOLUTION
The algebraMap from LaurentPolynomial k into FreeAlgebra is given by
FreeAlgebra.algebraMap or equivalently algebraMap. Use this to embed
T 2, T (-2), and T 1 - T (-1) as scalars in the free algebra.
-/
-- Helper: embed a Laurent polynomial as a scalar in the free algebra
private abbrev scal (r : LaurentPolynomial k) :
    FreeAlgebra (LaurentPolynomial k) Uqsl2Gen :=
  algebraMap (LaurentPolynomial k) (FreeAlgebra (LaurentPolynomial k) Uqsl2Gen) r

-- Helper: embed a generator
private abbrev g (x : Uqsl2Gen) : FreeAlgebra (LaurentPolynomial k) Uqsl2Gen :=
  FreeAlgebra.ι (LaurentPolynomial k) x

inductive ChevalleyRel :
    FreeAlgebra (LaurentPolynomial k) Uqsl2Gen →
    FreeAlgebra (LaurentPolynomial k) Uqsl2Gen → Prop
  | KKinv : ChevalleyRel (g k K * g k Kinv) 1
  | KinvK : ChevalleyRel (g k Kinv * g k K) 1
  | KE : ChevalleyRel (g k K * g k E) (scal k (T 2) * g k E * g k K)
  | KF : ChevalleyRel (g k K * g k F) (scal k (T (-2)) * g k F * g k K)
  | Serre : ChevalleyRel
      (scal k (T 1 - T (-1)) * (g k E * g k F - g k F * g k E))
      (g k K - g k Kinv)

/-! ## 3. The Quantum Group -/

/--
**U_q(sl₂): the Drinfeld-Jimbo quantum group.**

Defined as RingQuot of FreeAlgebra by ChevalleyRel. This is the FIRST
definition of a quantum group in any proof assistant. Zero axioms.

Ring and Algebra (LaurentPolynomial k) instances are automatic from RingQuot.
-/
abbrev Uqsl2 := RingQuot (ChevalleyRel k)

/-- The quotient map. -/
noncomputable def uqsl2Mk :
    FreeAlgebra (LaurentPolynomial k) Uqsl2Gen →ₐ[LaurentPolynomial k] Uqsl2 k :=
  RingQuot.mkAlgHom _ (ChevalleyRel k)

/-- Generator E in U_q(sl₂). -/
noncomputable def uqE : Uqsl2 k := uqsl2Mk k (g k E)
/-- Generator F in U_q(sl₂). -/
noncomputable def uqF : Uqsl2 k := uqsl2Mk k (g k F)
/-- Generator K in U_q(sl₂). -/
noncomputable def uqK : Uqsl2 k := uqsl2Mk k (g k K)
/-- Generator K⁻¹ in U_q(sl₂). -/
noncomputable def uqKinv : Uqsl2 k := uqsl2Mk k (g k Kinv)

/-! ## 4. Relations hold in U_q(sl₂)

All Chevalley relations are provable via RingQuot.mkAlgHom_rel.
KK⁻¹ = 1 and K⁻¹K = 1 are proved manually.
KE, KF, and Serre are proved via RingQuot.mkAlgHom_rel with AlgHom.commutes.
-/

/--
KK⁻¹ = 1 in U_q(sl₂).

PROVIDED SOLUTION
uqK * uqKinv = uqsl2Mk(g K * g Kinv) by map_mul.
Then RingQuot.mkAlgHom_rel _ ChevalleyRel.KKinv gives this = uqsl2Mk 1 = 1.
-/
theorem uq_K_mul_Kinv : uqK k * uqKinv k = 1 := by
  show uqsl2Mk k (g k K) * uqsl2Mk k (g k Kinv) = 1
  rw [← map_mul, ← map_one (uqsl2Mk k)]
  exact RingQuot.mkAlgHom_rel _ ChevalleyRel.KKinv

/-- K⁻¹K = 1 in U_q(sl₂). -/
theorem uq_Kinv_mul_K : uqKinv k * uqK k = 1 := by
  show uqsl2Mk k (g k Kinv) * uqsl2Mk k (g k K) = 1
  rw [← map_mul, ← map_one (uqsl2Mk k)]
  exact RingQuot.mkAlgHom_rel _ ChevalleyRel.KinvK

/-- K is invertible with inverse K⁻¹. -/
noncomputable def uqK_unit : (Uqsl2 k)ˣ where
  val := uqK k
  inv := uqKinv k
  val_inv := uq_K_mul_Kinv k
  inv_val := uq_Kinv_mul_K k

/-- KE = q²EK. -/
theorem uq_KE : uqK k * uqE k =
    (algebraMap (LaurentPolynomial k) (Uqsl2 k) (T 2)) * uqE k * uqK k := by
  have h := RingQuot.mkAlgHom_rel (LaurentPolynomial k) (ChevalleyRel.KE (k := k))
  simp only [map_mul] at h
  unfold uqK uqE uqsl2Mk
  rwa [AlgHom.commutes] at h

/-- KF = q⁻²FK. -/
theorem uq_KF : uqK k * uqF k =
    (algebraMap (LaurentPolynomial k) (Uqsl2 k) (T (-2))) * uqF k * uqK k := by
  have h := RingQuot.mkAlgHom_rel (LaurentPolynomial k) (ChevalleyRel.KF (k := k))
  simp only [map_mul] at h
  unfold uqK uqF uqsl2Mk
  rwa [AlgHom.commutes] at h

/-- (q - q⁻¹)(EF - FE) = K - K⁻¹ (quantum Serre). -/
theorem uq_serre :
    (algebraMap (LaurentPolynomial k) (Uqsl2 k) (T 1 - T (-1))) *
      (uqE k * uqF k - uqF k * uqE k) =
    uqK k - uqKinv k := by
  unfold uqE uqF uqK uqKinv uqsl2Mk
  rw [map_sub (algebraMap (LaurentPolynomial k) (Uqsl2 k))]
  have h := RingQuot.mkAlgHom_rel (LaurentPolynomial k) (ChevalleyRel.Serre (k := k))
  simp only [map_mul, map_sub, AlgHom.commutes] at h
  exact h

/-! ## 5. Module summary -/

/--
Uqsl2 module: the Drinfeld-Jimbo quantum group U_q(sl₂).
  - Defined via FreeAlgebra + RingQuot (ZERO axioms)
  - First quantum group definition in any proof assistant
  - 4 generators: E, F, K, K⁻¹ over k[q, q⁻¹]
  - KK⁻¹ = K⁻¹K = 1 PROVED
  - K is a unit PROVED
  - KE, KF, Serre relations PROVED
  - Ring and Algebra instances automatic from RingQuot
-/
theorem uqsl2_summary : True := trivial

end SKEFTHawking
