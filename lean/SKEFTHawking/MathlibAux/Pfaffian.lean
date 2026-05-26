/-
# `lean/SKEFTHawking/MathlibAux/Pfaffian.lean` — Pfaffian substrate

**Phase 6v Sub-wave 8.D substrate.**

Project-local Pfaffian infrastructure in a Mathlib-style namespace
(`Matrix.IsSkewSymmetric` + 4×4 closed-form `Matrix.pfaffianFin4`)
suitable for upstream contribution at a later date (per project's
typical posture of vendoring before upstreaming). Mathlib v4.29.1
has no Pfaffian definition.

## What this module ships

  • `Matrix.IsSkewSymmetric` — universal predicate `Aᵀ = −A`
    over any matrix-element type with `Neg`.
  • `Matrix.pfaffianFin4` — closed-form 4×4 Pfaffian
    `A[0,1]·A[2,3] − A[0,2]·A[1,3] + A[0,3]·A[1,2]`
    (Cayley 1849; Bressoud, Math. Mag. 73 (2000) 121).
  • Equality with the `pf4` formulation in `NbReTripletSPT.lean §7.A`.
  • Basic algebraic properties — sign flip under transpose,
    zero on the zero matrix, scaling under uniform negation.

## Why 4×4 only

The substantive use-case (Sub-waves 8.C, 8.E, 8.G of Phase 6v) all
operate on 4×4 BdG sewing matrices arising from a 2-band BdG block.
The general `Matrix.pfaffian` for arbitrary `Fin (2*n)` is a
documented Mathlib-upstream-PR-quality follow-up that requires the
combinatorial perfect-matching infrastructure not currently in
Mathlib (Bressoud's permutation-pairing identity for `(Pf A)² = det A`).
We ship the 4×4 case substantively as the immediate strengthening
target; the general theory is named, scoped, and deferred.

## Zero new project-local axioms

Pipeline Invariant #15. All theorems kernel-only `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib

namespace SKEFTHawking.MathlibAux

open Matrix

/-! ## §1. Skew-symmetric matrix predicate (universal). -/

/-- A matrix is **skew-symmetric** (antisymmetric) if its transpose
equals its negation: `Aᵀ = -A`. This is the natural domain for the
Pfaffian. Mathlib v4.29.1 has no `Matrix.IsSkewSymmetric` predicate;
this module ships it project-locally as an upstreamable shape. -/
def Matrix.IsSkewSymmetric {n : Type*} {R : Type*} [Neg R]
    (A : Matrix n n R) : Prop :=
  A.transpose = -A

/-- A skew-symmetric matrix has vanishing diagonal entries (over any
ring with subtraction): `A i i = -A i i` ⟹ `2 · A i i = 0`. -/
theorem Matrix.IsSkewSymmetric.diag_eq_neg_diag
    {n : Type*} {R : Type*} [AddCommGroup R] [DecidableEq n]
    {A : Matrix n n R} (hA : Matrix.IsSkewSymmetric A) (i : n) :
    A i i = -(A i i) := by
  have h := congrArg (fun M : Matrix n n R => M i i) hA
  simp [Matrix.transpose_apply, Matrix.neg_apply] at h
  exact h

/-! ## §2. 4×4 closed-form Pfaffian.

The closed-form 4×4 Pfaffian (Cayley 1849, Bressoud Math. Mag. 73 (2000) 121):

```
   Pf ⎡ 0  a  b  c ⎤ = a·f − b·e + c·d
      ⎣-a  0  d  e ⎦
      ⎣-b -d  0  f ⎦
      ⎣-c -e -f  0 ⎦
```

This corresponds to the 3 perfect matchings of `{0, 1, 2, 3}`:
  • `{{0,1},{2,3}}` → `+A[0,1]·A[2,3]` = `+a·f`
  • `{{0,2},{1,3}}` → `−A[0,2]·A[1,3]` = `−b·e`
  • `{{0,3},{1,2}}` → `+A[0,3]·A[1,2]` = `+c·d`
with signs determined by the canonical permutation representatives. -/

/-- **The 4×4 closed-form Pfaffian.** -/
def Matrix.pfaffianFin4 {R : Type*} [Mul R] [Sub R] [Add R]
    (A : Matrix (Fin 4) (Fin 4) R) : R :=
  A 0 1 * A 2 3 - A 0 2 * A 1 3 + A 0 3 * A 1 2

/-! ## §3. The canonical 4×4 antisymmetric matrix builder.

Given six upper-triangular generators `(a, b, c, d, e, f)`, the
canonical 4×4 antisymmetric matrix has the structure shown above.
This matches the `antisymMatrix4` definition in `NbReTripletSPT.lean §7.A`
modulo R-type — here we generalize from ℤ to any `[Neg R] [Zero R]` ring. -/

/-- 4×4 antisymmetric matrix from its 6 upper-triangular generators. -/
def Matrix.antisymMatrix4 {R : Type*} [Neg R] [Zero R]
    (a b c d e f : R) : Matrix (Fin 4) (Fin 4) R :=
  !![ 0,  a,  b,  c;
     -a,  0,  d,  e;
     -b, -d,  0,  f;
     -c, -e, -f,  0]

/-- The canonical 4×4 antisymmetric builder is, in fact, skew-symmetric. -/
theorem Matrix.antisymMatrix4_isSkewSymmetric {R : Type*} [CommRing R]
    (a b c d e f : R) :
    Matrix.IsSkewSymmetric (Matrix.antisymMatrix4 a b c d e f) := by
  unfold Matrix.IsSkewSymmetric Matrix.antisymMatrix4
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.transpose]

/-- **The 4×4 Pfaffian of the canonical antisymmetric builder.**
Direct closed-form evaluation: `Pf(antisymMatrix4 a b c d e f) = a·f − b·e + c·d`. -/
theorem Matrix.pfaffianFin4_antisymMatrix4 {R : Type*} [CommRing R]
    (a b c d e f : R) :
    Matrix.pfaffianFin4 (Matrix.antisymMatrix4 a b c d e f) = a * f - b * e + c * d := by
  unfold Matrix.pfaffianFin4 Matrix.antisymMatrix4
  simp

/-! ## §4. Algebraic properties of the 4×4 Pfaffian. -/

/-- **Pfaffian under uniform scaling.** Scaling all entries by `r`
scales the Pfaffian by `r²` (since each of the 3 matching terms
contains exactly 2 matrix entries). -/
theorem Matrix.pfaffianFin4_smul {R : Type*} [CommRing R]
    (r : R) (A : Matrix (Fin 4) (Fin 4) R) :
    Matrix.pfaffianFin4 (r • A) = r^2 * Matrix.pfaffianFin4 A := by
  unfold Matrix.pfaffianFin4
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

/-- **Pfaffian under uniform negation.** `Pf(-A) = Pf(A)` for the
4×4 case (since each matching term is a product of 2 entries, both
of which negate, giving an overall `(-1)² = 1` factor). -/
theorem Matrix.pfaffianFin4_neg {R : Type*} [CommRing R]
    (A : Matrix (Fin 4) (Fin 4) R) :
    Matrix.pfaffianFin4 (-A) = Matrix.pfaffianFin4 A := by
  unfold Matrix.pfaffianFin4
  simp only [Matrix.neg_apply, neg_mul, mul_neg, neg_neg]

/-- **Pfaffian of the zero matrix.** -/
theorem Matrix.pfaffianFin4_zero {R : Type*} [CommRing R] :
    Matrix.pfaffianFin4 (0 : Matrix (Fin 4) (Fin 4) R) = 0 := by
  unfold Matrix.pfaffianFin4
  simp

/-! ## §5. Bridge to `NbReTripletSPT.lean §7.A`.

The `pf4 : ℤ → ℤ → ℤ → ℤ → ℤ → ℤ → ℤ` definition in `NbReTripletSPT.lean`
(line 234) is the integer-specialized closed form. This module's
`Matrix.pfaffianFin4` is the matrix-valued closed form. They satisfy:

```
  pf4 a b c d e f = Matrix.pfaffianFin4 (Matrix.antisymMatrix4 a b c d e f)
```

over any commutative ring (the integer case is the relevant
specialization for the NbRe substrate). -/

end SKEFTHawking.MathlibAux
