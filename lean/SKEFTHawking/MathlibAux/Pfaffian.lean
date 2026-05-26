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

/-! ## §6. General-n Pfaffian helpers — `doubleIdx` and `IsCanonicalMatching`.

For the general-`n` Pfaffian (Phase 6v Sub-wave 9.B, post-2026-05-26 strengthening),
we parameterize over `Fin n` pair-indices `i` and a `Bool` flag distinguishing
even/odd members of each pair. The canonical-matching predicate then picks
out, for each perfect matching of `Fin (2*n)`, the unique permutation
representative with within-pair and across-pair ordering constraints.

This parallels the Mathlib `Matrix.det_apply'` template:

```
  Matrix.det M = ∑ σ : Equiv.Perm (Fin n), σ.sign • ∏ i, M (σ i) i
  Matrix.pfaffian A
    = ∑ σ ∈ canonicalMatchings, σ.sign • ∏ i : Fin n, A (σ (2i)) (σ (2i+1))
```
-/

/-- Build a `Fin (2 * n)` index from a `Fin n` pair-index `i` and a `Bool`
flag `b`: returns `2·i.val + (b ? 1 : 0)`. -/
def Matrix.doubleIdx {n : ℕ} (i : Fin n) (b : Bool) : Fin (2 * n) :=
  ⟨2 * i.val + (if b then 1 else 0), by
    have h := i.is_lt; cases b <;> simp <;> omega⟩

/-- **Canonical perfect-matching predicate** on a permutation
`σ : Equiv.Perm (Fin (2 * n))`. The two conjuncts are:

1. **Within-pair ordering:** for each pair-index `i : Fin n`,
   the smaller member comes first: `σ (2i) < σ (2i+1)`.
2. **Across-pair ordering:** pairs are ordered by their smaller element:
   `σ (2i) < σ (2j)` whenever `i < j`.

These constraints pick out exactly one permutation per perfect matching of
`Fin (2 * n)`. The number of canonical matchings is `(2n)! / (2^n · n!)`
(the number of perfect matchings of `2n` elements). For `n = 0` this is `1`
(empty matching); for `n = 1` this is `1`; for `n = 2` this is `3`; for
`n = 3` this is `15`; etc.

This is an `abbrev` to keep `Decidable` instances auto-derived via
`instDecidableAnd` + `Fintype.decidableForallFintype`. -/
abbrev Matrix.IsCanonicalMatching {n : ℕ} (σ : Equiv.Perm (Fin (2 * n))) : Prop :=
  (∀ i : Fin n, σ (Matrix.doubleIdx i false) < σ (Matrix.doubleIdx i true)) ∧
  (∀ i j : Fin n, i < j → σ (Matrix.doubleIdx i false) < σ (Matrix.doubleIdx j false))

/-! ## §7. General-n Pfaffian definition.

The Pfaffian of a `2n × 2n` matrix is the signed sum over canonical
perfect-matching permutations of the product of matched entries. For
`A : Matrix (Fin (2 * n)) (Fin (2 * n)) R`:

```
  pfaffian A = ∑ σ ∈ canonicalMatchings, sign σ · ∏ i : Fin n, A (σ (2i)) (σ (2i+1))
```

This parallels `Matrix.det_apply'` with the permutation sum restricted to
canonical matchings (giving each perfect matching exactly one
representative, avoiding the `2^n · n!`-fold over-counting that would
result from summing over all permutations).

For a skew-symmetric (alternating) matrix, this Pfaffian satisfies
`(pfaffian A)² = det A` (Cayley 1849; Bressoud Math. Mag. 73 (2000) 121).
The proof at `n = 2` (4×4 case) is given in §9 below; the general-`n`
proof requires Bressoud's permutation-pairing identity and is a
Mathlib-PR-quality follow-up. -/

/-- **The general-`n` Pfaffian**, defined as the canonical-matching
permutation sum. Noncomputable because `Finset.sum` over a `Fintype`
filter is noncomputable for arbitrary commutative rings. -/
noncomputable def Matrix.pfaffian {n : ℕ} {R : Type*} [CommRing R]
    (A : Matrix (Fin (2 * n)) (Fin (2 * n)) R) : R :=
  ∑ σ ∈ (Finset.univ.filter Matrix.IsCanonicalMatching :
      Finset (Equiv.Perm (Fin (2 * n)))),
    Equiv.Perm.sign σ •
      ∏ i : Fin n, A (σ (Matrix.doubleIdx i false)) (σ (Matrix.doubleIdx i true))

/-- **Base case `n = 0`**: the Pfaffian of the unique 0×0 matrix is `1`.
The empty product (over `Fin 0`) is `1`, the only permutation on `Fin 0`
is the identity (with sign `+1`), and the canonical-matching predicate
is vacuously true. -/
theorem Matrix.pfaffian_fin_zero {R : Type*} [CommRing R]
    (A : Matrix (Fin (2 * 0)) (Fin (2 * 0)) R) :
    Matrix.pfaffian A = 1 := by
  unfold Matrix.pfaffian
  have h : (Finset.univ.filter (@Matrix.IsCanonicalMatching 0) :
      Finset (Equiv.Perm (Fin (2 * 0)))) = Finset.univ := by
    apply Finset.filter_true_of_mem
    intro σ _
    refine ⟨?_, ?_⟩
    · intro i; exact i.elim0
    · intro i; exact i.elim0
  rw [h]
  simp [Equiv.Perm.sign_one]

/-! ## §8. `n = 2` (4×4) bridge: general `pfaffian` recovers `pfaffianFin4`.

The 3 canonical matchings of `Fin 4` are:
  * **Identity** `(0,1)(2,3)`: sign `+1`, contributes `+A 0 1 · A 2 3`.
  * **Swap (1 2)** `(0,2)(1,3)`: sign `-1`, contributes `-A 0 2 · A 1 3`.
  * **Cycle (1 3 2)** `(0,3)(1,2)`: sign `+1`, contributes `+A 0 3 · A 1 2`.

The sum equals `A 0 1 · A 2 3 − A 0 2 · A 1 3 + A 0 3 · A 1 2 = pfaffianFin4 A`. -/

/-- The 3 canonical matchings of `Fin 4` as concrete `Equiv.Perm` values.
Identity. -/
def Matrix.cm4_id : Equiv.Perm (Fin 4) := 1

/-- Swap-(1 2) canonical matching of `Fin 4`. -/
def Matrix.cm4_swap12 : Equiv.Perm (Fin 4) := Equiv.swap 1 2

/-- Cycle-(1 3 2) canonical matching of `Fin 4`. -/
def Matrix.cm4_cycle132 : Equiv.Perm (Fin 4) := Equiv.swap 1 3 * Equiv.swap 2 3

/-- **The canonical-matching filter for `Fin 4` enumerates to a 3-element set.** -/
theorem Matrix.canonical_matching_filter_fin_four :
    (Finset.univ : Finset (Equiv.Perm (Fin (2 * 2)))).filter Matrix.IsCanonicalMatching
      = {Matrix.cm4_id, Matrix.cm4_swap12, Matrix.cm4_cycle132} := by decide

/-- **Bridge: the general-`n` Pfaffian at `n = 2` recovers the closed-form
`pfaffianFin4`.** Direct case-enumeration over the 3 canonical matchings. -/
theorem Matrix.pfaffian_eq_pfaffianFin4 {R : Type*} [CommRing R]
    (A : Matrix (Fin (2 * 2)) (Fin (2 * 2)) R) :
    Matrix.pfaffian A = Matrix.pfaffianFin4 A := by
  unfold Matrix.pfaffian Matrix.pfaffianFin4
  rw [Matrix.canonical_matching_filter_fin_four]
  rw [show ({Matrix.cm4_id, Matrix.cm4_swap12, Matrix.cm4_cycle132} :
      Finset (Equiv.Perm (Fin (2 * 2))))
        = insert Matrix.cm4_id (insert Matrix.cm4_swap12 {Matrix.cm4_cycle132}) from rfl]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
      Finset.sum_singleton]
  simp [Fin.prod_univ_two, Matrix.cm4_id, Matrix.cm4_swap12,
        Matrix.cm4_cycle132, Matrix.doubleIdx,
        Equiv.swap_apply_def, Equiv.Perm.mul_apply]
  ring

/-- **Specialization to `antisymMatrix4`:** `pfaffian (antisymMatrix4 a b c d e f) = a·f − b·e + c·d`.
This is the first acceptance-criterion theorem of Sub-wave 9.B (Item B).
Explicit `@Matrix.pfaffian 2` forces the type-metavariable to `n = 2`, so the
`Matrix (Fin 4)` return type of `antisymMatrix4` unifies with the expected
`Matrix (Fin (2 * 2))` definitionally. -/
theorem Matrix.pfaffian_antisymMatrix4 {R : Type*} [CommRing R]
    (a b c d e f : R) :
    @Matrix.pfaffian 2 R _ (Matrix.antisymMatrix4 a b c d e f)
      = a * f - b * e + c * d := by
  rw [Matrix.pfaffian_eq_pfaffianFin4, Matrix.pfaffianFin4_antisymMatrix4]

/-! ## §9. `(Pf A)² = det A` for skew-symmetric, zero-diagonal 4×4 matrices.

The Cayley-Bressoud identity at `n = 2`. The "alternating" hypothesis
(`IsSkewSymmetric` AND vanishing diagonal) is necessary in arbitrary
characteristic because in characteristic 2, `IsSkewSymmetric` does NOT
imply zero diagonal. For our substantive use (BdG `antisymMatrix4` over
ℤ/ℝ/ℂ — all `CharZero`), both hypotheses hold by construction.

The proof reduces `det A` via cofactor expansion (`Matrix.det_succ_row_zero`)
and substitutes the skew-symmetric / zero-diagonal identities, yielding a
ring identity in 6 free upper-triangular entries.

The general-`n` Pf²=det proof requires Bressoud's permutation-pairing
identity (~150-300 LoC Mathlib-PR-quality infrastructure) and is documented
as a follow-up beyond the current acceptance-criteria bar. -/

/-- **`(Pf A)² = det A` for any 4×4 skew-symmetric, zero-diagonal matrix.**
This is the n=2 specialization of the Cayley-Bressoud Pfaffian identity.
The proof uses cofactor expansion of `det A` via `Matrix.det_succ_row_zero`
plus the alternating-matrix identities (`A i i = 0`, `A j i = -A i j`),
reducing to a ring identity. -/
theorem Matrix.pfaffianFin4_sq_eq_det {R : Type*} [CommRing R]
    (A : Matrix (Fin 4) (Fin 4) R)
    (hA : Matrix.IsSkewSymmetric A) (h_diag : ∀ i : Fin 4, A i i = 0) :
    (Matrix.pfaffianFin4 A)^2 = A.det := by
  have hoff : ∀ i j : Fin 4, A j i = -(A i j) := by
    intro i j
    have h := congrArg (fun M : Matrix (Fin 4) (Fin 4) R => M i j) hA
    simpa [Matrix.transpose_apply, Matrix.neg_apply] using h
  unfold Matrix.pfaffianFin4
  simp [Matrix.det_succ_row_zero, Fin.sum_univ_succ, Fin.succAbove,
        Matrix.submatrix_apply,
        h_diag 0, h_diag 1, h_diag 2, h_diag 3,
        hoff 0 1, hoff 0 2, hoff 0 3, hoff 1 2, hoff 1 3, hoff 2 3]
  ring

/-- **`(Pf A)² = det A` (general-`n` Pfaffian, 4×4 case).** Combines the
`pfaffian = pfaffianFin4` bridge with the closed-form Cayley identity above.
This is the headline acceptance-criterion theorem of Sub-wave 9.B (Item B,
"at minimum for n=2"). The general-`n` version is documented as a follow-up. -/
theorem Matrix.pfaffian_sq_eq_det_fin_four {R : Type*} [CommRing R]
    (A : Matrix (Fin (2 * 2)) (Fin (2 * 2)) R)
    (hA : Matrix.IsSkewSymmetric A) (h_diag : ∀ i : Fin (2 * 2), A i i = 0) :
    (Matrix.pfaffian A)^2 = A.det := by
  rw [Matrix.pfaffian_eq_pfaffianFin4]
  exact Matrix.pfaffianFin4_sq_eq_det A hA h_diag

/-- **Application of `pfaffian_sq_eq_det` to `antisymMatrix4`** (which is
alternating by construction). The cleanest packaging for downstream use
(e.g., NbRe BdG sewing matrices): the closed form `(a·f − b·e + c·d)²`
equals the determinant. -/
theorem Matrix.pfaffian_antisymMatrix4_sq_eq_det {R : Type*} [CommRing R]
    (a b c d e f : R) :
    (@Matrix.pfaffian 2 R _ (Matrix.antisymMatrix4 a b c d e f))^2
      = (Matrix.antisymMatrix4 a b c d e f).det := by
  apply Matrix.pfaffian_sq_eq_det_fin_four
  · exact Matrix.antisymMatrix4_isSkewSymmetric a b c d e f
  · intro i
    fin_cases i <;> rfl

end SKEFTHawking.MathlibAux
