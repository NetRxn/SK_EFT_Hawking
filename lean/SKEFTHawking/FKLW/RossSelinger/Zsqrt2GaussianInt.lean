/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 — `ℤ[√2][i]` (Gaussian integers over `ℤ[√2]`), for two-squares-over-ℤ[√2]

The two-squares-over-`ℤ[√2]` theorem (Ross thesis Prop 3.2.7, reduced via
`RelativeNorm.exists_relativeNorm_of_real_sumSq`) is the statement that a totally-positive
`β ∈ ℤ[√2]` whose absolute norm `N(β) = β•β` is a rational prime `≡ 1 (mod 8)` is a sum of two
squares `β = p² + q²` in `ℤ[√2]`. The classical proof is the Gaussian-integer descent **one level
up**: `β = p² + q² ⟺ β` splits in `ℤ[√2][i]`, and a `ℤ[√2]`-prime `β` with residue field `𝔽_n`
(`n = N(β)` prime) splits iff `−1` is a QR in `𝔽_n` iff `n ≡ 1 (mod 4)` (implied by `≡ 1 mod 8`).

This file builds `GaussInt2 = ℤ[√2][i]` — the **GaussianInt template over the `ℤ[√2]`
EuclideanDomain base** (`Zsqrt2EuclideanDomain.lean`). Its relative norm `re² + im²` is
positive-definite over both real places of `ℤ[√2]`, so (unlike `ℤ[√2]` itself) the
norm-Euclidean construction transfers cleanly. This file ships the **ring foundation**
(structure + `CommRing`); the `EuclideanDomain` and the splitting descent are the next bricks.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.Zsqrt2EuclideanDomain

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

/-- **`ℤ[√2][i]`** — Gaussian integers over `ℤ[√2] = Zsqrtd 2`: pairs `re + im·i` with `i² = −1`.
The base ring `ℤ[√2]` is a `EuclideanDomain` (`Zsqrt2EuclideanDomain.lean`); this is the degree-2
extension whose relative norm `re² + im²` drives the two-squares-over-`ℤ[√2]` descent. -/
@[ext] structure GaussInt2 where
  re : Zsqrtd 2
  im : Zsqrtd 2
deriving DecidableEq

namespace GaussInt2

instance : Zero GaussInt2 := ⟨⟨0, 0⟩⟩
instance : One GaussInt2 := ⟨⟨1, 0⟩⟩
instance : Add GaussInt2 := ⟨fun x y => ⟨x.re + y.re, x.im + y.im⟩⟩
instance : Neg GaussInt2 := ⟨fun x => ⟨-x.re, -x.im⟩⟩
instance : Sub GaussInt2 := ⟨fun x y => ⟨x.re - y.re, x.im - y.im⟩⟩
/-- Gaussian multiplication: `(a+bi)(c+di) = (ac − bd) + (ad + bc)i`. -/
instance : Mul GaussInt2 := ⟨fun x y => ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩⟩

@[simp] theorem zero_re : (0 : GaussInt2).re = 0 := rfl
@[simp] theorem zero_im : (0 : GaussInt2).im = 0 := rfl
@[simp] theorem one_re : (1 : GaussInt2).re = 1 := rfl
@[simp] theorem one_im : (1 : GaussInt2).im = 0 := rfl
@[simp] theorem add_re (x y : GaussInt2) : (x + y).re = x.re + y.re := rfl
@[simp] theorem add_im (x y : GaussInt2) : (x + y).im = x.im + y.im := rfl
@[simp] theorem neg_re (x : GaussInt2) : (-x).re = -x.re := rfl
@[simp] theorem neg_im (x : GaussInt2) : (-x).im = -x.im := rfl
@[simp] theorem sub_re (x y : GaussInt2) : (x - y).re = x.re - y.re := rfl
@[simp] theorem sub_im (x y : GaussInt2) : (x - y).im = x.im - y.im := rfl
@[simp] theorem mul_re (x y : GaussInt2) : (x * y).re = x.re * y.re - x.im * y.im := rfl
@[simp] theorem mul_im (x y : GaussInt2) : (x * y).im = x.re * y.im + x.im * y.re := rfl

/-- **`ℤ[√2][i]` is a commutative ring.** Component-wise axioms over the `CommRing ℤ[√2]`. -/
instance : CommRing GaussInt2 where
  nsmul := nsmulRec
  zsmul := zsmulRec
  add_assoc := by intros; ext <;> simp <;> ring
  zero_add := by intros; ext <;> simp
  add_zero := by intros; ext <;> simp
  add_comm := by intros; ext <;> simp <;> ring
  left_distrib := by intros; ext <;> simp <;> ring
  right_distrib := by intros; ext <;> simp <;> ring
  zero_mul := by intros; ext <;> simp
  mul_zero := by intros; ext <;> simp
  mul_assoc := by intros; ext <;> simp <;> ring
  one_mul := by intros; ext <;> simp
  mul_one := by intros; ext <;> simp
  mul_comm := by intros; ext <;> simp <;> ring
  neg_add_cancel := by intros; ext <;> simp
  sub_eq_add_neg := by intros; ext <;> simp [sub_eq_add_neg]

/-- **The relative norm** `N : ℤ[√2][i] → ℤ[√2]`, `N(re + im·i) = re² + im²`. Positive-definite
over both real places of `ℤ[√2]` (so the norm-Euclidean construction transfers from the `ℤ[√2]`
ED base) and multiplicative; `β = p² + q²` in `ℤ[√2]` ⟺ `β` is a relative norm from here. -/
def norm (x : GaussInt2) : Zsqrtd 2 := x.re ^ 2 + x.im ^ 2

@[simp] theorem norm_def (x : GaussInt2) : x.norm = x.re ^ 2 + x.im ^ 2 := rfl

/-- **The relative norm is multiplicative** (Brahmagupta–Fibonacci identity over `ℤ[√2]`). -/
theorem norm_mul (x y : GaussInt2) : (x * y).norm = x.norm * y.norm := by
  simp only [norm_def, mul_re, mul_im]; ring

/-- The relative norm of the conjugate-product `(re + im·i)(re − im·i) = re² + im² = N`. -/
theorem mul_conj_re (x : GaussInt2) :
    (x * ⟨x.re, -x.im⟩).re = x.norm := by simp only [mul_re, norm_def]; ring

@[simp] theorem mul_conj_im (x : GaussInt2) : (x * ⟨x.re, -x.im⟩).im = 0 := by
  simp only [mul_im]; ring

end GaussInt2

end SKEFTHawking.RossSelinger
