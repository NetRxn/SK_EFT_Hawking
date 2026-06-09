/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 1(b) — conjugation on `ℤ[√2][i] = GaussInt2`

Complex conjugation `conj(re + im·i) = re − im·i` on `GaussInt2`, a ring homomorphism (the extension
`ℤ[√2][i]/ℤ[√2]` is degree 2) with `x · conj x = N(x)` (the relative norm, a real element). This is
the next foundational bit toward the `GaussInt2` `EuclideanDomain` (whose division step is
`x / y = round(x · conj y / N y)`) and the two-squares-over-ℤ[√2] descent.

## Headlines

  * `GaussInt2.conj` (+ `conj_re`/`conj_im`/`conj_conj`) — the conjugation involution.
  * `GaussInt2.conj_add`/`conj_mul`/`conj_zero`/`conj_one` — conjugation is a ring homomorphism.
  * `GaussInt2.mul_conj` — `x · conj x = ⟨N x, 0⟩` (the real relative norm).
  * `GaussInt2.norm_conj` — `N (conj x) = N x`.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide`. Kernel-pure `{propext, Classical.choice, Quot.sound}`.
-/

import SKEFTHawking.FKLW.RossSelinger.Zsqrt2GaussianInt

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace GaussInt2

/-- **Complex conjugation** on `ℤ[√2][i]`: `conj(re + im·i) = re − im·i`. -/
def conj (x : GaussInt2) : GaussInt2 := ⟨x.re, -x.im⟩

@[simp] theorem conj_re (x : GaussInt2) : (conj x).re = x.re := rfl
@[simp] theorem conj_im (x : GaussInt2) : (conj x).im = -x.im := rfl

@[simp] theorem conj_conj (x : GaussInt2) : conj (conj x) = x := by
  ext <;> simp

@[simp] theorem conj_zero : conj 0 = 0 := by ext <;> simp
@[simp] theorem conj_one : conj 1 = 1 := by ext <;> simp

@[simp] theorem conj_add (x y : GaussInt2) : conj (x + y) = conj x + conj y := by
  ext <;> simp <;> ring

/-- **Conjugation is multiplicative** (a ring homomorphism, since `ℤ[√2][i]` is commutative). -/
theorem conj_mul (x y : GaussInt2) : conj (x * y) = conj x * conj y := by
  ext <;> simp <;> ring

/-- **`x · conj x` is the relative norm** `N x = re² + im²` (a real element, `im`-part `0`). -/
theorem mul_conj (x : GaussInt2) : x * conj x = ⟨x.norm, 0⟩ :=
  GaussInt2.ext (mul_conj_re x) (mul_conj_im x)

/-- **Conjugation preserves the relative norm**: `N (conj x) = N x`. -/
@[simp] theorem norm_conj (x : GaussInt2) : (conj x).norm = x.norm := by
  simp only [norm_def, conj_re, conj_im]; ring

end GaussInt2

end SKEFTHawking.RossSelinger
