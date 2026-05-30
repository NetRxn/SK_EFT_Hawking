/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Items G/H — the Ross-Selinger grid-problem solver (foundation)

The Ross-Selinger constructive synthesis (arXiv:1403.2975 §5) decomposes as:
  (a) `epsilonRegion θ ε` — the convex target region in `ℂ`;
  (b) `gridSolutions A B k` — enumerate `u ∈ ℤ[ω][1/√2]` with `u ∈ A`, Galois `u• ∈ B`;
  (c) `diophantine u k` — solve `t·t* = √2^{2k} − u·u*` in `ℤ[ω]`;
  (d) `assembleUnitary u t k` — `M = [[u, −t*],[t, u*]]/√2^k` (this file);
  (e) `kmmReduce` — the exact Clifford+T word (SHIPPED, `KMM.lean` / `CliffordBase.lean`).

This file ships step (d) (the assembly) *with its unitarity proof*, plus the cleared-ring
helpers it rests on. Steps (a)–(c) — the convex-geometry ε-region and the `ℤ[ω]`
prime-factorization Diophantine, the analytic core of the solver — are the next increment
(deterministic branch only; NO §4 factoring fast-path). Validated end-to-end in
`scripts/grid_stub_validation.py`: the (c)+(d) core yields an exactly realizable `det`-1
`SU(2)` matrix for every sample target.

## Headline results

  * `ZOmegaSqrt2.normSq_mk : normSq (mk z k) = mk (ZOmega.normSq z) (2*k)`.
  * `ZOmegaSqrt2.conj_neg`, `ZOmegaSqrt2.sqrt2_pow_two_mul` — cleared-ring `*`-involution and
    `√2^{2k} = ⟨0,0,0,2^k⟩` integer-column identities.
  * `assembleUnitary u t k = !![mk u k, −conj (mk t k); mk t k, conj (mk u k)]`.
  * `colNormSq` — the shared `normSq (mk u k) + normSq (mk t k) = 1` column identity.
  * `isUnitaryT_assembleUnitary` — `u·u* + t·t* = √2^{2k} ⟹ IsUnitaryT (assembleUnitary u t k)`.
  * `det_assembleUnitary` — same constraint `⟹ det = 1`, so `assembleUnitary u t k ∈ SU(2)`.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.UnitaryT
import SKEFTHawking.FKLW.RossSelinger.Conj
import SKEFTHawking.FKLW.RossSelinger.NormSqGde
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmegaSqrt2

/-- **Squared modulus of a cleared element**: `normSq (mk z k) = mk (|z|²_{ℤ[ω]}) (2k)`
— the `ZOmegaSqrt2` squared-modulus of `z/√2^k` is the `ℤ[ω]` squared-modulus of `z` over
`√2^{2k}`. (`conj_mk` + `mk_mul`; `ZOmega.normSq z = z·conj z`.) -/
theorem normSq_mk (z : ZOmega) (k : ℕ) : normSq (mk z k) = mk (ZOmega.normSq z) (2 * k) := by
  rw [normSq, conj_mk, mk_mul, ZOmega.normSq, two_mul]

/-- **Conjugation negates** over `ZOmegaSqrt2` (the `*`-involution is additive). Derived from
`conj_add` + `conj_zero`; `ZOmegaSqrt2` has no bundled `conj` ring-hom, so this fills the gap
the `ZOmega`-level `ZOmega.conj_neg` leaves at the cleared-ring level. -/
theorem conj_neg (x : ZOmegaSqrt2) : conj (-x) = -conj x :=
  eq_neg_of_add_eq_zero_left (by rw [← conj_add, neg_add_cancel, conj_zero])

/-- **`√2^{2k}` is the integer `2^k`** inside `ℤ[ω]`: `ZOmega.sqrt2 ^ (2k) = ⟨0,0,0,2^k⟩`.
The "real-integer column" identity that converts the Diophantine denominator `√2^{2k}` into a
plain integer (`Coords.d = 2^k`, all other coords `0`); the backbone of the `assembleUnitary`
unitarity proof and of step (c)'s norm equation `u·u* + t·t* = √2^{2k}`. -/
theorem sqrt2_pow_two_mul (k : ℕ) : ZOmega.sqrt2 ^ (2 * k) = (⟨0, 0, 0, 2 ^ k⟩ : ZOmega) := by
  induction k with
  | zero => decide
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 2 from by ring, pow_add, ih,
      show ZOmega.sqrt2 ^ 2 = (⟨0, 0, 0, 2⟩ : ZOmega) from by decide]
    show (⟨0, 0, 0, 2 ^ n⟩ : ZOmega) * ⟨0, 0, 0, 2⟩ = ⟨0, 0, 0, 2 ^ (n + 1)⟩
    ext <;> simp [pow_succ]

end ZOmegaSqrt2

namespace KMM

open ZOmegaSqrt2
open scoped Matrix

/-- **(d) Assemble** the Ross-Selinger unitary from a solved `(u, t)` pair at denominator
exponent `k`: `M = [[u, −t*], [t, u*]] / √2^k` over `ZOmegaSqrt2`. When `u·u* + t·t* =
√2^{2k}` (the Diophantine constraint) this is special unitary (`det = 1`, columns
orthonormal) — validated in `scripts/grid_stub_validation.py`; the Lean `IsUnitaryT`
proof (via `normSq_mk` + the column identities) is the next increment. -/
noncomputable def assembleUnitary (u t : ZOmega) (k : ℕ) : Mat2 :=
  !![mk u k, -(conj (mk t k)); mk t k, conj (mk u k)]

@[simp] theorem assembleUnitary_apply_zero_zero (u t : ZOmega) (k : ℕ) :
    assembleUnitary u t k 0 0 = mk u k := rfl
@[simp] theorem assembleUnitary_apply_one_zero (u t : ZOmega) (k : ℕ) :
    assembleUnitary u t k 1 0 = mk t k := rfl

/-- **Column squared-norm** under the Diophantine constraint: when `u·u* + t·t* = √2^{2k}`
(`= ⟨0,0,0,2^k⟩` in `ℤ[ω]` coords), the cleared column `(mk u k, mk t k)` is a unit vector:
`normSq (mk u k) + normSq (mk t k) = 1` (`normSq_mk` + `mk_add` + `sqrt2_pow_two_mul`). The
shared backbone of both unitarity and `det = 1`. -/
theorem colNormSq (u t : ZOmega) (k : ℕ)
    (h : ZOmega.normSq u + ZOmega.normSq t = (⟨0, 0, 0, 2 ^ k⟩ : ZOmega)) :
    normSq (mk u k) + normSq (mk t k) = 1 := by
  rw [normSq_mk, normSq_mk, mk_add, one_def, mk_eq_mk_iff, pow_zero, mul_one, one_mul,
      ← add_mul, h, ← sqrt2_pow_two_mul k, ← pow_add]

/-- **`assembleUnitary` produces a genuine unitary** over `ZOmegaSqrt2` whenever the solved
`(u, t)` pair satisfies the Ross-Selinger Diophantine constraint `u·u* + t·t* = √2^{2k}`
(equivalently, in `ℤ[ω]` coords, `= ⟨0,0,0,2^k⟩`): `M† · M = 1`. This is the formal
counterpart of the `okreal` check in `scripts/grid_stub_validation.py`. The two diagonal
entries collapse to `colNormSq`; the two off-diagonal entries vanish by commutativity
(`ring`, since the runtime `ZOmegaSqrt2` is a `CommRing`). With `det_assembleUnitary`, `M ∈
SU(2)` over `ℤ[ω][1/√2]` — exactly the realizable class fed to `kmmReduce`. -/
theorem isUnitaryT_assembleUnitary (u t : ZOmega) (k : ℕ)
    (h : ZOmega.normSq u + ZOmega.normSq t = (⟨0, 0, 0, 2 ^ k⟩ : ZOmega)) :
    IsUnitaryT (assembleUnitary u t k) := by
  have hcol := colNormSq u t k h
  have a01 : assembleUnitary u t k 0 1 = -(conj (mk t k)) := rfl
  have a11 : assembleUnitary u t k 1 1 = conj (mk u k) := rfl
  rw [IsUnitaryT, ← Matrix.ext_iff]
  simp only [Fin.forall_fin_two, Matrix.mul_apply, Fin.sum_univ_two, adjoint_apply,
    assembleUnitary_apply_zero_zero, assembleUnitary_apply_one_zero, a01, a11,
    conj_neg, conj_conj]
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · rw [Matrix.one_apply_eq, ← hcol, normSq, normSq]; ring
  · rw [Matrix.one_apply_ne (by decide : (0 : Fin 2) ≠ 1)]; ring
  · rw [Matrix.one_apply_ne (by decide : (1 : Fin 2) ≠ 0)]; ring
  · rw [Matrix.one_apply_eq, ← hcol, normSq, normSq]; ring

/-- **`assembleUnitary` is special** (`det = 1`) under the same Diophantine constraint, so its
output lands in `SU(2)` over `ℤ[ω][1/√2]` — the `k = 0` (det `ωS^0 = 1`) realizable class.
`det_fin_two` gives `M₀₀·M₁₁ − M₀₁·M₁₀ = (mk u k)·conj (mk u k) + conj (mk t k)·(mk t k) =
colNormSq = 1`. Together with `isUnitaryT_assembleUnitary` this certifies `M ∈ SU(2)`. -/
theorem det_assembleUnitary (u t : ZOmega) (k : ℕ)
    (h : ZOmega.normSq u + ZOmega.normSq t = (⟨0, 0, 0, 2 ^ k⟩ : ZOmega)) :
    Matrix.det (assembleUnitary u t k) = 1 := by
  rw [Matrix.det_fin_two, assembleUnitary_apply_zero_zero, assembleUnitary_apply_one_zero,
      show assembleUnitary u t k 0 1 = -(conj (mk t k)) from rfl,
      show assembleUnitary u t k 1 1 = conj (mk u k) from rfl,
      ← colNormSq u t k h, normSq, normSq]
  ring

end KMM

end SKEFTHawking.RossSelinger
