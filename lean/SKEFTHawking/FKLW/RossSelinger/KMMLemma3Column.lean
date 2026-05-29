/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F (M4) — KMM Lemma 3 lifted to `ZOmega` columns

`KMMLemma3.lean` proves KMM Lemma 3 over the residue ring `ℤ[ω]/(2³)`
(`kmm_lemma3_alg2`, over the residue-level `Coord4.gde`). `PropOneBridge.lean`
connects `Coord4.gde (coordOf ·)` to the genuine `√2`-gde of the squared modulus
(`coord4_gde_coordOf`). This file uses both to lift Lemma 3 onto actual `ZOmega`
elements.

  * `coordOf_add` — `coordOf` is additive (`coordOf (x+y) = add (coordOf x) (coordOf y)`).
  * `coordOf_omega_pow_mul` — `coordOf (ωᵏ·y) = mulOmegaPow k (coordOf y)`.
  * `kmm_lemma3_column` — **the `ZOmega`-level Lemma 3**: for `x, y` with
    `gde(|x|²) = gde(|y|²) = j ∈ {0,1}` and the unit-column congruences
    `(|x|²+|y|²).d ≡ (|x|²+|y|²).c ≡ 0 (mod 8)`, for each target `s+1 ∈ {1,2,3}`
    there is `k ∈ {0,1,2,3}` with `gde(|x+ωᵏy|²) = (s+1)+j`.

The `s = 2` case (target `gde` increment `3`) is the sde-reducing step; the
congruence hypotheses are exactly what the unit-column condition `|x|²+|y|²=2^m`
(`m ≥ 3`) supplies (the rational part is `2^m ≡ 0 (mod 8)`, the `√2`-part is `0`).
This is the fuel-sufficiency input for the `kmmReduce` discharge, modulo the
matrix-level translation of `gde(|·|²)` to `sdeC`.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected. `kmm_lemma3_column` inherits
  the `Lean.ofReduceBool` axiom from `kmm_lemma3_alg2` (KMM Algorithm 2's
  computer check); the `coordOf_*` homomorphism lemmas are kernel-pure.

-/

import SKEFTHawking.FKLW.RossSelinger.PropOneBridge

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmega

/-- **`coordOf` is additive**: the `mod 8` residue of a sum is the residue sum. -/
theorem coordOf_add (x y : ZOmega) :
    coordOf (x + y) = KMM.Coord4.add (coordOf x) (coordOf y) := by
  simp only [coordOf, KMM.Coord4.add, add_a, add_b, add_c, add_d]
  push_cast
  ring_nf

/-- **`coordOf` of `ωᵏ·y`** is the iterated residue `ω`-action: `coordOf (ωᵏ·y) =
mulOmegaPow k (coordOf y)`. Induction on `k` via `coordOf_omega_mul`. -/
theorem coordOf_omega_pow_mul (k : ℕ) (y : ZOmega) :
    coordOf (ω ^ k * y) = KMM.Coord4.mulOmegaPow k (coordOf y) := by
  induction k with
  | zero => simp [KMM.Coord4.mulOmegaPow]
  | succ n ih => rw [pow_succ', mul_assoc, coordOf_omega_mul, ih]; rfl

/-- **KMM Lemma 3 on `ZOmega` columns.** For `x, y : ZOmega` with equal base gde
`gde(|x|²) = gde(|y|²) = j ∈ {0,1}` (KMM Lemma 4) satisfying the unit-column
congruences `2·(|x|²+|y|²).d ≡ 0` (i.e. `(|x|²+|y|²).d ∈ {0,4}`) and
`(|x|²+|y|²).c ≡ 0 (mod 8)` (from `|x|²+|y|² = 2^m`, `m ≥ 2`; `2^m ≡ 0` for
`m ≥ 3` and `≡ 4` for `m = 2`), and each target `s+1 ∈ {1,2,3}`, there is
`k ∈ {0,1,2,3}` with `gde(|x+ωᵏy|²) = (s+1)+j`. The `≡ 4` case is the
`sde(|z|²) = 4` boundary (`m = 2`).

The faithful `ZOmega`-image of the residue-level `kmm_lemma3_alg2`: apply it to
`coordOf x`, `coordOf y` (the gde, `Pform`/`Qform`-sum hypotheses come from
`coord4_gde_coordOf`, `Pform_coordOf`/`Qform_coordOf`), then read the conclusion
back through `coordOf_add` + `coordOf_omega_pow_mul` + `coord4_gde_coordOf`. The
`s = 2` instance (gde increment `3`) is the sde-reducing `k`. -/
theorem kmm_lemma3_column (x y : ZOmega) (j : ℕ) (hj : j < 2)
    (hx : gdePeel (normSq x) 4 = j) (hy : gdePeel (normSq y) 4 = j)
    (hP : 2 * ((normSq x + normSq y).d : ZMod 8) = 0)
    (hQ : ((normSq x + normSq y).c : ZMod 8) = 0)
    (s : ℕ) (hs : s < 3) :
    ∃ k : ℕ, k < 4 ∧ gdePeel (normSq (x + ω ^ k * y)) 4 = (s + 1) + j := by
  have hgx : KMM.Coord4.gde (coordOf x) = j := (coord4_gde_coordOf x).trans hx
  have hgy : KMM.Coord4.gde (coordOf y) = j := (coord4_gde_coordOf y).trans hy
  have hsumd : ((normSq x).d : ZMod 8) + ((normSq y).d : ZMod 8)
      = ((normSq x + normSq y).d : ZMod 8) := by rw [add_d]; push_cast; ring
  have hPP : 2 * (KMM.Coord4.Pform (coordOf x) + KMM.Coord4.Pform (coordOf y)) = 0 := by
    rw [Pform_coordOf, Pform_coordOf, hsumd]; exact hP
  have hQQ : KMM.Coord4.Qform (coordOf x) + KMM.Coord4.Qform (coordOf y) = 0 := by
    rw [Qform_coordOf, Qform_coordOf]
    have hsum : ((normSq x).c : ZMod 8) + ((normSq y).c : ZMod 8)
        = ((normSq x + normSq y).c : ZMod 8) := by rw [add_c]; push_cast; ring
    rw [hsum, hQ]
  obtain ⟨k, hk⟩ := KMM.kmm_lemma3_alg2 (coordOf x) (coordOf y) ⟨j, hj⟩ hgx hgy hPP hQQ ⟨s, hs⟩
  refine ⟨k.val, k.isLt, ?_⟩
  have hcoord : KMM.Coord4.add (coordOf x) (KMM.Coord4.mulOmegaPow k.val (coordOf y))
      = coordOf (x + ω ^ (k.val) * y) := by
    rw [coordOf_add, coordOf_omega_pow_mul]
  rw [← coord4_gde_coordOf, ← hcoord, hk]

end ZOmega

end SKEFTHawking.RossSelinger
