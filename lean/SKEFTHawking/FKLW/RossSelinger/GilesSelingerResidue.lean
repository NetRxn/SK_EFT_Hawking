/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 2 (increment 18) — Giles–Selinger residue-norm classification

The KMM (arXiv:1212.0822) circuit `C` is the **Giles–Selinger column lemma** (arXiv:1212.0506, Lemma 20),
whose reduction is **elementary**: a parity argument on entry residue-NORMS modulo 2 (Lemma 5) plus an
explicit 3-case H/T row operation (Lemma 4). This file ships the number-theoretic entry point: the
**residue-norm classification** — Giles–Selinger's fact that for `z ∈ ℤ[ω]`, the squared modulus `|z|²`
has residue norm `mod 2` in the THREE classes `{0000, 0001, 1010}` (never `1011`).

Concretely, with `|z|² = ⟨−Q, 0, Q, P⟩` (`normSq_coords`; `P = a²+b²+c²+d²`, `Q = ab−ad+cb+cd`), modulo 2:
`P ≡ a+b+c+d = u+v` and `Q ≡ ab+ad+cb+cd = (a+c)(b+d) = u·v` where `u = a+c`, `v = b+d`. So
`(P mod 2, Q mod 2) ∈ {(0,0), (1,0), (0,1)}` — the case `(1,1)` is impossible (`Q ≡ 1 ⟹ u = v = 1 ⟹
P ≡ 0`). The headline of this file is exactly that exclusion: `(|z|²).c` and `(|z|²).d` are never both odd.

This is the seed of the Lemma-5 parity argument (the unit column `Σ|wᵢ|² = 2^s` forces an even number of
each irreducible residue-norm class, so a matching pair exists for the Lemma-4 reduction).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide` (the `decide` is KERNEL `decide` over `(ZMod 2)⁴`, 16 cases). Kernel-pure.
-/

import SKEFTHawking.FKLW.RossSelinger.RelativeNorm
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmega

/-- **Integer `% 2 = 0` from a `ZMod 2` vanishing** (the `ℤ ↔ 𝔽₂` bridge). -/
private theorem emod_two_eq_zero_of_zmod {n : ℤ} (h : (n : ZMod 2) = 0) : n % 2 = 0 :=
  Int.emod_eq_zero_of_dvd (by exact_mod_cast (ZMod.intCast_zmod_eq_zero_iff_dvd n 2).mp h)

/-- **Giles–Selinger residue-norm classification (the `{0000, 0001, 1010}` exclusion of `1011`).**
For `z ∈ ℤ[ω]`, the `√2`-coordinate `(|z|²).c` and the rational coordinate `(|z|²).d` are **never both
odd**. Equivalently `(P mod 2, Q mod 2) ≠ (1,1)`: with `u = a+c`, `v = b+d`, `Q ≡ uv` and `P ≡ u+v`, so
`Q` odd forces `u = v = 1`, hence `P ≡ 0`. The three admissible residue norms are `0000` (`P,Q` even),
`0001` (`P` odd, `Q` even), `1010` (`P` even, `Q` odd). -/
theorem normSq_cd_not_both_odd (z : ZOmega) :
    (normSq z).c % 2 = 0 ∨ (normSq z).d % 2 = 0 := by
  obtain ⟨a, b, c, d⟩ := z
  simp only [normSq_coords]
  have key : ∀ x y w t : ZMod 2,
      x * y - x * t + w * y + w * t = 0 ∨ x ^ 2 + y ^ 2 + w ^ 2 + t ^ 2 = 0 := by decide
  rcases key (a : ZMod 2) (b : ZMod 2) (c : ZMod 2) (d : ZMod 2) with h | h
  · left
    refine emod_two_eq_zero_of_zmod ?_
    push_cast
    exact h
  · right
    refine emod_two_eq_zero_of_zmod ?_
    push_cast
    exact h

end ZOmega

end SKEFTHawking.RossSelinger
