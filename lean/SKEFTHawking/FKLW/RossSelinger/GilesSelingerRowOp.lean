/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 2 (increment 22) — Giles–Selinger Lemma 4, the row-operation CORE STEP

The dim-4 column lemma's reduction (`ReductionStep`, `ColumnBaseRealizable`) is the **Giles–Selinger
column lemma** (arXiv:1212.0506): Lemma 5 (parity) supplies a **matching residue-norm pair**
(`exists_matching_residue_pair`, inc 21), and **Lemma 4** (this file) is the explicit `H/T` two-level
**row operation** that, applied to such a pair, lowers the denominator exponent.

## The kernel-confirmed construction (the 3 residue-norm cases)

Over `ℤ[ω]/2` (16 residues; `ω`-action `(a,b,c,d) ↦ (b,c,d,a)`, period 4 since `ω⁴ ≡ 1`), the **active**
residues (`¬ √2 ∣ ·`, i.e. residue norm `≠ 0000`) split by residue norm `(P,Q) = (a²+b²+c²+d², ab+bc+cd−ad)`
mod 2 — verified by `#eval` enumeration:

| residue norm | mod-2 residues | `ω`-orbits |
|---|---|---|
| `(P,Q)=(0,1)` ["1010"] | `{3,6,9,12}` | **one** orbit |
| `(P,Q)=(1,0)` ["0001"] | `{1,2,4,8} ∪ {7,11,13,14}` | **two** orbits `O₁, O₂` with `O₂ = O₁ ⊕ 1111` |

(The two `0001` sets are exactly Giles–Selinger's Case-3 sets `{0001,0010,0100,1000}` and
`{0111,1110,1101,1011}`.) Consequence:

  * **Same `ω`-orbit** (`x ≡ ωᵐy (mod 2)` for some `m`): a SINGLE `H·Tᵐ` drops both entries one level —
    this is `core_step` below. Covers the whole `1010` class (single orbit) and the same-orbit
    `0001` sub-case.
  * **Cross-orbit** (`0001`, one entry in `O₁`, the other in `O₂`): a 2-step `1111`-bridge (a follow-on
    increment) reduces to the same-orbit case.

## This increment: the core step

`core_step` — when the matched pair is mod-2 `ω`-aligned (`2 ∣ x − ωᵐy`), the two-level `H·Tᵐ`
combination `(x ± ωᵐy)/√2` lands at `denExp ≤ t` (from input level `t+1`): **both entries drop one
denominator level.** Mechanism: `2 ∣ x − ωᵐy` ⟹ `2 ∣ x + ωᵐy` (both `H`-combinations), and a
`2 = √2²`-divisible numerator at level `t+2` clears to `denExp ≤ t` (`denExp_mk_le_of_two_dvd`).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide` (the only `decide` is `√2·√2 = 2`, a kernel `decide`). Kernel-pure
  `{propext, Classical.choice, Quot.sound}`.
-/

import SKEFTHawking.FKLW.RossSelinger.AncillaState
import SKEFTHawking.FKLW.RossSelinger.ReduceStepColumn
import SKEFTHawking.FKLW.RossSelinger.MatchingResidue

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmega

/-- **Both Hadamard combinations clear together**: `2 ∣ x − y ⟹ 2 ∣ x + y` (since
`x + y = (x − y) + 2y`). So if the `−` combination is `2`-divisible, the `+` one is too. -/
theorem two_dvd_add_of_two_dvd_sub {x y : ZOmega} (h : (2 : ZOmega) ∣ (x - y)) :
    (2 : ZOmega) ∣ (x + y) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w + y, by rw [mul_add, ← hw]; ring⟩

end ZOmega

namespace ZOmegaSqrt2

/-- **A `2`-divisible numerator at level `k+2` clears to denominator exponent `≤ k`.** Since
`2 = √2²`, a numerator `2·w` peels two `√2` factors: `(2w)/√2^{k+2} = w/√2^k`. This is the
denominator-drop engine for the row-operation core step. -/
theorem denExp_mk_le_of_two_dvd {z : ZOmega} (h : (2 : ZOmega) ∣ z) (k : ℕ) :
    denExp (mk z (k + 2)) ≤ k := by
  obtain ⟨w, rfl⟩ := h
  rw [show (2 : ZOmega) * w = ZOmega.sqrt2 * (ZOmega.sqrt2 * w) from by
        rw [← mul_assoc]; norm_num [show ZOmega.sqrt2 * ZOmega.sqrt2 = (2 : ZOmega) from by decide],
      denExp_mk, show k + 2 = (k + 1) + 1 from rfl,
      ZOmega.lowestDenExp_sqrt2_mul, ZOmega.lowestDenExp_sqrt2_mul]
  exact ZOmega.lowestDenExp_le _ _

/-- **Same-denominator subtraction**: `mk a k − mk b k = mk (a − b) k`. -/
theorem mk_sub_same (a b : ZOmega) (k : ℕ) : mk a k - mk b k = mk (a - b) k := by
  rw [sub_eq_add_neg, mk_neg, mk_add_same, ← sub_eq_add_neg]

/-- **Giles–Selinger Lemma-4 core step.** For a matched pair that is mod-2 `ω`-aligned
(`2 ∣ x − ωᵐy`), the two-level `H·Tᵐ` operation drops BOTH entries one denominator level: each
combination `(x ± ωᵐy)/√2` (entries at input level `t+1`, written `invSqrt2 · (mk x (t+1) ± ωᵏ·mk y (t+1))`)
has `denExp ≤ t`. This is the single-`H·Tᵐ` case of Lemma 4 — it covers the whole `1010` residue-norm
class and the same-`ω`-orbit `0001` sub-case (see the module docstring's orbit table). -/
theorem core_step {x y : ZOmega} {m t : ℕ} (h : (2 : ZOmega) ∣ (x - ZOmega.ω ^ m * y)) :
    denExp (invSqrt2 * (mk x (t + 1) + CliffordTGate.ωS ^ m * mk y (t + 1))) ≤ t ∧
    denExp (invSqrt2 * (mk x (t + 1) - CliffordTGate.ωS ^ m * mk y (t + 1))) ≤ t := by
  have hpow : of (ZOmega.ω ^ m) = (of ZOmega.ω) ^ m := map_pow ofRingHom ZOmega.ω m
  have hmul : CliffordTGate.ωS ^ m * mk y (t + 1) = mk (ZOmega.ω ^ m * y) (t + 1) := by
    rw [show (CliffordTGate.ωS : ZOmegaSqrt2) = of ZOmega.ω from rfl, ← hpow, of_def, mk_mul,
        Nat.zero_add]
  have hinv : ∀ z : ZOmega, invSqrt2 * mk z (t + 1) = mk z (t + 2) := fun z => by
    rw [invSqrt2_def, mk_mul, one_mul, show 1 + (t + 1) = t + 2 from by omega]
  refine ⟨?_, ?_⟩
  · rw [hmul, mk_add_same, hinv]
    exact denExp_mk_le_of_two_dvd (ZOmega.two_dvd_add_of_two_dvd_sub h) t
  · rw [hmul, mk_sub_same, hinv]
    exact denExp_mk_le_of_two_dvd h t

end ZOmegaSqrt2

end SKEFTHawking.RossSelinger
