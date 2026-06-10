/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 2 (increments 22–24) — Giles–Selinger Lemma 4, the row operation

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

## Contents

  * **inc 22 — `core_step`** (the mod-2-aligned drop): when the matched pair is mod-2 `ω`-aligned
    (`2 ∣ x − ωᵐy`), the two-level `H·Tᵐ` combination `(x ± ωᵐy)/√2` lands at `denExp ≤ t` (from input
    level `t+1`): **both entries drop one denominator level.** Mechanism: `2 ∣ x − ωᵐy` ⟹ `2 ∣ x + ωᵐy`
    (both `H`-combinations), and a `2 = √2²`-divisible numerator at level `t+2` clears to `denExp ≤ t`
    (`denExp_mk_le_of_two_dvd`). Covers `1010` + same-orbit `0001`.
  * **inc 23 — `exists_sqrt2_match`** (Lemma-4 brick A): every matched-active pair admits `∃m∈{0,1}`,
    `√2 ∣ (w_p − ωᵐw_q)` — so step1 keeps both entries at the common level. Proof: the mod-`√2` residue
    is determined by the norm class and `ω` swaps its components, so equal norm ⟹ same swap-orbit (a
    `ZMod 2` kernel `decide`). This opens the uniform 2-step that also handles the cross-orbit `0001` case.
  * **inc 24 — `exists_mod2_align_of_normSq_c_odd`** (Lemma-4 brick B″) + **`lemma4_1010`**: a `1010`-norm
    pair (`(normSq ·).c` odd; mod-2 residue in the single ω-orbit `{3,6,9,12}`) is mod-2 `ω`-aligned
    (`∃m, 2 ∣ w_p − ωᵐw_q`, the `core_step` hypothesis), so `lemma4_1010` reduces the whole `1010` case of
    Lemma 4 in a single `H·Tᵐ`. Brick B′ (cross-orbit `0001` step1 → outputs land in `1010`, the mod-4
    core) then reduces the cross-orbit case to `lemma4_1010`.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide` (the only `decide` is `√2·√2 = 2`, a kernel `decide`). Kernel-pure
  `{propext, Classical.choice, Quot.sound}`.
-/

import SKEFTHawking.FKLW.RossSelinger.AncillaState
import SKEFTHawking.FKLW.RossSelinger.ReduceStepColumn
import SKEFTHawking.FKLW.RossSelinger.MatchingResidue
import SKEFTHawking.FKLW.RossSelinger.GilesSelingerResidue
import Mathlib.Tactic.LinearCombination

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmega

/-- **Both Hadamard combinations clear together**: `2 ∣ x − y ⟹ 2 ∣ x + y` (since
`x + y = (x − y) + 2y`). So if the `−` combination is `2`-divisible, the `+` one is too. -/
theorem two_dvd_add_of_two_dvd_sub {x y : ZOmega} (h : (2 : ZOmega) ∣ (x - y)) :
    (2 : ZOmega) ∣ (x + y) := by
  obtain ⟨w, hw⟩ := h
  exact ⟨w + y, by rw [mul_add, ← hw]; ring⟩

/-- **Lemma-4 brick (A): the √2-match always exists.** Every matched residue-norm *active* pair
`(w_p, w_q)` (`¬ √2∣w_p`, `¬ √2∣w_q`, equal residue norms `(normSq ·).c, (normSq ·).d` mod 2) admits
`∃ m, √2 ∣ (w_p − ωᵐ w_q)` — in fact `m ∈ {0,1}` suffices. So step1 = `H·Tᵐ` keeps both entries at
the common level (also `√2 ∣ w_p + ωᵐw_q` by `dividesSqrt2_add_of_dividesSqrt2_sub`), the opening move
of the uniform 2-step row operation.

**Proof** (the clean swap-orbit argument): the mod-`√2` residue `r(z) = (z.a+z.c, z.b+z.d) mod 2`
(so `√2∣z ⟺ r(z)=0`) is determined by the residue norm class — `1010` `(P,Q)=(0,1) ⟹ r=(1,1)`,
`0001` `(1,0) ⟹ r∈{(0,1),(1,0)}` — and `ω` acts on `r` by *swapping* its two components, so equal
residue norm ⟹ same swap-orbit ⟹ `r(w_p) = r(ωᵐ w_q)` for `m=0` (residues equal) or `m=1` (swapped).
Discharged as a `ZMod 2` `decide` over the eight coordinate parities (kernel `decide`, 256 cases) plus
the `ℤ → 𝔽₂` parity bridge. -/
theorem exists_sqrt2_match {wp wq : ZOmega}
    (hp : ¬ dividesSqrt2 wp) (hq : ¬ dividesSqrt2 wq)
    (hc : (normSq wp).c % 2 = (normSq wq).c % 2) (hd : (normSq wp).d % 2 = (normSq wq).d % 2) :
    ∃ m, dividesSqrt2 (wp - ω ^ m * wq) := by
  have key : ∀ pa pb pc pd qa qb qc qd : ZMod 2,
      ¬(pa = pc ∧ pb = pd) → ¬(qa = qc ∧ qb = qd) →
      (pa*pb - pa*pd + pc*pb + pc*pd = qa*qb - qa*qd + qc*qb + qc*qd) →
      (pa^2 + pb^2 + pc^2 + pd^2 = qa^2 + qb^2 + qc^2 + qd^2) →
      ((pa - qa = pc - qc ∧ pb - qb = pd - qd) ∨
       (pa - qb = pc - qd ∧ pb - qc = pd + qa)) := by decide
  have hbr : ∀ m n : ℤ, m % 2 = n % 2 ↔ (m : ZMod 2) = (n : ZMod 2) := fun m n =>
    (ZMod.intCast_eq_intCast_iff m n 2).symm
  obtain ⟨pa, pb, pc, pd⟩ := wp
  obtain ⟨qa, qb, qc, qd⟩ := wq
  simp only [dividesSqrt2, hbr] at hp hq
  rw [hbr, normSq_coords, normSq_coords] at hc hd
  push_cast at hc hd
  rcases key (pa : ZMod 2) pb pc pd qa qb qc qd hp hq hc hd with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · refine ⟨0, ?_⟩
    simp only [pow_zero, one_mul, dividesSqrt2, hbr, sub_eq_add_neg, add_a, add_b, add_c, add_d,
      neg_a, neg_b, neg_c, neg_d]
    exact ⟨by push_cast; linear_combination h1, by push_cast; linear_combination h2⟩
  · refine ⟨1, ?_⟩
    have homega : ω * (⟨qa, qb, qc, qd⟩ : ZOmega) = ⟨qb, qc, qd, -qa⟩ := by
      ext <;> simp [mul_a, mul_b, mul_c, mul_d]
    simp only [pow_one, homega, dividesSqrt2, hbr, sub_eq_add_neg, add_a, add_b, add_c, add_d,
      neg_a, neg_b, neg_c, neg_d, neg_neg]
    exact ⟨by push_cast; linear_combination h1, by push_cast; linear_combination h2⟩

/-- **Lemma-4 brick (B″): a `1010`-norm pair is mod-2 `ω`-aligned.** Two elements with `1010` residue
norm (`(normSq ·).c` odd — equivalently `(P,Q)≡(0,1)`, so the mod-2 residue lies in the single ω-orbit
`{3,6,9,12}`) satisfy `∃m, 2 ∣ (w_p − ωᵐw_q)` — the exact hypothesis `core_step` consumes. So a matched
`1010` pair is reduced by a SINGLE `H·Tᵐ` (`lemma4_1010`), and after the cross-orbit `0001` step1 lands
its outputs in the `1010` class (brick B′), this finishes the cross-orbit reduction too.

Proof: the four mod-2 `ω`-images `(qa,qb,qc,qd) ↦ (qb,qc,qd,qa) ↦ …` exhaust the orbit; `1010 ⟹ aligned`
is a `ZMod 2` kernel `decide` (`key2`) over the eight coordinate parities, bridged to `ℤ` by the parity
maps. The `decide` is phrased as `¬h₁ ∨ ¬h₂ ∨ concl` (an implication-chain `Decidable`-synthesis quirk
needs the `∨¬` form at this nesting depth). -/
theorem exists_mod2_align_of_normSq_c_odd {wp wq : ZOmega}
    (hp : (normSq wp).c % 2 = 1) (hq : (normSq wq).c % 2 = 1) :
    ∃ m, (2 : ZOmega) ∣ (wp - ω ^ m * wq) := by
  have key2 : ∀ pa pb pc pd qa qb qc qd : ZMod 2,
      ¬(pa*pb - pa*pd + pc*pb + pc*pd = 1) ∨ ¬(qa*qb - qa*qd + qc*qb + qc*qd = 1) ∨
      ((pa = qa ∧ pb = qb ∧ pc = qc ∧ pd = qd) ∨
       (pa = qb ∧ pb = qc ∧ pc = qd ∧ pd = qa) ∨
       (pa = qc ∧ pb = qd ∧ pc = qa ∧ pd = qb) ∨
       (pa = qd ∧ pb = qa ∧ pc = qb ∧ pd = qc)) := by decide
  have hdvd : ∀ z : ZOmega, z.a % 2 = 0 → z.b % 2 = 0 → z.c % 2 = 0 → z.d % 2 = 0 → (2 : ZOmega) ∣ z :=
    fun z ha hb hc hd => ⟨⟨z.a / 2, z.b / 2, z.c / 2, z.d / 2⟩, by
      rw [two_mul]; ext <;> simp only [add_a, add_b, add_c, add_d] <;> omega⟩
  have hQ : ∀ z : ZOmega, (normSq z).c % 2 = 1 →
      ((z.a : ZMod 2) * z.b - z.a * z.d + z.c * z.b + z.c * z.d = 1) := by
    intro z hz
    have h1 : ((normSq z).c : ZMod 2) = 1 := by rw [intCast_zmod2_eq_ite, if_pos hz]
    rw [normSq_coords] at h1; push_cast at h1; linear_combination h1
  have heq : ∀ x y : ℤ, (x : ZMod 2) = (y : ZMod 2) → (x - y) % 2 = 0 := by
    intro x y h; rw [emod_two_eq_zero_iff_zmod]; push_cast; rw [h]; ring
  have hadd : ∀ x y : ℤ, (x : ZMod 2) = (y : ZMod 2) → (x + y) % 2 = 0 := by
    intro x y h; have := heq x y h; omega
  have hw1 : (ω : ZOmega) ^ 1 * wq = ⟨wq.b, wq.c, wq.d, -wq.a⟩ := by
    ext <;> simp [pow_succ, pow_zero, mul_a, mul_b, mul_c, mul_d, ω_a, ω_b, ω_c, ω_d]
  have hw2 : (ω : ZOmega) ^ 2 * wq = ⟨wq.c, wq.d, -wq.a, -wq.b⟩ := by
    ext <;> simp [pow_succ, pow_zero, mul_a, mul_b, mul_c, mul_d, ω_a, ω_b, ω_c, ω_d]
  have hw3 : (ω : ZOmega) ^ 3 * wq = ⟨wq.d, -wq.a, -wq.b, -wq.c⟩ := by
    ext <;> simp [pow_succ, pow_zero, mul_a, mul_b, mul_c, mul_d, ω_a, ω_b, ω_c, ω_d]
  rcases key2 (wp.a : ZMod 2) wp.b wp.c wp.d wq.a wq.b wq.c wq.d with hn | hn | hcc
  · exact absurd (hQ wp hp) hn
  · exact absurd (hQ wq hq) hn
  · rcases hcc with ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩ | ⟨e1, e2, e3, e4⟩
    · refine ⟨0, ?_⟩
      rw [pow_zero, one_mul, show wp - wq = ⟨wp.a - wq.a, wp.b - wq.b, wp.c - wq.c, wp.d - wq.d⟩ from by
        ext <;> simp [sub_eq_add_neg]]
      exact hdvd _ (heq _ _ e1) (heq _ _ e2) (heq _ _ e3) (heq _ _ e4)
    · refine ⟨1, ?_⟩
      rw [hw1, show wp - (⟨wq.b, wq.c, wq.d, -wq.a⟩ : ZOmega)
            = ⟨wp.a - wq.b, wp.b - wq.c, wp.c - wq.d, wp.d + wq.a⟩ from by ext <;> simp [sub_eq_add_neg]]
      exact hdvd _ (heq _ _ e1) (heq _ _ e2) (heq _ _ e3) (hadd _ _ e4)
    · refine ⟨2, ?_⟩
      rw [hw2, show wp - (⟨wq.c, wq.d, -wq.a, -wq.b⟩ : ZOmega)
            = ⟨wp.a - wq.c, wp.b - wq.d, wp.c + wq.a, wp.d + wq.b⟩ from by ext <;> simp [sub_eq_add_neg]]
      exact hdvd _ (heq _ _ e1) (heq _ _ e2) (hadd _ _ e3) (hadd _ _ e4)
    · refine ⟨3, ?_⟩
      rw [hw3, show wp - (⟨wq.d, -wq.a, -wq.b, -wq.c⟩ : ZOmega)
            = ⟨wp.a - wq.d, wp.b + wq.a, wp.c + wq.b, wp.d + wq.c⟩ from by ext <;> simp [sub_eq_add_neg]]
      exact hdvd _ (heq _ _ e1) (hadd _ _ e2) (hadd _ _ e3) (hadd _ _ e4)

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

/-- **Lemma 4, the `1010` case (single `H·Tᵐ`).** A matched-active pair with `1010` residue norm
(`(normSq ·).c` odd) drops BOTH column entries one denominator level: `∃m`, both
`(w_p ± ωᵐw_q)/√2` (entries `mk w_p (t+1)`, `mk w_q (t+1)`) land at `denExp ≤ t`. Assembles brick (B″)
`exists_mod2_align_of_normSq_c_odd` (the alignment `m`) with `core_step` (the drop). This is the whole
`1010` case of the dim-4 column-lemma row operation; the cross-orbit `0001` case reduces to it via the
brick (B′) step1 (which lands its outputs in the `1010` class). -/
theorem lemma4_1010 {wp wq : ZOmega} {t : ℕ}
    (hp : (ZOmega.normSq wp).c % 2 = 1) (hq : (ZOmega.normSq wq).c % 2 = 1) :
    ∃ m, denExp (invSqrt2 * (mk wp (t + 1) + CliffordTGate.ωS ^ m * mk wq (t + 1))) ≤ t ∧
         denExp (invSqrt2 * (mk wp (t + 1) - CliffordTGate.ωS ^ m * mk wq (t + 1))) ≤ t := by
  obtain ⟨m, hm⟩ := ZOmega.exists_mod2_align_of_normSq_c_odd hp hq
  exact ⟨m, core_step hm⟩

end ZOmegaSqrt2

end SKEFTHawking.RossSelinger
