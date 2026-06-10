/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AO Track 3, site 2/4 — the structural `ma_step` existence (Matsumoto–Amano parity)

Replaces the `maStep_exists_core` `native_decide` (a ~809k-tuple sweep over `validCol t`³,
`t ∈ {2,4,8}`) with the Giles–Selinger §6 PARITY ARGUMENT, fully structural: for real
(`⟨p,0,−p,q⟩`-form) Bloch column triples with `selfDot = t` (`2 ∣ t` — ANY even `t`, no bound),
pairwise `dot = 0`, and some odd rational part, some syllable in `{T, HT, SHT}` kills all three.

## The parity argument

Write each entry as `q + p·√2`-data (`q = .d`, `p = .a`; reality pins `.b = 0`, `.c = −.a`).
The hypotheses contribute exactly four mod-2 congruence families:

  * `F1(X)`: `Σᵢ qᵢ² + 2Σᵢ pᵢ² = t ⟹ q₁+q₂+q₃ ≡ 0` — each column has 0 or 2 odd `q`'s;
  * `F2(X)`: the `√2`-part of `selfDot`: `Σᵢ pᵢqᵢ ≡ 0`;
  * `F3(X,Y)`: the rational part of `dot`: `Σᵢ qᵢˣqᵢʸ ≡ 0`;
  * `F4(X,Y)`: the `√2`-part of `dot`: `Σᵢ (pᵢˣqᵢʸ + qᵢˣpᵢʸ) ≡ 0`.

Distinct nonzero even-weight parity vectors in `𝔽₂³` have inner product `1`, so by `F3` all
odd columns share ONE parity vector `w` with `supp w = {i,j}`; the syllable with mixing pair
`{i,j}` (T = `{1,2}`, HT = `{2,3}`, SHT = `{1,3}`) kills every column: the pair-`q` and lone-`q`
conditions follow from `F1 + F3(·,W)`, and the pair-`p` condition from `F4(·,W) + F2(W)`
(for the odd witness column itself, `F3(W,W)`/`F4(W,W)` are derivable from `F1(W)`/triviality —
ONE engine lemma covers both). No enumeration, no coordinate bound: the former `kSO3 ≤ 3`
hypothesis is DROPPED (the step exists for every `kSO3 ≥ 1`).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.
  No `native_decide`. Kernel-pure `{propext, Classical.choice, Quot.sound}`.
-/

import SKEFTHawking.FKLW.RossSelinger.MAStepExists
import SKEFTHawking.FKLW.RossSelinger.BridgeParity

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger
namespace KMM

open CliffordTGate ZOmegaSqrt2

/-! ### Mod-2 product helpers -/

/-- `b` odd ⟹ `(a·b) % 2 = a % 2`. -/
theorem mul_emod_two_right_odd (a : ℤ) {b : ℤ} (hb : b % 2 = 1) : a * b % 2 = a % 2 := by
  rw [Int.mul_emod, hb, mul_one]; omega

/-- `b` even ⟹ `(a·b) % 2 = 0`. -/
theorem mul_emod_two_right_even (a : ℤ) {b : ℤ} (hb : b % 2 = 0) : a * b % 2 = 0 := by
  rw [Int.mul_emod, hb, mul_zero]; omega

/-- `a` odd ⟹ `(a·b) % 2 = b % 2`. -/
theorem mul_emod_two_left_odd (b : ℤ) {a : ℤ} (ha : a % 2 = 1) : a * b % 2 = b % 2 := by
  rw [mul_comm]; exact mul_emod_two_right_odd b ha

/-- `a` even ⟹ `(a·b) % 2 = 0`. -/
theorem mul_emod_two_left_even (b : ℤ) {a : ℤ} (ha : a % 2 = 0) : a * b % 2 = 0 := by
  rw [mul_comm]; exact mul_emod_two_right_even b ha

/-! ### The parity engine -/

/-- **The kill-condition engine** (canonical pattern `(1,1,0)`): from the witness column's
parity pattern, its `F2`, and the target column's `F1`/`F3`/`F4` against the witness, the
target satisfies all three kill conditions of the pair-`{0,1}` syllable. Instantiating
`X := W` (with `F3(W,W)` from `F1(W)` + `t² ≡ t` and `F4(W,W)` trivial) covers the witness
itself — one lemma for both the self and cross cases. -/
theorem killCond_engine {qW0 qW1 qW2 pW0 pW1 pW2 qX0 qX1 qX2 pX0 pX1 pX2 : ℤ}
    (h0 : qW0 % 2 = 1) (h1 : qW1 % 2 = 1) (h2 : qW2 % 2 = 0)
    (hF2W : (pW0 * qW0 + pW1 * qW1 + pW2 * qW2) % 2 = 0)
    (hF1X : (qX0 + qX1 + qX2) % 2 = 0)
    (hF3 : (qX0 * qW0 + qX1 * qW1 + qX2 * qW2) % 2 = 0)
    (hF4 : (pX0 * qW0 + pX1 * qW1 + pX2 * qW2
            + qX0 * pW0 + qX1 * pW1 + qX2 * pW2) % 2 = 0) :
    qX0 % 2 = qX1 % 2 ∧ qX2 % 2 = 0 ∧ pX0 % 2 = pX1 % 2 := by
  have e1 : qX0 * qW0 % 2 = qX0 % 2 := mul_emod_two_right_odd _ h0
  have e2 : qX1 * qW1 % 2 = qX1 % 2 := mul_emod_two_right_odd _ h1
  have e3 : qX2 * qW2 % 2 = 0 := mul_emod_two_right_even _ h2
  have hq01 : qX0 % 2 = qX1 % 2 := by omega
  have hq2 : qX2 % 2 = 0 := by omega
  have e4 : pX0 * qW0 % 2 = pX0 % 2 := mul_emod_two_right_odd _ h0
  have e5 : pX1 * qW1 % 2 = pX1 % 2 := mul_emod_two_right_odd _ h1
  have e6 : pX2 * qW2 % 2 = 0 := mul_emod_two_right_even _ h2
  have f3 : qX2 * pW2 % 2 = 0 := mul_emod_two_left_even _ hq2
  rcases (by omega : qX0 % 2 = 0 ∨ qX0 % 2 = 1) with hε | hε
  · have f1 : qX0 * pW0 % 2 = 0 := mul_emod_two_left_even _ hε
    have f2 : qX1 * pW1 % 2 = 0 := mul_emod_two_left_even _ (by omega)
    exact ⟨hq01, hq2, by omega⟩
  · have f1 : qX0 * pW0 % 2 = pW0 % 2 := mul_emod_two_left_odd _ hε
    have f2 : qX1 * pW1 % 2 = pW1 % 2 := mul_emod_two_left_odd _ (by omega)
    have g1 : pW0 * qW0 % 2 = pW0 % 2 := mul_emod_two_right_odd _ h0
    have g2 : pW1 * qW1 % 2 = pW1 % 2 := mul_emod_two_right_odd _ h1
    have g3 : pW2 * qW2 % 2 = 0 := mul_emod_two_right_even _ h2
    exact ⟨hq01, hq2, by omega⟩

/-! ### Reality and per-syllable kill lemmas -/

/-- Real form for a column: every entry is `⟨p, 0, −p, q⟩` (conjugation-fixed). -/
def ColReal (c : Col) : Prop :=
  c.1.b = 0 ∧ c.1.c = -c.1.a ∧ c.2.1.b = 0 ∧ c.2.1.c = -c.2.1.a
    ∧ c.2.2.b = 0 ∧ c.2.2.c = -c.2.2.a

/-- `T` kills a real column once the pair-`{1,2}` congruences and the lone-`q₃` evenness
hold (`stripRow`s: `c₁+c₂`, `−c₁+c₂`, `√2·c₃`). -/
theorem colKills_T_of {c : Col} (hr : ColReal c)
    (hq : c.1.d % 2 = c.2.1.d % 2) (hl : c.2.2.d % 2 = 0) (hp : c.1.a % 2 = c.2.1.a % 2) :
    colKills .T c = true := by
  obtain ⟨hb1, hc1, hb2, hc2, hb3, hc3⟩ := hr
  have e0 : stripRow .T 0 c = c.1 + c.2.1 := by
    show (1 : ZOmega) * c.1 + 1 * c.2.1 + 0 * c.2.2 = _; ring
  have e1 : stripRow .T 1 c = -c.1 + c.2.1 := by
    show (-1 : ZOmega) * c.1 + 1 * c.2.1 + 0 * c.2.2 = _; ring
  have e2 : stripRow .T 2 c = ZOmega.sqrt2 * c.2.2 := by
    show (0 : ZOmega) * c.1 + 0 * c.2.1 + ZOmega.sqrt2 * c.2.2 = _; ring
  rw [colKills, e0, e1, e2, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;>
    simp only [dvdTwo, ZOmega.add_a, ZOmega.add_b, ZOmega.add_c, ZOmega.add_d, ZOmega.neg_a,
      ZOmega.neg_b, ZOmega.neg_c, ZOmega.neg_d, ZOmega.mul_a, ZOmega.mul_b, ZOmega.mul_c,
      ZOmega.mul_d, ZOmega.sqrt2, hb1, hc1, hb2, hc2, hb3, hc3, Bool.and_eq_true,
      beq_iff_eq] <;>
    omega

/-- `HT` kills a real column once the pair-`{2,3}` congruences and the lone-`q₁` evenness
hold (`stripRow`s: `−c₂+c₃`, `−c₂−c₃`, `√2·c₁`). -/
theorem colKills_HT_of {c : Col} (hr : ColReal c)
    (hq : c.2.1.d % 2 = c.2.2.d % 2) (hl : c.1.d % 2 = 0) (hp : c.2.1.a % 2 = c.2.2.a % 2) :
    colKills .HT c = true := by
  obtain ⟨hb1, hc1, hb2, hc2, hb3, hc3⟩ := hr
  have e0 : stripRow .HT 0 c = -c.2.1 + c.2.2 := by
    show (0 : ZOmega) * c.1 + -1 * c.2.1 + 1 * c.2.2 = _; ring
  have e1 : stripRow .HT 1 c = -c.2.1 + -c.2.2 := by
    show (0 : ZOmega) * c.1 + -1 * c.2.1 + -1 * c.2.2 = _; ring
  have e2 : stripRow .HT 2 c = ZOmega.sqrt2 * c.1 := by
    show ZOmega.sqrt2 * c.1 + 0 * c.2.1 + 0 * c.2.2 = _; ring
  rw [colKills, e0, e1, e2, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;>
    simp only [dvdTwo, ZOmega.add_a, ZOmega.add_b, ZOmega.add_c, ZOmega.add_d, ZOmega.neg_a,
      ZOmega.neg_b, ZOmega.neg_c, ZOmega.neg_d, ZOmega.mul_a, ZOmega.mul_b, ZOmega.mul_c,
      ZOmega.mul_d, ZOmega.sqrt2, hb1, hc1, hb2, hc2, hb3, hc3, Bool.and_eq_true,
      beq_iff_eq] <;>
    omega

/-- `SHT` kills a real column once the pair-`{1,3}` congruences and the lone-`q₂` evenness
hold (`stripRow`s: `c₁+c₃`, `c₁−c₃`, `√2·c₂`). -/
theorem colKills_SHT_of {c : Col} (hr : ColReal c)
    (hq : c.1.d % 2 = c.2.2.d % 2) (hl : c.2.1.d % 2 = 0) (hp : c.1.a % 2 = c.2.2.a % 2) :
    colKills .SHT c = true := by
  obtain ⟨hb1, hc1, hb2, hc2, hb3, hc3⟩ := hr
  have e0 : stripRow .SHT 0 c = c.1 + c.2.2 := by
    show (1 : ZOmega) * c.1 + 0 * c.2.1 + 1 * c.2.2 = _; ring
  have e1 : stripRow .SHT 1 c = c.1 + -c.2.2 := by
    show (1 : ZOmega) * c.1 + 0 * c.2.1 + -1 * c.2.2 = _; ring
  have e2 : stripRow .SHT 2 c = ZOmega.sqrt2 * c.2.1 := by
    show (0 : ZOmega) * c.1 + ZOmega.sqrt2 * c.2.1 + 0 * c.2.2 = _; ring
  rw [colKills, e0, e1, e2, Bool.and_eq_true, Bool.and_eq_true]
  refine ⟨⟨?_, ?_⟩, ?_⟩ <;>
    simp only [dvdTwo, ZOmega.add_a, ZOmega.add_b, ZOmega.add_c, ZOmega.add_d, ZOmega.neg_a,
      ZOmega.neg_b, ZOmega.neg_c, ZOmega.neg_d, ZOmega.mul_a, ZOmega.mul_b, ZOmega.mul_c,
      ZOmega.mul_d, ZOmega.sqrt2, hb1, hc1, hb2, hc2, hb3, hc3, Bool.and_eq_true,
      beq_iff_eq] <;>
    omega

/-! ### Per-pattern assembly -/

section Assembly

variable {A B C W : Col}

/-- Pattern `(1,1,0)` (odd rows `{1,2}`) ⟹ `T` kills all three columns. -/
theorem killsAll_T (hAr : ColReal A) (hBr : ColReal B) (hCr : ColReal C)
    (hw0 : W.1.d % 2 = 1) (hw1 : W.2.1.d % 2 = 1) (hw2 : W.2.2.d % 2 = 0)
    (hF2W : (W.1.a * W.1.d + W.2.1.a * W.2.1.d + W.2.2.a * W.2.2.d) % 2 = 0)
    (hF1A : (A.1.d + A.2.1.d + A.2.2.d) % 2 = 0)
    (hF3A : (A.1.d * W.1.d + A.2.1.d * W.2.1.d + A.2.2.d * W.2.2.d) % 2 = 0)
    (hF4A : (A.1.a * W.1.d + A.2.1.a * W.2.1.d + A.2.2.a * W.2.2.d
             + A.1.d * W.1.a + A.2.1.d * W.2.1.a + A.2.2.d * W.2.2.a) % 2 = 0)
    (hF1B : (B.1.d + B.2.1.d + B.2.2.d) % 2 = 0)
    (hF3B : (B.1.d * W.1.d + B.2.1.d * W.2.1.d + B.2.2.d * W.2.2.d) % 2 = 0)
    (hF4B : (B.1.a * W.1.d + B.2.1.a * W.2.1.d + B.2.2.a * W.2.2.d
             + B.1.d * W.1.a + B.2.1.d * W.2.1.a + B.2.2.d * W.2.2.a) % 2 = 0)
    (hF1C : (C.1.d + C.2.1.d + C.2.2.d) % 2 = 0)
    (hF3C : (C.1.d * W.1.d + C.2.1.d * W.2.1.d + C.2.2.d * W.2.2.d) % 2 = 0)
    (hF4C : (C.1.a * W.1.d + C.2.1.a * W.2.1.d + C.2.2.a * W.2.2.d
             + C.1.d * W.1.a + C.2.1.d * W.2.1.a + C.2.2.d * W.2.2.a) % 2 = 0) :
    someKills A B C = true := by
  obtain ⟨ka1, ka2, ka3⟩ := killCond_engine hw0 hw1 hw2 hF2W hF1A hF3A hF4A
  obtain ⟨kb1, kb2, kb3⟩ := killCond_engine hw0 hw1 hw2 hF2W hF1B hF3B hF4B
  obtain ⟨kc1, kc2, kc3⟩ := killCond_engine hw0 hw1 hw2 hF2W hF1C hF3C hF4C
  rw [someKills, List.any_eq_true]
  refine ⟨.T, by simp, ?_⟩
  rw [Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨colKills_T_of hAr ka1 ka2 ka3, colKills_T_of hBr kb1 kb2 kb3⟩,
    colKills_T_of hCr kc1 kc2 kc3⟩

/-- Pattern `(0,1,1)` (odd rows `{2,3}`) ⟹ `HT` kills all three columns. Hypotheses in the
same canonical order as `killsAll_T`; the engine is applied through the row permutation
`(2,3,1)` (omega re-sorts the sums). -/
theorem killsAll_HT (hAr : ColReal A) (hBr : ColReal B) (hCr : ColReal C)
    (hw0 : W.1.d % 2 = 0) (hw1 : W.2.1.d % 2 = 1) (hw2 : W.2.2.d % 2 = 1)
    (hF2W : (W.1.a * W.1.d + W.2.1.a * W.2.1.d + W.2.2.a * W.2.2.d) % 2 = 0)
    (hF1A : (A.1.d + A.2.1.d + A.2.2.d) % 2 = 0)
    (hF3A : (A.1.d * W.1.d + A.2.1.d * W.2.1.d + A.2.2.d * W.2.2.d) % 2 = 0)
    (hF4A : (A.1.a * W.1.d + A.2.1.a * W.2.1.d + A.2.2.a * W.2.2.d
             + A.1.d * W.1.a + A.2.1.d * W.2.1.a + A.2.2.d * W.2.2.a) % 2 = 0)
    (hF1B : (B.1.d + B.2.1.d + B.2.2.d) % 2 = 0)
    (hF3B : (B.1.d * W.1.d + B.2.1.d * W.2.1.d + B.2.2.d * W.2.2.d) % 2 = 0)
    (hF4B : (B.1.a * W.1.d + B.2.1.a * W.2.1.d + B.2.2.a * W.2.2.d
             + B.1.d * W.1.a + B.2.1.d * W.2.1.a + B.2.2.d * W.2.2.a) % 2 = 0)
    (hF1C : (C.1.d + C.2.1.d + C.2.2.d) % 2 = 0)
    (hF3C : (C.1.d * W.1.d + C.2.1.d * W.2.1.d + C.2.2.d * W.2.2.d) % 2 = 0)
    (hF4C : (C.1.a * W.1.d + C.2.1.a * W.2.1.d + C.2.2.a * W.2.2.d
             + C.1.d * W.1.a + C.2.1.d * W.2.1.a + C.2.2.d * W.2.2.a) % 2 = 0) :
    someKills A B C = true := by
  obtain ⟨ka1, ka2, ka3⟩ := killCond_engine hw1 hw2 hw0 (by omega : (W.2.1.a * W.2.1.d
      + W.2.2.a * W.2.2.d + W.1.a * W.1.d) % 2 = 0) (by omega : (A.2.1.d + A.2.2.d
      + A.1.d) % 2 = 0) (by omega : (A.2.1.d * W.2.1.d + A.2.2.d * W.2.2.d
      + A.1.d * W.1.d) % 2 = 0) (by omega : (A.2.1.a * W.2.1.d + A.2.2.a * W.2.2.d
      + A.1.a * W.1.d + A.2.1.d * W.2.1.a + A.2.2.d * W.2.2.a + A.1.d * W.1.a) % 2 = 0)
  obtain ⟨kb1, kb2, kb3⟩ := killCond_engine hw1 hw2 hw0 (by omega : (W.2.1.a * W.2.1.d
      + W.2.2.a * W.2.2.d + W.1.a * W.1.d) % 2 = 0) (by omega : (B.2.1.d + B.2.2.d
      + B.1.d) % 2 = 0) (by omega : (B.2.1.d * W.2.1.d + B.2.2.d * W.2.2.d
      + B.1.d * W.1.d) % 2 = 0) (by omega : (B.2.1.a * W.2.1.d + B.2.2.a * W.2.2.d
      + B.1.a * W.1.d + B.2.1.d * W.2.1.a + B.2.2.d * W.2.2.a + B.1.d * W.1.a) % 2 = 0)
  obtain ⟨kc1, kc2, kc3⟩ := killCond_engine hw1 hw2 hw0 (by omega : (W.2.1.a * W.2.1.d
      + W.2.2.a * W.2.2.d + W.1.a * W.1.d) % 2 = 0) (by omega : (C.2.1.d + C.2.2.d
      + C.1.d) % 2 = 0) (by omega : (C.2.1.d * W.2.1.d + C.2.2.d * W.2.2.d
      + C.1.d * W.1.d) % 2 = 0) (by omega : (C.2.1.a * W.2.1.d + C.2.2.a * W.2.2.d
      + C.1.a * W.1.d + C.2.1.d * W.2.1.a + C.2.2.d * W.2.2.a + C.1.d * W.1.a) % 2 = 0)
  rw [someKills, List.any_eq_true]
  refine ⟨.HT, by simp, ?_⟩
  rw [Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨colKills_HT_of hAr ka1 ka2 ka3, colKills_HT_of hBr kb1 kb2 kb3⟩,
    colKills_HT_of hCr kc1 kc2 kc3⟩

/-- Pattern `(1,0,1)` (odd rows `{1,3}`) ⟹ `SHT` kills all three columns. Hypotheses in the
same canonical order; engine applied through the row permutation `(1,3,2)`. -/
theorem killsAll_SHT (hAr : ColReal A) (hBr : ColReal B) (hCr : ColReal C)
    (hw0 : W.1.d % 2 = 1) (hw1 : W.2.1.d % 2 = 0) (hw2 : W.2.2.d % 2 = 1)
    (hF2W : (W.1.a * W.1.d + W.2.1.a * W.2.1.d + W.2.2.a * W.2.2.d) % 2 = 0)
    (hF1A : (A.1.d + A.2.1.d + A.2.2.d) % 2 = 0)
    (hF3A : (A.1.d * W.1.d + A.2.1.d * W.2.1.d + A.2.2.d * W.2.2.d) % 2 = 0)
    (hF4A : (A.1.a * W.1.d + A.2.1.a * W.2.1.d + A.2.2.a * W.2.2.d
             + A.1.d * W.1.a + A.2.1.d * W.2.1.a + A.2.2.d * W.2.2.a) % 2 = 0)
    (hF1B : (B.1.d + B.2.1.d + B.2.2.d) % 2 = 0)
    (hF3B : (B.1.d * W.1.d + B.2.1.d * W.2.1.d + B.2.2.d * W.2.2.d) % 2 = 0)
    (hF4B : (B.1.a * W.1.d + B.2.1.a * W.2.1.d + B.2.2.a * W.2.2.d
             + B.1.d * W.1.a + B.2.1.d * W.2.1.a + B.2.2.d * W.2.2.a) % 2 = 0)
    (hF1C : (C.1.d + C.2.1.d + C.2.2.d) % 2 = 0)
    (hF3C : (C.1.d * W.1.d + C.2.1.d * W.2.1.d + C.2.2.d * W.2.2.d) % 2 = 0)
    (hF4C : (C.1.a * W.1.d + C.2.1.a * W.2.1.d + C.2.2.a * W.2.2.d
             + C.1.d * W.1.a + C.2.1.d * W.2.1.a + C.2.2.d * W.2.2.a) % 2 = 0) :
    someKills A B C = true := by
  obtain ⟨ka1, ka2, ka3⟩ := killCond_engine hw0 hw2 hw1 (by omega : (W.1.a * W.1.d
      + W.2.2.a * W.2.2.d + W.2.1.a * W.2.1.d) % 2 = 0) (by omega : (A.1.d + A.2.2.d
      + A.2.1.d) % 2 = 0) (by omega : (A.1.d * W.1.d + A.2.2.d * W.2.2.d
      + A.2.1.d * W.2.1.d) % 2 = 0) (by omega : (A.1.a * W.1.d + A.2.2.a * W.2.2.d
      + A.2.1.a * W.2.1.d + A.1.d * W.1.a + A.2.2.d * W.2.2.a + A.2.1.d * W.2.1.a) % 2 = 0)
  obtain ⟨kb1, kb2, kb3⟩ := killCond_engine hw0 hw2 hw1 (by omega : (W.1.a * W.1.d
      + W.2.2.a * W.2.2.d + W.2.1.a * W.2.1.d) % 2 = 0) (by omega : (B.1.d + B.2.2.d
      + B.2.1.d) % 2 = 0) (by omega : (B.1.d * W.1.d + B.2.2.d * W.2.2.d
      + B.2.1.d * W.2.1.d) % 2 = 0) (by omega : (B.1.a * W.1.d + B.2.2.a * W.2.2.d
      + B.2.1.a * W.2.1.d + B.1.d * W.1.a + B.2.2.d * W.2.2.a + B.2.1.d * W.2.1.a) % 2 = 0)
  obtain ⟨kc1, kc2, kc3⟩ := killCond_engine hw0 hw2 hw1 (by omega : (W.1.a * W.1.d
      + W.2.2.a * W.2.2.d + W.2.1.a * W.2.1.d) % 2 = 0) (by omega : (C.1.d + C.2.2.d
      + C.2.1.d) % 2 = 0) (by omega : (C.1.d * W.1.d + C.2.2.d * W.2.2.d
      + C.2.1.d * W.2.1.d) % 2 = 0) (by omega : (C.1.a * W.1.d + C.2.2.a * W.2.2.d
      + C.2.1.a * W.2.1.d + C.1.d * W.1.a + C.2.2.d * W.2.2.a + C.2.1.d * W.2.1.a) % 2 = 0)
  rw [someKills, List.any_eq_true]
  refine ⟨.SHT, by simp, ?_⟩
  rw [Bool.and_eq_true, Bool.and_eq_true]
  exact ⟨⟨colKills_SHT_of hAr ka1 ka2 ka3, colKills_SHT_of hBr kb1 kb2 kb3⟩,
    colKills_SHT_of hCr kc1 kc2 kc3⟩

end Assembly

/-! ### The structural `someKills` theorem -/

set_option maxRecDepth 4000 in
/-- **The structural MA-step kill theorem** (replaces the `maStep_exists_core`
`native_decide`): real column triples with even `selfDot` (ANY even `t` — no `t ≤ 8` bound),
pairwise orthogonality, and some odd rational part admit a syllable killing all three.
Giles–Selinger §6 parity argument; no enumeration. -/
theorem someKills_of_orthogonal {t : ℤ} (ht : t % 2 = 0) {A B C : Col}
    (hAr : ColReal A) (hBr : ColReal B) (hCr : ColReal C)
    (hA : Col.selfDot A = (⟨0, 0, 0, t⟩ : ZOmega))
    (hB : Col.selfDot B = (⟨0, 0, 0, t⟩ : ZOmega))
    (hC : Col.selfDot C = (⟨0, 0, 0, t⟩ : ZOmega))
    (hAB : Col.dot A B = 0) (hAC : Col.dot A C = 0) (hBC : Col.dot B C = 0)
    (hodd : notSqrt2Div A B C = true) :
    someKills A B C = true := by
  obtain ⟨ab1, ac1, ab2, ac2, ab3, ac3⟩ := hAr
  obtain ⟨bb1, bc1, bb2, bc2, bb3, bc3⟩ := hBr
  obtain ⟨cb1, cc1, cb2, cc2, cb3, cc3⟩ := hCr
  -- coordinate extractions: selfDot (.a and .d) per column
  have sdA := congrArg ZOmega.d hA
  have saA := congrArg ZOmega.a hA
  have sdB := congrArg ZOmega.d hB
  have saB := congrArg ZOmega.a hB
  have sdC := congrArg ZOmega.d hC
  have saC := congrArg ZOmega.a hC
  -- coordinate extractions: dot (.a and .d) per pair
  have ddAB := congrArg ZOmega.d hAB
  have daAB := congrArg ZOmega.a hAB
  have ddAC := congrArg ZOmega.d hAC
  have daAC := congrArg ZOmega.a hAC
  have ddBC := congrArg ZOmega.d hBC
  have daBC := congrArg ZOmega.a hBC
  simp only [Col.selfDot, Col.dot, ZOmega.add_a, ZOmega.add_d, ZOmega.mul_a, ZOmega.mul_d,
    ZOmega.zero_a, ZOmega.zero_d, ab1, ac1, ab2, ac2, ab3, ac3, bb1, bc1, bb2, bc2, bb3, bc3,
    cb1, cc1, cb2, cc2, cb3, cc3, mul_neg, neg_mul, neg_neg, mul_zero, zero_mul, add_zero,
    neg_zero] at sdA saA sdB saB sdC saC ddAB daAB ddAC daAC ddBC daBC
  -- F1: column q-sums even (squares ≡ bases mod 2)
  have F1A : (A.1.d + A.2.1.d + A.2.2.d) % 2 = 0 := by
    have s1 := ZOmega.sq_emod_two A.1.d; have s2 := ZOmega.sq_emod_two A.2.1.d
    have s3 := ZOmega.sq_emod_two A.2.2.d; omega
  have F1B : (B.1.d + B.2.1.d + B.2.2.d) % 2 = 0 := by
    have s1 := ZOmega.sq_emod_two B.1.d; have s2 := ZOmega.sq_emod_two B.2.1.d
    have s3 := ZOmega.sq_emod_two B.2.2.d; omega
  have F1C : (C.1.d + C.2.1.d + C.2.2.d) % 2 = 0 := by
    have s1 := ZOmega.sq_emod_two C.1.d; have s2 := ZOmega.sq_emod_two C.2.1.d
    have s3 := ZOmega.sq_emod_two C.2.2.d; omega
  -- F2: column √2-parts even (the .a-extraction carries both product orientations)
  have F2A : (A.1.a * A.1.d + A.2.1.a * A.2.1.d + A.2.2.a * A.2.2.d) % 2 = 0 := by
    have e1 := mul_comm A.1.d A.1.a; have e2 := mul_comm A.2.1.d A.2.1.a
    have e3 := mul_comm A.2.2.d A.2.2.a; omega
  have F2B : (B.1.a * B.1.d + B.2.1.a * B.2.1.d + B.2.2.a * B.2.2.d) % 2 = 0 := by
    have e1 := mul_comm B.1.d B.1.a; have e2 := mul_comm B.2.1.d B.2.1.a
    have e3 := mul_comm B.2.2.d B.2.2.a; omega
  have F2C : (C.1.a * C.1.d + C.2.1.a * C.2.1.d + C.2.2.a * C.2.2.d) % 2 = 0 := by
    have e1 := mul_comm C.1.d C.1.a; have e2 := mul_comm C.2.1.d C.2.1.a
    have e3 := mul_comm C.2.2.d C.2.2.a; omega
  -- F3/F4 for all ordered pairs (swapped orientations via linear_combination)
  have ddBA : 2 * (B.1.a * A.1.a) + B.1.d * A.1.d + (2 * (B.2.1.a * A.2.1.a)
      + B.2.1.d * A.2.1.d) + (2 * (B.2.2.a * A.2.2.a) + B.2.2.d * A.2.2.d) = 0 := by
    linear_combination ddAB
  have daBA : B.1.a * A.1.d + B.1.d * A.1.a + (B.2.1.a * A.2.1.d + B.2.1.d * A.2.1.a)
      + (B.2.2.a * A.2.2.d + B.2.2.d * A.2.2.a) = 0 := by linear_combination daAB
  have ddCA : 2 * (C.1.a * A.1.a) + C.1.d * A.1.d + (2 * (C.2.1.a * A.2.1.a)
      + C.2.1.d * A.2.1.d) + (2 * (C.2.2.a * A.2.2.a) + C.2.2.d * A.2.2.d) = 0 := by
    linear_combination ddAC
  have daCA : C.1.a * A.1.d + C.1.d * A.1.a + (C.2.1.a * A.2.1.d + C.2.1.d * A.2.1.a)
      + (C.2.2.a * A.2.2.d + C.2.2.d * A.2.2.a) = 0 := by linear_combination daAC
  have ddCB : 2 * (C.1.a * B.1.a) + C.1.d * B.1.d + (2 * (C.2.1.a * B.2.1.a)
      + C.2.1.d * B.2.1.d) + (2 * (C.2.2.a * B.2.2.a) + C.2.2.d * B.2.2.d) = 0 := by
    linear_combination ddBC
  have daCB : C.1.a * B.1.d + C.1.d * B.1.a + (C.2.1.a * B.2.1.d + C.2.1.d * B.2.1.a)
      + (C.2.2.a * B.2.2.d + C.2.2.d * B.2.2.a) = 0 := by linear_combination daBC
  -- self F3 (from F1 + t² ≡ t) and self F4 (commutator-doubled F2)
  have F3AA : (A.1.d * A.1.d + A.2.1.d * A.2.1.d + A.2.2.d * A.2.2.d) % 2 = 0 := by
    have s1 := ZOmega.sq_emod_two A.1.d; have s2 := ZOmega.sq_emod_two A.2.1.d
    have s3 := ZOmega.sq_emod_two A.2.2.d; omega
  have F3BB : (B.1.d * B.1.d + B.2.1.d * B.2.1.d + B.2.2.d * B.2.2.d) % 2 = 0 := by
    have s1 := ZOmega.sq_emod_two B.1.d; have s2 := ZOmega.sq_emod_two B.2.1.d
    have s3 := ZOmega.sq_emod_two B.2.2.d; omega
  have F3CC : (C.1.d * C.1.d + C.2.1.d * C.2.1.d + C.2.2.d * C.2.2.d) % 2 = 0 := by
    have s1 := ZOmega.sq_emod_two C.1.d; have s2 := ZOmega.sq_emod_two C.2.1.d
    have s3 := ZOmega.sq_emod_two C.2.2.d; omega
  have F4AA : (A.1.a * A.1.d + A.2.1.a * A.2.1.d + A.2.2.a * A.2.2.d
      + A.1.d * A.1.a + A.2.1.d * A.2.1.a + A.2.2.d * A.2.2.a) % 2 = 0 := by
    have e1 := mul_comm A.1.d A.1.a; have e2 := mul_comm A.2.1.d A.2.1.a
    have e3 := mul_comm A.2.2.d A.2.2.a; omega
  have F4BB : (B.1.a * B.1.d + B.2.1.a * B.2.1.d + B.2.2.a * B.2.2.d
      + B.1.d * B.1.a + B.2.1.d * B.2.1.a + B.2.2.d * B.2.2.a) % 2 = 0 := by
    have e1 := mul_comm B.1.d B.1.a; have e2 := mul_comm B.2.1.d B.2.1.a
    have e3 := mul_comm B.2.2.d B.2.2.a; omega
  have F4CC : (C.1.a * C.1.d + C.2.1.a * C.2.1.d + C.2.2.a * C.2.2.d
      + C.1.d * C.1.a + C.2.1.d * C.2.1.a + C.2.2.d * C.2.2.a) % 2 = 0 := by
    have e1 := mul_comm C.1.d C.1.a; have e2 := mul_comm C.2.1.d C.2.1.a
    have e3 := mul_comm C.2.2.d C.2.2.a; omega
  -- cross F3/F4 in (X, W)-orientation for all 6 ordered pairs
  have F3AB : (A.1.d * B.1.d + A.2.1.d * B.2.1.d + A.2.2.d * B.2.2.d) % 2 = 0 := by omega
  have F4AB : (A.1.a * B.1.d + A.2.1.a * B.2.1.d + A.2.2.a * B.2.2.d
      + A.1.d * B.1.a + A.2.1.d * B.2.1.a + A.2.2.d * B.2.2.a) % 2 = 0 := by omega
  have F3BA : (B.1.d * A.1.d + B.2.1.d * A.2.1.d + B.2.2.d * A.2.2.d) % 2 = 0 := by omega
  have F4BA : (B.1.a * A.1.d + B.2.1.a * A.2.1.d + B.2.2.a * A.2.2.d
      + B.1.d * A.1.a + B.2.1.d * A.2.1.a + B.2.2.d * A.2.2.a) % 2 = 0 := by omega
  have F3AC : (A.1.d * C.1.d + A.2.1.d * C.2.1.d + A.2.2.d * C.2.2.d) % 2 = 0 := by omega
  have F4AC : (A.1.a * C.1.d + A.2.1.a * C.2.1.d + A.2.2.a * C.2.2.d
      + A.1.d * C.1.a + A.2.1.d * C.2.1.a + A.2.2.d * C.2.2.a) % 2 = 0 := by omega
  have F3CA : (C.1.d * A.1.d + C.2.1.d * A.2.1.d + C.2.2.d * A.2.2.d) % 2 = 0 := by omega
  have F4CA : (C.1.a * A.1.d + C.2.1.a * A.2.1.d + C.2.2.a * A.2.2.d
      + C.1.d * A.1.a + C.2.1.d * A.2.1.a + C.2.2.d * A.2.2.a) % 2 = 0 := by omega
  have F3BC : (B.1.d * C.1.d + B.2.1.d * C.2.1.d + B.2.2.d * C.2.2.d) % 2 = 0 := by omega
  have F4BC : (B.1.a * C.1.d + B.2.1.a * C.2.1.d + B.2.2.a * C.2.2.d
      + B.1.d * C.1.a + B.2.1.d * C.2.1.a + B.2.2.d * C.2.2.a) % 2 = 0 := by omega
  have F3CB : (C.1.d * B.1.d + C.2.1.d * B.2.1.d + C.2.2.d * B.2.2.d) % 2 = 0 := by omega
  have F4CB : (C.1.a * B.1.d + C.2.1.a * B.2.1.d + C.2.2.a * B.2.2.d
      + C.1.d * B.1.a + C.2.1.d * B.2.1.a + C.2.2.d * B.2.2.a) % 2 = 0 := by omega
  -- locate the odd entry and case on its column + the witness pattern
  rw [notSqrt2Div, List.any_eq_true] at hodd
  obtain ⟨x, hmem, hx⟩ := hodd
  rw [beq_iff_eq] at hx
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  have hArc : ColReal A := ⟨ab1, ac1, ab2, ac2, ab3, ac3⟩
  have hBrc : ColReal B := ⟨bb1, bc1, bb2, bc2, bb3, bc3⟩
  have hCrc : ColReal C := ⟨cb1, cc1, cb2, cc2, cb3, cc3⟩
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  -- W = A, odd entry q₁
  · rcases (by omega : A.2.1.d % 2 = 0 ∨ A.2.1.d % 2 = 1) with h2 | h2
    · rcases (by omega : A.2.2.d % 2 = 0 ∨ A.2.2.d % 2 = 1) with h3 | h3
      · omega
      · exact killsAll_SHT hArc hBrc hCrc hx h2 h3 F2A F1A F3AA F4AA F1B F3BA F4BA F1C F3CA F4CA
    · rcases (by omega : A.2.2.d % 2 = 0 ∨ A.2.2.d % 2 = 1) with h3 | h3
      · exact killsAll_T hArc hBrc hCrc hx h2 h3 F2A F1A F3AA F4AA F1B F3BA F4BA F1C F3CA F4CA
      · omega
  -- W = A, odd entry q₂
  · rcases (by omega : A.1.d % 2 = 0 ∨ A.1.d % 2 = 1) with h1 | h1
    · rcases (by omega : A.2.2.d % 2 = 0 ∨ A.2.2.d % 2 = 1) with h3 | h3
      · omega
      · exact killsAll_HT hArc hBrc hCrc h1 hx h3 F2A F1A F3AA F4AA F1B F3BA F4BA F1C F3CA F4CA
    · rcases (by omega : A.2.2.d % 2 = 0 ∨ A.2.2.d % 2 = 1) with h3 | h3
      · exact killsAll_T hArc hBrc hCrc h1 hx h3 F2A F1A F3AA F4AA F1B F3BA F4BA F1C F3CA F4CA
      · omega
  -- W = A, odd entry q₃
  · rcases (by omega : A.1.d % 2 = 0 ∨ A.1.d % 2 = 1) with h1 | h1
    · rcases (by omega : A.2.1.d % 2 = 0 ∨ A.2.1.d % 2 = 1) with h2 | h2
      · omega
      · exact killsAll_HT hArc hBrc hCrc h1 h2 hx F2A F1A F3AA F4AA F1B F3BA F4BA F1C F3CA F4CA
    · rcases (by omega : A.2.1.d % 2 = 0 ∨ A.2.1.d % 2 = 1) with h2 | h2
      · exact killsAll_SHT hArc hBrc hCrc h1 h2 hx F2A F1A F3AA F4AA F1B F3BA F4BA F1C F3CA F4CA
      · omega
  -- W = B, odd entry q₁
  · rcases (by omega : B.2.1.d % 2 = 0 ∨ B.2.1.d % 2 = 1) with h2 | h2
    · rcases (by omega : B.2.2.d % 2 = 0 ∨ B.2.2.d % 2 = 1) with h3 | h3
      · omega
      · exact killsAll_SHT hArc hBrc hCrc hx h2 h3 F2B F1A F3AB F4AB F1B F3BB F4BB F1C F3CB F4CB
    · rcases (by omega : B.2.2.d % 2 = 0 ∨ B.2.2.d % 2 = 1) with h3 | h3
      · exact killsAll_T hArc hBrc hCrc hx h2 h3 F2B F1A F3AB F4AB F1B F3BB F4BB F1C F3CB F4CB
      · omega
  -- W = B, odd entry q₂
  · rcases (by omega : B.1.d % 2 = 0 ∨ B.1.d % 2 = 1) with h1 | h1
    · rcases (by omega : B.2.2.d % 2 = 0 ∨ B.2.2.d % 2 = 1) with h3 | h3
      · omega
      · exact killsAll_HT hArc hBrc hCrc h1 hx h3 F2B F1A F3AB F4AB F1B F3BB F4BB F1C F3CB F4CB
    · rcases (by omega : B.2.2.d % 2 = 0 ∨ B.2.2.d % 2 = 1) with h3 | h3
      · exact killsAll_T hArc hBrc hCrc h1 hx h3 F2B F1A F3AB F4AB F1B F3BB F4BB F1C F3CB F4CB
      · omega
  -- W = B, odd entry q₃
  · rcases (by omega : B.1.d % 2 = 0 ∨ B.1.d % 2 = 1) with h1 | h1
    · rcases (by omega : B.2.1.d % 2 = 0 ∨ B.2.1.d % 2 = 1) with h2 | h2
      · omega
      · exact killsAll_HT hArc hBrc hCrc h1 h2 hx F2B F1A F3AB F4AB F1B F3BB F4BB F1C F3CB F4CB
    · rcases (by omega : B.2.1.d % 2 = 0 ∨ B.2.1.d % 2 = 1) with h2 | h2
      · exact killsAll_SHT hArc hBrc hCrc h1 h2 hx F2B F1A F3AB F4AB F1B F3BB F4BB F1C F3CB F4CB
      · omega
  -- W = C, odd entry q₁
  · rcases (by omega : C.2.1.d % 2 = 0 ∨ C.2.1.d % 2 = 1) with h2 | h2
    · rcases (by omega : C.2.2.d % 2 = 0 ∨ C.2.2.d % 2 = 1) with h3 | h3
      · omega
      · exact killsAll_SHT hArc hBrc hCrc hx h2 h3 F2C F1A F3AC F4AC F1B F3BC F4BC F1C F3CC F4CC
    · rcases (by omega : C.2.2.d % 2 = 0 ∨ C.2.2.d % 2 = 1) with h3 | h3
      · exact killsAll_T hArc hBrc hCrc hx h2 h3 F2C F1A F3AC F4AC F1B F3BC F4BC F1C F3CC F4CC
      · omega
  -- W = C, odd entry q₂
  · rcases (by omega : C.1.d % 2 = 0 ∨ C.1.d % 2 = 1) with h1 | h1
    · rcases (by omega : C.2.2.d % 2 = 0 ∨ C.2.2.d % 2 = 1) with h3 | h3
      · omega
      · exact killsAll_HT hArc hBrc hCrc h1 hx h3 F2C F1A F3AC F4AC F1B F3BC F4BC F1C F3CC F4CC
    · rcases (by omega : C.2.2.d % 2 = 0 ∨ C.2.2.d % 2 = 1) with h3 | h3
      · exact killsAll_T hArc hBrc hCrc h1 hx h3 F2C F1A F3AC F4AC F1B F3BC F4BC F1C F3CC F4CC
      · omega
  -- W = C, odd entry q₃
  · rcases (by omega : C.1.d % 2 = 0 ∨ C.1.d % 2 = 1) with h1 | h1
    · rcases (by omega : C.2.1.d % 2 = 0 ∨ C.2.1.d % 2 = 1) with h2 | h2
      · omega
      · exact killsAll_HT hArc hBrc hCrc h1 h2 hx F2C F1A F3AC F4AC F1B F3BC F4BC F1C F3CC F4CC
    · rcases (by omega : C.2.1.d % 2 = 0 ∨ C.2.1.d % 2 = 1) with h2 | h2
      · exact killsAll_SHT hArc hBrc hCrc h1 h2 hx F2C F1A F3AC F4AC F1B F3BC F4BC F1C F3CC F4CC
      · omega

/-! ### The Bloch-column instantiation and the moved `ma_step` existence -/

/-- The `j`-th cleared Bloch column's self dot-product is `⟨0,0,0,2^kSO3⟩` (the `j = l`
case of `blochNum_orthogonal` in literal form). -/
theorem col_selfDot {M : Mat2} (hu : IsUnitaryT M) (j : Fin 3) :
    Col.selfDot (blochNum M 0 j, blochNum M 1 j, blochNum M 2 j)
      = (⟨0, 0, 0, 2 ^ kSO3 M⟩ : ZOmega) := by
  have hortho := blochNum_orthogonal hu j j
  rw [if_pos rfl, Fin.sum_univ_three] at hortho
  show blochNum M 0 j * blochNum M 0 j + blochNum M 1 j * blochNum M 1 j
      + blochNum M 2 j * blochNum M 2 j = _
  rw [hortho, two_pow_eq]

/-- **`ma_step` existence** (the MA recursion's reducing step), now STRUCTURAL and with the
former `kSO3 M ≤ 3` hypothesis DROPPED: a realizable `M` with `kSO3 M ≥ 1` admits a syllable
strip lowering `kSO3` by ≥ 1. Assembles reality (`blochNum_b_zero`/`c_eq`), the cleared-
column self/cross dot-products, `kSO3`-exactness (`col_notSqrt2Div`), and the parity
theorem `someKills_of_orthogonal`, then feeds the mod-2 condition to `kSO3_stripMat_lt`. -/
theorem ma_step_exists {M : Mat2} (h : IsCliffordTRealizable M) (hk1 : 1 ≤ kSO3 M) :
    ∃ s : Syllable, kSO3 (stripMat s M) < kSO3 M := by
  have hu := isUnitaryT_of_isCliffordTRealizable h
  have hreal : ∀ j : Fin 3,
      ColReal (blochNum M 0 j, blochNum M 1 j, blochNum M 2 j) := fun j =>
    ⟨blochNum_b_zero h 0 j, blochNum_c_eq h 0 j, blochNum_b_zero h 1 j,
      blochNum_c_eq h 1 j, blochNum_b_zero h 2 j, blochNum_c_eq h 2 j⟩
  have ht : (2 : ℤ) ^ kSO3 M % 2 = 0 := by
    have : (2 : ℤ) ^ kSO3 M = 2 * 2 ^ (kSO3 M - 1) := by
      rw [← pow_succ', show kSO3 M - 1 + 1 = kSO3 M from by omega]
    omega
  have hkills := someKills_of_orthogonal ht (hreal 0) (hreal 1) (hreal 2)
    (col_selfDot hu 0) (col_selfDot hu 1) (col_selfDot hu 2)
    (col_dot_eq_zero hu (by decide)) (col_dot_eq_zero hu (by decide))
    (col_dot_eq_zero hu (by decide)) (col_notSqrt2Div h hk1)
  rw [someKills, List.any_eq_true] at hkills
  obtain ⟨s, -, hs⟩ := hkills
  rw [Bool.and_eq_true, Bool.and_eq_true] at hs
  obtain ⟨⟨hk0, hk1c⟩, hk2c⟩ := hs
  refine ⟨s, kSO3_stripMat_lt hu s hk1 (fun i j => ?_)⟩
  fin_cases j
  · exact colKills_blochStripNum_dvd s M 0 hk0 i
  · exact colKills_blochStripNum_dvd s M 1 hk1c i
  · exact colKills_blochStripNum_dvd s M 2 hk2c i

end KMM
end SKEFTHawking.RossSelinger
