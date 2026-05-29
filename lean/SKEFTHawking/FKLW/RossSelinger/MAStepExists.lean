/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F — the `ma_step` EXISTENCE proof (reducing syllable exists)

`MAStepDecrease.lean` shipped the GIVEN-condition⟹decrease direction
(`kSO3_stripMat_lt`): if the mod-2 condition `∀ i,j: 2 ∣ blochStripNum s M i j`
holds, then `kSO3 (stripMat s M) < kSO3 M`. This file supplies the missing
EXISTENCE: for a realizable `M` with `kSO3 M ≥ 1`, SOME syllable `s ∈ {T,HT,SHT}`
satisfies the mod-2 condition, hence lowers `kSO3` by ≥ 1.

## The clean superset characterization (validated, then formalized)

The reducing syllable is governed by the cleared Bloch numerators
`B := blochNum M` (the `ℤ[ω]` matrix with `of (B i j) = √2^kSO3 · R(M) i j`). The
key constraints, both available from shipped substrate, are EXACT (not mod-2):

  * **Orthogonality** `∑ᵢ Bᵢⱼ · Bᵢₗ = 2^kSO3 · δⱼₗ` (cleared `blochMat_transpose_mul`).
  * **Reality** `conj (B i j) = B i j` (`R(M) ∈ SO(3)` is real; multiplicative
    via `bloch_hom` + per-gate `decide`).

Reality forces each `B i j` into the real subring `⟨a,0,-a,d⟩`, and the
conjugated column-sum `∑ᵢ normSq (B i j) = 2^kSO3` then bounds every coordinate
(`normSq.d = a²+b²+c²+d² ≥ 0`, summing to `2^kSO3 ≤ 8`). Over this finite,
column-decomposed domain, a `native_decide` establishes that a reducing syllable
always exists (validated in `scripts/kmm_ma_step_residue.py` /
`/tmp/btb_columns.py`: 0 failures over k = 1,2,3).

## This increment

`blochEntry_interp_real` / `blochEntry_realizable_real` — **reality** of the Bloch
image of any realizable matrix, the linchpin that bounds the `native_decide`
domain. Proof: `conj` is a ring hom and `bloch_hom` makes reality multiplicative,
so it reduces to the per-gate base case (`decide`).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected (`maxRecDepth` only, finite `decide`).
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.MAStepDecrease
import SKEFTHawking.FKLW.RossSelinger.BlochOrthogonal
import SKEFTHawking.FKLW.RossSelinger.UnitaryClosure
import SKEFTHawking.FKLW.RossSelinger.KMMLemma3Bridge

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace KMM

open CliffordTGate ZOmegaSqrt2

/-! ## Reality of the Bloch image -/

set_option maxRecDepth 4000 in
/-- **Per-gate reality**: each Clifford+T gate's Bloch image is conjugation-fixed
(`R(g) ∈ SO(3)` is real). Kernel-checked (`decide`) over the 8 gates × 9 entries. -/
theorem blochEntry_gate_real (g : CliffordTGate) (i j : Fin 3) :
    ZOmegaSqrt2.conj (blochEntry (gateMatrix g) i j) = blochEntry (gateMatrix g) i j := by
  cases g <;> revert i j <;> decide

set_option maxRecDepth 4000 in
/-- **Reality of the identity's Bloch image.** -/
theorem blochEntry_one_real (i j : Fin 3) :
    ZOmegaSqrt2.conj (blochEntry (1 : Mat2) i j) = blochEntry (1 : Mat2) i j := by
  revert i j; decide

/-- **Reality of any realizable matrix's Bloch image** — the linchpin bounding the
`native_decide` domain. `conj` is a ring hom and `bloch_hom` makes reality
multiplicative, so it reduces (by induction on the gate word) to the per-gate
base case `blochEntry_gate_real`. -/
theorem blochEntry_interp_real (gs : List CliffordTGate) (i j : Fin 3) :
    ZOmegaSqrt2.conj (blochEntry (interp gs) i j) = blochEntry (interp gs) i j := by
  induction gs generalizing i j with
  | nil => rw [interp_nil]; exact blochEntry_one_real i j
  | cons g gs ih =>
      rw [interp_cons, bloch_hom (interp_isUnitaryT gs) i j, Fin.sum_univ_three,
          ZOmegaSqrt2.conj_add, ZOmegaSqrt2.conj_add, ZOmegaSqrt2.conj_mul,
          ZOmegaSqrt2.conj_mul, ZOmegaSqrt2.conj_mul, blochEntry_gate_real g i 0,
          blochEntry_gate_real g i 1, blochEntry_gate_real g i 2, ih 0 j, ih 1 j, ih 2 j,
          ← Fin.sum_univ_three (fun k => blochEntry (gateMatrix g) i k * blochEntry (interp gs) k j),
          ← bloch_hom (interp_isUnitaryT gs) i j]

/-- **Reality for the realizability predicate.** -/
theorem blochEntry_realizable_real {M : Mat2} (h : IsCliffordTRealizable M) (i j : Fin 3) :
    ZOmegaSqrt2.conj (blochEntry M i j) = blochEntry M i j := by
  obtain ⟨gs, rfl⟩ := h
  exact blochEntry_interp_real gs i j

/-! ## Orthogonality of the cleared Bloch numerators -/

/-- **`of` is injective** (`ZOmega ↪ ZOmegaSqrt2`). -/
theorem of_injective : Function.Injective (ZOmegaSqrt2.of) := by
  intro z w h
  have := ZOmegaSqrt2.mk_eq_mk_iff.mp h
  simpa using this

/-- **Orthogonality of the cleared Bloch numerators**: `∑ᵢ Bᵢⱼ · Bᵢₗ = 2^kSO3 · δⱼₗ`
in `ZOmega` (the non-conjugated `RᵀR = I` of `blochMat_transpose_mul`, cleared by
`√2^(2·kSO3)` via `blochNum_spec`). Gives the per-column norm (`j = l`) and the
pairwise orthogonality (`j ≠ l`) the `ma_step` `native_decide` consumes. -/
theorem blochNum_orthogonal {M : Mat2} (hu : ZOmegaSqrt2.IsUnitaryT M) (j l : Fin 3) :
    ∑ i, blochNum M i j * blochNum M i l
      = if j = l then ((2 : ZOmega) ^ kSO3 M) else 0 := by
  apply of_injective
  have hδ : ∑ i, blochEntry M i j * blochEntry M i l = if j = l then (1 : ZOmegaSqrt2) else 0 := by
    have h := blochMat_transpose_mul hu
    have := congrFun (congrFun h j) l
    simpa [blochMat, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply,
      Matrix.one_apply] using this
  have hsq : (sqrt2 : ZOmegaSqrt2) ^ kSO3 M * sqrt2 ^ kSO3 M = ZOmegaSqrt2.of ((2 : ZOmega) ^ kSO3 M) := by
    rw [← pow_add, ← two_mul, pow_mul,
      show (sqrt2 : ZOmegaSqrt2) ^ 2 = ZOmegaSqrt2.of (2 : ZOmega) from by decide,
      ← ZOmegaSqrt2.ofRingHom_apply, ← map_pow]; rfl
  conv_lhs => rw [← ZOmegaSqrt2.ofRingHom_apply, map_sum]
  simp only [ZOmegaSqrt2.ofRingHom_apply, ZOmegaSqrt2.of_mul, ← blochNum_spec]
  rw [show (∑ i, sqrt2 ^ kSO3 M * blochEntry M i j * (sqrt2 ^ kSO3 M * blochEntry M i l))
      = sqrt2 ^ kSO3 M * sqrt2 ^ kSO3 M * ∑ i, blochEntry M i j * blochEntry M i l from by
        rw [Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring,
    hδ, hsq]
  by_cases hjl : j = l
  · rw [if_pos hjl, if_pos hjl, mul_one]
  · rw [if_neg hjl, if_neg hjl, mul_zero, ZOmegaSqrt2.of_zero]

/-! ## Reality of the cleared Bloch numerators + the coordinate bound -/

/-- **Reality of the cleared Bloch numerator** (in `ZOmega`): `conj (B i j) = B i j`.
Lifts `blochEntry_realizable_real` through the clearing (`of` injective + `conj_of`
+ `conj_sqrt2_pow`). -/
theorem blochNum_real {M : Mat2} (h : IsCliffordTRealizable M) (i j : Fin 3) :
    ZOmega.conj (blochNum M i j) = blochNum M i j := by
  apply of_injective
  rw [← ZOmegaSqrt2.conj_of, ← blochNum_spec, ZOmegaSqrt2.conj_mul,
      ZOmegaSqrt2.conj_sqrt2_pow, blochEntry_realizable_real h]

/-- Reality forces the `ω²`-coordinate to vanish. -/
theorem blochNum_b_zero {M : Mat2} (h : IsCliffordTRealizable M) (i j : Fin 3) :
    (blochNum M i j).b = 0 := by
  have hb := congrArg ZOmega.b (blochNum_real h i j)
  simp only [ZOmega.conj_b] at hb; omega

/-- Reality forces the `ω³`-coordinate to be `−a`. -/
theorem blochNum_c_eq {M : Mat2} (h : IsCliffordTRealizable M) (i j : Fin 3) :
    (blochNum M i j).c = -(blochNum M i j).a := by
  have hc := congrArg ZOmega.c (blochNum_real h i j)
  simp only [ZOmega.conj_c] at hc; omega

/-- **Per-column squared-modulus sum** `∑ᵢ |Bᵢⱼ|² = 2^kSO3` in `ZOmega`: by reality
`|Bᵢⱼ|² = Bᵢⱼ · conj Bᵢⱼ = Bᵢⱼ²`, so this is the `j = j` case of `blochNum_orthogonal`. -/
theorem blochNum_normSq_sum {M : Mat2} (h : IsCliffordTRealizable M) (j : Fin 3) :
    ∑ i, ZOmega.normSq (blochNum M i j) = (2 : ZOmega) ^ kSO3 M := by
  have hortho := blochNum_orthogonal (isUnitaryT_of_isCliffordTRealizable h) j j
  rw [if_pos rfl] at hortho
  rw [← hortho]
  apply Finset.sum_congr rfl
  intro i _
  rw [ZOmega.normSq, blochNum_real h i j]

/-- **`(2 : ZOmega)^k` has rational part `2^k`.** -/
theorem two_pow_d (k : ℕ) : ((2 : ZOmega) ^ k).d = 2 ^ k := by
  induction k with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ, pow_succ]
      rw [show (2 : ZOmega) = ZOmega.ofInt 2 from rfl] at *
      simp only [ZOmega.mul_d, ZOmega.ofInt_a, ZOmega.ofInt_b, ZOmega.ofInt_c, ZOmega.ofInt_d] at *
      ring_nf
      ring_nf at ih
      omega

/-- **Coordinate bound** from `kSO3 ≤ 3`: each cleared Bloch numerator's
squared-modulus rational part `(|Bᵢⱼ|²).d = a²+b²+c²+d² ≤ 2^kSO3 ≤ 8` (since the
three sum to `2^kSO3` and each is a sum of squares `≥ 0`). -/
theorem blochNum_normSq_d_le {M : Mat2} (h : IsCliffordTRealizable M) (hk : kSO3 M ≤ 3)
    (i j : Fin 3) : (ZOmega.normSq (blochNum M i j)).d ≤ 8 := by
  have hsum := congrArg ZOmega.d (blochNum_normSq_sum h j)
  rw [two_pow_d] at hsum
  have hsumd : ∑ i', (ZOmega.normSq (blochNum M i' j)).d = 2 ^ kSO3 M := by
    rw [← hsum]; simp [Fin.sum_univ_three, ZOmega.add_d]
  have hle : (ZOmega.normSq (blochNum M i j)).d ≤ 2 ^ kSO3 M := by
    rw [← hsumd]
    have hnn : ∀ i', 0 ≤ (ZOmega.normSq (blochNum M i' j)).d := by
      intro i'; rw [ZOmega.normSq_d]; positivity
    fin_cases i <;> simp_all [Fin.sum_univ_three] <;> nlinarith [hnn 0, hnn 1, hnn 2]
  have : (2 : ℤ) ^ kSO3 M ≤ 8 := by
    calc (2:ℤ)^kSO3 M ≤ 2^3 := pow_le_pow_right₀ (by norm_num) hk
      _ = 8 := by norm_num
  omega

/-! ## The `ma_step` existence `native_decide` core (column-decomposed) -/

/-- A cleared Bloch column as a `ZOmega` triple (entries at rows `0,1,2`). -/
abbrev Col : Type := ZOmega × ZOmega × ZOmega

/-- Self dot-product `∑ᵢ cᵢ²` (the cleared column's squared modulus, `= 2^kSO3`). -/
def Col.selfDot (c : Col) : ZOmega := c.1 * c.1 + c.2.1 * c.2.1 + c.2.2 * c.2.2

/-- Dot-product `∑ᵢ bᵢ cᵢ` (`= 0` for distinct cleared Bloch columns). -/
def Col.dot (b c : Col) : ZOmega := b.1 * c.1 + b.2.1 * c.2.1 + b.2.2 * c.2.2

/-- `(2 : ZOmega) ∣ x`, decided componentwise. -/
def dvdTwo (x : ZOmega) : Bool :=
  (x.a % 2 == 0) && (x.b % 2 == 0) && (x.c % 2 == 0) && (x.d % 2 == 0)

/-- `dvdTwo x = true → (2 : ZOmega) ∣ x` — the bridge to the `kSO3_stripMat_lt` hypothesis. -/
theorem dvd_two_of_dvdTwo {x : ZOmega} (h : dvdTwo x = true) : (2 : ZOmega) ∣ x := by
  simp only [dvdTwo, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨ha, hb⟩, hc⟩, hd⟩ := h
  refine ⟨⟨x.a / 2, x.b / 2, x.c / 2, x.d / 2⟩, ?_⟩
  have e2 : (2 : ZOmega) = ZOmega.ofInt 2 := rfl
  ext <;> simp only [e2, ZOmega.mul_a, ZOmega.mul_b, ZOmega.mul_c, ZOmega.mul_d,
    ZOmega.ofInt_a, ZOmega.ofInt_b, ZOmega.ofInt_c, ZOmega.ofInt_d] <;> ring_nf <;> omega

/-- The `i`-th stripped numerator `(c^s · column)ᵢ = ∑ₖ sylBlochNum s i k · cₖ`. -/
def stripRow (s : Syllable) (i : Fin 3) (c : Col) : ZOmega :=
  sylBlochNum s i 0 * c.1 + sylBlochNum s i 1 * c.2.1 + sylBlochNum s i 2 * c.2.2

/-- Syllable `s` "kills" column `c`: `2 ∣ (c^s·c)ᵢ` for every row `i`. -/
def colKills (s : Syllable) (c : Col) : Bool :=
  dvdTwo (stripRow s 0 c) && dvdTwo (stripRow s 1 c) && dvdTwo (stripRow s 2 c)

/-- Some syllable kills all three columns. -/
def someKills (A B C : Col) : Bool :=
  [Syllable.T, Syllable.HT, Syllable.SHT].any
    (fun s => colKills s A && colKills s B && colKills s C)

/-- `√2 ∤` the column triple: some entry has odd rational part `.d` (the `kSO3`-exact
clearing condition; `√2 ∣ ⟨a,0,-a,d⟩ ⟺ d` even). -/
def notSqrt2Div (A B C : Col) : Bool :=
  [A.1, A.2.1, A.2.2, B.1, B.2.1, B.2.2, C.1, C.2.1, C.2.2].any (fun x => x.d % 2 == 1)

/-- The 25 real bounded `ZOmega` elements `⟨a,0,-a,d⟩`, `|a|,|d| ≤ 2`. -/
def realBoxList : List ZOmega :=
  (List.range 5).flatMap (fun ai => (List.range 5).map (fun di =>
    (⟨(ai : ℤ) - 2, 0, -((ai : ℤ) - 2), (di : ℤ) - 2⟩ : ZOmega)))

/-- Columns from `realBoxList` with `selfDot = ⟨0,0,0,t⟩` (`= 2^k`). -/
def validCol (t : ℤ) : List Col :=
  (realBoxList.flatMap (fun x => realBoxList.flatMap (fun y =>
    realBoxList.map (fun z => ((x, y, z) : Col))))).filter
      (fun c => decide (Col.selfDot c = (⟨0, 0, 0, t⟩ : ZOmega)))

set_option maxRecDepth 10000 in
/-- **The `ma_step` existence core** (`native_decide`): for every `t ∈ {2,4,8}` and every
triple of `selfDot = t` columns that are pairwise orthogonal and `√2`-indivisible, some
syllable kills all three (i.e. lowers `kSO3` by ≥ 1 on the corresponding strip). The exact
orthogonality `BᵀB = 2^k I` (a superset of the achievable Bloch images, NO closure lemma
needed) suffices. Validated in `scripts/kmm_ma_step_residue.py` / `/tmp/btb_columns.py`
(0 failures over `k = 1,2,3`). -/
theorem maStep_exists_core :
    ([2, 4, 8] : List ℤ).all (fun t =>
      (validCol t).all (fun A => (validCol t).all (fun B => (validCol t).all (fun C =>
        !(decide (Col.dot A B = 0) && decide (Col.dot A C = 0) && decide (Col.dot B C = 0)
            && notSqrt2Div A B C)
          || someKills A B C)))) = true := by
  native_decide

end KMM

end SKEFTHawking.RossSelinger
