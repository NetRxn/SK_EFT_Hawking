/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F — `ma_step` existence SUBSTRATE (columns, kills, reality)

`MAStepDecrease.lean` shipped the GIVEN-condition⟹decrease direction
(`kSO3_stripMat_lt`): if the mod-2 condition `∀ i,j: 2 ∣ blochStripNum s M i j`
holds, then `kSO3 (stripMat s M) < kSO3 M`. This file supplies the SUBSTRATE for
the missing existence half: the column/kill vocabulary (`Col`, `dvdTwo`,
`colKills`, `someKills`, `notSqrt2Div`, `stripRow`) and the exact constraints
on the cleared Bloch numerators `B := blochNum M`:

  * **Orthogonality** `∑ᵢ Bᵢⱼ · Bᵢₗ = 2^kSO3 · δⱼₗ` (cleared `blochMat_transpose_mul`).
  * **Reality** `conj (B i j) = B i j` (`R(M) ∈ SO(3)` is real; multiplicative
    via `bloch_hom` + per-gate `decide`), forcing each `B i j` into the real
    subring `⟨a,0,−a,d⟩`.
  * **`kSO3`-exactness** (`blochNum_exists_odd_d`): some numerator has odd `.d`.

The existence theorem itself (`ma_step_exists`) lives in `MAStepStructural.lean`,
proved **structurally** (Phase 6AO Track 3): the former `native_decide` core
(`maStep_exists_core`, a ~809k-tuple sweep over the `validCol t`³ box,
`t ∈ {2,4,8}`) was eliminated 2026-06-10 in favor of the Giles–Selinger §6
parity argument, which needs no box, no coordinate bound, and no `kSO3 ≤ 3`
hypothesis. (The historical box validation: `scripts/kmm_ma_step_residue.py`,
0 failures over k = 1,2,3.)

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected (`maxRecDepth` only, finite `decide`).
- **#15** (no new project-local axioms): respected. No `native_decide`.

-/

import SKEFTHawking.FKLW.RossSelinger.MAStepDecrease
import SKEFTHawking.FKLW.RossSelinger.BlochOrthogonal
import SKEFTHawking.FKLW.RossSelinger.UnitaryClosure
import SKEFTHawking.FKLW.RossSelinger.KMMLemma3Bridge
import SKEFTHawking.FKLW.RossSelinger.GdeSqrt2

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
structural-existence domain. `conj` is a ring hom and `bloch_hom` makes reality
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
pairwise orthogonality (`j ≠ l`) the structural `ma_step` existence consumes. -/
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

/-! ## Reality of the cleared Bloch numerators -/

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


/-! ## The column/kill vocabulary (column-decomposed) -/

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


/-! ## Connecting `blochNum M` to the column vocabulary -/


/-- `(2 : ZOmega)^k = ⟨0,0,0,2^k⟩`. -/
theorem two_pow_eq (k : ℕ) : (2 : ZOmega) ^ k = (⟨0, 0, 0, 2 ^ k⟩ : ZOmega) := by
  induction k with
  | zero => rfl
  | succ n ih =>
      rw [pow_succ, ih, show (2 : ZOmega) = ZOmega.ofInt 2 from rfl]
      ext <;>
        simp only [ZOmega.mul_a, ZOmega.mul_b, ZOmega.mul_c, ZOmega.mul_d,
          ZOmega.ofInt_a, ZOmega.ofInt_b, ZOmega.ofInt_c, ZOmega.ofInt_d, pow_succ] <;> ring

/-- **`√2 ∤ B` from `kSO3`-exactness**: a realizable `M` with `kSO3 M ≥ 1` has some Bloch
numerator with odd rational part `.d` (i.e. `√2 ∤ Bᵢⱼ`). The `kSO3`-sup is attained at
some `(i,j)`; there `denExp (blochEntry) = kSO3 M`, so the cleared numerator is NOT
`√2`-divisible (else `√2^(kSO3-1)` would clear it, lowering `denExp`); and for a real
numerator `√2 ∤ ⟺ d` odd. -/
theorem blochNum_exists_odd_d {M : Mat2} (h : IsCliffordTRealizable M) (hk1 : 1 ≤ kSO3 M) :
    ∃ i j : Fin 3, (blochNum M i j).d % 2 = 1 := by
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin 3 × Fin 3))
    Finset.univ_nonempty (fun p => denExp (blochEntry M p.1 p.2))
  have hp' : kSO3 M = denExp (blochEntry M p.1 p.2) := hp
  refine ⟨p.1, p.2, ?_⟩
  by_contra hcon
  have hdeven : (blochNum M p.1 p.2).d % 2 = 0 := by omega
  have hdiv : ZOmega.dividesSqrt2 (blochNum M p.1 p.2) :=
    ⟨by rw [blochNum_c_eq h]; omega, by rw [blochNum_b_zero h]; omega⟩
  rw [ZOmega.dividesSqrt2_iff_dvd] at hdiv
  obtain ⟨w, hw⟩ := hdiv
  have hspec := blochNum_spec M p.1 p.2
  rw [hw, ZOmegaSqrt2.of_mul, show ZOmegaSqrt2.of ZOmega.sqrt2 = ZOmegaSqrt2.sqrt2 from rfl] at hspec
  -- hspec : sqrt2 ^ kSO3 M * blochEntry = sqrt2 * of w
  have hcancel : sqrt2 ^ (kSO3 M - 1) * blochEntry M p.1 p.2 = ZOmegaSqrt2.of w := by
    have key : ZOmegaSqrt2.sqrt2 * (sqrt2 ^ (kSO3 M - 1) * blochEntry M p.1 p.2)
        = ZOmegaSqrt2.sqrt2 * ZOmegaSqrt2.of w := by
      rw [← mul_assoc, ← pow_succ', show kSO3 M - 1 + 1 = kSO3 M from by omega]; exact hspec
    calc sqrt2 ^ (kSO3 M - 1) * blochEntry M p.1 p.2
        = invSqrt2 * (ZOmegaSqrt2.sqrt2 * (sqrt2 ^ (kSO3 M - 1) * blochEntry M p.1 p.2)) := by
          rw [← mul_assoc, ZOmegaSqrt2.invSqrt2_mul_sqrt2, one_mul]
      _ = invSqrt2 * (ZOmegaSqrt2.sqrt2 * ZOmegaSqrt2.of w) := by rw [key]
      _ = ZOmegaSqrt2.of w := by rw [← mul_assoc, ZOmegaSqrt2.invSqrt2_mul_sqrt2, one_mul]
  have hle : denExp (blochEntry M p.1 p.2) ≤ kSO3 M - 1 := denExp_le_iff.mpr ⟨w, hcancel⟩
  omega



/-- The stripped numerator of a Bloch column equals `blochStripNum`. -/
theorem stripRow_eq_blochStripNum (s : Syllable) (M : Mat2) (i j : Fin 3) :
    stripRow s i (blochNum M 0 j, blochNum M 1 j, blochNum M 2 j) = blochStripNum s M i j := by
  simp only [stripRow, blochStripNum, Fin.sum_univ_three]

/-- Pairwise orthogonality of the cleared Bloch columns (`j ≠ l`). -/
theorem col_dot_eq_zero {M : Mat2} (hu : ZOmegaSqrt2.IsUnitaryT M) {j l : Fin 3} (hjl : j ≠ l) :
    Col.dot (blochNum M 0 j, blochNum M 1 j, blochNum M 2 j)
      (blochNum M 0 l, blochNum M 1 l, blochNum M 2 l) = 0 := by
  have hb := blochNum_orthogonal hu j l
  rw [if_neg hjl, Fin.sum_univ_three] at hb
  show blochNum M 0 j * blochNum M 0 l + blochNum M 1 j * blochNum M 1 l
      + blochNum M 2 j * blochNum M 2 l = 0
  exact hb

/-- `√2 ∤ B`: the column triple of a realizable `kSO3 ≥ 1` matrix has some odd `.d` entry. -/
theorem col_notSqrt2Div {M : Mat2} (h : IsCliffordTRealizable M) (hk1 : 1 ≤ kSO3 M) :
    notSqrt2Div (blochNum M 0 0, blochNum M 1 0, blochNum M 2 0)
      (blochNum M 0 1, blochNum M 1 1, blochNum M 2 1)
      (blochNum M 0 2, blochNum M 1 2, blochNum M 2 2) = true := by
  obtain ⟨i, j, hij⟩ := blochNum_exists_odd_d h hk1
  rw [notSqrt2Div, List.any_eq_true]
  exact ⟨blochNum M i j, by fin_cases i <;> fin_cases j <;> simp,
    by rw [beq_iff_eq]; exact hij⟩

/-- From `colKills s (col j) = true`, the mod-2 condition `2 ∣ blochStripNum s M i j` for
every row `i` (`j` stays free — avoids `blochNum` whnf blow-up). -/
theorem colKills_blochStripNum_dvd (s : Syllable) (M : Mat2) (j : Fin 3)
    (hkj : colKills s (blochNum M 0 j, blochNum M 1 j, blochNum M 2 j) = true) (i : Fin 3) :
    (2 : ZOmega) ∣ blochStripNum s M i j := by
  rw [colKills, Bool.and_eq_true, Bool.and_eq_true] at hkj
  obtain ⟨⟨d0, d1⟩, d2⟩ := hkj
  have hdvd : (2 : ZOmega) ∣ stripRow s i (blochNum M 0 j, blochNum M 1 j, blochNum M 2 j) := by
    fin_cases i
    · exact dvd_two_of_dvdTwo d0
    · exact dvd_two_of_dvdTwo d1
    · exact dvd_two_of_dvdTwo d2
  rwa [stripRow_eq_blochStripNum] at hdvd


end KMM

end SKEFTHawking.RossSelinger
