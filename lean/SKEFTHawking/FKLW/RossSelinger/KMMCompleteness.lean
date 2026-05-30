/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item G — KMM Theorem 1 *converse* (completeness), descent ingredients

The shipped reduction machinery (`kmmReduceMu`, `coverage`, `cliffordBase`, …) all take
`IsCliffordTRealizable M` as a HYPOTHESIS — they *decompose* a matrix already known to be in
the `interp` image. The KMM Theorem 1 **converse**

  `IsUnitaryT M → (∃ k, det M = ωS^k) → IsCliffordTRealizable M`

is the deep direction: it makes *any* constructed `SU(2)`-over-`ℤ[ω][1/√2]` unitary
(e.g. `GridSynth.assembleUnitary`) synthesizable into a Clifford+T word, which is what the
grid-synthesis compiler (Items G/H/I) needs. The converse proof is a strong induction on the
squared-modulus sde `μ(M) = denExp (normSq (M 0 0))`:

  * **descent** (`μ ≥ 4`): `reduceStep M k = H·Tᵏ·M` is again unitary with `det = ωᵏ'` and
    strictly smaller `μ` (`mu_decrease`), and `M = interp (reconWordC k) · reduceStep M k`
    (`interp_reconWordC_reduceStep`) — so `M` is realizable as soon as `reduceStep M k` is.
  * **base** (`μ ≤ 3`): the 𝕊₃ coverage, realizability-free — the larger remaining piece
    (the MA-coverage chain `reconstruct_box_data → bridge → ma_step → coverage` must be
    re-pointed off realizability onto unitarity; `unitary_col1` + `reconstruct_box_data_unitary`
    here are the first links).

This file ships the **descent ingredients** (preservation of unitarity and `det = ωᵏ` under
`reduceStep`) and `reconstruct_box_data_unitary` (the box-data extraction, realizability-free,
via `unitary_col1`). The base-case re-point + the induction assembly are the next increments.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.CliffordBase
import SKEFTHawking.FKLW.RossSelinger.KMMForm
import SKEFTHawking.FKLW.RossSelinger.KMMDet
import SKEFTHawking.FKLW.RossSelinger.UnitaryClosure
import SKEFTHawking.FKLW.RossSelinger.MuDecrease

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace KMM

open CliffordTGate ZOmegaSqrt2
open scoped Matrix

/-! ## Unitarity / determinant are preserved under `reduceStep` (descent ingredients) -/

/-- **Every gate matrix is unitary** (singleton-word specialisation of `interp_isUnitaryT`). -/
theorem isUnitaryT_gateMatrix (g : CliffordTGate) : IsUnitaryT (gateMatrix g) := by
  simpa using interp_isUnitaryT [g]

/-- **The identity is unitary** (empty-word specialisation). -/
theorem isUnitaryT_one : IsUnitaryT (1 : Mat2) := by
  have := interp_isUnitaryT ([] : List CliffordTGate); rwa [interp_nil] at this

/-- **Unitarity is closed under powers**. -/
theorem isUnitaryT_pow {M : Mat2} (h : IsUnitaryT M) : ∀ n, IsUnitaryT (M ^ n)
  | 0 => by rw [pow_zero]; exact isUnitaryT_one
  | n + 1 => by rw [pow_succ]; exact (isUnitaryT_pow h n).mul h

/-- **`reduceStep` preserves unitarity**: `reduceStep M k = H·Tᵏ·M` is unitary when `M` is
(`H`, `Tᵏ` unitary; `IsUnitaryT.mul`). The first descent ingredient for KMM completeness. -/
theorem isUnitaryT_reduceStep {M : Mat2} (hu : IsUnitaryT M) (k : Fin 4) :
    IsUnitaryT (reduceStep M k) := by
  rw [reduceStep]
  exact ((isUnitaryT_gateMatrix .H).mul (isUnitaryT_pow (isUnitaryT_gateMatrix .T) _)).mul hu

/-- **`reduceStep` preserves the `det = ωᵏ` class**: `det (H·Tᵏ·M) = ω^{kH + kT·k + k}`
(`det_mul` + `det_pow` + `det_gateMatrix_eq_omega_pow`). The second descent ingredient. -/
theorem det_reduceStep {M : Mat2} {k : ℕ} (hdet : Matrix.det M = ωS ^ k) (j : Fin 4) :
    ∃ k' : ℕ, Matrix.det (reduceStep M j) = ωS ^ k' := by
  obtain ⟨kH, hH⟩ := det_gateMatrix_eq_omega_pow .H
  obtain ⟨kT, hT⟩ := det_gateMatrix_eq_omega_pow .T
  refine ⟨kH + kT * (j : ℕ) + k, ?_⟩
  rw [reduceStep,
      show (gateMatrix .H * gateMatrix .T ^ (j : ℕ) * M).det
        = (gateMatrix .H * gateMatrix .T ^ (j : ℕ)).det * M.det from Matrix.det_mul _ _,
      show (gateMatrix .H * gateMatrix .T ^ (j : ℕ)).det
        = (gateMatrix .H).det * (gateMatrix .T ^ (j : ℕ)).det from Matrix.det_mul _ _,
      Matrix.det_pow, hH, hT, hdet, ← pow_mul, ← pow_add, ← pow_add]

/-! ## The reality keystone (realizability-free) -/

/-- **Reality of the Bloch image, UNCONDITIONAL** — the keystone that frees the MA-coverage
base case from realizability. For *any* `M : Mat2`, `R(M)_{ij} = ½·Tr(σ_i·M·σ_j·M†)` is
conjugation-fixed (real). This needs **no** unitarity and **no** realizability: it is the
symmetry `conj(Tr(σ_i M σ_j M†)) = Tr(σ_i M σ_j M†)`, which holds because each Pauli satisfies
`σ̄ᵀ = σ` (`X̄ᵀ=X`, `Ȳᵀ=Y`, `Z̄ᵀ=Z`) and the trace is transpose- and cyclic-invariant —
i.e. `Tr(conjE σ_i · conjE M · conjE σ_j · conjE M†) = Tr(M σ_j M† σ_i) = Tr(σ_i M σ_j M†)`.
Proved by expanding the `2×2` trace and closing each of the 9 entries by `ring`
(`conj iS = -iS`; gate zeros via `conj_zero`).

The existing `blochEntry_realizable_real` (MAStepExists) proves the same fact by gate-word
induction (needs the realizable witness); this is the realizability-free generalisation that
lets `blochNum_real`/`b_zero`/`c_eq`/`normSq_sum`/… (and hence the whole MA base coverage)
re-point off realizability onto bare unitarity (`blochNum_orthogonal` already takes `IsUnitaryT`). -/
theorem blochEntry_real (M : Mat2) (i j : Fin 3) :
    conj (blochEntry M i j) = blochEntry M i j := by
  have hc1 : conj (1 : ZOmegaSqrt2) = 1 := by decide
  have hcn : ∀ x : ZOmegaSqrt2, conj (-x) = -conj x :=
    fun x => eq_neg_of_add_eq_zero_left (by rw [← conj_add, neg_add_cancel, conj_zero])
  have hci : conj iS = -iS := by decide
  rw [blochEntry, ZOmegaSqrt2.conj_mul, show conj half = half from by rw [half, conj_mk]; congr 1]
  congr 1
  fin_cases i <;> fin_cases j <;>
    simp only [pauliMat, Matrix.trace_fin_two, Matrix.mul_apply, Fin.sum_univ_two, adjoint_apply,
      gateMatrix, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.of_apply, Matrix.cons_val',
      Matrix.empty_val', Matrix.cons_val_fin_one, ZOmegaSqrt2.conj_add, ZOmegaSqrt2.conj_mul,
      ZOmegaSqrt2.conj_conj, ZOmegaSqrt2.conj_zero, hcn, hci, hc1] <;>
    ring

/-- **Reality of the cleared Bloch numerator, realizability-free** (was `blochNum_real`, which
needed the realizable witness): `conj (B i j) = B i j` in `ℤ[ω]`, lifting `blochEntry_real`
through the clearing (`of` injective + `conj_of` + `conj_sqrt2_pow`). -/
theorem blochNum_real_u (M : Mat2) (i j : Fin 3) :
    ZOmega.conj (blochNum M i j) = blochNum M i j := by
  apply of_injective
  rw [← ZOmegaSqrt2.conj_of, ← blochNum_spec, ZOmegaSqrt2.conj_mul,
      ZOmegaSqrt2.conj_sqrt2_pow, blochEntry_real]

/-- Reality forces the `ω²`-coordinate to vanish (realizability-free). -/
theorem blochNum_b_zero_u (M : Mat2) (i j : Fin 3) : (blochNum M i j).b = 0 := by
  have hb := congrArg ZOmega.b (blochNum_real_u M i j); simp only [ZOmega.conj_b] at hb; omega

/-- Reality forces the `ω³`-coordinate to be `−a` (realizability-free). -/
theorem blochNum_c_eq_u (M : Mat2) (i j : Fin 3) : (blochNum M i j).c = -(blochNum M i j).a := by
  have hc := congrArg ZOmega.c (blochNum_real_u M i j); simp only [ZOmega.conj_c] at hc; omega

/-! ## The MA reduction step, realizability-free (`ma_step_exists_u`)

Unitary mirrors of the `MAStepExists` chain: with reality now free (`blochNum_*_u`) and
orthogonality already `IsUnitaryT` (`blochNum_orthogonal`), every realizability hypothesis in
the MA-step existence collapses to bare `IsUnitaryT`. The bodies are the originals verbatim
with `isUnitaryT_of_isCliffordTRealizable h ↦ hu` and `blochNum_real/b_zero/c_eq h ↦ *_u M`. -/

/-- Per-column squared-modulus sum (realizability-free). -/
theorem blochNum_normSq_sum_u {M : Mat2} (hu : IsUnitaryT M) (j : Fin 3) :
    ∑ i, ZOmega.normSq (blochNum M i j) = (2 : ZOmega) ^ kSO3 M := by
  have hortho := blochNum_orthogonal hu j j
  rw [if_pos rfl] at hortho
  rw [← hortho]; apply Finset.sum_congr rfl; intro i _; rw [ZOmega.normSq, blochNum_real_u M i j]

/-- Coordinate bound from `kSO3 ≤ 3` (realizability-free). -/
theorem blochNum_normSq_d_le_u {M : Mat2} (hu : IsUnitaryT M) (hk : kSO3 M ≤ 3) (i j : Fin 3) :
    (ZOmega.normSq (blochNum M i j)).d ≤ 8 := by
  have hsum := congrArg ZOmega.d (blochNum_normSq_sum_u hu j)
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

/-- `√2 ∤ B` from `kSO3`-exactness (realizability-free — reality is automatic). -/
theorem blochNum_exists_odd_d_u (M : Mat2) (hk1 : 1 ≤ kSO3 M) :
    ∃ i j : Fin 3, (blochNum M i j).d % 2 = 1 := by
  obtain ⟨p, -, hp⟩ := Finset.exists_mem_eq_sup (Finset.univ : Finset (Fin 3 × Fin 3))
    Finset.univ_nonempty (fun p => denExp (blochEntry M p.1 p.2))
  have hp' : kSO3 M = denExp (blochEntry M p.1 p.2) := hp
  refine ⟨p.1, p.2, ?_⟩
  by_contra hcon
  have hdeven : (blochNum M p.1 p.2).d % 2 = 0 := by omega
  have hdiv : ZOmega.dividesSqrt2 (blochNum M p.1 p.2) :=
    ⟨by rw [blochNum_c_eq_u M]; omega, by rw [blochNum_b_zero_u M]; omega⟩
  rw [ZOmega.dividesSqrt2_iff_dvd] at hdiv
  obtain ⟨w, hw⟩ := hdiv
  have hspec := blochNum_spec M p.1 p.2
  rw [hw, ZOmegaSqrt2.of_mul, show ZOmegaSqrt2.of ZOmega.sqrt2 = ZOmegaSqrt2.sqrt2 from rfl] at hspec
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

/-- Each cleared Bloch numerator lies in `realBoxList` (realizability-free). -/
theorem blochNum_mem_realBoxList_u {M : Mat2} (hu : IsUnitaryT M) (hk3 : kSO3 M ≤ 3)
    (i j : Fin 3) : blochNum M i j ∈ realBoxList := by
  have hb := blochNum_b_zero_u M i j
  have hc := blochNum_c_eq_u M i j
  have hnd := blochNum_normSq_d_le_u hu hk3 i j
  rw [ZOmega.normSq_d, hb, hc] at hnd
  apply mem_realBoxList hb hc <;>
    nlinarith [sq_nonneg (blochNum M i j).a, sq_nonneg (blochNum M i j).d,
      sq_nonneg ((blochNum M i j).a - 2), sq_nonneg ((blochNum M i j).a + 2),
      sq_nonneg ((blochNum M i j).d - 2), sq_nonneg ((blochNum M i j).d + 2)]

/-- The `j`-th cleared Bloch column lies in `validCol (2^kSO3 M)` (realizability-free). -/
theorem col_mem_validCol_u {M : Mat2} (hu : IsUnitaryT M) (hk3 : kSO3 M ≤ 3) (j : Fin 3) :
    ((blochNum M 0 j, blochNum M 1 j, blochNum M 2 j) : Col) ∈ validCol (2 ^ kSO3 M) := by
  rw [validCol, List.mem_filter]
  refine ⟨?_, ?_⟩
  · rw [List.mem_flatMap]
    exact ⟨blochNum M 0 j, blochNum_mem_realBoxList_u hu hk3 0 j, by
      rw [List.mem_flatMap]
      exact ⟨blochNum M 1 j, blochNum_mem_realBoxList_u hu hk3 1 j, by
        rw [List.mem_map]
        exact ⟨blochNum M 2 j, blochNum_mem_realBoxList_u hu hk3 2 j, rfl⟩⟩⟩
  · rw [decide_eq_true_eq]
    have hortho := blochNum_orthogonal hu j j
    rw [if_pos rfl, Fin.sum_univ_three] at hortho
    show blochNum M 0 j * blochNum M 0 j + blochNum M 1 j * blochNum M 1 j
        + blochNum M 2 j * blochNum M 2 j = _
    rw [hortho, two_pow_eq]

/-- `√2 ∤` the column triple (realizability-free). -/
theorem col_notSqrt2Div_u (M : Mat2) (hk1 : 1 ≤ kSO3 M) :
    notSqrt2Div (blochNum M 0 0, blochNum M 1 0, blochNum M 2 0)
      (blochNum M 0 1, blochNum M 1 1, blochNum M 2 1)
      (blochNum M 0 2, blochNum M 1 2, blochNum M 2 2) = true := by
  obtain ⟨i, j, hij⟩ := blochNum_exists_odd_d_u M hk1
  rw [notSqrt2Div, List.any_eq_true]
  exact ⟨blochNum M i j, by fin_cases i <;> fin_cases j <;> simp,
    by rw [beq_iff_eq]; exact hij⟩

/-- **`ma_step` existence, realizability-free**: a unitary `M` with `1 ≤ kSO3 M ≤ 3` admits a
syllable strip lowering `kSO3` by ≥ 1 — the MA recursion's reducing step from bare unitarity
(the realizability hypothesis is gone). -/
theorem ma_step_exists_u {M : Mat2} (hu : IsUnitaryT M)
    (hk1 : 1 ≤ kSO3 M) (hk3 : kSO3 M ≤ 3) :
    ∃ s : Syllable, kSO3 (stripMat s M) < kSO3 M := by
  have htmem : (2 : ℤ) ^ kSO3 M ∈ ([2, 4, 8] : List ℤ) := by
    rcases (by omega : kSO3 M = 1 ∨ kSO3 M = 2 ∨ kSO3 M = 3) with hh | hh | hh <;> rw [hh] <;> decide
  have e4 := List.all_eq_true.mp (List.all_eq_true.mp (List.all_eq_true.mp
    (List.all_eq_true.mp maStep_exists_core _ htmem) _ (col_mem_validCol_u hu hk3 0))
    _ (col_mem_validCol_u hu hk3 1)) _ (col_mem_validCol_u hu hk3 2)
  have hbracket :
      (decide (Col.dot (blochNum M 0 0, blochNum M 1 0, blochNum M 2 0)
            (blochNum M 0 1, blochNum M 1 1, blochNum M 2 1) = 0)
        && decide (Col.dot (blochNum M 0 0, blochNum M 1 0, blochNum M 2 0)
            (blochNum M 0 2, blochNum M 1 2, blochNum M 2 2) = 0)
        && decide (Col.dot (blochNum M 0 1, blochNum M 1 1, blochNum M 2 1)
            (blochNum M 0 2, blochNum M 1 2, blochNum M 2 2) = 0)
        && notSqrt2Div (blochNum M 0 0, blochNum M 1 0, blochNum M 2 0)
            (blochNum M 0 1, blochNum M 1 1, blochNum M 2 1)
            (blochNum M 0 2, blochNum M 1 2, blochNum M 2 2)) = true := by
    rw [Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true, decide_eq_true_eq,
        decide_eq_true_eq, decide_eq_true_eq]
    exact ⟨⟨⟨col_dot_eq_zero hu (by decide), col_dot_eq_zero hu (by decide)⟩,
      col_dot_eq_zero hu (by decide)⟩, col_notSqrt2Div_u M hk1⟩
  rw [hbracket, Bool.not_true, Bool.false_or] at e4
  rw [someKills, List.any_eq_true] at e4
  obtain ⟨s, -, hs⟩ := e4
  rw [Bool.and_eq_true, Bool.and_eq_true] at hs
  obtain ⟨⟨hk0, hk1c⟩, hk2c⟩ := hs
  refine ⟨s, kSO3_stripMat_lt hu s hk1 (fun i j => ?_)⟩
  fin_cases j
  · exact colKills_blochStripNum_dvd s M 0 hk0 i
  · exact colKills_blochStripNum_dvd s M 1 hk1c i
  · exact colKills_blochStripNum_dvd s M 2 hk2c i

/-! ## Box-data extraction, realizability-free (base-case re-point, first link) -/

/-- **Box data of a `μ ≤ 3` unitary** (realizability-free form of `reconstruct_box_data`):
`M = reconstruct x y k` with `(x, y)` in the coordinate box and meeting the `𝕊₃` filter,
assuming only `IsUnitaryT M` + `det M = ωS^kd` (not `IsCliffordTRealizable M`). The col-1
structure comes from `unitary_col1` instead of `realizable_col1`; everything else
(`column0_cleared_bounded`, `unitary_col0_normSq`, the cleared-form algebra) already runs on
unitarity. This is the first link in re-pointing the MA-coverage base off realizability. -/
theorem reconstruct_box_data_unitary {M : Mat2} (hu : IsUnitaryT M) {kd : ℕ}
    (hkdet : Matrix.det M = ωS ^ kd) (hμ : muMeasure M ≤ 3) :
    ∃ (x y : ZOmega) (k : ℕ), M = reconstruct x y k ∧
      ZOmega.normSq x + ZOmega.normSq y = (⟨0, 0, 0, 4⟩ : ZOmega) ∧
      ZOmega.dividesSqrt2 (ZOmega.normSq x) ∧
      (ZOmega.normSq x).d ≤ 4 ∧ (ZOmega.normSq y).d ≤ 4 := by
  obtain ⟨x, y, hx, hy, hxd, hyd⟩ := column0_cleared_bounded hu hμ
  obtain ⟨hcol01, hcol11⟩ := unitary_col1 hu hkdet
  have h00 : M 0 0 = mk x 2 := eq_mk_of_sqrt2_pow_mul hx
  have h10 : M 1 0 = mk y 2 := eq_mk_of_sqrt2_pow_mul hy
  have hMrec : M = reconstruct x y kd := by
    rw [Matrix.eta_fin_two M, hcol01, hcol11, h00, h10]; rfl
  have hsum : ZOmega.normSq x + ZOmega.normSq y = (⟨0, 0, 0, 4⟩ : ZOmega) := by
    have := clearedCol_normSq_sum hx hy (unitary_col0_normSq hu)
    rwa [show ZOmega.sqrt2 ^ (2 * 2) = (⟨0, 0, 0, 4⟩ : ZOmega) from by decide] at this
  have hdvd : ZOmega.dividesSqrt2 (ZOmega.normSq x) := by
    obtain ⟨w, hw⟩ := denExp_le_iff.mp (show denExp (normSq (M 0 0)) ≤ 3 from hμ)
    have hns : ZOmega.normSq x = ZOmega.sqrt2 * w := by
      apply of_inj
      rw [of_mul, ← (sqrt2_pow_normSq_clearing hx), show 2 * 2 = 1 + 3 from rfl,
        pow_add, mul_assoc, hw, pow_one]
      simp only [sqrt2_def, of_def]
    exact (ZOmega.dividesSqrt2_iff_dvd _).mpr ⟨w, hns⟩
  exact ⟨x, y, kd, hMrec, hsum, hdvd, hxd, hyd⟩

end KMM

end SKEFTHawking.RossSelinger
