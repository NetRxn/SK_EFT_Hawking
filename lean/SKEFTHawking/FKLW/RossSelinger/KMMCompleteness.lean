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
import SKEFTHawking.FKLW.RossSelinger.GridSynth
import SKEFTHawking.FKLW.RossSelinger.BridgeStructural
import SKEFTHawking.FKLW.RossSelinger.MAStepStructural

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

Unitary mirrors of the `MAStepExists`/`MAStepStructural` chain: with reality now free
(`blochNum_*_u`) and orthogonality already `IsUnitaryT` (`blochNum_orthogonal`), every
realizability hypothesis in the MA-step existence collapses to bare `IsUnitaryT`. -/

/-- Per-column squared-modulus sum (realizability-free). -/
theorem blochNum_normSq_sum_u {M : Mat2} (hu : IsUnitaryT M) (j : Fin 3) :
    ∑ i, ZOmega.normSq (blochNum M i j) = (2 : ZOmega) ^ kSO3 M := by
  have hortho := blochNum_orthogonal hu j j
  rw [if_pos rfl] at hortho
  rw [← hortho]; apply Finset.sum_congr rfl; intro i _; rw [ZOmega.normSq, blochNum_real_u M i j]


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



/-- `√2 ∤` the column triple (realizability-free). -/
theorem col_notSqrt2Div_u (M : Mat2) (hk1 : 1 ≤ kSO3 M) :
    notSqrt2Div (blochNum M 0 0, blochNum M 1 0, blochNum M 2 0)
      (blochNum M 0 1, blochNum M 1 1, blochNum M 2 1)
      (blochNum M 0 2, blochNum M 1 2, blochNum M 2 2) = true := by
  obtain ⟨i, j, hij⟩ := blochNum_exists_odd_d_u M hk1
  rw [notSqrt2Div, List.any_eq_true]
  exact ⟨blochNum M i j, by fin_cases i <;> fin_cases j <;> simp,
    by rw [beq_iff_eq]; exact hij⟩

/-- **`ma_step` existence, realizability-free AND bound-free**: a unitary `M` with
`kSO3 M ≥ 1` admits a syllable strip lowering `kSO3` by ≥ 1 — the MA recursion's reducing
step from bare unitarity, via the structural parity theorem `someKills_of_orthogonal`
(`MAStepStructural.lean` — no box, and the former `kSO3 ≤ 3` hypothesis is gone). -/
theorem ma_step_exists_u {M : Mat2} (hu : IsUnitaryT M) (hk1 : 1 ≤ kSO3 M) :
    ∃ s : Syllable, kSO3 (stripMat s M) < kSO3 M := by
  have hreal : ∀ j : Fin 3,
      ColReal (blochNum M 0 j, blochNum M 1 j, blochNum M 2 j) := fun j =>
    ⟨blochNum_b_zero_u M 0 j, blochNum_c_eq_u M 0 j, blochNum_b_zero_u M 1 j,
      blochNum_c_eq_u M 1 j, blochNum_b_zero_u M 2 j, blochNum_c_eq_u M 2 j⟩
  have ht : (2 : ℤ) ^ kSO3 M % 2 = 0 := by
    have : (2 : ℤ) ^ kSO3 M = 2 * 2 ^ (kSO3 M - 1) := by
      rw [← pow_succ', show kSO3 M - 1 + 1 = kSO3 M from by omega]
    omega
  have hkills := someKills_of_orthogonal ht (hreal 0) (hreal 1) (hreal 2)
    (col_selfDot hu 0) (col_selfDot hu 1) (col_selfDot hu 2)
    (col_dot_eq_zero hu (by decide)) (col_dot_eq_zero hu (by decide))
    (col_dot_eq_zero hu (by decide)) (col_notSqrt2Div_u M hk1)
  rw [someKills, List.any_eq_true] at hkills
  obtain ⟨s, -, hs⟩ := hkills
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
      ZOmega.dividesSqrt2 (ZOmega.normSq x) := by
  obtain ⟨x, y, hx, hy, -, -⟩ := column0_cleared_bounded hu hμ
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
  exact ⟨x, y, kd, hMrec, hsum, hdvd⟩

/-! ## `stripMat` / `reduceStep` preservation + the base case + the KMM Theorem-1 converse -/

/-- `stripMat` preserves unitarity (`adjoint (sylMat s)` is realizable hence unitary). -/
theorem isUnitaryT_stripMat {M : Mat2} (hu : IsUnitaryT M) (s : Syllable) :
    IsUnitaryT (stripMat s M) := by
  rw [stripMat]
  exact (isUnitaryT_of_isCliffordTRealizable (IsCliffordTRealizable.adjoint ⟨sylWord s, rfl⟩)).mul hu

/-- **Determinant of the adjoint** `det (M†) = conj (det M)` (`2×2`). -/
theorem det_adjoint (M : Mat2) : Matrix.det (ZOmegaSqrt2.adjoint M) = conj (Matrix.det M) := by
  have hcn : ∀ x : ZOmegaSqrt2, conj (-x) = -conj x :=
    fun x => eq_neg_of_add_eq_zero_left (by rw [← conj_add, neg_add_cancel, conj_zero])
  rw [Matrix.det_fin_two, Matrix.det_fin_two, adjoint_apply, adjoint_apply, adjoint_apply,
      adjoint_apply,
      show M 0 0 * M 1 1 - M 0 1 * M 1 0 = M 0 0 * M 1 1 + -(M 0 1 * M 1 0) from by ring,
      conj_add, hcn, ZOmegaSqrt2.conj_mul, ZOmegaSqrt2.conj_mul]
  ring

/-- `conj (ωS^k) = ωS^{7k}` (`conj ωS = ωS⁷`, the `*`-involution on the `8`th root). -/
theorem conj_omegaS_pow (k : ℕ) : conj (ωS ^ k) = ωS ^ (7 * k) := by
  induction k with
  | zero => simp only [Nat.mul_zero, pow_zero]; decide
  | succ n ih =>
    rw [pow_succ, ZOmegaSqrt2.conj_mul, ih, show conj ωS = ωS ^ 7 from by decide,
        ← pow_add, show 7 * (n + 1) = 7 * n + 7 from by ring]

/-- `stripMat` preserves the `det = ωᵏ` class (`det_mul` + `det_adjoint` + `conj_omegaS_pow`). -/
theorem det_stripMat' {M : Mat2} (hdet : ∃ k, Matrix.det M = ωS ^ k) (s : Syllable) :
    ∃ k', Matrix.det (stripMat s M) = ωS ^ k' := by
  obtain ⟨k, hdet⟩ := hdet
  obtain ⟨ks, hks⟩ :=
    det_realizable_eq_omega_pow (⟨sylWord s, rfl⟩ : IsCliffordTRealizable (sylMat s))
  exact ⟨7 * ks + k, by rw [stripMat, show (ZOmegaSqrt2.adjoint (sylMat s) * M).det
      = (ZOmegaSqrt2.adjoint (sylMat s)).det * M.det from Matrix.det_mul _ _,
      det_adjoint, hks, conj_omegaS_pow, hdet, ← pow_add]⟩

/-- **`μ ≤ kSO3 + 2`, realizability-free** (was `muMeasure_le_kSO3_add_two`): the `(z,z)` Bloch
entry collapses via `unitary_col1` (instead of `realizable_col1`) to `R(M)₂₂ = 2|M₀₀|²−1`. -/
theorem muMeasure_le_kSO3_add_two_u {M : Mat2} (hu : IsUnitaryT M) {kd : ℕ}
    (hdet : Matrix.det M = ωS ^ kd) : muMeasure M ≤ kSO3 M + 2 := by
  have hbloch : blochEntry M 2 2 = half * (normSq (M 0 0) - normSq (M 0 1)
      - normSq (M 1 0) + normSq (M 1 1)) := by
    simp only [blochEntry, pauliMat, gateMatrix, Matrix.trace_fin_two, Matrix.mul_apply,
      Fin.sum_univ_two, adjoint_apply, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.of_apply, Matrix.cons_val', Matrix.empty_val', Matrix.cons_val_fin_one, normSq]
    ring
  have hc0 := unitary_col0_normSq hu
  obtain ⟨h01, h11⟩ := unitary_col1 hu hdet
  have hr11 : normSq (M 1 1) = normSq (M 0 0) := by
    rw [h11, normSq_mul, show ωS = of ZOmega.ω from rfl, normSq_omega_pow, one_mul, normSq_conj']
  have hr01 : normSq (M 0 1) = normSq (M 1 0) := by
    rw [h01, normSq_neg', normSq_mul, show ωS = of ZOmega.ω from rfl, normSq_omega_pow, one_mul,
      normSq_conj']
  have hhalf : half + half = 1 := by rw [half, mk_add, one_def, mk_eq_mk_iff]; decide
  have hc' : normSq (M 1 0) = 1 - normSq (M 0 0) := by linear_combination hc0
  have hid : normSq (M 0 0) = (blochEntry M 2 2 + 1) * half := by
    rw [hbloch, hr11, hr01, hc']
    linear_combination (half - normSq (M 0 0) - 2 * normSq (M 0 0) * half) * hhalf
  unfold muMeasure
  rw [hid]
  have h2 : denExp half = 2 := by rw [half, denExp_mk]; decide
  calc denExp ((blochEntry M 2 2 + 1) * half)
      ≤ denExp (blochEntry M 2 2 + 1) + denExp half := denExp_mul_le _ _
    _ ≤ denExp (blochEntry M 2 2) + 2 := by
        have := denExp_add_le (blochEntry M 2 2) 1; rw [denExp_one] at this; rw [h2]; omega
    _ ≤ kSO3 M + 2 := by have := denExp_blochEntry_le_kSO3 M 2 2; omega

/-- **The `μ → kSO3` bridge, realizability-free** (was `bridge`): `μ ≤ 3 ⟹ kSO3 ≤ 3` from
`IsUnitaryT` + `det = ωᵏ`, via `reconstruct_box_data_unitary` + the structural
`kSO3_reconstruct_le_three'` (`BridgeStructural.lean` — no finite check). -/
theorem bridge_u {M : Mat2} (hu : IsUnitaryT M) {kd : ℕ} (hdet : Matrix.det M = ωS ^ kd)
    (hμ : muMeasure M ≤ 3) : kSO3 M ≤ 3 := by
  obtain ⟨x, y, k, hMrec, hsum, hdvd⟩ := reconstruct_box_data_unitary hu hdet hμ
  rw [hMrec]; exact kSO3_reconstruct_le_three' hsum hdvd k

/-- **The Clifford base, realizability-free** (was `cliffordBase`): a unitary `M` with
`det = ωᵏ` and `kSO3 M = 0` is realizable — STRUCTURAL via `reconstruct_box_data_unitary` +
the `kSO3 = 0` quantization + the per-class kernel coverage checks (no box, no
`native_decide`). -/
theorem cliffordBase_u {M : Mat2} (hu : IsUnitaryT M) (hdet : ∃ k, Matrix.det M = ωS ^ k)
    (hk0 : kSO3 M = 0) : ∃ gs : List CliffordTGate, interp gs = M := by
  obtain ⟨kd, hkd⟩ := hdet
  have hμ : muMeasure M ≤ 3 := by have := muMeasure_le_kSO3_add_two_u hu hkd; omega
  obtain ⟨x, y, k, hMrec, hsum, hdvd⟩ := reconstruct_box_data_unitary hu hkd hμ
  have hk0' : kSO3 (reconstruct x y (k % 8)) = 0 := by rw [← reconstruct_mod, ← hMrec]; exact hk0
  have hk8 : k % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hZZ := four_dvd_normSq_sub_of_kSO3_eq_zero hk0'
  rcases normSq_quantized hsum hZZ with ⟨hx0, hy4⟩ | ⟨hx2, hy2⟩ | ⟨hx4, hy0⟩
  · obtain ⟨b, hb, rfl⟩ := ZOmega.two_torsion_of_normSq_eq_four hy4
    subst hx0
    obtain ⟨hint, -⟩ := cliffordCover_y2 b hb (k % 8) hk8 hk0'
    exact ⟨_, by rw [hint, hMrec, reconstruct_mod _ _ k]⟩
  · obtain ⟨a, ha, rfl⟩ := ZOmega.sqrt2_torsion_of_normSq_eq_two hx2
    obtain ⟨b, hb, rfl⟩ := ZOmega.sqrt2_torsion_of_normSq_eq_two hy2
    obtain ⟨hint, -⟩ := cliffordCover_mid a ha b hb (k % 8) hk8 hk0'
    exact ⟨_, by rw [hint, hMrec, reconstruct_mod _ _ k]⟩
  · obtain ⟨a, ha, rfl⟩ := ZOmega.two_torsion_of_normSq_eq_four hx4
    subst hy0
    obtain ⟨hint, -⟩ := cliffordCover_x2 a ha (k % 8) hk8 hk0'
    exact ⟨_, by rw [hint, hMrec, reconstruct_mod _ _ k]⟩

/-- **MA base coverage, realizability-free**: every unitary `M` with `det = ωᵏ` and
`kSO3 M = n ≤ 3` is realizable. Strong induction on `n`; base `cliffordBase_u`, step strips an
`ma_step_exists_u` syllable (drops `kSO3`, preserves unitarity+det). -/
theorem maCoverage_aux_u :
    ∀ (n : ℕ) (M : Mat2), IsUnitaryT M → (∃ k, Matrix.det M = ωS ^ k) → kSO3 M = n → n ≤ 3 →
      ∃ gs : List CliffordTGate, interp gs = M := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M hu hdet hkn hn3
    rcases Nat.eq_zero_or_pos n with hn0 | hnpos
    · subst hn0; exact cliffordBase_u hu hdet hkn
    · obtain ⟨s, hlt⟩ := ma_step_exists_u hu (by omega)
      have hmn : kSO3 (stripMat s M) < n := by rw [← hkn]; exact hlt
      obtain ⟨gs', hgs'⟩ := ih (kSO3 (stripMat s M)) hmn (stripMat s M)
        (isUnitaryT_stripMat hu s) (det_stripMat' hdet s) rfl (by omega)
      exact ⟨sylWord s ++ gs', by rw [interp_append, hgs', interp_sylWord_stripMat]⟩

/-- **KMM Theorem 1 converse (auxiliary, strong induction on `μ`).** -/
theorem kmm_completeness_aux :
    ∀ (μ : ℕ) (M : Mat2), IsUnitaryT M → (∃ k, Matrix.det M = ωS ^ k) → muMeasure M = μ →
      IsCliffordTRealizable M := by
  intro μ
  induction μ using Nat.strong_induction_on with
  | _ μ ih =>
    intro M hu hdet hμeq
    by_cases h3 : muMeasure M ≤ 3
    · obtain ⟨kd, hkd⟩ := hdet
      exact maCoverage_aux_u (kSO3 M) M hu ⟨kd, hkd⟩ rfl (bridge_u hu hkd h3)
    · have h4 : 4 ≤ denExp (normSq (M 0 0)) := by unfold muMeasure at h3; omega
      obtain ⟨k, hk⟩ := mu_decrease hu h4
      have hlt : muMeasure (reduceStep M k) < μ := by rw [← hμeq]; exact hk
      obtain ⟨kd, hkd⟩ := hdet
      have hIH := ih (muMeasure (reduceStep M k)) hlt (reduceStep M k)
        (isUnitaryT_reduceStep hu k) (det_reduceStep hkd k) rfl
      rw [← interp_reconWordC_reduceStep M k]
      exact IsCliffordTRealizable.mul
        (⟨reconWordC (k : ℕ), rfl⟩ : IsCliffordTRealizable (interp (reconWordC (k : ℕ)))) hIH

/-- **KMM Theorem 1 converse (completeness)** — the deep direction: every `2×2` matrix that is
unitary over `ZOmegaSqrt2` with determinant `ωᵏ` is Clifford+T-realizable. Strong induction on
`μ(M) = denExp(|M₀₀|²)`: the base (`μ ≤ 3`) is the realizability-free MA coverage
(`maCoverage_aux_u`, resting on the keystone `blochEntry_real`); the step (`μ ≥ 4`) descends via
`reduceStep = H·Tᵏ·M` (`mu_decrease` lowers `μ`; `reduceStep` preserves unitarity+det) and
reconstructs `M = interp (reconWordC k) · reduceStep M k`.

Together with `det_realizable_eq_omega_pow` (the easy direction) this is the full KMM Theorem 1
characterisation: **`IsCliffordTRealizable M ↔ IsUnitaryT M ∧ ∃ k, det M = ωS^k`**. In
particular it makes *any* constructed `SU(2)`-over-`ℤ[ω][1/√2]` unitary — e.g.
`GridSynth.assembleUnitary` (just certified `IsUnitaryT` + `det = 1`) — exactly synthesizable
by `kmmReduce`, closing the realizability gap in the Ross-Selinger grid-synthesis compiler. -/
theorem kmm_completeness {M : Mat2} (hu : IsUnitaryT M) (hdet : ∃ k, Matrix.det M = ωS ^ k) :
    IsCliffordTRealizable M :=
  kmm_completeness_aux (muMeasure M) M hu hdet rfl

/-- **`assembleUnitary` output is Clifford+T-realizable**: the immediate corollary tying the
grid-synthesis step (d) to the synthesizer — a solved `(u, t)` pair satisfying the Diophantine
constraint yields a matrix in the `interp` image (so `kmmReduce` synthesizes it exactly). -/
theorem isCliffordTRealizable_assembleUnitary (u t : ZOmega) (k : ℕ)
    (h : ZOmega.normSq u + ZOmega.normSq t = (⟨0, 0, 0, 2 ^ k⟩ : ZOmega)) :
    IsCliffordTRealizable (assembleUnitary u t k) :=
  kmm_completeness (isUnitaryT_assembleUnitary u t k h) ⟨0, by rw [det_assembleUnitary u t k h, pow_zero]⟩

end KMM

end SKEFTHawking.RossSelinger
