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
