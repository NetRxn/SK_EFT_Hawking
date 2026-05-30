/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item I — `compile_correct` (soundness of the Ross-Selinger compiler)

Composes the shipped pieces into the operator-norm approximation guarantee: when the grid finder
returns `(u, t, k)` with the cleared column `(u/√2^k, t/√2^k)` within `ε` of the target `SU(2)`
matrix's first column, the assembled unitary `assembleUnitary u t k` (det-1 SU(2), `GridSynth`)
approximates the target within `2ε` in the `linftyOpNorm` the Solovay-Kitaev headlines use, and
`kmmReduce` synthesizes it to an exact Clifford+T word. This is the SOUNDNESS half of `compile`;
completeness is the empirical ≥50-case pygridsynth cross-validation (the NT existence proof is the
roadmap's deferred optional follow-on).

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.RelativeNorm
import SKEFTHawking.FKLW.RossSelinger.GridSynth
import SKEFTHawking.FKLW.RossSelinger.CompileApprox
import SKEFTHawking.FKLW.RossSelinger.ComplexEmbeddingMatrix
import SKEFTHawking.FKLW.RossSelinger.GridSolver

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmegaSqrt2

/-- **`ZOmegaSqrt2.toComplex` is a `*`-homomorphism**: it intertwines `ZOmegaSqrt2.conj` with
complex conjugation. (Quotient induction `x = mk z k`; reduce to `ZOmega.toComplex_conj` and the
fact that `s2C = √2` is real, hence `star`-fixed.) -/
theorem toComplex_conj (x : ZOmegaSqrt2) :
    toComplex (conj x) = star (toComplex x) := by
  have hs : star s2C = s2C := by rw [s2C_eq]; simp
  induction x using Quotient.inductionOn with
  | _ a =>
    obtain ⟨z, k⟩ := a
    show toComplex (conj (mk z k)) = star (toComplex (mk z k))
    rw [conj_mk, toComplex_mk, toComplex_mk, _root_.SKEFTHawking.RossSelinger.toComplex_conj,
        star_div₀, star_pow, hs]

end ZOmegaSqrt2

open scoped Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup

/-- **First-column ε-approximation ⟹ `2ε` operator-norm approximation, for SU(2)-form matrices.**
If `M, U : Matrix (Fin 2) (Fin 2) ℂ` both have the SU(2) form `[[a, −b̄],[b, ā]]` (the second
column determined by the first via conjugation) and agree on the first column to within `ε`, then
`‖M − U‖ ≤ 2ε` in the `linftyOpNorm`. (The second-column entries differ by the conjugates of the
first-column differences, so all four entries are within `ε`; `linftyOpNorm_fin_two_le`.) -/
theorem linftyOpNorm_sub_le_of_su2_col {M U : Matrix (Fin 2) (Fin 2) ℂ} {ε : ℝ} (hε : 0 ≤ ε)
    (hM01 : M 0 1 = -star (M 1 0)) (hM11 : M 1 1 = star (M 0 0))
    (hU01 : U 0 1 = -star (U 1 0)) (hU11 : U 1 1 = star (U 0 0))
    (h00 : ‖M 0 0 - U 0 0‖ ≤ ε) (h10 : ‖M 1 0 - U 1 0‖ ≤ ε) :
    ‖M - U‖ ≤ 2 * ε := by
  refine linftyOpNorm_fin_two_le hε ?_
  simp only [Fin.forall_fin_two, Matrix.sub_apply]
  refine ⟨⟨h00, ?_⟩, h10, ?_⟩
  · rw [hM01, hU01,
        show -star (M 1 0) - -star (U 1 0) = -star (M 1 0 - U 1 0) from by rw [star_sub]; ring,
        norm_neg, norm_star]
    exact h10
  · rw [hM11, hU11,
        show star (M 0 0) - star (U 0 0) = star (M 0 0 - U 0 0) from (star_sub _ _).symm, norm_star]
    exact h00

/-- **`approx_assembleUnitary`** — the Ross-Selinger compile soundness step. If the grid finder's
cleared column `(mk u k, mk t k)` approximates the target `SU(2)` matrix `U`'s first column to
within `ε` (`|u/√2^k − U₀₀| ≤ ε`, `|t/√2^k − U₁₀| ≤ ε`), then the assembled (det-1 SU(2)) unitary
approximates `U` within `2ε` in operator norm. `toComplexMat (assembleUnitary u t k)` is in SU(2)
form by construction — diagonal `(toComplex(mk u k), star(toComplex(mk u k)))`, off-diagonal
`(−star(toComplex(mk t k)), toComplex(mk t k))` (the off-diagonals via `toComplex_conj`) — so
`linftyOpNorm_sub_le_of_su2_col` applies. -/
theorem approx_assembleUnitary (u t : ZOmega) (k : ℕ)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) {ε : ℝ} (hε : 0 ≤ ε)
    (h00 : ‖ZOmegaSqrt2.toComplex (ZOmegaSqrt2.mk u k) - (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ ≤ ε)
    (h10 : ‖ZOmegaSqrt2.toComplex (ZOmegaSqrt2.mk t k) - (U : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ≤ ε) :
    ‖toComplexMat (KMM.assembleUnitary u t k) - (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 2 * ε := by
  obtain ⟨hU01, hU11⟩ := su2_entry_structure U
  have e00 : toComplexMat (KMM.assembleUnitary u t k) 0 0
      = ZOmegaSqrt2.toComplex (ZOmegaSqrt2.mk u k) := by
    simp only [toComplexMat, RingHom.mapMatrix_apply, Matrix.map_apply,
      KMM.assembleUnitary_apply_zero_zero]
  have e10 : toComplexMat (KMM.assembleUnitary u t k) 1 0
      = ZOmegaSqrt2.toComplex (ZOmegaSqrt2.mk t k) := by
    simp only [toComplexMat, RingHom.mapMatrix_apply, Matrix.map_apply,
      KMM.assembleUnitary_apply_one_zero]
  have e01 : toComplexMat (KMM.assembleUnitary u t k) 0 1
      = -star (ZOmegaSqrt2.toComplex (ZOmegaSqrt2.mk t k)) := by
    show ZOmegaSqrt2.toComplex (KMM.assembleUnitary u t k 0 1) = _
    rw [show KMM.assembleUnitary u t k 0 1 = -(ZOmegaSqrt2.conj (ZOmegaSqrt2.mk t k)) from rfl,
        map_neg, ZOmegaSqrt2.toComplex_conj]
  have e11 : toComplexMat (KMM.assembleUnitary u t k) 1 1
      = star (ZOmegaSqrt2.toComplex (ZOmegaSqrt2.mk u k)) := by
    show ZOmegaSqrt2.toComplex (KMM.assembleUnitary u t k 1 1) = _
    rw [show KMM.assembleUnitary u t k 1 1 = ZOmegaSqrt2.conj (ZOmegaSqrt2.mk u k) from rfl,
        ZOmegaSqrt2.toComplex_conj]
  refine linftyOpNorm_sub_le_of_su2_col hε ?_ ?_ hU01 hU11 ?_ ?_
  · rw [e01, e10]
  · rw [e11, e00]
  · rw [e00]; exact h00
  · rw [e10]; exact h10

attribute [local instance] KMM.nonempty_kmmReduction

/-- **Ross-Selinger compile soundness (core).** When the grid pair `(u, t)` satisfies the
det-1 Diophantine constraint `|u|² + |t|² = √2^{2k}` (so `assembleUnitary u t k` is
Clifford+T-realizable) and approximates the target `U ∈ SU(2)`'s first column to within `ε`,
the KMM-synthesized Clifford+T word `kmmReduce (assembleUnitary u t k)` interprets to a unitary
within `2ε` of `U` in operator norm. Composes `kmmReduce_correct`
(`interp (kmmReduce M) = M`, via `isCliffordTRealizable_assembleUnitary`) with
`approx_assembleUnitary`. This is the soundness half of `compile`; the finder producing such a
`(u, t)` (Item H grid solver) + the ≥50-case pygridsynth cross-validation supply completeness. -/
theorem compile_correct_core (u t : ZOmega) (k : ℕ)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) {ε : ℝ} (hε : 0 ≤ ε)
    (hreal : ZOmega.normSq u + ZOmega.normSq t = (⟨0, 0, 0, 2 ^ k⟩ : ZOmega))
    (h00 : ‖ZOmegaSqrt2.toComplex (ZOmegaSqrt2.mk u k) - (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ ≤ ε)
    (h10 : ‖ZOmegaSqrt2.toComplex (ZOmegaSqrt2.mk t k) - (U : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ≤ ε) :
    ‖toComplexMat (CliffordTGate.interp (KMM.kmmReduce (KMM.assembleUnitary u t k)))
        - (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 2 * ε := by
  rw [KMM.kmmReduce_correct (KMM.assembleUnitary u t k)
        (KMM.isCliffordTRealizable_assembleUnitary u t k hreal)]
  exact approx_assembleUnitary u t k U hε h00 h10

/-- **The `ℤ[ω]` column numerator from grid-solver integer outputs.** The grid solver
(`twoDimGridSolution`) returns `(pm, pn, qm, qn)` — the real `ℤ[√2]` component `pm + pn√2` and
imaginary `qm + qn√2` of the column value `u = (pm+pn√2) + (qm+qn√2)·i`. This assembles them into
`ℤ[ω]` (`i = ω²`): `gridNumerator pm pn qm qn = (pm + pn·√2) + (qm + qn·√2)·ω²`. -/
noncomputable def gridNumerator (pm pn qm qn : ℤ) : ZOmega :=
  ((pm : ZOmega) + (pn : ZOmega) * ZOmega.sqrt2)
    + ((qm : ZOmega) + (qn : ZOmega) * ZOmega.sqrt2) * ZOmega.ω ^ 2

/-- **Complex value of the grid numerator**: `toComplex (gridNumerator pm pn qm qn) =
(pm + pn√2) + (qm + qn√2)·i`. (Ring hom + `toComplex √2 = √2`, `toComplex ω² = i`.) This is the
bridge from the grid solver's real-interval bounds to `approx_assembleUnitary`'s column hypotheses. -/
theorem toComplex_gridNumerator (pm pn qm qn : ℤ) :
    ZOmega.toComplex (gridNumerator pm pn qm qn)
      = ((pm : ℂ) + (pn : ℂ) * Real.sqrt 2) + ((qm : ℂ) + (qn : ℂ) * Real.sqrt 2) * Complex.I := by
  have hs : ZOmega.toComplex ZOmega.sqrt2 = (Real.sqrt 2 : ℂ) := by
    rw [← ZOmegaSqrt2.s2C_def]; exact ZOmegaSqrt2.s2C_eq
  have htw : ZOmega.toComplex ZOmega.ω = ZOmega.omegaC := by
    rw [show ZOmega.ω = (⟨0, 0, 1, 0⟩ : ZOmega) from rfl, ZOmega.toComplex_apply]; push_cast; ring
  have hi : ZOmega.toComplex (ZOmega.ω ^ 2) = Complex.I := by
    rw [map_pow, htw, ZOmega.omegaC_sq]
  simp only [gridNumerator, map_add, map_mul, map_intCast, hs, hi]

/-- **Cleared-scale complex value of the grid numerator**: `toComplex (mk (gridNumerator …) k) =
((pm+pn√2) + (qm+qn√2)·i) / √2^k` — the column value `u/√2^k` whose real and imaginary parts the
grid solver's interval bounds (`twoDimGridSolution_spec`) control to within `ε` of the target
column `U₀₀ = tr + ti·i`. Feeds `compile_correct_core`'s first-column hypothesis. -/
theorem toComplex_mk_gridNumerator (pm pn qm qn : ℤ) (k : ℕ) :
    ZOmegaSqrt2.toComplex (ZOmegaSqrt2.mk (gridNumerator pm pn qm qn) k)
      = (((pm : ℂ) + (pn : ℂ) * Real.sqrt 2) + ((qm : ℂ) + (qn : ℂ) * Real.sqrt 2) * Complex.I)
          / (Real.sqrt 2 : ℂ) ^ k := by
  rw [ZOmegaSqrt2.toComplex_mk, toComplex_gridNumerator, ZOmegaSqrt2.s2C_eq]

/-- **Column ε-approximation from the grid solver's real-interval bounds.** If the cleared real
and imaginary parts `(pm+pn√2)/√2^k` and `(qm+qn√2)/√2^k` are each within `ε` of the target
column entry `U₀₀`'s real/imaginary parts, then the `ℤ[ω]` column value is within `2ε` of `U₀₀`
in `ℂ` (`‖z‖ ≤ |z.re| + |z.im|`). This is the first-column hypothesis `h00` of
`compile_correct_core`, supplied by `twoDimGridSolution_spec`. -/
theorem gridNumerator_approx (pm pn qm qn : ℤ) (k : ℕ) (U₀₀ : ℂ) {ε : ℝ}
    (hre : |((pm : ℝ) + (pn : ℝ) * Real.sqrt 2) / Real.sqrt 2 ^ k - U₀₀.re| ≤ ε)
    (him : |((qm : ℝ) + (qn : ℝ) * Real.sqrt 2) / Real.sqrt 2 ^ k - U₀₀.im| ≤ ε) :
    ‖ZOmegaSqrt2.toComplex (ZOmegaSqrt2.mk (gridNumerator pm pn qm qn) k) - U₀₀‖ ≤ 2 * ε := by
  rw [toComplex_mk_gridNumerator,
      show (Real.sqrt 2 : ℂ) ^ k = ((Real.sqrt 2 ^ k : ℝ) : ℂ) from by push_cast; ring]
  set z : ℂ := ((pm : ℂ) + (pn : ℂ) * Real.sqrt 2) + ((qm : ℂ) + (qn : ℂ) * Real.sqrt 2) * Complex.I
    with hz
  have hzre : z.re = (pm : ℝ) + (pn : ℝ) * Real.sqrt 2 := by rw [hz]; simp
  have hzim : z.im = (qm : ℝ) + (qn : ℝ) * Real.sqrt 2 := by rw [hz]; simp
  have hdre : (z / ((Real.sqrt 2 ^ k : ℝ) : ℂ) - U₀₀).re
      = ((pm : ℝ) + (pn : ℝ) * Real.sqrt 2) / Real.sqrt 2 ^ k - U₀₀.re := by
    rw [Complex.sub_re, Complex.div_ofReal_re, hzre]
  have hdim : (z / ((Real.sqrt 2 ^ k : ℝ) : ℂ) - U₀₀).im
      = ((qm : ℝ) + (qn : ℝ) * Real.sqrt 2) / Real.sqrt 2 ^ k - U₀₀.im := by
    rw [Complex.sub_im, Complex.div_ofReal_im, hzim]
  calc ‖z / ((Real.sqrt 2 ^ k : ℝ) : ℂ) - U₀₀‖
      ≤ |(z / ((Real.sqrt 2 ^ k : ℝ) : ℂ) - U₀₀).re|
        + |(z / ((Real.sqrt 2 ^ k : ℝ) : ℂ) - U₀₀).im| := Complex.norm_le_abs_re_add_abs_im _
    _ ≤ ε + ε := by rw [hdre, hdim]; exact add_le_add hre him
    _ = 2 * ε := by ring

/-- **Ross-Selinger compile soundness from grid-solver bounds (assembled).** When two grid
numerators `u = gridNumerator pm pn qm qn`, `t = gridNumerator rm rn sm sn` satisfy the det-1
constraint and their cleared real/imaginary parts are each within `δ` of the target columns'
parts (`U₀₀` for `u`, `U₁₀` for `t`), the KMM-synthesized word interprets to within `4δ` of `U`.
Composes `gridNumerator_approx` (column-bounds → `2δ` per column) with `compile_correct_core`
(`2·(2δ) = 4δ`). The four `δ`-bounds are exactly what `twoDimGridSolution_spec` supplies (at the
chosen scale `k`); the det-1 constraint is the residual-`t` Diophantine. -/
theorem compile_correct_grid (pm pn qm qn rm rn sm sn : ℤ) (k : ℕ)
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) {δ : ℝ} (hδ : 0 ≤ δ)
    (hreal : ZOmega.normSq (gridNumerator pm pn qm qn) + ZOmega.normSq (gridNumerator rm rn sm sn)
      = (⟨0, 0, 0, 2 ^ k⟩ : ZOmega))
    (hu_re : |((pm : ℝ) + (pn : ℝ) * Real.sqrt 2) / Real.sqrt 2 ^ k
                - ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re| ≤ δ)
    (hu_im : |((qm : ℝ) + (qn : ℝ) * Real.sqrt 2) / Real.sqrt 2 ^ k
                - ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im| ≤ δ)
    (ht_re : |((rm : ℝ) + (rn : ℝ) * Real.sqrt 2) / Real.sqrt 2 ^ k
                - ((U : Matrix (Fin 2) (Fin 2) ℂ) 1 0).re| ≤ δ)
    (ht_im : |((sm : ℝ) + (sn : ℝ) * Real.sqrt 2) / Real.sqrt 2 ^ k
                - ((U : Matrix (Fin 2) (Fin 2) ℂ) 1 0).im| ≤ δ) :
    ‖toComplexMat (CliffordTGate.interp (KMM.kmmReduce
          (KMM.assembleUnitary (gridNumerator pm pn qm qn) (gridNumerator rm rn sm sn) k)))
        - (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 4 * δ := by
  have h00 := gridNumerator_approx pm pn qm qn k ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0) hu_re hu_im
  have h10 := gridNumerator_approx rm rn sm sn k ((U : Matrix (Fin 2) (Fin 2) ℂ) 1 0) ht_re ht_im
  have hmain := compile_correct_core (gridNumerator pm pn qm qn) (gridNumerator rm rn sm sn) k U
    (by linarith : (0 : ℝ) ≤ 2 * δ) hreal h00 h10
  linarith [hmain]

end SKEFTHawking.RossSelinger
