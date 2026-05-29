/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6z Wave 2b — SU(d) von-Neumann 1-parameter-subgroup theorem (construction)

The SU(d) generalization of `FKLW/OneParameterSubgroupSU2.lean`'s von-Neumann theorem: a closed subgroup
`H ≤ SU(d)` with `1` as an accumulation point contains a continuous nontrivial 1-parameter subgroup
`t ↦ exp(t • X)` (`X ∈ 𝔰𝔲(d)`, `X ≠ 0`) with image in `H`. Built on the existing `GenericSUd` matrix-log
local diffeo (`GenericSUdLocalDiffeoRestriction`, `GenericSUdMatrixLogTraceless`) rather than re-deriving
the SU(2) `su2Log`/`expAmbient` apparatus.

This is the engine that turns the Phase-6z seed's accumulation-point witness
(`CliffordCCZSU8.seedSU8_accPt_one`, Wave 2a) into the first continuous flow `exp(t•X₀) ∈ H_of_G`
(Wave 2). The flow is then spread to a spanning collection by Clifford conjugation (Wave 4) and fed to
`CartanFinalStep_SUd_v4` (Wave 5).

Increment 1 (this commit): **sequence extraction** — from `1 ∈ AccPt H` produce `seq : ℕ → SU(d)` in
`H \ {1}` with `seq n → 1`. The proof is pure topology (first-countable), ported verbatim from the SU(2)
`vonNeumann_extract_sequence`.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6z provenance

Phase 6z Wave 2b (SU(d) von-Neumann 1-parameter subgroup). 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.GenericSUdMatrixLogSkewHerm
import SKEFTHawking.FKLW.GenericSUdMatrixLogTraceless

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSUd

open Matrix

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- A point that is an accumulation point of `s` lies in the closure of `s \ {x}`. (Generic topology.) -/
theorem mem_closure_diff_singleton_of_accPt {X : Type*} [TopologicalSpace X] {s : Set X} {x : X}
    (hx : AccPt x (Filter.principal s)) : x ∈ closure (s \ {x}) := by
  rw [accPt_iff_frequently] at hx
  apply Filter.Frequently.mem_closure
  exact hx.mono (fun y hy => ⟨hy.2, fun heq => hy.1 heq⟩)

/-- **Von-Neumann sequence extraction (SU(d)).** From `1 ∈ AccPt H` extract a sequence in `H \ {1}`
converging to `1`. Pure-topology port of the SU(2) `vonNeumann_extract_sequence`. -/
theorem vonNeumann_extract_sequence {d : ℕ}
    [FrechetUrysohnSpace ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)]
    (H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))
    (hH : AccPt (1 : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))
      (Filter.principal (H : Set ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)))) :
    ∃ seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin d) ℂ),
      (∀ n, seq n ∈ H) ∧ (∀ n, seq n ≠ 1) ∧
      Filter.Tendsto seq Filter.atTop
        (nhds (1 : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))) := by
  have h_closure : (1 : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) ∈
      closure ((H : Set _) \ {1}) :=
    mem_closure_diff_singleton_of_accPt hH
  obtain ⟨seq, h_in, h_tendsto⟩ :=
    (mem_closure_iff_seq_limit (s := (H : Set _) \ {1})
      (a := (1 : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)))).mp h_closure
  refine ⟨seq, fun n => (h_in n).1, ?_, h_tendsto⟩
  intro n hne
  exact (h_in n).2 (by rw [Set.mem_singleton_iff]; exact hne)

/-- **Increment 2 — `matrixLog (seq n) → 0`.** The matrix logs of a sequence converging to `1` tend to
`0` (continuity of `matrixLog` at `1` + `matrixLog 1 = 0`). Port of the SU(2) `su2Log_seq_tendsto_zero`
onto the `GenericSUd` `matrixLog`. -/
theorem matrixLog_seq_tendsto_zero {d : ℕ}
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)}
    (h_seq : Filter.Tendsto seq Filter.atTop
      (nhds (1 : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)))) :
    Filter.Tendsto (fun n => matrixLog d ((seq n).val : Matrix (Fin d) (Fin d) ℂ))
      Filter.atTop (nhds (0 : Matrix (Fin d) (Fin d) ℂ)) := by
  have h_val : Filter.Tendsto (fun n => ((seq n).val : Matrix (Fin d) (Fin d) ℂ))
      Filter.atTop (nhds (1 : Matrix (Fin d) (Fin d) ℂ)) := by
    have h := (continuous_subtype_val (p :=
      fun M => M ∈ Matrix.specialUnitaryGroup (Fin d) ℂ)).continuousAt.tendsto.comp h_seq
    simpa using h
  have h_cont := matrixLog_continuousAt_one d
  have h := h_cont.tendsto.comp h_val
  rwa [matrixLog_one] at h

/-! ## Increment 3 — Bolzano–Weierstrass on the unit sphere

Port of `OneParameterSubgroupSU2.lean` §4.c–§4.d onto `GenericSUd.matrixLog`. The normalized matrix logs
`X n := ‖matrixLog (seq n)‖⁻¹ • matrixLog (seq n)` of a sequence `seq → 1` in `H \ {1}` live in the
compact closed unit ball of the finite-dimensional `Matrix (Fin d) (Fin d) ℂ`; Bolzano–Weierstrass
extracts a convergent subsequence whose limit has norm `1` (hence is nonzero). The limit's `𝔰𝔲(d)`
membership is added in a later increment (closedness of the traceless-skew-Hermitian set). -/

/-- `matrixLog d h = 0` with `h ∈ target` forces `h = 1` (injectivity of the exp–log diffeo at `0`:
`h = expAmbient d (matrixLog d h) = expAmbient d 0 = 1`). -/
theorem eq_one_of_matrixLog_eq_zero {d : ℕ}
    {h : Matrix (Fin d) (Fin d) ℂ}
    (hh : h ∈ (expAmbientPartialHomeo d).target)
    (h_log : matrixLog d h = 0) : h = 1 := by
  have h_rt := expAmbient_matrixLog d hh
  rw [h_log, expAmbient_zero] at h_rt
  exact h_rt.symm

/-- For `h ∈ target` with `h ≠ 1`, `matrixLog d h ≠ 0`. -/
theorem matrixLog_ne_zero_of_ne_one {d : ℕ}
    {h : Matrix (Fin d) (Fin d) ℂ}
    (hh : h ∈ (expAmbientPartialHomeo d).target)
    (h_ne : h ≠ 1) : matrixLog d h ≠ 0 :=
  fun h_log => h_ne (eq_one_of_matrixLog_eq_zero hh h_log)

/-- A subtype element distinct from `1` has matrix value distinct from `1`. -/
theorem subtype_val_ne_one_of_ne_one {d : ℕ}
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)} {n : ℕ}
    (h_ne : seq n ≠ 1) :
    ((seq n).val : Matrix (Fin d) (Fin d) ℂ) ≠ 1 :=
  fun h_eq => h_ne (Subtype.ext h_eq)

/-- From `seq → 1`, the matrix values `(seq n).val` eventually land in the exp–log diffeo target
(a nhd of `1`). -/
theorem eventually_val_mem_target {d : ℕ}
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)}
    (h_seq : Filter.Tendsto seq Filter.atTop
      (nhds (1 : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)))) :
    ∀ᶠ n in Filter.atTop,
      ((seq n).val : Matrix (Fin d) (Fin d) ℂ) ∈ (expAmbientPartialHomeo d).target := by
  have h_val : Filter.Tendsto (fun n => ((seq n).val : Matrix (Fin d) (Fin d) ℂ))
      Filter.atTop (nhds (1 : Matrix (Fin d) (Fin d) ℂ)) := by
    have h := (continuous_subtype_val (p :=
      fun M => M ∈ Matrix.specialUnitaryGroup (Fin d) ℂ)).continuousAt.tendsto.comp h_seq
    simpa using h
  exact h_val.eventually (expAmbientPartialHomeo_target_mem_nhds_one d)

/-- **Eventually `matrixLog (seq n) ≠ 0`**: from `seq → 1` and `seq n ≠ 1`. Mirror of the SU(2)
`eventually_su2Log_seq_ne_zero`. -/
theorem eventually_matrixLog_seq_ne_zero {d : ℕ}
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)}
    (h_ne : ∀ n, seq n ≠ 1)
    (h_seq : Filter.Tendsto seq Filter.atTop
      (nhds (1 : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)))) :
    ∀ᶠ n in Filter.atTop,
      matrixLog d ((seq n).val : Matrix (Fin d) (Fin d) ℂ) ≠ 0 := by
  filter_upwards [eventually_val_mem_target h_seq] with n hn
  exact matrixLog_ne_zero_of_ne_one hn (subtype_val_ne_one_of_ne_one (h_ne n))

/-- **Unit-sphere matrix sequence**: normalized matrix-log sequence (gives `0` when the log is `0`).
For `n` with nonzero log, `‖X n‖ = 1`. -/
noncomputable def vonNeumannUnitMatrixSeq {d : ℕ}
    (seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) (n : ℕ) :
    Matrix (Fin d) (Fin d) ℂ :=
  let Y := matrixLog d ((seq n).val : Matrix (Fin d) (Fin d) ℂ)
  if _h_ne : Y = 0 then 0 else (‖Y‖⁻¹ : ℂ) • Y

/-- The unit-sphere matrix sequence has norm `1` when the log is nonzero. -/
theorem vonNeumannUnitMatrixSeq_norm_eq_one {d : ℕ}
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)} {n : ℕ}
    (h_ne : matrixLog d ((seq n).val : Matrix (Fin d) (Fin d) ℂ) ≠ 0) :
    ‖vonNeumannUnitMatrixSeq seq n‖ = 1 := by
  unfold vonNeumannUnitMatrixSeq
  simp only [dif_neg h_ne]
  rw [norm_smul]
  have h_norm_ne : ‖matrixLog d ((seq n).val : Matrix (Fin d) (Fin d) ℂ)‖ ≠ 0 := by
    rw [norm_ne_zero_iff]; exact h_ne
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)]
  field_simp

/-- The closed unit ball in `Matrix (Fin d) (Fin d) ℂ` is compact (finite-dim ℝ-space ⟹ proper). -/
theorem isCompact_closedBall_one {d : ℕ} :
    IsCompact (Metric.closedBall (0 : Matrix (Fin d) (Fin d) ℂ) 1) :=
  ProperSpace.isCompact_closedBall (0 : Matrix (Fin d) (Fin d) ℂ) 1

/-- The unit-sphere matrix sequence is always in `closedBall 0 1` (norm `1` when the log is nonzero,
`0` otherwise). -/
theorem vonNeumannUnitMatrixSeq_mem_closedBall_one {d : ℕ}
    (seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) (n : ℕ) :
    vonNeumannUnitMatrixSeq seq n ∈
      Metric.closedBall (0 : Matrix (Fin d) (Fin d) ℂ) 1 := by
  by_cases h : matrixLog d ((seq n).val : Matrix (Fin d) (Fin d) ℂ) = 0
  · have h0 : vonNeumannUnitMatrixSeq seq n = 0 := by
      unfold vonNeumannUnitMatrixSeq; simp [h]
    simp [h0, Metric.mem_closedBall]
  · rw [Metric.mem_closedBall, dist_zero_right]
    exact le_of_eq (vonNeumannUnitMatrixSeq_norm_eq_one h)

/-- **BW EXTRACTION**: extract a subsequence of the unit-sphere matrix sequence converging to some
`X ∈ closedBall 0 1`. -/
theorem vonNeumann_BW_extract {d : ℕ}
    (seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) :
    ∃ X ∈ Metric.closedBall (0 : Matrix (Fin d) (Fin d) ℂ) 1,
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Filter.Tendsto (fun k => vonNeumannUnitMatrixSeq seq (φ k))
          Filter.atTop (nhds X) :=
  isCompact_closedBall_one.tendsto_subseq
    (vonNeumannUnitMatrixSeq_mem_closedBall_one seq)

/-- **Limit has norm `1`**: under the eventually-nonzero hypothesis, the BW-extracted limit `X` has
`‖X‖ = 1` (so `X ≠ 0`). -/
theorem vonNeumann_BW_limit_norm_eq_one {d : ℕ}
    (seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))
    (h_ev_ne : ∀ᶠ n in Filter.atTop,
      matrixLog d ((seq n).val : Matrix (Fin d) (Fin d) ℂ) ≠ 0)
    {X : Matrix (Fin d) (Fin d) ℂ} {φ : ℕ → ℕ}
    (hφ : StrictMono φ)
    (h_tendsto : Filter.Tendsto (fun k => vonNeumannUnitMatrixSeq seq (φ k))
      Filter.atTop (nhds X)) :
    ‖X‖ = 1 := by
  have h_norm_tendsto : Filter.Tendsto (fun k => ‖vonNeumannUnitMatrixSeq seq (φ k)‖)
      Filter.atTop (nhds ‖X‖) := (continuous_norm.tendsto X).comp h_tendsto
  have h_subseq_ne : ∀ᶠ k in Filter.atTop,
      matrixLog d ((seq (φ k)).val : Matrix (Fin d) (Fin d) ℂ) ≠ 0 :=
    hφ.tendsto_atTop.eventually h_ev_ne
  have h_subseq_norm_one : ∀ᶠ k in Filter.atTop,
      ‖vonNeumannUnitMatrixSeq seq (φ k)‖ = 1 := by
    filter_upwards [h_subseq_ne] with k hk
    exact vonNeumannUnitMatrixSeq_norm_eq_one hk
  have h_const_tendsto : Filter.Tendsto (fun k => ‖vonNeumannUnitMatrixSeq seq (φ k)‖)
      Filter.atTop (nhds 1) := by
    refine Filter.Tendsto.congr' ?_ tendsto_const_nhds
    filter_upwards [h_subseq_norm_one] with k hk
    rw [hk]
  exact tendsto_nhds_unique h_norm_tendsto h_const_tendsto

/-! ## Increment 3b — the BW limit lies in `𝔰𝔲(d)`

The traceless-skew-Hermitian submodule `𝔰𝔲(d)` is closed (finite-dim ℝ-submodule). Each
`vonNeumannUnitMatrixSeq seq n` is eventually in `𝔰𝔲(d)` (the matrix log lands in `𝔰𝔲(d)` near `1`
via `matrixLog_in_su_d_on_nhd_one`, and real-scalar normalization preserves the submodule). Hence the
BW limit `X` is traceless skew-Hermitian. Mirror of `OneParameterSubgroupSU2.lean` §4.i.5a + §9.12. -/

/-- **`𝔰𝔲(d)` is closed** in `Matrix (Fin d) (Fin d) ℂ` (finite-dim ℝ-submodule). d-generic lift of
the SU(2) `tracelessSkewHermitian_isClosed`. -/
theorem tracelessSkewHermitian_isClosed {d : ℕ} :
    IsClosed (SU2LieAlgebra.tracelessSkewHermitian (Fin d) :
      Set (Matrix (Fin d) (Fin d) ℂ)) :=
  (SU2LieAlgebra.tracelessSkewHermitian (Fin d)).closed_of_finiteDimensional

/-- **The unit-sphere matrix sequence is eventually in `𝔰𝔲(d)`.** For `seq → 1`, the matrix log of
`(seq n).val` is eventually traceless skew-Hermitian (`matrixLog_in_su_d_on_nhd_one`); the real-scalar
normalization stays in the submodule. Mirror of the SU(2) `*_eventually_uncond`. -/
theorem vonNeumannUnitMatrixSeq_mem_tracelessSkewHermitian_eventually {d : ℕ} [Nonempty (Fin d)]
    (hd_pos : 0 < d)
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)}
    (h_seq : Filter.Tendsto seq Filter.atTop
      (nhds (1 : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)))) :
    ∀ᶠ n in Filter.atTop,
      vonNeumannUnitMatrixSeq seq n ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin d) := by
  obtain ⟨V, hV, hV_discharge⟩ := matrixLog_in_su_d_on_nhd_one d hd_pos
  have h_val : Filter.Tendsto (fun n => ((seq n).val : Matrix (Fin d) (Fin d) ℂ))
      Filter.atTop (nhds (1 : Matrix (Fin d) (Fin d) ℂ)) := by
    have h := (continuous_subtype_val (p :=
      fun M => M ∈ Matrix.specialUnitaryGroup (Fin d) ℂ)).continuousAt.tendsto.comp h_seq
    simpa using h
  filter_upwards [eventually_val_mem_target h_seq, h_val.eventually hV] with n hn_target hn_V
  unfold vonNeumannUnitMatrixSeq
  by_cases h_zero : matrixLog d ((seq n).val : Matrix (Fin d) (Fin d) ℂ) = 0
  · simp only [h_zero, dif_pos]
    exact (SU2LieAlgebra.tracelessSkewHermitian (Fin d)).zero_mem
  · simp only [dif_neg h_zero]
    rw [show ((‖matrixLog d ((seq n).val : Matrix (Fin d) (Fin d) ℂ)‖⁻¹ : ℂ) •
            matrixLog d ((seq n).val : Matrix (Fin d) (Fin d) ℂ)) =
            ((‖matrixLog d ((seq n).val : Matrix (Fin d) (Fin d) ℂ)‖⁻¹ : ℝ) •
            matrixLog d ((seq n).val : Matrix (Fin d) (Fin d) ℂ)) by
      ext i j
      simp [Matrix.smul_apply, Complex.real_smul]]
    have h_Y_su : matrixLog d ((seq n).val : Matrix (Fin d) (Fin d) ℂ) ∈
        SU2LieAlgebra.tracelessSkewHermitian (Fin d) :=
      (SU2LieAlgebra.tracelessSkewHermitian_mem_iff _).mpr
        (hV_discharge _ hn_V (seq n).property hn_target)
    exact (SU2LieAlgebra.tracelessSkewHermitian (Fin d)).smul_mem _ h_Y_su

/-- **BW limit is in `𝔰𝔲(d)`**: the BW-extracted limit `X` is traceless skew-Hermitian (closedness of
`𝔰𝔲(d)` + the eventually-in-`𝔰𝔲(d)` subsequence). -/
theorem vonNeumann_BW_limit_mem_tracelessSkewHermitian {d : ℕ} [Nonempty (Fin d)]
    (hd_pos : 0 < d)
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)}
    (h_seq : Filter.Tendsto seq Filter.atTop
      (nhds (1 : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))))
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    {X : Matrix (Fin d) (Fin d) ℂ}
    (h_unit_tendsto : Filter.Tendsto (fun k => vonNeumannUnitMatrixSeq seq (φ k))
      Filter.atTop (nhds X)) :
    X ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin d) := by
  apply tracelessSkewHermitian_isClosed.mem_of_tendsto h_unit_tendsto
  exact hφ.tendsto_atTop.eventually
    (vonNeumannUnitMatrixSeq_mem_tracelessSkewHermitian_eventually hd_pos h_seq)

/-! ## Increment 4 — integer-rounding convergence and `exp(t•X) ∈ H_mat`

Port of `OneParameterSubgroupSU2.lean` §4.e–§4.i onto `GenericSUd.matrixLog` / `expAmbient d`. For each
`t : ℝ` and `m k := ⌊t / ‖matrixLog (seq (φ k))‖⌋ : ℤ`, the integer powers `(seq (φ k))^(m k)` converge
to `expAmbient d (t • X)`; since each lies in `H` and the image of `H` in matrices is closed,
`expAmbient d (t • X)` lies in that image. -/

/-- Entry-wise: real-scalar smul on a complex matrix equals coerced complex-scalar smul. d-generic lift
of the SU(2) `real_smul_matrix2C_eq_complex_smul`. -/
lemma real_smul_matrixdC_eq_complex_smul {d : ℕ}
    (r : ℝ) (M : Matrix (Fin d) (Fin d) ℂ) :
    (r : ℝ) • M = ((r : ℂ) • M) := by
  ext i j
  simp [Matrix.smul_apply, Complex.real_smul]

/-- **Explicit `ContinuousSMul ℝ` instance on `Matrix (Fin d) (Fin d) ℂ`** (linftyOp topology), via the
entry-wise identity `(r : ℝ) • M = (r : ℂ) • M` + continuity of `Complex.ofReal` and ℂ-smul. d-generic
lift of the SU(2) `continuousSMul_real_Matrix2C`. -/
noncomputable instance continuousSMul_real_MatrixdC {d : ℕ} :
    ContinuousSMul ℝ (Matrix (Fin d) (Fin d) ℂ) := by
  constructor
  have h_eq : (fun p : ℝ × Matrix (Fin d) (Fin d) ℂ => p.1 • p.2) =
              (fun p : ℝ × Matrix (Fin d) (Fin d) ℂ => (p.1 : ℂ) • p.2) := by
    funext p
    exact real_smul_matrixdC_eq_complex_smul p.1 p.2
  rw [h_eq]
  exact continuous_smul.comp
    ((Complex.continuous_ofReal.comp continuous_fst).prodMk continuous_snd)

/-- **Floor-times-scale converges**: for `r_k → 0` with `r_k > 0` eventually, `(⌊t / r_k⌋ : ℝ) · r_k → t`.
Generic reals (no matrices); port of the SU(2) lemma of the same name. -/
theorem floor_times_scale_tendsto
    {r : ℕ → ℝ} (h_pos : ∀ᶠ k in Filter.atTop, 0 < r k)
    (h_tendsto : Filter.Tendsto r Filter.atTop (nhds 0))
    (t : ℝ) :
    Filter.Tendsto (fun k => ((⌊t / r k⌋ : ℤ) : ℝ) * r k)
      Filter.atTop (nhds t) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have h_lt : ∀ᶠ k in Filter.atTop, |r k| < ε := by
    rw [Metric.tendsto_nhds] at h_tendsto
    have := h_tendsto ε hε
    filter_upwards [this] with k hk
    rwa [Real.dist_eq, sub_zero] at hk
  filter_upwards [h_lt, h_pos] with k hk_lt hk_pos
  rw [Real.dist_eq]
  have h_floor_bound : |((⌊t / r k⌋ : ℤ) : ℝ) - t / r k| < 1 := by
    have h1 := Int.floor_le (t / r k)
    have h2 := Int.lt_floor_add_one (t / r k)
    rw [abs_lt]
    constructor
    · linarith
    · linarith
  have h_rk_ne : r k ≠ 0 := ne_of_gt hk_pos
  calc |((⌊t / r k⌋ : ℤ) : ℝ) * r k - t|
      = |(((⌊t / r k⌋ : ℤ) : ℝ) - t / r k) * r k| := by
        congr 1
        field_simp
    _ = |((⌊t / r k⌋ : ℤ) : ℝ) - t / r k| * |r k| := abs_mul _ _
    _ ≤ 1 * |r k| := by
        apply mul_le_mul_of_nonneg_right _ (abs_nonneg _)
        exact le_of_lt h_floor_bound
    _ = |r k| := one_mul _
    _ < ε := hk_lt

/-- **Approximation lemma**: for the BW subsequence, `(m_k : ℝ) · ‖Y_k‖ → t` where
`m_k := ⌊t / ‖Y_k‖⌋`. -/
theorem vonNeumann_floor_scale_tendsto {d : ℕ}
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)}
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (h_ev_ne : ∀ᶠ n in Filter.atTop,
      matrixLog d ((seq n).val : Matrix (Fin d) (Fin d) ℂ) ≠ 0)
    (h_log_tendsto : Filter.Tendsto
      (fun n => matrixLog d ((seq n).val : Matrix (Fin d) (Fin d) ℂ))
      Filter.atTop (nhds (0 : Matrix (Fin d) (Fin d) ℂ)))
    (t : ℝ) :
    Filter.Tendsto
      (fun k => ((⌊t / ‖matrixLog d ((seq (φ k)).val : Matrix (Fin d) (Fin d) ℂ)‖⌋ : ℤ) : ℝ) *
                ‖matrixLog d ((seq (φ k)).val : Matrix (Fin d) (Fin d) ℂ)‖)
      Filter.atTop (nhds t) := by
  apply floor_times_scale_tendsto
  · have h_subseq_ne := hφ.tendsto_atTop.eventually h_ev_ne
    filter_upwards [h_subseq_ne] with k hk
    exact norm_pos_iff.mpr hk
  · have h_subseq_tendsto := h_log_tendsto.comp hφ.tendsto_atTop
    have := (continuous_norm.tendsto (0 : Matrix (Fin d) (Fin d) ℂ)).comp h_subseq_tendsto
    simp [norm_zero] at this
    exact this

/-- **Scalar-vector convergence (ℝ-smul form)**: `(m_k · ‖Y_{φk}‖) • X_{φk} → t • X`. -/
theorem vonNeumann_scaled_unit_tendsto_real {d : ℕ}
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)}
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (h_ev_ne : ∀ᶠ n in Filter.atTop,
      matrixLog d ((seq n).val : Matrix (Fin d) (Fin d) ℂ) ≠ 0)
    (h_log_tendsto : Filter.Tendsto
      (fun n => matrixLog d ((seq n).val : Matrix (Fin d) (Fin d) ℂ))
      Filter.atTop (nhds (0 : Matrix (Fin d) (Fin d) ℂ)))
    {X : Matrix (Fin d) (Fin d) ℂ}
    (h_unit_tendsto : Filter.Tendsto (fun k => vonNeumannUnitMatrixSeq seq (φ k))
      Filter.atTop (nhds X))
    (t : ℝ) :
    Filter.Tendsto
      (fun k =>
        (((⌊t / ‖matrixLog d ((seq (φ k)).val : Matrix (Fin d) (Fin d) ℂ)‖⌋ : ℤ) : ℝ) *
          ‖matrixLog d ((seq (φ k)).val : Matrix (Fin d) (Fin d) ℂ)‖) •
          vonNeumannUnitMatrixSeq seq (φ k))
      Filter.atTop (nhds (t • X)) :=
  (vonNeumann_floor_scale_tendsto hφ h_ev_ne h_log_tendsto t).smul h_unit_tendsto

/-- **Algebraic identity (real-scalar form)**: for `Y ≠ 0` and `c : ℝ`,
`(c * ‖Y‖) • ((‖Y‖⁻¹ : ℂ) • Y) = c • Y`. -/
lemma scaled_unit_eq_real_smul {d : ℕ}
    {Y : Matrix (Fin d) (Fin d) ℂ} (hY : Y ≠ 0) (c : ℝ) :
    (c * ‖Y‖) • ((‖Y‖⁻¹ : ℂ) • Y) = c • Y := by
  have h_norm_ne : (‖Y‖ : ℝ) ≠ 0 := by
    rw [Ne, norm_eq_zero]; exact hY
  have h_inner : ((‖Y‖⁻¹ : ℂ) • Y) = ((‖Y‖⁻¹ : ℝ) • Y) := by
    ext i j
    simp [Matrix.smul_apply, Complex.real_smul]
  rw [h_inner, smul_smul]
  congr 1
  field_simp

/-- **Real-scalar smul convergence**: `(m_k_real : ℝ) • Y_{φk} → t • X`. -/
theorem vonNeumann_intReal_smul_tendsto {d : ℕ}
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)}
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (h_ev_ne : ∀ᶠ n in Filter.atTop,
      matrixLog d ((seq n).val : Matrix (Fin d) (Fin d) ℂ) ≠ 0)
    (h_log_tendsto : Filter.Tendsto
      (fun n => matrixLog d ((seq n).val : Matrix (Fin d) (Fin d) ℂ))
      Filter.atTop (nhds (0 : Matrix (Fin d) (Fin d) ℂ)))
    {X : Matrix (Fin d) (Fin d) ℂ}
    (h_unit_tendsto : Filter.Tendsto (fun k => vonNeumannUnitMatrixSeq seq (φ k))
      Filter.atTop (nhds X))
    (t : ℝ) :
    Filter.Tendsto
      (fun k =>
        ((⌊t / ‖matrixLog d ((seq (φ k)).val : Matrix (Fin d) (Fin d) ℂ)‖⌋ : ℤ) : ℝ) •
          matrixLog d ((seq (φ k)).val : Matrix (Fin d) (Fin d) ℂ))
      Filter.atTop (nhds (t • X)) := by
  have h_f := vonNeumann_scaled_unit_tendsto_real hφ h_ev_ne h_log_tendsto h_unit_tendsto t
  have h_ev_ne_sub : ∀ᶠ k in Filter.atTop,
      matrixLog d ((seq (φ k)).val : Matrix (Fin d) (Fin d) ℂ) ≠ 0 :=
    hφ.tendsto_atTop.eventually h_ev_ne
  refine Filter.Tendsto.congr' ?_ h_f
  filter_upwards [h_ev_ne_sub] with k hk
  unfold vonNeumannUnitMatrixSeq
  simp only [dif_neg hk]
  exact scaled_unit_eq_real_smul hk _

/-- **ℤ-smul convergence**: cast from the real-scalar form via `Int.cast_smul_eq_zsmul`. -/
theorem vonNeumann_zsmul_seq_tendsto {d : ℕ}
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)}
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (h_ev_ne : ∀ᶠ n in Filter.atTop,
      matrixLog d ((seq n).val : Matrix (Fin d) (Fin d) ℂ) ≠ 0)
    (h_log_tendsto : Filter.Tendsto
      (fun n => matrixLog d ((seq n).val : Matrix (Fin d) (Fin d) ℂ))
      Filter.atTop (nhds (0 : Matrix (Fin d) (Fin d) ℂ)))
    {X : Matrix (Fin d) (Fin d) ℂ}
    (h_unit_tendsto : Filter.Tendsto (fun k => vonNeumannUnitMatrixSeq seq (φ k))
      Filter.atTop (nhds X))
    (t : ℝ) :
    Filter.Tendsto
      (fun k =>
        (⌊t / ‖matrixLog d ((seq (φ k)).val : Matrix (Fin d) (Fin d) ℂ)‖⌋ : ℤ) •
          matrixLog d ((seq (φ k)).val : Matrix (Fin d) (Fin d) ℂ))
      Filter.atTop (nhds (t • X)) := by
  have h_real := vonNeumann_intReal_smul_tendsto hφ h_ev_ne h_log_tendsto h_unit_tendsto t
  refine Filter.Tendsto.congr ?_ h_real
  intro k
  exact Int.cast_smul_eq_zsmul ℝ _ _

/-- **`expAmbient` convergence**: apply `expAmbient d` continuity to the ℤ-smul tendsto. -/
theorem vonNeumann_exp_zsmul_seq_tendsto {d : ℕ}
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)}
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (h_ev_ne : ∀ᶠ n in Filter.atTop,
      matrixLog d ((seq n).val : Matrix (Fin d) (Fin d) ℂ) ≠ 0)
    (h_log_tendsto : Filter.Tendsto
      (fun n => matrixLog d ((seq n).val : Matrix (Fin d) (Fin d) ℂ))
      Filter.atTop (nhds (0 : Matrix (Fin d) (Fin d) ℂ)))
    {X : Matrix (Fin d) (Fin d) ℂ}
    (h_unit_tendsto : Filter.Tendsto (fun k => vonNeumannUnitMatrixSeq seq (φ k))
      Filter.atTop (nhds X))
    (t : ℝ) :
    Filter.Tendsto
      (fun k =>
        expAmbient d
          ((⌊t / ‖matrixLog d ((seq (φ k)).val : Matrix (Fin d) (Fin d) ℂ)‖⌋ : ℤ) •
            matrixLog d ((seq (φ k)).val : Matrix (Fin d) (Fin d) ℂ)))
      Filter.atTop (nhds (expAmbient d (t • X))) := by
  have h_zsmul := vonNeumann_zsmul_seq_tendsto hφ h_ev_ne h_log_tendsto h_unit_tendsto t
  have h_cont : Filter.Tendsto (fun M : Matrix (Fin d) (Fin d) ℂ => expAmbient d M)
      (nhds (t • X)) (nhds (expAmbient d (t • X))) := by
    have : Continuous (expAmbient d : Matrix (Fin d) (Fin d) ℂ → Matrix (Fin d) (Fin d) ℂ) := by
      unfold expAmbient
      exact NormedSpace.exp_continuous
    exact this.tendsto _
  exact h_cont.comp h_zsmul

/-- **Integer-power form**: rewrite via `Matrix.exp_zsmul` as `(expAmbient Y_{φk}) ^ m_k`. -/
theorem vonNeumann_exp_pow_seq_tendsto {d : ℕ}
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)}
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (h_ev_ne : ∀ᶠ n in Filter.atTop,
      matrixLog d ((seq n).val : Matrix (Fin d) (Fin d) ℂ) ≠ 0)
    (h_log_tendsto : Filter.Tendsto
      (fun n => matrixLog d ((seq n).val : Matrix (Fin d) (Fin d) ℂ))
      Filter.atTop (nhds (0 : Matrix (Fin d) (Fin d) ℂ)))
    {X : Matrix (Fin d) (Fin d) ℂ}
    (h_unit_tendsto : Filter.Tendsto (fun k => vonNeumannUnitMatrixSeq seq (φ k))
      Filter.atTop (nhds X))
    (t : ℝ) :
    Filter.Tendsto
      (fun k =>
        expAmbient d (matrixLog d ((seq (φ k)).val : Matrix (Fin d) (Fin d) ℂ)) ^
          (⌊t / ‖matrixLog d ((seq (φ k)).val : Matrix (Fin d) (Fin d) ℂ)‖⌋ : ℤ))
      Filter.atTop (nhds (expAmbient d (t • X))) := by
  have h_exp := vonNeumann_exp_zsmul_seq_tendsto hφ h_ev_ne h_log_tendsto h_unit_tendsto t
  refine Filter.Tendsto.congr ?_ h_exp
  intro k
  unfold expAmbient
  exact Matrix.exp_zsmul _ _

/-- **Matrix-level rewrite (eventually)**: under `seq → 1`, eventually
`expAmbient d (matrixLog d (seq n).val) = (seq n).val`. -/
theorem expAmbient_matrixLog_seq_eventually {d : ℕ}
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)}
    (h_seq : Filter.Tendsto seq Filter.atTop
      (nhds (1 : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)))) :
    ∀ᶠ n in Filter.atTop,
      expAmbient d (matrixLog d ((seq n).val : Matrix (Fin d) (Fin d) ℂ))
        = ((seq n).val : Matrix (Fin d) (Fin d) ℂ) := by
  filter_upwards [eventually_val_mem_target h_seq] with n hn
  exact expAmbient_matrixLog d hn

/-- **SU(d)-matrix-level convergence**: `(seq (φ k)).val ^ m_k → expAmbient d (t • X)`. -/
theorem vonNeumann_suMat_pow_seq_tendsto {d : ℕ}
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)}
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (h_seq : Filter.Tendsto seq Filter.atTop
      (nhds (1 : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))))
    (h_ev_ne : ∀ᶠ n in Filter.atTop,
      matrixLog d ((seq n).val : Matrix (Fin d) (Fin d) ℂ) ≠ 0)
    (h_log_tendsto : Filter.Tendsto
      (fun n => matrixLog d ((seq n).val : Matrix (Fin d) (Fin d) ℂ))
      Filter.atTop (nhds (0 : Matrix (Fin d) (Fin d) ℂ)))
    {X : Matrix (Fin d) (Fin d) ℂ}
    (h_unit_tendsto : Filter.Tendsto (fun k => vonNeumannUnitMatrixSeq seq (φ k))
      Filter.atTop (nhds X))
    (t : ℝ) :
    Filter.Tendsto
      (fun k =>
        ((seq (φ k)).val : Matrix (Fin d) (Fin d) ℂ) ^
          (⌊t / ‖matrixLog d ((seq (φ k)).val : Matrix (Fin d) (Fin d) ℂ)‖⌋ : ℤ))
      Filter.atTop (nhds (expAmbient d (t • X))) := by
  have h_g4 := vonNeumann_exp_pow_seq_tendsto hφ h_ev_ne h_log_tendsto h_unit_tendsto t
  have h_ev_subseq := hφ.tendsto_atTop.eventually (expAmbient_matrixLog_seq_eventually h_seq)
  refine Filter.Tendsto.congr' ?_ h_g4
  filter_upwards [h_ev_subseq] with k hk
  rw [hk]

/-- **SU(d)-subtype zpow lifts to matrix-zpow**: `((g ^ m).val : Matrix _ _ ℂ) = (g.val) ^ m`.
d-generic lift of the SU(2) `specialUnitaryGroup_coe_zpow`. -/
theorem specialUnitaryGroup_coe_zpow {d : ℕ}
    (g : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) (m : ℤ) :
    ((g ^ m).val : Matrix (Fin d) (Fin d) ℂ) =
      (g.val : Matrix (Fin d) (Fin d) ℂ) ^ m := by
  cases m with
  | ofNat k =>
    show ((g ^ (k : ℤ)).val : Matrix (Fin d) (Fin d) ℂ) = g.val ^ (k : ℤ)
    rw [zpow_natCast, zpow_natCast]
    exact SubmonoidClass.coe_pow _ _
  | negSucc k =>
    show ((g ^ (Int.negSucc k)).val : Matrix (Fin d) (Fin d) ℂ) =
         g.val ^ (Int.negSucc k)
    rw [zpow_negSucc, zpow_negSucc]
    have h_inv_eq_star :
        ((g ^ (k+1))⁻¹).val = star ((g ^ (k+1)).val) := rfl
    rw [h_inv_eq_star]
    rw [SubmonoidClass.coe_pow]
    have h_pow_unitary : (g ^ (k+1)).val ∈ Matrix.unitaryGroup (Fin d) ℂ :=
      (Matrix.mem_specialUnitaryGroup_iff.mp (g ^ (k+1)).property).1
    have h_pow_val_eq : (g ^ (k+1)).val = g.val ^ (k+1) :=
      SubmonoidClass.coe_pow _ _
    have h_mul_star : ((g.val ^ (k+1)) * star (g.val ^ (k+1)) :
        Matrix (Fin d) (Fin d) ℂ) = 1 := by
      rw [← h_pow_val_eq]
      exact Matrix.mem_unitaryGroup_iff.mp h_pow_unitary
    exact (Matrix.inv_eq_right_inv h_mul_star).symm

/-- **`Matrix.specialUnitaryGroup (Fin d) ℂ` is closed** in `Matrix (Fin d) (Fin d) ℂ`. -/
theorem specialUnitaryGroup_isClosed {d : ℕ} :
    IsClosed ((Matrix.specialUnitaryGroup (Fin d) ℂ :
        Set (Matrix (Fin d) (Fin d) ℂ))) := by
  rw [show ((Matrix.specialUnitaryGroup (Fin d) ℂ :
        Set (Matrix (Fin d) (Fin d) ℂ))) =
      (Matrix.unitaryGroup (Fin d) ℂ : Set (Matrix (Fin d) (Fin d) ℂ)) ∩
        {M | M.det = 1} from ?_]
  · exact IsClosed.inter isClosed_unitary
      (isClosed_eq (Continuous.matrix_det continuous_id) continuous_const)
  · ext M
    simp [Matrix.mem_specialUnitaryGroup_iff]

/-- **H_mat (image of `H` in `Matrix _ _ ℂ`) is closed** when `H` is closed in the SU(d) subtype. -/
theorem H_mat_isClosed {d : ℕ}
    (H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))
    (hH_closed : IsClosed (H : Set ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))) :
    IsClosed ((fun h : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ) => h.val) ''
              (H : Set ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))) :=
  (specialUnitaryGroup_isClosed.isClosedEmbedding_subtypeVal.isClosed_iff_image_isClosed).mp hH_closed

/-- **Matrix-pow seq is in H_mat** (for all `k`). -/
theorem vonNeumann_mat_pow_mem_H_mat {d : ℕ}
    {H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)}
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)}
    (h_mem : ∀ n, seq n ∈ H)
    (φ : ℕ → ℕ) (t : ℝ) (k : ℕ) :
    ((seq (φ k)).val : Matrix (Fin d) (Fin d) ℂ) ^
        (⌊t / ‖matrixLog d ((seq (φ k)).val : Matrix (Fin d) (Fin d) ℂ)‖⌋ : ℤ) ∈
      (fun h : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ) => h.val) ''
        (H : Set ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) := by
  set m : ℤ := ⌊t / ‖matrixLog d ((seq (φ k)).val : Matrix (Fin d) (Fin d) ℂ)‖⌋
  refine ⟨(seq (φ k)) ^ m, ?_, ?_⟩
  · exact H.zpow_mem (h_mem (φ k)) m
  · exact specialUnitaryGroup_coe_zpow _ _

/-- **`expAmbient d (t • X)` is in H_mat**: the limit of the matrix-pow sequence is in the image of `H`
in `Matrix _ _ ℂ`. -/
theorem vonNeumann_expAmbient_mem_H_mat {d : ℕ}
    {H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)}
    (hH_closed : IsClosed (H : Set ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)))
    {seq : ℕ → ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)}
    (h_mem : ∀ n, seq n ∈ H)
    {φ : ℕ → ℕ} (hφ : StrictMono φ)
    (h_seq : Filter.Tendsto seq Filter.atTop
      (nhds (1 : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))))
    (h_ev_ne : ∀ᶠ n in Filter.atTop,
      matrixLog d ((seq n).val : Matrix (Fin d) (Fin d) ℂ) ≠ 0)
    (h_log_tendsto : Filter.Tendsto
      (fun n => matrixLog d ((seq n).val : Matrix (Fin d) (Fin d) ℂ))
      Filter.atTop (nhds (0 : Matrix (Fin d) (Fin d) ℂ)))
    {X : Matrix (Fin d) (Fin d) ℂ}
    (h_unit_tendsto : Filter.Tendsto (fun k => vonNeumannUnitMatrixSeq seq (φ k))
      Filter.atTop (nhds X))
    (t : ℝ) :
    expAmbient d (t • X) ∈
      (fun h : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ) => h.val) ''
        (H : Set ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)) := by
  have h_pow_tendsto := vonNeumann_suMat_pow_seq_tendsto
    hφ h_seq h_ev_ne h_log_tendsto h_unit_tendsto t
  apply (H_mat_isClosed H hH_closed).mem_of_tendsto h_pow_tendsto
  filter_upwards with k
  exact vonNeumann_mat_pow_mem_H_mat h_mem φ t k

/-! ## Increment 5 — the von-Neumann headline (SU(d))

The capstone: a closed subgroup `H ≤ SU(d)` with `1` as an accumulation point contains a continuous
nontrivial 1-parameter subgroup. In explicit-`X` form — `∃ X ∈ 𝔰𝔲(d), X ≠ 0 ∧ ∀ t, ∃ M ∈ H,
M.val = exp((t:ℂ)•X)` — which is exactly the shape consumed by `ClosureDenseWitness.hX_flow`. Mirror of
`OneParameterSubgroupSU2.vonNeumann_assemble_explicit_X_unconditional`.

The `[FrechetUrysohnSpace ↥(SU(d))]` instance binder is carried (sequential characterization of closure,
inc 1); it resolves automatically at concrete `d` under the linftyOp metric instances. -/

/-- **Von-Neumann 1-parameter-subgroup theorem (SU(d), explicit-X form).**

A closed subgroup `H ≤ SU(d)` with `1 ∈ AccPt H` contains a continuous nontrivial 1-parameter subgroup:
there is a nonzero traceless skew-Hermitian `X ∈ 𝔰𝔲(d)` whose entire flow line `t ↦ exp((t:ℂ)•X)` lands
in `H`. This is the engine turning the Phase-6z seed's accumulation-point witness
(`CliffordCCZSU8.seedSU8_accPt_one`) into the first continuous flow `exp(t•X₀) ∈ H_of_G` (Wave 2). -/
theorem vonNeumann_assemble_explicit_X_SUd {d : ℕ} [Nonempty (Fin d)]
    [FrechetUrysohnSpace ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)]
    (hd_pos : 0 < d)
    (H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))
    (hH_closed : IsClosed (H : Set ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)))
    (hH_accPt : AccPt (1 : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ))
      (Filter.principal (H : Set ↥(Matrix.specialUnitaryGroup (Fin d) ℂ)))) :
    ∃ X : Matrix (Fin d) (Fin d) ℂ,
      X ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin d) ∧ X ≠ 0 ∧
      ∀ t : ℝ, ∃ M : ↥(Matrix.specialUnitaryGroup (Fin d) ℂ),
        M ∈ H ∧ (M.val : Matrix (Fin d) (Fin d) ℂ) = expAmbient d (((t : ℝ) : ℂ) • X) := by
  obtain ⟨seq, h_mem, h_ne, h_seq⟩ := vonNeumann_extract_sequence H hH_accPt
  have h_ev_ne := eventually_matrixLog_seq_ne_zero h_ne h_seq
  have h_log_tendsto := matrixLog_seq_tendsto_zero h_seq
  obtain ⟨X, _hX_ball, φ, hφ, h_unit_tendsto⟩ := vonNeumann_BW_extract seq
  have h_norm_one : ‖X‖ = 1 :=
    vonNeumann_BW_limit_norm_eq_one seq h_ev_ne hφ h_unit_tendsto
  have hX_ne : X ≠ 0 := fun h => by rw [h, norm_zero] at h_norm_one; norm_num at h_norm_one
  have hX_su : X ∈ SU2LieAlgebra.tracelessSkewHermitian (Fin d) :=
    vonNeumann_BW_limit_mem_tracelessSkewHermitian hd_pos h_seq hφ h_unit_tendsto
  refine ⟨X, hX_su, hX_ne, ?_⟩
  intro t
  obtain ⟨M, hM_mem, hM_val⟩ :=
    vonNeumann_expAmbient_mem_H_mat hH_closed h_mem hφ h_seq h_ev_ne h_log_tendsto h_unit_tendsto t
  refine ⟨M, hM_mem, ?_⟩
  rw [← real_smul_matrixdC_eq_complex_smul t X]
  exact hM_val

end SKEFTHawking.FKLW.GenericSUd
