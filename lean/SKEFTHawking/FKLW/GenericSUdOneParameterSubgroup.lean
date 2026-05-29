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

/-! ## Remaining increments (the von-Neumann analytic core — next builds)

Built on the existing `GenericSUd` matrix-log local diffeo
(`GenericSUdLocalDiffeoRestriction.matrixLog_expAmbient_on_su_d` /
`expAmbient_matrixLog_on_SUd`, `GenericSUdMatrixLogTraceless.matrixLog_in_su_d_on_nhd_one`):

  * **inc 3b — BW limit in 𝔰𝔲(d):** the limit `X` from `vonNeumann_BW_extract` is traceless
    skew-Hermitian (each `vonNeumannUnitMatrixSeq seq n` is eventually in `𝔰𝔲(d)` via
    `matrixLog_isSkewHermitian_on_nhd_one` + the traceless analogue scaled by a real scalar; `𝔰𝔲(d)`
    is closed, so the limit is in it). Mirror SU(2) §9.12.
  * **inc 4 — integer-rounding convergence:** for each `t`, with `m k := ⌊t / ‖matrixLog (seq (φ k))‖⌋`,
    `(seq (φ k)) ^ (m k) = exp (m k • matrixLog (seq (φ k))) → exp (t • X)`; since each is in `H`
    (subgroup) and `H` is closed, `exp (t • X) ∈ H`. (Mirror SU(2) §4.e–§4.f.)
  * **inc 5 — main theorem:** assemble `1 ∈ AccPt H → ∃ X ∈ 𝔰𝔲(d), X ≠ 0 ∧ ∀ t, exp (t • X) ∈ H`.

Each is a port of the corresponding SU(2) lemma in `OneParameterSubgroupSU2.lean` with `su2Log` replaced
by the `GenericSUd` `matrixLog`. This is the genuine analytic core (multi-session). -/

end SKEFTHawking.FKLW.GenericSUd
