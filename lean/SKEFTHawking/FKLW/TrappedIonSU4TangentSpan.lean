/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A1′.2 (D) witness — the 15 tensor-Pauli tangents ℝ-span 𝔰𝔲(4)

The `hX_spans` field of the trapped-ion SU(4) `ClosureDenseWitness`: every traceless
skew-Hermitian `Y ∈ Matrix (Fin 4) (Fin 4) ℂ` is a real-linear combination of the 15 tensor-Pauli
tangents `X_{ab} = (i/2)·(σ_a ⊗ σ_b)`.

## Proof architecture (Hilbert-Schmidt / Pauli completeness)

  * `kronK p := kronSU4 (pauli4 p.1) (pauli4 p.2)` — the 16 Hermitian tensor-Paulis (`p : Fin 4²`).
  * **HS-orthogonality** `tr(kronK p · kronK q) = 4·𝟙[p = q]` (via `kronSU4_mul` + `kronSU4_trace`
    + the 2×2 Pauli product trace table `pauli4_mul_trace`).
  * **ℂ-linear independence** of the 16 `kronK` (orthogonality ⇒ independence).
  * Since `finrank ℂ (M₄) = 16 = #(Fin 4²)`, the `kronK` form a **ℂ-basis** of `M₄`; every `Y`
    decomposes as `Y = ∑ d_p · kronK p` with the HS coordinate `d_p = ¼·tr(kronK p · Y)`.
  * **Traceless** ⇒ `d_{(0,0)} = 0` (`kronK (0,0) = 1`, `tr(1·Y) = tr Y = 0`).
  * **Skew-Hermitian** ⇒ each `d_p` is purely imaginary (`tr(Hermitian · skew-Hermitian) ∈ iℝ`),
    so `d_p = (c_p : ℝ)·(i/2)` for a real `c_p`, i.e. `d_p · kronK p = c_p · X_{ab}`.
  * Re-index the `Fin 4²` sum over the 15-enumeration `idx15` (dropping the zero `(0,0)` term).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A1′ provenance

Phase 6y Roadmap §"Track T-A1′ detail" sub-wave T-A1′.2 PROPER — (D) witness `hX_spans`.
DR blueprint §2 (HS-projection lemma chain L_sp-1/2/3). 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.TrappedIonSU4Tangents
import SKEFTHawking.FKLW.TrappedIonSU4KronHom

set_option autoImplicit false

namespace SKEFTHawking.FKLW.TrappedIonSU4

open Matrix Complex

/-! ## 1. The 2×2 Pauli product-trace table -/

/-- `tr(σ_a · σ_b) = 2·𝟙[a = b]`. -/
theorem pauli4_mul_trace (a b : Fin 4) :
    (pauli4 a * pauli4 b).trace = if a = b then 2 else 0 := by
  fin_cases a <;> fin_cases b <;>
    simp [pauli4, SKEFTHawking.σ_x, SKEFTHawking.σ_y, SKEFTHawking.σ_z, Matrix.trace,
      Matrix.diag_apply, Fin.sum_univ_two] <;>
    norm_num [Complex.ext_iff]

/-! ## 2. The 16 tensor-Pauli matrices and their Hilbert-Schmidt orthogonality -/

/-- The 16 Hermitian tensor-Pauli matrices `kronK p = σ_{p.1} ⊗ σ_{p.2}`, `p : Fin 4 × Fin 4`. -/
noncomputable def kronK (p : Fin 4 × Fin 4) : Matrix (Fin 4) (Fin 4) ℂ :=
  kronSU4 (pauli4 p.1) (pauli4 p.2)

/-- **Hilbert-Schmidt orthogonality**: `tr(kronK p · kronK q) = 4·𝟙[p = q]`. -/
theorem kronK_mul_trace (p q : Fin 4 × Fin 4) :
    (kronK p * kronK q).trace = if p = q then 4 else 0 := by
  unfold kronK
  rw [← kronSU4_mul, kronSU4_trace, pauli4_mul_trace, pauli4_mul_trace]
  by_cases hpq : p = q
  · subst hpq; norm_num
  · rw [if_neg hpq]
    have hcomp : ¬(p.1 = q.1 ∧ p.2 = q.2) := fun h => hpq (Prod.ext_iff.mpr h)
    rcases not_and_or.mp hcomp with h1 | h2
    · rw [if_neg h1, zero_mul]
    · rw [if_neg h2, mul_zero]

/-! ## 3. ℂ-linear independence of the 16 tensor-Paulis -/

/-- The 16 tensor-Paulis are ℂ-linearly independent (Hilbert-Schmidt orthogonality). -/
theorem kronK_linearIndependent : LinearIndependent ℂ kronK := by
  rw [Fintype.linearIndependent_iff]
  intro g hg q
  -- Apply `tr(· * kronK q)` to `∑ p, g p • kronK p = 0`.
  have h_tr : (∑ p, g p • kronK p) * kronK q = 0 := by rw [hg]; simp
  have h_tr2 : ((∑ p, g p • kronK p) * kronK q).trace = 0 := by rw [h_tr]; simp
  rw [Finset.sum_mul] at h_tr2
  simp only [Matrix.trace_sum, smul_mul_assoc, Matrix.trace_smul, kronK_mul_trace] at h_tr2
  rw [Finset.sum_eq_single q] at h_tr2
  · simpa using h_tr2
  · intro p _ hpq; rw [if_neg hpq]; simp
  · intro hq; exact absurd (Finset.mem_univ q) hq

/-! ## 4. The tensor-Pauli ℂ-basis of `M₄` and the HS coordinate formula -/

/-- The 16 tensor-Paulis form a ℂ-basis of `Matrix (Fin 4) (Fin 4) ℂ`. -/
noncomputable def kronKBasis : Module.Basis (Fin 4 × Fin 4) ℂ (Matrix (Fin 4) (Fin 4) ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank kronK_linearIndependent (by
    rw [Module.finrank_matrix]; simp)

/-- The basis reconstruction: `Y = ∑ p, (kronKBasis.repr Y p) • kronK p`. -/
theorem kronKBasis_sum_repr (Y : Matrix (Fin 4) (Fin 4) ℂ) :
    ∑ p, (kronKBasis.repr Y p) • kronK p = Y := by
  have h := kronKBasis.sum_repr Y
  simpa only [kronKBasis, coe_basisOfLinearIndependentOfCardEqFinrank] using h

/-- **HS coordinate formula**: `kronKBasis.repr Y p = ¼·tr(kronK p · Y)`. -/
theorem kronKBasis_repr_eq (Y : Matrix (Fin 4) (Fin 4) ℂ) (p : Fin 4 × Fin 4) :
    kronKBasis.repr Y p = (4⁻¹ : ℂ) * (kronK p * Y).trace := by
  conv_rhs => rw [← kronKBasis_sum_repr Y]
  rw [Finset.mul_sum, Matrix.trace_sum]
  rw [Finset.sum_eq_single p]
  · rw [mul_smul_comm, Matrix.trace_smul, kronK_mul_trace, if_pos rfl, smul_eq_mul]
    ring
  · intro q _ hqp
    rw [mul_smul_comm, Matrix.trace_smul, kronK_mul_trace, if_neg (by exact fun h => hqp h.symm),
      smul_zero]
  · intro hp; exact absurd (Finset.mem_univ p) hp

/-! ## 5. The coordinates of a traceless skew-Hermitian `Y` -/

/-- `kronK p` is Hermitian. -/
theorem kronK_isHermitian (p : Fin 4 × Fin 4) : (kronK p).IsHermitian := by
  show (kronK p)ᴴ = kronK p
  unfold kronK
  rw [kronSU4_conjTranspose, pauli4_hermitian, pauli4_hermitian]

/-- `tr(K · Y)` is purely imaginary for `K` Hermitian and `Y` skew-Hermitian. -/
theorem trace_herm_mul_skew_re_zero {d : ℕ} (K Y : Matrix (Fin d) (Fin d) ℂ)
    (hK : K.IsHermitian) (hY : Y.IsSkewHermitian) : ((K * Y).trace).re = 0 := by
  have hconj : (starRingEnd ℂ) ((K * Y).trace) = -((K * Y).trace) := by
    rw [starRingEnd_apply, ← Matrix.trace_conjTranspose, Matrix.conjTranspose_mul,
      show Yᴴ = -Y from hY, show Kᴴ = K from hK, Matrix.neg_mul, Matrix.trace_neg,
      Matrix.trace_mul_comm]
  have hadd := Complex.add_conj ((K * Y).trace)
  rw [hconj, add_neg_cancel] at hadd
  have h2 : (2 : ℝ) * ((K * Y).trace).re = 0 := by exact_mod_cast hadd.symm
  linarith

/-- For skew-Hermitian `Y`, each tensor-Pauli coordinate `repr Y p` is purely imaginary. -/
theorem repr_re_zero (Y : Matrix (Fin 4) (Fin 4) ℂ) (hskew : Y.IsSkewHermitian)
    (p : Fin 4 × Fin 4) : (kronKBasis.repr Y p).re = 0 := by
  rw [kronKBasis_repr_eq, Complex.mul_re,
    trace_herm_mul_skew_re_zero (kronK p) Y (kronK_isHermitian p) hskew]
  norm_num

/-- For traceless `Y`, the `(0,0)` tensor-Pauli coordinate vanishes. -/
theorem repr_zero_zero (Y : Matrix (Fin 4) (Fin 4) ℂ) (htr : Y.trace = 0) :
    kronKBasis.repr Y (0, 0) = 0 := by
  have hk00 : kronK (0, 0) = 1 := by
    show kronSU4 (pauli4 0) (pauli4 0) = 1
    rw [show pauli4 0 = 1 from rfl, kronSU4_one]
  rw [kronKBasis_repr_eq, hk00, one_mul, htr, mul_zero]

/-! ## 6. The `Fin 15` re-indexing of the tensor-Pauli sum -/

/-- Inverse of `idx15`: `(a, b) ↦ 4a + b − 1`. -/
def invIdx15 (p : Fin 4 × Fin 4) : Fin 15 :=
  ⟨4 * p.1.val + p.2.val - 1, by have := p.1.isLt; have := p.2.isLt; omega⟩

theorem invIdx15_idx15 (j : Fin 15) : invIdx15 (idx15 j) = j := by
  apply Fin.ext; simp only [invIdx15, idx15]; have := j.isLt; omega

theorem idx15_invIdx15 {p : Fin 4 × Fin 4} (hp : p ≠ (0, 0)) : idx15 (invIdx15 p) = p := by
  have ha := p.1.isLt; have hb := p.2.isLt
  have hp' : ¬(p.1.val = 0 ∧ p.2.val = 0) := by
    rintro ⟨h1, h2⟩; exact hp (Prod.ext (Fin.ext (by simp [h1])) (Fin.ext (by simp [h2])))
  apply Prod.ext <;> apply Fin.ext <;> simp only [idx15, invIdx15] <;> omega

theorem idx15_ne_zero_pair (j : Fin 15) : idx15 j ≠ (0, 0) := by
  intro h
  rw [Prod.ext_iff, Fin.ext_iff, Fin.ext_iff] at h
  simp only [idx15, Fin.val_zero] at h
  have := j.isLt; omega

/-- Re-index a sum over `Fin 4 × Fin 4` (whose `(0,0)` term vanishes) as a sum over `Fin 15`. -/
theorem sum_eq_sum_idx15 {M : Type*} [AddCommMonoid M] (G : Fin 4 × Fin 4 → M)
    (h0 : G (0, 0) = 0) : ∑ p, G p = ∑ j : Fin 15, G (idx15 j) := by
  rw [← Finset.sum_erase Finset.univ h0]
  refine Finset.sum_bij' (fun p _ => invIdx15 p) (fun j _ => idx15 j)
    (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_ ?_
  · intro j _; rw [Finset.mem_erase]; exact ⟨idx15_ne_zero_pair j, Finset.mem_univ _⟩
  · intro p hp; rw [Finset.mem_erase] at hp; exact idx15_invIdx15 hp.1
  · intro j _; exact invIdx15_idx15 j
  · intro p hp; rw [Finset.mem_erase] at hp; rw [idx15_invIdx15 hp.1]

/-! ## 7. The spanning theorem (`hX_spans`) -/

/-- A purely-imaginary `z` rebuilt as `z = (z.im) · i`. -/
private theorem im_mul_I_of_re_zero (z : ℂ) (h : z.re = 0) : z = (z.im : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [h]

/-- **`hX_spans` for the SU(4) witness**: every traceless skew-Hermitian `Y` is a real-linear
combination of the 15 tensor-Pauli tangents. -/
theorem suFourTangent_spans (Y : Matrix (Fin 4) (Fin 4) ℂ)
    (hskew : Y.IsSkewHermitian) (htr : Y.trace = 0) :
    ∃ c : Fin 15 → ℝ, Y = ∑ i, ((c i : ℝ) : ℂ) • suFourTangent i := by
  refine ⟨fun j => 2 * (kronKBasis.repr Y (idx15 j)).im, ?_⟩
  conv_lhs => rw [← kronKBasis_sum_repr Y]
  rw [sum_eq_sum_idx15 (fun p => kronKBasis.repr Y p • kronK p)
    (by show kronKBasis.repr Y (0, 0) • kronK (0, 0) = 0; rw [repr_zero_zero Y htr, zero_smul])]
  apply Finset.sum_congr rfl
  intro j _
  set m : ℝ := (kronKBasis.repr Y (idx15 j)).im with hm_def
  have hm : kronKBasis.repr Y (idx15 j) = (m : ℂ) * Complex.I := by
    rw [hm_def]; exact im_mul_I_of_re_zero _ (repr_re_zero Y hskew (idx15 j))
  show kronKBasis.repr Y (idx15 j) • kronK (idx15 j) = ((2 * m : ℝ) : ℂ) • suFourTangent j
  rw [hm, show suFourTangent j = (Complex.I / 2) • kronK (idx15 j) from rfl, smul_smul]
  congr 1
  push_cast; ring

end SKEFTHawking.FKLW.TrappedIonSU4
