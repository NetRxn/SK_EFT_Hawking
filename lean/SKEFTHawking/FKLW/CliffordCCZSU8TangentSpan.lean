/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6y Track T-A2′.2 (D) witness — the 63 tensor-Pauli tangents ℝ-span 𝔰𝔲(8)

The `hX_spans` field of the SU(8) Clifford+CCZ `ClosureDenseWitness`: every traceless
skew-Hermitian `Y ∈ Matrix (Fin 8) (Fin 8) ℂ` is a real-linear combination of the 63 tensor-Pauli
tangents `X_{abc} = (i/2)·(σ_a ⊗ σ_b ⊗ σ_c)`.

## Proof architecture (Hilbert-Schmidt / Pauli completeness)

  * `kronK8 p := kronSU8 σ_{p.1} σ_{p.2.1} σ_{p.2.2}` — the 64 Hermitian tensor-Paulis.
  * **HS-orthogonality** `tr(kronK8 p · kronK8 q) = 8·𝟙[p = q]` (via `kronSU8_mul` + `kronSU8_trace`
    + the 2×2 Pauli product-trace table `pauli4_mul_trace`).
  * **ℂ-linear independence** of the 64 `kronK8` (orthogonality ⇒ independence).
  * Since `finrank ℂ (M₈) = 64 = #(Fin 4³)`, the `kronK8` form a **ℂ-basis**; every `Y` decomposes
    as `Y = ∑ d_p · kronK8 p` with the HS coordinate `d_p = ⅛·tr(kronK8 p · Y)`.
  * **Traceless** ⇒ `d_{(0,0,0)} = 0`; **skew-Hermitian** ⇒ each `d_p ∈ iℝ`
    (`trace_herm_mul_skew_re_zero`), so `d_p · kronK8 p = c_p · X_{abc}` for real `c_p`.
  * Re-index the `Fin 4³` sum over the 63-enumeration `idx63` (dropping the zero `(0,0,0)` term).

This is the SU(8) mirror of the SU(4) `suFourTangent_spans`, reusing the d-generic
`trace_herm_mul_skew_re_zero` + the `pauli4_mul_trace` table.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected.

## Phase 6y Track T-A2′ provenance

Phase 6y Roadmap §"Track T-A2′ detail" sub-wave T-A2′.2 PROPER — (D) witness `hX_spans`.
DR blueprint §5.3 (63-tangent reduction). 2026-05-28.
-/

import Mathlib
import SKEFTHawking.FKLW.CliffordCCZSU8Tangents
import SKEFTHawking.FKLW.TrappedIonSU4TangentSpan
import SKEFTHawking.FKLW.TrappedIonSU4KronHom

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix Complex SKEFTHawking.FKLW.TrappedIonSU4

/-! ## 1. `kronSU2SU4` / `kronSU8` mixed-product (homomorphism) -/

/-- **`kronSU2SU4` mixed-product**: `kronSU2SU4 (A*C) (B*D) = kronSU2SU4 A B * kronSU2SU4 C D`. -/
theorem kronSU2SU4_mul (A C : Matrix (Fin 2) (Fin 2) ℂ) (B D : Matrix (Fin 4) (Fin 4) ℂ) :
    kronSU2SU4 (A * C) (B * D) = kronSU2SU4 A B * kronSU2SU4 C D := by
  have hmix : Matrix.kronecker (A * C) (B * D) =
      Matrix.kronecker A B * Matrix.kronecker C D :=
    Matrix.mul_kronecker_mul A C B D
  unfold kronSU2SU4
  rw [hmix, reindex_self_mul finProdFinEquiv (Matrix.kronecker A B) (Matrix.kronecker C D)]

/-- **`kronSU8` mixed-product**: `kronSU8 (A*A') (B*B') (C*C') = kronSU8 A B C * kronSU8 A' B' C'`. -/
theorem kronSU8_mul (A B C A' B' C' : Matrix (Fin 2) (Fin 2) ℂ) :
    kronSU8 (A * A') (B * B') (C * C') = kronSU8 A B C * kronSU8 A' B' C' := by
  unfold kronSU8
  rw [kronSU4_mul, kronSU2SU4_mul]

/-! ## 2. The 64 tensor-Pauli matrices and their Hilbert-Schmidt orthogonality -/

/-- The 64 Hermitian tensor-Pauli matrices `kronK8 p = σ_{p.1} ⊗ σ_{p.2.1} ⊗ σ_{p.2.2}`. -/
noncomputable def kronK8 (p : Fin 4 × Fin 4 × Fin 4) : Matrix (Fin 8) (Fin 8) ℂ :=
  kronSU8 (pauli4 p.1) (pauli4 p.2.1) (pauli4 p.2.2)

/-- **Hilbert-Schmidt orthogonality**: `tr(kronK8 p · kronK8 q) = 8·𝟙[p = q]`. -/
theorem kronK8_mul_trace (p q : Fin 4 × Fin 4 × Fin 4) :
    (kronK8 p * kronK8 q).trace = if p = q then 8 else 0 := by
  unfold kronK8
  rw [← kronSU8_mul, kronSU8_trace, pauli4_mul_trace, pauli4_mul_trace, pauli4_mul_trace]
  by_cases hpq : p = q
  · subst hpq; norm_num
  · rw [if_neg hpq]
    have hcomp : ¬(p.1 = q.1 ∧ p.2.1 = q.2.1 ∧ p.2.2 = q.2.2) := by
      intro h
      exact hpq (Prod.ext_iff.mpr ⟨h.1, Prod.ext_iff.mpr ⟨h.2.1, h.2.2⟩⟩)
    rcases not_and_or.mp hcomp with h1 | h23
    · rw [if_neg h1]; ring
    · rcases not_and_or.mp h23 with h2 | h3
      · rw [if_neg h2]; ring
      · rw [if_neg h3]; ring

/-! ## 3. ℂ-linear independence of the 64 tensor-Paulis -/

/-- The 64 tensor-Paulis are ℂ-linearly independent (Hilbert-Schmidt orthogonality). -/
theorem kronK8_linearIndependent : LinearIndependent ℂ kronK8 := by
  rw [Fintype.linearIndependent_iff]
  intro g hg q
  have h_tr : (∑ p, g p • kronK8 p) * kronK8 q = 0 := by rw [hg]; simp
  have h_tr2 : ((∑ p, g p • kronK8 p) * kronK8 q).trace = 0 := by rw [h_tr]; simp
  rw [Finset.sum_mul] at h_tr2
  simp only [Matrix.trace_sum, smul_mul_assoc, Matrix.trace_smul, kronK8_mul_trace] at h_tr2
  rw [Finset.sum_eq_single q] at h_tr2
  · simpa using h_tr2
  · intro p _ hpq; rw [if_neg hpq]; simp
  · intro hq; exact absurd (Finset.mem_univ q) hq

/-! ## 4. The tensor-Pauli ℂ-basis of `M₈` and the HS coordinate formula -/

/-- The 64 tensor-Paulis form a ℂ-basis of `Matrix (Fin 8) (Fin 8) ℂ`. -/
noncomputable def kronK8Basis :
    Module.Basis (Fin 4 × Fin 4 × Fin 4) ℂ (Matrix (Fin 8) (Fin 8) ℂ) :=
  basisOfLinearIndependentOfCardEqFinrank kronK8_linearIndependent (by
    rw [Module.finrank_matrix]; simp)

/-- The basis reconstruction: `Y = ∑ p, (kronK8Basis.repr Y p) • kronK8 p`. -/
theorem kronK8Basis_sum_repr (Y : Matrix (Fin 8) (Fin 8) ℂ) :
    ∑ p, (kronK8Basis.repr Y p) • kronK8 p = Y := by
  have h := kronK8Basis.sum_repr Y
  simpa only [kronK8Basis, coe_basisOfLinearIndependentOfCardEqFinrank] using h

/-- **HS coordinate formula**: `kronK8Basis.repr Y p = ⅛·tr(kronK8 p · Y)`. -/
theorem kronK8Basis_repr_eq (Y : Matrix (Fin 8) (Fin 8) ℂ) (p : Fin 4 × Fin 4 × Fin 4) :
    kronK8Basis.repr Y p = (8⁻¹ : ℂ) * (kronK8 p * Y).trace := by
  conv_rhs => rw [← kronK8Basis_sum_repr Y]
  rw [Finset.mul_sum, Matrix.trace_sum]
  rw [Finset.sum_eq_single p]
  · rw [mul_smul_comm, Matrix.trace_smul, kronK8_mul_trace, if_pos rfl, smul_eq_mul]
    ring
  · intro q _ hqp
    rw [mul_smul_comm, Matrix.trace_smul, kronK8_mul_trace, if_neg (by exact fun h => hqp h.symm),
      smul_zero]
  · intro hp; exact absurd (Finset.mem_univ p) hp

/-! ## 5. The coordinates of a traceless skew-Hermitian `Y` -/

/-- `kronK8 p` is Hermitian. -/
theorem kronK8_isHermitian (p : Fin 4 × Fin 4 × Fin 4) : (kronK8 p).IsHermitian := by
  show (kronK8 p)ᴴ = kronK8 p
  unfold kronK8
  rw [kronSU8_conjTranspose, pauli4_hermitian, pauli4_hermitian, pauli4_hermitian]

/-- For skew-Hermitian `Y`, each tensor-Pauli coordinate `repr Y p` is purely imaginary. -/
theorem repr8_re_zero (Y : Matrix (Fin 8) (Fin 8) ℂ) (hskew : Y.IsSkewHermitian)
    (p : Fin 4 × Fin 4 × Fin 4) : (kronK8Basis.repr Y p).re = 0 := by
  rw [kronK8Basis_repr_eq, Complex.mul_re,
    trace_herm_mul_skew_re_zero (kronK8 p) Y (kronK8_isHermitian p) hskew]
  norm_num

/-- For traceless `Y`, the `(0,0,0)` tensor-Pauli coordinate vanishes. -/
theorem repr8_zero_zero_zero (Y : Matrix (Fin 8) (Fin 8) ℂ) (htr : Y.trace = 0) :
    kronK8Basis.repr Y (0, 0, 0) = 0 := by
  have hk000 : kronK8 (0, 0, 0) = 1 := by
    show kronSU8 (pauli4 0) (pauli4 0) (pauli4 0) = 1
    show kronSU2SU4 (pauli4 0) (kronSU4 (pauli4 0) (pauli4 0)) = 1
    rw [show pauli4 0 = (1 : Matrix (Fin 2) (Fin 2) ℂ) from rfl, kronSU4_one]
    show kronSU2SU4 1 1 = 1
    have h1 : Matrix.kronecker (1 : Matrix (Fin 2) (Fin 2) ℂ) (1 : Matrix (Fin 4) (Fin 4) ℂ) = 1 :=
      Matrix.one_kronecker_one
    unfold kronSU2SU4
    rw [h1]
    exact Matrix.submatrix_one_equiv finProdFinEquiv.symm
  rw [kronK8Basis_repr_eq, hk000, one_mul, htr, mul_zero]

/-! ## 6. The `Fin 63` re-indexing of the tensor-Pauli sum -/

/-- Inverse of `idx63`: `(a, b, c) ↦ 16a + 4b + c − 1`. -/
def invIdx63 (p : Fin 4 × Fin 4 × Fin 4) : Fin 63 :=
  ⟨16 * p.1.val + 4 * p.2.1.val + p.2.2.val - 1, by
    have := p.1.isLt; have := p.2.1.isLt; have := p.2.2.isLt; omega⟩

theorem invIdx63_idx63 (j : Fin 63) : invIdx63 (idx63 j) = j := by
  apply Fin.ext; simp only [invIdx63, idx63]; have := j.isLt; omega

theorem idx63_invIdx63 {p : Fin 4 × Fin 4 × Fin 4} (hp : p ≠ (0, 0, 0)) :
    idx63 (invIdx63 p) = p := by
  have ha := p.1.isLt; have hb := p.2.1.isLt; have hc := p.2.2.isLt
  have hp' : ¬(p.1.val = 0 ∧ p.2.1.val = 0 ∧ p.2.2.val = 0) := by
    rintro ⟨h1, h2, h3⟩
    exact hp (Prod.ext (Fin.ext (by simp [h1]))
      (Prod.ext (Fin.ext (by simp [h2])) (Fin.ext (by simp [h3]))))
  apply Prod.ext
  · apply Fin.ext; simp only [idx63, invIdx63]; omega
  apply Prod.ext
  · apply Fin.ext; simp only [idx63, invIdx63]; omega
  · apply Fin.ext; simp only [idx63, invIdx63]; omega

theorem idx63_ne_zero_triple (j : Fin 63) : idx63 j ≠ (0, 0, 0) := by
  intro h
  rw [Prod.ext_iff, Prod.ext_iff, Fin.ext_iff, Fin.ext_iff, Fin.ext_iff] at h
  simp only [idx63, Fin.val_zero] at h
  have := j.isLt; omega

/-- Re-index a sum over `Fin 4³` (whose `(0,0,0)` term vanishes) as a sum over `Fin 63`. -/
theorem sum_eq_sum_idx63 {M : Type*} [AddCommMonoid M] (G : Fin 4 × Fin 4 × Fin 4 → M)
    (h0 : G (0, 0, 0) = 0) : ∑ p, G p = ∑ j : Fin 63, G (idx63 j) := by
  rw [← Finset.sum_erase Finset.univ h0]
  refine Finset.sum_bij' (fun p _ => invIdx63 p) (fun j _ => idx63 j)
    (fun _ _ => Finset.mem_univ _) ?_ ?_ ?_ ?_
  · intro j _; rw [Finset.mem_erase]; exact ⟨idx63_ne_zero_triple j, Finset.mem_univ _⟩
  · intro p hp; rw [Finset.mem_erase] at hp; exact idx63_invIdx63 hp.1
  · intro j _; exact invIdx63_idx63 j
  · intro p hp; rw [Finset.mem_erase] at hp; rw [idx63_invIdx63 hp.1]

/-! ## 7. The spanning theorem (`hX_spans`) -/

/-- A purely-imaginary `z` rebuilt as `z = (z.im) · i`. -/
private theorem im_mul_I_of_re_zero8 (z : ℂ) (h : z.re = 0) : z = (z.im : ℂ) * Complex.I := by
  apply Complex.ext <;> simp [h]

/-- **`hX_spans` for the SU(8) witness**: every traceless skew-Hermitian `Y` is a real-linear
combination of the 63 tensor-Pauli tangents. -/
theorem suEightTangent_spans (Y : Matrix (Fin 8) (Fin 8) ℂ)
    (hskew : Y.IsSkewHermitian) (htr : Y.trace = 0) :
    ∃ c : Fin 63 → ℝ, Y = ∑ i, ((c i : ℝ) : ℂ) • suEightTangent i := by
  refine ⟨fun j => 2 * (kronK8Basis.repr Y (idx63 j)).im, ?_⟩
  conv_lhs => rw [← kronK8Basis_sum_repr Y]
  rw [sum_eq_sum_idx63 (fun p => kronK8Basis.repr Y p • kronK8 p)
    (by show kronK8Basis.repr Y (0, 0, 0) • kronK8 (0, 0, 0) = 0;
        rw [repr8_zero_zero_zero Y htr, zero_smul])]
  apply Finset.sum_congr rfl
  intro j _
  set m : ℝ := (kronK8Basis.repr Y (idx63 j)).im with hm_def
  have hm : kronK8Basis.repr Y (idx63 j) = (m : ℂ) * Complex.I := by
    rw [hm_def]; exact im_mul_I_of_re_zero8 _ (repr8_re_zero Y hskew (idx63 j))
  show kronK8Basis.repr Y (idx63 j) • kronK8 (idx63 j) = ((2 * m : ℝ) : ℂ) • suEightTangent j
  rw [hm, show suEightTangent j = (Complex.I / 2) • kronK8 (idx63 j) from rfl, smul_smul]
  congr 1
  push_cast; ring

end SKEFTHawking.FKLW.CliffordCCZSU8
