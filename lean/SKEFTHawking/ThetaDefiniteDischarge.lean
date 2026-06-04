/-
# [Θ] discharge — the definite even-unimodular input of the van der Blij reduction

`eight_dvd_latticeSig_of_HM_of_Theta` (VanDerBlijReduction) reduces `8 ∣ latticeSig` for *every* even
unimodular form to two classical inputs [HM] (indefinite ⟹ isotropic vector) and [Θ] (definite ⟹
`8 ∣ σ`). This file **discharges [Θ]** unconditionally, using the theta-modularity capstone
`eight_dvd_rank` (`ThetaModularWeight`): a positive-definite even unimodular form has `8 ∣ rank`, and a
definite form has `σ = ±rank`.

The bridge from the inertia hypothesis (`sigPos = 0 ∨ sigNeg = 0`) to positive-definiteness:
* a unimodular cast is nondegenerate (`det = ±1 ≠ 0`), so its radical is `⊥` (`nondeg_radical_eq_bot`);
* `sigPos + sigNeg + finrank radical = finrank` then forces `sigPos = finrank` when `sigNeg = 0`;
* `sigPos = finrank` means the maximal positive subspace is the whole space ⟹ `PosDef`
  (`posDef_of_sigPos_eq_finrank`);
* the `sigPos = 0` branch is the negative-definite mirror, handled via `-A`.

Kernel-pure, no new axioms, no `maxHeartbeats`.
-/

import Mathlib
import SKEFTHawking.ThetaModularWeight
import SKEFTHawking.ThetaModularity
import SKEFTHawking.BlockSignature
import SKEFTHawking.LatticeSignature
import SKEFTHawking.AlgebraicRokhlin

namespace SKEFTHawking

open Matrix QuadraticMap

/-- A real quadratic form whose positive inertia index equals the full dimension is positive-definite:
the maximal positive-definite subspace (`exists_finrank_eq_sigPos_and_posDef`) has full rank, hence is `⊤`. -/
theorem posDef_of_sigPos_eq_finrank {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (Q : QuadraticForm ℝ V) (h : sigPos Q = Module.finrank ℝ V) :
    Q.PosDef := by
  obtain ⟨W, hW, hWpd⟩ := exists_finrank_eq_sigPos_and_posDef Q
  have hWtop : W = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hW, h])
  intro x hx
  have := hWpd ⟨x, hWtop ▸ Submodule.mem_top⟩ (by simpa [Subtype.ext_iff] using hx)
  rwa [QuadraticMap.restrict_apply] at this

/-- For an even unimodular form with vanishing negative inertia, the real cast is positive-definite. -/
theorem posDef_cast_of_sigNeg_zero {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ) (heu : IsEvenUnimodular A)
    (h0 : sigNeg (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap' = 0) :
    (A.map (Int.cast : ℤ → ℝ)).PosDef := by
  set B := A.map (Int.cast : ℤ → ℝ) with hB
  have hsymB : Bᵀ = B := by rw [hB, ← Matrix.transpose_map, heu.1]
  have hAdet : A.det ≠ 0 := by rcases heu.2.1 with h | h <;> simp [h]
  have hdet : B.det ≠ 0 := by
    rw [hB, ← Int.cast_det]; exact Int.cast_ne_zero.mpr hAdet
  have hnd : B.Nondegenerate := Matrix.nondegenerate_iff_det_ne_zero.mpr hdet
  have hrad : B.toQuadraticMap'.radical = ⊥ := nondeg_radical_eq_bot B hsymB hnd
  have hsig : sigPos B.toQuadraticMap' = Module.finrank ℝ (Fin m → ℝ) := by
    have hsum := QuadraticForm.sigPos_add_sigNeg_add_radical (Q := B.toQuadraticMap')
    rw [hrad, h0] at hsum
    simpa using hsum
  exact Matrix.PosDef.of_toQuadraticForm' hsymB (posDef_of_sigPos_eq_finrank _ hsig)

/-- `-A` is even unimodular when `A` is. -/
theorem isEvenUnimodular_neg {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ) (heu : IsEvenUnimodular A) :
    IsEvenUnimodular (-A) := by
  refine ⟨?_, ?_, ?_⟩
  · show (-A)ᵀ = -A; rw [Matrix.transpose_neg, heu.1]
  · rw [IsUnimodular, Matrix.det_neg, Fintype.card_fin]
    rcases heu.2.1 with h | h <;> rcases neg_one_pow_eq_or ℤ m with hp | hp <;> simp [h, hp]
  · intro i; exact (heu.2.2 i).neg_right

/-- **[Θ] discharged.** A definite (`sigPos = 0 ∨ sigNeg = 0`) even unimodular form has `8 ∣ latticeSig`.
This is the exact hypothesis demanded by `eight_dvd_latticeSig_of_HM_of_Theta`, now a theorem rather than
an assumption — proved from theta-modularity (`eight_dvd_rank`) and Sylvester inertia. -/
theorem eight_dvd_latticeSig_of_definite {m : ℕ} (A : Matrix (Fin m) (Fin m) ℤ)
    (heu : IsEvenUnimodular A)
    (hdef : sigPos (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap' = 0 ∨
            sigNeg (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap' = 0) :
    8 ∣ latticeSig A := by
  rcases hdef with hsp | hsn
  · have hnegeu := isEvenUnimodular_neg A heu
    have hqm : ((-A).map (Int.cast : ℤ → ℝ)).toQuadraticMap'
        = -((A.map (Int.cast : ℤ → ℝ)).toQuadraticMap') := by
      have hmap : ((-A).map (Int.cast : ℤ → ℝ)) = -(A.map (Int.cast : ℤ → ℝ)) := by ext i j; simp
      rw [hmap]; simp [Matrix.toQuadraticMap']
    have hsn' : sigNeg ((-A).map (Int.cast : ℤ → ℝ)).toQuadraticMap' = 0 := by
      rw [hqm, sigNeg, neg_neg]; exact hsp
    have hpd := posDef_cast_of_sigNeg_zero (-A) hnegeu hsn'
    have hls : latticeSig A = -(m : ℤ) := latticeSig_of_negDef A hpd
    have h8 := eight_dvd_rank (-A) hnegeu.1 hnegeu.2.1 hpd hnegeu.2.2
    rw [hls]; exact (Int.dvd_neg).mpr (Int.natCast_dvd_natCast.mpr h8)
  · have hpd := posDef_cast_of_sigNeg_zero A heu hsn
    have hls : latticeSig A = (m : ℤ) := latticeSig_of_posDef A hpd
    have h8 := eight_dvd_rank A heu.1 heu.2.1 hpd heu.2.2
    rw [hls]; exact Int.natCast_dvd_natCast.mpr h8

end SKEFTHawking
