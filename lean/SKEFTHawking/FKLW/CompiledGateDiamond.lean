import SKEFTHawking.FKLW.CliffordTCompiler
import SKEFTHawking.QuantumNetwork.UnitaryDiamond
import SKEFTHawking.QuantumNetwork.MatrixNormBridge

/-!
# Compiled-gate diamond certificate (Phase 6AP, Wave 3 capstone)

The end-to-end kernel theorem connecting gate synthesis to worst-case channel error:
compiling any `U ∈ SU(2)` to precision `ε` with the correct-by-construction Clifford+T
compiler (`cliffordTCompile_correct`, operator-norm layer) yields a channel whose
**diamond distance** from the target's channel is certified:

  `diamondDist Φ_compiled Φ_U ≤ √2 · ε`

(½-diamond convention). The chain, every link kernel-checked:

  1. `cliffordTCompile_correct` — `‖W − U‖_{L∞op} ≤ ε` (compiler contract);
  2. `Matrix.linfty_opNorm_def` — the L∞ operator norm IS the sup of row ℓ¹-sums, so every
     row sum of `W − U` is `≤ ε` (`cliffordTCompile_rowSum_le`, instance-free hand-off);
  3. `MatrixNormBridge.l2_opNorm_le_sqrt_card_mul_of_rowSum_le` — `‖W − U‖_{L²op} ≤ √2·ε`;
  4. `diamondDist_unitaryKraus_le` (the AKN bound) — `diamondDist ≤ ‖W − U‖_{L²op}`.

The `√2` is the `card (Fin 2)` norm-bridge constant, not the AKN constant; the bound also
inherits the global-phase non-sharpness documented in `UnitaryDiamond.lean`.

Invariants: kernel-pure, zero sorry, zero project-local axioms, no `maxHeartbeats`.
-/

namespace SKEFTHawking.FKLW.GenericSU2

open SKEFTHawking.QuantumNetwork SKEFTHawking.FKLW.SolovayKitaevRecursion

/-! ## §1. L∞ side: the compiler contract as row sums (instance-free hand-off) -/

section LinftySide

attribute [local instance] Matrix.linftyOpNormedAddCommGroup

/-- **The compiler's error, row by row:** every row ℓ¹-sum of `W − U` is at most `ε`,
where `W` is the compiled Clifford+T word's matrix. Extracted from
`cliffordTCompile_correct` via `Matrix.linfty_opNorm_def` (the L∞ operator norm is the sup
of row sums). The statement mentions only entrywise ℂ-norms — no matrix-norm instance —
so it composes freely with the L²-side files. -/
theorem cliffordTCompile_rowSum_le
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ) (hε_pos : 0 < ε) (hε_le : ε ≤ ε₀)
    (i : Fin 2) :
    ∑ j, ‖(((cliffordTGeneratingSet.ρ_hom (cliffordTCompile U ε) :
          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)) i j‖ ≤ ε := by
  set A := (((cliffordTGeneratingSet.ρ_hom (cliffordTCompile U ε) :
      ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    Matrix (Fin 2) (Fin 2) ℂ) - (U : Matrix (Fin 2) (Fin 2) ℂ)) with hAdef
  have hcomp : ‖A‖ ≤ ε := (cliffordTCompile_correct U ε hε_pos hε_le).1
  have hsup : ((∑ j, ‖A i j‖₊ : NNReal) : ℝ) ≤ ‖A‖ := by
    rw [Matrix.linfty_opNorm_def]
    exact_mod_cast Finset.le_sup (f := fun i : Fin 2 => ∑ j, ‖A i j‖₊) (Finset.mem_univ i)
  calc ∑ j, ‖A i j‖ = ((∑ j, ‖A i j‖₊ : NNReal) : ℝ) := by push_cast; rfl
    _ ≤ ‖A‖ := hsup
    _ ≤ ε := hcomp

end LinftySide

/-! ## §2. L² side: the diamond certificate -/

section L2Side

open scoped Matrix.Norms.L2Operator

/-- **Compiled-gate diamond certificate (end-to-end):** for any target `U ∈ SU(2)` and
precision `0 < ε ≤ ε₀`, the Clifford+T-compiled channel is within diamond distance `√2·ε`
of the target's channel:

  `diamondDist Φ_compiled Φ_U ≤ √2 · ε`.

Every link in the chain is kernel-checked (compiler contract → row sums → L²-opnorm
bridge → AKN diamond bound); see the module header. This is the theorem a
"diamond-certified compiled gate" certificate cites by FQN. -/
theorem diamondDist_cliffordTCompile_le
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ) (hε_pos : 0 < ε) (hε_le : ε ≤ ε₀) :
    diamondDist
        (unitaryKraus ((cliffordTGeneratingSet.ρ_hom (cliffordTCompile U ε) :
            ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
          Matrix (Fin 2) (Fin 2) ℂ))
        (unitaryKraus (U : Matrix (Fin 2) (Fin 2) ℂ))
      ≤ Real.sqrt 2 * ε := by
  set W := ((cliffordTGeneratingSet.ρ_hom (cliffordTCompile U ε) :
      ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ) with hWdef
  have hWu : W ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    Matrix.specialUnitaryGroup_le_unitaryGroup
      (cliffordTGeneratingSet.ρ_hom (cliffordTCompile U ε) :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)).prop
  have hUu : (U : Matrix (Fin 2) (Fin 2) ℂ) ∈ Matrix.unitaryGroup (Fin 2) ℂ :=
    Matrix.specialUnitaryGroup_le_unitaryGroup U.prop
  have hAKN := diamondDist_unitaryKraus_le (n := 2) hWu hUu
  have hrow : ∀ i, ∑ j, ‖(W - (U : Matrix (Fin 2) (Fin 2) ℂ)) i j‖ ≤ ε := fun i =>
    cliffordTCompile_rowSum_le U ε hε_pos hε_le i
  have hbridge : ‖W - (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ Real.sqrt (Fintype.card (Fin 2)) * ε :=
    MatrixNormBridge.l2_opNorm_le_sqrt_card_mul_of_rowSum_le _ hε_pos.le hrow
  rw [Fintype.card_fin] at hbridge
  have h2 : ((2 : ℕ) : ℝ) = (2 : ℝ) := by norm_num
  rw [h2] at hbridge
  linarith

end L2Side

end SKEFTHawking.FKLW.GenericSU2
