/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item I — the runnable Ross-Selinger `compile` (SU(2) → Clifford+T word)

Composes the shipped pieces into the target-level compiler:
  (round U's first column via `twoDimGridSolution` → `gridNumerator` u)
  → (`gridFindT` residual t, det-1) → (`gridCompile` = `kmmReduce ∘ assembleUnitary`).
`compile_correct` is the SOUNDNESS: when the finder returns a word and the cleared columns
approximate `U`'s columns within `ε`, the word interprets to within `2ε` of `U` in operator norm
(composing `gridCompile_correct` with `approx_assembleUnitary`). Per the corrected scope, the
finder *producing* such columns (the `t`-near-`U₁₀` coupling) is supplied by the grid solver
(`twoDimGridSolution` for the first column) + the ≥50-case pygridsynth cross-validation
(empirical completeness); the unconditional `t`-existence is the parked NT follow-on.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected. **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.GridCompileCorrect
import SKEFTHawking.FKLW.RossSelinger.GridSolutions

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

open scoped Matrix

attribute [local instance] KMM.nonempty_kmmReduction Matrix.linftyOpNormedAddCommGroup

/-- **The first-column grid numerator for a target.** Rounds `√2^k · U₀₀` (real and imaginary
parts, conjugate centred at 0 — the unit-box constraint) via `twoDimGridSolution`, assembled into
the `ℤ[ω]` column numerator `u` by `gridNumerator`. -/
noncomputable def compileColumn (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (k : ℕ) : ZOmega :=
  let s := GridProblem.twoDimGridSolution
    (Real.sqrt 2 ^ k * ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re)
    (Real.sqrt 2 ^ k * ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im) 0 0
  gridNumerator s.1 s.2.1 s.2.2.1 s.2.2.2

/-- **The runnable Ross-Selinger compiler** `compile : SU(2) → (k, b) → Option (Clifford+T word)`.
Rounds `U`'s first column to `u = compileColumn U k`, finds the residual `t` (the det-1
Diophantine) via the bounded `gridFindT`, and KMM-synthesizes `assembleUnitary u t k`. Returns
`none` if no residual is found within the search bound. (`k = Θ(log(1/ε))` and the search bound
`b` are the precision/effort parameters; the front-end rounding is noncomputable over `ℝ`.) -/
noncomputable def compile (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (k b : ℕ) :
    Option (List CliffordTGate) :=
  KMM.gridCompile (compileColumn U k) k b

/-- **`compile` soundness.** When the bounded finder returns a residual `t` (so the det-1
constraint holds) and the cleared columns approximate `U`'s first column entry `U₀₀` (via the
rounded `u`) and second `U₁₀` (via `t`) within `ε`, `compile` returns a Clifford+T word that
interprets to within `2ε` of `U` in `linftyOpNorm`. Composes `gridCompile_correct`
(`compile = some word`, `interp word = assembleUnitary u t k`) with `approx_assembleUnitary`. -/
theorem compile_correct (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (k b : ℕ) {ε : ℝ}
    (hε : 0 ≤ ε) (t : ZOmega) (ht : KMM.gridFindT (compileColumn U k) k b = some t)
    (h00 : ‖ZOmegaSqrt2.toComplex (ZOmegaSqrt2.mk (compileColumn U k) k)
              - (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ ≤ ε)
    (h10 : ‖ZOmegaSqrt2.toComplex (ZOmegaSqrt2.mk t k)
              - (U : Matrix (Fin 2) (Fin 2) ℂ) 1 0‖ ≤ ε) :
    ∃ w, compile U k b = some w ∧
      ‖toComplexMat (CliffordTGate.interp w) - (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ 2 * ε := by
  refine ⟨KMM.gridSynthWord (compileColumn U k) t k, (KMM.gridCompile_correct ht).1, ?_⟩
  rw [(KMM.gridCompile_correct ht).2]
  exact approx_assembleUnitary (compileColumn U k) t k U hε h00 h10

/-- **Scale-k discharge of the first-column hypothesis.** For `k` large enough that the scaled
value half-width clears `1+√2` (`1+√2 ≤ 2ε·√2^k`), the rounded first-column numerator
`compileColumn U k` approximates `U₀₀` within `2ε` — `compile_correct`'s `h00`, now discharged
(no longer a hypothesis) from `twoDimGridSolution_spec` + `gridNumerator_approx`. (The residual
`t`-bound `h10` stays empirical — the grid-solver `t`-coupling / pygridsynth completeness.) -/
theorem compileColumn_approx (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (k : ℕ) {ε : ℝ}
    (hk : 1 + Real.sqrt 2 ≤ 2 * ε * Real.sqrt 2 ^ k) :
    ‖ZOmegaSqrt2.toComplex (ZOmegaSqrt2.mk (compileColumn U k) k)
        - (U : Matrix (Fin 2) (Fin 2) ℂ) 0 0‖ ≤ 2 * ε := by
  have hspos : (0 : ℝ) < Real.sqrt 2 ^ k := by positivity
  have hcne : (Real.sqrt 2 ^ k : ℝ) ≠ 0 := hspos.ne'
  simp only [compileColumn]
  set s := GridProblem.twoDimGridSolution
    (Real.sqrt 2 ^ k * ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re)
    (Real.sqrt 2 ^ k * ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im) 0 0 with hs
  obtain ⟨hvr, _, hvi, _⟩ := GridProblem.twoDimGridSolution_spec
    (Real.sqrt 2 ^ k * ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re)
    (Real.sqrt 2 ^ k * ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im) 0 0
    (2 * ε * Real.sqrt 2 ^ k) (2 * ε * Real.sqrt 2 ^ k)
    (1 + Real.sqrt 2) (1 + Real.sqrt 2) hk hk le_rfl le_rfl
  rw [← hs] at hvr hvi
  rw [show (2 * ε * Real.sqrt 2 ^ k / 2 : ℝ) = ε * Real.sqrt 2 ^ k from by ring] at hvr hvi
  apply gridNumerator_approx _ _ _ _ k _ ?_ ?_
  · rw [show ((s.1 : ℝ) + (s.2.1 : ℝ) * Real.sqrt 2) / Real.sqrt 2 ^ k
            - ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re
          = ((s.1 : ℝ) + (s.2.1 : ℝ) * Real.sqrt 2
              - Real.sqrt 2 ^ k * ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0).re) / Real.sqrt 2 ^ k
          from by field_simp, abs_div, abs_of_pos hspos, div_le_iff₀ hspos]
    exact hvr
  · rw [show ((s.2.2.1 : ℝ) + (s.2.2.2 : ℝ) * Real.sqrt 2) / Real.sqrt 2 ^ k
            - ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im
          = ((s.2.2.1 : ℝ) + (s.2.2.2 : ℝ) * Real.sqrt 2
              - Real.sqrt 2 ^ k * ((U : Matrix (Fin 2) (Fin 2) ℂ) 0 0).im) / Real.sqrt 2 ^ k
          from by field_simp, abs_div, abs_of_pos hspos, div_le_iff₀ hspos]
    exact hvi

end SKEFTHawking.RossSelinger
