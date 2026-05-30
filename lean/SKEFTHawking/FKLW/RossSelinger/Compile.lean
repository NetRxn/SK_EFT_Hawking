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

end SKEFTHawking.RossSelinger
