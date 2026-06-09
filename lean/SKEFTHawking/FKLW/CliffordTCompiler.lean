/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6AN Wave 5 — Correct-by-construction Clifford+T gate compiler ("CompCert for the gate compiler")

This module lifts the verified-compilation arc (bundle D8: Solovay–Kitaev / Dawson–Nielsen
Clifford+T) from **per-output certification** to a **correct-by-construction** statement: a single
named compile *function* `cliffordTCompile` whose correctness — approximation error AND output
gate-length — is a theorem about the *algorithm*, universally quantified over every target `U ∈ SU(2)`
and precision `ε ∈ (0, ε₀]`, rather than a per-instance check.

The load-bearing foundation is the Phase 6u/6x quantitative-SK substrate: the structural
Dawson–Nielsen recursion `skApproxC_generic`, the unconditional super-quadratic error invariant
`SkApproxCSuperQuadraticBound_generic_holds`, and the constructive length-bounded base finder
`cliffordTBaseFinder_constructive`.

## Compiler-correctness contract (all UNCONDITIONAL, kernel-only)

* `cliffordTCompile` — the compiler as a function `SU(2) → ℝ → FreeGroup (Fin 2)`.
* `cliffordTCompile_eq_recursion` — **termination / finite depth**: the compiler is the structural
  Dawson–Nielsen recursion `skApproxC_generic` run to the *explicit finite depth* `skLevel_polylog ε`.
  `skApproxC_generic` is structural recursion on `ℕ` (it bottoms out at the base finder), so it
  terminates by construction and is a total function.
* `cliffordTCompile_recursion_base` — **loop initialization**: at depth `0` the compiler returns the
  constructive base-finder word.
* `cliffordTCompile_loop_invariant` — **the loop invariant**: at *every* recursion depth `n` and for
  *every* target `U`, the approximation contract `‖ρ_CliffT(level n) − U‖ ≤ ε_seq K_compose (2ε₀) n`
  holds — each Dawson–Nielsen refinement step preserves (and super-quadratically tightens) the
  approximation contract.
* `cliffordTCompile_correct` — **the compiler-correctness theorem**: for every `U` and
  `ε ∈ (0, ε₀]`, the output `cliffordTCompile U ε` simultaneously (i) approximates `U` within `ε`,
  (ii) has SK recursion-level length `≤ skLengthConst·(log 1/ε)^skLengthExponent`, and (iii) has
  actual output-word length `≤ skLength_at_baseCase cliffordTFiniteCover_maxLength (skLevel_polylog ε)`.
  Every output provably meets its ε/length spec — a theorem about the algorithm, not a per-output
  check.
* `cliffordTCompile_correct_example` — a worked instantiation at a concrete target and precision.

**Residual (documented, decomposition-backed — NOT a gap in this wave's claim):** the output-word
length bound (iii) is parametric in `cliffordTFiniteCover_maxLength`, the constructive ε₀-cover's
maximum word length, NOT the Ross–Selinger information-theoretically optimal `O(log 1/ε)` constant.
Tightening (iii) to the optimal constant requires the full Ross–Selinger 2014 ℤ[ω][1/√2] exact-synthesis
development (~1,600–3,000 LoC; `Lit-Search/tasks/ross_selinger_arxiv_1403_2975_zomega_invsqrt2_synthesis.md`)
and is the natural follow-on; the correct-by-construction guarantee here is complete and unconditional
at the constructive base finder.

## Pipeline invariants
- kernel-pure `{propext, Classical.choice, Quot.sound}`; no new project-local axioms (#15);
  no `maxHeartbeats` (#10); no `native_decide`.
-/

import SKEFTHawking.FKLW.RossSelingerLightweight
import SKEFTHawking.FKLW.CliffordTQuantitative

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSU2

open Matrix SKEFTHawking SKEFTHawking.FKLW
  SKEFTHawking.FKLW.SolovayKitaevRecursion
  SKEFTHawking.FKLW.SolovayKitaevLengthBound

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-- **The Clifford+T Solovay–Kitaev compiler, as a function.** Given a target `U ∈ SU(2)` and a
precision `ε`, returns a `FreeGroup (Fin 2)` word over `{of 0 ↦ H_SU, of 1 ↦ T_SU}` — the
constructive Dawson–Nielsen composition run to depth `skLevel_polylog ε` over the constructive
length-bounded base finder. -/
noncomputable def cliffordTCompile
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ) :=
  solovayKitaev_compile_strict_constructive_generic
    cliffordTGeneratingSet cliffordTBaseFinder_constructive U ε

/-- **Termination / finite recursion depth.** The compiler is the structural Dawson–Nielsen recursion
`skApproxC_generic` run to the explicit finite depth `skLevel_polylog ε`. Because `skApproxC_generic`
recurses structurally on the depth `ℕ` and bottoms out at the base finder
(`cliffordTCompile_recursion_base`), it terminates by construction and is a total function. -/
theorem cliffordTCompile_eq_recursion
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ) :
    cliffordTCompile U ε
      = skApproxC_generic cliffordTGeneratingSet cliffordTBaseFinder_constructive
          (skLevel_polylog ε) U := rfl

/-- **Loop initialization.** At recursion depth `0` the compiler returns the constructive
base-finder word. -/
theorem cliffordTCompile_recursion_base
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
    skApproxC_generic cliffordTGeneratingSet cliffordTBaseFinder_constructive 0 U
      = cliffordTBaseFinder_constructive U :=
  skApproxC_generic_zero cliffordTGeneratingSet cliffordTBaseFinder_constructive U

/-- **The compiler loop invariant.** At *every* recursion depth `n` and for *every* target `U`, the
output of the depth-`n` Dawson–Nielsen recursion approximates `U` within the super-quadratically
shrinking budget `ε_seq K_compose (2ε₀) n`. Each refinement step preserves (and tightens) the
approximation contract — the inductive invariant that powers `cliffordTCompile_correct`. Unconditional
(no tracked Props) for the constructive base finder. -/
theorem cliffordTCompile_loop_invariant :
    SkApproxCSuperQuadraticBound_generic K_compose cliffordTGeneratingSet
      cliffordTBaseFinder_constructive :=
  SkApproxCSuperQuadraticBound_generic_holds cliffordTGeneratingSet
    cliffordTBaseFinder_constructive
    cliffordTBaseFinder_constructive_approximates_within_two_ε₀

/-- **Correct-by-construction compiler theorem (CompCert for Clifford+T).** For every target
`U ∈ SU(2)` and precision `ε ∈ (0, ε₀]`, the output `cliffordTCompile U ε` satisfies, as a single
theorem about the compilation *algorithm*:

  - **error**: `‖ρ_CliffT (cliffordTCompile U ε) − U‖ ≤ ε`;
  - **recursion-level length**: `skLength (skLevel_polylog ε) ≤ skLengthConst·(log 1/ε)^skLengthExponent`;
  - **output-word length**: `(cliffordTCompile U ε).toWord.length ≤ skLength_at_baseCase
    cliffordTFiniteCover_maxLength (skLevel_polylog ε)`.

Every output provably meets its ε/length spec — not a per-output certification. Unconditional,
kernel-only. -/
theorem cliffordTCompile_correct
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ) (hε_pos : 0 < ε) (hε_le : ε ≤ ε₀) :
    ‖((cliffordTGeneratingSet.ρ_hom (cliffordTCompile U ε) :
          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε ∧
      skLength (skLevel_polylog ε) ≤
        skLengthConst * (Real.log (1 / ε)) ^ skLengthExponent ∧
      ((cliffordTCompile U ε).toWord.length : ℝ)
        ≤ skLength_at_baseCase (cliffordTFiniteCover_maxLength : ℝ) (skLevel_polylog ε) :=
  solovayKitaev_dawson_nielsen_quantitative_cliffordT_strict_concrete_constructive_unconditional
    U ε hε_pos hε_le

/-- **Worked instantiation.** The compiler-correctness contract instantiated at the identity target
and precision `ε = ε₀`: a concrete operating point witnessing that `cliffordTCompile_correct` is
non-vacuous. -/
theorem cliffordTCompile_correct_example :
    ‖((cliffordTGeneratingSet.ρ_hom (cliffordTCompile 1 ε₀) :
          ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) -
        ((1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤ ε₀ ∧
      skLength (skLevel_polylog ε₀) ≤
        skLengthConst * (Real.log (1 / ε₀)) ^ skLengthExponent ∧
      ((cliffordTCompile 1 ε₀).toWord.length : ℝ)
        ≤ skLength_at_baseCase (cliffordTFiniteCover_maxLength : ℝ) (skLevel_polylog ε₀) :=
  cliffordTCompile_correct 1 ε₀ ε₀_pos (le_refl ε₀)

end SKEFTHawking.FKLW.GenericSU2
