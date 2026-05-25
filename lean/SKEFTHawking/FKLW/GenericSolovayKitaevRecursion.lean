/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6u Wave 4 — Generic Solovay-Kitaev recursion engine

Generalizes the Phase 6t Path A Option C constructive Dawson-Nielsen
Solovay-Kitaev compiler (`SolovayKitaevPathA.skApproxC` + its
unconditional super-quadratic discharge `SkApproxCSuperQuadraticBound_holds`)
to arbitrary `GeneratingSet`s.

## Headline definitions

  * `dnStepFG_su2 V_n U` — alphabet-agnostic version of `dnStepFG`. Takes
    the V_n SU(2) value directly (instead of as a braid word). Body is
    structurally identical, ensuring `dnStepFG V_n_braid U` ≡
    `dnStepFG_su2 (ρ_Fib_SU2 V_n_braid) U`.

  * `skApproxC_generic gs baseFinder : ℕ → SU(2) → gs.W` — the
    parametric SK recursion. Takes a `baseFinder : SU(2) → gs.W`
    parameter for the level-0 ε₀-net approximator.

  * `SkApproxCSuperQuadraticBound_generic K gs baseFinder : Prop` — the
    parametric super-quadratic error bound predicate.

  * `SkApproxCSuperQuadraticBound_generic_fibonacci` — validation:
    at the Fibonacci instance with the Fibonacci ε₀-net base finder,
    the generic predicate REDUCES DEFINITIONALLY to Phase 6t's
    `SkApproxCSuperQuadraticBound`, and the existing
    `SkApproxCSuperQuadraticBound_holds` discharges it.

## Wave 4a / Wave 4b split

This file ships Wave 4a (definitions + Fibonacci bridge). The substantive
**generic discharge** (analog of Phase 6t Path A Option C's ~981-LoC
`SkApproxCSuperQuadraticBound_holds`, parametrized over `gs`) is shipped
in `GenericSolovayKitaevRecursionDischarge.lean` (Wave 4b).

The Wave 4a Fibonacci-bridge approach is non-trivial: it observes that for
the Fibonacci instance (with the Fibonacci base finder), the generic
recursion reduces to Phase 6t's existing `skApproxC`, so Phase 6t's
discharge becomes the Fibonacci-instance generic discharge.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new axioms): respected.
- **Strengthening discipline**: `dnStepFG_su2` makes alphabet-agnostic
  what was previously bundled with the BraidGroup-typed Fibonacci API;
  the equality with `dnStepFG` makes the abstraction LOAD-BEARING. The
  generic recursion is non-trivial. The generic predicate is non-vacuous
  (Fibonacci instance discharges it via Phase 6t).

-/

import SKEFTHawking.FKLW.GenericEpsilonNet
import SKEFTHawking.FKLW.SolovayKitaevPathA
import SKEFTHawking.FKLW.SolovayKitaevRecursion

set_option autoImplicit false

namespace SKEFTHawking.FKLW.GenericSU2

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

open Matrix SKEFTHawking SKEFTHawking.FKLW
  SKEFTHawking.FKLW.SU2BalancedCommutator
  SKEFTHawking.FKLW.FibonacciEpsilonNet
  SKEFTHawking.FKLW.SolovayKitaevRecursion
  SKEFTHawking.FKLW.SolovayKitaevLengthBound
  SKEFTHawking.FKLW.OneParameterSubgroupSU2
  SKEFTHawking.FKLW.SolovayKitaevPathA

/-! ## 1. Alphabet-agnostic Dawson-Nielsen step

`dnStepFG_su2` takes V_n as a SU(2) value (not a braid word), exposing
the alphabet-agnostic SU(2)-geometric content of one Dawson-Nielsen step.
The body matches Phase 6t Path A's `dnStepFG` after the initial
`V_n := ρ_Fib_SU2 V_n_braid` evaluation. -/

/-- **Alphabet-agnostic Dawson-Nielsen F, G extraction**.

Takes V_n directly as a `↥SU(2)` value. Used by `skApproxC_generic` to
extract the (F, G) pair for any GeneratingSet's level-(n+1) composition
step.

By design, `dnStepFG V_n_braid U = dnStepFG_su2 (ρ_Fib_SU2 V_n_braid) U`
definitionally (both bodies coincide once V_n is evaluated). -/
noncomputable def dnStepFG_su2
    (V_n : ↥(specialUnitaryGroup (Fin 2) ℂ))
    (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) : DNStepData :=
  let Δ : ↥(specialUnitaryGroup (Fin 2) ℂ) := V_n⁻¹ * U
  let H : Matrix (Fin 2) (Fin 2) ℂ := ((-Complex.I) : ℂ) • Y_h Δ.val
  let θ : ℝ := ‖H‖
  if h : 0 < θ ∧ θ ≤ 1 then
    let H_unit : Matrix (Fin 2) (Fin 2) ℂ := ((1 / θ : ℝ) : ℂ) • H
    let hH_herm : H.IsHermitian := neg_I_smul_Y_h_isHermitian Δ.property
    let hH_tr : H.trace = 0 := neg_I_smul_Y_h_trace_zero Δ.property
    let hH_unit_herm : H_unit.IsHermitian :=
      IsHermitian_real_smul hH_herm (1 / θ)
    let hH_unit_tr : H_unit.trace = 0 := smul_trace_zero hH_tr _
    let hH_unit_norm : ‖H_unit‖ = 1 := norm_normalize h.1
    let ex := balanced_commutator_general_axis_lie_traceless
                H_unit hH_unit_herm hH_unit_tr hH_unit_norm θ h.1.le h.2
    { F := ex.choose
      G := ex.choose_spec.choose
      hF_herm := ex.choose_spec.choose_spec.1
      hG_herm := ex.choose_spec.choose_spec.2.1
      hF_tr := ex.choose_spec.choose_spec.2.2.1
      hG_tr := ex.choose_spec.choose_spec.2.2.2.1 }
  else
    { F := 0, G := 0
      hF_herm := Matrix.isHermitian_zero
      hG_herm := Matrix.isHermitian_zero
      hF_tr := Matrix.trace_zero (Fin 2) ℂ
      hG_tr := Matrix.trace_zero (Fin 2) ℂ }

/-- **Compatibility with Phase 6t `dnStepFG`**: at the Fibonacci instance,
`dnStepFG_su2 (ρ_Fib_SU2 V_n_braid) U` reduces to `dnStepFG V_n_braid U`.

Holds by definitional unfolding (`rfl`); the equality is the Phase 6u
bridge invariant by construction (`dnStepFG_su2`'s body is structurally
identical to `dnStepFG`'s body after the initial
`V_n := ρ_Fib_SU2 V_n_braid` evaluation step). This rfl is load-bearing
for `skApproxC_generic_fibonacci_eq` (the structural induction reducing
the generic recursion at the Fibonacci instance to Phase 6t's recursion). -/
theorem dnStepFG_su2_eq_dnStepFG
    (V_n_braid : FibonacciBraidWord)
    (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) :
    dnStepFG_su2 (ρ_Fib_SU2 V_n_braid) U = dnStepFG V_n_braid U := by
  rfl

/-! ## 2. The generic Solovay-Kitaev recursion `skApproxC_generic`

Parametric over a `GeneratingSet gs` and a base-case finder
`baseFinder : ↥SU(2) → gs.W`. -/

/-- **Generic constructive Dawson-Nielsen Solovay-Kitaev recursion**.

For every level `n` and target `U ∈ SU(2)`, `skApproxC_generic gs baseFinder n U`
returns a word in `gs.W` constructed as a level-n Dawson-Nielsen composition.

  - Level 0: the base-case approximation via `baseFinder`.
  - Level (n+1): the visible composition
    `V_n_word · groupCommutator (skApproxC_generic n A_F) (skApproxC_generic n A_G)`
    where F, G are the traceless balanced commutator decomposition
    of the residual matrix log (via `dnStepFG_su2`).

For the Fibonacci instance with `baseFinder := fun U => fibonacciEpsilonNet_findNearest U ε₀ ε₀_pos`,
this reduces DEFINITIONALLY to `SolovayKitaevPathA.skApproxC`. -/
noncomputable def skApproxC_generic
    (gs : GeneratingSet) (baseFinder : ↥(specialUnitaryGroup (Fin 2) ℂ) → gs.W) :
    ℕ → ↥(specialUnitaryGroup (Fin 2) ℂ) → gs.W
  | 0, U => baseFinder U
  | n + 1, U =>
    let V_n_word : gs.W := skApproxC_generic gs baseFinder n U
    let V_n_SU2 : ↥(specialUnitaryGroup (Fin 2) ℂ) := gs.ρ_hom V_n_word
    let data : DNStepData := dnStepFG_su2 V_n_SU2 U
    let A_F : ↥(specialUnitaryGroup (Fin 2) ℂ) :=
      expIsu2 data.F data.hF_herm data.hF_tr
    let A_G : ↥(specialUnitaryGroup (Fin 2) ℂ) :=
      expIsu2 data.G data.hG_herm data.hG_tr
    let A_F_word : gs.W := skApproxC_generic gs baseFinder n A_F
    let A_G_word : gs.W := skApproxC_generic gs baseFinder n A_G
    V_n_word * (A_F_word * A_G_word * A_F_word⁻¹ * A_G_word⁻¹)

/-- Level-0 unfolding: base case is the supplied base finder. -/
lemma skApproxC_generic_zero
    (gs : GeneratingSet) (baseFinder : ↥(specialUnitaryGroup (Fin 2) ℂ) → gs.W)
    (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) :
    skApproxC_generic gs baseFinder 0 U = baseFinder U := rfl

/-- Level-(n+1) unfolding: the visible Dawson-Nielsen composition. -/
lemma skApproxC_generic_succ
    (gs : GeneratingSet) (baseFinder : ↥(specialUnitaryGroup (Fin 2) ℂ) → gs.W)
    (n : ℕ) (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) :
    skApproxC_generic gs baseFinder (n + 1) U =
      let V_n_word := skApproxC_generic gs baseFinder n U
      let data := dnStepFG_su2 (gs.ρ_hom V_n_word) U
      let A_F := expIsu2 data.F data.hF_herm data.hF_tr
      let A_G := expIsu2 data.G data.hG_herm data.hG_tr
      V_n_word *
        (skApproxC_generic gs baseFinder n A_F *
          skApproxC_generic gs baseFinder n A_G *
          (skApproxC_generic gs baseFinder n A_F)⁻¹ *
          (skApproxC_generic gs baseFinder n A_G)⁻¹) := rfl

/-! ## 3. The generic super-quadratic bound predicate

Parametric over `K`, `gs`, and `baseFinder`. The bound on `baseFinder`
itself (it ε₀-approximates U) is required to discharge the base case
in Wave 4b. -/

/-- **Base-case ε₀-approximation property** for a `baseFinder`. -/
def BaseFinder_approximates_within
    (gs : GeneratingSet) (baseFinder : ↥(specialUnitaryGroup (Fin 2) ℂ) → gs.W)
    (ε : ℝ) : Prop :=
  ∀ U : ↥(specialUnitaryGroup (Fin 2) ℂ),
    ‖((gs.ρ_hom (baseFinder U) : ↥(specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ < ε

/-- **Generic super-quadratic bound predicate**.

For every level `n` and every target `U ∈ SU(2)`,
`‖ρ_hom (skApproxC_generic n U) - U‖ ≤ ε_seq K (2·ε₀) n`. -/
def SkApproxCSuperQuadraticBound_generic
    (K : ℝ) (gs : GeneratingSet)
    (baseFinder : ↥(specialUnitaryGroup (Fin 2) ℂ) → gs.W) : Prop :=
  ∀ (n : ℕ) (U : ↥(specialUnitaryGroup (Fin 2) ℂ)),
    ‖((gs.ρ_hom (skApproxC_generic gs baseFinder n U) :
          ↥(specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) -
        (U : Matrix (Fin 2) (Fin 2) ℂ)‖ ≤
      SKEFTHawking.FKLW.EpsilonSeq.ε_seq K (2 * ε₀) n

/-! ## 4. Fibonacci instantiation

Validates that the generic substrate recovers Phase 6t Path A Option C
at the Fibonacci instance. The key observation: with the Fibonacci base
finder, `skApproxC_generic fibonacciGeneratingSet ...` reduces
DEFINITIONALLY to `SolovayKitaevPathA.skApproxC`. -/

/-- **The canonical Fibonacci base finder** (Phase 6t Wave 3 ε₀-net). -/
noncomputable def fibonacciBaseFinder
    (U : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) : BraidGroup 3 :=
  SKEFTHawking.FKLW.FibonacciEpsilonNet.fibonacciEpsilonNet_findNearest U ε₀ ε₀_pos

/-- **Fibonacci-instance reduction**: at the Fibonacci instance with the
Fibonacci base finder, `skApproxC_generic` equals Phase 6t's `skApproxC`. -/
theorem skApproxC_generic_fibonacci_eq
    (n : ℕ) (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) :
    skApproxC_generic fibonacciGeneratingSet fibonacciBaseFinder n U =
      SolovayKitaevPathA.skApproxC n U := by
  induction n generalizing U with
  | zero =>
    -- Both reduce to the Fibonacci ε₀-net.
    rfl
  | succ m ih =>
    rw [skApproxC_generic_succ]
    rw [SolovayKitaevPathA.skApproxC_succ]
    simp only [ih]
    -- After ih, the V_n_word, A_F, A_G are identical to Phase 6t's V_n_braid.
    -- Need: gs.ρ_hom = ρ_Fib_SU2 (definitional for fibonacciGeneratingSet).
    -- dnStepFG_su2 (ρ_Fib_SU2 ...) = dnStepFG ... by dnStepFG_su2_eq_dnStepFG.
    rfl

/-- **Fibonacci-instance super-quadratic bound discharge**.

At the Fibonacci instance with the Fibonacci base finder, the generic
super-quadratic predicate REDUCES DEFINITIONALLY (via
`skApproxC_generic_fibonacci_eq`) to Phase 6t's
`SkApproxCSuperQuadraticBound K_compose`, which is unconditionally
discharged by `SkApproxCSuperQuadraticBound_holds`. -/
theorem SkApproxCSuperQuadraticBound_generic_fibonacci :
    SkApproxCSuperQuadraticBound_generic K_compose
      fibonacciGeneratingSet fibonacciBaseFinder := by
  intro n U
  -- Goal: ‖ρ_Fib_SU2 (skApproxC_generic ...) - U‖ ≤ ε_seq K_compose (2·ε₀) n.
  rw [show
        skApproxC_generic fibonacciGeneratingSet fibonacciBaseFinder n U =
          SolovayKitaevPathA.skApproxC n U from
      skApproxC_generic_fibonacci_eq n U]
  -- Goal becomes: ‖ρ_Fib_SU2 (skApproxC n U) - U‖ ≤ ε_seq K_compose (2·ε₀) n
  exact SkApproxCSuperQuadraticBound_holds n U

/-! ## 5. Generic constructive compiler

Wraps `skApproxC_generic` at level `skLevel_polylog ε`, producing the
canonical constructive compiler API. -/

/-- **The Generic Path A constructive compiler**: returns a word in
`gs.W` whose UNDERLYING STRUCTURE is a level-`skLevel_polylog ε`
Dawson-Nielsen composition.

For the Fibonacci instance with the Fibonacci base finder, this reduces
DEFINITIONALLY to `solovayKitaev_compile_strict_constructive`. -/
noncomputable def solovayKitaev_compile_strict_constructive_generic
    (gs : GeneratingSet) (baseFinder : ↥(specialUnitaryGroup (Fin 2) ℂ) → gs.W)
    (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ) : gs.W :=
  skApproxC_generic gs baseFinder (skLevel_polylog ε) U

/-- Fibonacci-instance reduction of the generic compiler. -/
theorem solovayKitaev_compile_strict_constructive_generic_fibonacci_eq
    (U : ↥(specialUnitaryGroup (Fin 2) ℂ)) (ε : ℝ) :
    solovayKitaev_compile_strict_constructive_generic
      fibonacciGeneratingSet fibonacciBaseFinder U ε =
      solovayKitaev_compile_strict_constructive U ε := by
  unfold solovayKitaev_compile_strict_constructive_generic
        solovayKitaev_compile_strict_constructive
  exact skApproxC_generic_fibonacci_eq (skLevel_polylog ε) U

end SKEFTHawking.FKLW.GenericSU2
