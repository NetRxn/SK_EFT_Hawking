/-
Phase 6p Wave 2c.4a-R4.2.d.R5.4 Layer E: final density composition.

## What this module ships

The conditional Fibonacci density theorem composed from all R5.4 Cartan
layers. Takes the IFT-based "exp image lands in H_Fib" hypothesis and
produces `DenseInSpecialUnitary 3 2 ρ_Fib_SU2`.

**Tier 1 substrate (this commit, ~60 LoC)**:

  - **`fibonacci_density_from_exp_image_subset`** (HEADLINE):
    If there exists an open `U ⊆ Matrix _ _ ℂ` with `0 ∈ U` such that
    every SU(2)-element whose underlying matrix is in `exp '' U` is in
    H_Fib, then `DenseInSpecialUnitary 3 2 ρ_Fib_SU2`.

    Direct composition of three shipped components:
    1. `SU2InteriorBridge.H_Fib_closure_eq_univ_from_subset_exp_image`
       (Cartan-D): exp-image hypothesis → closure(H_Fib) = univ.
    2. `H_Fib_eq_top_iff_closure_eq_univ`: closure = univ → H_Fib = ⊤.
    3. `fibonacci_density_from_H_Fib_eq_top`: H_Fib = ⊤ → density.

**This closes the chain MODULO the BCH-spanning hypothesis**: the
remaining substantive content is producing the witness `U` whose
exp-image is in H_Fib. That uses shipped substrate (D.3.h + D.3.i.1 +
D.2.c + D.3.{e,f,g}).

**Pipeline Invariant compliance**:
  - #10 (no `maxHeartbeats`): RESPECTED.
  - #15 (no new project-local axioms): RESPECTED.
  - ADR-003 (zero sorry): RESPECTED.
-/

import Mathlib
import SKEFTHawking.FKLW.SU2InteriorBridge
import SKEFTHawking.FKLW.FibSU2Density

set_option autoImplicit false

namespace SKEFTHawking.FKLW.FibonacciDensityConditional

open Matrix Complex NormedSpace

/-- **HEADLINE — Fibonacci density from exp-image subset hypothesis**.

If there exists an open `U ⊆ Matrix (Fin 2) (Fin 2) ℂ` with `0 ∈ U`
such that every SU(2)-element whose underlying matrix is in `exp '' U`
belongs to H_Fib, then the Fibonacci representation `ρ_Fib_SU2` is
DENSE in SU(2).

This is the **final composition** of all R5.4 Cartan layers:
  - Cartan-A `SU2LieAlgebra`: 𝔰𝔲(2) substrate.
  - Cartan-B `SU2MatrixExp`: exp(skew-Hermitian) ∈ unitaryGroup.
  - Cartan-C `SU2LocalDiffeo`: IFT applied to exp at 0.
  - Cartan-D `SU2InteriorBridge`: composition bridge to closure-eq-univ.
  - Layer E (this): + `H_Fib_eq_top_iff_closure_eq_univ` +
    `fibonacci_density_from_H_Fib_eq_top` (both shipped).

The remaining substantive content is the BCH-spanning hypothesis,
provable via shipped substrate (D.3.h + D.3.i.1 + D.2.c + D.3.{e,f,g})
in a multi-session Layer F follow-on. -/
theorem fibonacci_density_from_exp_image_subset
    (h_open_witness :
      ∃ U : Set (Matrix (Fin 2) (Fin 2) ℂ), IsOpen U ∧
        (0 : Matrix (Fin 2) (Fin 2) ℂ) ∈ U ∧
        ∀ (g : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)),
          (g : Matrix (Fin 2) (Fin 2) ℂ) ∈
            (NormedSpace.exp : Matrix (Fin 2) (Fin 2) ℂ →
                                Matrix (Fin 2) (Fin 2) ℂ) '' U →
          g ∈ SKEFTHawking.FKLW.H_Fib) :
    SKEFTHawking.FKLW.AharonovAradBridge.DenseInSpecialUnitary 3 2
      (fun b => (SKEFTHawking.FKLW.ρ_Fib_SU2 b : Matrix (Fin 2) (Fin 2) ℂ)) := by
  -- Step 1: Cartan-D yields closure (H_Fib : Set _) = univ
  have h_closure :=
    SKEFTHawking.FKLW.SU2InteriorBridge.H_Fib_closure_eq_univ_from_subset_exp_image
      h_open_witness
  -- Step 2: bridge to H_Fib = ⊤ via H_Fib_eq_top_iff_closure_eq_univ
  have h_top : SKEFTHawking.FKLW.H_Fib = ⊤ := by
    rw [SKEFTHawking.FKLW.H_Fib_eq_top_iff_closure_eq_univ]
    -- Need: closure (Set.range ρ_Fib_SU2) = univ
    -- We have:  closure ((H_Fib : Subgroup _) : Set _) = univ
    -- H_Fib := (ρ_Fib_SU2.range).topologicalClosure;
    -- so (H_Fib : Set _) = closure (Set.range ρ_Fib_SU2)
    have h_coe : (SKEFTHawking.FKLW.H_Fib :
        Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) =
        closure (Set.range SKEFTHawking.FKLW.ρ_Fib_SU2) := by
      unfold SKEFTHawking.FKLW.H_Fib
      rw [Subgroup.topologicalClosure_coe, SKEFTHawking.FKLW.ρ_Fib_SU2.coe_range]
    rw [h_coe] at h_closure
    -- h_closure : closure (closure (range ρ_Fib_SU2)) = univ
    rw [closure_closure] at h_closure
    exact h_closure
  -- Step 3: apply fibonacci_density_from_H_Fib_eq_top
  exact SKEFTHawking.FKLW.fibonacci_density_from_H_Fib_eq_top h_top

end SKEFTHawking.FKLW.FibonacciDensityConditional
