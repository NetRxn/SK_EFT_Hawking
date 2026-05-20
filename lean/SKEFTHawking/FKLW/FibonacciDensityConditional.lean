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

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

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

/-! ## §2. Consumer-friendly variant — Fibonacci density from H_Fib
having a SU(2)-nbhd of 1 (R5.4 Layer F.20.c.d.2.e)

Often the downstream consumer wants to feed the IFT hypothesis in
its SU(2)-subtype form ("H_Fib contains a nbhd of 1 in SU(2)") rather
than the ambient-`exp`-image form. This section provides that bridge:
the subtype-topology hypothesis is reduced to the ambient hypothesis
via continuity of `Subtype.val` + matrix `exp` continuity at 0.

This makes downstream work (e.g., Cartan-classification-based density
proofs) plug-in compatible with `fibonacci_density_from_exp_image_subset`
without forcing the consumer to manually navigate the
`Subtype.val ↔ Matrix _ _ ℂ` translation. -/

/-- **R5.4 Layer F.20.c.d.2.e — Fibonacci density from H_Fib-open-at-1**.

If there exists an open neighborhood `V ⊆ SU(2)` of `(1 : SU(2))` (in the
subtype topology) such that `V ⊆ H_Fib`, then `DenseInSpecialUnitary 3 2
ρ_Fib_SU2`.

Proof outline:
  1. From the hypothesis, get `V open ⊆ SU(2)`, `1 ∈ V`, `V ⊆ H_Fib`.
  2. By `Topology.IsInducing.subtypeVal`, `V = Subtype.val ⁻¹' V'` for
     some `V' open ⊆ Matrix _ _ ℂ` with `1 ∈ V'`.
  3. `exp : Matrix _ _ ℂ → Matrix _ _ ℂ` is continuous at 0 with `exp 0 = 1`,
     so `exp ⁻¹' V' ∈ nhds (0 : Matrix _ _ ℂ)`.
  4. Get open `U ⊆ exp ⁻¹' V'` with `0 ∈ U`.
  5. Apply `fibonacci_density_from_exp_image_subset` with this U.
     For `g ∈ SU(2)` with `g.val ∈ exp '' U`:
     - `g.val ∈ exp '' U ⊆ V'` (since `U ⊆ exp ⁻¹' V'`).
     - `g.val ∈ V' ⟹ g ∈ V` (since `V = Subtype.val ⁻¹' V'`).
     - `V ⊆ H_Fib ⟹ g ∈ H_Fib`. -/
theorem fibonacci_density_from_H_Fib_open_at_one
    (h_nhd : ∃ V ∈ nhds (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)),
      V ⊆ (SKEFTHawking.FKLW.H_Fib :
        Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))) :
    SKEFTHawking.FKLW.AharonovAradBridge.DenseInSpecialUnitary 3 2
      (fun b => (SKEFTHawking.FKLW.ρ_Fib_SU2 b :
        Matrix (Fin 2) (Fin 2) ℂ)) := by
  obtain ⟨V, hV_nhds, hV_sub_H⟩ := h_nhd
  -- Step 1: pull V back via Subtype.val to get V' open in ambient with V = Subtype.val ⁻¹' V'
  have h_inducing :
      Topology.IsInducing
        (Subtype.val : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) →
          Matrix (Fin 2) (Fin 2) ℂ) :=
    Topology.IsInducing.subtypeVal
  -- nhd of 1 in subtype = preimage of nhd of (1 : Matrix _ _ ℂ) via Subtype.val
  -- Specifically, ∃ V' ∈ nhds 1 (in Matrix), V = Subtype.val ⁻¹' V' (using IsInducing.nhds_eq_comap)
  rw [h_inducing.nhds_eq_comap, Filter.mem_comap] at hV_nhds
  obtain ⟨V', hV'_nhds, hV'_pre⟩ := hV_nhds
  -- Now: V' ∈ nhds (Subtype.val 1) = nhds (1 : Matrix) ; Subtype.val ⁻¹' V' ⊆ V
  -- The "1" in subtype, when pushed by Subtype.val, gives (1 : Matrix _ _ ℂ).
  have h_val_one_eq : (Subtype.val (1 :
      ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
        Matrix (Fin 2) (Fin 2) ℂ) = 1 := rfl
  rw [h_val_one_eq] at hV'_nhds
  -- Step 2: exp is continuous, with exp 0 = 1, so exp ⁻¹' V' ∈ nhds 0
  have h_exp_cont : Continuous
      (NormedSpace.exp : Matrix (Fin 2) (Fin 2) ℂ →
                                  Matrix (Fin 2) (Fin 2) ℂ) :=
    NormedSpace.exp_continuous
  have h_exp_zero : (NormedSpace.exp (0 : Matrix (Fin 2) (Fin 2) ℂ) :
      Matrix (Fin 2) (Fin 2) ℂ) = 1 := NormedSpace.exp_zero
  have hV'_nhds_exp : V' ∈ nhds
      (NormedSpace.exp (0 : Matrix (Fin 2) (Fin 2) ℂ)) := by
    rw [h_exp_zero]; exact hV'_nhds
  have h_pre_V' : (NormedSpace.exp ⁻¹' V' : Set (Matrix (Fin 2) (Fin 2) ℂ)) ∈
      nhds (0 : Matrix (Fin 2) (Fin 2) ℂ) :=
    h_exp_cont.tendsto 0 hV'_nhds_exp
  -- Step 3: find open U ⊆ exp ⁻¹' V' with 0 ∈ U
  obtain ⟨U, hU_sub, hU_open, hU_zero⟩ := mem_nhds_iff.mp h_pre_V'
  -- Step 4: apply fibonacci_density_from_exp_image_subset
  refine fibonacci_density_from_exp_image_subset ⟨U, hU_open, hU_zero, ?_⟩
  intro g hg
  -- Show g ∈ H_Fib
  -- hg : g.val ∈ exp '' U
  obtain ⟨x, hx_U, hx_exp⟩ := hg
  -- x ∈ U ⊆ exp ⁻¹' V', so exp x ∈ V'
  have hx_pre : x ∈ NormedSpace.exp ⁻¹' V' := hU_sub hx_U
  -- hx_pre : x ∈ exp ⁻¹' V' means exp x ∈ V'
  have h_exp_x_V' : NormedSpace.exp x ∈ V' := hx_pre
  -- Now g.val = exp x ∈ V'
  have h_g_val_V' : (g : Matrix (Fin 2) (Fin 2) ℂ) ∈ V' := by
    rw [← hx_exp]; exact h_exp_x_V'
  -- hV'_pre : Subtype.val ⁻¹' V' ⊆ V, so g ∈ V
  have h_g_V : g ∈ V := hV'_pre h_g_val_V'
  -- hV_sub_H : V ⊆ H_Fib
  exact hV_sub_H h_g_V

end SKEFTHawking.FKLW.FibonacciDensityConditional
