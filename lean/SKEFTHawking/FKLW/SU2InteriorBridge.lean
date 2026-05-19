/-
Phase 6p Wave 2c.4a-R4.2.d.R5.4 Layer Cartan-D: composition layer
bridging IFT-derived local-diffeo to subgroup closure-equals-universe.

## What this module ships

This is the **architectural bridge** between (i) the IFT/exp local-diffeo
substrate (Layers Cartan-A, B, C) and (ii) the topological closure
theorem (`closure_eq_univ_of_one_mem_interior` from
`AharonovAradBridgeIteration.lean`).

**Tier 1 substrate (this commit, ~100 LoC)**:

  - **`closure_eq_univ_from_subset_exp_image`** (HEADLINE):
    If `H` is a Subgroup of `SU(2)` such that for some open `U ∋ 0` in
    `Matrix _ _ ℂ`, every SU(2)-element whose underlying matrix is in
    `exp '' U` belongs to H, then `closure (H : Set _) = univ` in the
    SU(2) subtype topology.

  The proof composes:
    - Cartan-C `expAmbient_image_nhds_zero_subset_nhds_one`:
      `∃ V ∈ 𝓝(1) in Matrix _, V ⊆ exp '' U`.
    - Continuity of `Subtype.val : SU(2) → Matrix _` to pull back V
      into a nbhd of 1 in SU(2).
    - The hypothesis collapses the nbhd into a subset of H.
    - `mem_interior_iff_mem_nhds`: a set containing a nbhd of 1 has 1
      in its interior.
    - `closure_eq_univ_of_one_mem_interior` applied to H.

**The remaining substantive content** (Layer Cartan-E, multi-session):
prove the hypothesis `exp '' U ∩ SU(2) ⊆ H_Fib` for some open `U ∋ 0`
via the BCH-spanning iteration argument using shipped substrate:
  - D.3.h `H_Fib_small_pair_with_distinct_conjugate` (small witnesses)
  - D.3.i.1 `H_Fib_iteration_sequence` (geometric scale shrinkage)
  - D.2.c cubic Lie linearization
  - D.3.{e,f,g} dispersion + non-scalar (3 directions)

**Pipeline Invariant compliance**:
  - #10 (no `maxHeartbeats`): RESPECTED.
  - #15 (no new project-local axioms): RESPECTED.
  - ADR-003 (zero sorry): RESPECTED.
-/

import Mathlib
import SKEFTHawking.FKLW.SU2LocalDiffeo
import SKEFTHawking.FKLW.FibSU2Density
import SKEFTHawking.FKLW.AharonovAradBridgeIteration

set_option autoImplicit false

namespace SKEFTHawking.FKLW.SU2InteriorBridge

open Matrix Complex NormedSpace Filter Topology

attribute [local instance] Matrix.linftyOpNormedAddCommGroup
  Matrix.linftyOpNormedRing
  Matrix.linftyOpNormedAlgebra

/-! ## §1. Conditional bridge — the architectural composition

The bridge from "exp image lands in H" to "closure H = univ". -/

/-- **Conditional bridge: from `exp '' U` SU(2)-elements ⊆ H to closure-eq-univ**.

If H is a Subgroup of SU(2) and there exists an open `U ⊆ Matrix _ _ ℂ`
with 0 ∈ U such that every SU(2)-element whose underlying matrix lies in
`exp '' U` is in H, then `closure (H : Set _) = univ` (in SU(2) subtype
topology).

Proof: composes IFT (Cartan-C) + Subtype.val continuity + the hypothesis
to land 1 in interior of H, then applies `closure_eq_univ_of_one_mem_interior`. -/
theorem closure_eq_univ_from_subset_exp_image
    (H : Subgroup ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))
    (h_open_witness :
      ∃ U : Set (Matrix (Fin 2) (Fin 2) ℂ), IsOpen U ∧
        (0 : Matrix (Fin 2) (Fin 2) ℂ) ∈ U ∧
        ∀ (g : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)),
          (g : Matrix (Fin 2) (Fin 2) ℂ) ∈
            (NormedSpace.exp : Matrix (Fin 2) (Fin 2) ℂ →
                                Matrix (Fin 2) (Fin 2) ℂ) '' U →
          g ∈ H) :
    closure (H : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) = Set.univ := by
  obtain ⟨U, hU_open, hU_zero, hU_in_H⟩ := h_open_witness
  -- Step 1: get V ∈ 𝓝(1) in Matrix with V ⊆ exp '' U (Cartan-C IFT)
  have hU_nhds : U ∈ nhds (0 : Matrix (Fin 2) (Fin 2) ℂ) :=
    hU_open.mem_nhds hU_zero
  obtain ⟨V, hV_nhds, hV_sub⟩ :=
    SU2LocalDiffeo.expAmbient_image_nhds_zero_subset_nhds_one hU_nhds
  -- Step 2: pull back V via Subtype.val to nbhd of 1 in SU(2)
  have h_val_one : (Subtype.val (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :
      Matrix (Fin 2) (Fin 2) ℂ) = 1 := rfl
  have hV_pullback : (Subtype.val ⁻¹' V :
      Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∈
      nhds (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) := by
    have h_cont_at : ContinuousAt
      (Subtype.val : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ) →
        Matrix (Fin 2) (Fin 2) ℂ) 1 :=
      continuous_subtype_val.continuousAt
    have h_V_nhds_val : V ∈ nhds (Subtype.val (1 :
        ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) : Matrix _ _ ℂ) := by
      rw [h_val_one]; exact hV_nhds
    exact h_cont_at h_V_nhds_val
  -- Step 3: Subtype.val ⁻¹' V ⊆ H (using hypothesis + V ⊆ exp '' U)
  have h_sub_H : (Subtype.val ⁻¹' V :
      Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ⊆ (H : Set _) := by
    intro g hg_V
    apply hU_in_H g
    exact hV_sub hg_V
  -- Step 4: H ∈ nhds 1 (since H ⊇ Subtype.val ⁻¹' V ∈ nhds 1)
  have hH_nhds : (H : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∈
      nhds (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :=
    Filter.mem_of_superset hV_pullback h_sub_H
  -- Step 5: 1 ∈ interior H (via mem_interior_iff_mem_nhds)
  have h_one_in_int : (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∈
      interior (H : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) :=
    mem_interior_iff_mem_nhds.mpr hH_nhds
  -- Step 6: 1 ∈ interior (closure H) (since interior H ⊆ interior (closure H))
  have h_one_in_int_closure : (1 : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) ∈
      interior (closure (H : Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ))) :=
    interior_mono subset_closure h_one_in_int
  -- Step 7: apply closure_eq_univ_of_one_mem_interior
  exact SKEFTHawking.FKLW.AharonovAradBridge.closure_eq_univ_of_one_mem_interior
    H h_one_in_int_closure

/-! ## §2. Specialization for H_Fib + downstream density

If the IFT-image hypothesis holds for H_Fib specifically, the chain closes
all the way to `DenseInSpecialUnitary 3 2 ρ_Fib_SU2`. -/

/-- **H_Fib density from exp-image hypothesis**: if `H_Fib` contains all
SU(2)-elements whose matrix is in `exp '' U` for some open `U ∋ 0`, then
`closure (H_Fib : Set _) = univ` (equivalently `H_Fib = ⊤` as Subgroup
and Fibonacci density holds). -/
theorem H_Fib_closure_eq_univ_from_subset_exp_image
    (h_open_witness :
      ∃ U : Set (Matrix (Fin 2) (Fin 2) ℂ), IsOpen U ∧
        (0 : Matrix (Fin 2) (Fin 2) ℂ) ∈ U ∧
        ∀ (g : ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)),
          (g : Matrix (Fin 2) (Fin 2) ℂ) ∈
            (NormedSpace.exp : Matrix (Fin 2) (Fin 2) ℂ →
                                Matrix (Fin 2) (Fin 2) ℂ) '' U →
          g ∈ SKEFTHawking.FKLW.H_Fib) :
    closure ((SKEFTHawking.FKLW.H_Fib : Subgroup _) :
        Set ↥(Matrix.specialUnitaryGroup (Fin 2) ℂ)) = Set.univ :=
  closure_eq_univ_from_subset_exp_image SKEFTHawking.FKLW.H_Fib h_open_witness

/-! ## §3. Module summary

`SU2InteriorBridge.lean` (Phase 6p Wave 2c.4a-R4.2.d.R5.4 Layer Cartan-D,
session 38): the architectural composition layer.

**Shipped (zero new axioms)**:

  - **§1**: `closure_eq_univ_from_subset_exp_image` — the conditional
    bridge from `exp '' U ⊆ H` to `closure H = univ`. Composes Cartan-C
    IFT + Subtype.val continuity + `mem_interior_iff_mem_nhds` +
    `closure_eq_univ_of_one_mem_interior`.

  - **§2**: `H_Fib_closure_eq_univ_from_subset_exp_image` —
    consumer-friendly specialization to H_Fib.

**Substrate downstream**:

  - **Cartan-E (multi-session)**: prove the substantive hypothesis
    `exp '' U ⊆ H_Fib` via the BCH-spanning iteration argument using
    shipped substrate (D.3.h + D.3.i.1 + D.2.c + D.3.{e,f,g}).

  - **Layer E (final)**: trivial composition with
    `fibonacci_density_from_H_Fib_eq_top` (already shipped).
-/

end SKEFTHawking.FKLW.SU2InteriorBridge
