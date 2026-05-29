/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6z Wave 5 — the headline: literal Clifford+CCZ (no `T`) is dense in SU(8)

The culmination of Phase 6z: the **faithful, CCZ-essential** literal generating set
`{H_qi, S_qi, CNOT_ij, CCZ}` (no `T`-gate) is **dense in SU(8)**. The whole pipeline composes:

  * **Wave 1** — the von-Neumann/Kronecker irrational seed `seedSU8` has infinite order.
  * **Wave 2** — infinite order ⟹ accumulation point at `1` ⟹ a continuous one-parameter flow `X₀`
    inside `H_of_G` (`seedSU8_first_flow`), via the SU(d) von-Neumann 1-parameter-subgroup engine.
  * **Wave 4** — the Clifford-adjoint action on `𝔰𝔲(8)` is irreducible (`clifford_irreducible_spans`),
    so the Clifford orbit of the non-explicit seed tangent `X₀` spans `𝔰𝔲(8)` (`cliffOrbit_spans_su8`);
    every orbit element is a traceless skew-Hermitian tangent carrying a flow (`CliffordCCZSU8OrbitProps`).
  * **Wave 5 (here)** — a finite spanning subfamily of the orbit
    (`Submodule.subset_span_finite_of_subset_span`) assembles a `ClosureDenseWitness`, which the
    unconditional SU(d) Cartan closed-subgroup discharge (`CartanFinalStep_SUd_v4_holds`,
    `H_of_G_eq_top_of_witness`) turns into `H_of_G = ⊤`, hence density.

Headlines:

  * `cliffordCCZLiteral_H_of_G_eq_top` — `H_of_G cliffordCCZLiteralGeneratingSetSU8 = ⊤`.
  * `cliffordCCZLiteral_dense` — `IsDenseInSUd_gs cliffordCCZLiteralGeneratingSetSU8`: every `U ∈ SU(8)`
    is approximated to arbitrary precision by a word in `{H_qi, S_qi, CNOT_ij, CCZ}`.

`CCZ` is the essential non-Clifford resource: `⟨H, S, CNOT⟩` alone is the finite 3-qubit Clifford group;
density comes from the global irrational-angle seed `H₁H₂H₃·CCZ`, not from any per-qubit dense subgroup
(contrast Phase 6y's universal Clifford+`T`).

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected. Kernel-pure.

## Phase 6z provenance

Phase 6z Wave 5 (density headline). 2026-05-29.
-/

import Mathlib
import SKEFTHawking.FKLW.CliffordCCZSU8OrbitProps
import SKEFTHawking.FKLW.GenericSUdDischargeUnconditional
import SKEFTHawking.FKLW.SU2LieAlgebra

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix SKEFTHawking.FKLW.GenericSUd SKEFTHawking.FKLW.SU2LieAlgebra

/-- Reindex a `Finset`-indexed ℝ-linear combination as a `Fin T.card` combination with complexified
coefficients (the `ClosureDenseWitness.hX_spans` shape). -/
theorem cliffOrbit_sum_reindex (T : Finset (Matrix (Fin 8) (Fin 8) ℂ))
    (f : Matrix (Fin 8) (Fin 8) ℂ → ℝ) :
    (∑ a ∈ T, f a • a)
      = ∑ i : Fin T.card, ((f ((T.equivFin.symm i : ↥T) : Matrix (Fin 8) (Fin 8) ℂ) : ℝ) : ℂ) •
          ((T.equivFin.symm i : ↥T) : Matrix (Fin 8) (Fin 8) ℂ) := by
  have key : (∑ a ∈ T, f a • a)
      = ∑ i : Fin T.card, f ((T.equivFin.symm i : ↥T) : Matrix (Fin 8) (Fin 8) ℂ) •
          ((T.equivFin.symm i : ↥T) : Matrix (Fin 8) (Fin 8) ℂ) := by
    rw [Equiv.sum_comp T.equivFin.symm
      (fun m : ↥T => f (m : Matrix (Fin 8) (Fin 8) ℂ) • (m : Matrix (Fin 8) (Fin 8) ℂ))]
    exact (Finset.sum_attach T (fun a => f a • a)).symm
  rw [key]
  exact Finset.sum_congr rfl (fun i _ => (Complex.coe_smul _ _).symm)

/-- **The `ClosureDenseWitness` for the literal Clifford+CCZ generating set.** Built from the seed flow
`X₀` (Wave 2), a finite spanning subfamily of its Clifford orbit (Wave 4 irreducibility), each carrying a
flow line in `H_of_G` (`CliffordCCZSU8OrbitProps`). -/
theorem witness_nonempty : Nonempty (ClosureDenseWitness cliffordCCZLiteralGeneratingSetSU8) := by
  obtain ⟨X0, hX0_ts, hX0_ne, hX0_flow⟩ := seedSU8_first_flow
  rw [tracelessSkewHermitian_mem_iff] at hX0_ts
  obtain ⟨hX0skew, hX0tr⟩ := hX0_ts
  -- A finite subfamily of the Clifford orbit that still spans 𝔰𝔲(8).
  have hfin : ∃ T : Finset (Matrix (Fin 8) (Fin 8) ℂ), ↑T ⊆ cliffOrbitSet X0 ∧
      ∀ Y : Matrix (Fin 8) (Fin 8) ℂ, Y.IsSkewHermitian → Y.trace = 0 →
        Y ∈ Submodule.span ℝ (↑T : Set (Matrix (Fin 8) (Fin 8) ℂ)) := by
    have hS63_sub :
        ((Finset.image suEightTangent Finset.univ : Finset (Matrix (Fin 8) (Fin 8) ℂ)) :
          Set (Matrix (Fin 8) (Fin 8) ℂ)) ⊆ ↑(Submodule.span ℝ (cliffOrbitSet X0)) := by
      intro m hm
      rw [Finset.coe_image, Set.mem_image] at hm
      obtain ⟨j, _, rfl⟩ := hm
      exact cliffOrbit_spans_su8 X0 hX0_ne hX0skew hX0tr (suEightTangent j)
        (suEightTangent_isSkewHermitian j) (suEightTangent_trace_zero j)
    obtain ⟨T, hT_sub, hS63_subT⟩ := Submodule.subset_span_finite_of_subset_span hS63_sub
    refine ⟨T, hT_sub, fun Y hYs hYt => ?_⟩
    obtain ⟨c, hc⟩ := suEightTangent_spans Y hYs hYt
    rw [hc]
    refine Submodule.sum_mem _ (fun j _ => Submodule.smul_mem _ _ (hS63_subT ?_))
    rw [Finset.coe_image, Set.mem_image]; exact ⟨j, Finset.mem_univ j, rfl⟩
  obtain ⟨T, hT_sub, hTspans⟩ := hfin
  refine ⟨{
    n := T.card
    X := fun i => ((T.equivFin.symm i : ↥T) : Matrix (Fin 8) (Fin 8) ℂ)
    hX_in_sud := fun i => ⟨cliffOrbit_mem_skew X0 hX0skew _ (hT_sub (T.equivFin.symm i).2),
      cliffOrbit_mem_trace X0 hX0tr _ (hT_sub (T.equivFin.symm i).2)⟩
    hX_flow := fun i => cliffOrbit_mem_flow X0 hX0_flow _ (hT_sub (T.equivFin.symm i).2)
    hX_spans := fun Y hYs hYt => ?_ }⟩
  obtain ⟨f, _hsupp, hf⟩ := Submodule.mem_span_finset.mp (hTspans Y hYs hYt)
  exact ⟨fun i => f ((T.equivFin.symm i : ↥T) : Matrix (Fin 8) (Fin 8) ℂ),
    hf ▸ cliffOrbit_sum_reindex T f⟩

/-- **Phase 6z headline (top-subgroup form)**: the literal Clifford+CCZ (no-`T`) closure subgroup is all
of SU(8). Composes the witness with the unconditional SU(d) Cartan closed-subgroup discharge. -/
theorem cliffordCCZLiteral_H_of_G_eq_top :
    H_of_G cliffordCCZLiteralGeneratingSetSU8 = ⊤ := by
  obtain ⟨w⟩ := witness_nonempty
  exact H_of_G_eq_top_of_witness (by norm_num) w

/-- **Phase 6z headline (density form)**: the literal Clifford+CCZ (no-`T`) generating set is dense in
SU(8) — every `U ∈ SU(8)` is approximated to arbitrary precision by a word in `{H_qi, S_qi, CNOT_ij, CCZ}`.
`CCZ` is the essential non-Clifford resource (the Clifford subgroup alone is finite); density arises from
the global irrational-angle seed, with no per-qubit dense subgroup. -/
theorem cliffordCCZLiteral_dense : IsDenseInSUd_gs cliffordCCZLiteralGeneratingSetSU8 := by
  obtain ⟨w⟩ := witness_nonempty
  exact densityFromWitness (by norm_num) w

end SKEFTHawking.FKLW.CliffordCCZSU8
