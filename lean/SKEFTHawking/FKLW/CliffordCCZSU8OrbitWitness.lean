/-
Copyright (c) 2026 John Roehm. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: John Roehm

# Phase 6z Wave 4 increment 4h.1 — the Clifford orbit of the seed tangent spans 𝔰𝔲(8)

The Phase 6z `ClosureDenseWitness` needs a `𝔰𝔲(8)`-spanning family of tangents each carrying a flow line
in `H_of_G`. The seed tangent `X₀` (`seedSU8_first_flow`, a non-explicit Bolzano-Weierstrass limit) has a
flow, and so does every Clifford conjugate `R·X₀·R⁻¹` for `R ∈ H_of_G` (`flow_conj_mem`). This module
proves that the ℝ-span of the **Clifford orbit** of `X₀`,

  `cliffOrbitSet X₀ = {R·X₀·R⁻¹ : R ∈ H_of_G}`,

covers all of `𝔰𝔲(8)` — the `hX_spans` engine for the witness. The orbit-span is a Clifford-conjugation-
invariant submodule (`cliffOrbit_conj_closed`, by `span_induction`: conjugation maps `R·X₀·R⁻¹ ↦
(gR)·X₀·(gR)⁻¹`) containing the nonzero traceless skew-Hermitian `X₀` (`X0_mem_cliffOrbit`); the
nine literal Clifford generators lie in `H_of_G` (`genMap_mem`); so the Clifford-adjoint irreducibility
`clifford_irreducible_spans` forces it to contain every traceless skew-Hermitian matrix.

`Hlit` is a `def` (not `abbrev`) so the heavy `H_of_G`/`topologicalClosure` unfolding is gated during
`whnf`; the nine closure hypotheses are discharged as separate `refine` goals to avoid a simultaneous
18-argument elaboration blow-up.

## Pipeline invariants

  * **#10** (no `maxHeartbeats`): respected.
  * **#15** (no new project-local axioms): respected. Kernel-pure.

## Phase 6z provenance

Phase 6z Wave 4 increment 4h.1 (Clifford orbit spans 𝔰𝔲(8)). 2026-05-29.
-/

import Mathlib
import SKEFTHawking.FKLW.CliffordCCZSU8Irreducible
import SKEFTHawking.FKLW.CliffordCCZSU8SeedFlow

set_option autoImplicit false

namespace SKEFTHawking.FKLW.CliffordCCZSU8

open Matrix SKEFTHawking.FKLW.GenericSUd SKEFTHawking.FKLW.GenericSU2

/-- The literal Clifford+CCZ closure subgroup (a `def`, not `abbrev`, to gate `H_of_G` unfolding). -/
noncomputable def Hlit : Subgroup ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ) :=
  H_of_G cliffordCCZLiteralGeneratingSetSU8

/-! ## 1. The Clifford orbit set and its span -/

/-- The **Clifford orbit** of a tangent `X₀`: all `H_of_G`-conjugates `R·X₀·R⁻¹`. -/
def cliffOrbitSet (X0 : Matrix (Fin 8) (Fin 8) ℂ) : Set (Matrix (Fin 8) (Fin 8) ℂ) :=
  {M | ∃ R : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ), R ∈ Hlit ∧
    M = (R : Matrix (Fin 8) (Fin 8) ℂ) * X0 * (R : Matrix (Fin 8) (Fin 8) ℂ)⁻¹}

/-- `X₀` itself lies in the orbit span (`R = 1`). -/
theorem X0_mem_cliffOrbit (X0 : Matrix (Fin 8) (Fin 8) ℂ) :
    X0 ∈ Submodule.span ℝ (cliffOrbitSet X0) :=
  Submodule.subset_span ⟨1, Hlit.one_mem, by simp⟩

/-- The orbit span is closed under conjugation by any `H_of_G` element (in particular the generators):
`g·(R·X₀·R⁻¹)·g⁻¹ = (gR)·X₀·(gR)⁻¹`, and `span_induction` lifts this from the orbit to its span. -/
theorem cliffOrbit_conj_closed (X0 : Matrix (Fin 8) (Fin 8) ℂ)
    (g : ↥(Matrix.specialUnitaryGroup (Fin 8) ℂ)) (hg : g ∈ Hlit)
    (Y : Matrix (Fin 8) (Fin 8) ℂ) (hY : Y ∈ Submodule.span ℝ (cliffOrbitSet X0)) :
    (g : Matrix (Fin 8) (Fin 8) ℂ) * Y * (g : Matrix (Fin 8) (Fin 8) ℂ)⁻¹ ∈
      Submodule.span ℝ (cliffOrbitSet X0) := by
  induction hY using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨R, hR, rfl⟩ := hz
      refine Submodule.subset_span ⟨g * R, Hlit.mul_mem hg hR, ?_⟩
      rw [Submonoid.coe_mul, Matrix.mul_inv_rev]; noncomm_ring
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add, add_mul]; exact Submodule.add_mem _ ha hb
  | smul r a _ ha => rw [Matrix.mul_smul, Matrix.smul_mul]; exact Submodule.smul_mem _ r ha

/-! ## 2. The literal Clifford generators lie in `H_of_G` -/

/-- Every literal generator-image `ρ(of i)` lies in the closure subgroup `H_of_G`. -/
theorem genMap_mem (i : Fin 10) : cliffordCCZLiteralGenMap i ∈ Hlit := by
  have h := H_of_G_ρ_mem cliffordCCZLiteralGeneratingSetSU8 (FreeGroup.of i)
  have heq : cliffordCCZLiteralGeneratingSetSU8.ρ_hom (FreeGroup.of i)
      = cliffordCCZLiteralGenMap i := by
    show cliffordCCZLiteralRho (FreeGroup.of i) = _
    rw [cliffordCCZLiteralRho, FreeGroup.lift_apply_of]
  rw [heq] at h; exact h

/-! ## 3. The orbit span covers 𝔰𝔲(8) -/

/-- **The Clifford orbit of a nonzero traceless skew-Hermitian seed spans 𝔰𝔲(8)** (`hX_spans` engine).
Every traceless skew-Hermitian matrix lies in the ℝ-span of the Clifford orbit of `X₀`. The orbit span is
a Clifford-conjugation-invariant submodule (`cliffOrbit_conj_closed` at the nine generators `∈ H_of_G`)
containing the nonzero traceless skew-Hermitian `X₀`, so `clifford_irreducible_spans` forces it to contain
all of `𝔰𝔲(8)`. -/
theorem cliffOrbit_spans_su8 (X0 : Matrix (Fin 8) (Fin 8) ℂ)
    (hne : X0 ≠ 0) (hskew : X0.IsSkewHermitian) (htr : X0.trace = 0)
    (Y : Matrix (Fin 8) (Fin 8) ℂ) (hYskew : Y.IsSkewHermitian) (hYtr : Y.trace = 0) :
    Y ∈ Submodule.span ℝ (cliffOrbitSet X0) := by
  refine clifford_irreducible_spans (Submodule.span ℝ (cliffOrbitSet X0))
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ X0 (X0_mem_cliffOrbit X0) hne hskew htr Y hYskew hYtr
  · exact cliffOrbit_conj_closed X0 (qubit1Embed H_SU) (genMap_mem ⟨0, by decide⟩)
  · exact cliffOrbit_conj_closed X0 (qubit2Embed H_SU) (genMap_mem ⟨1, by decide⟩)
  · exact cliffOrbit_conj_closed X0 (qubit3Embed H_SU) (genMap_mem ⟨2, by decide⟩)
  · exact cliffOrbit_conj_closed X0 (qubit1Embed S_SU) (genMap_mem ⟨3, by decide⟩)
  · exact cliffOrbit_conj_closed X0 (qubit2Embed S_SU) (genMap_mem ⟨4, by decide⟩)
  · exact cliffOrbit_conj_closed X0 (qubit3Embed S_SU) (genMap_mem ⟨5, by decide⟩)
  · exact cliffOrbit_conj_closed X0 CNOT_12_SU8 (genMap_mem ⟨6, by decide⟩)
  · exact cliffOrbit_conj_closed X0 CNOT_13_SU8 (genMap_mem ⟨7, by decide⟩)
  · exact cliffOrbit_conj_closed X0 CNOT_23_SU8 (genMap_mem ⟨8, by decide⟩)

end SKEFTHawking.FKLW.CliffordCCZSU8
