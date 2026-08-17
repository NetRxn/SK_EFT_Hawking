/-
Phase 5q.B: assembling `8 ∣ σ` from the classification ([E3] in `docs/dev-loops/Phase5qB/LAB_NOTEBOOK.md`).

The classification of even unimodular lattices says every such form is congruent to a block-diagonal sum
`E₈^a ⊕ (−E₈)^b ⊕ H^c`. Granting that normal form, `8 ∣ σ` is now PURELY the signature calculus built in
`E8Signature` / `LatticeSignatureCongr` / `BlockSignature` / `LatticeSigBlock` / `GeneratorNondeg`: each
generator has `8 ∣ σ`, block sums preserve it, and congruence/reindexing preserve `latticeSig`. This module
records exactly those closure facts — the inductive content of the assembly. What remains to make `8 ∣ σ`
*unconditional* is solely the classification's EXISTENCE statement (every even unimodular form is congruent
to such a normal form), whose two irreducible inputs — Hasse–Minkowski (indefinite represents 0) and
theta-modularity (definite `8 ∣ rank`) — have no Mathlib substrate and are tracked as the remaining gap.

* `eight_dvd_latticeSig_e8lit` / `…_neg_e8lit` / `…_hyp` — the three generators each satisfy `8 ∣ σ`
  (`σ = 8, −8, 0`).
* `eight_dvd_latticeSigOf_fromBlocks` — block sums of nondegenerate `8 ∣ σ` blocks satisfy `8 ∣ σ` (the
  inductive step).
* `eight_dvd_latticeSig_congr` / `eight_dvd_latticeSigOf_reindex` — `8 ∣ σ` is invariant under integer
  congruence and reindexing (so it transfers across the classification isomorphism).

All proofs are kernel-pure (`propext`/`Classical.choice`/`Quot.sound` only); no `native_decide`, no
`maxHeartbeats`, no axiom.
-/

import Mathlib
import SKEFTHawking.AlgebraicRokhlin
import SKEFTHawking.E8Signature
import SKEFTHawking.LatticeSignatureCongr
import SKEFTHawking.BlockSignature
import SKEFTHawking.GeneratorNondeg
import SKEFTHawking.LatticeSigBlock

namespace SKEFTHawking

open Matrix

/-! ## Generators: each has `8 ∣ σ` -/

/-- `8 ∣ σ(E₈)` (`σ = 8`). -/
theorem eight_dvd_latticeSig_e8lit : (8 : ℤ) ∣ latticeSig E8lit := by rw [e8lit_latticeSig]

/-- `8 ∣ σ(−E₈)` (`σ = −8`). -/
theorem eight_dvd_latticeSig_neg_e8lit : (8 : ℤ) ∣ latticeSig (-E8lit) := by
  rw [neg_e8lit_latticeSig]; norm_num

/-- `8 ∣ σ(H)` (`σ = 0`). -/
theorem eight_dvd_latticeSig_hyp : (8 : ℤ) ∣ latticeSig Hyp := by rw [hyp_latticeSig]; norm_num

/-! ## Closure under block sums, congruence, and reindexing -/

/-- **Inductive step:** a block-diagonal sum of two nondegenerate blocks, each with `8 ∣ σ`, has `8 ∣ σ`. -/
theorem eight_dvd_latticeSigOf_fromBlocks {na nb : ℕ} (A : Matrix (Fin na) (Fin na) ℤ)
    (B : Matrix (Fin nb) (Fin nb) ℤ)
    (hA : (A.map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥)
    (hB : (B.map (Int.cast : ℤ → ℝ)).toQuadraticMap'.radical = ⊥)
    (hdA : (8 : ℤ) ∣ latticeSigOf A) (hdB : (8 : ℤ) ∣ latticeSigOf B) :
    (8 : ℤ) ∣ latticeSigOf (Matrix.fromBlocks A 0 0 B) := by
  rw [latticeSigOf_fromBlocks A B hA hB]
  exact Dvd.dvd.add hdA hdB

/-- `8 ∣ σ` is invariant under integer congruence `M ↦ Pᵀ M P` (`P ∈ GL(ℤ)`) — so it transfers from the
classification normal form back to `M`. -/
theorem eight_dvd_latticeSig_congr {n : ℕ} (M P : Matrix (Fin n) (Fin n) ℤ) (hP : IsUnit P.det) :
    (8 : ℤ) ∣ latticeSig (Pᵀ * M * P) ↔ (8 : ℤ) ∣ latticeSig M := by
  rw [latticeSig_congr M P hP]

/-- `8 ∣ σ` is invariant under reindexing the lattice basis. -/
theorem eight_dvd_latticeSigOf_reindex {ι ι' : Type*} [Fintype ι] [DecidableEq ι] [Fintype ι']
    [DecidableEq ι'] (e : ι ≃ ι') (M : Matrix ι ι ℤ) :
    (8 : ℤ) ∣ latticeSigOf (Matrix.reindex e e M) ↔ (8 : ℤ) ∣ latticeSigOf M := by
  rw [latticeSigOf_reindex]

/-! ## Bridge to the Rokhlin conclusion -/

/-- **The Rokhlin composition in `latticeSig` terms.** For an even unimodular form, the algebraic bound
`8 ∣ latticeSig M` (van der Blij — the classification target) together with the topological factor
`2 ∣ latticeSig M / 8` (Â-genus even / `Arf(q̄)=0`) gives `16 ∣ latticeSig M`, kernel-pure. This bridges the
signature machinery of this Phase to the wired Rokhlin conclusion: the only non-geometric input is the
single, precisely-isolated `8 ∣ latticeSig M`. -/
theorem sixteen_dvd_latticeSig_of_eight_dvd_of_topo {n : ℕ} (M : Matrix (Fin n) (Fin n) ℤ)
    (h8 : (8 : ℤ) ∣ latticeSig M) (htopo : (2 : ℤ) ∣ latticeSig M / 8) :
    (16 : ℤ) ∣ latticeSig M :=
  rokhlin_from_serre_plus_topology (latticeSig M) h8 htopo

end SKEFTHawking
