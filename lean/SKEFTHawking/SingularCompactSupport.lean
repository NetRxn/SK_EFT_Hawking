import Mathlib
import SKEFTHawking.SingularExcision

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD5-cptsupp) — compact support of singular chains

Every singular chain `c : Cₙ(X)` is **supported in a compact set**: `c ∈ subspaceChains K n` for some
compact `K ⊆ X`. The witness is the (finite) union of the images of the simplices in `c.support`, each
the continuous image of the compact standard simplex; the lifting lemma
`SingularExcision.single_mem_subspaceChains_of_subordinate` puts each basis simplex into `C(K)`.

This is the clean, **true** enabling fact for the compactly-supported-cohomology Poincaré-duality route
(Hatcher 3.36 over open covers): it gives `H_n(U) ≅ colim_{K ⊆ U compact} H_n(sub K)` for the bottom
row of the duality ladder — replacing the *false* closed-cover homology Mayer–Vietoris of the prior
framework. (See the 2026-06-19 PD-framework re-resolution note.)

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
  SKEFTHawking.SingularExcision

namespace SKEFTHawking.SingularCompactSupport

variable {X : TopCat} {n : ℕ}

/-- **Compact support of a singular chain**: every `c : Cₙ(X)` lies in `subspaceChains K n` for some
**compact** `K ⊆ X` — the union of the images of the (finitely many) simplices in `c.support`. Each
image is the continuous image of the compact standard simplex, and the lifting lemma
`single_mem_subspaceChains_of_subordinate` puts each basis simplex into `C(K)`. -/
theorem exists_compact_support (c : SingularChain X n) :
    ∃ K : Set ↑X, IsCompact K ∧ c ∈ subspaceChains K n := by
  classical
  haveI : CompactSpace ↥(stdSimplex ℝ (Fin (n + 1))) :=
    isCompact_iff_compactSpace.mp (isCompact_stdSimplex ℝ (Fin (n + 1)))
  set K : Set ↑X := ⋃ τ ∈ c.support,
    Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) with hKdef
  refine ⟨K, ?_, ?_⟩
  · rw [hKdef]
    refine (c.support.finite_toSet).isCompact_biUnion (fun τ _ => ?_)
    exact isCompact_range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) τ).continuous
  · rw [← Finsupp.sum_single c]
    refine Submodule.finsuppSum_mem (ZMod 2) (subspaceChains K n) c _ (fun τ hτ => ?_)
    have hτ' : τ ∈ c.support := Finsupp.mem_support_iff.mpr hτ
    have hrange : Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) ⊆ K := by
      rw [hKdef]; intro x hx; exact Set.mem_biUnion hτ' hx
    show Finsupp.single τ (c τ) ∈ subspaceChains K n
    have hsingle : (Finsupp.single τ (c τ) : SingularChain X n)
        = (c τ) • Finsupp.single τ (1 : ZMod 2) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [hsingle]
    exact Submodule.smul_mem _ _ (single_mem_subspaceChains_of_subordinate hrange)

end SKEFTHawking.SingularCompactSupport
