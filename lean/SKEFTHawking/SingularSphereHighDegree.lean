import Mathlib
import SKEFTHawking.SingularDisjointUnion
import SKEFTHawking.SingularSphereAcyclic
import SKEFTHawking.SingularLocalHomology

/-!
# Phase 5q.F (w₂-foundation) — high-degree vanishing of sphere homology `Hₚ(Sⁿ) = 0` for `p > n`

The convex base case of the fundamental-class compactness induction (`Hᵢ(M | K) = 0` for `i > n`,
`K` a compact convex chart set) reduces, via the radial retract `ℝⁿ ∖ K ≃ ℝⁿ ∖ 0 ≃ Sⁿ⁻¹` and the
acyclic-ambient connecting iso, to the **high-degree vanishing of sphere homology**: `Hₚ(Sⁿ) = 0`
for `p ≥ n + 1`. This module builds that vanishing by induction on the sphere dimension `n`, using the
suspension/dimension-reduction iso `SingularSphereAcyclic.dimReductionEquiv : Hₖ₊₂(Sⁿ) ≅ Hₖ₊₁(Sⁿ⁻¹)`.

The base case `Hₚ(S⁰) = 0` (`p ≥ 1`) comes from the general **clopen-split vanishing**: if `X` splits as
a clopen partition `U ⊔ Uᶜ` and both pieces are acyclic in degree `p`, then `Hₚ(X) = 0` (`S⁰` is two
points, each homeomorphic to the acyclic `ℝ⁰`). Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularPairLES
open SKEFTHawking.SingularLocalHomology SKEFTHawking.SingularDisjointUnion
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularExcision

namespace SKEFTHawking.SingularSphereHighDegree

/-- **Clopen-split vanishing**: if `U ⊆ X` is clopen and both `Hₖ₊₁(U) = 0` and `Hₖ₊₁(Uᶜ) = 0`, then
`Hₖ₊₁(X) = 0`. The chain complex of `X` splits as `C(U) ⊕ C(Uᶜ)` (`subspaceChains_sup_compl_eq_top`,
`subspaceChains_inf_compl_eq_bot`), so any `(k+1)`-cycle is a sum of a `U`-cycle and a `Uᶜ`-cycle, each
of which is a boundary by hypothesis. -/
theorem homology_trivial_of_clopen_split {X : TopCat} {U : Set ↑X} (hU : IsClopen U) (k : ℕ)
    (hUtriv : ∀ x : Homology (sub U) (k + 1), x = 0)
    (hUctriv : ∀ x : Homology (sub Uᶜ) (k + 1), x = 0)
    (x : Homology X (k + 1)) : x = 0 := by
  refine homology_trivial_of_acyclic ?_ x
  intro z hz
  have hmem : z ∈ subspaceChains (S := U) (k + 1) ⊔ subspaceChains (S := Uᶜ) (k + 1) := by
    rw [subspaceChains_sup_compl_eq_top hU]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, hab⟩ := Submodule.mem_sup.mp hmem
  -- Pull `a`, `b` back to chains in the subspaces.
  set a' := (inclRangeEquiv U (k + 1)).symm ⟨a, ha⟩ with ha'
  set b' := (inclRangeEquiv Uᶜ (k + 1)).symm ⟨b, hb⟩ with hb'
  have hAeq : chainIncl U (k + 1) a' = a := chainIncl_inclRangeEquiv_symm U (k + 1) ⟨a, ha⟩
  have hBeq : chainIncl Uᶜ (k + 1) b' = b := chainIncl_inclRangeEquiv_symm Uᶜ (k + 1) ⟨b, hb⟩
  -- The boundary of `z = a + b` vanishes; split it across the partition.
  have hsum : chainIncl U k (chainBoundary (sub U) k a')
      + chainIncl Uᶜ k (chainBoundary (sub Uᶜ) k b') = 0 := by
    rw [chainIncl_chainBoundary, chainIncl_chainBoundary, hAeq, hBeq, ← map_add, hab, hz]
  -- Each boundary piece lands in its own clopen subspace; their sum being `0` forces each to vanish.
  have hkey : chainIncl U k (chainBoundary (sub U) k a')
      = chainIncl Uᶜ k (chainBoundary (sub Uᶜ) k b') := by
    rw [← neg_eq_of_add_eq_zero_left hsum]
    exact neg_eq_of_add_eq_zero_left (ZModModule.add_self _)
  have hbotU : chainIncl U k (chainBoundary (sub U) k a') = 0 := by
    have hinf : chainIncl U k (chainBoundary (sub U) k a')
        ∈ subspaceChains (S := U) k ⊓ subspaceChains (S := Uᶜ) k :=
      ⟨⟨chainBoundary (sub U) k a', rfl⟩, ⟨chainBoundary (sub Uᶜ) k b', hkey.symm⟩⟩
    rw [subspaceChains_inf_compl_eq_bot, Submodule.mem_bot] at hinf
    exact hinf
  have hcycA : chainBoundary (sub U) k a' = 0 :=
    chainIncl_injective U k (hbotU.trans (map_zero _).symm)
  have hcycB : chainBoundary (sub Uᶜ) k b' = 0 := by
    apply chainIncl_injective Uᶜ k
    rw [← hkey, hbotU, map_zero]
  -- Each piece is a boundary in its subspace (acyclic), hence in `X`.
  have haB : a ∈ boundaries X (k + 1) := by
    rw [← hAeq]
    exact chainIncl_mem_boundaries U (k + 1) a' (boundaries_of_homology_trivial hUtriv a' hcycA)
  have hbB : b ∈ boundaries X (k + 1) := by
    rw [← hBeq]
    exact chainIncl_mem_boundaries Uᶜ (k + 1) b' (boundaries_of_homology_trivial hUctriv b' hcycB)
  rw [← hab]
  exact Submodule.add_mem _ haB hbB

end SKEFTHawking.SingularSphereHighDegree
