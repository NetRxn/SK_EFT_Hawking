import Mathlib
import SKEFTHawking.SingularLocalDualityK
import SKEFTHawking.SingularRelativeDuality
import SKEFTHawking.SingularExcision

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD6e-ii) — cycle-difference compatibility of `D_W`

The `H(sub W)`-valued duality `relativeDualityK (S) (W) (z)` (for an open `W` and a `W`-supported
relative cycle `z`) is **independent of the choice of `W`-supported representative** within a relative
homology class: if `z`, `z'` are `W`-supported relative cycles for `(M, S)` that are relatively
homologous (`[z] = [z']` in `H(M, S)`), then `[a ⌢ z]_{sub W} = [a ⌢ z']_{sub W}`.

This is the **homology-variable well-definedness** of the duality pairing (the cohomology-variable
well-definedness is `relativeDualityK` itself; the cohomology-restriction compatibility is
`SingularLocalDualityKRestrict.relativeDualityK_restrict_compat`). It is the second `DirectLimit.lift`
compatibility effect for the open duality `D_W : Hᵏ_c(W) → H_{n-k}(sub W)` (the colimit legs cap
different per-`K` fundamental cycles, all rel-homologous to a common global ancestor).

The crux is that the difference `a ⌢ (z + z')` must bound *inside* `sub W`, not merely absolutely.
Resolved by the relative small-chains theorem (`relative_small_boundary` for the excisive cover
`{W, S}`): the relative-boundary witness can be taken `{W, S}`-**small**, so its `W`-part `w_W` is
genuinely `W`-supported, and `a ⌢ (z + z') = ∂(a ⌢ w_W)` (Leibniz with `δa = 0` absolutely, and
`a ⌢ (S-chain) = 0`) is a `sub W` boundary.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularRelativeCap SKEFTHawking.SingularCapSupport
  SKEFTHawking.SingularRelativeDuality SKEFTHawking.SingularLocalDualityK
  SKEFTHawking.SingularSubspaceChainsEquiv SKEFTHawking.SingularExcision

namespace SKEFTHawking.SingularLocalDualityKCycle

variable {X : TopCat}

/-- **The cap of a `W`-supported relative-`S`-boundary is a `sub W` boundary** (chain-level core, stated
on a plain cochain `ac` to keep the elaboration light): if `ac` vanishes on `S`-simplices and is an
absolute cocycle, and `u + ∂wW ∈ C(S)` with `u`, `wW` both `W`-supported, then the pulled-back `cap ac u`
is a boundary of `sub W`. Witness chain `cap ac wW` (`W`-supported); `∂(cap ac wW) = cap ac u` since
`∂(ac ⌢ wW) = ac ⌢ ∂wW` (`cap_cocycle_chainMap`, `δac = 0`) and `ac ⌢ (u + ∂wW) = 0`
(`cap_subspaceChain_eq_zero`). -/
theorem cap_pullback_mem_boundaries_of_relBoundaryW {k m : ℕ} {S W : Set ↑X}
    (ac : SingularCochain X k)
    (hav : ∀ (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk k))),
      ac (simplexIncl S k τ) = 0)
    (hδ : coboundaryₗ X k ac = 0)
    (u : SingularChain X (k + m + 1)) (wW : SingularChain X (k + m + 1 + 1))
    (huW : u ∈ subspaceChains W (k + m + 1)) (hwW : wW ∈ subspaceChains W (k + m + 1 + 1))
    (hrel : u + chainBoundary X (k + m + 1) wW ∈ subspaceChains S (k + m + 1)) :
    (subspaceChainsEquiv W (m + 1)).symm ⟨cap (m := m + 1) ac u, cap_mem_subspaceChains W ac huW⟩
      ∈ boundaries (sub W) (m + 1) := by
  refine subspaceChainsEquiv_symm_mem_boundaries W m (cap (m := m + 1) ac u) _
    (cap (m := m + 2) ac wW) (cap_mem_subspaceChains W ac hwW) ?_
  rw [cap_cocycle_chainMap (m := m + 1) ac hδ wW]
  show cap (m := m + 1) ac (chainBoundary X (k + m + 1) wW) = cap (m := m + 1) ac u
  have hz := cap_subspaceChain_eq_zero (m := m + 1) S ac hav hrel
  rw [map_add] at hz
  rw [← add_right_inj (cap (m := m + 1) ac u), hz, ZModModule.add_self]

theorem relativeDualityK_cycle_compat {k m : ℕ} {S W : Set ↑X}
    (z z' : SingularChain X (k + m + 1))
    (hzK : z ∈ subspaceChains W (k + m + 1)) (hz'K : z' ∈ subspaceChains W (k + m + 1))
    (hzS : chainBoundary X (k + m) z ∈ subspaceChains S (k + m))
    (hz'S : chainBoundary X (k + m) z' ∈ subspaceChains S (k + m))
    (hcov : (⋃ U ∈ ({W, S} : Set (Set ↑X)), interior U) = Set.univ)
    (w : SingularChain X (k + m + 1 + 1))
    (hw : (z + z') + chainBoundary X (k + m + 1) w ∈ subspaceChains S (k + m + 1))
    (x : RelativeCohomology S k) :
    relativeDualityK S W k m z hzK hzS x = relativeDualityK S W k m z' hz'K hz'S x := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  -- Step 1: the relative-boundary witness can be taken {W,S}-small (relative_small_boundary).
  have hsmall : z + z' ∈ smallChains ({W, S} : Set (Set ↑X)) (k + m + 1) :=
    subspaceChains_le_smallChains (Set.mem_insert _ _) (k + m + 1) (Submodule.add_mem _ hzK hz'K)
  have hrcyc : chainBoundary X (k + m) (z + z') ∈ subspaceChains S (k + m) := by
    rw [map_add]; exact Submodule.add_mem _ hzS hz'S
  obtain ⟨w', hw'small, hw'rel⟩ := relative_small_boundary hcov hsmall hrcyc hw
  -- Step 2: split the small witness `w' = wW + wS` (W-part + S-part).
  obtain ⟨wW, hwW, wS, hwS, hsplit⟩ :=
    Submodule.mem_sup.mp (smallChains_two_le W S (k + m + 1 + 1) hw'small)
  -- the W-part `wW` is itself a relative-boundary witness for `z + z'`.
  have hwWrel : (z + z') + chainBoundary X (k + m + 1) wW ∈ subspaceChains S (k + m + 1) := by
    have hbdeq : chainBoundary X (k + m + 1) wW
        = chainBoundary X (k + m + 1) w' - chainBoundary X (k + m + 1) wS :=
      eq_sub_of_add_eq (by rw [← map_add, hsplit])
    rw [hbdeq, ← add_sub_assoc]
    exact Submodule.sub_mem _ hw'rel (chainBoundary_mem_subspaceChains S (k + m + 1) wS hwS)
  -- Step 3+4: the difference cap-chain is a `sub W` boundary (the chain-level core helper).
  have hmem := cap_pullback_mem_boundaries_of_relBoundaryW (S := S) (W := W) a.1.1
    (relCochain_vanish S a.1) (relCocycle_coboundary_zero S a) (z + z') wW
    (Submodule.add_mem _ hzK hz'K) hwW hwWrel
  -- Step 5: the two duality classes differ by `[cap a (z+z')]_{sub W} = 0`.
  have hpull : pullbackDualityₗ S W z hzK a - pullbackDualityₗ S W z' hz'K a
      = (subspaceChainsEquiv W (m + 1)).symm
          ⟨cap (m := m + 1) a.1.1 (z + z'), cap_mem_subspaceChains W a.1.1 (Submodule.add_mem _ hzK hz'K)⟩ := by
    apply chainIncl_injective W (m + 1)
    rw [map_sub, chainIncl_pullbackDualityₗ, chainIncl_pullbackDualityₗ,
      chainIncl_subspaceChainsEquiv_symm]
    show cap (m := m + 1) a.1.1 z - cap (m := m + 1) a.1.1 z' = cap (m := m + 1) a.1.1 (z + z')
    rw [map_add, sub_eq_add_neg, neg_eq_of_add_eq_zero_left (ZModModule.add_self _)]
  rw [show (Submodule.Quotient.mk a : RelativeCohomology S k) = RelativeCohomology.mk S k a from rfl,
    relativeDualityK_mk, relativeDualityK_mk, Homology.mk, Homology.mk]
  refine (Submodule.Quotient.eq _).mpr ?_
  rw [Submodule.submoduleOf, Submodule.mem_comap, map_sub]
  show pullbackDualityₗ S W z hzK a - pullbackDualityₗ S W z' hz'K a ∈ boundaries (sub W) (m + 1)
  rw [hpull]
  exact hmem

end SKEFTHawking.SingularLocalDualityKCycle
