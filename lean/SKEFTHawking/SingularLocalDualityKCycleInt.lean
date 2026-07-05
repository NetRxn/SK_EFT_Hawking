/-
# Phase 5q.H (E1 integral topology) — cycle-difference compatibility of `D_W` (integral)

Integral (`ZMod 2 → ℤ`) mirror of `SingularLocalDualityKCycle`. The `H(sub W)`-valued duality
`relativeDualityKInt S W z` (for an open `W` and a `W`-supported relative cycle `z`) is **independent
of the choice of `W`-supported representative** within a relative homology class: if `z`, `z'` are
`W`-supported relative cycles for `(M, S)` that are relatively homologous, then
`[a ⌢ z]_{sub W} = [a ⌢ z']_{sub W}`. This is the homology-variable well-definedness of the duality —
the second `DirectLimit.lift` compatibility for the open duality `D_W`.

The crux is that `a ⌢ (z − z')` must bound *inside* `sub W`, resolved by the integral relative
small-chains theorem (`relative_small_boundaryInt` for the excisive cover `{W, S}`): the relative-
boundary witness can be taken `{W, S}`-small, so its `W`-part is genuinely `W`-supported.

**The two genuine ℤ-differences vs the mod-2 mirror:** (i) the mod-2 proof uses `z + z'` and
`ZModModule.add_self` (`x + x = 0`) throughout — over ℤ this is the honest DIFFERENCE `z − z'` in both
statements; (ii) `capInt_cocycle_chainMap` carries the sign `(-1)^k`, so the `sub W`-boundary witness is
`(-1)^{k+1} • (ac ⌢ wW)` (the `(-1)^{2k+1} = -1` making it cancel), the same pattern as the D_K witness.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularLocalDualityKInt
import SKEFTHawking.SingularCapSupportInt
import SKEFTHawking.SingularSubspaceChainsEquivInt
import SKEFTHawking.SingularExcisionIsoInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub simplexIncl)
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularCapSupportInt
open SKEFTHawking.SingularLocalDualityKInt
open SKEFTHawking.SingularExcisionInt
open SKEFTHawking.SingularExcisionIsoInt

namespace SKEFTHawking.SingularLocalDualityKCycleInt

variable {X : TopCat}

/-- **The cap of a `W`-supported relative-`S`-boundary is a `sub W` boundary** (integral chain-level
core): if `ac` vanishes on `S`-simplices and is an absolute cocycle, and `u + ∂wW ∈ C(S)` with `u`,
`wW` both `W`-supported, then the pulled-back `cap ac u` is a boundary of `sub W`. Witness chain
`(-1)^{k+1} • (ac ⌢ wW)` (`W`-supported); the sign makes `∂((-1)^{k+1}•(ac⌢wW)) = (-1)^{2k+1}•(ac⌢∂wW)
= -(ac⌢∂wW) = ac⌢u` (using `ac⌢(u+∂wW)=0` so `ac⌢∂wW = -ac⌢u`). -/
theorem capInt_pullback_mem_boundaries_of_relBoundaryW {k m : ℕ} {S W : Set ↑X}
    (ac : SingularCochainInt X k)
    (hav : ∀ (τ : (TopCat.toSSet.obj (sub S)).obj (op (SimplexCategory.mk k))),
      ac (simplexIncl S k τ) = 0)
    (hδ : coboundaryₗ X k ac = 0)
    (u : SingularChainInt X (k + m + 1)) (wW : SingularChainInt X (k + m + 1 + 1))
    (huW : u ∈ subspaceChainsInt W (k + m + 1)) (hwW : wW ∈ subspaceChainsInt W (k + m + 1 + 1))
    (hrel : u + chainBoundary X (k + m + 1) wW ∈ subspaceChainsInt S (k + m + 1)) :
    (inclRangeEquiv W (m + 1)).symm
        ⟨capInt (m := m + 1) ac u, capInt_mem_subspaceChainsInt W ac huW⟩
      ∈ boundaries (sub W) (m + 1) := by
  refine inclRangeEquiv_symm_mem_boundariesInt W m (capInt (m := m + 1) ac u) _
    ((-1 : ℤ) ^ (k + 1) • capInt (m := m + 2) ac wW)
    (Submodule.smul_mem _ _ (capInt_mem_subspaceChainsInt W ac hwW)) ?_
  rw [map_smul, capInt_cocycle_chainMap (m := m + 1) ac hδ wW, smul_smul, ← pow_add]
  have hodd : Odd ((k + 1) + k) := ⟨k, by ring⟩
  rw [hodd.neg_one_pow, neg_one_smul]
  have hz := capInt_subspaceChainInt_eq_zero (m := m + 1) S ac hav hrel
  rw [map_add] at hz
  exact neg_eq_of_add_eq_zero_left hz

/-- **Cycle-difference compatibility of the integral `H(sub W)`-valued duality**: `D_W` is independent
of the `W`-supported relative-cycle representative. Integral mirror of
`SingularLocalDualityKCycle.relativeDualityK_cycle_compat`, with the honest difference `z − z'`. -/
theorem relativeDualityKInt_cycle_compat {k m : ℕ} {S W : Set ↑X}
    (z z' : SingularChainInt X (k + m + 1))
    (hzK : z ∈ subspaceChainsInt W (k + m + 1)) (hz'K : z' ∈ subspaceChainsInt W (k + m + 1))
    (hzS : chainBoundary X (k + m) z ∈ subspaceChainsInt S (k + m))
    (hz'S : chainBoundary X (k + m) z' ∈ subspaceChainsInt S (k + m))
    (hcov : (⋃ U ∈ ({W, S} : Set (Set ↑X)), interior U) = Set.univ)
    (w : SingularChainInt X (k + m + 1 + 1))
    (hw : (z - z') + chainBoundary X (k + m + 1) w ∈ subspaceChainsInt S (k + m + 1))
    (x : RelativeCohomologyInt S k) :
    relativeDualityKInt S W k m z hzK hzS x = relativeDualityKInt S W k m z' hz'K hz'S x := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hsmall : z - z' ∈ smallChainsInt ({W, S} : Set (Set ↑X)) (k + m + 1) :=
    subspaceChainsInt_le_smallChainsInt (Set.mem_insert _ _) (k + m + 1)
      (Submodule.sub_mem _ hzK hz'K)
  have hrcyc : chainBoundary X (k + m) (z - z') ∈ subspaceChainsInt S (k + m) := by
    rw [map_sub]; exact Submodule.sub_mem _ hzS hz'S
  obtain ⟨w', hw'small, hw'rel⟩ := relative_small_boundaryInt hcov hsmall hrcyc hw
  obtain ⟨wW, hwW, wS, hwS, hsplit⟩ :=
    Submodule.mem_sup.mp (smallChainsInt_two_le W S (k + m + 1 + 1) hw'small)
  have hwWrel : (z - z') + chainBoundary X (k + m + 1) wW ∈ subspaceChainsInt S (k + m + 1) := by
    have hbdeq : chainBoundary X (k + m + 1) wW
        = chainBoundary X (k + m + 1) w' - chainBoundary X (k + m + 1) wS :=
      eq_sub_of_add_eq (by rw [← map_add, hsplit])
    rw [hbdeq, ← add_sub_assoc]
    exact Submodule.sub_mem _ hw'rel (chainBoundary_mem_subspaceChainsInt S (k + m + 1) wS hwS)
  have hmem := capInt_pullback_mem_boundaries_of_relBoundaryW (S := S) (W := W) a.1.1
    (relCochainInt_vanish S a.1) (relCocycleInt_coboundary_zero S a) (z - z') wW
    (Submodule.sub_mem _ hzK hz'K) hwW hwWrel
  have hpull : pullbackDualityIntₗ S W z hzK a - pullbackDualityIntₗ S W z' hz'K a
      = (inclRangeEquiv W (m + 1)).symm ⟨capInt (m := m + 1) a.1.1 (z - z'),
          capInt_mem_subspaceChainsInt W a.1.1 (Submodule.sub_mem _ hzK hz'K)⟩ := by
    apply chainIncl_injective W (m + 1)
    rw [map_sub, chainIncl_pullbackDualityIntₗ, chainIncl_pullbackDualityIntₗ,
      chainIncl_inclRangeEquiv_symm]
    show capInt (m := m + 1) a.1.1 z - capInt (m := m + 1) a.1.1 z'
      = capInt (m := m + 1) a.1.1 (z - z')
    rw [map_sub]
  rw [show (Submodule.Quotient.mk a : RelativeCohomologyInt S k)
      = RelativeCohomologyInt.mk S k a from rfl,
    relativeDualityKInt_mk, relativeDualityKInt_mk, Homology.mk, Homology.mk]
  refine (Submodule.Quotient.eq _).mpr ?_
  rw [Submodule.submoduleOf, Submodule.mem_comap, map_sub]
  show pullbackDualityIntₗ S W z hzK a - pullbackDualityIntₗ S W z' hz'K a
    ∈ boundaries (sub W) (m + 1)
  rw [hpull]
  exact hmem

end SKEFTHawking.SingularLocalDualityKCycleInt
