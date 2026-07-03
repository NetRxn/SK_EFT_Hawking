import Mathlib
import SKEFTHawking.SingularConnSquareCloseNCBot
import SKEFTHawking.SingularOpenDualityBot

/-!
# Phase 5q.G (G1 PD-induction, brick B3a) — the bottom pairing-mirror pack

Six degree-`0` mirrors of apex-body step lemmas whose statements are `(deg+1)`-floored and hence
not instantiable at the bottom test-cochain altitude `0` (the B3 audit, 48th-push list):

* `mem_boundaries_of_mk_eq₀` / `mk_eq_of_mem_boundaries₀` — the APPROACH-D class-membership
  round-trip at homology degree `0` (`cycles _ 0 = ⊤`, so the cycle hypotheses vanish);
* `joint_cap_rcap_match_pairing₀` — the pairing-relaxed cup–cap joint match with the test cochain
  `ω` at degree `0` (over the `{k l}`-generic core `kronecker_cap_eq_kronecker_rcap` at `l = 0`);
* `chainIncl_rcap_mem_relCycles₀` — the `hWcyc` builder with the test cocycle at `0`
  (cast-free: at the bottom `k+0+1 ≡ k+1+0 ≡ k+1` are all definitionally equal);
* `relKroneckerH_chainIncl_rcap_eq_kronecker₀` — pd-leg step 2's bridge, proved DIRECT
  (`relKroneckerH_mk_mk` + `relKronecker_mk`; the generic version's `relativeDualityK` detour
  cancels and is not needed);
* `pullbackDualityₗ₀_eq_subcap` — the ₀-family duality chain is a genuine `sub K`-cap
  (1:1 mirror of `pullbackDualityₗ_eq_subcap` over `chainIncl_pullbackDualityₗ₀`).

All other apex steps were audited degree-generic and reuse as-is at the bottom.
Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularLocalDualityK SKEFTHawking.SingularCapChainIncl
  SKEFTHawking.SingularSubspaceChainsEquiv SKEFTHawking.SingularRelativePairing
  SKEFTHawking.SingularRightCapBoundary SKEFTHawking.SingularRelativeCap
  SKEFTHawking.SingularExcisionIso SKEFTHawking.SingularLocalDualityKBot
  SKEFTHawking.SingularConnSquareMatchLHS

namespace SKEFTHawking.SingularConnSquareCloseNCBotApex

variable {X : TopCat}

/-- **APPROACH-D forward leg at the bottom**: two degree-`0` chains of `sub K` representing the
same `H₀` class have their sum a boundary (`cycles _ 0 = ⊤` — no cycle hypotheses). -/
theorem mem_boundaries_of_mk_eq₀ (K : Set ↑X)
    (chainL pd : SingularChain (sub K) 0)
    (hmk : Homology.mk (sub K) 0 ⟨chainL, Submodule.mem_top⟩
         = Homology.mk (sub K) 0 ⟨pd, Submodule.mem_top⟩) :
    chainL + pd ∈ boundaries (sub K) 0 := by
  have hz : Homology.mk (sub K) 0 ⟨chainL + pd, Submodule.mem_top⟩ = 0 := by
    rw [show (⟨chainL + pd, Submodule.mem_top⟩ : cycles (sub K) 0)
          = ⟨chainL, Submodule.mem_top⟩ + ⟨pd, Submodule.mem_top⟩ from rfl,
        SingularCapHomology.Homology.mk_add, hmk,
        ← SingularCapHomology.Homology.mk_add, ZModModule.add_self]
    rfl
  rw [SingularCapHomology.Homology.mk_eq_zero] at hz
  simpa using Submodule.mem_comap.mp hz

/-- **APPROACH-D reverse leg at the bottom**: over `ℤ/2`, two degree-`0` chains whose sum is a
boundary represent the same `H₀` class. -/
theorem mk_eq_of_mem_boundaries₀ (K : Set ↑X)
    (chainL pd : SingularChain (sub K) 0)
    (hmem : chainL + pd ∈ boundaries (sub K) 0) :
    Homology.mk (sub K) 0 ⟨chainL, Submodule.mem_top⟩
      = Homology.mk (sub K) 0 ⟨pd, Submodule.mem_top⟩ := by
  have hz : Homology.mk (sub K) 0 ⟨chainL + pd, Submodule.mem_top⟩ = 0 := by
    rw [SingularCapHomology.Homology.mk_eq_zero]
    exact Submodule.mem_comap.mpr (by simpa using hmem)
  have hsplit : Homology.mk (sub K) 0 ⟨chainL, Submodule.mem_top⟩
      + Homology.mk (sub K) 0 ⟨pd, Submodule.mem_top⟩ = 0 := by
    rw [← SingularCapHomology.Homology.mk_add,
      show (⟨chainL, Submodule.mem_top⟩ + ⟨pd, Submodule.mem_top⟩ : cycles (sub K) 0)
        = ⟨chainL + pd, Submodule.mem_top⟩ from rfl]
    exact hz
  calc Homology.mk (sub K) 0 ⟨chainL, Submodule.mem_top⟩
      = Homology.mk (sub K) 0 ⟨chainL, Submodule.mem_top⟩
          + (Homology.mk (sub K) 0 ⟨chainL, Submodule.mem_top⟩
            + Homology.mk (sub K) 0 ⟨pd, Submodule.mem_top⟩) := by
        rw [hsplit, add_zero]
    _ = Homology.mk (sub K) 0 ⟨pd, Submodule.mem_top⟩ := by
        rw [← add_assoc, ZModModule.add_self, zero_add]

/-- **The pairing-relaxed cup–cap joint match at the bottom test altitude** (`ω` a `0`-cochain):
the `{k l}`-generic duality core `kronecker_cap_eq_kronecker_rcap` instantiated at `l = 0`. -/
theorem joint_cap_rcap_match_pairing₀ {M : TopCat} {N : ℕ}
    (ω : SingularCochain M 0) (gM : SingularCochain M (N + 1))
    (F : SingularChain M (N + 1 + 0))
    (L : SingularChain M 0) (R : SingularChain M (N + 1))
    (hL : kronecker ω L = kronecker ω (cap (k := N + 1) (m := 0) gM F))
    (hR : kronecker gM R = kronecker gM (SingularCapChainIncl.rcap (k := N + 1) ω F)) :
    kronecker ω L = kronecker gM R := by
  rw [hL, hR]
  exact SingularConnSquareMatchLHS.kronecker_cap_eq_kronecker_rcap (k := N + 1) (l := 0) gM ω F

/-- **The `hWcyc` builder at the bottom test altitude** (`a'` a `0`-cocycle): the right cap of a
`0`-cocycle against a `K`-supported chain with `S`-supported boundary is a relative cycle.
Cast-free (`k+0+1 ≡ k+1+0 ≡ k+1` definitionally at the bottom). -/
theorem chainIncl_rcap_mem_relCycles₀ {k : ℕ} {S K : Set ↑X}
    (z : SingularChain X (k + 1)) (hzK : z ∈ subspaceChains K (k + 1))
    (hzS : chainBoundary X k z ∈ subspaceChains S k)
    (a' : LinearMap.ker (coboundaryₗ (sub K) 0)) :
    RelativeChain.mk S (k + 1)
        (chainIncl K (k + 1) (rcap (k := k + 1) a'.1
          ((subspaceChainsEquiv K (k + 1)).symm ⟨z, hzK⟩)))
      ∈ relCycles S (k + 1) := by
  rw [show relCycles S (k + 1) = LinearMap.ker (relBoundary S k) from rfl, LinearMap.mem_ker,
    relBoundary_mk, RelativeChain.mk_eq_zero_iff, ← chainIncl_chainBoundary,
    chainIncl_mem_subspaceChains_iff S K]
  have key : chainBoundary (sub K) k (rcap (k := k + 1) a'.1
        ((subspaceChainsEquiv K (k + 1)).symm ⟨z, hzK⟩))
      = rcap (k := k) a'.1 (chainBoundary (sub K) k
          ((subspaceChainsEquiv K (k + 1)).symm ⟨z, hzK⟩)) :=
    rcap_cocycle_chainMap (k := k) (l := 0) a'.1 (LinearMap.mem_ker.mp a'.2)
      ((subspaceChainsEquiv K (k + 1)).symm ⟨z, hzK⟩)
  rw [key]
  have hbmem : chainBoundary (sub K) k ((subspaceChainsEquiv K (k + 1)).symm ⟨z, hzK⟩)
      ∈ subspaceChains (Subtype.val ⁻¹' S) k := by
    rw [← chainIncl_mem_subspaceChains_iff S K, chainIncl_chainBoundary,
      chainIncl_subspaceChainsEquiv_symm]
    exact hzS
  exact rcap_mem_subspaceChains (X := sub K) (k := k) (l := 0) (Subtype.val ⁻¹' S) a'.1 hbmem

/-- **pd-leg step 2's bridge at the bottom test altitude**, proved DIRECT: the relative Kronecker
pairing of `[ω]` against the `mk`-presented rcap class is the chain-level ambient pairing. The
generic version's `relativeDualityK` detour cancels — `relKroneckerH_mk_mk` + `relKronecker_mk`
close it with no degree floor. -/
theorem relKroneckerH_chainIncl_rcap_eq_kronecker₀ {k : ℕ} {S K : Set ↑X}
    (z : SingularChain X (k + 1)) (hzK : z ∈ subspaceChains K (k + 1))
    (ω : LinearMap.ker (relCoboundaryₗ S (k + 1)))
    (a' : LinearMap.ker (coboundaryₗ (sub K) 0))
    (hWcyc : RelativeChain.mk S (k + 1)
        (chainIncl K (k + 1) (rcap (k := k + 1) a'.1
          ((subspaceChainsEquiv K (k + 1)).symm ⟨z, hzK⟩)))
        ∈ relCycles S (k + 1)) :
    relKroneckerH S (RelativeCohomology.mk S (k + 1) ω)
        (RelativeHomology.mk S (k + 1)
          ⟨RelativeChain.mk S (k + 1)
              (chainIncl K (k + 1) (rcap (k := k + 1) a'.1
                ((subspaceChainsEquiv K (k + 1)).symm ⟨z, hzK⟩))),
            hWcyc⟩)
      = kronecker ω.1.1
          (chainIncl K (k + 1) (rcap (k := k + 1) a'.1
            ((subspaceChainsEquiv K (k + 1)).symm ⟨z, hzK⟩))) := by
  rw [relKroneckerH_mk_mk, relKronecker_mk]

/-- **The ₀-family duality chain is a genuine `sub K`-cap** (1:1 mirror of
`pullbackDualityₗ_eq_subcap` over `chainIncl_pullbackDualityₗ₀`): apex step `hpd_cap`'s bottom
form, exposing `pullbackDualityₗ₀` for the cup–cap adjunction. -/
theorem pullbackDualityₗ₀_eq_subcap {k : ℕ} {S K : Set ↑X} (z : SingularChain X (k + 1))
    (hzK : z ∈ subspaceChains K (k + 1))
    (a : LinearMap.ker (relCoboundaryₗ S (k + 1))) :
    SKEFTHawking.SingularLocalDualityKBot.pullbackDualityₗ₀ S K z hzK a
      = cap (k := k + 1) (m := 0) (SingularCapChainIncl.pullbackCochain K (k + 1) a.1.1)
          ((subspaceChainsEquiv K (k + 1)).symm ⟨z, hzK⟩) := by
  apply chainIncl_injective K 0
  rw [SKEFTHawking.SingularLocalDualityKBot.chainIncl_pullbackDualityₗ₀,
    ← SingularCapChainIncl.cap_chainIncl (k := k + 1) (m := 0)]
  exact congrArg (cap (k := k + 1) (m := 0) a.1.1)
    (chainIncl_subspaceChainsEquiv_symm K (k + 1) ⟨z, hzK⟩).symm

end SKEFTHawking.SingularConnSquareCloseNCBotApex
