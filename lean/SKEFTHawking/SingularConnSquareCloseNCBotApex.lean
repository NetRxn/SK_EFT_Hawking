import Mathlib
import SKEFTHawking.SingularConnSquareCloseNCBot
import SKEFTHawking.SingularOpenDualityBot
import SKEFTHawking.SingularConnSquareCloseChainMapBot
import SKEFTHawking.SingularOpenDualityBotNat
import SKEFTHawking.SingularOpenDualityMVSquare
import SKEFTHawking.SingularCSCMayerVietorisMiddle
import SKEFTHawking.SingularCSCMayerVietorisSumExact
import SKEFTHawking.SingularCSCMayerVietorisConnExact
import SKEFTHawking.SingularOpenDualityConnSquareColimit
import SKEFTHawking.SingularMayerVietorisLESBot
import SKEFTHawking.SingularSubHomSumEnd
import SKEFTHawking.SingularOpenDualityMonotoneUnion

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
  SKEFTHawking.SingularConnSquareMatchLHS SKEFTHawking.SingularConnSquareCloseNC
  SKEFTHawking.SingularMayerVietoris SKEFTHawking.SingularOpenDualityBot
  SKEFTHawking.SingularConnSquareCloseNCBot SKEFTHawking.SingularConnSquareCloseChainMapBot
  SKEFTHawking.SingularOpenDuality SKEFTHawking.SingularOpenDualityCycle
  SKEFTHawking.SingularCompactsInOpen SKEFTHawking.SingularCompactlySupportedOpen
  SKEFTHawking.SingularCSCMayerVietorisConnecting SKEFTHawking.SingularCohomologySnake
  SKEFTHawking.SingularFunctoriality SKEFTHawking.SingularKroneckerFunctoriality
  SKEFTHawking.SingularPairLES SKEFTHawking.SingularMayerVietorisLES
  SKEFTHawking.SingularOpenDualityBotNat SKEFTHawking.SingularOpenDualityMVSquare
  SKEFTHawking.SingularCSCMayerVietoris SKEFTHawking.SingularCSCMayerVietorisMiddle
  SKEFTHawking.SingularCSCMayerVietorisSumExact SKEFTHawking.SingularCSCMayerVietorisConnExact
  SKEFTHawking.SingularSubHomologyMV

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
        ← SingularCapHomology.Homology.mk_add,
          -- v4.32: the subtype's `+` comes via `AddSubgroupClass`, not the `AddCommGroup.toAdd`
          -- that `ZModModule.add_self` is stated over, so `rw` cannot match `?x + ?x`.
          show (⟨pd, Submodule.mem_top⟩ : cycles (sub K) 0) + ⟨pd, Submodule.mem_top⟩ = 0 from
            Subtype.ext (by simpa using ZModModule.add_self pd)]
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

variable [T2Space ↑X]

/-! ## B3b — the bottom fact-(ii) mirror chain

`fact_ii_two_legs_discharge` and its engines `gamma_two_legs_close` /
`rcap_singularSd_iterate_chainBoundary_arg` / `rcap_singularSd_iterate` are all `(l+1)`-floored
in the test-cochain degree. The four ₀-mirrors below run at `β`-degree `0`; every cast in the
generic bodies (the `n+2+l+1 ↔ n+1+(l+1)+1` recasts, the T₀ double-cast collapse, the
`chainBoundary_cast_comm` bridge) degenerates at the bottom — both spellings coincide at `n+1+1`
— so the mirrors are shorter than their generics. -/

/-- **`rcap` Sd-bridge on a cycle, bottom cochain** (mirror of `rcap_singularSd_iterate` at
`l+1 → 0`): for a `0`-cocycle `ω` and a cycle `z`, `rcap ω z` equals `rcap ω (Sdʲz)` modulo a
boundary. Cast-free (the generic's homotopy-term cast has definitionally equal endpoints). -/
theorem rcap_singularSd_iterate₀ {M : TopCat} {k : ℕ} (ω : SingularCochain M 0)
    (hω : coboundaryₗ M 0 ω = 0) {z : SingularChain M (k + 1)}
    (hz : chainBoundary M k z = 0) (j : ℕ) :
    SingularCapChainIncl.rcap (k := k + 1) ω z
      = SingularCapChainIncl.rcap (k := k + 1) ω
          ((⇑(SingularSubdivision.singularSd M (k + 1)))^[j] z)
        + chainBoundary M (k + 1)
            (SingularCapChainIncl.rcap (k := k + 1 + 1) ω
              (SingularSubdivision.iterHomotopy M (k + 1) j z)) := by
  have hb : z + (⇑(SingularSubdivision.singularSd M (k + 1)))^[j] z
      = chainBoundary M (k + 1) (SingularSubdivision.iterHomotopy M (k + 1) j z) :=
    SingularExcision.add_singularSd_iterate_eq_boundary hz j
  have hcm : chainBoundary M (k + 1)
        (SingularCapChainIncl.rcap (k := k + 1 + 1) ω
          (SingularSubdivision.iterHomotopy M (k + 1) j z))
      = SingularCapChainIncl.rcap (k := k + 1) ω
          (chainBoundary M (k + 1) (SingularSubdivision.iterHomotopy M (k + 1) j z)) :=
    SingularRightCapBoundary.rcap_cocycle_chainMap (k := k + 1) (l := 0) ω hω
      (SingularSubdivision.iterHomotopy M (k + 1) j z)
  rw [hcm, ← hb, map_add]
  abel_nf
  simp only [two_smul, ZModModule.add_self, zero_add]

/-- **`rcap` Sd-bridge on a `∂`-argument, bottom cochain** (mirror of
`rcap_singularSd_iterate_chainBoundary_arg` at `l+1 → 0`). -/
theorem rcap_singularSd_iterate_chainBoundary_arg₀ {M : TopCat} {k : ℕ}
    (ω : SingularCochain M 0) (hω : coboundaryₗ M 0 ω = 0)
    (c : SingularChain M (k + 1 + 1)) (j : ℕ) :
    SingularCapChainIncl.rcap (k := k + 1) ω
        (chainBoundary M (k + 1) ((⇑(SingularSubdivision.singularSd M (k + 1 + 1)))^[j] c))
      = SingularCapChainIncl.rcap (k := k + 1) ω (chainBoundary M (k + 1) c)
        + chainBoundary M (k + 1)
            (SingularCapChainIncl.rcap (k := k + 1 + 1) ω
              (SingularSubdivision.iterHomotopy M (k + 1) j (chainBoundary M (k + 1) c))) := by
  rw [SingularSubdivision.singularSd_iterate_chainBoundary]
  have hz : chainBoundary M k (chainBoundary M (k + 1) c) = 0 :=
    chainBoundary_chainBoundary_apply M k c
  rw [rcap_singularSd_iterate₀ ω hω hz j]
  abel_nf
  simp only [two_smul, ZModModule.add_self, add_zero]

omit [T2Space ↑X] in
/-- **The γ two-legs close, bottom cochain** (mirror of `gamma_two_legs_close` at `l+1 → 0`):
the two realized V-legs of the pd-side (`jP`) and F-side (`jF`) splits pair equally against the
rel-`(A∩B)` cocycle `g`, via the β2 boundary-kill on the combined parent `DP + DF`. Cast-free. -/
theorem gamma_two_legs_close₀ {A B W : Set ↑X} (hA : IsOpen A) (hB : IsOpen B) {n : ℕ}
    (g : SingularCochain X (n + 1)) (hgc : coboundary X (n + 1) g = 0)
    (hg : g ∈ relCochains (A ∩ B) (n + 1))
    (β : SingularCochain (sub W) 0)
    (hβ : coboundaryₗ (sub W) 0 β = 0)
    (zsub : SingularChain (sub W) (n + 1 + 1))
    (hzbdcov : chainIncl W (n + 1) (chainBoundary (sub W) (n + 1) zsub)
      ∈ subspaceChains (A ∪ B) (n + 1))
    (Camb : SingularChain X (n + 1 + 1)) (jP : ℕ)
    (hCore : chainBoundary X (n + 1) Camb
      = chainIncl W (n + 1) (SingularCapChainIncl.rcap (k := n + 1) β
          (chainBoundary (sub W) (n + 1) zsub)))
    {a₁ b₁ : SingularChain X (n + 1)}
    (ha₁ : a₁ ∈ subspaceChains A (n + 1)) (hb₁ : b₁ ∈ subspaceChains B (n + 1))
    (hP₁ : chainBoundary X (n + 1)
        ((⇑(SingularSubdivision.singularSd X (n + 1 + 1)))^[jP] Camb) = a₁ + b₁)
    (jF : ℕ) {a₂ b₂ : SingularChain (sub W) (n + 1)}
    (ha₂ : chainIncl W (n + 1) a₂ ∈ subspaceChains A (n + 1))
    (hb₂ : chainIncl W (n + 1) b₂ ∈ subspaceChains B (n + 1))
    (hQ : chainBoundary (sub W) (n + 1)
        ((⇑(SingularSubdivision.singularSd (sub W) (n + 1 + 1)))^[jF] zsub)
      = a₂ + b₂) :
    kronecker g b₁
      = kronecker g (chainIncl W (n + 1) (SingularCapChainIncl.rcap (k := n + 1) β b₂)) := by
  classical
  have hcyc : chainBoundary X n (chainBoundary X (n + 1) Camb) = 0 :=
    chainBoundary_chainBoundary_apply X n Camb
  have hhomP := SingularExcision.add_singularSd_iterate_eq_boundary hcyc jP
  have hSdP : (⇑(SingularSubdivision.singularSd X (n + 1)))^[jP] (chainBoundary X (n + 1) Camb)
      = a₁ + b₁ := by
    rw [← SingularSubdivision.singularSd_iterate_chainBoundary, hP₁]
  have hrc := rcap_singularSd_iterate_chainBoundary_arg₀ (k := n) β hβ zsub jF
  rw [hQ, map_add] at hrc
  have hIncl := congrArg (chainIncl W (n + 1)) hrc
  rw [map_add, map_add, SingularRelativeHomologyMod2.chainIncl_chainBoundary, ← hCore] at hIncl
  set DP := SingularSubdivision.iterHomotopy X (n + 1) jP (chainBoundary X (n + 1) Camb) with hDP
  set DF := chainIncl W (n + 1 + 1) (SingularCapChainIncl.rcap (k := n + 1 + 1) β
      (SingularSubdivision.iterHomotopy (sub W) (n + 1) jF
        (chainBoundary (sub W) (n + 1) zsub))) with hDF
  have hDPbd : chainBoundary X (n + 1) DP
      = chainBoundary X (n + 1) Camb + (a₁ + b₁) := by
    rw [← hhomP, hSdP]
  have hDFbd : chainBoundary X (n + 1) DF
      = chainIncl W (n + 1) (SingularCapChainIncl.rcap (k := n + 1) β a₂)
        + chainIncl W (n + 1) (SingularCapChainIncl.rcap (k := n + 1) β b₂)
        + chainBoundary X (n + 1) Camb := by
    rw [hIncl]
    abel_nf
    simp only [two_smul, ZModModule.add_self, zero_add]
  have hsplitE : chainBoundary X (n + 1) (DP + DF)
      = (a₁ + chainIncl W (n + 1) (SingularCapChainIncl.rcap (k := n + 1) β a₂))
        + (b₁ + chainIncl W (n + 1) (SingularCapChainIncl.rcap (k := n + 1) β b₂)) := by
    rw [map_add, hDPbd, hDFbd]
    abel_nf
    simp only [two_smul, ZModModule.add_self, zero_add]
  have hbdmem : chainBoundary X (n + 1) Camb ∈ subspaceChains (A ∪ B) (n + 1) := by
    rw [hCore]
    exact chainIncl_rcap_subspaceChains β _ hzbdcov
  have hDPmem : DP ∈ subspaceChains (A ∪ B) (n + 1 + 1) :=
    SingularExcision.iterHomotopy_mem_subspaceChains hbdmem jP
  have hDFmem : DF ∈ subspaceChains (A ∪ B) (n + 1 + 1) := by
    rw [hDF]
    refine (SingularExcisionIso.chainIncl_mem_subspaceChains_iff (A ∪ B) W _).mpr ?_
    have hDmem : SingularSubdivision.iterHomotopy (sub W) (n + 1) jF
          (chainBoundary (sub W) (n + 1) zsub)
        ∈ subspaceChains (Subtype.val ⁻¹' (A ∪ B)) (n + 1 + 1) :=
      SingularExcision.iterHomotopy_mem_subspaceChains
        ((SingularExcisionIso.chainIncl_mem_subspaceChains_iff (A ∪ B) W _).mp hzbdcov) jF
    exact SingularRightCapBoundary.rcap_mem_subspaceChains (X := sub W) (k := n + 1 + 1) (l := 0)
      _ β hDmem
  have hzero := kronecker_boundary_split_V_leg_zero hA hB g hgc hg (DP + DF)
    (Submodule.add_mem _ hDPmem hDFmem)
    (Submodule.add_mem _ ha₁ (chainIncl_rcap_subspaceChains β a₂ ha₂))
    (Submodule.add_mem _ hb₁ (chainIncl_rcap_subspaceChains β b₂ hb₂))
    hsplitE
  rw [kronecker_add_right, add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at hzero
  exact hzero

/-- **Fact-(ii) discharge at the bottom** (mirror of `fact_ii_two_legs_discharge` at `l+1 → 0`;
the F₂-slot is the ONE fundamental presentation `f` — at the bottom BOTH the pd-spelling and the
F-spelling coincide at `n+1+1`, so the generic's recast/`hswap`/T₀-collapse machinery vanishes
and `hQsplit` takes the bare (cast-free) subdivision split. ℤ/2. -/
theorem fact_ii_two_legs_discharge₀ {A B W : Set ↑X} (hA : IsOpen A) (hB : IsOpen B) {n : ℕ}
    (g : ↥(relCoboundaryₗ (A ∩ B) (n + 1)).ker)
    (β : SingularCochain (sub W) 0) (hβ : coboundaryₗ (sub W) 0 β = 0)
    {f : SingularChain X (n + 1 + 1)}
    (hfmem : f ∈ subspaceChains W (n + 1 + 1))
    (hfbd : chainBoundary X (n + 1) f ∈ subspaceChains (A ∪ B) (n + 1))
    (jP : ℕ) {aR : SingularChain (sub (A ∩ W)) (n + 1)} {bR : SingularChain (sub (B ∩ W)) (n + 1)}
    (hP : chainBoundary X (n + 1) ((⇑(SingularSubdivision.singularSd X (n + 1 + 1)))^[jP]
        (chainIncl W (n + 1 + 1) (SingularCapChainIncl.rcap (k := n + 1 + 1) β
          ((SingularSubspaceChainsEquiv.subspaceChainsEquiv W (n + 1 + 1)).symm ⟨f, hfmem⟩))))
      = chainIncl (A ∩ W) (n + 1) aR + chainIncl (B ∩ W) (n + 1) bR)
    (jF : ℕ) {aF : SingularChain (sub (A ∩ W)) (n + 1)}
    {bF : SingularChain (sub (B ∩ W)) (n + 1)}
    (hQsplit : chainBoundary X (n + 1)
        ((⇑(SingularSubdivision.singularSd X (n + 1 + 1)))^[jF] f)
      = chainIncl (A ∩ W) (n + 1) aF + chainIncl (B ∩ W) (n + 1) bF)
    (hbFmem : chainIncl (B ∩ W) (n + 1) bF ∈ subspaceChains W (n + 1))
    (hmem3 : chainIncl W (n + 1) (SingularCapChainIncl.rcap (k := n + 1) β
        ((SingularSubspaceChainsEquiv.subspaceChainsEquiv W (n + 1)).symm ⟨_, hbFmem⟩))
      ∈ subspaceChains (B ∩ W) (n + 1)) :
    kronecker g.1.1 (chainIncl (B ∩ W) (n + 1) bR)
      = kronecker g.1.1 (chainIncl (B ∩ W) (n + 1)
          ((SingularSubspaceChainsEquiv.subspaceChainsEquiv (B ∩ W) (n + 1)).symm
            ⟨_, hmem3⟩)) := by
  classical
  have hgprops := SingularConnSquareRHSPairing.relCocycle_props g
  set zsub := (SingularSubspaceChainsEquiv.subspaceChainsEquiv W (n + 1 + 1)).symm
    ⟨f, hfmem⟩ with hzsubdef
  have hchz := SingularSubspaceChainsEquiv.chainIncl_subspaceChainsEquiv_symm
    (S := W) (n + 1 + 1) ⟨f, hfmem⟩
  have hbdchain : chainIncl W (n + 1) (chainBoundary (sub W) (n + 1) zsub)
      = chainBoundary X (n + 1) f :=
    (SingularRelativeHomologyMod2.chainIncl_chainBoundary W (n + 1) zsub).trans
      (congrArg (chainBoundary X (n + 1)) hchz)
  have hzbdcov : chainIncl W (n + 1) (chainBoundary (sub W) (n + 1) zsub)
      ∈ subspaceChains (A ∪ B) (n + 1) :=
    hbdchain.symm ▸ hfbd
  have hrcbd : chainBoundary (sub W) (n + 1)
        (SingularCapChainIncl.rcap (k := n + 1 + 1) β zsub)
      = SingularCapChainIncl.rcap (k := n + 1) β (chainBoundary (sub W) (n + 1) zsub) :=
    SingularRightCapBoundary.rcap_cocycle_chainMap (k := n + 1) (l := 0) β hβ zsub
  have hCore : chainBoundary X (n + 1)
      (chainIncl W (n + 1 + 1) (SingularCapChainIncl.rcap (k := n + 1 + 1) β zsub))
      = chainIncl W (n + 1) (SingularCapChainIncl.rcap (k := n + 1) β
          (chainBoundary (sub W) (n + 1) zsub)) :=
    (SingularRelativeHomologyMod2.chainIncl_chainBoundary W (n + 1) _).symm.trans
      (congrArg (chainIncl W (n + 1)) hrcbd)
  have ha₁ := SingularMayerVietoris.subspaceChains_mono Set.inter_subset_left (n + 1)
    (⟨aR, rfl⟩ : chainIncl _ (n + 1) aR ∈ subspaceChains _ (n + 1))
  have hb₁ := SingularMayerVietoris.subspaceChains_mono Set.inter_subset_left (n + 1)
    (⟨bR, rfl⟩ : chainIncl _ (n + 1) bR ∈ subspaceChains _ (n + 1))
  have haFmem : chainIncl (A ∩ W) (n + 1) aF ∈ subspaceChains W (n + 1) :=
    SingularMayerVietoris.subspaceChains_mono Set.inter_subset_right (n + 1) ⟨aF, rfl⟩
  have e₆ : chainIncl W (n + 1)
        ((SingularSubspaceChainsEquiv.subspaceChainsEquiv W (n + 1)).symm ⟨_, haFmem⟩)
      = chainIncl (A ∩ W) (n + 1) aF :=
    SingularSubspaceChainsEquiv.chainIncl_subspaceChainsEquiv_symm (S := W) (n + 1) ⟨_, haFmem⟩
  have e₇ : chainIncl W (n + 1)
        ((SingularSubspaceChainsEquiv.subspaceChainsEquiv W (n + 1)).symm ⟨_, hbFmem⟩)
      = chainIncl (B ∩ W) (n + 1) bF :=
    SingularSubspaceChainsEquiv.chainIncl_subspaceChainsEquiv_symm (S := W) (n + 1) ⟨_, hbFmem⟩
  have ha₂ := e₆.symm ▸ SingularMayerVietoris.subspaceChains_mono Set.inter_subset_left
    (n + 1) (⟨aF, rfl⟩ : chainIncl _ (n + 1) aF ∈ subspaceChains _ (n + 1))
  have hb₂ := e₇.symm ▸ SingularMayerVietoris.subspaceChains_mono Set.inter_subset_left
    (n + 1) (⟨bF, rfl⟩ : chainIncl _ (n + 1) bF ∈ subspaceChains _ (n + 1))
  have hQamb : chainIncl W (n + 1)
        (chainBoundary (sub W) (n + 1)
          ((⇑(SingularSubdivision.singularSd (sub W) (n + 1 + 1)))^[jF] zsub))
      = chainIncl W (n + 1)
          ((SingularSubspaceChainsEquiv.subspaceChainsEquiv W (n + 1)).symm ⟨_, haFmem⟩
            + (SingularSubspaceChainsEquiv.subspaceChainsEquiv W (n + 1)).symm ⟨_, hbFmem⟩) :=
    (SingularRelativeHomologyMod2.chainIncl_chainBoundary W (n + 1) _).trans
      (((congrArg (chainBoundary X (n + 1))
          (singularSd_iterate_chainIncl jF zsub).symm).trans
        ((congrArg (fun t => chainBoundary X (n + 1)
            ((⇑(SingularSubdivision.singularSd X (n + 1 + 1)))^[jF] t)) hchz).trans
          (hQsplit.trans
            ((map_add (chainIncl W (n + 1)) _ _).trans
              (congrArg₂ (· + ·) e₆ e₇)).symm))))
  have hQ := SingularRelativeHomologyMod2.chainIncl_injective W (n + 1) hQamb
  exact (gamma_two_legs_close₀ hA hB g.1.1 hgprops.1 g.1.2 β hβ zsub hzbdcov _ jP hCore
    ha₁ hb₁ hP jF ha₂ hb₂ hQ).trans
    (congrArg (kronecker g.1.1)
      (SingularSubspaceChainsEquiv.chainIncl_subspaceChainsEquiv_symm (S := B ∩ W) (n + 1)
        ⟨_, hmem3⟩).symm)

/-! ## B3c — the bottom apex assembly -/

/-- **The per-`K` BOTTOM connecting square** (the apex₀): the MAIN-family `legW (m := 0)` H₁-leg
and the ₀-family `openDuality₀ ∘ legδ` H₀-leg close the connecting square at homology degree `0`.
Mirror of the L2 apex `subHomConnecting_openDuality` body over B1c's `of_chainMatch₀` reducer,
with the B3a/B3b ₀-mirrors at the five `(deg+1)`-floored sites, `fact_i_discharge₀` (B2) and
`fact_ii_two_legs_discharge₀` (B3b) discharging the two Sun facts. Cast-free at the bottom. -/
theorem subHomConnecting_openDuality₀ {N : ℕ} {U V : Set ↑X}
    (hU : IsOpen U) (hV : IsOpen V)
    (z₀ : SingularChain X (N + 1 + 0 + 1)) (hz₀ : chainBoundary X (N + 1 + 0) z₀ = 0)
    (K : SingularCompactsInOpen.CompactsIn (U ∪ V)) (g : cohomGW (U ∪ V) (N + 1) K) :
    SKEFTHawking.SingularSubHomologyMV.subHomConnecting U V hU hV 0
        (SKEFTHawking.SingularOpenDuality.legW (k := N + 1) (m := 0) (hU.union hV) z₀ hz₀ K g)
      = openDuality₀ (k := N + 1) (hU.inter hV) z₀ hz₀
          (SKEFTHawking.SingularCSCMayerVietorisConnecting.legδ U V hU hV N K g) := by
  apply subHomConnecting_openDuality₀_of_chainMatch hU hV z₀ hz₀ K g
  intro g_rep zc0 hzc0 zA zB hcyc hpart a'rep hzBmem σR_rep hσR
  -- ▶ the hmatch₀-close, mirroring the L2 apex body (NC:3554+) at the bottom degrees.
  refine hmatch_close _ _ 0 a'rep _ _ ?_
  refine factB_transport _ _ _ _ ?_
  have hKeq : ((↑K.1 : Set ↑X))ᶜ
      = (↑(legSplitU U V hU hV K).1 : Set ↑X)ᶜ ∩ (↑(legSplitV U V hU hV K).1 : Set ↑X)ᶜ := by
    rw [legSplit_cover U V hU hV K, Set.compl_union]
  -- Bottom simplification vs the apex: the mem_boundaries_of_mk_eq / mk_eq_of_mem_boundaries
  -- round-trip is a no-op detour, and cycle-ness at degree 0 is free (`cycles _ 0 = ⊤`) — go
  -- straight to Kronecker non-degeneracy in `sub (U∩V)`.
  refine mem_boundaries_of_kroneckerH_zero_space _ Submodule.mem_top ?_
  intro β
  have hfundmem2 : fundCycleW₀ (hU.inter hV) z₀ hz₀
      (infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K))
      ∈ subspaceChains (U ∩ V) (N + 1 + 1) :=
    fundCycleW₀_mem_W (hU.inter hV) z₀ hz₀ _
  have hpd_cap : SKEFTHawking.SingularLocalDualityKBot.pullbackDualityₗ₀
      ((↑(infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K)).1 : Set ↑X)ᶜ)
      (U ∩ V)
      (fundCycleW₀ (hU.inter hV) z₀ hz₀
        (infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K)))
      hfundmem2 σR_rep
      = cap (k := N + 2) (m := 0)
          (SingularCapChainIncl.pullbackCochain (U ∩ V) (N + 2) σR_rep.1.1)
          ((subspaceChainsEquiv (U ∩ V) (N + 1 + 1)).symm
            ⟨fundCycleW₀ (hU.inter hV) z₀ hz₀
              (infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K)),
              hfundmem2⟩) :=
    pullbackDualityₗ₀_eq_subcap _ hfundmem2 σR_rep
  have hpd_kronecker : kronecker β.1
      (SKEFTHawking.SingularLocalDualityKBot.pullbackDualityₗ₀
        ((↑(infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K)).1 : Set ↑X)ᶜ)
        (U ∩ V)
        (fundCycleW₀ (hU.inter hV) z₀ hz₀
          (infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K)))
        hfundmem2 σR_rep)
      = kronecker (cup (SingularCapChainIncl.pullbackCochain (U ∩ V) (N + 2) σR_rep.1.1) β.1)
          ((subspaceChainsEquiv (U ∩ V) (N + 1 + 1)).symm
            ⟨fundCycleW₀ (hU.inter hV) z₀ hz₀
              (infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K)),
              hfundmem2⟩) := by
    rw [hpd_cap, SingularCapChainIncl.kronecker_cup_cap]
    rfl
  rw [kronecker_add_right, hpd_kronecker]
  erw [← kronecker_double_pullback]
  -- pd-leg step 1 (cup → ambient σR pairing) at (k := N+2, l := 0):
  erw [← SingularConnSquareClose.kronecker_chainIncl_rcap_eq_cup]
  -- pd-leg step 2 (chain pairing → relKroneckerH class pairing) — the ₀-bridge (B3a-⑤):
  erw [← relKroneckerH_chainIncl_rcap_eq_kronecker₀ _ _ σR_rep β
    (chainIncl_rcap_mem_relCycles₀ _ _ (fundCycleW₀_boundary (hU.inter hV) z₀ hz₀ _) β)]
  -- pd-leg step 3: expose the connecting class (mk-convert, then hσR).
  rw [← show (Submodule.Quotient.mk σR_rep : RelativeCohomology _ (N + 1 + 1))
      = RelativeCohomology.mk _ (N + 1 + 1) σR_rep from rfl]
  erw [hσR]
  -- pd-leg step 4: peel the OUTER relCohomSetCongr (relIncl-refl shape + collapse).
  rw [← SingularTwoCoverBridge.relIncl_refl_apply (Set.Subset.refl _)
    (RelativeHomology.mk _ (N + 1 + 1) _)]
  erw [SingularTwoCoverBridge.relKroneckerH_relCohomSetCongr_relIncl_collapse]
  -- pd-leg step 5: mk-push through the MvConnecting's cohomology argument.
  rw [show (Submodule.Quotient.mk g_rep : RelativeCohomology _ (N + 1))
      = RelativeCohomology.mk _ (N + 1) g_rep from rfl,
    SingularRelCohomSetCongrMk.relCohomSetCongr_mk,
    SingularRelativeCohomologyRestrict.relCohomRestrict_mk]
  -- pd-leg step 6: push the collapse's `▸` through the RelativeHomology.mk, landing over the
  -- union set; the relCycles witness comes from the fund₀ boundary in cover form.
  have hfund₀bdcov : chainBoundary X (N + 1)
      (fundCycleW₀ (hU.inter hV) z₀ hz₀
        (infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K)))
      ∈ subspaceChains ((↑(legSplitU U V hU hV K).1 : Set ↑X)ᶜ
          ∪ (↑(legSplitV U V hU hV K).1 : Set ↑X)ᶜ) (N + 1) := by
    have h := fundCycleW₀_boundary (hU.inter hV) z₀ hz₀
      (infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K))
    rwa [infCompact_compl_legSplit hU hV K] at h
  rw [relHomology_mk_setCongr_transport ((infCompact_compl_legSplit hU hV K).symm) _ _
    (chainIncl_rcap_mem_relCycles₀ _ _ hfund₀bdcov β)]
  -- pd-leg step 7 (whnf dodge + the partition-exposing reduce):
  generalize hRRdef :
    SingularRelativeCohomologyRestrict.relCocycleRestrict (Set.Subset.refl _) (N + 1) = RR
  obtain ⟨jP, uP, wP, hpair2, hsplit2⟩ :=
    SingularConnSquareRHSPairing.rhs_pairing_reduce_partition _ _
      (legSplitU U V hU hV K).1.isCompact'.isClosed.isOpen_compl
      (legSplitV U V hU hV K).1.isCompact'.isClosed.isOpen_compl
      (RR (hKeq ▸ g_rep))
      (chainIncl (U ∩ V) (N + 1 + 1) (SingularCapChainIncl.rcap (k := N + 1 + 1) β.1
        ((subspaceChainsEquiv (U ∩ V) (N + 1 + 1)).symm
          ⟨fundCycleW₀ (hU.inter hV) z₀ hz₀
            (infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K)),
            hfundmem2⟩)))
      (chainIncl_rcap_mem_relCycles₀ _ _ hfund₀bdcov β)
  erw [hpair2]
  -- pd-leg step 8: δ↔∂ adjunction + U-leg drop + cochainSplit↦ω swap.
  erw [kronecker_coboundary_cochainSplit_eq _ _ (RR (hKeq ▸ g_rep)) _ uP wP hsplit2]
  -- pd-leg step 9: realize the V-leg ON sub(U∩V) (support-preserving repartition).
  have hMem0 : chainIncl _ (N + 1) uP + chainIncl _ (N + 1) wP
      ∈ subspaceChains (U ∩ V) (N + 1) :=
    hsplit2 ▸ chainBoundary_singularSd_iterate_chainIncl_mem (T := U ∩ V) jP _
  obtain ⟨aR, bR, hbRchain, hbR⟩ :=
    rhs_realize_V_leg (RR (hKeq ▸ g_rep)).1.1 (RR (hKeq ▸ g_rep)).1.2 uP wP hMem0
  have hsum : kronecker (cochainSplit
        (↑(legSplitU U V hU hV K).1 : Set ↑X)ᶜ (N + 1) (RR (hKeq ▸ g_rep)).1.1)
        (chainIncl _ (N + 1) uP + chainIncl _ (N + 1) wP)
      = kronecker (cochainSplit
        (↑(legSplitU U V hU hV K).1 : Set ↑X)ᶜ (N + 1) (RR (hKeq ▸ g_rep)).1.1)
        (chainIncl _ (N + 1) wP) := by
    rw [kronecker_add_right]
    erw [(mem_relCochains _ _ _).1 (cochainSplit_mem_relCochains _ _ _) _ ⟨uP, rfl⟩, zero_add]
  erw [← kronecker_cochainSplit_V_leg_eq
    (↑(legSplitU U V hU hV K).1 : Set ↑X)ᶜ _ (RR (hKeq ▸ g_rep)) wP, ← hsum, hbR]
  have hbmem : chainIncl _ (N + 1) bR ∈ subspaceChains (U ∩ V) (N + 1) :=
    subspaceChains_mono Set.inter_subset_right (N + 1) ⟨bR, rfl⟩
  erw [show (chainIncl _ (N + 1) bR : SingularChain X (N + 1)) = chainIncl (U ∩ V) (N + 1)
      ((subspaceChainsEquiv (U ∩ V) (N + 1)).symm ⟨_, hbmem⟩) from
    (chainIncl_subspaceChainsEquiv_symm _ _ ⟨_, hbmem⟩).symm,
    kronecker_chainIncl_eq_pullbackCochain]
  -- FINAL MATCH SETUP: un-peel the seam, ℤ/2-convert to the pairing-match shape.
  erw [kronecker_double_pullback]
  rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq]
  -- THE SHARED cover-V-projection of the ONE fund choice, split at the RAW (N+1,0)-spelling
  -- (h := rfl — cast-free bottom); the fund₀-side spellings bridge by defeq ascription.
  obtain ⟨jF, aF, bF, hFsplit⟩ := exists_cast_cover_V_projection
    (legSplitU U V hU hV K).1.isCompact'.isClosed.isOpen_compl
    (legSplitV U V hU hV K).1.isCompact'.isClosed.isOpen_compl
    (rfl : N + 1 + 0 = N + 1 + 0)
    (fundCycleW (k := N + 1) (m := 0) (hU.inter hV) z₀ hz₀
      (infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K)))
    (fundCycleW_mem_W (k := N + 1) (m := 0) (hU.inter hV) z₀ hz₀ _)
    (by
      have h := fundCycleW_boundary (k := N + 1) (m := 0) (hU.inter hV) z₀ hz₀
        (infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K))
      rwa [infCompact_compl_legSplit hU hV K] at h)
  rw [show (cast (congrArg (SingularChain X) (congrArg (· + 1)
      (rfl : N + 1 + 0 = N + 1 + 0)))
      (fundCycleW (k := N + 1) (m := 0) (hU.inter hV) z₀ hz₀
        (infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K))))
      = fundCycleW (k := N + 1) (m := 0) (hU.inter hV) z₀ hz₀
        (infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K)) from rfl] at hFsplit
  have hbFmem : chainIncl _ (N + 1 + 0) bF ∈ subspaceChains (U ∩ V) (N + 1 + 0) :=
    subspaceChains_mono Set.inter_subset_right (N + 1 + 0) ⟨bF, rfl⟩
  -- The pairing-relaxed joint match at the bottom (B3a-③); the TWO SUN FACTS remain.
  refine joint_cap_rcap_match_pairing₀ _ _
    ((subspaceChainsEquiv (U ∩ V) (N + 1 + 0)).symm ⟨_, hbFmem⟩) _ _ ?_ ?_
  -- SUN FACT (i) — fact_i_discharge₀ (B2), fed the RAW (N+1,0)-instance rel-witnesses (no casts).
  · obtain ⟨η₂, a₂, heq₂, ha₂⟩ := fundCycleW_chain_rel (k := N + 1) (m := 0) (hU.inter hV)
      z₀ hz₀ (infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K))
    rw [infCompact_compl_legSplit hU hV K] at ha₂
    have hgg : (RR (hKeq ▸ g_rep)).1.1 = g_rep.1.1 := by
      rw [← hRRdef]
      exact ker_relCoboundary_cast_coe hKeq g_rep
    have hF₂bd : chainBoundary X (N + 1 + 0)
        (fundCycleW (k := N + 1) (m := 0) (hU.inter hV) z₀ hz₀
          (infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K)))
        ∈ subspaceChains ((↑(legSplitU U V hU hV K).1 : Set ↑X)ᶜ
            ∪ (↑(legSplitV U V hU hV K).1 : Set ↑X)ᶜ) (N + 1 + 0) := by
      have h := fundCycleW_boundary (k := N + 1) (m := 0) (hU.inter hV) z₀ hz₀
        (infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K))
      rwa [infCompact_compl_legSplit hU hV K] at h
    exact fact_i_discharge₀ hU hV
      (legSplitU U V hU hV K).1.isCompact'.isClosed.isOpen_compl
      (legSplitV U V hU hV K).1.isCompact'.isClosed.isOpen_compl
      (legSplitU U V hU hV K).2
      (legSplitV U V hU hV K).2
      (RR (hKeq ▸ g_rep)) z₀ hz₀ K g_rep hgg hKeq
      (SingularSubHomologyMV.cover_preimage U V hU hV)
      zc0 hzc0 zA zB hcyc hpart hzBmem _ _
      (chainIncl_seam_boundaryExtract (fun x hx => Or.inl hx.1) (fun q => Iff.rfl))
      _ (fundCycleW_mem_W (k := N + 1) (m := 0) (hU.inter hV) z₀ hz₀ _)
      η₂ a₂ heq₂ ha₂ hF₂bd
      jF aF bF hFsplit hbFmem β
  -- SUN FACT (ii) — fact_ii_two_legs_discharge₀ (B3b) via the pullback-legs assembly.
  · have e₅ : chainIncl (U ∩ V) (N + 1 + 0)
        ((subspaceChainsEquiv (U ∩ V) (N + 1 + 0)).symm ⟨_, hbFmem⟩)
        = chainIncl _ (N + 1 + 0) bF :=
      chainIncl_subspaceChainsEquiv_symm (S := U ∩ V) (N + 1 + 0) ⟨_, hbFmem⟩
    have hmem3 := chainIncl_rcap_subspaceChains β.1 _
      (e₅.symm ▸ (⟨bF, rfl⟩ : chainIncl _ (N + 1 + 0) bF
        ∈ subspaceChains _ (N + 1 + 0)))
    refine pullback_pairing_legs_assemble (RR (hKeq ▸ g_rep)).1.1 β.1 bR hbmem bF hbFmem
      hmem3 ?_
    have hA2 : IsOpen ((↑(legSplitU U V hU hV K).1 : Set ↑X)ᶜ) :=
      (legSplitU U V hU hV K).1.isCompact'.isClosed.isOpen_compl
    have hB2 : IsOpen ((↑(legSplitV U V hU hV K).1 : Set ↑X)ᶜ) :=
      (legSplitV U V hU hV K).1.isCompact'.isClosed.isOpen_compl
    have hP2 := hsplit2.trans hbRchain
    -- Bridge the raw (N+1,0)-spelled split objects to fact_ii₀'s fund₀/(N+1)-spellings by
    -- defeq ascription (fundCycleW₀ = castChain rfl (fundCycleW (N+1,0)) is rfl-collapsible),
    -- so the big application unifies syntactically (no castChain-delta inside the unifier).
    have hfund₀eq : fundCycleW₀ (hU.inter hV) z₀ hz₀
        (infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K))
        = fundCycleW (k := N + 1) (m := 0) (hU.inter hV) z₀ hz₀
            (infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K)) := by
      rw [fundCycleW₀, SingularOpenDualityMVConnSquare.castChain_eq]
    rw [← hfund₀eq] at hFsplit
    have hQsplit₀ : chainBoundary X (N + 1)
        ((⇑(SingularSubdivision.singularSd X (N + 1 + 1)))^[jF]
          (fundCycleW₀ (hU.inter hV) z₀ hz₀
            (infCompact U V (legSplitU U V hU hV K) (legSplitV U V hU hV K))))
        = chainIncl _ (N + 1) aF + chainIncl _ (N + 1) bF := hFsplit
    have hbFmem₀ : chainIncl _ (N + 1) bF ∈ subspaceChains (U ∩ V) (N + 1) := hbFmem
    have hmem3₀ : chainIncl (U ∩ V) (N + 1) (SingularCapChainIncl.rcap (k := N + 1) β.1
        ((subspaceChainsEquiv (U ∩ V) (N + 1)).symm ⟨_, hbFmem₀⟩))
        ∈ subspaceChains ((↑(legSplitV U V hU hV K).1 : Set ↑X)ᶜ ∩ (U ∩ V)) (N + 1) := hmem3
    exact fact_ii_two_legs_discharge₀ (W := U ∩ V) (n := N) hA2 hB2
      (RR (hKeq ▸ g_rep)) β.1 (LinearMap.mem_ker.mp β.2)
      hfundmem2 hfund₀bdcov
      jP hP2 jF hQsplit₀ hbFmem₀ hmem3₀

/-- **The colimit-level BOTTOM `δ` connecting square** (mirror of brick 2a
`subHomConnecting_openDuality_colimit` at the bottom row): `subHomConnecting (D_{U∪V} α) =
D⁰_{U∩V} (cscMvConnecting α)` for every compactly-supported class `α`. With the ₀-family's
`subHomDiag_openDuality₀` / `subHomSum_openDuality₀` (part 3) this completes all the commuting
squares of the `(3,0)`-row ladder at colimit level. Cast-free (the bottom shares the `z₀`-frame). -/
theorem subHomConnecting_openDuality₀_colimit {N : ℕ} {U V : Set ↑X}
    (hU : IsOpen U) (hV : IsOpen V)
    (z₀ : SingularChain X (N + 1 + 0 + 1)) (hz₀ : chainBoundary X (N + 1 + 0) z₀ = 0)
    (α : CompactlySupportedCohomologyOpen (U ∪ V) (N + 1)) :
    SKEFTHawking.SingularSubHomologyMV.subHomConnecting U V hU hV 0
        (openDuality (k := N + 1) (m := 0) (hU.union hV) z₀ hz₀ α)
      = openDuality₀ (k := N + 1) (hU.inter hV) z₀ hz₀
          (cscMvConnecting U V hU hV N α) := by
  induction α using Module.DirectLimit.induction_on with
  | ih K g =>
    rw [openDuality_of, cscMvConnecting_of]
    exact subHomConnecting_openDuality₀ hU hV z₀ hz₀ K g

/-! ## The (3,0)-center Mayer–Vietoris five-lemma step -/

/-- **The (3,0)-center MV five-lemma step**: bijectivity of the duality `D_{U∪V} :
CSCᴺ⁺¹(U∪V) → H₁(sub (U∪V))` from bijectivity on the pieces, via the Mathlib five lemma on the
MV ladder whose window is `cscMvDiag(N+1) → cscMvSum(N+1) → cscMvConnecting N → cscMvDiag(N+2)`
over `subHomDiag 1 → subHomSum 1 → subHomConnecting 0 → subHomDiag 0`, with the four commuting
squares `subHomDiag_openDuality` / `subHomSum_openDuality` (generic, at `m = 0`) /
`subHomConnecting_openDuality₀_colimit` (the bottom square) / `subHomDiag_openDuality₀`. -/
theorem openDuality_union_bijective_bot {N : ℕ} {U V : Set ↑X}
    (hU : IsOpen U) (hV : IsOpen V)
    (z₀ : SingularChain X (N + 1 + 0 + 1)) (hz₀ : chainBoundary X (N + 1 + 0) z₀ = 0)
    (hDI : Function.Surjective (openDuality (k := N + 1) (m := 0) (hU.inter hV) z₀ hz₀))
    (hDU : Function.Bijective (openDuality (k := N + 1) (m := 0) hU z₀ hz₀))
    (hDV : Function.Bijective (openDuality (k := N + 1) (m := 0) hV z₀ hz₀))
    (hD0I : Function.Bijective (openDuality₀ (k := N + 1) (hU.inter hV) z₀ hz₀))
    (hD0U : Function.Injective (openDuality₀ (k := N + 1) hU z₀ hz₀))
    (hD0V : Function.Injective (openDuality₀ (k := N + 1) hV z₀ hz₀)) :
    Function.Bijective (openDuality (k := N + 1) (m := 0) (hU.union hV) z₀ hz₀) := by
  have hc₁ : (subHomDiag U V (0 + 1)).comp
        (openDuality (k := N + 1) (m := 0) (hU.inter hV) z₀ hz₀)
      = ((openDuality (k := N + 1) (m := 0) hU z₀ hz₀).prodMap
          (openDuality (k := N + 1) (m := 0) hV z₀ hz₀)).comp (cscMvDiag U V (N + 1)) := by
    refine LinearMap.ext fun α => ?_
    simp only [LinearMap.comp_apply, LinearMap.prodMap_apply, cscMvDiag, LinearMap.prod_apply,
      Function.prod_def]
    exact subHomDiag_openDuality (k := N + 1) (m := 0) hU hV z₀ hz₀ α
  have hc₂ : (subHomSum U V (0 + 1)).comp
        ((openDuality (k := N + 1) (m := 0) hU z₀ hz₀).prodMap
          (openDuality (k := N + 1) (m := 0) hV z₀ hz₀))
      = (openDuality (k := N + 1) (m := 0) (hU.union hV) z₀ hz₀).comp
          (cscMvSum U V (N + 1)) := by
    refine LinearMap.ext fun p => ?_
    simp only [LinearMap.comp_apply, LinearMap.prodMap_apply]
    exact (subHomSum_openDuality (k := N + 1) (m := 0) hU hV z₀ hz₀ p.1 p.2).symm
  have hc₃ : (SKEFTHawking.SingularSubHomologyMV.subHomConnecting U V hU hV 0).comp
        (openDuality (k := N + 1) (m := 0) (hU.union hV) z₀ hz₀)
      = (openDuality₀ (k := N + 1) (hU.inter hV) z₀ hz₀).comp
          (cscMvConnecting U V hU hV N) := by
    refine LinearMap.ext fun α => ?_
    simp only [LinearMap.comp_apply]
    exact subHomConnecting_openDuality₀_colimit hU hV z₀ hz₀ α
  have hc₄ : (subHomDiag U V 0).comp (openDuality₀ (k := N + 1) (hU.inter hV) z₀ hz₀)
      = ((openDuality₀ (k := N + 1) hU z₀ hz₀).prodMap
          (openDuality₀ (k := N + 1) hV z₀ hz₀)).comp (cscMvDiag U V (N + 2)) := by
    refine LinearMap.ext fun α => ?_
    simp only [LinearMap.comp_apply, LinearMap.prodMap_apply, cscMvDiag, LinearMap.prod_apply,
      Function.prod_def]
    exact subHomDiag_openDuality₀ hU hV z₀ hz₀ α
  have hi₂ : Function.Bijective
      ⇑((openDuality (k := N + 1) (m := 0) hU z₀ hz₀).prodMap
        (openDuality (k := N + 1) (m := 0) hV z₀ hz₀)) := by
    rw [LinearMap.coe_prodMap]
    exact hDU.prodMap hDV
  have hi₅ : Function.Injective
      ⇑((openDuality₀ (k := N + 1) hU z₀ hz₀).prodMap
        (openDuality₀ (k := N + 1) hV z₀ hz₀)) := by
    rw [LinearMap.coe_prodMap]
    exact hD0U.prodMap hD0V
  exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (f₁ := cscMvDiag U V (N + 1)) (f₂ := cscMvSum U V (N + 1))
    (f₃ := cscMvConnecting U V hU hV N) (f₄ := cscMvDiag U V (N + 2))
    (g₁ := subHomDiag U V (0 + 1)) (g₂ := subHomSum U V (0 + 1))
    (g₃ := SKEFTHawking.SingularSubHomologyMV.subHomConnecting U V hU hV 0)
    (g₄ := subHomDiag U V 0)
    (i₁ := openDuality (k := N + 1) (m := 0) (hU.inter hV) z₀ hz₀)
    (i₂ := (openDuality (k := N + 1) (m := 0) hU z₀ hz₀).prodMap
      (openDuality (k := N + 1) (m := 0) hV z₀ hz₀))
    (i₃ := openDuality (k := N + 1) (m := 0) (hU.union hV) z₀ hz₀)
    (i₄ := openDuality₀ (k := N + 1) (hU.inter hV) z₀ hz₀)
    (i₅ := (openDuality₀ (k := N + 1) hU z₀ hz₀).prodMap (openDuality₀ (k := N + 1) hV z₀ hz₀))
    hc₁ hc₂ hc₃ hc₄
    (cscMv_exact_middle U V hU hV) (cscMv_exact_sum U V hU hV)
    (cscMv_exact_connecting U V hU hV)
    (subHom_exact_middle U V hU hV) (subHom_exact_sum U V hU hV)
    (subHom_exact_connecting U V hU hV)
    hDI hi₂ hD0I hi₅

/-! ## The upper (m ≥ 1) Mayer–Vietoris five-lemma step (covers the (2,1)-center at `p := 0`) -/

/-- **The upper-window MV five-lemma step** (all-generic verticals): bijectivity of
`D_{U∪V} : CSCᴺ⁺¹(U∪V) → H_{p+2}(sub (U∪V))` from the pieces. The verticals carry the
castChain-presented `z₀` forms of the generic family, so the connecting square is brick 2a
(`subHomConnecting_openDuality_colimit`) verbatim; the diag/sum squares are the generic
`subHomDiag/Sum_openDuality` at `(N+1, p+1)` and `(N+2, p)`. The `(2,1)`-center of the deg-4
ladder is the `p := 0` instance. -/
theorem openDuality_union_bijective_upper {N p : ℕ} {U V : Set ↑X}
    (hU : IsOpen U) (hV : IsOpen V)
    (z₀ : SingularChain X (N + p + 3)) (hz₀ : chainBoundary X (N + p + 2) z₀ = 0)
    (hDI : Function.Surjective (openDuality (k := N + 1) (m := p + 1) (hU.inter hV)
      (SingularOpenDualityMVConnSquare.castChain
        (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
        z₀ hz₀)))
    (hDU : Function.Bijective (openDuality (k := N + 1) (m := p + 1) hU
      (SingularOpenDualityMVConnSquare.castChain
        (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
        z₀ hz₀)))
    (hDV : Function.Bijective (openDuality (k := N + 1) (m := p + 1) hV
      (SingularOpenDualityMVConnSquare.castChain
        (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
        z₀ hz₀)))
    (hDI' : Function.Bijective (openDuality (k := N + 2) (m := p) (hU.inter hV)
      (SingularOpenDualityMVConnSquare.castChain (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
        z₀ hz₀)))
    (hDU' : Function.Injective (openDuality (k := N + 2) (m := p) hU
      (SingularOpenDualityMVConnSquare.castChain (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
        z₀ hz₀)))
    (hDV' : Function.Injective (openDuality (k := N + 2) (m := p) hV
      (SingularOpenDualityMVConnSquare.castChain (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
        z₀ hz₀))) :
    Function.Bijective (openDuality (k := N + 1) (m := p + 1) (hU.union hV)
      (SingularOpenDualityMVConnSquare.castChain
        (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
        z₀ hz₀)) := by
  have hc₁ : (subHomDiag U V (p + 1 + 1)).comp
        (openDuality (k := N + 1) (m := p + 1) (hU.inter hV) (SingularOpenDualityMVConnSquare.castChain
      (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
        z₀ hz₀))
      = ((openDuality (k := N + 1) (m := p + 1) hU (SingularOpenDualityMVConnSquare.castChain
      (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
        z₀ hz₀)).prodMap
          (openDuality (k := N + 1) (m := p + 1) hV (SingularOpenDualityMVConnSquare.castChain
      (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
        z₀ hz₀))).comp (cscMvDiag U V (N + 1)) := by
    refine LinearMap.ext fun α => ?_
    simp only [LinearMap.comp_apply, LinearMap.prodMap_apply, cscMvDiag, LinearMap.prod_apply,
      Function.prod_def]
    exact subHomDiag_openDuality (k := N + 1) (m := p + 1) hU hV (SingularOpenDualityMVConnSquare.castChain
      (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
        z₀ hz₀) α
  have hc₂ : (subHomSum U V (p + 1 + 1)).comp
        ((openDuality (k := N + 1) (m := p + 1) hU (SingularOpenDualityMVConnSquare.castChain
      (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
        z₀ hz₀)).prodMap
          (openDuality (k := N + 1) (m := p + 1) hV (SingularOpenDualityMVConnSquare.castChain
      (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
        z₀ hz₀)))
      = (openDuality (k := N + 1) (m := p + 1) (hU.union hV) (SingularOpenDualityMVConnSquare.castChain
      (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
        z₀ hz₀)).comp
          (cscMvSum U V (N + 1)) := by
    refine LinearMap.ext fun q => ?_
    simp only [LinearMap.comp_apply, LinearMap.prodMap_apply]
    exact (subHomSum_openDuality (k := N + 1) (m := p + 1) hU hV (SingularOpenDualityMVConnSquare.castChain
      (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
        z₀ hz₀) q.1 q.2).symm
  have hc₃ : (SKEFTHawking.SingularSubHomologyMV.subHomConnecting U V hU hV (p + 1)).comp
        (openDuality (k := N + 1) (m := p + 1) (hU.union hV) (SingularOpenDualityMVConnSquare.castChain
      (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
        z₀ hz₀))
      = (openDuality (k := N + 2) (m := p) (hU.inter hV) (SingularOpenDualityMVConnSquare.castChain
      (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
        z₀ hz₀)).comp
          (cscMvConnecting U V hU hV N) := by
    refine LinearMap.ext fun α => ?_
    simp only [LinearMap.comp_apply]
    exact SKEFTHawking.SingularOpenDualityConnSquareColimit.subHomConnecting_openDuality_colimit
      hU hV z₀ hz₀ α
  have hc₄ : (subHomDiag U V (p + 1)).comp
        (openDuality (k := N + 2) (m := p) (hU.inter hV) (SingularOpenDualityMVConnSquare.castChain
      (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
        z₀ hz₀))
      = ((openDuality (k := N + 2) (m := p) hU (SingularOpenDualityMVConnSquare.castChain
      (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
        z₀ hz₀)).prodMap
          (openDuality (k := N + 2) (m := p) hV (SingularOpenDualityMVConnSquare.castChain
      (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
        z₀ hz₀))).comp (cscMvDiag U V (N + 2)) := by
    refine LinearMap.ext fun α => ?_
    simp only [LinearMap.comp_apply, LinearMap.prodMap_apply, cscMvDiag, LinearMap.prod_apply,
      Function.prod_def]
    exact subHomDiag_openDuality (k := N + 2) (m := p) hU hV (SingularOpenDualityMVConnSquare.castChain
      (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
        z₀ hz₀) α
  have hi₂ : Function.Bijective
      ⇑((openDuality (k := N + 1) (m := p + 1) hU (SingularOpenDualityMVConnSquare.castChain
      (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
        z₀ hz₀)).prodMap
        (openDuality (k := N + 1) (m := p + 1) hV (SingularOpenDualityMVConnSquare.castChain
      (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
        z₀ hz₀))) := by
    rw [LinearMap.coe_prodMap]
    exact hDU.prodMap hDV
  have hi₅ : Function.Injective
      ⇑((openDuality (k := N + 2) (m := p) hU (SingularOpenDualityMVConnSquare.castChain
      (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
        z₀ hz₀)).prodMap
        (openDuality (k := N + 2) (m := p) hV (SingularOpenDualityMVConnSquare.castChain
      (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
        z₀ hz₀))) := by
    rw [LinearMap.coe_prodMap]
    exact hDU'.prodMap hDV'
  exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (f₁ := cscMvDiag U V (N + 1)) (f₂ := cscMvSum U V (N + 1))
    (f₃ := cscMvConnecting U V hU hV N) (f₄ := cscMvDiag U V (N + 2))
    (g₁ := subHomDiag U V (p + 1 + 1)) (g₂ := subHomSum U V (p + 1 + 1))
    (g₃ := SKEFTHawking.SingularSubHomologyMV.subHomConnecting U V hU hV (p + 1))
    (g₄ := subHomDiag U V (p + 1))
    (i₁ := openDuality (k := N + 1) (m := p + 1) (hU.inter hV) (SingularOpenDualityMVConnSquare.castChain
      (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
        z₀ hz₀))
    (i₂ := (openDuality (k := N + 1) (m := p + 1) hU (SingularOpenDualityMVConnSquare.castChain
      (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
        z₀ hz₀)).prodMap
      (openDuality (k := N + 1) (m := p + 1) hV (SingularOpenDualityMVConnSquare.castChain
      (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
        z₀ hz₀)))
    (i₃ := openDuality (k := N + 1) (m := p + 1) (hU.union hV) (SingularOpenDualityMVConnSquare.castChain
      (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
        z₀ hz₀))
    (i₄ := openDuality (k := N + 2) (m := p) (hU.inter hV) (SingularOpenDualityMVConnSquare.castChain
      (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
        z₀ hz₀))
    (i₅ := (openDuality (k := N + 2) (m := p) hU (SingularOpenDualityMVConnSquare.castChain
      (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
        z₀ hz₀)).prodMap
      (openDuality (k := N + 2) (m := p) hV (SingularOpenDualityMVConnSquare.castChain
      (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
      (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
        z₀ hz₀)))
    hc₁ hc₂ hc₃ hc₄
    (cscMv_exact_middle U V hU hV) (cscMv_exact_sum U V hU hV)
    (cscMv_exact_connecting U V hU hV)
    (subHom_exact_middle U V hU hV) (subHom_exact_sum U V hU hV)
    (subHom_exact_connecting U V hU hV)
    hDI hi₂ hDI' hi₅

/-! ## The D⁰ Mayer–Vietoris five-lemma step (the truncated ladder at H₀) -/

/-- **The D⁰ MV five-lemma step** (the LAST five-lemma of the PD-induction ladder): bijectivity
of `D⁰_{U∪V} : CSCᴺ⁺²(U∪V) → H₀(sub (U∪V))` from the pieces. The homology row is EXTENDED BY THE
ZERO MODULE (`PUnit`) below `H₀`: the far verticals are zero maps whose bijectivity/injectivity
is exactly the csc-top vanishing (`hvan…`, supplied by the geometry at the induction stage via
`cscOpen_eq_zero_of_isOpen`); exactness past `subHomSum 0` degenerates to
`subHomSum_zero_surjective` (track A) and a triviality; `hg₁` is `subHom_exact_middle₀`. -/
theorem openDuality₀_union_bijective {N : ℕ} {U V : Set ↑X}
    (hU : IsOpen U) (hV : IsOpen V)
    (z₀ : SingularChain X (N + 1 + 0 + 1)) (hz₀ : chainBoundary X (N + 1 + 0) z₀ = 0)
    (hvanI : ∀ α : CompactlySupportedCohomologyOpen (U ∩ V) (N + 1 + 2), α = 0)
    (hvanU : ∀ α : CompactlySupportedCohomologyOpen U (N + 1 + 2), α = 0)
    (hvanV : ∀ α : CompactlySupportedCohomologyOpen V (N + 1 + 2), α = 0)
    (hD0I : Function.Surjective (openDuality₀ (k := N + 1) (hU.inter hV) z₀ hz₀))
    (hD0U : Function.Bijective (openDuality₀ (k := N + 1) hU z₀ hz₀))
    (hD0V : Function.Bijective (openDuality₀ (k := N + 1) hV z₀ hz₀)) :
    Function.Bijective (openDuality₀ (k := N + 1) (hU.union hV) z₀ hz₀) := by
  have hc₁ : (subHomDiag U V 0).comp (openDuality₀ (k := N + 1) (hU.inter hV) z₀ hz₀)
      = ((openDuality₀ (k := N + 1) hU z₀ hz₀).prodMap
          (openDuality₀ (k := N + 1) hV z₀ hz₀)).comp (cscMvDiag U V (N + 1 + 1)) := by
    refine LinearMap.ext fun α => ?_
    simp only [LinearMap.comp_apply, LinearMap.prodMap_apply, cscMvDiag, LinearMap.prod_apply,
      Function.prod_def]
    exact subHomDiag_openDuality₀ hU hV z₀ hz₀ α
  have hc₂ : (subHomSum U V 0).comp
        ((openDuality₀ (k := N + 1) hU z₀ hz₀).prodMap (openDuality₀ (k := N + 1) hV z₀ hz₀))
      = (openDuality₀ (k := N + 1) (hU.union hV) z₀ hz₀).comp (cscMvSum U V (N + 1 + 1)) := by
    refine LinearMap.ext fun p => ?_
    simp only [LinearMap.comp_apply, LinearMap.prodMap_apply]
    exact (subHomSum_openDuality₀ hU hV z₀ hz₀ p.1 p.2).symm
  have hc₃ : (0 : Homology (sub (U ∪ V)) 0 →ₗ[ZMod 2] PUnit.{1}).comp
        (openDuality₀ (k := N + 1) (hU.union hV) z₀ hz₀)
      = (0 : CompactlySupportedCohomologyOpen (U ∩ V) (N + 1 + 2) →ₗ[ZMod 2] PUnit.{1}).comp
          (cscMvConnecting U V hU hV (N + 1)) :=
    LinearMap.ext fun _ => Subsingleton.elim _ _
  have hc₄ : (0 : PUnit.{1} →ₗ[ZMod 2] PUnit.{1}).comp
        (0 : CompactlySupportedCohomologyOpen (U ∩ V) (N + 1 + 2) →ₗ[ZMod 2] PUnit.{1})
      = ((0 : CompactlySupportedCohomologyOpen U (N + 1 + 2)
            × CompactlySupportedCohomologyOpen V (N + 1 + 2) →ₗ[ZMod 2] PUnit.{1})).comp
          (cscMvDiag U V (N + 1 + 2)) :=
    LinearMap.ext fun _ => Subsingleton.elim _ _
  have hg₂ : Function.Exact (subHomSum U V 0)
      (0 : Homology (sub (U ∪ V)) 0 →ₗ[ZMod 2] PUnit.{1}) := by
    intro y
    exact ⟨fun _ => SKEFTHawking.SingularSubHomSumEnd.subHomSum_zero_surjective U V y,
      fun _ => rfl⟩
  have hg₃ : Function.Exact (0 : Homology (sub (U ∪ V)) 0 →ₗ[ZMod 2] PUnit.{1})
      (0 : PUnit.{1} →ₗ[ZMod 2] PUnit.{1}) := by
    intro y
    exact ⟨fun _ => ⟨0, Subsingleton.elim _ _⟩, fun _ => Subsingleton.elim _ _⟩
  have hi₂ : Function.Bijective
      ⇑((openDuality₀ (k := N + 1) hU z₀ hz₀).prodMap (openDuality₀ (k := N + 1) hV z₀ hz₀)) := by
    rw [LinearMap.coe_prodMap]
    exact hD0U.prodMap hD0V
  have hi₄ : Function.Bijective
      ⇑(0 : CompactlySupportedCohomologyOpen (U ∩ V) (N + 1 + 2) →ₗ[ZMod 2] PUnit.{1}) :=
    ⟨fun a b _ => (hvanI a).trans (hvanI b).symm, fun y => ⟨0, Subsingleton.elim _ _⟩⟩
  have hi₅ : Function.Injective
      ⇑(0 : CompactlySupportedCohomologyOpen U (N + 1 + 2)
          × CompactlySupportedCohomologyOpen V (N + 1 + 2) →ₗ[ZMod 2] PUnit.{1}) :=
    fun p q _ => Prod.ext ((hvanU p.1).trans (hvanU q.1).symm)
      ((hvanV p.2).trans (hvanV q.2).symm)
  exact LinearMap.bijective_of_surjective_of_bijective_of_bijective_of_injective
    (f₁ := cscMvDiag U V (N + 1 + 1)) (f₂ := cscMvSum U V (N + 1 + 1))
    (f₃ := cscMvConnecting U V hU hV (N + 1)) (f₄ := cscMvDiag U V (N + 1 + 2))
    (g₁ := subHomDiag U V 0) (g₂ := subHomSum U V 0)
    (g₃ := (0 : Homology (sub (U ∪ V)) 0 →ₗ[ZMod 2] PUnit.{1}))
    (g₄ := (0 : PUnit.{1} →ₗ[ZMod 2] PUnit.{1}))
    (i₁ := openDuality₀ (k := N + 1) (hU.inter hV) z₀ hz₀)
    (i₂ := (openDuality₀ (k := N + 1) hU z₀ hz₀).prodMap (openDuality₀ (k := N + 1) hV z₀ hz₀))
    (i₃ := openDuality₀ (k := N + 1) (hU.union hV) z₀ hz₀)
    (i₄ := (0 : CompactlySupportedCohomologyOpen (U ∩ V) (N + 1 + 2) →ₗ[ZMod 2] PUnit.{1}))
    (i₅ := (0 : CompactlySupportedCohomologyOpen U (N + 1 + 2)
        × CompactlySupportedCohomologyOpen V (N + 1 + 2) →ₗ[ZMod 2] PUnit.{1}))
    hc₁ hc₂ hc₃ hc₄
    (cscMv_exact_middle U V hU hV) (cscMv_exact_sum U V hU hV)
    (cscMv_exact_connecting U V hU hV)
    (SKEFTHawking.SingularMayerVietorisLESBot.subHom_exact_middle₀ U V hU hV) hg₂ hg₃
    hD0I hi₂ hi₄ hi₅

/-- **Monotone-union stability for the ₀-duality** (the arc-2 generic core
`duality_monotone_union_bijective` instantiated at `D := openDuality₀`, `d := 0` — the payoff
deferred from wt1, where the ₀-family modules were unavailable). -/
theorem openDuality₀_monotone_union_bijective {k : ℕ} {W : ℕ → Set ↑X}
    (hmono : ∀ n, W n ⊆ W (n + 1)) (hopen : ∀ n, IsOpen (W n))
    (z₀ : SingularChain X (k + 0 + 1)) (hz₀ : chainBoundary X (k + 0) z₀ = 0)
    (hbij : ∀ n, Function.Bijective (openDuality₀ (k := k) (hopen n) z₀ hz₀)) :
    Function.Bijective (openDuality₀ (k := k) (isOpen_iUnion hopen) z₀ hz₀) :=
  SingularOpenDualityMonotoneUnion.duality_monotone_union_bijective (k := k + 1) (d := 0)
    hmono hopen (fun _V hV => openDuality₀ (k := k) hV z₀ hz₀)
    (fun _V _V' hV hV' hVV' α => openDuality₀_cscOpenMonotone hV hV' hVV' z₀ hz₀ α) hbij

end SKEFTHawking.SingularConnSquareCloseNCBotApex
