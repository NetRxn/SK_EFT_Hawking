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
  SKEFTHawking.SingularConnSquareMatchLHS SKEFTHawking.SingularConnSquareCloseNC
  SKEFTHawking.SingularMayerVietoris

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

end SKEFTHawking.SingularConnSquareCloseNCBotApex
