import Mathlib
import SKEFTHawking.SingularCapSubKDuality
import SKEFTHawking.SingularRightCapBoundary
import SKEFTHawking.SingularOpenDualityCycle
import SKEFTHawking.SingularExcision

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4) — relative rcap-homology-invariance (BRICK 1)

The two-cover bridge's residual `hcross` (in `SingularTwoCoverBridge`) is a homology-class identity in
`H(M, (↑K)ᶜ)` between two `rcap`-realizations of the SAME global cycle `z₀`, capped with two distinct
`Classical.choice` fundamental-cycle witnesses (`z_K` over the union, `z_J` over the intersection). Each
witness is rel-homologous to `z₀` via `SingularOpenDualityCycle.fundCycleW_relHomologous`. To collapse
the two-witness gap we need: **the operation `z ↦ [chainIncl K (rcap b z_sub)]` depends only on the
relative homology class of `z`** (over the cap-target subspace `S`). This is the right-cap (`rcap`)
relative mirror of the absolute `SingularCapHomology.capHomology` / `capHomology_mk`, built on the same
`{K, S}`-small-witness move that `SingularLocalDualityKCycle.relativeDualityK_cycle_compat` uses for the
left cap.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularLocalDualityK SKEFTHawking.SingularCapChainIncl
  SKEFTHawking.SingularSubspaceChainsEquiv SKEFTHawking.SingularCapSubKDuality
  SKEFTHawking.SingularRightCapBoundary SKEFTHawking.SingularExcision
  SKEFTHawking.SingularExcisionIso

namespace SKEFTHawking.SingularRcapRelHomology

variable {X : TopCat}

/-- **The realized rcap of a `K`-supported relative-`S`-boundary is a relative-`S` boundary** (the
right-cap mirror of `SingularLocalDualityKCycle.cap_pullback_mem_boundaries_of_relBoundaryW`,
chain-level core). For a `sub K`-cocycle `a'`, a `K`-supported `u` and a `K`-supported witness `wW`
with `u + ∂wW ∈ C(S)`, the realized right cap `chainIncl K (a' ⌢ʳ u_sub)` is a relative-`S` boundary,
witnessed by `chainIncl K (a' ⌢ʳ wW_sub)`. Indeed `∂(chainIncl K (a' ⌢ʳ wW_sub)) =
chainIncl K (a' ⌢ʳ (∂wW)_sub)` (`rcap_cocycle_chainMap` + `chainIncl_chainBoundary`), and over `S` the
`(z+z')`-part is what we want while the residual `S`-part of `∂wW` is killed by `rcap`/`chainIncl`
locality. -/
theorem chainIncl_rcap_mem_relBoundaries_of_relBoundaryK {k m : ℕ} {S K : Set ↑X}
    (a' : LinearMap.ker (coboundaryₗ (sub K) (m + 1)))
    (u : SingularChain X (k + 1 + m + 1)) (wW : SingularChain X (k + 1 + m + 1 + 1))
    (huK : u ∈ subspaceChains K (k + 1 + m + 1))
    (hwWK : wW ∈ subspaceChains K (k + 1 + m + 1 + 1))
    (hrel : u + chainBoundary X (k + 1 + m + 1) wW ∈ subspaceChains S (k + 1 + m + 1)) :
    RelativeChain.mk S (k + 1)
        (chainIncl K (k + 1) (rcap a'.1 ((subspaceChainsEquiv K (k + 1 + m + 1)).symm ⟨u, huK⟩)))
      ∈ relBoundaries S (k + 1) := by
  -- The boundary witness: the realized rcap of the `K`-supported homotopy chain `wW`.
  have e0 : k + 1 + m + 1 = k + 1 + (m + 1) := by omega
  refine ⟨RelativeChain.mk S (k + 2)
      (chainIncl K (k + 2)
        (rcap a'.1 ((by omega : k + 1 + (m + 1) + 1 = k + 1 + 1 + (m + 1)) ▸
          (congrArg (· + 1) e0 ▸ (subspaceChainsEquiv K (k + 1 + m + 1 + 1)).symm ⟨wW, hwWK⟩)))), ?_⟩
  rw [relBoundary_mk]
  refine (Submodule.Quotient.eq _).mpr ?_
  -- Push `∂` inside `chainIncl`, then turn `∂_{sub K}(rcap a' wW_sub)` into `rcap a' (∂_{sub K} wW_sub)`.
  rw [← chainIncl_chainBoundary]
  have key := rcap_cocycle_chainMap (X := sub K) (k := k + 1) (l := m + 1) a'.1
    (LinearMap.mem_ker.mp a'.2)
    (congrArg (· + 1) e0 ▸ (subspaceChainsEquiv K (k + 1 + m + 1 + 1)).symm ⟨wW, hwWK⟩)
  rw [key, ← map_sub, chainIncl_mem_subspaceChains_iff S K, ← map_sub]
  apply rcap_mem_subspaceChains
  -- Reflect to ambient: it suffices that `∂wW + u ∈ C(S)` (which is `hrel`).
  rw [← chainIncl_mem_subspaceChains_iff S K, map_sub]
  -- `chainIncl K (∂_{sub K}(cast wW_sub)) = ∂wW`, `chainIncl K u_sub = u`.
  have hbd : chainIncl K (k + 1 + (m + 1))
      ((chainBoundary (sub K) (k + 1 + (m + 1)))
        (congrArg (· + 1) e0 ▸ (subspaceChainsEquiv K (k + 1 + m + 1 + 1)).symm ⟨wW, hwWK⟩))
      = chainBoundary X (k + 1 + m + 1) wW := by
    rw [chainIncl_chainBoundary]
    congr 1
    exact chainIncl_subspaceChainsEquiv_symm K (k + 1 + m + 1 + 1) ⟨wW, hwWK⟩
  have hu_incl : chainIncl K (k + 1 + (m + 1))
      ((subspaceChainsEquiv K (k + 1 + m + 1)).symm ⟨u, huK⟩) = u :=
    chainIncl_subspaceChainsEquiv_symm K (k + 1 + m + 1) ⟨u, huK⟩
  rw [hbd, hu_incl]
  -- `∂wW - u = ∂wW + u = u + ∂wW ∈ C(S)` (over ℤ/2), which is `hrel`.
  have hsub : chainBoundary X (k + 1 + m + 1) wW - u = u + chainBoundary X (k + 1 + m + 1) wW := by
    rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left (ZModModule.add_self u)]
    exact add_comm _ _
  rw [hsub]
  exact hrel

/-- **BRICK 1 (relative rcap-homology-invariance), boundary form.** If `z`, `z'` are two `K`-supported
chains with `∂ ∈ C(S)` that are relatively homologous over `S` (general witness `w`), and the cover
`{K, S}` is excisive, then the two realized right caps `chainIncl K (a' ⌢ʳ z_sub)` and
`chainIncl K (a' ⌢ʳ z'_sub)` differ by a relative-`S` boundary. The `{K, S}`-small-witness move
(`relative_small_boundary` + two-cover split) extracts a `K`-supported homotopy witness `wW`, on which
the chain-level core `chainIncl_rcap_mem_relBoundaries_of_relBoundaryK` fires. -/
theorem chainIncl_rcap_add_mem_relBoundaries_of_relHomologous {k m : ℕ} {S K : Set ↑X}
    (z z' : SingularChain X (k + 1 + m + 1))
    (hzK : z ∈ subspaceChains K (k + 1 + m + 1)) (hz'K : z' ∈ subspaceChains K (k + 1 + m + 1))
    (hzS : chainBoundary X (k + 1 + m) z ∈ subspaceChains S (k + 1 + m))
    (hz'S : chainBoundary X (k + 1 + m) z' ∈ subspaceChains S (k + 1 + m))
    (hcov : (⋃ U ∈ ({K, S} : Set (Set ↑X)), interior U) = Set.univ)
    (w : SingularChain X (k + 1 + m + 1 + 1))
    (hw : (z + z') + chainBoundary X (k + 1 + m + 1) w ∈ subspaceChains S (k + 1 + m + 1))
    (a' : LinearMap.ker (coboundaryₗ (sub K) (m + 1))) :
    RelativeChain.mk S (k + 1)
        (chainIncl K (k + 1) (rcap a'.1 ((subspaceChainsEquiv K (k + 1 + m + 1)).symm ⟨z, hzK⟩)))
      + RelativeChain.mk S (k + 1)
        (chainIncl K (k + 1) (rcap a'.1 ((subspaceChainsEquiv K (k + 1 + m + 1)).symm ⟨z', hz'K⟩)))
      ∈ relBoundaries S (k + 1) := by
  -- Step 1: take the relative-boundary witness `{K, S}`-small (`relative_small_boundary`).
  have hsmall : z + z' ∈ smallChains ({K, S} : Set (Set ↑X)) (k + 1 + m + 1) :=
    subspaceChains_le_smallChains (Set.mem_insert _ _) (k + 1 + m + 1) (Submodule.add_mem _ hzK hz'K)
  have hrcyc : chainBoundary X (k + 1 + m) (z + z') ∈ subspaceChains S (k + 1 + m) := by
    rw [map_add]; exact Submodule.add_mem _ hzS hz'S
  obtain ⟨w', hw'small, hw'rel⟩ := relative_small_boundary hcov hsmall hrcyc hw
  -- Step 2: split the small witness `w' = wW + wS` (K-part + S-part); the K-part is itself a witness.
  obtain ⟨wW, hwW, wS, hwS, hsplit⟩ :=
    Submodule.mem_sup.mp (smallChains_two_le K S (k + 1 + m + 1 + 1) hw'small)
  have hwWrel : (z + z') + chainBoundary X (k + 1 + m + 1) wW ∈ subspaceChains S (k + 1 + m + 1) := by
    have hbdeq : chainBoundary X (k + 1 + m + 1) wW
        = chainBoundary X (k + 1 + m + 1) w' - chainBoundary X (k + 1 + m + 1) wS :=
      eq_sub_of_add_eq (by rw [← map_add, hsplit])
    rw [hbdeq, ← add_sub_assoc]
    exact Submodule.sub_mem _ hw'rel (chainBoundary_mem_subspaceChains S (k + 1 + m + 1) wS hwS)
  -- Step 3: the chain-level core gives the realized rcap of `z+z'` is a relative-`S` boundary.
  have hcore := chainIncl_rcap_mem_relBoundaries_of_relBoundaryK a' (z + z') wW
    (Submodule.add_mem _ hzK hz'K) hwW hwWrel
  -- Step 4: split the realized rcap of `z+z'` into the two summands and conclude.
  have hsymmadd : ((subspaceChainsEquiv K (k + 1 + m + 1)).symm ⟨z, hzK⟩)
        + ((subspaceChainsEquiv K (k + 1 + m + 1)).symm ⟨z', hz'K⟩)
      = (subspaceChainsEquiv K (k + 1 + m + 1)).symm ⟨z + z', Submodule.add_mem _ hzK hz'K⟩ := by
    rw [← map_add]; congr 1
  have hmkadd : RelativeChain.mk S (k + 1)
        (chainIncl K (k + 1) (rcap a'.1 ((subspaceChainsEquiv K (k + 1 + m + 1)).symm ⟨z, hzK⟩)))
      + RelativeChain.mk S (k + 1)
        (chainIncl K (k + 1) (rcap a'.1 ((subspaceChainsEquiv K (k + 1 + m + 1)).symm ⟨z', hz'K⟩)))
      = RelativeChain.mk S (k + 1)
        (chainIncl K (k + 1)
          (rcap a'.1 ((subspaceChainsEquiv K (k + 1 + m + 1)).symm
            ⟨z + z', Submodule.add_mem _ hzK hz'K⟩))) := by
    have hadd : chainIncl K (k + 1) (rcap a'.1 ((subspaceChainsEquiv K (k + 1 + m + 1)).symm ⟨z, hzK⟩))
          + chainIncl K (k + 1) (rcap a'.1 ((subspaceChainsEquiv K (k + 1 + m + 1)).symm ⟨z', hz'K⟩))
        = chainIncl K (k + 1)
            (rcap a'.1 ((subspaceChainsEquiv K (k + 1 + m + 1)).symm
              ⟨z + z', Submodule.add_mem _ hzK hz'K⟩)) := by
      rw [← map_add, ← map_add, hsymmadd]
    show Submodule.Quotient.mk _ + Submodule.Quotient.mk _ = Submodule.Quotient.mk _
    rw [← hadd]
    rfl
  rw [hmkadd]
  exact hcore

/-- **BRICK 1 (relative rcap-homology-invariance), class form.** The relative homology class
`[chainIncl K (a' ⌢ʳ z_sub)]` in `H(X, S)` depends only on the relative homology class of the
`K`-supported cycle `z`: two `K`-supported `z`, `z'` (each `∂ ∈ C(S)`) that are relatively homologous
over `S` (`{K, S}` excisive) realize **equal** relative homology classes. The homology-variable
well-definedness of the realized right-cap duality — the right-cap relative mirror of
`SingularLocalDualityKCycle.relativeDualityK_cycle_compat`. -/
theorem relHomology_mk_chainIncl_rcap_eq_of_relHomologous {k m : ℕ} {S K : Set ↑X}
    (z z' : SingularChain X (k + 1 + m + 1))
    (hzK : z ∈ subspaceChains K (k + 1 + m + 1)) (hz'K : z' ∈ subspaceChains K (k + 1 + m + 1))
    (hzS : chainBoundary X (k + 1 + m) z ∈ subspaceChains S (k + 1 + m))
    (hz'S : chainBoundary X (k + 1 + m) z' ∈ subspaceChains S (k + 1 + m))
    (hcov : (⋃ U ∈ ({K, S} : Set (Set ↑X)), interior U) = Set.univ)
    (w : SingularChain X (k + 1 + m + 1 + 1))
    (hw : (z + z') + chainBoundary X (k + 1 + m + 1) w ∈ subspaceChains S (k + 1 + m + 1))
    (a' : LinearMap.ker (coboundaryₗ (sub K) (m + 1))) :
    RelativeHomology.mk S (k + 1)
        ⟨RelativeChain.mk S (k + 1)
          (chainIncl K (k + 1) (rcap a'.1 ((subspaceChainsEquiv K (k + 1 + m + 1)).symm ⟨z, hzK⟩))),
          chainIncl_rcap_mem_relCycles z hzK hzS a'⟩
      = RelativeHomology.mk S (k + 1)
        ⟨RelativeChain.mk S (k + 1)
          (chainIncl K (k + 1) (rcap a'.1 ((subspaceChainsEquiv K (k + 1 + m + 1)).symm ⟨z', hz'K⟩))),
          chainIncl_rcap_mem_relCycles z' hz'K hz'S a'⟩ := by
  refine (Submodule.Quotient.eq _).mpr ?_
  rw [Submodule.submoduleOf, Submodule.mem_comap]
  -- The class difference is the relative-`S` boundary produced by the boundary-form invariance.
  have hbd := chainIncl_rcap_add_mem_relBoundaries_of_relHomologous z z' hzK hz'K hzS hz'S hcov w hw a'
  -- `⟨A,_⟩ - ⟨B,_⟩` has underlying chain `A + B` (over ℤ/2, `- = +`); match it to `hbd`.
  show RelativeChain.mk S (k + 1)
      (chainIncl K (k + 1) (rcap a'.1 ((subspaceChainsEquiv K (k + 1 + m + 1)).symm ⟨z, hzK⟩)))
    - RelativeChain.mk S (k + 1)
      (chainIncl K (k + 1) (rcap a'.1 ((subspaceChainsEquiv K (k + 1 + m + 1)).symm ⟨z', hz'K⟩)))
    ∈ relBoundaries S (k + 1)
  rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left (ZModModule.add_self _)]
  exact hbd

open SKEFTHawking.SingularOpenDualityCycle SKEFTHawking.SingularCompactsInOpen
  SKEFTHawking.SingularFundCycleOpen

variable [T2Space ↑X]

/-- **BRICK 1 (the `fundCycleW` two-witness collapse).** This is the form that directly shrinks the
two-cover bridge residual `hcross`: the realized right cap of the per-`K` fundamental cycle
`z_K = fundCycleW W z₀ K` (one `Classical.choice` of the global cycle `z₀`) realizes the **same**
relative homology class in `H(X, (↑K)ᶜ)` as the realized right cap of the global ancestor `z₀` itself.
Both are `W`-supported with `∂ ∈ C((↑K)ᶜ)`, and they are relatively homologous over `(↑K)ᶜ` by
`fundCycleW_relHomologous`, so the class-form invariance
`relHomology_mk_chainIncl_rcap_eq_of_relHomologous` collapses the two-witness gap. Capping with `b`
under `[b] = absCohomConn[a']` then makes `hcross` an identity purely between `z₀`-realized classes. -/
theorem relHomology_mk_chainIncl_rcap_fundCycleW_eq {k m : ℕ} {W : Set ↑X} (hW : IsOpen W)
    (z₀ : SingularChain X (k + 1 + m + 1)) (hz₀ : chainBoundary X (k + 1 + m) z₀ = 0)
    (K : CompactsIn W) (b : LinearMap.ker (coboundaryₗ (sub W) (m + 1)))
    (hz₀W : z₀ ∈ subspaceChains W (k + 1 + m + 1))
    (hzKbd : chainBoundary X (k + 1 + m) (fundCycleW hW z₀ hz₀ K)
      ∈ subspaceChains ((↑K.1 : Set ↑X)ᶜ) (k + 1 + m)) :
    RelativeHomology.mk ((↑K.1 : Set ↑X)ᶜ) (k + 1)
        ⟨RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + 1)
          (chainIncl W (k + 1) (rcap b.1
            ((subspaceChainsEquiv W (k + 1 + m + 1)).symm
              ⟨fundCycleW hW z₀ hz₀ K, fundCycleW_mem_W hW z₀ hz₀ K⟩))),
          chainIncl_rcap_mem_relCycles (fundCycleW hW z₀ hz₀ K) (fundCycleW_mem_W hW z₀ hz₀ K) hzKbd b⟩
      = RelativeHomology.mk ((↑K.1 : Set ↑X)ᶜ) (k + 1)
        ⟨RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + 1)
          (chainIncl W (k + 1) (rcap b.1
            ((subspaceChainsEquiv W (k + 1 + m + 1)).symm ⟨z₀, hz₀W⟩))),
          chainIncl_rcap_mem_relCycles z₀ hz₀W
            (by rw [hz₀]; exact Submodule.zero_mem _) b⟩ := by
  -- The `{W, (↑K)ᶜ}` cover is excisive (`K.1` compact ⊆ open `W`).
  have hcov : (⋃ U ∈ ({W, ((↑K.1 : Set ↑X)ᶜ)} : Set (Set ↑X)), interior U) = Set.univ :=
    interiors_cover_of_compact_subset_open K.1.isCompact' hW K.2
  -- The rel-homology witness `z_K ≡ z₀ (mod C((↑K)ᶜ))` from `fundCycleW_relHomologous`.
  obtain ⟨wRel, hwRel⟩ := fundCycleW_relHomologous hW z₀ hz₀ K
  obtain ⟨w, rfl⟩ := Submodule.Quotient.mk_surjective _ wRel
  have hw : (fundCycleW hW z₀ hz₀ K + z₀) + chainBoundary X (k + 1 + m + 1) w
      ∈ subspaceChains ((↑K.1 : Set ↑X)ᶜ) (k + 1 + m + 1) := by
    rw [← RelativeChain.mk_eq_zero_iff]
    show Submodule.Quotient.mk _ = 0
    rw [Submodule.Quotient.mk_add, Submodule.Quotient.mk_add,
      show (Submodule.Quotient.mk (chainBoundary X (k + 1 + m + 1) w)
          : RelativeChain ((↑K.1 : Set ↑X)ᶜ) (k + 1 + m + 1))
        = RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + 1 + m + 1) z₀
          + RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + 1 + m + 1) (fundCycleW hW z₀ hz₀ K) from hwRel]
    show (RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + 1 + m + 1) (fundCycleW hW z₀ hz₀ K)
        + RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + 1 + m + 1) z₀)
      + (RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + 1 + m + 1) z₀
        + RelativeChain.mk ((↑K.1 : Set ↑X)ᶜ) (k + 1 + m + 1) (fundCycleW hW z₀ hz₀ K)) = 0
    abel_nf
    rw [two_smul, two_smul, ZModModule.add_self, ZModModule.add_self, add_zero]
  exact relHomology_mk_chainIncl_rcap_eq_of_relHomologous (fundCycleW hW z₀ hz₀ K) z₀
    (fundCycleW_mem_W hW z₀ hz₀ K) hz₀W hzKbd (by rw [hz₀]; exact Submodule.zero_mem _)
    hcov w hw b

end SKEFTHawking.SingularRcapRelHomology
