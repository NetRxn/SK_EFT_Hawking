import Mathlib
import SKEFTHawking.SingularConnSquareRHSScaffold
import SKEFTHawking.SingularRelMvDeltaPartition

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4) — the W5-dance RHS reduction of the connecting-square `hcore`

`rhs_dance` is the complete, kernel-pure reduction of the connecting-square match's RHS
(`kroneckerH a' (relativeDualityK … (relCohomMvConnecting g↾))`) to the connecting-INPUT pairing
`kronecker σ.1.1 w` (`w` the V-part of `∂(Sdᵐ(rcap chain))`). Unlike the mis-aimed
`SingularConnSquareRHSScaffold.rhs_relativeDualityK_to_input` (whose `relMvDelta_pairing` needs the
un-subdivided rcap chain cover-fine — not satisfiable for `z_J`), this subdivides the **rcap chain** and
uses `relMvDelta`'s class-invariance (`relHomology_mk_singularSd_iterate`) + `relMvDelta_cover_partition`
(M9b). Chain: M4 → cover-fine subdivision → rep-swap → M9b → `relKronecker_mk`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2

namespace SKEFTHawking.SingularConnSquareRHSDance

open SKEFTHawking.SingularConnSquareRHSN2 SKEFTHawking.SingularLocalDualityK
  SKEFTHawking.SingularRelativeCohomologyMVConnecting SKEFTHawking.SingularCompactlySupportedTop
  SKEFTHawking.SingularCapChainIncl SKEFTHawking.SingularSubspaceChainsEquiv
  SKEFTHawking.SingularConnSquareRHSScaffold SKEFTHawking.SingularRelMvDeltaPartition

variable {X : TopCat}

/-- **The correct W5-dance RHS reduction** of the connecting-square `hcore`: reduces the RHS to the
connecting-INPUT pairing `⟨σ, w⟩` (`w` the V-part of `∂(Sdᵐ(rcap chain))`). Subdivides the rcap chain
(not `z`) and uses `relMvDelta` class-invariance, dodging the algebraic-split gap. -/
theorem rhs_dance {N p : ℕ} {U' V' K S' : Set ↑X} (hU' : IsOpen U') (hV' : IsOpen V')
    (hSeq : U' ∪ V' = S')
    (z : SingularChain X (N + 2 + p + 1)) (hzK : z ∈ subspaceChains K (N + 2 + p + 1))
    (hzS : chainBoundary X (N + 2 + p) z ∈ subspaceChains (U' ∪ V') (N + 2 + p))
    (hzS' : chainBoundary X (N + 2 + p) z ∈ subspaceChains S' (N + 2 + p))
    (a' : LinearMap.ker (coboundaryₗ (sub K) (p + 1)))
    (σ : LinearMap.ker (relCoboundaryₗ (U' ∩ V') (N + 1))) :
    ∃ w : SingularChain X (N + 1), w ∈ subspaceChains V' (N + 1) ∧
      kroneckerH (X := sub K) (p + 1) (Submodule.Quotient.mk a')
          (relativeDualityK S' K (N + 2) p z hzK hzS'
            (relCohomSetCongr hSeq (N + 2)
              (relCohomMvConnecting U' V' hU' hV' N (RelativeCohomology.mk (U' ∩ V') (N + 1) σ))))
        = kronecker σ.1.1 w := by
  rw [kroneckerH_relativeDualityK_setCongr_relCohomMvConnecting_N2 hU' hV' hSeq z hzK hzS hzS' a'
      (RelativeCohomology.mk (U' ∩ V') (N + 1) σ)]
  have hC0cyc := SingularCapSubKDuality.chainIncl_rcap_mem_relCycles z hzK hzS a'
  have hC0bd : chainBoundary X (N + 1)
      (chainIncl K (N + 2) (rcap a'.1 ((subspaceChainsEquiv K (N + 2 + p + 1)).symm ⟨z, hzK⟩)))
      ∈ subspaceChains (U' ∪ V') (N + 1) := by
    rw [← RelativeChain.mk_eq_zero_iff, ← relBoundary_mk]
    exact LinearMap.mem_ker.mp hC0cyc
  obtain ⟨m, u', w', hsplit⟩ := exists_cover_fine_subdivision hU' hV' _ hC0bd
  refine ⟨chainIncl V' (N + 1) w', ⟨w', rfl⟩, ?_⟩
  have hSdcyc : RelativeChain.mk (U' ∪ V') (N + 1 + 1)
      ((⇑(SingularSubdivision.singularSd X (N + 1 + 1)))^[m]
        (chainIncl K (N + 2) (rcap a'.1 ((subspaceChainsEquiv K (N + 2 + p + 1)).symm ⟨z, hzK⟩))))
      ∈ relCycles (U' ∪ V') (N + 1 + 1) := by
    rw [show relCycles (U' ∪ V') (N + 1 + 1) = LinearMap.ker (relBoundary (U' ∪ V') (N + 1)) from rfl,
      LinearMap.mem_ker, relBoundary_mk, RelativeChain.mk_eq_zero_iff, hsplit]
    exact Submodule.add_mem _
      (SingularMayerVietoris.subspaceChains_mono Set.subset_union_left (N + 1) ⟨u', rfl⟩)
      (SingularMayerVietoris.subspaceChains_mono Set.subset_union_right (N + 1) ⟨w', rfl⟩)
  have hcyc : chainIncl U' (N + 1) u' + chainIncl V' (N + 1) w' ∈ cycles X (N + 1) := by
    rw [show cycles X (N + 1) = LinearMap.ker (chainBoundary X N) from rfl, LinearMap.mem_ker,
      ← hsplit, chainBoundary_chainBoundary_apply]
  have hwcyc : RelativeChain.mk (U' ∩ V') (N + 1) (chainIncl V' (N + 1) w')
      ∈ relCycles (U' ∩ V') (N + 1) := by
    rw [show relCycles (U' ∩ V') (N + 1) = LinearMap.ker (relBoundary (U' ∩ V') N) from rfl,
      LinearMap.mem_ker, relBoundary_mk, RelativeChain.mk_eq_zero_iff,
      ← SingularMayerVietoris.subspaceChains_inf]
    have hz0 := LinearMap.mem_ker.mp hcyc
    rw [map_add] at hz0
    have hBeqA : chainBoundary X N (chainIncl V' (N + 1) w')
        = chainBoundary X N (chainIncl U' (N + 1) u') := by
      have h := hz0; rw [add_comm] at h
      exact eq_of_sub_eq_zero (by
        rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_right (ZModModule.add_self _)]; exact h)
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · rw [hBeqA, ← chainIncl_chainBoundary]; exact ⟨_, rfl⟩
    · rw [← chainIncl_chainBoundary]; exact ⟨_, rfl⟩
  rw [relHomology_mk_singularSd_iterate _ hC0bd _ m hSdcyc,
    relKroneckerH_relMvDelta_cover_partition U' V' hU' hV' N σ _ (chainIncl U' (N + 1) u')
      (chainIncl V' (N + 1) w') ⟨u', rfl⟩ ⟨w', rfl⟩ hsplit hwcyc hSdcyc,
    SingularRelativePairing.relKronecker_mk]

end SKEFTHawking.SingularConnSquareRHSDance
