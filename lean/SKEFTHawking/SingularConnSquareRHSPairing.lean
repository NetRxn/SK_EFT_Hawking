import Mathlib
import SKEFTHawking.SingularConnSquareRHSScaffold
import SKEFTHawking.SingularRelCohomMvConnectingGeom
import SKEFTHawking.SingularExcisionIso
import SKEFTHawking.SingularCohomologySnake

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4) — RHS pairing reduction (gap-free, pairing form)

The RHS leg of the Poincaré-duality connecting-square match, reduced to an **explicit cochain pairing**
via the *pairing-form* MV-connecting realization (`relKroneckerH_relCohomMvConnecting_cover_partition`,
which is **unconditional** — it needs only a cover-partition `∂c = u + w`, NOT the union-level membership
`δφ ∈ relCochains (U'∪V')` that the *class*-form rep requires). This is the gap-free route around the
small-simplices / excision obstruction: a relative `(U'∪V')`-cycle `c` is swapped for a cover-fine
subdivision `Sdʲc` (preserving the homology class, `relHomology_mk_singularSd_iterate`), whose boundary
splits cover-subordinately (`exists_cover_fine_subdivision`); the pairing form then reads the connecting
pairing off as `⟨δ(cochainSplit U' ωR), Sdʲc⟩`.

The subdivision `Sdʲ` is **carried** into the output (it cannot be dropped: `kronecker δφ (Sdʲc) = ⟨δφ,c⟩`
fails for a non-cycle `c` — `δφ` is a coboundary, not a cocycle, so the subdivision-homotopy slack
`⟨δφ, T(∂c)⟩` need not vanish). The downstream cap-Leibniz match over the shared `z₀` absorbs it.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularRelativeMV SKEFTHawking.SingularConnSquareRHSScaffold
  SKEFTHawking.SingularRelCohomMvConnectingGeom SKEFTHawking.SingularRelativeCohomologyMVConnecting
  SKEFTHawking.SingularRelativePairing SKEFTHawking.SingularSubdivision SKEFTHawking.SingularExcisionIso
  SKEFTHawking.SingularCohomologySnake

namespace SKEFTHawking.SingularConnSquareRHSPairing

/-- **RHS pairing reduction (gap-free).** The cohomology-MV-connecting pairing of `relCohomMvConnecting (mk ωR)`
against the class of a relative `(U'∪V')`-cycle `c` equals the explicit chain-level Kronecker pairing of the
seam-supported coboundary `δ(cochainSplit U' ωR)` against a cover-fine subdivision `Sdʲc`. Via the pairing form
`relKroneckerH_relCohomMvConnecting_cover_partition` (unconditional in the union-level membership), after a
class-preserving subdivision swap so `∂(Sdʲc)` splits cover-subordinately. The `Sdʲ` is intrinsic (the
coboundary `δφ` is not a cocycle, so it cannot be peeled off a non-cycle `c`). -/
theorem rhs_pairing_reduce {M : TopCat} [T2Space ↑M] {N : ℕ} (U' V' : Set ↑M)
    (hU' : IsOpen U') (hV' : IsOpen V')
    (ωR : LinearMap.ker (relCoboundaryₗ (U' ∩ V') (N + 1)))
    (c : SingularChain M (N + 1 + 1))
    (hccyc : RelativeChain.mk (U' ∪ V') (N + 1 + 1) c ∈ relCycles (U' ∪ V') (N + 1 + 1)) :
    ∃ j : ℕ,
      relKroneckerH (U' ∪ V')
          (relCohomMvConnecting U' V' hU' hV' N (RelativeCohomology.mk (U' ∩ V') (N + 1) ωR))
          (RelativeHomology.mk (U' ∪ V') (N + 1 + 1)
            ⟨RelativeChain.mk (U' ∪ V') (N + 1 + 1) c, hccyc⟩)
        = kronecker (coboundary M (N + 1) (cochainSplit U' (N + 1) ωR.1.1))
            ((⇑(SingularSubdivision.singularSd M (N + 1 + 1)))^[j] c) := by
  have hc : chainBoundary M (N + 1) c ∈ subspaceChains (U' ∪ V') (N + 1) := by
    have h := hccyc
    rw [show relCycles (U' ∪ V') (N + 1 + 1) = LinearMap.ker (relBoundary (U' ∪ V') (N + 1)) from rfl,
      LinearMap.mem_ker, relBoundary_mk, RelativeChain.mk_eq_zero_iff] at h
    exact h
  obtain ⟨j, u', w', hsplit⟩ := exists_cover_fine_subdivision hU' hV' c hc
  refine ⟨j, ?_⟩
  have hu : chainIncl U' (N + 1) u' ∈ subspaceChains U' (N + 1) := ⟨u', rfl⟩
  have hw : chainIncl V' (N + 1) w' ∈ subspaceChains V' (N + 1) := ⟨w', rfl⟩
  have hSdcyc : RelativeChain.mk (U' ∪ V') (N + 1 + 1)
      ((⇑(SingularSubdivision.singularSd M (N + 1 + 1)))^[j] c) ∈ relCycles (U' ∪ V') (N + 1 + 1) := by
    rw [show relCycles (U' ∪ V') (N + 1 + 1) = LinearMap.ker (relBoundary (U' ∪ V') (N + 1)) from rfl,
      LinearMap.mem_ker, relBoundary_mk, RelativeChain.mk_eq_zero_iff, hsplit]
    exact Submodule.add_mem _
      (SKEFTHawking.SingularMayerVietoris.subspaceChains_mono Set.subset_union_left (N + 1) hu)
      (SKEFTHawking.SingularMayerVietoris.subspaceChains_mono Set.subset_union_right (N + 1) hw)
  have hwcyc : RelativeChain.mk (U' ∩ V') (N + 1) (chainIncl V' (N + 1) w')
      ∈ relCycles (U' ∩ V') (N + 1) := by
    rw [show relCycles (U' ∩ V') (N + 1) = LinearMap.ker (relBoundary (U' ∩ V') N) from rfl,
      LinearMap.mem_ker, relBoundary_mk, RelativeChain.mk_eq_zero_iff,
      ← SingularExcision.subspaceChains_inf]
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · have hUcyc : chainBoundary M N (chainIncl U' (N + 1) u')
          + chainBoundary M N (chainIncl V' (N + 1) w') = 0 := by
        rw [← map_add, ← hsplit]; exact chainBoundary_chainBoundary_apply M N _
      have hVU : chainBoundary M N (chainIncl V' (N + 1) w')
          = chainBoundary M N (chainIncl U' (N + 1) u') :=
        eq_of_sub_eq_zero (by rw [ZModModule.sub_eq_add, add_comm]; exact hUcyc)
      rw [hVU, ← chainIncl_chainBoundary]; exact ⟨_, rfl⟩
    · rw [← chainIncl_chainBoundary]; exact ⟨_, rfl⟩
  rw [relHomology_mk_singularSd_iterate c hc hccyc j hSdcyc,
    relKroneckerH_relCohomMvConnecting_cover_partition U' V' hU' hV' N ωR _
      (chainIncl U' (N + 1) u') (chainIncl V' (N + 1) w') hu hw hsplit hwcyc hSdcyc]

end SKEFTHawking.SingularConnSquareRHSPairing
