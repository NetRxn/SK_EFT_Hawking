import Mathlib
import SKEFTHawking.SingularTwoCoverBridge
import SKEFTHawking.SingularRcapRelHomology
import SKEFTHawking.SingularRcapCoverAgree
import SKEFTHawking.SingularConnSquareRHSScaffold
import SKEFTHawking.SingularRelMvDeltaPartition

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4) — closing `hcross` (the PD connecting square's deepest residual)

`hcross` (the hypothesis of `SingularTwoCoverBridge.subHomConnecting_openDuality_of_crossRealization`)
is the homology-class identity in `H(M, (↑K)ᶜ)(N+1)`:

  `[chainIncl (U∪V) (rcap b z_K)]  =  hSet ▸ relMvDelta (legSplitUᶜ) (legSplitVᶜ) (N+1)
      [chainIncl (U∩V) (rcap a' z_J)]`

with `[b] = absCohomConn [a']`, `z_K = fundCycleW (U∪V) (castChain z₀) K`,
`z_J = fundCycleW (U∩V) (castChain z₀) infCompact`, `hSet : (↑K)ᶜ = legSplitUᶜ ∩ legSplitVᶜ`.

This file ships two kernel-pure bricks that reduce the RHS of `hcross` to its V-part form:

* `relMvDelta_eq_legVpart` — the **class-form RHS dance**, the class-level mirror of the committed
  pairing-form `SingularConnSquareRHSDance.rhs_dance`. It reduces
  `relMvDelta A B [c]` (for any `(A∪B)`-relative cycle `c`) to `[chainIncl B w']` (the `B = legSplitVᶜ`
  V-part of a cover-fine subdivision `Sdᵐc = chainIncl A u' + chainIncl B w'`) via
  `exists_cover_fine_subdivision` (M4), `relHomology_mk_singularSd_iterate` (subdivision-invariance of
  the class), and `relMvDelta_cover_partition` (M9b: the connecting = the V-part class).
* `rhs_relMvDelta_rcap_eq_legVpart` — the directly-usable specialization to a **right-cap** chain
  `c = chainIncl Kc (a' ⌢ʳ z_sub)`, discharging the dance's boundary-support hypothesis from the
  right-cap rel-cycle membership the bridge already carries (`chainIncl_rcap_mem_relCycles`). This is
  the form that fires on the bridge's RHS connecting leg directly.

These shrink `hcross` to its **irreducible reconciliation core**: matching the LHS
`[chainIncl (U∪V) (rcap b z_K)]` to the RHS V-part `[chainIncl legSplitVᶜ w']`. That core is the
**cap-naturality of the MV connecting on the shared `z₀`** under `[b] = absCohomConn [a']`. The genuine
obstruction (see the module-end note) is that `absCohomConn` is **Kronecker-defined** (the
`dualMap`-conjugate through the perfect pairing; `SingularSubHomologyMVCohomConn.absCohomConn`), so
`[b] = absCohomConn [a']` yields no chain-level handle on `b` — only the pairing adjunction. Closing the
core non-circularly needs a **class-form representative** of `absCohomConn` (the absolute mirror of
`SingularRelCohomMvConnectingGeom.relCohomMvConnecting_eq_mk_coboundary_cochainSplit`, giving
`b = δ(cochainSplit …)` as an explicit cocycle), which is not yet committed — building it crosses the
documented doubly-nested `restr (val⁻¹U) (val⁻¹V)` whnf wall and is the next brick.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2

namespace SKEFTHawking.SingularHcrossClose

open SKEFTHawking.SingularCapChainIncl SKEFTHawking.SingularSubspaceChainsEquiv
  SKEFTHawking.SingularCapSubKDuality SKEFTHawking.SingularConnSquareRHSScaffold
  SKEFTHawking.SingularRelMvDeltaPartition SKEFTHawking.SingularRcapRelHomology
  SKEFTHawking.SingularRelativeMV

variable {X : TopCat}

/-- **The class-form RHS dance** — class-level mirror of `SingularConnSquareRHSDance.rhs_dance`. For an
ambient relative cycle `c` over `A ∪ B` (`A`, `B` open) of degree `N+1+1` whose boundary lands in
`C(A∪B)`, the relative MV connecting class `relMvDelta A B [c]` equals the class of the `B`-part `w'` of a
cover-fine barycentric subdivision `Sdᵐc = chainIncl A u' + chainIncl B w'`. Subdivides `c` itself
(`exists_cover_fine_subdivision`), swaps `[c] = [Sdᵐc]` (`relHomology_mk_singularSd_iterate`), then
reads off the `V`-part via `relMvDelta_cover_partition` (M9b). -/
theorem relMvDelta_eq_legVpart {N : ℕ} {A B : Set ↑X} (hA : IsOpen A) (hB : IsOpen B)
    (c : SingularChain X (N + 1 + 1))
    (hcbd : chainBoundary X (N + 1) c ∈ subspaceChains (A ∪ B) (N + 1))
    (hccyc : RelativeChain.mk (A ∪ B) (N + 1 + 1) c ∈ relCycles (A ∪ B) (N + 1 + 1)) :
    ∃ (w' : SingularChain (sub B) (N + 1))
      (hwcyc : RelativeChain.mk (A ∩ B) (N + 1) (chainIncl B (N + 1) w') ∈ relCycles (A ∩ B) (N + 1)),
      relMvDelta A B hA hB (N + 1)
          (RelativeHomology.mk (A ∪ B) (N + 1 + 1)
            ⟨RelativeChain.mk (A ∪ B) (N + 1 + 1) c, hccyc⟩)
        = RelativeHomology.mk (A ∩ B) (N + 1)
            ⟨RelativeChain.mk (A ∩ B) (N + 1) (chainIncl B (N + 1) w'), hwcyc⟩ := by
  -- Cover-fine subdivision of `c` over `{A, B}`: `Sdᵐc = chainIncl A u' + chainIncl B w'`.
  obtain ⟨m, u', w', hsplit⟩ := exists_cover_fine_subdivision hA hB c hcbd
  -- The `B`-part is a `(A∩B)`-relative cycle (its boundary equals the `A`-part boundary, in `C(A)∩C(B)`).
  have hcyc : chainIncl A (N + 1) u' + chainIncl B (N + 1) w' ∈ cycles X (N + 1) := by
    rw [show cycles X (N + 1) = LinearMap.ker (chainBoundary X N) from rfl, LinearMap.mem_ker, ← hsplit,
      chainBoundary_chainBoundary_apply]
  have hwcyc : RelativeChain.mk (A ∩ B) (N + 1) (chainIncl B (N + 1) w')
      ∈ relCycles (A ∩ B) (N + 1) := by
    rw [show relCycles (A ∩ B) (N + 1) = LinearMap.ker (relBoundary (A ∩ B) N) from rfl,
      LinearMap.mem_ker, relBoundary_mk, RelativeChain.mk_eq_zero_iff,
      ← SingularMayerVietoris.subspaceChains_inf]
    have hz0 := LinearMap.mem_ker.mp hcyc
    rw [map_add] at hz0
    have hBeqA : chainBoundary X N (chainIncl B (N + 1) w')
        = chainBoundary X N (chainIncl A (N + 1) u') := by
      have h := hz0; rw [add_comm] at h
      exact eq_of_sub_eq_zero (by
        rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_right (ZModModule.add_self _)]; exact h)
    refine Submodule.mem_inf.2 ⟨?_, ?_⟩
    · rw [hBeqA, ← chainIncl_chainBoundary]; exact ⟨_, rfl⟩
    · rw [← chainIncl_chainBoundary]; exact ⟨_, rfl⟩
  refine ⟨w', hwcyc, ?_⟩
  -- The subdivided chain is a `(A∪B)`-relative cycle.
  have hSdcyc : RelativeChain.mk (A ∪ B) (N + 1 + 1)
      ((⇑(SingularSubdivision.singularSd X (N + 1 + 1)))^[m] c) ∈ relCycles (A ∪ B) (N + 1 + 1) := by
    rw [show relCycles (A ∪ B) (N + 1 + 1) = LinearMap.ker (relBoundary (A ∪ B) (N + 1)) from rfl,
      LinearMap.mem_ker, relBoundary_mk, RelativeChain.mk_eq_zero_iff, hsplit]
    exact Submodule.add_mem _
      (SingularMayerVietoris.subspaceChains_mono Set.subset_union_left (N + 1) ⟨u', rfl⟩)
      (SingularMayerVietoris.subspaceChains_mono Set.subset_union_right (N + 1) ⟨w', rfl⟩)
  -- Swap `[c] = [Sdᵐc]`, then read off the `V`-part via `relMvDelta_cover_partition`.
  rw [relHomology_mk_singularSd_iterate c hcbd hccyc m hSdcyc]
  exact relMvDelta_cover_partition A B hA hB (N + 1)
    ((⇑(SingularSubdivision.singularSd X (N + 1 + 1)))^[m] c)
    (chainIncl A (N + 1) u') (chainIncl B (N + 1) w') ⟨u', rfl⟩ ⟨w', rfl⟩ hsplit hwcyc hSdcyc

/-- **RHS reduction of the bridge's connecting leg** — the directly-usable specialization of the
class-form dance to a right-cap chain. For a `Kc`-supported chain `z` (the cap-realization subspace
`Kc`, here `U∩V`) whose right cap with `a'` has its `(A∪B)`-relative cycle representative (i.e.
`∂(chainIncl Kc (a' ⌢ʳ z_sub)) ∈ C(A∪B)`), the relative MV connecting class
`relMvDelta A B [chainIncl Kc (a' ⌢ʳ z_sub)]` is the class of the `B = legSplitVᶜ` V-part `w'` of a
cover-fine subdivision. This is `relMvDelta_eq_legVpart` with the boundary-support hypothesis discharged
from the right-cap rel-cycle membership — so a caller only supplies the rel-cycle witness the bridge
already carries (`chainIncl_rcap_mem_relCycles`). -/
theorem rhs_relMvDelta_rcap_eq_legVpart {N p : ℕ} {A B Kc : Set ↑X} (hA : IsOpen A) (hB : IsOpen B)
    (z : SingularChain X (N + 1 + 1 + p + 1)) (hzKc : z ∈ subspaceChains Kc (N + 1 + 1 + p + 1))
    (a' : LinearMap.ker (coboundaryₗ (sub Kc) (p + 1)))
    (hccyc : RelativeChain.mk (A ∪ B) (N + 1 + 1)
        (chainIncl Kc (N + 1 + 1) (rcap a'.1
          ((subspaceChainsEquiv Kc (N + 1 + 1 + p + 1)).symm ⟨z, hzKc⟩)))
      ∈ relCycles (A ∪ B) (N + 1 + 1)) :
    ∃ (w' : SingularChain (sub B) (N + 1))
      (hwcyc : RelativeChain.mk (A ∩ B) (N + 1) (chainIncl B (N + 1) w') ∈ relCycles (A ∩ B) (N + 1)),
      relMvDelta A B hA hB (N + 1)
          (RelativeHomology.mk (A ∪ B) (N + 1 + 1)
            ⟨RelativeChain.mk (A ∪ B) (N + 1 + 1)
              (chainIncl Kc (N + 1 + 1) (rcap a'.1
                ((subspaceChainsEquiv Kc (N + 1 + 1 + p + 1)).symm ⟨z, hzKc⟩))), hccyc⟩)
        = RelativeHomology.mk (A ∩ B) (N + 1)
            ⟨RelativeChain.mk (A ∩ B) (N + 1) (chainIncl B (N + 1) w'), hwcyc⟩ := by
  -- Extract the `(A∪B)`-boundary support of the right-cap chain from its rel-cycle membership.
  have hcbd : chainBoundary X (N + 1)
      (chainIncl Kc (N + 1 + 1) (rcap a'.1
        ((subspaceChainsEquiv Kc (N + 1 + 1 + p + 1)).symm ⟨z, hzKc⟩)))
      ∈ subspaceChains (A ∪ B) (N + 1) := by
    have h := hccyc
    rw [show relCycles (A ∪ B) (N + 1 + 1) = LinearMap.ker (relBoundary (A ∪ B) (N + 1)) from rfl,
      LinearMap.mem_ker, relBoundary_mk, RelativeChain.mk_eq_zero_iff] at h
    exact h
  exact relMvDelta_eq_legVpart hA hB _ hcbd hccyc

end SKEFTHawking.SingularHcrossClose
