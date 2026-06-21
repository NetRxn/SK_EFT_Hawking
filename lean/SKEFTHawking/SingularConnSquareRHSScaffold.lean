import Mathlib
import SKEFTHawking.SingularConnSquareRHSN2
import SKEFTHawking.SingularConnSquareCloseFinal
import SKEFTHawking.SingularRelCohomMvConnectingGeom
import SKEFTHawking.SingularOpenDualityCycle
import SKEFTHawking.SingularCapSubKDuality
import SKEFTHawking.SingularSubdivision

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4) — RHS-reduction scaffold for the connecting-square match

Three kernel-pure bricks that compose into the full reduction of the connecting-square match's RHS
(`kroneckerH ωrep (relativeDualityK ... (relCohomMvConnecting g↾))`) to the unifying cup form
`⟨(pullbackCochain g↾) ∪ ωrep, ·⟩`:

1. `relativeDualityK_singularSd_iterate` — subdivision-invariance of `relativeDualityK`, so the fundamental
   cycle `z` can be swapped for a **cover-fine** `Sdʲz` (the cover-partition hypothesis of brick 2 then
   becomes satisfiable).
2. `rhs_relativeDualityK_to_input` — `relativeDualityK → relMvDelta → ⟨δφ, c⟩ → ⟨σ, w⟩`, the
   connecting-INPUT pairing (`w` = V-part of `∂c`), composing M4 + `relKroneckerH_relMvDelta_pairing` +
   `kronecker_coboundary_cochainSplit_eq`.
3. `kronecker_chainIncl_rcap_eq_cup` — the cup bridge `⟨σ, chainIncl K (a' ⌢ʳ c)⟩ = ⟨(pullbackCochain σ) ∪ a', c⟩`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2

namespace SKEFTHawking.SingularConnSquareRHSScaffold

open SKEFTHawking.SingularConnSquareRHSN2 SKEFTHawking.SingularConnSquareCloseFinal
  SKEFTHawking.SingularRelCohomMvConnectingGeom SKEFTHawking.SingularLocalDualityK
  SKEFTHawking.SingularRelativeCohomologyMVConnecting SKEFTHawking.SingularCompactlySupportedTop
  SKEFTHawking.SingularCapChainIncl SKEFTHawking.SingularSubspaceChainsEquiv

variable {X : TopCat}

/-- **Subdivision-invariance of `relativeDualityK`**: the per-`K` Poincaré-duality value is unchanged by
barycentric subdivision of the fundamental cycle `z` (`z` and `Sdʲz` are rel-homologous in `(M, S)` by
`relative_add_singularSd_iterate_mem_relBoundaries`, so `relativeDualityK_cycle_compat_relB` applies).
This lets the connecting-square RHS swap `z_J` for a **cover-fine** `Sdʲz_J` so the cover-partition
hypothesis of `rhs_relativeDualityK_to_input` becomes satisfiable. -/
theorem relativeDualityK_singularSd_iterate {k m : ℕ} {S W : Set ↑X}
    (z : SingularChain X (k + m + 1)) (hzK : z ∈ subspaceChains W (k + m + 1))
    (hzS : chainBoundary X (k + m) z ∈ subspaceChains S (k + m))
    (hcov : (⋃ U ∈ ({W, S} : Set (Set ↑X)), interior U) = Set.univ)
    (j : ℕ) (x : RelativeCohomology S k) :
    relativeDualityK S W k m z hzK hzS x
      = relativeDualityK S W k m ((⇑(SingularSubdivision.singularSd X (k + m + 1)))^[j] z)
          (SingularExcision.singularSd_iterate_mem_subspaceChains hzK j)
          (by rw [SingularSubdivision.singularSd_iterate_chainBoundary]
              exact SingularExcision.singularSd_iterate_mem_subspaceChains hzS j) x :=
  SingularOpenDualityCycle.relativeDualityK_cycle_compat_relB z _ hzK _ hzS _ hcov
    (SingularExcision.relative_add_singularSd_iterate_mem_relBoundaries hzS j) x

/-- **RHS reduction of the connecting-square match to the connecting-INPUT pairing.** Composes the
committed M4 engine (`kroneckerH_relativeDualityK_setCongr_relCohomMvConnecting_N2`,
relativeDualityK → relMvDelta), `relKroneckerH_relMvDelta_pairing` (relMvDelta → `⟨δφ, c⟩`), and
`kronecker_coboundary_cochainSplit_eq` (`⟨δφ, c⟩ = ⟨σ, w⟩`, `w` = V-part of `∂c`). Takes the
cover-partition `∂(chainIncl K (rcap a' z)) = u + w` as a hypothesis (abstract `U'`/`V'`/`K` ⟹ no whnf
wall). `σ` is the cohomology-connecting INPUT cocycle. -/
theorem rhs_relativeDualityK_to_input {N p : ℕ} {U' V' K S' : Set ↑X}
    (hU' : IsOpen U') (hV' : IsOpen V') (hSeq : U' ∪ V' = S')
    (z : SingularChain X (N + 2 + p + 1)) (hzK : z ∈ subspaceChains K (N + 2 + p + 1))
    (hzS : chainBoundary X (N + 2 + p) z ∈ subspaceChains (U' ∪ V') (N + 2 + p))
    (hzS' : chainBoundary X (N + 2 + p) z ∈ subspaceChains S' (N + 2 + p))
    (a' : LinearMap.ker (coboundaryₗ (sub K) (p + 1)))
    (σ : LinearMap.ker (relCoboundaryₗ (U' ∩ V') (N + 1)))
    (u w : SingularChain X (N + 1))
    (hu : u ∈ subspaceChains U' (N + 1)) (hw : w ∈ subspaceChains V' (N + 1))
    (hbd : chainBoundary X (N + 1)
        (chainIncl K (N + 2) (rcap a'.1 ((subspaceChainsEquiv K (N + 2 + p + 1)).symm ⟨z, hzK⟩)))
      = u + w)
    (hwcyc : RelativeChain.mk (U' ∩ V') (N + 1) w ∈ relCycles (U' ∩ V') (N + 1)) :
    kroneckerH (X := sub K) (p + 1) (Submodule.Quotient.mk a')
        (relativeDualityK S' K (N + 2) p z hzK hzS'
          (relCohomSetCongr hSeq (N + 2)
            (relCohomMvConnecting U' V' hU' hV' N (RelativeCohomology.mk (U' ∩ V') (N + 1) σ))))
      = kronecker σ.1.1 w := by
  rw [kroneckerH_relativeDualityK_setCongr_relCohomMvConnecting_N2 hU' hV' hSeq z hzK hzS hzS' a'
      (RelativeCohomology.mk (U' ∩ V') (N + 1) σ),
    relKroneckerH_relMvDelta_pairing hU' hV' σ a' z hzK
      (SingularCapSubKDuality.chainIncl_rcap_mem_relCycles z hzK hzS a') u w hu hw hbd hwcyc,
    kronecker_coboundary_cochainSplit_eq U' V' N σ _ u w hu hw hbd]

/-- **Cup bridge**: a chain pairing `⟨σ, chainIncl K (a' ⌢ʳ c)⟩` of a cochain `σ` against the inclusion of
a right-cap equals the cup pairing `⟨(pullbackCochain K σ) ∪ a', c⟩` against the underlying `sub K`-chain.
The unifying form both legs of the connecting-square match target (`⟨g ∪ ω, ·⟩`). Two committed adjunctions:
`kronecker_pullbackCochain` (lift to ambient) + `kronecker_cup_rcap` (extract the left cup factor). -/
theorem kronecker_chainIncl_rcap_eq_cup {k l : ℕ} {K : Set ↑X} (σ : SingularCochain X k)
    (a' : SingularCochain (sub K) l) (c : SingularChain (sub K) (k + l)) :
    kronecker σ (chainIncl K k (rcap a' c))
      = kronecker (cup (pullbackCochain K k σ) a') c := by
  rw [← SingularCapSubKDuality.kronecker_pullbackCochain, ← kronecker_cup_rcap]

end SKEFTHawking.SingularConnSquareRHSScaffold
