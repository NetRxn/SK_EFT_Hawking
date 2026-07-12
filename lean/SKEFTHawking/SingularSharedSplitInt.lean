/-
# Phase 5q.H (E1 CSC-PD tower) — support-preserving repartition + the SHARED F₂-split (integral)

The two bricks that close the seam-match `(★)` support gap (the 2026-07-12 design correction — the
"A∩B-collapse" is support algebra, not manifold topology):

* `repartition_subspaceChainsInt` — ℤ port of the mod-2
  `SingularConnSquareCloseNC.repartition_subspaceChains` (per-simplex support re-partition): a cover
  split `chainIncl A cA + chainIncl B cB` whose SUM is `S`-supported re-partitions into legs over
  `A ∩ S` / `B ∩ S`. Direct over ℤ (no smallChains detour): each support simplex of the sum survives
  the signed sum, hence has range in `A` or `B` (via a leg) AND in `S` (via the sum), so its
  `Finsupp.single` lands in `C(A∩S)` or `C(B∩S)`; sum over the support.
* `exists_shared_boundary_split_int` — the SHARED split producer (the fix): for a `W`-supported chain
  `F` with `∂F ∈ C(U'∪V')`, some iterated subdivision has
  `∂(Sdʲ F) = chainIncl (U'∩W) aF + chainIncl (V'∩W) bF`. Applied at `F := z_J = fundCycleW (A∩B)`,
  `W := A∩B`, `{U', V'} = {legSplitUᶜ, legSplitVᶜ}`, this is the ONE `(jF, aF, bF)` datum that feeds
  BOTH `fact_i_ambient_coreInt`'s `hFsplit` slot AND the zc-side cap computation — sharing it is what
  keeps every residual `C(A∩B)`-supported (the independent-split route left a `C(Jᶜ)` residue).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularCoverFineSplitInt
import SKEFTHawking.SingularExcisionIsoInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularSubdivisionInt
open SKEFTHawking.SingularExcisionIsoInt
  (range_of_mem_subspaceChainsInt mem_subspaceChainsInt_of_support
    singularSdInt_iterate_mem_subspaceChainsInt)
open SKEFTHawking.SingularCoverFineSplitInt (exists_cover_fine_split_of_boundaryInt)

namespace SKEFTHawking.SingularSharedSplitInt

variable {X : TopCat}

/-- **Support-preserving cover re-partition** (integral). ℤ port of the mod-2
`repartition_subspaceChains`: the `Submodule.mem_sup` legs of a cover split need not inherit the
parent's `S`-support (cross-leg cancellation), but a per-simplex re-partition does — each support
simplex of the SUM has range in `A` or `B` (it survives the signed sum, so it lies in a leg's
support) and in `S` (the sum is `S`-supported), so assigning it to `A ∩ S` resp. `B ∩ S` re-partitions
the sum with support-preserving legs. Coefficient-agnostic (the mod-2 proof's only char-2 artifact was
routing through `smallChains`; over ℤ the per-simplex `Finsupp.single` decomposition lands directly). -/
theorem repartition_subspaceChainsInt {A B S : Set ↑X} {n : ℕ}
    (cA : SingularChainInt (sub A) n) (cB : SingularChainInt (sub B) n)
    (hS : chainIncl A n cA + chainIncl B n cB ∈ subspaceChainsInt S n) :
    ∃ (a : SingularChainInt (sub (A ∩ S)) n) (b : SingularChainInt (sub (B ∩ S)) n),
      chainIncl A n cA + chainIncl B n cB
        = chainIncl (A ∩ S) n a + chainIncl (B ∩ S) n b := by
  classical
  set c := chainIncl A n cA + chainIncl B n cB with hc
  have hsup : c ∈ subspaceChainsInt (A ∩ S) n ⊔ subspaceChainsInt (B ∩ S) n := by
    rw [← Finsupp.sum_single c, Finsupp.sum]
    refine Submodule.sum_mem _ (fun τ hτ => ?_)
    have hτAB : τ ∈ (chainIncl A n cA).support ∪ (chainIncl B n cB).support :=
      Finsupp.support_add (by rw [← hc]; exact hτ)
    have hτS : Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) ⊆ S :=
      range_of_mem_subspaceChainsInt hS hτ
    have hsingle : ∀ {T : Set ↑X},
        Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) τ) ⊆ T →
        Finsupp.single τ (c τ) ∈ subspaceChainsInt T n := fun hT =>
      mem_subspaceChainsInt_of_support (fun σ hσ => by
        rcases Finset.mem_singleton.1 (Finsupp.support_single_subset hσ) with rfl
        exact hT)
    rcases Finset.mem_union.1 hτAB with hA' | hB'
    · exact Submodule.mem_sup_left (hsingle (Set.subset_inter
        (range_of_mem_subspaceChainsInt (LinearMap.mem_range_self _ cA) hA') hτS))
    · exact Submodule.mem_sup_right (hsingle (Set.subset_inter
        (range_of_mem_subspaceChainsInt (LinearMap.mem_range_self _ cB) hB') hτS))
  obtain ⟨u, hu, v, hv, huv⟩ := Submodule.mem_sup.1 hsup
  obtain ⟨a, ha⟩ := hu
  obtain ⟨b, hb⟩ := hv
  exact ⟨a, b, by rw [← huv, ← ha, ← hb]⟩

/-- **The SHARED boundary split** (the `(jF, aF, bF)` producer). For `F ∈ C(W)` with
`∂F ∈ C(U'∪V')`: some iterated subdivision has
`∂(Sdʲ F) = chainIncl (U'∩W) aF + chainIncl (V'∩W) bF` — a cover split whose legs are ALSO
`W`-supported. Cover-fine split of `∂F` (`exists_cover_fine_split_of_boundaryInt`) + the sum's
`W`-support (`∂F ∈ C(W)`, `Sd` preserves support) + `repartition_subspaceChainsInt`. At
`F := fundCycleW (A∩B)` this is the ONE split shared by `fact_i_ambient_coreInt` and the zc-side. -/
theorem exists_shared_boundary_split_int {U' V' W : Set ↑X}
    (hU' : IsOpen U') (hV' : IsOpen V') {n : ℕ}
    (F : SingularChainInt X (n + 1))
    (hFmem : F ∈ subspaceChainsInt W (n + 1))
    (hFbd : chainBoundary X n F ∈ subspaceChainsInt (U' ∪ V') n) :
    ∃ (j : ℕ) (aF : SingularChainInt (sub (U' ∩ W)) n)
      (bF : SingularChainInt (sub (V' ∩ W)) n),
      chainBoundary X n ((⇑(singularSdInt X (n + 1)))^[j] F)
        = chainIncl (U' ∩ W) n aF + chainIncl (V' ∩ W) n bF := by
  obtain ⟨j, pU, pV, hsplit⟩ :=
    exists_cover_fine_split_of_boundaryInt hU' hV' (chainBoundary X n F) hFbd
  have hSdW : (⇑(singularSdInt X n))^[j] (chainBoundary X n F) ∈ subspaceChainsInt W n :=
    singularSdInt_iterate_mem_subspaceChainsInt
      (chainBoundary_mem_subspaceChainsInt W n F hFmem) j
  rw [hsplit] at hSdW
  obtain ⟨aF, bF, hab⟩ := repartition_subspaceChainsInt pU pV hSdW
  refine ⟨j, aF, bF, ?_⟩
  rw [singularSdInt_iterate_chainBoundary, hsplit, hab]

end SKEFTHawking.SingularSharedSplitInt
