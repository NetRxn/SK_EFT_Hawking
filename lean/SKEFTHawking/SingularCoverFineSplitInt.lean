/-
# Phase 5q.H (E1 CSC-PD tower) — cover-fine split of a subspace chain (integral, hcore brick 6e-C)

`exists_cover_fine_split_of_boundaryInt` — the THIRD cover-fine subdivision the seam-match needs (beyond
the `Sdʲ z_K` of the cover-partition). A `(U∪V)`-supported chain has an iterated subdivision
`Sdⁱ c = chainIncl U pU + chainIncl V pV` that is per-simplex in `U` or `V`. Applied to `∂z_J` along
`{U'=legSplitUᶜ, V'=legSplitVᶜ}` so that `capInt_indUf_subspaceU_eq_zeroInt` kills the `U'`-part and
Brick 1 (`capInt_indUf_eq_on_subspaceVInt`) handles the `V'`-part. `Sd`-invariance of the cap is applied
separately at the consumer via the committed c-1/c-2 (`capInt_sub_singularSd_mem_boundariesInt`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularRelativeMVInt
import SKEFTHawking.SingularConnSquareLHSSubdivInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularSubdivisionInt (singularSdInt)
open SKEFTHawking.SingularRelativeMVInt (exists_iterate_mvUnionInt)
open SKEFTHawking.SingularConnSquareLHSSubdivInt (exists_chainIncl_partition_of_mem_mvUnionChainsInt)

namespace SKEFTHawking.SingularCoverFineSplitInt

variable {M : TopCat}

/-- **Brick 3** (cover-fine split of a subspace chain): a `(U∪V)`-supported chain has a cover-fine iterated
subdivision `Sdⁱ c = chainIncl U pU + chainIncl V pV`. The third subdivision needed to split `∂z_J` along
`{U'=legSplitUᶜ, V'=legSplitVᶜ}` (so `capInt_indUf_subspaceU_eq_zeroInt` kills the `U'`-part and Brick 1
handles the `V'`-part). `Sd`-invariance of the cap is applied separately via c-1/c-2 at the consumer. -/
theorem exists_cover_fine_split_of_boundaryInt {U V : Set ↑M} (hU : IsOpen U) (hV : IsOpen V) {n : ℕ}
    (c : SingularChainInt M n) (hc : c ∈ subspaceChainsInt (U ∪ V) n) :
    ∃ (i : ℕ) (pU : SingularChainInt (sub U) n) (pV : SingularChainInt (sub V) n),
      (⇑(singularSdInt M n))^[i] c = chainIncl U n pU + chainIncl V n pV := by
  obtain ⟨i, hi⟩ := exists_iterate_mvUnionInt U V hU hV n c hc
  obtain ⟨pU, pV, hsplit⟩ := exists_chainIncl_partition_of_mem_mvUnionChainsInt U V n _ hi
  exact ⟨i, pU, pV, hsplit⟩

end SKEFTHawking.SingularCoverFineSplitInt
