/-
# Phase 5q.H (E1 CSC-PD tower) — the cap ↔ indicator-split bridge (integral, brick 6e ingredient)

The first bridge between the `capInt` cap-product machinery and the `indUf` cochain-indicator-split
machinery (previously disjoint in-tree). The U-indicator restriction `indUf U g` vanishes on every
U-simplex by construction, so it caps every U-supported chain to `0`:
  `capInt (indUf U g) c = 0`  for  `c ∈ subspaceChainsInt U`.
This is the load-bearing locality fact behind the seam-match: it is why `δ(indUf U g)` detects only the
seam (`coboundary_indUf_mem_mvUnion`), and it feeds the cap-Leibniz extraction of the connecting term.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularEuclideanCapIsoInt
import SKEFTHawking.SingularRelativeCohomologyMVConnectingInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeCohomologyMVConnectingInt (indUf indUf_apply)
open SKEFTHawking.SingularExcisionIsoInt (range_simplexIncl_subsetInt)
open SKEFTHawking.SingularEuclideanCapIsoInt (capInt_subspaceChainInt_eq_zero)

namespace SKEFTHawking.SingularCapIndUfBridgeInt

variable {X : TopCat}

/-- **The U-indicator cochain caps every U-supported chain to zero** (integral). `indUf U g` vanishes on
every U-simplex (`indUf_apply` + `range_simplexIncl_subsetInt`), so `capInt (indUf U g) c = 0` whenever `c`
is a U-subspace chain. The cap ↔ indicator-split locality bridge. -/
theorem capInt_indUf_subspaceU_eq_zeroInt (U : Set ↑X) {k m : ℕ} (g : SingularCochainInt X k)
    {c : SingularChainInt X (k + m)} (hc : c ∈ subspaceChainsInt U (k + m)) :
    capInt (m := m) (indUf U k g) c = 0 := by
  apply capInt_subspaceChainInt_eq_zero U (indUf U k g) _ hc
  intro τ
  rw [indUf_apply, if_pos (range_simplexIncl_subsetInt U τ)]

end SKEFTHawking.SingularCapIndUfBridgeInt
