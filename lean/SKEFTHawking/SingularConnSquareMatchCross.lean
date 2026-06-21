import Mathlib
import SKEFTHawking.SingularConnSquareMatchLHS
import SKEFTHawking.SingularCapSubKDuality

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4) — the cross-realization MATCH extraction

The heavy-term-free pivot core of the connecting-square match (NC `SingularConnSquareCloseNC` l.334).
After the cover-partition descent both legs land as bare chain pairings in *different* spaces/degrees
(LHS on `sub W` deg `p+1`, RHS on `X` deg `k`). This lemma pivots them through the committed cap↔rcap
core `kronecker_cap_eq_kronecker_rcap` + the `pullbackCochain`↔`chainIncl` adjunction
`kronecker_pullbackCochain`, reducing the match to the two genuine cross-realization obligations:
`hLHS` (sub-lemma A: the LHS connecting-cap naturality — the seam-transported `mvConnecting` V-part is
the cap `(pullbackCochain W gamb) ⌢ c` for the shared `c`) and `hRHS` (sub-lemma B: the rcap-vs-`LVᶜ`
subdivision realization). No heavy `set` term (`c`/`z₀''`/`J`/`Sdᵐ`) appears in this statement ⟹ no
whnf wall on the pivot `rw` — the whole point of the extraction.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularCapChainIncl
  SKEFTHawking.SingularCapSubKDuality SKEFTHawking.SingularConnSquareMatchLHS

namespace SKEFTHawking.SingularConnSquareMatchCross

variable {X : TopCat}

/-- **The cross-realization match, pivoted** (heavy-term-free). Given the LHS *pairing* equal to the
full-cap pairing `⟨a', cap (pullbackCochain W gamb) c⟩` (sub-lemma A, `hLHS` — a *pairing* equality,
not a chain equality, since the connecting-map V-part boundary equals the full cap only mod-boundary,
which the cocycle `a'` absorbs) and the RHS rcap-vs-`LVᶜ` agreement (sub-lemma B, `hRHS`), the two
match legs agree by the cap↔rcap pivot (`kronecker_cap_eq_kronecker_rcap`) + the
`pullbackCochain`↔`chainIncl` adjunction (`kronecker_pullbackCochain`). The pivot is a 4-rewrite chain
over committed lemmas; all heavy geometry is deferred into the two hypotheses (discharged at the NC
call site, over a shared `c` = `z₀`-realized in `sub W`). -/
theorem cross_realization_match {k p : ℕ} {W LVc : Set ↑X}
    (a' : SingularCochain (sub W) (p + 1))
    (gamb : SingularCochain X k)
    (lhsChain : SingularChain (sub W) (p + 1))
    (c : SingularChain (sub W) (k + (p + 1)))
    (w' : SingularChain (sub LVc) k)
    (hLHS : kronecker a' lhsChain = kronecker a' (cap (pullbackCochain W k gamb) c))
    (hRHS : kronecker gamb (chainIncl W k (rcap a' c)) = kronecker gamb (chainIncl LVc k w')) :
    kronecker a' lhsChain = kronecker gamb (chainIncl LVc k w') := by
  rw [hLHS, kronecker_cap_eq_kronecker_rcap, kronecker_pullbackCochain, hRHS]

end SKEFTHawking.SingularConnSquareMatchCross
