/-
# Phase 5q.H (E1 CSC-PD tower) — degree-cast helpers (integral, Route B utilities)

Three generic `subst`-based degree-cast helpers, public (cross-file reusable) mirrors of the mod-2
`subspaceChains_cast_mem` / `chainBoundary_cast` / `singularChain_cast_eq_rec` (the ℤ versions in
`SingularEuclideanCapIsoInt` are `private`). Consumed by the Route B fact-(i)/fact-(ii) subtree bricks
for the degree-shape casts (`(k+m)+1` vs `k+(m+1)` etc.). (`singularChain_cast_add` is already public as
`SingularCohomologyInt.singularChainInt_cast_add` — reuse that; not re-declared here.)

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularRelHomologyInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt

namespace SKEFTHawking.SingularConnSquareCloseNCInt

variable {X : TopCat}

/-- **Degree-cast transports subspace membership** (integral generic `subst`-helper). -/
theorem subspaceChains_cast_memInt {a b : ℕ} (e : a = b) {S : Set ↑X}
    {c : SingularChainInt X a} (hc : c ∈ subspaceChainsInt S a) :
    (e ▸ c : SingularChainInt X b) ∈ subspaceChainsInt S b := by subst e; exact hc

/-- **Degree-cast commutes with `∂`** (integral generic `subst`-helper; proof-irrelevance collapses the
residual self-cast). -/
theorem chainBoundary_castInt {a b : ℕ} (e : a + 1 = b + 1) (e' : a = b)
    (c : SingularChainInt X (a + 1)) :
    chainBoundary X b (e ▸ c) = e' ▸ chainBoundary X a c := by subst e'; rfl

/-- **`cast` along a `congrArg`-lifted degree equality is the `▸`-recast** (integral generic bridge). -/
theorem singularChain_cast_eq_recInt {a b : ℕ} (e : a = b) (c : SingularChainInt X a) :
    cast (congrArg (SingularChainInt X) e) c = e ▸ c := by subst e; rfl

end SKEFTHawking.SingularConnSquareCloseNCInt
