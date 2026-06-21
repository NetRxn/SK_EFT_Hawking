import Mathlib
import SKEFTHawking.SingularHomologyMod2
import SKEFTHawking.SingularOpenDualityMVConnSquare
import SKEFTHawking.SingularCapChainIncl

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4) — cap/rcap commute with `castChain`

`cap_castChain` / `rcap_castChain`: the cap (and right-cap) of a degree-recast chain `castChain e z`
is the recast of the cap — `a ⌢ (castChain e z) = castChain e' (a ⌢ z)`. Since `castChain e = e ▸ ·`
is a pure degree-transport, this is `Nat.add_left_cancel` + transport.

The connecting-square cross-realization needs exactly this: the legW fundamental `z_K = castChain z₀`
and the openDuality fundamental `z_J = castChain z₀` are BOTH `z₀` up to a degree-cast, so `cap g z_K`
and `rcap ωrep z_J` both reduce to `cap`/`rcap` over the SINGLE shared `z₀` — after which the committed
V-part cup-cap match (`kronecker_cap_chainIncl_eq_rcap_chainIncl`) over one cover-split of `z₀` closes
the two legs. This unifies the two different-`W` fundamentals (the obstruction that blocked the cap route).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularOpenDualityMVConnSquare SKEFTHawking.SingularCapChainIncl

namespace SKEFTHawking.SingularCapCastChain

variable {X : TopCat}

/-- **Cap commutes with `castChain`**: `a ⌢ (castChain e z) = castChain (cancel e) (a ⌢ z)`. -/
theorem cap_castChain {k m m' : ℕ} (a : SingularCochain X k) (e : k + m = k + m')
    (z : SingularChain X (k + m)) :
    cap (m := m') a (castChain e z) = castChain (Nat.add_left_cancel e) (cap (m := m) a z) := by
  obtain rfl : m = m' := Nat.add_left_cancel e
  rw [castChain_eq, castChain_eq]

/-- **Right-cap commutes with `castChain`**: `b ⌢ʳ (castChain e z) = castChain (cancel e) (b ⌢ʳ z)`. -/
theorem rcap_castChain {l : ℕ} (b : SingularCochain X l) {m m' : ℕ} (e : m + l = m' + l)
    (z : SingularChain X (m + l)) :
    rcap b (castChain e z) = castChain (Nat.add_right_cancel e) (rcap b z) := by
  obtain rfl : m = m' := Nat.add_right_cancel e
  rw [castChain_eq, castChain_eq]

end SKEFTHawking.SingularCapCastChain
