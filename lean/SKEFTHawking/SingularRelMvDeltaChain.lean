import Mathlib
import SKEFTHawking.SingularRelativeMV

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD6f-c4-M1) — the `relMvDelta` chain action via a `relLift`

The relative Mayer–Vietoris connecting map `relMvDelta = relConnecting ∘ iotaEquiv⁻¹` is, on the class
of a small-chains lift `Σ b` of a `relLift` `b = (b_U, b_V)` (a cover-subordinate decomposition), the
class of its `U∩V`-extraction:
  `relMvDelta (ι [Σ b]) = [extractA b]`.
This unwraps the connecting map's snake/Q-machinery (`relConnecting_relLiftToQHom`) into a single
`extractA` (an explicit chain), the concrete form needed to match the connecting square's two legs at the
chain level (the genuine cap-commutes-with-connecting computation, where the `relLift` is the
cover-partition of the capped fundamental cycle).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeMV

namespace SKEFTHawking.SingularRelMvDeltaChain

variable {M : TopCat}

/-- **The `relMvDelta` chain action via a `relLift`**: on the small-chains-lift class `ι [Σ b]` of a
`relLift` `b`, the relative MV connecting map is the class of the `U∩V`-extraction `extractA b`. -/
theorem relMvDelta_iotaEquiv_relLiftToQHom (U V : Set ↑M) (hU : IsOpen U) (hV : IsOpen V) (k : ℕ)
    (b : relLift U V k) :
    relMvDelta U V hU hV k (iotaEquiv U V hU hV k (relLiftToQHom U V k b))
      = RelativeHomology.mk (U ∩ V) k ⟨extractA U V k b, extractA_mem_relCycles U V k b⟩ := by
  rw [relMvDelta, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply,
    relConnecting_relLiftToQHom, relConnectingLift_apply]

end SKEFTHawking.SingularRelMvDeltaChain
