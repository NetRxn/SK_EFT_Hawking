import Mathlib
import SKEFTHawking.SingularOpenDualityMVConnSquare
import SKEFTHawking.SingularCapSubKDuality

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD6f-c) — the connecting-square headline (SCRATCH, hcore sorry)

Assembling `subHomConnecting_openDuality` from the per-`K` cycle core via
`subHomConnecting_openDuality_of_core`. The `hcore` obligation is left `sorry` here so the concrete goal
can be inspected (the cap-commutes-with-connecting computation, route (b)).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCompactlySupportedOpen
  SKEFTHawking.SingularOpenDuality SKEFTHawking.SingularSubsetHomology
  SKEFTHawking.SingularOpenDualityMVConnSquare SKEFTHawking.SingularSubHomologyMV
  SKEFTHawking.SingularCSCMayerVietorisConnecting

namespace SKEFTHawking.SingularOpenDualityMVConnSquareCore

variable {X : TopCat} [T2Space ↑X]

theorem subHomConnecting_openDuality {N p : ℕ} {U V : Set ↑X} (hU : IsOpen U) (hV : IsOpen V)
    (z₀ : SingularChain X (N + p + 3)) (hz₀ : chainBoundary X (N + p + 2) z₀ = 0)
    (γ : CompactlySupportedCohomologyOpen (U ∪ V) (N + 1)) :
    SKEFTHawking.SingularSubHomologyMV.subHomConnecting U V hU hV (p + 1)
        (openDuality (k := N + 1) (m := p + 1) (hU.union hV)
          (castChain (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
          (chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀) γ)
      = openDuality (k := N + 2) (m := p) (hU.inter hV)
          (castChain (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
          (chainBoundary_castChain_eq_zero (by omega) (by omega) z₀ hz₀)
          (SKEFTHawking.SingularCSCMayerVietorisConnecting.cscMvConnecting U V hU hV N γ) := by
  apply subHomConnecting_openDuality_of_core hU hV z₀ hz₀
  intro K g
  sorry

end SKEFTHawking.SingularOpenDualityMVConnSquareCore
