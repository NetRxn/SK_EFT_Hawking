import Mathlib
import SKEFTHawking.SingularConnSquareCloseNC
import SKEFTHawking.SingularCSCMayerVietorisConnExact

/-!
# Phase 5q.G (G1 PD-induction, brick 2a) — the COLIMIT-level connecting square

The colimit lift of the per-`K` connecting square `subHomConnecting_openDuality` (the L2 close):
the `δ` cap-naturality square of the Poincaré-duality 5-lemma ladder,

`subHomConnecting ∘ D_{U∪V} = D_{U∩V} ∘ cscMvConnecting`,

at the level of the compactly-supported-cohomology colimits. With `subHomDiag_openDuality` and
`subHomSum_openDuality` (`SingularOpenDualityMVSquare`) this completes ALL THREE commuting squares
of the ladder at colimit level; the two rows' exactness is already proven
(`subHom_exact_*` / `cscMv*Exact`), so the Mayer–Vietoris step of the duality induction reduces to
`Mathlib.Algebra.FiveLemma`.

Proof: colimit induction (`Module.DirectLimit.induction_on`) — on a `K`-stage class the two
`@[simp]` computation rules (`openDuality_of`, `cscMvConnecting_of`) reduce the square to exactly
the per-`K` theorem.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularOpenDuality
  SKEFTHawking.SingularCSCMayerVietorisConnecting SKEFTHawking.SingularCompactsInOpen
  SKEFTHawking.SingularCompactlySupportedOpen

namespace SKEFTHawking.SingularOpenDualityConnSquareColimit

variable {X : TopCat} [T2Space ↑X]

/-- **The colimit-level `δ` connecting square**: `subHomConnecting (D_{U∪V} α) = D_{U∩V}
(cscMvConnecting α)` for every compactly-supported class `α` — the colimit lift of the per-`K`
L2 close `subHomConnecting_openDuality`. -/
theorem subHomConnecting_openDuality_colimit {N p : ℕ} {U V : Set ↑X}
    (hU : IsOpen U) (hV : IsOpen V)
    (z₀ : SingularChain X (N + p + 3)) (hz₀ : chainBoundary X (N + p + 2) z₀ = 0)
    (α : CompactlySupportedCohomologyOpen (U ∪ V) (N + 1)) :
    SKEFTHawking.SingularSubHomologyMV.subHomConnecting U V hU hV (p + 1)
        (openDuality (k := N + 1) (m := p + 1) (hU.union hV)
          (SingularOpenDualityMVConnSquare.castChain
            (show N + p + 3 = N + 1 + (p + 1) + 1 by omega) z₀)
          (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
            z₀ hz₀)
          α)
      = openDuality (k := N + 2) (m := p) (hU.inter hV)
          (SingularOpenDualityMVConnSquare.castChain
            (show N + p + 3 = N + 2 + p + 1 by omega) z₀)
          (SingularOpenDualityMVConnSquare.chainBoundary_castChain_eq_zero (by omega) (by omega)
            z₀ hz₀)
          (cscMvConnecting U V hU hV N α) := by
  induction α using Module.DirectLimit.induction_on with
  | ih K g =>
    rw [openDuality_of, cscMvConnecting_of]
    exact SKEFTHawking.SingularConnSquareCloseNC.subHomConnecting_openDuality hU hV z₀ hz₀ K g

end SKEFTHawking.SingularOpenDualityConnSquareColimit
