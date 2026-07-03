import Mathlib
import SKEFTHawking.SingularConnSquareCloseM2

/-!
# Phase 5q.G (G1 PD-induction, brick B1b) — the degree-GENERIC `of_mvConnecting` reducer

`SingularConnSquareCloseM2.subHomConnecting_legW_eq_legW_of_mvConnecting` is stated at the
`(m := p + 1)`-instantiation; its 3-line proof runs over the fully `p`-generic
`subHomConnecting_legW` (`SingularConnSquareLHSExplicit:193`) + two `LinearEquiv`-cancellations.
This module restates it degree-generically (`m := p`, any `p : ℕ` — in particular `p = 0`, the
bottom row of the `(3,0)`-ladder), so the bottom connecting square's reducer needs no mirror.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
  SKEFTHawking.SingularSubHomologyMV
  SKEFTHawking.SingularMayerVietorisLES SKEFTHawking.SingularOpenDuality
  SKEFTHawking.SingularCompactlySupportedOpen SKEFTHawking.SingularCompactsInOpen
  SKEFTHawking.SingularConnSquareLHSExplicit

namespace SKEFTHawking.SingularConnSquareCloseM2Gen

variable {X : TopCat} [T2Space ↑X]

/-- **The degree-generic `of_mvConnecting` reducer**: the per-compact connecting square
`subHomConnecting (legW K g) = R` follows from the `mvConnecting`-evaluation hypothesis `hmv`
(the MV connecting of the leg equals the double-seam-transport of `R`), at ANY homology degree
`p` — in particular `p = 0` (the bottom row). -/
theorem subHomConnecting_legW_eq_of_mvConnecting_gen (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V)
    {k p : ℕ} (z₀ : SingularChain X (k + p + 1))
    (hz₀ : chainBoundary X (k + p) z₀ = 0)
    (K : CompactsIn (U ∪ V)) (g : cohomGW (U ∪ V) k K)
    (R : Homology (sub (U ∩ V)) p)
    (hmv : mvConnecting (X := sub (U ∪ V)) (Subtype.val ⁻¹' U) (Subtype.val ⁻¹' V) p
          (SingularSubHomologyMV.cover_preimage U V hU hV)
          (legW (m := p) (hU.union hV) z₀ hz₀ K g)
        = (seamHomologyEquiv (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) p).symm
            ((seamI U V p).symm R)) :
    subHomConnecting U V hU hV p (legW (m := p) (hU.union hV) z₀ hz₀ K g) = R := by
  have hL := subHomConnecting_legW U V hU hV z₀ hz₀ K g
  rw [hL]
  rw [hmv, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]

end SKEFTHawking.SingularConnSquareCloseM2Gen
