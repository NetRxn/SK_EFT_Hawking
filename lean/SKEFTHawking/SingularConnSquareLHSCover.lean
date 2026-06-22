import Mathlib
import SKEFTHawking.SingularConnSquareRHSPairing
import SKEFTHawking.SingularConnSquareCloseFinal

/-!
# Connecting-square LHS-leg cover assembly (Phase 5q.F L2)

The LHS leg of the connecting-square cross-realization match pairs a *relative cocycle*
`cup (gL↾) b` (the cup of the pulled-back relative-cohomology rep `gL↾ = pullbackCochain (gL)`
with the absCohomConn rep `b`) against the (only relatively closed) fundamental cycle `fund_∪`.

This file isolates the **relative-cocycle property of the LHS cochain** `cup (gL↾) b`, composing the
committed `SingularConnSquareRHSPairing` bricks: `cup_cocycle` (cup of cocycles is a cocycle),
`cup_mem_relCochains` (cup with a relative cochain stays relative), `pullbackCochain_mem_relCochains`
(pullback preserves relative cochains), and `relCocycle_props` (a relative-cohomology kernel element's
underlying cochain is an absolute cocycle vanishing on the subspace). It is the hypothesis bundle the
relative subdivision-invariance step (`kronecker_relCocycle_singularSd_invariant`) consumes before the
cap cover-partition readoff.
-/

namespace SKEFTHawking.SingularConnSquareLHSCover

open SKEFTHawking SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularConnSquareRHSPairing

/-- **The LHS-leg cochain `cup (gL↾) b` is a relative cocycle.** For a relative-cohomology kernel
element `gL` over a subspace `S` and an absolute cocycle `b` on `sub W`, the cup of the pulled-back
`gL↾ = pullbackCochain W gL.1.1` with `b` (a) is an absolute cocycle (`coboundary = 0`) and (b) vanishes
on `C(val⁻¹ S)` (lies in `relCochains (val⁻¹ S)`). This is exactly the relative-cocycle hypothesis bundle
that `kronecker_relCocycle_singularSd_invariant` needs to make the LHS pairing subdivision-invariant. -/
theorem cup_pullback_relCocycle {X : TopCat} {N p : ℕ} {S W : Set ↑X}
    (gL : LinearMap.ker (relCoboundaryₗ S (N + 1)))
    (b : LinearMap.ker (coboundaryₗ (sub W) (p + 2))) :
    coboundary (sub W) (N + 1 + (p + 2))
        (cup (SingularCapChainIncl.pullbackCochain W (N + 1) gL.1.1) b.1) = 0
      ∧ cup (SingularCapChainIncl.pullbackCochain W (N + 1) gL.1.1) b.1
          ∈ relCochains (Subtype.val ⁻¹' S : Set ↑(sub W)) (N + 1 + (p + 2)) := by
  have hgcoc : coboundary (sub W) (N + 1)
      (SingularCapChainIncl.pullbackCochain W (N + 1) gL.1.1) = 0 := by
    rw [SingularConnSquareCloseFinal.coboundary_pullbackCochain,
      (SingularConnSquareRHSPairing.relCocycle_props gL).1]
    funext τ; simp
  refine ⟨SingularConnSquareRHSPairing.cup_cocycle _ _ hgcoc b.2, ?_⟩
  exact SingularConnSquareRHSPairing.cup_mem_relCochains _ b.1
    (SingularConnSquareRHSPairing.pullbackCochain_mem_relCochains gL.1.1
      ((SingularRelativeCohomologyMod2.mem_relCochains (S := S) (N + 1) gL.1.1).2
        (SingularConnSquareRHSPairing.relCocycle_props gL).2))

end SKEFTHawking.SingularConnSquareLHSCover
