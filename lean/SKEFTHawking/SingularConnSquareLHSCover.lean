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

/-- **Cover-partition cup-pairing readoff** (on an already-subdivided chain). For a cover `{A, B}` and
the `(A∪B)`-supported `fund`, some subdivision `Sdᵐfund` cover-splits so the cup pairing
`⟨g ⌣ b, Sdᵐfund⟩` reads off as the sum of the two cover-part pairings (via `exists_cap_cover_partition`
+ `kronecker_cup_cover_partition`). This is the wall-free half of the LHS-leg cover reduction: it carries
the single `Sdᵐ` of the cover-partition, so it has none of the `singularSd (n+1)` vs `singularSd (k+l)`
`Function.iterate`-defeq friction that composing it with `kronecker_relCocycle_singularSd_invariant` in a
single term provokes — the subdivision-invariance step is applied separately at the concrete-degree use site. -/
theorem cup_cover_pairing_sd {M : TopCat} {N p : ℕ} (A B : Set ↑M) (hA : IsOpen A) (hB : IsOpen B)
    (g : SingularCochain M (N + 1)) (b : SingularCochain M (p + 2))
    (fund : SingularChain M (N + 1 + (p + 2)))
    (hfund_mem : fund ∈ subspaceChains (A ∪ B) (N + 1 + (p + 2))) :
    ∃ (m : ℕ) (u : SingularChain (sub A) (N + 1 + (p + 2))) (w : SingularChain (sub B) (N + 1 + (p + 2))),
      kronecker (cup g b) ((SingularSubdivision.singularSd M (N + 1 + (p + 2)))^[m] fund)
        = kronecker (SingularCapChainIncl.pullbackCochain A (p + 2) b)
            (cap (SingularCapChainIncl.pullbackCochain A (N + 1) g) u)
          + kronecker (SingularCapChainIncl.pullbackCochain B (p + 2) b)
            (cap (SingularCapChainIncl.pullbackCochain B (N + 1) g) w) := by
  obtain ⟨m, u, w, hsplit, hcap⟩ :=
    SingularConnSquareRHSScaffold.exists_cap_cover_partition A B hA hB g fund hfund_mem
  exact ⟨m, u, w, SingularConnSquareMatchLHS.kronecker_cup_cover_partition (b := b) (hpart := hcap)⟩

end SKEFTHawking.SingularConnSquareLHSCover
