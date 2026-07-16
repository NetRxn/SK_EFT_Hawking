import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalAlphaU
import SKEFTHawking.SingularRelativeCoverMVTransport

/-!
# Phase 5q.H — THE CYLINDER CLASS AS A DETECTING CHAIN (the cover-glue's cylinder-side feed)

The cylinder engine's unconditional `[W,∂W]` witness (`hasRelFundClass_cylGen`, for any closed
connected charted `M`) produces, through the representation and detection-producer layer
(`SingularRelativeCoverMVTransport`), a concrete CHAIN on `M × I` whose boundary is supported in
the cylinder's manifold boundary `M × {⊥,⊤}` and whose local class is nonzero at every interior
point. This is exactly the piece-intrinsic input the cylinder-core detection supplier
(`SingularSurgeryCoreDetect.cylCore_relClassOf_ne_zero`) consumes on the surgery-trace carrier —
the cover-glue's cylinder-side chain, delivered by the engine rather than assumed.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no
`native_decide`, no `maxHeartbeats`.
-/

open scoped Manifold
open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularMayerVietoris
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalAlphaU
open SKEFTHawking.SingularRelativeCoverMV
open SKEFTHawking.SingularRelativeCoverMVTransport

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderChainRep

variable {m' : ℕ}
  {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M] [PreconnectedSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M]

/-- **The cylinder's detecting chain** — the unconditional cylinder `[W,∂W]` witness realized as a
concrete chain: a `(m'+3)`-chain on `M × I` whose boundary is supported in the manifold boundary
`∂(M×I) = M × {⊥,⊤}` and whose local class is NONZERO at every interior point of the cylinder. The
cover-glue's cylinder-side feed, produced by `hasRelFundClass_cylGen` through the representative
(`exists_relClassOf_rep`) and the detection producer
(`relClassOf_rep_ne_zero_of_restrictsToRelGen`). -/
theorem exists_cylinder_detecting_chain [T1Space (cylW M)] :
    ∃ (c : SingularChain (TopCat.of (cylW M)) (m' + 1 + 2))
      (hc : chainBoundary (TopCat.of (cylW M)) (m' + 1 + 1) c
        ∈ subspaceChains (X := TopCat.of (cylW M)) ((cylModel m').boundary (cylW M))
            (m' + 1 + 1)),
      ∀ (y : ↑(TopCat.of (cylW M))) (hy : y ∉ (cylModel m').boundary (cylW M)),
        relClassOf (X := TopCat.of (cylW M)) ({y}ᶜ) (m' + 1) c
          (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hy) (m' + 1 + 1) hc) ≠ 0 := by
  obtain ⟨α, hα⟩ := hasRelFundClass_cylGen (M := M) (m' := m')
  obtain ⟨c, hc, rfl⟩ :=
    exists_relClassOf_rep (X := TopCat.of (cylW M)) ((cylModel m').boundary (cylW M)) (m' + 1) α
  exact ⟨c, hc, fun y hy => relClassOf_rep_ne_zero_of_restrictsToRelGen c hc hα y hy⟩

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderChainRep
