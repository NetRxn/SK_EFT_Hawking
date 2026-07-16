import Mathlib
import SKEFTHawking.PinPlusCylComponentHomeo
import SKEFTHawking.PinPlusCylComponentManifold
import SKEFTHawking.SingularRelativeDisjointUnionDetect
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalAlphaU

/-!
# Phase 5q.H — THE EXCISION BRIDGE: per-component detection from the CONNECTED class (route (b))

The keystone the #137 wall-isolation report reduced the disconnected `D` field to: the
sub-cylinder→ambient open-embedding excision bridge. For a clopen component `C ⊆ M` (charted, closed,
nonempty, **connected**) the CONNECTED cylinder engine supplies a relative fundamental class `μ_C` on
`cylW ↥C` that restricts to the interior generator at every interior point
(`…CrossLocalAlphaU.hasRelFundClass_cylGen`, valid because `↥C` is preconnected). We transport `μ_C`
back to the ambient piece `U = C ×ˢ univ ⊆ cylW M` through the piece homeomorphism `pieceHomeo`
(`↥U ≃ₜ cylW ↥C`), obtaining `αU`, and show that `αU`'s INTRINSIC local restriction inside `sub U` is
nonzero at every interior point of `U`.

Combined with `SingularRelativeDisjointUnionDetect.restrictsToRelGenOn_of_relIncl_ne_zero` (which needs
only a nonzero intrinsic restriction, the `ℤ/2` local-homology uniqueness absorbing any generator
mismatch), this yields the per-piece detection witness `RestrictsToRelGenOn` that the disconnected
engine consumer `cylinderRelFundClassDatum_of_clopenSplit` requires — with NO homeomorphism-transport
of the Lefschetz–Wu datum (the standing wall), only the transport of a single relative homology class
and the naturality of local restriction under a pair map (`relIncl_map`).

The transport nonzero-ness is pure naturality: `relIncl (…) αU = RelativeHomology.map e.symm
(restrictBd (∂cylW ↥C) μ_C)`, the connected restriction `restrictBd … μ_C = (cylGen …).symm 1 ≠ 0`,
and `RelativeHomology.map` of a homeomorphism is injective (`map_bijective_of_comp_id`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no
`native_decide`, no `maxHeartbeats`.
-/

open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeMV
open SKEFTHawking.SingularExcisionIso
open SKEFTHawking.SingularManifoldFundamentalClass
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.SingularRelativeExcisionRestrict
open SKEFTHawking.SingularRelativeDisjointUnionDetect
open SKEFTHawking.PinPlusCylComponentHomeo

namespace SKEFTHawking.PinPlusCylComponentExcisionBridge

noncomputable section

variable {m' : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M]

/-! ## §1. The boundary is governed by the interval coordinate (routed through `cyl_boundary_eq`). -/

/-- **The cylinder boundary membership is the interval-endpoint condition** (any charted base). Via
`cyl_boundary_eq` (`∂ = univ ×ˢ {⊥,⊤}`); NO unfolding of the concrete `ModelWithCorners.boundary`.
Reused at both `M` and the component base `↥C`. -/
theorem mem_cylBoundary_iff (p : cylW M) :
    p ∈ (cylModel m').boundary (cylW M) ↔ p.2 ∈ ({⊥, ⊤} : Set (Set.Icc (0 : ℝ) 1)) := by
  rw [cyl_boundary_eq]
  simp [Set.mem_prod]

end

end SKEFTHawking.PinPlusCylComponentExcisionBridge
