/-
# Phase 5q.H (E1 CSC-PD tower) — relCohomSetCongrInt `mk`-push helpers (integral)

The three `subst`-based `mk`-push rules for `relCohomSetCongrInt` (the relative-cohomology set-congruence
transport), filling the notebook-noted "`relCohomSetCongrInt` has NO `_mk`" gap that blocked the seam-match
connecting-rep decomposition. Consumed by the `hcoreG` seam-match discharge to strip the `relCohomSetCongr`
wrappers off `relCohomMvConnectingInt`'s argument so `exists_mvUnion_of_connecting_mk_eq` fires.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularCSCMayerVietorisMiddleInt
import SKEFTHawking.SingularEuclideanCapIsoInt

open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularCSCMayerVietorisMiddleInt (relCohomSetCongrInt)

namespace SKEFTHawking.SingularCSCMayerVietorisMiddleInt

variable {X : TopCat}

/-- `relCohomSetCongrInt` pushed through `mk` (the missing `_mk` rule). -/
theorem relCohomSetCongrInt_mk {S T : Set ↑X} (h : S = T) (n : ℕ)
    (z : LinearMap.ker (relCoboundaryIntₗ S n)) :
    relCohomSetCongrInt h n (RelativeCohomologyInt.mk S n z)
      = RelativeCohomologyInt.mk T n (h ▸ z) := by
  subst h; rfl

/-- `(relCohomSetCongrInt h).symm` pushed through `mk`. -/
theorem relCohomSetCongrInt_symm_mk {S T : Set ↑X} (h : S = T) (n : ℕ)
    (z : LinearMap.ker (relCoboundaryIntₗ T n)) :
    (relCohomSetCongrInt h n).symm (RelativeCohomologyInt.mk T n z)
      = RelativeCohomologyInt.mk S n (h ▸ z) := by
  subst h; rfl

/-- Transporting a relative cocycle along a set-equality preserves its underlying cochain. -/
theorem ker_transport_coe {S T : Set ↑X} (h : S = T) (n : ℕ)
    (z : LinearMap.ker (relCoboundaryIntₗ T n)) :
    ((h ▸ z : LinearMap.ker (relCoboundaryIntₗ S n)).1.1 : SingularCochainInt X n)
      = (z.1.1 : SingularCochainInt X n) := by
  subst h; rfl

end SKEFTHawking.SingularCSCMayerVietorisMiddleInt
