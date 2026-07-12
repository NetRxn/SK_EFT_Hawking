/-
# Phase 5q.H (E1 CSC-PD tower) — `HcoreG` discharge from the two seam-matches (integral)

`HcoreG M zM hzM` (the per-`(A,B,K,g)` connecting-square naturality — takes NO orientation input, pure
topological naturality) discharged by applying `SingularSeamMatchInt.seamMatch_upperInt` (upper conjunct)
and `seamMatch_botInt` (bot conjunct) for each `(A,B,K,g)`. This VERIFIES the reduction is correctly shaped
end-to-end; it is kernel-pure ONCE the two seam-match `hmatch` residuals are discharged.

(WIP: transitively depends on the two `hmatch` sorries in `SingularSeamMatchInt` — becomes kernel-pure the
moment those close. NOT imported into the library root until then.)
-/
import Mathlib
import SKEFTHawking.SingularPDWindowInt
import SKEFTHawking.SingularSeamMatchInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularPDWindowInt (HcoreG)

namespace SKEFTHawking.SingularHcoreGDischargeInt

/-- **`HcoreG` discharged (integral)** — the connecting-square naturality bundle, from the two per-window
seam-matches. Unconditional (no orientation input); feeds `openDuality_univ_bij_of_hcoreGInt`. -/
theorem hcoreG_intrinsicInt {M : Type} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]
    (zM : SingularChainInt (TopCat.of M) (1 + 0 + 3))
    (hzM : chainBoundary (TopCat.of M) (1 + 0 + 2) zM = 0) :
    HcoreG M zM hzM := by
  intro A B hA hB
  exact ⟨fun K g => SKEFTHawking.SingularSeamMatchInt.seamMatch_upperInt A B hA hB zM hzM K g,
    fun K g => SKEFTHawking.SingularSeamMatchInt.seamMatch_botInt A B hA hB zM hzM K g⟩

end SKEFTHawking.SingularHcoreGDischargeInt
