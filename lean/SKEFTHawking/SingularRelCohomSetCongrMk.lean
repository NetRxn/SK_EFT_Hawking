import Mathlib
import SKEFTHawking.SingularCompactlySupportedTop

/-!
# Phase 5q.F (w₂-foundation) — `relCohomSetCongr` pushed through `mk`

The set-congruence transport of a relative cohomology class is the class of the transported cocycle
representative — the cohomology-side mirror of `SingularRelativeMV.relIncl_mk`. `relCohomSetCongr` is
`subst h; LinearEquiv.refl`, so once the set equality `h : S = T` is substituted the transport is the
identity. Used by `SingularConnSquareCloseNC` to collapse the `relCohomSetCongr` left over after the
`relCohomRestrict'`/`relIncl_mk` RHS-bridge peel, before `relKroneckerH_mk_mk`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularCompactlySupportedTop

namespace SKEFTHawking.SingularRelCohomSetCongrMk

variable {M : TopCat}

/-- **`relCohomSetCongr` through `mk`.** Transporting `[a]_S` along `h : S = T` is `[h ▸ a]_T`. -/
theorem relCohomSetCongr_mk {S T : Set ↑M} (h : S = T) (n : ℕ)
    (a : (relCoboundaryₗ S n).ker) :
    relCohomSetCongr h n (RelativeCohomology.mk S n a) = RelativeCohomology.mk T n (h ▸ a) := by
  subst h
  rfl

end SKEFTHawking.SingularRelCohomSetCongrMk
