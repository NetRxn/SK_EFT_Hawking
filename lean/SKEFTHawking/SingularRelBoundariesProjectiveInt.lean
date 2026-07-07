/-
# Phase 5q.H (E1 CSC-PD tower) — `hproj` DISCHARGED: relative boundaries are projective

`hproj` (`∀ S j, Module.Projective ℤ (relBoundariesInt S j)`) is one of the four deep inputs threaded
through the pdWindow cover-induction. It is now a THEOREM, not a posit: `relBoundariesInt S j` is a
submodule of the free ℤ-module `RelativeChainInt S j` (`free_relChainInt`), so Kaplansky
(`FreeSubmoduleInt.projective_submodule_of_free` — a submodule of a free ℤ-module is projective, arbitrary
rank) applies. This removes the `hproj` hypothesis from the UCT-Ext-vanishing story unconditionally.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.FreeSubmoduleOfFreeInt
import SKEFTHawking.SingularSmallChainsSplitInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularSmallChainsSplitInt

namespace SKEFTHawking.SingularRelBoundariesProjectiveInt

variable {X : TopCat}

/-- **`hproj` discharged (Kaplansky)**: the relative boundaries `relBoundariesInt S j` are a projective
ℤ-module — a submodule of the free `RelativeChainInt S j`. Holds for ANY subspace `S` and degree `j`
(arbitrary, possibly infinite, rank). -/
theorem relBoundariesInt_projective (S : Set ↑X) (j : ℕ) :
    Module.Projective ℤ (relBoundariesInt S j) := by
  haveI := free_relChainInt S j
  exact SKEFTHawking.FreeSubmoduleInt.projective_submodule_of_free (relBoundariesInt S j)

/-- **Relative boundaries are FREE** (Kaplansky, the stronger form) — a submodule of the free
`RelativeChainInt S j`. -/
theorem relBoundariesInt_free (S : Set ↑X) (j : ℕ) : Module.Free ℤ (relBoundariesInt S j) := by
  haveI := free_relChainInt S j
  exact SKEFTHawking.FreeSubmoduleInt.free_submodule_of_free (relBoundariesInt S j)

/-- **Relative cycles are FREE** (Kaplansky) — a submodule of the free `RelativeChainInt S j`. The
free-part building block of the integral UCT (the `Hom(−,ℤ)`-dual of a free complex) and of the
`H₂`-free Kronecker pairing (`kron`). -/
theorem relCyclesInt_free (S : Set ↑X) (j : ℕ) : Module.Free ℤ (relCyclesInt S j) := by
  haveI := free_relChainInt S j
  exact SKEFTHawking.FreeSubmoduleInt.free_submodule_of_free (relCyclesInt S j)

end SKEFTHawking.SingularRelBoundariesProjectiveInt
