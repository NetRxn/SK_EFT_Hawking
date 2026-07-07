/-
# Phase 5q.H (E1 CSC-PD tower) — top relative homology is free (the `hfree` foundation)

`hfree` (top-degree relative-homology freeness of a good-compact, `Module.Free ℤ (RelHomologyInt Sᶜ (m+2))`)
is a deep input threaded through the pdWindow. Its **base case** — a single point `S = {x}` — is a clean
discharge: `manifoldLocalHomologyIsoInt` gives `H₄(M, M∖x; ℤ) ≅ ℤ`, and `ℤ` is free, so
`Module.Free ℤ (RelHomologyInt {y | y ≠ x} 4)` follows by transport. This is the seed of the general
good-compact freeness (a good-compact is a finite chart-ball union; its top homology assembles from these
local `ℤ`'s via excision/MV — the substantial remaining step).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularLocalHomologyIsoInt

open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularLocalHomologyIsoInt

namespace SKEFTHawking.SingularTopHomologyFreeInt

/-- **The top relative homology at a point is free**: `H₄(M, M∖x; ℤ)` is a free ℤ-module (it is `≅ ℤ`
via `manifoldLocalHomologyIsoInt`). The base case of the good-compact top-homology freeness `hfree`. -/
theorem relHomology_point_top_free {M : Type} [TopologicalSpace M] [T1Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] (x : M) :
    Module.Free ℤ (RelHomologyInt (X := TopCat.of M) {y | y ≠ x} 4) :=
  Module.Free.of_equiv (manifoldLocalHomologyIsoInt x).symm

end SKEFTHawking.SingularTopHomologyFreeInt
