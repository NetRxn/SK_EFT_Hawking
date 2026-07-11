/-
# Phase 5q.H (E1 CSC-PD tower) — cover-split cap-boundary (integral, hcore brick 6e-B)

`cover_partition_cap_boundaryInt` — the `∂w_X`-leg of the seam-match. When the cap of an absolute
cocycle `g` against `z` splits along the cover `{A,B}` as `chainIncl A zA + chainIncl B zB`, the ambient
boundary distributes and equals `(-1)^k • capInt g (∂z)` (via `capInt_cocycle_chainMap` +
`chainIncl_chainBoundary`). The integral 3-line port of the mod-2 `cover_partition_cap_boundary_mod` — no
`η`-correction is needed since the integral cap-split `hpart` is exact. Consumed by the LHS
(`capInt g_rep (∂w_X)`) leg, which the descent bridge glues to the RHS.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.IntCapProductInt
import SKEFTHawking.SingularCapChainInclInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)

namespace SKEFTHawking.SingularCoverPartitionCapBoundaryInt

variable {M : TopCat}

/-- **Brick 2** (cover-split cap-boundary): if the cap of an absolute cocycle `g` against `z` splits
along the cover `{A,B}` as `chainIncl A zA + chainIncl B zB`, then `∂` distributes and equals
`(-1)^k • capInt g (∂z)` (via `capInt_cocycle_chainMap` + `chainIncl_chainBoundary`). Instantiated at
`sub(A∪B)` with `hcap`, and `capInt g (∂z) = 0` when `∂z` lands where `g` vanishes, this forces
`chainIncl A (∂zA) + chainIncl B (∂zB) = 0` — the seam-localization of the cover-split boundary. -/
theorem cover_partition_cap_boundaryInt {k m : ℕ} {A B : Set ↑M}
    (g : SingularCochainInt M k) (hg : coboundaryₗ M k g = 0)
    (z : SingularChainInt M (k + m + 1))
    (zA : SingularChainInt (sub A) (m + 1)) (zB : SingularChainInt (sub B) (m + 1))
    (hpart : capInt (m := m + 1) g z
        = chainIncl A (m + 1) zA + chainIncl B (m + 1) zB) :
    chainIncl A m (chainBoundary (sub A) m zA) + chainIncl B m (chainBoundary (sub B) m zB)
      = (-1 : ℤ) ^ k • capInt (m := m) g (chainBoundary M (k + m) z) := by
  have h1 := capInt_cocycle_chainMap g hg z
  rw [hpart, map_add, ← chainIncl_chainBoundary, ← chainIncl_chainBoundary] at h1
  exact h1

end SKEFTHawking.SingularCoverPartitionCapBoundaryInt
