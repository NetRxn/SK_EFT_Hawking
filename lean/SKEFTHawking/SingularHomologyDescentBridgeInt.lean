/-
# Phase 5q.H (E1 CSC-PD tower) — cohomology-level descent bridge (integral, hcore brick 6e-c-descent)

`homology_eq_of_ambient_boundaryInt` — the rigorous ℤ replacement for the mod-2 Kronecker descent (the
mechanism the seam-match core needs). Two cycles of `sub S` are homologous **iff** their ambient
`chainIncl`-realizations differ by the boundary of an `S`-supported chain. The subtlety it resolves: the
homology map `chainIncl(S)_* : H(sub S) → H(X)` is NOT injective, so realizing to the ambient does not by
itself descend. But the **chain map** `chainIncl S` IS injective, so an ambient bounding chain that is
itself `S`-supported reflects back (via `inclRangeEquiv.symm`) to a genuine `sub S` bounding chain.

This is exactly where the mod-2 side used the field-only Kronecker pairing (~3900 lines of
`SingularConnSquareCloseNC`); over ℤ it is this ~15-line chain-injectivity argument. Consumed by the
seam-match `hmatch` to descend the ambient-realized `∂w_X` vs `∂z_J` identity back to `H₁(sub(A∩B))`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularRelHomologyInt
import SKEFTHawking.SingularExcisionIsoInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)

namespace SKEFTHawking.SingularHomologyDescentBridgeInt

variable {X : TopCat}

/-- **Cohomology-level descent bridge**: two cycles of `sub S` are homologous if their ambient
`chainIncl`-realizations differ by the boundary of an `S`-supported chain. (The rigorous replacement for
the mod-2 Kronecker descent: `chainIncl S` is injective, so an ambient bounding chain that is itself
`S`-supported reflects back to a `sub S` bounding chain.) -/
theorem homology_eq_of_ambient_boundaryInt {S : Set ↑X} {n : ℕ}
    (cL cR : cycles (sub S) (n + 1)) (E : SingularChainInt X (n + 1 + 1))
    (hE : E ∈ subspaceChainsInt S (n + 1 + 1))
    (h : chainBoundary X (n + 1) E
        = chainIncl S (n + 1) (cL : SingularChainInt (sub S) (n + 1))
          - chainIncl S (n + 1) (cR : SingularChainInt (sub S) (n + 1))) :
    Homology.mk (sub S) (n + 1) cL = Homology.mk (sub S) (n + 1) cR := by
  refine (Submodule.Quotient.eq _).2 ?_
  simp only [Submodule.submoduleOf, Submodule.mem_comap, Submodule.subtype_apply,
    AddSubgroupClass.coe_sub]
  refine ⟨(inclRangeEquiv S (n + 1 + 1)).symm ⟨E, hE⟩, ?_⟩
  apply chainIncl_injective S (n + 1)
  rw [chainIncl_chainBoundary, chainIncl_inclRangeEquiv_symm, map_sub]
  exact h

end SKEFTHawking.SingularHomologyDescentBridgeInt
