/-
# Phase 5q.H close-out — the canonical disjoint-union block-congruence FEEDS the banked σ-additivity

`IntersectionMatrixDisjointSumInt` proved the canonical disjoint-union intersection matrix is exactly
block-diagonal (`interMatrix_disjointSum_eq_blockDiag`) and, directly, σ-additive
(`latticeSig_interMatrix_disjointSum`). This module closes the loop with the BANKED lattice lemma the
σ-descent additivity plumbing was reduced to — `PinPlusKTSpinSigmaStock.latticeSig_of_blockCongr` — by
supplying the `IntCongr (reindex (finCongr hn)) (blockDiag)` shape that lemma consumes, and re-deriving
σ-additivity THROUGH it (`latticeSig_interMatrix_disjointSum_via_blockCongr`).

## Where this lands the σ-descent

`PinPlusKTSpinSigmaStock.sigAdditivity_atoms_of_blockCongr` discharges the `hadd` (disjoint-union
additivity) input of `sigDescend` from a single geometric atom `InterMatrixBlockAtom prov a`: the
intersection matrix of `p ⊔ q` is integer-congruent to the block sum. The #161 assessment established
that for an ARBITRARY disclosed bundle `a` this atom is not provable (its `fc`/`B` on `p ⊔ q` bear no
relation to the summands). **This module discharges exactly that congruence for the CANONICAL sum
construction** (`intFundClassSum`/`intH2BasisSum`): the `IntCongr` a canonical bundle's block atom needs
is `IntCongr.rfl` post the block-diagonal equality, and it feeds `latticeSig_of_blockCongr` verbatim. So
the σ-descent additivity plumbing is fully discharged for the canonical construction; only the deep
bordism-invariance half `hbord` of `sigDescend` remains.

**Honest reduction of the remaining bridge.** Landing this on a genuine `SpinSigmaAtoms` bundle `a` — i.e.
proving `InterMatrixBlockAtom prov a` outright — requires `a` to DISCLOSE that its `fc`/`B` on a disjoint
union are the canonical sum constructions (`a.fc ⟨p.1.sum q.1, _⟩ = intFundClassSum … (a.fc p) (a.fc q)`
and likewise for `B`, modulo the carrier identification `(p.1.sum q.1).M ≃ ↑p.1.M ⊕ ↑q.1.M`). That
`canonical-sum disclosure` is the single named sub-atom the full `SpinSigmaAtoms`-level bridge reduces to;
the lattice/geometry content it gates is entirely discharged here.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.IntersectionMatrixDisjointSumInt
import SKEFTHawking.PinPlusKTSpinSigmaStock

namespace SKEFTHawking.SingularCohomologyInt

open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularCohomologyDisjointSum (sumSpace)
open SKEFTHawking.SpinSigmaRoute (blockDiag)
open SKEFTHawking.PinPlusKTSpinSigmaStock (latticeSig_of_blockCongr)

variable (A B : TopCat)

/-- **The canonical-bundle block-congruence, in the exact `latticeSig_of_blockCongr` shape.** For the
canonical sum construction, the reindexed disjoint-union intersection matrix is `IntCongr` to the block
sum of the pieces' matrices (`hn : rank = b₂(M) + b₂(N)`, taken at the definitional value
`BA.rank + BB.rank`). Since `interMatrix_disjointSum_eq_blockDiag` makes them literally equal, the
congruence is the identity change of basis — this is the discharged form of the block atom
`InterMatrixBlockAtom` for the canonical construction. -/
theorem intCongr_reindex_interMatrix_disjointSum_blockDiag (fcA : IntFundamentalClass A)
    (fcB : IntFundamentalClass B) (BA : IntH2Basis A) (BB : IntH2Basis B) :
    IntCongr
      (Matrix.reindex (finCongr (rfl : BA.rank + BB.rank = BA.rank + BB.rank))
        (finCongr (rfl : BA.rank + BB.rank = BA.rank + BB.rank))
        (interMatrix (intFundClassSum A B fcA fcB) (intH2BasisSum A B BA BB)))
      (blockDiag (interMatrix fcA BA) (interMatrix fcB BB)) := by
  rw [finCongr_refl, Matrix.reindex_refl_refl, interMatrix_disjointSum_eq_blockDiag]
  exact IntCongr.rfl _

/-- **σ-additivity of the canonical disjoint-union signature, re-derived THROUGH the banked
`latticeSig_of_blockCongr`.** This exhibits the block-congruence (`intCongr_reindex_…`) feeding the exact
lattice lemma the σ-descent additivity was reduced to: `σ(M ⊔ N) = σ(M) + σ(N)` for the canonical
construction, from the two per-piece even-unimodular obligations. Same conclusion as
`latticeSig_interMatrix_disjointSum`, but routed through `latticeSig_of_blockCongr` — the concrete
witness that the σ-descent's `hadd` plumbing is discharged for the canonical bundle. -/
theorem latticeSig_interMatrix_disjointSum_via_blockCongr (fcA : IntFundamentalClass A)
    (fcB : IntFundamentalClass B) (BA : IntH2Basis A) (BB : IntH2Basis B)
    (heuA : IsEvenUnimodular (interMatrix fcA BA)) (heuB : IsEvenUnimodular (interMatrix fcB BB)) :
    latticeSig (interMatrix (intFundClassSum A B fcA fcB) (intH2BasisSum A B BA BB))
      = latticeSig (interMatrix fcA BA) + latticeSig (interMatrix fcB BB) :=
  latticeSig_of_blockCongr (n := BA.rank + BB.rank) (np := BA.rank) (nq := BB.rank) rfl
    (interMatrix (intFundClassSum A B fcA fcB) (intH2BasisSum A B BA BB))
    (interMatrix fcA BA) (interMatrix fcB BB) heuA heuB
    (intCongr_reindex_interMatrix_disjointSum_blockDiag A B fcA fcB BA BB)

end SKEFTHawking.SingularCohomologyInt
