# D4, D8 and D9 module coverage reconciliation

The existing module resolver and declaration map supply the proof locators.
The validator reports 146 registered modules without visible manuscript
coverage, down from 181 on the paired base. The ceiling moves from 147 to
146. The lookup and falsifiability rules stay in force.

| Bundle | Previously missing | Now missing | Repair |
| --- | ---: | ---: | --- |
| D4 | 24 | 2 | Ten registrations from three documented empty lifts are removed through the append-only writer. The density and Fibonacci compilation sections identify their existing Lean dependencies. |
| D8 | 33 | 25 | The existing verification appendix identifies the literal gate alphabet, Toffoli bound and channel representation, compiler alphabet and length functions, and the two operator-norm dependencies. |
| D9 | 16 | 11 | The existing protocol and entropy sections identify the swap and chain definitions, the formal erasure-bound function and the two concrete entropy carriers. |

## Source evidence

- D4 density is the entry point in `SU2BCHBracketClosure` and calls the
  Cartan argument in `OneParameterSubgroupSU2`. The declaration map
  traces the argument to the explicit braid matrices in `FibSU2LieBundle`
  and the traceless skew-Hermitian carrier in `SU2LieAlgebra`.
- D4's same-word accuracy and length result lives in `SolovayKitaevPathA`.
  The abstract quantitative Fibonacci result calls
  `skLength_at_skLevel_polylog_le`. The length bound uses the precision
  threshold and level selection from `SolovayKitaevRecursion`. The
  compiled error proof uses the commutator and base-word constructions.
- D8's declarations already use the referenced modules in their types
  or proof bodies. For example, `diamondDist_unitaryKraus_le` calls the
  tensor norm bound from `KroneckerOpNorm`, and
  `diamondDist_cliffordTCompile_le` uses the row-sum estimate from
  `MatrixNormBridge`.
- D9 retains its distinction between the coded erasure-bound function
  and the capacity theorem cited from the literature.

The original D4 lift records remain in the append log. The corresponding
work remains available upstream. The D4 Drinfeld double discussion has
related terminology, so the `SymTFTAudit.DrinfeldCenter` registration
remains for separate review. The original publication review findings
and manuscript freshness states require their own dispositions.
