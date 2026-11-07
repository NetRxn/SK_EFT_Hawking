# Independent original Eq11 shifted determinant source review R1

**ACCEPT the exact one-module source increment for the pointwise shifted
determinant and Berezin coefficient identities.** Scope is source semantics
and composition. ROOT separately owns kernel replay, aggregate registration,
native absorption, and all publication gates.

## Exact authority

Worker commit `b2a835128af0276672e15bdbad1527586cb62a19` has sole parent
`212e9f91e9c18d61e234c1144af7063efe4923db` and adds only
`lean/SKEFTHawking/ADW/FiniteGrassmannShiftedDiracBerezin.lean`, 248 lines.
The exact Git blob has SHA-256
`998ee608d89effbf1ad624ed62c00741c3a4dd1decf8ca1914890d66f76bf75c`,
matching the frozen review input. The diff whitespace check passed. Its
three imports match the accepted design, two project modules plus
`Mathlib.Algebra.Polynomial.Roots` for scalar polynomial extensionality.
The file introduces no admitted proof, declared axiom, unsafe definition,
or new matrix, action, measure, or Berezin normalization.

I read the original coframe, evaluation, Dirac/Berezin, perturbation and
weighted-Haar sources at the exact parent, the accepted design and its
independent assessment, and the held source text for the Eq. (23)
anchor. That anchor is the dimensionless alpha=1/2 convention. The
four coframe blocks have signs +,-,-,+ and the quarter prefactor.
`hopping_reconstructs_coframe` and `globalMatrix_eq9` preserve the same
ordered bilinears and sum coincident periodic anchors. The fixed
`sourceBasis` uses the literal barred/unbarred order. Relative to the
interleaved diagonal row order its local permutation is even (two
inversions), and the existing matrix-independent unit top coefficient
feeds `rowBerezin_normalization` and `berezin_nilExp_det` at cutoff 4V.

## All nine public statements

| Exact public theorem | Independent semantic check |
|---|---|
| `shiftedDiracDetAtLink_eval` | Translation acts on X only, fixes every link coefficient, and sends X_i to X_i+J_i. Specialization of the continuous link coefficient is point evaluation at U. Generator extensionality gives evaluation at x+J over complex coordinates. The entrywise identity and ring-hom determinant map retain all signed hopping blocks, with no conjugation of J, transpose, or inverse. |
| `shiftedDiracDetAtLink_first` | Eval of the one-coordinate formal increment is eval at x+t e_a. The source polynomial and its increment have zero constant coefficients. The existing joint-zero identity at 4V splits the finite exponential in the commutative even carrier, with increment first. Evaluating the scalar coefficient polynomial then gives the actual Berezin functional; coefficient one inserts the original T_a. |
| `shiftedDiracDetAtLink_mixed` | Apply the first identity pointwise at the independently incremented b coordinate. The scalar polynomial left multiplier is T_a throughout, so coefficient one inserts T_b to its right. Exterior multiplication outside the even carrier is merely associated and distributed. No distinctness, evenness of the generic left multiplier, or commutation of arbitrary exterior factors is assumed. |
| `shiftedDiracDetHaarPolynomial_zero` | Translation at J=0 is the identity ring hom on C and X generators, so the original determinant polynomial is recovered exactly. |
| `shiftedDiracDetAtLink_coeff_one` | The existing one-increment bridge converts coefficient one to the identical evaluated partial. |
| `shiftedDiracDetAtLink_coeff_one_one` | The first coefficient is taken in the outer increment for a, then in the independent inner increment for b. The existing bridge gives d_b(d_a P), including a=b. The exact coframe product T_a T_b uses the same order. |
| `shiftedDiracDetHaarPolynomial_eval` | Existing real-Haar evaluation specializes link coefficients and casts only h into the complex base. J remains arbitrary complex. |
| `shiftedDiracDetHaarPolynomial_first` | Move one partial through coefficient specialization and apply the fixed-link first identity, preserving the original coframe. |
| `shiftedDiracDetHaarPolynomial_mixed` | Move both partials through coefficient specialization, preserving d_b(d_a P), then use the fixed-link mixed identity with the diagonal allowed. |

The use of scalar polynomial extensionality is valid over infinite ℂ.
In the insertion polynomial, scalar coefficients carry 1/k! from
the existing finite exponential. Coefficient one selects k=1, where
the factorial is exactly one. A site exists via the zero point of the
product torus, and positive extents make the site type finite, so V>0
and 1 is in range(4V+1). There is no empty-torus obligation on this
carrier. Zero coframe, base, source and singular matrices are permitted.
The one-coordinate evaluation argument never divides by a determinant,
a weight, or a partition function. The three source-cast/diagonal/
orientation controls and the singular and swapped symbolic determinant
controls are supplementary arithmetic witnesses in the adjacent
`publication-l1-eq11-determinant-semantic-r1.controls.json`.
These do not measure an actual lattice input or replay Lean.

## Downstream boundary

The module has no Gaussian variance or scale hypothesis and does not
translate the site weight or measure. A consumer must retain all
original site weights, the actual printed and closed source words and
their distinct continuity witnesses, and both original iterated orders.
For the proven d_b(d_a P) order, the existing weighted transfer takes
indices (b,a) and returns A_a(A_b W). Its expansion retains both
gradients and the negative diagonal contact. Source-integral wrappers,
zero-source Eq10 recovery at the integral level, full Z, normalization,
physical response, and publication acceptance remain separate.

The first and final packet checks are both SAME, with `fresh=true`
and no changed paths. No repository write, slot action, Lean execution
or aggregate build occurred in this review.
