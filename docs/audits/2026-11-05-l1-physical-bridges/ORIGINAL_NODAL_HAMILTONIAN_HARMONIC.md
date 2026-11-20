# Retained-link harmonic support and the Hamiltonian-cycle coefficient of P0

Executor01a1ac65, task l1-nodal-hamiltonian-harmonic-r1, source `53765e44ee86bbc3e77d0dc208b7521346d34a1d`. ROOT accepted that source at its scoped evidence boundary. This candidate derives an exact projection of the full mixed-direction coefficient. Its scalar value remains open. The task packet was checked fresh before the formal write-up. The work uses manual algebra and static source reads.

## Harmonic bound on the original nodal variables

Use the accepted zero-source baseframe coefficient `P0(B) = ∫ dU1 I64 A8^16`. The nodal retained pair is `(B_e,B_e^-1)` on each of the twelve spatial endpoint pairs, with an arbitrary orientation for e. The twenty-four moving spatial anchors are still independently integrated. At each base x and direction i the curvature orders are `U1_i(x)† U0_i(x)` and `U0_i(x)† U1_i(x)`. Both coframe orders and the original internal sums and quarters stay in A8. Each vertex has one curvature occurrence and two coframe occurrences in three distinct spatial directions.

Expand into terms with a fixed chirality for each moving occurrence. Fix a moving anchor a and chirality χ. Write c_(a,χ) for the number of curvature factors on it and h_(a,χ) for the number of coframe factors. Its retained oriented matrix is B_a, which is B_e or B_e^-1. Before moving Haar integration the only B_a factors come from curvature, with one fundamental or dual fundamental entry per curvature occurrence in that chirality. For a second bound, change U_a to B_a W_a independently in that anchor. Both curvature orders become W_a† or W_a. Each coframe occurrence of U_a or U_a† then carries one B_a or B_a† factor. Haar normalization and the inherited odd polynomial are preserved by this change of variables.

For SU(2), let the harmonic label n denote the irreducible representation Sym^n(C²), of spin n/2. An entry of the fundamental or its dual is in label 1. Products of d such entries are matrix coefficients of tensor powers of the fundamental, using its invariant alternating tensor to identify the dual. The symmetric tensor decomposition by contraction with that tensor gives labels d,d−2,..., down to 0 or 1. These coefficient spaces are orthogonal for normalized Haar. Inversion preserves each label, since it exchanges matrix entries with those of the dual. Consequently after integrating this moving variable, its dependence on B_a has labels at most min(c_(a,χ),h_(a,χ)). If c and h have different parity the moving-anchor center flip already annihilates the term. One can first give every based B_a an independent argument to obtain these separate bounds and then impose the nodal inverse relation. This order handles shared retained variables without assuming the two moving anchors are identified.

On the nodal pair, multiplication of the two endpoint factors and restriction to `(B_e,B_e^-1)` therefore gives the necessary bound

`n_(e,χ) <= Σ_(a on e) min(c_(a,χ),h_(a,χ)).`                 (1)

For example, the bound follows from the maximum weight in the tensor product of the two endpoint harmonic representations. This argument applies termwise after expanding and taking the inherited Berezin top, which is independent of the retained matrices. It is valid for both chiralities and every direction mixture. The sum of the right sides over all e,χ is at most 16, the total curvature count. The previously accepted pure-direction subtotal has trivial retained harmonic support.

## A normalized spin-one loop projection

Fix a Hamiltonian cycle H of Q3 with ordered vertices x_0,...,x_7, for example `000,100,110,010,011,111,101,001` and back to `000`. Give its eight edges the cycle orientation, use inverse matrices when the pair orientation differs, and choose one chirality χ. Put

`W_(H,χ)(B) = Tr_(Sym² C²)[D(B_(x7→x0),χ)...D(B_(x0→x1),χ)]`,

where D is the spin-one representation. Use normalized product Haar on the twelve independent Spin(4) pair coordinates B to extract

`λ_(H,χ) = ∫ dB overline(W_(H,χ)(B)) P0(B).`                (2)

This is a test of the nodal function across its admissible arguments. The original conditional coefficient still uses the original moving Haar. The test has label 2 in χ on every cycle edge and label 0 elsewhere, including the other chirality. Its squared norm is 1, since the product of the eight independent Haar matrices is Haar and the irreducible character has norm 1 by Schur orthogonality.

The original P0 is invariant under arbitrary retained site gauges on the pairs. In gauge V1=I apply the same gauge at old and new copies of each site. This keeps V1=I, sends the pair to another inverse pair, preserves the contracted A8 and changes the moving variables by Haar translations. The inherited Berezin top is preserved by the spinor change of determinant 1. The projection to the above product label commutes with these gauges, because left and right translations preserve the coefficient spaces. It is independent of all other variables. Along the cycle, site gauges set seven χ matrices to identity, with the remaining matrix the ordered holonomy up to conjugacy. Its residual dependence is a class function in label 2. Schur's lemma makes that space one dimensional. Thus the whole specified harmonic component is λ_(H,χ) W_(H,χ). A nonzero λ would certify a nonzero P0 at some admissible node. Its value is not established here.

## Complete occupation selection for (2)

The eight selected labels already sum to 16, exhausting the total curvature count in (1). Hence every curvature occurrence contributing to (2) lies on H in χ. For each cycle edge the total curvature count is exactly 2 and the total coframe count is at least 2. Each vertex contributes one moving matrix occurrence on each incident pair, so m_x+m_y>=4 on each cycle edge. Summing the eight inequalities gives equality since each site is counted twice and Σ m_x=16. It follows that m_t+m_(t+1)=4 on every edge. Hence m_even=a and m_odd=4−a, with a in {0,1,2,3,4}. Each cycle edge has exactly two coframe occurrences, both in χ. Moreover each based anchor on that edge has h_(a,χ)=c_(a,χ), since the sum of their minima is 2 and both totals equal 2. The matching edges off the cycle have no curvature and can carry either coframe chirality. Individual moving-anchor and Grassmann restrictions still apply.

Let k_t be the number of curvatures centered at x_t in its forward cycle direction. The remaining m_t−k_t at x_t are in the backward cycle direction. This convention is geometric along the cycle, with each curvature still using its original based positive-direction anchor. The count on the pair e_t gives

`k_t + m_(t+1) − k_(t+1) = 2.`

Therefore k_even=k and k_odd=k+2−a. The complete range from nonnegative centered counts is

`max(0,a−2) <= k <= min(a,2).`                              (3)

The original endpoint saturation condition also holds for all these count assignments. The incoming curvature count at x_t is `k_(t−1) + m_(t+1) − k_(t+1) = 4−m_t`, by the two cycle-pair equations and the absence of matching-edge curvature. All three neighboring sites have multiplicity 4−m_t because Q3 is bipartite. Hence the accepted flow right side is `2m_t + 3(4−m_t) − 8 = 4−m_t`, as required. The five possible a values give 1,2,3,2,1 assignments for a total of nine. They are site-direction occupancy assignments and may have zero signed contractions.

An exact expression for (2) is the sum over these nine assignments of the original `16! / ∏_(x,i) c_(x,i)!` times the integral in (2) with `P0(B)` replaced by `∫dU1 I64 ∏_(x,i) (A_(x,i)^χ)^c_(x,i)`. Here `A_(x,i)^χ` projects only the curvature trace onto its χ block after the accepted internally antisymmetric contraction, with both world orders and the original coframes unchanged. The other coframe restrictions above follow from the projection and can be used as selection rules when expanding. This computes an isolated harmonic of the full coefficient once its nine signed contractions are evaluated or otherwise controlled. It neither drops mixed terms within that harmonic nor assumes their signs. All nine could cancel or vanish, and a zero result would only settle this label.

The construction relies on the accepted original nodal boundary reduction, fixed-direction sector, full center parity, and closed-word gauge covariance in the full-cut transport record. Full P0, positive R_b and the physical reconstruction remain open. No scientific evaluator, Lean, slot, build, or numerical resource was used. Separate actual math and original-source reviews are required.
