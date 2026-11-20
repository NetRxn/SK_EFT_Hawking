# Independent manual review: one-site invariant metric response

ACCEPT for the explicitly declared finite Euclidean one-site model. I independently checked equations (1)–(15), including every repeated-index contraction, possible interaction contribution, the full ten-source matrix, the joint twenty-six-source rank, and the local analytic domains. No mandatory mathematical correction was found. This accepts the finite algebraic construction, not a physical nondegenerate spacetime metric or a native result.

The reviewed CONSTRUCTION.md is 34b71b716bf7ad08b69626b59a96d5a5d10dea585939992e7a79b5ba1256e2c6. Its coefficient premise 4a67387106671b28092b62843869adc1b54b54886b6826b20e980d9734c5d9c3 was independently derived in my prior review dfa4f6a4ec82a39cf6278ed478ee629dc80785a462274919965e255068b56ff7 and subsequently accepted by the lead in bb9f49b94cb20a03f1b2d207115923533e233f966ea17d34c1a7873d5adb22bb. I am not the author of this new metric-response note. Its author's original pending-premise wording is a frozen chronological statement, superseded by those actual separate acceptances; it is not evidence that the present mathematical premise is unaccepted.

## Invariance, observable and source convention: equations (1)–(3)

I retain the actual original anticommutator coframe, plus-exponent action, normalized chiral Haar measures and four fermion pairs. Under simultaneous psi→U psi, barpsi→barpsi U-dagger and Omega→U Omega U-dagger, conjugating the gamma matrices in the bilinear sends T_mu,A to R_AB T_mu,B. Spin(4) gives an orientation-preserving orthogonal R; its barred/unbarred Jacobians are one. The quartic epsilon contraction is invariant. In the curvature term, the curvature and the gamma insertions transform consistently, gamma5 commutes with Spin(4), and the two coframes complete the invariant contraction. Rotating only links would not justify this conclusion.

Because the T's are Grassmann-even, their products commute. Thus G_mu,nu=sum_A T_mu,A T_nu,A is symmetric and invariant by R^T R=I. Its contraction is the internal Euclidean delta, and T=a ehat makes G=a² times the corresponding coframe composite. No positivity or ordinary real-valued Gram-matrix interpretation follows from the Grassmann observable. It is not a normalized Lorentzian metric. The ten independent H coordinates couple off-diagonal G's once. The equivalent symmetric full-index source has K_off=H_off/2, so missing a factor two here would alter the subsequent matrix.

## Saturation and all moment contractions: equations (4)–(6)

Each G consumes two barred/unbarred pairs; a product of three G's already exceeds four available pairs. The possible partition terms are the constant g1 S4 and g2² S2²/2, the linear g2 S2 L_H and L_H²/2. The g1 term vanishes by the accepted center argument. For diagonal G the mixed curvature term leaves odd counts in some S2 direction. For off-diagonal G only the matching unordered S2 pair survives the center test. Its complementary curvature links then have independent zero antisymmetric-vector mean. The diagonal curvature trace must first be removed by the original epsilon contraction, as the premise does. Hence the mixed term is zero without setting the curvature or G to zero. Nothing involving a larger-volume interaction is inferred.

Four-T insertions saturate the Berezin integral, so extra interaction factors cannot affect them. Differentiating the accepted quartic gives the two-row tensor

4b delta_CE delta_DF+2c(delta_CD delta_EF+delta_CF delta_ED),

and the same-row fourth powers 24alpha and mixed squares 8alpha. There is no further Taylor-factor division after differentiation. These are unnormalized top coefficients, not a Wick assumption or a positive-variable covariance.

For G_mu,mu² there are four identical-index terms and twelve ordered distinct-index terms: 4(24alpha)+12(8alpha)=192alpha=75/2. For distinct diagonal coordinates the tensor has C=E=A,D=F=B; summing gives 16(4b)+4(4c)=27. For an off-diagonal square set C=D=A,E=F=B, obtaining 4b delta_AB+2c(1+delta_AB); its sixteen-term sum is 4(4b)+20(2c)=9. These two different contractions must not be interchanged. A diagonal/off-diagonal product, or two different unordered off-diagonal pairs, leaves an odd direction count and is killed by center parity. This exhausts all hundred entries of the symmetric ten-coordinate moment matrix.

## Complete polynomial and local response: equations (7)–(12)

The resulting diagonal-coordinate block has diagonal 75/2 and off-diagonal 27, hence (21/2)I+27*11^T. The other block is 9I_6, with no cross block. Expanding H^T M H/2 gives precisely 75/4 times each diagonal square, 27 times each unordered product of different diagonal coordinates, and 9/2 times each off-diagonal square. Thus Z_G=D+Q has no omitted linear or interaction-dependent H term.

The equal-diagonal vector has eigenvalue 21/2+4*27=237/2; its three-dimensional zero-sum complement has 21/2; the six off-diagonals have 9. These are source-coordinate eigenvalues. In a Frobenius-orthonormal symmetric-matrix basis the off-diagonal observable is sqrt(2)G_off and its variance is 18. Neither basis supplies physical polarizations or masses. M is positive definite even though individual cross terms of Q may be negative.

Differentiation gives q=MH/Z and C=M/Z−(MH)(MH)^T/Z². At H=0,g2≠0, Z=96g2², q=0 and C=M/(96g2²), with eigenvalues 79/(64g2²), three copies of 7/(64g2²), and six copies of 3/(32g2²). At real g2=1 this is a full ten-dimensional positive definite response at zero source. Its mean metric is nevertheless the zero matrix, hence physically degenerate. An invertible source-to-observable derivative does not reverse that fact.

On a local zero-free log branch, invertibility of C invokes the holomorphic inverse-function theorem. Differentiating H(q).q−log Z(H(q)) cancels the q.dH terms and gives dGamma/dq=H; the origin is stationary and Gamma''(0)=D M^-1. This is a local composite function, not an established physical scalar potential, tetrad vacuum or positive-measure effective action. No global inverse is asserted.

## Joint generating function and complete rank: equation (13)

Expanding a single H insertion against exp(J.T) is exactly sum H_mu,nu sum_A partial_JmuA partial_JnuA F(J). The derivatives already retain the correct J²/2 factor from the exponential. Double H insertion contributes H^T M H/2. Together with D+F these exhaust all pair counts; the putative g2 H and g2 J² terms vanish by the actual prior arguments, not an omission of the action. There is no degree-JH term. At zero sources the full joint Hessian therefore has a zero sixteen-dimensional T block, zero mixed block and M/D in the ten-dimensional G block. Its rank is exactly ten when g2≠0; the invariant observable does not repair the full tetrad response there.

## Determinant, inertia, zeros and cumulants: equations (14)–(15)

The determinant lemma on C=M/Z−vv^T/Z² uses v^T M^-1 v=H^T M H=2Q. It gives det C=(det M)/Z^10 times (1−2Q/Z)=(det M)(D−Q)/(D+Q)^11. The exponent eleven is correct. With det M=(237/2)(21/2)^3*9^6 nonzero, normalization requires D+Q≠0 and response invertibility additionally requires D−Q≠0.

For real g2≠0, D>0 and Q≥0. Congruence by M^1/2 reduces the sign question to I−ww^T/Z, with w²=2Q. Nine directions are positive and the remaining sign is D−Q; at Q=D rank is nine, and beyond it inertia is (9,1). These are congruence/inertia conclusions, not generic coordinate eigenvalues. At real g2=0,H≠0, Q>0 gives invertibility with inertia (9,1), while H=0 is unnormalizable. Thus positivity of Z does not imply log-convexity or a positive sampling measure.

For complex sources all ten |H_i|≤r imply |Q|≤[4(75/4)+6*27+6(9/2)]r²=264r². At g2=1,r=1/2 this is 66<96, so both D+Q and D−Q stay nonzero throughout the closed polydisc. This proves the stated finite neighborhood properties, not global injectivity. Scaling a real nonzero direction by complex z makes Q scale as z²; the two choices z²=−D/Q and +D/Q produce distinct zero-normalization and singular-response loci. Complex bilinear symmetry is not Hermitian positivity.

Saturation kills every unnormalized moment of three or more G insertions. It does not kill all higher normalized cumulants. For example along a direction v at the origin, log Z(tv)=log D+t²(v^T M v)/(2D)−t^4(v^T M v)²/(8D²)+..., so its fourth derivative is −3(v^T M v)²/D², generically nonzero. Odd cumulants at the origin vanish by the even source polynomial; the note's 'need not vanish' does not assert otherwise.

## Scope and evidence

The original first continuity check was 0/fresh. Selected inputs, full separate check channels and base64, static pin observations, and original terminal check are recorded in the companion JSON files. Authority r52 and the unchanged prior source/algebra premises are reused transparently; this was not another primary-literature, historical or physical-model audit. Only manual mathematics and stdlib file/hash/JSON/preservation operations were used. No project import, coefficient/model evaluator, numerical/symbolic software, tests, Verify, Lean/native, build/compiler, network, Git mutation, holding/source/notebook change occurred.

The exact finite invariant response is a substantive new microscopic construction. Physical source/state and normalization, nondegenerate ordered background, larger-volume errors and thermodynamic limits, full tetrad stationarity, scalar reduction, propagating modes/spin2, Lorentzian/continuum control, vacuum magnitude, sampling/native qualification remain BUILD. L1's scalar channel, projector, adopted window, coupling and transport/frequency matching are separate. No lifecycle, closure, protected integration, main or publication/human acceptance is supplied.

## CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES

No mandatory mathematical contradiction was found under the declared finite one-site conventions. A nondegenerate ten-observable response at zero source coexists with a zero, degenerate mean metric and a rank-ten joint twenty-six-observable response. Neither the physical metric nor its dynamical modes are established by this result. The author's frozen pending-premise statement records its authorship time; the newly supplied exact coefficient acceptance resolves that dependency without rewriting the original note.
