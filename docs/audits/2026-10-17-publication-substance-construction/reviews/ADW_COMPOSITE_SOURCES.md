# Independent ADW composite-source construction review

**Verdict: SCOPED_EXACT_FINITE_COMPOSITE_SOURCE_CONSTRUCTION_ACCEPT. No mandatory mathematical repair found in the complete eight-section construction, equations (1)–(13), coefficient algorithm or stated countercontrols.** I accept the assigned independent verification responsibility. This banks the finite regulated source/response construction and its conditional local Legendre theorem. It does not establish an actual nonzero lattice normalization point, nondegenerate lattice response, phase, scalar reduction, physical vacuum magnitude, numerical implementation or native proof.

Reviewed complete CONSTRUCTION.md SHA256 `6be0e1c5d1423a7bcd9015351567933ed58ff5aed74319f02947e31443b3d738`, author REPORT/evidence/process and both original check captures. I personally read the complete accepted auxiliary note `e74fc4b792d59d19f88917f8f0365a2336583ca0abc5cac1403917b98ebd3cd8` and its independent review `75727aa9418997ab8dac30f5c66a789f5fad5c04ffb2d64a8344bbaf7e007103`. Their regulated-action identity and bounded primary-source correspondence are accepted premises here; I did not newly inspect the primary PDF body or certify its acquisition/holding. The mathematical verification below is independent manual reasoning, not the author's document-completeness checks and not model/software execution.

## Actual source and regulator: section 1

The four blocks of (1) agree with the accepted symmetric coframe: forward gamma–link-dagger, reverse minus link–gamma, backward minus gamma–link, and its reverse plus link-dagger–gamma, each with coefficient 1/4. The actual Dirac representation is block-diagonal Spin(4), with four barred and four unbarred independent generators per site. Hence the matrix size is n=4V and there are d=4×4×V=16V independent source coordinates. Contributions reaching the same matrix block must be added, as the note explicitly requires, including coincident neighbors. Paired real boundary signs preserve the carrying convention; no arbitrary twist is inserted.

The cosmological term has degree four in T and the Einstein–Hilbert–Cartan term degree two, with the same epsilon/trace order, g1/g2 normalization, 1/4 curvature coefficient and positive exponent as the accepted note. Additional source-paper interactions represented by an ellipsis are outside this specified action. No bare kinetic term, Majorana identification, scalar ansatz or fitted Gaussian weight has been smuggled into M.

Multiplying the accepted Grassmann identity by exp(J·T) before fermion integration changes the bilinear to (h+J)·T. Therefore (2) is exactly integral W(h,Omega) det M(h+J,Omega): W is unchanged. This uses no shift of a real Gaussian contour and remains valid for complex J by polynomial identity. A source on h would instead define a different observable. The Berezin orientation is the accepted integral exp(barpsi M psi)=det M; n=4V does not introduce a new odd reordering sign.

The units are internally consistent: T=a ehat and t=<T> give <ehat>=t/a. Under the expressly conditional continuum source sum a^4 j ehat, the dimensionless source is J=a^3 j. This is bookkeeping for that convention, not physical source calibration or an independently matched continuum normalization.

## Saturation, evenness, convergence and normalization: section 2

Every T is an even bilinear, so the T's commute and a product with degree exceeding n vanishes. Expanding the original exponential, q quartic vertices, p quadratic vertices and |k| source insertions can contribute to the top Berezin monomial only when 4q+2p+|k|=n. This proves the necessary selection rule and coupling degrees in (4), including |k| even, q<=V and p<=2V. Factorials remain those of the exponential expansion; this rule is not a sufficiency/nonzero theorem.

Independently, changing all unbarred generators to their negatives changes T to -T, leaves S2/S4 invariant and has Berezin Jacobian (-1)^n=+1. Thus Z(-J)=Z(J). Where Z(0) is nonzero, its first source derivatives vanish and the normalized finite-volume one-point function is zero. This is not a claim that a gauge-fixed state, metric correlator or ordered thermodynamic/source-limit phase is impossible.

M is homogeneous linear in h+J, so its determinant has homogeneous degree n, unless it vanishes identically. Its integrated source polynomial has degree at most n; the count binomial(d+n,n) is an upper bound, not evidence of attainable coefficients or feasible computational cost. The product of V weights has h-degree at most Vn, giving the safe total bound n(V+1) after multiplication by the determinant. Compact-link polynomial coefficients are bounded, and every absolute Gaussian polynomial moment exists. This justifies coefficientwise interchange and source differentiation without an uncontrolled limit.

The translated-coefficient inequality in section 2 is a valid sufficient zero-free polydisc certificate: on the stated closed infinity-norm ball the polynomial's change is bounded by the displayed positive-degree coefficient sum, strictly smaller than |Z0|. No actual J0, radius or coefficient error certificate has been evaluated here. The admissible actual-lattice case g1=g2=J=0 has integrand 1 before Berezin integration and therefore Z=0 for V>0. Universal nonzero normalization is genuinely false, rather than merely unproved.

## Singular-safe determinant insertions: section 3

For any increment A, differentiate the determinant's permutation expansion once. Selecting entry (i,j) leaves its signed complementary minor, giving (5) with Cof_ij A_ij, with no transposition or inverse ambiguity. The integral of this derivative is the insertion of the original T_alpha, since the source was introduced before fermion integration. W is not differentiated in this calculation.

More generally, the polynomial expansion of det(M+D) is the sum over equally sized sorted row/column sets I,J of (-1)^(sum I+sum J) det M_(I^c,J^c) det D_(I,J). For two sets of size two and D=tA+sB, the coefficient of ts is exactly A_ij B_kl+B_ij A_kl-A_il B_kj-B_il A_kj. This independently proves (6), its complementary-minor sign and both crossed minus signs. For A=B it gives twice the 2×2 minor, so the repeated-source factorial is retained.

For k directions, taking the coefficient of t1…tk in the selected k×k determinant is exactly the mixed derivative, without an extra k! for distinct parameters. Equal directions are substituted afterward and correctly generate their multiplicities. Higher derivatives beyond n vanish. Every complementary minor has size n-k; rank M<n-k kills these minors, while a smaller rank defect does not by itself kill all k-insertions.

All three stated singular controls are correct by hand: det(diag(0,m)+tE11)=tm; det(tE11+sE22)=ts; det(tI2)=t². They distinguish zero determinant, zero first insertions and nonzero higher insertions. They are generic determinant controls, not claimed evaluations of the actual lattice matrix. No division by detM or singular inverse enters the accepted construction.

## A complete finite coefficient specification: section 4

This is more than an instruction to run an unspecified group integral. The accepted weight construction supplies finite monomial coefficients; the determinant permutation expansion supplies d_(beta,k), with |beta|+|k|=n. Multiplying finite polynomials and contracting each h-monomial by the normalized independent Gaussian moments gives the stated coefficient sum. An odd exponent yields zero; for even exponents E h^nu=sigma^|nu| product(nu_alpha-1)!!. The normal probability measure and (-1)!!=1 give the correct constant normalization. No factorial from polynomial coefficients is silently removed.

For each independent SU(2) factor, U=q0 I+i q·tau uses a normalized unit quaternion. The fundamental representation and its dagger are polynomial in the same real coordinates, as are ordered products and conjugates. With four independent standard Gaussians z=Rq, E product z_a^(2k_a)=product(2k_a-1)!! and E R^(2K)=4·6·…·(4+2K-2). Radius and uniform angle separate. Dividing proves (7), equivalently product(1/2)_(k_a)/(2)_K. Reflection symmetry kills odd coordinate exponents. It gives 1/4, 1/8 and 1/24 for the three displayed degree-two/four cases. There is no missing factor from Haar normalization, or replacement of Spin(4)'s two independent SU(2) factors by a different spinor representation.

Thus, after explicit basis/boundary/regulator choices, all remaining integrations reduce to specified finite moments. Variable-pivot elimination alone could introduce illegal divisions; the universally valid permutation fallback prevents that gap, including singular M. Direct top-Grassmann-coefficient extraction from exp(g1S4+g2S2+J·T) is a genuinely independent finite specification against which an implementation can be checked. Sigma independence follows from the accepted identity, not an unperformed empirical cancellation test. For unspecified arbitrary couplings, “exact arithmetic” is understood as exact symbolic coefficients in those supplied parameters, not finite computability of an oracle real input.

No actual-volume coefficient population, run time, numerical errors or practical volume scaling has been produced. The finite constructive specification is accepted; an operational implementation and its conditioning/error qualification remain substantive next work.

## Connected response and both auxiliary correction identities: section 5

At Z!=0, quotient differentiation gives (8), and a local log branch gives t=partial w and C=partial²w. Source derivatives are holomorphic in independent J coordinates. Even Grassmann insertions commute, so C is complex symmetric. It is not thereby Hermitian or positive semidefinite. A zero of detM at an integration point does not invalidate polynomial insertions; a zero of integrated Z does invalidate normalization and logZ. Replacing Z by |Z| would change the theory.

For the normalized Gaussian, the integration-by-parts adjoint of partial_i is D_i*=h_i/sigma²-partial_i. Since partial_h detM=partial_J detM, applying D_i* to W gives exactly the undivided weight in (9). Applying D_i*D_j* gives

    (h_i h_j/sigma^4-delta_ij/sigma²)W
    -h_i partial_j W/sigma²-h_j partial_i W/sigma²+partial_i partial_j W.

This verifies every term and sign in (10), including the coincident-index Kronecker term. Polynomial Gaussian boundary terms vanish. There is no need to divide by W at its zeros. Both derivative-of-weight terms and the delta correction matter, so neither a naive auxiliary mean nor its naive connected covariance is automatically the physical composite response.

## Exact scope of the local Legendre theorem: section 6

A nonzero Z0 supplies a zero-free complex neighborhood and local holomorphic log. If its Hessian C(J0) is nonsingular on the stated independent coordinates, the holomorphic inverse-function theorem supplies a local analytic inverse J(t). Differentiating J·t-w(J) cancels the dJ terms because t=partial_J w. Hence partial_t Gamma=J and its Hessian is C^-1, exactly (11). The pairing is bilinear; inserting conjugates would not be this holomorphic Legendre construction. Changing a local log branch changes only an additive constant. At nonzero J0 the derivative is J0, not an asserted zero-source stationarity condition.

The recursive power-series construction is valid: after translation, the linear term is H0 deltaJ; at each homogeneous order multiplication by H0^-1 determines the next inverse coefficient from earlier ones. The analytic inverse theorem supplies local convergence, not a global convergence or polynomial-Gamma result. A singular full Hessian provides no such inverse theorem; a separately identified restricted subspace would need its own nonsingular Jacobian. No physical gauge-mode deletion is licensed.

The construction has not established the existence of a lattice J0 with both conditions, or a real convex thermodynamic action. Physical normalization, gauge/state interpretation, positivity, limits and dynamics remain necessary. Conditional detM=det(K†K)>=0 for real h under the accepted Euclidean/chiral/paired-boundary assumptions is retained. It does not prove W>=0, a positive full sampling measure, reflection positivity or a spin-2/Lorentzian spectrum.

## Exact controls and original physical objective: sections 7–8

For two independent Grassmann pairs, T²=2t1t2 and T³=0. The top coefficient of exp(gT²+JT) is 2g+J². Its derivatives are 2J and 2, giving t and C in (12). The toy's auxiliary weight is 1+b He2(h/sigma), where b=g/sigma²-1/2. Gaussian moments give EW=1, EWh=0 and EWh²=sigma²(1+2b)=2g, so (13) integrates detM=(h+J)² to exactly 2g+J².

Parity gives E[Wh(h+J)²]=2J EWh²=4gJ. Also W'=2b h/sigma², so E[W'(h+J)²]=4bJ=(4g/sigma²-2)J. Their combination in (9) is 2J, independently confirming the correction and the strict g=0,J!=0 countercase: the naive auxiliary mean vanishes while the true mean is 2/J.

At g=J=0 the normalization fails although N2=2 remains. At g<0 the real roots J²=-2g have N!=0. At g>0, Z stays positive for every real J, but C vanishes at J²=2g and is negative beyond; at J=0, C=1/g and Gamma''=g. The real source-to-mean map is not globally injective. These exact controls demonstrate that the response and inverse conditions have real content; they are explicitly not actual Diakonov-volume computations or a physical no-order theorem.

The complete original BUILD remains: actual finite-volume coefficients and controlled errors; physically normalized source/state/gauge construction; thermodynamic/source limits and order; full tetrad effective action and microscopic scalar correspondence; constraints, fluctuations and propagating gravitational modes; physical coupling/cutoff and continuum/Lorentzian control; independently derived nonzero vacuum magnitude and uncertainty; sampling and ordinary native/numerical admission. Equal critical couplings, the accepted auxiliary identity and this new local finite construction do not substitute for those goals. No reduced target, infeasibility, approved deferral, scientific finding closure, G4/G5/G11, main or human publication acceptance follows.

## Evidence and continuity

The original first supported review check returned 0, fresh=true, changed=[]. The final ORIGINAL check is preserved separately and reconciled in evidence/process, with no packet refresh. A captured stdlib-only source/pin/JSON child returned 0: all 23 unique referenced file pins matched; their hashes, modes, sizes and nanosecond mtimes remained equal to the recorded review preservation snapshot. This count describes the actual deduplicated packet files, not an added scope or new corpus census. All available base64/raw author channel pairs matched. These static observations are preservation checks, not mathematical test results.

Current r51 book is 9d11c89f. The author's r50 book is exactly preserved in archive 2d275643; the explicit terminal-author reconciliation c3e4cd55 and r51-update 9b554108 record the deliberate later change. The author's original first0/final1-owned-only history and pre-seal paired-boundary clarification remain unchanged. No old packet was refreshed or its historical book falsely presented as current. Earlier native source-display commands expose tool metadata and may truncate displayed aggregates; separate full enclosing UTC/channels are not reconstructed. Complete original author files and the later captured static observations remain available and pinned.

Only the assigned five ignored review files and fresh scratch were written. No project/model import, numerical/symbolic oracle, coefficient evaluation, tests/Verify, Lean/native/slot/controller, graph/build/compiler/render, network/holding, source/notebook/other-writer, Git/index/ref or closure mutation was performed. Existing governance is reused at exact unchanged pins; this review does not create another tracker or modify closure ownership.

## CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES

No mandatory contradiction remains in this proposed finite construction. Source J couples the original T and shifts M alone; auxiliary h moments require the derivative-of-W corrections. Singular M permits nonzero insertions, while zero integrated Z blocks normalization and degenerate C blocks the stated inverse theorem. Exact finite Haar/Gaussian contraction is a constructive specification, not evaluated lattice coefficients or a positive physical action. Finite evenness, the toy and conditional determinant positivity neither discharge nor refute the original ordered-state, full-gravity and magnitude BUILD.
