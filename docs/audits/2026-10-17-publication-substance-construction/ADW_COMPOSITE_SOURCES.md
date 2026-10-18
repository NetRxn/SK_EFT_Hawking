# Finite ADW composite sources, singular-safe response and local Legendre construction

17 October 2026. I accept the assigned microscopic composite-source construction under the original Phase5d/ADW BUILD. **Independently reviewed manual finite-model construction.** See the [complete independent review](reviews/ADW_COMPOSITE_SOURCES.md); physical and native acceptance remain separate. This continues the accepted exact auxiliary identity, not the assumed scalar/NJL potential. It supplies an explicit finite coefficient/observable algorithm and local response/Legendre conditions; it does not compute a lattice phase, claim a positive sampling measure or settle physical gravity/magnitude.

## 1. Exact carrying regulator, action and source convention

Use exactly the regulator/normalization in `ADW_EXACT_AUXILIARY_IDENTITY.md` (SHA256 e74fc4b792d59d19f88917f8f0365a2336583ca0abc5cac1403917b98ebd3cd8), independently accepted by review75727aa9418997ab8dac30f5c66a789f5fad5c04ffb2d64a8344bbaf7e007103. This is the declared finite hypercubic torus with V sites, spacing a>0, four independent psi and four independent barred generators per site, compact block-diagonal Spin(4) links and fixed consistent boundary signs. Let n=4V be the fermion-matrix size and d=16V the number of composite components. Index alpha=(x,mu,A), and retain the actual symmetric coframe T_alpha=a ehat_alpha:

    T_(x,mu,A)=1/4[barpsi_x gamma_A Omega_(x,mu)^dagger psi_(x+mu)
      −barpsi_(x+mu) Omega_(x,mu) gamma_A psi_x
      −barpsi_x gamma_A Omega_(x−mu,mu) psi_(x−mu)
      +barpsi_(x−mu) Omega_(x−mu,mu)^dagger gamma_A psi_x].       (1)

Boundary signs here are the declared real periodic/antiperiodic ±1 factors, paired consistently on reversed hoppings; no unpaired complex twist is inserted. All four block increments are ADDED, including coincident neighbors on small tori. These are even degree2 Grassmann composites, so they commute; any product of more than n of them vanishes. This is a safe global degree bound, not a hard physical occupation cutoff.

For commuting X let S=sum_x S_x, with precisely

    S_x(X,Omega)=g1 epsilon_ABCD X_(x,1,A)X_(x,2,B)X_(x,3,C)X_(x,4,D)
      +(g2/4) sum_(k,l,mu,nu,C,D) epsilon^(k l mu nu)
        Tr[Omega_(x,k l) gamma_C gamma_D gamma5] X_(x,mu,C)X_(x,nu,D).

The oriented plaquette and gamma/link orders are those of the carrying note. The dimensionless finite couplings, cancelled a^4/a^2 factors and source exp(+S) convention are unchanged. Additional source-action interactions indicated by the original paper's ellipsis are not silently included. Define A_alpha(Omega) by T_alpha=barpsi A_alpha psi. Each A_alpha contains exactly the four1/4-signed blocks in(1), with boundary coefficients incorporated. Then M(h,Omega)=sum_alpha h_alpha A_alpha is exactly the accepted n by n matrix, with no added mass/kinetic term.

Introduce independent commuting, dimensionless sources J_alpha coupled to the ORIGINAL composites, not to auxiliary h:

    Z(J)=integral dHaar(Omega) dBerezin exp[S(T,Omega)+sum_alpha J_alpha T_alpha]
        =integral dHaar dmu_sigma(h) W(h,Omega) det M(h+J,Omega),
    W=product_x W_x,  sigma²>0.                              (2)

The second equality is the accepted algebra identity multiplied by exp(J.T) BEFORE Berezin integration. Its weight is unchanged: W_x is the explicitly truncated Hermite polynomial of the carrying note, not W_x(h+J), a new Gaussian ansatz or a positive scalar potential. The shift occurs in M only. J may be complex: the determinant is a polynomial and no complex-contour shift is used. Orientation remains integral exp(barpsi M psi)=det M.

In this lattice convention t_alpha=<T_alpha>, so <ehat_alpha>=t_alpha/a when defined. If a future continuum-source convention is sum_x a^4 j_alpha ehat_alpha, then J_alpha=a^3 j_alpha. Without the volume factor a different relation results. Neither a physical source calibration nor a continuum field normalization is inferred from the dimensionless choice in(2). W, logZ and the Legendre function below are dimensionless.

## 2. Finite generating polynomial and nonzero domain

For each fixed h and Omega, det M(h+J) has total degree n in (h,J) because M is linear and homogeneous. Therefore

    Z(J)=sum_(|k|<=n) c_k J^k,                              (3)

with possibly vanishing highest coefficients. In particular there are at most binomial(d+n,n) source monomials, prior to symmetries. This is a finite bound, not a feasible-cost assertion. There is no source-power approximation or discarded tail.

For the specified action write S=g1 S4+g2 S2. Grassmann saturation of n barred/unbarred pairs implies a necessary selection rule for a coefficient with source degree |k|:

    4q+2p+|k|=n,     q,p>=0,
    c_k=sum_(4q+2p+|k|=n) g1^q g2^p c_(k,p,q).              (4)

Taylor factorials are included by expanding the exponent; additional cancellations may set any allowed coefficient to zero. In particular |k| must be even, q<=V and p<=2V. No assertion that a particular allowed coefficient is nonzero follows.

Equivalently change every unbarred psi to −psi. There are n=4V of them, so the Berezin Jacobian is+1; T changes sign, S2 and S4 do not. Thus Z(−J)=Z(J). If Z(0)!=0, every finite-volume zero-source one-point function vanishes. This does not rule out a nonzero two-point/metric correlator or a symmetry-breaking infinite-volume/source-limit construction; it prevents inferring an ordered finite-volume tetrad merely from the auxiliary representation. Gauge fixing, covariance and a physical ordered background remain additional work.

All coefficients in(3) are actual finite integrals. The degree of product_x W_x in h is at most Vn, and the determinant adds at most n. Coefficients in links are polynomials in finitely many compact matrix entries and their conjugates, hence bounded. Every absolute Gaussian polynomial moment is finite. Source differentiation and coefficient extraction commute with these integrals; locally uniform convergence is immediate for a finite polynomial. Positivity, reality or Z!=0 are NOT implied.

If a computed source point J0 has Z0=Z(J0)!=0, the translated finite coefficients c_k^(0) give an explicit zero-free sufficient neighborhood: choose r>0 such that

    sum_(1<=|k|<=n) |c_k^(0)| r^|k| < |Z0|.

For ||delta J||_infinity<=r, the triangle inequality then bounds |Z(J0+delta J)| below by the positive difference. This is an algebraic certificate once coefficients and their errors are actually known, not a claimed numerical radius here.

## 3. Singular-safe one/two insertions

Write the unnormalized insertions N_alpha=partial_alpha Z and N_alpha beta=partial_alpha partial_beta Z. Differentiating the ORIGINAL integral proves they insert T_alpha and T_alpha T_beta, with the same plus-source convention. In(2), no derivative hits W. For any n by n M and increment A define

    D det(M)[A]=sum_(i,j) Cof_(ij)(M) A_(ij),
    Cof_(ij)=(-1)^(i+j) det M_(delete i,delete j).             (5)

Indices are1-based and an empty determinant is1. Consequently N_alpha is the integral in(2) with det M replaced by Ddet(M)[A_alpha]. This is valid at singular M, including where detM=0; neither M^-1 nor division by detM is needed.

For two increments A,B the complete mixed derivative is

    D²det(M)[A,B]=sum_(i<k,j<l) (-1)^(i+k+j+l)
      det M_(delete {i,k},delete {j,l})
      ×[ A_ij B_kl+B_ij A_kl−A_il B_kj−B_il A_kj ].          (6)

N_alpha beta is the corresponding integral with A=A_alpha, B=A_beta. The formula includes coincident source labels; for A=B the bracket is twice the2 by2 minor. Thus it does not omit the repeated-derivative factorial. It follows by selecting exactly two replaced rows/columns in the determinant's permutation expansion; the signed complementary-minor Laplace expansion supplies the displayed sign. For n<2 the second derivative vanishes. For the actual n=4V the ordinary formula applies directly.

More generally the k-th derivative in k independent directions is the sum over sorted row/column subsets I,J of size k of
(-1)^(sum I+sum J) det M_(I^c,J^c) times the coefficient of t1...tk in det[(sum_s t_s A_s)_(I,J)]. This finite mixed-minor rule yields ALL insertions through k=n; higher ones vanish. Equal directions can be substituted afterward. It is a determinant-coefficient identity, not an inverse-based limiting prescription.

Two strict singular controls are immediate. For M=diag(0,m), A=E11, detM=0 but Ddet(M)[A]=m. For M=0 of size2, A=E11, B=E22, the first derivatives vanish while D²det(M)[A,B]=1. For A=B=I2 at M=0 the result is2, consistent with det(tI2)=t². These are manual determinant controls, not executions of the Diakonov model. They expose why setting all insertions to zero at detM=0 or using an undefined inverse is wrong. More generally rankM<n−k forces every complementary (n−k)-minor to vanish, but rank deficiency alone does not kill higher insertions.

## 4. Explicit finite coefficient/observable algorithm

The following algorithm computes the coefficients c_k and unnormalized observables of the DECLARED finite lattice, in exact arithmetic in principle. It is not an implemented solver or simulation claim.

1. Fix V, boundary coefficients, gamma basis, link ordering, finite couplings and sigma²>0. Build all sparse A_alpha by ADDING the four blocks of(1). Construct the finite W_x via the accepted total-degree<=n expansion of exp(S_x)exp(−sigma² X²/2) and the exact probabilists' Hermite formula. Keep all weights and complex signs.
2. Expand the determinant by permutations or polynomial-preserving elimination into
   det M(h+J)=sum_(beta,k) d_(beta,k)(Omega) h^beta J^k,
   |beta|+|k|=n. Expand the finite product W=sum_eta w_eta(Omega)h^eta. Polynomial-preserving means no uncancelled division by a variable pivot; the permutation algorithm is a complete universally valid fallback at singular matrices.
3. Contract every h monomial using the normalized independent Gaussian moments

       G_nu=0 if any nu_alpha is odd;
       G_nu=sigma^|nu| product_alpha (nu_alpha−1)!! otherwise,
       (−1)!!=1.

   Thus c_k=integral dHaar sum_(beta,eta) d_(beta,k) w_eta G_(beta+eta). No determinant ratios appear and no Gaussian quadrature tail remains. Maximum h degree in this direct bound is n(V+1).
4. Each SU(2) link factor may be represented exactly by U=q0 I+i sum_(a=1)^3 q_a tau_a, sum q_a²=1, with independent unit-quaternion Haar variables for left/right factors. U^dagger has the opposite i sign; plaquettes preserve ordered matrix multiplication. For a normalized S³ Haar monomial, any odd exponent integrates to zero. For even exponents2k0,...,2k3, K=sum k_a,

       integral product_a q_a^(2k_a)
         =product_a (1/2)_(k_a)/(2)_K
         =product_a (2k_a−1)!! / product_(j=0)^(K−1)(4+2j).    (7)

   Empty products are1. This follows by separating radius and angle in four independent standard Gaussians: numerator is the product of even Gaussian moments, and E R^(2K)=4·6·...·(4+2K−2). Independent link factors multiply. Consequently every remaining link integral is a finite exact moment contraction. With an explicit Pauli/Euclidean gamma basis, matrix entries are algebraic constants; this yields explicit coefficients in the supplied couplings, with no unspecified group-integration oracle. Link expressions containing conjugates/inverses are polynomial in these same real quaternion coordinates. This is Spin(4), not a substituted spinor representation.
5. Store (3) and its coefficients; differentiate the finite polynomial or use(5)/(6). At an actual J with Z!=0 form normalized results only after exact/controlled evaluation of Z. Cross-check against direct expansion of exp(g1S4+g2S2+J.T) and top Grassmann coefficient extraction, using the selection rule(4). This direct original-action algorithm does not use a Gaussian approximation and is an independent finite algebraic specification.

For example the Haar contraction gives integral q_a²=1/4 and integral q_a^4=1/8, while mixed q_a²q_b²=1/24 for a!=b, directly from(7). These are symbolic moment consequences, not a numerical model run. There is no practical volume complexity bound, new code, sampled dataset or native certificate. The exact sigma-independence follows from the carrying identity; any implemented coefficient dependence on sigma would diagnose a missing term, normalization or truncation error. Truncation at total T-degree n is exact by Grassmann saturation and must not be replaced by an unproved cheaper order.

## 5. Normalized connected response and auxiliary-field distinction

ONLY at Z(J)!=0 define

    t_alpha(J)=N_alpha/Z,
    C_alpha beta(J)=N_alpha beta/Z−N_alpha N_beta/Z².          (8)

On any small zero-free complex neighborhood choose a branch w(J)=log Z(J). Then t=partial w and C=partial²w; partial_beta t_alpha=C_alpha beta. All composites are even so there is no additional exchange sign. C is complex symmetric under index exchange, not automatically a Hermitian/positive covariance. Derivatives are with respect to independent J components, not J conjugates. At Z=0 the unnormalized polynomial/insertion formulas survive but(8) and logZ are undefined. Replacing Z by |Z| changes the construction.

For an auxiliary observable define <f>_aux=integral dHaar dmu W f detM(h+J)/Z. This is a signed/complex normalized functional, not necessarily a probability expectation. Gaussian integration by parts, with partial_alpha acting on h, gives

    N_alpha=integral dHaar dmu [h_alpha W/sigma²−partial_alpha W] detM(h+J),
    t_alpha=<h_alpha>_aux/sigma²
          −(integral dHaar dmu (partial_alpha W)detM)/Z.       (9)

No ratio partial W/W is required, including at zeros of W. The determinant's h and J derivatives agree because M depends linearly on h+J. The Gaussian boundary terms vanish coefficientwise. Twice integrating by parts gives the undivided two-insertion weight

    [(h_alpha h_beta/sigma^4−delta_alpha beta/sigma²)W
      −h_alpha partial_beta W/sigma²−h_beta partial_alpha W/sigma²
      +partial_alpha partial_beta W] detM.                  (10)

Integrating(10) equals N_alpha beta, including alpha=beta. Thus even connected <h h>/sigma^4 is not automatically the connected physical composite response: the delta term and derivative-of-weight terms remain. Sigma is a representation parameter; dropping these terms can manufacture sigma-dependent “physics.”

## 6. Local Legendre construction, not a convex physical action by fiat

Let J0 be a point with Z0!=0, t0=partial w(J0), and let H0=C(J0) on the stated independent source coordinates. If detH0!=0, the holomorphic inverse-function theorem gives a local inverse J(t) near t0. Define the BILINEAR complex Legendre function

    Gamma(t)=sum_alpha J_alpha(t)t_alpha−w(J(t)),
    partial_t Gamma=J(t),   partial²_t Gamma=C(J(t))^−1.      (11)

There is no complex conjugation in this analytic pairing. A different log branch changes Gamma only by an additive constant. A nonzero-source point yields derivative J0, not a falsely asserted zero-source saddle. If the Hessian is degenerate, this theorem does not supply an inverse. A specifically identified independent subspace/quotient or gauge/source constraint can be considered only with its own nondegenerate restricted Jacobian; deleting arbitrary zero modes is not a proof.

The coefficients from §4 provide constructive local series: translate w about J0 by the convergent log(1+(Z−Z0)/Z0) series in a zero-free small neighborhood; solve delta t=H0 delta J+terms of degree>=2 recursively, using H0^−1 at each homogeneous order, then substitute into(11). Each requested finite order is determined by the earlier coefficients. Convergence near t0 follows from the inverse-function theorem, not a global series/convergence claim. Gamma usually is NOT a finite polynomial even though Z is.

For a real convex thermodynamic effective action, much more is needed: a specified real domain and real logZ, convexity/positive susceptibility, correct extensive/source normalization, gauge/constraint treatment and thermodynamic/state/continuum limits. A positive measure over real composite observables would imply a positive semidefinite covariance but has NOT been proved for this Grassmann/signed-weight representation. Even the conditional nonnegative detM for real fields, Euclidean Hermitian gamma matrices and paired boundaries does not make W nonnegative. No Legendre–Fenchel/global supremum, reflection positivity, Lorentzian spectrum, stable physical scalar mode or spin2 pole follows from(11).

## 7. Exactly soluble controls, explicitly not the Diakonov lattice

Consider TWO independent Grassmann pairs, t1=barpsi1 psi1, t2=barpsi2 psi2, with Berezin orientation integral t1t2=1, T=t1+t2 and T³=0. Adopt the declared toy exponent gT²+JT. Its exact integral is

    Z_toy(J)=2g+J²,
    N=2J, N2=2,
    t=2J/(2g+J²),
    C=2(2g−J²)/(2g+J²)².                                 (12)

The exponent's plus sign and T²=2t1t2 fix every coefficient. This is a finite declared bilinear toy, not actual Spin(4) links, the four-dimensional source action or a computed lattice phase.

Its exact one-component auxiliary transform has M=(h+J)I2 and

    W(h)=1+(g−sigma²/2) sigma^−2 He2(h/sigma),
    integral dmu W detM=2g+J².                              (13)

Indeed E Wh²=2g, E Wh=0, E W=1. Direct polynomial moments give
integral dmu W h detM=4gJ and
integral dmu W' detM=(4g/sigma²−2)J. Substituting in(9) restores2J/Z; omitting W' instead reports4gJ/(sigma²Z). At g=0,J!=0 the naive auxiliary mean is identically zero while the actual composite mean is2/J. This is a strict analytic countercontrol to <h>/sigma², despite real nonnegative detM=(h+J)². No division by W is involved.

At g=0,J=0, Z=0 while N2=2 remains finite: normalized response/logZ fail, and the unnormalized construction remains valid. More generally for g<0, J²=−2g gives zeros with nonzero N. At g>0, Z is positive for EVERY real J, yet C vanishes at J=±sqrt(2g) and is negative outside that interval. Thus a positive scalar partition polynomial on real sources does not establish log-convexity or global invertibility; the Legendre Hessian condition is substantive. At J=0 with g>0, H0=1/g is nonsingular and local Gamma''(0)=g, consistent with(11). Source t(J) is not globally one-to-one. These are exact hand derivations, not executed examples.

For the actual declared lattice, g1=g2=0,J=0 also yields Z=integral dBerezin1=0 for V>0. This admissible finite-coupling case proves that nonzero normalization cannot be assumed universally. Other actual couplings/source points require their own coefficient evaluation; no general nonzero or positive theorem is inferred from the toy.

## 8. What has been constructed and what remains

This supplies the actual composite-source polynomial for the accepted regulated multifermion action, singular-safe unnormalized one/two/all insertions, exact finite Gaussian/Haar coefficient contraction, a normalized response domain and explicit local analytic Legendre/Hessian conditions. It advances the original source-response step beyond an auxiliary identity or caveat list. No original source is silently replaced by a fitted scalar potential.

Independent review must check normalization, cofactor/mixed-minor signs and repeated derivatives, the Haar moment denominator, saturation/parity selection, auxiliary correction terms and the toy countercases. A future allocated implementation must retain singular/zero-Z/degenerate-Hessian refusals, exact coefficient/error conditioning, original-source comparison and sigma cancellation; this note does not execute one or select its tolerances.

Still BUILD: physically normalized sources and their gauge/state interpretation, tractable actual-volume coefficients and errors, physical order/large-volume source limits, full tetrad Legendre action, scalar reduction and matching, Lorentzian constraints/dynamics and propagating gravitational modes, continuum control, independently derived vacuum magnitude, and admitted native/numerical qualification. Positive determinant under its exact assumptions is preserved; signed W is not discarded, and no automatic positive RHMC/Pfaffian claim appears. Original roadmap/owner/map/closure/main/human responsibilities are unchanged.

## CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES

The proposed construction is not the assumed scalar Gaussian HS/NJL model. Actual T sources shift the fermion matrix to M(h+J) with W unchanged; h sources would be different observables. Cofactors/minors remain valid when M is singular, while normalized correlations still require Z!=0 and local Legendre inversion requires a nondegenerate response. Even-in-T finite-volume symmetry forces a zero one-point function at zero source when normalized; it does not prove absence of a physical ordered infinite-volume phase. The toy demonstrates that nonnegative determinant or positive real Z alone does not justify <h>/sigma², convexity or a global physical effective action. No new primary-source claim, physical no-go or approved deferral follows.
