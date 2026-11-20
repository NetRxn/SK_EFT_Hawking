# D10: general finite-N continuum fermionic constrained search

Author: publication_d2_proposal_review, accepting scientific authorship under the assigned B1 construction. Status: INDEPENDENTLY ACCEPTED MANUAL CONSTRUCTION; [full original nonauthor mathematical/source review](reviews/D10_MANY_ELECTRON_CONSTRAINED_SEARCH.md). The separate [finite-Coulomb HK construction](D10_COULOMB_HOHENBERG_KOHN.md) and [full original independent review](reviews/D10_COULOMB_HOHENBERG_KOHN.md) complete the manual finite-Coulomb HK/common-state/strictness result, including degeneracy. Native integration, appropriate binding/existence and full B1 remain OPEN BUILD; arbitrary-potential UCP is an optional broader-domain extension. No source application, numerical experiment, native proof or scientific closure is asserted.

This proves a general many-electron pure-state density construction and fiber-attainment theorem, with the Coulomb interaction retained. It does not replace the original full molecular/Hohenberg–Kohn/native objective with a one-electron charter. The separately independently reviewed N=1 note is context, not a premise; all arguments needed here are supplied below.

## 1. Actual carrier, coefficients and theorem

Fix integers N>=1 and q>=1, a spin set S={1,...,q}, alpha>0 and g>=0. All spatial measures are Lebesgue; spin uses counting measure. Let H=L2((R3 x S)^N; C), equivalently a direct sum of q^N copies of L2(R^(3N)). H1 uses weak spatial derivatives, with

    K[Psi] = sum_i ||grad_i Psi||2^2.

The subscript a means antisymmetry under simultaneous permutation of spatial and spin labels. Permutation operators are unitary and preserve H1; the finite alternating projection (1/N!) sum_pi sgn(pi) U_pi is bounded on both spaces. Thus H1_a is closed in H1 and dense in H_a (smooth approximation followed by that projection). Define

    S_N = {Psi in H1_a : ||Psi||2=1},
    rho_Psi(x) = N sum_(sigma_1,...,sigma_N) integral |Psi(x,sigma_1;x2,sigma_2;...;xN,sigma_N)|^2 dx2...dxN.       (1)

Antisymmetry implies that all one-particle spatial marginals agree, including after summing spins. Tonelli gives integral rho_Psi=N||Psi||2^2. Define

    T_W[Psi] = alpha K[Psi] + g sum_(i<j) integral |Psi|^2/|xi-xj|,
    D_N = {rho>=0 a.e. : integral rho=N, sqrt(rho) in H1(R3)}.             (2)

The sum over spin components is implicit in every configuration integral. Collision sets have measure zero; any value assigned to 1/r at r=0 does not change these forms. Functions/densities are equivalence classes a.e.

For finitely many fixed nuclei (R_b,Z_b), set v(x)=-sum_b Z_b/|x-R_b|. Real Z_b are allowed in the estimates using absolute values; physical attractive nuclei have Z_b>=0. The source's pair-count-once potential is this v plus g=1 electron repulsion in its encoded Coulomb units. Its kinetic operator has coefficient alpha=hbar^2/(2m), not an implicit hbar=1: `momentumCLM` contains -i hbar, and Physlib's kinetic coefficient is (2m)^(-1). Restoring electrical units requires restoring the source Coulomb coefficients as well. K has length^(-2), alpha has energy times length^2, g and Z_b have energy times length; rho has length^(-3). There is no nuclear–nuclear constant in the displayed source potential. An added fixed such constant would shift every energy equally, and is not inserted here.

**Theorem.** D_N is exactly the set of total densities of S_N, for every finite q>=1. All Coulomb forms above are finite on H1; the molecular quadratic form on H1_a is closed and bounded below. For every rho in D_N, the nonempty fiber has a finite attained infimum

    F_LL(rho)=min {T_W[Psi] : Psi in S_N, rho_Psi=rho}.                  (3)

The molecular state infimum equals inf_(rho in D_N) [F_LL(rho)+integral v rho], as a finite real number. Ground-state attainment and density-minimum attainment are equivalent, with the fiber minimizers described below. Neither attainment is asserted for every unconstrained molecular problem. This is the pure-state functional, with no asserted convexity or ensemble/Legendre replacement.

## 2. Sobolev marginal inequality, including zeros

We first prove the needed Hilbert-valued norm fact. If U in H1(R^d; E) for a separable Hilbert space E, then u=||U||_E belongs to H1 and

    ||u||2=||U||2,   integral |grad u|^2 <= sum_j ||partial_j U||2^2.    (4)

For finite-dimensional smooth U use u_epsilon=(||U||^2+epsilon^2)^(1/2)-epsilon. The subtraction makes u_epsilon square-integrable on infinite space. Its derivative is Re<U,partial_j U>/(||U||^2+epsilon^2)^(1/2), bounded in modulus by ||partial_j U||. Finite-rank projections, spatial cutoffs and convolution approximate a Hilbert-valued H1 function in H1 (a countable orthonormal expansion and its derivative tails justify the projections). This derivative bound passes to the approximation limit: the norms converge strongly in L2 by the norm's Lipschitz property, derivatives have weakly convergent subsequences, and testing against compact smooth functions identifies the weak derivatives. Finally u_epsilon->||U|| in L2 by domination 0<=u_epsilon<=||U||; weak lower semicontinuity gives (4). No division by u or phase choice on its zero set is used.

Apply (4) to the first spatial coordinate of Psi, with E=L2 of all remaining spatial variables and all q^N spin labels. Fubini for Psi and its weak derivatives supplies this Hilbert-valued H1 function. Since sqrt(rho_Psi)=sqrt(N)||U|| and permutation symmetry gives N||grad_1 Psi||2^2=K[Psi],

    I(rho_Psi):=integral |grad sqrt(rho_Psi)|^2 <= K[Psi].              (5)

Together with (1), this proves rho_Psi in D_N. A separate useful continuity estimate follows by integrating | |Psi|^2-|Phi|^2 |<=|Psi-Phi|(|Psi|+|Phi|) and applying Cauchy–Schwarz:

    ||rho_Psi-rho_Phi||1 <= N (||Psi||2+||Phi||2)||Psi-Phi||2.          (6)

It holds for antisymmetric, not necessarily normalized, states with (1).

## 3. Coulomb finiteness, pair constants and closed forms

For smooth compactly supported complex u away from the origin in R3, integration by parts and div(x/r^2)=1/r^2 give

    0 <= integral |grad u + x u/(2r^2)|^2
       = integral |grad u|^2 - (1/4) integral |u|^2/r^2.              (7)

The cross term uses grad|u|^2=2 Re(conj(u) grad u). To extend (7) to H1, first approximate by smooth compact functions. A smooth cutoff removing a radius-epsilon ball has derivative O(1/epsilon), supported in a volume O(epsilon^3); on a fixed smooth bounded function the added squared derivative error is O(epsilon), and the other errors tend to zero. Thus the punctured smooth class is H1-dense. Inequality (7) makes the weighted approximants Cauchy in L2(r^(-2)dx); an a.e. subsequence identifies their limit with u/r. Hence (7), translated to any center, holds for H1. Slicing, Fubini and summing the finite spin components yield, with K_i=||grad_i Psi||2^2 and n=||Psi||2,

    integral |Psi|^2/|xi-R_b|^2 <= 4 K_i,
    integral |Psi|^2/|xi-R_b|   <= 2 n sqrt(K_i).                     (8)

For a pair use r=xi-xj and R=(xi+xj)/2. The absolute Jacobian is one, grad_r=(grad_i-grad_j)/2, and

    K_i+K_j = (1/2)||grad_R Psi||2^2 + 2||grad_r Psi||2^2.
    integral |Psi|^2/|xi-xj|^2 <= 2(K_i+K_j),
    integral |Psi|^2/|xi-xj|   <= sqrt(2) n sqrt(K_i+K_j).            (9)

These are configuration-slice identities, not a mistaken Hardy bound in dimension 3N with r interpreted as a full configuration radius.

Put Z_abs=sum_b |Z_b| and M=N(N-1)/2. Sum (8) and use sum_i sqrt(K_i)<=sqrt(NK). For the pairs, sum_(i<j)(K_i+K_j)=(N-1)K and Cauchy–Schwarz over M pairs gives

    V_abs[Psi] := sum_(i,b)|Z_b| integral |Psi|^2/|xi-R_b|
          <= 2 Z_abs sqrt(N) n sqrt(K)
          <= epsilon K + (N Z_abs^2/epsilon)n^2,
    W[Psi] := g sum_(i<j) integral |Psi|^2/rij
          <= g(N-1)sqrt(N) n sqrt(K)
          <= epsilon K + [g^2 N(N-1)^2/(4 epsilon)]n^2.              (10)

Here epsilon>0 has the appropriate kinetic-form units; the N=1 pair sum is exactly zero, without dividing by N-1. Weighted Cauchy–Schwarz polarizes these finite positive forms and makes them continuous on H1. In particular all the displayed forms, not just their diagonal values, are well-defined.

Let q_v=alpha K+W+sum_i integral v(xi)|Psi|^2. For epsilon=alpha/2 in the first inequality of (10),

    q_v[Psi] >= (alpha/2)K[Psi] - C ||Psi||2^2,
    C=2N Z_abs^2/alpha.                                           (11)

The shifted positive form q_v+(C+1)||.||2^2 has a norm equivalent to the H1 norm: (11) supplies the lower estimate and (10) supplies the upper. Completeness of H1_a therefore proves closedness and semiboundedness. The same argument is simpler for T_W since W>=0. The finite spin direct sum and the permutation-invariant scalar potential preserve the antisymmetric space. Standard closed-semibounded-form representation consequently gives a self-adjoint form realization on H_a; this use of the analysis representation theorem is not a new Lean theorem or an identification with the source's already constructed operator. That source-to-form/operator/unit/spin bridge still requires proof. The current source's unconditional molecular self-adjointness and Fourier/Kato–Rellich work are credited; this Hardy proof does not claim to replace their native route.

## 4. Reverse representability: explicit phases, no density assumption

Take any rho in D_N, put u=sqrt(rho) and I=||grad u||2^2. Define its one-coordinate marginal f(t)=integral_R2 rho(t,x2,x3) dx2 dx3. Applying (4) to t->u(t,.,.) gives h=sqrt(f) in H1(R), with ||h||2^2=N and ||h'||2^2<=I.

For completeness the needed one-dimensional bound is global. The locally absolutely continuous representative has H=|h|^2 in W^(1,1)(R), with H'=2 Re(conj(h)h'). Since H' and H are integrable, its two end limits exist and equal zero. Thus 2H(t)=integral_(-infty,t) H' - integral_(t,infty) H', so

    ||f||infty <= ||h||2 ||h'||2 <= sqrt(N I),
    integral_R f^3 <= ||f||infty^2 integral f <= N^2 I.              (12)

Weak H1 representatives in one dimension are locally absolutely continuous by integrating their weak derivative and identifying the difference as a constant. The end-limit argument above justifies the boundary terms, rather than assuming decay pointwise. All quantities in (12) are finite. Define the absolutely continuous Lipschitz cumulative function

    F(t)=(1/N) integral_(-infty,t) f(s) ds,
    F'=f/N a.e., F(-infty)=0, F(+infty)=1,
    phi_k(x)=sqrt(rho(x)/N) exp(2 pi i k F(x1)),   k=0,...,N-1.     (13)

No inverse CDF is used; f can vanish and F can have plateaus. The phase is bounded W1,infty, so the product rule puts phi_k in H1. Its amplitude and amplitude derivative are real; the phase derivative term is imaginary relative to them. The real cross term therefore vanishes, including at density zeros in the weak derivative formula, and gives the exact formula

    ||grad phi_k||2^2 = I/N + (4 pi^2 k^2/N^3) integral f^3.         (14)

For orthogonality, integration over x2,x3 reduces <phi_k,phi_l> to integral F' exp(2 pi i(l-k)F). For l=k this is one. For the nonzero integer n=l-k, the integrand is the derivative of exp(2 pi i nF)/(2 pi i n). Integrate on [-R,R] and let R->infty; the two end values coincide. The integral is zero. This proves orthonormality without requiring a strictly positive marginal or a change-of-variables theorem with an inverse.

Choose one spin label sigma0 and set chi_k(x,sigma)=phi_k(x) 1_(sigma=sigma0). Then

    Psi_rho(y1,...,yN)=(N!)^(-1/2) det[chi_(k-1)(yi)]_(i,k=1..N).   (15)

This is antisymmetric under exchanging the full labels y=(x,sigma). Expanding both determinants in the squared norm leaves N! diagonal permutation terms by orbital orthogonality, proving normalization. Integrating N-1 variables leaves (N-1)! copies of each |chi_k|^2; multiplying the marginal by N gives sum_k sum_sigma |chi_k|^2=rho. In each kinetic integral, the other N-1 variables similarly force the two permutations to agree, giving K[Psi_rho]=sum_k ||grad phi_k||2^2. Products here depend on separate particle variables; their L2 norms and single-particle derivative norms factor, so the finite determinant is genuinely H1. Therefore

    K[Psi_rho] = I + (4 pi^2/N^3)[N(N-1)(2N-1)/6] integral f^3
       <= [1+(2 pi^2/3)(N-1)(2N-1)] I.                            (16)

Equation (9) gives finite electron repulsion for this actual state, and (10), with n=1, gives the explicit upper witness T_W<=alpha K+g(N-1)sqrt(NK). Equations (5),(13)-(16) prove exact equality of the represented total-density class and D_N. Finite q is handled by a fully polarized spin determinant, with no q>=N requirement; spin-resolved, singlet or other fixed-spin-sector representability has not been imposed or claimed. The witness is not asserted to minimize T_W when N>1. D_N itself is nonempty: if a is a nonnegative normalized smooth compact bump, rho=N a^2 is in D_N.

## 5. Every fiber has an actual minimizer

For a fixed rho in D_N let A_rho={T_W[Psi]:Psi in S_N,rho_Psi=rho}. Section4 makes A_rho nonempty with a finite element, and A_rho>=0. Its real infimum F is finite. Choose Psi_j in the fiber with F<=T_W[Psi_j]<F+1/j. Since g>=0, K[Psi_j]<=(F+1)/alpha for j>=1. Thus Psi_j is H1 bounded and normalized.

Weak sequential compactness of a bounded sequence in this Hilbert space follows, for example, by diagonal extraction of its coefficients in a countable orthonormal basis; the bounded coefficient limit defines a vector by Bessel's inequality, and approximation by finite combinations identifies weak convergence. Pass to Psi_j weakly converging to Psi in H1. Antisymmetry is a closed linear condition. A crucial estimate which does not use a binding hypothesis is

    integral_(max_i |xi|>R) |Psi_j|^2
       <= sum_i integral_(|xi|>R) |Psi_j|^2
        = integral_(|x|>R) rho(x) =: delta_R ->0.                    (17)

The equality uses normalization of the total density (1), so there is no extra N in the final tail. It is uniform in j because the entire density is fixed.

Here is an elementary local compactness argument, rather than an assumed global compact embedding on R^(3N). On a finite cube Q in dimension d=3N, subdivide into cubes of side ell. In one dimension the identity h(t)-average(h)=ell^(-1) integral [h(t)-h(s)] ds, followed by the fundamental theorem and Cauchy–Schwarz, gives ||h-average(h)||2<=ell||h'||2. Apply the coordinate-averaging operators successively on a d-dimensional small cube. They are L2 contractions and commute with the other coordinate derivatives; telescope the d differences and use the squared sum bound to obtain

    ||h-P_ell h||_(L2(Q))^2 <= d ell^2 ||grad h||_(L2(Q))^2.        (18)

P_ell is the cell-average projection. The proof holds for complex finite vectors (the q^N spin components), and extends from smooth functions to H1 by reflection/convolution approximation on cubes. Bounded P_ell images lie in a finite-dimensional bounded set; with ell small, (18) gives finite nets for every bounded H1 sequence. This proves L2 precompactness on Q. Extract diagonally over integer cubes. Its local strong limits equal the global weak L2 limit Psi. Weak lower semicontinuity after multiplication by a tail indicator also gives the same bound delta_R for the limit. Outside the coordinate cube [-R,R]^(3N), max_i |xi|>R, hence

    limsup_j ||Psi_j-Psi||2^2 <= 4 delta_R.

Let R->infty to get global strong L2 convergence, in particular ||Psi||2=1. Antisymmetry also passes by the unitary permutation equalities. Equation (6) shows rho_Psi_j->rho_Psi in L1, so rho_Psi=rho exactly a.e. No density is assumed as an extra field of the limit.

Weak lower semicontinuity gives K[Psi]<=liminf K[Psi_j]. From strong L2 extract a subsequence converging a.e. in every spin component (choose squared L2 errors summable and use Tonelli). Away from the collision null sets the Coulomb integrands are nonnegative and converge a.e., so Fatou gives W[Psi]<=liminf W[Psi_j]. Applied along a subsequence realizing the liminf of the sum, these yield

    T_W[Psi] <= liminf_j T_W[Psi_j]=F.

Fiber membership gives the reverse inequality. Thus (3) is an attained minimum for EVERY rho in D_N. The argument is for finite spin q, fixed finite N, repulsive g>=0 and alpha>0. It is not an appeal to compactness of unconstrained molecular minimizing sequences: (17) is a fixed-density fact.

For N=1, (5) gives F>=alpha I and the real sqrt(rho) witness gives equality, independently of the separate N=1 note. For N>1, equality with the Fisher lower bound is not claimed. General bounds established here include alpha I(rho)<=F_LL(rho)<=T_W[Psi_rho]<infty.

## 6. Exact molecular variational reduction and epsilon witnesses

By (8)-(10), integral |v|rho_Psi is finite for every state in S_N. Symmetry, absolute integrability and Fubini give the actual decomposition

    q_v[Psi]=T_W[Psi]+integral v(x)rho_Psi(x)dx.                    (19)

For every rho in D_N, its explicit Slater witness proves integral |v|rho finite. Thus E_v(rho)=F_LL(rho)+integral v rho is a finite real number on the ENTIRE admissible class. Define E0=inf_(Psi in S_N) q_v[Psi]. This is finite real: (11) bounds it below and Section4 supplies a finite trial state. Each fiber attainer has q_v=E_v, hence E_v(rho)>=E0 and the density infimum is bounded below. Conversely every Psi satisfies E_v(rho_Psi)<=q_v[Psi]. For epsilon>0 choose a state with q_v<E0+epsilon, possible by the nonempty real-infimum property; its density has E_v<E0+epsilon. Therefore

    E0 = inf_(rho in D_N) E_v(rho) = inf_(Psi in S_N) q_v[Psi].     (20)

Equivalently a density epsilon-minimizer can be lifted by its ACTUAL attained fiber to a state with exactly the same energy, while a state epsilon-minimizer projects to a density with no greater energy. These are genuine nonempty finite-valued infima, not an unconstrained Real infimum over empty fibers or all raw real functions.

If a normalized ground state Psi0 attains E0, put rho0=rho_Psi0. Replacing it by a fiber attainer gives

    E0 <= F_LL(rho0)+integral v rho0 <= q_v[Psi0]=E0.

Hence rho0 is a density minimizer and Psi0 itself minimizes T_W in its fiber. Conversely, if rho0 minimizes E_v, a fiber attainer supplied by Section5 is a normalized ground state. In the closed-form realization, the variational ground state is an eigenvector: positivity of q_v-E0||.||2^2 and polarization of the linear term at Psi0+t eta (real and imaginary t) give q_v(Psi0,eta)=E0<Psi0,eta> for all form-domain eta. The form representation theorem then places Psi0 in the associated operator domain with eigenvalue E0. No universal existence of such a state is assumed to prove (3) or (20).

This distinction has an exact countercontrol. With no nuclei, alpha>0 and g>=0, dilate any smooth Slater trial by Psi_L(X)=L^(-3N/2)Psi(X/L). Its kinetic energy is alpha K/L^2 and its pair energy W/L, so E0=0. A normalized H1 state cannot have K=0: all distributional gradients zero make each component constant on connected R^(3N), and square-integrable constants are zero. Consequently E0=0 is NOT attained. Fiber attainment remains true. This refutes automatic binding from semiboundedness/self-adjointness or from the constrained-search theorem, not the feasibility of the original molecular programme under appropriate binding hypotheses.

Adding a constant c to v adds Nc to (19),(20) and does not change F_LL. Potential uniqueness modulo constants is NOT proved by that fact. Nondegeneracy of a ground state does not by itself rule out a common state for two potentials and establish both strict cross inequalities. The full HK argument still needs the appropriate common-state exclusion/UCP and domain/binding hypotheses. No convexity of the pure-state functional, mixed-state replacement, spin-resolved uniqueness, universal ground-state existence or physical measurement claim is made.

## 7. Actual DFT/source interface and original B1 debt

The current source gives the molecular potential with its pair counted once and an unconditional molecular essential-self-adjointness apex consuming genuine kinetic/relative-bound work. Those results remain credited. The three DFT modules are genuine conditional scalar/order results, but do not yet construct this physical continuum instance:

* `HohenbergKohnUniqueness.GroundStateData` records density, energy and F with a decomposition; its uniqueness theorem consumes the two strict cross inequalities. The continuum strict inequalities/common-state exclusion are not produced by (20).
* `HohenbergKohnVariational.DensityVariational` defines Ev over all functions X->R and stores a lower bound, a ground minimizer and nondegeneracy. Here the justified carrier is D_N. In general E0 is only an infimum; the stored ground/nondegeneracy fields cannot be populated for every molecular input by this proof.
* `LevyLiebFunctional.LevyLiebData` stores a bounded-below fiber over every raw function; an empty fiber does not become physical +infinity through a Real infimum. Here the fiber is proved nonempty and attained only for the admissible subtype D_N. Its existing conditional witness theorem is not a native general-N constructor.

Next native work must formalize the antisymmetric finite-spin Sobolev carrier, total-density measurable equivalence classes, the marginal/Hardy/Slater/compactness proofs and attained-fiber constructor; identify alpha=hbar^2/(2m), the source's coordinate extraction/Coulomb conventions and the closed-form operator restriction; and then repair/instantiate the interfaces on the admissible carrier without fictitious all-function witnesses. The separate [finite-Coulomb HK construction](D10_COULOMB_HOHENBERG_KOHN.md) and [full original independent review](reviews/D10_COULOMB_HOHENBERG_KOHN.md) now supply the independently accepted manual common-state exclusion and both strict cross inequalities for finite-nuclear Coulomb inputs with existing ground states, including degeneracy and without wavefunction UCP. Appropriate binding/existence hypotheses, native finite-Coulomb multiplier/common-state/strictness lemmas, any justified nondegenerate unique-density specialization and manuscript/consumer propagation remain substantive BUILD obligations. Arbitrary-potential UCP is separate optional broader-domain work, not a new original Coulomb B1 gate. The original B1 full-strength molecular objective and dependency/runner admission process are unchanged. This general-N construction has complete independent manual proof review in the linked original report, not an operator-approved reduction, new closure, green gate, native build or release.

## 8. Manual controls and review targets

The following controls are proved in the arguments, not executed samples: N=1 removes all pair/extra-orbital terms; finite q=1 already supports all N through phases; marginal plateaus and density zeros require no division/inverse; pair-coordinate Jacobian and factor2 in (9) differ from the one-particle factor4; normalization fixes the no-extra-N tail in (17); no-nuclei scaling separates fiber from molecular attainment; external constants shift energy by Nc; arbitrary empty raw-function fibers are excluded by D_N. Review must challenge all these constants and transitions, especially the local-to-global compactness step, source coefficient identification and native-interface limits. No numerical result or proof-assistant acceptance is supplied by these manual controls.

## CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES

The suggested general-N construction is consistent after deriving its constants and domains; it does not itself imply general HK/binding/native results. The separate linked finite-Coulomb HK continuation has independent manual acceptance; binding/native integration remain open. The old roadmaps' pending hkin/hrel/hreal accounts are historically stale relative to the actual unconditional molecular/source work. Conversely source self-adjointness does not establish binding. The raw-function Real-infimum interfaces are not yet this admissible-density construction. The separate N=1 note has its own independent manual acceptance and has not been used as a premise here. No source or roadmap has been edited by this author package.
