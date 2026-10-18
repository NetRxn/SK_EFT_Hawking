# D10: ground-density injectivity for physical finite-nuclear Coulomb potentials

Author and accepted construction owner: publication thread /root, continuing original B1. Status: INDEPENDENTLY ACCEPTED MANUAL CONSTRUCTION; [full original independent review](reviews/D10_COULOMB_HOHENBERG_KOHN.md). Native molecular integration and full B1 remain OPEN BUILD. No theorem-assistant execution, source installation, numerical experiment, scientific closure or publication acceptance is asserted.

This supplies a general finite-N Hohenberg–Kohn injectivity argument for the actual finite-nuclear Coulomb external-potential class. It uses analyticity of the external-potential difference, not unique continuation or analyticity of a wavefunction. Ground-state existence remains a hypothesis to be supplied under appropriate binding assumptions. This advances the original full B1 molecular Coulomb/native charter. An arbitrary-potential UCP extension is separate optional broader-domain work, not an added prerequisite for that original Coulomb objective.

## 1. Physical carrier and exact statement

Fix N>=1, finite spin multiplicity q>=1, alpha=hbar^2/(2m)>0, and the same electron interaction coefficient g>=0 for both systems. Work in the antisymmetric Hilbert space H_a of q^N-component complex L2 functions on R^(3N), with form domain H1_a and normalized state set S_N. Density and kinetic/pair forms are

    rho_Psi(x) = N sum_spins integral |Psi(x,x2,...,xN;spins)|^2 dx2...dxN,
    K[Psi] = sum_i ||grad_i Psi||2^2,
    T_W[Psi] = alpha K[Psi] + g sum_(i<j) integral |Psi|^2/|xi-xj|.

The density sums all spin labels and integrates the other spatial variables; integral rho_Psi=N for a normalized state. Simultaneous spatial/spin antisymmetry makes all one-particle marginals equal. The accepted general-N constrained-search construction proves the needed Hardy estimates, finiteness, density decomposition and closed semibounded forms on precisely this carrier. Its normalization and physical alpha are retained.

Allow external potentials

    v(x)=c_v - sum_(a=1..M_v) Z_a/|x-R_a|,
    w(x)=c_w - sum_(b=1..M_w) Y_b/|x-S_b|,                         (1)

with real finite coefficients and finitely many fixed centers. Physical attractive nuclei have nonnegative Z_a,Y_b. Coincident centers are first aggregated; zero aggregated charges may be removed. Thus uniqueness of nuclear data below means the finite weighted atomic measure, not an ordered list of labels or zero-charge locations. The units are those of the source: Z and g carry energy times length, alpha carries energy times length squared, c has energy, rho has inverse-volume units. An independently added nuclear–nuclear constant is not inserted into the source's electronic Hamiltonian; such a fixed constant only shifts the many-electron energy and must be handled separately if introduced.

Let

    q_v[Psi] = T_W[Psi] + integral v rho_Psi,
    E_v = inf_(Psi in S_N) q_v[Psi],                              (2)

and similarly for w. Both infima are finite real numbers. A ground state here is an actual normalized form-domain state attaining (2), including possible degeneracy.

**Theorem.** Suppose normalized ground states Psi_v and Psi_w exist and their total spatial densities agree a.e. Then

    v-w = c_v-c_w a.e.,
    E_v-E_w = N(c_v-c_w),
    sum_a Z_a delta_(R_a) = sum_b Y_b delta_(S_b).                 (3)

No nondegeneracy, spectral gap, positivity of a wavefunction, wavefunction UCP or analyticity is assumed. Conversely adding a scalar c to the external potential adds Nc to every normalized state's energy and preserves the entire ground-state set and its densities. Therefore the sets of ground-state densities of two different Coulomb potentials, modulo constants, are disjoint whenever those sets are nonempty. This is density-to-potential uniqueness; it does not assert that one potential has only one ground-state density.

## 2. Domain and cross-energy facts actually required

The general-N construction proves, after slicing three-dimensional Hardy and summing finite spin components,

    ||Psi/|xi-A|||2^2 <= 4 ||grad_i Psi||2^2.                    (4)

Consequently every finite external-potential difference times any H1 state is in L2: each 1/|xi-A| term is square-integrable against |Psi|^2 by (4), and the finite constant term is harmless. Cauchy–Schwarz and finite sums also make integral |v|rho_Psi and integral |w|rho_Psi finite. These are genuine cross-energy expectations for each other's state, not a formal cancellation of undefined integrals.

The form realization is closed and bounded below on H_a. For an attained normalized ground state Psi, the positive form

    a_v[eta]=q_v[eta]-E_v ||eta||2^2 >=0

vanishes at Psi. Expanding a_v[Psi+t eta] for real and imaginary scalar t forces its linear cross term to vanish. Hence

    q_v(Psi,eta)=E_v <Psi,eta>                                  (5)

for all eta in H1_a, with consistent sesquilinear convention. This also places Psi in the domain of the associated self-adjoint form operator; no pre-existing Lean operator identification is assumed. Conversely a normalized state attaining the form infimum satisfies (5) by the same argument, whether or not the ground state is nondegenerate.

## 3. Equal densities force a genuine common ground state

Let rho=rho_Psi_v=rho_Psi_w a.e. Define the finite real number

    D = integral (v-w) rho.

The ordinary, non-strict variational inequalities give

    E_v <= q_v[Psi_w] = E_w + D,
    E_w <= q_w[Psi_v] = E_v - D.                               (6)

Both inequalities are equalities, since their nonnegative gaps add to zero. In particular Psi_v also attains E_w and Psi_w also attains E_v. No assertion that nondegeneracy alone makes the cross inequalities strict has been used.

Choose one of these actual common normalized ground states Psi. Subtract the two weak eigenvalue identities (5). Kinetic and electron-interaction terms cancel because alpha,g,N,q and the carriers are identical. By (4), multiplication by the external difference is L2. It is antisymmetric because sum_i(v-w)(xi) is symmetric under particle permutations. Since H1_a is dense in H_a, the weak equality implies the genuine L2/a.e. identity

    [sum_i (v-w)(xi) - (E_v-E_w)] Psi(X;spins) = 0.              (7)

Testing only in the antisymmetric space is sufficient here: the left member itself lies in that space. This is not an unjustified upgrade from a projected weak equation to a full-space identity.

## 4. Analytic zero sets: full elementary lemma

We need a fact about the multiplier in (7), not about Psi.

**Lemma.** If a real-analytic real function f on a connected open subset U of R^d vanishes on a set of positive d-dimensional Lebesgue measure, it is identically zero.

Here is a local proof, including the measure step. Let A be the set of points at which every partial derivative of f, including order zero, vanishes. A is relatively closed by derivative continuity. It is relatively open: at any point of A, the convergent Taylor series is zero in a neighborhood, so f and all derivatives vanish there. Connectedness therefore implies A is empty unless f is identically zero.

Assume f is not identically zero. At each p in U some derivative of finite order k is nonzero. If f(p)!=0 there is a neighborhood without zeros. Otherwise k>=1, and the order-k derivative tensor gives a nonzero homogeneous polynomial in a direction e; choose e with directional derivative D_e^k f(p)!=0. Such a direction exists because a nonzero real polynomial cannot vanish everywhere (successive one-variable polynomial coefficients prove this). Derivative continuity gives a small rectangular box, rotated so its last coordinate is e, on which D_e^k f never vanishes. On each line parallel to e in that box, f has at most k distinct zeros: k+1 zeros would force a zero of its kth derivative by repeated Rolle's theorem. Thus each one-dimensional section of its zero set has measure zero. The zero set is measurable since f is continuous; Fubini makes its measure in the box zero. The local boxes admit a countable subcover because Euclidean open sets have a countable base. Their union covers U, so the whole zero set has measure zero. This contradicts the assumed positive measure and proves the lemma.

Finite Coulomb sums are real analytic off their centers. At x0!=A write

    1/|x0+h-A| = (1/r0) [1 + 2(x0-A).h/r0^2 + |h|^2/r0^2]^(-1/2),
    r0=|x0-A|>0.

For sufficiently small h the bracket perturbation has absolute value less than one. The convergent binomial power series gives the local real-analytic expansion; finite sums and independent coordinate substitutions preserve it. This establishes the needed analyticity without a claim about any solution to the Schrödinger equation.

## 5. A nonzero common state excludes a nonconstant Coulomb difference

Let B be the finite union of centers in (1), Omega=R3 minus B and U=Omega^N. Omega is open and path-connected: a polygonal path between two points can be detoured around finitely many excluded points in three dimensions. Finite products are path-connected, so U is connected and open. The complement of U in R^(3N) is a finite union of sets with at least one coordinate fixed at a center and therefore has measure zero. Electron-collision sets need not be removed from U: the multiplier below contains no electron-interaction singularities, because they already canceled.

The real scalar function

    f(X)=sum_i (v-w)(xi) - (E_v-E_w)                             (8)

is analytic on U. At least one of the finite q^N spin components of normalized Psi has nonzero L2 norm. Its nonzero set has positive measure. Removing the null complement of U and the null exceptional set in (7) leaves a positive-measure subset of U on which f=0. The lemma proves f identically zero on U.

Hold x2,...,xN at arbitrary fixed points of Omega (for N=1 there are no such coordinates) and vary x1. Equation (8) then shows v-w is constant throughout Omega. Substituting any tuple gives

    v-w=(E_v-E_w)/N on Omega.                                  (9)

There is no division by a wavefunction and no supposition that it is nonzero a.e. Only its nonzero norm and the analytic multiplier's positive-measure exclusion are needed.

To identify the nuclear data, write v-w=c_v-c_w+sum_(A in B) b_A/|x-A| using aggregated signed coefficients. Along |x|->infinity all finitely many Coulomb terms tend to zero. Hence the constant in (9) is c_v-c_w. Near any fixed A, multiply

    sum_(B in centers) b_B/|x-B|=0

by |x-A| and let x->A through Omega. The other finitely many centers have positive separation from A, so all their terms tend to zero and the A term is b_A. Thus b_A=0 at every center. No distributional Laplacian or wavefunction regularity theorem is required. This proves all of (3).

The converse is exact: q_(v+c)[eta]=q_v[eta]+Nc||eta||2^2 on the N-particle space, so E_(v+c)=E_v+Nc and normalized minimizing states are the same. Any fixed nuclear–nuclear scalar must be separately included as an energy shift; it is not N times a per-electron potential constant unless defined that way.

## 6. Genuine strict inequalities for the original scalar reductio

If v-w is not constant in this physical class, (7)-(9) show that there is no normalized common ground state. Therefore for ANY chosen ground states Psi_v,Psi_w, even if either energy is degenerate,

    E_v < q_v[Psi_w] = T_W[Psi_w] + integral v rho_Psi_w,
    E_w < q_w[Psi_v] = T_W[Psi_v] + integral w rho_Psi_v.          (10)

Indeed equality in either non-strict variational inequality would make that other state a ground state for both operators, contradicting common-state exclusion. Equation (10) is a construction of the load-bearing strict cross inequalities under precise physical hypotheses, rather than assuming them as fields.

For source mapping, use single-particle X=R3 and Lebesgue measure in the displayed `GroundStateData` scalar integrals, with n=rho_Psi, E the actual bottom energy and F=T_W[Psi]. The decomposition is (2); the strict hvar inputs are (10). Ground states themselves minimize T_W in their fixed-density fibers by the accepted constrained-search theorem, so F also equals the actual F_LL at that density. Physical densities are equivalence classes a.e.; the current Lean equality is pointwise. A native bridge must work on the appropriate a.e. carrier or choose a common measurable representative when a.e. equality is hypothesized. Merely assigning arbitrary representatives does not make an a.e. statement pointwise.

The source's comment that nondegeneracy alone makes the cross inequalities strict is not a proof of the common-state exclusion. This construction supplies that exclusion for the finite-nuclear Coulomb class and does not need nondegeneracy. It is a manual physical instantiation route, not an installed Lean instance or fresh kernel receipt.

## 7. Boundaries, controls and next native construction

The proof keeps the interacting many-electron continuum with physical kinetic coefficient and finite spin. It covers signed finite external Coulomb coefficients in the estimates, hence the attractive nuclear subclass. It fixes the same alpha,g,N,q for both systems. It does not identify different interactions or kinetic masses from equal density. It does not cover arbitrary external functions, magnetic/vector or spin-dependent potentials, hard walls/disconnected configuration domains, infinite nuclear arrays or variable particle number. General UCP-based extensions remain separate optional broader-domain work; the original molecular Coulomb/native charter is unchanged.

Degenerate ground states are allowed. The result says density determines the external potential modulo constants; it does not make potential-to-density assignment single-valued. A nondegenerate normalized ground eigenvector up to phase does give one density, but existence and nondegeneracy cannot be inferred from self-adjointness. The accepted no-nuclei scaling example still has no unconstrained normalized minimizer. No binding theorem, strict positivity of an eigenfunction, universal nondegeneracy or experimental density reconstruction has been derived here.

Manual controls: N=1 follows without empty-coordinate mistakes; q=1 and arbitrary finite q use the same positive-support argument; coincident/zero nuclear labels cannot defeat aggregated-measure uniqueness; additive constants give exactly N times the energy shift; different nonconstant Coulomb potentials cannot share even a single normalized ground state; real-analyticity of f excludes a positive-measure support, without assuming Psi analytic/nonzero a.e.; disconnected/hard-wall and arbitrary-potential settings cannot inherit the analytic-multiplier step. No sample, numerical or native test was executed for these controls.

Next substantive native work: build the shared physical antisymmetric Sobolev/form/density carrier from the accepted general-N note; prove the finite Coulomb multiplication and analytic-zero-set/common-state exclusion lemmas; connect actual molecular operator/units/spin to the form realization; derive (10) for admitted bound inputs and repair/instantiate the scalar interfaces on the admissible a.e. density carrier. Appropriate molecular binding/existence hypotheses and native molecular integration remain BUILD. The larger arbitrary-potential HK/UCP domain is a separate optional extension, not a new prerequisite for the original Coulomb objective. Independent mathematical review of the analytic lemma, antisymmetric weak-equality upgrade, cross-energy integrability, degeneracy and charge-identification limits is complete in the linked full original review. Source propagation, independent source verification, native evidence and canonical closure through the existing writer remain separate.

## CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES

A general wavefunction UCP theorem is not necessary for this finite-nuclear Coulomb multiplier argument. That does not establish an arbitrary-potential HK theorem or binding. Nondegeneracy alone does not justify the source's strict-cross premise, whereas the actual common-state exclusion here does, including degenerate ground states. Density uniqueness is not wavefunction uniqueness or a single-valued potential-to-density map. No prior source, acceptance review, roadmap or manuscript is changed by this author note.
