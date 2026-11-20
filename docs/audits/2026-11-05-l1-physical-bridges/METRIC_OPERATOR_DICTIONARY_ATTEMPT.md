# Original metric/operator dictionary: kinetic and source construction attempts

Manual mathematical/source candidate for independent review. This attempts
specific operator constructions from the original fields and functional; it
does not choose a CAR algebra, state, source contact, quotient or replacement
action. No scientific evaluator, CAS/matrix/Haar test, contraction, Lean/native
or slot job is authorized or run. Full normalization and N4 remain OPEN.

## 1. Exact input and the physical correspondence being attempted

Use the original closed g1 S4+g2 S2, oriented Berezin and full compact Haar
functional, including S4 and both temporal interfaces. The already accepted
N16 temporal identity specifies the literal independent metric source

    Z[J,j]=I exp(S_g(T(j))+sum_(x,mu<=nu) J_x,mu,nu Q_x,mu,nu(T(j))),
    Q_x,mu,nu=sum_A T_x,mu^A T_x,nu^A.

At fixed j=0 and J=0 it is the unchanged original action. No scalar matter
determinant, ordinary body or altered time boundary is added. Q is a degree4
Grassmann polynomial, not an ordinary metric value. The intended physical
target is [Volovik2312.09435v2](https://arxiv.org/html/2312.09435v2), III(18)-(22),
an expectation-valued metric with a physical operator/product/state map.
Its Euclidean/Lorentzian signature map, matter coupling and source units
remain owed. An ordinary positive metric body cannot be inferred from Q.

The original source and action are supported by
[Diakonov1109.0091v1](https://arxiv.org/abs/1109.0091v1), I, II(1)-(2),
IV(11), V(23)-(28), VI. The introduction expressly allows psi/barpsi to be
abstract Grassmann variables in this model, with actual matter interpretation
a future possibility. The dagger notation alone therefore does not derive
canonical CAR, a Hilbert adjoint or a Hamiltonian. The higher-term ellipsis
is not introduced into this fixed two-term analysis.

[CGL1511.03646v3](https://arxiv.org/html/1511.03646v3), I(1.7), uses an actual
Tr(U1 rho U2-dagger) with physical metric/current sources; I.F(1.60) specifies
the thermal Gibbs density. Those are source-dependent evolution and operator
statements, not an identification of every Euclidean same-site derivative
with an ordinary operator power. The original W1 charter requires deriving
the map; it does not stipulate the dictionaries tested below. Source jets
through second order and their contacts are already explicitly required by
the common-source construction. Higher-jet identifications need justification.

## 2. Attempt A: derive the original bare kinetic structure before using CAR

This is a direct time split of the ORIGINAL continuum polynomial densities
(1),(2),(11), not an asserted continuum limit of the finite symmetric-time
regulator or a Wick-rotation certificate. Write E_mu^A for the composite
coframe of (11), barpsi for the independent Grassmann dagger variable, and
epsilon^(0ijk)=epsilon^(ijk). All E are even and commute as coefficients.
Let repeated antisymmetric internal pairs use the same full-index convention
as (2). Define

    C_A=1/3! epsilon^(ijk) epsilon_(ABCD) E_i^B E_j^C E_k^D,
    P_i^(AB)=1/2 epsilon^(ijk) epsilon_(ABCD) E_j^C E_k^D,
    K_C=1/2 epsilon^(ijk) epsilon_(ABCD) F_ij^(AB) E_k^D.

Expansion of the determinant along its time row and splitting the unique
world time index in (2) give EXACTLY

    L4=C_A E_0^A,
    L2=P_i^(AB) F_0i^(AB)+K_C E_0^C.

For the second identity, placing0 in either curvature index gives the first
term with factor2/4. Placing0 in either coframe index gives the second term
with the same factor2/4, after simultaneously reversing the world and internal
epsilon signs. All spatial/internal channels remain. Passing to independent
AB components changes the corresponding sum convention, not the degree result.

Set Lambda_A=g1 C_A+g2 K_A. Since

    E_0^A=1/2(barpsi gamma_A dotpsi-dotbarpsi gamma_A psi)
                       +terms with omega_0 but no time derivative,
    F_0i=dotomega_i-D_i omega_0,

the velocity one-form extracted directly from the two original terms is

    alpha=integral_space [g2 P_i^(AB) delta omega_i^(AB)
           +1/2 Lambda_A (barpsi gamma_A delta psi
                                      -delta barpsi gamma_A psi)].

No fermionic momentum sign convention is needed to invert a matrix here:
alpha itself states the extracted coefficient and its ordering. omega_0 is
nondynamical in this split. E_i has Grassmann degree2, so C has degree6,
P degree4 and K degree2. Thus fermionic velocity coefficients have degrees3
or7, and connection velocity coefficients have degree4. In particular the
bare kinetic term is NOT a field-independent barpsi dotpsi term.

Consider Omega=delta alpha with the usual graded field variation. At any
finite spatial Grassmann regularization preserving these polynomial degrees,
fermion/fermion coefficients have minimum degree2 (or6 from C), mixed
fermion/connection coefficients minimum3, and connection/connection
coefficients minimum4. Spatial derivatives of delta fields can be integrated
by parts; they do not remove the positive Grassmann degree of their
coefficients. The precise graded signs do not change these degree bounds.
Consequently EVERY coefficient has zero ordinary Grassmann body.

Reduction modulo the positive-degree nilpotent ideal therefore gives the zero
matrix/differential operator. A matrix inverse over the same coefficient
algebra would reduce to an inverse of zero, which is impossible on any
nontrivial coordinate space. No regular invertible change of coordinates can
change this zero-body property of the two-form. Ordinary connection backgrounds
or finite values of g1,g2 do not create a body in these coefficients.

This is a demonstrated failure of the NAIVE unconstrained bare presymplectic
inversion used to infer canonical equal-time brackets. It does NOT prove
constrained quantization, a quantum condensate/effective kinetic term, or the
physical continuum theory impossible. Those require an actual constraint,
state and limiting construction. Replacing E by an ordinary expectation before
inversion would be an additional dynamical approximation, not an algebraic
inverse of this original zero-body matrix. No such approximation is adopted.
This calculation therefore prevents importing a convenient CAR dictionary
without deriving its relation to the original action.

## 3. Actual finite source jets and their order

For any prescribed real linear combination Q_f of the original Q components
at reference j=0, keep that coefficient/source direction fixed. On N16 it is
homogeneous degree4 in128 Grassmann generators. Therefore

    Q_f^33=0,
    Z_f(t)=I exp(S_g+t Q_f)=sum_(n=0..32) t^n/n! I[exp(S_g) Q_f^n].

This holds before Haar and without a positivity or coupling assumption. For
a spatial half-local combination using only spatial Q_ij in one64-generator
half, the sharper bound Q_f^17=0 applies and the polynomial degree is at
most16. Temporal Q_00 and Q_0i cross the cut and are NOT half-local operators
by definition. Their source jets belong to the full boundary kernel.

Wherever the FULL Z=Z_f(0) is nonzero, put M_f(t)=Z_f(t)/Z. Then

    M_f^(n)(0)=I[exp(S_g) Q_f^n]/Z,    M_f(0)=1.

No nonzero Z or particular normalized point is evaluated here. All64th
derivatives vanish, and all32nd derivatives vanish for the spatial-half case.
In contrast, varying the world-frame source j differentiates S_g(T(j)) and
Q(T(j)) too: second jets contain S_jj and Q_j contacts as well as products.
They are NOT simply Q_f^2. The accepted complete contact identities remain
in force, and a proof about literal J at j=0 cannot remove those terms.

## 4. Required positive one-mode control: derive the product/source map

This is the fixed known positive fermion control requested by Publication,
NOT an assigned quantization of the gravity variables. One canonical fermion
has n=c-dagger c, n^2=n. Keep H=epsilon n, beta>0, q=exp(-beta epsilon),
and the actual thermal density rho=diag(1,q)/(1+q), with p=q/(1+q). No state
or physical source is changed. Direct spectral calculation gives

    Tr(rho exp(t n))=(1+q exp(t))/(1+q)=1+p(exp(t)-1).

For its ordinary normal-ordered diagonal symbols use B=bar eta eta, B^2=0,
sigma(1)=1, sigma(n)=B. This symbol map on the two-dimensional diagonal
operator space is fixed by the GIVEN control, not fitted to a result.
Its thermal linear functional is necessarily

    L(a+b B)=a+p b=I[(p+B)(a+b B)],    I(B)=1.

In particular L(1)=1 and L(B)=p. Ordinary Grassmann multiplication is NOT
the transported operator product: sigma(n^2)=B but B^2=0. The actual
transported product satisfies B star B=B and, exactly,

    (a+b B) star (c+d B)=ac+(ad+bc+bd) B,
    sigma(exp(t n))=1+(exp(t)-1)B.

Thus the SAME physical trace/source has its correct symbol generating
function L(1+(exp(t)-1)B), not L(exp(t B))=1+p t. The latter is a DIFFERENT
symbol source. Its first jet happens to match, but its second raw moment is0
rather than p. It would falsely assign connected variance -p^2 instead of
the correct p(1-p)>=0. The second source contact p, and all higher contacts,
are FORCED by n^k=n and the fixed exponential; they are not a chosen repair.
Equivalently h(t)=exp(t)-1 is derived here. It is not transferred to gravity.

This positive control demonstrates why truncation of Grassmann source moments
cannot by itself disprove a physical positive state. The product/insertion/
source/contact correspondence must be obtained from the actual theory first.

## 5. Attempt B: ordinary self-adjoint metric moment dictionary

Try to find a self-adjoint physical metric observable A_f and positive
normalized state omega with the proposed literal correspondence

    omega(A_f^n)=M_f^(n)(0)                         for n=0..64.

This does NOT assume a representation of the entire Grassmann algebra or a
CAR dictionary. It is a specific, finite-order but high-order source map to
ordinary powers. Assume all required moments exist. By positivity and
Cauchy-Schwarz, |omega(A_f^k)|^2<=omega(A_f^(2k)) for k a positive integer.
The actual64th moment is0. Successively k=32,16,8,4,2,1 gives

    omega(A_f^32)=...=omega(A_f^2)=omega(A_f)=0.

Thus its mean and variance are zero. For the spatial-half source only jets
through32 are needed. In a finite density-matrix realization,
omega(A_f^2)=Tr(rho A_f^2)=||A_f sqrt(rho)||_HS^2, so A_f vanishes on the
state's support; it need not vanish on the entire Hilbert space. In an
abstract positive moment functional, the same conclusion about mean/variance
uses only the displayed Cauchy-Schwarz chain.

For a genuine fixed ordinary shift b_f, the same test on the CENTERED
observable A_f-b_f I forces its centered mean/variance to vanish. It does
not supply such a body to the original theory. For several components,
positive-state Cauchy-Schwarz makes all ordinary centered cross-covariances
zero once each component has zero second centered moment. This is not a
claim that every geometric/source-contact or retarded susceptibility vanishes.

Therefore a nonzero unshifted expectation-valued metric, or a fluctuating
ordinary metric around a prescribed body, cannot be realized by THIS precise
literal ordinary-power dictionary. It is not a proof against a derived
normal-ordered/time-ordered/contact prescription. In particular the required
C2 response map alone does NOT imply the32/64-jet hypothesis, and this
argument cannot be used to close the original W1/B3 requirements. The
positive one-mode control fails this hypothesis exactly as it must.

## 6. Attempt C: affine Gibbs trace, including noncommuting operators

An alternative concrete attempt is a finite-dimensional physical thermal
construction with Hermitian K and A_f and the literal source relation

    M_f(t)=Tr exp(K+t A_f)/Tr exp(K)            for |t|<delta.

This is NOT assumed to be the original Hamiltonian. It tests the proposed
affine trace dictionary if it were derived. It permits [K,A_f]!=0: its
derivatives are Duhamel ordered, not the ordinary moments of section5.
Both sides are entire functions in the finite-dimensional case, so equality
on an open real interval implies equality for every real t.

If A_f has a nonzero real eigenvalue a with unit eigenvector v, spectral
decomposition and scalar Jensen give

    Tr exp(K+t A_f)>=<v,exp(K+t A_f)v>
                    >=exp(<v,Kv>+t a).

Take t toward infinity with the sign of a. The right side grows exponentially;
no finite polynomial M_f(t) can satisfy that lower bound. Therefore A_f=0
and M_f=1. The same argument for a fixed shift b_f factors out exp(t b_f)
and forces the remaining operator to be zero. This excludes nontrivial
FINITE-DIMENSIONAL affine Gibbs realizations of the literal polynomial, even
with noncommuting K/A_f. It does not identify a gravity Hamiltonian or state.

The original compact gauge-link Hilbert space need not be finite-dimensional.
No unrestricted infinite-dimensional/unbounded-operator extension is claimed.
Nor is every physical source affine in a Hamiltonian. A nonlinear physical
source, insertion product/contact map, continuum limit or unbounded-domain
construction must be DERIVED, not chosen to pass this test. No such replacement
is adopted. The one-mode correct source gives an exponential, not the bare
polynomial, and satisfies the positive thermal control without contradiction.

## 7. Result of the construction attempts and exact next scientific debt

Attempt A starts from the actual original kinetic fields/action and exposes
the zero-body presymplectic inversion obstruction. It does not furnish CAR
or rule out constrained/emergent quantization. Attempts B and C start from
the actual literal metric-source polynomial and expose the precise failed
ordinary-power/finite-affine-Gibbs dictionaries. Neither dictionary has been
established as REQUIRED by the original theory; this report is not a final
original-goal breakdown. No favorable dictionary is selected afterward.

The missing constructive step is now specific: obtain the physical constraint/
boundary state and operator insertion/product prescription from the original
composite action (or prove that required construction impossible), including
the metric's first/second source jets and contacts. The positive control
shows how that prescription can matter; it supplies no gravity prescription.
The exact temporal boundary kernel remains the original finite source-level
object, with crossing metric components handled as kernel insertions. It is
not yet a transfer/thermal trace of a positive physical state. The full-symbol
robustness theorem shortens the task by ruling out purported full-pairing-
preserving convention repairs, not by supplying the physical operator map.

Substrate reconciliation is static and bounded: the existing imported
QuantumNetwork.MixedState.IsDensityOperator is Matrix PSD plus unit trace,
and psdSqrt/spectral trace results consume rather than construct positivity.
The source matches primary; a primary olean exists, while this delivery
checkout has no matching build artifact. Existence is not a fresh dependency/
build match certificate. No Lean proof task, build, slot or cache repair was
opened. A future proof assignment still requires current type/import/LSP and
controller admission. No search absence is used as a substrate theorem.

Full Z/c0, N4 tensor, original B3 range/normalization, physical matter/tensor/
light and causal transport remain OPEN. Publication ROOT retains ordinary
L1 propagation/readiness, gates, integration and operator disposition. Any
actual changed physical premise needs its evidence-backed disposition; this
report asks for no invented convention and changes no physical acceptance.

Independent mathematical review must check the complete time split/degree
argument, source nilpotence, fixed positive control, moment-order chain,
finite Gibbs analytic/growth proof and all conditional scopes. Independent
physics/source review must verify that failed hypotheses are not presented
as mandated physics and that response-order, contacts, constraints and actual
state construction remain explicit. Manual/source acceptance is separate from
kernel, full-wave, publication integration and human acceptance.
