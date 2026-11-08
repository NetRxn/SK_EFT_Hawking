# First physical-model construction: pumped lossy mode, controlled cutoff and quadratic boson pair

**Scientific-author acceptance.** I accept scientific-author responsibility for the explicit model, derivations and limitations in this report. The lead retains the complete physical-platform objective and its integration; /root/publication_d2_proposal_review is the assigned independent reviewer, whose result is not presumed. This is a genuine first manual construction, not the completed device/Hamiltonian/transport classification, a native theorem or an infeasibility finding. Existing E1:2.3 and original Phase6v.3 remain open.

## 1. Model and exact drive-to-occupation map

Fix one bosonic Fock space with orthonormal |n>, n>=0, annihilator a|n>=sqrt(n)|n-1>, number N=a†a and finite-particle common algebraic core. Define a coherent input envelope beta(t), piecewise continuous on a finite interval [0,T], normalized so |beta|² is incident photons per unit time in the selected input mode. Assume a narrowband carrier of positive angular frequency omega_d, so its mean input energy is E_in=hbar omega_d integral |beta|²dt. The selection of this normalized optical mode and its coupling are model inputs, not inferred from a total beam/pulse energy.

Choose occupation-loss rate gamma>0, external-port coupling 0<=gamma_ext<=gamma, gamma_int=gamma-gamma_ext, real detuning Delta=omega_c-omega_d, vacuum loss baths and initial cavity vacuum. Let epsilon(t)=sqrt(gamma_ext) beta(t). In the rotating frame take

    H(t)/hbar = K(t) = Delta N + i(epsilon(t) a† - epsilon(t)* a),
    dot rho = -i[K(t),rho] + gamma(a rho a† - {N,rho}/2).             (1)

Thus gamma/2 is amplitude decay; gamma is occupation decay. This convention is declared rather than silently identified with the surface gravity kappa or an experimental linewidth. The model is a passive, linear, Markov, zero-temperature single-mode cavity. It has no Kerr interaction, exciton reservoir, multimode flow or horizon.

There is an explicit solution rho(t)=|alpha(t)><alpha(t)|, where

    dot alpha = -(gamma/2+i Delta)alpha + epsilon(t), alpha(0)=0,
    alpha(t)=sqrt(gamma_ext) integral_0^t
                  exp[-(gamma/2+i Delta)(t-s)] beta(s) ds.             (2)

Verification is direct: insert the coherent coefficients
c_n=exp(-|alpha|²/2) alpha^n/sqrt(n!) into the matrix elements of (1);
a|alpha>=alpha|alpha>, the drive commutator gives the two linear
epsilon terms, damping gives -gamma alpha/2 and free rotation gives
-i Delta alpha. The scalar normalization derivative supplies the
remaining diagonal terms. The identities extend through alpha=0 by
their power series. Coherent states have all number moments finite;
on a bounded time interval the terms in (1) applied to this rank-one
state are trace class. This verifies this solution on the stated
domain; it is not a new general unbounded-GKSL existence theorem.

Write mu(t)=|alpha(t)|² and N_in(t)=integral_0^t |beta(s)|²ds.
Cauchy–Schwarz in (2) gives the actual finite-pulse inequality

    mu(t) <= (gamma_ext/gamma)(1-exp(-gamma t)) N_in(t).              (3)

It includes the coupling, loss and duration that the repository's
E_pulse/(hbar omega) conversion omits. For a constant resonant input
beta_0,

    mu(t)=4 gamma_ext |beta_0|²/gamma² (1-exp(-gamma t/2))².           (4)

Its steady value is 4 gamma_ext |beta_0|²/gamma², not generically
P_in/(hbar omega_d gamma). There is no universal “one lifetime's
incident energy equals intracavity mode number” identity.

A separate conservation check uses beta_out=beta-sqrt(gamma_ext)alpha:

    dot mu = |beta|² - |beta_out|² - gamma_int mu,
    mu(t)+integral_0^t |beta_out|²ds
          +gamma_int integral_0^t mu(s)ds = N_in(t).                 (5)

This follows by expanding the output modulus and substituting
dot mu=-gamma mu+2 Re(epsilon alpha*). It proves passivity and
mu<=N_in independently of the sharper finite-time bound. Zero drive,
zero external coupling and ring-down after the drive ends give the
correct zero-input/exponential-decay controls. No numerical example
or project model was executed.

## 2. A justified tail, not a hard occupation cap

For this actual solution, P(N=n)=exp(-mu)mu^n/n!: occupation has
Poisson statistics. For nonzero mu its support is unbounded however
small its mean. For integer M>=1 put p_tail=P(N>M), L=M+1. The
factorial-moment identity E[(N)_L]=mu^L, obtained by shifting the
Poisson series, yields

    p_tail <= mu^(M+1)/(M+1)! .                                     (6)

A complementary bound follows from E exp(theta N)=
exp(mu(exp(theta)-1)) and Markov's inequality. For L>mu>0,
theta=log(L/mu)>0 gives

    P(N>=L) <= exp(-mu)(e mu/L)^L.                                  (7)

At mu=0 the tail is exactly zero; use the exact probability or the
minimum with1 when an upper estimate is loose. On [0,T], (3) provides
a uniform upper mean mu_bar=(gamma_ext/gamma)N_in(T); a larger M can
then be selected to meet a declared error tolerance. There is no
derived universal special occupation10^6.

For P_M=sum_{n=0}^M |n><n|, normalized projection
|alpha_M>=P_M|alpha>/sqrt(1-p_tail) obeys

    traceDist(rho, |alpha_M><alpha_M|) = sqrt(p_tail),                (8)

where traceDist=||rho-sigma||_1/2. For every bounded observable B,
the expectation discrepancy is at most2||B||sqrt(p_tail). This
does not control an unbounded number observable merely by citing
trace distance. Its exact missing first moment is instead

    E[N 1_{N>M}] = mu P(Poisson(mu)>=M).                             (9)

This identity and (6) with L=M bound the omitted energy/number tail
explicitly. Finite expectation alone is never promoted to an
operator-norm or spectral-support bound.

## 3. Actual finite-cutoff dynamics: error, not just a projected state

The normalized projection in (8) is not in general a solution of a
hard-truncated cavity. Construct that finite model separately:

    a_M=P_M a P_M, N_M=P_M N P_M,
    K_M=Delta N_M+i(epsilon a_M†-epsilon* a_M),
    dot rho_M=-i[K_M,rho_M]+gamma D[a_M]rho_M,
    rho_M(0)=|0><0|.                                                (10)

It is a finite-dimensional trace-preserving completely positive
time-dependent evolution, embedded back into full Fock space.
This is a computational cutoff; the coherent drive does not make
its subspace invariant in the full model.

Here is a boundary-residual comparison with the exact full solution.
Set q=P_M rho P_M (subnormalized), v=P_M|alpha>,
x=a_M v, w=P_M a(1-P_M)|alpha>. Only the raising/lowering boundary
connects the two sectors, and

    ||v||<=1, ||x||<=sqrt(mu),
    b_M:=||w||=sqrt((M+1)P(N=M+1))
               =sqrt(mu P(N=M)).                                  (11)

The free number Hamiltonian and anticommutator N terms commute
with P_M. Consequently q'=L_M q+R_M, where the Hamiltonian remainder
is the projected cross-sector commutator and the loss remainder is

    R_loss=gamma(|x><w|+|w><x|+|w><w|).

Indeed P a rho a† P=|x+w><x+w|, while the finite model's jump term
is |x><x|. For the drive PK(1-P)=-i epsilon* P a(1-P); the trace norm
of its two rank-one cross terms is at most2|epsilon|b_M. Thus

    ||R_M||_1 <= r_M(t)
       :=2|epsilon| b_M + gamma(2 sqrt(mu)b_M+b_M²).                 (12)

Variation of constants for the finite model and trace-norm
contractivity of its CPTP propagator on Hermitian inputs give
||q-rho_M||_1<=integral_0^t r_M(s)ds. For a pure full state,
||rho-P rho P||_1=sqrt(4p_tail-3p_tail²)<=2sqrt(p_tail).
The real dynamics error therefore satisfies

    traceDist(rho(t),rho_M(t))
       <= sqrt(p_tail(t)) + (1/2)integral_0^t r_M(s)ds.              (13)

One may cap the right side by1. This proves finite-cutoff accuracy
for bounded observables over the declared finite time, including
boundary leakage, instead of assuming a pump-induced invariant
cutoff. All factors in (12) are explicit Poisson probabilities and
the drive/loss parameters of (1). Convergence as M increases follows
uniformly on a finite interval with bounded drive: the Poisson
boundary mass and tail tend uniformly to zero for bounded mu,
and (12) has an integrable uniform bound. It is not a long-time
uniform or nonlinear-device guarantee. Unbounded observables
require further moment estimates such as (9), not (13) alone.

## 4. Actual commutators and comparison with the repository's F3

The current predicate is

    HasOperatorGrowthBound c epsilon n0Norm
        := forall k, c(k)<=k! epsilon^k n0Norm.

The polariton specialization fixes epsilon=sqrt(n_max), n0Norm=1
and ASSUMES this bound. It has no H, rho, observable or physical
time/energy normalization. Here these objects can be supplied, but
their actual norm must not be changed silently.

Introduce a positive reference frequency nu, dimensionless
Kbar=H/(hbar nu), d=Delta/nu and u=epsilon/nu, and freeze a drive
value when forming nested Hamiltonian commutators. Let D=[Kbar,.].
On the finite-particle core of the untruncated oscillator,

    D N = -i(u a†+u* a),
    D²N = -i d(u a†-u* a)-2|u|² I,
    D^(k+2)N=d² D^kN, k>=1.                                       (14)

These follow from [N,a]=-a, [N,a†]=a† and [a,a†]=I. In particular,
at d=0 the second commutator is the nonzero constant
-2|u|² I and the third vanishes. This is an actual nested-commutator
calculation, not an assumed factorial sequence.

For u!=0 the first commutator is an unbounded quadrature on full
Fock space. Also ||N||=infinity. Therefore (14) supplies no finite
global operator-norm c:Nat->Real for this observable in the current
F3 contract. Small coherent mu does not alter that operator fact.
Nor does vacuum occupation zero force commutators to vanish.

For the finite cutoff, M>=1, take O_M=N_M/M so ||O_M||=1. The exact
matrix norms ||a_M||=sqrt(M), ||N_M||=M imply

    h_M:=|d|M+2|u|sqrt(M) >= ||Kbar_M||,
    ||ad_(Kbar_M)^k O_M|| <= (2h_M)^k <= k!(2h_M)^k.                (15)

The induction uses ||[A,B]||<=2||A||||B||. With bounded drive on
[0,T], use sup|u(t)| for a uniform frozen-Hamiltonian bound.
Thus an ACTUAL operator sequence on an ACTUAL finite carrier
satisfies F3 with derived epsilon=2h_M and reference norm1. A
generic time-ordered derivative is a different object; (15) does
not omit drive derivatives by pretending it is that object.

This does not prove the repository's epsilon=sqrt(M) estimate:
that sufficient comparison would require

    2|d|sqrt(M)+4|u| <= 1.                                         (16)

Neither mu<M nor incident energy below a numerical threshold
implies (16). Setting n_max=(2h_M)^2 would merely rename a derived
growth scale; it must not be presented as a derived physical
occupation cap. For the finite open model, the dimensionless
adjoint-generator norm additionally obeys
||L_M†/nu||<=2h_M+2(gamma/nu)M, by bounding each Lindblad term;
this is a distinct generator-power bound, not Hamiltonian F3.

There is also a legitimate but DIFFERENT untruncated state-weighted
estimate. Define ||X||_(2,alpha)=||X|alpha>||. From coherent
quadrature moments,

    ||DN||_(2,alpha) <= C1:=|u|(2sqrt(mu)+1),
    ||D²N||_(2,alpha) <= C2:=|d|C1+2|u|².

Equation (14), R=max(1,|d|) and
C=max(sqrt(mu²+mu),C1,C2) yield
||D^k N||_(2,alpha)<=C R^k<=k! C R^k for every k>=0.
For u=mu=0 the zero-sequence case is exact. Otherwise positive
constants can be chosen. This explicit moment bound is not a
global operator norm, and C is not generally the state norm of N:
at alpha=0, ||N|0>||=0 but ||DN|0>||=|u|. A state-weighted or
energy-constrained F3 extension would need a separately proved
bridge to the particular transport argument. This report does
not quietly substitute one norm for another.

## 5. Independent quadratic-pair milestone for the BEC branch

To avoid predetermining super-factorial growth, choose a specific
closed two-mode quadratic pair model, not a claim about an actual
inhomogeneous acoustic BEC:

    H_pair/hbar = omega(N_a+N_b)+g(a†b†+ab),                        (17)

with real omega>0 and real g (a phase may be absorbed into b).
Use two-mode Fock space, its finite-particle invariant algebraic
core and initial vacuum. Put Z=N_a+N_b+I, X=a†b†+ab,
Y=a†b†-ab. The CCR give

    [Z,X]=2Y, [Z,Y]=2X, [X,Y]=2Z.
    D Z=-2g Y, D X=2omega Y, D Y=2omega X+2g Z,
    D^(k+2)Z=4(omega²-g²) D^k Z, k>=1,                             (18)

where D=[H_pair/hbar,.]. Thus the true commutator hierarchy closes
in a three-dimensional quadratic Lie algebra; it is not the
postulated real sequence (2k)!.

The Heisenberg column (a,b†) obeys
dot v=-i A v with A=[[omega,g],[-g,-omega]],
A²=(omega²-g²)I. In the stable regime omega>|g|, Omega=sqrt(omega²-g²),

    a(t)=(cos(Omega t)-i omega sin(Omega t)/Omega)a
                  -i g sin(Omega t)/Omega b†,                     (19)
    mean(N_a)=mean(N_b)=m(t)=g² sin²(Omega t)/Omega².

The pair state has probabilities
P(N_a=N_b=j)=(1-q)q^j with q=m/(1+m). This follows by solving the
two transformed vacuum-annihilation conditions: adjacent pair
amplitudes have a constant ratio of squared modulus q, and
normalization fixes the geometric prefactor. Consequently
P(N_a>M)=q^(M+1), a justified tail but no hard cutoff when m>0.
At |g|=omega the continuous limit is m=g²t²; at |g|>omega,
m=g² sinh²(sqrt(g²-omega²)t)/(g²-omega²). The latter is dynamical
instability/exponential-in-time amplification, not by itself
super-factorial growth in commutator ORDER.

For a precise positive state-weighted growth witness, make (17)
dimensionless using nu>0. Let R_pair=2(|omega|+|g|)/nu.
The l1 coefficient norm of each commutator on the basis Z,X,Y is
at most R_pair times the preceding norm, by (18). On the actual
initial vacuum, ||Z|0,0>||=||X|0,0>||=||Y|0,0>||=1. Hence

    ||ad_(H_pair/(hbar nu))^k Z |0,0>||
        <= R_pair^k <= k! R_pair^k.                                (20)

Here the reference state norm of Z is exactly1, including k=0;
the shift by I avoids the zero-reference-norm pitfall for N.
Global operator norms of Z and nonzero quadratic commutators
remain unbounded. Equation (20) is not a proof of global-norm
CHHK F3 on an actual BEC; it is a real counter-control against
the inference “unbounded bosons imply (2k)!.” The number-conserving
g=0 limit commutes with Z exactly. Spatially local density n_x,
interactions beyond quadratic order, continuum limits and
reservoirs have not been identified with this two-mode observable.

## 6. Source fidelity and what this builds

Actual held Falque arXiv:2311.01392v2 (5 July2024), PDF SHA256
c430ff83eaf35a4b56dc40a9f64306a66c2221fe3337400cb27981da1bf011bf,
has driven-dissipative GPE(2) on physical page2, with -i hbar gamma/2,
a nonlinear polariton interaction and spatial pump F_p. Its same
page explicitly says incident intensity and cavity density have
a nonlinear detuning-dependent relation and optical bistability.
Physical page3 includes reservoir terms and damped collective
dispersion; page6 distinguishes CW from prospective pulsed
configurations. I reread these carrying text sections directly;
the source-page3/5/6 images had been personally inspected in the
preceding source review. No new all-page pixel or publisher-final
inspection is claimed.

Equations (1)–(20) are newly derived manual results for declared
models, not a statement that Falque's nonlinear fluid has been
reduced to the linear mode. Equation(1) adopts a Markov vacuum-loss
quantization of a passive mode. Matching its input envelope,
external loss fraction, modal volume/Hopfield weights and
neglected nonlinear/reservoir terms to that experiment remains
a substantive calibration/reduction problem. The source's prose
sometimes calls gamma/2 a decay rate, so identifying a measured
linewidth with this report's occupation-loss gamma must retain
the declared amplitude/occupation factor. No measured numbers,
4fJ per-mode support or universal10^6 threshold were imported.

Useful actual output: a complete incident-mode -> intracavity
occupation law with passivity and finite-time bounds; justified
Poisson tails; an explicit dynamical truncation error; derived
finite-matrix operator F3 constants; true untruncated commutator
identities with norm distinctions; and an independent quadratic
pair growth/occupation witness. This pays a first construction
milestone. It does not reduce the original target to a toy model
or close E1:2.3.

Remaining seams, with lead responsible for coherent continuation:
(1) independently review this manual derivation and especially
(12)–(13); (2) map the actual polariton drive/cavity reservoir and
nonlinear/multimode model to a valid cutoff or weighted topology
with quantified reduction error; (3) construct the actual BEC
Hamiltonian/local observable/domain and decide the applicable
growth class rather than require (2k)!; (4) prove the transport
bootstrap in whichever norm/regulator was justified; (5) derive
physical transport/correlator parameters and an explicit uniqueness
target, preserving that an MIR inequality and inclusive OR are
not an exclusive platform classification. Native/formal source,
experimental calibration, actual numerical controls and downstream
manuscript/roadmap/gates require separate normal ROOT allocation
and independent evidence. No slot or closure is inferred here.

## 7. Evidence, ownership and limits

The r40 notebook explicitly accepts lead accountable scientific
construction ownership, updating the earlier coordination-only
state. I have explicitly accepted this scoped scientific author
role above; the independent reviewer is assigned, not pre-accepted.
The first r2 packet check passed0, fresh=true. The original r1
roadmap-location preparation refusal is retained by the lead;
this report does not rewrite or refresh it. All bound references
and separately inspected carrying-source pins are preserved in
evidence.json, with actual first/final original checks in the
process receipt. Expected final owned-output changes are not a
source/authority refresh.

All algebra was derived manually, without numerical/symbolic
software evaluation, project imports, tests, model execution,
native Lean/MCP/build/controller, compiler, graph, Git mutation,
network/fetch or source/holding/registry changes. Processes only
read source and write the three assigned ignored outputs.
Oversized source displays were truncated in the tool UI; their
complete captured streams remain, and the carrying GPE/source
paragraph was reread in a bounded display. No physical/native/
runtime/readiness/closure acceptance is represented.

## CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES

Finite pump expectation yields the model-specific mean/tail
results above, not the hard per-mode support used in the old
Wave6v.3 inference. The actual finite-cutoff F3 constant depends
on detuning, drive, units and cutoff; sqrt(n_max) is not derived
merely from photon count. A coherent quantum mode has unbounded
occupation support, and its first driven number commutator has
unbounded global norm despite finite mean. A quadratic boson pair
can have a closed exponentially bounded commutator hierarchy in
a stated state norm; the general physical BEC (2k)! claim still
requires its own actual Hamiltonian construction. The r40 lead
acceptance is a real new ownership event, not proof that earlier
unknown private assignments were absent or that this result has
already passed independent review.
