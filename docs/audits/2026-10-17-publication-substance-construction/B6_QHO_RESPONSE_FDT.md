# B6: finite-Hamiltonian QHO response, equilibrium FDT and controlled quantum crossover

Original construction author: publication_e2_landing. R2 causal-kernel convergence/contact repair author: publication_checkpoint_source. Complete r2 has independent full manual acceptance by publication_b6_fdt_review and lead acceptance c5b29a26ed80b3853590387b022d649cdd6928cc0645f911a007901601bf0605; [full original independent review](reviews/B6_QHO_RESPONSE_FDT.md). Original r1 and its complete M1 rejection remain historical evidence and are not accepted by this propagation. Native, full D9/device, Caves and publication acceptance remain open.

## 0. Original objective, existing facts and nonduplication

B6 in REMEDIATION_PLAN requires a real fluctuation–dissipation statement with thermal-to-quantum crossover. Phase6AM W4 retains its original derived quantum-floor and operating-point/native objectives. This note constructs actual bounded Hamiltonian dynamics and Gibbs correlations, derives the force-response first variation without an FDT hypothesis, and controls the oscillator cutoff limit. It then derives a conditional electrical-port normalization and a finite-band regular-spectrum example.

QuantumFDTFloor.lean already genuinely instantiates a counting-measure QHO ensemble, proves geometric/energy summability and its partition function, and invokes PhysLib meanEnergy to obtain E0*coth(beta E0/2)/2. That mathematical result is preserved. It has energy units, not current-PSD units. Its final fdt_quantum_noise_floor cancels the Johnson term and proves positivity/addition; it constructs no force response or spectral density. FDTNoiseFloor.lean explicitly assumes a physical noise-floor inequality, and its amplifier theorem explicitly assumes hcaves. Those are honest hypotheses, not this missing derivation.

The independently accepted E1 acoustic-phonon note48a47bc4… already derives free-bath ordered/symmetric spectra and a retarded thermal relation using declared oscillator contractions, and supplies the stronger x*coth(x)-1<=x²/3 bound. I reuse and credit those spectral/thermal identities below, while deriving their single-mode contractions and susceptibility from actual finite dynamics and controlling the cutoff. The accepted E1 quadratic-noise noteabe18e37… gives an explicitly driven/lossy quadratic Markov process whose noise/response ratio generally is NOT a Gibbs coth. It is not made thermal by this construction. No source propagation is counted as new mathematics.

## 1. Actual finite oscillator and normalized Gibbs state

Fix hbar>0 [J s], m>0 [kg], Omega>0 [s^-1], beta>0 [J^-1], and an integer M>=0. Write r=exp(-beta hbar Omega), so 0<r<1, and ell=sqrt(hbar/(2m Omega)) [m]. Let H_M act on C^(M+1) with orthonormal basis |n>, n=0,...,M:

H_M|n>=hbar Omega(n+1/2)|n>.
a_M|n>=sqrt(n)|n-1> for n>=1; a_M|0>=0.
a_M^dagger|n>=sqrt(n+1)|n+1> for n<M; a_M^dagger|M>=0.
X_M=ell(a_M+a_M^dagger).

These are actual matrices; X_M is self-adjoint and ||X_M||<=2ell sqrt(M) (X_0=0). Direct action on basis vectors gives

[H_M,a_M]=-hbar Omega a_M,
[a_M,a_M^dagger]=I-(M+1)|M><M|.                                      (1)

Thus no finite-dimensional CCR=I is assumed. Taking a trace of (1) gives zero on both sides, an independent boundary check.

The actual Gibbs state is rho_M=exp(-beta H_M)/Z_M, with

Z_M=exp(-beta hbar Omega/2)(1-r^(M+1))/(1-r),
p_n=(1-r)r^n/(1-r^(M+1)), sum_(n=0)^M p_n=1.                         (2)

It is positive, trace one and commutes with H_M. Define empty sums as zero and

A_M=sum_(n=0)^(M-1) (n+1)p_n,
B_M=sum_(n=1)^M n p_n=r A_M,
c_M=(1-r)A_M=1-(M+1)p_M.                                           (3)

For M>=1, A_M>0 and c_M>0; for M=0 both vanish. Multiplying the finite geometric sum by (1-r), or differentiating a finite polynomial, gives

A_M=[1-(M+1)r^M+M r^(M+1)]/[(1-r)(1-r^(M+1))],
e_M:=1/(1-r)-A_M=(M+1)r^M/(1-r^(M+1))>0.                           (4)

For example M=1 gives A_1=1/(1+r), c_1=(1-r)/(1+r), which checks both the truncated matrix and the edge correction. No numerical software is needed for these finite identities.

The finite mean energy is E_M=hbar Omega(r A_M+1/2). Its limit is the already proved ensemble expression

E_infty=hbar Omega[r/(1-r)+1/2]=(hbar Omega/2)coth(beta hbar Omega/2),
E_infty-E_M=hbar Omega r e_M.                                     (5)

Do not impose a false finite-cutoff virial identity: m Omega² <X_M²>=hbar Omega A_M(1+r)/2, so E_M-m Omega²<X_M²>=hbar Omega(1-c_M)/2. The upper-level defect disappears in the limit.

## 2. Force response derived by finite-matrix Duhamel expansion

Let f be real and integrable, supported on a finite time interval [t0,T], with units force [J/m]. Apply the genuine Hamiltonian

H_(M,lambda)(t)=H_M-lambda f(t)X_M, lambda real.                     (6)

For each M, the interaction-picture propagator satisfies
dot U_I(t)=(i lambda/hbar) f(t) X_M(t) U_I(t), U_I(t0)=I,
where X_M(t)=exp(iH_M t/hbar)X_M exp(-iH_M t/hbar).

Its Volterra/Dyson series converges in matrix norm: the kth iterated integral has norm at most (|lambda| ||X_M|| ||f||_1/hbar)^k/k!. Differentiating at lambda=0 is therefore justified, not postulated. Since f is real, the generator is skew-adjoint and U_I is unitary. Expanding the actual expectation Tr(rho_M U_I^dagger X_M(t) U_I), cyclicity of the finite trace gives

d/dlambda <X_M(t)>_lambda at0
 =(i/hbar) integral_(t0)^t ds f(s) Tr(rho_M[X_M(t),X_M(s)])
 =integral_(t0)^t ds chi_M(t-s) f(s),

chi_M(t)=(i/hbar) theta(t)<[X_M(t),X_M(0)]>_M.                       (7)

Stationarity follows from [rho_M,H_M]=0. The sign is positive for a perturbation MINUS fX; a PLUS source would reverse it. The value of theta at0 is immaterial because the commutator vanishes there.

For an explicit remainder, the interaction density solves dot rho_I=(i lambda/hbar)f[X_M(t),rho_I]. On trace-class matrices the commutator map has norm <=2||X_M||, because ||AB||_1<=||A|| ||B||_1 and the triangle inequality. Let K_M=2||X_M|| ||f||_1/hbar. Subtracting its zeroth and first Dyson terms yields the rigorous finite-M expectation bound

|<X_M(t)>_lambda-<X_M(t)>_0-lambda(chi_M*f)(t)|
 <=||X_M||[exp(|lambda|K_M)-1-|lambda|K_M]
 <=||X_M|| (|lambda|K_M)^2 exp(|lambda|K_M)/2.                        (8)

This proves genuine finite-system linear response. The bound depends on M; I do NOT use it to interchange an infinite-cutoff limit with the derivative of a nonlinear driven evolution. Section5 constructs the explicit limit of these independently justified first variations. A fully unbounded driven-unitary/native theorem is a separate interface, not silently supplied by (8).

## 3. Actual correlations, response and spectral measures

From (1), a_M(t)=exp(-iOmega t)a_M exactly. The Gibbs state is diagonal, so anomalous expectations vanish and

C_M^>(t):=<X_M(t)X_M(0)>
 =ell² A_M[exp(-iOmega t)+r exp(+iOmega t)],
<X_M>=0,

C_M^sym(t):=< {X_M(t),X_M(0)} >/2
 =ell² A_M(1+r)cos(Omega t),

<[X_M(t),X_M(0)]>=-2i ell² c_M sin(Omega t),
chi_M(t)=2ell² c_M theta(t)sin(Omega t)/hbar
         =c_M theta(t)sin(Omega t)/(m Omega).                        (9)

These follow by multiplying the two actual ladder matrices: <aa^dagger>=A_M and <a^dagger a>=r A_M. In particular the commutator expectation is c_M, not an assumed1.

Use Fourier transform F(omega)=integral_R exp(+iomega t)F(t)dt; all omega/Omega are angular frequencies. Retarded transforms mean z=omega+i eta, eta>0, then eta down to0 in distributions. Integrating the sine explicitly gives

chi_M(z)=c_M/[m(Omega²-z²)]
 =(ell² c_M/hbar)[1/(z+Omega)-1/(z-Omega)].                           (10)

This is analytic in the upper half-plane. It has no growing free mode, but the isolated undamped oscillator is not asymptotically stable. Real-axis resonant response is distributional; persistent resonant forcing can grow secularly. No finite resonant gain or line height follows.

As measures/distributions, using integral exp(i(omega-Omega)t)dt=2pi delta(omega-Omega), set delta_+=delta(omega-Omega), delta_-=delta(omega+Omega). Then

S_M^>(omega)=2pi ell² A_M(delta_+ + r delta_-),
S_M^<(omega)=S_M^>(-omega)=2pi ell² A_M(r delta_+ + delta_-),
S_M^sym=(S_M^>+S_M^<)/2
        =pi ell² A_M(1+r)(delta_+ + delta_-),

chi_M''=Im chi_M(omega+i0)
        =(pi ell² c_M/hbar)(delta_+ - delta_-).                     (11)

The imaginary sign follows from Im1/(x+i0)=-pi delta(x), hence chi'' is positive at the positive-frequency line. One can establish this boundary identity by testing against a smooth compactly supported function: eta/(x²+eta²) is a positive approximate identity of integralpi; its odd companion tends to the principal value. That proves the distributional use of (10), not a pointwise pole evaluation.

The normalization check is
integral S_M^sym(domega)/(2pi)=ell² A_M(1+r)=<X_M²>.
S^> is a positive measure, S^sym even, chi'' odd. Detailed balance is the measure identity S^>(-omega)=exp(-beta hbar omega)S^>(omega), verified separately on both nonzero atoms.

At a positive probe frequency, the positive S^> line describes upward transitions: the system absorbs hbarOmega from a weak external probe. The negative line describes downward emission and has ratio r. Detector terminology varies; these explicit transition definitions fix ours. A normally ordered emission measurement is not the symmetrized spectrum.

## 4. FDT is a conclusion, not a hypothesis

At the positive atom, hbar chi'' has weight pi ell² c_M and the thermal ratio is

A_M(1+r)/c_M=(1+r)/(1-r)=coth(beta hbar Omega/2).

At the negative atom both coth and chi'' change sign. Thus, for every beta>0 and M>=0,

S_M^sym(omega)=hbar coth(beta hbar omega/2) chi_M''(omega),
S_M^>-S_M^<=2hbar chi_M''.                                          (12)

The coth multiplier is only evaluated on support omega=+/-Omega, away from0; no undefined product at0 is introduced. For M=0 both sides are the zero measure. This finite-matrix FDT came from (6)-(9) and the Gibbs weights, without an assumed FDT inequality or classical Johnson term.

At beta=infinity take the ground state directly: for M>=1 A_M=c_M=1, r=0, S^> has only the positive absorption line, S^< only its negative reflection, and S^sym retains equal half-sum vacuum lines. It is legitimate to write the limiting multiplier as sign(omega) on support. The emission line at negative frequency of S^> is zero. There is no universal positive finite normally ordered photodetection floor and no continuum white PSD from two delta lines.

For this actual oscillator the ordinary infinite mean energy equals mOmega² variance. Its coth is therefore the same thermal factor in a derived covariance and response, not an energy added to an unrelated PSD. Section7 supplies the missing electrical dimensional factor.

## 5. Controlled cutoff limit and honest operator boundary

At fixed beta hbarOmega>0,
0<e_M<=(M+1)r^M/(1-r) tends to0 geometrically with a polynomial prefactor.
This last limit follows, for example, from the ratio of successive (M+1)r^M terms tending to r<1; choose a constant between r and1 after a finite index.

Embed the diagonal Gibbs matrices in ell²(N). The infinite normalized state is rho_infty=(1-r)sum_(n>=0)r^n|n><n|. It is positive trace-class. Direct summation gives

||rho_M-rho_infty||_1=2r^(M+1).                                     (13)

State trace distance alone does not control an unbounded X; the explicit weighted estimates below do. On finite-support sequences define the actual weighted shift a|n>=sqrt(n)|n-1> and its adjoint raising shift. The diagonal free Hamiltonian has domain sum E_n²|psi_n|²<infinity and unitary evolution exp(-iE_n t/hbar) coordinatewise. For the unbounded quadratic-form correlations, sum p_n||X|n>||²=ell²(2r/(1-r)+1)<infinity. Hence X rho_infty^(1/2) is Hilbert–Schmidt, and the Gibbs two-point forms are absolutely convergent. They are genuine free-oscillator correlations and equal the explicit limits below. No unproved all-domain CCR or self-adjoint driven extension is used.

Let C_infty, S_infty, chi_infty denote (9)-(11) with A=1/(1-r), c=1. Then

sup_t |C_infty^>(t)-C_M^>(t)| <=ell²(1+r)e_M,
sup_t |C_infty^sym(t)-C_M^sym(t)| <=ell²(1+r)e_M,
sup_t |chi_infty(t)-chi_M(t)| <=2ell²(1-r)e_M/hbar.                   (14)

Total-variation errors of the spectral measures are respectively
||S_infty^>-S_M^>||_TV=2pi ell²(1+r)e_M,
||S_infty^sym-S_M^sym||_TV=2pi ell²(1+r)e_M,
||chi_infty''-chi_M''||_TV=2pi ell²(1-r)e_M/hbar.

Consequently any bounded spectral weighting W has an error at most ||W||_infty times the applicable TV bound. Any finite-integrable force satisfies

sup_t |[(chi_infty-chi_M)*f](t)| <=2ell²(1-r)e_M ||f||_1/hbar.         (15)

For Im z>=eta>0, the susceptibility error is at most
2ell²(1-r)e_M/(hbar eta), from the damped kernel integral. There is no uniform finite real-axis pointwise error through the delta resonances. Equations(14)-(15) explicitly define the limiting linear-response observable from actual finite forced systems, with the derivative taken first for each M. Together with the convergent free Gibbs forms, this is our precise cutoff-limit construction; it does not assert uniform convergence of full driven unbounded propagators for finite lambda.

The finite mean energy limit (5) matches the existing QHO ensemble theorem. At fixed M, beta down to0 instead gives the uniform finite Gibbs state, A_M tends toM/2 and c_M tends to0. The infinite oscillator has no normalized beta=0 Gibbs state. Therefore cutoff removal and a literal infinite-temperature state cannot be interchanged. High-temperature error bounds concern finite beta, with M chosen to satisfy (4), not a fixed-dimensional beta=0 surrogate.

Omega=0, m<=0 or hbar<=0 are excluded, not divided through. Negative beta does not define the infinite Gibbs oscillator. At T=0, any M>=1 already contains the sole ground-to-first excitation needed for (9); M=0 remains the degenerate zero-observable countercontrol.

## 6. Quantitative thermal-to-quantum crossover

For x>=0 define R(x)=x coth x by continuity R(0)=1. The previously accepted E1 phonon-bath argument gives the stronger bound

0<=R(x)-1<=x²/3 (therefore also <=x²/2).                             (16)

For completeness: g=x cosh x-sinh x has g(0)=0, g'=x sinh x>=0, giving the lower bound. h=(1+x²/3)sinh x-x cosh x has h(0)=0 and h'=x g/3>=0, giving the upper bound. Both are strict for x>0. This is a proven inequality, not a truncated Taylor series; it is credited reuse, not new B6 mathematics.

A finite thermal band |omega|<=omega_max has x_max=beta hbar omega_max/2. Wherever the dissipative response measure is nonnegative on positive frequencies, the quantum symmetric spectrum exceeds its classical thermal counterpart and has relative excess <=x_max²/3. The absolute positive-measure inequality remains meaningful where response vanishes; division by a zero classical PSD does not.

At low T on omega>=omega_min>0,
coth(beta hbar omega/2)-1=2/(exp(beta hbar omega)-1)
 <=2/(exp(beta hbar omega_min)-1).                                  (17)

Thus the vacuum approximation is controlled relative to its own nonzero spectral weight on a strictly positive-frequency band. At frequencies approaching0 no uniform low-T vacuum relative bound follows. x of order1 is the crossover, not an empirically chosen detector threshold. At finite beta and nonzero response support, the quantum formula strictly exceeds the classical approximation; a disconnected/zero-coupling port need not have a positive floor.

## 7. Conditional physical charge/current port, units and Hz conversion

Declare an actual Hermitian charge Q=gX with real g [C/m], and an applied real voltage V coupled by H'= -V(t)Q. This is an explicit physical identification, not the assertion that D9's conductance or an amplifier already has it. Equations(6)-(12) apply with X replaced by Q and ell² replaced by g²ell².

If the terminal current is I=dot Q=(i/hbar)[H,Q], then the perturbation adds no instantaneous current term because [Q,Q]=0. The response satisfies
delta I(omega)=-iomega chi_QQ(omega)V(omega), hence

Y(omega)=-iomega chi_QQ(omega),
Re Y(omega)=omega chi_QQ''(omega).                                  (18)

The sign is checked by a passive positive-frequency oscillator line, where ReY is nonnegative as a measure. Equivalently, a sinusoidal voltage gives mean absorbed power (|V|²/2)ReY after a regular stationary/band interpretation; a delta resonance is not a finite steady-state power value.

Stationarity gives <dot Q(t)dot Q(0)>=-d²C_QQ(t)/dt², so S_II^sym=omega² S_QQ^sym, directly checked also by the finite matrix current. Thus

S_(I,omega)^(2),sym(omega)
 =hbar omega coth(beta hbar omega/2) ReY(omega).                      (19)

Our two-sided angular convention is Var(I)=integral_R S_(I,omega)^(2)(omega)domega/(2pi). Q susceptibility has units C²/J=F; Y has A/V; hbar*omega*Y has A²*s, as required for current PSD. The susceptibility time kernel has F/s, distinct from its Fourier transform F. Position covariance has m² and S_X has m²*s. Energy alone has J and cannot be added to A²/Hz.

For f=omega/(2pi) in Hz define the two-sided cyclic PSD by S_(I,f)^(2)(f)=S_(I,omega)^(2)(2pi f), so Var(I)=integral_R df S_(I,f)^(2)(f). This is a distribution pullback: delta(2pi f-Omega)=delta(f-Omega/(2pi))/(2pi). There is no additional free 2pi factor. For a real symmetrized process, define the one-sided PSD at f>0 by doubling the two-sided value:

S_(I,f)^(1),sym(f)=2hbar(2pi f)coth(beta hbar(2pi f)/2) ReY(2pi f).
High-T limit: 4 k_B T ReY(2pi f).
Zero-T limit at f>0: 2hbar(2pi f) ReY(2pi f).                        (20)

Equivalently, on response support this is 4 ReY times the mean oscillator energy at that frequency. It REPLACES the classical approximation, not 4kBTG plus an energy. The static limit of a regular finite-conductance thermal port is finite4kBTG, but a discrete isolated oscillator has delta admittance, not that broadband conductance. No finite SNR, ENBW, photodetection floor or amplifier added-noise result follows from (20).

## 8. An explicit regular finite-band oscillator limit, not an assumed resistor

For finitely many independent oscillators at the SAME beta, in the product Gibbs state, let Q=sum_j g_j X_j. Centered cross-correlations and cross-commutators vanish. All responses/spectral measures add, so the already derived FDT and (18)-(20) hold term by term. Define the positive frequency-weight measure
nu=sum_j g_j² hbar/(2m_j Omega_j) delta_(Omega_j), with units charge².

For a limit measure nu on Omega>0, assume
integral coth(beta hbarOmega/2) nu(dOmega)<infinity
and, if current variance is required,
integral Omega² coth(beta hbarOmega/2) nu(dOmega)<infinity.
Then the forms
C_QQ^>(t)=integral [(n_B+1)e^(-iOmega t)+n_B e^(iOmega t)]nu(dOmega),
chi_QQ(t)=(2/hbar)theta(t)integral sin(Omega t)nu(dOmega)
are absolutely controlled. The positive-frequency spectral density/measure of chi'' is pi nu/hbar; ReY has positive-frequency measure pi Omega nu/hbar. These statements follow from finite sums by controlled integration, rather than putting an arbitrary susceptibility into an FDT hypothesis. For unrestricted noncompact measures one must specify an approximating sequence and convergence with these weights; no convergence from vague measure limits alone is claimed.

A fully explicit example avoids that caveat: choose 0<Omega_min<Omega_max<infinity and G>0, and
nu(dOmega)=hbar G/(pi Omega) 1_[Omega_min,Omega_max] dOmega.             (21)

Approximate (21) by positive Riemann-sum weights on that compact interval. Each weight is realizable by a real g_j since g_j² hbar/(2m_j Omega_j) equals that chosen positive weight. The following distinction between smooth factors and causal kernels is essential; ordinary derivatives of a retarded kernel do not exist through its causal join at t=0.

Write a=Omega_min, b=Omega_max, and h(Omega)=hbar G/(pi Omega). Take partitions of [a,b] with mesh d_n tending to0, intervals I_(n,j) of lengths Delta_(n,j)>0 and tags Omega_(n,j) in those intervals. Choose the explicit positive weights

w_(n,j)=h(Omega_(n,j)) Delta_(n,j),
nu_n=sum_j w_(n,j) delta_(Omega_(n,j)).
k_n(t)=(2/hbar) sum_j w_(n,j) sin(Omega_(n,j)t),
k(t)=(2/hbar) integral_[a,b] sin(Omega t) nu(dOmega),
chi_n(t)=theta(t)k_n(t),    chi(t)=theta(t)k(t).                     (21a)

For a fixed bounded time interval [-T,T], each free ordered correlation integrand
F(Omega,t)=(n_B(Omega)+1)exp(-iOmega t)+n_B(Omega)exp(+iOmega t),
the symmetrized correlation integrand (2n_B(Omega)+1)cos(Omega t), and the smooth response factor (2/hbar)sin(Omega t), together with their first two ordinary time derivatives, is jointly continuous on [a,b] times [-T,T]. Here a>0 and beta>0 keep n_B and its multipliers bounded; multiplication by h also preserves joint continuity. Differentiation under the finite-band integral through order2 is justified by these uniform bounds. For any one of these integrands F and r=0,1,2, set H_r=h partial_t^r F. Comparing each cell integral with its tagged value gives the explicit bound

sup_(|t|<=T) |sum_j Delta_(n,j) H_r(Omega_(n,j),t)
                     - integral_a^b H_r(Omega,t)dOmega|
 <= (b-a) sup_{|u-v|<=d_n, u,v in[a,b], |t|<=T}
                      |H_r(u,t)-H_r(v,t)| ->0.                    (21b)

The last limit is uniform continuity on a compact set, not an executed quadrature. Thus the smooth free correlations and smooth k_n converge with their first two derivatives uniformly on bounded time intervals. Multiplication by the bounded theta preserves uniform convergence of chi_n itself: sup|chi_n-chi|<=sup|k_n-k|. On any compact set separated from0, the first two ordinary derivatives of chi_n converge uniformly: they equal the corresponding derivatives of k_n on t>0 and vanish on t<0.

At the causal join, k_n(0)=k(0)=0, but the right-hand slopes are nonzero. In fact

J_n=k_n'(0)=(2/hbar) sum_j Omega_(n,j) w_(n,j),
J=k'(0)=(2/hbar) integral_[a,b] Omega nu(dOmega)
       =2G(b-a)/pi>0.                                              (21c)

Equation(21b) applied to the first sine-factor derivative gives J_n->J. For our explicit density-times-cell-length weights the stronger exact control holds: Omega_(n,j)h(Omega_(n,j))=hbar G/pi, so J_n=2G sum_j Delta_(n,j)/pi=J for every partition. The left derivative of chi at0 is0 and its right derivative is J; every chi_n has the corresponding jump J_n. Hence these continuous retarded kernels are not classically differentiable at0. Changing theta(0) cannot repair that failure, since k(0)=k_n(0)=0.

The correct derivative statement through0 is distributional. For any smooth compactly supported test function phi, integration by parts on (0,infinity) gives

<D chi,phi>=-integral_0^infinity k(t)phi'(t)dt
           =integral_0^infinity k'(t)phi(t)dt,
<D² chi,phi>=-integral_0^infinity k'(t)phi'(t)dt
            =integral_0^infinity k''(t)phi(t)dt + J phi(0).
D chi=theta k',    D² chi=theta k''+J delta_0.                       (21d)

The first boundary term vanishes because k(0)=0; the second has the displayed positive coefficient k'(0). There is no delta-prime term. Identical identities hold for chi_n with J_n. In particular, for q=1,2,

|<D^q chi_n-D^q chi,phi>|
 <=sup_(supp phi)|chi_n-chi| integral_R |phi^(q)(t)|dt ->0.           (21e)

This proves convergence in distributions across0. It also explicitly preserves the contact: theta k_n'' converges to theta k'' as a locally bounded regular part by (21b), and J_n delta_0 converges to J delta_0 by (21c). The first derivative has only a step, not a delta, because k(0)=0. Therefore the charge-to-current differentiation used in (18) remains valid, but a second ordinary derivative across0 must not replace (21d).

For Im z>0 the actual causal transforms are
chi_n(z)=(2/hbar) sum_j Omega_(n,j)w_(n,j)/(Omega_(n,j)²-z²),
chi(z)=(2/hbar) integral_[a,b] Omega nu(dOmega)/(Omega²-z²).
On any compact subset of the upper half-plane, the integrand times h is jointly continuous in Omega and z and its denominator is uniformly separated from0. The same cell-error/uniform-continuity argument therefore proves uniform susceptibility convergence on those compacts. No uniform pointwise real-axis convergence through spectral lines follows. Spectral measures converge weakly against continuous bounded test functions on the fixed compact support (and its reflected negative band), using the same Riemann argument with their bounded continuous Bose/frequency multipliers; this is not total-variation convergence of atomic measures to a density.

This constructs a limiting observable bath spectrum with causal response, not a trace-class global infinite-tensor Gibbs density or an unbounded interacting device evolution. Causality, the second-derivative contact and the finite positive band are retained; no linewidth or noncompact-limit hypothesis is inserted.

In the limiting band, ReY=G; outside the mirrored band it is zero, with endpoint values understood almost everywhere. The imaginary/reactive part is fixed by the causal susceptibility integral, not dropped. Hence one-sided current PSD in-band is exactly (20), and high-T whiteness is bounded by x_max²/3 relative to4kBTG. Low-T error is bounded by (17). Finite sums remain spectral lines; a smooth density is a specified continuum limit, not an imposed linewidth or a numerical bin height.

This example proves existence of a response/noise system with a controlled regular thermal-to-quantum crossover. It is NOT a proof that D9 has this admittance, that any real conductance stays Ohmic down to zero frequency, or that the bath band can be extended to infinity. Indeed extending nu~1/Omega to0 generally destroys finite charge variance, while extending toinfinity destroys other moments. The displayed finite band is essential, not a convenient hidden cutoff.

## 9. Concrete proof controls, source interface and next milestones

Manual independent controls: finiteM=0 andM=1; explicit missing top-ladder edge; both spectral atom signs/2pi factors; equal-time variance; energy/variance finite-cutoff difference; classical finite-beta and direct ground-state limits; no beta=0 infinite state; zero coupling; real force/source sign; causality/upper-half-plane analyticity; charge/current differentiation and Hz delta Jacobian; finite bath versus regular continuum. No control here is a test execution.

Prospective native decomposition under ordinary ROOT admission:
1. Actual finite Hilbert matrices and Gibbs normalization; commutator edge identity and A/B/c finite sums.
2. Finite real-force Volterra propagator/first derivative with norm remainder; no assumed hFDT.
3. Matrix two-point correlation, retarded kernel and spectral-measure identities; exact ordered/sym conventions.
4. Explicit geometric bounds (4),(13)-(15), Hilbert–Schmidt weighted free-state forms and the stated derivative-first cutoff interface; only then stronger infinite driven evolution if needed.
5. Derived FDT/crossover bounds, charge-current response/units, actual port/admittance identification and controlled operating-band assumptions.
6. Completed independent full manual review is linked above. Next native backend/axiom/source checks, actual source propagation and canonical finding lifecycle/checkpoint remain; native code is not authored or accepted here.

The existing qho_meanEnergy result should be reused, not weakened or deleted. Its genuine thermodynamic content becomes part of a response bridge; fdt_quantum_noise_floor's scalar addition does not become that bridge by renaming. A physical PSD theorem needs typed/explicit units/convention plus actual response/coupling and bath assumptions, with source-qualified conductance and detector weighting. There is no inferred amplifier calibration, experimental parameter, full transistor/transmon/detector model or device-specific crossover.

The full Caves phase-insensitive amplifier obligation remains separate. A Gibbs oscillator mean energy, finite commutator identity or high-gain phrase is not a proof of an amplifier's gain-dependent input/output added-noise bound. No cited hcaves binder is removed here, no high-gain limit is substituted for an exact finite-gain theorem, and absence of library CCR/matrix machinery or estimated LoC is not an infeasibility finding or authorized deferral.

The original B6 physical operating-point/full-native objective stays OPEN until its real interface is constructed, independently reviewed and integrated. The coherently pumped E1 state remains nonequilibrium; the accepted E1 free-phonon and Markov notes are credited separately. No G4/G5/G11, D9/fullbundle, main, human, sourceholding or closure acceptance is conferred by this author's note.

## CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES

No new contradiction in the supplied finite A_M formula was found: it follows exactly, including M=0. Current source's meanEnergy theorem is real mathematics but an energy, whereas its terminal Johnson-plus-energy addition is not a PSD/FDT construction. Prior acoustic-bath work already supplies the stronger1/3 crossover bound and oscillator spectral FDT under contractions; those are reused, not claimed as new. The finite-cutoff Duhamel remainder is M-dependent, so it does not justify interchanging full infinite driven dynamics with differentiation. The explicit derivative-first cutoff limit and optional regular finite-band bath are the actual results. A zero-temperature symmetric vacuum measure is not normally ordered emission, white detector noise, universal positive finite line height or a Caves added-noise theorem.
