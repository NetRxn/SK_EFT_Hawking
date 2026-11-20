# Nonlinear driven mode: finite-cutoff stationary moments, tails and operator scope

**Scientific author:** /root/e1_focused_review; seminorm qualification by the publication lead. **Independently reviewed manual declared-model construction.** The complete [original mathematical review](reviews/PLATFORM_NONLINEAR_PUMP_TAIL_ORIGINAL.md) retains its required topology correction, and the [corrected-scope review](reviews/PLATFORM_NONLINEAR_PUMP_TAIL.md) verifies that correction and accepts the complete finite model. All physical pump/platform/BEC/transport and native obligations remain OPEN. This is a substantive continuation of the accepted passive-mode construction, not device calibration, a native proof or closure of E1:2.3.

All results below are manually derived. No symbolic/numerical software, project import, model/test/Verify execution, Lean/backend/build or compiler is used. The finite model is specified rather than inferred from a pulse photon count.

## 1. Exact finite carrier and declared units

For integer L>=0 let calH_L=span{|0>,...,|L>}, P_n=|n><n|, and

    a_L = sum_(n=1)^L sqrt(n)|n-1><n|,   N_L=sum_(n=0)^L n P_n.
    a_L†a_L=N_L,   a_L a_L†=N_L+I_L-(L+1)P_L,
    [N_L,a_L]=-a_L,   [a_L,a_L†]=I_L-(L+1)P_L.                 (1)

The last term is essential. The truncated annihilator does NOT have full bosonic CCR. All operators here are finite matrices on the entire carrier. Write a,N,I for these finite matrices when L is fixed.

Choose gamma>0, constant complex F, real Delta,U, and

    K_L=f(N)+i(F a†-F* a),
    f(n)=Delta n+U n(n-1)/2,
    dot rho=G_L(rho)=-i[K_L,rho]+gamma D[a](rho),
    D[a](rho)=a rho a†-(N rho+rho N)/2.                        (2)

More generally the stationary occupation results hold for ANY real-valued sequence f(0),...,f(L), consistently chosen as cutoffs vary when comparisons are made. K_L is self-adjoint. H_phys,L= hbar K_L in physical units; Delta,U,F and gamma are angular-frequency/rate quantities in inverse seconds, while N and L are dimensionless. The carrier calH_L is distinct from the physical Hamiltonian H_phys,L.

The adopted bath is zero-temperature Markov one-photon loss. Gamma is not used here: gamma is occupation-loss rate, gamma/2 is the amplitude-loss contribution. It is not automatically the measured optical linewidth, a surface gravity or a hydrodynamic decay coefficient.

A declared flat input-port convention may set

    F=sqrt(gamma_ext) beta,  0<=gamma_ext<=gamma,
    |beta|² = incident photons/second in the SELECTED normalized mode. (3)

This parameterization is an assumption about the port reduction, not a derivation of actual nonlinear polariton coupling. Narrowband input energy over [0,T] is hbar omega_d integral_0^T |beta(t)|²dt with omega_d>0. A total laser pulse energy does not identify beta, gamma_ext, modal projection or the intracavity state. Finite truncation is a computational carrier, not an exact physical input-output CCR model.

## 2. Finite invariant state exists; uniqueness is unnecessary

The finite GKSL generator (2) defines a trace-preserving completely positive semigroup T_t on matrices. To exhibit an invariant state without assuming uniqueness, choose any initial density matrix and form

    rho_bar(T)=(1/T) integral_0^T T_t(rho_0)dt.
    G_L rho_bar(T)=(T_T(rho_0)-rho_0)/T.                       (4)

Density matrices form a compact finite-dimensional set. Along a sequence T_j -> infinity, rho_bar(T_j) converges to a density matrix rho_L. The trace norm of the right side is at most2/T_j. Continuity of G_L gives G_L rho_L=0. This proves existence for every finite L and every admitted f,F,gamma. It proves neither uniqueness nor convergence from every initial state, a uniform mixing gap or a physical bistable-phase claim.

All following stationary inequalities hold for EVERY invariant density matrix, not just one selected by a solver. The L=0 carrier is a trivial vacuum model even when F!=0, so it is not a faithful finite-drive cavity. The substantive cutoff statements concern L>=1 and their controlled large-L limits.

## 3. Mean occupation and finite-duration pump bound, without a coherent ansatz

The adjoint generator is

    G_L*(O)=i[K_L,O]+gamma(a†Oa-{N,O}/2).

Because f(N) commutes with N, the exact number equation is

    d<N>/dt = -gamma <N> + F<a†> + F*<a>
             <= -gamma <N> + 2|F| sqrt(<N>).                    (5)

The inequality is positivity/Cauchy–Schwarz |<a>|²<=<a†a>=<N>, valid for any mixed finite state. No replacement <N²>=<N>² or coherent closure is used.

For a time-dependent integrable drive F(t), the same argument and regularization y_epsilon=sqrt(<N>+epsilon) give

    y_epsilon' <= -(gamma/2)y_epsilon+|F(t)|+gamma sqrt(epsilon)/2.

Integrating and taking epsilon down to0 yields

    sqrt(<N>(t)) <= e^(-gamma t/2) sqrt(<N>(0))
          + integral_0^t e^(-gamma(t-u)/2)|F(u)|du.               (6)

Indeed the extra term arises from gamma epsilon/(2 sqrt(<N>+epsilon))<=gamma sqrt(epsilon)/2. This handles points with zero mean instead of illegally dividing by sqrt(<N>). For initial vacuum and the selected-port convention (3), Cauchy–Schwarz gives

    <N>(t) <= (gamma_ext/gamma)(1-e^(-gamma t))
                                integral_0^t |beta(u)|²du.     (7)

For constant drive it also gives <N>(t)<=R(1-e^(-gamma t/2))² from vacuum, where

    R=4|F|²/gamma²=4 gamma_ext |beta|²/gamma².                   (8)

These inequalities hold at every finite cutoff and for any diagonal f(N), including Kerr. Their saturation belongs to the separate untruncated resonant LINEAR benchmark below. They do not supply transient Poisson statistics or a nonlinear coherent state. For a constant-drive stationary state (5) independently gives <N><=R. A finite mean is not a hard spectral support claim.

The mean amplitude itself is not closed under Kerr or truncation. Equation (1) gives the exact diagnostic

    d<a>/dt=-i<a[Delta+U(N-1)]>-(gamma/2)<a>
                         +F[1-(L+1)<P_L>].                    (9)

Thus even the drive term has a top-boundary correction, and the Kerr moment is not Delta times a alone. Equation (9) prevents importing the old linear coherent steady state by assumption.

## 4. Exact stationary exponential generator and weighted Cauchy bound

Fix any invariant rho_L. Let s>=0, z=e^s and V=e^(sN). Define the actual number generating function and its derivative

    M_L(s)=Tr(rho_L V),   M_L'(s)=Tr(rho_L N V),   M_L(0)=1.     (10)

Finite dimension makes these differentiations exact for every real s. The diagonal Hamiltonian drops out. The exact finite ladder identities are

    a† V a=z^(-1)N V,
    [a,V]=(z-1)V a,   [a†,V]=-(z-1)a† V.                       (11)

They hold also at n=0 and n=L because the prohibited raising/lowering action vanishes. There is NO missing top term in (11); one must not use aa†=N+I to prove it. Direct action on each basis vector proves the identities with the truncated a.

Substituting (11) gives

    G_L*(V)=-gamma(1-z^(-1))N V
                    +(z-1)(F a†V+F*V a).                     (12)

Let X=Tr(rho_L a†V). The second term is 2(z-1)Re(F X), since its two summands are adjoints. For A=V^(1/2)a and B=V^(1/2), state Cauchy–Schwarz gives

    |X|²=|Tr(rho_L A†B)|²
          <=Tr(rho_L A†A) Tr(rho_L B†B)
          =z^(-1) M_L'(s) M_L(s).                            (13)

This is a weighted NONCOMMUTATIVE Cauchy inequality; replacing it by an unproved bound on the ordinary mean <a> would be wrong.

For s>0, stationarity in (12), cancellation of z-1>0 and (13) imply

    (gamma/z) M_L'(s)=2 Re(F X)
                <=2|F| sqrt(M_L'(s) M_L(s)/z).

M_L'(s)>=0 and M_L(s)>0. If M_L'=0 the next inequality already holds; otherwise divide by sqrt(M_L') and square the nonnegative sides. With R from (8),

    0<=M_L'(s)<=R e^s M_L(s).                                (14)

The s=0 inequality follows either by continuity or directly from (5). This DERIVES the weighted derivative estimate before using any MGF upper envelope. No derivative is inferred by differentiating an upper bound.

Integrating (log M_L)'<=R e^s from0 to s proves the cutoff-uniform bound

    M_L(s)<=exp[R(e^s-1)]        for every s>=0, every L,
    Tr(rho_L N e^(sN))<=R e^s exp[R(e^s-1)].                  (15)

No hypothesis bounds Delta,U or requires a stable classical mean-field branch: any real diagonal f leaves this exact estimate unchanged. It also does NOT prove that Kerr statistics are Poisson, stochastic domination by a Poisson law, or bounds on all derivatives/factorial moments obtained by formally differentiating (15).

## 5. Explicit tails, weighted errors and compression

For integer m>=1, every s>0 gives

    P_rhoL(N>=m)<=min{1, exp[R(e^s-1)-s m]}.                   (16)

For R>0 and m>R, minimize by s=log(m/R):

    P(N>=m)<=exp[-m log(m/R)+m-R].                            (17)

For m<=R use the safe bound1 (or any valid fixed-s form); do not use the positive-s optimizer outside its domain. For R=0, (5) forces <N>=0 and positivity forces rho_L=P_0, so every positive occupation tail is EXACTLY zero. This is not a singular logarithmic evaluation of (17).

Weighted tails are separately controlled by the second inequality of (15):

    <N 1_(N>=m)> <= R e^s exp[R(e^s-1)-s m].                  (18)

More generally, for integer j>=1 and t>0, n^j<=j! t^(-j)e^(tn) gives explicit higher moments/tails via (15) and Markov. These are valid pointwise inequalities; there is no unauthorized differentiation of an MGF majorant.

If 0<=M<L, Q_M=sum_(n=0)^M P_n and delta=Tr(rho_L(I-Q_M)), (16) applies with m=M+1. When delta<1, normalized compression

    rho_(L->M)=Q_M rho_L Q_M/(1-delta)

satisfies

    ||rho_L-rho_(L->M)||_1<=2 sqrt(delta).                     (19)

To see this for a mixed state, purify rho_L, project its cavity factor, normalize, and note the purified overlap sqrt(1-delta). The pure-state trace-norm distance is2sqrt(delta); partial trace contracts it. Bounded-observable errors are at most2||O||sqrt(delta). Unbounded number/energy observables require weighted bounds such as (18), not (19) alone. Compression is not asserted to be stationary for the smaller generator.

For the cutoff boundary p_L=<P_L>, (16) gives p_L<=exp[R(e^s-1)-sL]. Thus the mean CCR defect is bounded by (L+1)p_L, and the state-weighted quadratic seminorm of the defect is (L+1)sqrt(p_L). Both vanish at fixed s>0 as L grows, uniformly over stationary states. The GLOBAL operator norm of the defect I-[a_L,a_L†] remains L+1; no operator-norm CCR convergence or hard physical cutoff follows.

## 6. A genuine finite-time truncation consequence, not a mixing claim

Embed a stationary rho_L into any larger carrier calH_J, J>=L+1, using the SAME f(n), drive and loss. The diagonal term and loss agree on that embedded state. The only missing Hamiltonian link is

    B=i F sqrt(L+1)|L+1><L| -i F*sqrt(L+1)|L><L+1|.

Consequently G_J(rho_L)=-i[B,rho_L]. On the embedded state B rho_L has only its raising term. Its trace norm is

    ||B rho_L||_1
       =|F|sqrt(L+1) sqrt(<L|rho_L²|L>)
       <=|F|sqrt((L+1)p_L),

where rho_L²<=rho_L. Therefore

    ||G_J(rho_L)||_1<=eta_L:=2|F|sqrt((L+1)p_L)
         <=2|F|sqrt(L+1) exp{[R(e^s-1)-sL]/2}.                (20)

This is a rate-valued residual, uniform in J and the diagonal f. The loss has no hidden raising boundary because a†a=N exactly. For the larger finite CPTP evolution,

    ||T_t^(J)(rho_L)-rho_L||_1 <= min{2, t eta_L}.              (21)

Proof: integrate T_u^(J)G_J(rho_L) from0 to t and use trace-norm contractivity on Hermitian matrices. This controls approximate invariance on a fixed observation interval; eta_L tends to0 exponentially up to its polynomial prefactor. It does not bound distances between arbitrary stationary states at different cutoffs or justify taking infinite time before L without an independent mixing/stability bound.

Together (16)–(21) give a quantitatively useful cutoff choice/error for this nonlinear model. They are not a claim that incident finite energy makes a finite Fock subspace invariant.

## 7. Optional infinite-carrier limit: exactly what is and is not constructed

The uniform tails make the family of embedded rho_L trace-norm relatively compact: choose Q_M with uniformly small tail, use the gentle bound ||rho_L-Q_M rho_L Q_M||_1<=2sqrt(delta), and cover the bounded finite-dimensional matrix block by a finite net. Trace class is complete; hence a subsequence converges in trace norm to a positive trace-one rho_infty. Monotone finite-number compression transfers the bound M_infty(s)<=exp[R(e^s-1)].

For any finite-matrix observable O=P_M O P_M, the formal infinite adjoint expression

    i[f(N)+i(Fa†-F*a),O]+gamma(a†Oa-{N,O}/2)

is a bounded finite-matrix observable supported at most through M+1. Its entries agree exactly with the finite adjoint for all L>=M+1. Passing its stationary expectation to the trace-norm subsequential limit proves zero expectation on this algebraic finite-matrix test core.

This supplies a NORMAL STATE with WEAK ALGEBRAIC stationary identities, not yet invariance under a specified infinite-dimensional quantum dynamical semigroup or uniqueness. For arbitrary fast-growing real f the exponential-number bounds alone need not control every f(N)-weighted generator domain. Even for polynomial Kerr, a physical infinite evolution claim requires an identified conservative CP trace-preserving semigroup, its unbounded Hamiltonian/dissipator domains, a core/closure or uniqueness theorem connecting the formal expression with the actual generator, and the appropriate approximation theorem. None is silently supplied by finite-matrix existence. The finite results (4)–(21) do not depend on asserting that completion.

## 8. Actual intrinsic Kerr commutators in a stated state seminorm

Now take only K_0=f(N)=Delta N+U N(N-1)/2, excluding the drive AND dissipation. With d(n)=Delta+U(n-1), direct basis action gives, for every integer k>=0,

    ad_(K_0)^k(a)=(-1)^k a d(N)^k,
    ad_(K_0)^k(a†)=a†[Delta+UN]^k.                              (22)

For k=0 both mean the original ladder operator. At the top, a†|L>=0, so (22) still has no fictitious extra raising link. On full Fock space these identities initially hold on the finite-particle algebraic core; no bounded global norm follows.

Let nu>0 be an explicitly chosen reference rate, and define the state-weighted Hilbert–Schmidt seminorm

    ||X||_(rho,2)=[Tr(rho X†X)]^(1/2).

This is a seminorm on the operator vector space for an arbitrary positive trace-one rho, with no faithfulness assumption. In finite dimension it equals the Hilbert–Schmidt norm of X rho^(1/2); its null space consists of X satisfying X rho^(1/2)=0. Quotienting by that linear null space gives an induced Hilbert norm. For allowed vacuum rho=P_0 and L>=1, X=P_1 is nonzero but has seminorm zero. All following bounds concern the displayed seminorm of the represented operators. No commutator or transport generator is asserted to preserve its null space, descend to the quotient, or become bounded there. On an infinite carrier further operator domains and completion would have to be specified separately.

For any stationary finite rho_L from (2), (22) gives the EXACT seminorm identity

    ||ad_(K_0/nu)^k a||_(rho_L,2)^2
            =nu^(-2k)<N |Delta+U(N-1)|^(2k)>.                 (23)

This is not an operator norm and rho_L need not commute with N. The product in (23) is diagonal, which is enough.

For n>=1, |Delta+U(n-1)|<=b n with b=|Delta|+|U|. For t>0 the pointwise inequality n^(2k)<= (2k)! t^(-2k)e^(tn), together with the DERIVED weighted estimate (14)–(15), implies

    ||ad_(K_0/nu)^k a||_(rho_L,2)^2
       <= (b/(nu t))^(2k) (2k)! R e^t exp[R(e^t-1)].

Using (2k)!<=(4^k)(k!)² yields the uniform factorial estimate

    ||ad_(K_0/nu)^k a||_(rho_L,2)
      <= C(R,t) k! [2b/(nu t)]^k,
    C(R,t)=sqrt(R) exp{[t+R(e^t-1)]/2}.                        (24)

This holds for all k>=0, t>0 and every finite-cutoff invariant state. At k=0 the formula is an upper bound for sqrt(<N>), not an equality identifying C as the exact initial seminorm. Treat the b=0 order0 factor as1; every positive-order commutator is then0. At R=0 the state is vacuum and all left sides vanish. No Poisson ansatz was needed.

The bound is a concrete weighted topology result for the INTRINSIC diagonal Hamiltonian and observable a. It is not a bound for repeated commutators with the FULL driven K_L, not powers of G_L*, not the physical density observable, and not repository F3 in global operator norm. A topology/reference-observable/transport bridge is a separate construction. The distinction already appears at first order: [K_L,a]=-a d(N)-i F[I-(L+1)P_L]. The drive term is absent from (22), so using (24) for that full commutator would discard a real contribution.

## 9. Actual finite global bounds and comparison with epsilon=sqrt(n_max)

For L>=1 let

    m_L=max_(1<=n<=L)|Delta+U(n-1)|/nu.
    O_L=a_L/sqrt(L),  ||O_L||=1.

Equation (22) gives the finite global operator bound

    ||ad_(K_0/nu)^k O_L||<=m_L^k<=k! m_L^k.                   (25)

At k=0 the value is1. A sufficient comparison with the repository's epsilon=sqrt(L) would require m_L<=sqrt(L). Mean occupation<=R or an exponentially small tail does not imply that condition; the Kerr gap generally grows linearly with L, independently of drive. This does not exclude sharper bounds for other specified observables or a justified physical norm.

For the FULL finite pumped Hamiltonian, use instead

    h_L=max_(0<=n<=L)|f(n)|+2|F|sqrt(L)
         <= |Delta|L+|U|L(L-1)/2+2|F|sqrt(L)  (Kerr).
    ||K_L||<=h_L.

For EVERY bounded O and k>=0, the ordinary finite operator estimate gives

    ||ad_(K_L/nu)^k O|| <= (2h_L/nu)^k ||O||.                  (26)

Proof is induction from ||[A,O]||<=2||A||||O||. This is an actual full-pumped Hamiltonian bound on the finite carrier, with explicitly cutoff-dependent constants, not a reinterpretation of (24). Adding the finite Lindblad part gives the DISTINCT generator-power estimate

    ||(G_L*/nu)^k O|| <= [(2h_L+2gamma L)/nu]^k ||O||.          (27)

Here ||a†Oa||<=L||O|| and ||{N,O}/2||<=L||O|| prove the loss contribution. Powers of a generator are not nested Hamiltonian commutators.

The actual repository predicate inspected in source is

    HasOperatorGrowthBound c epsilon n0Norm
       := forall k, c(k)<=k! epsilon^k n0Norm.

PolaritonF3Bound fixes epsilon=sqrt(n_max), n0Norm=1 and assumes the pointwise bound. It has no Hamiltonian, state, norm or calibrated rate binder. For a normalized finite observable (26) supplies a concrete sequence with epsilon=2h_L/nu, not a derived epsilon=sqrt(L). For (24), C is an upper prefactor in a different state seminorm; setting it to1 or relabelling a growth constant as an occupation is not justified. The full-Fock a is unbounded; when d(n) is not identically zero, its nonzero intrinsic Kerr ladder commutators are also globally unbounded, despite the stationary weighted moments. The zero-drive vacuum control is particularly sharp: weighted seminorms in (23) vanish while the corresponding nonzero global ladder operators remain unbounded.

Thus this construction pays a real nonlinear state/tail milestone but does not prove pump<threshold -> physical F3 -> MIR/uniqueness. The genuine existing conditional exclusion theorem and normalized MIR arithmetic remain mathematics; their missing physical bridge is not assumed.

## 10. Controls, source scope and next substantive construction

- Zero drive: stationarity in (5) forces vacuum for every diagonal f and gamma>0; all positive-number tails and residuals vanish. There is no false claim of nonzero thermal/vacuum occupation.
- Linear untruncated benchmark: for U=0 the already accepted passive-mode calculation gives alpha_ss=F/(gamma/2+iDelta), mu=|alpha_ss|² and M=exp[mu(e^s-1)]. At Delta=0, mu=R and (13)–(15) saturate. This verifies the rate and factor4 convention. It is a separate explicitly solved full linear model, not a coherent finite-cutoff or Kerr ansatz.
- Finite cutoff: nilpotency prevents a_L from having a nonzero coherent eigenvalue. Equation (9) keeps the actual top-boundary correction; (20) quantifies the omitted drive link. No projected coherent state is asserted stationary.
- Lossless/nonconstant limits: gamma>0 and constant F are required for the stationary bound. Divergence of R as gamma->0 at fixed F does not prove anything about existence of a lossless invariant state. Equation (6) is a separate finite-time drive statement.
- Kerr and diagonal variants: the stationary-number bound is independent of f because [f(N),e^(sN)]=0; it is not a claim that nonlinear states/correlations or relaxation rates are f-independent.
- No physical numbers were inserted. There is no derived4fJ intracavity occupation, universal10^6 cutoff or nonlinear optical calibration.

The old full platform note and independent review are retained as the linear/pair antecedent; this note extends their nonlinear stationary-state weakness rather than rewriting them. The selected actual Lean declarations were reread as source, not through a fresh kernel. No new primary-paper equivalence is claimed: the real driven polariton problem still has spatial projection, excitonic/reservoir/nonlinear/multimode couplings, physical bath/state and experimental normalization to derive.

Next coherent scientific work: independently verify the present weighted stationarity/tail and boundary proof, then construct the source-supported modal/reservoir reduction and quantify its omitted terms in a topology compatible with the moments. Establish actual unbounded semigroup/domain and controlled finite-time convergence if taking the infinite model as physical; construct full pumped/nonlocal observable growth in the norm used by transport; carry non-normalized response parameters into the MIR/uniqueness target. The actual BEC local Hamiltonian/domain/growth classification remains separate from the earlier quadratic pair example. Fresh native/numerical/device checks require ordinary ROOT admission. None is a prerequisite waived by this manual milestone, and no new queue/gate or native allocation is created.

CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES

The exact finite MGF calculation supports a Poisson-shaped UPPER ENVELOPE, not Poisson Kerr statistics or hard occupation support. The cutoff ladder has a top CCR defect; retaining it is necessary for the amplitude and truncation statements. Uniform stationary moments give controlled tails/residuals, not a uniform mixing theorem, an identified infinite physical semigroup or global operator-norm convergence. Intrinsic Kerr weighted commutators and full pumped Hamiltonian/generator bounds have different domains and constants; none supplies the repository's sqrt(n_max) physical claim merely from pump energy.
