# E1: an actual oscillator-bath Hamiltonian, memory/noise reduction and a controlled Markov limit

Manual construction by the publication lead, independently accepted by publication_g4_traceability, SHA2566cd0e782305b5d29d87515b1229fb30a3aec454e3b664c3d9a1139199739c495; [complete original independent review](reviews/E1_HAMILTONIAN_BATH_MEMORY_MARKOV_ERROR.md); lead acceptancea6cdb6f0aa514ba96f8f1d94d985eb04472aa6bbb125855adbf1c7bfaa8e8be8. This advances original E1/D1 response/noise BUILD within the specified passive microscopic linear oscillator model only. The earlier paired-mode model is matched directly only at B=0, gamma_prior=2gamma and A=hbar*omega0 before rotation. Material/paired/Kerr/phonon/spatial/horizon/calibrated detector and a usable experimental band remain owed. No native, runtime, source-installation, finding-closure or publication acceptance is asserted.

The independently accepted E1 quantum/noise construction supplied a stable Gaussian Markov generator and input covariance. Here those objects are derived, within an explicit Hamiltonian bath, with finite-band errors. The separately accepted phonon bath/readout and B6 force-response/FDT results retain their scopes; a thermal bath alone does not make a coherently driven coupled system an equilibrium state.

## 1. Actual Hilbert space, Hamiltonian and coherent drive

Let one-particle space be H=C e0 plus C^m, or C e0 plus L2(I,domega), where I=[a,b] is compact, 0<a<b. Frequencies are angular frequencies; a cavity annihilator is dimensionless and its coherent-drive amplitude eta has units inverse time. In the continuum let g in L2(I), J=|g|², and define the bounded self-adjoint operator

 h = [ omega0       (b -> integral g(omega)b(omega)domega) ]
     [ (z -> conjugate(g) z)        multiplication by omega ].       (1)

The finite case replaces the integrals by finite sums. Self-adjointness follows from the displayed conjugate entries, bounded multiplication and Cauchy–Schwarz; no formal pointwise bath annihilator is needed. On bosonic Fock space F(H)=direct_sum_{n>=0} Sym^n H, define dGamma(h) as the direct sum of sum_{j=1}^n h_j, with domain sum_n ||sum_j h_j psi_n||²<infinity. Each summand is bounded self-adjoint. Resolvents (sum_j h_j +/- i)^-1 have norm<=1, so their direct sums are everywhere-defined inverses of dGamma(h)+/-i; this proves self-adjointness. Its unitary group is Gamma(exp(-iht)), verified on every finite-particle sector and then by norm density. This construction does not require a lower bound or a whole-bath Gibbs density.

If a positive energy gap is wanted, complete the quadratic form square:

 <(z,b),h(z,b)> = integral omega |b+conjugate(g)z/omega|²
                    +(omega0-integral J/omega)|z|².                (2)

Thus omega0>integral J/omega implies positivity; bounded invertibility of the triangular square-completion map and a>0 give a strict gap c>0. We will state explicitly when this stronger condition is used.

Let eta in L1([0,T]) and add the coherent drive i hbar(eta a†-conjugate(eta)a). The solution is not posited as a Lindblad equation. Put U(t)=exp(-iht) and d(t)=integral_0^t U(t-s)e0 eta(s)ds in H. Weyl displacement implements c -> c+d. Composing that displacement with Gamma(U(t)) gives a unitary implementing

 c(t)=U(t)c(0)+d(t).                                                (3)

Here c denotes annihilators smeared against vectors of H. The Weyl relations prove that implementation on every smearing; the scalar phase of the implementer has no effect on (3). For smooth eta, differentiating on finite-particle analytic vectors verifies the displayed driven Hamiltonian up to the removable scalar phase. L1 drives follow by norm convergence of d and strong continuity of Weyl operators. We claim the automorphism and all finite-moment observables in (3), not a common invariant domain for an arbitrary discontinuous unbounded time-dependent generator.

For finite baths use the actual product of thermal number densities rho_k=(1-r_k)sum_{n>=0} r_k^n |n><n|, r_k=exp(-beta hbar omega_k), beta>0, and an independent cavity density with finite second moments. The finite product is trace class. In the continuum use the actual gauge-invariant Gaussian state with occupation operator N=multiplication by n_beta(omega)=(exp(beta hbar omega)-1)^-1. It is bounded and positive because a>0. Its positivity on Weyl polynomials is constructive: for the finite-dimensional span of any finite list of smearings, restrict the positive covariance N to that span, take its finite-dimensional centered complex Gaussian displacement, and average the vacuum Weyl functional. Its covariance is precisely vacuum plus N. All such restrictions agree on overlaps, so they define one positive normalized functional on the Weyl algebra. This does NOT assert a trace-class Gibbs density on an infinite continuum Fock space. Tensoring with the independent actual cavity state gives the required initial state; (3) transports it by an actual CCR automorphism.

Zero-temperature bath means N=0. More general bounded nonnegative occupation functions work with the same positivity argument. No equilibrium assertion about the driven cavity follows from this initial product preparation.

## 2. Eliminate the bath exactly, including the quantum commutator

The finite Hamiltonian equations, or their smeared continuum form, give

 adot(t)=-i omega0 a(t)-integral_0^t K(t-s)a(s)ds+F(t)+eta(t),
 K(t)=integral_I J(omega) exp(-i omega t)domega,
 F(t)=-i integral_I g(omega) exp(-i omega t)b_omega(0)domega.          (4)

The last line is a smearing notation for an annihilator, never a claim that b_omega is an individual operator. The bath solution b(t)=exp(-i M_omega t)b(0)-i integral_0^t exp(-i M_omega(t-s))conjugate(g)a(s)ds proves (4) by substitution. All kernels are continuous and bounded; Volterra iteration converges uniformly on finite time intervals, with the factorial bound on successive iterates, hence existence/uniqueness. The cavity component of (3) is the same solution by that uniqueness.

Set G(t)=<e0,U(t)e0>, t>=0. Then G(0)=1, |G(t)|<=1, and

 a(t)=G(t)a(0)+integral_0^t G(t-s)(F(s)+eta(s))ds.                    (5)

The ordered noise correlations in the initial state are actual expectations:

 [F(t),F†(s)]=K(t-s),
 <F(t)F†(s)>=integral J(omega)(n_beta(omega)+1)e^{-i omega(t-s)}domega,
 <F†(s)F(t)>=integral J(omega)n_beta(omega)e^{-i omega(t-s)}domega,
 <F(t)F(s)>=0.                                                     (6)

Thus vacuum contributes to the first ordering, and not normally ordered emission. An energy hbar omega by itself is not a PSD. The correlation kernel units are time^-2; its two-sided angular-frequency spectral density is 2pi J times its occupation weight, on I. Ordinary-frequency conversion and a detector transfer have not been silently inserted.

The actual output CCR is

 |G(t)|²+integral_0^t integral_0^t G(t-s)conjugate(G(t-u))K(s-u)dsdu=1. (7)

This is the norm of the cavity row of the unitary U(t), using (5). Equivalently expand the commutator using (6). Dropping the initial-system term generally violates (7). No decay, absence of a bound state, or long-time thermalization is assumed.

The mean responds to eta by the causal kernel theta(t)G(t). For a real force f coupled as -f X, X=x_zpf(a+a†), eta=i x_zpf f/hbar, and its quadrature response is

 chi_X(t)=-(2 x_zpf²/hbar)theta(t) Im G(t)
         =(i/hbar)theta(t)[X(t),X(0)].                              (8)

Here the initial bath commutes with X(0), so the commutator identity follows directly from (5). This is a force-response derivation, not an FDT assumption. The causal boundary/domain qualifications of the accepted B6 note still apply to derivatives at t=0.

For Im z>0 the upper-half-plane transform and Schur complement give

 integral_0^infinity e^{izt}G(t)dt = i R00(z),
 R00(z)=[z-omega0-Sigma(z)]^-1,
 Sigma(z)=integral_I J(omega)/(z-omega)domega.                        (9)

The transform exists because |G|<=1. The operator resolvent exists for self-adjoint h. Block elimination proves the Schur expression; its denominator cannot vanish in the upper half plane. For an interior continuity point of a smooth J, its boundary self-energy is the principal-value integral minus i pi J. This last density assertion is used only at such points; neither a finite bath nor an arbitrary spectral measure has a finite pointwise linewidth. We do not use a boundary-density assertion to prove any finite-time estimate below.

## 3. Equilibrium FDT for this coupled model, and its preparation condition

Under the explicit gap condition (2), N_h=n_beta(h) is a bounded positive operator. The finite-dimensional Gaussian-restriction argument in §1 constructs the coupled Gaussian state with that covariance. It is stationary because N_h commutes with U(t). In a finite bath it is also the genuine thermal density of hbar dGamma(h); in the continuum only the stated Gaussian functional is required.

Let mu0 be the actual positive spectral measure <e0,E_h(dlambda)e0>, supported in a positive bounded interval and of total mass1. The spectral theorem gives

 <a(t)a†(0)>=integral(n_beta(lambda)+1)e^{-i lambda t}mu0(dlambda),
 <a†(0)a(t)>=integral n_beta(lambda)e^{-i lambda t}mu0(dlambda).       (10)

Consequently the positive-frequency ordered quadrature spectrum has weight 2pi x_zpf²(n+1)mu0, its negative-frequency partner has weight 2pi x_zpf² n reflected(mu0), the symmetric spectrum has weight pi x_zpf²(2n+1) at both reflected supports, and the dissipative susceptibility has positive weight pi x_zpf²/hbar mu0 and its negative reflection. Thus

 S_XX,sym(domega)=hbar coth(beta hbar omega/2) chi_X''(domega).        (11)

At negative frequencies both factors on the right change sign. This is an equality of spectral measures, with the reactive part fixed by causality; no finite-atom peak height is assigned. It follows from the actual state and Hamiltonian via (8),(10), and n/(n+1)=exp(-beta hbar lambda). The initial factorized bath/cavity state in §1 generally differs from N_h and is not stationary under the coupling. Its correct finite-time fluctuations are instead (5),(6). Bath thermality therefore does not discharge an equilibrium-FDT applicability condition for a pumped material system.

## 4. An explicitly positive-frequency finite flat band

Now fix gamma>0, omega0>W>0 and

 I=[omega0-W,omega0+W],       J(omega)=gamma/pi on I, 0 elsewhere.    (12)

This is a particular declared spectral density, not a measured material fit. Rotate a(t) by exp(i omega0 t). Its scalar Green function g(t)=exp(i omega0 t)G(t) is still bounded by1 and solves

 g'(t)=-integral_0^t k(t-s)g(s)ds,  g(0)=1,
 k(t)=(2gamma/pi)sin(Wt)/t,  k(0)=2gamma W/pi.                       (13)

The thermal bath occupation remains n_beta(omega0+xi), xi in[-W,W]; it has not been replaced by n_beta(omega0). The optional whole-Hamiltonian gap is guaranteed by

 omega0>(gamma/pi)log((omega0+W)/(omega0-W)),                         (14)

using (2). Finite-time unitary/Volterra/noise results do not require this optional equilibrium preparation.

To compare with the Markov Green function g_M(t)=exp(-gamma t), construct the primitive residual

 R_W(t)=gamma-integral_0^t k(s)ds
       =gamma[1-(2/pi)Si(Wt)].                                    (15)

The Dirichlet integral used here is established by inserting exp(-epsilon x), differentiating integral exp(-epsilon x)sin(bx)/x in b, and obtaining arctan(b/epsilon). The tail from X is bounded by 2/X by one integration by parts/Dirichlet monotone-amplitude bound, uniformly for the damped kernels as well. Taking epsilon down to0 first on finite intervals and then using that tail proves integral_0^infinity sin(x)/x dx=pi/2. It also gives

 |R_W(t)|<=2gamma for Wt<=1,
 |R_W(t)|<=4gamma/(pi Wt) for Wt>=1.                                (16)

The first follows directly from |Si(x)|<=x for x<=1 and 1+2/pi<2. Define

 I_W(T)=(gamma/W)[2 min(WT,1)+(4/pi)log_+(WT)],
 L_W(T)=(2gamma/pi)[1+log_+(WT)].                                  (17)

Then integral_0^T |R_W|<=I_W and integral_0^T |k|<=L_W, by splitting the integrals at1/W and using |sin x|<=min(x,1). Since |g|<=1, (13) gives sup_[0,T]|g'|<=L_W.

Integration by parts, with R_W(0)=gamma and g(0)=1, gives the EXACT identity

 k*g=gamma g-R_W-(R_W*g'),
 g'+gamma g=R_W+(R_W*g').                                         (18)

Variation of constants for g-g_M therefore yields the fully explicit bound

 sup_[0,T]|g-g_M|<=E_W(T),
 E_W(T)=min{2, I_W(T)[1+T L_W(T)]}.                                (19)

Indeed the convolution with exp(-gamma t) costs at most the L1 norm I_W; the second term costs at most T L_W I_W. The independent bound2 follows from |g|,|g_M|<=1. The cavity's derivative at0 is0 in this rotating frame, whereas g_M'(0)=-gamma; (19) never asserts uniform derivative convergence through the initial layer.

For the rotated drive eta_r=exp(i omega0 t)eta and an initially centered thermal bath, the mean difference from the Markov response on[0,T] is at most

 E_W(T)(|<a(0)>|+||eta_r||_L1[0,T]).                               (20)

This follows from (5), applying (19) separately to the homogeneous and forced terms. It is a finite-band causal error estimate with an explicit initial term, not an assumed exponential response or a formal delta-kernel replacement.

## 5. Actual finite-time filtered covariance and a white-noise error bound

Let f in L1([0,T];C), F1=||f||1. Define the centered rotated field tilde a and the linear output z_f=integral_0^T f(t)tilde a(t)dt. Direct substitution of (5) and Fubini gives

 z_f=alpha_f delta a0+integral_0^T q_f(s)F_r(s)ds,
 alpha_f=integral_0^T f(t)g(t)dt,
 q_f(s)=integral_s^T f(t)g(t-s)dt,
 Q_f(xi)=integral_0^T q_f(s)e^{-i xi s}ds.                           (21)

All rearrangements are justified by finite intervals, bounded kernels and F1<infinity; the noise integral is a smearing with finite thermal second moment. Put n_s=<delta a0†delta a0>, m_s=<delta a0 delta a0>; positivity imposes |m_s|²<=n_s(n_s+1). The ordered covariances are

 <z_f†z_f>=|alpha_f|² n_s+(gamma/pi)integral_{-W}^W n_beta(omega0+xi)|Q_f(xi)|²dxi,
 <z_f z_f†>=|alpha_f|²(n_s+1)+(gamma/pi)integral_{-W}^W(n_beta(omega0+xi)+1)|Q_f(xi)|²dxi,
 <z_f z_f>=alpha_f² m_s.                                          (22)

The anomalous bath term vanishes by the actual gauge-invariant state; it has not been deleted for a squeezed initial cavity. For the Hermitian output z_f+z_f†, add the first two lines and 2Re of the last. A coherent drive shifts the mean only in this linear model. This is not a statement that the actual nonlinear/pumped device has drive-independent noise.

Construct the Markov reference by an actual smeared white CCR input on L2([0,T]), [B(q),B†(r)]=integral q(s)conjugate(r(s))ds, occupation n0=n_beta(omega0), and

 a_M(t)=e^{-gamma t}a0+sqrt(2gamma)B(1_[0,t](s)e^{-gamma(t-s)})
                         +integral_0^t e^{-gamma(t-s)}eta_r(s)ds.   (23)

Its covariance functional is positive by the same finite-span construction and its CCR is e^{-2gamma t}+2gamma integral_0^t e^{-2gamma(t-s)}ds=1. Thus the comparison process exists at the level of actual Gaussian observables; it is not an arbitrary covariance declaration. A thermal trace-class density for all white modes is not asserted.

Let alpha_M,q_M be (21) with g_M. The bounds

 |alpha_f-alpha_M|<=E_W F1,
 ||q_f||2,||q_M||2<=sqrt(T)F1,
 ||q_f-q_M||2<=sqrt(T)E_W F1                                      (24)

follow pointwise from (19) and |g|,|g_M|<=1. For any nonnegative occupation weight w(xi), compare its actual bath contribution to white weight w0>=0. Put delta_w=sup_|xi|<=W|w(xi)-w0| and Tail_W(q)=integral_|xi|>W|Q(xi)|²dxi. Parseval with this Fourier convention gives

 |(gamma/pi)integral_{-W}^W w|Q_f|²-2gamma w0||q_M||2²|
 <=2gamma delta_w||q_f||2²+(gamma/pi)w0 Tail_W(q_f)
             +2gamma w0||q_f-q_M||2(||q_f||2+||q_M||2).             (25)

Proof: subtract the constant weight on the same band, extend that constant integral to the whole real line, then compare the two full L2 norms. The first, missing-band, and response errors are distinct and nonnegative. This proves, using(24), the explicit weaker upper bound

 2gamma delta_w T F1²+(gamma/pi)w0 Tail_W(q_f)
                         +4gamma w0 T E_W F1².                    (26)

No bandwidth is identified with a detector's equivalent noise bandwidth.

The tail is also controlled rather than simply asserted small. The function q_f is absolutely continuous, q_f(T)=0, and

 q_f'(s)=-f(s)-integral_s^T f(t)g'(t-s)dt,
 |q_f(0)|+||q_f'||1 <=[2+T L_W(T)]F1=:V_f.                         (27)

Extend q_f by0 off[0,T]. Its total variation is at most V_f, including the possible jump at0. Integration by parts in its finite derivative measure gives |Q_f(xi)|<=V_f/|xi| for xi!=0, hence

 Tail_W(q_f)<=2 V_f²/W.                                           (28)

No zero-endpoint or differentiable detector-window condition is smuggled in. This is a deliberately conservative bound; a smoother actual window can be analyzed separately.

For the two orderings use w=n or n+1, w0=n0 or n0+1. For the Hermitian-output bath variance use w=2n+1, w0=2n0+1 and delta_w=2delta_n. The actual finite-temperature occupation error satisfies

 delta_n<=beta hbar W n_beta(omega0-W)[n_beta(omega0-W)+1],          (29)

by differentiating n_beta and the mean-value bound on the admitted positive-frequency interval. At zero temperature delta_n=0 exactly; the symmetric vacuum weight is1 and the normal-order weight is0. The initial-cavity contribution to the Hermitian variance has additional absolute difference at most

 2 E_W F1²[2n_s+1+2|m_s|],                                       (30)

since both |alpha_f|,|alpha_M|<=F1. Equations(26),(28) plus(30) bound the full actual filtered quadrature variance, including any initial squeezing, against the Markov reference. Cross-covariances follow by complex polarization; they are not claimed independently zero.

## 6. A nontrivial admissible Markov scaling, with positive physical frequencies

Sending W to infinity at fixed omega0 would violate (12) and does not describe this model. There is instead an explicit weak-coupling/narrow-relative-band regime. Fix omega0>0, beta>0 and a dimensionless tau_*>0; take gamma down to0, W=sqrt(gamma omega0), T=tau_*/gamma. Eventually 0<W<omega0. Then W/gamma goes to infinity and W/omega0 goes to0.

From (17)–(19),

 E_W(T)=O((gamma/W)[1+log(W/gamma)]²) ->0.                          (31)

This is a deduction from the displayed bounds with fixed tau_*, not a numerical fit. At rescaled times t=tau/gamma, g_M=e^{-tau}; the limiting response is nonconstant on[0,tau_*]. For pulses eta_r(t)=gamma eta_*(gamma t), the L1 norm is fixed and (20) converges as well. For filters f(t)=gamma f_*(gamma t), F1 is fixed. Equation(29) gives delta_n=O(W); the three terms in(26),(28) are respectively O(delta_w), O((gamma/W)[1+log(W/gamma)]²), and O(E_W), all tending to0. Equation(30) also tends to0 for a fixed finite-energy initial state. The optional positivity condition(14) eventually holds, since its right side is O(gamma W/omega0).

Thus actual means, ordered/symmetrized filtered covariances and their cross versions converge to the nontrivial Markov reference at the cavity decay time scale. For Gaussian initial cavity states, the Gaussian characteristic functions of any finite list of these smeared observables consequently converge, directly from their means/covariances. No energy-uniform diamond-norm convergence or assertion for all nonlinear observables is made. This scaling supplies a mathematically nonempty parameter regime; physical material parameters and detector observables still need matching before it can be an experimental detection band.

## 7. Finite bath approximants and actual source boundaries

A tagged partition of I gives actual finite Hamiltonians by omega_k in each cell and |g_k|²=J(omega_k)Delta omega_k. With continuous J and occupation on a compact positive band, quadrature uniform continuity makes K_m, the two ordered free-noise kernels and their t-derivatives through each fixed finite order converge uniformly on compact time intervals. For the flat band(12), total coupling weight is EXACTLY 2gamma W/pi at every partition.

For completeness this implies response convergence without assuming the answer. If sup_[0,T]|K_m-K|<=delta_K and |K_m|<=M uniformly, both actual unitary Green functions have norm<=1. Integrating their Volterra difference gives

 sup_[0,T]|G_m-G|<=(delta_K T²/2)exp(M T²).                         (32)

Indeed the forcing difference after two time integrals is <=delta_K T²/2, while the memory term is <=MT integral_0^t |G_m-G|; ordinary integral Gronwall gives(32). The derivative difference in the original frame is then <=(omega0+MT) sup|G_m-G|+delta_K T; in the rotating frame the omega0 term is absent. Combining finite noise-kernel convergence with the response and Fubini proves finite-time covariance convergence, including the initial cavity term. At fixed gamma,W,T all constants are finite. No uniform-in-T bound or exchange with the weak-coupling scaling is inferred; if using finite approximants along(31), choose the quadrature accuracy separately so the explicit(32) error tends to0. No classical derivative claim across a retarded step is added.

The carrying scientific result is an explicit Hamiltonian->memory/noise->filtered quantum-response chain and controlled Markov approximation in a specified linear reservoir model. The spectral density/rotating-wave coupling/state are declared physical-model assumptions, not derived polariton material parameters. Original E1/E2/D1 obligations remain: actual exciton/cavity/material/phonon/reservoir reduction and calibration; nonlinear Kerr/spatial/horizon/scattering error; physical optical ports/aperture/background/efficiency/filter/counting matching; nonempty identifiable device band and uncertainties. This note neither derives an occupation hard cutoff nor transfers a finite-mode tail bound into physical F3/MIR uniqueness. It does not restore a universal quadratic dispersion law.

The source-accepted quadratic quantum-noise generator, phonon noise and modulated-photocurrent notes can now consume this actual bath derivation after matching their variables and error budgets. That matching is a substantive next task, not a completed installation. The complete independent manual operator/noise/error review is accepted. It bound and read the three earlier E1 context notes/reviews that the original author packet did not bind; no retroactive author-read or sourceholding claim follows. Native representation, physical verification, fresh source review, protected integration, canonical closure and publication gates remain separate. No scientific infeasibility, reduced charter or operator deferral is requested or inferred.
