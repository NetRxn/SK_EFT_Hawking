# E1 actual Falque dark-reservoir response

**Authorship accepted:** publication_e2_landing accepts the bounded scientific author assignment. Status: **SCOPED MANUAL SOURCE-MODEL CONSTRUCTION ACCEPTED; UNIMPLEMENTED. Independent review SHA256 1b3db89dfb2de2ecf7b012c3ce1c41d82124bfd12f3f6a91ea4d23b9f144b26a.** This constructs the deterministic linear response of Falque Appendix B1/B2 about an actual homogeneous pumped branch. It supplements the accepted frozen-reservoir and declared quantum-port models; it does not replace the original physical E1 calibration, bath/noise, inhomogeneous scattering or error-controlled usable-band BUILD.

## 1. Source, units, normalization and actual stationary branch

Carrying source: held Falque arXiv:2311.01392v2, workspace Lit-Search/Phase-5w/primary-sources/Falque2025.pdf, SHA256 c430ff83eaf35a4b56dc40a9f64306a66c2221fe3337400cb27981da1bf011bf. I directly extracted and read complete PDF pages2,3,9, including main Eq2, homogeneous dispersion Eq3/7 and Appendix B1–B3. This was text inspection, not my own page-image inspection or publisher-final/all-page equivalence claim. Actual extraction argv, raw channels and source pins are retained. The lead supplied SOURCE_MODEL.md 54788a50c9b38f4c1bd819dc35cc39202a1f42c2e837012777fb9629d9d2820d and has separately visually read p9.

Main Eq2 writes hbar*g, whereas B1 displays g and g_r as energies multiplying density. Accordingly use explicitly energy-valued interaction coefficients U and U_R, not an unqualified symbol g transferred between equations. Let n=|psi|² and R be densities in the same declared normalization. In a two-dimensional spatial normalization U,U_R have energy*area units; a different chosen mode normalization must be carried consistently. Density is not a total photon count or Fock cap. Assume finite real parameters n0>0, m>0, U>0, U_R>=0, gamma0>=0, gamma_in>=0, gamma_R>0. Define Gamma=gamma0+gamma_in and eta=hbar*Gamma/2. Strict damping/stability statements below require Gamma>0.

After the pump rotation and removal of its spatial phase, Delta is the ENERGY detuning including the background pump kinetic energy but EXCLUDING the reservoir shift. With a real chosen background amplitude sqrt(n0), the actual uniform equations and stationary conditions are

    i hbar dt psi=[kinetic and flow -Delta+U|psi|²+U_R R-i eta]psi
                  +F+V psi,
    dt R=-gamma_R R+gamma_in |psi|²,
    R0=gamma_in*n0/gamma_R,
    F=(Delta-U n0-U_R R0+i eta)sqrt(n0).                    (1)

Here V is a real physical potential perturbation entering as +V, and F is a complex pump amplitude; both field and drive cannot generally be chosen simultaneously real at finite loss. The Fourier convention is exp[i q·x-i omega t], with omega an angular laboratory frequency, q measured relative to pump wave vector, v=hbar*k_p/m, epsilon=hbar²|q|²/(2m), and d=hbar*v·q. Energies divided by hbar give angular frequencies; a displayed GHz/Hz marker would require its explicit 2pi convention. No numerical linewidth or rate is inferred here.

Define U_eff=U+U_R gamma_in/gamma_R. The stationary intensity relation is

    I=|F|²=n0[(Delta-U_eff n0)²+eta²].                       (2)

This follows from the source, rather than importing a generic gain-reservoir pump model. Multiple stationary branches can exist. The Appendix B3 ratio beta=U_R R0/(U n0)=U_R gamma_in/(U gamma_R) is static. Page9 uses approximately1.84 at the stated same-sample/exciton-photon-detuning condition to fit gn; neither that ratio nor the reported approximately80microeV polariton decay energy identifies gamma_R and gamma_in separately. In particular I do not assign another experiment's reservoir lifetime to Falque, identify gamma0 with Gamma without evidence, or equate a fitted intensity to calibrated density.

## 2. Exact three-component linearization and full inverse

Write delta_n=sqrt(n0)(u+v_h), where u=delta_psi_q and v_h=delta_psi^*_-q; the subscript h avoids confusing the hole component with the flow v. Let r=delta_R_q. Define

    A=epsilon-Delta+2U n0+U_R R0,   B=U n0,
    E=A-B,   S=A+B,   C=U_R gamma_in n0,
    Z=hbar(omega-v·q)+i eta,   H=hbar omega+i hbar gamma_R. (3)

A,B,E,S are energies, C is energy/time, Z,H are energies. Complexified Fourier r is a real-field component paired with its conjugate at -q; it is not a third bosonic annihilation operator. The Nambu/reservoir dynamical equation is

    i hbar dt (u,v_h,r)^T=L3(q)(u,v_h,r)^T
                              +sqrt(n0)(V,-V,0)^T,
    L3=[[d+A-i eta, B, U_R sqrt(n0)],
        [-B,d-A-i eta,-U_R sqrt(n0)],
        [i hbar gamma_in sqrt(n0),i hbar gamma_in sqrt(n0),
                                                  -i hbar gamma_R]]. (4)

The reservoir row follows directly from B2. It has NO Doppler/convective term. A change to the fluid's coordinates would transform that row too; its laboratory frequency cannot be replaced by omega-v·q while leaving B2 fixed.

For a full inverse in transparent density/phase variables set s=u+v_h and t=u-v_h. For arbitrary energy-equation sources (f_s,f_t,f_r), including possible mathematical reservoir forcing, the frequency matrix is

    T=[[Z,-E,0],
       [-S,Z,-2g_R],
       [-i k_R,0,H]],
    g_R=U_R sqrt(n0),  k_R=hbar gamma_in sqrt(n0),
    Q0=Z²-E S,
    D=det T=H Q0-2i hbar C E.                              (5)

Direct cofactors give the COMPLETE inverse

    T^-1=1/D * [[Z H, E H, 2E g_R],
                [S H+2i hbar C, Z H, 2Z g_R],
                [i k_R Z, i k_R E, Q0]].                  (6)

This is a three-component response to all declared sources, not only a fitted polariton dispersion. Multiplication by T checks every entry: in particular g_R*k_R=hbar*C and the off-diagonal terms cancel. The physical +V probe has f_s=0, f_t=2sqrt(n0)V and f_r=0. Therefore, with

    D_rate=(gamma_R-i omega)Q0-2CE,  D=i hbar D_rate,

    u/V=sqrt(n0)(gamma_R-i omega)(Z+E)/D_rate,
    v_h/V=sqrt(n0)(gamma_R-i omega)(E-Z)/D_rate,
    chi_nn=delta_n/V=2n0 E(gamma_R-i omega)/D_rate,
    chi_RV=r/V=2gamma_in n0 E/D_rate.                       (7)

chi_nn and chi_RV have density/energy units. Probe forcing, density readout and all signs follow from +V; optical-field forcing would use another source vector and the separately derived input-output map. No response is silently declared a PSD.

## 3. Reservoir memory and genuine poles

The exact initial-value reservoir solution is

    r_q(t)=exp[-gamma_R(t-t0)]r_q(t0)
        +gamma_in integral_t0^t exp[-gamma_R(t-s)]delta_n_q(s)ds. (8)

Thus a stationary retarded elimination, after the decaying initial transient and for a stable coupled branch, gives

    r=gamma_in*delta_n/(gamma_R-i omega),
    alpha(omega)=C/(gamma_R-i omega),
    D_pol=Q0-2E alpha(omega),   chi_nn=2n0 E/D_pol.          (9)

The polariton inverse is the frozen2x2 inverse modified by alpha*(1,-1)^T(1,1): both its diagonal A and anomalous B acquire alpha. It is a frequency-dependent causal memory, not merely a real static blueshift or an arbitrary damping substitution. A finite initial reservoir fluctuation in8 is an initial-condition contribution, not a specified quantum-noise covariance.

Elimination9 is algebraically singular at omega=-i gamma_R, but the original inverse6 is the authority. The full poles are zeros of the cubic D, with multiplicities and observable cancellations checked. The bare reservoir denominator is NOT automatically a full coupled-system pole. If C E!=0 then D at H=0 is nonzero; the apparent singularity in9 cancels in7. For example at that complex frequency chi_nn=0 and chi_RV=-1/U_R when U_R,gamma_in,E are nonzero. Conversely if E=0 or a coupling vanishes, factors can be genuine modes while cancelling out of the density/probe transfer. At compensation q=0, chi_nn=chi_RV=0 for this potential probe despite the nontrivial three-component initial-value system. Roots of a response numerator are not stability proofs.

For a stable branch, causal susceptibilities are analytic for Im omega>0 and the real-frequency inverse is the stationary retarded response. For an unstable branch, the algebraic inverse still exists away from poles but a real-frequency stationary spectrum is not justified; the initial-value Laplace contour must lie above growing poles. No noise or physical occupation follows from this pole algebra.

## 4. Exact stability in the material rest frame

Set v=0 and use growth variable lambda=-i omega, so a pole with Re lambda>0 grows. Let a=Gamma/2, R_d=gamma_R,

    Omega_q²=E S/hbar²,  K_q=2CE/hbar².

The full characteristic cubic, up to a nonzero constant factor, is

    P(lambda)=(lambda+R_d)[(lambda+a)²+Omega_q²]+K_q
      =lambda³+c1 lambda²+c2 lambda+c3,
    c1=2a+R_d,
    c2=a²+Omega_q²+2a R_d,
    c3=R_d(a²+Omega_q²)+K_q.                              (10)

All coefficients are real in this rest-frame problem. The cubic Routh table has first column
1,c1,(c1*c2-c3)/c1,c3; therefore strict stability is equivalent to c1>0,c2>0,c3>0 and c1*c2>c3. Equality or a vanishing entry must be handled as a boundary, not called strictly stable. This criterion also states how to test a general detuned branch, where E,S,K may have either sign. A pump-curve slope condition alone is not the complete criterion.

For the repulsive, statically compensated branch

    Delta=U n0+U_R R0=U_eff n0,
    E=epsilon, S=epsilon+2B,
    Omega_q²=epsilon(epsilon+2B)/hbar²>=0, K_q>=0.          (11)

With a>0 and R_d>0, c1,c2,c3 are strictly positive for all q. The sole remaining strict condition is

    K_q < 2a[(a+R_d)²+Omega_q²].                           (12)

Indeed direct expansion gives c1*c2-c3=2a[(a+R_d)²+Omega_q²]-K_q. At equality the polynomial factors (lambda+c1)(lambda²+c2): a nonzero imaginary pair and a negative real root. Above it, the Routh signs have two changes; the positive-coefficient polynomial has no positive real root, so an oscillatory growing pair is present for this violation. Finite-q feedback can therefore destabilize a branch whose q=0 modes all decay.

An independent elementary sign check avoids relying only on the named Routh test here. Positive cubic coefficients exclude nonnegative real roots. If all roots are real they must all be negative. Otherwise write the pair as alpha_g±i b_g and the remaining root as -(c1+2alpha_g)<0 (the latter sign follows from c3>0). Direct multiplication gives c1*c2-c3=-2alpha_g[(c1+alpha_g)²+b_g²], so the margin has exactly the opposite sign to the pair's growth rate. This proves the strict compensated criterion and its oscillatory violation directly.

At q=0, K=Omega²=0 and P=(lambda+R_d)(lambda+a)²: all modes decay when a,R_d>0. If Gamma=0, nonnegative rates force gamma_in=0; that conservative/marginal case is not covered by strict stationarity. At coincident decay rates the characteristic polynomial can have repeated roots/Jordan transients; negative real parts still imply asymptotic decay but do not make a transient amplification bound automatic.

For the entire continuum epsilon>=0,12 is equivalent to

    epsilon²+(2B-C/a)epsilon+hbar²(a+R_d)²>0 for all epsilon>=0,
    C < 2a[B+hbar(a+R_d)].                                (13)

Proof: if C/a<=2B the quadratic is positive. Otherwise its minimum occurs at epsilon=(C/a-2B)/2>0 and equals hbar²(a+R_d)²-(C/a-2B)²/4. This proves13, including its strict boundary. At equality the dangerous epsilon=hbar(a+R_d). If L_c=C/a-2B>2hbar(a+R_d), the exact unstable interval is epsilon_-<epsilon<epsilon_+, with epsilon_±=[L_c±sqrt(L_c²-4hbar²(a+R_d)²)]/2; both endpoints are positive and marginal. No model evaluation is needed to exhibit this finite-q countercase. For a restricted physically admitted q band use12 over that actual band; the all-continuum result is a model statement, not a measured UV-validity claim.

Writing C=beta*gamma_R*B in13 shows why beta alone cannot settle it: rates and interaction/loss energies still enter. The source static fit1.84 is not a stability certificate.

At nonzero flow the polynomial becomes

    P_q(lambda)=(lambda+R_d)[(lambda+a+i v·q)²+Omega_q²]+K_q. (14)

Only the polariton factor is Doppler shifted; the reservoir remains in the laboratory/material frame. Its coefficients are generally complex. The real-coefficient rest-frame Routh test cannot simply be reused with omega replaced by omega-v·q. One must assess the actual flowing roots or the corresponding real +/-q system. This work proves no blanket flowing/horizon stability.

## 5. Static, fast and frozen limits are different

For real laboratory omega, alpha=C/(gamma_R-i omega). In the slow/frozen regime |omega|>>gamma_R it is small only if the actual feedback compared with the polariton inverse is small; a large static beta need not prevent a finite nonzero-frequency frozen limit. At laboratory omega=0, however, alpha=alpha0=C/gamma_R=beta*B and

    chi_nn(q,0)=2n0 E/[(-d+i eta)²-E(S+2alpha0)].            (15)

This is the exact static density response at fixed drive/parameters where its denominator is nonzero, not the frozen-R answer. At q=0 in the rest frame,
I'(n0)=eta²+E0(S0+2alpha0), and15 gives -2n0 E0/I'(n0). Independently differentiating2 with Delta replaced by Delta-V at fixed I yields exactly the same result. Also c3(q=0)=gamma_R I'(n0)/hbar², so a negative static pump slope is unstable; positive slope alone need not satisfy all of10.

The fast-reservoir approximation is alpha≈alpha0, obtained when the laboratory frequencies satisfy |omega|/gamma_R small and the response stays away from poles. It makes delta_R≈(gamma_in/gamma_R)delta_n; it does NOT set delta_R=0. The effective polariton matrix has A+alpha0 and B+alpha0. On11 its dispersion becomes the instantaneous model with epsilon[epsilon+2(B+alpha0)], so c_s,adiabatic²=(B+alpha0)/m rather than the frozen value B/m. This is a declared limiting prediction, not a new measured sound speed.

For laboratory omega=0 followed by a formal conservative limit and then nonzero q→0,11/15 give -1/U_eff when damping is negligible first. At finite damping the q→0 compensated response is instead0. A physically admissible conservative limiting family must respect Gamma=gamma0+gamma_in: one cannot send eta to0 holding a positive gamma_in fixed. An explicit allowed family is gamma0=tau*g0, gamma_in=tau*g_in, gamma_R=tau*g_R with positive fixed g_R and g0+g_in>0; take laboratory omega=0 first, tau→0 at fixed n0 and nonzero q, with the stationary drive/detuning retuned according to1, then q→0. It retains U_eff and yields the preceding -1/U_eff limit. This is a mathematical family, not a measured sweep.

In contrast a comoving-static condition omega=v·q at nonzero flow leaves alpha=C/(gamma_R-i v·q), not generally alpha0. In that same small-rate family at fixed nonzero v·q, alpha→0: the reservoir feedback is frozen, and the polariton comoving-static conservative q limit gives -1/U if the specified limiting path keeps v·q nonzero before taking q→0. Directions with v·q=0 must be treated separately; do not hide this nonuniformity. Laboratory-static flow instead retains alpha0 and, after damping→0 through the stated family, has directional small-q value

    chi_nn -> (n0/m)/[(v·qhat)²-U_eff*n0/m]                 (16)

when the denominator is nonzero; a sonic direction is singular. These are different limit paths, not contradictory compressibilities. All presume n0>0; at n0=0 the density response to this probe vanishes.

A rapid-reservoir limit at fixed alpha0 (hence C=gamma_R alpha0) retains instantaneous feedback and does not converge to frozen delta_R=0. A rapid-reservoir limit at fixed C instead has alpha0→0 and can approach frozen feedback. A slow-reservoir limit with fixed beta*B makes C=gamma_R beta B→0: finite laboratory frequencies freeze, while omega=0 still has alpha0=beta B. Stationary R0 and pump detuning must be tracked in any such parameter family. No limit may silently hold incompatible source parameters fixed.

## 6. Controlled uniform frozen-reservoir response error

Fix a declared compact real frequency/wavevector domain K, a selected homogeneous branch and its actual A(q),B,C,gamma_R. No physical band or measured input bounds are supplied automatically. For a stationary retarded interpretation, additionally require the coupled and comparison branches stable on their admitted dynamical domains; the estimates below by themselves are algebraic inverse bounds. Let

    chi0=2n0 E/Q0,  Sigma=2E C/(gamma_R-i omega),
    m0=inf_K |Q0|>0,
    rho=sup_K |Sigma/Q0|<1.                               (17)

Then the full denominator is Q0-Sigma and, exactly,

    chi-chi0=chi0*(Sigma/Q0)/(1-Sigma/Q0),
    |chi-chi0| <= |chi0| rho/(1-rho),
    sup_K|chi-chi0| <= [2n0 Emax/m0] rho/(1-rho),           (18)

where Emax=sup_K|E|. This is an absolute bound everywhere, including E=0 where both susceptibilities are zero; a ratio divided by chi0 at such a zero is not defined. It is not a relative error bound after silently dividing by a vanishing observable.

For omega_min=inf_K|omega|, a convenient sufficient explicit condition is

    rho <= rho_bound =
      2Emax*C/[m0 sqrt(gamma_R²+omega_min²)] <1.             (19)

Thus away from zero laboratory frequency a slow reservoir at fixed alpha0 gives a controlled frozen limit as gamma_R→0, if m0 and the branch/domain bounds stay uniform. A domain including laboratory omega=0 instead requires small static feedback relative to m0; the source beta fit alone does not establish that. Near a frozen resonance m0 can be tiny, so a small raw rate or frequency ratio is insufficient. Pole shifts/stability still require the separate analysis in §4; a real-axis approximation is not a global pole certificate.

For all polariton source/readout vectors, define G0 as the frozen2x2 energy inverse and k=(1,-1)^T,l=(1,1)^T. The exact polariton inverse is [G0^-1-alpha*k*l]^-1. In Euclidean operator norm ||k*l||=2. If

    r_mat=sup_K 2|alpha| ||G0|| <1,

the Neumann resolvent identity gives
||G_pol-G0|| <= ||G0|| r_mat/(1-r_mat) pointwise with the uniform constant. This supplies an explicit sufficient field/probe-response comparison, not a new reservoir-noise map. The actual induced reservoir probe response obeys

    |chi_RV| <= [gamma_in/sqrt(gamma_R²+omega_min²)]
                  [2n0 Emax/(m0(1-rho))].                 (20)

A frozen-R model discards this variation rather than approximating every reservoir observable by the same relative error. Finite initial conditions add8 and must be separately bounded.

For comparison, the instantaneous/adiabatic approximation uses D_ad=Q0-2E alpha0 and m_ad=inf_K|D_ad|>0. Since

    |alpha-alpha0| =
       alpha0 |omega|/sqrt(gamma_R²+omega²)
       <=alpha0 omega_max/gamma_R,

the same identity18 holds relative to chi_ad with a sufficient feedback ratio
2Emax alpha0 omega_max/(gamma_R m_ad)<1. This is a controlled FAST-reservoir error and is distinct from19. The conditions, detuning branch, density/rate intervals, norms and evaluator errors must be independently established before calling either one a device-qualified useful band.

## 7. What is and is not constructed

This package supplies the actual B1/B2 three-component homogeneous linear response, explicit memory/initial transient, full cubic poles and rest-frame compensated stability, laboratory/comoving distinction, static pump-response control and uniform sufficient frozen/adiabatic response errors. It is stronger than naming beta or fitting a two-branch dispersion; no generic gain reservoir or extra diffusion/backconversion term was substituted for the carrying equations.

B1/B2 are deterministic first-moment equations. They do not supply reservoir jump operators, quantum state, commutator embedding or stochastic/quantum covariance; many fluctuation models share the same mean relaxation law. Assigning an equilibrium FDT or a white positive PSD from gamma_R/gamma_in would be invented input. The accepted independent thermal-Markov port construction84aed74f/review4bba8287 remains a declared different model whose actual microscopic applicability and coupling to this reservoir must be derived, not inferred from equal notation. Treating the density reservoir as a third canonical bosonic mode would require an additional physical construction.

Original E1/D1 response/noise/calibration/scattering objectives remain OPEN BUILD: physical spatial pump/density/profile and boundary conditions, nonlinear/inhomogeneity/linearization errors, actual reservoir rates/interaction/density uncertainty, finite-band optical bath and port coupling, quantum noise/Keldysh/occupation, normalized horizon/greybody scattering, detector transfer/efficiency/PSD convention and independent calibration, and a nonempty identifiable error-controlled frequency/time regime. The ONE shared D1/E1/E2 material-to-spectrum dispersive law and platform/F3/microscopic branches remain separate; no pi/6 coefficient, thermal occupation or Hawking attribution follows from this kernel.

Current lead ownership and existing original finding/roadmap obligations are retained by the r45 notebook and installed REPAIR_DISPOSITION_MAP.md; this ignored package creates no new routing ledger, native lease, sourceholding verification, human date or closure. Independent manual scientific review is next. Any production numerical/native/source/consumer adoption needs its separate ordinary allocation and review. No production import/evaluation, tests/Verify/model runtime, symbolic/numerical software derivation, native/MCP/build/compiler/controller, network/acquisition, source apply, direct Git mutation or lead-notebook write was performed. Python/Poppler were used only for read-only source/text/JSON/hashes/receipt handling. Earlier full-authority read displays were truncated; complete raw subprocess outputs are retained, and the carrying source/prior kernel/current notebook context was reread in bounded visible form rather than claiming unseen output as fully inspected.

## Original checks and preservation

First supported original packet check returned0, fresh=true/changed=[]. Final original check returned1 with changed=["owned-files"]. This is exactly the expected owned-output drift; no source or authority drift was reported. All57 captured original reference/source comparisons also matched on direct final rehash. Neither packet nor historical source/review artifacts was refreshed or rewritten. Full actual argv/cwd/environment/UTC/rc and separate decoded/base64 channels are retained in process.json/evidence.json. These bounded snapshot comparisons do not certify a live lease, full repository state, runtime or physical model.

## CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES

There is no license in B2 to Doppler-shift the reservoir with the polariton fluid; the full material-frame denominator is gamma_R-i*omega. The source static beta ratio does not identify a relaxation time or guarantee stability/frozen response. Fast instantaneous feedback is not frozen delta_R=0. B1/B2 do not supply quantum noise or FDT. A conservative eta→0 family must respect gamma_in<=Gamma, and static/comoving/slow-reservoir limits can fail to commute. These qualifications preserve the actual source rather than replacing it with a convenient generic reservoir or declaring the original physical target complete.
