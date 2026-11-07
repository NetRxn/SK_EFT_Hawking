# E1 acoustic-phonon bath: colored quantum noise and a controlled white-band limit

17 October 2026. Author: Physics Publication Remediation lead /root, accepting scientific construction responsibility. Parent: original E1/D1 physical noise/readout BUILD and Phase5/Phase5w W10a. This source-linked analytical construction has scoped independent acceptance, review SHA256 c5a1538d333115f71f5194fac7988e0a61f1fb655e5e9d6f2267dafc7aaa0cee. No production implementation, native proof, device calibration, horizon, total detector PSD or finding closure is claimed.

## Source and model boundaries

Lead directly read Stepanov2019 publisher Supplementary Notes1 and8, including the carrying PDF pages10-13; page13 was visually inspected. Note8 supplies density/deformation-potential coupling to acoustic phonons and a linear stochastic-response treatment. Its constant spectrum is adopted using a high-temperature approximation. Its vector/polarization response and spatial aperture matter to the observed signal. These are source facts, not a physical white-band error proof. The following derivation is original here, with additional assumptions displayed explicitly.

The supplement is the official companion of DOI10.1038/s41467-019-11886-3, SHA256 bccc2fb309b70d361bda5a3f4293d50cf860747acace40cfa937b3066bdf1580. Held Falque AppendixB1/B2/B3 (PDF page9, personally visually inspected) gives coherent polaritons coupled to a material dark-reservoir rate and a static blueshift ratio. Neither that ratio nor the deterministic rate fixes the reservoir noise covariance or all phonon parameters. No2019 sample temperature, linewidth, coupling or reservoir time is silently transferred to the Falque device.

The source writes a difference b-b-dagger with a phase-bearing coupling. We instead fix an explicitly Hermitian potential and its coupling phase below. This is a specified convention, not a claimed verbatim equality of the source's G and our g. The source's classical normal thermal correlator is also distinct from our quantum symmetrized spectrum, whose vacuum term is retained.

## 1. Thermal harmonic bath with explicit units and Fourier normalization

Take a periodic in-plane area A [m^2] and thickness L [m]. Wavevectors q,k_z have units m^-1; all omega,Omega are angular frequencies [s^-1]. With bosonic [b_Q,b_Q' dagger]=delta_QQ', define

H_B=sum_Q hbar Omega_Q b_Q dagger b_Q,
V_q(t)=sum_k g_(q,k)[b_(q,k) exp(-iOmega_(q,k)t)+b_(-q,-k) dagger exp(+iOmega_(q,k)t)],       (1)

where Omega_(-q,-k)=Omega_(q,k)>0 and g_(-q,-k)=g_(q,k)*. Thus V_q dagger=V_-q, and g,V have energy units. The density coupling is H_int=sum_q N_-q V_q, N_q=integral_A exp(-iq.r) n(r) d^2r, a dimensionless number mode. In a thermal Gaussian free-bath state, <b dagger b>=n_B(Omega) and <bb dagger>=n_B+1, n_B=(exp(beta hbar Omega)-1)^-1. Mean bath potential is zero.

Equations below are exact for the specified free-bath input. Initially take finitely many wavevectors or an integrable ultraviolet form factor. No well-posedness of the full unbounded nonlinear driven polariton-plus-bath evolution is asserted from these free-bath identities. Continuum statements require the displayed integrals to converge; singular thresholds are not smoothed away.

Use the two-sided angular-frequency convention
S^>_V(q,omega)=integral_R dt exp(iomega t)<V_q(t)V_-q(0)>.
For an inversion-symmetric bath define J_q(Omega)=sum_k |g_(q,k)|^2 delta(Omega-Omega_(q,k)), Omega>0. J has units energy^2*time. Direct contraction gives

S^>_V(q,omega)=2pi J_q(omega)[n_B(omega)+1] for omega>0,
S^>_V(q,-omega)=2pi J_q(omega)n_B(omega) for omega>0.                         (2)

Thus positive- and negative-frequency spectra are not equal. The symmetrized spectrum, defined as half their sum, is

S^sym_V(q,omega)=pi J_q(|omega|) coth(beta hbar |omega|/2).                   (3)

For one oscillator this follows by integrating exp[i(omega-Omega)t] and exp[i(omega+Omega)t], including the full2pi delta normalization. At T=0, the negative-frequency normal-ordered absorption contribution vanishes but (3) has the nonzero vacuum half-sum. No classical thermal-only noise can reproduce that zero-temperature commutator.

For perturbation +f(t)V_-q the retarded response convention is D^R_q(t)=-(i/hbar)theta(t)<[V_q(t),V_-q(0)]>. Integration with the retarded +i0 prescription yields

D^R_q(omega)=(1/hbar)integral_0^infty dOmega J_q(Omega)
 [1/(omega-Omega+i0)-1/(omega+Omega+i0)].                                  (4)

Im D^R_q(omega)=-pi J_q(omega)/hbar for omega>0, and opposite sign at negative frequency. Therefore

S^sym_V(q,omega)=-hbar coth(beta hbar omega/2) Im D^R_q(omega).                (5)

This is a thermal relation for the specified phonon bath. It is NOT an equilibrium FDT for the coherently pumped, lossy polariton/dark-reservoir system. D^R has energy units; S^sym has energy^2*time; hbar Im D^R has the same units. In particular D^R(0)=-(2/hbar)integral J_q(Omega)/Omega dOmega when finite. Dropping this dispersive backaction requires a separate approximation or renormalization contract, not merely a temperature limit.

## 2. A declared deformation-potential continuum and its threshold

To make frequency dependence computable, additionally ASSUME one isotropic longitudinal acoustic branch Omega_(q,k)=u sqrt(|q|^2+k^2), u>0 [m/s], uniform material mass density rho [kg/m^3], a real effective deformation energy D_eff, and normalized nonnegative confinement density w(z), integral w dz=1. Its form factor F(k)=integral w(z)exp(ikz)dz has F(0)=1 and |F|<=1. If a constant exciton fraction is used, D_eff can be parametrized as |X|^2 D; its actual value and momentum dependence must be independently matched to the device. Define, rather than infer from the source,

|g_(q,k)|^2 = hbar D_eff^2 sqrt(|q|^2+k^2)/(2 rho A L u) |F(k)|^2.           (6)

The finite-area normalization is essential. The expression has energy^2 units. In the L->infinity mode-density limit, sum_k -> L integral dk/(2pi). For omega>u|q| put k0=sqrt(omega^2-u^2|q|^2)/u. The two roots +/-k0 of omega=u sqrt(q^2+k^2) have Jacobian u k0/(omega/u). Consequently

J_q(omega)= hbar D_eff^2 omega^2 /[2pi rho A u^3 sqrt(omega^2-u^2|q|^2)] |F(k0)|^2, omega>u|q|;
J_q(omega)=0, 0<omega<u|q|.                                               (7)

Equation(7) follows by inserting (6) into J and evaluating the delta function; no fitted noise amplitude is chosen. At q=0 it reduces to the Ohmic expression

J_0(omega)=hbar D_eff^2 omega/(2pi rho A u^3)|F(omega/u)|^2.                  (8)

At fixed nonzero q and D_eff!=0, the square-root threshold in (7) is necessarily unsuppressed: k0 tends to0 and the normalized confinement form factor has |F(0)|^2=1. The singularity is integrable in frequency but is not uniformly bounded. Suppression would require a different coupling model, such as an additional vertex zero outside assumption(6). At frequencies below u|q| there is no noise from this branch, even at high T. General quantum-well confinement, multiple acoustic branches, anisotropy, phonon escape and momentum-dependent Hopfield coefficients modify (6)-(8); the source's general G cannot be replaced by these assumptions without matching them.

## 3. Quantitative high-temperature and white-band error

For x>=0, 1<=x coth x<=1+x^2/3, using the continuous value at0. For completeness, x cosh x-sinh x has derivative x sinh x>=0 and vanishes at0. Also h(x)=(1+x^2/3)sinh x-x cosh x has derivative x[x cosh x-sinh x]/3>=0 and vanishes at0. These prove both inequalities without a series truncation.

For T>0 and 0<|omega|<=omega_max define x_max=hbar omega_max/(2k_B T). Then

S^sym_V(q,omega)=[2pi k_B T J_q(|omega|)/(hbar |omega|)] [1+e_T(omega)],
0<=e_T(omega)<=x_max^2/3.                                                  (9)

This controls the thermal approximation relative to its own classical spectrum; it does not make J_q/omega constant.

If w has finite variance sigma_z^2, then |F(k)|^2=E cos(k(Z-Z')) for independent Z,Z' with density w. Since 1-cos y<=y^2/2,

0<=1-|F(k)|^2<=k^2 sigma_z^2.                                            (10)

For q=0 set S_0=D_eff^2 k_B T/(rho A u^3), a constant with units energy^2*time. Equations(3),(8)-(10) yield the finite-band bound

|S^sym_V(0,omega)/S_0-1| <= (omega_max sigma_z/u)^2+x_max^2/3               (11)

for 0<|omega|<=omega_max; the omega->0 limit is included by continuity. Assume D_eff!=0 to use the ratio; for D_eff=0 all spectra vanish and use absolute bounds. To prove (11), write the ratio f(1+e_T),0<=f<=1, use |f-1|<=a_F and f e_T<=e_T. Thus white noise follows from BOTH thermal and confinement scale separation for this specified q=0 model.

For a finite momentum-frequency band, explicitly assume 0<omega_min<=omega_max<infinity, q_max>=0, |q|<=q_max, omega_min<=|omega|<=omega_max and 0<=b=u q_max/omega_min<1; let G=(1-b^2)^-1/2 and a_F=(omega_max sigma_z/u)^2. Then

|S^sym_V(q,omega)/S_0-1| <= (G-1)+G[a_F+x_max^2/3].                       (12)

Indeed the geometric factor g=(1-u^2 q^2/omega^2)^-1/2 lies in[1,G], and |g f(1+e_T)-1|<=g-1+g(1-f)+g f e_T. As b->1 this bound diverges, reflecting an actual threshold. High temperature alone does not control that limit. Extending the white approximation to the entire real line would discard the finite model range and is not justified by(11)-(12).

## 4. Connecting to the material-reservoir response without inventing a total PSD

Let chi_N^0(q,omega) be the independently derived linear response of the scalar polariton-plus-material-reservoir system to an applied ENERGY potential +V, using number Fourier mode N_q. If a previous GPE susceptibility chi_n was for density rather than total number, chi_N^0=A chi_n. Do not drop A or replace the laboratory reservoir frequency by the comoving frequency.

Assume the FULL feedback-coupled linear model is causal and stable and the required bath integrals converge; stability of the bare chi_N^0 alone is insufficient. A real-frequency-band bound in(14) does not establish global coupled stability. Under these premises, with harmonic bath response (4), eliminating the bath gives

chi_N^eff=chi_N^0/[1-chi_N^0 D^R_q],
S_NN,ph^sym=|chi_N^eff|^2 S_V,free^sym.                                   (13)

Here delta V_q=V_q,free+D^R_q delta N_q follows directly from H_int and retarded bath response, then delta N=chi_N^0 delta V. Equation(13) is the phonon-input contribution under that linearization and independent thermal input. It is not the total polariton covariance: radiative vacuum/thermal inputs, dark conversion noise and cross-correlations, pump fluctuations and their channel transfer remain required. Ignoring those missing channels does not establish CCR preservation or positivity of the complete system. It also does not turn phonon-driven polariton fluctuations into Hawking radiation.

A useful controlled omission criterion is sup_band |chi_N^0 D^R_q|<=a<1. Then

|chi_N^eff-chi_N^0|<=|chi_N^0| a/(1-a),
| |chi_N^eff|^2-|chi_N^0|^2 |<=|chi_N^0|^2 (2a+a^2)/(1-a)^2.                (14)

The second estimate follows from |chi_eff-chi0|(|chi_eff|+|chi0|), yielding the tighter a(2-a)/(1-a)^2, which is bounded by the displayed expression. It remains valid, but this a must actually be estimated from (4) and the system resolvent. Small bare coupling is not uniform near a system pole or acoustic threshold. No such numerical a is supplied for the real device here.

For any nonnegative calibrated spectral weighting W(q,omega), a pointwise relative bound e from(11) or(12) gives |integral W S_exact-integral W S_0|<=e integral W S_0 over the stated band. W can include a justified |chi_eff|^2 and detector weighting, but an unknown W is not a calibration. Combining a uniform bath bound with(14) is possible only when both hypotheses hold. The actual polarization/collection aperture/readout must be propagated before comparing to detected optical counts or a usable SNR interval.

## 5. What this construction pays down, and what remains owed

This construction replaces an unqualified white-bath assumption with an explicit source-linked quantum bath, normalization, colored spectral density, retarded memory and quantitative finite-band error under declared material/confinement assumptions. It supplies thermal and vacuum controls and concrete nonwhite countercases. The mean material dark-reservoir response is a different memory source; neither is substituted for the other.

Remaining original BUILD obligations: actual mode projection and absolute deformation/phonon parameters; source-qualified anisotropy/multiple branches/form factors and material temperature for the target device; quantum/stochastic dark conversion and backconversion; complete polariton channel noise/CCR and nonlinear reduction error; actual inhomogeneous horizon/scattering/transmission, polarization and aperture transfer; independently calibrated detector/background and nonempty physical error/SNR band. There is no empirical prediction, FDT for the pumped system, universal quadratic dispersive law, native proof, main integration, G4/G5/G11 acceptance or scientific deferral in this note.

CONTRADICTIONS BETWEEN THE BRIEF AND THE SOURCES: A static dark blueshift ratio does not determine a dynamic rate or quantum noise. A thermal high-temperature limit alone does not establish a white momentum-frequency spectrum. The source's stochastic normal thermal correlator is not its quantum vacuum completion. The carrying hysteresis inequality printed near source Eq19 is not used; its apparent sign inconsistency is not silently propagated.
