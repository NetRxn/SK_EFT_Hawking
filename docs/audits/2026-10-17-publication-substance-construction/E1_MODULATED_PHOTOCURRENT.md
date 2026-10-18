# E1: modulated optical probe to a counted photocurrent and analyzer observable

Author: Physics Publication Remediation lead. Independent full manual scientific review: publication_d2_proposal_review, SHA256 cd8cdef6ce8eec04fe4e960cdabd4951592f4cad5255f26ae18675fa722d7d06. Original E1 physical-response/noise/detection-band BUILD is retained. This is an independently reviewed manual construction under explicit receiver assumptions, not a calibrated apparatus model, native proof, measured Hawking signal or completed detection band. Native, physical-device and publication acceptance remain separate.

## 1. Carrying source and three different frequency scales

The lead directly read the held Falque arXiv2311.01392v2 body, especially PDF page4 sectionIII, and personally viewed that complete rendered page. The held13-page preprint is not silently identified with a later journal body. Its coherent probe is a second CW laser, roughly two orders below pump intensity, intensity-modulated at5MHz. For each probe wavevector, the optical probe frequency scans400GHz around the pump. A reciprocal-space pinhole selects transmitted light sent to a photodiode; a spectrum analyzer filters its electronic signal around the modulation frequency in zero-span mode, with nominal resolution bandwidth300Hz. The source uses transmission resonance maxima to identify excitation branches. It separately describes off-axis interferometry for the fluid phase. It does not establish that the spectral readout is a balanced homodyne receiver or that its300Hz setting is a measured noise PSD or known ENBW.

Define angular optical detuning delta=omega_pr-omega_p, modulation Omega=2pi times5MHz, and ordinary electronic frequency f_m=Omega/(2pi). The actual sidebands sample optical response at delta+nOmega. Neither delta nor the laboratory pump-frame argument of the material reservoir response is generally equal to Omega. The nominal300Hz analyzer setting is a third scale. The source's plotted f-f_pump in GHz is an optical detuning coordinate. The derivation below does not use0.81K as a noise PSD or infer detector sensitivity from these settings.

## 2. Optical response including the pinhole, idler and pump leakage

Assume a stationary pumped background, a stable small-signal optical response about it, and sufficiently narrow optical sidebands that photon-flux normalization and a frequency-flat quantum efficiency eta with0<=eta<=1 are meaningful over the admitted optical band. Let K be the Hilbert space of transmitted spatial/polarization modes actually integrated by the photodiode, with its usual inner product (antilinear in the first argument). A pinhole followed by a multimode photodiode need not select a single coherent mode. Its aperture/propagation is a linear map into K; subsequent square-law detection integrates the norm in K. Orthogonal modes add intensities; coherent spatial overlap is retained by the inner product.

For a discrete coherent input spectrum alpha_q, a general linearized pumped response has detected coherent amplitudes

    c_q = T(q) alpha_q + U(q) alpha_{-q}^* + p 1_{q=0}.                 (1)

Here T and U include actual input coupling, background/horizon retarded propagation, aperture and output collection. U permits pump-induced conjugate/idler conversion. The vector p is collected coherent pump leakage; no separate local oscillator is presumed. For a probe triplet alpha_{delta+nOmega}, n=-1,0,1, the candidate frequency set contains0 and both signs of those three detunings. Coincident frequencies are grouped by adding their vectors before evaluating intensities. The real input/output operators, T/U coefficients, spatial profile, weak-probe error and collected pump amplitude still need physical derivation/calibration; writing (1) does not supply them.

The accepted material-reservoir construction provides an internal retarded kernel. Its deterministic response can enter

    T(q)=T_bg(q)+C(q) K(q)^{-1} B(q),
    K(q)=hbar q I-L_0-Sigma_R(q),                                 (2)

with compatible energy-valued matrices and proper domains. In the homogeneous material model Sigma_R carries the laboratory-frequency factor1/(gamma_R-iq). Actual boundary/input/output maps B,C and aperture are still required. A homogeneous3-by3 density response is not itself an optical transmission or a calibrated quantum scattering matrix. The independently constructed phonon and quadratic-noise models also retain their declared-model scopes; they must be transported through actual channels, with commutators and all loss inputs accounted for.

## 3. Exact coherent square-law harmonic and degeneracies

For the declared finite spectrum write c(t)=sum_q c_q exp(-iqt), with ||c_q||^2 in photons per second. Let e>0 be the elementary charge. This coherent contribution equals the full optical mean only for a coherent detected output state; general output populations add the incoherent mean flux specified in section6. The coherent contribution to the mean photocurrent is

    i_bar(t)=e eta ||c(t)||^2
            =e eta sum_{q,r} <c_r,c_q> exp[-i(q-r)t].              (3)

Thus the coefficient multiplying exp(-iOmega t) is exactly

    I_Omega=e eta sum_{q-r=Omega} <c_r,c_q>.                       (4)

The full current contains I_Omega exp(-iOmega t)+its conjugate; its sinusoidal amplitude is2|I_Omega|, not |I_Omega|. Formula(4) includes idler self-beating, coherent pump interference and cross-branch terms whenever their actual frequency differences equal Omega. It remains valid at delta=0 or2delta an integer multiple of Omega after coincident lines are grouped. A formula that simply adds separate signal and idler intensities misses such coherent degeneracies. Finite-window leakage when differences are close rather than equal is handled in section7.

For a norm-preserving embedding in the direct sum of distinct frequency-mode spaces, the frequency-shift partial isometry S has norm at most1, and I_Omega=e eta <c,S c> with an appropriate shift orientation. If a controlled optical-amplitude approximation gives ||d||<=epsilon in that direct-sum norm, then

    |I_Omega(c+d)-I_Omega(c)|
       <= e eta [2 ||c|| epsilon + epsilon^2].                    (5)

This supplies a concrete way to transport a proved amplitude/reduction bound into the harmonic. It does not bound unknown device coefficients by declaration. Its norm is the distinct-frequency coefficient norm, not a claim about unresolved finite-time lines.

## 4. Explicit scalar control: modulation is not the carrier detuning

Consider only a single collected mode, no admitted idler or pump-overlap contribution, a linear scalar T and three input amplitudes alpha_0=alpha, alpha_+=alpha_-=m alpha/4 with0<=m<1, choosing the modulation phase as the time origin. This triplet is the first-order field expansion of intensity modulation Phi_in(t)=|alpha|^2[1+m cos(Omega t)]; it is not an exact finite-m intensity identity. Any omitted higher sidebands require a separate bound such as(5).

Set T_0=T(delta), T_+=T(delta+Omega), T_-=T(delta-Omega). Direct substitution in(4) gives

    I_Omega=e eta m |alpha|^2/4
              [T_0^* T_+ + T_-^* T_0].                          (6)

When T is flat across these sidebands, I_Omega=e eta m|alpha|^2|T_0|^2/2. Its real-current amplitude is therefore e eta m|alpha|^2|T_0|^2, relative to the unmodulated carrier baseline e eta |alpha|^2|T_0|^2. For the EXACT truncated triplet, the period-averaged photon flux is |alpha|^2|T_0|^2(1+m^2/8), and its AC/DC fraction is m/(1+m^2/8), not exactly m at finite m. The intended intensity-modulation fraction m is recovered to first order, or is an exact baseline-normalized harmonic for this triplet. Its second-harmonic intensity coefficient is |alpha|^2|T_0|^2 m^2/16. These checks fix the factor of two without discarding the finite-modulation correction. For a pure delay T(q)=a exp(iq tau), the bracket is2|a|^2 exp(iOmega tau), as required for the delayed modulation; the optical detuning phase cancels. Replacing all three response arguments by5MHz in a detuning scan would fail both the scan's physical meaning and the resonance structure.

Suppose T is continuously differentiable on the entire sideband interval and |T'(q)|<=L there. Then |T_+-T_0| and |T_--T_0| are at most Omega L, giving

    |I_Omega-e eta m|alpha|^2|T_0|^2/2|
       <= e eta |m| |alpha|^2 |T_0| Omega L/2.                   (7)

This is a conditional modulation-following bound, not evidence that5MHz is adiabatic in the actual device. For constant B,C and T_bg, (2) yields

    |T'(q)| <= ||C|| ||K(q)^{-1}||^2 ||K'(q)|| ||B||,
    K'(q)=hbar I-Sigma_R'(q),
    ||Sigma_R'(q)|| <= ||J||/(gamma_R^2+q^2)                    (8)

when Sigma_R(q)=J/(gamma_R-iq). Frequency-dependent B,C,T_bg add their product-rule derivative terms. Stability alone need not give a useful resolvent bound for a nonnormal matrix; a uniform singular-value/resolvent gap over the whole sideband interval is needed. Unknown gamma_R cannot be inferred from the source's static beta=1.84.

## 5. What a zero-span power analyzer measures

Let h be a real linear current-to-voltage response (including the selected RF filter), with v(t)=integral h(t-s)i(s)ds and H(f)=integral h(u)exp(+i2pi f u)du, matching the exp(-iOmega t) harmonic convention. The coherent output at f_m has coefficient V_Omega=H(f_m) I_Omega. At a calibrated real load R_L, its time-averaged sinusoidal power is

    P_tone=2 |H(f_m) I_Omega|^2/R_L.                             (9)

A zero-span RF power measurement need not retain the complex phase of I_Omega. Equations(4),(6) are theoretical intermediates for its power; the source does not supply phase-sensitive data merely by naming a photodiode. Actual analyzer gain, impedance and displayed-power normalization must be calibrated rather than identified with an arbitrary lock-in convention.

For stationary additive noise with one-sided voltage PSD S_vv^(1)(f), f>0, the integrated noise power in an additional known analysis response A(f) is

    P_noise=(1/R_L) integral_0^infinity S_vv^(1)(f)|A(f)|^2 df.    (10)

One may instead absorb A into H for current noise; it must not be counted twice. Only with a sufficiently flat local PSD can this be approximated using

    B_eff=integral_0^infinity |A(f)|^2 df / |A(f_m)|^2.            (11)

The source's nominal300Hz resolution bandwidth does not specify the filter shape, equivalent noise bandwidth, averaging time, detector responsivity, photon flux, pump rejection or actual PSD. A measured transmission resonance identifies an excitation response, not automatically spontaneous emission, entanglement or a Hawking-specific excess-power contrast.

## 6. Shot term, normally ordered fluctuations and PSD conventions

Under the declared ideal photon-counting model, take a COHERENT DETECTED OUTPUT STATE and let Phi(t)=||c(t)||^2. Its detected events form a Poisson process of intensity eta Phi(t). Coherent incident illumination alone does NOT imply this output-state condition: nonzero conjugate Bogoliubov response U together with physical quantum input ports can produce displaced squeezed or other noncoherent outputs even from coherent/vacuum inputs. Equation(1) determines their coherent mean, not their full photon flux or counting statistics. For the ideal impulse current i(t)=e sum_j delta(t-t_j),

    E i(t)=e eta Phi(t),
    Cov[i(t),i(t')]=e^2 eta Phi(t) delta(t-t').                  (12)

The normal-order shot term is indispensable even if a classical field-noise model is zero. For a general optical state in ideal direct detection, define the TOTAL mean collected photon flux mu(t)=<b_out(t)^dagger b_out(t)>_K, including all collected incoherent populations. With c=<b_out> and d=b_out-c, it decomposes as mu=||c||^2+sum_j<d_j^dagger d_j> over an orthonormal collected-mode basis, with finite total mean photon flux assumed; it is not generally equal to the coherent Phi. Replace the shot coefficient in(12) by e^2 eta mu(t). A separate normally ordered connected TOTAL intensity correlation contributes e^2 eta^2 C_N(t,t'). Adding C_N while retaining only ||c||^2 in the shot term is incorrect, even when the coherent mean vanishes. C_N is defined by the appropriate normally ordered four-field intensity correlation minus mu(t)mu(t'), not by subtracting just coherent intensity. Let mu_inc=mu-||c||^2. Its harmonic also contributes to the TOTAL mean current: I_Omega,total=e eta[sum_{q-r=Omega}<c_r,c_q>+(mu_inc)_Omega] whenever that periodic harmonic decomposition exists. Thus(4),(6),(9) give the coherent-field harmonic/power control; the full apparatus mean tone additionally requires mu_inc and its modulation response, or a justified bound showing its harmonic negligible. The coherent probe does not eliminate this obligation. That correlation is not fixed by a retarded response or equilibrium bath FDT in a pumped system. Physical validity/positivity of the total counting covariance must be shown; a negative excess contribution does not mean negative total noise. Dark counts, electronic noise and their relevant cross-covariances need their own evidence.

For stationary coherent flux Phi_0, define C(tau)=integral_{-infinity}^infinity S^(2)(f) exp(-i2pi f tau)df. Equation(12) gives S_ii^(2)(f)=e^2 eta Phi_0=e i_0, and for the real-current one-sided PSD at positive f,

    S_ii^(1)(f)=2 e i_0.                                        (13)

These are A^2/Hz conventions; they are not angular-frequency PSDs with an unmentioned2pi factor. Collected coherent pump leakage contributes to i_0 and shot noise even if it does not beat at Omega. Countercase: two orthogonal collected spatial modes do not coherently interfere, but each adds its own photon flux and shot term. A matched mean-field energy scale alone supplies neither quantity.

## 7. Finite-window estimator and cyclostationary covariance

To quantify a harmonic theoretically, first take a real nonnegative integrable time window w with W=integral w>0 and w square integrable. For ideal current define

    Z=(1/W) integral w(t) i(t) exp(iOmega t)dt.

For the coherent spectrum(3), its exact mean is

    E Z=e eta sum_{q,r} <c_r,c_q>
             W_hat(q-r-Omega)/W,
    W_hat(nu)=integral w(t)exp(-i nu t)dt.                        (14)

For a general output state the full mean is instead E Z=(e eta/W) integral w(t) mu(t) exp(iOmega t)dt, so covariance-generated population harmonics are included, not mistaken for zero just because the coherent mean vanishes. Equation(14) is its coherent contribution. This retains DC, negative-harmonic, nearby-line and pump/idler leakage. A rectangular interval of integer modulation periods removes DC and nonresonant INTEGER-multiple harmonics exactly, but does not remove arbitrary optical-beat detunings. Thus finite-window nonaliasing or an explicit leakage bound is required; an assertion that all nonresonant beats average away is false at finite time.

For a general linear detector/filter followed by this functional, write the effective complex current weight g(s)=W^{-1} integral w(t) exp(iOmega t) h(t-s)dt. Ideal Poisson counting gives exact variance and pseudovariance

    V=E|Z-EZ|^2=e^2 eta integral Phi(s)|g(s)|^2 ds,
    Q=E[(Z-EZ)^2]=e^2 eta integral Phi(s)g(s)^2 ds.                (15)

Consequently Var(Re Z)=(V+Re Q)/2, Var(Im Z)=(V-Re Q)/2, and Cov(Re Z,Im Z)=Im Q/2. For a general optical state, FIRST replace Phi by the TOTAL mu in BOTH shot integrals of(15), then add the double integrals of e^2 eta^2 C_N(s,s') against g(s)g(s')^* or g(s)g(s'), respectively, plus qualified detector/background correlations. Equation(15) requires square-integrable effective weights and finite integrals; detector transients and observation boundaries are included through g, not discarded.

For h=delta, a rectangular integer-period window and constant Phi_0, V=e^2 eta Phi_0/T and Q=0. With periodic intensity, Q probes its2Omega component and need not vanish. Even the exact three-sideband coherent field has an order-m^2 second harmonic. Using a stationary scalar shot PSD as the whole quadrature covariance without checking this cyclic component can therefore be wrong. The source's power analyzer is not asserted to implement Z; (14)-(15) specify a checkable theoretical estimator and its noise, and can be transported to an explicitly characterized instrument.

Two independent quantum counterchecks enforce the total-flux replacement. For a collected thermal SINGLE temporal mode with mean photon number n and counting its complete pulse, c=0, integral mu=n, and the integrated normally ordered connected intensity is n^2. The detected charge variance is e^2(eta n+eta^2 n^2), not just e^2 eta^2 n^2. For ONE photon in a normalized wavepacket psi, mu(t)=|psi(t)|^2 and C_N(t,t')=-mu(t)mu(t'). Counting the whole pulse yields e^2 eta(1-eta), the Bernoulli variance. A coherent-only shot term would instead yield the impossible negative -e^2 eta^2. More generally this state gives V=e^2[eta integral mu|g|^2-eta^2|integral mu g|^2]>=0 by Cauchy-Schwarz and0<=eta<=1. These are exact analytic countercontrols of the declared counting model, not new device or runtime measurements.

For an actual on/off contrast D, the independent-sample simplification Var(D)=Var(on)+Var(off) is valid only after independence is established; generally one must subtract2Cov(on,off). Background subtraction does not remove shot noise by fiat and does not make excess noise necessarily positive.

## 8. A concrete uncertainty route and the still-open physical band

If the complex calibrated voltage coefficient has uncertainty |dV|<=epsilon_V, its coherent power error satisfies

    |dP_tone| <= (2/R_L)[2|V| epsilon_V+epsilon_V^2].             (16)

Equations(5),(7),(8),(14) transport actual scattering/reduction/modulation/window errors into this budget; transfer and calibration errors must also be included. A usable detuning interval would require actual validity bounds, actual on/off physical contrast, calibrated collection/transfer/background covariance, and a declared statistical error criterion whose full bias plus noise is smaller than that contrast. No nonempty interval is established by defining that inequality. The present note does not compute a detector significance or replace the missing device scattering/PSD with an ideal one-shot SNR.

## 9. Acceptance and next substantive action

The construction supplies an explicit optical-input-to-square-law-to-RF-observable chain for the apparatus type actually described by the carrying source, with idler/pump/spatial overlap, factor-of-two controls, modulation-following bound, analyzer-power/ENBW distinction and finite-window counting covariance. Its original physical E1 parent remains OPEN. Next derive or calibrate the actual optical boundary/aperture maps and material noise inputs, bind the spatial/horizon response with uniform errors, and use the actual analyzer filter/efficiency/flux/background data to test for a nonempty identifiable band. No scientific infeasibility, reduced scope, historical ownership absence, sourceholding acceptance or human verification is inferred.
