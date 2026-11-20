# E1 next construction: an explicit quantum loss model and fluctuation spectrum

Author: Physics Publication Remediation lead. **Independent manual declared-model review accepted.** Reviewer `/root/publication_figures`, report SHA256 `26436ee0c750af6345800f141a189cadefcb23eedb1ecf56f58f05b5d7905d68`, accepted the full author construction `abe18e37af2833ebebaead2fac480475970c8d81541903725c5b617fd492e0b7`; the lead rechecked all52 bound inputs. This source copy changes the author-stage status only; mathematical content remains as reviewed. This advances the accepted homogeneous frozen-reservoir GPE response kernel (source22deb33f; independent9cae8993) by specifying a quantum generator and state of its input. It is a declared quadratic fluctuation model, not a controlled derivation of the actual nonlinear/reservoir device, a horizon/Hawking spectrum or experimental calibration. No production formula, native declaration, gate or sourceholding field is changed.

## 1. Fixed model and conventions

One normalized real standing-wave fluctuation mode has bosonic d with [d,d†]=1. The real background amplitude is sqrt(N), N>0, and the linear observable is X=sqrt(N)(d+d†), a mode occupation fluctuation. A physical density/current/optical detector additionally requires volume, spatial-mode and transfer matching; do not call this normalized X a calibrated density PSD. A and B are real energies, gamma>0 is a loss rate, eta=hbar*gamma/2, and the actual quadratic Hamiltonian is

H2=A d†d+(B/2)(d†²+d²).

Take the explicit thermal Markov generator

L rho= -i[H2,rho]/hbar + gamma(n_b+1) D[d]rho + gamma n_b D[d†]rho,
D[c]rho=c rho c† - {c†c,rho}/2, n_b>=0.

The drift damping is gamma/2 independently of n_b. The bath here is specified with constant n_b over the declared model, not inferred from the response, an assumed Hawking occupation or equilibrium FDT. The corresponding input satisfies

<b(t)b†(t')>=(n_b+1)delta(t-t'),
<b†(t)b(t')>=n_b delta(t-t'), <bb>=0.

The equivalent linear Langevin equation is

i hbar d_t (d,d†)^T = L (d,d†)^T + i hbar sqrt(gamma)(b,b†)^T,
L=[[A,B],[-B,-A]]-i eta I.

The second noise entry has the same +i sign: conjugate the first ordinary time-derivative equation and then multiply by i hbar. This fixes the Nambu sign convention. L has eigenenergies -i eta +/-sqrt(A²-B²); a stationary stable Gaussian process exists exactly when A²+eta²>B². At equality there is a marginal mode and no stationary frequency-spectrum claim is made. The stable quadratic Markov model has stationary covariance given by its convergent propagator/noise integral, not a postulated thermal Gibbs state.

## 2. Retarded response and actual noise spectrum

Use f(omega)=integral dt exp(i omega t)f(t). Add +V(t)X to H2. With Y=(d,d†)^T and J=diag(1,-1), the source vector is sqrt(N)(1,-1)^T V. Therefore

R(omega)=[hbar omega I-L]^-1,
chi_XV(omega)=2N(A-B)/D(omega),
D(omega)=(hbar omega+i eta)²-A²+B².

This is the response to +V X and its sign is fixed by the commutator equation. The stationary unsymmetrized spectral density is defined by

S_XX(omega)=integral dt exp(i omega t)<X(t)X(0)>.

Because X is Hermitian, it equals the spectrum obtained from <Y(omega)Y†(omega')> and v†Y=X with v=sqrt(N)(1,1)^T. The independent bath construction gives

S_XX(omega)=hbar² gamma v† R diag(n_b+1,n_b) R† v.

Writing x=hbar omega and E=A-B,

v†R = sqrt(N)[x+i eta+E, x+i eta-E]/D,
S_XX(omega)=hbar² gamma N { (n_b+1)[(x+E)²+eta²] + n_b[(x-E)²+eta²] } / |D|².

The symmetrized spectrum is

S_sym(omega)=[S_XX(omega)+S_XX(-omega)]/2
 = hbar² gamma N(2n_b+1)[x²+eta²+E²]/|D|².

This is a two-sided angular-frequency spectrum: variance=integral d omega S_sym/(2pi). X is dimensionless, so S has units of time. It is nonnegative by its Gram form. One-sided/Hz conventions or a detector PSD require explicit conversion. The difference

S_XX(omega)-S_XX(-omega)=4 hbar² gamma N E x/|D|²=-2 hbar Im chi_XV(omega)

checks the quantum commutator/retarded normalization independently of bath occupation.

## 3. Compensated repulsive homogeneous specialization

For the declared compensated mean-field background, set B=U N>=0 and A=epsilon+B with epsilon>0 the kinetic-mode energy. Then E=epsilon and A²-B²=epsilon(epsilon+2UN)>0. The stable density-quadrature response and spectra follow by substitution, without importing a thermal relation. In this specialization,

S_sym/[-hbar Im chi_XV]
 =(2n_b+1)[x²+eta²+epsilon²]/(2 epsilon x), x>0.

It generally is not coth(x/(2 k_B T)) for a fixed temperature. In particular its large-x growth in this mathematical white-noise model differs from a finite-temperature coth limit. Do not use that large-x calculation to claim the physical Markov approximation holds to arbitrarily high frequency. Even at n_b=0, finite loss gives off-resonance fluctuations; response alone does not identify their physical origin as Hawking radiation. The finite-band validity of this quantum Markov reduction remains a separate construction.

A Doppler/comoving frequency shift can be introduced only with its spatial-mode/bath convention established; this note does not silently import a laboratory-static limit. At epsilon=0 the specialization's division by epsilon is unavailable. Zero-loss limits require their order and observation/state preparation: gamma=0 itself has no unique dissipatively selected stationary state.

## 4. Remaining full-strength construction and acceptance

This calculation explicitly supplies a quantum bath and derives a fluctuation spectrum for a declared quadratic model. Still owed: actual physical open generator/reservoir and state reduction from the source device; validity of linearization, nonlinear/Hopfield/mode/cutoff remainder; spatial horizon/in-out scattering and transmission; actual density/optical coupling and detector transfer; calibration/independent background covariance; a useful nonempty interval and identifiable error-controlled estimator. The input n_b is not a fitted physical noise result.

Independent review must rederive the generator-to-Langevin drift/noise convention, stationary stability, Fourier/Nambu normalization, both spectra and commutator identity, dimensions and every limit qualification. Native and numerical implementation require ordinary ROOT admission. This note does not close E1, D1 physical FDR/noise, platform classification, G4/G5/G11 or the original publication charter.
