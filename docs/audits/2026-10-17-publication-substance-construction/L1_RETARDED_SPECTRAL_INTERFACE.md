# L1 retarded tensor spectral interface

Assume a matched stationary equilibrium state and a reciprocal Hermitian tensor channel. Project the once-pair sources into transverse-traceless polarizations after fixing operator normalization, mixing, and off-diagonal weights. Use the response convention (R(t)=+i\theta(t)\langle[Q(t),Q(0)]\rangle) for a source Hamiltonian `H' = −jQ`. After subtracting matched local contact terms and treating any static-only zero mode separately, a positive semidefinite spectral measure on positive frequencies gives

```text
R(z,k) = ∫ 2ν/(ν² − z²) dΣ(ν,k),  Im z > 0
E(Ω,k) = R(iΩ,k)
```

This uses the reciprocal odd commutator spectrum. A nonreciprocal channel needs the signed-frequency matrix and the corresponding momentum reversal. The existing Euclidean normalization provides the source scaling under its hypotheses. It leaves the existence, positivity, and real-time matching of the physical state open.

## Exact positive countercontrol

At fixed momentum, use the static-weight measure `dμ = 2 dΣ/ν`, with frequencies in one common unit. Model A places unit weight at 1. Model B places half weights at 1/2 and 2. Both give `E(0)=1` and `E(1)=1/2` under the kernel `ν²/(ν²+Ω²)`. At Ω=2 they give 1/5 and 19/68 respectively. Their causal time responses are `θ(t) sin t` and `θ(t) [sin(t/2)/4 + sin(2t)]`. The two measures can multiply the same positive semidefinite polarization matrix and have identical local contacts.

For N distinct sampled squared frequencies, form the N-by-(N+1) matrix of sampled kernels at distinct positive atoms. A real null vector perturbs any strictly positive starting weights in both directions by a sufficiently small amount while preserving all samples. The two resulting measures have different retarded poles or residues. With N distinct baseline atoms the corresponding square matrix is an invertible diagonally scaled Cauchy matrix. A small positive spectral band can therefore be added and its sampled contribution canceled by changing the baseline atom weights, which stay positive for sufficiently small added mass. This gives admissible data sets where even the presence of continuous absorption is underdetermined.

## Physical acceptance boundary

The countercontrol applies to finite Euclidean samples in this spectral class. To identify the L1 retarded pole and transport coefficient, the original model still needs a physical matched state, control of contact terms and static modes, and time-dependent evidence. Candidate routes include a controlled real-time correlator, complete Euclidean time data under a justified continuation class, or enough dynamic measurements to test a prospectively justified finite-parametric model. For a flat added static-weight density ε on (0,δ) below the baseline poles, the positive-frequency absorptive response changes from zero to πεΩ/2 in that interval. This is a susceptibility slope. Extracting Γ_H requires isolating the pole and matching the inverse response.

## Independent review

The independent adversarial reviewer `/root/l1_transport_review` verified the causal sign and time kernel, exact atom example, scaled Cauchy invertibility, and positive band compensation. The result is existential for admissible positive spectra with matched contacts. Physical tensor realization and the L1 transport finding remain open.

## Positive transfer test for the literal four-site plus channel

Take either extended axis as Euclidean time, with spacing `a` and
period `2a`. Use the two spatial sites and the same Hermitian matched
plus operator at both times, in the time-reflection-even channel, with a common nonzero real source factor.
The reviewed nearest-time plus numerator vanishes. Translation gives
the same diagonal-separation numerator in both off-diagonal entries.
The Pin symmetry kills the one-point term. At real nonzero `g2` and
where the source-free denominator `Z` is nonzero, the connected
cross-time matrix therefore has zero diagonal and off-diagonal
`d = (-3113/27648) g2^6/Z` times the squared source factor.

A positive thermal transfer representation requires this matrix to be
positive semidefinite. For a spatial linear combination `O_f` of
centered operators, its quadratic form is
`Tr(e^(-aH) O_f† e^(-aH) O_f)/Z_thermal`, the squared Hilbert–Schmidt
norm of `e^(-aH/2) O_f e^(-aH/2)` divided by `Z_thermal > 0`.
A positive semidefinite matrix with zero diagonal has zero
off-diagonal entries. Here `d` is nonzero for every finite nonzero
`Z`. Coincident-time contact subtractions cannot alter the half-period
matrix. If the literal denominator vanishes, its normalized connected
response is undefined.

This obstruction applies to the literal pure-g₂ torus channel with
the specified matching. It leaves physical operator mixing, a different
regulator or state, and the continuum response as separate construction
tasks. See the [exact numerator and nearest-time controls](L1_OFFDIAGONAL_HESSIAN.md).

Independent review verified the half-period Gram identity, translation,
the exact numerator inputs and the support of allowed contact terms.
The obstruction applies for either sign of a real denominator and
also excludes a complex off-diagonal entry in the symmetric matrix.

### Operator mixing and momentum projection

An invertible change of source basis acts by congruence on the
half-period matrix. For real nonzero `d` this preserves a negative
direction. For nonreal `d` it preserves the failure of Hermiticity. Adding more
operators while retaining the tested ones also retains the original
matrix as a principal submatrix. In a positive enlargement any
zero-diagonal source must have zero mixed half-period entries with
every added operator, by the two-by-two principal minor test.

A projection that discards directions is a separate test. On the
two-site spatial torus the normalized constant and staggered modes
have half-period values `d` and `-d`, respectively. Thus for a real
nonzero denominator, precisely one mode passes this positivity test.
In particular the nonzero spatial momentum mode passes if `Z > 0`
under the stated common real source matching. This single inequality
does not establish a positive transfer state. A projected physical
construction needs an independently derived operator and projection,
its full mixed half-period Gram matrix, and time-dependent data.

### Two-time test for the staggered mode

For a centered Hermitian staggered operator, write `A = C(0)` after
matching and subtracting local contacts, and `B = C(a)`. In a finite
faithful thermal model the Lehmann weights give `A = s + Σ w_j` and
`B = s + Σ w_j sech(a ν_j)`, where `s ≥ 0` is static weight and
positive-frequency pairs have `w_j > 0` and `ν_j > 0`. With fixed
`s`, a realization exists for `A = B = s` or `s < B < A`. The
strict case is realized by a two-level transition of gap
`arcosh((A-s)/(B-s))/a` and an independent static centered spin
with variance `s`. Thus a two-time pass permits dynamics but leaves
the retarded spectrum underdetermined.

The staggered half-period numerator is already known. Its equal-time
numerator reduces to the same-site plus square because the nearest-space
term vanishes. The [support enumerator](l1_interacting_support.py) gives
185 multisets (51,930 ordered terms) for that degree-six contraction.
The source-map second derivative multiplied by the metric one-point
function vanishes by Pin symmetry. An independently matched local
quadratic contact can still shift `A`, so the raw equal-time Hessian
alone cannot qualify this test.

Independent review derived the half-period factor from each unordered
Lehmann pair and verified the one-gap construction. It also reproduced
the 185 unique support words and their multiplicities with a separate
ordered count. The equal-time value and its contact subtraction remain
open.

### Finite frequency contrast

Translation invariance and the exact nearest-time and nearest-space
zeros give the four Fourier eigenvalues of the literal Hessian as
`H_on + (-1)^(n_t+n_x) d`, with each Fourier index in `{0,1}`.
Here `H_on` is the same-site entry and `d` is the normalized
diagonal-separation entry. Consequently the frequency contrast at
zero spatial momentum, between temporal characters one and zero, is
`4303411200/(11270712996006127 g₂²)` in the stated source coordinates.
At staggered spatial momentum the contrast has the opposite sign.
A term supported strictly at coincident lattice time is independent
of the temporal character and cancels in this contrast. The two
discrete samples still leave the retarded spectrum underdetermined.

Write the full same-site raw numerator as `n₀ g₂⁶`, the verified
normalization as `D g₂⁸`, and the common real source match as `α`.
For a contact `C` subtracted from the matched equal-time value, the
two-time inequality gives the upper bound
`C ≤ α² (n₀ - 3113/27648)/(D g₂²)`.
Equality leaves only a static contribution. Finite-frequency weight
requires a strict inequality and independently fixed static weight
`0 ≤ s < B`. The literal source enters the exponent linearly and
has zero bare second derivative. The contact in this bound is a
separate matching term whose coefficient must follow from the
physical source coupling.

The full bare staggered equal-time value is now
`A_raw = α² (10179913/32)/(D g₂²)`. With zero matched contact the
ratio `B/A_raw = 3113/8795444832` lies strictly between zero and one.
Thus the bare projected pair admits a finite-gap scalar thermal
realization. The actual matched contact, operator, static component,
and physical state still require independent construction.

### Regulated metric source and its quadratic contact

For an explicit comparison model, take an N-component real Gaussian
with inverse propagator `K_j = pᵀ exp(-2jE) p + r`, where `E` is a
constant traceless, Frobenius-unit symmetric polarization. Hold the
coordinate momentum ball fixed. Differentiating the Gaussian log
partition function gives `N/2 Tr[G K' G K' - G K'']`, where
`K' = -2pᵀEp` and `K'' = 4pᵀE²p` at zero source. In four dimensions
the angular averages of `(pᵀEp)²` and `pᵀE²p` are `p⁴/12` and
`p²/4`. The static response density is therefore

`(N/6) ∫ p⁴/(p²+r)² - (N/2) ∫ p²/(p²+r)`,

with both integrals over the fixed ball using `d⁴p/(2π)⁴`.
The second term is the quadratic contact from this source action.
If the cutoff ball is instead defined by `pᵀ exp(-2jE) p ≤ Λ²`, the
determinant-one momentum substitution makes the constant-source
partition function independent of `j`. The cutoff boundary
contributions then cancel the fixed-ball response. This calculation
fixes the contact for each specified comparison model. Matching the
literal lattice shear to a microscopic metric action and regulator
remains open.

For `r > 0`, the fixed-ball radial integrand is
`-N/(96π²) d[p⁶/(p²+r)]/dp`. The response is exactly
`-N Λ⁶/[96π²(Λ²+r)]`. The moving-cutoff cancellation concerns
constant sources. A time-dependent contact would require the full
regulator prescription. Independent review verified the Gaussian
derivatives, both angular averages and the momentum substitution.

### Time-dependent spatial shear with a fixed spatial cutoff

For a separate comparison with continuous Euclidean time, use
`K_j = -∂_τ² + pᵀ exp(-2j(τ)E)p + r` and a fixed three-dimensional
spatial momentum ball. Here `E` is spatial, traceless and has unit
Frobenius norm. At zero temperature let `e = √(p²+r)`. The two
linear source vertices contribute `2N(pᵀEp)²/[e(Ω²+4e²)]` to the
frequency-space Hessian integrand, since the Fourier transform of
`G_p(τ)² = exp(-2e|τ|)/(4e²)` is `1/[e(Ω²+4e²)]`.
The quadratic vertex contributes `-N pᵀE²p/e`, using the equal-time
propagator `1/(2e)`. This term is instantaneous under the specified
source action and cutoff.

Angular averaging gives the response density
`N ∫ [4p⁴/(15e(Ω²+4e²)) - p²/(3e)] d³p/(2π)³`.
Subtracting the zero-frequency response cancels the contact and gives
`-N Ω²/15 ∫ p⁴/[e³(Ω²+4e²)] d³p/(2π)³`.
The contrast is strictly negative for nonzero real Ω, positive N and
positive cutoff. This comparison is at zero spatial momentum and uses
a spatial cutoff. The earlier four-dimensional cutoff calculation
uses a different regulator. The microscopic lattice operator match
remains open.

Independent analytic review reproduced the Fourier transform, vertex
factors, angular moments and sign. For `r > 0` the reviewer also
obtained the zero-frequency response
`−NΛ⁵/[30π²√(Λ²+r)]` by a radial total derivative and the
low-frequency coefficient
`−N/60 ∫ p⁴/e⁵ d³p/(2π)³` multiplying `Ω²`.

For the retarded convention `χ_R(t) = −i θ(t) ⟨[O(t),O(0)]⟩`
with Fourier transform using `exp(+iωt)`, the dynamical sector is
the negative of the continued Euclidean connected response. At
positive frequency its weight is `−Im χ_R = N p_*⁵/(60π e_*)`,
where `e_* = ω/2` and `p_*² = ω²/4 − r`. It is supported on
`2√r < ω < 2√(Λ²+r)`. Independent review reproduced the delta
function Jacobian `8p_*` and the retarded sign. The instantaneous
quadratic term has no spectral discontinuity.

### Translation constraint on the uniform metric source map

Consider a real source map that commutes with spatial translations,
uses the same time-local map at each Euclidean time, fixes zero
source, and couples only to the literal plus channel. At zero source
its first derivative commutes
with the exchange of the two spatial sites. Hence it sends the
uniform metric source into the uniform lattice direction and the
staggered source into the staggered direction. The mixed second
derivative of the source map between times 0 and a is zero by time
locality. Any separate coincident-time quadratic source term also
vanishes in that mixed derivative.

For real nonzero g₂ the verified pure-g₂ denominator is positive.
The uniform direction therefore has a negative half-period Hessian
entry d. A nonzero real uniform matching coefficient multiplies
that entry by its square and preserves its sign. A zero coefficient
instead removes the linear response. Thus this class of source maps
cannot turn the positive staggered control into a positive uniform
metric response. A candidate using a staggered internal carrier
must derive how physical translations act on that carrier. A
candidate using additional operators must derive the physical
uniform operator and test its full mixed Gram data. Independent
review verified the chain rule and identified the need for the same
map at both times. With different real coefficients the cross-time
factor would be their product, which could reverse the sign.

### Mixed-channel acceptance test

At half-period write the candidate uniform metric operator as
`M = α L + X`, with `L` the literal uniform plus operator, real α, and
`X` the net additional uniform contribution. For Hermitian
operators with a real symmetric half-period form, set
`d = B(L,L) < 0`, `b = B(L,X)`, and `c = B(X,X)`.
A necessary scalar test for matching is
`2αb + c ≥ α²|d|`. A coincident-time term cannot contribute to
any entry of this test.

If the proposed physical observable space includes both M and X,
and α is nonzero, it also contains L = (M − X)/α. Its half-period
Gram matrix then has a negative direction regardless of b and c.
A projected construction may retain M alone, but it must derive
that restriction from the physical observable algebra and test M
with the other retained observables. Passing the scalar inequality
only tests a single vector. For a finite set of additional retained observables
with Gram block G and cross vector v, positivity requires G ≥ 0,
v in the range of G, and B(M,M) ≥ v† G⁺ v. These conditions follow
by minimizing the Gram quadratic form over the additional
observables, including its nullspace. Independent review verified
the expansion, negative direction, and singular-block criterion.
These checks establish positivity only on the tested half-period span.

### Stability under a small second action coupling

At fixed real nonzero g₂, the finite-volume partition function and
the first and mixed second source derivatives are polynomials in g₁.
Berezin saturation makes the exponential expansion finite, and Haar
integration acts linearly on each coefficient. The normalized
connected uniform half-period response is therefore a rational
function of g₁ near zero, since the verified partition value at zero
is strictly positive. Its real part is continuous and strictly
negative at zero. It remains negative on an open interval about
zero, even if reality has yet to be established for all mixed
coefficients. A Hermitian positive transfer realization would have a
real nonnegative value there, so the same literal uniform channel
fails throughout that interval. This argument gives neither a
quantitative radius nor a conclusion at arbitrary g₁ or at larger
volume. Independent review verified the continuity argument and the
saturation bounds. Homogeneity gives the response as g₂⁻² times a
rational function of g₁/g₂², so the open interval can be taken in that
ratio at this fixed volume.

In the four-site degree-32 extraction, an action monomial
`g₁^m g₂^n` with k metric insertions obeys `2m+n+k=8`.
The simultaneous Pin sign reversal of both action couplings
preserves the metric insertions, so only even `m+n` survive.
Consequently m has the parity of k. The denominator has only
g₁ degrees 0, 2, 4, each one-point numerator has degrees 1, 3,
and the mixed two-point numerator has degrees 0, 2. The
connected response is therefore even in g₁ and differs from the
pure-g₂ response by O(g₁²) at fixed nonzero g₂. Computing the
allowed coefficients would give a quantitative sign domain. Independent review verified the Pin premise and the parity refinement.

### Coefficient certificate for the finite-volume interval

Write `x = g₁/g₂²` and `y = x²`. After extracting the powers of g₂,
write the partition polynomial as `z(y) = z₀ + z₂y + z₄y²`, the
mixed second derivative as `u(y) = u₀ + u₂y`, and the two first
derivatives as `x v(y)` and `x w(y)`, with v and w linear in y.
The normalized response is `g₂⁻² P(y)/z(y)²`, where
`P = zu − yvw` has degree at most three and `P(0) < 0`.

This also gives a certificate without assuming reality away from
zero. Form the real polynomial
`Q(y) = Re[P(y) conjugate(z(y))²]`, with `Q(0) < 0`.
Let `S_z` be the sum of the absolute nonconstant coefficients of
z and `S_Q` the corresponding sum for Q. For
`0 ≤ y ≤ min(1, z₀/(2S_z), |Q(0)|/(2S_Q))`, omit any ratio with
zero denominator. Then `|z(y)| ≥ z₀/2` and `Q(y) ≤ Q(0)/2 < 0`,
by bounding each positive power of y by y. The response has
negative real part because its real part is `g₂⁻² Q(y)/|z(y)|⁴`.
The certificate requires the actual coefficients or verified
upper bounds on the two sums. No numerical radius is claimed.
Independent review verified the coupling powers and the real-part bound.

### Conservative explicit interval from exterior coefficient norms

Use the sum of absolute exterior coefficients at fixed links. This
norm is submultiplicative under wedge multiplication. Each coframe
has norm at most 16, since its two hopping blocks have 16 entries
each, and each entry of an anticommutator of two unitary matrices
has modulus at most 2 before the factor 1/4. Coincident blocks
obey the same bound by the triangle inequality. Each curvature
trace has modulus at most 4, canceled in the bound by the
S2 prefactor 1/4. Thus the four-site action vertices
have norms bounded by `4·24·16⁴` for S4 and
`4·24·16·16²` for S2, using all internal pairs in S2.
Each uniform plus source insertion uses two quadratic coframe
products at each of two sites, with norm at most `4·16²` for
the unnormalized sum. Unit normalization can only decrease it.
All three bounds are below `2²⁴`.

Each coefficient in z, u, v or w is a top coefficient with at most
eight such factors, divided by the action factorials and integrated
against normalized Haar. Its modulus is at most `B = 2¹⁹²`.
The coefficient sums satisfy `||z||₁ ≤ 3B`, `||u||₁ ≤ 2B`,
and `||v||₁, ||w||₁ ≤ 2B`. Hence `||P||₁ ≤ 10B²` and
`||Q||₁ ≤ 90B⁴ < 2⁷⁷⁵`. The known pure-g₂ values give
`z₀ > 1` and `|Q(0)| = z₀³ |u₀| > 1`.
The preceding certificate therefore applies for
`|g₁/g₂²| ≤ 2⁻⁴⁰⁰`, since `y ≤ 2⁻⁸⁰⁰`. This bound is deliberately
coarse and concerns only the specified four-site regulator and
uniform source normalization. Independent review verified the
coframe, action and source norms and the resulting interval.
