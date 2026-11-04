# L1 retarded tensor spectral interface

**Verified normalization correction.** Conditional Haar projection
retains singleton link dependencies. Independent enumeration confirmed
5,718 transferable normalization words and 1,812 transferable cross
words. Only four checkerboard words transfer by this census. The
independent all-64 direct closed checkerboard replay at `76704b872`
gave 5039025/8192 and the literal control gave 136051531/221184,
both exactly real. The earlier numerical subtotal survives. The
four newly excluded mixed-cycle words already have direct closed
coverage. This supersedes the earlier transfer counts and restores
the downstream denominator, dressed response and coupling bound.
The raw composite numerators were computed separately.


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

### Candidate curvature-dressed operator from coframe shear

A different source prescription can be tested on the existing action.
At each site replace the world-index coframe by
`T(j) = exp(jE) T`, with real traceless symmetric spatial E extended
by zero on time. Hold the plaquette holonomies and integration
measure fixed. The S4 density is unchanged because it is a
determinant and `det exp(jE) = 1`. Write the local S2 density as
the curvature-weighted bilinear `B(T,T)`, with B symmetrized
in its two arguments. Its first source derivative is
`2 B(ET,T)` and its second is
`2 B(E²T,T) + 2 B(ET,ET)`. For a spatially uniform slice source,
sum these expressions over the sites of that slice. The second
expression gives the local quadratic insertion. At distinct slices
the Hessian instead measures the connected correlation of the two
curvature-dressed first derivatives.

This source acts on the action rather than inserting the literal
quadratic metric composite. It supplies a concrete uniform operator
and contact to evaluate in the finite regulator. Because it holds
curvature holonomies fixed, its identification with a background
metric variation still requires a derivation. Its Gram matrix and
continuum normalization are open. Independent review verified the determinant
invariance and both source derivatives. The full action inserts g₂
times each first or second derivative above.

For diagonal plus polarization with entries (0,0,e,−e), each S2
term has source multiplier exp[j(λ_μ+λ_ν)] on its coframe pair.
Only mixed extended/transverse curvature planes carry a nonzero
weight, since the complementary curvature axes have opposite sum.
At pure g₂ the distinct-slice numerator therefore uses two tagged
mixed-plane vertices and six ordinary S2 vertices. An exact
transverse exchange symmetry sending E to −E would kill the
one-point terms. This symmetry must be checked on the oriented
finite action and measure before using that simplification.

The pure-g₂ calculation can reuse the exact normalization support.
For a supported multiset w of eight S2 terms, let C_w denote its
existing Haar–Berezin weight including the action factorial.
For time slice t define A_t(w) as the sum of λ_μ+λ_ν over all
occurrences centered on that slice. The deformed partition function
divided by g₂⁸ is exactly

    Σ_w C_w exp(j_0 A_0(w) + j_a A_a(w)).

The shear rescales each term by a scalar and preserves its center
parities and site degrees, so the 6,451-word support remains complete.
The half-period connected response is

    Σ_w C_w A_0 A_a / Σ_w C_w
      − (Σ_w C_w A_0)(Σ_w C_w A_a)/(Σ_w C_w)^2.

This weighting includes the multiplicity of repeated vertices
automatically. In the diagonal same-slice derivative A_t² includes
both tags on one occurrence, which is the quadratic contact, and
tags on distinct occurrences. The weights C_w are signed and the
formula does not assume a positive probability measure. The
sector subtotals alone do not determine these moments because
A_t can vary within a sector. Exact weighted evaluation is in progress. Independent review
verified the reweighting, factorial treatment and contact term.

A support-only pass using `component_multisets()` from
`l1_normalization_coverage.py` reproduced 6,451 words. For time
axis zero, slice is the low bit of the center site index. Setting
e=1 for the count, add `−(λ_k+λ_l)` at the center slice for each
occurrence with curvature labels k,l. Exactly 2,160 words have
nonzero cross-time multiplier. They split into small components
192, mixed chain 128, private repeated 504, private paired 458,
correlated six 32, correlated eight 494, mixed cycle 160,
checkerboard 64, X1 64 and Y1 64. All other sectors contribute
zero to the raw cross moment. The count tests support only.
It supplies neither the weighted contraction nor a sign.

For pure g₂, swapping the two length-one transverse directions
permutes their link variables at each site and leaves the time
slices fixed. The world epsilon in S2 contributes a minus sign
under that relabeling. All surviving words have eight S2 factors,
so the resulting sign is positive on the saturated coefficient.
The link Haar measure is unchanged and no fermion sites are
permuted. The swap exchanges the transverse diagonal shear
entries, sending both A_t to −A_t. Consequently each raw
first source moment vanishes at pure g₂. This argument leaves
the product A_0 A_a invariant and does not fix its sign.
Independent review verified the orientation sign, Haar invariance
and all ten support counts.

The first exact weighted subtotal is `8999/96` for the 192
small-component words, using e=1. The calculation applied the
existing component evaluator and top wedge product to each word,
divided by its repeated-label factorials and component moment
denominators, and multiplied by `A_0 A_a`. The subtotal awaits
independent reproduction. The other nine sectors remain open.

The mixed-chain replay reproduced the unweighted sector sum 325
over 256 words. At unit shear amplitude, 64 same-singleton words
contribute 326 and 64 opposite-singleton words contribute −324,
giving an exact weighted subtotal of 2. The weighting was applied
to the original labels before using translated contraction
representatives. Independent reproduction of this subtotal is
pending.

The private-paired run grouped 458 selected words by their existing
canonical contraction plan, curvature-reduction count and factorial.
Within each of the 18 groups it summed the signed original-label
weights before multiplying by the exact plan contraction. The
weighted subtotal is −72441 at unit shear amplitude. Together
with the two preceding subtotals this covers 778 of the 2,160
contributing words. Independent reproduction and the seven
remaining sectors are open.

The private-repeated replay covers 1,120 normalization words,
of which 504 carry a nonzero cross-time multiplier. Across 11
contraction plans it reproduced the unweighted sum `8071653/32`
and gave the weighted subtotal `−121389/2` at unit shear amplitude.
This brings the evaluated cross-time support to 1,282 of 2,160
words. The subtotal awaits independent reproduction.

The existing correlated contraction evaluator gave weighted
subtotals `652/3` (32 six-component words) and `13453205/108`
(494 eight-component words), grouped in 19 plans. The checkerboard
replay found the same multiplier 16 on all 64 words, giving
`136051531/13824` from its verified unweighted sector. X1 and Y1
each have multiplier −4 on all 64 words. Their orientation sums
are `31543/10616832` and zero respectively, with four layouts per
orientation sum. Their combined weighted subtotal is
`−31543/663552`. These weighted subtotals await independent
reproduction. Only the 160 contributing mixed-cycle words remain
to evaluate.

The fresh mixed-cycle replay reproduced both nonzero plane
coefficients, `6947573/1769472` and `147830509/84934656` per
16 orientations. The weighted layout multiplicity is 32 for
each class, yielding `481314013/2654208` with zero imaginary part.
Summing all ten weighted sectors gives `1563566443/884736`.
The one-point terms vanish by the verified transverse exchange.
Dividing by the exact source-free normalization gives the
connected uniform half-period response
`33773035168800/11270712996006127 > 0` at e=1 and pure g₂.
This establishes the scalar sign in the specified regulator
subject to independent reproduction of the weighted contractions.
Independent review reproduced the checkerboard, wire and mixed-cycle
weights and the rational assembly. The other six weighted contractions
still await independent reproduction. The physical match and positivity
on any larger retained observable space remain open.

### Mixed entry with the literal uniform operator at pure g₂

The mixed half-period entry of the literal metric insertion and
the curvature-dressed insertion vanishes by the same Pin change
of variables used for the literal one-point test. Both insertions
have Grassmann degree four. The dressed insertion counts as one
S2 factor and changes sign under Pin, while the literal insertion
is invariant. Saturation requires six ordinary S2 factors in
addition to the tagged one, so the total of seven S2 factors is
odd. The mixed numerator changes sign and vanishes after
Haar–Berezin integration. The literal one-point term is also zero.
There is no shared contact at distinct times. Thus on the span of
these two uniform observables, the mixed half-period Gram is
diagonal. Its dressed direction passes the scalar test given the
assembled weighted sum, and the enlarged span containing the
literal direction still fails positivity. Independent review verified the selection rule at pure g₂.

For a retained single real combination `M = α L + β X` of the
literal uniform plus operator and the unit-amplitude dressed
operator in these source coordinates, the zero mixed entry gives
the exact scalar sign criterion

    α²/g₂² ≤ β² · 1563566443/99616.

This follows from the two diagonal entries and is conditional on
the assembled dressed subtotal. If the physical source retains
both operators separately, the negative literal direction remains.
The inequality constrains the required source match without fixing
its coefficients or constructing a thermal representation.

### Equal-time dressed product and local contact support

For slice zero, let `B_0` be the sum of the squares of the individual
occurrence weights on that slice. The quadratic action insertion
has weight `B_0`, while the equal-time product of first insertions
has weight `A_0² − B_0`. Their sum is the Hessian weight `A_0²`.
The first moment is zero at pure g₂. The equal-time two-point test
uses the product with the local action contact removed.

On the same exact support with e=1, the counts of nonzero weights
are 4,092 for the contact, 3,964 for the product and 2,770 for the
Hessian. In particular X2, Y2 and diagonal mixed words contribute
to the product and contact separately even though they cancel in
the Hessian. An equal-time calculation restricted to nonzero
Hessian weights would therefore omit required contributions.
These are support counts. Exact coefficient sums and independent
verification remain open.

The checkerboard and wire sectors have constant (contact, product)
weights within each class at e=1. The 64 words in each class give
(4,12) for checkerboard, (2,2) for X1 and Y1, and (2,−2) for X2
and Y2. Applying these weights to their exact normalization sums
gives partial raw contact `19591665287/7962624` and partial raw
operator product `58774395085/7962624`. The other equal-time
sectors and independent reproduction remain open.

### Independent cross-time reproduction

At `24960a1c`, the independent reviewer reproduced all six
remaining weighted subtotals. The replay independently counted
original-label weights before symmetry reduction and reused the
existing exact contraction kernels. Together with the earlier
checkerboard, wire and mixed-cycle checks, this verifies the
ten-sector assembly. The result supplies a positive half-period
scalar for the specified dressed operator. Physical metric matching
and equal-time thermal tests remain open.

The exact small-component equal-time replay evaluated 368 words.
At e=1 it gives raw contact `2924675/96` and raw operator product
`1466837/48`. The same pass reproduced the cross-time control
`8999/96`. These equal-time subtotals await independent reproduction.

The private-curvature replays reproduced both cross-time controls.
Their equal-time (contact, product) subtotals are
`(4303005/8, 3856815/8)` for private repeated and
`(301833, 229392)` for private paired. All 160 diagonal-mixed words
have `A_0=0` and `B_0=2`. Their previously verified normalization
sum `−40213/16` therefore gives contact `−40213/8` and product
`40213/8`. These equal-time results await independent reproduction.

The last (contact, product) pairs are `(650,652)` for mixed chain,
`(30943735159/191102976,3710873777/191102976)` for mixed cycle,
`(652/3,1304/3)` for correlated six and
`(38961401/108,26207303/54)` for correlated eight.
All four reproduce their cross-time controls. The full raw contact
is `234940237883935/191102976` and the full raw operator product is
`237137274962921/191102976`. The contact-subtracted normalized
equal-time value is `23713727496292100/11270712996006127`.
The ratio of half-period to equal-time product is
`337730351688/237137274962921`, strictly between zero and one.
The finite pair passes the scalar two-time compatibility test.
Independent reproduction, physical operator matching and
reconstruction from further time samples remain open.

### Conditional low-frequency weight bound

In any positive thermal realization of the contact-subtracted
pair, normalize the Lehmann weights by the equal-time value A,
including static weight as an atom at frequency zero. The
half-period ratio is the expectation of `sech(aν)` under this
probability measure. For every cutoff `ν_c ≥ 0`, monotonicity
of sech yields

    weight([0, ν_c]) ≤ min(1, (B/A) cosh(a ν_c)).

In particular the static fraction is at most B/A. At unit shear
in the four-site pure-g₂ model, the assembled ratio gives a bound
of about 0.1424 percent on the static fraction, conditional on
such a realization. The scalar one-gap model saturates the
low-frequency bound at its gap. The bound does not determine
the spectrum or establish a positive physical state. Independent
review verified the bound and its one-gap saturation.

Independent reproduction confirmed all 13 sector contributions,
the separate contact and product totals, and the compatibility
ratio. The replay independently computed occurrence squares and
ordered-pair weights before symmetry reduction and reused the
existing exact kernels. This verifies the scalar finite pair.

### Coframe-only variation versus simultaneous pullback

Write the local continuum-form curvature term as the wedge
contraction `ε^{klμν} F_{kl} T_μ T_ν`, with internal contractions
suppressed. For a world-index matrix A acting on each covariant
slot, transform both `T → AT` and `F → AFAᵀ`. The contraction
then gains exactly `det A`, by the four-index alternating-tensor
identity. With `A=exp(jE)` and traceless E this gives zero first and
second derivatives pointwise. For diagonal E the same check is
termwise: the curvature multiplier is
`exp(j(λ_k+λ_l))`, the coframe multiplier is its inverse, and
their product is one.

This is an algebraic pullback control. At finite lattice spacing,
plaquette holonomies need a separately specified response to a
physical background metric. The fixed-holonomy dressed operator
varies only the coframe slots and gives the nonzero response
calculated above. The simultaneous pullback calculation therefore
identifies a curvature variation that would cancel it. Physical
matching must derive which curvature response the regulator
actually implements. Independent review verified the alternating
tensor identity and this distinction.

A geometric test of this control is to keep a smooth connection
one-form fixed and move the edges of an infinitesimal plaquette.
For constant diagonal A, its k,l tangent vectors become
`a exp(jλ_k) e_k` and `a exp(jλ_l) e_l`. The leading holonomy
increment is their oriented area times the curvature component,
`a² exp(j(λ_k+λ_l)) F_{kl}`, with errors of order a³ for smooth
bounded connection and curvature derivatives near the base point.
Thus moving the edges produces the compensating curvature
multiplier at leading order if the coframes are also evaluated
on the moved tangent basis. This tests a geometric change of
basis at fixed fields. It does not specify the functional variation
at fixed lattice coordinates, including the measure and regulator,
needed for a physical stress operator. The two constructions
can already differ in their leading response. Independent review
verified the area factor for the oriented loop convention. Bounds on
source derivatives require a remainder uniform with its first two
source derivatives. The pointwise small-loop estimate supplies no
bound on the integrated quantum response.

### Source contract for a background extension

The held primary [Diakonov 2011, arXiv:1109.0091v1](https://arxiv.org/abs/1109.0091v1)
specifies the Euclidean grid in §III, the independent link and
plaquette variables in Eqs. (13) and (17), the composite tetrad
in Eq. (23), the lattice interactions in Eqs. (24)–(25), and the
Berezin and normalized Haar integrals in Eqs. (26)–(27).
The metric is a tetrad composite. These lattice equations specify
the zero-source measure and action. They supply no independent
background-metric family whose first and second variations would
select between the literal composite insertion, the fixed-holonomy
coframe variation, and a simultaneous pullback. Those prescriptions
agree at zero source and give different derivatives. A physical
extension needs an independent matching condition on the
background family and its source-dependent measure or regulator.

### Local Legendre transform for the specified dressed source

Let W(j) be the finite log partition function for the two
slice sources, and let C be the normalized quadratic contact.
With contact subtraction `W_sub(j)=W(j)−C(j_0²+j_a²)/2`,
the zero-source Hessian has diagonal A and off-diagonal B,
where A is the verified equal-time product and B the verified
half-period response. Time translation fixes the equality of the
diagonal entries. Since A>B>0, its eigenvalues A+B and A−B
are strictly positive. In a real neighborhood where W_sub is
defined, the inverse function theorem gives a local source
as a function of the contact-subtracted conjugate response
`φ=∇W_sub(j)`. The Legendre transform
`Γ(φ)=j·φ−W_sub(j)` then has Hessian
`(A²−B²)⁻¹ [[A,−B],[−B,A]]` at the source-free point.

The [fixed-link reality identity](L1_OFFDIAGONAL_HESSIAN.md#reality-of-fixed-link-top-coefficients)
applies to every labelled action coefficient. The dressed source
multiplies each coefficient by a real exponential for real j,
so the finite sum is real analytic. The verified positive
partition value at zero gives a neighborhood with positive Z
and real analytic W. This establishes a local inverse response
for the specified finite source prescription.
Converting it to the physical L1 susceptibility requires the
operator normalization, volume and time units, and a background
source match. Independent review verified the contact subtraction,
reality argument and inverse Hessian.

### Exact dependence on a curvature-source prescription

For the diagonal shear, define a local algebraic extension
indexed by real c. Multiply the curvature trace in plane k,l
by `exp(c j_t (λ_k+λ_l))` at its center slice t, while
retaining the coframe shear and the zero-source measure.
This gauge-inert scalar preserves the transformation law of the
underlying term, including its existing local covariance defect.
It does not assert that the rescaled trace comes from a
deformed compact-group plaquette. The complementary coframe
indices give the inverse multiplier at c=1, so every term
has net multiplier `exp((1−c) j_t (λ_μ+λ_ν))`.
Consequently the finite partition functions obey the exact identity

    Z_c(j_0,j_a) = Z_0((1−c)j_0,(1−c)j_a),

where the subscript zero labels the coframe-only prescription.
The first insertion scales by 1−c, and the quadratic contact,
equal-time product and half-period response all scale by (1−c)².
For c≠1 the scalar compatibility ratio is unchanged. At c=1
both samples vanish and their ratio is undefined. Thus the
positive finite sign test cannot determine the normalization
of the background source. An independent background matching
condition must fix that coefficient. Independent review verified the
exact identity and derivative scaling under the fixed measure.

Even a first-order matching condition leaves independent
contact data. For example, adding
`κ(j_0²+j_a²)/2` to the finite exponent preserves the zero-source
measure and all first action insertions. It shifts the diagonal
log-partition Hessian by κ, with no change to the distinct-slice
Hessian or to the operator product obtained after subtracting the
full quadratic insertion. This field-independent local term is a
source counterterm. Its freedom shows why a background matching
condition must also specify the quadratic source convention.

### Gauge average as an exact finite control

The existing literal coefficient controls exhibit a local Wilson-law
covariance failure. For the finite regulator one can nevertheless
form the invariant weight `P(exp S)(q)=∫dg exp(S(g·q))`, using
independent normalized Spin(4) Haar at each site. The link Haar
and site Berezin measures are invariant under this change of
variables. For every gauge-invariant insertion O, changing
variables separately at each g gives

    ∫dq O(q) P(exp S)(q) = ∫dq O(q) exp(S(q)).

Thus projection at the weight level preserves the zero-source
partition function and invariant correlators, including any
source whose full insertion is invariant. For a general source
the joint weight must be projected with its source present.
Projecting the action before exponentiating is a different
operation. The projected weight can be nonlocal or signed and
does not establish reflection positivity. In particular this
identity cannot transfer the dressed-operator result to a
different covariant action. Independent review verified the measure
change of variables and both projected source derivatives.

In particular, let `W_0=exp S(0)`, `J_t=∂_t S(0)` and
`K_{tu}=∂_t∂_u S(0)`. Before integrating over lattice variables,
the projected source derivatives are

    ∂_t P(W)|₀ = P(W₀ J_t)
    ∂_t∂_u P(W)|₀ = P(W₀ (J_t J_u + K_tu)).

This identity needs no division of Grassmann-valued weights.
Replacing the second line by a product of separately averaged
insertions would discard their shared gauge-orbit correlations.
Even when `K_tu=0` for distinct slices in the literal source,
the projected joint derivative is the orbit average of their
product with the original weight. The positive-state test for
a covariant observable must use its own specified insertion
and measure. This calculation does not identify it with the
projected response.

### Local covariance of the closed-path source candidate

Use the endpoint convention of the existing
[coefficient reference](l1_full_action_reference.py):
`U_{xy} → g_y U_{xy} g_x⁻¹`. In the closed ordering, the
rightmost factor traverses the first edge. Intermediate gauge
factors cancel pairwise around the plaquette, leaving
`P_x → g_x P_x g_x⁻¹`. Each coframe block transports its
neighbor spinor to x before contraction with the gamma matrix
at x, or transports the corresponding barred spinor in the
reverse contraction. Under the site gauge change the four
blocks therefore give the same internal vector rotation at x.
The gamma-contracted frame transforms by conjugation at x.
The closed-path curvature trace with two frame factors is
invariant because the chirality matrix commutes with Spin(4).
The determinant term is invariant under the internal proper
rotation.

A world-index shear commutes with the internal rotation,
so replacing the frames by exp(jE)T in this closed ordering
gives a locally invariant sourced action for any site source.
Its differentiated action has the same local form as the
dressed-source construction but uses closed-path curvature.
This gives an explicit candidate whose response can be
evaluated independently. Its normalization and weighted
correlations cannot use the literal signed coefficients
without new comparison. Independent review verified all four
coframe blocks, the plaquette ordering and the sourced action.

For any fixed spanning tree of extended links, choose the gauge
at the root to be the identity and choose the remaining gauges
recursively so every tree link becomes the identity. At fixed
tree link values this is a sitewise determinant-one Berezin change
of variables. It acts on every remaining link by fixed left and
right multiplications, preserving its Haar integral. If each
labelled action factor is the complete internal contraction at
its center, it transforms invariantly on its own. The same
tree change of variables then applies to each such word before
integrating tree links, which now contribute unit Haar volume.
This allows the existing tree-incidence profile to guide the
closed-path evaluator. The reduction applies to complete
internal contractions, so individual gamma-index summands
cannot be fixed separately on this argument. Independent review
verified the reduction for invariant Berezin top coefficients.

A modular control reused the eight labels and seed 1 of
`l1_tree_covariance_control.cpp` with the reversed plaquette
matrix product and the endpoint law above. The top coefficient
was 28318 modulo 65537 both before and after a one-site rotation.
A separate scratch run set the tree links (0,0), (0,1), (1,1)
to identity. Starting from root gauge G₀=I, each directed
tree edge x→y sets G_y=G_x U_xy⁻¹. Transforming all links
by the endpoint law again gave 28318 and verified all three
tree identities explicitly. Both runs check the fixed-link
top coefficient of one complete word. The integrated
closed-path normalization and response remain open.

Reversing the plaquette product preserves link incidence and site
degrees. On the 6,451 support candidates, optimizing over the 32
extended-link spanning trees gives remaining degree counts
`{30:160,32:212,34:328,36:2565,38:1784,40:1120,42:282}`.
On the 2,160 words with nonzero dressed cross multiplier, the
counts are `{30:40,32:64,34:176,36:1072,38:536,40:272}`.
These are upper degrees before further cancellations and
give the contraction budget after tree fixing. The support
conditions leave the signed Haar coefficients to be evaluated.

### Exact reuse for the private-curvature sectors

The two private-curvature reductions give a direct comparison
between literal and closed ordering. At each elimination step,
a link that occurs once in the common plaquette and nowhere in
the remaining word makes that plaquette conditionally Haar,
in either multiplication order. Its two curvature insertions
therefore have the same joint Haar moment. When both links of a
singleton commutator are private, the original product
`U V U⁻¹ V⁻¹` and the reversed product `V⁻¹ U⁻¹ V U`
have the same distribution by `(U,V)→(V⁻¹,U⁻¹)`.
The elimination order depends only on incidence and is unchanged.
After these integrations the remaining coframe contractions are
identical. This argument requires that both factors of each pair
use the same oriented plaquette and that the eliminated links are
absent from every remaining coframe.

The two disjoint sectors selected by the existing coverage
classifier then inherit the normalization contributions
`8071653/32` and `535869/4` and the dressed cross subtotals
`−121389/2` and `−72441`, respectively. Since the source weights
are fixed by the world labels, equal-time contact and product
subtotals carry over by the same wordwise argument. This is a
partial comparison. The sectors without private elimination
still require a closed-order calculation. Independent review
verified the conditional Haar argument, classifier incidence
and all transferred subtotals.

The same distribution argument works for any number of
occurrences of a common oriented plaquette. An incidence pass
counted each distinct plaquette once when tracking link use,
but counted every coframe occurrence. It repeatedly removed a
plaquette with one private single-use port, or a singleton
commutator whose two links were both private. The pass removed
all plaquettes for 4,026 words, of which 1,114 carry nonzero
cross-time weight. Beyond the two previously reviewed private
sectors it selects 128 mixed-chain, 800 odd-commutator,
64 pure-chain, 618 small-component and 504 transport-cycle
increment words. Of those additional words, 64 mixed-chain and
88 small-component words have nonzero cross weight. Their
incidence counts were independently reproduced. Their
coefficient subtotals require the sector-level checks below.

In mixed chain the complete elimination selects exactly the
128 opposite-singleton words. Half have zero cross multiplier
and half have multiplier −4. Their existing per-word value
`81/64` gives normalization 162 and cross subtotal −324.
The same-singleton half requires a new closed-order contraction.

The pure-chain, transport-cycle increment, and odd-commutator
sectors are fully selected by the reviewed incidence pass. Their
exact normalization subtotals are `24`, `32380/81`, and zero,
respectively. All three use only transverse curvature planes
and their diagonal plus source weights vanish on both slices.
The remaining 618 selected small-component words are being
replayed with all four coefficient weights.

A second incidence scan minimized each word's product of Haar
denominator scales over the 32 trees, then included its repeated
label factorial. In the evaluator convention with the action
factor 16 absorbed at every vertex, the least common multiple
of these bounds is `7791007453025402880000`. The largest
single-word bound is `486937965814087680000`. The common scale
has residue 26548 modulo 65537. The unscaled action adds the
factor 16⁸, also invertible at this prime. Thus exact modular
integration can certify a nonzero rational result if it returns
a nonzero residue. These are denominator controls, not a
computed normalization residue or a sign test.

The small-component replay finished with 618 selected words and
88 nonzero cross weights. Its exact (normalization, cross,
contact, product) subtotals are
`(142007171/64800, −62073/8, 62073/8, 0)`. For the 128
opposite-singleton mixed-chain words the corresponding subtotals
are `(162, −324, 324, 0)`. Including the previously accepted
private-curvature sectors and the three source-neutral sectors
gives `3150767387/8100` for the partial normalization and
`−1129749/8` for the partial cross numerator. The new weighted
small-component sums await independent reproduction. There are
2,425 normalization words and 1,046 cross-weight words outside
this elimination, so the partial signs do not settle either full sum.

After private elimination, the remaining words group by the
number of distinct plaquettes still coupled. Two plaquettes
remain in 1,488 normalization words and 544 cross-weight words.
Four remain in 425 and 214, respectively. Eight remain in 512
and 288. In the two-plaquette group the cross support is 368
correlated-eight, 32 correlated-six, 64 same-singleton
mixed-chain and 80 small-component words. A shared-link
two-plaquette kernel would therefore address more than half
the remaining cross support. This census does not determine
which of those contractions are equal after tree fixing.

The same-singleton mixed-chain block also transfers by a separate
conditional law. With fixed transverse links X,Y and private
extended Haar link U, the literal plaquette is `U Y U† X†`
and the closed one is `X† U† Y U`. Both conjugates of Y have
the same conjugation-invariant law. Moving X† from left to right
conjugates the random factor by X and preserves that law. The
two private extended links are independent, so the conditional
joint moment agrees at fixed shared transverse links. Independent
incidence review found the extended links absent from every
coframe and other plaquette in all 128 words. The remaining
singleton commutator is private. The same-singleton normalization
163 and weighted cross subtotal 326 therefore transfer. Together
with the opposite-singleton results the full mixed-chain sector
contributes 325 and 2, respectively, in the closed ordering.

Adding the private-conjugator rule to the iterative incidence
pass selects 5,778 of 6,451 normalization words and 1,868 of
2,160 cross-weight words. For a mixed plaquette with one
extended and one collapsed axis, the added rule requires that
its extended link occurs only in that plaquette, exactly twice.
It selects all small-component, mixed-chain and correlated
words, 60 of 64 checkerboard words, and four source-neutral
mixed-cycle words, in addition to the earlier full sectors.
The remaining 292 cross-weight words are 128 plaquette-wire,
160 mixed-cycle and four checkerboard. Independent enumeration reproduced these totals and all
remaining sector counts.

For the all-local word, the transverse coframe saturation is
unchanged. The curvature dependence is the same character
polynomial on each time-space plaquette in either ordering.
The exposed-link criterion for proper face subsets is unchanged.
For the full adjoint surface, an explicit index scan assigned a
cyclic trace index at each face corner. Each shared link identifies
the two pairs of indices in opposite orientation and contributes
1/3. Both matrix orders give four free index loops from eight
link integrations, hence factor 3⁴/3⁸ = 1/81. The normalization
contribution 104978 therefore transfers to the closed ordering.
Its shear weights vanish. Independent review obtained the same
closed-order result by Schur orthogonality on the periodic cell complex.

The four residual checkerboard words form one orbit under
extended and transverse axis exchanges. In these words all
four extended links share curvature and coframe transport.
The closed-order scratch evaluator retained only the joint
link moment in the repeated-cycle kernel and reversed the
curvature product before the exact trace. It gives real
normalization `315015/8192` for the four words and weighted
cross contribution `315015/512`. The largest certified sparse
multiplication bound is below 2⁶³. A literal shared-only
control is in progress to isolate the corresponding four
words from the earlier 64-word sector total.

The literal shared-only checkerboard control gives
`8503261/221184`, so replacing those four words changes the
normalization by `67/6912` and the cross numerator by `67/432`.
The full closed-order checkerboard normalization is
`136053675/221184`.

The closed mixed-cycle replay replaced the joint extended-link
projection of `U Y U† X†` with `X† U† Y U`, retaining the
same Haar scales and transport tensors. For the four original
layout classes in lexicographic order it gives
`19981/4096`, `2900539/1572864`, `7356675/2097152`, and
`172649/55296` per sixteen orientations, all real. The full
256-word normalization is `1246110337/28311552`. This covers
the four words already eligible for reuse as well as the
252 residual words. Independent replay reproduced all four
coefficients and verified the passive-edge first moment on all
16 quaternion basis pairs.

Applying the independently enumerated source weights to these
four closed mixed-cycle coefficients gives cross subtotal
`10573243/49152`, contact `1246110337/7077888`, and operator
product `276436655/7077888`.

For the diagonal-mixed sector, an independent scratch evaluator
changed the curvature projection to the closed order and replayed
the original order as a control. A raw coefficient changed sign
under reversal, but all 160 reduced local Haar tensor rows and
the final per-case contractions matched exactly. Thus its
normalization `−40213/16`, contact `−40213/8` and product
`40213/8` carry over. The cross weight vanishes.

Subtracting the literal wire sector and replacing the checkerboard
and mixed-cycle values gives the closed non-wire subtotals:

| Quantity | Exact non-wire subtotal |
| --- | ---: |
| Normalization | 1252308935395403/2123366400 |
| Cross numerator | 796813043/442368 |
| Contact numerator | 966843377209/786432 |
| Equal-time product numerator | 2927667245669/2359296 |

The wire replay reverses the source trace by transposing its
link factors and the base-site gamma block while retaining the
edge traversal. It also reverses the mixed projection and the
Y singleton commutator. The X1 and X2 orientation sums are
`6491/196608` and `111949/7077888`. Each class has four layouts.
The above totals exclude
all four wire classes until they can be assembled together.

Both Y orientation sums finished at exact zero. The 256-word
closed wire contribution is normalization `345625/1769472`,
cross `−6491/12288`, contact `345625/884736` and product
`121727/884736`. Adding it to the non-wire totals gives:

| Quantity | Complete closed-order value at e=1 |
| --- | ---: |
| Normalization divided by g₂⁸ | 1252309350145403/2123366400 |
| Raw cross numerator divided by g₂⁸ | 796579367/442368 |
| Raw contact divided by g₂⁸ | 8701593159881/7077888 |
| Raw equal-time operator product divided by g₂⁸ | 8783002710823/7077888 |
| Normalized half-period response | 3823580961600/1252309350145403 |
| Normalized equal-time operator product | 239536437567900/113846304558673 |
| Half-period to equal-time ratio | 12745269872/8783002710823 |

The transverse exchange cancellation also holds in the closed
ordering because it preserves the ordered matrix factor sequence
while reversing the world epsilon and source weights. The positive
ratio below one passes the finite scalar two-time test.

Independent scoped review of `340074356` accepted the closed wire
implementation and rational assembly. The reviewer independently reran
X1 and Y2, recovering `6491/196608` and exact zero, and inspected the X2
and Y1 receipts. A noncommuting matrix control distinguished the
original trace order from the reversed order and confirmed the
transpose implementation. The reviewer recomputed the non-wire, wire,
and full totals and normalized ratios.

The next B3 acceptance step is to match the dressed lattice insertion
to the physical metric source, including its tensor projection and
units. The reviewed two-time ratio is a scalar moment check. Positive
transfer, a physically normalized zero-frequency bubble, and the
separate RPA coupling still require evidence before evaluating the
susceptibility window.

The [closed wire replay](l1_normalization_closed_wire.py) uses
the same argument tuples as the literal evaluator. Run with the
repository Python environment and arguments `1 2 2 3 3`,
`1 2 3 2 3`, `0 2 2 3 3`, and `0 2 3 2 3` for X1, X2, Y1,
and Y2, respectively. Each invocation reports the exact orientation
sum, before the four-layout multiplier.

The checkpoint replay of X1 exited successfully and reproduced
`6491/196608` with zero imaginary part.

### Zero temporal mode of the closed-path source Hessian

Let the two slice sources be (j_0,j_a), with the spatial weighting
held fixed as in the finite replay. Time translation gives equal
diagonals, and the first derivatives vanish by the polarization
exchange symmetry. Using the table above, the Hessian of log Z has
diagonal A+C and off-diagonal B, where A is the normalized
operator product, C the normalized contact, and B the half-period
entry. The common-source path (j_0=j_a=j) therefore gives
`d² log Z/dj² = 2(A+B+C)`. Exact rational assembly yields:

| Quantity | Value |
| --- | ---: |
| Contact C | 2610477947964300/1252309350145403 |
| Contact-subtracted zero-mode eigenvalue A+B | 2638724394208500/1252309350145403 |
| Full zero-mode eigenvalue A+B+C | 477200212924800/113846304558673 |
| Full common-source second derivative | 954400425849600/113846304558673 |

For an action source constant over a physical Euclidean time length
β and spatial volume V, the static log-partition Hessian density
uses the common-source derivative divided by βV. A linear
identification `j = αh` contributes a further factor α².
This conversion is conditional on identifying the replay's spatial
weighting with the intended physical polarization. The physical
source may also vary links, measure, and regulator and thereby
change the contact and connected terms. Neither eigenvalue in the
table identifies the B3 bare bubble without that matching.

Independent review of `912195889` verified the two symmetries
and reproduced all four fractions. The zero mode refers to time
at the replay's fixed spatial weighting. Spatial momentum and
physical volume normalization require separate matching.

### Metric amplitude and the linear-path contact

For the replay generator E = diag(0,0,1,−1), set P = E/√2.
If the frame shear is interpreted as a background coframe
A = exp(jE), its Euclidean metric is AᵀA = exp(2jE).
Thus the Frobenius-unit metric perturbation has linear
amplitude h = 2√2 j. Under this coframe identification the
common-source response along the exponential metric path,
per βV, is 119300053231200/(113846304558673 βV).
This fixes the kinematic factor for the specified prescription.

An affine metric path I+hP has the same tangent but uses the
coframe (I+hP)^(1/2). The exponential and affine coframes have
the expansions I+hP/2+h²P²/8 and I+hP/2−h²P²/8,
respectively. Consequently, at fixed links and measure, the
affine-path second derivative differs from the exponential-path
second derivative by −DW[I](P²)/2, where W[A] is log Z with the
common coframe deformation. This one-point term is a transverse
dilation response. Polarization exchange reverses P and leaves
P² invariant, so the vanishing shear one-point function does
not remove this contact. The connected first-vertex contribution
is identical on the two paths. Physical matching must specify
the metric path and account for its contact as well as any
link, regulator, or measure variation.

The affine contact can be isolated without a new Haar integral.
Let n₂(w) count the vertices with two transverse coframe slots in
a word w, and n₁(w) those with one. At fixed links and measure,
DW[I](P²) is the normalized signed moment of n₁/2+n₂, since
P² has diagonal entries (0,0,1/2,1/2). The common-source
quadratic contact 2C counts n₁, because the square of the
generator weight is one on a mixed coframe pair and zero
otherwise. The affine-path static Hessian is therefore

    (A+B−C)/4 − (Σ_w C_w n₂(w))/(2 Σ_w C_w).

This leaves one new exact moment, counting the vertices whose
curvature plane is the pair of extended directions. A common
transverse dilation changes scalar word weights and preserves
the closed-order Haar–Berezin kernels and support. The existing
transverse exchange preserves n₂ and cannot supply its moment.

Independent review of the metric conversion at `cef5bf63d`
reproduced the amplitude factor 1/8, the affine path correction,
and the reduction to the extended-plane count. A support census
using the canonical sector classifier found 913 of 6,451 words
with nonzero weight for that count. Of these, 832 have count two,
80 have count four, and one has count eight.

The all-local word has count eight. Every diagonal-mixed and wire
word has count two. Their joint contribution to the raw count
numerator is therefore
`8 × 104978 + 2 × (−40213/16 + 345625/1769472)`.
The remaining contribution is entirely private curvature. The
private paired and repeated sectors contain words of counts zero,
two and four, so their total normalizations cannot substitute for
the weighted sum. Their exact closed-order replay is assigned.

The private replay returned 439344 for the 176 paired words and
907200 for the 320 repeated words. It counts occurrences before
canonicalizing the private kernel plans and uses the reviewed
closed-order transfer for those kernels. See
[l1_affine_private_moment.py](l1_affine_private_moment.py).
Adding the previously resolved sectors gives raw extended-plane
moment 1929911588377/884736 and normalized moment
4631787812104800/1252309350145403. The full common affine
metric-source derivative of log Z is then
−2308832294491350/1252309350145403. Thus the affine and
exponential prescriptions have opposite full static signs in
this finite model despite identical connected first vertices.
Independent review at `5280cb77a` reran both private sectors,
verified their original-label multiplicity factorials, and reproduced
the raw moment, normalized moment, and affine response exactly.

### Linear composite-metric source on the closed action

For the existing plus polarization P = diag(0,0,1,−1)/√2,
define Q_x = Z_G (G₂₂(x)−G₃₃(x))/(√2 a²) using the
dimensionless lattice composite and a real matching coefficient
Z_G. For spacing a in every direction, add
a⁴ Σ_x J_x Q_x to the exponent of the closed action. The source
does not change the link or Berezin integration measure. In this
specified generating functional the first derivative inserts
a⁴ Q_x, and the second derivative of log Z inserts the connected
covariance multiplied by a⁸. There is no bare quadratic vertex
for this linear source.

For a common J and a translation-invariant four-site lattice,
divide the second derivative by βV = 4a⁴. The resulting
zero-momentum static covariance density is
a⁴ Σ_y ⟨Q₀ Q_y⟩_c. More generally the Fourier transform weights
each summand by exp(−ik·y). The Legendre stiffness is the inverse
on a nonsingular source block. Invertibility of that Euclidean
block alone does not imply a positive thermal transfer
representation, which also constrains the cross-time block.

The two derivatives of this linear composite source are distinct
from the curvature-dressed first vertex and the dilation contact
of the fixed-link coframe family. Comparing the two requires a
closed-action composite covariance, with the original-order
contraction as a control. The closed-action diagonal-separation
replay has been assigned. For physical B3, the remaining match
must fix Z_G, source and operator mixing, the spatial tensor
projection, and any regulator-dependent contact, then establish
the scaling regime and the separate RPA coupling.

Independent review of `7a6b80478` verified the linear source
normalization. Write s, p, n and d for the pure-g₂⁶ raw connected
plus coefficients at coincident, nearest spatial, nearest temporal
and diagonal separation. The one-point term vanishes by transverse
exchange. The half-period spatial Fourier eigenvalues are n±d
times Z_G²/(2a⁴g₂²Z₈), with positive closed normalization Z₈.
Thus a nonzero real matching coefficient requires n ≥ |d|.
The equal-time eigenvalues have the same factor multiplying s±p.
For a faithful finite positive thermal realization each sector
must either have both moments zero or satisfy
0 < n±d ≤ s±p. These checks concern the two scalar spatial
sectors. Full transfer positivity and physical matching require
additional evidence.

The diagonal replay recovered the existing original-order modular
control and found a different residue with the closed order.
Of 128 support words, 30 vanish by a private-link center parity
in either ordering. The remaining 98 require closed-order tensor
checks or exact joins. The modular control does not determine the
sign of d or the status of the transfer test.

The nearest-time support replay returned 128 words, with
source-link incidence (2,0) and (0,2) for 64 words each.
Reordering the plaquette factors changes neither the site degree
nor the link-incidence multiset. Thus each word still has a
source site whose two transverse links are absent from every
action factor. Their identical one-link conditional Haar
integrals cancel the plus insertion coefficientwise, giving
n = 0. The closed-order transfer argument now hinges on d.
Any nonzero real d gives one negative eigenvalue in the
half-period spatial Fourier block. If d vanishes, both
half-period eigenvalues vanish and faithful positive thermal
transfer additionally requires zero equal-time weight.
Independent review of `9b4101e88` reproduced the full nearest
census (11,520 ordered terms) and verified the coefficientwise
Haar cancellation. The same proof gives p = 0 by exchange
of the two extended axes. Hence a faithful finite thermal
representation for the full two-sector composite block requires
both d = 0 and s = 0. The diagonal replay tests the first
condition. An independent same-site calculation tests the
second condition without depending on the diagonal replay.
This criterion applies to the composite insertion in the
specified finite model and leaves a dressed or mixed physical
operator as a separate construction.

The same-site calculation gives a separate route to deciding the
finite transfer test. The 145 source-decoupled words transfer by
private single-occurrence Haar projection. Any remaining squared
local commutator is independent of the source and frames and has
the same Haar law in both orders. For the 40 coupled words the
joint private projection changes the quaternion order from
(Ad_U Y) X† to X† (Ad_(U†) Y). An exact local tensor comparison
matched all six retained source-coordinate classes and every
gamma/Berezin entry, with 104 nonzeros per scalar case and 96
per vector chirality. This gives the coupled subtotal −23063/32
and full same-site coefficient s = 10179913/32. The direct closed coupled replay reproduced the exact 40-word
histogram and subtotal. Its full reduced-tensor comparison
changed 48 raw curvature entries and retained equality in all
six source classes at both centers. Independent review of
`04e107a2c` reran the transfer control, confirmed all 12 tensor
equalities and the 41/104/40 incidence split, and verified the
conditional Haar substitutions for the decoupled terms. The
author's direct closed replay supplies the 40-word subtotal.
The independent control checked its transfer by tensor equality.

The same-site coefficient decides the faithful
finite thermal test regardless of the diagonal result. With n
zero, half-period positivity forces d to vanish. Faithfulness
then requires the centered operator to vanish and consequently
s to vanish, contradicting the same-site coefficient. The
result would apply to the specified linear composite source.
The dressed source, physical matching and continuum limit
remain separate constructions.

The closed diagonal replay now resolves the eight residual orbits.
With the source commutator ordered as V†U†VU, the exact source
table has 432 coefficients over denominator 18 and 5,184
adjacency edges. The Gaussian-rational join gives
(−3563/3072, 0) for the real and imaginary parts of the residual
subtotal. The earlier center tests retained the same 320 and
608 supported slices. All 320 same-center slices vanish and
the 24 nonzero mixed-center entries reverse sign. These center
identities do not by themselves carry over the shifted join,
which uses the reordered source tensor. The residual subtotal
excludes that shifted contribution and the full closed diagonal
coefficient awaits the shifted replay and elimination review.

### Full closed diagonal result and stability

The eleven shifted orbits contributed 25/1536. The closed support
lists matched the original ones. Four same-center groups vanished.
For the seven mixed groups the two reversed center signs canceled
in the join, giving 25/49152 per word. The 28 isolated transport
zeros precede curvature insertion, and the 14 isolated center
zeros use the replayed closed zero tensor. The eight residual
orbits contributed −3563/3072. Their sum gives d = −1171/1024,
with zero imaginary part. The two original-order batched controls
also reproduced the earlier receipts. Independent review rebuilt the closed evaluator at `9d4012c47`
and reproduced the shifted and residual subtotals and full
coefficient. The corrected validator at `e41960619` checked
all 3,712 fresh projection receipts against the submitted slices,
including each of the 320 unindexed base zeros.

Since n = 0, the uniform half-period covariance eigenvalue is

    −(2428185600/1252309350145403) Z_G²/(2a⁴g₂²).

The staggered eigenvalue has the opposite sign. For fixed real
nonzero g₂ and Z_G, the finite integrals and source derivatives
are polynomials in g₁. The normalized uniform covariance is
continuous near g₁ = 0 because the closed partition function
there is positive. Its real part therefore remains negative on
some open neighborhood of zero. This yields an obstruction for
the specified composite insertion beyond the pure-g₂ line once
the diagonal calculation is verified. Continuity alone gives no quantitative range in g₁. The
physical metric insertion requires separate matching.

### Conservative interval for the closed ordering

Use x = g₁/g₂². Degree-32 saturation gives Z = g₂⁸ z(x),
the two one-point numerators g₂⁷ v(x) and g₂⁷ w(x), and the
two-point numerator g₂⁶ u(x). The degrees are at most four
for z and three for each of v, w and u. Keep the one-point
subtraction at mixed coupling. Its constant term vanishes by
the already checked pure-g₂ symmetry.

The exterior norm bounds above transfer to the closed action:
reordering unitary plaquette factors preserves the bound on
their trace, and no coframe or composite coefficient changes.
In the unnormalized uniform plus convention, every polynomial
coefficient has modulus at most B = 2¹⁹². For
R = Re[(zu − vw) conjugate(z)²], the coefficient norm satisfies

    ||R||₁ ≤ (5B·4B + 4B·4B)(5B)² = 900B⁴ < 2⁷⁷⁸.

The pure-g₂ constants give z(0) > 1 and R(0) < −1.
For |x| ≤ 2⁻⁸⁰⁰ the change in z is at most 5B |x|,
and the change in R at most 2⁷⁷⁸ |x|. Hence z stays nonzero
and R remains negative. The real part of the normalized
connected response has the sign of R, since its denominator
is g₂²|z|⁴. This interval is conditional on verification of
the closed diagonal constant and applies to the specified
finite source. It is a conservative bound rather than an
estimate of a physical coupling range.

Independent review of `12c43c544` verified the saturation degrees,
transfer of the exterior norm bound, and the strict margins on z
and R throughout the stated interval. Acceptance of the diagonal
constant remains a separate replay review.

### Mixed composite and coframe half-period response

Use the uniform slice composite L and the dressed first vertex X
on opposite slices. The mixed Hessian of the joint generating
functional inserts their connected product. The separate linear
composite source and coframe source give no mixed bare contact.
The metric-amplitude conversion on the dressed leg is 1/(2√2).
The composite leg uses the linear source normalization above.

At pure g₂ the mixed coefficient vanishes. The two degree-four
insertions leave six untagged S2 factors. Under internal Pin,
the composite is even and each of the six S2 factors and the
tagged dressed S2 are odd. This makes the mixed numerator odd.
The first symmetry-allowed term is the degree-32 coefficient of

    g₁ g₂⁵ L (∂S2) S4 S2⁴ / 4!

with the tag on the opposite slice. The next allowed term is
g₁³ g₂ L (∂S2) S4³ / 3!. The combined transverse-axis exchange
and internal Pin preserves the action and makes each source odd,
so the one-point terms vanish. Exact evaluation of the leading
allowed coefficient must retain the original action factorials
and the tagged mixed-plane weight before symmetry reduction.
A nonzero result would measure overlap of these finite sources.
The physical metric matching must still derive which operator
combination is sourced and how the regulator responds.

For a pure-g₂ comparison, take L to be the raw composite plus
sum over the two spatial sites divided by √2, and X the derivative
with respect to the unrescaled uniform coframe parameter j.
The diagonal half-period Gram entries are d/(g₂²Z₈) and
(796579367/442368)/Z₈, respectively. Pin makes the off-diagonal
entry zero in both directions. A proposed source αL+βX therefore
passes the nonnegative scalar half-period test precisely when

    α² ≤ (796579367/505872) g₂² β².

This is a constraint in the stated lattice source coordinates.
Rescaling the sources rescales the coefficients. The full
two-source span still contains a negative direction. A physical
construction retaining a single combination must derive its
coefficients and the restriction on the retained observable
span. The numeric threshold uses the independently reproduced diagonal coefficient.

The [support replay](l1_mixed_g1_support.py) fixes the composite
at site 0 and tags the opposite time slice, sites 1 and 3. Spatial
translation supplies the contribution with the other composite
site. Saturation and link center parity leave 192 multisets.
The signed coframe tag sum eliminates 96, leaving 48 with
weight +2 and 48 with weight −2. Among the 96 weighted words
the determinant sits at site 3 in 64 and at site 2 in 32.
The signed weights must multiply the original per-word
Haar–Berezin amplitudes and factorials. Equal counts with
opposite tags alone cannot cancel the coefficient.

The source-link incidence check removes another 64 words exactly.
Neither transverse link at site 0 appears in their action factors.
The two source terms therefore have equal conditional Haar
integrals and cancel before the remaining links are integrated.
The other 32 words touch both source links. A conditional
projection can eliminate its private integration variable while
retaining dependence on the other links in the projected tensor.
Subsequent reductions must use that retained dependence.

The corrected census and all-64 checkerboard replay are tracked
at `76704b872`. A separate support enumeration confirmed every
checkerboard word has cross, contact and product weights
(16, 4, 12). Consequently the direct subtotal contributes
5039025/512, 5039025/2048 and 15117075/2048 to those three
raw numerators. The agreement of the unweighted subtotal thus
propagates to all three weighted totals for this sector.

The 32 remaining words contain one site-0 curvature factor
with label (0,2,3,u,v). Counting all action and determinant
occurrences of the two transport links (u,0) and (v,1)
gives eight words in each degree profile (2,2), (2,4), (4,2)
and (4,4). In the (2,2) class both links occur only in frame
factors. The existing two-link antisymmetric Haar tensor
therefore removes these eight terms before inserting the
curvature coefficient.

The 24 candidates left can be joined by site. The site-0
composite and commutator use the existing closed residual
source tensor, with two extended frame boundaries. Site 3
uses the determinant tensor, with its two singleton frame
factors paired against incident curvature legs. Sites 1 and 2
supply two mixed curvature vertices each. Shared extended
links require fourth Haar moments and split links require
separate second moments. The determinant tensor evaluation is
assigned. A fixed-link modular control for one (4,2) candidate
survives a single-link projection. It does not settle the full
Haar contraction or the signed sum.

The cubic g₁³g₂ term vanishes on this regulator. The support
replay combines each of the 816 unordered triples of determinant
labels with each oppositely sliced nonzero shear tag and tests
the same site degrees and link-center parity. None passes both.
Thus the leading g₁g₂⁵ contraction is the only remaining
coefficient in the raw mixed numerator on this lattice.

The cubic zero also follows from site degrees alone. Each
determinant contributes six degrees at its center and one at
each extended neighbor. A center at site 0 exceeds the four
degrees left by the composite insertion. A repeated center
exceeds eight. The three centers must therefore be 1, 2 and 3,
leaving degree deficits (2,1,1,0). A tagged mixed curvature
vertex has one collapsed frame and one extended frame, giving
three degrees at its center. Neither allowed tag center on
the opposite time slice (1 or 3) has that capacity.

Independent review verified the Pin and transverse exchange
signs, the invariant Berezin and Haar measures, and the vanishing
one-point subtraction. A separate ordered enumeration tested
65,536 cubic words. Both the site saturation test alone and
the link-center parity test alone excluded every word.

The determinant-center output has 50,176 distinct nonzero
coordinate/mask rows, with 12,544 per extended anchor pair.
Every mask has site degrees (0,1,1,6). The maximum absolute
Gaussian integer component is 128. The physical denominator
for this tensor is 4096 from the four frame factors and two
quadratic Haar projections. The remaining join uses the two
open extended coordinates and the source tensor at site 0.

The exact four-site tensor join found two nonzero endpoint
modes in the canonical transverse pattern, each 15/16384.
Its tag is −2. The transverse-exchanged pattern reverses both
the raw tensor sign and the tag, so the contributions add.
The result at one fixed composite site is
−(15/2048) g₁g₂⁵, with zero imaginary part. The all-16 endpoint
replay also returned zero for the four modes excluded by the
isolated-link argument. Independent review ran a clean replay of `8e569c8ba`,
reproduced both nonzero modes and all zeros, and checked the
wedge signs, source denominators and factorial weights.

For L = (D₀+D₂)/√2 and the unrescaled dressed slice derivative,
spatial translation multiplies the fixed-site numerator by √2.
The one-point subtraction vanishes by the reviewed symmetry.
Writing the exact partition function as g₂⁸ z(g₁/g₂²), the
mixed covariance for g₂ ≠ 0 and nonzero partition function is

    −15√2 g₁ / (2048 g₂³ z(g₁/g₂²)).

This is the finite overlap in the stated source coordinates.
Physical matching still has to derive the source combination,
its dimensions, the regulator response and its retained
observable space.

### Local gauge invariance and the metric-source ambiguity

Consider a single site strain h with the coframe deformation
exp(hP/2), P = diag(0,0,1,−1)/√2, in the closed action.
Add a linear term c h D, where D = G₂₂−G₃₃ at that site
and c is a real coefficient in lattice units. Both terms
are invariant under internal site gauge rotations for arbitrary
h. The coframe rotates internally in every world component,
the world strain commutes with that rotation, and D contracts
the internal indices of the two frames. The Haar and Berezin
measures are independent of c and h. Hence the internal
gauge Ward identity holds for the whole family, including
at nonuniform h, while its metric derivative changes by cD.

For common strain on a slice, the first vertex is
X/(2√2) + c√2 L in the source convention above. The added
linear term does not change the bare second vertex. At
pure g₂ the uniform half-period response is consequently

    B_X/8 + 2c² B_L,

where B_X is positive and B_L is negative. Thus two members
of the same internally gauge-invariant source family can
give opposite uniform half-period signs. The finite Ward
test constrains the gauge transformation law but leaves c
undetermined. Fixing c requires a metric matching condition,
such as matching the response of independently normalized
matter to the same background. The family gives a control
for that construction, not a prescription for choosing c.

### Matter calibration control for the collapsed transverse axes

For a minimally coupled real scalar probe, discretize the
kinetic term with periodic forward differences and the inverse
background metric. Use a fixed coordinate cell volume and the
diagonal background g(h) = exp(hP). This background has
determinant one at every site, and its inverse components along
the two extended axes are one. The transverse forward
differences vanish identically on a 2×2×1×1 lattice. The
mass term also has no strain dependence because the volume
factor is one. Thus the entire scalar probe action, including
its quadratic contact, is independent of h even if h varies
over the extended directions. This statement assumes a
source-independent scalar measure and the usual periodic
identification without transverse twist.

This probe cannot fix the shear normalization on the current
regulator. A minimally coupled scalar calibration needs a
transverse kinetic mode, for example by extending a transverse
direction and using a probe with nonzero momentum along it.
Then the derivative of the probe kinetic term measures the
difference of the two transverse gradient squares. Even with
that calibration, fixing c requires a joint observable or a
microscopic coupling that ties the calibrated probe strain to
the same composite metric. A separately added scalar action
has no dependence on c.

For a constant strain and a periodic scalar lattice with both
transverse axes extended, the Fourier inverse propagator is

    K_h(p) = m² + p̂₀² + p̂₁²
             + exp(−h/√2) p̂₂² + exp(h/√2) p̂₃²,
    p̂_i² = 4 sin²(p_i a/2)/a².

This follows by squaring the forward-difference multiplier
(exp(i p_i a)−1)/a. In a transverse square with at least two
sites on each axis, compare modes with equal nonzero transverse
momentum magnitude along axis 2 or axis 3 and identical other
components. The inverse-propagator splitting is exactly
−2 p̂² sinh(h/√2). Its slope at zero is −√2 p̂² and its
second derivative at zero vanishes. The two individual
second derivatives of K are equal, each p̂²/2. The corresponding
Taylor coefficients are p̂²/4. These give separate
linear and quadratic calibration checks in the declared scalar
action. The splitting calibrates the strain felt by the probe.
It leaves the coefficient c in the gravitational generating
functional free unless the microscopic joint action specifies
how the scalar feels the composite geometry.

Independent review of the preceding internal gauge argument
verified the first-vertex normalization, the pure-g₂ sign
change and the nonuniform site gauge symmetry. Its scope is
the internal Ward identity. Background metric matching and
thermal positivity impose additional conditions.

Independent review of `a842701ac` and `2226852ab` verified the
collapsed-axis zero, the Fourier splitting and both derivatives
for the stated periodic scalar measure.

A joint-response test can isolate the missing matter coupling.
At zero interaction let D_x be the composite shear and O_x the
scalar shear vertex from the calibrated kinetic action, with
both operators centered in their respective measures. Use the
exponent convention +λ Σ_x D_x O_x for a candidate local joint
interaction. If the measures factorize at λ = 0, then

    ∂_λ Cov(D_y,O_z)|₀
      = Σ_x Cov_geometry(D_y,D_x) Cov_scalar(O_z,O_x).

This follows by differentiating the normalized expectation
and factoring its four insertions at zero interaction. The
subtractions in the connected derivative vanish there by
centering. For translation-invariant measures the Fourier
transform is the product of the two covariance kernels in
matched lattice coordinates. This is a first-order check for
the stated candidate interaction. It requires both kernels on
the same extended regulator. The independent probe alone gives
zero mixed covariance and cannot measure λ. A physical match
must justify the joint interaction and its normalization.

For the free real scalar with positive mass, the connected
uniform shear covariance is available exactly. The uniform
vertex is O = −φᵀK'φ/2 for the exponent −φᵀKφ/2.
Wick contraction gives

    Var(O) = (1/2) Tr[(K⁻¹K')²]
           = (1/4) Σ_p (p̂₃²−p̂₂²)²/K₀(p)².

The sum uses all lattice momenta. Equivalently it is the trace
over real field coordinates, with conjugate momentum pairs
accounting for two real modes. The quadratic action contact
is separate from this covariance. At unit spacing and mass on
the 2×2×2×2 torus, each squared lattice momentum is 0 or 4.
Summing the 16 exact terms gives 193312/342225. The covariance
per site is 12082/342225 in this convention. It vanishes on the
collapsed transverse torus and is strictly positive on the
extended example. This supplies the scalar factor in the
zero-momentum joint test. The corresponding geometry kernel
must be evaluated on the same extended lattice.

For the pure-g₂ geometry on that same 16-site regulator,
top degree is 128. Write D_total = Σ_x D_x and use normalized
product Haar. The two raw constants needed for the uniform
geometry kernel are

    z₃₂ = ∫ [top] S2³²/32!,
    d₃₀ = ∫ [top] D_total² S2³⁰/30!.

Each insertion is quartic. The one-point term has 31 curvature
factors and vanishes by internal Pin. For g₂ ≠ 0 and z₃₂ ≠ 0
the uniform geometry covariance per site is
d₃₀/(16 g₂² z₃₂). With the local coupling convention above,
the derivative of the uniform mixed covariance per site is
the product of the two per-site susceptibilities. This follows
by summing over both exterior insertion sites before using
translation invariance. Thus the unit-mass scalar example
fixes its factor to 12082/342225. The two geometry coefficients
and a physical matching law remain to be established on the
extended regulator.

Independent review verified the scalar Wick contraction and
the joint-response normalization. With the unnormalized Fourier
transform the relative-coordinate convolution gives
C̃_D(p) C̃_O(−p). Translation-invariant autocovariances are
even, so this is also the same-momentum product. The covariance
of the two uniform sums has one extra factor of volume.

The four-site word enumerator does not scale directly to the
16-site geometry. There are 384 labelled curvature terms before
selection: 16 centers, six planes and four endpoint choices.
Degree and center parity alone do not eliminate all words.
For example, choose a fixed curvature plane (0,1) and include
the same labelled vertex twice at each site. Each vertex gives
two degrees at its center and one at each neighbor along axes
2 and 3. With the doubled vertices, every site receives four
local degrees and two from each of those neighbors. All link
multiplicities are even because each label occurs twice.
This is a support witness only. It does not establish a
nonzero exterior coefficient or signed integral. A practical
exact contraction must impose saturation during tensor
assembly and integrate each link before summing over its
boundary states.

For the selected doubled (0,1)-plane word, the link measure
separates into four curvature layers at fixed (x₂,x₃) and
four frame layers at fixed (x₀,x₁). The curvature uses only
links along axes 0 and 1. The frame factors and their
Grassmann generators use only axes 2 and 3. At each site
the two copies of the action term leave two open curvature
component indices, each contracted against a frame bilinear.
Taking the local top coefficient on each transverse frame
layer and integrating its links therefore yields four
frame tensors. Integrating each curvature layer yields four
curvature tensors, with one paired component index for each
intersection between the two layer families. This reduces
the selected 128-generator integral to a finite eight-tensor
join. The repeated-label factorial is (2!)¹⁶. Evaluation of
this witness is assigned. Even an exact nonzero value would
establish one term of the signed partition sum.

A second selected word admits an exact evaluation. Use four
identical (0,1)-plane vertices at each even-parity site, with
both transverse frame links based at the center. The eight
curvature plaquettes have disjoint links. Their holonomies
are independent Haar in either ordering. On each transverse
layer the two opposed centers jointly saturate its 32
generators. The [exact replay](l1_extended_opposed.py) integrates
the curvature fourth moments and reuses the transverse fourth
frame tensors. Each opposed pair contributes 61875/262144
including its repetition factorials. The full word contributes
(61875/262144)⁴, strictly positive. This verifies one term of
the signed partition sum. The sum may contain cancellations.

The 16-site witness has twelve distinct symmetry images:
six curvature planes and two center parity choices. The
support and disjoint-link check holds for all twelve. Axis
permutation can reverse the world epsilon, but there are
32 vertices, so the resulting overall sign is positive.
Relabeling whole site blocks of eight Grassmann generators
also has even sign. Translation exchanges center parities.
Thus this orbit contributes 12(61875/262144)⁴ to the signed
sum, using the independently verified base witness.
The remaining orbits can still cancel that contribution.

Independent review of `9c9e7dfa9` reproduced the exact opposed
pair and full word values, verified the disjoint Haar ports
and even Grassmann block signs, and checked the distinction
between gamma-slot multiplicities and action factorials.

### Effective matter actions and absolute metric scale

Volovik's scalar action uses the inverse and volume density
of the effective tetrad metric. This supplies a comparison
kinetic and mass term on a nondegenerate collective background.
The microscopic Berezin composite has vanishing body, so it
cannot be substituted directly into an inverse metric. A joint
lattice construction needs a nondegenerate collective branch
or a polynomial auxiliary-field formulation and a matching
condition. [Scalar comparison action, Eq. (5)](https://arxiv.org/abs/2003.00915)

The vestigial-gravity proposal identifies the metric with the
tetrad two-point expectation and proposes Maxwell matter on
that metric. In four dimensions the classical Maxwell density
contains one volume factor and two inverse metrics. Under
g → c g these scale as c² and c⁻², so Maxwell propagation
cannot fix a common constant metric normalization. It can
still constrain the causal cone. The massive scalar density
has kinetic and mass terms scaling as c and c². After
canonical field normalization its mass-squared term scales
as c, giving a possible dimensional matching observable if the
mass is fixed independently. The effective actions leave that
microscopic normalization to be derived.
[Vestigial gravity and Maxwell proposal, Eq. (19)](https://arxiv.org/abs/2312.09435v2)

### Polynomial scalar coupling about a nondegenerate background

On the finite Euclidean lattice, take a positive body metric
ḡ and a degree-four even Grassmann perturbation δg built from
the composite. For X = ḡ⁻¹δg, every entry of X is nilpotent
in the finite Grassmann algebra. The inverse of ḡ+δg is the
terminating Neumann series in X times ḡ⁻¹. Its volume is
√det(ḡ) times the terminating binomial expansion of
√det(I+X). These define an exact polynomial matter coupling
with a positive body scalar quadratic form for positive mass.
At each order the scalar integrals reduce to Gaussian moments.

At first order the kinetic density varies by
√det(ḡ)[tr(X) ḡ⁻¹/2 − ḡ⁻¹δg ḡ⁻¹], and the volume
varies by √det(ḡ) tr(X)/2. For a traceless perturbation
δg = λ D P at ḡ = I this gives the joint term λ D O
in the scalar exponent, with O the probe shear vertex
defined above. This constructs a lattice family in which
the joint-response test applies. The positive body and λ
are inputs to the family. Deriving the physical background
and matching λ to the gravity source remain B3 obligations.

Independent review verified the polynomial construction. Matrix
nilpotence follows because every entry lies in the same
positive-degree ideal of the finite Grassmann algebra. For
t = λD and the affine family I+tP, the volume is 1−t²/4
through second order, and the inverse-metric density is
I−tP+t²(P²−I/4). The scalar exponent therefore has a quadratic
coefficient D²/8 multiplying the sum of the extended-axis
gradient squares minus the transverse gradient squares plus
m²φ², with the common cell weight. The second derivative
has twice this coefficient. Higher powers may survive when
D uses neighboring sites.

For a constant ordinary affine strain h, the scalar kernel
satisfies K'' = p̂₂²+p̂₃²−K₀/2 at h=0. At unit mass and
spacing on the 16-site lattice, the trace of
(p̂₂²+p̂₃²)/K₀ is 21824/3315. The log-partition Hessian is
therefore 193312/342225 + 4 − (21824/3315)/2 =
7407044/5817825. The connected vertex variance is the first
term and the rest is the quadratic contact. This checks the
affine matter source independently of the unknown geometry
kernel. Independent exact enumeration at `57ad93dbd` reproduced the
contact 2348/3315 and the full affine Hessian.

Integrating the candidate scalar exactly produces a geometry
weight det(K[D]/K₀)⁻¹/² relative to the scalar vacuum. The
positive body makes the finite Grassmann log and determinant
expansions well defined. For K[D] = K₀ + λ A[D] + λ² B[D²]
through second order and C = K₀⁻¹, its exponent is

    −λ Tr(C A)/2
    + λ² (Tr(C A C A)/4 − Tr(C B)/2).

Here A is linear in the site shear, and B contains the affine
density and mass-volume terms. On the symmetric periodic
regulator the linear trace vanishes coefficientwise because
the two transverse gradient expectations agree. The
second-order term is a degree-eight geometry interaction.
Its connected part, including the diagonal, is half the scalar
shear covariance kernel. Its bare contact part is local and is
half the affine scalar contact kernel.
For a uniform ordinary strain used as a check, summing
the kernels gives half the independently reviewed affine
Hessian as the quadratic log-weight coefficient. This
matter-induced interaction is a calculable candidate in the
chosen source family. Its coefficient in physical units
still depends on the microscopic identification of λ.

Independent review verified the determinant expansion and
the uniform coefficient 3703522/5817825. The connected kernel
can also be evaluated at every separation. On the unit
2⁴ torus, index sites and momenta by four bits. Define

    G(r) = (1/16) Σ_p (−1)^popcount(p & r)/(1+4 popcount(p)),
    H_ij(r) = G(r⊕e_i⊕e_j) − G(r⊕e_i) − G(r⊕e_j) + G(r),

where e_i is bit i. H is the covariance of the two forward
differences. Wick contraction gives the connected kernel
K(r) = (H₂₂²+H₃₃²−H₂₃²−H₃₂²)/4. Exact enumeration gives
K(0)=208123/11635650 and Σ_r K(r)=12082/342225, reproducing
the uniform per-site variance. The local affine contact
adds 587/13260 at r=0 only. These formulas fix the scalar
kernel for the matched-lattice contraction at all separations.

Independent review of `e0c32a7c1` inverted the real-space
16×16 scalar kernel over the rationals and reproduced the
diagonal, uniform sum and affine contact. The connected
kernel is signed by separation. In particular the offset
that changes both transverse bits gives −2993/1292850.
The mixed contraction must retain this sign.

For the extended geometry covariance, translation reduces
the two-source numerator to one source at the origin and
one at an offset r. Exchange of axes 0 and 1 preserves D.
Exchange of axes 2 and 3 reverses both D insertions. Each
exchange reverses the world epsilon in S2, and the numerator
has 30 such vertices, so the action sign is even. Relabeling
site blocks preserves the top-form orientation. Thus the
16 offsets reduce to nine classes (i,j), the Hamming weights
in the two extended-axis pairs (0,1) and (2,3). The uniform
numerator is 16 times the sum over the nine representative
coefficients with weights binom(2,i) binom(2,j). This reduction
applies to the full signed integral and keeps the origin and
the doubly transverse separation in distinct classes.

The grouped-center contraction has a measured width bottleneck.
Subset elimination on the 16 centers gives treewidth six for
the nearest-neighbor hypercube and twelve for the graph
joining all pairs within each closed center star. An exhaustive
balanced-cut scan gives at least twelve crossing stars, with
four anchored link variables per star. Fixing a spanning tree
removes at most fifteen of those 48 crossing links. These are
bounds for the grouped-center representation. They do not
rule out a split sparse contraction.

The next exact computation splits curvature and frame factors,
projects each link onto Haar moments locally, and measures the
remaining sparse boundary support before joining. A modular
nonzero result with an admissible prime certifies nonzero
rational amplitude. Reconstructing signs and normalized
covariances requires rational reconstruction with a bound or
a separate argument. A zero residue alone is inconclusive.

The [split-layer replay](l1_extended_split_layer.py) sums both
endpoint frame choices at each opposed center in the restricted
(0,1)-plane sector. Integrating independent endpoint links
before assembly leaves only the fourth moments and the six
two-slot products of second moments. The replay reproduces the
one-anchor control and gives 9995625/131072 for the full
anchor-summed layer, including the action factorials. Each
direction has 380 nonzero post-Haar entries, at most 38 masks
per tuple, and the join peaks at 38 masks. Four independent
layers give the fourth power of this result. Mixed-plane
couplings between layers still require a separate contraction.

Independent review of `f9aabb718` reproduced both layer
values and the sparse counts. It verified the two single-anchor
terms, six two-plus-two assignments, the relative rescaling
24 for the second-moment products, and the action factorials.
The next assigned test retains a mixed-plane link between
sheets and measures the post-Haar boundary of that coupled
join. The verified layer is a control for the split projection.

The [inter-sheet replay](l1_extended_inter_sheet.py) switches
centers 0 and 6 to plane (0,2). It sums both frame anchors.
Every curvature plaquette still has a private port, even
though four link variables are shared by curvature and frame
factors. Conditional Haar integration removes the curvature
dependence while retaining those frame variables. The
resulting four-center cycle has 38 rows at every boundary
and contributes 21690819140625/34359738368. Two remaining
two-center cycles reproduce the prior anchor-summed value.
The unswitched control also reproduces four independent
layers. Independent review of `5f0335be0` reproduced the
four shared links, sparse counts and all three exact cycles.
The reviewer independently lifted the four-center join to
128-bit global exterior masks and reproduced the top coefficient.
A loop with no private curvature port remains the next test.

The [coupled-curvature replay](l1_extended_coupled_curvature.py)
covers a different restricted sector. Each of two longitudinal
sheets has four plaquettes, every curvature link lies in two
plaquettes, and no port can be integrated privately. After
integrating the transverse frame factors and saturating the
active center, local gauge conjugation leaves only three
chiral radial channels per center. The sheet contractions
use the SU(2) character basis. Schur integration forces a
common representation around a sheet and gives the fourth
power of the inverse representation dimension. All 81
channel assignments and 6,561 sheet joins contribute.
The exact bounded coefficient is
2686789328589557725241742448284154145239249/79407184549937850344905113600000000.
It differs from the independent-Haar control, which the same
frame tensors reproduce when supplied independent moments.
Independent review of `1a7f330b7` reproduced the coefficient
and independently counted four free index loops and eight Schur
edge pairings, verifying the inverse fourth power of the
representation dimension. It also checked the local gauge
rotation and the two chiral radial character expansions.
This sector has shared curvature links but no shared
curvature/frame link variables.

### Saturated sector with shared curvature and frame links

At each x₃=0 site take one (0,1) and one (0,2) vertex.
At each x₃=1 site take two identical (0,1) vertices. For
frames along axis 1 or 2 at x₃=0, choose the link anchored
at the lower endpoint. Anchor all other frames at the
center. Direct incidence counting gives degree eight at
all 16 sites and even link parity. Link degree pairs
(curvature, frame) are (4,0) on 24 links, (2,0) on eight,
(0,2) on 24 and (2,2) on eight. Thus all 40 curvature
links lack a private single-use port.

The eight shared links form two squares along axes 1
and 2 at x₃=0, one at each x₀. A spanning tree can include
three links from each square and gauge-fix them to identity
for a gauge-invariant closed-order word. The two remaining
shared links carry independent cycle variables before
contraction with the other factors. The first shared-link
projection is being computed with both curvature indices
and frame exterior masks retained. The census alone gives
no value for the full signed integral.

The [shared-link replay](l1_extended_overlap_projection.py)
integrates the two curvature coordinates and two actual
frame factors on one shared link. The 36×36 fourth-moment
matrix has 92 nonzero entries and rank 35. The projected
boundary retains 1,600 frame labels and 10,752 nonzero
entries, with rank 35 and maximum Gaussian component 14.
The only quadratic relation is equality of the two chiral
unit norms. The surviving channels comprise one scalar,
nine traceless quadratic channels for each chirality, and
sixteen mixed-chirality products. The physical scale uses
the fourth-moment denominator 48 and two factors of 1/4
from the frames. The full motif still requires joining the
remaining link and exterior boundaries.

Independent review of `72842b97f` reproduced all counts and
the rank. The Haar matrix is the Gram matrix of quadratic
polynomials on S³×S³. The common norm supplies the scalar
channel and the norm difference supplies its sole null
direction. Same-chirality fourth moments give weight 2
per pairing in the 48-scaled matrix, while mixed second
moments give weight 3. The review verified the reversed
frame anchor and absence of an extra factorial in collecting
ordered coordinates into symmetric monomials. The next
assigned contraction uses the spanning-tree reduction to
measure the two remaining mixed cycle boundaries.

An explicit tree consists of the eight (x,3) links for
x=0,…,7, the link (0,0), and (x,1), (x,2), (x⊕2,2) for
x=0,1. A union check confirms the 15 links connect all
16 sites with no cycle. After fixing the tree, the two
shared links are (4,1) and (5,1). They belong to the same
two longitudinal plaquettes and can be projected jointly.
Of 24 distinct plaquettes, the counts with one through four
live ports are 2, 4, 2 and 16. A separate curvature-only
projection at (2,0) couples four incident faces. These two
patches are being evaluated before assembly of the motif.

The [two-link strip replay](l1_extended_overlap_strip.py)
projects both remaining shared links. It retains four
longitudinal coordinate legs, two chiral curvature vector
indices and the quadratic frame coordinates. Each of the
four chirality blocks has 2,304 nonzero rows. The
same-chirality blocks have 76,608 entries each and the
opposite-chirality blocks have 36,864 each. The largest
row holds 70 entries. These signed integers have denominator
48² before the frame exterior tensor is joined.

For the separate four-face link, the replay fixes the other
boundary links to identity except for four coordinate unit
values of the retained link (6,0). The exact projection
has 276 nonzero vector components over denominator 48.
This checks one family of boundary slices. The complete
four-face tensor and full motif contraction remain open.

Combining the four chirality blocks over common frame
coordinates gives 528 rows up to sign and 584 occupied
columns. Exact rational elimination gives rank 455. Each
individual frame map is injective on its rank-35 Haar image,
as checked in the single-link replay. Their tensor product
preserves rank on the strip subspace. The 455 channels
therefore survive application of the two frame maps before
external site saturation. This is smaller than the 1,225
channels of two independent rank-35 interfaces.

Independent review of `59044ed5b` and `3a598282d`
reproduced rank 455 and checked the closed-loop indices,
Haar denominators, and frame-map injectivity. The four-face
control uses Q†, Q, R†Q and Q†R on the four faces, with
R=(6,0). Unit-coordinate R inputs verify the diagonal
coefficients of its homogeneous quadratic boundary slice.
Mixed-coordinate coefficients remain outside that control.

The full [four-face replay](l1_extended_overlap_four_face.cpp)
retains linear coordinates for (2,1), (3,1), (6,2), (7,2)
and the symmetric quadratic pair for (6,0). The exact
48-scaled projection gives 173,664 nonzero entries across
25,088 boundary monomials, with at most 21 entries per row.
It recovers the unit-coordinate control. The separate Python
identity-slice calculation also retains the mixed coordinates
of (6,0): 408 additional terms supplement the 276 equal-coordinate
terms. Independent review of `25d25d380` reproduced the
entry and monomial counts, checked the closed face orientations
and complete boundary keys, and verified the Haar denominator.
The complete motif still needs the remaining boundary joins.

The [exact rank check](l1_extended_overlap_four_face_rank.py)
takes the row dump from the C++ replay. Chirality partitions
the column support into eight blocks. Each same-chirality
block has rank 60 and each of the six two-plus-two blocks
has rank 36. Their disjoint column supports give total rank
336. The next projection joins the retained quadratic (6,0)
leg to both remaining occurrences in the (4,0,1) and (6,0,1)
plaquettes before applying its fourth moment.

The [factored (6,0) replay](l1_extended_overlap_u6.py)
takes the four-face row dump and projects that quadratic
leg together with both remaining curvature occurrences.
The projected left factor has 343,440 entries and the
two-face right factor 147,456. All 64 ordered interface
slots contribute. The remaining boundary includes four
old linear ports, four new linear ports along axis 1,
and a quadratic (4,0) port. The combined Haar denominator
for the two integrated links is 48². A direct identity
boundary specialization reproduces all 672 nonzero
components. Keeping the factors separate avoids materializing
791,285,760 raw products before cancellations. Independent
review of `f1cf1a8ce` replayed a fresh C++ four-face dump and
accepted the orientations, interface indexing and Haar weight.
The identity control changes contraction order using shared
input tensors. Downstream joins remain open.

The [exact rank replay](l1_extended_overlap_u6_rank.py) combines
ordered pairs into 36 symmetric channels. Over the rationals the
left factor has rank 35 and the right factor has full column rank 36,
so the contracted tensor has rank 35. The left relation is
(L_{77}=L_{00}+L_{11}+L_{22}+L_{33}-L_{44}-L_{55}-L_{66})
with zero-based indices. Eliminating this channel increases the
raw product count from 744,256,512 to 840,896,640 by densifying
the right factor. Carry the sparser 36-channel form into the (4,0)
projection, which can be performed on the right factor before
forming outer products.

The [right-factor replay](l1_extended_overlap_u4_pair.py) projects
(4,0) with the (0,0,2) and (4,0,2) plaquettes. It then absorbs
(5,0,2) and projects the shared curvature-only links (4,2) and
(5,2). The additional Haar denominator is (48\cdot16).
The replay yields 2,737,152 nonzero entries across the 64 ordered
U6 slots, peaking at 54,432 in a slot. It retains the mixed-frame
coordinates and the open (1,0) and (5,0) ports. Independent review
accepted `da06554ca` after replaying the exact commit and reproducing
the counts. The reviewer checked the three closed orientations
(U_4^\dagger), (J^\dagger K U_4), and (K^\dagger V^\dagger J W),
the two (1/4) second moments, the ordered fourth-moment slots
with no extra permutation factor, and the five curvature indices.

For the next join, add (5,0,1) and project (4,1) and (5,1)
with the frame tensors. The (4,0,1) plaquette was already
absorbed at U6. Using the entire earlier mixed-link strip here
would count that plaquette twice.

The right boundary can also be grouped before the mixed-frame join.
For an off-diagonal U6 pair, add its two ordered right tensors
coefficient by coefficient because the corresponding left tensors
are equal. After removing zero coefficients this gives 2,083,968
entries in 36 symmetric channels, with at most 62,208 entries in
one channel. This is an exact reindexing with the same Haar weight.

The [mixed-frame replay](l1_extended_overlap_mixed_frames.py)
constructs the two-endpoint frame attachment for either surviving
shared link. Its exact fourth-moment numerator has 734,304
nonzero complex coefficients across 36 rows and 175,104 distinct
boundary keys. The unprojected and projected row ranks over Q(i)
are both 35. Every projected exterior mask has local site
populations (3,3,1,1). The replay emits the integer real and
imaginary components separately. Independent review accepted
the reversed upper anchor, exterior signs, and denominator
`48 * 4^4` at `018c2a823`. The independent replay was byte-identical
to the author dump. A [direct quartic cubature control](l1_extended_overlap_mixed_frames_control.py)
also reproduced the entire exterior-mask maps for five fixed
coordinate and curvature slices, including cross-chirality pairs.
The join to the curvature boundary remains open. Feed the projected
frame tensors the raw shared-link curvature coordinates so each
link is integrated once.

The [fixed-boundary composition replay](l1_extended_overlap_mixed_strip_control.py)
contracts the already projected two-link strip against the raw frame
maps. For the two emitted pairs of fixed exterior boundaries it gives
432 and 288 nonzero curvature outputs, respectively. Both controls
are real and retain their signed coefficient histograms. This tests
the attachment across both shared links. The full contraction should
apply complementary site masks while the factors are separate.

The [upper local block replay](l1_extended_overlap_upper_block.py)
exhausts all 441 pairs of unordered curvature channels. Exactly
36 survive, with both local curvature pairs diagonal. Each survivor
has the same 216-entry exterior tensor, with populations (2,2,6,6)
in low, low, upper, upper site order. The four translated blocks
therefore contract with complementary lower masks of populations
(6,6,2,2). No upper curvature label has to cross that interface.
Each upper sheet uses the squared-curvature weight
`(6 - chi_L - chi_R)/4`, where the two characters are spin-one adjoint characters.
Character orthogonality leaves the constant channel and two
spin-one channels, giving `(6/4)^4 + 2*(1/4)^4/3^4 =
52489/10368` per sheet. The full upper factor uses its square and
the repeated-vertex factor `1/2^8`. Independent verification
and the final exterior contraction remain open.

The upper replay exposes the 216 signed lower complements in
local site order [x, x^4, x^8, x^12], for x=0,1,2,3.
The coefficient includes the exterior sign for lower-mask wedge
upper-mask. The generator matched the review-side scratch table
coefficient by coefficient. The upper normalization is the squared
sheet scalar divided by `8^16 * 4^32 * 2^8`, including the sixteen
raw second-moment factors and the repeated-vertex weights. Reordering
whole site blocks has even parity here because each site population
in the upper factor is even.

A lower-column replay matched 8,736 fixed original masks against
216 upper complements. The 31,488 compatible pairs reduce to
9,088 live mixed masks carrying 59,312 Gaussian coefficients.
The measured direct continuation still has 170,968,703,152
products over curvature labels. The column contraction therefore
splits the fixed mixed pair at the two crossing Grassmann bits.
Each upper-projected block absorbs its own fixed vertex and
retains only the incoming and outgoing bit indices, an 8 by 8
interface. The exact factored replay is in progress.

The [lower half-column replay](l1_extended_overlap_lower_halves.py)
builds both signed factors. Each has 78,144 entries in 64 crossing
channels across 288 retained endpoint masks. On the fixed mask
pair (7,16), (193,64), all 11,712 nonzero curvature coefficients
match the direct unsplit contraction exactly. This control caught
an overall minus in the first split: the endpoint crossing and
the standalone middle-byte swap cancel. The replay uses the
corrected signs.

The [full lower-column join](l1_extended_overlap_lower_join.cpp)
removes every exterior mask and emits 2,321,664 real nonzero rows
over 36 coordinate pairs. Generate the two half files with
`l1_extended_overlap_lower_half_dump.py OUTPUT_DIR`. Run the
mixed-frame replay and keep its seven-column numeric rows only
(`awk 'NF==7 && $1 ~ /^[0-9]+$/'` removes import diagnostics).
Compile the join with `c++ -O3 -std=c++17`, then pass half0,
half1, and mixed rows in that order. The replay matched the
author's complete sorted output byte for byte. The author also
matched all 44,736 rows of the (0,0) pair to the unsplit evaluator.

Output rows are the shared pair, the packed base-6 curvature
key, and real and imaginary numerators. The curvature order
for the first column is mixed x4,x6,x0,x2 followed by original
x0,x4,x2,x6. Translate sites by XOR 1 for the other column.
The lower denominator is `48 * 4^16` per column. The upper
blocks retain their separate normalization. The remaining
curvature-only join has yet to be evaluated.

Independent review accepted `6de1392e6` for the exterior
contraction. The reviewer regenerated both half files and the
mixed input, compiled the exact commit, and reproduced every
row byte for byte. The output SHA-256 was
`3f15a76fc3ae9af4f3340cfc14626feebee2839c0fb25ead9cf2750ee37bf702`.
Review checked the packed curvature order, the reversed crossing
channel, the exterior signs and the denominator. The two stages
performed 216,702,848 and 1,351,772,160 products without checked
overflow or imaginary output. The acceptance covers the exterior
contraction through the column boundary.

For the curvature-only join, incidence counting gives four
private degree-four axis-0 links per column. Each of the 16
transverse links occurs once in each column before tree fixing.
Group the faces into four strips along the undirected transverse
square. In each strip the two pure transverse links A and B
appear in faces of the form `P=A† X B Y` and `Q=B† Z A T`.
With normalized Haar measure set `A=X B Y P†`. Then
`Q=B† Z X B Y P† T`. Averaging the conjugation over B gives
the scalar part of ZX in each chiral quaternion factor.
For common chirality the projected vector-coordinate pair is
`-scalar(ZX) * vec_j(Y e_i T) / 4`, by the second moment of P.
Opposite chirality integrates to zero by independence and
centering. This removes the pure transverse pair analytically
before the time-link cycle. Exact coordinate controls and the
remaining network contraction are pending.

The [identity-transverse cycle control](l1_extended_overlap_identity_cycle.py)
pins every transverse link to the identity and integrates all
time links. The independent character calculation gives
46,798,847,841,893,967,231,713,280 per column before exterior
and upper normalization, using 23,616 contributing column rows.
The two columns decouple under this specialization. This control
also rejects equality filtering on the inverse-oriented face
labels. Four edges with vector label pair (0,1) have a nonzero
moment of 1/3456. The earlier diagonal-only mixed-boundary scratch
value is therefore excluded from the full boundary calculation.

The [transverse pair control](l1_extended_overlap_transverse_control.py)
checks the analytic projection on all 2,304 quaternion-basis
components by summing the two independent second moments directly.
It reproduces all 144 nonzero components and every zero. Each
expression is multilinear in X, Y, Z, and T, so the basis check
covers arbitrary quaternion inputs in the common-chirality block.

The [corrected temporal cycle replay](l1_extended_overlap_column_time.py)
takes the full lower column dump, retains all six path labels,
integrates the temporal and mixed links, and fixes the eight pure
transverse links to identity. It yields 132 even-column and 30
odd-column boundary entries, with 64 live join assignments.
Before exterior and upper normalization, its value after the
temporal Haar denominator is
`475206911416848403432581016416162736561360748937216`.
Setting the mixed links to identity as a separate control gives
`46798847841893967231713280` in each column, matching the
independent character replay. The unrestricted join still needs
the pure transverse integrations.

The [dual-column strip replay](l1_extended_overlap_pure_strip.py)
implements the pure pair projection with two temporal pair indices
at each endpoint. Its fixed nonpure-anchor branch emits 165,540
nonzero coefficients over 648 curvature label quadruples. The
largest quadruple has 256 entries, and the two endpoints use 484
and 1,096 paired states. Each coefficient carries a common
denominator 4. The mixed-anchor branch retains its four spatial
coordinates for the cycle join. The strip replay checks an
intermediate tensor, with the paired-node cycle still to be closed.

The [all-link zero-label control](l1_extended_overlap_all_links_alpha0.py)
closes the full Haar network for the sector in which all exterior
curvature labels are zero. It integrates the eight pure transverse
links, eight temporal links, and both mixed links. Of 256 candidate
mixed assignments, 16 contribute. After the temporal and pure
transverse factors `48^8 * 4^4`, the sector contributes
`55210154735836356378659569767502493257826304` before the
remaining exterior and upper scales. This is one signed sector
of the full sum. The other curvature labels remain to be contracted.

The [curvature numerator bound](l1_extended_overlap_curvature_bound.py)
uses the exact column coefficient sum with a conservative factor
of two for off-diagonal coordinate pairs. Each quaternion
coordinate and curvature vector component has absolute value at
most one under normalized Haar measure. Squaring the column bound
and applying the curvature denominator `48^8 * 4^4` therefore
bounds the absolute raw numerator by a 261-bit integer. A product
of pairwise coprime moduli greater than twice that integer allows
unique signed reconstruction. This bound precedes exterior and
upper normalization.

The [signed gauge-block replay](l1_extended_overlap_gauge_block.py)
evaluates the entire all-left block with both shared coordinate
pairs (0,0). The two exterior columns each contribute 1,641
rows. The factored gauge kernel has 100 paired temporal states
and gives 2,247,513 nonzero products in the 2,692,881 candidate
row pairs. The gauge dot products are bounded by 97,221,869,568,
so the sparse Gram calculation fits signed int64. Exterior
coefficients and their signed accumulation use Python integers.
The exact value after `48^8 * 4^4` is
`1959689171103691034414437601649194086717980672` before exterior
and upper normalization. The other coordinate and chirality
blocks remain part of the required signed sum.

Independent review accepted the exact block at `159825103`.
The reviewer reproduced the value and checked the two paths
`H S3ᵀ F S0 H` and `S2 H S1ᵀ`, their common endpoints,
and the row-one-norm bound. The mixed coordinates change S2
only, so the first path can be reused within a chirality topology.
The [chirality replay](l1_extended_overlap_chirality_control.py)
also checks all 2,321,664 exterior coefficients under simultaneous
interchange of the two chiral factors. Haar moments and quaternion
multiplication are identical in the two factors. The full gauge
contraction can therefore pair globally flipped blocks with equal
contributions. The unrestricted block scheduler remains open.

The [unrestricted scheduler](l1_extended_overlap_scheduler.py)
enumerates 589,194 compatible coordinate and chirality blocks,
covering 94,748,063,904 candidate signed exterior pairs. It sums
all raw mixed placements for each block before its sparse Gram
products. The replay with `--signature 00000000 00000000 --limit 3`
completed 8,075,361 pairs in three blocks and returned raw subtotal
`36470954866014950021831666988213349744589679523499452051488768`.
This run reused the fixed left path across all three blocks.
The scheduler provides an exact baseline and bounded slices for
verification. The remaining cost motivates checking additional
symmetries before running the unrestricted sum.

The [signed rotation replay](l1_extended_overlap_rotation_check.py)
checks all exterior coefficients under two quaternion rotation
generators in each chirality. All four signed comparisons match.
Conjugation preserves the gauge contractions, and the coordinate
signs appear in both the exterior and gauge factors and cancel.
The [orbit census](l1_extended_overlap_schedule_orbits.py) combines
these rotations with global chirality interchange. It selects
35,084 representatives, covering all 589,194 blocks and
94,748,063,904 candidate pairs with orbit weights. Evaluating
the representatives still requires 5,166,551,904 candidate
pairs, 32 left kernels and 1,600 right kernels.

The [orbit runner](l1_extended_overlap_run_orbits.py) accepts
the exact column file and a half-open range of representative
indices. It asserts weighted block and candidate-pair coverage
before starting, then emits one line per completed representative
with its index, weight, pair count, nonzero count, signed numerator,
and elapsed time. The first two representatives reproduced the
unreduced scheduler values with weights 2 and 6. A complete sum
requires every index exactly once, weighted by its orbit size.

The [orbit reducer](l1_extended_overlap_sum_orbits.py) regenerates
the schedule from the same column rows, rejects missing or duplicate
indices and inconsistent weights or pair counts, and only then sums
the signed numerators. A two-index replay matched exact arithmetic
and exercised the incomplete, duplicate and inconsistent controls.

The all-left signature replay completed 218,921,616 weighted
candidate pairs in 121 seconds. Its raw subtotal before global
chirality doubling is
`493558895505829437085178565821657728079248882488555076558258176`.
This is one complete signature, with the others still owed.

The exact column scan also gives a common divisor of
`23906980319527578894336`. Dividing both column tensors by it
leaves maximum coefficient magnitude 3,264 and weighted one-norm
733,410,816. The resulting signed curvature numerator has absolute
bound `3880292686383659548704577595375616` (112 bits). A checked
signed 128-bit accumulator can hold the scaled total and partial
sums bounded by the same absolute estimate. Restore the square of
the divisor before applying the physical normalization.

The tracked scheduler now divides the exterior weights by their
common factor inside the kernel. It bounds each signed int64
batch by its maximum absolute product, adds the batch totals
with Python integers, and restores the common factor squared.
A two-representative replay matched every prior index, orbit
weight, candidate count, nonzero count, and signed numerator.

The indexed runner preserves the full schedule while emitting
exact zeros for incompatible temporal chirality. At each unfixed
node, the fourth moment is zero unless the incident strips have
equal parity of their two chiral labels. The three unfixed nodes
of the pinned column still connect all four strips. The other
column has all four constraints. Exhausting all 4,096 coordinate
quadruples confirms the local Haar rule. Exactly 770 of the
35,084 representatives survive this necessary condition.

The unpruned kernel independently checked excluded signature
(00101000,00000000) at coordinate pairs (0,0),(0,0).
All 900,909 exterior pairs give a zero gauge block. The
opposite signature also gives zero. The excluded even
signature has strip parities (1,1,0,0), which disagree at
unfixed nodes. This control does not impose a constraint
at the pinned temporal root.

The unrestricted run uses the verified lower-column SHA-256
`3f15a76fc3ae9af4f3340cfc14626feebee2839c0fb25ead9cf2750ee37bf702`.
Its half-open output ranges are [0,2) and [2,11) under
`91bc5e71d`, [11,66) under `09552bf0d` with parity pruning,
and [66,35084) under `4bb50163c` after the empty-strip packing
repair. Independent review
replayed indices 65 and 66 across the repair boundary and matched
negative index 10747 with plain Python-integer accumulation.
The packing repair preserves row, column and coefficient order
semantics. The reducer applies `48^8 * 4^4` for curvature,
`(48 * 4^16)^2` for the lower frames, and
`8^16 * 4^32 * 2^8` for the upper frames and repeated vertices,
then multiplies by the squared upper-sheet factor.

The unrestricted run completed all 35,084 orbit records.
The exact reducer validated the unique indices, weights and pair
counts covering 589,194 blocks and 94,748,063,904 candidate pairs.
It returned raw signed numerator
`4549345865844500133837056022073964680182394381773293174409658368`.
After all curvature, exterior and upper scales, the selected
finite motif coefficient is
`1057574865922986076396613/3696469150265516934764386546876416`.

| Half-open shard | Records | SHA-256 |
| --- | ---: | --- |
| [0,2) | 2 | `d487deadea8c31337cecc5ac5ffcceaff79a30e3e0422f9b07b7f4ecbe277b32` |
| [2,11) | 9 | `c0d4aa7fb4885a3be2bd5e3752f44a4d72894197aa9df94e8b6a189777bebbde` |
| [11,66) | 55 | `a94d6412e0793b1abe95a0c138ef3a1b84406daf1e823c73e89d07e796e8280e` |
| [66,35084) | 35,018 | `7f3a9f22590f96a728b01dd49cb7cd822b0affe2b66a38c43d99e6fc5ba41d1d` |

The shard digests include elapsed-time fields. A fresh run can
compare the first five fields independently of timing. The full
sum is ready for independent result review. The selected motif
still needs to be placed in the full physical matching calculation.

Independent review accepted the selected finite motif at
`1b7941250`. A separate integer reducer matched all four shard
digests and the regenerated column digest, verified 35,084 unique
indices and counted 1,480,986,408 weighted nonzero pairs. It
reproduced the signed numerator and applied the combined
denominator independently. This is a single order-`g2^32`
normalization word with the specified planes and anchor choices.
The sum over other words and the order-`g2^30` two-source
numerator remain separate open constructions.

The [upper source replacement replay](l1_extended_source_upper.py)
tests the selected same-site cross term `-2 G22(8) G33(8)`
with outgoing frame anchors in place of the two repeated upper
action vertices. All six diagonal channels at the other site
reproduce the same 216-entry upper exterior block. All 15
off-diagonal channels vanish. The punctured curvature sheet
retains only the trivial character and contributes `27/8`
in place of `52489/10368`. Removing one repeated-vertex
factorial and including the source cross term gives the ratio
`-139968/52489` to the selected normalization word. The
resulting candidate numerator term is
`-60445514255728976151/79228162514264337593543950336`.
Independent review of the insertion anchors and normalization
is pending. The term belongs to one selected source word.

The replay checks both positions within an upper block, for 42
exact channel comparisons. Translating the selected replacement
across the eight upper sites gives eight distinct missing
action-vertex choices with the same coefficient. The subtotal
for this specified family is
`-60445514255728976151/9903520314283042199192993792`.

Independent review accepted the selected replacement at
`23f7be09d`. The replay found 84 source masks. At site 8
the outgoing axis-2 and axis-3 frames use the same anchors
as the action vertices they replace, preserving the four
raw frame and two Haar second-moment factors. Schur
orthogonality propagates the trivial representation from
the missing face across the punctured sheet. The reviewer
reproduced the exact single-site coefficient. The two-position
replay at `00a6572f2` checks the local identity needed for
the eight-word subtotal. This uses identical upper blocks
with the lower anchor choices held fixed.

Independent review accepted the eight-word subtotal at
`00a6572f2`. It replayed all 42 channel comparisons and
verified the independent outgoing links at each local site.
The ordered embeddings into the four upper blocks preserve
the exterior tensor coefficientwise. This holds with the
lower network fixed. Either upper sheet can be punctured,
and there are eight distinct choices of the missing
repeated action vertex.

For this fixed replacement, the two diagonal terms in
`(G22(x)-G33(x))^2` vanish before Haar integration. Removing
the repeated action vertex removes degree four at x and
degree two at each of the distinct neighbors x XOR 4 and
x XOR 8. A same-anchor square restores degree four at x
and four at one neighbor, yielding degrees ten and six
at those neighbors. The top form requires degree eight
at both. This degree argument is specific to the fixed
remaining action word and the outgoing source anchors.

The [direct square replay](l1_extended_source_squares.py) verifies
the square-term exclusion with exact fourth-moment cubature. Each
square has 38 nonzero local masks. Joining all 21 remaining
curvature channels gives site populations (0,2,6,8),
(4,2,6,4), (2,0,8,6), or (2,4,4,6), depending on the site
and axis. None complements the fixed lower tensor.

The [separated upper source replay](l1_extended_source_separated.py)
enumerates the degree-compatible replacements among two removed
upper action vertices and two outgoing upper sources. There are
16 same-site cross-term orderings and eight separated-site
placements before restoring the symmetric source order. For a
separated placement, the outgoing axis-2 source shares the
retained action link and requires a fourth moment. At both local
positions all off-diagonal channels vanish and the diagonal
blocks retain the original 216-mask support. The raw coefficient
ratios are 24 and 36. With the relative Haar denominator of 24,
the reweights are 1 and 3/2 by mask. The lower contraction must
use these reweighted complements to determine the separated
subtotal. Independent review of this intermediate is pending.

Independent review accepted the separated upper tensor at
`a1eee3c4a`. All diagonal maps at both endpoints are identical.
The raw relative factor is `(96 * 2^4 * 8^2) / 8^4 = 24`.
The [half-column writer](l1_extended_overlap_lower_half_dump.py)
accepts `--separated-half 0` or `--separated-half 1` to
replace one local upper complement. The replacement carries
an extra factor of two to keep every coefficient integral.
The first regenerated half pair matched the scratch input
byte for byte. The first modified column has 2,321,664 rows.
The second position is being evaluated separately.

Both modified lower columns have 2,321,664 rows and identical
SHA-256 `0efc3eeb5329ae9499e36b22c77346542da36c360498beee41ca5fb74caffd41`.
The local upper endpoint maps are identical. The time-bit
translation exchanges columns while preserving the anchor
convention. Before pinning the temporal root, a residual gauge
transformation permits either column's root to be fixed.

The [separated orbit replay](l1_extended_source_orbits.py) takes
the baseline and modified column files, a half-open index range,
and the baseline orbit shards. It records 34,314 parity zeros,
450 coefficientwise proportional blocks and 320 recomputed
blocks. Its complete receipt has SHA-256
`bf6102da684a4c3ee03809de143d195b7c7d8021de3acaabe4bc0305899f9d65`.
The [source reducer](l1_extended_source_sum.py) removes the
extra factor of two and reproduces the eight separated terms
`-45709102752653698569/4951760157141521099596496896`.
Together the eight grouped same-site and eight grouped separated upper terms contribute
`-151863719761036373289/9903520314283042199192993792`.
Independent review of the completed signed sum is pending.

The expanded degree and Haar-parity census covers the 284
distinct ways to remove two vertices from this fixed action word.
It finds 104 degree-compatible placements, counting distinct
source sites once and retaining both axis orders at coincident
sites. Link parity leaves 40 such placements. Each removes both
repeated vertices at one upper site. They comprise 16 coincident
axis orders, eight separated upper pairs, and 16 low/upper
pairs. Restoring both source orders for distinct sites gives
64 ordered contributions. The low/upper family is the remaining
sum for this fixed action word. The census covers this word only.

Independent review accepted the separated upper signed sum at
`af10b752f`. It reproduced the coverage and normalization,
checked all proportional reuses against the exact columns,
and verified the modified rotation and chirality symmetries.

The [low/upper source replay](l1_extended_source_low_upper.py)
uses the tree-fixed outgoing axis-3 link at the low source.
It checks both upper positions and both choices of upper axis-2
link. Each case gives 504 exterior masks. All diagonal
curvature channels coincide within each case and all
off-diagonal channels vanish. The 288 additional masks must
be tested against the lower tensors. The lower and final
signed joins remain in progress.

The [lower–upper reuse control](l1_extended_source_low_upper_control.py)
checks all 78,144 half-tensor entries at both local sites and in
both half positions. The unshared replacement equals the physical
separated upper tensor S. The shared replacement equals
`(5 S - 3 B)/2`, where B is the baseline tensor. These equalities
hold coefficientwise after removing the extra factor of two in
the shared and separated integer inputs. Linearity of the
remaining contraction gives the shared lower–upper subtotal
`-275754484759350057237/19807040628566084398385987584`.
Adding the eight unshared terms, the same-site terms, and the
separated upper terms gives
`-762318335292037598091/19807040628566084398385987584`
for all degree- and parity-compatible replacements of the
selected action word. Independent review of the complete
selected-word result remains pending.

Independent review accepted the complete selected-word sum at
`1ec500284`. Its fully ordered census checked 284 removals,
192 degree matches and 64 parity survivors, 16 per source family.
It verified the fixed low-link normalization, the common `-2`
factor for grouped sources and the half-tensor identities at all
four placements. A separate full-column check also reproduced
both linear identities on all 2,321,664 coefficients. The two
lower–upper column SHA-256s are
`848994f93cf75af43a45d2b87990983065d6daed06cb20e1041467b6bdf844ea`
and `b8b70a2ef3e28b618d9c02231ddc4352cd4a1cd53d66311348d692049b0a7eb8`.
The next scope is the full action-word census for both the
normalization and the two-source numerator.

### Full action-word support and aggregation

The [repeated-vertex census](l1_extended_repeated_support.cpp)
restricts to one action variant repeated twice per site. Each
site then requires two incoming frame incidences. The two
checkerboard classes give independent counts of 2,970 plane
assignments. Each plane assignment has four frame-anchor
choices per site, with even link parity from repetition.
This subclass alone has 37,885,477,021,286,400 distinct
saturated, Haar-even multisets. The count concerns support
conditions. The signed coefficients can cancel or vanish.

For the ordered support count, first fix center-plane
multiplicities. At an undirected frame edge with F frame
occurrences, changing one anchor toggles both directed link
parities. Let p and q be the two curvature parities. If F is
positive, feasibility requires `p XOR q = F mod 2` and gives
`2^(F-1)` anchor assignments. If F is zero, both p and q must
vanish. These factors multiply independently across frame
edges for a fixed labeled center-plane word. The number of
center-plane orderings is the multinomial coefficient. The
source quartics shift the target site degrees and add even
link powers. This removes explicit anchor enumeration from
the support count. The signed evaluator still has to sum
the corresponding exterior and Haar tensors with their
actual coefficients and factorial weights.

The [anchor-marginalized replay](l1_extended_anchor_census.py)
reproduces 51,930 ordered words for the collapsed six-action
source control from just 14 center-plane patterns. The existing
explicit-anchor support routine counts 185 multisets and gives
the same ordered total. For the extended regulator, duplicating
one plane at every center with one prescribed removed plane
gives 1,578,561,542,553,600 candidate multisets for a fixed
same-site cross source. This is a lower bound on structural
support, prior to signed contraction. The next pilot measures
frontier growth by summing site degrees and edge parities as
soon as the contributing centers have been processed.

The [center frontier pilot](l1_extended_center_frontier.cpp)
keeps partial site degrees, directed curvature parity and
frame-edge support and parity. It aggregates identical states
after each center. The first three steps retain 208, 10,312,
and 647,597 states. None has a closed site or edge constraint.
The fourth step reaches the one-million-state cap after
2,749,529 attempted joins. This measures the cost of retaining
complete center labels even in the support-only calculation.
The signed construction needs earlier link and exterior
elimination. The cutoff gives no bound on the physical result.

For signed aggregation, collect the actual quadratic coframe
bilinears in a vector B. The action and source are quadratic in B,
with a symmetric coefficient matrix C depending on the links
and couplings. Formal Wick contraction of the auxiliary variables
with covariance C sends `exp(J·B)` to `exp(Bᵀ C B/2)`.
The top exterior coefficient at fixed J is a fermion determinant.
There are four barred and four unbarred generators per site,
so changing from grouped to site order gives even parity.
On the extended bipartite lattice the fermion matrix has blocks
`[0,A;−A†,0]` for real J and fixed unitary links. Its determinant
is `det(A) det(A†)`, with A of size 32. The Wick covariance can
be indefinite, so the fixed-J determinant sign gives no sign
bound after Wick contraction.

The [exact Wick control](l1_extended_wick_det_control.py)
uses the actual coframe endpoint matrices on a nontrivial
fixed link and an indefinite covariance with a diagonal
difference source. Its 35 determinant-product monomials
reproduce the independent exterior coefficients
23,923,344, 1,703,040 and 324,480 at source powers zero through
two. Full lattice Wick and Haar contractions remain open.

Independent review accepted `b92bfa301`. It checked the
formal identity over a characteristic-zero coefficient ring
with symmetric covariance and commuting even coframes,
and reproduced the three signed control coefficients. The
[fixed-link checkerboard replay](l1_extended_wick_checkerboard_control.py)
also checks the full 64 by 64 hopping matrix with both
anchor orientations. Its exact determinant equals the product
of the squared norms of the two 16 by 16 chiral determinants.
The factors share auxiliary variables. Their Wick expectation
must still be evaluated jointly with the link Haar integrals.

The [joint local Taylor and Haar cut](l1_wick_haar_cut.cpp)
retains all 18 action labels of a two-site, three-collapsed-axis
lattice and integrates one Spin(4) link with seven links fixed.
It joins complementary exterior masks while applying spherical
moments. Modulo 65,537, the three source coefficients are
63,737, zero and 30,791. A separate accumulation order forms
the global exterior polynomial first and gives the same residues.
The quadratic source join uses 270 signed monomial products.
This pilot checks an interleaved contraction on a restricted
cut. It leaves the other link integrations and the 16-site
coefficient calculation open.

The dense cut (`2 1 1` arguments) uses doubled quaternions,
including the integrated link. The closed action vertex has
link degree six and the source vertex degree two. At source
order h, divide the raw residue by `2^(24-4h)` to recover the
unit-link control. The raw residues are 62,538, 264 and 1,349.
A separate replay using unit coordinates in the polynomial
builder returned 18,700, 32,752 and 64,188, which matches the
homogeneous rescaling exactly. Local and global accumulation
orders agree at each source order. The linear term can be
nonzero on this cut with seven links fixed.

The [explicit local pairing replay](l1_wick_haar_paired.cpp)
checks the Wick recurrence coefficientwise against the Taylor
powers before joining with Haar moments. The [rational lift](l1_wick_haar_cut_crt.py)
uses both embeddings of the imaginary unit, an eleven-prime
176-bit modulus against a 162-bit numerator bound, and an
unused prime 65,293. After unit-link normalization the exact
coefficients are 385,114,112, 1,081,344 and 88,408,064,
all real. This resolves the exact one-link dense control.
The unrestricted lattice still requires the joint contraction
of the other links and centers.

### Two independent link integrations

On the same dense cut, the paired replay with the final argument set to
`1` integrates both axis-2 links, at sites 0 and 1, leaving six fixed.
It retains all 18 action labels. Four independent sphere moment factors
replace two. Each quartic factor uses at most two occurrences of active
links, so the top exterior coefficient has total active degree at most
eight. Sixteen four-bit exponents suffice for this cut.

The paired local join and the separate global exterior accumulation
give residues 8,647, 56 and 29,951 modulo 65,537. The rational lift
(`--two-links`) gives real unit coefficients **287,430,656, 229,376 and
83,791,872**. The four-sphere denominator LCM is 11,520 and the
176-bit reconstruction passes the withheld prime 65,293. Independent
review recompiled both evaluators, checked the exponent and denominator
bounds, and reproduced the residues and exact coefficients.

Replay with a C++20 compiler, from this directory:

```sh
c++ -std=c++20 -O3 l1_wick_haar_paired.cpp -o /tmp/l1-wick-haar-paired
python3 l1_wick_haar_cut_crt.py /tmp/l1-wick-haar-paired --two-links
c++ -std=c++20 -O3 l1_wick_haar_cut.cpp -o /tmp/l1-wick-haar-power
/tmp/l1-wick-haar-power 2 1 1 65537 256 1
```

The same paired replay now also projects the site-0 link first,
accumulating a polynomial in the site-1 link before applying its Haar
moment. At the first prime and embedding, 334,508, 58,104 and 41,144
signed products survive the first projection. They combine into 401,
919 and 578 nonzero monomials, respectively. The executable checks
equality to the direct joint projection before emitting each CRT
residue, including the withheld prime. The one-link invocation still
gives its original raw residues. Independent review reproduced the
residues and boundary counts and verified the exterior sign at
saturation. This cut closes both Wick centers and saturates all
exterior masks before the first link projection. A full-lattice cut
through an unfinished Wick center must also retain unmatched
auxiliary indices.

On the full lattice, an elimination schedule must close a link only
after its last contributing factor and project a site onto its top
exterior component only after its last contributing factor. Until
then the boundary must retain both chiral moment exponents on each
open directed link and the actual exterior occupancy on each open
site, with signs carried in the coefficients. Keep source order and
its signed insertion weights through the join. A support count that
keeps only parity and degrees cannot perform this contraction. The
next full-geometry control is to compare this elimination order with
the existing selected 16-site normalization motif before admitting
all center-plane factors.
Extending the staged calculation requires revisiting exponent and
denominator bounds and evaluating the joint contraction over the
remaining links and centers. The physical susceptibility and its
window remain open.

### Staged center contraction on the extended opposed word

The [opposed-word replay](l1_extended_opposed.py) exercises staged
elimination on the 16-site repeated-plane word with disjoint curvature
plaquettes and frame links. It projects the curvature tensor against
one Haar-integrated frame, sums the eliminated frame index and retains
the second frame label and the exact exterior mask. There are 380
nonzero boundary terms across ten second-frame labels. Joining that
frame and only then imposing center saturation gives exactly the same
38-term center polynomial as the direct contraction. Complementary
exterior saturation of each opposed pair returns 61875/262144,
including the repetition factorials. The four disjoint layers give
14657531890869140625/4722366482869645213696.

This replay uses the same local Haar tensors as the direct calculation.
Independent review reproduced the equality, boundary counts and exact
coefficient. The equality checks the order of tensor contraction and the delayed
center saturation. The disjoint opposed word is separate from the
35,084-record shared-link motif. The next shared-link control needs
to retain open link moment indices until both incident factors are
joined.

### Staged projection on the two shared links

The [mixed-link strip replay](l1_extended_overlap_strip.py) now sums
the two curvature faces in their raw coordinate-pair basis. It applies
the fourth-moment map on the first shared link against that link's
frame-coordinate pair, retains the second link's raw curvature pair,
and then applies the second fourth-moment map. Each link contributes
one factor of 48 in the integer numerator convention. Frame-coordinate
labels remain open for the subsequent exterior attachment.

The staged and simultaneous projections agree on all 9,216 nonzero
rows and all 226,944 signed entries. Independent review reproduced the signed equality and exact rank 455.
The fixed-frame composition replay also completed with 432 and 288
nonzero outputs for its two boundary choices. Both projections use
the same quaternion and moment tables, so their agreement checks
elimination order and boundary indexing. The strip covers two faces
of the shared-link motif. Full source insertion and unrestricted
lattice normalization remain open.

The [early frame attachment replay](l1_extended_overlap_mixed_strip_control.py)
applies each Haar map to its actual fixed-mask frame slice, then attaches
the first slice before closing the second link. It retains the raw
second-link coordinate pair during the intermediate contraction. Each
output is accumulated with exact integer real and imaginary parts.
The full signed maps agree coefficientwise with late frame attachment
for both tested boundary pairs, with 432 and 288 nonzero rows.
This tests actual frame data at fixed exterior masks. The exterior
join over all masks and the unrestricted action-word sum are separate.
The previously accepted selected-word source numerator at `1ec500284`
provides a signed end-to-end control for an unrestricted evaluator.

Independent review also reproduced a mixed-phase slice with 432 purely
imaginary outputs. It checked the positive exterior interleaving sign
and the combined integer scale `48² × 4⁸`.

### Moving the mixed-link Haar map across exterior closure

The lower-column exterior map acts at fixed shared-link pair and is
linear over Gaussian integers. The fourth Haar moment mixes only the
shared-link pair, so the two maps commute. This lets the replay close
the entire lower exterior boundary in raw coordinates and apply the
Haar map afterward, with the same factor of 48 as early projection.
It also works when one lower half is replaced by the separated-source
tensor. These are lower-column checks. The remaining curvature and
other columns still enter the full numerator and normalization.

From this directory, generate and compare the two orders:

```sh
mkdir -p /tmp/l1-frame-close
work=/tmp/l1-frame-close
python l1_extended_overlap_lower_half_dump.py "$work"
c++ -std=c++17 -O3 l1_extended_overlap_lower_join.cpp -o "$work/join"
python l1_extended_overlap_mixed_frames.py --raw |
    awk 'NF==7 && $1 ~ /^[0-9]+$/' > "$work/raw.rows"
python l1_extended_overlap_mixed_frames.py |
    awk 'NF==7 && $1 ~ /^[0-9]+$/' > "$work/projected.rows"
for mode in raw projected; do
    "$work/join" "$work/half0.rows" "$work/half1.rows" "$work/$mode.rows" > "$work/$mode.closed"
done
python l1_extended_overlap_closed_control.py "$work/raw.closed" "$work/projected.closed"
```

For the separated-source check, regenerate the halves in a separate
directory with `--separated-half 0` and use the same raw and projected
mixed-frame inputs.

The base run matched all 2,321,664 signed coefficients in 36 groups.
Independent review checked the raw keys and compared the late projection
against its separately generated early-projection reference
(`3f15a76fc3ae9af4f3340cfc14626feebee2839c0fb25ead9cf2750ee37bf702`).
The raw export switch also reproduced the exact input used in the run.

With the separated-source replacement at half 0, both orders again
matched all 2,321,664 coefficients across 36 groups. Independent
review matched the raw-derived result to the known projected source
column and checked that only the intended half changed. This supplies
a full-mask source-column control for the next extension across
action-word sectors.

### Two-source contribution from the disjoint opposed word

The [opposed-source replay](l1_extended_opposed_source.py) evaluates
all two-source replacements of the disjoint repeated-plane word
with four identical action vertices at each of the eight even-parity
centers. Removing one vertex at each of two distinct centers leaves
odd powers on their private curvature links. The sources touch only
the transverse frame links, so those terms integrate to zero.

Removing two vertices at one center leaves bilinear deficits
`(4,2,2)` at the center and its two transverse neighbors. The
ordered degree census forces one source per incident transverse
edge. Each source may be based at either endpoint. A source based
at the action center shares the link and uses a fourth moment. A
source based at the other endpoint uses the separate reverse-directed
link and two independent second moments. The signed layer coefficients,
including the surviving action factorials and both source orders, are:

| Separation bits | Layer coefficient |
| --- | ---: |
| 0 | −22275/16384 |
| 4 | −2025/2048 |
| 8 | −2025/2048 |
| 12 | −6075/8192 |

All eight choices of removed center have the same contribution.
Multiplying by eight and by the three unchanged layer factors gives
`-15830134442138671875/36893488147419103232`. Independent review
reproduced the four layer coefficients and subtotal, and checked the
private-link parity, distinct directed anchors, and factorials.
This is a second exact selected-word numerator contribution. Other
action-word sectors and the full signed denominator remain open.

### Sum over the repeated anchor choices

The same replay now sums all four directed frame-anchor choices at
each of the eight active centers, for 65,536 assignments at fixed
curvature plane and checkerboard. The four vertices at any center
use a single repeated anchor choice. The transverse undirected edges
are distinct across active centers, so the directed choices preserve
the disjoint-link factorization. The reversed action coframe and the
source based at the other endpoint keep their distinct matrix
orderings.

Each transverse layer sums the 16 opposed-center anchor pairs. For
the source layer, the remaining two action vertices at the affected
center use the same anchor pair and the sources can occupy either
directed link on each incident edge. The replay then sums four
possible affected layers and multiplies by the three unchanged layer
factors. The sector normalization is
`14657531890869140625/72057594037927936`. Each of separations
0, 4, 8 and 12 contributes
`-15830134442138671875/2251799813685248` to the numerator.
Their sum is `-15830134442138671875/562949953421312`.
Independent review reproduced the normalization and all four
separation coefficients. The equality across separations follows from
this anchor sum.
Mixed anchor choices within a center's repeated vertices and
other curvature words are outside this sector.

### Mixed anchors and the homogeneous opposed orbit

For a fourth moment of the sum of the two action anchors, the two
uniform terms and all six labeled two-plus-two assignments survive
directed-link parity. The mixed terms factor into two independent
second moments, including when gamma labels repeat. The replay
brings all terms to the same `96² × 8⁴` frame scale. In the source
layer, the insertion has even degree on its directed link. The two
surviving action factors on each edge must therefore use the same
anchor, with both choices included.

Independent review reproduced the one-checkerboard normalization
`9982511481025756988525390625/295147905179352825856` and numerator
`-151675751259254608154296875/144115188075855872`. The four separation
coefficients are equal. Permutations and translations give twelve
equal normalization terms over the six planes and two checkerboards.
For the specified shear, same-center deficits require both frame
directions to be 2 and 3. Distinct-center removals still have odd
curvature-link parity because each source is even on its link.
Only the two checkerboards with curvature plane (0,1) contribute to
the numerator. Independent review checked these orbit factors.

The remaining plane-homogeneous configurations with nonalternating
opposed pairs across transverse layers can share curvature links.
They require a joint curvature contraction. Other action sectors
and the unrestricted lattice sums remain open.

### Private-link elimination for the other layer patterns

Each of the four transverse frame layers chooses one of two opposite
center pairs. For a fixed curvature slice the chosen plaquettes are a
subset of the four faces of its periodic square. Any nonempty proper
subset has a directed link used by just one remaining face. With all
other links fixed, that face is a left and right translate of a Haar
link or its inverse. Its holonomy is therefore conditionally Haar and
can be integrated out while the other faces retain their integrands.
Repeating this step gives independent Haar holonomies for every
proper subset, including subsets whose original faces share links.

The replay checks all 16 layer patterns against the actual directed
plaquette incidences. Fourteen peel completely. The two constant
patterns each fill two curvature slices and have no private link in
either slice. For each of the fourteen, the frame layers still close on
opposed pairs and the source degree census gives the same two-link
replacements. Two distinct removals leave an odd directed curvature
edge. An outgoing source cannot repair its parity because it is even
on its directed link. Consequently the normalization of this family
uses 84 copies of the single pattern, and the specified shear
numerator uses 14. The two constant patterns remain for a joint
four-face contraction.

The exact replay gives normalization
`209632741101540896759033203125/73786976294838206464`
and numerator `-1061730258814782257080078125/72057594037927936`.
Independent review confirmed the incidence census and the conditional
Haar argument. These totals already include the two disjoint
checkerboard patterns.

### Joint curvature integral for the constant layer patterns

The [torus replay](l1_extended_opposed_torus.py) handles the two
constant patterns. Each fills two separate four-face curvature
slices. Within a slice, independent gauge rotations at the four
base sites conjugate the corresponding holonomies independently.
The curvature links are separate from the transverse frames, so the
average can be taken coefficientwise before frame attachment.
Only the scalar radii of the two chiral imaginary quaternion vectors
remain after this angular average.

Expand the resulting radial polynomials in SU(2) characters.
For scalar coordinate q₀, the needed characters are
`1`, `4q₀²−1` and `16q₀⁴−12q₀²+1`. The sum of the chiral spins
is at most two for a fourth moment and one at a source center.
Opposite orientations at every shared edge let Schur orthogonality
identify a common representation throughout each connected slice.
The eight link integrations contribute dimension to power −8,
and the four vertex index loops contribute dimension to power 4,
giving dimension to power −4 per chirality. This is the torus
character contraction, as in the [finite-lattice character formula](https://arxiv.org/html/1901.09830#S2).

The two slices have separate link measures. Their characters couple
through the four transverse frame layers, so the replay takes the
fourth power of each fixed-channel layer contraction before summing
channels. For the source it replaces one layer, retaining the two
action factors at the affected center, and sums the four placements,
two affected centers per layer and two source orders. The trivial
channel reproduces the independent-Haar normalization and numerator
at every source offset.

Independent review reproduced the normalization and source coefficients
for one constant pattern. The normalization agrees with the earlier
coupled-curvature replay at `1a7f330b7`. The two patterns are
translations, so they have equal coefficients. Combining them with
the fourteen peelable patterns and the plane multiplicities gives
the complete homogeneous opposed family:

- Normalization: `21486793742471357002066547707988743988989249/6617265379161487528742092800000000`.
- Two-source numerator: `-1048423566519771992133385501445/62257761248769736704`.

The four source offsets contribute equally in this family. Other
curvature-plane assignments and center multiplicities still enter the
unrestricted lattice sums.

### Mixed curvature planes on the two checkerboards

The [mixed-plane cycle replay](l1_extended_mixed_plane.py) sums the
sector with four action vertices at each active checkerboard site and
a single curvature plane per site. It includes every frame-anchor
assignment for those vertices. The two complementary frame
directions at each active site give two incident edges. Saturation
requires exactly two incoming frame edges at each passive site.
The enumeration gives 2,970 plane assignments per checkerboard.

Every face has a directed link based at its own active site that is
private to its curvature factor and outside the protected frame
links. A face based at another active site can reach that link
neither at its base nor after one step to a passive site. This
justifies the independent Haar reduction for all 2,970 assignments.
The frame incidence graph is a union of even cycles. A transfer
matrix retains the four-generator mask on each passive boundary.
Its sign wedges the preceding outgoing mask with the next incoming
mask. Closing each cycle by a trace gives the saturated coefficient.

For a source replacement at one center, its two frame axes must
be 2 and 3. Distinct-center removals give odd curvature-link parity.
The modified trace uses the two-source tensor at the affected
center, with the two source orders and the remaining action
factorial. The homogeneous normalization and all four source
offsets are exact controls for the transfer implementation.

For both checkerboards together the normalization is
`894775334784931468048095703125/147573952589676412928`.
The signed numerator is
`-4491709929939096221923828125/144115188075855872`,
distributed equally across offsets 0, 4, 8 and 12. Independent review
reproduced the census and both totals.
These totals already include the homogeneous global checkerboards.
The other homogeneous layer patterns are separate. Mixed planes
within a center and general center counts remain open.
