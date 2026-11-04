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

### Two centers with mixed curvature planes

The [two-center replay](l1_extended_two_mixed_centers.py) starts from
the even checkerboard with frame axes (2,3). At sites 0 and 9 it
replaces two of the four vertices by vertices with frame axes (0,2).
The replacements exchange passive endpoint incidences and preserve
the required degree at every site. All ten curvature faces peel
with both directed anchors of every frame edge protected.

At each changed center the common frame axis has four factors and
the other axes have two each. The replay uses the anchor-summed
fourth and second moments and two independent curvature second
moments. It retains 84 local exterior coefficients. A site mask
closes only after its final incident tensor, with its full
eight-generator block removed after saturation. The all-homogeneous
control reproduces the previously checked exact normalization.

Independent review reproduced the representative coefficient
`123512167576473721435546875/9223372036854775808`, including the
`(2!)²` divisor at each changed center. Axis permutations and
translations preserve the measure and coefficient because the
plane multiplicities are even. The replay enumerates 192 distinct
images, giving normalization contribution
`370536502729421164306640625/144115188075855872`. This orbit has
two planes at two centers and is disjoint from the one-plane-per-center
sector. Other mixed-center words
remain open.

The same replay now evaluates the two-source numerator for this orbit.
Removing action vertices from two different based faces leaves an
odd directed curvature link. Each outgoing source has even degree
on its link, so only two removals from the same face survive. Degree
matching requires one source on each complementary frame edge.
At a mixed center the surviving face retains its two frames. The
shared frame edge carries two action factors and one source, and the
removed face's other edge carries a source alone. The implementation
keeps the two directed endpoint choices separate on each edge.

For either frame-pair role, all four endpoint choices give equal
coefficients after summing the eligible affected centers. For the
baseline pair each is
`-53430265908021716455078125/576460752303423488`. For the secondary
pair each is `-8441946259170128173828125/576460752303423488`.
Each role matches the specified shear on 32 of the 192 images,
and the roles have distinct frame pairs. The summed orbit numerator
is `-30936106083595922314453125/2251799813685248`.
Independent review reproduced both endpoint tables and independently
enumerated the frame-pair multiplicities.

### Census and contraction of balanced two-mixed-center words

The [census replay](l1_extended_mixed_center_census.py) covers four
vertices at each checkerboard center, with exactly two centers split
2+2 across distinct planes and the others using one plane. In units
of two vertices the pure centers give even passive degrees. The
symmetric differences of the two mixed centers' passive neighbor
pairs must therefore coincide. Distinct active centers share at
most two passive neighbors, so the symmetric difference has size
two and each mixed center has one unchanged frame axis. Choosing
opposite endpoints at the two changed centers gives a balanced
pure assignment. The replay reverses these reciprocal swaps from
the known balanced assignments and deduplicates the resulting words.

Per checkerboard, the census gives 12,192 fully peelable words,
576 words with two unpeeled curvature faces, and 384 words with
four. Parity-preserving translations and axis permutations reduce
these classes to 73, three and three orbits, respectively.
The joint cases require explicit curvature and frame moments.

For all 73 peelable orbits the replay contracts the signed exterior
tensors exactly. It sums the four source endpoint choices at each
eligible removed plane before contracting. Averaging the six shear
pairs over axis permutations gives the contribution for the fixed
shear. Both checkerboards together give normalization
`2923108773834037462646484375/144115188075855872` and source numerator
`-30307783239724343994140625/281474976710656`. The totals include
the earlier selected 192-word orbit and exclude the six joint
curvature orbits.
Independent review reproduced the full census and normalization and
checked the source contraction against the exact 192-word control.
The full source aggregate was executed locally.

### Conditional kernels for the six joint curvature orbits

The [conditional core replay](l1_extended_mixed_curvature_core.py)
retains the directed links used by the frames. For the three two-face
cores the remaining faces share one unprotected link. For the
three four-face cores the unprotected links form a four-edge cycle
on the faces. Each unprotected link occurs once in each incident
holonomy and twice in each incident curvature square. Its join is
therefore an exact fourth-moment contraction of two coordinate
pairs. When the cycle closes, the last two partial tensors share
two live links and both Haar factors must be applied.

The replay compares coordinate-pair contraction with direct
fourth-order cubature of the same conditional integrals for all
six representatives, including cross-chirality labels. Independent
review reproduced all 18 controls. In a fixed
unit-quaternion slice the same-chirality control gives 1/24, 1/24
and 1/8 for the two-face cores and 41/10368 for each four-face core.
One cross-chirality control is negative, −1/16. The conditional
kernel integrates the unprotected links. The next calculation
must keep the protected link dependence through the frame join
and integrate those links jointly to obtain the sector coefficients.

### Joint moments on the protected frame links

The [protected-link frame replay](l1_extended_mixed_frame_moment.py)
enumerates the frame degrees on the six curvature cores. In a
two-face core, two protected edges carry two frame factors and
four carry four. In a four-face core, four edges carry two and
four carry four. Each protected directed link occurs in one core
face. Thus its frame tensor needs one retained curvature coordinate
pair, with moments up to degree six.

The replay expands each frame in unit quaternion coordinates. It
keeps the two possible directed anchors separate, sums ordered
frame slots over their allowed even allocations, and inserts the
coordinate pair on the protected anchor only. Degree-six sphere
moments have a common integer scale of 192, including mixed
chiralities on the product group. The two-anchor result has Haar
scale `192²` and raw frame scale `4^n` for n frame factors.
For every symmetric gamma tuple, summing the four diagonal probes
of either chirality inserts the unit norm and reproduces the
previous exact frame tensor with the scale adjusted. Independent
review checked the incidence, moment scaling and selected probes. The
full local replay computed 3,240 tensors and checked all 180 norm
identities. Individual off-diagonal coefficients share the same
moment implementation.

The remaining join must combine these exterior tensors with the
open coordinate-pair indices of each curvature core. The completed
frame tensors alone do not give the joint orbit totals.

### Protected-frame attachment on fixed gamma slices

The [frame-attachment replay](l1_extended_mixed_frame_join.py) attaches
all six protected frame edges in each two-face core. It uses gamma
labels equal to the frame-axis labels and chooses a compatible
curvature component from the nonzero Dirac trace entries. Each face
retains the raw coordinate pair of the shared unprotected link until
the two exterior factors join. The signed contraction has 600 entries
on each face boundary and 84 entries after the shared-link Haar
projection, in each of the three orbits. Reversing the attachment
order and swapping the joined factors preserves every coefficient.
Independent review reproduced the two-face result.

The coordinate scale for this fixed-label boundary is
`48 × 192¹² × 4²⁰` before the Dirac trace weights and remaining frames and action factors.
The contraction preserves exact Gaussian integers and uses a
complement lookup for sites whose fixed degrees add to eight.
The four-face replay pairs the two faces at each mixed center first,
closing one shared link and the saturated frame endpoints in each
pair. The final join closes the two remaining links together.
For the fixed labels, each face has 27,360 input exterior entries
across its two open links. Reversal of the contraction order
preserves all 2,702 coefficients after the last Haar projection.
The other four-face representatives have translated core incidences.
The replay checks equality of the full translated attached factors
before reusing the closure. All three representatives passed the coefficientwise check. Whole
site blocks have even occupancy,
so that translation carries no exterior sign.
The raw scale here is `48⁴ × 192¹⁶ × 4²⁴`. The remaining gamma
labels, Dirac trace weights and exterior factors still have to be
summed to obtain an orbit coefficient.

### Full exterior closure and remote gamma sums

The same replay now joins the unprobed frame tensors to the retained
core exterior boundary and saturates all 128 generators. It applies
the peeled-face Haar moments, the selected residual Dirac trace
weights, and the factorial of each repeated face. The translated
four-face core is mapped back before attaching the remaining frames.
Reversing the factor order preserves the saturated coefficient.

A second contraction sums every gamma channel at a center if its
faces have all peeled and neither directed anchor of any of its frame
edges occurs in the attached core. These centers use the existing
full pure- or mixed-plane tensors. This leaves the gamma channels
at coupled centers fixed. Independent review reproduced the two-face
fixed-label coefficients and checked the gate and normalization of
the remote sums.

| Core | Fixed-label coefficient | Remote centers summed | Partial gamma sum |
| --- | ---: | ---: | ---: |
| Two faces, each representative | `1579577626270265625/1237940039285380274899124224` | 5 | `8885124147770244140625/37778931862957161709568` |
| Four faces, first representative | `390359454918280734375/9903520314283042199192993792` | 4 | `243974659323925458984375/2417851639229258349412352` |
| Four faces, second representative | `88199871071686734375/19807040628566084398385987584` | 4 | `55124919419804208984375/4835703278458516698824704` |
| Four faces, third representative | `83950203115186734375/19807040628566084398385987584` | 4 | `52468876946991708984375/4835703278458516698824704` |

The four-face exterior boundaries coincide after translation.
The coefficients differ once the remaining frame factors are included.
The remaining gamma channels at the protected-edge centers and the
other residual curvature components are needed for complete orbit
coefficients.

### Summing residual Dirac components

The frame-join replay now expands both curvature occurrences at each
residual face over its nonzero Dirac trace components. It multiplies
each ordered component pair by the two trace weights before attaching
the frames. Both orders of a mixed component pair are included.
The `--single-component` option reproduces the earlier controls,
with the same trace weight applied at the face.

The complete residual-component run for all three two-face
representatives gives 1,200 entries per attached face and 84 after
the shared-link join. The saturated fixed-gamma coefficient is
`3159044015968265625/618970019642690137449562112`. Summing gamma
channels at the five remote centers gives
`17769622589821494140625/18889465931478580854784`. Both values are
four times the one-component controls. Independent review checked
the ordered multiplicities and placement of trace weights.

The join indexes each right-hand exterior factor once by the masks
that must complement the left factor. It precomputes prefix parity
of each right-hand mask for the exact wedge sign. Ten thousand
128-bit controls matched the existing direct sign calculation.
The four-face path compares the full translated input geometry
and frame tables before reusing the attached closure. The expanded
four-face replay completed for all three representatives. Each face
had 185,792 input entries and each joined core had 2,702 exterior
entries. The saturated fixed-gamma coefficients and the remote
gamma sums were sixteen times their one-component controls.

### Gamma sum at a pure center with two protected edges

The [paired-probe replay](l1_extended_protected_center.py) now sums
all local gamma assignments at a pure center while retaining one
curvature coordinate pair on each of its two frame edges. In all six
cores, a protected pure center has both protected links directed
from the passive endpoints. Its own curvature face has already
peeled, so its fourth moment can contract the local gamma labels
before the external probe indices are joined.

The replay first eliminates the gamma tuple of one frame, then
reuses that partial tensor across probes on the second frame.
It uses the existing staged exterior projection. The integer
scale before the action factorial is `48 × 192⁴ × 4⁸`.
Summing the diagonal probes of either chirality on both edges
reproduces the 38-entry unprobed tensor at the adjusted scale.
Independent review reproduced a norm control and checked both
directed anchors, multiplicities and remapping. The exhaustive
local run computed all 1,296 probe pairs. Of these, 488 have
nonzero rows, with 16,480 exterior entries in total.

This tensor supplies the pure-center factors for the joint
contraction. Its two open probes must still be joined to the
residual curvature faces and to the mixed-center gamma tensors.

### Gamma sum at a mixed center with two residual faces

The [mixed-center gamma replay](l1_extended_mixed_center_gamma.py)
sums all local frame gamma labels while retaining one coordinate
pair on each protected edge and one curvature-component pair on
each residual face. The incidence check covers all six cores.
Both exclusive axes use protected links based at the mixed center.
The common axis has no probe and uses the existing anchor-summed
fourth frame moment.

The face weights enumerate ordered gamma and curvature occurrences
before folding the symmetric labels. Exchanging common and exclusive
axes reverses both Dirac traces and preserves their product.
The integer frame scale is `192⁴ × 4⁴ × 96² × 8⁴`.
The residual curvature link moments and the two repeated-face
factorials enter when joining the core. Independent review
reproduced the two norm controls, which integrate independent Haar
faces as a check and recover the previously verified 84-entry
mixed-center tensor. At scalar-coordinate probes the replay found
111 live component rows with 4,278 exterior entries. At the
mixed-chirality probes it found 291 rows with 41,904 entries.

Both pure- and mixed-center gamma factors are now available. The
joint orbit calculation still has to join their open probe and
component indices against the residual curvature factors and
close the exterior masks. The mixed-center replay exercises two
probe pairs and does not enumerate the entire two-probe table.

### Full gamma closure for fixed probes in the two-face cores

The [two-face gamma replay](l1_extended_two_face_gamma_join.py)
extracts the protected coordinate-pair coefficients on each
residual face and joins the one free link with its Haar fourth
moment. It applies that component kernel to the mixed-center gamma
tensor, attaches the two gamma-summed protected pure centers and
the five remote centers, and saturates every exterior site. The
independent review checked the trace multiplicities, all moment
scales and the repeated-face factorials. Its replay matched both
tested assignments on all three representatives.

With all six protected probes set to `(0,0)`, the kernel has 12
component rows and 86 mixed-core exterior entries. The saturated
coefficient is `277641541909346923828125/37778931862957161709568`.
With all six set to `(0,4)`, there are nine rows and 144 entries,
and the coefficient is `243274383544921875/75557863725914323419136`.
Both closures are exact and invariant under reversing factor order.

The unsummed face has 6,000 distinct protected probe triples.
Joining the two face supports before attaching frame tensors
would consider 130,658,304 compatible free-pair products in the
first representative. The incidence check shows that two of each
face's three protected probes belong to the same pure center in
all three representatives. The next contraction can sum those two
probes against that center first, leaving one protected probe and
the free link on each face. The fixed-probe coefficients above
are controls for that sum. The targeted coefficient extractor also
matched the full raw face expansion on 24 exact slice checks.

### Pure-center fusion and remote exterior boundary

The two-face replay can now sum each face's two pure-center probes
before joining the residual faces. It multiplies the raw curvature
row by the full pure-center gamma tensor and accumulates over both
probe pairs exactly once. The fused row retains a residual curvature
component pair, the mixed-center probe and the free-link pair.
Every one of the six faces gives 3,456 fused rows and 110,784 signed
exterior entries. Restricting both summed probes to the original
assignments reproduces the exact fixed-probe face controls.

The five remote centers contract to an environment with 84 entries
on four passive sites in each representative. A site outside this
boundary is projected onto its full exterior block only after its
last incident factor. The final lookup pairs a boundary mask with
its signed complement. The local replay reproduced all six
fixed-probe coefficients by both this boundary closure and the
direct full-lattice closure. Independent review checked the fusion
indices and the complement signs.

The two fused pure-center factors share one passive site. Their
masks there are complementary degree-four masks, and the other
three passive sites are still needed to close against the mixed
center and the remote environment. The next join can use this
complement alongside the free-link Haar matrix. The mixed probes
and residual curvature-component labels still have to be summed.

### Two-face normalization with one first probe open

The two fused faces can now join on the free-link fourth moment and
the complementary masks at their common passive site. The two pure
center blocks are already saturated. The remaining join contracts
the mixed-center tensor and remote environment against the signed
exterior complement. The replay recovers both fixed-probe controls
when all six probes are restricted.

With only the first mixed-center probe restricted to `(0,0)`,
the other five probes and every gamma label are summed. Each of
the three representatives gives 384 joined component and probe
rows and coefficient
`999591240231406494140625/73786976294838206464`.
Independent review checked the exact Gaussian signs and divisor.
The cached gamma blocks also matched the direct local evaluator
in twelve exact comparisons.

Use `--first-probe 0` for this shard, or `--all-probes` for all
36 first-probe indices in each representative. The latter applies
the orbit multiplicity and the factor of two for the second
checkerboard only after all selected shards finish. The optional
`--orbit` restricts a run to a single representative. The full
two-face normalization and source numerator remain open.

### First-probe classes under signed quaternion permutations

For normalization, split the selected directed link into two
independent formal variables, one for its curvature occurrences
and one for its frame occurrences. Both variables transform
with the same endpoint gauge rotations. Each labelled plane and
frame-anchor term remains invariant after transforming the
spinors and summing its internal gamma labels. Product Haar and
the top exterior coefficient preserve this covariance when the
other links are integrated. The residual curvature dependence on
the selected link is homogeneous of degree two.

A unit-quaternion rotation at one endpoint signed-permutes the
four coordinates by a Klein four permutation. Conjugations
permuting the three imaginary axes generate the remaining
coordinate permutations. These operations act independently in
the two chiral factors. For each signed permutation, the curvature
monomial and the corresponding frame insertion acquire the same
sign, which cancels in their contraction. Thus the 36 first
probes have five classes. Each chirality has four diagonal and
six off-diagonal probes. The mixed-chirality class has sixteen.
This argument uses the sum over every other probe and internal
gamma label.

The `--probe-classes` run evaluates one representative of each
class with its multiplicity. The complete `--all-probes` route
remains available as a separate direct check. The replay also
compares the complete fused factors and remote environment in
the same four passive-site roles before reusing a subtotal
between representatives. Each local site block has even exterior
degree, so this relabelling carries no additional wedge sign.
The comparison includes the remote multiplicities that enter
the normalization divisor.

Independent review checked the split-link argument and the
canonical input comparison. A permutation enumeration recovered
the five disjoint classes and all 36 probes. The direct run
reproduced the same coefficient
`28388500213623046875/18446744073709551616` at probes
`(0,1)`, `(0,2)` and `(0,3)` of the first representative.
The full class-weighted subtotal remains pending.

### Completed two-face normalization

The historical two-face and combined two-mixed totals in this section
are under revalidation following the [probe attachment correction](#fused-probe-attachment-correction).

The class-weighted replay finished. Each chiral diagonal class
gave `999591240231406494140625/73786976294838206464` per probe,
each chiral off-diagonal class gave
`28388500213623046875/18446744073709551616`, and the mixed class
gave `3162566986083984375/9223372036854775808`. Independent
arithmetic reproduced the weighted representative subtotal
`999812172304465576171875/9223372036854775808`.

The full canonical inputs matched in all three two-face
representatives. With their multiplicity of 192 and both
checkerboards, the exact normalization contribution is
`8998309550740190185546875/72057594037927936`. Adding the
73 peelable orbits gives
`2941105392935517843017578125/144115188075855872`.
The three four-face normalization orbits remain outside this sum.

### Source terms that delete a residual face

The [deleted-face replay](l1_extended_core_removed_source.py)
removes both action vertices of one residual face while retaining
the original frame protection. The replacement sources use the
two complementary frame edges and preserve their degrees.
Each two-face core then has one face with a private unprotected
link. Each four-face cycle breaks and also peels completely.
The replay checks this on every residual face of all six
representatives before applying the independent Haar tensors.

The exact source subtotal for these deletions is
`-3158571447608642578125/35184372088832` for the two-face cores
and `-22489113943181480712890625/4503599627370496` for the
four-face cores. These contributions include the orbit and
checkerboard weights and the six-axis-pair average. Replacements
at other centers that retain a joint core remain open.

The protected frame replay also supplies a probed source-edge
tensor with two action frames and a quadratic source on either
directed anchor. Independent review reproduced all sixteen
unit-norm controls. At a protected pure center the perpendicular
edges use separate passive-site bytes, with a degree profile of
(8,4,4) after central saturation. All three tested endpoint
configurations recovered 38 entries against independent frame
references for the two directions.

### Two-face source terms at remote centers

The `--remote-source` replay replaces one of the five remote
center tensors at a time and sums the six eligible removed-plane
choices. Each replacement preserves the passive degrees and uses
the original protected frame links. It retains the complete
two-face core. The resulting boundary has the same 84 masks as
normalization, but the weights change by two distinct ratios, so
the source coefficient requires its own contraction.

The fixed-probe controls compare the direct full-lattice source
sum with the fused closure. They agree at
`-84154409757059326171875/590295810358705651712` for the scalar
probe assignment and `-621701202392578125/9444732965739290427392`
for the mixed assignment. They share local source tensors and
therefore check the contraction and placement.

The complete probe-class replay gives the same-chirality diagonal
coefficient `-302980142310624755859375/1152921504606846976`,
off-diagonal coefficient `-8433277130126953125/288230376151711744`
and mixed coefficient `-8082115631103515625/1152921504606846976`.
All three canonical source inputs agree exactly. Applying the
probe weights, orbit multiplicities, both checkerboards and the
six-shear average gives the independently checked subtotal
`-909140718614003173828125/2251799813685248`.
Together with the deleted-face terms, the exact two-face source
subtotal is `-1111289291260956298828125/2251799813685248`.
The source replacements at the two protected pure centers remain open.

### Completed two-face source numerator

The historical two-face and combined two-mixed totals in this section
are under revalidation following the [probe attachment correction](#fused-probe-attachment-correction).

The `--protected-source` replay sums both endpoints on each
source edge before the pure-center gamma contraction. It inserts
the source tensor on one fused face at a time and adds the two
joins. The common normalization divisor is retained by using
a factor of −24 for the two ordered opposite-sign sources and
the replacement of 4! by 2!. Fixed-probe closures match the
direct full-lattice substitutions at
`-546949200591068115234375/9444732965739290427392` and
`-1167717041015625/2361183241434822606848`. The grouped local
source tensor also matches explicit sums over the four endpoint
choices at those probe assignments.

The class coefficients for the protected replacements are
`-1969105346634223388671875/18446744073709551616` per chiral
diagonal, `-30659580230712890625/4611686018427387904` per chiral
off-diagonal, and `-15180321533203125/288230376151711744` per
mixed probe. The three canonical inputs agree exactly. The
weighted protected-source subtotal is
`-5907873741590291748046875/36028797018963968` across both
checkerboards and all three orbits for the specified shear.
Adding the remote-center and deleted-face terms gives the
complete two-face numerator
`-23688502401765592529296875/36028797018963968`.

### Gauge fixing the four-face core

The four unprotected links of each four-face core form a disjoint
matching. Adding three of the four protected links based at the
mixed centers gives a spanning tree on the eight curvature sites.
The incidence replay checked all three representatives. The full
gamma-summed, exterior-saturated integral can set those tree
links to identity using site gauge transformations and invariance
of Haar and Berezin measures. This leaves one live mixed-center
probe and four protected probes at the pure centers. The
fixed-identity frame branch retains the same integer convention
and passed direct action and source checks. These tree choices
apply to the full integral. The fixed-label and fixed-probe
controls keep their existing variables.

The pure centers share two passive sites and saturate them by
complement. Their sites are disjoint from the four passive
sites touched by the mixed centers. The remote environments
retain 1,444 terms on the mixed-center sites and none on the
pure sites. The next replay can contract the pure and mixed
exterior factors separately and join their curvature component
indices. The four-face normalization and the retained-core
source terms remain open.

### Completed four-face normalization

The [tree-gauge replay](l1_extended_four_face_gauge_join.py) fixes
the seven verified links to identity and sums all remaining gamma
and probe labels. Each residual face has one protected pure-center
link. Only one face also has the live mixed-center link. The
pure-center exterior masks close on their two shared passive sites.
The mixed-center masks close against the remote environment on
four disjoint passive sites. The implementation pairs these two
scalar contractions using the four ordered face component labels.
No Haar scale is inserted for the fixed tree links.

Conjugation by signed imaginary-axis permutations preserves the
tree identities. The surviving mixed probe has twelve classes,
with multiplicities (1,3,3,3) in each chirality and (1,3,3,9)
for mixed chirality. Direct enumeration checked that the classes
partition all 36 probes. The replay retains the direct probe loop
as a separate route. Independent review checked the tree, factor
indices, divisor and residual symmetry. Its first exact replay
matched the uncached coefficient
`3952470397264491175048828125/2361183241434822606848`.

The full class-weighted replay completed with these representative
coefficients, before the orbit and checkerboard weights:

| Multiplicity per checkerboard | Representative normalization |
| ---: | ---: |
| 96 | `63238242420019660273681640625/4722366482869645213696` |
| 192 | `223255944709626144287109375/147573952589676412928` |
| 96 | `212498972694735519287109375/147573952589676412928` |

The four-face normalization across both checkerboards is
`252979770023001810375732421875/73786976294838206464`.
Adding the peelable and two-face parts gives the complete
balanced two-mixed-center normalization
`1758825731205986946000732421875/73786976294838206464`.
The four-face source terms retaining the core remain open.
Other center counts and the unrestricted lattice sum remain open.

Independent arithmetic reproduced both normalization totals.
Independent removal enumeration also checked that the remaining
source terms come from the two protected pure and four remote
pure centers in each representative. The four removals at mixed
centers are already in the deleted-face subtotal.

### Completed four-face source numerator

The historical two-face and combined two-mixed totals in this section
are under revalidation following the [probe attachment correction](#fused-probe-attachment-correction).

The `--source --probe-classes` replay inserts the source tensor
at one protected pure center at a time, or contracts the ordinary
pure centers with the summed remote-source environment. The
retained-core cases use the same tree gauge and twelve probe
classes as normalization. For a protected pure center the
common divisor is corrected by −24, accounting for the two
opposite-sign ordered source insertions and 4!/2!. Remote
adjustments are already included in the source environment.
The full source run also reproduced the exact four-face
normalization coefficient.

The probe-summed, all-shear source subtotals before orbit weighting
are:

| Multiplicity per checkerboard | Remote source | Protected source |
| ---: | ---: | ---: |
| 96 | `-122777718908600388373681640625/590295810358705651712` | `-15373615982220589928466796875/147573952589676412928` |
| 192 | `-53368148060444543994140625/2305843009213693952` | `-434199464206081244384765625/36893488147419103232` |
| 96 | `-51024442902222429931640625/2305843009213693952` | `-413278757800081244384765625/36893488147419103232` |

For both checkerboards and the fixed shear pair, the remote
subtotal is `-163164468098516936961181640625/18446744073709551616`
and the protected subtotal is
`-20500326727069564861083984375/4611686018427387904`.
Including the independently replayed deleted-face terms gives the
complete four-face numerator
`-337281185718066541405517578125/18446744073709551616`.
Independent arithmetic reproduced the weighted subtotals. Including
the peelable and two-face terms gives the numerator
for the full balanced family with exactly two mixed centers:
`-2335660581346345132780517578125/18446744073709551616`.

### Size of the remaining even-multiplicity checkerboard sector

The mixed-center census with `--even-center-census` now splits
the eight centers into two halves, counts their passive degrees,
and joins against complementary degrees. Each center has two
unordered plane slots, each representing two action vertices.
In those units the target passive degree is four. The exact
counts on one checkerboard are:

| Mixed centers | Balanced words |
| ---: | ---: |
| 0 | 2,970 |
| 1 | 0 |
| 2 | 13,152 |
| 3 | 41,760 |
| 4 | 224,436 |
| 5 | 607,776 |
| 6 | 1,279,872 |
| 7 | 1,502,112 |
| 8 | 1,065,933 |

Independent replay reproduced these counts. The total is
4,738,011 on each checkerboard. This counts geometric degree
support before signed evaluation. It covers even plane
multiplicities and four action vertices per active center.
The sectors with three or more mixed centers, other plane
multiplicities, and general center counts still enter the
unrestricted sums.

### Peelable words with exactly three mixed centers

The complementary-degree join retains the actual plane labels when
evaluating this sector. It gives 41,760 words on one checkerboard.
Axis permutations and parity-preserving translations partition them
into the following orbits. The core size counts faces left after
removing faces with private, unprotected links.

| Core size | Disjoint-pair centers | Orbits | Words per checkerboard |
| ---: | ---: | ---: | ---: |
| 0 | 0 | 73 | 13,920 |
| 0 | 1 | 22 | 3,744 |
| 1 | 1 | 13 | 2,208 |
| 2 | 0 | 80 | 15,072 |
| 2 | 1 | 23 | 3,744 |
| 3 | 1 | 5 | 960 |
| 4 | 0 | 10 | 1,920 |
| 6 | 0 | 1 | 192 |

At a center with disjoint frame pairs, the product of two independent
second-curvature tensors has four frame edges. Each carries its own
second frame moment. Saturation at the active site leaves degree two
at each of its four passive neighbors. The normalization divisor for
this center is the same as for overlapping pairs:
`48² × 96⁴ × 8⁸ × (2!)²`.

Independent execution of the [census replay](l1_extended_mixed_center_census.py)
with `--three-mixed-normalization` reproduced the following peelable
normalization subtotals across both checkerboards.

| Disjoint-pair centers | Normalization |
| ---: | ---: |
| 0 | `916382184034353565166015625/36028797018963968` |
| 1 | `52039623692311411728515625/18014398509481984` |

The `--three-mixed-source` replay reproduced these normalization
subtotals and evaluated the numerator for a fixed shear pair. At a
disjoint center it replaces one plane's two action slots by two
outgoing source factors, each summed over its two endpoint anchors.
The surviving plane retains its second-curvature moment. Relative to
the normalization divisor the source substitution requires a factor
of `48 × 2!` in addition to the signed ordered-insertion factor.
Independent review checked the combinatorics and replayed both local
source variants, including the passive-site permutation and exterior
degrees.

| Disjoint-pair centers | Source numerator |
| ---: | ---: |
| 0 | `-309232389767181283276171875/2251799813685248` |
| 1 | `-36159881747516299859765625/2251799813685248` |

The next contraction target is the 132 residual-core orbits,
representing 24,096 words per checkerboard. The one-face cores
provide a first check for the disjoint frame pairs with protected
links. Full lattice normalization and the physical B3 matching
remain open.

### One-face cores with three mixed centers

The 13 one-face orbits cover 2,208 words per checkerboard. In
each orbit the face is based at the disjoint mixed center. Its
two base links carry the frame of the peeled face, and its two
upper links carry the frame of the opposite pure center. Thus
all four links are protected. Independent incidence enumeration
verified this geometry and the source removal parity.

The [one-face replay](l1_extended_one_face_gauge_join.py) fixes
three links of the square to identity in the complete integral.
The live base link supplies the residual face's quaternion pair.
The two protected frames at the mixed base use the second Haar
moment of the peeled face. Its complementary frame uses the
component labels of the residual face. The opposite pure frame
uses the same fixed-link tensor as the four-face replay. The
remaining six centers supply the exterior complement. The
tree-fixed links contribute no curvature Haar factor.

The exact normalization subtotal across both checkerboards is
`9946437304000029521484375/4503599627370496`. Independent review
checked the gauge choice, frame labels, divisor and exterior signs.

Each orbit admits 11 source removal types after site and link
parity. Each removes two slots from one plane at one center. One
deletes the residual face, one changes the peeled plane at the
base, one changes the opposite pure center, and eight change
remote centers. The `--deleted-face-source` replay verifies that
deleting the face leaves an empty core and gives the fixed-shear
subtotal `-552933221560551123046875/562949953421312`.

For the retained-face replay the opposite pure and remote source
insertions reuse the two- and four-face tensors. The source at the
mixed base replaces the peeled-plane frame pair with two outgoing
source factors, keeping the probe on the live link. The two
chiral traces of the new probed edge recover the unprobed source
tensor exactly. The base replacement carries the signed adjustment
`−2 × 48 × 2!`, and the opposite pure replacement carries
`−2 × 4!/2!`. The remote boundary sums one replacement at a
time with its own adjustment. Independent review checked these
weights and the canonical square remap.

The `--retained-face-source` exact replay completed all 13
orbits. Across both checkerboards the fixed-shear subtotal is
`-50909654198214352297265625/4503599627370496`. Adding the
deleted-face term gives the full one-face numerator
`-55333119970698761281640625/4503599627370496`.

The next 103 two-face orbits separate into 80 with one free link
and 23 with every link protected. The remaining three-, four-,
and six-face orbits and other multiplicity sectors still contribute
to the full lattice sums.

### Source deletion in the three-mixed-center two-face cores

The [deleted-face replay](l1_extended_core_removed_source.py)
with `--two-face-deleted-source` checks site and geometric link
parity on all 103 two-face orbits. In the 80 orbits with one free
link, either residual-face deletion restores complete peeling.
Their 15,072 words per checkerboard give the fixed-shear numerator
subtotal `-6455243019158686318359375/562949953421312` across both
checkerboards. Each contribution replaces the two action slots of
one residual face and sums the two directed anchors of each source.
The multiplicity is twice the one-checkerboard orbit size, with the
all-axis source sum divided by six to select a fixed shear.
Independent replay reproduced the subtotal and the 80 orbit rows.

The other 23 orbits contain 3,744 words per checkerboard. Either
deletion there leaves a protected face, so the empty-core replay
excludes both source types. Those terms require a one-face
contraction with the affected base tensor.

For the 80 free-link orbits, the two opposite-center roles per orbit
give 160 role occurrences. There are 12 pure roles with two
protected fourth frame moments, 44 overlapping mixed roles with one
protected fourth and one protected second frame moment, and 104
overlapping mixed roles with two protected second frame moments.
The ordinary normalization and retained-face source joins for this
family require these mixed opposite-center tensors.

### Mixed opposite-center tensors for the free-link two-face join

The two curvature faces at an overlapping mixed base share one
unprotected link. Each face has one protected link at the base and
two at its opposite center. Keeping one opposite-center link per
face live leaves five links. The incidence replay verifies that
these five form a spanning tree on six vertices in all 80 orbits.
The full closed integral can therefore fix both base probes, the
free link, and the other upper link of each face to identity.
Each residual curvature component pair then selects a quadratic
probe on its face's remaining live link.

The [mixed-center replay](l1_extended_mixed_center_gamma.py)
with `--opposite-center` constructs the opposite-center tensor in
exclusive, common, exclusive axis order. Both of that center's
curvature faces peel, so the two gamma weights are the ordinary
second Haar channels. The protected links are on the passive
anchors. The protected frame factors use the joint moment scale
`192² × 4^d` for degree `d`. The unprobed exclusive frame uses
`96 × 8²`, and the unprobed common frame uses `96² × 8⁴`.
Multiplying the frame scales by `48² × (2!)²` accounts for the
two peeled curvature moments and the action multiplicities.
The active exterior degree is eight and the three passive
degrees are two, four, and two.

The chiral diagonal traces remove the two probes and recover
the previously evaluated overlapping mixed tensor after scale
conversion. The replay tests both exclusive slots together and
each pairing of the common slot with an exclusive slot.
All six trace controls passed. The representative two-probe and
one-live/one-fixed rows contain 86 exterior entries for the
exclusive pair and 96 for each common-exclusive pair. Independent
review reproduced the spanning-tree census and checked the
fixed-link prescription and frame scales. The global normalization
and retained-face source contraction for these orbits still require
joining both upper factors to the mixed base and remote centers.

### Two-face tree join control discrepancy

The [tree join](l1_extended_two_face_tree.py) contracts both
upper factors against the fixed mixed base and the remote
exterior environment. The reference comparison uses the three
previously evaluated free-link orbits with two mixed centers.
All three tree contractions give
`999693567199179931640625/9223372036854775808` per representative.
The earlier fused probe replay gave
`999812172304465576171875/9223372036854775808`. The tree subtotal
across both checkerboards is
`8997242104792619384765625/72057594037927936`; the comparison
expects `8998309550740190185546875/72057594037927936`.

The default replay asserts agreement with the earlier result.
The three-mixed output from `--candidate` is diagnostic and
remains outside the normalization ledger while this discrepancy
is open. The comparison can be repeated with
`--control --reverse-upper` to change the live link at each upper
center. The fused first-probe route can test the diagonal class
assumption independently of the tree contraction.

#### Fused probe attachment correction

The reverse-upper tree reproduced the initial tree value on all
three control orbits. The direct fused `(1,1)` probe reproduced
the earlier chiral diagonal value, so that scalar-versus-vector
comparison did not explain the discrepancy.

Independent incidence enumeration found a crossed probe assignment
in the fused join. Its face rows are ordered by the exclusive
**frame** axis that the face supplies gamma components for. The
face's local protected link instead lies in its **curvature**
plane, on the other exclusive axis. Thus the base tensor takes
the probe indices in reverse row order while retaining the
component indices in face order. The corrected join asserts this
incidence relation. Independent enumeration confirmed it for the
three control orbits and all 80 free-link three-mixed orbits.

The old equal-probe controls are insensitive to this exchange.
The `--crossed-control` replay compares the fused and direct
contractions with unequal probes bound to their actual links.
The correction affects the earlier fused normalization and the
remote and protected retained-face source replays. Their totals
and the combined two-mixed totals that include them require fresh
evaluation. Deleted-face terms use the separate peeling calculation.

#### Corrected two-face normalization

All three unequal-probe comparisons passed. The two nonzero
direct and fused values were
`240622240501324951171875/37778931862957161709568` and
`−107288360595703125/4722366482869645213696`. After crossing the
base probes, the alternate tree with both live links at the base
reproduced the upper-live value on the first orbit.

The corrected fused class replay gives
`999553002659690185546875/73786976294838206464` for each chiral
diagonal, `15642642974853515625/18446744073709551616` for each
chiral off-diagonal, and
`729823150634765625/2305843009213693952` for the mixed class.
The weighted sum matches the tree value
`999693567199179931640625/9223372036854775808` on the first
representative. The three tree values agree exactly, so the
corrected subtotal across both checkerboards is
`8997242104792619384765625/72057594037927936`.
Adding the peelable and four-face normalization gives the corrected
balanced two-mixed normalization
`1758824638141336633500732421875/73786976294838206464`.

The retained-source replay uses the same corrected probe mapping.
The tree control separately replaces one remote or pure upper
center at a time. The upper replacement carries `−2 × 4!/2!`,
and the remote boundary already carries the corresponding source
weights. Both source subtotals are divided by six for a fixed
shear. The source replays are pending.

#### Mixed upper-center retained-source construction

When a source pair replaces a peeled plane at a mixed upper
center, the surviving exclusive edge keeps its second action
moment. The common edge carries two action slots and a quadratic
source, and the removed exclusive edge carries a quadratic source
alone. Both source endpoints are summed on each source edge. The
probe and fixed-link branches retain the passive anchor convention,
and the unprobed branches use the existing independent Haar
tensors. Independent review checked the frame scales and exterior
signs. The removed peeled moment and its multiplicity give the
signed adjustment `−2 × 48 × 2!` per mixed upper replacement.

The `--opposite-source` replay compares chiral traces against
the existing unprobed source tensor for both removed slots and
all three protected-slot layouts. The tree join accepts the
resulting mixed upper tensors through `--candidate-source`.
The `--orbit` selector allows a focused comparison while the
default enumerates the whole selected family.

The first corrected two-mixed tree source control gives the
fixed-shear representative values
`−101003861826116455078125/288230376151711744` for the remote
insertions and `−656389069332207275390625/4611686018427387904`
for the upper insertions before orbit and checkerboard weighting.
These are provisional pending the corrected fused source comparisons.

All twelve chiral trace checks passed, as did the six
one-live/one-fixed exterior-degree checks. The two-mixed tree
source replay reproduced both representative values in all
three orbits. With orbit and checkerboard weights, the provisional
remote and upper subtotals are respectively
`−909034756435048095703125/2251799813685248` and
`−5907501623989865478515625/36028797018963968`.

#### Retained-source comparison and all-protected deletion path

The corrected fused protected-source replay on the first control
orbit gives `−1969167207996621826171875/36028797018963968`
across both checkerboards. The three tree orbits have identical
values, giving the reconciled upper subtotal
`−5907501623989865478515625/36028797018963968`.

The first corrected remote-source comparison exposed a separate
replay defect. Its fixed-probe control overwrote the outer list of
probe-class indices and weights with a dictionary keyed by directed
links. The final loop then interpreted link coordinates as probe
indices and multiplicities. The emitted selected-orbit total
`−302989267639909423828125/9007199254740992` is rejected.
The replay now uses a separate fixed-probe dictionary and keeps the
class sum intact. The remote subtotal and combined source numerator
remain pending the corrected full comparison.

For the 23 all-protected two-face orbits, the
`--surviving-face-source` option of the one-face replay removes
each face in turn. Both removals leave one face at the same
disjoint base. It fixes both base links and one upper link of that
face. The base carries two source-only factors on the fixed axes
and the surviving second frame pair with open curvature components.
The upper tensor contributes the remaining live-link moment and
the other six centers provide the exterior complement. Independent
incidence enumeration found 42 mixed-upper and four pure-upper
roles across the 46 removal cases. The exact weighted subtotal
requires the full replay.

#### All-protected two-face tree contraction

In the 23 all-protected orbits the residual squares meet only at
their disjoint mixed base. Leaving one upper link live per square
gives a six-link tree on seven vertices. Both choices of upper link
pass the tree check on all 23 orbits. Each face supplies the gamma
weights for the complementary pair of fixed frame axes at the base.
The four fixed frame edges give the base divisor
`192⁸ × 4⁸ × (2!)²`. There is no free-link Haar moment.

The [two-face tree replay](l1_extended_two_face_tree.py) selects
these orbits with `--candidate --all-protected` for normalization
or `--candidate-source --all-protected` for the retained-face
source. The base removals are accounted for separately by the
surviving-face replay. Independent review checked that the upper
and remote source replacements preserve both faces. The exact
normalization and source sums remain pending.

#### Corrected balanced two-mixed numerator

The repaired remote-source loop completed with all 36 probe
weights. Its mixed-class representative is
`−1865103607177734375/288230376151711744`. The corrected fused
subtotal on the first orbit is
`−303011585478349365234375/2251799813685248` across both
checkerboards, exactly matching the first tree orbit. All three
tree orbit values are identical, giving the remote subtotal
`−909034756435048095703125/2251799813685248`.

Adding the corrected remote, protected-upper and deleted-face
terms gives the revised two-face numerator
`−23686434889301885009765625/36028797018963968`.
Together with the peelable and four-face source terms, the
balanced two-mixed numerator is
`−2335659522779963714530517578125/18446744073709551616`.
These replace the earlier fused and combined source values for
this sector.

Independent arithmetic reproduced both corrected numerator sums
and gives the balanced two-mixed numerator-to-normalization ratio
`−5832562966198281588/1098025562845132579`.

The surviving-face source replay completed all 23 all-protected
orbits. Summing both possible deletions in each orbit gives the
fixed-shear subtotal `−1494543246329579853515625/562949953421312`
across both checkerboards. This adds the base removals for the
all-protected family. The normalization and source insertions
that retain both faces remain open.

#### Three-face deletion subtotal and remaining core geometry

The `--three-face-deleted-source` replay covers five orbits
with 960 words per checkerboard. Both unprotected links in each
core become peelable after removing any one of the three faces.
The replay asserts that the protected set stays fixed and that
the remaining core is empty before contracting the source
replacement. The fixed-shear subtotal across both checkerboards
is `−778235981974605966796875/2251799813685248`.

| Initial core faces | Orbits | Words per checkerboard | Free links | Core faces after any single omission |
| ---: | ---: | ---: | ---: | ---: |
| 3 | 5 | 960 | 2 | 0 |
| 4 | 10 | 1,920 | 2 | 2 |
| 6 | 1 | 192 | 3 | 4 |

The three-face squares have two mixed bases, one carrying two
residual faces and one carrying one. Their upper ends are two
pure centers. Selecting the first protected upper link at each
face in axis order leaves a seven-link spanning tree on eight
vertices in each of the five orbits. Each face then has one
live upper link, with two probes incident to one pure center.
The next calculation joins those pure tensors to the fixed
overlapping and disjoint mixed bases. The four- and six-face
deletion terms require their surviving cores.

#### Four-face deletions with a surviving two-face core

All 40 representative deletions from the ten four-face orbits
leave two faces at the other mixed base. The two faces share one
unprotected link of incidence two. The protected-link set stays
fixed. In 20 cases the deleted plane is at an upper center of the
surviving core. In the other 20 it is at a remote center.

The two-face tree replay with `--four-face-deleted-source`
selects the single removed plane by its original curvature
coordinates. At an upper center this selects one exclusive
source slot and retains the live or fixed protected frame
moments. At a remote center it selects exactly one replacement
in the exterior environment. The other face at the removed
base peels and contributes its ordinary Haar moment. The replay
uses the signed mixed-plane source factor `−2 × 48 × 2!` once
and divides the all-axis source sum by six before applying orbit
and checkerboard weights. The exact subtotal is pending.

#### Three-face tree normalization replay

The [three-face tree replay](l1_extended_three_face_tree.py)
first sums the channel linking the disjoint base to the pure
upper center shared by two faces. It then pairs the grouped
tensor and the other pure upper tensor with the overlapping
base and remote exterior environment. The disjoint base has
one peeled and one residual curvature pair. Its divisor is
`48 × 192⁸ × 4⁸ × (2!)²`. The overlapping base uses the same
fixed exclusive frame tensors as the free-link two-face join.

Both upper-link choices pass the tree check in all five orbits.
The 30 resulting face maps each give one live coordinate pair
with unit coefficient for every curvature component pair.
Independent review checked the component grouping, exterior signs
and divisors. The full numerical subtotal and the retained-source
replay remain open.

The first four-face deletion, at face `(3,2,3)` in orbit zero,
gave `−40832373647928076171875/288230376151711744` before orbit
and checkerboard weighting in both upper-link choices. The other
deletion rows still enter the full replay.

#### Three-face retained-source replay

The `--source` option verifies all eight substitutions per
representative that preserve the three residual faces and their
protected links. Five are remote, two are at pure upper centers,
and one replaces the peeled plane at the disjoint base. The
three residual-face deletions are in the separate peeling
subtotal.

The replay contracts each replacement once. The remote exterior
environment carries its existing signed weights. The upper
replacement uses `−2 × 4!/2!` and the disjoint base uses
`−2 × 48 × 2!`. Both protected frames of the removed peeled
plane become fixed-link source factors, while the complementary
frame still carries the live face's components. The join
includes channels present only in the source upper tensor.
Independent review and the 40-case incidence replay confirmed
the coverage and weights. The numerical subtotal is pending.

#### Streamed exterior contraction

The two- and three-face joins index the exterior environment
once and construct a single dual row for each component channel.
They accumulate the ordinary contraction and each applicable
upper or base source replacement before releasing that row.
The remote-source environment is contracted separately. Sparse
pairing visits the smaller of the right-factor support and the
dual support and preserves exact Gaussian-integer arithmetic.

An independent explicit exterior-inversion oracle reproduced
seven dual rows and the full channel sums, including keys present
only in source rows. Both sparse pairing branches matched the
same signed Gaussian-integer fixture. The established first
two-face orbit is the full-orbit control for the streamed path.
The running earlier replays remain comparison evidence. The first
three-face orbit in the earlier path gave
`164441394041669509962041015625/604462909807314587353088`
before orbit and checkerboard weighting. The five-orbit subtotal
and full-workload performance comparison remain pending.

#### Larger-core tree and directed frame moments

The streamed join passed the first two-face orbit control exactly.
It reproduced `999693567199179931640625/9223372036854775808`
before orbit and checkerboard weighting.

The `--larger-core-trees` census chooses a spanning tree with
every unprotected or shared curvature link fixed. Each remaining
live directed link occurs in one face. At most one direction of
each geometric frame edge remains live. Nine four-face orbits
then have live-link counts (2,2,1,1) by face, and the tenth has
(2,1,1,1). The six-face orbit has (2,2,2,2,1,1). Two, one,
and four live links respectively have their reverse directed
link fixed by the tree.

The frame moment replay now specifies the moment of each directed
anchor separately. A live quadratic probe can coexist with a
fixed identity at the reverse anchor. Summing either chiral
diagonal restores the ordinary Haar moment at the live anchor.
Eight action traces and eight source traces passed exactly.
Independent direct identity evaluations checked the action
tensor when both anchors are fixed. These controls establish
the local inputs for the larger-core join. Its full contraction
remains open.

#### Larger-core face-to-frame routing

The [larger-core replay](l1_extended_larger_core_frames.py)
routes each directed protected link to its active center, frame
axis, and anchor. The incidence check covers ten four-face
orbits and one six-face orbit. Every residual face is based at
an overlapping mixed center, and its component labels belong
to the complementary frame plane. The common axis receives
both pairs of frame labels. Pure centers use the peeled
fourth curvature moment.

The replay distinguishes a fixed identity, an independent Haar
link, and a live quadratic probe before contracting a local
frame tensor. It verifies one selected probe slice per orbit
by placing a vector coordinate on one live link of each face
and scalar coordinates on the others. The exact curvature row
then selects one component pair with unit coefficient. The
`--first-slice` option also contracts the eight exterior tensors
for the first four-face orbit. This slice supplies a control for
a later sum over all live probes. The complete sum is open.

#### Larger-core sparse probe sum

The local pure and mixed frame controls agree exactly with the
earlier replays after converting the frame divisors. The literal
first four-face probe slice gives
`354031776851001767578125/18889465931478580854784`.

The sparse replay associates each face's residual component pair
and live-link probes with the center tensors that use them.
Each label connects one face factor to one center factor.
Shared labels join by equality because the center tensor already
includes the probe's Haar moment. The exterior contraction uses
the same signed sparse multiplication as the earlier frame joins.
Independent review checked the projections in all 11 orbits and
reproduced an exact signed complex fixture with an overlapping
mask excluded. The fixed-probe comparison with the literal slice
is running.

The first orbit's four face factors have 300, 21, 21, and 300
nonzero rows. One center has 199,584 candidate projected keys
before testing its exterior support. The `--full-first` route
constructs the full factors. Its runtime and peak memory remain
unqualified, and the full normalization remains open.

A first-orbit tree search restricted to at most two live links per
face found another valid tree with a maximum of 69,696 projected
keys at any center and 70,213 in total. These are candidate counts
before exterior pruning. Use projected center key counts when
selecting trees for the complete replay.

#### Completed four-face deletion sum and cost-based tree choice

The four-face deletion replay completed 40 terms, four per
representative. Independent reduction of the exact rows gave
the same fixed-shear subtotal across both checkerboards:
`−194729223170660245751953125/144115188075855872`.
The independent alternate upper-link replay completed all 40
terms and reproduced this subtotal exactly. The ordinary
four-face normalization and
source insertions that retain the full core remain open.

The sparse factor join reproduced the literal first four-face
slice exactly. The `--tree-costs` replay scores admissible trees
using the largest center key count and then the sum of those
counts. Each count uses the joint projections of the actual
face-factor rows. It does not treat correlated keys within a
face as independent. The first orbit's maximum falls from
199,584 to 69,696 keys. The last four-face orbit falls from
116,424 to 5,544, with 6,026 keys total. The six-face orbit still
has 1,463,616 keys at its largest center after tree selection.
These counts precede exterior pruning. The first complete
probe sum uses the smaller four-face orbit via `--full-orbit 10`.

#### Larger-core retained-source factors

The retained-source census finds seven replacements in each
four-face orbit, five pure and two mixed. The six-face orbit
has five pure replacements. All 75 representative replacements
preserve the residual faces and protected links. Core-face
deletions are evaluated separately.

The sparse replay's `--retained-source` option replaces one
center factor at a time. It retains the original label scope
and divisor. A pure replacement gives two action slots and a
source on each frame edge, with the signed factor `−24`.
A mixed replacement leaves the surviving exclusive frame
unchanged, adds a source to the common frame, and puts a
source-only factor on the removed exclusive edge. Its factor
is `−192`. The directed moments distinguish fixed, live, and
independent links for each of the two source anchors. The
result divides the all-axis numerator by six.

Independent review checked the placement and weights and
reproduced six direct fixed-identity source wedge controls.
The local comparisons to the earlier probed tensors and the
full-orbit contractions are pending.

#### Six-face deletions and all-protected replay capacity

The generic retained-source local tensors match the established
pure and both mixed source replacements exactly. The
`--six-deletions` replay applies the same local source tensor
to the original removed plane. Every omission leaves four faces
at the other two bases, two free links, and the original protection.
The removed center has no surviving residual components. The replay
keeps the original plane multiplicities and applies the signed
source factor and six-shear average once. Each orbit is weighted
by 192 per checkerboard.

The six reduced cores pass the tree and routing checks. The
largest projected center table has 69,696 keys for the four
omissions at centers 9 and 12, and 5,544 for the two at center
15. The fixed-probe comparison for deletion 4 uses both the
literal exterior contraction and the sparse factor join.
The fixed-probe and full sums remain pending.

The two earlier eager all-protected normalization processes
were stopped after each reached roughly 12 GiB resident memory
without producing its first orbit. The streamed first-orbit
replay replaces them and records its memory and elapsed time.
The full all-protected normalization is still open.

#### Completed three-face normalization and six-face deletion control

The three-face normalization replay completed all five orbits,
each of multiplicity 192 per checkerboard. The weighted subtotal
across both checkerboards is
`1395884377237587968864619140625/4722366482869645213696`.
Independent reduction reproduced the weighted subtotal. The first
two normalization rows in the retained-source replay also match
exactly. Its full numerator subtotal remains open.

For six-face deletion 4, removing face `(15,0,1)` leaves a
four-face core with 5,544 projected keys at its largest center.
The literal exterior contraction and the sparse equality join
agree at the selected fixed probes:
`−22081446205224609375/2305843009213693952` before orbit and
checkerboard weighting. The full live-probe sum for this
deletion and the other five deletion sums remain open.

#### Exact exterior sign in the streamed dual

For disjoint base and environment masks `A` and `B` inside
the retained mask, the complementary mask is `T = keep xor A xor B`.
The sign of the ordered product `A ∧ T ∧ B` can be evaluated
from the parity of `A & prefix(keep xor A)` and
`T & prefix(B)`, where `prefix` gives the exclusive prefix parity
of a mask. This follows from XOR linearity of prefix parity and
`A | T = keep xor B`. The dual indexes the environment prefix
once and uses one parity calculation per surviving inner pair.

Independent verification checked 39,366 disjoint assignments
and exact complex contraction fixtures on sparse supports.
A synthetic three-site fixture produced 103,681 identical
nonzero dual entries. Its measured CPU time was 0.268 seconds
with the reference sign routine and 0.134 seconds with the
prefix calculation. The established two-face orbit control
is running with the new kernel. Full-orbit timing remains open.

#### Grouped larger-core probe evaluation

The prefix-sign kernel reproduced the established first two-face
representative `999693567199179931640625/9223372036854775808`.
The timing wrapper reported 165.72 seconds elapsed and 125.26
seconds user CPU, then exited with a sandbox error reading
`kern.clockrate`. This gives no peak-memory measurement.

The larger-core replay groups the joint projected face keys by
their directed probe assignments. It reuses the same local
exterior products across residual component pairs while those
probe moments are fixed. Only one probe block per center stays
cached at a time. On the largest center of orbit 10, the
grouped traversal visits each of the 5,544 original keys exactly
once across 756 consecutive probe blocks. Independent review
reproduced the key census and checked the exterior order and
divisors. Twenty nonzero exact gamma contractions with a shared
frame block reproduced the direct route in a synthetic fixture.
The physical component-row comparison and complete orbit remain open.

#### Single-link probe classes in the sparse sum

The six physical component rows in the grouped-probe control
matched the direct contractions exactly. On that fixture the
direct and reused paths took 8.303 and 3.240 CPU seconds,
respectively, with one cache miss and five hits.

The full sparse sum now applies the established twelve probe
classes to one selected live edge. Residual global gauge
conjugation preserves the tree identities. Signed permutations
of the imaginary coordinates in each chirality permute the
quadratic probes, with the signs canceling between curvature
and frame factors. The same argument covers the summed
source insertion at a directed frame endpoint. The replay
weights the selected face factor once and sums all other
labels. Fixed-probe controls bypass the class weights, and
`--all-probes` selects the direct sum.

Independent enumeration checked the twelve classes and their
36 total probes. Selecting the edge by joint projected-key
cost reduces the maximum in orbit 10 from 5,544 to 1,320, and
in the other four-face orbits from 69,696 to 22,176. In the
six-face orbit it reduces the maximum from 1,463,616 to
348,480. These are counts before exterior pruning. The full
class-weighted numerical comparison remains open.

#### Joint normalization and retained-source contraction

The larger-core join now carries an ordinary channel and a
single-replacement source channel. Combining two blocks multiplies
their ordinary factors and adds the two products with a source in
exactly one block. Terms with a source in both blocks are excluded.
All replacements at the same center share their label scope and
divisor and are added before joining. The final source channel
therefore equals the sum of separate one-replacement contractions,
with the six-shear average applied after closure.

Exact controls reproduced separate contractions and kept
source-only keys when ordinary entries were absent or canceled.
Independent verification checked the signs, the same-center sum,
and exclusion of double insertions. The literal-versus-joint
fixed-probe comparison for orbit 10 is running. Full numerical
retained-source results remain open.

The orbit 10 fixed-probe control completed. The joint contraction
gives normalization `6771437162655380859375/147573952589676412928`
and fixed-shear retained numerator
`−26526433675651611328125/147573952589676412928`.
The literal exterior contraction reproduced the normalization,
and summing the seven literal one-replacement contractions
reproduced the retained numerator exactly. These are fixed-probe
values before orbit and checkerboard weighting.

#### Completed free-link three-mixed normalization

The tree replay completed all 80 free-link two-face orbits.
The orbit sizes sum to 15,072 words per checkerboard. Applying
both checkerboard weights gives the exact normalization subtotal
`290879065364323137721259765625/18446744073709551616`.
Independent arithmetic reproduced the subtotal. The first 19
normalization rows from the retained-source replay match the
normalization-only replay exactly. The retained-source
subtotal and the all-protected normalization remain open.

The complete class-weighted probe sum for four-face orbit 10
gives `280809426113170260908203125/1180591620717411303424`
before orbit and checkerboard weighting. The all-probe comparison
and the joint retained-source sum are running. This is a
single-orbit result.

#### Single-link classes for the two-face tree

The two-face tree accepts `--probe-classes`. It weights the live
upper link on the first face and sums the second face directly.
Because the other three links of the selected face are fixed to
identity, only imaginary coordinates enter its curvature vector.
Independent enumeration at all four possible live-link placements
gives 21 coordinate pairs. Five of the twelve probe classes
contribute, with weights 3, 3, 3, 3, and 9.

The selected upper factor carries these weights in normalization,
retained-source, and designated deletion replays. If the source
replaces that factor, the replacement carries the weights instead.
Remote replacements use the same weighted upper factor. The
default remains the direct sum, including the three-face callers.
The class-weighted normalization and retained-source control for
two-mixed orbit zero is running.

The two-mixed orbit-zero class control completed. Across both
checkerboards it gives normalization
`2999080701597539794921875/72057594037927936`, remote source
`−303011585478349365234375/2251799813685248`, and upper source
`−1969167207996621826171875/36028797018963968`.
Independent reduction of the corrected fused probe classes
reproduced all three values, as did the direct tree replay.
The tree control now asserts both source values as well as
normalization. A class-weighted first-orbit comparison is
running for the all-protected three-mixed family.

#### Four-face orbit 10 class-weighted normalization and source

The joint source run reproduced the class-weighted normalization
`280809426113170260908203125/1180591620717411303424`
and gives the retained fixed-shear numerator
`−275006875764888102568359375/295147905179352825856`
before orbit and checkerboard weighting. The four deletion rows
for this representative are orbit 9 of the four-face-only replay.
They sum to `−12757631041178400146484375/36893488147419103232`.
The resulting numerator per representative is
`−377067924094315303740234375/295147905179352825856`.
With 192 words per checkerboard, this representative contributes
normalization `842428278339510782724609375/9223372036854775808`
and numerator `−1131203772282945911220703125/2305843009213693952`.
The all-probe comparison and remaining larger-core orbits are open.

#### Free-link retained-source range control

Run `l1_extended_two_face_tree.py --candidate-source --probe-classes
--orbit-range 21 22` to reproduce orbit 21 with the class-weighted
contraction. The interval is half-open and preserves the full census
orbit numbering. The unweighted normalization `458812262505811520302734375/1180591620717411303424`,
remote source `-11455499507026972447265625/9223372036854775808`, and upper source
`-40832373647928076171875/72057594037927936` match the direct contraction exactly.
The partial totals multiply each by 384, accounting for 192 words per
checkerboard. This comparison qualifies the range replay on one free-link
orbit. The full retained-source sum still requires one row per orbit,
with disjoint intervals covering [0, 80) and the existing census check.

#### All-protected orbit zero normalization comparison

Run `l1_extended_two_face_tree.py --candidate --all-protected --orbit 0`
and repeat with `--probe-classes`. The direct streamed and class-weighted
logs agree exactly on the representative normalization `1460729721830618365576171875/590295810358705651712`.
Both report `4382189165491855096728515625/9223372036854775808` after weighting 96 words per checkerboard.
The class-weighted process exited zero. The timed direct command emitted
its final subtotal and returned status 1, with no diagnostic in its
captured log. The comparison establishes agreement of the emitted values.
Direct command exit status, the other 22 normalization orbits, and
the retained-source subtotal remain open.

#### Independent protected intersite frame control

Run [the direct exterior oracle](l1_protected_edge_oracle.py) against
`frame_edge`. It builds both directed anchors from explicit chiral
quaternion and gamma matrices, enumerates all 16⁴ coordinate assignments,
counts exterior inversions directly, and evaluates exact sphere moments
at scale 192². It imports the production frame function only as the
comparison target.

| Gamma labels | Probe | Haar-live assignments | Nonzero exterior masks | Positive / negative components |
| --- | --- | ---: | ---: | ---: |
| (0, 0, 1, 1) | Off-diagonal (0, 4) | 176 | 16 | 8 / 8 |
| (0, 0, 1, 1) | Fixed identity | 384 | 58 | 32 / 26 |
| (0, 1, 2, 3) | (1, 2) | 176 | 0 | 0 / 0 |

The complete signed maps agree, including the exact cancellation case.
This checks the local two-anchor frame tensor used in the all-protected
calculation. It does not evaluate the upper-center tensor or the orbit
subtotal.

#### Independent orbit-zero upper-center channel

The [upper-channel oracle](l1_orbit0_upper_oracle.py) uses face
`(12,1,3)` of all-protected orbit zero, with upper center 6,
live link `(4,1)`, fixed upper link `(14,3)`, and neighboring sites
`(4,7,14)` in exclusive, common, exclusive order. For curvature
components `(0,0)`, the remaining plaquette is the inverse live link,
and the two spatial signs cancel. The surviving probe `(1,1)` has
weight one, in agreement with the production face tensor.

The independent edge enumeration and trace covariance give 18 peeled
gamma weight groups. The complete Gaussian exterior map agrees with
the production upper tensor for this probe, with 86 nonzero masks,
14 positive components and 72 negative components. The local grades
are `(8,2,4,2)` and the mixed upper row divisor is
`121029087867608368152576`. The oracle reuses the independent frame
control's matrix and sphere helpers. Other curvature components and
the global exterior contraction are outside this comparison.

#### Complete three-face retained-source subtotal

The `l1_extended_three_face_tree.py --source` replay emitted all five
representatives and the final totals. Each representative has multiplicity
192 per checkerboard. The separate normalization replay matches all five
rows exactly. The following source terms are before checkerboard weighting.

| Orbit | Remote | Upper | Disjoint base |
| ---: | ---: | ---: | ---: |
| 0 | `-13630750028099597498888671875/18889465931478580854784` | `-13114241078168807566147265625/37778931862957161709568` | `-2283906895445079193623046875/18889465931478580854784` |
| 1 | `-13642470306291136991080078125/18889465931478580854784` | `-13108952032956743514584765625/37778931862957161709568` | `-2283025189125526598408203125/18889465931478580854784` |
| 2 | `-5211288149646161870553515625/18889465931478580854784` | `-5047779401092483059659765625/37778931862957161709568` | `-881715212310860401376953125/18889465931478580854784` |
| 3 | `-94360101758479878416015625/590295810358705651712` | `-5709566239230037250390625/73786976294838206464` | `-7920133264392871728515625/295147905179352825856` |
| 4 | `-94225261756078179685546875/590295810358705651712` | `-5709566239230037250390625/73786976294838206464` | `-7920133264392871728515625/295147905179352825856` |

After weighting each row by 384, the retained-source column totals are
`−115557720349508262659316796875/147573952589676412928`,
`−111352705023568776854375390625/295147905179352825856`, and
`−19387273064171261323974609375/147573952589676412928`.
Adding the separately replayed three-face deletion subtotal
`−778235981974605966796875/2251799813685248` gives a fixed-shear
numerator of `−483247638480303378100958203125/295147905179352825856`.
The normalization is `1395884377237587968864619140625/4722366482869645213696`.
These are the three-face sector contributions to the full word sum.
Independent review at `4ad372d3b` checked the replay source, all five
normalization rows, the eight retained and three deletion variants per
orbit, and the exact weighting and reduction. It reused the tracked
deletion subtotal. This review did not rerun the underlying contractions
or verify the terminal process exit.

#### All-protected orbit-zero retained-source result

The `--candidate-source --all-protected --probe-classes --orbit 0`
run exited zero and reproduced the orbit-zero normalization.
The unweighted retained source terms are `-36888186278621288225390625/4611686018427387904` (remote)
and `-1039919139505603564453125/288230376151711744` (upper). With 96 words per checkerboard,
the contributions across both checkerboards are `-110664558835863864676171875/72057594037927936` and
`-3119757418516810693359375/4503599627370496`, respectively. This is one representative. The direct
source comparison and remaining orbit sums are open.

#### Complete free-link two-face subtotal

The direct source replay supplied orbit IDs 0–39. The class-weighted
source replay supplied ranges [40,60) and [60,80), each with a zero
exit status. These ranges contain exactly 80 unique representatives,
with 77 of multiplicity 192 and three of multiplicity 96 per
checkerboard. Every normalization row and multiplicity agrees with the
standalone replay. To reproduce a range, run
`l1_extended_two_face_tree.py --candidate-source --orbit-range START STOP`
with `--probe-classes` for the class-weighted ranges.

The direct orbit-41 run exited zero and agrees with the class-weighted
run on normalization and both retained-source terms. This checks a
mixed upper with a common-axis live link, complementing the orbit-21
exclusive-axis comparison.

| Both-checkerboard contribution | Exact value |
| --- | ---: |
| Normalization | `290879065364323137721259765625/18446744073709551616` |
| Remote retained source | `−3657404130214533220402734375/72057594037927936` |
| Upper retained source | `−26402371190237855140435546875/1152921504606846976` |
| Tracked face deletions | `−6455243019158686318359375/562949953421312` |
| Fixed-shear numerator | `−98141174976907376246879296875/1152921504606846976` |

Independent review recomputed the exact reductions, reconciled the
normalization and multiplicities, and checked the orbit-41 receipts.
It reused the previously reviewed deletion subtotal and did not rerun
the underlying contractions. The direct prefix was taken from the
ongoing unbounded run. These values cover the free-link two-face sector.

#### Fused replay for the same-side all-protected layout

The [opt-in replay](l1_allprotected_fused.py) accepts the 11 eligible
orbit IDs 0, 1, 4–11 and 20. Each mixed upper has a remote pair on its
own exclusive and common sites. The remaining remote pair crosses
between the far exclusive sites. The replay contracts those factors
against the base without expanding a full exterior dual. It checks
the actual site footprints and degrees for each ordinary and source
component. The ordinary tree contraction remains available for the
other 12 orbits.

Run `l1_allprotected_fused.py --orbit 0 --orbit 8` for the exact
controls. Both complete normalization and source triples matched in
36.12 seconds in a single run. Orbit 8's normalization agrees with
the standalone tree replay. Its unweighted remote and upper terms
are `−8234693198583117711328125/9223372036854775808` and
`−233919342720723779296875/576460752303423488`, with 192 words per
checkerboard.

Independent review checked eligibility, the existing caller defaults,
and the cache's row lifetimes. An independent exterior oracle with
interleaved sites and complex coefficients reproduced the normal and
single-source sums. This review did not rerun the full controls.

#### Complete same-side fused range

The fused replay exited zero for all 11 eligible representatives.
The rows below give exact unweighted coefficients.

| Orbit | Words per checkerboard | Normalization | Remote source | Upper source |
| ---: | ---: | ---: | ---: | ---: |
| 0 | 96 | `1460729721830618365576171875/590295810358705651712` | `-36888186278621288225390625/4611686018427387904` | `-1039919139505603564453125/288230376151711744` |
| 1 | 192 | `1460729721830618365576171875/590295810358705651712` | `-36888186278621288225390625/4611686018427387904` | `-1039919139505603564453125/288230376151711744` |
| 4 | 192 | `330053836700073321826171875/1180591620717411303424` | `-8234693198583117711328125/9223372036854775808` | `-233919342720723779296875/576460752303423488` |
| 5 | 192 | `330053836700073321826171875/1180591620717411303424` | `-8234693198583117711328125/9223372036854775808` | `-233919342720723779296875/576460752303423488` |
| 6 | 192 | `330053836700073321826171875/1180591620717411303424` | `-8234693198583117711328125/9223372036854775808` | `-233919342720723779296875/576460752303423488` |
| 7 | 192 | `330053836700073321826171875/1180591620717411303424` | `-8234693198583117711328125/9223372036854775808` | `-233919342720723779296875/576460752303423488` |
| 8 | 192 | `330053836700073321826171875/1180591620717411303424` | `-8234693198583117711328125/9223372036854775808` | `-233919342720723779296875/576460752303423488` |
| 9 | 192 | `343493570646223821826171875/1180591620717411303424` | `-8558440934603607298828125/9223372036854775808` | `-244531653623695458984375/576460752303423488` |
| 10 | 192 | `320561135521401321826171875/1180591620717411303424` | `-8020374208893957111328125/9223372036854775808` | `-227697234260645654296875/576460752303423488` |
| 11 | 192 | `320561135521401321826171875/1180591620717411303424` | `-8020374208893957111328125/9223372036854775808` | `-227697234260645654296875/576460752303423488` |
| 20 | 192 | `314151409411450821826171875/1180591620717411303424` | `-7865984569060737523828125/9223372036854775808` | `-222646854771345849609375/576460752303423488` |

The 2,016 words per checkerboard give both-checkerboard normalization
`5498419200069524244873046875/2305843009213693952`,
remote source `−69113699531336892104296875/9007199254740992`, and
upper source `−7817890663555143310546875/2251799813685248`.
Independent receipt review reproduced these sums and matched the
available tree overlaps for normalization (0, 1, 4, 5, 6, 8) and
source (0, 1). The other 12 orbits and sector-wide retained sum
remain open. The source-deletion terms are tracked separately.

#### Fused replay for three crossing remote pairs

The opt-in companion also accepts mixed-upper orbit IDs 2, 13–19,
21 and 22. Each remote pair meets both upper tensors. The join checks
the partition of the six upper sites and closes common-site masks
against exact complements. Only the four exclusive sites can receive
base coefficients. The retained-source product uses one replacement
across the three open factors and the closed scalar. Pure-upper
orbits 3 and 12 continue to use the tree replay.

Integrated controls on orbits 2 and 14 exited zero in 48.177 seconds,
including a bounded comparison with the expanded dual. Orbit 2
reproduced its recorded normalization and scratch source terms
exactly. Orbit 14 tests common sites on different crossing pairs.
On one actual channel slice of 64 base coefficients, the expanded
dual reproduced all six Gaussian join values for ordinary and
remote environments against the ordinary and two upper replacement
rows. This control is a slice of the full orbit 14 calculation.
Independent review also matched a separate signed exterior oracle
and verified the 11 same-side, ten crossing, and two pure-upper IDs.

#### Complete all-protected two-face subtotal

The crossing-pair fused run and the pure-upper tree replays exited
zero. Together with the same-side table they cover all 23 orbits.
The remaining twelve rows are unweighted.

| Orbit | Words per checkerboard | Normalization | Remote source | Upper source |
| ---: | ---: | ---: | ---: | ---: |
| 2 | 96 | `528111682107330805576171875/590295810358705651712` | `-13303693999582087250390625/4611686018427387904` | `-374240228781168017578125/288230376151711744` |
| 3 | 96 | `8438249327525738602998046875/9444732965739290427392` | `-446706963099196669423828125/147573952589676412928` | `-679230460856309371716796875/590295810358705651712` |
| 12 | 96 | `2105868443665929881748046875/18889465931478580854784` | `-109464987647537233330078125/295147905179352825856` | `-168477148549924214466796875/1180591620717411303424` |
| 13 | 192 | `559022222205966796875/9007199254740992` | `-892064810722166015625/4503599627370496` | `-203448425088427734375/2251799813685248` |
| 14 | 192 | `4716491040120146484375/72057594037927936` | `-7511471383241323828125/36028797018963968` | `-426957061224462890625/4503599627370496` |
| 15 | 192 | `123910215934071141826171875/1180591620717411303424` | `-3075968674669047823828125/9223372036854775808` | `-87279996249627099609375/576460752303423488` |
| 16 | 192 | `1088250144110419921875/18014398509481984` | `-1741822009280876953125/9007199254740992` | `-395125094686376953125/4503599627370496` |
| 17 | 192 | `1088250144110419921875/18014398509481984` | `-1741822009280876953125/9007199254740992` | `-395125094686376953125/4503599627370496` |
| 18 | 96 | `123910215934071141826171875/1180591620717411303424` | `-3072509440169487823828125/9223372036854775808` | `-87525123410877099609375/576460752303423488` |
| 19 | 96 | `131725262038179141826171875/1180591620717411303424` | `-3260079194754328723828125/9223372036854775808` | `-92550230216502099609375/576460752303423488` |
| 21 | 192 | `123910215934071141826171875/1180591620717411303424` | `-3072509440169487823828125/9223372036854775808` | `-87525123410877099609375/576460752303423488` |
| 22 | 96 | `123910215934071141826171875/1180591620717411303424` | `-3072509440169487823828125/9223372036854775808` | `-87525123410877099609375/576460752303423488` |

The full census gives 3,744 words per checkerboard.

| Both-checkerboard contribution | Exact value |
| --- | ---: |
| Normalization | `881598317342918561915888671875/295147905179352825856` |
| Remote retained source | `−44437447644003391382820703125/4611686018427387904` |
| Upper retained source | `−79570275971565588173701171875/18446744073709551616` |
| Tracked face deletions | `−1494543246329579853515625/562949953421312` |
| Fixed-shear numerator | `−306293259643306826344983984375/18446744073709551616` |

Independent review recomputed the weighting and the 23 deletion
rows, with exact agreement on the full numerator. The external
normalization overlaps for orbits 0–9 and source overlaps for orbits
0 and 1 all agree. This was a receipt reduction, without a full
independent rerun. The direct orbit-zero source comparison remains
separate from this review.

#### Exact reuse of the unprobed common-frame table

The larger-core replay uses the existing summed fourth-frame table
for the mixed common edge only when both directed anchors are
unprobed Haar. Both expansions sum the same directed-anchor terms.
The raw scales differ by `96²·8⁴/(192²·4⁴)=4`. The replay checks
divisibility of both Gaussian components before taking the quotient.

The bounded mixed-row control and the grouped-product path agreed
on 232 masks and divisor `13132496513412366336`. A direct
Haar/Haar gamma tuple agreed on all 38 masks. Independent static
review checked the anchor and site conventions, the scale, and
dispatch to the existing fixed, probed, pure, and source paths.
Dispatch controls passed. The full fixed/Haar fallback and source
controls reached their cold time caps before emitting totals.
The larger-core sums still require complete execution receipts.

#### Full class-weighted six-face deletion 4

The `--six-deletions --deletion-index 4` replay exited zero.
Omitting face `(15,0,1)` gives source frame `(2,3)` and a
four-face surviving core. The fixed-shear source coefficient before
orbit weighting is `−915708720021982470703125/18446744073709551616`.
Across both checkerboards it contributes
`−2747126160065947412109375/144115188075855872`.
Independent review checked the geometry, class edge, and factor
of 384. The previous fixed-probe comparison covers one slice.
A full direct all-probe comparison and five deletion sums remain open.

#### Opt-in integer accumulation for ordinary mixed rows

The `--integer-gamma` option on full larger-core orbits accumulates
signed Gaussian integers for ordinary grouped mixed rows and then
constructs the existing ring output. The integer map cache is scoped
to the current moment group. The reference path remains the default
and still handles pure centers and explicit source-replacement rows.

All 36 rows of the real orbit-zero control group and their divisor
matched the reference exactly. A separate complex cancellation and
reuse control passed independent review. The control does not measure
full-orbit runtime or peak memory.

#### Four-face orbit zero normalization and source

The class-weighted `--full-orbit 0 --retained-source` replay exited
zero. The normalization per representative is
`458873528424254506142578125/1180591620717411303424` and the
retained fixed-shear numerator is
`−450242679556860068724609375/295147905179352825856`.
The four tracked deletion rows sum to
`−10407087279062881787109375/18446744073709551616`.
Independent review reconciled the two orbit enumerations and the
four faces `(3,2,3)`, `(3,1,3)`, `(5,2,3)`, and `(5,1,2)`.

Weighting 192 words per checkerboard gives normalization
`1376620585272763518427734375/9223372036854775808` and full
fixed-shear numerator
`−1850268228065598531955078125/2305843009213693952`.
Independent review reproduced the arithmetic from the receipts.

#### Four-face orbit 1 normalization and source

The class-weighted `--full-orbit 1 --retained-source` replay exited
zero, giving normalization
`1014107394039901259765625/4611686018427387904` and retained source
`−31275675424624693359375/36028797018963968` per representative.
The four-only orbit 1 deletion rows correspond to faces
`(3,2,3)`, `(3,1,3)`, `(15,0,3)`, and `(15,0,2)`. They sum to
`−46081191263316064453125/144115188075855872`.
Independent receipt review matched the pattern and multiplicity.
Weighting 192 words per checkerboard gives normalization
`3042322182119703779296875/36028797018963968` and full numerator
`−513551678885444513671875/1125899906842624`.

The separate all-protected normalization run for [8,13) also exited
zero. Independent reduction matched the fused rows 8–11, the
pure-upper source run's normalization for orbit 12, and the reported
weighted subtotal `132525894456351369226494140625/295147905179352825856`.

#### Four-face orbit 2 normalization and source

The `--full-orbit 2 --retained-source --integer-gamma` replay exited
zero, giving normalization
`458870752071894957802734375/1180591620717411303424` and retained
source `−14070103247269059697265625/9223372036854775808` per
representative. The four-only orbit 2 deletion rows match faces
`(3,2,3)`, `(3,1,3)`, `(15,1,3)`, and `(15,1,2)`. They sum to
`−81305170921668603515625/144115188075855872`.
Independent receipt review verified the mapping and the weight of
192 words per checkerboard. Across both checkerboards, normalization
is `1376612256215684873408203125/9223372036854775808` and full
numerator is `−57820902558767550966796875/72057594037927936`.
This is the first completed full orbit on the opt-in integer path.
The receipt review did not rerun the orbit on the reference path.
