# L1 retarded tensor spectral interface

**Withdrawal of the site-11 signed subtotals.** The repository
port exposed a defect in the scratch `close_site11` routine
used by the environment-query prefix runs. The loop computed
the left-to-middle join key once per exterior row and then
reassigned that variable to the scalar-center lookup key
inside the mask loop. Subsequent masks could use the wrong
key and silently omit valid products. All signed zero and
nonzero site-11 prefix subtotals and their reported 144-prefix
two-tuple aggregate are withdrawn. The numeric receipts below
are retained as history and cannot serve as exact controls.
The corrected replay keeps the keys separate. It exceeded
the original scan cap on the first nonzero control, so it
has yet to establish a replacement scalar. The B census,
primitive maps, and signed eight-value slice use separate
contractions.


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

### Moving-edge plaquette and its first two source derivatives

Use the locally covariant closed ordering in
`l1_full_action_reference.py`, with a forward link transporting
the start fiber to the end fiber (`link` endpoint law). The positively
oriented path is +k,+l,−k,−l. If its chronological transports are
V1,V2,V3,V4, the matrix at the base is U = V4 V3 V2 V1.
Axis reversal on the same rectangle and base gives U⁻¹. Take the
anti-Hermitian connection convention V′ = A(y′) V and
F_kl = ∂k A_l − ∂l A_k − [A_k,A_l]. This sign makes the leading
increment +area F_kl for the stated orientation. The gauge at
the base is fixed across the source family.

The curvature coefficient is the traceless chiral projection in
`l1_normalization_opposed_fourth.py::curv_coeff`. With distinct
internal indices b,c, write
L_bc(U) = tr(U γ_b γ_c γ₅). In each SU(2) block write
U = q₀ I + Σ q_d (−i σ_d); the scalar part of either block has zero
trace against γ_b γ_c γ₅. This gives exactly the repo's
`(-I*p*gamma[b]*gamma[c]*g5).trace()` coefficients. In particular
L_bc(U⁻¹) = −L_bc(U), without a small-loop approximation. Equivalently
one may apply L_bc to (U−U⁻¹)/2. The exact raw ordered action coefficient
multiplies L_bc by g₂ ε^{klμν}/4 and the two frame coefficients,
as in `l1_full_action_reference.py::coefficient`. Keep that quarter;
do not insert an additional antisymmetrization factor when using
the existing ordered-world-index sum. The b=c contraction cancels
in the antisymmetric frame slots. The statements below concern the
curvature multiplier of an existing distinct internal pair.

#### Uniform C² bound

Let E = diag(λ₀,…,λ₃) be real with trace zero and fix |j| ≤ J.
Take a piecewise-linear unit square r(t) on the k,l coordinate
plane, rooted at the origin, with each edge traversed in one
unit of t, t∈[0,4]. Use y(t,j)=a exp(jE)r(t). Assume the entire
family and its radial segments stay in a convex coordinate
neighborhood. Choose one radial gauge about the base, independent
of j. Assume the smooth curvature in that gauge and its first two
coordinate derivatives have uniform multilinear operator bounds
M₀,M₁,M₂ there. Use a submultiplicative matrix norm.

For source-dependent functions write
‖f‖₂ = Σ_{p=0}² sup_{|j|≤J} ‖∂ⱼᵖ f‖/p!.
This norm is submultiplicative by the Leibniz rule. Choose finite R,T
such that ‖y‖₂≤aR and ‖ẏ‖₂≤aT on every edge. For example use
R=√2 e^(JΛ)(1+Λ+Λ²/2), T=R/√2, Λ=max |λ_i|.
Radial gauge gives A_μ(y)=∫₀¹ u y^ν F_{νμ}(u y)du. This identity
uses the fixed radial trivialization, so F and A are matrices in
the same gauge. For the generator K=A_μ(y)ẏ^μ on each edge,
define K₀=F_{νμ}(0)y^νẏ^μ/2.

For Z(j)=F(u y(j))−F(0), the bounds term by term are
‖Z‖ ≤ M₁ u |y|,
‖Z′‖ ≤ M₁ u |y′|,
and ‖Z″‖ ≤ M₁ u |y″| + M₂ u² |y′|², where primes in this line
mean source derivatives. Thus ‖Z‖₂ ≤ M₁ u aR +
M₂ u² a² R²/2. Multiply by the two y and ẏ factors in the
radial formula and integrate u to obtain

    ‖K−K₀‖₂ ≤ a³ M₁ R² T/3 + a⁴ M₂ R³ T/8.

Also ‖K₀‖₂ ≤ a² M₀ RT/2. These bounds include all source derivatives
of the two explicit tangent factors. They are piecewise bounds,
and the four time integration intervals and corners are fixed in j.

Put D=∫₀⁴ ‖K(t)‖₂ dt. The ordered Dyson term of order n has
‖·‖₂≤Dⁿ/n! by the ordered simplex and submultiplicativity.
The resulting absolute uniform convergence permits taking both
source derivatives term by term. The sum of all n≥2 terms
is bounded in ‖·‖₂ by D² exp(D)/2. The order-one term from K₀
is exact: (1/2)∮ F_{νμ}(0)y^ν dy^μ =
a² e^{j(λ_k+λ_l)} F_kl(0). Hence

    ‖U−I−a² e^{j(λ_k+λ_l)}F_kl(0)‖₂
       ≤ 4(a³ M₁ R² T/3 + a⁴ M₂ R³ T/8) + D² exp(D)/2.

The RHS is O(a³) uniformly for bounded J and 0<a≤a₀
with the stated curvature bounds. Applying the fixed bounded
linear functional L_bc preserves the order. With fixed reference
coframes evaluated on the two complementary moved tangent axes,
the multiplicative strain factor is e^{j(λ_μ+λ_ν)} =
e^{−j(λ_k+λ_l)}. Multiply by that factor and divide by the
reference area a². The resulting curvature-frame multiplier
is L_bc(F_kl(0)) plus an O(a) error in ‖·‖₂, so the first
and second source derivatives of the normalized multiplier
are O(a) too. If the underlying frames themselves are spatially
varying and evaluated at shifted points, their separate Taylor
terms must also be included. The area division here compares
geometries in reference units; it does not add a factor to
the finite-lattice action replay.

#### Exact commuting tests with the repository projection

Choose H=diag(−i σ₃,0) in the left chiral block. For the actual
gamma matrices in `l1_full_action_reference.py`,
L_01(H)=2 and L_01(exp(Hθ))=2 sin θ. Set A=H f(x^k) dx^l,
with a constant shift in f immaterial. Then exact chronological
transport gives

    θ(j)=a e^{jλ_l}[f(a e^{jλ_k})−f(0)].

Write s=λ_k+λ_l. The normalized projected curvature multiplier
including the complementary strain is
Y(j)=2 a⁻² e^{−sj} sin θ(j). For an explicit orientation control
take E=diag(0,0,1,−1), k=2,l=0, μ=1,ν=3, so s=1,
ε^{2013}=+1 and λ_k=1. The ordered action weight before
reference-area division is then (g₂/4) a²Y times the fixed
complementary frame coefficients.

* Linear f(x)=f(0)+b x gives θ=b a² e^{sj}.
  The compensated log multiplier is exactly constant. For the
  actual projected U, Y′=2 a⁻² s e^{−sj}(θ cosθ−sinθ) and
  Y″=2 a⁻² s² e^{−sj}[(1−θ²)sinθ−θ cosθ].
  These are O(a⁴), including the zero b or s controls. This
  detects substituting log(U) for the repo projection.
* Quadratic f(x)=f(0)+b x+c x²/2 gives θ=e^{sj}
  (b a²+c a³ e^{jλ_k}/2). The compensated log projected through
  L_01 and divided by a² is 2b+c a e^{jλ_k}.
  Its first and second derivatives at zero are c a λ_k and
  c a λ_k². The actual projected U differs by O(a⁴) in C².
  These terms test the O(a) residual and its normalization.
  Taking λ_k=0 eliminates the quadratic log-source derivatives.
* Reverse traversal with the same base changes θ→−θ and
  Y→−Y exactly, including both derivatives. The epsilon factor
  also reverses if the world indices are exchanged in the
  full action, so that exchange does not flip the full ordered
  contribution.

The proof is a smooth-field control for the simultaneous moving-edge
prescription. It supplies no derivative bound after integrating
unrestricted lattice links, no definition of a background-dependent
measure, and no choice between the physical background source
and the independent coframe-only or composite source extensions.
It also supplies no B3 susceptibility or retarded pole.

Independent review checked the fixed radial gauge identity, the
factorial-weighted derivative norm, the first-order loop integral,
and the Dyson remainder estimate. A symbolic control using the
repository's gamma matrices and curvature coefficients reproduced
the trace, orientation and both derivative identities.

### Conditions for averaging the moving-edge remainder

Write the Berezin-reduced expectation as a ratio relative to a fixed
link reference measure `ν`. For the normalized curvature error
`e_j`, let `N = ∫ e_j w_j dν` and `Z = ∫ w_j dν`, allowing signed
weights. Suppose the integrands have two source derivatives with
uniform integrable domination on the source interval and `inf|Z|>0`
there at each spacing. A uniform bound
`∫|(∂_j^p e_j)(∂_j^q w_j)| dν/|Z| ≤ C a` for `p+q≤2`, together with
uniform bounds on `∫|∂_j^k w_j| dν/|Z|` for `k=1,2`, suffices for
`N/Z` and its first two derivatives to be `O(a)`. Here the
derivatives are with respect to the source `j`. The second derivative
is `N″/Z - 2N′Z′/Z² - NZ″/Z² + 2N(Z′)²/Z³`.
This accounts for derivatives of a moving density, including any
source dependence of the regulator, action and measure Jacobian.
It uses absolute weighted moments and remains valid with signed
weights when the stated denominator and integrability conditions hold.

The product Haar link law supplies an exact obstruction to obtaining
these conditions from typical smooth fields alone. In a genuine
plaquette with one independent Haar edge used once, condition on the
other edges. The ordered product is Haar by left and right invariance
and inversion. In one SU(2) block its scalar quaternion coordinate
`q₀` has density `(2/π)√(1-q₀²)` on `[-1,1]`, and
`‖U-I‖op² = 2(1-q₀)`. Bounding the density near `q₀=1` gives
`P(‖U-I‖op≤r) ≤ 2r³/(3π)` for `0≤r≤2`. The two independent
Spin(4) blocks therefore give at most `4r⁶/(9π²)` in the
maximum block norm. At `r=Ca²` this is `O(a¹²)`.
For a positive normalized link density `ρ_a` relative to product Haar,
Hölder bounds the same probability by
`‖ρ_a‖ₚ [4(Ca²)⁶/(9π²)]^(1-1/p)` for `p>1`.
Uniform `Lᵖ` control thus precludes concentration on these balls.
For signed weights this controls normalized total variation in
the ball, under the corresponding absolute-density hypothesis.

Independent review checked the quotient identity and the exact
small-ball integral bound. The bare Haar result concerns the
reference link marginal. The finite Berezin partition function
vanishes when the action is zero and Grassmann variables are
present. A physical interacting ensemble still needs its own
weighted remainder and source-measure construction.

### Positive local Gibbs comparison

Condition on all links except one edge used once in the plaquette.
For a positive local Gibbs measure, let `V_e` be the sum of action
terms that depend on this edge and let `Δ` bound its oscillation
uniformly in the other links. If the small-ball event has Haar
probability `q`, comparison of the largest weight inside with the
smallest weight outside bounds its conditional probability by
`e^Δ q/(1-q+e^Δ q)`. The same bound holds after averaging.
At radius `Ca²`, the Haar bound implies that a probability bounded
below by a fixed `p>0` requires
`Δ ≥ 12 log(1/a)+O(1)`. Only incident terms enter `Δ`, so the
condition does not grow weaker with lattice volume.

There is a stronger bound for a smooth conditional action. Give
the two chiral groups their unit-sphere product metric and suppose
the geodesic Hessian of `V_e` is bounded above by `H≥0`.
At its minimum the first derivative vanishes. On a ball of radius
`r=min(1,H^(-1/2))` the action is within `1/2` of its minimum,
with `r=1` at `H=0`. The ball contains the product of the chiral
balls of radius `r/√2`. Integrating their radial Haar densities
with `sin θ≥2θ/π` gives a lower mass bound `8r⁶/(9π⁶)`.
The conditional density is therefore bounded above by
`(9π⁶/8)e^(1/2) max(1,H)³`. The conditional smooth-ball
probability at radius `ε` is at most
`(π⁴/2)e^(1/2) max(1,H)³ ε⁶`.
At `ε=Ca²`, maintaining a fixed positive probability requires
`max(1,H) ≳ a^(-4)`.

For a normalized fundamental-trace Wilson comparison with six
incident faces per edge in four dimensions, each face contributes
at most `β` to the directional Hessian along a unit-speed product
geodesic. Thus `H≤6β`, and the pointwise event requires
`β ≳ a^(-4)` in this comparison. The derivation and both Haar
constants were independently checked. L1 has signed Berezin
weights and still requires its own measure and weighted-error
analysis. This comparison concerns a pointwise plaquette event.
It gives no scaling law for an averaged or renormalized curvature.

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

#### Full class-weighted six-face deletion 0

The `--six-deletions --deletion-index 0` replay exited zero.
The omitted face `(9,0,1)` selects source frame `(2,3)` at site 9.
Independent review matched the four surviving faces and unchanged
protection. The class edge `(12,0)` reduces the projected key
counts from `(69696,70213)` to `(22176,22693)`.

The fixed-shear source before orbit weighting is
`−915607170319704345703125/18446744073709551616`.
Weighting 192 words per checkerboard gives
`−2746821510959113037109375/144115188075855872`.
Independent review reproduced the weighting. A full direct-probe
rerun was outside the receipt review.

#### Four-face orbit 3 normalization and source

The `--full-orbit 3 --retained-source --integer-gamma` replay exited
zero with normalization `2370001036358775322265625/18446744073709551616`
and retained source `−2342587495855294599609375/4611686018427387904`
per representative. The four deletion rows for faces `(9,0,1)`,
`(9,0,2)`, `(15,1,3)`, and `(15,1,2)` contribute
`−107877634645257861328125/576460752303423488` per representative.
Independent review matched the two orbit enumerations and the
weight of 192 words per checkerboard. Across both checkerboards,
normalization is `7110003109076325966796875/144115188075855872`
and the full numerator is `−9616825719052072470703125/36028797018963968`.
The independent check reduced the receipts.

#### Four-face orbit 4 and six-face deletion 1

The `--full-orbit 4 --retained-source --integer-gamma` replay exited
zero. Independent review matched the four-only deletion rows for faces
`(12,1,3)`, `(12,0,3)`, `(15,0,1)`, and `(15,1,3)`.
Their unweighted sum is `−28680949746879345703125/144115188075855872`.
At 192 words per checkerboard, the both-checkerboard normalization is
`1898428922982908701171875/36028797018963968` and the retained plus
deleted source numerator is `−2555164473661523267578125/9007199254740992`.

The `--six-deletions --deletion-index 1` replay exited zero. It omits
`(9,0,2)` and replaces frame `(1,3)` at site 9. Independent review
matched the surviving faces and class edge `(12,0)` and multiplied
the raw source `−915607170319704345703125/18446744073709551616`
by 384 to give `−2746821510959113037109375/144115188075855872`.
This equals the independently evaluated deletion 0 subtotal.
Both reviews reconciled existing receipts without rerunning contractions.

#### Four-face orbit 5 normalization and source

The `--full-orbit 5 --retained-source --integer-gamma` replay exited
zero. Independent receipt review matched the four-only orbit 5
deletions for faces `(5,2,3)`, `(5,0,3)`, `(12,0,1)`, and `(12,1,3)`.
The raw deletion sum is `−730354247481162744140625/2305843009213693952`.
Adding the retained term gives
`−43379408608429674111328125/36893488147419103232` per representative.
Weighting 192 words per checkerboard gives normalization
`48217872201553281708984375/576460752303423488` and full numerator
`−130138225825289022333984375/288230376151711744`.

#### Full class-weighted six-face deletion 2

The `--six-deletions --deletion-index 2` receipt reports the final
subtotal for omitting `(12,1,3)` and replacing frame `(0,2)` at site
12. Independent review checked the surviving faces `(9,0,1)`,
`(9,0,2)`, `(15,0,1)`, and `(15,1,2)`, unchanged protection,
and class edge `(9,1)`. The raw fixed-shear source
`−1811653176073974609375/36028797018963968` times 384 gives
`−5434959528221923828125/281474976710656` across both checkerboards.
The process had ended when inspected. Its exit status was unavailable.
The review checked the emitted receipt without rerunning the contraction.

#### Four-face orbit 6 normalization and source

The `--full-orbit 6 --retained-source --integer-gamma` replay exited
zero. Independent receipt review matched the four-only orbit 6
deletions for faces `(5,1,3)`, `(5,0,3)`, `(12,0,1)`, and `(12,1,3)`.
The raw deletion sum is `−619097397441737255859375/1152921504606846976`.
Adding the retained term gives
`−18383954389091815587890625/9223372036854775808` per representative.
Weighting 192 words per checkerboard gives normalization
`1310289118862622881220703125/9223372036854775808` and full numerator
`−55151863167275446763671875/72057594037927936`.

#### Full class-weighted six-face deletion 3

The `--six-deletions --deletion-index 3` replay exited zero.
It omits `(12,0,3)` and replaces source plane `(1,2)`.
Independent receipt review checked the surviving faces, unchanged
protection, and class edge `(9,1)`. The raw fixed-shear source
`−231921055885506591796875/4611686018427387904` weighted by 384 gives
`−695763167656519775390625/36028797018963968` across both checkerboards.
The residual face geometry is shared with deletion 2, while the
source plane differs.

#### Complete four-face subtotal

The integer replays for larger-core orbits 7 and 8 exited zero.
Independent review matched their deletion receipts and the whole
census. Larger-core IDs 0–8 and 10 map to four-only IDs 0–9 in
order. Each has 192 words per checkerboard, for 1,920 per board.

| Both-checkerboard contribution | Normalization | Full source numerator |
| --- | ---: | ---: |
| Orbit 7 | `340982603779997760908203125/9223372036854775808` | `−14235544765209909216796875/72057594037927936` |
| Orbit 8 | `842363672069868038349609375/9223372036854775808` | `−1131146564525152047158203125/2305843009213693952` |
| All ten orbits | `2145163737913113504814453125/2305843009213693952` | `−11545743096830174649943359375/2305843009213693952` |

The retained subtotal is `−8430075526099610717912109375/2305843009213693952`.
The 40 deletion rows contribute
`−194729223170660245751953125/144115188075855872`.
Independent review reproduced all sums from the receipts without
rerunning the full contractions. This subtotal covers the
four-face cores and their source deletions.

#### Direct all-probe comparison for all-protected orbit zero

The direct `--candidate-source --all-protected --orbit 0` run
exited zero. Its entire output is byte-identical to the
class-weighted source receipt. This reproduces the normalization,
remote source and upper source with the direct sum over probes,
including the exact weights for both checkerboards. It qualifies
the comparison for this representative.

#### Complete six-face deletion subtotal

Deletion 5 exited zero. Omitting `(15,1,2)` produces raw fixed-shear
source `−915708720021982470703125/18446744073709551616` and weighted
subtotal `−2747126160065947412109375/144115188075855872`. Independent
review checked the geometry and factor of 384 for all six deletion
receipts. Their combined value is `−32331342365480126953125/281474976710656`.
The original six-face core contributes separately.

#### Joint probe classes for the original six-face core

The opt-in `--full-orbit 9 --joint-probe-classes` path groups the
ordered exclusive probes by the stabilizer of the existing common
probe representative. It applies each orbit weight once. The
independent census verified 2,006 representatives for 6,480 probe
triples. The largest factor has 102,564 projected keys after
grouping, with weights recovering all 348,480 keys.

A rotated fixed-label pair reproduced the exact nonzero normalization
`27130079114482421875/2361183241434822606848` and one retained source
`−134816675478515625/18446744073709551616` at center 0, plane `(0,1)`.
That control covers one insertion. The full quotient replay and
comparison with the existing path are pending.

#### Four-mixed all-disjoint peelable subtotal

The `--four-mixed-disjoint-peelable` replay exited zero. Its four
orbit weights are 48, 48, 24 and 24 per checkerboard. Independent
enumeration recovered 144 fully peelable words from 24,300 balanced
all-disjoint words. Each representative has 12 source variants and
each omission preserves protection and full peeling. Independent
review checked the normalization scale, fixed-shear factor and
checkerboard weighting, reproducing the both-checkerboard
normalization `840586565680766015625/70368744177664` and numerator
`−161126273244493265625/2199023255552`. This covers four of the
1,314 four-mixed representatives.

#### Three-mixed subtotal before the original six-face contribution

The exact census has 227 orbits and 41,760 words per checkerboard.
The completed non-six-face cores cover 226 orbits and 41,568 words.
Across both checkerboards their normalization is
`238543309704664272839141337890625/4722366482869645213696` and
their full numerator is `−80883502865629918910161751953125/295147905179352825856`.
Adding all six deletion terms once gives the current numerator
`−80917404735282144599761751953125/295147905179352825856`.
Independent review recomputed each constituent subtotal. The remaining
original core contributes its normalization and five retained
source insertions, each weighted by 384. Do not add the six
deletions again.

#### Complete three-mixed subtotal

The joint-probe replay of original six-face orbit 9 exited zero.
The per-representative normalization was
`40507039180322706181640625/295147905179352825856`
and the retained numerator was
`−64881605749841979451171875/147573952589676412928`.
Multiply each by 384 and add to the preceding subtotals. The
preceding numerator already includes all six deletions.

| Both-checkerboard contribution for 227 orbits | Exact value |
| --- | ---: |
| Normalization | `238792184953388175545921337890625/4722366482869645213696` |
| Full fixed-shear numerator | `−80967233808498023239980251953125/295147905179352825856` |

This covers all 41,760 words per checkerboard with exactly three
mixed centers. The original unquotiented replay is a separate
cross-check.

#### Four-mixed two-disjoint peelable subtotal

The `--four-mixed-peelable 2` replay exited zero with all 13
representatives, covering 1,536 words per checkerboard. Both-board
normalization is `9181537442128001953125/17592186044416` and the
fixed-shear source numerator is `−53309602963571608265625/17592186044416`.
The replay checks 12 source removal types per representative.
The existing all-disjoint command remains an alias for stratum 4.
Independent review reproduced the census, all row weights, exact
receipt sums and source-removal parity. It checked the original
default and alias dispatch without rerunning the contractions.

#### Complete four-mixed peelable subtotal

The `--four-mixed-peelable 0` and `--four-mixed-peelable 1` runs
exited zero. The four receipts give the following exact sums.

| Disjoint centers | Orbits | Words per checkerboard | Both-board normalization | Both-board numerator |
| ---: | ---: | ---: | ---: | ---: |
| 0 | 285 | 45,216 | `1198041652025881998809765625/18014398509481984` | `−102782803120596881263546875/281474976710656` |
| 1 | 25 | 4,800 | `5173496975635812931640625/1125899906842624` | `−3652390070796549923859375/140737488355328` |
| 2 | 13 | 1,536 | `9181537442128001953125/17592186044416` | `−53309602963571608265625/17592186044416` |
| 4 | 4 | 144 | `840586565680766015625/70368744177664` | `−161126273244493265625/2199023255552` |
| Total | 327 | 51,696 | `1290434688137608355816015625/18014398509481984` | `−110961161072582421981515625/281474976710656` |

Independent receipt review checked sequential orbit IDs, multiplicities,
and every stratum subtotal. This completes the peelable subset of the
four-mixed sector. The 987 nonpeelable orbits and physical matching
remain open.

#### Four-mixed one-face pure-upper subtotal

The `--four-mixed-pure-upper` replay exited zero on local IDs 3, 4,
13, 14, 15, and 16 of the one-disjoint one-face census. Each has a
disjoint mixed base, a matching pure upper center, and four protected
face links. All other mixed centers have overlapping frames. The
run checks 12 source omissions per orbit, with 11 preserving the
core and one peeling it completely. Each representative has 192
words per checkerboard, giving 1,152 words per board.

| Both-checkerboard contribution | Exact value |
| --- | ---: |
| Normalization | `1022804892165847798828125/1125899906842624` |
| Retained source | `−5314137510513438276328125/1125899906842624` |
| Deleted source | `−3553702798836427734375/8796093022208` |
| Full fixed-shear numerator | `−5769011468764501026328125/1125899906842624` |

Independent static and census review checked the four-pure and
four-mixed deletion divisor, the omission guards, and compatibility
with the existing three-mixed replay. Receipt reduction covers this
six-orbit subset of the nonpeelable four-mixed sector.

#### Four-mixed two-disjoint one-face pure-upper subtotal

The `--four-mixed-pure-upper-d2` replay exited zero on local IDs 1–7
of the two-disjoint one-face census. Each has multiplicity 192 per
checkerboard. The additional disjoint center is remote and carries
four degree-two Haar edge moments at the same total frame scale as
the overlapping center's degree-two, degree-four, degree-two moments.
Independent review checked the two disjoint source slots, their
weights, and all 12 omission types per representative.

| Both-checkerboard contribution | Exact value |
| --- | ---: |
| Normalization | `91191729675557436328125/140737488355328` |
| Retained source | `−244688210038443385546875/70368744177664` |
| Deleted source | `−10139009570861044921875/35184372088832` |
| Full fixed-shear numerator | `−264966229180165475390625/70368744177664` |

Independent receipt reduction reproduced all sums. The existing
one-disjoint and three-mixed paths retain their environment builder.
The review did not rerun those contractions.

#### Four-mixed overlapping-upper orbit 0

The one-disjoint census gives orbit 0 multiplicity 192 per
checkerboard. Its residual face is `(12, 1, 2)`; upper center 10
carries overlapping planes `((0, 2), (1, 2))` with the exclusive
and common directions in the live pair. Of 12 distinct source
omissions, 11 retain the core and one clears it. The contraction
joins the fixed base and projected upper tensor against the
indexed remote environment. Of the five retained component pairs,
only `(0, 0)` and `(3, 3)` contribute, with identical real values.

| Both-checkerboard contribution | Exact value |
| --- | ---: |
| Normalization | `60630985510941167578125/70368744177664` |
| Retained source | `−633070085839488357609375/140737488355328` |
| Deleted source | `−13478814619913963671875/35184372088832` |
| Full fixed-shear numerator | `−686985344319144212296875/140737488355328` |

Independent review reduced the raw retained-source and normalization
receipt, checked the geometry and orbit weight, and reran the
deleted-face evaluator. The remaining overlapping-upper coefficients
require their own replay.

#### Four-mixed one-face disjoint-upper subtotal

The `--four-mixed-disjoint-upper` replay exited zero on IDs 0,
8, 9, 10, 11, and 12 of the two-disjoint one-face census. Their
multiplicities are 96, 192, 192, 192, 96, and 192 per checkerboard.
The two protected upper edges lie in different frame planes.
Each upper source placement replaces one plane's ordinary pair.
The evaluator checks all 12 distinct omissions per orbit. Eleven
retain the face and one deletes it.

The `--upper-trace-controls` checks recover the unprobed ordinary
tensor and both individual source tensors at scale `96²` with either
chiral diagonal trace on the protected edges. Independent source
review checked the actual plane slot remapping, the `−192` factor
for each source placement, and the common `/6` source weight. The
end-to-end replay includes the off-diagonal probe classes.

| Both-checkerboard contribution | Exact value |
| --- | ---: |
| Normalization | `204592677545270281640625/562949953421312` |
| Retained source | `−274444149839920168921875/140737488355328` |
| Deleted source | `−22732519727252253515625/140737488355328` |
| Full fixed-shear numerator | `−74294167391793105609375/35184372088832` |

The separately launched orbit 0 replay agrees with the full replay.
This completes the six disjoint-upper orbits and 960 words per
checkerboard.

#### Complete four-mixed one-face overlapping-upper subtotal

The full `--four-mixed-overlap-upper` run at `7de45d708` exited
zero on all 38 overlapping-upper orbits. It covers 23 with two
exclusive directions and 15 with one common and one exclusive
direction. Every representative carries 192 words per checkerboard.
The replay checks 12 distinct source omissions per orbit, with 11
preserving the core and one peeling it completely. The orbit 0 row
agrees with its separate replay.

| Both-checkerboard contribution | Exact value |
| --- | ---: |
| Normalization | `194263487986590298451953125/36028797018963968` |
| Retained source | `−15789074324733835579265625/562949953421312` |
| Deleted source | `−337317426020214256640625/140737488355328` |
| Full fixed-shear numerator | `−17138344028814692605828125/562949953421312` |

This subtotal includes orbit 0. Together with the pure-upper and
disjoint-upper subtotals it completes all 57 four-mixed one-face
orbits and 10,752 words per checkerboard. Larger cores remain open.

#### Four-mixed two-face overlap-base replay

The opt-in `--four-mixed-overlap-base` route selects 160 orbits
with one free link and a shared overlapping base, covering 30,624
words per checkerboard. The upper pairs are 93 overlap/overlap,
64 overlap/pure, and 3 pure/pure. Independent source and census
review checked both tree choices and all 12 omissions per orbit.
Ten retain the same core and protection. The two base-face
deletions each remove the core and use the peelable deletion
evaluator. Orbit 32 uses a separate remote environment because
it has a disjoint remote center.

Orbit 0 exited zero with `--orbit 0 --probe-classes` and with
`--reverse-upper` added. The two receipts agree byte for byte.
Independent exact reduction checked the factor of `2 × 192`
and all source weights. This closes the representative's
192 words per checkerboard.

| Both-checkerboard contribution | Exact value |
| --- | ---: |
| Normalization | `86452182234420759179296875/72057594037927936` |
| Remote source | `−8964673780431276484734375/2251799813685248` |
| Upper source | `−126138712725514102559765625/72057594037927936` |
| Deleted source | `−15392181136584814453125/17592186044416` |
| Full fixed-shear numerator | `−476054647634766350071265625/72057594037927936` |

The `--orbit-range 1 4 --probe-classes` replay also completed.
Independent exact reduction verified orbits 1–3 at multiplicity 192
each, totaling 576 words per checkerboard. Orbit 1 matches orbit 0
in all four fields, and orbits 2 and 3 match each other.

| Both-checkerboard contribution for orbits 1–3 | Exact value |
| --- | ---: |
| Normalization | `259350992354042601127734375/72057594037927936` |
| Remote source | `−109364592214179317524640625/9007199254740992` |
| Upper source | `−363959220154970572463953125/72057594037927936` |
| Deleted source | `−184829311088110451953125/70368744177664` |
| Full fixed-shear numerator | `−1428141172422630215461078125/72057594037927936` |

Exact receipts now cover four of 160 representatives. The next
nonoverlapping batch uses `--orbit-range 4 8 --probe-classes`.

For this family, `--component-remotes` reuses exact disconnected
remote components within one replay. The legacy path remains the
default and handles connected and disjoint-remote cases. Independent
review checked site relabeling signs, source linearity, and cache
scope. The complete ordinary and source maps matched the legacy
calculation in the orbit 0 and 1 fixtures. The tracked end-to-end
orbit 1 replay exited zero and matched the legacy row in every
field. The warmed orbit 1 scratch benchmark took 0.47 s for remote
assembly versus 81.87 s for the two legacy maps. This timing covers
the remote stage only.

Use separate contiguous orbit ranges for parallel replay. Keep
ranges disjoint when accumulating exact totals. The first factored
batch uses `--orbit-range 8 16 --probe-classes --component-remotes`
while the legacy batch covers `--orbit-range 4 8`.

#### Two-face overlap-base orbits 4–15

Both disjoint batches exited zero. Independent exact reduction
checked each row's multiplicity of 192 per checkerboard and all
four weighted totals. Orbits 4–7 use the legacy evaluator and
8–15 use the reviewed component evaluator at `3be37b34e`.

| Both-checkerboard contribution | Orbits 4–7 | Orbits 8–15 |
| --- | ---: | ---: |
| Normalization | `68610804300455546731640625/18014398509481984` | `4256897144834508794089453125/1152921504606846976` |
| Remote source | `−113619082978295704954828125/9007199254740992` | `−3562892705058510616568578125/288230376151711744` |
| Upper source | `−200137616867989925553515625/36028797018963968` | `−1509041228534878338159609375/288230376151711744` |
| Deleted source | `−48731921872847349609375/17592186044416` | `−378816735106141991015625/140737488355328` |
| Full fixed-shear numerator | `−754416924776764117372828125/36028797018963968` | `−1461937651772691938082046875/72057594037927936` |

The reviewed batches bring two-face coverage to 16 orbits and
3,072 words per checkerboard. The next component replay ranges
are `[16,32)` and `[32,48)`.

#### Two-face overlap-base orbits 16–47

The two component batches exited zero. Independent exact reduction
checked all 32 raw rows and the weighted normalization and source
components. Each range covers 3,072 words per checkerboard.

| Both-checkerboard contribution | Orbits 16–31 | Orbits 32–47 |
| --- | ---: | ---: |
| Normalization | `517617956644112980142578125/144115188075855872` | `3240069235512036719579296875/1152921504606846976` |
| Remote source | `−428019459161629775075015625/36028797018963968` | `−1352189370205258839486421875/144115188075855872` |
| Upper source | `−750232568800826556944484375/144115188075855872` | `−576498439758337048154953125/144115188075855872` |
| Deleted source | `−735871402982549562890625/281474976710656` | `−36054169642181816015625/17592186044416` |
| Full fixed-shear numerator | `−2839076563774411033444546875/144115188075855872` | `−278005445959043665555171875/18014398509481984` |

The covered prefix now comprises 48 orbits and 9,216 words per
checkerboard. Next ranges are `[48,64)` and `[64,80)`.

#### Two-face overlap-base orbits 48–79

Both component batches exited zero. Each range covers 16 orbits
and 3,072 words per checkerboard. The weighted sums are:

| Both-checkerboard contribution | Orbits 48–63 | Orbits 64–79 |
| --- | ---: | ---: |
| Normalization | `1959501387618402693331640625/576460752303423488` | `346284829071709163820703125/144115188075855872` |
| Remote source | `−3264083089106852460904171875/288230376151711744` | `−143501648275342351024453125/18014398509481984` |
| Upper source | `−697928476006277070886828125/144115188075855872` | `−498763837345636495058765625/144115188075855872` |
| Deleted source | `−348192808029399863671875/140737488355328` | `−122872547390677822265625/70368744177664` |
| Full fixed-shear numerator | `−5373038911963617523477828125/288230376151711744` | `−1898420000604483483254390625/144115188075855872` |

The covered prefix comprises 80 orbits and 15,360 words per
checkerboard. Next ranges are `[80,96)` and `[96,112)`.

#### Two-face overlap-base orbits 80–111

Both component batches completed. Each range covers 16 orbits
and 3,072 words per checkerboard. The weighted sums are:

| Both-checkerboard contribution | Orbits 80–95 | Orbits 96–111 |
| --- | ---: | ---: |
| Normalization | `3211235873846211438144140625/2305843009213693952` | `251103272454583289996484375/144115188075855872` |
| Remote source | `−2672568933907037851556296875/576460752303423488` | `−413381133178441403149828125/72057594037927936` |
| Upper source | `−1130386329205088800377515625/576460752303423488` | `−179752579748617950406828125/72057594037927936` |
| Deleted source | `−35643990127587444140625/35184372088832` | `−89054868058580499609375/70368744177664` |
| Full fixed-shear numerator | `−1096736599340629834183453125/144115188075855872` | `−342162948909522892578328125/36028797018963968` |

The covered prefix comprises 112 orbits and 21,504 words per
checkerboard. The next range is `[112,128)`.

#### Two-face overlap-base orbits 112–127

The component replay exited zero on 16 orbits and 3,072 words
per checkerboard.

| Both-checkerboard contribution | Exact value |
| --- | ---: |
| Normalization | `1264222082024857004150390625/1152921504606846976` |
| Remote source | `−1050749499456705588646359375/288230376151711744` |
| Upper source | `−445177953012018609629015625/288230376151711744` |
| Deleted source | `−224929025117258291015625/281474976710656` |
| Full fixed-shear numerator | `−215781846773599586034421875/36028797018963968` |

The covered prefix comprises 128 orbits and 24,576 words per
checkerboard. The final ranges are `[128,144)` and `[144,160)`.

#### Complete four-mixed two-face overlap-base subtotal

The final ranges `[128,144)` and `[144,160)` exited zero and
cover 2,976 and 3,072 words per checkerboard, respectively.
Independent exact reduction combined every raw row from orbit 0
through orbit 159. Each representative has multiplicity 192
except one of weight 96. The totals cover 30,624 words per
checkerboard, with no overlaps between replay ranges.

| Both-checkerboard contribution | Exact value |
| --- | ---: |
| Normalization | `74607956790591063781423828125/2305843009213693952` |
| Remote source | `−31051312008454048046727796875/288230376151711744` |
| Upper source | `−26657370007909238984681390625/576460752303423488` |
| Deleted source | `−6630998493398806937109375/281474976710656` |
| Full fixed-shear numerator | `−102340278939298091685336984375/576460752303423488` |

This closes the 160-orbit overlap-base replay. The disjoint-upper
and other two-face families contribute separately.

#### Four-mixed two-face split disjoint-upper orbit 0

The `--four-mixed-split-disjoint-upper` route covers 25 orbits
and 4,800 words per checkerboard. Each disjoint upper has one
protected incoming edge in each of its two frame planes. Both
tree choices pass the census and all 12 omission guards.
The other 25 disjoint-upper geometries require a same-plane
upper tensor and are outside this replay.

Orbit 0 with `--probe-classes` gave identical receipts with
and without `--reverse-upper`. Independent exact reduction
checked the factor of `2 × 192` and each source component.

| Both-checkerboard contribution | Exact value |
| --- | ---: |
| Normalization | `274791598594085450390625/1125899906842624` |
| Remote source | `−113728389777910330171875/140737488355328` |
| Upper source | `−111149268703484839453125/281474976710656` |
| Deleted source | `−6260468676577400390625/35184372088832` |
| Full fixed-shear numerator | `−388689797671924702921875/281474976710656` |

#### Split disjoint-upper orbits 1–16

Both disjoint batches exited zero. Each has eight orbits with
multiplicity 192, totaling 1,536 words per checkerboard.

| Both-checkerboard contribution | Orbits 1–8 | Orbits 9–16 |
| --- | ---: | ---: |
| Normalization | `731349799555229623828125/562949953421312` | `1623332554948730499609375/4503599627370496` |
| Remote source | `−604920139176228343171875/140737488355328` | `−671731128266467689703125/562949953421312` |
| Upper source | `−591690214428681835546875/281474976710656` | `−164068337504921143640625/281474976710656` |
| Deleted source | `−16647517293294076171875/17592186044416` | `−9208999138893591796875/35184372088832` |
| Full fixed-shear numerator | `−2067890769473843740640625/281474976710656` | `−1147211789498607445734375/562949953421312` |

The covered prefix comprises 17 orbits and 3,264 words per
checkerboard. The final range is `[17,25)`.

#### Complete two-face split disjoint-upper subtotal

The final `[17,25)` replay exited zero. Independent reduction of
all four receipts found each of the 25 orbits exactly once, with
multiplicity 192 and 4,800 words per checkerboard.

| Both-checkerboard contribution | Exact value |
| --- | ---: |
| Normalization | `646614016397387045715234375/288230376151711744` |
| Remote source | `−16722632967480093321140625/2251799813685248` |
| Upper source | `−65231747951097610871859375/18014398509481984` |
| Deleted source | `−57442652890073595703125/35184372088832` |
| Full fixed-shear numerator | `−228423449970656038440984375/18014398509481984` |

#### Four-mixed two-face same-plane disjoint-upper orbit 0

The `--four-mixed-same-plane-disjoint-upper` route selects 25
orbits and 4,800 words per checkerboard. At least one disjoint
upper puts both protected incoming edges in the same frame
plane. Its ordinary tensor and both source placements recover
the unprobed disjoint tensors at scale `96²` under all four
chirality trace combinations. Independent review checked both
tree choices, the source weights, and all 12 omissions.

Orbit 0 with `--probe-classes` exited zero under both tree
choices and produced identical receipts. Independent exact
reduction checked the factor of `2 × 192`.

| Both-checkerboard contribution | Exact value |
| --- | ---: |
| Normalization | `9096369489972317654296875/18014398509481984` |
| Remote source | `−943421736919176905203125/562949953421312` |
| Upper source | `−14720276927261829617578125/18014398509481984` |
| Deleted source | `−1619173292222865234375/4398046511104` |
| Full fixed-shear numerator | `−51541906313620346584078125/18014398509481984` |

#### Same-plane disjoint-upper orbits 1–8

The `[1,9)` replay exited zero. Independent exact reduction
verified eight orbits and 1,536 words per checkerboard.

| Both-checkerboard contribution | Exact value |
| --- | ---: |
| Normalization | `32867576630546856162890625/36028797018963968` |
| Remote source | `−6783590580408946247203125/2251799813685248` |
| Upper source | `−53184937577933388357421875/36028797018963968` |
| Deleted source | `−5841260874538962890625/8796093022208` |
| Full fixed-shear numerator | `−185648191406588120312671875/36028797018963968` |

The covered prefix comprises nine orbits and 1,728 words per
checkerboard. The next range is `[9,17)`.

#### Complete two-face same-plane disjoint-upper subtotal

The final `[9,17)` and `[17,25)` runs exited zero. Independent
exact reduction verified all 25 distinct orbit IDs and all
weighted receipt columns. The full family covers 4,800 words per
checkerboard at multiplicity 192 per representative.

| Both-checkerboard contribution | Exact value |
| --- | ---: |
| Normalization | `324776379618735246516796875/144115188075855872` |
| Remote source | `−268347609756070565052515625/36028797018963968` |
| Upper source | `−262154042372930087183484375/72057594037927936` |
| Deleted source | `−28849875224747677734375/17592186044416` |
| Full fixed-shear numerator | `−917018350805637705288515625/72057594037927936` |

#### All-protected disjoint-base two-face candidate

The `--four-mixed-all-protected-disjoint-base` route selects 35
orbits and 6,720 words per checkerboard from the larger 67-orbit
family. Its upper and remote centers fit the existing tensor
builders. The two disjoint base faces share a vertex and no links.
Both tree choices pass the geometry census and all 12 omission
guards for every representative. Ten omissions preserve both
faces and the protection set. Each of the two base omissions
leaves one all-protected face and uses the surviving-face source
contraction. Independent source review checked that each omission
enters once and that the previous replay routes remain available.

Orbit 0 replayed with
`--four-mixed-all-protected-disjoint-base --orbit 0 --probe-classes`
and again with `--reverse-upper`. Both runs exited zero and their
receipts agree byte for byte. Independent exact reduction verified
the weight of 384 across both checkerboards. The surviving-face
calculation is independent of the tree flag.

| Both-checkerboard contribution | Exact value |
| --- | ---: |
| Normalization | `62074824594543350433984375/72057594037927936` |
| Remote source | `−6432756072704477288859375/2251799813685248` |
| Upper source | `−90630894339657337292578125/72057594037927936` |
| Surviving-face source | `−13478814619913963671875/17592186044416` |
| Full fixed-shear numerator | `−351688313349368205736078125/72057594037927936` |

##### All-protected disjoint-base batch covering orbits 1–5

The probe-class evaluator at `d40c986cd` exited zero for
`--four-mixed-all-protected-disjoint-base --orbit-range 1 6 --probe-classes`.
The five orbits cover 960 words per checkerboard. Independent receipt
review reproduced each subtotal using weight 384 per orbit across both
checkerboards and one surviving-face term per base deletion.

| Both-checkerboard contribution | Exact value |
| --- | ---: |
| Normalization | `13084196796353149600735546875/4611686018427387904` |
| Remote source | `−10963236487976088236081578125/1152921504606846976` |
| Upper source | `−4649602685840543796905109375/1152921504606846976` |
| Surviving-face source | `−355210877489031889453125/140737488355328` |
| Full fixed-shear numerator | `−4630681670551695317846671875/288230376151711744` |

##### All-protected disjoint-base batch covering orbits 6–10

The probe-class evaluator at `fcfad029e` exited zero for
`--four-mixed-all-protected-disjoint-base --orbit-range 6 11 --probe-classes`.
Independent receipt review reproduced the exact weighted sum for
960 words per checkerboard, with one surviving-face term per base
deletion.

| Both-checkerboard contribution | Exact value |
| --- | ---: |
| Normalization | `232557216687590213717578125/288230376151711744` |
| Remote source | `−383622448696074371877609375/144115188075855872` |
| Upper source | `−337588464804443512656890625/288230376151711744` |
| Surviving-face source | `−25253859175075747265625/35184372088832` |
| Full fixed-shear numerator | `−1311712976558812778012109375/288230376151711744` |

##### All-protected disjoint-base batch covering orbits 11–15

The probe-class evaluator at `18ff91d6f` exited zero for
`--four-mixed-all-protected-disjoint-base --orbit-range 11 16 --probe-classes`.
Independent review verified all five orbits and 960 words per checkerboard.
The evaluator is identical to the preceding batch's evaluator.

| Both-checkerboard contribution | Exact value |
| --- | ---: |
| Normalization | `74485107345802245338671875/144115188075855872` |
| Remote source | `−3878526692805710156296875/2251799813685248` |
| Upper source | `−105341321343425233772953125/144115188075855872` |
| Surviving-face source | `−64704638672459715234375/140737488355328` |
| Full fixed-shear numerator | `−419824579683589432175953125/144115188075855872` |

##### All-protected disjoint-base batch covering orbits 16–20

The probe-class evaluator at `76bba72b0` exited zero for
`--four-mixed-all-protected-disjoint-base --orbit-range 16 21 --probe-classes`.
Independent review verified all five orbits and 960 words per checkerboard.

| Both-checkerboard contribution | Exact value |
| --- | ---: |
| Normalization | `2427385717062785533285546875/9223372036854775808` |
| Remote source | `−2015326915349783984601328125/2305843009213693952` |
| Upper source | `−853804901907311996103609375/2305843009213693952` |
| Surviving-face source | `−32945948609504143359375/140737488355328` |
| Full fixed-shear numerator | `−852229559818802966376234375/576460752303423488` |

The range `[21,26)` exited zero. Independent review verified
multiplicity 192 for each of the five orbits and 960 words per
checkerboard.

| Both-checkerboard contribution | Exact value |
| --- | ---: |
| Normalization | `3395444431191001224609375/9007199254740992` |
| Remote source | `−173814225559875344671875/140737488355328` |
| Upper source | `−19747483311160114386328125/36028797018963968` |
| Surviving-face source | `−47184185595006298828125/140737488355328` |
| Full fixed-shear numerator | `−76323076566809815122328125/36028797018963968` |

The stdout SHA-256 is
`81c15253a9c09763af5a1427136c336268430623ed1d304963e566a5bedcc922`.
Orbits 0–25 now have reviewed receipts. The next range is `[26,31)`.

The companion
`--four-mixed-all-protected-disjoint-base-remaining` route covers
the other 32 orbits and 4,896 words per checkerboard. It generalizes
the disjoint remote contraction to the actual number of remote
disjoint centers. When a base omission removes a face, the former
upper of that face enters the surviving-face remote calculation.
Both tree choices passed the census and all omission guards.
Independent source review checked each source weight, normalization,
and preservation of the existing paths. Orbit 0 of this companion
route exited zero with `--probe-classes` under both tree choices.
The receipts agree byte for byte. Independent reduction verified
96 words per checkerboard and total weight 192.

| Both-checkerboard contribution | Exact value |
| --- | ---: |
| Normalization | `6515328353360571938671875/36028797018963968` |
| Remote source | `−5663194737178488619359375/9007199254740992` |
| Upper source | `−1190421454183976991796875/4503599627370496` |
| Surviving-face source | `−353894419130628515625/2199023255552` |
| Full fixed-shear numerator | `−9493589186305497002953125/9007199254740992` |

The companion range `[1,6)` exited zero. Independent exact
reduction checked each orbit at multiplicity 192, for 960 words
per checkerboard. The range is disjoint from the reviewed orbit 0.

| Both-checkerboard contribution | Exact value |
| --- | ---: |
| Normalization | `3026106787211402296728515625/4611686018427387904` |
| Remote source | `−1263023994452441560088765625/576460752303423488` |
| Upper source | `−299719141847279991194765625/288230376151711744` |
| Surviving-face source | `−20522565260050911328125/35184372088832` |
| Full fixed-shear numerator | `−2198703987367675673678296875/576460752303423488` |

The raw stdout SHA-256 is
`c4ec5e9df085666a935f10109a0e3af1dcb2378d7db07d8a461db6dff965747b`.
The next companion replay range is `[6,11)`.

### Exact temporal transfer control for the scalar probe

Keep periodic spatial forward differences and let the temporal
spacing be a_t, the number of slices N_t, and β = N_t a_t.
For spatial momentum p write Ω_p² = m² + Σ_i p̂_i². The inverse
of the one-dimensional periodic difference kernel, with action
time weight a_t, is

    E_p = 2 asinh(a_t Ω_p/2)/a_t,
    C_p(τ) = A_p (e^(−E_p τ) + e^(−E_p(β−τ)))/(1−e^(−β E_p)),
    A_p = a_t/[2 sinh(a_t E_p)].

This solves the periodic Green function recurrence with source
δ_{τ0}/a_t. For the uniform spatial slice sum of the shear vertex
the connected covariance at separation τ is
Σ_p w_p C_p(τ)² with w_p = (p̂₃²−p̂₂²)²/4. Divide by the
number of spatial sites for the per-site result. Put
q_p = e^(−β E_p). Each summand is a nonnegative static weight
2w_p A_p² q_p/(1−q_p)² plus a pair with gap 2E_p and thermal
kernel e^(−2E_p τ)+e^(−2E_p(β−τ)), multiplied by
w_p A_p²/(1−q_p)². The static term supplies no nonzero-frequency
commutator weight. At zero temperature only the forward
exponential survives. Modes with equal transverse squared
momenta have exactly zero weight. Thus this finite free-scalar control has no absorption below the
first active pair gap at zero spatial momentum.

The discrete connected zero-frequency sum obeys
a_t Σ_τ C_p(τ)² = β⁻¹ Σ_n (Ω_p²+p̂₀,n²)⁻² by Parseval.
At unit spacing and mass on the 2⁴ torus the exact per-spatial-site
connected values at separations 0 and 1 are 11306/342225 and
776/342225. Their sum is the independently checked uniform
per-site covariance 12082/342225. The bare affine contact is
587/13260 at coincident time only and is excluded from these
connected values. The `l1_scalar_temporal_spectral_control.py` replay tests the finite transfer
formula and time sum against the temporal Fourier representation
at multiple temporal extents.

This supplies a controlled frequency-dependent probe kernel.
A physical Γ_H requires a matched geometry operator, subtraction
of permitted contacts and calibration of the inertial part of
the inverse response. A dissipative coefficient belongs to the
coefficient linear in frequency in the imaginary part of the
matched inverse pole kernel at nonzero
spatial momentum under a specified pole convention. The scalar
shear susceptibility alone supplies neither that coefficient nor
a real speed correction at physical frequencies.

### Nonzero spatial character and contact dependence of the inverse secant

On the unit 2⁴ scalar torus, put the nonzero spatial momentum
on axis 1. This flips bit 1 of a spatial momentum and leaves
the two transverse vertex factors unchanged. The time kernel
is the momentum-pair sum of w_p C_p(τ) C_(p⊕e₁)(τ), divided
by the spatial volume. Independently, the real-space route
multiplies the connected Wick kernel by the spatial character
(−1)^(r₁) before summing each time slice. Both methods give
154/5265 at coincidence and 8/5265 at the half period, hence
temporal eigenvalues 162/5265 and 146/5265. The affine bare
contact remains 587/13260 at coincident time, independent of
spatial character because it is local.

The closed geometry regulator 2×2×1×1 has a separate exact
nonzero-momentum control. In raw source units at pure g₂ put
A₀ = s/(g₂² Z₈) and B = −d/(g₂² Z₈) > 0 for the staggered
spatial character. Here s is the reviewed same-site value at
04e107a2c, d the reviewed diagonal value at 9d4012c47, and Z₈
the closed normalization coefficient, with full normalization
`g₂⁸ Z₈`. The same-time cross-space and same-space half-period
covariances both vanish. With a coincident-time contact
subtraction C the temporal eigenvalues are A₀−C±B. Their
Nyquist-minus-zero contrast is −2B for every C. In contrast,
the inverse secant in squared lattice frequency is

    (a_t²/4) · 2B / [(A₀−C)²−B²].

The replay compares C=0 and C=(A₀−B)/2. Both have strictly
positive temporal eigenvalues and the same direct contrast.
The second gives a strictly larger inverse secant. These
choices test contact sensitivity and are not physical matching
prescriptions. The staggered mode is not the uniform metric
channel. The Nyquist secant is a finite-lattice number and does
not determine a low-frequency inverse pole or Γ_H. The scalar
and geometry torus extents differ, so these controls cannot be
multiplied into a matched joint response.

### Common-regulator joint control in a restricted geometry sector

Use the unit 2⁴ scalar kernel and the reviewed independent
homogeneous opposed geometry sector with curvature plane (0,1).
The replay `l1_extended_opposed_torus.py` checks the trivial-channel
one-checkerboard normalization
Z_s = 9982511481025756988525390625/295147905179352825856
and the raw numerator per offset
N_s = −151675751259254608154296875/576460752303423488
for r = 0, 4, 8, 12. That numerator includes four layers,
two centers, and both source orders. Its four offsets are equal.
The two translated checkerboards give total coefficient 2N_s
at each offset. Their sum is translation invariant, so the
coefficient for one origin is 2N_s/16. The sector normalizer
is 2Z_s, giving geometry covariance −864/(1777 g₂²) at each
of the four offsets. The pure-g₂ one-point vanishes by Pin
parity: one degree-four insertion leaves 31 curvature factors.
This sector normalization is a control and does not normalize
the contribution to the full geometry ensemble.

The scalar connected values at those offsets are
208123/11635650, 5329/684450, 5329/684450, and −2993/1292850.
Their signed sum is 10658/342225. The coincident derivative
of the mixed covariance under +λ Σ_x D_x O_x is consequently
−341056/(22523475 g₂²) in the declared sector. The derivative
uses the scalar connected covariance, with the affine bare
contact excluded.

The geometry support has no time or axis-1 displacement. Its
Fourier values at characters 0, 1, 2 and 3 are therefore equal.
The replay verifies this independent character sum. The full
scalar Fourier kernel varies with those characters, so the
joint convolution can vary through its scalar factor even
though the restricted geometry part has no axial or temporal
contrast. This calculation checks the common-lattice mixed
contraction and source normalization. Matching the physical
geometry ensemble, joint coupling, and inverse pole remains
separate.

### Axial and temporal source-pair support on the common regulator

The `l1_extended_offset_pair_census.py` replay fixes the first
source origin at zero and the second at offset 1 or 2. It counts
a restricted family of 30-action label multisets with one repeated
center-plane label at each of 15 sites. Each ordered same-axis
source choice gives 4,138,344 multisets per offset. Each ordered
mixed-axis choice gives 3,769,740, for 15,816,168 source-labeled
cases per offset before anchor choice or action ordering.

After dividing exterior degrees by two, the two sources contribute
one unit at each endpoint. Every paired action center uses two
local units and sends one unit along each frame direction. The
checkerboard halves satisfy independent incoming demands. Axis
exchange checks each of the 16 omitted-center bins. The explicit
witness and its exchanged image have 20 occupied undirected frame
edges and 60 binary anchor choices subject to one parity condition
per occupied edge. The existing anchor census independently
reproduces the resulting `2^40` assignments. Independent review
checked the degree count, parity rule, and axis exchange.

These counts establish structural support. The next step is the
signed exterior and Haar contraction for the predeclared witness.

#### Exact signed coefficient for the selected temporal word

The `l1_extended_offset_witness.py` replay evaluates the
predeclared paired-label action word with ordered insertions
`G22(0) G22(1)`. It sums the directed action anchors and the
exterior and curvature labels. The source link incident to the
remaining curvature torus is fixed to identity. The other source
link remains Haar integrated.

Eleven curvature faces peel, leaving a four-face tensor. Its
diagonal baseline and chiral corrections give 15 scalar branches.
The replay verifies a fixed-label join, a one-center enumeration,
and a direct restricted linked-center calculation. All 15 branch
receipts match the separately reviewed scratch calculation.
Independent source review also checked the 128 local coframe
orientation and sign cases against the existing frame evaluator.

The exact coefficient is
`2028966652060713225/1099511627776` before the factor `g₂³⁰`.
It establishes a nonzero contribution for one word and one
ordered source pair. The full shear coefficient still requires
summing the other source pairs and action words, including their
signs, and normalizing in the full geometry ensemble.

#### Complete two-deviation paired subfamily at temporal offset 1

The `l1_extended_offset_witness_k2.py` replay counts and evaluates
the paired words with exactly two frame-plane deviations from
`(0,1)`. With the first origin fixed, there are four words for
ordered source axes `(2,2)` and two for `(2,3)`. The other
axis choices follow by transverse exchange. Every word leaves
two disjoint four-face curvature tori. The same-axis cases
jointly integrate the action and source on their shared Haar
edge. The exterior join checks complementary masks before
multiplication and retains components that share a gamma label.

The repository replay exited zero and matched all six reviewed
scratch coefficients. Exact controls cover the local Haar trace,
curvature channels, indexed exterior signs and disconnected
components. The same-axis subtotal is
`247348708021702592193669/70368744177664` and the unsigned
mixed-axis subtotal is `16670281986745651878525/70368744177664`.
The fixed-origin shear contribution is twice their difference,
`28834803254369617539393/4398046511104` before `g₂³⁰`.
The factor of two is from the source-axis symmetry. Other paired
and unpaired words and full-ensemble normalization remain open.

#### Complete three-deviation paired subfamily at temporal offset 1

The `l1_extended_offset_witness_k3.py` replay evaluates eight
same-axis and four mixed-axis words with exactly three deviations.
Four reuse two torus factors. The others each include a protected
square, with three links fixed and one live Haar link. Its live
probe is integrated with the action edge, so it introduces no
separate divisor of 48. Independent review checked the fixed
anchor and reverse orientation, direct quaternion and cubature
controls, and the exact source weighting.

The repository replay exited zero and matched the independently
reviewed scratch coefficients for all 12 words. The same-axis
subtotal is `26227592827558479037125/70368744177664` and the unsigned
mixed-axis subtotal is `22069465733850467267925/1125899906842624`.
The fixed-origin shear contribution is twice their difference,
`397572019507085197326075/562949953421312` before `g₂³⁰`.
The remaining paired and unpaired strata and full-ensemble
normalization remain open.

#### Exact support exclusion for a selected unpaired temporal word

For the seven-coordinate bit-2 cut of the selected odd-curvature
word, an exact signed contraction of the upper B environment leaves
16 gamma keys and 3,456 exterior rows. The projection matches the
two shared gamma labels before checking complementary exterior
masks at sites 13 and 15. At each site the degrees are 2 from the
incoming frame, 2 from the environment, and 4 from the connector.
Dropping exterior constraints on other sites enlarges the support,
so absence of a simultaneous complement proves the full shard is zero.

Independent review checked this implication and the exact coordinate
census. The two omitted coordinates have 48 combinations per case.
The scratch run excluded 12,480 of the 24,576 cases on the five
retained coordinates, certifying zero for 599,040 of the 1,179,648
full tuples for this cut. It rejected the control with only
`q(15,3)=5` changed from the all-one tuple. The all-one control
and the `q(15,1)=5` control passed the projection despite their
separately verified signed zeros. Passing the projection gives
no nonzero certificate.

The scratch receipt SHA-256 is
`0e8c4ab9e79edcb98e97b5f479bb85038ffb8a9cfdb1b78bbac5d5dd313e72ef`.
The independently reviewed repository replay
[`l1_unpaired_upper_support.py`](l1_unpaired_upper_support.py)
reproduces these counts without scratch imports. Its
[factor assembly](l1_unpaired_offset_factors.py) represents one
predeclared word. Run the replay with the repository Python environment.
Signed evaluation of the surviving tuples remains open. Retaining
the coupled site-5 and site-7 masks can strengthen the exclusion
before that evaluation.

A separate signed control fixes `q(5,1)=5` and all six other
coordinates to 1. This tuple survives the upper projection.
Independent review confirmed that the cached seven-factor B
calculation and the direct 20-factor B calculation use the same
eight action centers and twelve frame edges. Both find an empty
join at site 7 with zero compatible products. Once all seven
cut labels are fixed, the full shard is a bilinear exterior closure
of the A and B halves. The empty B map therefore gives exact zero
for this shard. It provides a regression for a lower support
projection.

The independently reviewed lower projection first contracts the
signed lower environment to four gamma keys and 336 rows. It
matches the shared gamma label on edge `(7,3)` before projecting
the site-7 masks of degrees 4, 2, and 2. An empty complement
test certifies an exact zero. The lower projection excludes
654,336 full tuples and overlaps the upper exclusion on 334,080.
Their union excludes 919,296 of 1,179,648 tuples, leaving 260,352
for further evaluation. The lower projection excludes the
signed-zero `q(5,1)=5` control above. The all-one and
`q(15,1)=5` signed zeros still pass both projections.

The two projections can currently match different rows of the
shared edge. Retaining its site-7 and site-15 bytes together
gives a stronger necessary support condition. The full signed
coefficient remains open.

The independently reviewed correlated projection indexes both
endpoint bytes and the shared gamma from the same `(7,3)` edge
row. A candidate survives only when that row meets both endpoint
complement constraints. Across the guarded domain of 1,179,648
tuples it leaves 249,120 candidates and certifies 930,528 zeros,
including 11,232 beyond the separate projections. Both incoming
flip controls are excluded. The all-one and connector-flip
controls still require the signed calculation to establish zero.
The tracked port should assert the exact projected key domains
before relying on the coverage count.

A signed eight-value slice fixes the coordinates on
`(5,1),(5,3),(7,1),(7,3),(13,3),(15,3)` to
`(5,5,1,5,1,1)` and varies `q(15,1)` over 0–7.
All eight pass the correlated support test. Independent review
confirmed that the signed B calculation gives empty maps for
six values, certifying six zero shards. The B maps at 1 and 5
each contain 24 rows and have distinct digests. The direct
20-factor route reproduced the entire signed map at 1.
Direct contraction also reproduced the full map at 5. For
both nonempty maps, insert the signed B boundary as an even-degree
factor before A. The site-4 closure has 32 compatible products
and 24 signed rows. The site-5 closure has zero compatible
products in both cases. Independent review checked the factor
order and exact receipts, including the negative wedge-sign
control. Thus all eight scalars vanish and the complete slice
subtotal is exactly zero. Other slices and the full word remain
open.

The independently reviewed source-supported cut moves the only
A-side factors incident on sites 4 and 5 into the signed lower
environment. The two source factors are independent of the seven
cut coordinates. This closes site 4 and leaves four gamma keys
and 5,040 rows with degrees `{0:2,1:2,5:4,7:4}`. The
projection keeps the site-5 and site-7 masks correlated, matches
the gamma labels and retains the shared edge's endpoint relation
through the site-13 and site-15 checks. This support test excludes
1,055,232 of 1,179,648 tuples, leaving 124,416 possible survivors.
Both nonempty B maps in the verified slice are excluded at this
stage. The independently reviewed [source support replay](l1_unpaired_source_support.py)
reproduces the count and four known-zero controls without scratch
imports. Its deterministic iterator provides the signed replay's
candidate order. The surviving candidates still require signed
evaluation.

Run [the signed slice replay](l1_unpaired_signed_slice.py) with
the repository Python environment to reproduce the complete zero
subtotal. Independent source review and a fresh run without
scratch imports confirmed exact agreement of the cached and
direct B maps at all eight coordinates.

The first signed source-supported batch takes the first 16
survivors in ascending coordinate order
`(q51,q71,q73,q153,q53,q133,q151)`. The scratch receipt prints
each tuple in order `(q51,q53,q71,q73,q133,q151,q153)`.
Independent review confirmed 16 distinct tuples, exact empty
signed maps after source absorption for all 16, and zero capped
or timed-out evaluations. Six maps vanish when sites 13 and 7
close, and ten at site 15. The exact batch subtotal is zero.
The 1.67-second evaluation reused both environments after factor
assembly. The next signed ranges can reuse lower blocks and
upper connector contractions across repeated coordinates.

The next scratch replay caches the signed lower, middle and
upper connector blocks by their incident cut coordinates.
Independent review confirmed that the first 128 distinct
survivors all have an empty exact block, giving subtotal zero
with no capped evaluations. The first 16 match the preceding
tuple roster and were also checked through the uncached
seven-factor route. The 1.12-second signed phase includes
those checks and excludes factor assembly. The final join
for nonempty blocks remains to be exercised. Classify the
repeated lower blocks across the guarded domain before
contracting the remaining survivors.

The completed signed lower-block census covers all 3,072 keys
of `(1,2,3,5,6,7) × range(8)³` in order
`(q51,q71,q73,q153)`. The wall-limited prefix `[0,1600)` and
resumed suffix `[1600,3072)` have no overlap or gap. Independent
receipt review found 1,436 signed-empty keys, 820 support-empty
skips with zero candidate lifts, and 816 nonempty signed maps.
Empty signed maps exclude 46,944 additional tuples among the
124,416 source-support survivors. This leaves 77,472 tuples
for the remaining joins. The count makes no extra deduction
for earlier signed batches because those can overlap these
exclusions. Next join the upper and middle signed blocks once
per suffix before matching the exact site-5 and site-15
complements against the lower maps.

The first 128 tuples after signed lower-block pruning exercised
the site-13-closed upper and middle join. Independent review
confirmed the ordered roster and exact signed B-side agreement
with the unfactored route for the first 16 tuples. That control
includes four nonempty maps. Across the batch, 102 tuples
resolved to exact zero. The other 26 produced nonempty
source-absorbed B maps and hit the A-side product cap when
closing site 3. The available subtotal covers the 102 zeros
only. Separate B-side classification from A-side closure so
the A caps do not interrupt the B census. Group by the right
block's fixed coordinates to reuse its signed map.

The next B-only batch evaluates 512 tuples disjoint from all
128 previous attempts. It groups them by the right block's
coordinates. Independent review verified 437 exact empty
maps and 75 nonempty maps, with no B-side caps. The nonempty
results contain eight distinct signed maps and five primitive
maps under signed integer rescaling. The grouping compares
full coefficient tuples. Digests identify the receipt rows.
B-only contraction took 0.90 seconds after setup. A scalar
can reuse a primitive contraction only after verifying the
corresponding frozen A factors or retaining their coordinate
dependence in the sum.

The larger B-only run completed the contiguous survivor range
`[640,2688)` and 218 separately indexed tuples in
`[2688,3712)` before the wall-time limit. Independent review
verified all 2,266 indices and outcomes. There are 1,999 exact
zeros and 267 nonempty signed maps. Index 2688 is still due.
The nonempty maps have four distinct exact values and one
primitive map up to signed integer scale. All 267 frozen A
input signatures are distinct, including after factorwise
scale normalization. Those input signatures do not establish
distinct scalar outputs. A possible grouping preserves the
common primitive B, fixes the frozen inputs at centers 1, 3,
and 9, and sums the appropriately weighted center-11 maps
before completing the A closure.

A five-tuple group at survivor indices 678, 772, 774, 871, and
967 has one common primitive B map and identical frozen A
center factors at sites 1, 3, and 9. Independent review checked
the exact weighted sum of center-11 maps. The signed B scale
weights each raw center-11 map once. The sum retains 576 of
624 distinct row keys and agrees with direct coefficientwise
reduction. This replaces five terms with one signed factor
without dividing before the scalar contraction. The grouped
scalar remains open. A broader contraction can carry all
seven cut labels in one sparse B factor and eliminate them
against their four owning A center tables.

A separate two-tuple test shares an exact 36-row B map. The
two tuples differ only at `q(7,3)` and `q(15,3)`. Independent
review verified that eliminating their paired selector through
A centers 3 and 11 gives the same 41,472 signed rows as the
explicit sum of the two frozen products. Joining that factor
to the bridge edge `(3,3)` exceeded the 120,000-row cap before
closing a site. Keeping the selector sparse deferred the
expansion, but the subsequent bridge join still reached the
cap without closing either endpoint. The scalar remains open.
Close an endpoint in the bridge join before emitting the
intermediate rows.

A follow-up completed the missing 806 B evaluations in
`[2688,3712)`. Independent review checked all indices against
the previous 218 receipts and verified 1,024 distinct tuples
with no gap or overlap. The complete interval has 880 exact
zeros and 144 nonempty B maps. With the preceding interval,
`[640,3712)` now has 2,688 exact zeros and 384 nonempty maps
whose A closures remain due. The next untouched B index is 3712.

Independent review verified the next complete interval
`[3712,4736)`. Its 1,024 distinct tuples include 908 exact
zeros and 116 nonempty B maps. Twelve maps were checked
against the unfactored signed route. The contiguous interval
`[640,4736)` has 3,596 exact zeros and 500 nonempty maps.
Resume the B census at index 4736 and keep A closures separate.

**Withdrawn scratch result.** The indexed environment query reported one A subshard
of the two-tuple grouping. It fixes `q(15,3)=5`, selecting
the first tuple, with `γ(9,0)=(0,0)`, `γ(9,1)=(1,)`, and
`q(9,1)=1`. Independent review checked that the remaining
label and exterior sums are retained. The run checked 46,944
site-11-compatible products, queried 1,888 distinct exact
environment complements, and found no nonzero matches.
This subshard has raw Gaussian scalar `(0,0)`. The receipt's
final scalar label refers to the pinned subshard. The wider
cuts reached the cap and the full two-tuple scalar remains open.

The resumable B run pinned to `76bba72b0` has an independently
verified snapshot over `[4736,22144)`. Seventeen contiguous
1,024-row receipts cover 17,408 distinct tuples. Their hashes
match the run log. There are 15,199 exact zeros and 2,209
nonempty B maps awaiting A closure, with no caps in this
snapshot. The live run continues beyond this recorded interval.

An independently reviewed outer-key support census for the
two-word group has 6,144 label-compatible keys. Preserving
the paired exterior bytes at sites 2, 9, and 11 excludes
3,840 keys and leaves 2,304 possible signed contributions.
The four-label prefix `(q153,g90,g91,q91)` partitions these
into 144 blocks of 16 retained keys each. One block is
already verified zero by the pinned environment query.
The remaining 143 blocks require exact signed evaluation.

Prefix 3, `(q153,g90,g91,q91)=(5,(0,0),(1,),5)`, is the
first independently reviewed nonzero A subtotal. After locating
a match, the replay restarted the selected prefix and exhausted
all 16 retained keys. It checked 55,080 compatible products
and found 25,344 nonzero signed environment matches. Applying
the full divisor once gives real subtotal
`−8371769346801/73786976294838206464` and imaginary subtotal
zero. This prefix is disjoint from the verified `q91=1` zero
prefix. The other prefixes can contribute with either sign.
The receipt's scalar applies only to this prefix.

Independent review extended the first bulk snapshot through
`[4736,33408)`. All 28 complete chunks match the logged hashes
and cover 28,672 distinct tuples. The receipts certify 25,034
exact zeros and leave 3,638 nonempty maps for A closure. The
subsequent partial chunk is outside this verified snapshot.
The resume run uses the same runner hash and unchanged Python
inputs and fills the missing rows in the same chunk partition.

The first batched replay completed prefixes 2–10. Independent
review matched all nine IDs to the sorted 144-prefix census.
The signed contractions checked 436,176 candidates and found
133,056 nonzero matches, with no caps. Prefix 3 reproduced
the earlier control. Four blocks vanish, three contribute
`−8371769346801/73786976294838206464`, and two contribute
its positive counterpart. The combined subtotal for 2–10
equals prefix 3 alone, with zero imaginary part. The generic
footer describes the unresolved full group, while all nine
requested prefixes have exact terminal receipts.

The resumed bulk run replaced the 800-row partial chunk
with its complete 1,024-row receipt. Independent review
verified four contiguous chunks in `[33408,37504)` and
their logged hashes. They contain 3,588 exact zeros and
508 nonempty B maps. The combined verified bulk range
`[4736,37504)` covers 32,768 distinct tuples, with 28,622
exact zeros and 4,146 nonempty maps awaiting A closure.

The independently reviewed [repository B evaluator](l1_unpaired_B_census.py)
reconstructs the ordered roster from the signed low-prefix receipts
and the source support replay. It validated the full 3,072-key
domain and reproduced all 77,472 retained indices in order.
Both previous gap receipts matched by index. Twelve direct
seven-factor controls matched the cached signed maps, including
nonempty maps and their primitive scales. This module supplies
the calculation core. The live bulk driver still uses its pinned
scratch runner and receipt partition.

The next replay completed prefixes `[11,35)`. Independent
review verified the pinned inputs, all 24 distinct prefix
identities, and the separately repeated prefix-3 control.
The new batch checked 1,199,088 compatible products with
329,472 nonzero matches and no caps. Twelve prefixes vanish,
eight contribute `−8371769346801/73786976294838206464`, and
four contribute its positive counterpart. The real subtotal
is `−8371769346801/18446744073709551616` and the imaginary
subtotal is zero. The next untouched prefix is 35.

The next independently checked bulk snapshot covers
`[4736,52864)`. All 47 complete chunks match the hashes
in the original and resume logs. The 48,128 distinct tuples
contain 42,053 exact zeros and 6,075 nonempty B maps.
The resumed complete chunk replaces its earlier partial
receipt. A closure remains due for the nonempty maps.

The [repository replay command](l1_unpaired_B_replay.py)
uses the same ordered indices and exact row format. It binds
each receipt directory to the evaluator source bytes, low
receipts, and ordered roster. A single writer atomically
replaces each chunk after validating its saved rows. Unresolved
caps remain pending. A native control reproduced all four
`[3712,3716)` rows byte for byte and checked each against
the unfactored signed route. These four maps are empty.
Use the same input files, interval, and chunk boundaries
when resuming into that receipt directory. The already live
bulk process continues with its original pinned scratch driver.

An independently verified snapshot of the longer A replay
covers `[35,100)`. The pinned hashes, sorted census identities,
and repeated prefix-3 control match. Among 65 new exact
prefixes, 33 vanish, 21 contribute the negative reference
value, and 11 contribute the positive counterpart. The real
subtotal is `−41858846734005/36893488147419103232` with zero
imaginary part. The snapshot excludes the repeated control
and later rows. The full two-word subtotal remains due.

The first two bulk runs have independent receipt verification
over `[4736,62080)`. The 56 full chunks cover 57,344
distinct tuples, with 50,105 exact zeros and 7,239 nonempty
B maps awaiting A closure. Every full-chunk hash matches its
phase log. The second run stopped at its wall limit with
66 additional rows in the next chunk. The third run resumes
that chunk using the same runner hash and unchanged existing
tracked Python inputs. Its partial and later results are
outside this verified range.

A native nonempty control at index 3792 completed in a new
receipt directory. Its 208-row signed map passed the unfactored
control and its exact digest, primitive digest, and signed
scale matched the independently reviewed bulk-gap receipt byte
for byte. This extends the native command's controls to a
nonempty B map. A closure is separate.

**Withdrawn scratch aggregate.** The selected two-word group previously reported scalar
`−25115308040403/9223372036854775808` with zero imaginary part.
Independent review reconstructed all 144 disjoint prefixes,
including the two initial zero controls, and counted the
repeated prefix-3 control once. No prefix capped. The final
`[35,144)` batch contributed
`−159063617589219/73786976294838206464`. The full raw sum
uses one common 40-factor divisor. Each of the two selected
words contributes half the combined value. This gives a
signed nonzero control for future bulk A contraction.
The full unpaired word coefficient remains open.

Independent review verified the third bulk run's first eight
complete chunks in `[62080,70272)`. They add 7,147 exact zeros
and 1,045 nonempty B maps. The complete bulk union
`[4736,70272)` now covers 65,536 distinct tuples, with 57,252
exact zeros and 8,284 nonempty B maps awaiting A closure.
The completed chunk supersedes the earlier 66-row partial.

The B census is complete over all 77,472 retained indices.
Independent review matched all 72 bulk chunk hashes and
reconciled the earlier batches in their original index order.
The ordered roster SHA-256
`282471134d9ee196c94f791cf4a757a400ef466af3c9f01cc8900f90caff0d17`
matches the independently regenerated repository roster.
There are 67,680 exact full-shard zeros and 9,792 nonempty
B maps. The two previously credited A+B results are withdrawn.
All 9,792 nonempty cases require valid A closure in this accounting. No B caps
remain. This completes the B stage for one selected word.

Within `[640,70272)`, 8,784 nonempty maps have 20 exact
digests and seven primitive digests. The tracked B evaluator
regenerated all seven representatives and checked their
full signed maps against the unfactored route, including
the exact digests and signed scales. This is a reuse
opportunity for B maps. Each subsequent A contraction must
preserve its own cut coordinates and signed B scale.

Regenerate the seven verified representatives using B roster
indices 4737, 12916, 12946, 13156, 13204, 51076, and 51412.
The recovered primitive maps have 208, 36, 162, 72, 36, 72,
and 162 rows respectively. A separate check reconstructed
each exact map from its primitive rows and signed scale and
reproduced both receipt digests.

The [corrected repository A replay](l1_unpaired_A_group.py)
uses distinct middle-factor and scalar-center lookup keys.
An independent brute-force Gaussian-integer oracle reproduces
the old omission with two masks in one left row. The corrected
join agrees with that oracle in all six factor orders, including
a negative wedge contribution. The replay regenerates 2,304
supported leaves and guards their exact roster.

Prefix 3, leaf 0 fixes
`(q153,g90,g91,q91,g33,q33)=(5,(0,0),(1,),5,(0,),4)`.
The corrected run checked 64,800 compatible products and
36,864 nonzero environment matches. Independent review
verified the normalized leaf scalar
`−2790589782267/18446744073709551616` with zero imaginary
part. This result covers one leaf. All other leaves still
require corrected evaluation.

The corrected repository replay completed all 16 leaves
of prefix 3 under the unchanged per-leaf caps. Independent
review checked every leaf against the ordered census and the
pinned source. Twelve leaves have equal negative contributions
and four vanish. The run checked 1,202,688 compatible products
and found 479,232 nonzero matches. Summing the raw signed rows
and dividing once gives `−8371769346801/4611686018427387904`
with zero imaginary part. This replaces only the withdrawn
prefix-3 subtotal. Other prefixes require their own replay.

An alternative production-leaf contraction reproduced the
corrected prefix-3 leaf-0 raw numerator exactly. It freezes
the six leaf labels, materializes the incident and environment
maps separately with ordinary indexed joins, and computes
the sign by direct inversion count over 1,152 complementary
mask pairs. It shares upstream factor construction with the
repository replay and independently checks the contraction
after the site-11 cut.

The corrected repository replay also completed prefixes 0–2.
All 48 leaves match the ordered census. Each prefix scanned
265,392 candidates with no nonzero matches and no caps. Their
subtotals are exactly zero. The receipt SHA-256 is
`b64abdd97c6a656c3c40730ea7fd7dfd4b9a2eee561ef8c30b927a828affa94d`.
These results replace the withdrawn subtotals for 0–2 only.

The native B evaluator reproduced the first 128 indexed
classifications, including 102 zeros and 26 nonempty maps.
The 26 nonempty maps matched the direct contraction, and
their primitive scales reconstruct the exact coefficients.

The independent pairwise materialization was extended to all
16 leaves of corrected prefix 3. Every raw numerator agrees
with the repository replay, including the four zeros. The
materialization and complement dot took 1.258 seconds after
31.440 seconds of shared assembly. Peak joins used 53,616
products and 16,128 rows, within the existing caps. Use the
same exact census and separate cap status when expanding this
route to all 2,304 leaves.

The complete B receipt roster has 20 distinct exact maps
and seven primitive maps. The 208-row primitive occurs at
9,216 retained indices. Two 36-row primitives account for
288 indices, two 162-row primitives account for 144, and
two 72-row primitives account for 144. All seven were
regenerated by the native evaluator. The normalized indexed
receipt SHA-256 is
`e13657e8830741675f5f4d2730f8055991bd99172082bfd0b836f210e22d25ec`.
The dominant primitive can be reused, with each occurrence's
coordinates and signed scale preserved in the A contraction.

**Corrected full two-tuple result.** Independent pairwise
materialization completed all 2,304 leaves across 144 prefixes
without caps. A separate receipt reduction matched every leaf
to the ordered census and all 64 corrected native control
numerators for prefixes 0–3. There are 1,440 zero, 576
negative, and 288 positive leaves. Applying the full divisor
once gives `−25115308040403/576460752303423488` with zero
imaginary part. Each selected tuple contributes
`−25115308040403/1152921504606846976`. This replaces the
withdrawn scratch aggregate and closes these two tuples only.

The exact JSONL receipt SHA-256 is
`631a6115481895efa8c73f2157898475f550b87e6b2f574c85ba3e981000f339`.
The replay took 124.201 seconds after 31.837 seconds of assembly.
Peak joins used 68,448 products and 19,920 rows. The remaining
9,790 nonempty B cases still require A closure.

**Repository pairwise replay.** The independently reviewed
[runner](l1_unpaired_A_pairwise.py) shares the selected-group assembly
and roster with the corrected query evaluator. It closes both factor
maps separately after fixing the six external labels, then contracts
complementary masks with the inversion sign. It reports capped leaves
without a numerator and exits nonzero if any leaf caps.

Running `python l1_unpaired_A_pairwise.py 3 4 --cross-check` with the
repository Python environment produced all 16 expected rows (indices
48–63). Independent review compared the ordered keys and raw signed
numerators against both native and scratch outputs, and matched the
13,824 complementary pairs against scratch. The exact subtotal was
`−8371769346801/4611686018427387904` with zero imaginary part.
The source SHA-256 is
`3cfffb177b6d789efdee7e81de72e7cb46d6a340cd68129a67d45584ecc47374`
and the raw stdout SHA-256 is
`fd6c09ad969ea84d23f46da18ad98b2883dc39fc070827d8b56078d9fb171841`.
This repository receipt covers prefix 3. The full selected-group
result above comes from the separate scratch replay. For parallel
replay, record the pinned source and command for each disjoint
half-open prefix range and verify exact status and ordered coverage
before reducing raw numerators with the common divisor.

The pinned repository replay at `83ae2cff6` also completed
`python l1_unpaired_A_pairwise.py 0 3` with exit zero. All 48
ordered keys, statuses, raw signed coefficients and complement counts
matched the independently assembled scratch receipt. Each of the
three prefixes has exact subtotal zero in both components. Raw
stdout SHA-256 is
`fb05d207c0aad6dd605df55d893722a39a5b66f29f6620adf159bc343d883be4`.

**Dominant-map pair.** Bulk indices 4,776 and 17,672 have the same
208-row B primitive and exact opposite signed scales. Independent
review reconstructed both exact B hashes and checked that the two
changed coordinates, `q51` and `q53`, occur only in A center 1.
Subtracting the two center maps leaves 24 signed rows with
coefficients ±4. The pair uses its own regenerated roster of 1,152
leaves over 72 prefixes, SHA-256
`489f340dc12c5e1935e05b842b46325bb2573a14fa575066835b76b6e2b94cf4`.
All 16 leaves of prefix 0 have empty complementary products and
exact zero numerators. The independent scratch JSONL SHA-256 is
`c41d1dd322a32bf9ece899ae260028f73fc8887b73c3ff44c7aa814953a9fab9`.
This establishes one prefix for the pair. A port must preserve the
coordinate incidence guards and the common signed scale.

Independent review accepted the next range `[1,5)` against the
same roster digest. Its 64 ordered leaves were exact with no caps.
Prefixes 1 and 2 are zero. Prefixes 3 and 4 each have eight negative
and eight zero leaves and 8,688 complementary pairs. Applying the
positive scale of index 17,672 once to the raw sum and dividing by
the common divisor gives `−88476104653270299/9444732965739290427392`
with zero imaginary part. Scratch JSONL SHA-256 is
`5ceb2b8c307d8e3d5101ad60db3e3abc99f1ee4484dfd967270597d5d4d7c089`.
The accepted contiguous range is now `[0,5)` for this pair, leaving
67 prefixes and the other dominant-map occurrences open.

Independent review accepted another 256 exact leaves over four
disjoint ranges of the same roster, with no caps and zero imaginary
components. The raw rows were reduced using the same signed scale
and divisor.

| Prefix range | Exact subtotal | Raw JSONL SHA-256 |
|---|---:|---|
| `[5,9)` | `85486870439155395/18889465931478580854784` | `0546adcc397b7756166fa09af2641c202d15f26bd9d6b890652bd558dacabbeb` |
| `[9,13)` | `−91465338867385203/18889465931478580854784` | `d527d47c0d081c911d70da27d36149aa076767b3a339b6eb9108102695f20077` |
| `[13,17)` | `−373654276764363/2361183241434822606848` | `b2c03de342f6eb66a1a322a3110fd4b2f22b84b4cef457009027003da9eb2253` |
| `[17,21)` | `−88476104653270299/18889465931478580854784` | `3934f261eac3b26382bf7fe7b697fc2de8eea2da83342dff17d92f9a7235a10e` |

The accepted union `[0,21)` has 336 distinct ordered leaves and
subtotal `−274396016602155609/18889465931478580854784`.
Fifty-one prefixes remain for this pair.

**Dominant-map grouping.** Independent review reconciled 9,211
distinct indexed occurrences and five disjoint older exact B
receipts. The signed scale of each of the 9,216 occurrences
reconstructs its exact B hash from the common 208-row primitive.
On the A side only center 1 depends on `q51,q53`. Holding
`(q71,q73,q133,q151,q153)` fixed therefore permits the weighted
center maps to be summed before the full contraction. The
disjoint partition contains 4,608 singletons, 1,536 pairs, and
512 triples, for 6,656 groups. No weighted center map vanishes.
The singles have 16 rows and the pairs and triples have 24.
Normalizing the signed coefficient gcd gives 25 center-1
primitive maps. This normalization only identifies the center-1
factor. The other A factors must still be accounted for before
reusing any complete contraction. The reviewed scratch census
stdout SHA-256 is
`246d3bd6e12440d1adf4b34e5ec3f0f7100648a27c9b16fea70c56785c512aeb`.

Independent review accepted the next 256 exact leaves with no caps
on the same regenerated roster. Each imaginary subtotal is zero.

| Prefix range | Exact subtotal | Raw JSONL SHA-256 |
|---|---:|---|
| `[21,25)` | `−91465338867385203/18889465931478580854784` | `2a80b16d55d15e05e58bfe2da37bda226b399408cf244fc35b159af634de2b0e` |
| `[25,29)` | `−373654276764363/2361183241434822606848` | `0e18d422663466211852a7232ed39e7f1608f9f06b728f626641019be0a596c6` |
| `[29,33)` | `−88476104653270299/18889465931478580854784` | `f37e3581be7c109e3e0b812d44d96ab880e9f991be7fd58309257abce6aa0fc8` |
| `[33,37)` | `−91465338867385203/18889465931478580854784` | `1e47aec30ebb0bbc263d0de72ffb71abe1f08373573aead29a7e7f9167808d62` |

The accepted union `[0,37)` now covers 592 distinct ordered
leaves and gives `−274396016602155609/9444732965739290427392`.
The new block subtotal equals the prior block by exact reduction.
The remaining 35 prefixes still require evaluation and review.

Independent review accepted the 256 exact leaves in `[37,53)`.
The regenerated roster digest is unchanged, no leaf capped, and
all imaginary subtotals are zero.

| Prefix range | Exact subtotal | Raw JSONL SHA-256 |
|---|---:|---|
| `[37,41)` | `−373654276764363/2361183241434822606848` | `1115ec0b48616226878e365582fa32f014e561856d62c53aa8048804cba1a0a4` |
| `[41,45)` | `−88476104653270299/18889465931478580854784` | `c6677864cab064926ce1451f694aac97dc31cd092af223627fed4a916f719940` |
| `[45,49)` | `−91465338867385203/18889465931478580854784` | `4b5e8602466bc6b58bd307493459cea3f02fbe4f8665363207406d34424a0f1c` |
| `[49,53)` | `−88476104653270299/9444732965739290427392` | `0ce1f444cd1ad34c90dfa9f7b8769a09cb2428eb9bd4ed4ad603f2751020c40d` |

The accepted union `[0,53)` covers 848 ordered leaves and gives
`−454337460122811111/9444732965739290427392` with zero imaginary
part. The final 19 prefixes of the pair remain due.

**Complete dominant-pair contraction.** The final five shards
cover all 304 remaining leaves exactly, with no caps.

| Prefix range | Exact real subtotal | Raw JSONL SHA-256 |
|---|---:|---|
| `[53,57)` | `85486870439155395/18889465931478580854784` | `dc7e969cc19bf9a780872317dab1078d9c1d139eef93aa924eec8f22a2fb501a` |
| `[57,61)` | `−91465338867385203/18889465931478580854784` | `56c4c28c225b7b792e12c6bbd5a471d1076bd86ac3c5843a07418d16152ce0ea` |
| `[61,65)` | `−373654276764363/2361183241434822606848` | `cd8596bdd139345bd1f5154c70a30c81671f30ec0dd071f8dea7acd0b7b5baa3` |
| `[65,69)` | `−88476104653270299/18889465931478580854784` | `b897362d9a91d4e57b48c45a570868acb926ef03a4900c8b45c86904f532db2e` |
| `[69,72)` | `−91465338867385203/18889465931478580854784` | `7262e67520f24cd3551b282a6bdfc274cc9bced102ddc6b9c2c2b7a66c229506` |

Independent review matched the complete scratch union to the
pinned roster digest. There are 816 zero, 264 negative and
72 positive leaves. The combined contribution of indices 4,776
and 17,672 is `−274396016602155609/4722366482869645213696`
with zero imaginary part. This is a joint contribution to the
selected word sum. It does not separate the two tuple values.

The independently reviewed [repository runner](l1_unpaired_A_dominant_pair.py)
regenerates both B maps by direct and factored evaluation,
checks their exact and primitive hashes and opposite scales,
and pins the projected roster. The repository run `0 1`
matched all 16 scratch leaf keys, raw values and pair counts.
The source SHA-256 is
`3a35f3bd94039873da8bcc3be1c77b2b9437f3b3c3616e57965349735559ecc2`
and its prefix-0 stdout SHA-256 is
`35c8bc6443586220c206b3ce0e237ab9520008e881ff09faf13f4a8200d605ef`.
The full exact total above is from the reviewed scratch union.

The full repository replay `python l1_unpaired_A_dominant_pair.py
0 72` at `8ab9b3288` exited zero. Independent review matched all
1,152 raw keys, statuses, real and imaginary numerators and
complement counts to the complete scratch union. It reproduced
the same roster digest and exact total without a cap. The raw
repository stdout SHA-256 is
`549235ff9768e6afd2f2ccd7a3ee5c8bb9910b2558c06731a3a72591f7332a86`.

**Rank-one partition for the dominant map.** The reviewed
[manifest generator](l1_unpaired_A_dominant_components.py) replays
the 9,216 signed occurrences against their exact B hashes.
It accounts for all 6,656 fixed-coordinate groups in 104 blocks.
Each block holds normalized centers 1 and 9 fixed and partitions
the center-3/center-11 weight matrix into 20 integer rank-one
components. The 2,080 components consist of 1,248 of shape
1×1, 416 of 1×5, 312 of 4×1, and 104
of 4×5. The generator checks each coefficient, including
implicit zeros, against the integer outer product. Independent
review rehashed all 78 receipt inputs and matched each word
and signed scale to its unique manifest membership. The repository
generator reproduced the same manifest byte for byte, SHA-256
`eebf286061137a1354f831fae29ad20223bf74ce43f22aaa90e15a98b5031e75`.
Replay requires the explicit B receipts and primitive input.
The emitted hashes fingerprint the weighted factors.

For block 0, component 3, an independent local check matched
all 221,184 joint coefficients of the weighted pair to the
explicit 20-term sum over 60 original B words. The exterior
scalar check remains open. The initial join hit the 120,000-row
cap when attaching weighted center 11. Deferring that attachment
moved the cap to a site-1 join that closes no site. Neither route
reached a supported leaf. The next comparison must preserve the
complete conditioned label sum, the same exact scale and divisor,
and the existing cap.

Conditioning on the shared site-1 gamma label gave the exact
intersection `[(0,), (1,), (2,), (3,)]` at its two incidences.
In the first slice, the join that closes site 10 emitted
120,001 slots before completing, above the unchanged 120,000
cap. The two operands had 15,552 and 336 rows and no common
ordinary label at that join. The unclosed grades on sites
1, 2, 9, and 11 are all four. No slice reached the exterior
roster. The next attempt tests alternate exact join orders
within each conditioned slice.

**Minority-map census.** Independent review verified 576
distinct occurrences across six primitives, using 506 indexed
and 70 additional legacy receipts. The two 36-row primitives
each occur 144 times. The two 72-row and two 162-row primitives
each occur 72 times. Each occurrence reconstructs the exact B
digest from its primitive and signed scale. Within each
primitive, holding all cut labels except the two at center 1
fixed produces only singleton groups. The normalized full A
center signatures are also distinct. Grouping on centers 1
and 9 organizes the minority cases into eight-member blocks.
That census alone leaves their scalar contractions open.

Independent review verified a separate exact pairing across
the minority maps. There are 288 disjoint pairs, split as
72 pairs for each 36-row primitive and 36 for each other
primitive. Members share their exact B hash and signed scale,
and differ only at `q(15,1)`, taking values 0 and 4. That
coordinate occurs on the A side only at center 11. The two
frozen center factors have matching axes and disjoint
144-row supports, yielding a 288-row sum for every pair.
The census stdout SHA-256 is
`cced0771f3436665ff6244c4d2e24d4c47c62828b3a32f06a46a764cd5dbd6a1`.
This proves the input pairing and leaves the exterior sums
open. The 162-row pair at indices 34 and 35 is the first
new scalar control.

In the dominant pilot, an alternate join order in the first
site-1 slice avoided the initial cap by taking a 31,616-row
join. At the next step all 14 admissible joins hit the same
limits. Ten hit the 120,000-row cap, and four hit the 300,000
compatible-product cap. The only candidate that closed a
site was the site-10 closure. It hit the row cap. The next
route keeps its four exterior grade-four bytes factored
and queries the opposite environment before emitting rows.

**Minority 162-row pair.** For indices 34 and 35, both B routes
regenerated the same signed 162-row map and the two frozen center-11
factors summed to 288 rows. The projected roster keeps 2,304 of
3,072 candidate leaves in 72 prefixes of 32. Its SHA-256 is
`7c7950b416c5f358873483fccd6e750fc38cc5582eaa54dcf3863babfec7ec6a`.
Independent review verified the contiguous first 1,248 leaves.
Of those, 780 are zero, 396 positive, and 72 negative, with
922,752 complementary pairs. Applying the common signed scale
and divisor once gives `14474789200618929/4611686018427387904`
with zero imaginary part. Stdout SHA-256 is
`d73859b00fc5d6d1b3250c90c7756f351a4a2d52e397cbeecc0277ce63fbfda4`.
The wall alarm ended this run after 39 complete prefixes with no
recorded join cap. The remaining 1,056 leaves require a separate
disjoint replay on the same roster.

A bounded cache control matched the first 96 raw results. Both
sides depend on all six external labels, so neither side reused
a materialization on those leaves. Caching whole sides by external
keys does not address repeated joins within a side.

**Site-10 query control.** On a signed two-product fixture the
sparse complement query and materialized contraction both give
`−32−64i`. The query applies the incident wedge sign and then the
exterior complement sign. The actual weighted target reached the
15,552-by-336 site-10 cut. The fixture qualifies the arithmetic
on that control; the target result and its unfactored comparison
remain open.

The suffix for minority indices 34 and 35 exited zero and
covered all 1,056 remaining leaves exactly. It contributed
`12247898554369863/4611686018427387904` with zero imaginary part.
Its stdout SHA-256 is
`e3f3a2218f94847842465a197a921f9a7ff0b501bf5a648a97f23c141e59581f`.
Independent review matched the combined 2,304 ordered leaves
to the full roster digest above. The union has 1,440 zero,
720 positive and 144 negative leaves. The pair contributes
`3340335969373599/576460752303423488` with zero imaginary part
to the word sum.

The independently source-reviewed [generic minority runner](l1_unpaired_A_minority_pair.py)
takes the explicit two coordinates, expected exact B hash and
optional roster hash. It regenerates both B maps and checks the
center-11 incidence. An empty range is a roster census. For
indices 4 and 5, a separate 36-row primitive control exercised
the runner over `[0,32)` and gave
`21945749275359/18446744073709551616` with zero imaginary part.
The roster matched the 2,304-leaf digest above. The control
stdout SHA-256 is
`eeb79d035184857c414e71a69cb2f6a4f18c6ac2542bbbd275cd1c7172c9c98f`.
That run used source SHA-256
`47c80de136832690718858f964ebcf903e2038859ba8a717cc90478ebce3dcd0`
before the tuple/range receipt header and census help were added.

**Complete 36-row minority control.** The repository runner
completed indices 4 and 5 in disjoint ranges `[0,32)` and
`[32,2304)`. Independent review verified all 2,304 exact leaves,
the same roster digest, the regenerated signed B map and the
normalization. There are 1,440 zero, 720 positive and 144 negative
leaves. The suffix gives
`1686446425083357/18446744073709551616` with zero imaginary part.
The full pair contributes `427098043589679/4611686018427387904`
with zero imaginary part. The suffix stdout SHA-256 is
`1169d875ca9d3dc9c4143e45d97c76440491131978348ac0f838307690535bb0`.
It used the repository runner at `ca1ec11ab`. Independent review
reproduced the earlier source hash by reverting only the receipt
header and CLI help changes.

**Complete 72-row minority control.** For indices 13,156 and
13,158, the repository assembly regenerated the same signed
72-row B map for both words. The projected roster has 2,304
leaves and SHA-256
`d5130984b0161d7589797ce8ed832e26bc247eec0435a485e940728779e47535`.
The first replay reached the wall limit after 1,869 exact leaves.
The disjoint suffix exited zero with 435 exact leaves. Independent
review matched their ordered union to the full roster. There are
1,440 zero, 720 positive and 144 negative leaves, with 940,032
complementary pairs. The joint contribution is
`871859979116847/144115188075855872` with zero imaginary part.
The prefix and suffix stdout SHA-256 values are
`73693f6f3d80a378c2294099719f12e6712a43cdea7de4a3149eed837084f7f8`
and
`377a439ccde40c7d4f71686e3ac5a8ba3e3de1e1223d588c40444b2cba1c302b`.

**Conditioned site-10 query.** For the first weighted selector,
the indexed search reaches its visit limit on boundary query 186.
Independent review verified an exact split of that complement
query over the joint values of `gamma(11,3)` and `q(11,3)`.
Each label occurs at the same two factors, and intersecting the
paired supports yields 16 disjoint slices. All 16 slices finish
with zero matching products and no cap. This certifies zero for
the queried complement. The outer diagnostic stops at this query
and supplies no scalar for the selector. The raw stdout SHA-256
is `ef8951148298f1830af9a7ecb64e379660df1946c1c15f0142d0ee470cc415ab`.

**Minority bulk inputs and exact reuse.** The independently
reviewed [manifest generator](l1_unpaired_A_minority_manifest.py)
binds the 78 input receipt hashes and covers all 576 minority
words exactly once. It emits 288 ordered pairs with signed B
hashes and scales, source origins, and weighted center-11 hashes.
The repository replay is byte-identical under input path
reordering. The manifest SHA-256 is
`48d9d1cf6ed7445be86b772602f8ee682966f56d4c6c0c7f301eb9e5938e40c4`.
The three completed controls are pair IDs 0, 24, and 52. The
manifest admits independent pair runs with the existing runner
and supplies no scalar results by itself.

A separate scratch replay for pair 0 shared a materialization
only when the full ordered frozen-factor inputs were equal.
The keys retain axes, signed Gaussian rows, exterior masks
and site grades. Independent review matched all 2,304 result
rows to the uncached receipts. The cache recorded 1,368 hits
and 3,240 misses. It peaked at 120,000 retained logical row
slots across keys and results, with at most 128 entries.
The stdout SHA-256 is
`c47db55216c7a795ddb4215237cb28fb69d3ed914bb423ea3f0f7e1b0f190784`.
This verifies exactness for the one pair. A controlled speed
comparison remains open.

For the weighted site-10 selector, the candidate census has
8,956 compatible products and 4,174 distinct complement queries.
Each paired byte subset, sites 1 and 2 or sites 9 and 11, has 318
distinct values. The full selector reached its wall limit after
151 completed 16-slice fallbacks without a per-slice cap. The
next reuse target is a partial environment transfer that retains
its shared labels, boundary masks and signed coefficients.

**First disjoint minority manifest batch.** Independent review
verified IDs 1 and 2 against their signed B inputs. Each has all
2,304 exact ordered leaves and zero imaginary part, with no caps.

| Manifest ID | Exact real subtotal | Roster SHA-256 | Stdout SHA-256 |
|---|---:|---|---|
| 1 | `454108196543967/4611686018427387904` | `ee3dc0fce0d794f5fd56d22a97c7c57849b540593178e482984086a8478de83a` | `a58caf1cc1901cee5fffa8b46f343e0d90531afb6005305d89a9011974bad338` |
| 2 | `470989542140397/4611686018427387904` | `f097c6aefd81af88b01661845763a570a9e71e39fb4109b9b2c83b1fab2ba1de` | `4a65183d4f1b90d1296bc7f7cb78b63d0818a9fb362f6ab29df2aa90a41aa0f6` |

The fixed 256-leaf pair-0 benchmark ran direct, cached, cached,
direct after a common assembly. All four outputs were identical.
The uncached CPU times were 15.42 and 15.34 seconds. The cache
took 16.98 and 16.99 seconds, despite 152 hits in each pass.
The current cache is therefore kept out of bulk replay.

**Weighted site-10 selector control.** The paired partial
transfers completed all 4,174 distinct complement queries from
8,956 compatible site-10 products. Of these queries, 1,786 have
nonzero environments. Eight actual queries, including two
nonzero cases, matched the earlier indexed route. For the
all-zero external gamma labels and internal `gamma(1,1)=(0,)`,
the weighted component gives
`30242684552249295/18889465931478580854784` with zero imaginary part.

Independent review reconstructed the 20 original matrix
weights and checked each unfactored raw Gaussian result times
its signed weight. All 20 terms completed within the same caps
and used the same selector and cut. The sum agrees exactly
with the weighted route after applying the common divisor once.
Both routes share the partial-transfer routine. The comparison
verifies the weighting and grouping for this conditioned
selector. The remaining internal slices and exterior selectors
are separate. The weighted and unfactored stdout SHA-256 values are
`a4c8e0a2a649a75e425b83046a7279bbbec96ff7de509d177e761f327a8d376f`
and
`65017657906d5dd872b532330ae403cd2f4c31aef75c04ea0f598aa5ad24d6db`.

**Full scalar for the first exterior selector.** The exact
intersection of the two internal gamma incidences is
`[(0,), (1,), (2,), (3,)]`. For the fixed exterior selector,
the last three slices each lack the required left-table key.
Independent review confirmed their exact zero contributions
under the same cut and guards. All three runs exited zero.
Together with slice 0, this exhausts the internal labels for
this selector and gives
`30242684552249295/18889465931478580854784` with zero imaginary
part. The other exterior selectors remain open.

| Internal gamma slice | Raw stdout SHA-256 |
|---|---|
| `(1,)` | `ac4fedf7eb0ff709c2967bb67cffe0ad21528baa323252be1a6ff73f3349d776` |
| `(2,)` | `f41c262525473f90e5e77154d05541c7fd0a38bbd1f1bab95e8a2555b122f8a6` |
| `(3,)` | `dd655367fea9a08ca051bfa2402349ee9c1c58f229f280f96932397145013cfa` |

**Minority manifest IDs 3 and 4.** Independent review matched
both signed B inputs and all 2,304 ordered leaves of each pair
to the regenerated rosters, with no caps and zero imaginary
part. ID 4 cancels the previously verified ID 52 contribution
to the word sum. The two evaluations establish that cancellation.

| Manifest ID | Exact real subtotal | Roster SHA-256 | Stdout SHA-256 |
|---|---:|---|---|
| 3 | `470989542140397/4611686018427387904` | `cfc0228ea35ffdb5a01b6d1ce785c14654c608972b4107c0970ab85b0e3515a0` | `a3ae1e8d77db67f895fc2eb5648eed8ef8aef4d64eaff35413c30aca5a8fdc19` |
| 4 | `−871859979116847/144115188075855872` | `d5130984b0161d7589797ce8ed832e26bc247eec0435a485e940728779e47535` | `21f580eaaf7cbe2ae1095e02dfb87a0702f4f621b0ccac849b5cf52bf04588e5` |


**Exterior selector census.** Independent review verified the
necessary support of the weighted site-10 component from the
actual signed factor keys and the correlated projections of the
opposite factors. Each internal gamma slice gives 64 candidates.
There are 256 distinct exterior selectors. Each has a unique
internal slice, since the exterior gamma at `(1,3)` equals
the internal gamma value in every retained row. The four
disjoint ranges are `[0,64)`, `[64,128)`, `[128,192)` and
`[192,256)`. Row 0 is the already verified scalar. The other
255 rows still need exact contraction. The ordered roster SHA-256
is `b8bde9d2380ff0fa25a5d2478cd30042c4144d024638729801ddbd5c439e4dae`.
The census stdout SHA-256 is
`4823aa1223c813c6ada21d32464d3c17b584d1f8b00a40606e9fccd2ca339c57`.

**Selector batch `[1,8)`.** All seven weighted selectors in
this disjoint interval exited exact under the original caps.
Independent review checked the pinned exterior roster, raw
signed numerators, and divisor. Each selector evaluated 8,956
compatible products and 4,174 distinct complement queries.
The interval contributes `−312275330437816179/37778931862957161709568`
with zero imaginary part. The run took 57.41 seconds including
assembly and 20.07 seconds after assembly. Stdout SHA-256 is
`2fa68f18c90a654b73562fc3684ecaef350439890774796ec0d1d430a99e5419`.
The first eight of 256 selectors now have verified scalars.

**Minority manifest IDs 5 and 6.** Both complete 2,304-leaf
receipts passed independent verification with no caps.
Each contributes `−871859979116847/144115188075855872` with zero
imaginary part.

| ID | Roster SHA-256 | Stdout SHA-256 |
|---|---|---|
| 5 | `c9df3f9363627766347ff8f971c16b2c1db9873bae6ce7658cac78c5548cc58d` | `5fc724eaacd3ebebd56eb0d7e53270a5305b3bb9a32580f12546e42399ba9875` |
| 6 | `dfa01092e60d4ce09c3f7e50e043009931a106e985a0d79a286de5bab4b07090` | `ee4f4caf7ab5c2b593d122d6714c60428b418a943bffb540002d14092aac2815` |

**Selector batch `[8,32)`.** Independent review verified all
24 exact rows on the pinned roster with no caps. Each row
evaluated 8,956 compatible products and 4,174 complement queries.
The exact real subtotal is
`1008348807432951747/37778931862957161709568`, with zero imaginary
part. The run took 101.54 seconds including assembly and 66.68
seconds after assembly. Stdout SHA-256 is
`908c80c779cb6f0628b2071d4498e0f844252be7db32a77865ec92de6494d888`.
The first 32 of 256 selectors now have verified scalars.

**Minority manifest IDs 7 and 8.** Both complete 2,304-leaf
receipts passed independent verification with no caps and zero
imaginary parts.

| ID | Exact real subtotal | Roster SHA-256 | Stdout SHA-256 |
|---|---:|---|---|
| 7 | `−871859979116847/144115188075855872` | `608c4d56a2f7c6f3eff75a84082bfd9e83d2d0ff0e7e0b79b1d6132f53acfba4` | `733f27ea6a5ffa8b4acc12b0b5b0ba39cc8ed07780efc3b20de36985da7f0a53` |
| 8 | `−207640550836089/2305843009213693952` | `7c7950b416c5f358873483fccd6e750fc38cc5582eaa54dcf3863babfec7ec6a` | `ecff25806cd467f173b28a7acb53702b77eee8d87564d89b7cd0e7e559f72028` |

**Complete first internal slice.** Independent review verified
the two disjoint batches `[32,48)` and `[48,64)` against the
same roster. All 32 additional rows are exact with no caps.
Each batch contributes
`378279423049817079/37778931862957161709568` with zero imaginary
part. The full `[0,64)` slice subtotal is
`378279423049817079/9444732965739290427392` with zero imaginary
part. The two new stdout SHA-256 values are
`0bdbd4771a6ec4f9a7a4d0e96be95799e91b4ad785fb0905bf92c9cf2c5b92dc`
and
`61232bf290a7f4de2a29e1ab30866bc2b9f319b2f4b8a7713c18ec34c6307c31`.
The other three slices remain separate.

**Second-slice selector batch `[64,80)`.** Independent review
verified all 16 exact rows on the pinned exterior roster, with no
caps. Each evaluated 8,956 compatible products and 4,174 distinct
complement queries. The exact subtotal is
`378279423049817079/37778931862957161709568` with zero imaginary part.
The stdout SHA-256 is
`e270d8afe58cf1319a92b046900ab212425f508f988613e8324f822076888d9c`.
The first 80 of 256 selector scalars have verified receipts.

**Minority manifest IDs 9 and 10.** Both 2,304-leaf receipts passed
independent verification with no caps. Each contributes
`−231274434671091/2305843009213693952` with zero imaginary part.

| ID | Roster SHA-256 | Stdout SHA-256 |
|---|---|---|
| 9 | `ee3dc0fce0d794f5fd56d22a97c7c57849b540593178e482984086a8478de83a` | `def0caa6124b665a740e3867f1bd516b2eac8ef9d98a5b22d4a18017a7f29d93` |
| 10 | `f097c6aefd81af88b01661845763a570a9e71e39fb4109b9b2c83b1fab2ba1de` | `3c735792898dfeed0bf6997a37148f67933cef89df8048a9e008bc8f0fdf9be9` |

**Repository site-10 replay.** The independently reviewed
[runner](l1_unpaired_A_site10.py) reconstructs the target 60-word
component from explicit signed B receipts. It checks its member
indices, weighted-factor digest, the full 256-selector roster,
and the requested internal slice. It retains the original row
and product caps and supplies a terminal subtotal only after
the complete requested range.

The repository control `[33,34)` reproduced the scratch selector
exactly. Its scalar is `16188097425307101/9444732965739290427392`
with zero imaginary part, from 8,956 compatible products, 4,174
complement queries and 2,038 nonzero environments. The runner
also rejected a range outside its requested slice. The source
SHA-256 is
`b88a65eae741df00d90b73cf1766b6f477a1081551a83d37d5d2d8fa47cb88c9`.
The control stdout SHA-256 is
`be75be107b3a2bf52c6871a1a132abefda2ac6d2d5e4116a874a13045f44001f`.
This comparison exercises one repository selector. Earlier
full-range receipts came from the reviewed scratch driver.

**Second-slice selector batch `[80,96)`.** Independent review
verified all 16 exact rows on the same exterior roster with no
caps. Each evaluated 8,956 compatible products and 4,174 distinct
complement queries. The interval contributes
`378279423049817079/37778931862957161709568` with zero imaginary part.
The stdout SHA-256 is
`c4f2f49419782b0023c1cdf76cfd895747684f3e4c8afbec88c57c44daba2b93`.
The first 96 of 256 selector scalars now have verified receipts.

**Complete second internal slice.** The repository runner
completed `[96,112)` and `[112,128)`. Independent review
verified all 32 exact selectors against the pinned roster.
Every selector evaluated 8,956 compatible products and 4,174
complement queries with no caps. Each range contributes
`378279423049817079/37778931862957161709568` with zero imaginary
part. The complete second slice `[64,128)` contributes
`378279423049817079/9444732965739290427392`, equal to the first
slice by exact summation. The two new stdout SHA-256 values are
`9f5c4cd51f661ce6b96da54de756ea936afc5e258875309d68919c16d40a691d`
and
`554618901b360933d05c6b650770ea26e3d241b842aa62613a6f92852641ee11`.
Two of four slices are complete.

**Minority manifest IDs 11 and 12.** Both 2,304-leaf receipts
passed independent signed-roster verification with no caps
and zero imaginary part.

| ID | Exact real subtotal | Roster SHA-256 | Stdout SHA-256 |
|---|---:|---|---|
| 11 | `−241403242028949/2305843009213693952` | `cfc0228ea35ffdb5a01b6d1ce785c14654c608972b4107c0970ab85b0e3515a0` | `4496823abdccd3935055769f223ec62ff955a8b0ee97c6e3185dcbdd650c1421` |
| 12 | `871859979116847/144115188075855872` | `d5130984b0161d7589797ce8ed832e26bc247eec0435a485e940728779e47535` | `31980880099a6b0796e4efbe80232bfd6a909f631383af49a892de7e2cc69ca3` |

**Third-slice batches `[128,144)` and `[144,160)`.** The
repository runner exited zero in both ranges. Independent review
verified all 32 exact rows against the pinned roster, with no caps.
Every selector evaluated 8,956 compatible products and 4,174
complement queries. Each range contributes
`378279423049817079/37778931862957161709568` with zero imaginary part.
The stdout SHA-256 values are
`e56576d7ff6a3298dfd40ed19f3650a2e9fcfd5d93d023b351bc079c685e1b48`
and
`1e2ba037a1288fd6456350eab5e0eca94a9cd0741d152dab90005727763f1a95`.
The first 160 of the 256 selector scalars have verified receipts.

**Selector ranges `[160,176)` and `[192,208)`.** Independent
review verified both 16-row receipts against the pinned roster,
with no caps. Each row evaluated 8,956 compatible products and
4,174 complement queries. Each range contributes
`378279423049817079/37778931862957161709568` with zero imaginary part.
The respective stdout SHA-256 values are
`88a7637529038fcb2bb21330769969e7ef962dedc45b7c46abcf86e374f0c271`
and
`d9a691abad122c02724c2b064a7ab1d79170b02deb6061a97f7e41e953bc43b6`.
Verified coverage is `[0,176)` and `[192,208)`, for 192 of
the 256 selectors.

**Minority manifest IDs 13 and 14.** Each 2,304-leaf receipt
passed independent signed-roster verification with no caps.
Both contribute `871859979116847/144115188075855872` with zero
imaginary part.

| ID | Roster SHA-256 | Stdout SHA-256 |
|---|---|---|
| 13 | `c9df3f9363627766347ff8f971c16b2c1db9873bae6ce7658cac78c5548cc58d` | `f38de68e8fccb501c4cf8ace7142607a0e97ffd305132224ff8034c532829b3d` |
| 14 | `dfa01092e60d4ce09c3f7e50e043009931a106e985a0d79a286de5bab4b07090` | `5aa079a20da8d4d3c5d0362c7c6abcad76e3bdc66fbf44955cc3d3ce1ae456a8` |

**Complete weighted 60-word component.** The final four
ranges each have 16 exact scalars and no caps. Each contributes
`378279423049817079/37778931862957161709568` with zero imaginary part.

| Selector range | Stdout SHA-256 |
|---|---|
| `[176,192)` | `afe38eaf7fbecf06d7764a73f4e7c9d5c106e169328a5d83dd3dce9ab507189d` |
| `[208,224)` | `343022347fdfeace0d01bacc7a2d36cbeeb2760e78481a8d88f596f7099e15db` |
| `[224,240)` | `d0edf4eddc7c0f31a4cc798beed8ac0ee627231d72fb3d0e4ad98211b2c3dfeb` |
| `[240,256)` | `3d75cab25bbfb58a97af8ca7e6be45903fc97260eab93d76df65c1d37c9010f4` |

Independent review bound selector 0 to its explicit exterior
tuple and reduced the raw receipts for all 256 distinct keys
against the pinned roster. Each of the four internal slices
contributes `378279423049817079/9444732965739290427392`. These
equalities follow from the raw sums. Applying the common
divisor once to the full union gives
`378279423049817079/2361183241434822606848` with zero imaginary part.
This closes the selected component of the dominant word sum.
The other components require their own evaluation or an exact
reduction that preserves all their factors and weights.

**Minority Spin symmetry and verified subtotal.** Independent
review verified the disjoint partition of all 288 minority
pairs into 34 orbits under proper signed axis permutations
in each chirality. The orbit sizes are 3 (six), 6 (twelve),
9 (ten), and 18 (six). The witness for each member maps both
fixed words and keeps the exact signed B digest and scale.

The chiral quarter-turn generators act by unitary conjugation
on the links and by a proper orthogonal rotation on the Dirac
coframe labels. They preserve Haar measure, fixed identity links,
the paired Dirac contractions, oriented action, source frames,
and the Berezin volume. The six minority B primitives are
invariant under the signed exterior expansion for the generators
on both chiralities. On A, each fixed cut coordinate occurs
at one live face. The two retained coordinates are unit support
restrictions. The three equal-coordinate pairs therefore cancel
their two matching signs, and the seventh coordinate is a
chirality scalar. These facts identify complete pair coefficients.

Independent reduction verified 18 exact pair receipts across
12 represented orbits, with all six within-orbit comparisons
agreeing. Multiplicity weighting gives
`4451788014082227/36028797018963968` with zero imaginary part
across 81 pairs. The orbit manifest SHA-256 is
`aebcb716a1f6bb0b66dd9d5bad3e33afba9d21829111c382cf572ea2a599024c`.
The remaining 22 orbits still require representative evaluation.

**Second dominant component control.** At selector 0 in
component `(0,0)`, the direct route gives
`26336732102857701/18889465931478580854784` with zero imaginary part.
The signed site-10 pair and the physical opposite-side Q
factors match the first component on this selector. Independent
review verified three exact coefficientwise controls for shared Q,
including one with four rows. The shared calculation then hit
the original live-row cap. The direct scalar is verified and
the full shared-Q contraction remains open.

The repository [orbit generator](l1_unpaired_A_minority_spin_orbits.py)
reproduces the signed orbit manifest from the pinned minority
manifest, exact primitive maps, and explicit direct receipts.
It checks both transformed words, the paired signs, the exact B
identity, and all observed coefficient equalities before
writing each orbit. Replaying the 18 direct receipts reproduced
the reviewed manifest byte for byte. The generator SHA-256 is
`586038c666e4956871e2d4193e7d8f9d58200416a9469fedcafa8170a8b57d61`.

**Minority orbit reduction readback.** These are the accepted
coefficients and multiplicities that produce the 81-pair subtotal.
Every imaginary coefficient is zero. ID 16 was evaluated separately
after the original manifest replay and matched ID 8 exactly.

| Orbit representative | Multiplicity | Directly evaluated IDs | Exact real coefficient |
|---|---:|---|---:|
| 0 | 3 | 0 | `427098043589679/4611686018427387904` |
| 1 | 3 | 1 | `454108196543967/4611686018427387904` |
| 2 | 6 | 2, 3 | `470989542140397/4611686018427387904` |
| 4 | 3 | 4 | `−871859979116847/144115188075855872` |
| 5 | 9 | 5, 6, 7 | `−871859979116847/144115188075855872` |
| 8 | 6 | 8, 16 | `−207640550836089/2305843009213693952` |
| 9 | 6 | 9 | `−231274434671091/2305843009213693952` |
| 10 | 6 | 10 | `−231274434671091/2305843009213693952` |
| 11 | 6 | 11 | `−241403242028949/2305843009213693952` |
| 12 | 6 | 12, 52 | `871859979116847/144115188075855872` |
| 13 | 18 | 13, 14, 15 | `871859979116847/144115188075855872` |
| 24 | 9 | 24 | `3340335969373599/576460752303423488` |

ID 16 has 2,304 exact leaves and no caps. Its stdout SHA-256 is
`fc627a7c25f5e87c15ce0abf3d09cec4953643041c9e89e5f4db9e8d09016969`.
It supplies a seventh within-orbit comparison and leaves
the multiplicity-weighted subtotal unchanged.

**Exact reuse of signed site-10 weights.** Independent review
verified that a single signed map of 4,174 complement masks,
built from 8,956 compatible products, reproduces both direct
selector-0 results for components `(0,3)` and `(0,0)`.
The respective real scalars are
`30242684552249295/18889465931478580854784` and
`26336732102857701/18889465931478580854784`, with zero imaginary
parts. Each uses its own opposite-side transfer. The shared
map took 0.025 seconds to prepare, and the two subsequent
contractions took 3.05 and 2.70 seconds. Thus this exact reuse
has limited effect on the overall cost of the two selectors.
The stdout SHA-256 is
`d1436991977a1b99454e3dc2b99339c9e4cef700252affc43828adcd0044a0b0`.

### Dominant Spin orbit reduction

The four chiral Spin quarter-turns preserve all 208 exact rows of
the dominant B primitive. Each generator permutes all 9,216 words
and maps each rank-one component onto a complete component. The
transformed B scale acquires the same coordinate sign as the A
probe, so the signs cancel in the contracted scalar. The independent
replay checked every generator action and reconstructed the same
148 component orbits from the 2,080 components.

| Orbit size | Component orbits |
|---:|---:|
| 1 | 4 |
| 3 | 20 |
| 6 | 6 |
| 9 | 48 |
| 18 | 54 |
| 36 | 16 |

The [orbit generator](l1_unpaired_A_dominant_spin_orbits.py) consumes
the pinned rank-one partition, its 78 receipt inputs, and the B
primitive receipt. Its optional pilot input binds the 256 raw
selector results and emits the exact already-evaluated scalar for
component `(0,3)`. The full replay produced manifest SHA-256
`1600b0e8c87ef548acdd17c057fc483c0e118d29faf775456778fd12ec2d37f5`.
The pilot orbit consists of `(0,3)`, `(1,2)`, and `(2,1)`.
Run the remaining 147 representatives in disjoint batches, using
exact membership and selector receipts before weighting each orbit.
The second direct selector control belongs to the separate orbit
represented by `(0,0)`. Its remaining selectors still require evaluation.

A conditioned shared-Q replay completed both selector-0 controls
across 318 byte-pair keys. All 32 split response maps matched the
two direct maps coefficient by coefficient, and both final exact
scalars agreed. The largest response held 118,272 rows under the
120,000-row cap. The shared route took 38.90 seconds versus 5.50
seconds for direct replay on this workload. Use the direct route
for the next representative batch. The full dominant contraction,
physical transport matching, and B3 remain open.

### Four additional minority representatives

Independent receipt review checked 2,304 distinct ordered leaves per
representative against the pinned roster. It recomputed each exact
coefficient from the raw sum, signed manifest scale and common
divisor. Each receipt had 864 nonzero real leaves, zero imaginary
contribution and no caps.

| Representative | Multiplicity | Exact real coefficient | Raw receipt SHA-256 |
|---:|---:|---:|---|
| 25 | 9 | `3340335969373599/576460752303423488` | `918c2b22d000c170c64304dc9c2d418acedfe02855fc6f9090c31c4f2de64310` |
| 26 | 18 | `3340335969373599/576460752303423488` | `391cededb46b4ca624506e102fd088ff1bd78b141984e8d01f71034a85513ae4` |
| 28 | 9 | `-125576540202015/576460752303423488` | `a1e3aa13765505e87fd593dd662d075110e43471a82a6b77661f429b055c4785` |
| 29 | 9 | `-125576540202015/576460752303423488` | `df21e1f7bf50374df764b0c65fa33a54e305684368f666a200d20f1794370433` |

These four distinct orbits cover 45 pairs and add
`87928693449450903/576460752303423488`. The minority subtotal
is now `159157301674766535/576460752303423488` across 126 of
288 pairs in 16 of 34 orbits, with zero imaginary part. The
other 18 orbits still require representative evaluation.

### Direct selectors for dominant component (0,0)

The [site-10 runner](l1_unpaired_A_site10.py) selects this block-0
component with `--component 0`. Its 12 original words form a
4×1 rank-one component, with weighted center rows of sizes 384
and 144. The runner checks membership, the exact joint product
and the same 256-selector roster used by the pilot. Selector 0
reproduces the earlier direct scalar and its 8,956 products,
4,174 queries and 1,770 nonzero replies.

Independent reduction checked the ordered exact selectors and
raw-to-scaled arithmetic in the following ranges. All imaginary
subtotals vanish.

| Selector range | Exact real subtotal | Receipt SHA-256 |
|---|---:|---|
| [0,8) | `388574307412283223/37778931862957161709568` | `530672f0514ab45196c263a95b29d73e7cb15155ae05d4443b7aa1d38bee22d6` |
| [8,24) | `688672510171296147/37778931862957161709568` | `e742352c15896585bafa8968747cb8dfcffa91860a15c4170211bca468b31a89` |
| [64,80) | `688672510171296147/37778931862957161709568` | `3be4d5dff3b8a9406b90007343b7fd01bb895fbac8e91ef759b22e3412962040` |

The 40 verified selectors contribute
`1765919327754875517/37778931862957161709568` before orbit
weighting. The other selectors must be verified before the
component's multiplicity of three can be applied.

Four subsequent ranges each reduce to
`688672510171296147/37778931862957161709568` with zero imaginary
part. Independent review checked all 16 ordered exact rows in each
range, the pinned membership, joint and roster, and the raw-to-scaled
arithmetic.

| Selector range | Receipt SHA-256 |
|---|---|
| [24,40) | `57d1fb02fc21c5e77a1d3a337f7be296a0faf3d75e14d21c03814fa9ce8c6d5c` |
| [40,56) | `f9d33916b800879788635c18073a363ea76a0db0aa04ca960df6e43af397d8f2` |
| [80,96) | `74f333b24296334d1c4ea7d1cfc54a41aeb91cf8cbed5cfce720e7fc2bd47b68` |
| [96,112) | `0a23fde2fb171d62e4046a2652c7d273ca7599d550defe6a565223a921d3bad1` |

The disjoint union `[0,56) ∪ [64,112)` covers 104 of 256
selectors. Its exact real subtotal is
`4520609368440060105/37778931862957161709568` before orbit
weighting.

The first two gamma slices are now complete. Independent readback
checked every selector in `[0,128)`, including the two terminal
ranges below, against the pinned roster and exact raw reduction.

| Selector range | Exact real subtotal | Receipt SHA-256 |
|---|---:|---|
| [56,64) | `75024550689753231/9444732965739290427392` | `b90ea0f75338664e7a67c648302947c6b103511ba0811586ca940e0c3827fbee` |
| [112,128) | `688672510171296147/37778931862957161709568` | `f71ea6d31709b43dc2a19eb651dfa8a54bb0a64f79c93cf734939d2a9c13b0ba` |

Each complete slice contributes
`688672510171296147/9444732965739290427392`, giving a
direct half-component subtotal of
`688672510171296147/4722366482869645213696` with zero
imaginary part. Evaluate the other two slices directly before
applying the component-orbit multiplicity.

### Minority representatives 30 and 144

Independent review checked all 2,304 ordered exact leaves in each
receipt against its pinned roster and recomputed the signed
coefficients. Each has 864 nonzero leaves and zero imaginary
contribution. The two raw real totals have opposite signs, as
do their manifest scales. Each scaled coefficient is
`-125576540202015/576460752303423488`.

| Representative | Multiplicity | Raw receipt SHA-256 |
|---:|---:|---|
| 30 | 18 | `f69c37a6c920bc75fe0397207abc44734372afe0f9167728884a40e3566d10ca` |
| 144 | 9 | `88011c0d9fd92ccbff2cbcf3641eb4351036542918291dc8b05f9b2055af4fa8` |

These disjoint orbits bring the reviewed subtotal to
`77883367544656065/288230376151711744` across 153 of 288 pairs
in 18 of 34 orbits. Sixteen representative evaluations remain.

### Complete second dominant component and orbit

All four gamma slices of `(0,0)` were evaluated directly.
Independent review reduced the raw rows in 17 terminal receipts,
confirmed unique complete coverage of `[0,256)` against the
pinned roster, and reproduced the exact slice subtotals. Each
slice contributes `688672510171296147/9444732965739290427392`
with zero imaginary part. The compact JSON array of filename
and receipt SHA-256 pairs, sorted by numeric range start, has
SHA-256 `f48e4717aa109a2f3307782b5b2e8713c67ab5c8cdec850a77d064d9c65752fd`.

The direct total is `688672510171296147/2361183241434822606848`.
The independently reconstructed signed orbit consists of
`(0,0)`, `(1,0)` and `(2,0)`, covering 36 unique source words.
Its weighted contribution is
`2066017530513888441/2361183241434822606848`.
The pilot orbit covers 180 words disjoint from these 36. The
combined exact real contribution of these two orbits is
`1600427899831669839/1180591620717411303424`.
The remaining 146 dominant orbits still require their own
representative results. The next direct component `(0,1)`
belongs to a separate six-member orbit.

### Minority representatives 145 and 146

Independent review verified 2,304 ordered exact leaves and 864
nonzero contributions per representative, with zero imaginary
part. Each raw sum reduces with its signed manifest scale to
`-125576540202015/576460752303423488`.

| Representative | Multiplicity | Raw receipt SHA-256 |
|---:|---:|---|
| 145 | 9 | `d6e2b275dd262c336ebe656d764a0d6400a4bd99cdc713219c14a90031abf1e6` |
| 146 | 18 | `44dfeddc832fe650752680e08274397c31e1a26b98b03015979c08291653e21a` |

These distinct orbits bring the reviewed subtotal to
`152376168503857725/576460752303423488` across 180 of 288 pairs
in 20 of 34 orbits. Fourteen representatives remain.

### Minority representative 148

Independent readback verified 2,304 ordered exact leaves on the
pinned roster, with 864 nonzero contributions and zero imaginary
part. The signed manifest scale gives
`3340335969373599/576460752303423488`. The raw receipt SHA-256 is
`b3b14c91699cc2179eea5d021566b63b1c2ff19e2117ff5a2b0d6fcafa735a66`.
The disjoint orbit of nine brings the reviewed minority subtotal
to `45609798057055029/144115188075855872` across 189 of 288 pairs
in 21 of 34 orbits.

### Complete third dominant component and orbit

For `(0,1)`, independent review checked all 256 exact selectors
across 16 terminal ranges. The 12-member source pin is
`00d37e216c5067f53c1e003261060fdb5f902ced30223128f5377cd46063cedf`.
The joint table pin is
`313a62f36772a3063835cff00cb8532c23441351f02cbbae9f910d0459705874`.
The roster matches the previous direct components. Each gamma
slice contributes `688672510171296147/9444732965739290427392`
with zero imaginary part.

| Receipt selector coverage | SHA-256 |
|---|---|
| [0,16) | `7e4f582f17792e0e0453f9221f4cfecbe68951f0cff2999856ade7f144a244f6` |
| [16,128) | `ebed0257d5f6ba0ddb8c01fd98d2a498b9ab0fef0a6e80a2118b00cd5c165285` |
| [128,256) | `68312a5ac7b7df1ff16bf8d4426e203fb7d0f3e5c74c936b9073fd5e63707814` |

The direct total is `688672510171296147/2361183241434822606848`.
The signed orbit consists of `(0,1)`, `(0,2)`, `(1,1)`,
`(1,3)`, `(2,2)`, and `(2,3)`. The 72 source words are
disjoint from the 216 words of the two previous orbits. The
weighted contribution is
`2066017530513888441/1180591620717411303424`.
Three of 148 dominant orbits now have full direct results.

### Minority representatives 149 and 150

Independent review verified both pinned rosters of 2,304 distinct
ordered leaves. Each has 864 nonzero contributions, zero imaginary
part, and exact signed coefficient
`3340335969373599/576460752303423488`.

| Representative | Multiplicity | Raw receipt SHA-256 |
|---:|---:|---|
| 149 | 9 | `2868d615fda716880c26802030f286f816d7b8d2a60143c75f5a72b7b6738fce` |
| 150 | 18 | `8d1d22ac04f4e25bbdd288722136eb13085a5b0b098bbacef6f845f96c396e15` |

The two disjoint orbits bring the verified subtotal to
`272628263401307289/576460752303423488` across 216 of 288 pairs
in 23 of 34 orbits.

### Minority representative 168

Independent review matched all 2,304 ordered exact leaves to the
pinned roster and recomputed the signed coefficient
`-871859979116847/144115188075855872`, with 864 nonzero leaves
and zero imaginary part. Raw receipt SHA-256 is
`5c578dbf21d242419043b3c6af6d4d15cf672a04656f8519f6fde455fa88810a`.
Its disjoint three-member orbit brings the reviewed subtotal to
`262165943651905125/576460752303423488` across 219 of 288 pairs
in 24 of 34 orbits.

### Minority representatives 169 and 173

Independent review checked the signed scales and the complete
ordered rosters. Each representative has 2,304 exact leaves,
864 nonzero contributions and zero imaginary part.

| Representative | Multiplicity | Exact real coefficient | Raw receipt SHA-256 |
|---:|---:|---|---|
| 169 | 9 | `-871859979116847/144115188075855872` | `6b180fa2b7ad100a7ecce7fd3bf03d10af36a3bab20f04a99b3a6bb816c38406` |
| 173 | 3 | `454108196543967/4611686018427387904` | `7e0616a166a3175330bfc31124cf80a8e963b5421aaa53d923af09e7a1459020` |

The two disjoint orbits bring the reviewed subtotal to
`1847594199819220965/4611686018427387904` across 231 of 288 pairs
in 26 of 34 orbits.

### Minority representatives 172 and 176

Independent review matched each pinned roster of 2,304 ordered
exact leaves and verified both signed scales. Each has 864
nonzero contributions and zero imaginary part.

| Representative | Multiplicity | Exact real coefficient | Raw receipt SHA-256 |
|---:|---:|---|---|
| 172 | 3 | `427098043589679/4611686018427387904` | `f66d30053b684bbb093101fcedc532d3184438aeb2de3bc67dd4e393a79b5bdf` |
| 176 | 6 | `871859979116847/144115188075855872` | `087d9596b67d9a932848825632728a25b8e58c08f6ddaa5a62c300cb9ef7bf36` |

Their disjoint orbits bring the reviewed subtotal to
`1008136304970212313/2305843009213693952` across 240 of 288 pairs
in 28 of 34 orbits.

### Complete fourth dominant component and orbit

The shared-preparation runner evaluated all 256 selectors of
`(0,4)` directly in 16 terminal shards. Independent review
checked the ordered selector tuples against the pinned roster,
reduced the exact raw coefficients, and verified the absence
of unresolved selectors or cap exits. The full receipt SHA-256
is `f5c592b644d38a86e975c691047f30aae4b03b111517811e3b3681c5d0f9a13e`.

Each gamma slice contributes
`688672510171296147/37778931862957161709568`. The complete
component gives `688672510171296147/9444732965739290427392`
with zero imaginary part. Its nine-member orbit contributes
`6198052591541665323/9444732965739290427392` across 27 signed
source words. Independent reconstruction found the words
disjoint from the 288 words covered by the first three orbits.
Four of 148 dominant orbits now have complete results.

### Minority representatives 174, 177, 180 and 182

Independent review checked all four pinned rosters and their
signed manifest scales. Each has 2,304 ordered exact leaves,
864 nonzero contributions and zero imaginary part.

| Representative | Multiplicity | Exact real coefficient | Raw receipt SHA-256 |
|---:|---:|---|---|
| 174 | 6 | `470989542140397/4611686018427387904` | `c815b2819e205a1b5bb4eba6385520c309f597a74b2ff9c2f69eca766ed3761a` |
| 177 | 18 | `871859979116847/144115188075855872` | `467794d93dcf1fc9156ab2dd39785530b42733c416f588e8720c0cd3b1f38d2b` |
| 180 | 6 | `-207640550836089/2305843009213693952` | `27bd5ff7cbba3d71d30edd2710cc996fe048697ceb0973107249a8140fb19c27` |
| 182 | 6 | `-231274434671091/2305843009213693952` | `b84a43ed196e1e031e80af5501826cfeadf79a2ed5e0a2713df6b424a8c772a7` |

The repository orbit verifier replayed the terminal receipts and
reproduced the reviewed subtotal
`157251432208655295/288230376151711744` over 276 of 288 pairs
in 32 of 34 orbits. The remaining representatives are 181 and 183.

### Dominant orbit covered by the existing two-word replay

The prior direct replay of indices 4,776 and 17,672 exhausts
component `(65,13)`. Independent review matched both signed
scales and all 1,152 exact ordered leaves to the pinned inputs,
then recovered the direct subtotal
`-274396016602155609/4722366482869645213696` with zero imaginary
part. The full direct receipt SHA-256 is
`549235ff9768e6afd2f2ccd7a3ee5c8bb9910b2558c06731a3a72591f7332a86`.

Component `(65,13)` belongs to the orbit represented by `(20,8)`.
All 36 component images preserve the signed contraction. Their
72 source words are disjoint from the 315 words in the four
accepted block-0 orbits. The weighted contribution is
`-2469564149419400481/1180591620717411303424`, bringing the
reviewed dominant subtotal to
`15773102838950927715/9444732965739290427392` across 387 source
words in five of 148 orbits. This subtotal includes the direct
pair once through its orbit weight.

### Complete minority contraction

Independent review verified the final two exact receipts and
reduced all 34 orbit contributions over 288 distinct pair IDs
and 576 source words. Each final receipt has 2,304 exact leaves,
864 nonzero contributions, and zero imaginary part.

| Representative | Multiplicity | Exact real coefficient | Raw receipt SHA-256 |
|---:|---:|---|---|
| 181 | 6 | `-231274434671091/2305843009213693952` | `1c088eef984304745a5461a0de8bb8fe78a934034ec0b5edd47fa85eb5d047c7` |
| 183 | 6 | `-241403242028949/2305843009213693952` | `c81fbc86776eed24a78c45cb5e5ab37a758770c69cfd662a66050173a8925757` |

The complete real minority subtotal is
`156896923951130265/288230376151711744`. The repository orbit
verifier reproduced full coverage and the same subtotal. Its
complete manifest SHA-256 is
`500c8d667a31b454a0bdec5857f99cbad4f0ff64b27f692f76d6dadaa6fa71ac`.
The pinned minority and dominant word sets are disjoint and
together cover all 9,792 nonempty B occurrences. The remaining
143 dominant orbits still require representative results.

### Manifest-pinned direct representative replay

The [site-10 runner](l1_unpaired_A_site10.py) accepts repeatable
`--representative BLOCK COMPONENT` selections together with
the pinned component and orbit manifests. It regenerates the
signed tables and word membership, uses one immutable factor
preparation, and checks the preparation digest after each
representative. A full `0 256` replay runs 16 bounded shards.
The original component-0 and component-3 entry points retain
their slice guards.

Independent review matched both exact selector-0 controls for
`(0,4)` and `(0,8)` to their direct receipts. The combined
control SHA-256 is
`7bb1f56b8943632e0398836a1736a6c6b0ba5569ad72be3387e2cdca545a2b60`.
Each matched the raw Gaussian scalar, 8,956 products,
4,174 queries, and 1,746 nonzero replies.

The runner requires the existing ordered roster digest.
The block-20 probe independently regenerated 256 selectors
but yielded a different roster, with SHA-256
`ab0c93745e811a0ff1620599953c5d3daa874b6c43e8937e6b385df11ec6e9f1`.
Its full replay is a separate qualification against the known
two-word orbit subtotal. A guarded left-transfer cache trial
for four block-0 selectors matched exact values and reduced
left contractions from 72 to 18. Total selector wall time
changed from 11.12 to 10.95 seconds, so the replay continues
to use the original cache scope.

### Complete dominant representative (0,8)

Independent review reconstructed the exact ordered roster from
all 256 directly evaluated selectors in 16 terminal shards.
No caps were hit. Each gamma slice contributes
`688672510171296147/37778931862957161709568`, for a complete
direct subtotal of `688672510171296147/9444732965739290427392`
with zero imaginary part. The receipt SHA-256 is
`04a49ea23c5604e21eeda9830bc04ffa10a1a4006efc46ca03440720587a2211`.

The verified 18-member orbit covers 54 signed source words,
all disjoint from the 387 already accepted. Its contribution is
`6198052591541665323/4722366482869645213696`. Six of 148
dominant orbits now have complete results, covering 441 words.

### Complete dominant representative (0,7)

Independent review checked all 256 ordered exact selectors and
16 terminal shards against the pinned roster. No caps were hit.
The raw-to-scaled reduction gives
`4055515893230966199/9444732965739290427392` with zero imaginary
part. The complete receipt SHA-256 is
`c74d5320fbb7eabe43f02fbd9af49eee7d2ec92de32dbe4bbd65ebc9c7e2de1f`.

The signed orbit consists of `(0,7)`, `(1,11)`, and `(2,15)`.
Its weighted contribution is
`12166547679692898597/9444732965739290427392`. Its 45 source words
are disjoint from all six previous orbits. Complete dominant
coverage is now seven of 148 orbits and 486 source words.

### Complete dominant representatives (0,11) and (0,16)

Independent review reconstructed both pinned rosters from all
256 ordered exact selectors per component and verified each set
of 16 terminal shards. Both raw-to-scaled reductions have zero
imaginary part and no caps.

| Representative | Multiplicity | Exact real subtotal before weighting | Receipt SHA-256 |
|---|---:|---|---|
| (0,11) | 6 | `4055515893230966199/9444732965739290427392` | `cc921a9665c2ce2f537ff650b0d7482e313799e2a66199caa324b0e9487ccd15` |
| (0,16) | 9 | `688672510171296147/9444732965739290427392` | `bb846389fefce4a3c6a06931295e82944c8a7468abfb1f33b8ab3120ed94e02d` |

Their 90 and 27 signed source words are mutually disjoint and
disjoint from all seven previously accepted orbits. The verified
dominant coverage is now nine of 148 orbits and 603 source words.

### Two pinned rosters for the dominant representatives

An independently reviewed census regenerated all 148 representative
rosters in one immutable preparation. Each has four gamma slices
of 64 selectors. The original roster covers 108 representatives,
1,600 components and 6,144 signed source words. Blocks 16, 19, 20,
and 23 use the second roster, covering 40 representatives,
480 components and 3,072 signed source words. The census receipt
SHA-256 is
`1e0f21c8c1e0656bfcb21dd5e0b25e967f0a698f43b110feb241be223892d042`.

The direct replay of `(20,8)` completed all 256 selectors under
the second roster and recovered
`-274396016602155609/4722366482869645213696` with zero imaginary
part. This equals the independently accepted two-word subtotal
from component `(65,13)` in the same orbit. The cross-check adds
no duplicate contribution. The full receipt SHA-256 is
`930d217f73c945f4217fdd4ca81366c50cc7be9d2631cdf39ca3514c9c207ff7`.

The repository runner selects the expected digest from the pinned
representative's block and checks the exact regenerated roster
before emitting results. One shared preparation tested selector 0
from `(8,9)` on the original roster and `(20,8)` on the second.
The control SHA-256 is
`c5bea6490c54581c1fa8fe8bfb535f26c2ebf30727e85ec6a6c8efb3c4622d0d`.

### Complete dominant representative (0,19)

The repository runner produced all 256 exact ordered selectors
and 16 terminal shards without a cap. Independent review
checked the roster, raw reduction and terminal representative pin.
The direct total is `4055515893230966199/9444732965739290427392`
with zero imaginary part. The receipt SHA-256 is
`0a8a3f3789f6f7c95cc1a29d157937c2e10bac0214882ec136f4cb2fa5a8f756`.

The verified signed orbit `{(0,19),(1,19),(2,19)}` contributes
`12166547679692898597/9444732965739290427392` and adds 45
distinct source words. The nine block-0 representatives are
complete. Including the separately accepted `(20,8)` orbit,
coverage is ten of 148 dominant orbits and 648 source words.

### Signed stabilizers for complete gamma slices

A simultaneous proper signed rotation of both chiral blocks acts
on the three spatial Clifford components by its signed permutation
and fixes the fourth. It preserves the dominant B primitive,
Haar measure, identity tree links, closed oriented traces, and
the Berezin top form. The fixed target label `gkey(1,1)` has
one singleton Clifford index on each of two factors, the center
and its coframe edge. The same sign appears on both legs and
their product is positive. All other Clifford labels and exterior
generators are summed in the full slice.

For a representative, keep only the diagonal rotations that
map its entire weighted word set bijectively to itself with
the exact induced probe sign on each scale. The scale and probe
signs then cancel term by term. A rotation of this signed
stabilizer can equate two complete gamma-slice contractions.
It supplies no equality between individual selector rows.
The fixed fourth component is a singleton slice.

Independent review verified the rotation `(2,-1,3)` for
`(0,4)`, `(0,7)`, `(0,16)`, and `(0,19)`. It exchanges
gamma slices 0 and 1, which also agree in each complete direct
receipt. The census of all canonical representatives found 92
with four distinct slices, 52 with three, and four with two,
so guarded replay can evaluate 532 of the 592 slices. The
census source SHA-256 is
`a1772986235d544df23e0609d2edfe23690afedf2ade9f6e14eeadec2c3acfd7`.
A replay must record a signed stabilizer witness and a complete
direct subtotal for each retained slice before weighting it.

### Complete dominant representatives (8,9) and (9,8)

Independent review checked all 256 exact ordered selectors per
representative, each set of 16 terminal shards, and the raw-to-scaled
arithmetic. No caps were hit. Both directly evaluated subtotals are
`-742478726025364419/9444732965739290427392` with zero imaginary part.

| Representative | Multiplicity | Receipt SHA-256 |
|---|---:|---|
| (8,9) | 36 | `27e1838fe5bb0e3106256088f4e20e32e22233f3729b0f7ba1ce15209adc4824` |
| (9,8) | 36 | `d09b7ba679663aa7bdf9fda4d2a11cb23baab328b42ef68d461b6fa330b5fb45` |

The two signed orbits are disjoint from each other and all ten
previous orbits. Their combined contribution is
`-6682308534228279771/1180591620717411303424`, bringing complete
dominant coverage to 12 of 148 orbits and 720 source words.

### Complete dominant representative (16,0)

The repository runner completed the first new orbit under the
second pinned roster. Independent review checked all 256 ordered
exact selectors and 16 terminal shards, with no caps. The direct
subtotal is `-274396016602155609/1180591620717411303424` with zero
imaginary part. The receipt from the component marker through its
terminal marker has SHA-256
`deb076a9a8b3ede047c92f215824fc0d28519e8f0795a36c56d1c3402f30c206`.

Its nine-member orbit contributes
`-2469564149419400481/1180591620717411303424`. The 72 signed source
words are disjoint from all 720 previously accepted words. Complete
dominant coverage is now 13 of 148 orbits and 792 source words.

### Complete dominant representatives (9,9) and (9,11)

Independent review verified 256 ordered exact selectors and 16
terminal shards per representative, with no caps and zero imaginary
part. Each direct subtotal is
`-742478726025364419/9444732965739290427392`.

| Representative | Multiplicity | Receipt SHA-256 |
|---|---:|---|
| (9,9) | 36 | `7528c08d7c621ca912223d2e483b4f8995968eadda5af3bec4de3d4e8c03c36a` |
| (9,11) | 36 | `7bd6d69f82c179b92fe9bcb32457bed259add45cbf109ea6347939f0216aa4e9` |

The disjoint signed orbits add 72 words and contribute
`-6682308534228279771/1180591620717411303424`. Verified dominant
coverage is now 15 of 148 orbits and 864 source words.

### Verified symmetry replay control

The repository runner's opt-in `--gamma-symmetry` mode uses
exact signed stabilizers for manifest-pinned full replays. It
emits distinct direct and weighted raw totals, one exact class
receipt per complete slice, and the signed rotation witnesses.
A failed shard prevents the class and representative terminals.

For `(0,4)` the control ran 192 direct selectors in gamma slices
0, 2 and 3. Independent review matched each raw row and its
counters to the full direct receipt, reconstructed all three
class witnesses, and checked the weighted raw sum against
all 256 direct selectors. The exact total was
`688672510171296147/9444732965739290427392` with zero imaginary
part. The symmetry control SHA-256 is
`fda20159fe194c05d00616f9f50304d3af5d0b74547a2137dcb8d2f778e09bc9`.
This validates the reduced route on the control without adding
a duplicate orbit contribution.

### Complete dominant representative (16,1)

Independent review checked all 256 ordered exact selectors
and 16 terminal shards on the second pinned roster. No caps
were hit. The direct subtotal is
`-274396016602155609/1180591620717411303424` with zero imaginary
part. The component receipt through its terminal marker has
SHA-256 `0a105c7866c5cfcec9ce340f5706e5094765cb3d543dfcb8cb77053124c34706`.

The verified 18-member orbit contributes
`-2469564149419400481/590295810358705651712`. It adds 144
signed source words disjoint from the 864 previously accepted.
Complete coverage is now 16 of 148 dominant orbits and 1,008 words.

### First new orbit accepted using gamma-slice symmetry

The repository runner directly evaluated 128 selectors for `(3,0)`
in gamma slices 0 and 3. Independent review checked eight terminal
shards and regenerated the signed word maps. The three-member
slice class covers gamma 0, 1, and 2 from slice 0. Gamma 3 is
a singleton. Both direct slices have exact real subtotal
`378279423049817079/9444732965739290427392`. The weighted component
total is `378279423049817079/2361183241434822606848`, with zero
imaginary part. The component receipt SHA-256 is
`30fdd487411c15f31e6700e2cb96d9bbc46906aa16afa1e7b59a9814c126ace9`.

The component's dominant orbit has multiplicity one and contains
60 source words disjoint from the 1,008 previously accepted.
Complete coverage is now 17 of 148 dominant orbits and 1,068 words.

### Complete dominant representatives (7,4) and (7,19)

Independent review checked 128 ordered exact selectors and eight
terminal shards per representative on the original pinned roster.
Each uses direct slices 0 and 3. The signed proper rotations map
slice 0 to slices 1 and 2 and leave slice 3 as a singleton class.
The reviewed weighted results have zero imaginary part. Both
dominant orbits are singletons.

| Representative | Source words | Exact contribution | Receipt byte interval | Receipt SHA-256 |
|---|---:|---|---|---|
| [(7,4)](l1_gamma_7_4.out.txt) | 60 | `378279423049817079/2361183241434822606848` | [1317, 47370) | `fe0c3fe6d3c18a5fac3c23fdac5cca7634eaab0b726c56cf5fd466e5c2c14269` |
| [(7,19)](l1_gamma_7_19.out.txt) | 15 | `4055515893230966199/9444732965739290427392` | [1319, 47432) | `534f14cfe32f65a449354d5345b239b24c9cfc287f066d889b1d9202bac92b70` |

The 75 signed source words are disjoint from each other and the
1,068 previously accepted words. Verified dominant coverage is
19 of 148 orbits and 1,143 of 9,216 words.

### Complete dominant representative (3,4)

Independent review verified 192 ordered exact selectors in gamma
slices 0, 2, and 3 on the original pinned roster. It checked all
12 terminal shards and regenerated the signed witness
`(-2,-1,-3)` mapping slice 0 to slice 1. The exact weighted
component subtotal is `688672510171296147/9444732965739290427392`
with zero imaginary part. The component receipt byte interval
is [47367, 115753) in the [shared block 3 run](l1_gamma_block3.out.txt). Its SHA-256 is
`c66a5fbd2889295f6a1b71e6a353334e61d7feac954c286859c4a7beca4743e4`.

The nine-member signed orbit adds 27 source words disjoint from
the previously accepted 1,143. Its contribution is
`6198052591541665323/9444732965739290427392`. Verified dominant
coverage is 20 of 148 orbits and 1,170 of 9,216 words.

### Complete dominant representatives (13,1) and (16,8)

Independent review verified 256 ordered exact selectors and 16
terminal shards per representative. All four gamma classes were
singletons in each run. The reviewer checked the distinct pinned
rosters, class hashes, exact scaling, zero imaginary parts, and
absence of caps.

| Representative | Words | Direct subtotal | Orbit multiplicity | Full receipt SHA-256 |
|---|---:|---|---:|---|
| [(13,1)](l1_gamma_13_1.out.txt) | 144 | `-58583762512121259/2361183241434822606848` | 36 | `617d7da02c8e6c1cfc0a43a7167e9c7881a92116f69444d61ca71c1bb626e96d` |
| [(16,8)](l1_gamma_16_8.out.txt) | 72 | `-274396016602155609/4722366482869645213696` | 36 | `d34b733d247ffe42acf3dad4b0436ec5c7f6af4898f252c3031441a07802df4f` |

The signed maps prove disjointness from each other and the 1,170
previously accepted words. The two orbits contribute
`-3524071874637583143/1180591620717411303424` together.
Verified dominant coverage is 22 of 148 orbits and 1,386 of
9,216 words.

### Global chirality exchange pairs the dominant orbits

Independent scientific review accepted a second exact symmetry
for the full dominant contraction. Conjugation by `γ₃` exchanges
the two chiral spin blocks. On the seven probe coordinates it
acts by `x XOR 4`. On the exterior algebra it sends each local
generator index `i` to `i XOR 2`, with the wedge permutation sign.
It preserves the Berezin top form, identity tree links and
normalized product Haar measure. The closed curvature vertices
each acquire one sign from `γ₅`, which cancel across the fourteen
retained vertices. Signs on the matched internal Dirac legs
occur twice. The cut projection commutes with the chiral block
exchange, and the frozen auxiliary unit remains fixed.

The [exact control](l1_chirality_swap_control.py) checks all 208
primitive B rows, the seven A center tables, 128 directed
coframes, and 495 frame Haar monomials through degree four.
The pinned signed source maps verify coefficientwise equality
for all 9,216 words under the swap. It pairs all 2,080 components
and descends to 74 pairs of distinct Spin orbits. The two
members of each pair have equal whole contraction and equal
orbit multiplicity. This identity applies at the level of
whole contractions.

Of the 22 directly evaluated orbits, four already belong to
two completed pairs, `(3,0)/(7,4)` and `(16,8)/(20,8)`.
Independent review verified that the other 18 counterparts
add 1,122 disjoint source words. Verified dominant coverage is
therefore 40 of 148 orbits and 2,508 of 9,216 words. The remaining
108 orbits require one exact representative per pair, with
separate signed membership and multiplicity accounting.

| Direct representative | Added counterpart | Orbit multiplicity | Added words |
|---|---|---:|---:|
| (0,0) | (4,4) | 3 | 36 |
| (0,3) | (4,7) | 3 | 180 |
| (0,1) | (4,5) | 6 | 72 |
| (0,4) | (4,0) | 9 | 27 |
| (0,8) | (4,8) | 18 | 54 |
| (0,7) | (4,3) | 3 | 45 |
| (0,11) | (4,11) | 6 | 90 |
| (0,16) | (4,16) | 9 | 27 |
| (0,19) | (4,19) | 3 | 45 |
| (8,9) | (12,9) | 36 | 36 |
| (9,8) | (13,8) | 36 | 36 |
| (16,0) | (20,4) | 9 | 72 |
| (9,9) | (13,9) | 36 | 36 |
| (9,11) | (13,11) | 36 | 36 |
| (16,1) | (20,5) | 18 | 144 |
| (7,19) | (3,19) | 1 | 15 |
| (3,4) | (7,0) | 9 | 27 |
| (13,1) | (9,5) | 36 | 144 |

The exact added subtotal is
`-30789502461494097867/4722366482869645213696`.
The aggregate dominant subtotal over the 40 accepted orbits is
`-39911200213072065633/2361183241434822606848`, with zero
imaginary part.

### Complete chirality pairs (9,7)/(13,3) and (16,3)/(20,7)

Independent review checked all 256 direct selectors and 16
terminal shards in each direct run, using the appropriate pinned
roster. All gamma classes were singletons. Exact scaling and
signed witnesses matched, with zero imaginary parts and no caps.

| Direct representative | Chirality counterpart | Words per orbit | Direct subtotal | Multiplicity | Full receipt SHA-256 |
|---|---|---:|---|---:|---|
| [(9,7)](l1_gamma_9_7.out.txt) | (13,3) | 360 | `-557561034463996143/2361183241434822606848` | 18 | `d6dfef8762368e766d1efa8abccbd306a2984eb5d34f16adebc7780ebef019c2` |
| [(16,3)](l1_gamma_16_3.out.txt) | (20,7) | 360 | `-744421773825188613/1180591620717411303424` | 9 | `cf56371c521098e42188beb017297f8df2568b2a918b7faa74d4b065343c7fad` |

The exact whole-member maps establish both chirality counterparts
and disjointness among the four orbits and from prior coverage.
The four add 1,440 words and contribute
`-2929461318650665701/147573952589676412928`.
Verified dominant coverage is 44 of 148 orbits and 3,948 of
9,216 words.

### Direct replay controls for chirality exchange

Two independently reviewed controls match previously accepted
whole-component totals exactly, with zero imaginary part and
no caps. Both counterpart orbits were already counted.

| Control | Comparison | Direct selectors | Whole-component subtotal | Full receipt SHA-256 |
|---|---|---:|---|---|
| [(13,3)](l1_gamma_13_3.out.txt) | (9,7) | 256 | `-557561034463996143/2361183241434822606848` | `8cd8ef016a0ff9035f93d6b7794ae339da056a78f7590f556da06dafec163b09` |
| [(4,7)](l1_gamma_4_7.out.txt) | (0,3) | 192 | `378279423049817079/2361183241434822606848` | `3687be647901af88a5c4abbf838243aee7ea46a96891faefed43163d1b856820` |

The second control uses the proper signed witness from gamma
slice 0 to slice 1, with slices 2 and 3 evaluated directly.

The [(20,7) control](l1_gamma_20_7.out.txt) tests the second
pinned roster. Independent review checked 256 ordered direct
selectors, 16 terminal shards, four singleton witnesses, and
exact raw equality to (16,3). The whole-component subtotal is
`-744421773825188613/1180591620717411303424` with zero imaginary
part and no caps. The full receipt SHA-256 is
`d4cbcf5120e2ca1b57f134662cf3420940196e715d9749b54aeb3759410f5c1c`.
The orbit was already counted.

### Complete chirality pairs (8,7)/(12,3) and (11,7)/(15,3)

Independent review checked 192 ordered direct selectors and
12 terminal shards in each run. A proper signed witness supplies
gamma slice 1 from slice 0. Slices 2 and 3 were evaluated directly.
Each whole component has exact subtotal
`-557561034463996143/2361183241434822606848`, with zero imaginary
part and no caps.

| Direct representative | Chirality counterpart | Words per orbit | Orbit multiplicity | Full receipt SHA-256 |
|---|---|---:|---:|---|
| [(8,7)](l1_gamma_8_7.out.txt) | (12,3) | 180 | 9 | `42d2ca00ae35991bb205015365de820edb5150ee85c8c051587ef84dd82aa952` |
| [(11,7)](l1_gamma_11_7.out.txt) | (15,3) | 180 | 9 | `3daeb080f3da129d11cf373f19ff96bcc05115db0d380aa051c875bd02709e12` |

All four signed orbits are disjoint from each other and prior
coverage. They add 720 words with combined contribution
`-5018049310175965287/590295810358705651712`.
Verified dominant coverage is 48 of 148 orbits and 4,668 of
9,216 words.

### Complete chirality pairs for (9,10), (16,10), and (19,0)

Independent review checked 256 ordered direct selectors and
16 terminal shards in each of the first two runs. For (19,0)
it checked 192 direct selectors and 12 shards. The proper
signed witness `(-1,-3,-2)` maps gamma slice 1 to slice 2.
The distinct pinned rosters, exact scales, and signed
witnesses match. All three imaginary parts vanish and no caps
were hit.

| Direct representative | Chirality counterpart | Words per orbit | Direct subtotal | Multiplicity | Full receipt SHA-256 |
|---|---|---:|---|---:|---|
| [(9,10)](l1_gamma_9_10.out.txt) | (13,10) | 180 | `-1545409315094236263/9444732965739290427392` | 36 | `4aa2a6c9abf7f3a05b9ced460605f0ce638dd5572ec7deb8f8723af69100b452` |
| [(16,10)](l1_gamma_16_10.out.txt) | (20,10) | 180 | `-1297036003818215493/4722366482869645213696` | 18 | `00d5cd351fcd3c24545034d2ab3b45882e12e8e3d2b2c0dbe10f60dad3ebfdb0` |
| [(19,0)](l1_gamma_19_0.out.txt) | (23,4) | 120 | `-744421773825188613/1180591620717411303424` | 3 | `081e1c8de8f29ce054b5e02e01ebd68329776ca585d664059be6443215d74949` |

The six signed orbits are mutually disjoint and disjoint from
the prior 48. They add 960 source words. Verified dominant
coverage is 54 of 148 orbits and 5,628 of 9,216 words.

### Complete chirality pair (19,1)/(23,5)

Independent review checked 192 ordered direct selectors in
gamma slices 0, 1 and 3, with 12 terminal shards on the second
pinned roster. The proper signed witness `(-1,-3,-2)` maps
slice 1 to slice 2. Exact scaling gives the whole-component
subtotal `-274396016602155609/1180591620717411303424`, with zero
imaginary part and no caps. The [full receipt](l1_gamma_19_1.out.txt)
has SHA-256 `12eef921bdceb67a6eb53219ed250c35e1a84c1632d6a8ec558b006486abc95c`.

Each signed orbit contains 72 words with multiplicity nine.
The two are disjoint from each other and all prior coverage.
They add 144 words and contribute
`-2469564149419400481/590295810358705651712` together.
Verified dominant coverage is 56 of 148 orbits and 5,772 of
9,216 words.

### Complete chirality pair (8,11)/(12,11)

Independent review checked 256 ordered direct selectors and 16
terminal shards on the original pinned roster. All four class
witnesses are singletons. The exact subtotal is
`-1545409315094236263/9444732965739290427392`, with zero imaginary
part and no caps. The [full receipt](l1_gamma_8_11.out.txt) has
SHA-256 `6bb33d6ff28eb0c2c7c53771218d20c0450b3ab54cc65269984dc76bb0912e83`.

Each signed orbit contains 90 words with multiplicity 18. The
two orbits are mutually disjoint and disjoint from prior coverage.
Together they contribute `-13908683835848126367/2361183241434822606848`
and add 180 words. Verified dominant coverage is 58 of 148
orbits and 5,952 of 9,216 words.

### Complete chirality pairs for (9,2), (9,18), and (11,8)

Independent review checked 256 ordered direct selectors and 16
terminal shards in each run on the original pinned roster.
All four class witnesses per run are singletons. Each exact
component subtotal is `-1545409315094236263/9444732965739290427392`,
with zero imaginary part and no caps.

| Direct representative | Chirality counterpart | Words per orbit | Multiplicity | Full receipt SHA-256 |
|---|---|---:|---:|---|
| [(9,2)](l1_gamma_9_2.out.txt) | (13,6) | 90 | 18 | `dcebafb398b6ee4eb73e0b9f7a8da99216317888e6ba83dd580d30ffe698e3b6` |
| [(9,18)](l1_gamma_9_18.out.txt) | (13,18) | 90 | 18 | `800d93a4204cec683e9f5571793755831196d12cea1990c950d2c9c47d628db2` |
| [(11,8)](l1_gamma_11_8.out.txt) | (15,8) | 90 | 18 | `fcdd441f07134e7c50fb75508caf121ec6ebb58007fef325ba711879d04f1d8b` |

The six signed orbits add 540 disjoint words and contribute
`-41726051507544379101/2361183241434822606848` together.
Verified dominant coverage is 64 of 148 orbits and 6,492 of
9,216 words.

### Complete chirality pair (16,6)/(20,2)

Independent review checked 256 ordered direct selectors, 16
terminal shards and four singleton witnesses on the second pinned
roster. Exact scaling gives `-1297036003818215493/4722366482869645213696`
with zero imaginary part and no caps. The [full receipt](l1_gamma_16_6.out.txt)
has SHA-256 `4fcdbb4a88ccfa514e853363c2faadaa1d0eb5163277a382449df29749b7431f`.

Each signed orbit contains 90 words with multiplicity nine.
They are mutually disjoint and disjoint from prior coverage.
The pair adds 180 words and contributes
`-11673324034363939437/2361183241434822606848`.
Verified dominant coverage is 66 of 148 orbits and 6,672 of
9,216 words.

### Complete chirality pair (16,18)/(20,18)

Independent review checked 256 ordered direct selectors, 16
terminal shards and four singleton witnesses on the second pinned
roster. The exact component subtotal is
`-1297036003818215493/4722366482869645213696` with zero imaginary
part and no caps. The [full receipt](l1_gamma_16_18.out.txt) has
SHA-256 `572cf3f06afa0caa4a78f748695e0bd8c013e72ff27f3d91800eb2f7b0a746c2`.

Each signed orbit contains 90 words with multiplicity nine.
The pair adds 180 disjoint words and contributes
`-11673324034363939437/2361183241434822606848`.
Verified dominant coverage is 68 of 148 orbits and 6,852 of
9,216 words.

### Complete chirality pairs for (19,6), (8,5), and (9,4)

Independent review verified 256 ordered direct selectors, 16
terminal shards, four singleton class witnesses and exact scaling
in each run. All imaginary parts vanish and no caps were hit.

| Direct representative | Chirality counterpart | Words per orbit | Direct subtotal | Multiplicity | Full receipt SHA-256 |
|---|---|---:|---|---:|---|
| [(19,6)](l1_gamma_19_6.out.txt) | (23,2) | 90 | `-1297036003818215493/4722366482869645213696` | 9 | `6b380215100b5644c9ef21914228fce43f740426256e3df006c009da6c3da93c` |
| [(8,5)](l1_gamma_8_5.out.txt) | (12,1) | 72 | `-58583762512121259/2361183241434822606848` | 18 | `b5a0dd52f6761f9d9cca1302c5e608bd052dabce0011ef305e54026e466e4ac6` |
| [(9,4)](l1_gamma_9_4.out.txt) | (13,0) | 72 | `-58583762512121259/2361183241434822606848` | 18 | `ed278cbf5a2ad4ac19a6ad026d406c989d9abb569653b1fc9b0e3cae430b40ba` |

The six signed orbits add 468 disjoint words. Verified dominant
coverage is 74 of 148 orbits and 7,320 of 9,216 words.

### Complete chirality pairs (11,5)/(15,1) and (3,7)/(7,3)

Independent review checked all 256 ordered direct selectors and
16 terminal shards for (11,5). It checked 192 direct selectors and
12 shards for (3,7), where the proper signed rotation
`(-2,-1,-3)` maps gamma slice 0 to slice 1. Both runs used the
original pinned roster, with exact scaling, zero imaginary
parts and no caps.

| Direct representative | Chirality counterpart | Words per orbit | Direct subtotal | Multiplicity | Full receipt SHA-256 |
|---|---|---:|---|---:|---|
| [(11,5)](l1_gamma_11_5.out.txt) | (15,1) | 72 | `-58583762512121259/2361183241434822606848` | 18 | `aeb9688e922801cb73fe94727d191ce83aa9a843c4742dd350d6f1b0e77d9852` |
| [(3,7)](l1_gamma_3_7.out.txt) | (7,3) | 45 | `4055515893230966199/9444732965739290427392` | 3 | `295347f5d70840849728201815b171877caa6787a8609efc6164b88b9992000f` |

The four signed orbits are disjoint from each other and prior
coverage. They add 234 source words. Verified dominant coverage
is 78 of 148 orbits and 7,554 of 9,216 words.

### Complete chirality pairs for (8,3), (8,19), and (11,0)

Independent review verified 192 ordered direct selectors and
12 terminal shards in each run on the original pinned roster.
The proper signed witness `(-2,-1,-3)` maps gamma slice 0 to 1.
Each exact whole-component subtotal is
`-1545409315094236263/9444732965739290427392`, with zero imaginary
part and no caps.

| Direct representative | Chirality counterpart | Words per orbit | Multiplicity | Full receipt SHA-256 |
|---|---|---:|---:|---|
| [(8,3)](l1_gamma_8_3.out.txt) | (12,7) | 45 | 9 | `99d6414c5877ee24e75776ce82ad0f3fc08c8f4603f5a06ea7ce62a7bbb4531a` |
| [(8,19)](l1_gamma_8_19.out.txt) | (12,19) | 45 | 9 | `5cb0f1d3a214ba8bc61dc206b1745b6a83a86745257921cc6ecd3661b20d4133` |
| [(11,0)](l1_gamma_11_0.out.txt) | (15,4) | 45 | 9 | `124c8b21a578944647430506579a2b068deffec289491a844a892324b4244726` |

The six signed orbits add 270 disjoint words and contribute
`-41726051507544379101/4722366482869645213696` together.
Verified dominant coverage is 84 of 148 orbits and 7,824 of
9,216 words.

### Complete chirality pairs (11,16)/(15,16) and (3,1)/(7,5)

Independent review checked 192 ordered direct selectors and
12 terminal shards per run on the original pinned roster.
For (11,16) a signed witness maps gamma slice 0 to 1.
For (3,1) a signed witness maps slice 1 to 2. Exact scaling
and signed witnesses match, with zero imaginary parts and no caps.

| Direct representative | Chirality counterpart | Words per orbit | Direct subtotal | Multiplicity | Full receipt SHA-256 |
|---|---|---:|---|---:|---|
| [(11,16)](l1_gamma_11_16.out.txt) | (15,16) | 45 | `-1545409315094236263/9444732965739290427392` | 9 | `bc9688bdfff7892053bc3f02a31c3a3d4560bfa026a91d16057ac10c43aecd25` |
| [(3,1)](l1_gamma_3_1.out.txt) | (7,5) | 36 | `688672510171296147/2361183241434822606848` | 3 | `a4df7184df3094944ca74d5b7a26b60fc4eac37ad1458e308323e4d2253e8b23` |

The four signed orbits add 162 disjoint words and contribute
`-5644613713792572603/4722366482869645213696` together.
Verified dominant coverage is 88 of 148 orbits and 7,986 of
9,216 words.

### Complete chirality pairs for (8,4), (11,4), and (19,18)

Independent review verified 192 ordered direct selectors and
12 terminal shards per run. On the first pinned roster, a
signed witness maps gamma slice 0 to 1. On the second, it maps
slice 1 to 2. All exact scales and signed witness hashes match,
with zero imaginary parts and no caps.

| Direct representative | Chirality counterpart | Words per orbit | Direct subtotal | Multiplicity | Full receipt SHA-256 |
|---|---|---:|---|---:|---|
| [(8,4)](l1_gamma_8_4.out.txt) | (12,0) | 36 | `-58583762512121259/2361183241434822606848` | 9 | `e31915fe3519053edbd6b0573c50b295d40d37d89b60a4de86bad9a1a10eb0ac` |
| [(11,4)](l1_gamma_11_4.out.txt) | (15,0) | 36 | `-58583762512121259/2361183241434822606848` | 9 | `10aa5b56acd600acf3e8e10fc2b34f31af1e9950cdcaf103d140397cc615d1b5` |
| [(19,18)](l1_gamma_19_18.out.txt) | (23,18) | 30 | `-1297036003818215493/4722366482869645213696` | 3 | `fd0d8001e9647bbcb9a0e0ce582574f39af5e0c05f636b0c29612a76137e40ab` |

The six signed orbits add 204 disjoint words and contribute
`-6000123461891011803/2361183241434822606848` together.
Verified dominant coverage is 94 of 148 orbits and 8,190 of
9,216 words.

### Complete chirality pairs (11,9)/(15,9) and (16,4)/(20,0)

Independent review verified 256 ordered direct selectors, 16
terminal shards, four singleton class witnesses, and exact
scaling per run on the respective pinned rosters. Both imaginary
parts vanish and no caps were hit.

| Direct representative | Chirality counterpart | Words per orbit | Direct subtotal | Multiplicity | Full receipt SHA-256 |
|---|---|---:|---|---:|---|
| [(11,9)](l1_gamma_11_9.out.txt) | (15,9) | 36 | `-742478726025364419/9444732965739290427392` | 36 | `7171cb125143a89e5be840df2f5f8b670fa8147b29aaa394934a3e6608d89ab6` |
| [(16,4)](l1_gamma_16_4.out.txt) | (20,0) | 36 | `-274396016602155609/4722366482869645213696` | 18 | `673a6d248f4c381bcaed29346d0bd7413c8994ffd0601ccb9138841ceb5e47ac` |

The four signed orbits add 144 disjoint words and contribute
`-2287968170911920063/295147905179352825856` together.
Verified dominant coverage is 98 of 148 orbits and 8,334 of
9,216 words.

### Complete chirality pairs (16,11)/(20,11) and (16,16)/(20,16)

Independent review checked all 256 ordered direct selectors, 16
terminal shards, four singleton class witnesses, and exact scales
per run on the second pinned roster. Both direct subtotals are
`-274396016602155609/4722366482869645213696` with zero imaginary
part and no caps.

| Direct representative | Chirality counterpart | Words per orbit | Multiplicity | Full receipt SHA-256 |
|---|---|---:|---:|---|
| [(16,11)](l1_gamma_16_11.out.txt) | (20,11) | 36 | 18 | `31ace0ee01a14d38bf55ce84ec1ace74800a2934a907efd47467a5bfab473327` |
| [(16,16)](l1_gamma_16_16.out.txt) | (20,16) | 36 | 18 | `6989c9836ae078286bafd866c000c4122d8a0e43ea3d4cd5af8a3917f39373ae` |

The four signed orbits add 144 disjoint words and contribute
`-2469564149419400481/590295810358705651712` together.
Verified dominant coverage is 102 of 148 orbits and 8,478 of
9,216 words.

### Complete chirality pair (19,4)/(23,0)

Independent review checked 256 ordered direct selectors, 16
terminal shards, four singleton class witnesses and exact scaling
on the second pinned roster. The component subtotal is
`-274396016602155609/4722366482869645213696` with zero imaginary
part and no caps. The [full receipt](l1_gamma_19_4.out.txt) has
SHA-256 `b4f235887a3b227d19d5b2d5ec2d1864cc58af087cb4ff7f2c6f9a867123a480`.

Each orbit contains 36 words with multiplicity 18. They are
mutually disjoint and disjoint from prior coverage. The pair
adds 72 words and contributes
`-2469564149419400481/1180591620717411303424`.
Verified dominant coverage is 104 of 148 orbits and 8,550 of
9,216 words.

### Modular controls for the common normalization

The [modular replay](l1_modular_motif_control.py) reuses the
exact center tensors and Haar reductions of two reviewed
16-site restricted motifs. It then performs the signed cycle
joins modulo 65,537. Independent review reran the joins,
checked the prime and denominator inverses, and compared
against separately reduced rational receipts.

| Restricted motif | Cycle residues | Coefficient residue |
|---|---|---:|
| Four unswitched layers | 15768, 15768, 15768, 15768 | 53479 |
| Planes switched at centers 0 and 6 | 15768, 54472, 15768 | 48879 |

Live cycle widths are 38 in these controls. The reviewed
35,084-orbit overlap motif reduces to 38375 modulo the same
prime. That value is a target for a direct modular replay.
A nonzero residue would certify nonvanishing of the complete
partition coefficient after exact signed coverage and
denominator checks. The restricted motifs leave that
complete coefficient open.

### Complete chirality pairs for (8,1), (8,8), (8,17), and (9,0)

Independent review checked 256 direct selectors, 16 terminal
shards, four singleton class witnesses, and exact scaling per
run on the original pinned roster. Each component contributes
`-742478726025364419/9444732965739290427392` with zero imaginary
part and no caps. Each signed orbit has multiplicity 18 and
contains 18 words.

| Direct representative | Chirality counterpart | Full receipt SHA-256 |
|---|---|---|
| [(8,1)](l1_gamma_8_1.out.txt) | (12,5) | `3bbe023ea7b9ca03111f80fb46c7dae60e3daeefe520e53ac7bfb1b2cdbe38d5` |
| [(8,8)](l1_gamma_8_8.out.txt) | (12,8) | `4fd2b68f58d165056f0d6bfd40b496a239d1268e2fe9a5dabda2b6a3582f60c7` |
| [(8,17)](l1_gamma_8_17.out.txt) | (12,17) | `e2d2fa3d6e98002f567800610cc8271e3749aa6716f57c6ac15a065fe5720962` |
| [(9,0)](l1_gamma_9_0.out.txt) | (13,4) | `a49179cd4501a645375907af1bc640024ad197de98f2e7c5fbbde7b10862d63f` |

The eight signed orbits add 144 disjoint words and contribute
`-6682308534228279771/590295810358705651712` together.
Verified dominant coverage is 112 of 148 orbits and 8,694 of
9,216 words.

### Two direct modular overlap rows

The [modular overlap control](l1_modular_overlap_two.py)
loads the previously reproduced lower-column rows at SHA-256
`3f15a76fc3ae9af4f3340cfc14626feebee2839c0fb25ead9cf2750ee37bf702`
and the [reviewed exact rows 0 and 1](l1_overlap_control_exact.rows)
at `d487deadea8c31337cecc5ac5ffcceaff79a30e3e0422f9b07b7f4ecbe277b32`.
Run it with the lower-column file and the exact two-row file as
its two positional arguments. The existing lower-column
contraction above documents the reproducible input.

The replay reduces the tracked integer factors and exterior
weights modulo 65,537 before the signed join. Sparse matrices
are canonicalized after reduction. The replay checks the
integer bounds for duplicate summation and sparse products.
Independent review checked the index, signs, and invertible
scale factors. The checked replay took 18.72 seconds.

| Orbit row | Weight | Candidate pairs | Nonzero joined pairs | Raw residue |
|---|---:|---:|---:|---:|
| 0 | 2 | 2,692,881 | 2,247,513 | 28290 |
| 1 | 6 | 2,691,240 | 2,031,218 | 35445 |

The weighted raw residue is 7102. Applying the full motif
scale to these two rows gives residue 7262, matching the
exact rational subtotal
`10561246637180471/1762613844998129336721604608`.
This qualifies the join for the two selected rows. The
35,084-orbit modular replay and the complete common
partition coefficient remain open.

### Complete chirality pairs for (9,1), (9,3), and (9,16)

Independent review checked 256 direct selectors, 16 terminal
shards, four singleton witnesses, and exact scaling per run on
the original pinned roster. Each component subtotal is
`-742478726025364419/9444732965739290427392`, with zero imaginary
part and no caps. Each orbit has multiplicity 18 and 18 words.

| Direct representative | Chirality counterpart | Full receipt SHA-256 |
|---|---|---|
| [(9,1)](l1_gamma_9_1.out.txt) | (13,5) | `e1b179b07fe53c37bb0ca7029e9d9f785222cc72a7d7e4b27ff23334b4b5e940` |
| [(9,3)](l1_gamma_9_3.out.txt) | (13,7) | `141da89fac6b32929ed1391e27dbab482c4b268ea506e1ad7cefb2185fae391b` |
| [(9,16)](l1_gamma_9_16.out.txt) | (13,16) | `3231cca959d33a119e111c7832c0d961a65d633c75769ae1c9a52399dfd1c923` |

The six signed orbits add 108 disjoint words and contribute
`-20046925602684839313/2361183241434822606848` together.
Verified dominant coverage is 118 of 148 orbits and 8,802 of
9,216 words.

### Complete overlap modular replay contract

The [shard runner](l1_modular_overlap_shards.py) uses the pinned
lower-column file and the directory of four reviewed exact
shards. Run `plan` to emit the 97 contiguous ranges, then
`run START STOP OUTPUT` for each range. Once each terminal
receipt is present, `reduce RECEIPTS...` checks the complete
35,084-orbit roster, all multiplicities, and all exact row
residues. The plan calls for 770 active modular joins and
one direct parity-zero control. Its target is raw residue
10618 and normalized motif residue 38375 at prime 65,537.

Independent review checked the schedule, row-wise signed
reduction, caps and normalization. The runner binds the
resolved local source files and verifies their hashes before
publishing a receipt. It writes and flushes a temporary file,
then installs it with an exclusive atomic link. The guarded
two-row replay reproduced raw residue 7102. A one-second cap
left no terminal receipt, and the reducer rejected the
two-row receipt as incomplete. This route verifies the
selected overlap motif. The complete common partition
coefficient requires separate full-sector coverage.

### Complete chirality pair (9,17)/(13,17)

Independent review checked 256 ordered direct selectors, 16
terminal shards, four singleton class witnesses and exact
scaling on the original pinned roster. The component subtotal is
`-742478726025364419/9444732965739290427392` with zero imaginary
part and no caps. The [full receipt](l1_gamma_9_17.out.txt) has
SHA-256 `1c4c1d59e50edab7474963f64014d7a8dbf6418a9f1169ce9e4ff6af7c67d367`.

Each orbit has multiplicity 18 and contains 18 words. The
disjoint pair adds 36 words and contributes
`-6682308534228279771/2361183241434822606848`.
Verified dominant coverage is 120 of 148 orbits and 8,838 of
9,216 words.

### Complete chirality pairs for (11,1), (11,11), and (9,19)

Independent review checked 256 ordered direct selectors, 16
terminal shards, four singleton witnesses, and exact scaling
per run on the original pinned roster. Each component subtotal
is `-742478726025364419/9444732965739290427392` with zero imaginary
part and no caps. Each orbit contains 18 words and has
multiplicity 18.

| Direct representative | Chirality counterpart | Full receipt SHA-256 |
|---|---|---|
| [(11,1)](l1_gamma_11_1.out.txt) | (15,5) | `16721cd76fef74ec6fea58e6cc3a913b334aed8e93da0eeaf3dde2ef8e4fc28a` |
| [(11,11)](l1_gamma_11_11.out.txt) | (15,11) | `da31c6b611b21f1a5ae236720ca896bdfc9035b6e19682160f03d8013dc6ef30` |
| [(9,19)](l1_gamma_9_19.out.txt) | (13,19) | `2609e7cfc50d3667c7a359525f89825fd74e5c9dc4309d85f8549933326039b5` |

The six signed orbits add 108 disjoint words and contribute
`-20046925602684839313/2361183241434822606848` together.
Verified dominant coverage is 126 of 148 orbits and 8,946 of
9,216 words.

### Complete chirality pairs for (11,17), (16,7), and (16,19)

Independent review checked all 256 ordered direct selectors,
16 terminal shards, four singleton witnesses, and exact scaling
per run on the respective pinned rosters. All imaginary parts
vanish and no caps were hit. Each orbit contains 18 words.

| Direct representative | Chirality counterpart | Direct subtotal | Multiplicity | Full receipt SHA-256 |
|---|---|---|---:|---|
| [(11,17)](l1_gamma_11_17.out.txt) | (15,17) | `-742478726025364419/9444732965739290427392` | 18 | `f94fa78447f14dfb8c07cffbb1f84b9a6505dd41f3ec66b466327b93f6ef6e7f` |
| [(16,7)](l1_gamma_16_7.out.txt) | (20,3) | `-274396016602155609/4722366482869645213696` | 9 | `070c667cf7d632c36b0998e33eae8b5283a7e8acf270228507693cd56c0cab51` |
| [(16,19)](l1_gamma_16_19.out.txt) | (20,19) | `-274396016602155609/4722366482869645213696` | 9 | `ead832e8ae6e7aed6e9159f73c7730d3fbab6128a648263fb93a8e388ede86cf` |

The six signed orbits add 108 disjoint words and contribute
`-11621436833067080733/2361183241434822606848` together.
Verified dominant coverage is 132 of 148 orbits and 9,054 of
9,216 words.

### Complete chirality pairs for (19,7), (3,16), and (8,0)

Independent review reduced every ordered raw selector and shard,
checked exact scaling and signed gamma witness hashes, and verified
the six word sets against the previously accepted population. The
first representative used 256 direct selectors. The other two used
192 direct selectors from slices 0, 2 and 3 and a verified signed
witness transferring slice 0 to slice 1. All imaginary parts vanish
and no caps were hit.

| Direct representative | Chirality counterpart | Direct subtotal | Multiplicity | Words per orbit | Full receipt SHA-256 |
|---|---|---|---:|---:|---|
| [(19,7)](l1_gamma_19_7.out.txt) | (23,3) | `-274396016602155609/4722366482869645213696` | 9 | 18 | `6aa15f37c6f8206ef28bc052833610498bf9561a9ee4a73076e9b66f17b09445` |
| [(3,16)](l1_gamma_3_16.out.txt) | (7,16) | `688672510171296147/9444732965739290427392` | 3 | 9 | `aa893989f98c0ec0d6dec393a686f7353b3694452c7eecee6b104942e7219154` |
| [(8,0)](l1_gamma_8_0.out.txt) | (12,4) | `-742478726025364419/9444732965739290427392` | 9 | 9 | `669a596467a4ef46046ca8e0e4855e08646c135a2ebef78b52e7913206e470c3` |

These orbits add 72 disjoint words and contribute
`-2388854825638298073/1180591620717411303424`.
Verified dominant coverage is 138 of 148 orbits and 9,126 of
9,216 words for the selected ordered G22 coefficient.

### Complete chirality pairs for (19,16), (8,16), (11,3), and (11,19)

Independent review checked the exact ordered selectors, shard
reductions and scaling, signed witness digests, and disjoint word
membership. The first representative used 256 direct selectors.
Each other representative used 192 direct selectors from slices
0, 2 and 3 with the signed transfer from slice 0 to slice 1.
All imaginary parts vanish and no caps were hit.

| Direct representative | Chirality counterpart | Direct subtotal | Multiplicity | Words per orbit | Full receipt SHA-256 |
|---|---|---|---:|---:|---|
| [(19,16)](l1_gamma_19_16.out.txt) | (23,16) | `-274396016602155609/4722366482869645213696` | 6 | 12 | `42e977c492530b3f341533b0f8c25becb56b0e9e4d795366cb03270d60a1bcd7` |
| [(8,16)](l1_gamma_8_16.out.txt) | (12,16) | `-742478726025364419/9444732965739290427392` | 9 | 9 | `5148c26dc4e461f70555eedbbb521be5e18bf6f307d679574e28804e34def7d1` |
| [(11,3)](l1_gamma_11_3.out.txt) | (15,7) | `-742478726025364419/9444732965739290427392` | 9 | 9 | `9c362c011fc869e14b1d4620b8827a400d006f4f32c613aa3030790a827431fa` |
| [(11,19)](l1_gamma_11_19.out.txt) | (15,19) | `-742478726025364419/9444732965739290427392` | 9 | 9 | `d4b99dbcfa8902d58ca911c37502c5d3bbcce0c41a198b55e33c8ef2779a2146` |

These orbits add 78 disjoint words and contribute
`-23339677801910706621/4722366482869645213696`.
Verified dominant coverage is 146 of 148 orbits and 9,204 of
9,216 words for the selected ordered G22 coefficient. The final
pair, (19,19) and (23,19), requires its own accepted receipt.

Independent cumulative reconstruction checked 75 direct representative
values including overlapping controls. It reduced the archived raw
rows, shards and classes, checked the original pilot through its
hashed receipt list, and deduplicated equal overlapping controls.
The 146 accepted orbits cover 9,204 distinct signed words and
sum to `-432109557732318904053/2361183241434822606848` with zero
imaginary part.

### Complete selected dominant and minority contraction

Independent review verified the final [(19,19) receipt](l1_gamma_19_19.out.txt),
including its 192 ordered selectors from slices 0, 1 and 3,
12 exact tranches, and the signed slice-1-to-slice-2 witness.
The component subtotal is
`-274396016602155609/4722366482869645213696`.
Its orbit has multiplicity 3 and six words. Its signed
counterpart (23,19) has the same value and multiplicity, supplying
the last twelve disjoint words. The pair contributes
`-823188049806466827/2361183241434822606848`.
All imaginary parts vanish and no caps were hit.
The full receipt SHA-256 is
`2f276294cfda1f6de015e5c28ddbeeb3d2ba185e077f5e9794a113f881109349`.

The independent raw-receipt reconstruction and the lead's replay
both cover all 148 dominant orbits and 9,216 signed words.
They give the dominant subtotal
`-845571769105713615/4611686018427387904`.
The complete minority contraction above uses the same source
ordering, frame planes, Haar orientation and divisor. The signed
primitive scale is restored exactly once in each calculation.
Its 576 words are disjoint from the dominant population.
Thus all 9,792 nonempty B occurrences for this selected ordered
G22 contribution give
`1664779014112370625/4611686018427387904`,
with zero imaginary part. No extra source-pair or factorial
multiplicity is inserted between these two sums. Full action
and source summation, the common geometry normalization, and
the physical retarded response remain separate constructions.

### Full modular verification of the selected overlap motif

The [complete receipt archive](l1_modular_overlap_complete_receipts.jsonl)
contains 97 terminal envelopes with their original filenames
and file SHA-256 hashes. Each original envelope is recovered by
serializing its `receipt` field with sorted keys and compact
JSON separators, followed by one newline. The archive SHA-256 is
`0dbff506efb30c6718253f29027dfa4f07ace852569ac0ea1fd67bf83c430b1d`.
The [canonical reducer output](l1_modular_overlap_complete_reduction.json)
records every shard range and hash. The coverage digest is
`fc4f7dca24cabf2c791d8f0bb94e8ff467721196c1481ff14c454d4396675f7c`.

Independent review and the lead's canonical reducer run verified
unique contiguous coverage of [0,35084), 589,194 orbit weights
and 94,748,063,904 weighted candidates. The receipts contain 770
joined rows, one explicitly joined zero control and 34,313
parity-excluded zero rows. Every raw residue agrees with its
hash-verified archived exact row modulo 65,537. The full raw
residue is 10,618, and the normalized motif residue is 38,375.
The independent reviewer checked the curvature, exterior and
upper-sheet scales and retained 238 negative exact rows.

This is rowwise arithmetic and receipt-custody verification of
the selected normalization motif. The review did not freshly
rerun all 770 contractions. Full common normalization, complete
source response and physical susceptibility acceptance remain
open.

### Complete paired four-deviation census

The [four-deviation runner](l1_extended_offset_witness_k4.py)
reuses the paired-word census, geometry and exact contraction
kernels. The census's optional deviation count defaults to
three, preserving the existing k3 entry point. Independent
meet-in-the-middle enumeration agrees word for word with the
complete k2, k3 and k4 populations. It enforces the full degree
equation at each of the sixteen sites.

| Ordered source axes | Two deviations | Three deviations | Four deviations |
|---|---:|---:|---:|
| (2,2) | 4 | 8 | 164 |
| (2,3) | 2 | 4 | 108 |

The [complete census receipt](l1_k4_census.out.txt) records
all 272 four-deviation words. Its manifest digest is
`ada6e3a7bd8b32b238a85f1a8e7070dde1d2846f5fe6bc5184068a0fc9596d5b`.
Independent private-link peeling verifies 90 supported words
across five geometry classes. The other 182 entries retain
their geometry failures explicitly. Of these, 86 are fully
peeled cases for which the existing geometry routine encounters
an empty-set-union error. None of the unsupported words has
been assigned a zero coefficient.

The next exact replay covers all 42 same-axis words with one
protected four-face torus, no square, and no free torus.
Independent review checked one protected source link and no
other protected curvature edge in every word. Thirty-six words
share a geometric action/source edge, handled by the existing
joint Haar integration; six do not. The normalization retains
fifteen paired vertices, `2!^15`, existing frame and source
scales, and one factor of `48` per peeled face.

The [word-4 receipt](l1_k4_word4.out.txt) gives
`28491102303472560120705/35184372088832` with a peak of 3,952
rows. This is an author-run exact contraction using the
independently reviewed kernel applicability. Independent review
has not rerun this new contraction. The full 42-word sum and
the remaining four-deviation words require their own completed
receipts and verification. All full-ensemble and physical
acceptance requirements remain open.

### Fully peeled four-deviation source words

Independent topology review identifies 86 completely peeled
words in the four-deviation census: 54 same-axis and 32
mixed-axis. The [fully peeled evaluator](l1_extended_offset_witness_k4_peeled.py)
retains both source Haar integrals and evaluates one contraction
branch. It introduces no fixed gauge links. Every shared
source/action edge has exactly one action-center incidence.

| Ordered source axes | No shared edge | One shared edge | Two shared edges |
|---|---:|---:|---:|
| (2,2) | 6 | 32 | 16 |
| (2,3) | 20 | 12 | 0 |

For `E` geometric action-frame edges and `J` shared edges, the
divisor is `(192²)^E · 4^64 · 192^(2−J) · 48^15 · 2^15`.
Shared sources use the existing joint moments and are excluded
from both independent source factors and exclusive-edge
diagonal pruning. Both relative endpoint orientations occur.
The remaining sources are integrated with the existing Haar
moment. All fifteen curvature pairs peel, so there is no
protected-core branch sum.

The [canonical preparation controls](l1_k4_peeled_controls.out.txt)
check representatives with zero, one and two shared edges.
The independent implementation reviewer reproduced the
[double-shared word-0 result](l1_k4_peeled_word0_review.out.txt)
exactly. Its coefficient is
`834814503361393106337/2199023255552`, with peak 3,952 rows.
The evaluator SHA-256 is
`7eb0114dec24a2cc0674c2e3e3865ffc34d12924f131868d95ad121c62d31a4c`.
The old census's `supported_geometry:false` field describes
the original k3 geometry kernel. This evaluator supplies the
separate fully peeled route.

The full 86-word coefficient sums remain pending. Together
with the 90 words supported by the original geometry kernel,
these words leave 96 census entries requiring other core
constructions. All full action, source, common normalization
and physical matching requirements remain open.

### Complete four-deviation single-protected-torus class

The [42-word receipt archive](l1_k4_core42_receipts.jsonl) and
[independent verification](l1_k4_core42_verification.json)
cover every same-axis census word with one protected torus,
no square and no free torus. All 42 CLI runs exited zero.
Every terminal row matches its declared census word, manifest,
reduced rational coefficient and integral numerator under its
divisor. Maximum peak is 3,952 rows, with no cap failures.

The complete unsigned same-axis subtotal is
`53640259931094413213475/8796093022208`.
No shear or axis multiplicity has been applied. Independent
covariance verification translates sites by XOR1, swapping the
two commuting same-axis sources. All 21 paired coefficients
agree exactly. The per-receipt bundle digest is
`46719bf801747b0d9f497ef28cdd3fb1695a411be3d1be372be6d361d90f1c22`.

The fully peeled 86-word population is a separate contraction.
The other supported geometry classes and the remaining
residual-core words are still required for the complete k4
coefficient.

### Complete fully peeled four-deviation population

The [86-word receipt archive](l1_k4_peeled86_receipts.jsonl)
and [independent verification](l1_k4_peeled86_verification.json)
cover all fully peeled words. Every declared unique word has
an exit-zero terminal, matching census row, exact reduced
coefficient and integral reconstructed numerator under its
audited divisor. Maximum peak is 3,952 rows. No cap was hit.

| Ordered source axes | Words | Exact subtotal |
|---|---:|---|
| (2,2) | 54 | `496437586062832211319/68719476736` |
| (2,3) | 32 | `2863352227266063230535/4398046511104` |

This symmetry-closed population has restricted shear
`2(same−mixed) = 28908653280755198293881/2199023255552`.
All 27 same-axis translation pairs and all 16 mixed
translation/axis-exchange pairs agree exactly. The independently
reproduced double-shared word-0 control remains part of the
acceptance evidence. The receipt bundle digest is
`bb3c432d527e0ef539b378fab3f76455b72711712c3e577ccc5abbecce55792b`.

Together with the separate 42-word class, 128 of the 272
four-deviation words are computed. The other 48 words already
supported by the original geometry kernel and 96 words needing
other core constructions remain open. The complete action/source
ensemble, common partition coefficient and physical response
matching remain required.
