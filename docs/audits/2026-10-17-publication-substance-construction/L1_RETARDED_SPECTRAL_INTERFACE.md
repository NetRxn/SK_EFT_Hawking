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
