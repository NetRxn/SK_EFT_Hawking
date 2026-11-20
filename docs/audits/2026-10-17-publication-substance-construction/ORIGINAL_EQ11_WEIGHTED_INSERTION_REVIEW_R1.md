# Independent original weighted Eq11 design review R1

**Accept the mathematical design for implementation.** The first Lean
assignment is the generic centered complex polynomial Stein identity with
absolute integrability. Full acceptance still requires the actual printed and
closed coframe insertion statements, both derivative orders, joint
integrability and coefficient correspondence. This review establishes a
proof route and tests its algebra. Elaboration, native and publication
acceptance are pending.

## Original source and exact bridge

I checked the held Diakonov 2011 primary PDF at SHA256
`132d63150a678ef17bfbbc04978a8cab9c9801f03556982a6aa67c11d3fbc4da`.
Its page 9 Eq. (11) defines the continuum covariant fermion-bilinear
coframe. Page 13 Eq. (23) gives the four-term lattice discretization with a
family of regulator choices. Equations (24)–(28) specify the action terms,
Berezin orientation and normalized left/right Haar measures. The project
selects the symmetric regulator and keeps printed and closed curvature
words separately. The weighted insertion identities reviewed here are the
project's finite response for the original Eq. (11) coframe, with the actual
formula in project composite-source §5 Eqs. (9)–(10).

At exact primary `25b5f229ce3f518ac08a9279f1680f2068cd4a4c`, I read
`FiniteGrassmannSourceAuxiliary.uncurried_global_eq7` and
`uncurried_global_integrable`. The latter needs positive scale and exact
variance, while the former also takes every site polynomial's zero
constant coefficient. Both use the original full compensated integrand
at each link configuration. To express the original exponent as a single
source, `atSite` and `siteFamily_evaluation` supply the exact global
polynomial. Mathlib `MvPolynomial.constantCoeff_rename` preserves its
required zero constant. Use `FiniteGrassmannEvaluation.coframe_nilExp_add`
in the commutative bilinear subalgebra and transport with its algebra
inclusion. General exterior multiplication need not commute. Multiplication
by the fixed insertions and fixed source exponential is complex-linear
on the finite-dimensional exterior space. Compose its continuous version
with `berezinContinuous`, then use `integral_comp_comm` with actual
integrability, following the existing `berezin_integral`.

The original `fullWeight` is the product of all site compensation weights,
and `completeHaarPolynomial` builds that product times the original
determinant. `siteWeightHaarPolynomial_eval`,
`diracHaarPolynomial_eval`, `globalMatrix_eq9`, and
`berezin_nilExp_det` carry exact original coframes, all coincident-anchor
increments and normalization. Only the determinant polynomial gets the
translation by complex J. The single-variable specialization of
`haarPolynomialEvaluation` commutes with partial derivatives through
`MvPolynomial.pderiv_map` and `MvPolynomial.eval₂_eq_eval_map`. The
recorded read-only Lean probe at `4672e9fec` confirms the core Haar and
partial-derivative declaration types. I confirmed no Lean source/toolchain
difference between that candidate and this primary.

The existing `haarPolynomial_integrable` handles each final expanded
weighted polynomial under the product measure, including arbitrary
continuous link coefficients. With the fixed-link pointwise result, it
supports original Haar integrability, and the same `integral_prod` and
`integral_integral_swap` route as `original_eq10` and
`original_eq10_gaussian_outer` yields both iterated orders. Reuse
`printedSource_constantCoeff`, `printed_source_coeff_continuous`,
`closedSource_constantCoeff` and `closed_source_coeff_continuous` to
discharge the hypotheses independently. With J=0 and no insertion, the
two wrappers must recover `printed_full_eq10` and `closed_full_eq10`.
A common cutoff `4 * volume L` is valid. The site type is inhabited by
the zero site, so its finite cardinality is positive and the first
coefficient occurs in each cutoff exponential.

## First proof assignment

Use one new module for the generic complex scalar identity. The direct
imports `SKEFTHawking.ADW.GaussianAuxiliaryComplex` and
`Mathlib.Algebra.MvPolynomial.PDeriv` suffice at the source level if the
measure is stated as `Measure.pi (fun _ : ι ↦ gaussianReal 0 v)`.
The project alias `gaussianMeasure` lives in
`GaussianGrassmannAuxiliary` and is definitionally this measure. Keep
that heavier import out of the scalar file and use the alias downstream.
Specify `[Fintype ι]`, `σ : ℝ`, `0 < σ`, `v : ℝ≥0`,
`(v : ℝ) = σ ^ 2`, `P : MvPolynomial ι ℂ` and for Stein `a : ι`.
Write `ev h := MvPolynomial.eval (fun i ↦ (h i : ℂ))` and
`q := (((σ : ℂ) ^ 2)⁻¹)`. Prove the following exact targets.

1. `Integrable (fun h ↦ ev h P) μ`.
2. `(∫ h, ev h (MvPolynomial.pderiv a P) ∂μ) =
   ∫ h, q * (h a : ℂ) * ev h P ∂μ`.

For the first theorem, reuse
`integrable_auxiliaryHermite_mul_monomial` at the zero Hermite
multiindex, use `.ofReal` and finite sums, and reconcile the finite
support product with the full finite product as
`gaussian_monomial_integrable` already does in the specialized Haar
module. For the second theorem, expand by `MvPolynomial.induction_on'`
or support sum and use `MvPolynomial.pderiv_monomial`.
`integral_auxiliaryHermite_mul_monomial` at zero and at
`Finsupp.single a 1` gives the two moment products. The singleton
Hermite insertion evaluates to h_a/σ, and its a-factor is
σ times the descending factorial β(a) times the lowered moment. At
other coordinates factors agree by equality, with no division by a
moment. Explicitly handle β(a)=0, which makes the insertion integral
zero. An equivalent route uses `auxiliaryMoment_recurrence` for positive
β(a) and `auxiliaryMoment_odd` at β(a)=0. Use the positivity of σ
only to invert its complex cast. The identities hold for arbitrary
polynomial degrees and complex coefficients with no positivity
assumption on P. The already-checked names and source are evidence of
available support, and the first assignment should still check the
actual imported terms and elaborate the statements in its slot.

Next lift through coefficient evaluation and the existing joint
integrability theorem. With A_a(W)=q X_a W−∂aW, use
`MvPolynomial.pderiv_mul` to transfer ∂a and then ∂b. The product rule
`pderiv_X_self` and `pderiv_X_of_ne` gives the diagonal contact
−qδ_ab W in A_b(A_a(W)). The two gradient terms and ∂b∂aW remain.
Use derivative order consistent with composition, or prove commutation
from `coeff_pderiv` if a downstream statement needs the opposite order.

## Coefficients and adverse controls

At fixed link and base point, specialize the determinant coefficients
to ℂ and substitute two independent perturbations t and s. The
univariate degree-one coefficient rule can use
`MvPolynomial.induction_on` with constants, sums and multiplication
by a variable. For products, Mathlib `Polynomial.mul_coeff_one`
supplies exactly the Leibniz sum, with constant coefficient
evaluation at zero. Apply the same lemma over `Polynomial ℂ`
for the outer coefficient in t. Apply it over ℂ for the inner
coefficient in s. This computes ∂b∂a even when a=b. For example,
the coefficients of ts and t² in (h+J+t+s)² are 2 and 1.

For the Grassmann side, take coefficients of the product of the
two finite nilExp factors and the base exponential, after applying
the existing complex Berezin functional to each coefficient. Evaluate
at actual t,s ∈ ℂ and apply `globalMatrix_eq9`,
`coframe_nilExp_add` and `berezin_nilExp_det` pointwise. Mathlib
`Polynomial.funext` can then be used twice over ℂ. One direct proof
first evaluates the inner coefficient ring at an arbitrary s, uses
univariate extensionality in t, and reads each t coefficient. A
second use in s identifies the inner polynomials. This preserves
the actual complex determinant theorem. No Berezin identity over a
new coefficient ring or inverse of a potentially singular matrix is
required. Explicitly carry the finite source polynomial through the
fixed measure coefficientwise if the published statement names
formal derivatives of Z. This is justified by polynomial
integrability and finite sums, without a limit interchange.

I independently recomputed the controls by exact rational product
moments and formal differentiation. For variance 2, W=x²+2 and
D=(x+1)², both weighted derivatives are 8. Dropping W' from the
first gives 16. Omitting the diagonal contact, either gradient term,
or W'' from the second gives 18, 22, or 2. For unit variance,
W=1+xy and D=(x+1)²(y+1)², the mixed terms are 20−8−8+4=8.
For W=x, D=x² and variance 2, Z=0 and the first insertion is 4.
Dropping W' gives 6. For W=1, D=(x+i)² and unit variance, Z=0
and the first insertion is 2i. Conjugating the source reverses
this value. Keep a downstream actual-source check for both words
and a nontrivial coframe. A zero identity-link one-site control
cannot by itself detect loss of insertion factors.

All of this concerns undivided finite identities at arbitrary complex
J and both couplings. Numerical full Z, connected normalization on
a demonstrated nonzero domain, analytic inverse/Hessian, continuum
control and physical susceptibility/transport remain separate tasks.
