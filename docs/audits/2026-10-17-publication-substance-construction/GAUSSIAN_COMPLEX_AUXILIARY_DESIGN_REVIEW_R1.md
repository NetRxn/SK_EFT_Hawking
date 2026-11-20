# Independent prospective review: complete complex auxiliary transform r1

Verdict: **APPROVE_FOR_ADMITTED_DISCOVERY_AND_IMPLEMENTATION**.

This approves the mathematical specification and source-composition direction prospectively. It does not certify an implemented theorem, Lean elaboration, kernel result, build, slot admission, canonical integration, publication gate, physical premise, or full B3 result. No blocking mathematical correction is required. ROOT retains acceptance, scheduling, primary notebook, and authoritative build ownership.

Task: `publication-complex-auxiliary-design-review-r1`; parent: `publication-remediation`. Candidate primary: `2c201cd00cd1d17e7665ea0a6711344abc1c1524`. Governing reviewer packet: `/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/.codex/continuity/publication-complex-auxiliary-design-review-r1.json`. Initial same-packet check returned exit 0, fresh=true, changed=[]. Final same-packet check is reported in the final return; no source change is accepted implicitly by this review.

## Inputs and independence

I read the original complete 98-line `ADW_EXACT_AUXILIARY_IDENTITY.md`, not a rewritten excerpt, and the complete proposed `/tmp/publication-complex-auxiliary-design-r1.md` and `.json`. I inspected mandatory project correctness/continuity guidance, relevant ADR-008 authority, ADR-017, owning roadmap and ROOT notebook context. I independently read the complete existing `GaussianPolynomialAffine.lean`, `GaussianPolynomialHermite.lean`, and `GaussianPolynomialIBP.lean`, and the relevant actual local Mathlib scalar-extension, factorial, Gaussian, power-series substitution/exponential, polynomial coefficient, and multivariate series coefficient source. I did not consult the designer or another reviewer. I made no repository, source, registry, notebook, or other-report edit. Only this report and its JSON companion are mine.

## Original full-strength contract

Eq5 permits arbitrary finite complex coefficients, signed or complex W, every positive sigma, and no degree-four restriction. Eq6 is a formal coefficient identity for arbitrary finite P before evaluating at Grassmann elements. The proposed P : MvPolynomial iota Complex, finite iota including empty, W defined explicitly from finite Hermite support, and all-beta theorem meet that contract. Retaining v : NNReal with coe(v)=sigma^2 is a representation of the actual Gaussian variance, not an added physical hypothesis. Finsupp multiindices have coordinatewise order and truncated natural subtraction; the explicit order test is indispensable.

No alpha-factorial belongs in W. No coefficient conjugation belongs in the transform. The exponential generating parameter carries beta-factorial, so the normalizing denominator is the product of coordinate factorials, never total-degree factorial.

## Independent mathematical derivation

For each alpha and beta, the actual existing affine product theorem gives the real integral as the product over i of

`sigma^(alpha_i) * beta_i.descFactorial(alpha_i) * m_sigma(beta_i-alpha_i)`.

If alpha is not coordinatewise at most beta, at least one descending factorial vanishes. Thus natural subtraction cannot spuriously retain an off-order coefficient. If alpha <= beta, the product of sigma powers is sigma^|alpha| and cancels W's inverse scale. Dividing by product(beta_i!) and using `(beta_i-alpha_i)! * beta_i.descFactorial(alpha_i) = beta_i!` leaves

`product_i [m_sigma(beta_i-alpha_i)/(beta_i-alpha_i)!]`.

All denominators are nonzero after casting into Complex. Polynomial Gaussian moments exist absolutely. The Gaussian recurrence `m(0)=1`, `m(1)=0`, `m(n+2)=(n+1)*sigma^2*m(n)` yields odd zero and

`m(2k)/(2k)! = (sigma^2/2)^k/k!`.

The proposed fallback recurrence follows correctly from Hermite order one and p=X^(n+1): the left side is m(n+2)/sigma and the right side is sigma*(n+1)*m(n). Positive sigma permits the division. This fallback is a viable mathematical proof strategy if live typed search finds no preferable existing all-order result; this review asserts no API absence.

Complex scalar extension then gives the same formula for every complex coefficient without conjugation. Finite summation gives exactly the proposed all-index convolution. This derivation treats beta above P's degree as fully meaningful; Gaussian tails remain in infinitely many higher formal coefficients. The theorem must not be restricted to beta below degree(P).

## Genuine complex Bochner integrability

The proposed route is sound: distribute each Hermite-product times monomial into the actual integrable real product supplied by `integrable_prod_hermite_mul_pow_affine`, lift by `Integrable.ofReal`, multiply by the complex constant coefficient and real inverse sigma cast, and sum finitely. This proves Integrable of W*h^beta independently of any equality of integrals. Beta=0 gives Integrable W. Arbitrary products of separate integrable functions are not used. Empty coordinate products reduce to constants under the probability product measure and preserve a nonreal constant integral.

The scalar-extension integral theorem itself is total and does not require a written Integrable argument. That does not remove the separate integrability requirement, which the proposed acceptance contract correctly retains.

## Actual exp(Q) and full series assembly

The Gaussian series definition is independent: `PowerSeries.subst Q (PowerSeries.exp Complex)` with Q=sum_i C(sigma^2/2)*X_i^2. Its constant coefficient is zero, so substitution has the necessary nilpotent constant coefficient. This is an actual formal exponential, not the desired Gaussian coefficients installed as a definition.

For gamma with any odd coordinate, the coefficient in every Q^n is zero. For gamma=2k coordinatewise, only n=sum_i k_i contributes, with coefficient `n!/(product_i k_i!) * (sigma^2/2)^n`. Multiplying the exponential coefficient 1/n! gives product_i g_sigma(gamma_i). This argument also handles zero coordinates and the zero multiindex. For empty iota, Q=0 and exp(Q)=1.

Defining AuxiliarySeries by the actual normalized integral coefficients is legitimate. Its equality with exp(Q)*P is substantive only after both the genuine integral coefficient identity and the independent actual-exp(Q) coefficient theorem. Extensionality at the end is assembly, not an alternate proof of those results. Defining AuxiliarySeries as the RHS, defining GaussianSeries as the transform of 1, or replacing Q's exponential by an unproved product would fail the contract. The design explicitly excludes those moves.

No analytic integration of an infinite exponential series is needed or certified. Formal coefficient extraction uses a finite Gaussian moment in each coefficient. Local finiteness of formal substitution follows from zero constant coefficient; degree-two homogeneity further isolates the unique possible n. This must remain distinct from a dominated-convergence/analytic exponential interchange argument.

## Actual source API evidence and pending discovery

Static source confirms:

- Existing affine integrability/integral statements take alpha,beta as ordinary functions, allow arbitrary Fintype iota, and have sigma>0 and the stated v,hv; they contain no Nonempty or finite-degree cutoff. Their exact product placement matches the pointwise redistribution required here.
- `Integrable.ofReal` in Mathlib L1Space/Integrable lifts an integrable real-valued function to an RCLike codomain. Bochner/ContinuousLinearMap supplies `integral_complex_ofReal` and `integral_ofReal`.
- `Nat.factorial_mul_descFactorial` requires k<=n and states `(n-k)! * n.descFactorial k = n!`; `descFactorial_eq_zero_iff_lt` and `descFactorial_of_lt` provide the off-order case.
- `PowerSeries.exp A` has coefficients `algebraMap Rational A (1/n!)`. `PowerSeries.HasSubst a` is `IsNilpotent (MvPowerSeries.constantCoeff a)`. `HasSubst.of_constantCoeff_zero` supplies precisely the needed sufficient condition.
- `PowerSeries.subst a f` accepts a multivariate target, and `PowerSeries.coeff_subst` computes coefficients as a finsum over natural n of `coeff n f` acting on `coeff gamma (a^n)`. `coeff_subst_finite` states finite support of those terms. There is a direct univariate-to-multivariate API; guessing that only `MvPowerSeries.coeff_subst` exists is unnecessary.
- `MvPowerSeries.coeff_mul_monomial` has exactly the coordinatewise-order and subtraction conditional needed by convolution. `MvPolynomial.coeff_coe` identifies polynomial embedding coefficients. `MvPowerSeries.coeff_pow` is an antidiagonal sum, not already the desired closed multinomial formula.
- Mathlib `MvPolynomial.coeff_linearCombination_X_pow_of_fintype` gives a finite linear-form power coefficient using `s.multinomial`. Combining polynomial expansion/coordinate squaring, embedding, and this theorem is a plausible alternate route to Q's quadratic-power coefficient. That composition remains an implementation obligation.
- Gaussian.Real has the complex MGF, mean integral, and all finite Lp moment integrability substrate. The complex MGF is not by itself the Hermite polynomial theorem or a formal coefficient interchange proof.

Actual matching LSP statement/type searches, coercion/import elaboration, outline/goal diagnostics, and export `lean_verify` are **PENDING**, required before/during admitted implementation. Static `rg` and source reading do not substitute for these searches. In particular, discover current all-order normalized moments, existing complex polynomial integrability, Finsupp/order/coercion lemmas, exact scalar extension types, polynomial support expansion, and quadratic homogeneous coefficient/multinomial tools. Uncertainty about signatures or shortest proof architecture is not a mathematical impossibility and does not require weakening P to real coefficients, nonempty dimension, or degree four. The claim that no new runtime infrastructure is needed is reasonable; auxiliary mathematical lemmas may still be needed.

## Independent manual checks of every proposed control

These are hand calculations, not executed tests or Lean checks.

1. Empty iota: its sole multiindex is zero; W is P's constant, product Gaussian mass is one, and the actual integral for P=-2+3i is -2+3i. Q=0, GaussianSeries=1, AuxiliarySeries=P.
2. P=1+iX-2X^2: He1=z and He2=z^2-1 give `W=1+i*h/sigma^2-2*h^2/sigma^4+2/sigma^2`. Using m2=sigma^2, m4=3sigma^4, m6=15sigma^6, the raw integrals at beta=0..4 are `1, i, sigma^2-4, 3i*sigma^2, 3sigma^4-24sigma^2`. Dividing respectively by `1,1,2,6,24` gives exactly `1,i,sigma^2/2-2,i*sigma^2/2,sigma^4/8-sigma^2`. At sigma=2 they are `1,i,0,2i,-2`, and the raw beta4 integral is -48.
3. P=(1+i)X1X2: normalized coefficients at (1,1),(3,1),(2,1) are respectively `1+i,(1+i)*sigma^2/2,0`. Raw (3,1) is `3*sigma^2*(1+i)`. The denominator is 3!*1!=6, whereas total factorial 4!=24 would wrongly divide the result by four. At (1,1), total factorial 2!=2 would already halve it.
4. Alpha=(2,0), beta=(1,8): the first descending factorial is 1.descFactorial(2)=0 despite total degree 2<=9. Alpha=5,beta=4 likewise gives zero, despite truncated difference being zero. Both controls are valid.
5. P=iX^7: beta7 normalized is i and raw is 7!*i=5040i; beta9 normalized is i*sigma^2/2 and raw is 181440*sigma^2*i. At sigma=2 raw beta9 is 725760i and normalized is 2i. At the second positive nonunit scale sigma=1/2 raw beta9 is 45360i and normalized is i/8. Beta7 remains 5040i at both scales.
6. For any pure monomial with alpha=beta, scale cancellation gives exactly p_alpha. For mixed alpha=(1,1), dropping inverse scale gives sigma^2*(1+i), as stated. Changing the inverse to sigma^(-2|alpha|) instead gives sigma^(-|alpha|)*p_alpha and fails nonunit diagonal controls.
7. P=1: beta0,1,2,4 normalized are `1,0,sigma^2/2,sigma^4/8`; these force the plus sign in Q.

The prospective mutations also have the stated discriminatory value. He2=z^2+1 makes the zero coefficient for P=-2X^2 become -4/sigma^2. Omitting beta-factorial, conjugating p, using total-degree order, truncating support at four, or changing Q's sign all fail an indicated nonzero control. A zero/nonintegrable surrogate is excluded jointly by independent Integrable evidence and the nonzero constant/diagonal controls. These controls must later instantiate carrying theorems and actual integrals; testing only definitions with the same duplicated error is insufficient.

## Remaining acceptance and original downstream obligations

Admit discovery first, then implement the complete A-D mathematical block, independently review actual statements/proofs/controls, verify actual exports, and let ROOT run required integration/build/extraction/gates. This prospective approval grants none of those receipts.

Eq4 still needs the actual source polynomial, formal expansion, compensation and truncation proof. Eq7 still needs the concrete Grassmann algebra, explicit source coframes, degree-two/even commutation, global M=4V nilpotence bound, and legitimate commuting-family evaluation. The full all-index formal identity removes no obligation to prove these evaluation/truncation steps. General noncommutative formal substitution cannot be assumed.

The source matrix/signs, Berezin orientation/determinant, compact-link coefficient continuity/boundedness and actual Gaussian/Haar/Berezin exchange, Eq11 retaining derivative of W, Z nonzero for normalized observables, physical source/response/state/domain/adjoint/dynamics and B3 scale/window/mode/transport remain open. Signed/complex W gives no positivity/RHMC or scalar-potential inference. No new physical premise, axiom, native certificate or full B3 claim is introduced by this review.

Commands executed were read-only continuity checking and bounded source/guidance inspection (`cat`, `sed`, `rg`, `wc`, `head`, `tail`), followed by writing only the two assigned /tmp reports with Python. No tests, builds, LSP, slots, controller/process operations, dependency repair, Git write, external research, or source mutation were executed. Final continuity is checked again on the identical reviewer packet immediately before return.
