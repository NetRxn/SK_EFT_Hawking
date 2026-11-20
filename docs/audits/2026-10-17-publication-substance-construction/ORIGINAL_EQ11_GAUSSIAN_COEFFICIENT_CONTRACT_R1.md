# Original Eq11 explicit finite coefficient evaluation

Parent is publication-l1-eq11-compensation. Start from the exact accepted
symbolic weight and periodic Eq11 wrappers after native qualification. Pin
the new source and built imports. Search by type before adding a new claim.

Use GaussianAuxiliaryComplex.auxiliaryMoment_normalized for arbitrary n and
the product Gaussian identity already used by
GaussianPolynomialStein.integral_auxiliaryMonomial_complex.
The normalized single-coordinate coefficient must be multiplied by n!,
or equivalently by auxiliaryFactorial at the multi-index. Keep the
positive variance hypothesis v = sigma² used by the existing wrappers.

Construct a finite linear contraction of a polynomial in h and J onto
its J polynomial. On an h/J monomial (d,e), keep e unchanged and multiply
by the product of the exact unnormalized Gaussian moments for d. Prove the
whole evaluator agrees with the integral of the original polynomial. Apply
it to the result of the joint Haar contraction for both actual Eq11 words
and all insertion constructors, so every J coefficient is a finite sum
with exact moments rather than a remaining measure integral. Reuse the
existing coefficient collision discipline in QuaternionSU2HaarPolynomial.
Discriminate h^4 at nonunit variance, a surviving J exponent, an odd h
factor, and two contributions that collide and cancel at the same J label.

For executable correspondence, sourceInsertionValue_eq_nilExp already
transports the same original insertion to the direct finite exterior
exponential. Use that bridge as the comparison specification for the
actual Python quarter increments, signed product and coefficient extraction.
A standalone exact moment theorem or bounded Python control leaves that
production correspondence and the full original numerical coefficients open.
