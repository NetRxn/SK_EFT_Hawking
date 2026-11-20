# Independent original weighted Eq11 Stein source review R1

**ACCEPT exact source commit `dd07bcfef48c6eb973e8ddd49121af5c77be96a3`
for the approved scalar increment.** Parent is
`25b5f229ce3f518ac08a9279f1680f2068cd4a4c`. The complete commit adds
only `lean/SKEFTHawking/ADW/GaussianPolynomialStein.lean`.
Its SHA256 `0b98ff4bb84daeed13d52281c87a20c54a3c8478eb43ae8e4db490366a0cdbe5`
matches the live leased file. The Git whitespace check passed and the
pinned source and index were clean.

Both public declarations live under `SKEFTHawking.ADW` and retain an
arbitrary finite coordinate type, arbitrary complex coefficients, real
coordinates, positive real scale σ and the exact variance relation
`(v : ℝ) = σ ^ 2`. The measure is precisely
`Measure.pi (fun _ : ι ↦ gaussianReal 0 v)`. The imports are exactly the
agreed complex auxiliary transform and Mathlib polynomial partial
derivatives. The statement has no coordinate cardinality lower bound,
no degree truncation and no positivity or reality requirement on P.

`integrable_gaussianPolynomialEval` proves absolute integrability of
evaluation by genuine monomial induction. The monomial branch reconciles
the exact support product with the full finite product, uses the existing
zero-Hermite integrability result, and multiplies by the actual complex
coefficient. Addition preserves integrability by pointwise evaluation.
For `integral_gaussianPolynomial_pderiv`, the weighted right side is
itself integrable by evaluating `X a * Q` and multiplying by σ⁻².
The left side is evaluation of an ordinary finite polynomial. The
addition step invokes integral additivity with both integrability
obligations established.

The coordinate-moment helper starts from the exact singleton Hermite
insertion h_a/σ. Splitting its product factors gives the factor
σ d(a) times the lowered product moment. Multiplying by σ gives
σ² d(a), with the variance normalization carried by the existing
Hermite theorem. When d(a)=0, the descending factorial is zero;
there is no division by d(a), a moment, or any polynomial value.
The final monomial step uses Mathlib's actual `pderiv_monomial`
with exponent d−single a 1 and coefficient c*d(a). All inverses used
in the field calculation come from σ>0. The resulting transfer has
the exact positive sign and σ⁻² normalization, with no complex
conjugation and no altered measure. It supplies the scalar lemma
needed for the later weighted Haar transfer.

I reviewed the full proof and exact pinned source read-only. There are
no new axiom, admission or placeholder declarations in the module.
The author's reported exact file diagnostic pass and standard-axiom
outputs are separate worker evidence. I did not invoke Lean or a
controller or perform a build. Aggregate registration, authoritative
build and absorption remain ROOT's responsibility. The weighted Haar
adjoint, both original printed and closed source-word insertions,
diagonal contact, determinant coefficient correspondence and remaining
scientific obligations are distinct next increments.
