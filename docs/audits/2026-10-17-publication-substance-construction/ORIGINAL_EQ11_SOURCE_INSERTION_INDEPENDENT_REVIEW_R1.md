# Independent original finite Eq11 source-insertion review R1

**ACCEPT the exact source increment for finite undivided Eq11 at orders
zero, first and ordered mixed second, including the diagonal.** This is
source and scientific statement acceptance. ROOT owns the independent
kernel replay, import, native build, and delivery decisions.

Commit `ba5846ebc416e07ee2dfa3c106f4f926203febfa` has exact sole parent
`0ce96127c1b76af607faefa34d9ac9e6d297cf2d` and adds only
`lean/SKEFTHawking/ADW/FiniteGrassmannSourceInsertion.lean` (367 lines).
Git blob SHA-256 is
`2f16db2350844ad62d09f7b730a44009d61bfec67140bd7613849ed6a2799b12`.
Git whitespace check passes. Both imports are the existing independently
reviewed shifted determinant and Gaussian-Haar polynomial Stein modules.
I compared the exact declarations against the pinned Eq7/10, pointwise
Berezin and weighted transfer source, plus the weighted insertion design
and the composite report §§1–3, 5–6. No new matrix, action, Gaussian
variance convention, link measure or Berezin orientation appears.

## Fifteen theorem checks

| Exact theorem | Independent semantic check |
|---|---|
| `sourceWeightHaarPolynomial_eval` | Evaluation of the product over all sites yields the original `fullWeight` with its original global cutoff in every site compensation. Its source input S depends on U and the original couplings, and there is no J argument. |
| `sourceInsertionDensity_eval` | The factors are exactly 1, T_a and T_a T_b. Their density multiplies W by the shifted determinant or its appropriate partials. At every real h and link U the original Grassmann insertions are evaluated at complex h+J. No source, conjugation, derivative, or compensating factor is inserted into W. |
| `sourceInsertionDensity_integrable` | The actual joint polynomial bound applies to the full density, including all continuous link coefficients and finite Gaussian moments. The product measure has Haar first and the original Gaussian second. |
| `sourceInsertion_fixed_link` | The private proof applies the actual continuous linear map G ↦ berezin((I E_J)G) to the integrable original Eq7 Grassmann integrand. The fixed link U is arbitrary. The two linear coframe sums have zero constant coefficients, so their same-cutoff exponentials multiply by the original joint nilpotence theorem. Scalar W passes through complex linearity. The Grassmann products are associated with I on the left, and no general commutation assumption is used. |
| `sourceInsertionValue_integrable` | Joint integrability implies integrability of the inner integral as a function of the outer link, and the everywhere fixed-link equality transfers this to the original Berezin value. |
| `sourceInsertion_eq11` | The original link-integrated insertion equals the integral of the full density on the same product measure by Fubini plus the fixed-link identity. |
| `sourceInsertion_iterated` | Derives both Haar-outer/Gaussian-inner and Gaussian-outer/Haar-inner orders from that exact joint integrability, including every insertion case. |
| `sourceInsertion_eq11_adjoint` | The zero case is identical; first transfers d_a using A_a. Mixed d_b(d_a D) invokes the existing theorem with (b,a), so W becomes A_a(A_b W). No derivative order is silently exchanged. |
| `sourceInsertion_mixed_adjointWeight` | The expansion is (q² X_b X_a − q delta_ba)W − q X_b d_a W − q X_a d_b W + d_a(d_b W). It retains both weight gradients, the full second derivative and the negative contact only at b=a. q=(σ²)⁻¹ with σ cast into ℂ. |
| `sourceInsertionValue_eq_nilExp` | The original coframe source polynomial for J and the globally renamed sum of S have zero constant coefficient. Applying the exact commutative even-carrier exponential law and then inclusion proves the equality with the actual single combined cutoff exponential, under the same ordered insertion. |
| `sourceInsertionValue_zero` | J=0 makes the coframe linear source zero and the exponential one. The zero insertion factor is one, so the original source-word integrand is recovered. |
| `sourceInsertionDensity_zero` | The zero derivative selector and exact zero translation reduce the density to the previously used Eq10 polynomial with precisely the same W and determinant. |
| `sourceInsertion_eq11_zero_eq10` | Combines the preceding exact reductions and original polynomial evaluation to yield the same Eq10 integrands and joint measure. With `sourceWordExp` unfolded this is the statement of `original_eq10`; both word specializations use the witnesses of their corresponding original Eq10 theorem. |
| `printed_sourceInsertion_eq11` | Instantiates the actual `printedSource`, with its printed curvature and own zero-constant and continuity proofs. Both direct and transferred equalities are present for arbitrary complex g1, g2 and J, and all three selectors. |
| `closed_sourceInsertion_eq11` | Instantiates the independently retained `closedSource`, its closed curvature and distinct witness paths. Both direct and transferred equalities are present for the same full ranges. |

The adjoint right-hand integrand is also a `HaarPolynomial` evaluation
on the same product measure, so joint absolute integrability follows
from the existing generic bound. The earlier weighted-transfer module
states both sides' integrability for first and mixed second explicitly.
The two-orders theorem above states the direct form. The transferred
form can use the same product-integral rule with its own integrability
witness. No assumption that W, D, or the undivided integral is nonzero
or positive occurs.

Independent exact moment controls in the adjacent controls JSON give
first and diagonal second values both 8 at variance 2. Dropping the
negative diagonal contact changes the second result to 18. The
off-diagonal control gives 20−8−8+4=8, with no diagonal contact.
Zero-partition controls preserve a nonzero first insertion, including
the 2i complex-source phase. These are mechanism controls at exact
scalar inputs, separate from lattice coefficient execution.

The proved algebra is the finite unnormalized original coframe
insertion transfer recorded in the composite report's equations (9)
and (10). The explicit `sourceInsertionValue_eq_nilExp` identifies the
original complex source and Grassmann product. The standalone
coefficient theorem for an integrated generating polynomial in J,
formal complementary-minor correspondence to the executable
coefficients, and an exact actual-lattice comparison with the saved N16
raw coefficients remain separate. The current identities also leave
higher orders, numerical full Z, a nonzero normalization domain,
connected and local Legendre response (the composite report's separate
equation (11)), susceptibility calibration, physical/continuum
validation and publication gates open.

Both continuity checks report SAME. The review made no repository
or slot mutation and performed no Lean or aggregate build.
