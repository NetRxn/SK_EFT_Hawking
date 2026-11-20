# Independent Eq11 perturbation coefficient source review R1

**ACCEPT exact source commit `096befa1afd37e9ed46805902fa5e168bec9f48e`**
for the generic coefficient increment. Its parent is
`db527ae05268a0ea0f5ee534847d32dc356bc968`. The complete commit adds
only `lean/SKEFTHawking/ADW/PolynomialPerturbationCoeff.lean`. The
file SHA256
`88ced02b832b6967b35f43f90b24e88068e6edf14cb468e70fa7f781b205bf56`
matches the live leased file. The exact Git whitespace check passed.

`coordinatePerturbation` is a ring homomorphism using
`MvPolynomial.eval₂Hom Polynomial.C`. It fixes coefficients and maps
coordinate i to its base value plus the formal increment only when
i=a. The constant coefficient theorem has the exact evaluation at
the unperturbed base. Its proof uses the constant, addition and
multiplication-by-X branches of `MvPolynomial.induction_on`.
The first coefficient theorem uses the same induction and
`Polynomial.mul_coeff_one`. That product coefficient is exactly
the Leibniz expression using the proved constant coefficient,
and the variable derivative branches match `pderiv_X_self`
and `pderiv_X_of_ne`.

`twoCoordinatePerturbations` maps original coefficients to constant
inner polynomials and uses a base with the b-increment already
present in the inner ring. It then adds the a-increment in the
outer ring. Thus extracting outer coefficient one differentiates
in a while the inner increment remains formal, and extracting
inner coefficient one differentiates that result in b. The source
proof uses `pderiv_map` to commute coefficient embedding with
the partial derivative, and `eval_map` to recover exactly the
single-perturbation substitution at the inner level. The conclusion
is `eval x (pderiv b (pderiv a P))`. No switch of derivative order
or commuting-partials assumption is used. Both indeterminates remain
independent when a=b. In particular the quadratic repeated-coordinate
coefficient is two, with no division by a factorial and no missing
factor of two.

I independently enumerated coefficient choices on X³Y at base (2,3).
The mixed coefficient is 12, the repeated X coefficient is 36,
and repeating Y gives zero. The zero-base quadratic repeated
coefficient is 2. This discriminates a two-direction extraction
from one-variable coefficient two, which would give 18 and 1 in
the nonzero repeated cases.

The only assumptions are `[CommSemiring R]` and
`[DecidableEq ι]` for the coordinate branches. There is no finiteness
restriction on the variable type, no characteristic-zero or field
premise, no bound on degree, no distinctness requirement, and no
determinant or weight nonvanishing premise. The module contains no new
axioms, admissions or placeholders. This was a read-only exact source
review. ROOT's diagnostics and axiom results are separate evidence.
The actual determinant/Grassmann coefficient correspondence, source
measure transport and weighted printed/closed insertion wrappers
remain separate proof increments.
