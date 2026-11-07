# Independent finite Haar polynomial proof review

**ACCEPT** for the finite polynomial transfer, residual coefficient
accumulation and existing symbolic specialization at
`fc087cfb99afe4740522b50d8c9644edf6716d14`, parent
`07d76dc9eede4a6455e30a27ae2a090178da5d47`. The clean commit adds only
`lean/SKEFTHawking/ADW/QuaternionSU2HaarPolynomial.lean`, SHA-256
`07de25befa5dbfb07ac4bc55c0a49ec4522bec34851f34a971d9ea3baf9499b6`.
Intake and terminal continuity checks both matched.

- The proof integrates against the original `linkHaar`, the finite product
  over sites and forward directions of `spin4Haar = su2Haar.prod su2Haar`.
  The anchored coordinate uses the actual left or right chiral group
  matrix and its existing plus-i coordinate inverse. `Finsupp.prod_pow`
  preserves every quaternion power when invoking the already accepted
  complex monomial theorem. The moment factors use the full
  site, direction and chirality key.
- `contract` is complex-linear on arbitrary finite multivariate polynomial
  support. The exponent equivalence separates the quaternion and residual
  arms. `coeff_contract` sums over all source exponents with the queried
  residual exponent, preserving collisions and cancellation. The
  integration identity expands the exact support, establishes continuity
  for each summand on the compact link space and uses finite integral
  linearity and the complex monomial identity. No degree restriction or
  sampled equality appears in the theorem.
- The shared-link theorem uses the same evaluation at both factors, then
  contracts their product. The first moment vanishes and the square is
  one quarter. The cancellation theorem gives an exact zero after two
  different quaternion powers project to the same residual exponent.
- `contractSymbolic` reassociates the existing
  `h ⊕ (J ⊕ q)` variable type to `(h ⊕ J) ⊕ q`. Its theorem uses the
  existing `specialize` map, arbitrary real auxiliary values and arbitrary
  complex source values. The ring-hom equality checks constants and each
  variable arm. The generic residual type can distinguish a source and
  its conjugate as separate labels. The specialized source arm is the
  existing original h/J model.
- The independent Python oracle uses the exact factorial formula for the
  Dirichlet moments of the four squared sphere coordinates. Ten explicit
  checks, 64 seeded exact complex polynomials and 96 actual assembled
  Dirac entries agree with the corresponding production Haar operations.
  On the checked four-site assembly, the actual Python symbols use
  `h/J` on auxiliary triples and `q` on site/direction/L-or-R/coordinate
  quadruples, with no conjugated source symbol. These bounded controls
  supplement the source audit and the mathematical identity.
- The supplied ROOT kernel receipt binds the exact commit and path.
  I independently compared the complete public declaration roster and
  all 11 diagnostic lines. Each declaration reports exactly
  `propext`, `Classical.choice` and `Quot.sound`. The added source has
  no proof placeholders, native decision procedure, extra axiom or
  proof heartbeat override.

A formal correspondence from the full executable producer into the
symbolic polynomial, actual Eq11 coefficient assembly, native absorption
and publication closure remain open. Review was source inspection and
exact Python testing. ROOT supplied the matching kernel evidence.
