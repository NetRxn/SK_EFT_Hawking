# Independent anchored Haar shifted determinant and raw jet review

**ACCEPT** the exact scoped assembly proof at
`02dffda6133710a940d5944883f59fcec12d3c35`, parent
`abef78af0ec5397a7c3f3bf65e0af6b012661f12`. The only changed path is
`lean/SKEFTHawking/ADW/QuaternionSU2HaarAssembly.lean`, SHA-256
`eeb103bc2aa2609fad86a451eb1ecdbe3079cb3b43b0d271cb15c58339e376be`.
The candidate is clean and its patch passes whitespace verification.

## Source review

- The original Haar variable is an actual `Links L` value. The proof obtains
  unit norm for both chiral blocks from `unit_coordinates` and reconstructs
  each block by `block_coordinates`, then extensionality reconstructs every
  site and direction. The integration uses the existing `linkHaar L`.
- The determinant uses `twistedLinks` on the original carrier. Its established
  central sign acts on both chiral blocks at each wrapping forward link and
  supplies the same real sign to the reverse hop. The axis equivalence
  transports only the gamma index. The complex shift uses
  `J ∘ (sourceCoordinate L axis).symm` and the determinant polynomial is
  renamed by that same inverse. The derivative theorem takes the physical
  derivative at the forward-transported label, as required by that rename.
- `specialize_pderiv` preserves the differentiated auxiliary variable and
  evaluates the source and quaternion variables at constants. The generic
  contraction derivative theorem proves the commutation monomial by monomial
  and retains the entire quaternion exponent. This is a polynomial identity.
  It covers distinct and coincident labels without determinant division.
  Differentiation uses the retained h arm of the h+J source shift at arbitrary
  complex J.
- The actual raw determinant program is connected by
  `shiftedAssembly_rawJet` and `polynomialJet_eq_select`. The four recorded
  integrals represent value, first outer, first inner and second. The order
  uses the two positional indices even when their coordinate labels coincide.
  The integrated result is evaluated on the contracted symbolic determinant
  at the original h/J pair. The periodic identity-axis corollary removes the
  label transport, and the final example keeps a nontrivial axis swap,
  wrapping sign and coincident labels in the four-slot theorem.
- ROOT's kernel receipt binds the exact commit. The 11 public declarations
  match the source roster, and all 11 information diagnostics list only
  `propext`, `Classical.choice` and `Quot.sound`. The exact check reports success.

## Independent exact executable controls

The scratch Python control uses the original constructors and exact rational
complex arithmetic. It checks four chiral coordinate round trips with
nontrivial rational unit quaternions. A two-site matrix equality checks the
paired boundary signs and gamma-label transport, including an extent-one
self-wrap. Removing either the wrap sign or the gamma transport changes the
matrix. The two-site probe uses the executable metric convention's
non-involutive (3,0,1,2) axis map.

On the one-site four-by-four assembly with nonzero imaginary source shifts,
independent signed permutation expansion reproduces the production
determinant. The direct control counts derivative multiplicities on
monomials and integrates each anchored quaternion factor by the exact
Dirichlet factorial formula. All eight ordered derivative/convention
cases agree with the four production raw slots and with differentiation
after contraction. Both repeated labels and both orders of distinct labels
are exercised in each gamma convention. First derivatives in h and J
agree at the tested h+J shifts. The code and exact values are frozen.

## Boundary

This is acceptance of the original-carrier determinant and raw jet transfer.
Formal full executable producer correspondence, compensated Eq11 source
assembly, physical normalization, native absorption and publication
qualification remain separate. Intake and terminal continuity matched.
All writes were private scratch evidence.
