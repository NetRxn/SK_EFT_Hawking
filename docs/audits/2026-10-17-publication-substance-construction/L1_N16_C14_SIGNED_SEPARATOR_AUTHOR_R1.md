# Original periodic N16 c14 signed separator preflight

Candidate is the clean primary checkout at 27012c18fa374e8341e124b510abbedeedb18d29.
Input is the independently accepted exact c14 directional occupancy roster,
SHA-256 8168c8266e615be09764346a09b1fbd3e63fb94cd900b20c2b3ccc8dc1fa7254.
The row target is source-zero coupling grade g1^14 g2^4. The controls
contract only restricted products of owners of a chosen separator. They
provide no complete c14, c16 or original-run coefficient.

## Exact parity and translation

In the roster, a listed plane gives the two coframe axes. The other two
axes form the curvature plaquette. A coframe is homogeneous of degree
one across the two original directed anchors of its unoriented edge.
Each raw plaquette monomial has exactly one coordinate from each of the
four original directed anchors of that plaquette. Reversing plaquette
orientation permutes the anchor set. Every S4 factor contributes one
coframe on each axis. These assertions follow from the four signed
coframe increments and multilinearity of the actual ordered link
product and trace. The probe additionally checks both orientation anchor
incidences and degrees of the source monomials at the exercised owners.

For a fixed roster row, negate all four chiral quaternions belonging
to the two directed anchors of any one edge. These are four independent
measure-preserving transformations of normalized S3. This multiplies
every contribution by the same sign, given by the parity of the
combined edge degree. Any odd degree annihilates the entire row after
Haar integration. The cut preserves all four exact coordinate powers
and independent anchor identities in any subsequent contraction.

| Center multiplicities | Occupancy rows | Killed by edge parity | Even on every edge |
| --- | ---: | ---: | ---: |
| (1,1,1,1) | 96 | 96 | 0 |
| (2,2) | 1,776 | 1,776 | 0 |
| (4) | 96 | 48 | 48 |

The 48 rows give three periodic translation orbits of size 16, rooted
at site zero with doubled plane pairs 01/23, 02/13 and 03/12 and divisor
512. Periodic translation commutes with the steps and preserves each
signed quarter increment, each plaquette orientation and the actual
anchor and chirality labels. It permutes the independent Haar factors.
On the full exterior coefficient it permutes eight-generator site
blocks, with sign +1 because swapping blocks contributes (-1)^64.
Translation preserves the factorial divisor. Thus after contracting the
three representatives their weighted contribution can be summed with
multiplicity 16. The source control checks one nonidentity translation
across a periodic boundary against 408 raw factors, 49,176 coefficient
rows (including the 24 scalar S4 rows), and 64 signed quarter blocks.
An axis identification would require a distinct proof of transport of
the chiral and orientation conventions.

## Exact signed controls

The separator consists of both directed axis-0 anchors at ranks 0 and 8,
including both chiral factors on each. The probe finds every owner
occurrence of those anchors from the full original row before selecting
the restrictions. All factors outside the owner list have zero
incidence to the separator. For each selected owner it fixes a component
tuple, a generator mask and exact coordinate key per coframe, and one
exact trace coordinate key. This is a literal restriction of the
product, and the resulting open Grassmann mask and quaternion key are
reported. Different controls can have different fixed restrictions.
The observed numbers omit unrelated factors and global exponential
divisors.

The canonical route adds the signed ordered S2 coefficients for the
same even coframe word and uses the existing exterior product.
The comparator independently traverses the matching raw orientations
and the actual raw BlockIncrement entries in their original coframe
order. It computes the sign by counting inversions of the literal
ordered Grassmann word and uses pairs of Python fractions for the exact
complex arithmetic. Both routes preserve the full q key until every
selected owner has joined, then integrate the separator using independent
moments for each directed/chiral block.

| Control | Raw ordered paths | Pre-Haar coefficient | Haar multiplier | Open coefficient |
| --- | ---: | ---: | ---: | ---: |
| Four distinct centers, same anchor with q0² | 4 | -i/2048 | 1/4 | -i/8192 |
| Four distinct centers, split q0 over reciprocal anchors | 4 | i/2048 | 0 | 0 |
| Two paired centers, odd q0³ | 16 | i/16384 | 0 | 0 |
| One center, repeated planes with q0²q1² | 256 | 1/4096 | 1/24 | 1/98304 |

The reciprocal negative would produce multiplier 1/4 if the two directed
anchors were incorrectly identified. The positive mixed moment contains
two coframe and two curvature contributions to the same anchor/chirality.
For each S2 operand all four matching raw orientations contribute to
the selected restricted trace key.

The prospective caps were two million charged restricted operations
and 8,192 rows per materialized restricted table. A normalized scalar
payload ceiling of 2,048 total bits was checked per scalar. The run
charged 842 operations, had at most four rows in a restricted operand
table and one canonical output row, and observed 30 bits in a scalar.
The source enumerators construct the original action/coframe inputs
separately and are outside these restricted-operation counts.
The first shell Python lacked NumPy. The exact control used the primary
checkout's existing environment.

## Next substantive contraction

Each surviving representative has exactly 24 degree-two and eight
degree-four unoriented edges. Start by integrating individual edge
tensors before exterior site closure. An edge's labelled Haar legs
must retain direction, chirality and quaternion component. The joint
support of the Haar tensor has at most 16 nonzero assignments at
degree two and 736 at degree four. At degree two, the two legs must
match in one of four anchor/chirality blocks and one of four
coordinates. At degree four, either all four legs land in one block
(160 choices across the four blocks) or they pair across two blocks
(576 choices). These counts precede gamma, coframe direction, wedge and
other source filters.

Compile the actual quarter-increment weights and signed original
plaquette trace incidence onto those edge tensors. Contract first a
complete degree-four edge and one adjacent site's eight-generator
exterior closure, carrying signed open spin/coordinate state and its
coefficient budget. Compare that unrestricted local cut against raw
source on a frozen smaller cut before admitting a larger representative.
Keep the three axis arrangements distinct. The present tests establish
exact signed seam controls and the orbit reduction, and leave the full
representative contraction and its feasibility budget open.
