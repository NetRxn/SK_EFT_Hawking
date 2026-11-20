# Independent review of the pure-EHC directed-square pilot

**ACCEPT for the single signed representative** `(37086699520,8935831015554)`
at orbit weight 48. Independent exact contraction gives
`43150358914340032656914557421875/510015580149921683079168`.
The coefficient times its orbit weight is
`43150358914340032656914557421875/10625324586456701730816`.

Continuity checked fresh at the pinned primary candidate and the four frozen
input manifests, plus both nested historical manifests, verified. The prior
coframe, adjoint, product representation and bivector exports agree between
the author and independent predecessors. The audit reused those established
literal source exports and the preceding independent ordinary/mixed signed edge
tables. The new root Fourier projection, special spatial expansion and network
sewing were replayed independently.

## Source, projection, orientation and signs

The prior original-occupation roster has the unique row at weight 48.
Decoding gives the four quartics at A sites 2–5, all on spatial axis 0, and
one quadratic at each B site. Running the two-chirality support constraint
forces the four A quartics and the four odd-site B quadratics to scalar.
The four nontrivial candidate roots left in B are the actual directed cycle
0→4→6→2→0, of spatial axes 2,1,2,1 in cube indexing. Every selected
edge has exactly one root of power two. All four representation possibilities
remain at each of those roots.

The closed source word reverses the listed factors of the forward plaquette
and therefore gives a_r† V_next† b_r V_r at each oriented root. Original anchors
on an L=2 pair are distinct, including for arrows rooted at the larger site
label. Expand a root as sum F[i,j] D(H)[i,j]. In a fixed channel, writing the
original matrix elements as A†[i,l] V_next†[l,m] B[m,n] V_r[n,j],
integration with the previous root identifies n with its m and j with its l.
Thus current B's row connects to next B's column. Its column lies at the
root and row lies at the destination. In the own trace F takes the outgoing
column index i as its first index, and incoming row index j as its second.
The surviving A†[i,l] is conjugate of A[l,i]. Those constraints give opposite
trace orders and d^-4 in dimensions 1,3,3,4. They are derived with the original
spatial variables retained, including when the coframe owner differs from
the plaquette anchor.

The cross-layer root Fourier tensor was reconstructed as
d × Haar(literal quadratic × conjugate(D[i,j])) on two independent S³ factors.
The 702 coefficients agree exactly with the frozen projection. The same
chirality quadratics split into scalar plus spin one (dimensions 1 and 3),
and the left/right cross term has dimension 4. Whole-root world signs square
to one in this case. The other roots reduce by moments of the projected
linear trace. For exactly one nonzero orthogonal bivector coefficient in each
chirality, the normalized Haar averages are 2 times the Gram square and 10
times the Gram fourth power, since E(q_i²)=1/4 and E(q_i⁴)=1/8. In fact
E[(2q_i±2r_j)^4]=2·16/8+6·16/16=10. The same expressions extend by
polarization to the scalar Gram polynomials. Retaining every original
multiplicity divisor gives 10^4·2^4/(4!^4·2!^8)=625/331776.
The four non-scalar-capable quadratics contribute via the complete tensor,
including its scalar channel, so none gets an extra factor of 2.

Each coframe supplies one generator at each endpoint and a quarter factor.
Every live integrated edge has even degree d=2 or d=4. Passing even endpoint
blocks across each other preserves sign when grouping by site. Within a site
one must count inversions of the ordered, disjoint masks to reach the local
eight-generator top. The independent sewing counts those inversions directly.
Special Haar scales are 192·4^d, because normalized degree-four and degree-six
coordinate moments, on the distinct groups labeled by anchor and chirality,
have denominators dividing 192. Ordinary scales are 64 and 12288.

## Independent exact channel results

| Representation | Opposite spatial layer | Own spatial layer | Complete scaled contribution |
| --- | ---: | ---: | ---: |
| Scalar | 12948662480625/67108864 | 30509142075/131072 | 3048245241532485029296875/36028797018963968 |
| Left spin one | 2428936875/2097152 | 4253517961/603979776 | 2952539615897265625/15564440312192434176 |
| Right spin one | 2428936875/2097152 | 4253517961/603979776 | 2952539615897265625/15564440312192434176 |
| Left × right fundamentals | 4554256640625/4294967296 | 86307275961/4194304 | 3032912690429310791015625/18889465931478580854784 |

Imaginary accumulators remain exact and each fully contracted layer is real.
Reverse network scheduling and conjugating all tensors independently reproduce
the same result. Omitting only the own-side spatial conjugation yields
`1598205430059242490151906640625/18889465931478580854784`.
Omitting the B-site 0 wedge sign yields
`98542793700490987350390625/7782220156096217088`, matching the frozen mutant.

## Prospective resource bounds and findings

- The author's fixed-input spatial log is a measured receipt. In frozen
  `square_signed.cpp` the raw 50M flag is printed after computation, so the
  original driver itself does not prospectively enforce that work cap. The
  reviewer counted from parity bucket histogram sizes before expanding any
  signed products. For the original quartic pairing the largest raw-monomial
  work and cached-coordinate work are 43,266,176 and 14,198,720, respectively.
  Both prospectively fit 50M. The distinct quartic pairing would require
  59,801,856 raw work and only 19,811,712 cached coordinate products. The
  reviewer executed the cached schedules only. Both schedules reproduce all
  207,296 signed spatial rows byte-for-byte under UBSan. The two replays
  stream one coordinate-pair accumulator at a time under a 150,000-key
  guard. A conservative coefficient-mass bound is below 2^57, from at
  most 64² unit coefficient products per pair, Haar numerator scale at most
  192, and fewer than 2^25 cached candidate products per block.
- All 70,448 spatial representation-matrix rows match after separate
  assembly. The frozen matrix receipt shows at most 47,332 allocated keys
  per owner/anchor/degree block and 161,104 matrix assembly products.
  The author's site-complement work cap is checked incrementally before
  each batch. The independent implementation plans all batches at the site
  before executing any. The frozen site trial maximum is 6,368.
- The frozen greedy join and closing triangle use prospective product and
  coefficient-height bounds. For the primary schedule the recorded maximum
  ordinary or closing work is 239,616, the maximum populated factor is
  6,272, and the maximum triangle resident input is 14,192. These are
  observations for this pilot. They do not establish general schedule
  admission. Even using 2,744,000 dense interface rows as an upper bound
  for this shape, that dense allocation still exceeds the configured
  150,000 limit.

The accepted result adds one exact signed orbit, covering 48 occupations
inside the temporal block. Subtracting its existing weight from the
preceding exact remainder leaves 10,457 orbits and 903,771 labels in the
same block, provided the ledger records this pilot once. The full block,
other shapes and source words, full c0 value/sign/nonvanishing, and all
native or publication gates remain open.

## Commands

Run from this scratch directory with its frozen package links intact.

```sh
clang++ -I "$PWD/AUTHOR" -std=c++20 -O3 -Wall -Wextra -Werror -fsanitize=undefined spatial.cpp -o spatial
clang++ -I "$PWD/AUTHOR" -std=c++20 -O3 -Wall -Wextra -Werror -fsanitize=undefined spatial_original_schedule.cpp -o spatial-original
scratch=$PWD
(cd AUTHOR && "$scratch/spatial") > signed.tsv 2> spatial.out
(cd AUTHOR && "$scratch/spatial-original") > signed-guarded.tsv 2> spatial-guarded.out
cmp signed.tsv frozen/square-signed.tsv
cmp signed-guarded.tsv frozen/square-signed.tsv
PYTHONDONTWRITEBYTECODE=1 python3 project_root.py
for mode in ordinary reverse all-conjugated missing-conjugation omit-wedge; do
  PYTHONDONTWRITEBYTECODE=1 python3 sew.py "$mode"
done
shasum -a 256 -c manifest.sha256
```
