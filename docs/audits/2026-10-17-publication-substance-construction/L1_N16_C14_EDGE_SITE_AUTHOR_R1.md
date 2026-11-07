# Original N16 c14 exact local edge and adjacent site contraction

The authority is the original periodic closed source_C at primary
27012c18fa374e8341e124b510abbedeedb18d29. The exact c14 roster and accepted
signed seam are unchanged. This cut takes the zero-centered (01,01,23,23)
row with divisor 512 and closes rank 8. It is a full-support *local*
contraction with an explicitly factored boundary representation.

## What is contracted

All eight Grassmann generators at rank 8 come from two coframe
occurrences on each of its four incident edges. Along axis 0 both
coframes come from the two S2 occurrences at rank 0. Along axes 1, 2,
and 3 they come from the paired S4 occurrences at ranks 12, 10, and 9.
The axis 0 and axis 1 edges have degree four. Both receive a trace leg
from each of the two original (23) S2 occurrences at rank 0. The other
two edges have degree two. All other terms of the full row have no
quaternion incidence to these four unoriented edges and no exterior
incidence to rank 8.

Each edge tensor integrates the independent normalized Haar factors at
both ends and both chiralities, leaving exact open coframe component
indices and original trace-coordinate legs. A row is encoded as
`[[rank8mask, othermask, component0, component1, trace_q0?, trace_q1?],
[real_numerator, imaginary_numerator]]`. The common denominator is
recorded per edge. The q code 0–15 denotes the lower-rank endpoint and
then the higher-rank endpoint, each with L0–L3 and R0–R3 in that order.
The trace occurrence IDs and its actual directed anchor are in
`result.json`. The two trace coordinates for a given original
occurrence, carried on different edges, are both plugged into that
same original plaquette coefficient. Its other legs remain open.
The coframe component labels plug into their original ordered trace
or S4 epsilon tensors. Unrelated action factors and the global row
factorial divisor have not been applied.

For a fixed tuple of open edge labels, sum the products of the four
matching edge slice coefficients, using the signs in
`site-factors.jsonl`. Each entry records four local two-generator masks,
the signed exterior projection, and the number of term-product visits
needed to flatten that term. These are disjoint slices per edge but
different local-mask partitions can contribute to the same open key.
All such cancellations remain defined by the exact sum. Only rank 8
is projected to degree eight and removed. The other four sites'
two-generator masks are open. Reordering pairs between distinct
site blocks has even sign, so the sign for the full 128-generator order
equals the inversion parity of the eight projected site generators.
No coefficient threshold, parity projection on open labels, or sample
restriction was applied.

## Independent checks

The primary route uses the existing canonical exterior coframes and
S3 coordinate moments. A separate route extracts every signed raw
quarter-increment entry before canonicalization, computes wedge
signs by explicit pair inversions, and computes Haar moments by
anchor/chirality-preserving Kronecker pairings. The resulting complete
sparse edge tables agree exactly. Only exact zeros after accumulation
are pruned.

The site contraction uses disjoint local-mask partitions. A separate
route exhausts all 8! literal local words and checks each ordered
partition and sign. Serialized readback additionally checks the full
128-generator wedge sign of every emitted partition, recalculates
slice counts and flat expansion cost, and independently recomputes
selected fixed open-boundary coefficients from literal wedge words.
The four smaller signed seam controls, including the mixed moment and
reciprocal-anchor false-alias negative, are frozen in the accepted
independent signed seam review.

## Counts and budget

| Edge axis | Admissible Haar coordinate tuples before coframe filtering | Exact nonzero edge rows | Common scalar denominator |
| --- | ---: | ---: | ---: |
| 0 | 240 | 14,208 | 768 |
| 1 | 240 | 14,208 | 768 |
| 2 | 16 | 48 | 64 |
| 3 | 16 | 48 | 64 |

The site has 240 nonzero signed partition terms in the factored
representation. Five fixed-boundary coefficients from serialized
readback agree and are nonzero. The original run does not evaluate
the full row. The factored output is exact as a symbolic tensor sum.
A separate flat preflight counts 2,559,967,232 term-product visits.
Processing whole partitions in lexical order would next raise that
count from 3,178,496 to 9,732,096 at masks (5,10,80,160), beyond its
4,000,000 cap. No flat products were executed.

The contraction charged 406,096 operations against its prospective
4,000,000 limit. The retained-table meter charged 74,848 cumulative
new entries across primary, comparator, and site tables against
100,000, using a conservative 512-byte accounting unit per entry
against 64 MiB. This meter does not represent measured process memory.
The five exact output streams used 715,296 bytes under a prospective
4 MiB byte cap. Checked integer real and imaginary numerators have a
prospective magnitude bound of 2^61−1 for accumulation and products.
Actual peak process RSS was 115,572,736 bytes, polled during the
contraction with an observed ceiling of 384 MiB. That ceiling is a
sampled refusal guard, not an OS hard cap. Original-source constructors
and caches, list indexing/sorting, zero-row cleanup, runtime and
readback allocations are outside the charged table or operation meters.
Source-construction memory within the contraction process is reflected
in its reported peak RSS. Readback runs separately on the bounded
serialized artifact.

## Admission boundary

The next candidate should reattach the two original shared S2 trace
occurrences jointly to the axis-0 and axis-1 slices using their actual
joint q indices. Both axes retain sizable open tables but each trace
leg has a small coordinate alphabet. Keep the result factored and
first measure sparse per-trace conditional joins and exact boundary
coalescence. Do not distribute all four edge slice products across
the boundary. The two other axis arrangements, whole representative
coefficients, c14, c0 and the full denominator remain open.
