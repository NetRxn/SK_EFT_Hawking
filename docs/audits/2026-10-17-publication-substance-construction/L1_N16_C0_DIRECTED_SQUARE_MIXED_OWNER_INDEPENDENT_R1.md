# Independent mixed-owner directed-square review

**ACCEPT** the 28 B-core same-direction single-root quadratic square
representatives in `reviewed-exact.tsv`, including the three whose original
untiled schedules refused. The 2,544 original labels contribute
`41101994788076062939485274495683/73786976294838206464`. Removing precisely
these 28 from the preceding temporal residual leaves **10,382 orbits and
897,147 labels**.

The selected class requires at least one (2,2) mixed-owner coframe load on
the opposite side of the directed temporal cycle. The independent census
also found 14 A-core representatives with the mirrored condition, covering
1,152 original labels. They remain in the residual and are recorded separately
in `both-core-census.out`. The full original c0 sign, value and nonvanishing
remain open.

## Frozen inputs and reconstructed tensor

The continuity check returned fresh. The original frozen review, nested
spatial and pilot manifests, and the separate author recovery manifest
verified. The accepted residual was extracted from the clean pinned
publication checkout at `9dca03a9a`. It agrees exactly with the preceding
independent residual after removing the 42 accepted same-owner rows.

From the matched literal original coframe exports, the independent native
generator groups each same-owner quadratic by its exact ordered exterior
mask and coordinate parity. For each left mask it enumerates the 225 masks
with two generators per endpoint drawn from the two complements, then looks
up the right quadratic with the required coordinate parity. The two owner
component words remain separate. Wedge inversion sign restores the canonical
order of the final four generators per endpoint. The sixth-degree Haar
moment uses four independent S³ variables indexed by actual anchor and
chirality. Those sectors are never merged.

The owner-major exponent ordering and independent complement search reproduce
all 404,480 signed moment rows byte-for-byte under UBSan. On each anchor,
the hypothetical raw source expansion has 62,720,000 matched products,
above the 50-million cap. Coordinate-pair caching with prior mask
disjointness requires only 21,305,856 matched products, prospectively
checked before accumulation. Its largest coordinate pair uses 1,744,768
products and 15,840 allocated rows. A prospective Gaussian-integer mass
check uses the safe bound `192 * 64^4 * cached_products < 2^62`.

Independent assembly reproduces all 204,320 representation-matrix rows.
Each anchor and channel is planned separately. The largest planned assembly
has 272,384 signed products and no accumulator exceeds 78,336 allocated
keys. In each anchor's scalar channel, summing the four q_i² coordinates
of the same selected chirality is the unit-sphere identity. The 3,952
assembled scalar rows agree exactly with four times the prior ordinary
mixed table, since the present scale 192·4⁴ is four times 12,288.

## Signed contractions and initial refusals

The independent projection decodes every accepted residual occupation,
checks both chirality supports, verifies one collection of four directed
arrows closing on distinct vertices, and checks original coframe loads on
both layers. The 28 B-core entries, weight, arrows, scalar-forced powers and
mixed-edge counts match the frozen author roster exactly. Each own layer
uses the original dagger conjugation and each local join retains its
eight-generator inversion sign. Projected scalar moments, original
multiplicity factorials, and the complete channel Schur factors d^-4
are retained.

A separately run guarded direct probe reproduces the two initial refusals
before 5,103,040 joined products and the third before appending the edge
(5,7) to a resident set exceeding 150,000 rows. These are refused schedules.
The reviewer replays the 25 initially exact author cases directly.

For each refused case the independent schedule splits the opposite spatial
trace over the second and fourth vertices of its ordered cycle. The author's
recovery fixes the first and third vertices instead. A complete opposite
trace has one ordinary representation index at each vertex. Imposing its
fixed value on both incident edge states and the local equality factor gives
a unique tile for every full assignment. Distinct combinations are disjoint
and their union exhausts the two vertex index domains. Every nontrivial
channel is reconstructed by nine, nine, or sixteen exact tiles, respectively.
The original spatial Haar and d^-4 remain unchanged by this finite expansion.
The scalar channel is evaluated directly.

All 112 reconstructed channel contributions and 224 constituent layer values
agree with the separately frozen author results. Every final representative
is positive. There are 25 weights of 96 and three weights of 48. The numbers
of mixed edges per representative are one in 18 cases, two in six, three
in one, and four in three.

| Original occupation | Independent tiled coefficient |
| --- | --- |
| (279173406850,40210711025225) | 2012126439283695835060248430625/2361183241434822606848 |
| (279173406850,40210715152985) | 2012126439283695835060248430625/2361183241434822606848 |
| (8935713546370,40210711025225) | 316666352905758389478307946373/36893488147419103232 |

The accepted independent schedules use at most 7,680 site complement
trials, 34,832 populated factor rows, 119,952 initial resident rows, and
1,728,000 matched operations in any ordinary or closing join. The author
receipts separately show maxima of 737,280 ordinary matched products,
1,728,000 closing work, and 86,400 closing resident rows. The reviewer
checks site product counts, initial and populated row limits, join or
closing work, and the conservative coefficient-height bound prospectively.
Other temporal orientations, core shapes, and native and publication
acceptance remain outside this receipt.

## Reproduction

The scratch directory expects the frozen literal-table trees at `AUTHOR` and
`INDEPENDENT`, the prior reviewer exports at `root.tsv` and `spatial.tsv`,
the previous independent residual and signed increment at
`prior-batch-residual.tsv` and `prior-extension-exact.tsv`, and the frozen
author input root at `frozen`. The accepted residual is the
`block-remaining.tsv` member of the checkpoint's
`L1_N16_C0_DIRECTED_SQUARE_SAME_OWNER_R1.zip`.

```sh
clang++ -I "$PWD/AUTHOR" -std=c++20 -O3 -Wall -Wextra -Werror -fsanitize=undefined mixed.cpp -o mixed
scratch=$PWD
(cd AUTHOR && "$scratch/mixed") > mixed-signed.tsv 2> mixed-spatial.out
cmp mixed-signed.tsv frozen/mixed-owner/signed-mask.tsv
python3 assemble.py > mixed-assembly.out
cmp mixed-matrices.tsv frozen/mixed-owner/matrices.tsv
PYTHONDONTWRITEBYTECODE=1 python3 mixed-cohort.py census > both-core-census.out
PYTHONDONTWRITEBYTECODE=1 python3 mixed-cohort.py 0 8 > direct-0.out
PYTHONDONTWRITEBYTECODE=1 python3 mixed-cohort.py 8 16 > direct-8.out
PYTHONDONTWRITEBYTECODE=1 python3 mixed-cohort.py 16 25 > direct-16.out
PYTHONDONTWRITEBYTECODE=1 python3 mixed-cohort.py 25 28 direct-probe > refused-probe.out
PYTHONDONTWRITEBYTECODE=1 python3 mixed-cohort.py 25 28 > recovered.out
python3 compare.py > comparison.out
shasum -a 256 -c manifest.sha256
```
