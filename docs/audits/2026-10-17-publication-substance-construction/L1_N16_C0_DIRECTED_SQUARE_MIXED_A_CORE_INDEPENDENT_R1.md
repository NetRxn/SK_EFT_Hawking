# Independent A-core mixed-owner directed-square review

**ACCEPT** the 14 A-core mixed-owner directed-square representatives in
`reviewed-exact.tsv`. All coefficients are positive. The 1,152 original
labels contribute `94444265482534360455287322645/1152921504606846976`
to the signed subtotal. Recording only these rows leaves **10,368
unresolved temporal orbits and 895,995 labels**.

## Inputs, geometry and normalization

The continuity snapshot checked fresh. The 22-file frozen author manifest
and the preceding independent B-core manifest verified. I extracted the
residual from the clean checkpoint `3a795ab29`, which agreed with its
tracked upstream and with the preceding independent residual after
removing exactly the 28 accepted B-core representatives.

The reviewer again scanned both physical layers for every current
residual row using the original occupation decoder and two-chirality
representation support projection. Four power-two roots must form one
simple directed component with no second live core. Its own spatial
cycle edges must have degree two or four on a single owner. Its opposite
edges admit the same loads and require at least one (2,2) mixed owner.
The scan found 14 A-core cases and no remaining B-core cases in this
scope. The census matches both the preceding independent two-layer
census and the author's exact orientation, weight and scalar-root roster.
Weights are ten × 96 and four × 48. Four cases use one mixed cycle edge,
nine use two, and one uses three.

All A configurations use the actual cycle 0→4→6→2→0. The reviewer keeps
the physical tuple (A,B) in its original order, identifies A as the own
spatial layer, and applies the conjugated representation coefficients to
A's actual directed spatial anchors. The opposite B-site equality
contracts the untwisted trace with the reverse cycle order. The four
root channels use dimensions 1,3,3,4 with Haar divisors d⁴. The default
spatial tables, original root tensor and separately verified (2,2)
mixed-owner matrices cover both actual anchor choices. Every site
projects disjoint edge masks onto its local top with the original
wedge-inversion sign. Factorials of all original multiplicities and
scalar moments of all forced roots are included. Each case is an
independent network evaluation on its own occupations. No equality
between A-core and B-core signed coefficients is presumed.

## Refusal and independent recovery

The guarded direct probe reproduces the two original channel-1 refusals
before a proposed count of 7,409,664 products, over the 2,000,000 cap.
The cases are `(8935831015554,10541081071769)` and
`(8935831015554,110572205610569)`, each at weight 48. Both recover the
exact coefficient `49967180153530467548442525/1152921504606846976`.

The reviewer fixes the opposite spatial trace's representation indices
at cycle positions 1 and 3, namely vertices (4,2). The frozen author
fixes positions 0 and 2, vertices (0,6). At a fixed site both adjacent
spatial matrix states and the site equality carry the same constrained
index. Every full contraction term belongs to exactly one tile, and
the Cartesian product of the two index domains exhausts the possibilities.
The nontrivial channels execute 9, 9 and 16 tiles per recovered case.
Each tile keeps the original spatial Haar scales. Their exact sum
receives the same temporal d⁴ divisor as the unsliced trace. Both
scalar channels and the other 12 cases are evaluated directly.

The complete independent run reproduces all 56 scaled channel
contributions and 112 constituent layer values in the frozen logs. The
real sums and the supplemental author values agree exactly. Prospective
site, product, row and height checks pass on the admitted schedules.
Measured independent maxima are 6,112 site trials, 34,832 populated
factor rows, 119,952 initial resident rows and 835,584 ordinary or
closing matched products. Frozen author maxima for ordinary and
closing joins are each 835,584, and closing resident input peaks at
73,120 rows. The previously qualified spatial tensors are reused
without new accumulation in this pass.

This completes the named directed mixed-owner A/B intake class.
Other temporal orientations and core shapes, full original c0 sign,
value and nonvanishing, and all native and publication gates remain
outside this result. No repository or Lean state changed.

## Reproduction

Scratch needs the preceding independent source table trees at `AUTHOR`
and `INDEPENDENT`, the independently reviewed `root.tsv`, `spatial.tsv`,
and `mixed-matrices.tsv`, and `frozen` pointing to the author input root.
The clean checkpoint's `L1_N16_C0_DIRECTED_SQUARE_MIXED_OWNER_R1.zip`
contains the `block-remaining.tsv` copied here as
`accepted-b-core-residual.tsv`. The prior review provides
`prior-owner-residual.tsv`, `prior-b-exact.tsv` and the A rows extracted
from its two-layer census as `prior-a-census.tsv`.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 a-cohort.py census > census.out
PYTHONDONTWRITEBYTECODE=1 python3 a-cohort.py 0 14 direct-probe > refused-probe.out
PYTHONDONTWRITEBYTECODE=1 python3 a-cohort.py 0 7 > cases-0.out
PYTHONDONTWRITEBYTECODE=1 python3 a-cohort.py 7 12 > cases-7.out
PYTHONDONTWRITEBYTECODE=1 python3 a-cohort.py 12 14 > cases-12.out
python3 compare.py > comparison.out
shasum -a 256 -c manifest.sha256
```
