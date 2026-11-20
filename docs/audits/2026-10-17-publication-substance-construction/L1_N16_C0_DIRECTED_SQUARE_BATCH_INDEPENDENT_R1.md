# Independent review of five additional pure-EHC directed squares

**ACCEPT** the five new exact representative values. Every row has orbit
weight 48. The accepted pilot `(37086699520,8935831015554)` is excluded
from this increment.

| Original occupation | Directed B cycle | Exact coefficient |
| --- | --- | --- |
| (37086699520,9416749883529) | 0→2→6→4→0 | 43150358914340032656914557421875/510015580149921683079168 |
| (279173406850,41327402455625) | 4→6→7→5→4 | 754550924457308069087169494375/885443715538058477568 |
| (279173406850,41327406716505) | 4→6→7→5→4 | 754550924457308069087169494375/885443715538058477568 |
| (279173922820,40210711025225) | 0→2→3→1→0 | 43150358914340032656914557421875/510015580149921683079168 |
| (279173922820,40210715152985) | 0→1→3→2→0 | 43150358914340032656914557421875/510015580149921683079168 |

The new 240-label signed subtotal is
`332897913905946331186387643261875/3541774862152233910272`.
After exactly one subtraction from the accepted-pilot residual, the
temporal block has **10,452 unresolved orbits and 903,531 labels**.

## Roster and exact replay

The continuity check returned fresh. The ten-file frozen batch manifest
and the accepted pilot's independent manifest verified. The checkpoint
checkout was clean at `a95c3d160`. Its portable archive's exact residual
agrees row for row with the frozen prior residual after removing solely
the accepted pilot. The five new rows are unique members at their
original weights.

The reviewer independently loops over all 10,458 earlier residual
orbits, using the original independent occupation decoder and both
chirality representation-support constraints. It selects one surviving
component in one layer, requires four single-root quadratic edges,
walks the actual outgoing arrows to test closure and distinct vertices,
then checks the special and ordinary spatial coframe endpoint loads.
This reproduces exactly the six frozen memberships, their weights,
ordered arrows, core side and scalar-forced powers. Each result in the
table uses a separate contraction. Equality of paired coefficients
was checked directly.

The frozen pilot's independently verified root Fourier and special
spatial tables cover both coframe owners and both actual directed
anchors and are reused here. An outgoing root uses the first local
Fourier index and an incoming edge uses the second. The opposite
spatial trace equates its two indices at each cycle vertex. On the own
side the spatial matrices use conjugated coefficients in the original
anchor convention. The normalized Schur weights are 1, 3^-4, 3^-4 and
4^-4. Each prospective site join complements the original ordered
eight-generator mask and uses the complete inversion count. The
exact scalar factors and every original occupation factorial are
included, including all four live-root quadratic factorials. The two
spatial layers have been contracted as exact Gaussian integers with
rational normalization.

Both independent schedules reproduce all twenty scaled channel
contributions and all forty constituent layer values in the frozen
author logs. Every complete layer is real. The forward and reverse
schedules agree on all five values.

## Resource scope

The independent schedule prospectively checks each site trial count,
each ordinary and closing join's work, and coefficient height before
arithmetic, and limits populated table rows during assembly. Both
runs reach maxima of 6,368 site-complement trials, 239,616 matched join
or closing products, 6,272 populated factor rows and 53,968 initial
resident factor rows. The frozen author logs report, for each new
case, 6,368 site trials, 6,272 populated rows, 239,616 ordinary and
closing work, and 14,192 closing resident input rows. The separate
special-spatial expansion has already been verified prospectively
for the reusable tables, including 43,266,176 raw and 14,198,720
cached matched products in the original pairing. Frozen retrospective
work reporting is not a reusable prospective limit. The reviewed
scope is these five newly exact members of the stated geometry and
load class. Other orientations and loads, multi-component and
doubly rooted squares, the remaining temporal block, full c0 sign,
value and nonvanishing, and native and publication gates remain open.

## Reproduction

The scratch inputs point to the frozen original and independent pilot
packages. `accepted-pilot-residual.tsv` is extracted with
`unzip -p L1_N16_C0_DIRECTED_SQUARE_PILOT_R1.zip block-remaining.tsv`
from the archive in the pinned publication checkpoint.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 batch.py > independent.out
PYTHONDONTWRITEBYTECODE=1 python3 batch.py reverse > reverse.out
python3 compare.py > comparison.out
shasum -a 256 -c manifest.sha256
```
