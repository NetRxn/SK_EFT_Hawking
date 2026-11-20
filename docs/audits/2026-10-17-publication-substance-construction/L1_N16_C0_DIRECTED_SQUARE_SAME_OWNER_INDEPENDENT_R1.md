# Independent review of the 42-case same-owner directed-square extension

**ACCEPT** the 42 additional pure-EHC directed-square representatives in
`reviewed-exact.tsv`. All coefficients are positive. Their original weights
are 38 × 96 and 4 × 48, for **3,840 newly resolved labels**. Their exact
weighted subtotal is `1677014379339527105381299959417/18446744073709551616`.
The remaining temporal block contains **10,410 orbits and 899,691 labels**.

## Membership and independent replay

Continuity returned fresh. The frozen extension manifest and the
previous independent batch manifest verified. I extracted the exact
residual from the clean publication checkpoint at `ea01a7687`. It
agrees byte-for-byte with the author's copy and also agrees row for
row with the earlier independent residual after removing exactly the
six accepted original rows. There are no duplicate labels in the
reviewed orbit-representative roster.

The reviewer decodes the original occupations and reapplies the
independent two-chirality representation support propagation to each
row of that residual. It selects all-even cases with one four-edge core
in one layer, one power-two root per edge and one simple coherently
directed cycle. The spatial test permits the ordinary same-owner degree
two and four and mixed (2,2) tensors, and requires same-owner degree two
or four in both spatial layers on each cycle edge. Scanning both
possible core layers produces 42 eligible B-core cases and zero
A-core cases. The observed cycle-edge loads are:

| Spatial layer | Degree two | Degree four |
| --- | ---: | ---: |
| Own | 168 | 0 |
| Opposite | 100 | 68 |

Each outgoing B site has only its quadratic live root. The orientation
lists, forced scalar powers and original weights agree exactly with
the author roster. Each case starts with its own decoded occupation.
No relabeling equality is used to infer another value.

The ordinary/mixed edge moments, special spatial matrices and
literal-root Fourier coefficients were verified in preceding reviews
and reused. Spatial endpoint indices follow the actual arrow and
directed anchor. The two traces are sewn with opposite orders, including
the own-side spatial dagger conjugation. The four channel weights
use the original Schur dimensions 1, 3, 3 and 4 and corresponding
fourth powers in the denominator. At every site the independent
contraction keeps the signed inversion count needed to reach its
eight-generator top. The original multiplicity factorials and each
scalar root moment remain in the normalization.

Both the ordinary and reversed independent contraction schedules
reproduce all 168 scaled channel contributions and 336 component
layer values exactly. The complete layer contractions are real,
and every case's final signed coefficient matches the frozen result.
No case was refused.

## Resource scope

The independent run counts every site-inversion schedule before
executing its products and guards sparse row insertion. The ordinary
and closing join counts and coefficient-height bounds are checked
before multiplying. The older independently guarded spatial build
covers both owners, both anchors and both special edge degrees, so
the extension reuses those rows without new spatial generation.

The independent schedules reached 27,392 site-complement trials,
64,512 populated factor rows and 48,360 initial resident rows.
The ordinary schedule's largest join or closing count was 995,328.
The reversed schedule's maximum was 921,600. The frozen author
receipts show 746,496 ordinary join products, 995,328 closing work
and 105,984 closing resident input rows. All checks passed under the
specified caps. As in the pilot, the frozen original spatial builder's
raw-work flag alone is retrospective. Its independently guarded
replay is the prospective evidence for the shared special tables.

This acceptance covers this one-core, same-owner spatial class in the
existing residual. Mixed-owner square edges, other orientations and
temporal shapes, and the full original c0 sign, value and nonvanishing
remain open. No repository, manuscript, native or Lean state changed.

## Reproduction

In this scratch directory, `INDEPENDENT` points to the preceding frozen
literal tables and census, `root.tsv` and `spatial.tsv` to the prior
independent pilot outputs, `prior-batch-exact.tsv` to the previous five
accepted rows, and `frozen` to the author input directory with the
`same-owner-extension` subtree. The current residual is the
`block-remaining.tsv` member of the pinned
`L1_N16_C0_DIRECTED_SQUARE_BATCH_R1.zip`.

```sh
PYTHONDONTWRITEBYTECODE=1 python3 orientation-census.py > orientations.out
PYTHONDONTWRITEBYTECODE=1 python3 extension.py > independent.out
PYTHONDONTWRITEBYTECODE=1 python3 extension.py reverse > reverse.out
python3 compare.py > comparison.out
shasum -a 256 -c manifest.sha256
```
