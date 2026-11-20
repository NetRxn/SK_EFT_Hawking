# Original N16 Task3 direct edge acceptance R2

ROOT accepts the direct local edge at
[043896cf0](https://github.com/NetRxn/SK_EFT_Hawking/commit/043896cf0494ce28b5a02993bb6f3ee24065e8af).
It is pushed on `codex/publication-l1-original-n16-task3`, with
verified remote readback and exact base `4672e9fec`. Only the three
assigned Python and test paths changed. The direct route computes both
36-entry literal tables and both 36-entry dual tables. The two
original endpoint coframes remain distinct, and both independent
anchors and chiral Haar factors contribute. The oriented fourth moment
is `1125/4`, with accepted scale factors `45/4` and `12` emerging as
outputs. A deliberate same-endpoint poison failed the two anchor
controls and the mixed table.

The first review demonstrated that each NaN limit passed the initial
admission. R2 validates positive exact integer caps before allocation,
keeps legacy generic conjugation, and separates attempted wedge pairs
from exact products. Independent re-review rejected all 27 malformed
caps before allocation and triggered all three valid low-limit refusals.
It reproduced every table entry and the fourth moment. The measured
local call used 7,120 attempted pairs, including 5,672 overlaps and
1,448 wedge products. Other steps used 1,072 products, for 2,520 total.
It reached 28,652 logical occupied or reserved records and 14 checked
bits. The author's 133 bounded tests and the independent 30 focused
tests passed. The complete one-site test was deselected.

[Exact author and independent review evidence](ORIGINAL_TASK3_N16_DIRECT_EVIDENCE_R2.zip),
35,084 bytes, SHA256
`8ceb7579affb476fdcc7c1a4993c4b866aa9d74492928cbe8381c044950e6cf8`.
R1 adverse evidence, exact patches, test output and continuity checks
are retained. Acceptance covers only the local direct source and
bounded execution.

ROOT also ran an [exact local covariance probe](original_n16_curvature_temporal_probe_r1.py)
on the same scientific source. It reproduced all 256 curvature
covariance entries and all 32 two-anchor temporal covariance entries
in each of source C and metric M conventions. The probe derives the
temporal sewing factors `1/2` for the literal Q00 and `3/8` for the
curvature area. [Raw result](ORIGINAL_TASK3_N16_CURVATURE_TEMPORAL_PROBE_R1.json).
This is local corroboration for the scalar implementation. The
plaquette and spectator incidence, geometric support, auxiliary
minors, entire scalar/contact family, formal bridges, full Z,
physical B3 and publication gates remain separate.

The independent auxiliary and geometric-support authors work in
scratch with isolated responsibilities. They supply source increments
for ROOT to compose and submit to independent review. The full N16
calculation still needs explicit runtime admission.
