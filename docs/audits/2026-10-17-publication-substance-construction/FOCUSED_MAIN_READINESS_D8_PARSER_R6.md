# Publication readiness after the D8 parser repair

The canonical graph measured **21 bundles and 231 gates** at draft
`0112750cd` on [PR #118](https://github.com/NetRxn/SK_EFT_Hawking/pull/118).
One state changed from `3f9461f0f`. **D8 G11 moved from blocked to recheck**.
Totals are **158 passed, 23 blocked, 30 open and 20 requiring recheck**.
No bundle has all eleven gates passed.

D8's canonically counted blocking findings fell from two at R4 to
one after the source closure and zero after the parser closure.
Seven advisory findings remain. The bundle count writer reports
YELLOW while the gate matrix still shows independent G5 and G7
blocks. G1 also has an unmeasured bibliography coverage path. L2
and D11 lost three and fourteen advisory parser artifacts respectively.
The parser repair preserved all retained findings and active edges.

All three gate snapshots use the same retained Lean catalog and
unchanged Lean source. The extractor signaled that its catalog hash
needs refresh. This comparison isolates the D8 publication changes
using that fixed catalog. The graph's own source fingerprint is
unchanged between R5 and R6, so the exact Git heads and graph byte
hashes distinguish the runs.

✓ Mechanical pass · × blocked · ? open · ↻ recheck · ◌ pass with coverage caveat.

| Bundle | G1 | G2 | G3 | G4 | G5 | G6 | G7 | G8 | G9 | G10 | G11 | Movement |
|---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|---|
| F | ✓ | ✓ | ? | ? | × | ◌ | ✓ | ✓ | ↻ | ✓ | × | No gate-state change |
| D1 | ✓ | ✓ | ? | ? | × | ◌ | ✓ | ✓ | ↻ | ✓ | × | No gate-state change |
| D2 | × | ✓ | ✓ | ? | × | ◌ | ✓ | ✓ | ✓ | ✓ | × | No gate-state change |
| D3 | ✓ | ✓ | ✓ | ? | ✓ | ◌ | ✓ | ✓ | ✓ | ✓ | × | No gate-state change |
| D4 | ✓ | ✓ | ? | ? | ✓ | ◌ | ✓ | ✓ | ↻ | ✓ | × | No gate-state change |
| D5 | ✓ | ↻ | ? | ? | × | ◌ | × | ✓ | ↻ | ↻ | × | No gate-state change |
| D6 | ✓ | ✓ | ? | ? | ✓ | ◌ | ✓ | ✓ | ↻ | ✓ | ✓ | No gate-state change |
| D7 | ✓ | ✓ | ✓ | ? | ✓ | ◌ | ✓ | ✓ | ✓ | ✓ | ↻ | No gate-state change |
| D8 | ? | ✓ | ✓ | ? | × | ◌ | × | ✓ | ✓ | ↻ | ↻ | G11 blocker cleared, seven advisory |
| D9 | ✓ | ↻ | ? | ? | ✓ | ◌ | ✓ | ✓ | ↻ | ✓ | ✓ | No gate-state change |
| D10 | ? | ✓ | ✓ | ? | ✓ | ◌ | × | ✓ | ✓ | ↻ | ↻ | No gate-state change |
| D11 | ✓ | ✓ | ✓ | ? | ✓ | ◌ | ✓ | ✓ | ✓ | ✓ | ↻ | False findings removed |
| D12 | ✓ | ✓ | × | ◌ | ✓ | ◌ | ✓ | ✓ | ✓ | ✓ | × | No gate-state change |
| L1 | ✓ | ✓ | ? | ? | ✓ | ◌ | ✓ | ✓ | ↻ | ✓ | × | No gate-state change |
| L2 | ✓ | ✓ | ✓ | ? | ✓ | ◌ | ✓ | ✓ | ✓ | ✓ | × | False findings removed |
| L3 | ✓ | ✓ | ✓ | ? | ✓ | ◌ | ✓ | ✓ | ✓ | ✓ | × | No gate-state change |
| I1 | ✓ | ✓ | ✓ | ? | × | ◌ | ✓ | ✓ | ✓ | ✓ | × | No gate-state change |
| I2 | ✓ | ✓ | ✓ | ? | ✓ | ◌ | ✓ | ✓ | ✓ | ✓ | ↻ | No gate-state change |
| I3 | ✓ | ✓ | ✓ | ? | ✓ | ◌ | ✓ | ✓ | ✓ | ✓ | ↻ | No gate-state change |
| E1 | ✓ | ✓ | ✓ | ? | ✓ | ◌ | ✓ | ✓ | ✓ | ✓ | × | No gate-state change |
| E2 | ✓ | ✓ | ? | ? | ✓ | ◌ | ✓ | ✓ | ↻ | ✓ | ↻ | No gate-state change |

[Exact R5 baseline gate nodes](FOCUSED_MAIN_GATES_D8_SOURCE_R5.json)
and [R6 gate nodes](FOCUSED_MAIN_GATES_D8_PARSER_R6.json) retain
the fingerprints and evidence. The
[canonical count refresh](D8_L2_D11_PARSER_COUNT_REFRESH_R2.json)
is a separate measurement. Merge qualification, all original
scientific acceptance and final human approval remain open.
