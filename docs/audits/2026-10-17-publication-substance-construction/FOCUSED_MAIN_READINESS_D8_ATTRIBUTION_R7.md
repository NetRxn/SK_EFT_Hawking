# Publication readiness after the D8 attribution repairs

The canonical graph measured **21 bundles and 231 gates** at draft
`be3a46c96` on [PR #118](https://github.com/NetRxn/SK_EFT_Hawking/pull/118).
**No gate state changed** from `0112750cd`. Totals are **158 passed,
23 blocked, 30 open and 20 requiring recheck**. No bundle has all
eleven gates passed.

D8's per-anchor roster now accounts for all 19 active citations,
and the trapped-ion manuscript, figure and registry distinguish the
Brylinski result from the actual Lean tensor-Pauli closure-flow proof.
Both findings are canonically fixed. D8 has zero blocking review
findings and six advisory findings. G11 remains at recheck, while
G5 and G7 are still blocked and G1's bibliography coverage remains open.

The exact comparison uses unchanged Lean source and the same retained
Lean catalog as R6. The extractor still requires a catalog refresh.
The measured gate states therefore retain that coverage limit.

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
| D8 | ? | ✓ | ✓ | ? | × | ◌ | × | ✓ | ✓ | ↻ | ↻ | Two attribution findings closed, six advisory |
| D9 | ✓ | ↻ | ? | ? | ✓ | ◌ | ✓ | ✓ | ↻ | ✓ | ✓ | No gate-state change |
| D10 | ? | ✓ | ✓ | ? | ✓ | ◌ | × | ✓ | ✓ | ↻ | ↻ | No gate-state change |
| D11 | ✓ | ✓ | ✓ | ? | ✓ | ◌ | ✓ | ✓ | ✓ | ✓ | ↻ | No gate-state change |
| D12 | ✓ | ✓ | × | ◌ | ✓ | ◌ | ✓ | ✓ | ✓ | ✓ | × | No gate-state change |
| L1 | ✓ | ✓ | ? | ? | ✓ | ◌ | ✓ | ✓ | ↻ | ✓ | × | No gate-state change |
| L2 | ✓ | ✓ | ✓ | ? | ✓ | ◌ | ✓ | ✓ | ✓ | ✓ | × | No gate-state change |
| L3 | ✓ | ✓ | ✓ | ? | ✓ | ◌ | ✓ | ✓ | ✓ | ✓ | × | No gate-state change |
| I1 | ✓ | ✓ | ✓ | ? | × | ◌ | ✓ | ✓ | ✓ | ✓ | × | No gate-state change |
| I2 | ✓ | ✓ | ✓ | ? | ✓ | ◌ | ✓ | ✓ | ✓ | ✓ | ↻ | No gate-state change |
| I3 | ✓ | ✓ | ✓ | ? | ✓ | ◌ | ✓ | ✓ | ✓ | ✓ | ↻ | No gate-state change |
| E1 | ✓ | ✓ | ✓ | ? | ✓ | ◌ | ✓ | ✓ | ✓ | ✓ | × | No gate-state change |
| E2 | ✓ | ✓ | ? | ? | ✓ | ◌ | ✓ | ✓ | ↻ | ✓ | ↻ | No gate-state change |

[Exact R7 gate nodes](FOCUSED_MAIN_GATES_D8_ATTRIBUTION_R7.json) ·
[R6 baseline](FOCUSED_MAIN_READINESS_D8_PARSER_R6.md) ·
[Canonical count refresh](D8_ATTRIBUTION_CLOSURE_COUNTS_R1.json).
Full merge qualification, original scientific acceptance and final
human approval remain open.
