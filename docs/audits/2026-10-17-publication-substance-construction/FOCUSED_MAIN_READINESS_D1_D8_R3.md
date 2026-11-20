# Publication readiness after the D1 crossover and D8 figure repairs

The canonical graph measured **21 bundles and 231 gates** at draft
delivery head `1ece12af7` on [PR #118](https://github.com/NetRxn/SK_EFT_Hawking/pull/118).
Compared with `040ca7871` on the same branch, **0 gate states changed**
and **0 bundles have all eleven gates passed**. The totals are
**158 passed, 24 blocked, 30 open and 19 requiring recheck**.

The graph resolves D1 1.1 and D8 1.8 as fixed. D1 has 12 blocking
and 40 total open review findings, down from 13 and 41. D8 has five
blocking findings and 21 total open, down from 22 total. Both G11
states remain blocked. The draft's D1/F numerical checks passed.
G4 remains open for 20 bundles because its formula grounding covers
only D12 in this snapshot. G5 is blocked for six bundles. G11 is
blocked for 13, needs recheck for six, and passes for two.

✓ Mechanical pass · × blocked · ? open · ↻ recheck · ◌ pass with coverage caveat.

| Bundle | G1 | G2 | G3 | G4 | G5 | G6 | G7 | G8 | G9 | G10 | G11 | Movement from 040ca7871 |
|---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|---|
| F | ✓ | ✓ | ? | ? | × | ◌ | ✓ | ✓ | ↻ | ✓ | × | Thermal crossover propagation verified |
| D1 | ✓ | ✓ | ? | ? | × | ◌ | ✓ | ✓ | ↻ | ✓ | × | Crossover 1.1 fixed. G11 blocking findings 13 → 12 |
| D2 | × | ✓ | ✓ | ? | × | ◌ | ✓ | ✓ | ✓ | ✓ | × | No gate-state change |
| D3 | ✓ | ✓ | ✓ | ? | ✓ | ◌ | ✓ | ✓ | ✓ | ✓ | × | No gate-state change |
| D4 | ✓ | ✓ | ? | ? | ✓ | ◌ | ✓ | ✓ | ↻ | ✓ | × | No gate-state change |
| D5 | ✓ | ↻ | ? | ? | × | ◌ | × | ✓ | ↻ | ↻ | × | No gate-state change |
| D6 | ✓ | ✓ | ? | ? | ✓ | ◌ | ✓ | ✓ | ↻ | ✓ | ✓ | No gate-state change |
| D7 | ✓ | ✓ | ✓ | ? | ✓ | ◌ | ✓ | ✓ | ✓ | ✓ | ↻ | No gate-state change |
| D8 | ? | ✓ | ✓ | ? | × | ◌ | × | ✓ | ✓ | ↻ | × | Figure 1.8 fixed. G11 total open findings 22 → 21 |
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

[Exact canonical gate nodes and graph fingerprint](FOCUSED_MAIN_GATES_D1_D8_R3.json).
The [previous chart](FOCUSED_MAIN_READINESS_DAWSON_R2.md) retains the
earlier measurement and the separate mixed-paper-population boundary.
The graph builder refreshed only the generated Lean dependency hash
on disk, which was restored to the committed value after measurement.
Full merge qualification, native/catalog acceptance, the broader
scientific BUILDs and final human approval remain open.
