# Publication readiness after D4 and D8 attribution repair

The canonical graph measured all 21 bundles and 231 gates at focused
main-delivery commit `040ca7871` on PR #118. Compared with focused baseline
`818f98007`, the states remain **158 passed, 24 blocked, 30 open, 19 requiring
recheck**. Zero gate transitions and zero all-pass bundles. The separate
integrated R6 snapshot has a different paper population.

D4:2.2 and D8:1.4 now resolve as fixed in the graph. The two declared
verifiers passed through the canonical closure writer. The ledger preserved
all 1,236 prior records, and its 46 focused tests passed. FixPropagation
remains blocked for both papers. D8:1.8 remains open. The D8 review
document still fails validation for four legacy routing lane names.
The two manuscripts compiled in scratch with zero errors or unresolved
references. See the [scope and review evidence on PR #118](https://github.com/NetRxn/SK_EFT_Hawking/blob/040ca78710432a995ab99a3d9b47db9f10cafa62/docs/audits/2026-10-17-publication-substance-construction/D4_D8_DAWSON_ATTRIBUTION_ACCEPTANCE_R2.md).

The graph reader automatically ran dependency extraction after the
comment edits and updated only the tracked catalog hash. ROOT restored
that generated change to its committed value. The catalog JSON bytes
were unchanged. The graph used the current source and same catalog data.
Native build and catalog freshness acceptance still require their
normal qualification.

✓ Mechanical pass · × blocked · ? open · ↻ recheck · ◌ pass with coverage caveat.

| Bundle | G1 | G2 | G3 | G4 | G5 | G6 | G7 | G8 | G9 | G10 | G11 | Movement from 818f98007 |
|---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|---|
| F | ✓ | ✓ | ? | ? | × | ◌ | ✓ | ✓ | ↻ | ✓ | × | No gate-state change |
| D1 | ✓ | ✓ | ? | ? | × | ◌ | ✓ | ✓ | ↻ | ✓ | × | No gate-state change |
| D2 | × | ✓ | ✓ | ? | × | ◌ | ✓ | ✓ | ✓ | ✓ | × | No gate-state change |
| D3 | ✓ | ✓ | ✓ | ? | ✓ | ◌ | ✓ | ✓ | ✓ | ✓ | × | No gate-state change |
| D4 | ✓ | ✓ | ? | ? | ✓ | ◌ | ✓ | ✓ | ↻ | ✓ | × | Attribution finding 2.2 fixed |
| D5 | ✓ | ↻ | ? | ? | × | ◌ | × | ✓ | ↻ | ↻ | × | No gate-state change |
| D6 | ✓ | ✓ | ? | ? | ✓ | ◌ | ✓ | ✓ | ↻ | ✓ | ✓ | No gate-state change |
| D7 | ✓ | ✓ | ✓ | ? | ✓ | ◌ | ✓ | ✓ | ✓ | ✓ | ↻ | No gate-state change |
| D8 | ? | ✓ | ✓ | ? | × | ◌ | × | ✓ | ✓ | ↻ | × | Attribution finding 1.4 fixed. Figure finding 1.8 open |
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

[Raw canonical gate nodes and source fingerprint](FOCUSED_MAIN_GATES_DAWSON_R2.json).
The [previous focused measurement](FOCUSED_MAIN_READINESS_BEFORE_NOW_20261107_R1.md)
retains gate names, citation and computation coverage caveats. Full merge
qualification, native verification and final human approval remain open.
