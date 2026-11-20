# Publication readiness after the D8 proof and count repairs

The canonical graph measured **21 bundles and 231 gates** at draft head `8a99bcc0e`
on [PR #118](https://github.com/NetRxn/SK_EFT_Hawking/pull/118).
Compared with `1ece12af7`, **0 gate states changed**.
**0 bundles have all eleven gates passed**. Totals are **158 passed, 24 blocked, 30 open, 19 requiring recheck**.

D8 findings 1.1–1.3 and 1.9 resolve as fixed. D8 G11 blocking findings
went from 5 to 2. The canonical
metadata count check passed all 21 bundles with zero drift after refreshing
D1, D4 and D8. All three bundle verdicts remain red. D8's remaining
G11 blockers are findings 1.5 and 1.7 on full-text source custody and
review ingestion. G5 still flags the definitional compiler equation.
G7 flags the first-claim sentence. G4 remains open for 20 bundles.
D12 is the single measured pass, with two unresolved Lean-grounding
advisories.

✓ Mechanical pass · × blocked · ? open · ↻ recheck · ◌ pass with coverage caveat.

| Bundle | G1 | G2 | G3 | G4 | G5 | G6 | G7 | G8 | G9 | G10 | G11 | Movement |
|---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|---|
| F | ✓ | ✓ | ? | ? | × | ◌ | ✓ | ✓ | ↻ | ✓ | × | No gate-state change |
| D1 | ✓ | ✓ | ? | ? | × | ◌ | ✓ | ✓ | ↻ | ✓ | × | Live counts synchronized |
| D2 | × | ✓ | ✓ | ? | × | ◌ | ✓ | ✓ | ✓ | ✓ | × | No gate-state change |
| D3 | ✓ | ✓ | ✓ | ? | ✓ | ◌ | ✓ | ✓ | ✓ | ✓ | × | No gate-state change |
| D4 | ✓ | ✓ | ? | ? | ✓ | ◌ | ✓ | ✓ | ↻ | ✓ | × | Live counts synchronized |
| D5 | ✓ | ↻ | ? | ? | × | ◌ | × | ✓ | ↻ | ↻ | × | No gate-state change |
| D6 | ✓ | ✓ | ? | ? | ✓ | ◌ | ✓ | ✓ | ↻ | ✓ | ✓ | No gate-state change |
| D7 | ✓ | ✓ | ✓ | ? | ✓ | ◌ | ✓ | ✓ | ✓ | ✓ | ↻ | No gate-state change |
| D8 | ? | ✓ | ✓ | ? | × | ◌ | × | ✓ | ✓ | ↻ | × | Four fixed findings |
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

[Exact canonical gate nodes and fingerprint](FOCUSED_MAIN_GATES_D8_COUNTS_R4.json).
The [previous chart](FOCUSED_MAIN_READINESS_D1_D8_R3.md) describes the
formula-grounding and coverage caveats. Full merge qualification, scientific
acceptance and final human approval remain open.
