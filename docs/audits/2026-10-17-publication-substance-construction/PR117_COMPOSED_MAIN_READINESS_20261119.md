# Publication readiness on PR117 composed with current main

Measured 2026-11-19T23:09:25.260859+00:00 using the existing graph builder. Draft head 0b1d4bfa8 and main a912c5542 compose without conflicts as tree 741449313eb8f4e5740ea72abaa25b15144397c0. The five added paths are L1 research references. The stored Lean dependency index matched the Lean source hash cc4ef5dc92850ea4 before graph generation.

**21 bundles, 231 gates.** 160 passed, 25 blocked, 28 open and 18 need recheck. This is a measurement of the composed draft. The November 7 focused snapshot used a different paper population and is unsuitable as a transition baseline.

✓ Mechanical pass · × Blocked · ? Open · ↻ Needs recheck

| Bundle | G1 | G2 | G3 | G4 | G5 | G6 | G7 | G8 | G9 | G10 | G11 |
|---|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|:---:|
| F | ✓ | ✓ | ? | ? | × | ✓ | ✓ | ✓ | ↻ | ✓ | × |
| D1 | ✓ | ✓ | ? | ? | × | ✓ | ✓ | ✓ | ↻ | ✓ | × |
| D2 | × | ✓ | ✓ | ? | × | ✓ | ✓ | ✓ | ✓ | ✓ | × |
| D3 | ✓ | ✓ | ✓ | ? | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | × |
| D4 | ✓ | ✓ | ? | ? | ✓ | ✓ | ✓ | ✓ | ↻ | ✓ | × |
| D5 | ✓ | ↻ | ? | ? | × | ✓ | × | ✓ | ↻ | ↻ | × |
| D6 | ✓ | ✓ | ? | ? | ✓ | ✓ | ✓ | ✓ | ↻ | ✓ | ✓ |
| D7 | ✓ | ✓ | ✓ | ? | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ↻ |
| D8 | ? | ✓ | ✓ | ? | × | ✓ | × | ✓ | ✓ | ↻ | × |
| D9 | ✓ | ↻ | ? | ? | ✓ | ✓ | ✓ | ✓ | ↻ | ✓ | ✓ |
| D10 | ? | ✓ | ✓ | ? | ✓ | ✓ | × | ✓ | ✓ | ↻ | ↻ |
| D11 | ✓ | ✓ | ✓ | ? | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ↻ |
| D12 | ✓ | ✓ | × | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | × |
| L1 | ✓ | ✓ | × | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | × |
| L2 | ✓ | ✓ | ✓ | ? | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | × |
| L3 | ✓ | ✓ | ✓ | ? | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | × |
| I1 | ✓ | ✓ | ✓ | ? | × | ✓ | ✓ | ✓ | ✓ | ✓ | × |
| I2 | ✓ | ✓ | ✓ | ? | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ↻ |
| I3 | ✓ | ✓ | ✓ | ? | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | ↻ |
| E1 | ✓ | ✓ | ✓ | ? | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | × |
| E2 | ✓ | ✓ | ? | ? | ✓ | ✓ | ✓ | ✓ | ↻ | ✓ | ↻ |

Gate definitions follow the [canonical gate taxonomy](../../READINESS_GATES.md). The [full gate evidence](PR117_COMPOSED_MAIN_READINESS_20261119.json) records measurement flags and supporting evidence, including caveats on mechanical passes.

L1 G3 records 20 parameters and seven missing human verification dates. G11 identifies the open Stage 13 finding for the adopted susceptibility window. G4 covers static test grounding for seven declared formulas. The reviewed historical Paper 25 compile and dependency findings both read fixed on this composition. L1 and Paper 25 each compile at five pages with zero fatal errors, overfull reports and unresolved references. Three focused graph tests passed. Full merge qualification, the original physical deliverables and final human approval remain open.


## 20 November venue provenance recheck

The canonical graph was rebuilt on PR117 head `b6994984f044eb39a43c1435e3ab91458a02b522`
composed against the same main `a912c5542d897c22ac8d4cdec07649a4872215a6`,
tree `bd2778b884e19b053433a5949737e6131ce556e7`.
The exact same-base change is limited to three length-source text fields
in `papers/L1/bundle_metadata.json`. The new graph has 51,500 nodes and
19,076 edges, source hash `562af3e2785d2fe0`, and SHA-256
`f179ac2ec58ca6f1fbd3c58d9ccc3d16e0095ee3abddc6c67023f5ebe6736afa`.
It was built at 2026-11-20 09:56:37 UTC. All 704 paper-level gate
payloads agree after removing evaluation and modification timestamps.
All 231 bundle gate states and measured flags agree. The table above
also describes this exact composition. L1 still requires the seven
human provenance dates and the physical window evidence for finding 2.1.
