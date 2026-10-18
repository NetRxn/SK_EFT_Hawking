# Calibrated inference and temporal approximation review

Status: independently source-reviewed and aggregate-built; extracted evidence, canonical sync and substrate gate complete; locally accepted. Owning contract: [CALIBRATION_COARSE_GRAINING.md](../dev-loops/MemoryProcesses/CALIBRATION_COARSE_GRAINING.md). Public acceptance is local feature-branch integration only.

## Candidates and independent review

Calibration proof candidate `69470aef` was reviewed by a separate agent against the original contract. It proves physical budget validity for diagonal reset states and a stable confusion law, direct random-budget rejection containment, six-group concentration, confidence gating, and power for an explicit finite sampling law connected to the actual partial-interaction trajectories. The reviewer reproduced all model constants, all 64 coverage-box corners and 11,794 physical-null calibration corners. No substantive findings. Author MCP checks of seven principal closures returned only the standard core axioms; full extracted audit remains separate.

Coarse-graining candidate `606c7524` was independently reviewed. Actual joint collision and partial trace realize the linear channel; density preservation, exact matrix-difference/trace-distance product, shared downstream binary bound, operational saturation, scalar-predictor lower bound and endpoint cases are all connected. Twelve principal author MCP closure checks used only standard core axioms. No substantive findings.

CPU candidate `100c4ad7` passed 305 combined memory tests. Independent review also checked 2,000 asymmetric rational calibration cases, 4,096 physical coverage cases, 1,000 weighted-history comparisons and 500 coherent rational joint-matrix collisions. It found two documentation defects: a proposed theorem name and an ambiguous lower-bound domain. Both were corrected in `f1d0128a`. Independent AST comparison confirmed executable code was unchanged. The lower bound concerns arbitrary states at the suffix boundary, not necessarily states reachable through a fixed prefix.

Root absorbed the proof candidates through the existing controller as `a083290f` and `17be8083`. Aggregate `8a11b06a` passed `lake build SKEFTHawking.ExtractDeps` through the controller, epoch `7fedd34c9b6510a35d7232d1880e1f5c5bba4ec186d312b1fa71e32150e12a99`. Independent integrated review verified byte-identical proof sources, unchanged executable CPU AST, 305 tests in 0.28 seconds, and D9 claim/metadata/manifest correctness.

## Publication and scope

D9 is homed and queued under D.0; its manuscript and pending review/readiness states are unchanged. The canonical source manifest was independently reproduced. Its existing parser renders `Synthesize` as unspecified; the owning mapping retains the explicit action. This existing limitation does not lose the D9 destination and is outside this increment's machinery scope.

The theorem and CPU implementation are separate evidence layers. Physical applicability, trusted standards, stable readout, diagonal reset structure, fixed protocols and within-group independent trials remain assumptions. No hardware observations, optional-stopping guarantee, quantum-only memory, unusual-time claim or general simulation advantage is asserted. The coarse model discards outputs and does not cover arbitrary feedback or retained measurement records. Pre-existing paper-corpus failures are outside scope by owner instruction.

## Extracted evidence

Canonical `update_counts.py` and `sync.py --fast` completed. Compared with accepted `147aea7f`, the inventory adds exactly 91 declarations (46 calibration, 45 coarse-graining), removes none and changes no existing declaration. Every new declaration has empty project-axiom dependencies, no extraction timeout and only `propext`, `Classical.choice`, `Quot.sound` where required. Global extraction reports zero project axioms and zero sorry. Counts are inventory records, not 91 independently authored scientific theorems.

## Final acceptance

Independent final evidence review accepted the complete 91-record delta, counts and atlas. It found one stale future-tense G1 paragraph; root corrected it to the implemented varying-retention product and boundary-state domain, and the reviewer accepted the correction. No actionable findings remain.

`gate_precheck.py s13-lean` passed in 521.4 seconds: 70/89 checks green, no Lean/Python-side failure, and the same 19 pre-existing paper-corpus failures as the prior accepted sampling increment. Those failures remain visible and outside owner-authorized scope. All three ADR-008 slots are free. Public main and remote remain unchanged; acceptance is confined to this local feature branch. The passing aggregate build applies to unchanged proof sources; subsequent commits contain only generated evidence and documentation.
