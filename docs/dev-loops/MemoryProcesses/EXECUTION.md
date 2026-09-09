# Finite memory experiment — supervised increment

Status: authorized bounded development; proof validation and review pending.

Root owns integration, notebook writing and acceptance. CPU-reference work may proceed independently of Lean slot admission. No native compaction or unattended-operation claim is implied.

## Scope

For two qubits S and E, initially E=0 and S=b, demonstrate SWAP, reset S only, SWAP, computational-basis measurement. The final outcome is b; resetting both factors produces zero for either history. The reset must be discard-and-prepare on arbitrary joint input, not a favorable-outcome selection.

Use existing concrete matrix/Kraus foundations. The robustness theorem is binary-first: with two post-reset states within epsilon_i of a common reference, a common channel and common binary measurement yield outcome-probability separation at most min(1, epsilon_0+epsilon_1). Include explicit observed-probability errors separately. No arbitrary finite-POVM coverage, quantum advantage, or new theory of time is claimed.

## CPU package

The existing formulas module owns mathematical computation. Add small pure NumPy functions there, plus focused tests. Basis order is (S,E), with S the first factor. Validate dimensions/state and probability conventions as appropriate; document any unchecked preconditions. Return state trajectory, normalized binary probabilities, reset-both control and a deterministic imperfect-reset example. Verify reset semantics on a correlated joint state, not only product states. No random search, GPU, hardware, new dependencies or manuscript changes.

## Proof package

Admit a controller-managed slot before proof edits. Reuse traceDist triangle, concrete Kraus contraction, swapMat and partial trace. Prove required reset and measurement adapters; inspect actual axiom closure and kernel-check before reporting proof acceptance. Source discovery is not validation.

## Review and completion

Tests must distinguish a retained environment from reset-both control and catch an incorrect factor ordering or reset that destroys E. Independent semantic review checks common-continuation/common-measurement assumptions and the memoryless comparison boundary. Root integrates accepted changes and updates evidence. Only consumed results claim completion.
