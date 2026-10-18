# Finite memory experiment — supervised increment

Status: accepted under substrate scope after integrated validation and independent scientific review. Integration records: PR 67 (process) and PR 71 (science).

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


## Implemented mathematical and numerical boundary

`QuantumNetwork/FiniteMemoryProcess.lean` proves arbitrary-input discard-and-prepare,
normalized SWAP/reset channels, the retained-history and erased-environment control,
and exclusion of a common system-only continuation with a common measurement.
`BinaryMemoryRobustness.lean` proves the binary separation bound and its extension
with explicit observation-error budgets.

`FiniteMemoryResetMixture.lean` connects the CPU reset-skip mixture and raw diagonal
measurement sums to exact matrix operations. The basis-history experiment is
insensitive to the skip probability because S is already zero at the reset; this
is not a general imperfect-reset robustness result. `BinaryMemoryFixture.lean`
provides a separate diagonal-state family with exact trace distances and a common
bit-flip channel that instantiates the binary bound.

The CPU functions in `src/core/formulas.py` reference these mathematical results.
Their floating-point execution, eigensolver, input tolerances, clipping and
renormalization have no formal error certificate. Synthetic observation checks
bound errors relative to represented computed probabilities; using the observed
Lean theorem for physical evidence additionally requires budgets relative to
exact Born probabilities. This increment supplies the model and conditional
criterion, not a certified numerical decision procedure.

## Integration and closure

Process and science candidates remain on reviewed feature branches until accepted.
Run the existing `gate_precheck.py s13-lean` substrate path for this increment,
which changes no paper corpus: paper failures remain reported and do not become
submission-readiness claims. Record full-test results separately; do not describe
scoped acceptance as a clean full suite. Regenerate dependency evidence and counts
through the existing producers, then obtain independent adversarial review of the
integrated candidate. Notebook evidence records exact commits and executed checks.

`s13-lean` establishes eligibility for substrate-focused Stage-13 review; it does
not replace `verify_scope.py --merge-gate` or waive failing pytest checks. Report
any remaining merge-certification failure separately.

The integrated review at `8d71b7e9` found no substantive defects and independently
reproduced the memory tests and additional correlated-state/fixture checks. The
stable substrate precheck passed with paper failures reported separately. PR 71
holds the scientific review record; PR 67 holds the process review record. Neither
result certifies paper submission or a green full-pytest merge gate.

Owner acceptance on 2026-09-09 explicitly excludes pre-existing corpus-test
failures from this increment. Integration is authorized using the passed
substrate gate and independent reviews, with those failures disclosed. This
scoped acceptance does not modify the merge script, raise corpus ratchets,
change paper readiness, or certify a green full pytest run.

## Reset-sensitive extension

The subsequent [partial-interaction increment](PARTIAL_INTERACTION.md) adds a probabilistic identity/SWAP model where reset failure changes the signal, with an exact residual-system comparison bound. Its acceptance and local-only integration boundary are recorded in that owning plan.
