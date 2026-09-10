# Fixed-sample binary memory inference

Status: authorized implementation under supervised coordination. This increment follows the accepted [partial-interaction model](PARTIAL_INTERACTION.md). Root owns integration, the primary machine-local notebook and acceptance; workers own separate source packages and report to root. Public changes remain local on `codex/memory-sampling`, based on `2f48a1e6`. Independent review precedes local integration and acceptance.

## Scientific contract

For each history h in {0,1}, collect a fixed positive number n_h of independent identically distributed binary trials with observed success probability q_h. Each complete trial starts from the specified preparation, including a fresh environment. Memory is retained within a trial, not assumed absent there. Independence between the two history groups is unnecessary for the union bound. Sample sizes, intervention, effect, budgets and decision rule are fixed before observing outcomes. Adaptive stopping, selected best-of-many tests and uncontrolled drift are not covered.

Let the empirical proportions be f_h and choose positive rational radii rho_h. Prove their simultaneous concentration from the bounded independent trial model, not by assuming the desired coverage. Under a common normalized system channel and common binary effect, justified reset-state budgets epsilon_h and observation-bias budgets delta_h imply the true observed gap is at most B = min(1, epsilon_0 + epsilon_1) + delta_0 + delta_1. Reject that comparison class only if |f_0-f_1| > B + rho_0 + rho_1. Show false rejection probability is bounded by the simultaneous sampling failure probability. The bias budgets relate observed trial probabilities to ideal Born probabilities; they are separate from sampling error and require justification.

Use Hoeffding tails 2 exp(-2 n_h rho_h^2), with a rational conservative certificate: for natural k_h <= 2 n_h rho_h^2, each tail is at most 2 / 2^k_h, since exp(1) >= 2. The total failure bound is capped at one. Python uses exact rational arithmetic for proportions, supplied budgets and radii, exponent checks and strict decision comparisons. It does not rely on floating-point log or square root at the decision boundary. Resource limits must be explicit and must not silently weaken confidence. A checked arithmetic decision does not verify experimental assumptions or certify the Python runtime in Lean.

The requested failure level alpha must satisfy 0 < alpha < 1. A certified arithmetic rejection requires both the computed failure bound beta <= alpha and the strict empirical inequality. Insufficient confidence allocation and an inconclusive margin are reported separately. All physical budgets are nonnegative. If calibration establishes those budgets only with failure probability gamma, that additional failure event must be accounted for separately; the present result conditions on valid budgets.

For the accepted model at t=1/2,p=1/4, the true retained gap is 5/16 and reset allowance is 1/8. With n_0=n_1=4096, rho_0=rho_1=1/32 and zero observation bias, k_0=k_1=8 gives total failure bound 1/64. On simultaneous coverage, empirical gap is at least 1/4, above rejection threshold 3/16. Prove the corresponding non-vacuous power result and connect the means and allowance to the actual existing partial-interaction theorems. The same test applied to an admissible common-system null must obey its false-positive bound.

The example's quantified power is rejection probability at least 63/64; its proof consumes simultaneous coverage and the existing trajectory/reset-distance results. It is not merely an example of favorable counts. The design received an independent read-only scientific review before implementation; confidence gating, calibration validity and the quantified power conclusion are explicit acceptance requirements.

## Packages and acceptance

- S1: `lean/SKEFTHawking/QuantumNetwork/BinaryMemorySampling.lean`: concentration derived from bounded independent samples; joint coverage; dyadic conservative tail certificate; common-channel false-positive guarantee; power and actual partial-interaction example. Use the admitted slot and MCP loop. Root owns aggregate imports and generated evidence. No new axioms, sorry or native_decide.
- S2: canonical sampling functions in `src/core/formulas.py` and `tests/test_memory_sampling.py`: validated exact inputs, rational report and hypothesis decision, explicit confidence budget, nontrivial decision/boundary and invalid-input tests. Seeded synthetic trials may demonstrate behavior but cannot establish coverage by simulation. No hardware or CUDA.
- S3: independent scientific and numerical review, authoritative build and axiom extraction, focused tests and the existing substrate gate, canonical counts/atlas sync and durable review receipt. Existing unrelated publication-corpus failures stay outside scope. Local public acceptance is the integration boundary.

Use the existing source, notebook and review workflows. This increment supplies a finite-observation statistical bridge; it does not infer a client's architecture, establish quantum-only memory, produce a new manuscript, add an adaptive test or silently revise an existing downstream run's pinned provenance. Publication positioning remains a potential D9 contribution subject to its separate review gates.

## Evidence

Implementation and acceptance evidence will be recorded here after verification. The owning process is unchanged; no new harness or scheduler is part of this increment.
