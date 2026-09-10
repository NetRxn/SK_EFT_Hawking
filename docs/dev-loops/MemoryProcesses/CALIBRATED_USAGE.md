# Calibrated inference and finite-history prediction

These calculations implement the contract in [CALIBRATION_COARSE_GRAINING.md](CALIBRATION_COARSE_GRAINING.md). Acceptance status and the final evidence receipt live there.

## Calibrated count test

Choose the entire protocol before looking at outcomes: two preparations, reset, common continuation and binary measurement, four calibration groups, two test groups, fixed sample sizes, positive radii and a total failure level. Independently repeated complete trials require fresh preparations, including the environment. Memory within a trial is permitted.

The supported calibration model has trusted basis standards and a stable classical confusion law `Q(x)=a*(1-x)+(1-b)*x`. The false-negative group counts **reported zeros on a trusted one standard**. Every other group counts reported ones. Separate reset-calibration groups sample the two post-reset populations. Reset states must be established as diagonal by the model or other evidence; basis counts do not establish this. For example, a coherent plus state has outcome-one population one half but trace distance from the zero state greater than one half. Population alone would underestimate its reset distance.

```python
from fractions import Fraction as F
from src.core.formulas import memory_calibrated_sampling_certificate

names = ('false_positive', 'false_negative', 'reset0', 'reset1', 'main0', 'main1')
counts = (320, 320, 320, 10480, 80, 6430)
groups = {
    name: dict(n=81920 if i < 4 else 20480, count=count,
               radius=F(1, 128 if i < 4 else 64))
    for i, (name, count) in enumerate(zip(names, counts))
}
report = memory_calibrated_sampling_certificate(groups=groups, alpha=F(1, 64))
```

These are synthetic, illustrative exact-mean counts for the specified partial-interaction model with `t=1/2,p=1/4` and readout rates `a=b=1/256`. They are not observations from a device. The derived comparison bound is `199/1024`, observed gap `635/2048`, strict margin `173/2048`, and total failure bound `3/256`. Main-sampling failure contributes `1/256`; calibration contributes `1/128`. Ignoring the latter would overstate confidence.

`reject_common_channel` requires both `confidence_sufficient` and `positive_margin`. Equality at the threshold is inconclusive. No rejection establishes neither absence of memory nor truth of the null. Support for preparations, readout stability and independent trials remains external; the calculator does not turn a supplied assertion into verified experimental evidence. A single joint union-bound argument accommodates dependencies between groups. Optional stopping, choosing the best of several protocols, uncontrolled drift and unmodeled coherent reset states are outside this guarantee.

Sample sizes/counts/cap must be strict integers, never booleans. Radii and alpha accept integers or `Fraction`; JSON adapters must parse exact rational values without floating-point conversion. The exponent cap only weakens confidence. The proof verifies mathematics; Python is separately reviewed and tested, not extracted from Lean.

## How much history can be discarded?

A fresh input bit collides with a retained qubit through a probabilistic identity/SWAP interaction. Discarding the fresh system gives the memory update `rho <- lambda*rho + (1-lambda)*|bit><bit|`, where `lambda` is retention and SWAP probability is `1-lambda`. Inputs are chronological and predetermined. Outputs discarded by this model are not available as extra measurement records.

```python
from fractions import Fraction as F
from src.core.formulas import memory_history_approximation

report = memory_history_approximation(
    inputs=[0]*8, retentions=[F(1,2)]*8,
    initial=1, reference=0, cutoff=8,
)
```

`cutoff` is the number of most recent rounds replayed from `reference`. The omitted prefix is replaced by that reference state. The report computes the complete trajectory and the suffix independently. Its prediction-error upper bound is the product of suffix retentions, here `1/256`; the example attains that bound. For arbitrary orthogonal memories at the truncation boundary, any predictor that sees only the common suffix has worst-case error at least half the product, here `1/512`. This lower bound need not hold for the smaller set of states reachable through a specified prefix; that prefix may already have erased their difference.

At retention one, the initial memory persists and this lower bound stays one half regardless of suffix length. A zero-retention collision erases prior memory. The formal model handles arbitrary density states; this exact rational CPU example represents diagonal states. Tests additionally evaluate joint rational matrix collisions, including coherent inputs, independently of the scalar recurrence.

Full replay uses N scalar updates; suffix replay uses L. Both can maintain a constant-size state while streaming, so this comparison does not imply a general simulation speedup or quantum advantage. The report also computes the prefix for diagnostics; its total runtime is not merely L updates. Prediction bounds apply to the modeled unconditioned memory state and a common downstream channel/measurement, not to arbitrary feedback or stored output histories.
