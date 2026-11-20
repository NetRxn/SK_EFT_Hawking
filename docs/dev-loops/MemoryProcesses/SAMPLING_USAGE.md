# Using the fixed-sample memory criterion

The [sampling increment](SAMPLING.md) connects a finite set of binary observations to a conditional test of a common system-only continuation. A positive result excludes that comparison class under its stated assumptions. It does not identify a unique architecture or establish quantum advantage. An inconclusive result does not establish absence of memory.

## Protocol and inputs

Choose the two preparations, common intervention and measurement, number of complete trials, sampling radii, error budgets and requested failure level before collecting the test observations. A complete trial contains the within-trial interactions and reset. Independent repeated trials require fresh preparations, including the environment. Reusing an environment between trials requires a different statistical argument.

Supply the counts of outcome one and total trials separately for each preparation. All counts and sample sizes must be Python integers; each sample size is positive and each count lies between zero and its size. Supply radii, budgets and the requested failure level as integers or `fractions.Fraction`, not floats. Sampling radii are positive; budgets are nonnegative; the failure level lies strictly between zero and one.

The reset budgets `eps0`, `eps1` bound trace distances of the actual post-reset system states from the same reference. The observation-bias budgets `delta0`, `delta1` bound differences between the sampled probabilities and exact Born probabilities. These inputs require physical or calibration justification; the function cannot establish them from the counts. If their calibration has its own failure probability, account for that separately.

## Exact example

From the repository root:

```python
from fractions import Fraction as F
from src.core.formulas import memory_sampling_certificate

report = memory_sampling_certificate(
    n0=4096, n1=4096,
    count0=0, count1=1280,
    rho0=F(1, 32), rho1=F(1, 32),
    eps0=0, eps1=F(1, 8),
    delta0=0, delta1=0,
    alpha=F(1, 64),
)
```

These illustrative counts give an empirical gap of `5/16`, a comparison allowance of `1/8`, a threshold including sampling radii of `3/16`, and a positive margin of `1/8`. The failure bound is `1/64`. Both the confidence check and strict margin check pass.

At the previously proved model point `t=1/2, p=1/4`, the exact underlying probabilities are zero and `5/16`, with reset allowance `1/8`. The probability theorem establishes detection probability at least `63/64` under its sampling assumptions. That power conclusion is about repeated sampling from the model; the displayed count pair alone is not evidence of power or a record of an experiment.

## Reading the report

`failure_bound` is the proved conservative upper bound on sampling failure for the supplied radii and sample sizes. `confidence_sufficient` checks whether it meets the requested `alpha`. `positive_margin` checks the strict empirical inequality. `reject_common_channel` requires both. Equality at the margin threshold is inconclusive. A positive margin with insufficient confidence is not a rejection at the requested level.

The certificate chooses natural exponents no greater than `2*n*rho**2` and bounds each tail by `2/2**exponent`. It computes proportions, bounds and decisions using rational arithmetic, avoiding floating-point logarithms or square roots. The report preserves exact values; converting them for display must not alter the decision path. Python is not extracted from Lean, so kernel verification of the mathematics and review/testing of this implementation remain distinct evidence.

`exponent_cap` is an explicit implementation resource limit between zero and 4096. Capping downward can only make the failure bound more conservative. The report exposes uncapped and used exponents and whether the cap applied. If the resulting bound misses `alpha`, the report says confidence is insufficient. Input integer/rational bit lengths remain caller-controlled.

## Scope of the guarantee

The statistical theorem permits independent bounded observations with the same mean within each group; fixed IID binary trials are a special case. It does not require independence between the two groups for the union bound. Fixed sample sizes are essential here: repeated peeking, stopping after a positive result, or choosing the most favorable setting from many tests requires additional error control. This function does not supply that control.

The common-channel comparison requires the same subsequent system channel and the same binary effect for both histories. History-dependent continuations or unbudgeted readout changes are different comparison models. Floating-point matrix simulations can help select a prospective experiment, but their computed reset distances are not automatically justified error budgets for this test.
