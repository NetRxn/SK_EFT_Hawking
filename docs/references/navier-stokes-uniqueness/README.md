# Bounded classical uniqueness backport

This directory records the upstream attribution and exact source closure for the
67 vendored modules under `lean/NavierStokes`. Source and original pins are in
`source-manifest.json`; Apache-2.0 license is preserved verbatim in `LICENSE`.
Port modifications are listed in the manifest and marked in the affected source files.

The separate `NavierStokes` Lean library preserves upstream `autoImplicit=true`.
Its root imports only `NavierStokes.R3.WholeSpaceUniqueness`. Euler, Comparator
and challenge modules are outside the selected closure. The project stays on its
existing coupled Lean/Mathlib/PhysLib/REPL 4.32 pins.

The bounded closure compiles on the existing pins at `4390030d`: the project
build passed 10,911 jobs. Four files required the disclosed proof-normalization
adaptations; independent review confirmed unchanged theorem statements.
Original source hashes, import-closure completeness and the license were verified.
The elaborated axiom closure of `classical_uniqueness_on_Icc` contains exactly
`propext`, `Classical.choice`, and `Quot.sound`. This measured compatibility
supports the bounded backport without a coordinated toolchain upgrade.

Model-specific consumers must explicitly transport coordinates, derivatives,
support, measure and energy, and discharge the theorem's hypotheses.
The theorem concerns smooth classical flows with a compact reference and a
finite-energy competitor; it does not establish global or weak-solution uniqueness.

## Quantitative stability consumer

`SKEFTHawking.ClassicalFlowStability` derives nonzero-initial-error stability
from this closure's actual equal-force equations, pressure recovery and localized
energy identity. The squared L2 difference obeys `E(t) ≤ E(0) exp(2Gt)` when `G`
bounds the reference gradient; compact smooth reference support supplies a finite
nonnegative coefficient. Weighted initial energy is dominated by actual initial
energy before cutoff exhaustion. Zero initial error recovers pointwise uniqueness.

The six named theorems passed independent scientific review and raw standard-axiom
audits at `66eff70a`. The public aggregate includes this module at `b01e09e0` and
passed the authoritative build, epoch
`e373db382f79e373d00935c3433a60008b64918d7eac85cff1b336494a3ac756`.
The vendored source and provenance manifest are unchanged. Canonical extraction
adds exactly the six named stability records with ordinary core axioms and no
project axioms or dependency timeouts. Independent integrated review passed at
`4fcc7af1`; the final `s13-lean` gate passed in 445.7 seconds, retaining the same
19 unresolved paper-corpus failures. This quantitative consumer is accepted locally;
no publication or broader flow-regularity claim follows.

## Continuous-gradient stability

`ClassicalFlowTimeStability.lean` proves the actual energy bound
`E(t) <= E(0) exp(2 integral_0^t g)` for continuous nonnegative reference-gradient
envelopes. The localized PDE estimate has a cutoff error constant independent of
time and radius. An integrating factor supplies the scalar estimate, and cutoff
exhaustion transfers it to the actual squared L2 difference. Equal residuals,
smoothness, compact reference support and the finite-energy competitor remain
explicit. The vendored closure and its provenance are unchanged.

Constant envelopes recover the existing coefficient. For `g(t)=A+Bt`, the
actual PDE consumer has exponent `2At+Bt^2`; with positive initial error and
positive slope at an interior time, it is strictly smaller than the slab-maximum
estimate. This is a quantitative stability result, not an existence theorem.

Independent review accepted source `63794e0c`: all six existing stability
statements are preserved, one time-dependent cutoff-rate helper is added, and
the new module supplies nine theorems. All 16 current named declarations have
raw ordinary-core-axiom audits and clean source scans. Combined-source diagnostics
and post-build standalone module diagnostics pass. Aggregate `363508f6` passes
the authoritative build. Canonical and final gate acceptance is recorded below
when complete.

Post-build canonical extraction contains 41,912 records, adding 55: ten new
fluid declarations and 45 block-expectation records (42 named and three generated
support records). No prior record was removed. The preserved pressure-flux theorem
now depends on the new time-gradient helper; only its immediate proof-dependency
fields change, with its type and axiom fields unchanged. All added and changed
closures have ordinary core axioms, no project axioms and no dependency timeout.
Final integrated review and the substrate gate remain pending.
