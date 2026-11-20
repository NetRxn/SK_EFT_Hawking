# Finite intervention trees and finite clock diagnostics

These canonical functions are in `src/core/formulas.py`. The owning program is [PROCESS_CLOCK_PROGRAM.md](PROCESS_CLOCK_PROGRAM.md). Component tests, mathematical proofs, model applicability and final aggregate acceptance are separate evidence. Check the owning program for current acceptance.

## Exact finite process evaluator

`finite_intervention_process` takes positive integer `system_dim`, `environment_dim`, and `outcome_count`, a density matrix `initial`, and `protocol`. Joint basis order is system first, environment second. Every matrix entry is a Python integer or `Fraction`, or a tuple `(real, imaginary)` of those exact scalar types. Floating-point numbers, booleans, strings and symbolic expressions are refused. Output matrices always use pairs of `Fraction` values.

A terminal protocol is `None`. Every other node has exactly three keys:

- `evolution`: a list of joint Kraus matrices satisfying sum `K†K = I` exactly.
- `instrument`: one local Kraus family per outcome, with the sum over all outcomes and Kraus indices normalized exactly. Families must have the same length; pad impossible outcomes or unequal ranks with zero matrices.
- `next`: one child protocol per outcome. Distinct children implement classical feedback. All leaves must have the same depth, and the outcome count is fixed throughout.

Evolution occurs first; the local instrument acts as `K ⊗ I_environment`. The full tree is validated before evaluation, including cycles, dimensions, channel normalization and exact positive-semidefinite trace-one initial state. No branch is divided by its probability. Impossible outcomes remain zero matrices.

```python
from fractions import Fraction as F
from src.core.formulas import finite_intervention_process

z0, z1 = [[1, 0], [0, 0]], [[0, 0], [0, 1]]
report = finite_intervention_process(
    system_dim=2, environment_dim=1, outcome_count=2,
    initial=[[F(9,25), F(12,25)], [F(12,25), F(16,25)]],
    protocol={
        "evolution": [[[1, 0], [0, 1]]],
        "instrument": [[z0], [z1]],
        "next": [None, None],
    },
)
assert report["branches"][(0,)]["weight"] == F(9,25)
assert report["total_probability"] == 1
```

`branches` contains every prefix, including `()`, with its subnormalized state and exact weight. `leaves` lists complete histories. `prefix_marginals` independently sums complete-history weights sharing each prefix; this equals the corresponding branch weight when all future outcomes are included. Postselection is a different question. Reports also expose depth, arity and leaf count.

The Lean backing is `FiniteInstrument` and `FiniteInterventionProcess`, particularly `normalized_weights` and `no_future_signaling`. This is a realized finite model, not a representation theorem for arbitrary combs. The implementation is separately checked, not extracted from Lean. Full enumeration has `outcome_count**depth` leaves and retains all prefix matrices. Matrix dimensions, tree size and rational bit lengths remain caller-controlled; constant-dimensional states do not make history enumeration cheap.

## Exact coherent intervention example

`coherent_memory_process()` constructs actual protocols for the generic evaluator with `U = c I - i s SWAP`, default `c=3/5, s=4/5`. Both coefficients accept exact integers or fractions and must satisfy `c²+s²=1`. These rational complex matrices avoid trigonometric approximation.

```python
from fractions import Fraction as F
from src.core.formulas import coherent_memory_process

example = coherent_memory_process()
assert example["uninterrupted_one"] == F(49,625)
assert example["measured_one"] == F(337,625)
assert example["interference_contrast"] == F(288,625)
assert example["retained_one"] == (0, F(256,625))
assert example["control_one"] == (0, 0)
```

The uninterrupted case uses two coherent interactions with a singleton-effective identity intervention; its second outcome branch is explicitly impossible. The measured case inserts a resolved local Z instrument. Its exact two-outcome history table, rows for intermediate outcome and columns for final outcome, is `[[144,256],[144,81]]/625`. Changing only the later interaction to identity changes the joint distribution but preserves earlier marginals `16/25,9/25`.

The retained cases reset only the system between interactions. The controls add an explicit joint reset channel clearing both factors before readout. A separate feedback example prepares the state indicated by the first measured outcome; its diagonal histories each have weight one half and cross histories are zero. All examples consume the generic evaluator.

The default coefficients are backed by `CoherentMemoryProcess.coherent_probability`, `measured_table`, `interference_contrast`, `reset_probability` and `control_probability`. The explicit `coherent_readout_equivalence` and `reset_readout_equivalence` theorems connect singleton-outcome paths with external binary readout to padded arity-two final-instrument trees. Lean resets the environment in its control; Python clears both factors, which agrees after the exact system reset used here. Other rational coefficient choices remain separately tested computational instances, not instances of a parameter-general coherent theorem. The example distinguishes these chosen protocols, not every classical hidden-state or entanglement-breaking explanation. The reset-only contrast also has an incoherent-mixture realization. No experimental observation, quantum advantage or unusual-time claim follows.

## Floating finite Gibbs-clock comparison

`finite_gibbs_clock` accepts finite nonempty Hermitian `hamiltonian`, a matching arbitrary complex `observable`, positive real `beta` and `hbar`, and real `modular_time`. It computes the Gibbs density from the Hamiltonian spectrum, then independently reconstructs its matrix logarithm from the density spectrum.

Conventions are explicit: `sigma_s(X) = rho^(i s) X rho^(-i s)` and `alpha_t(X) = exp(i t H/hbar) X exp(-i t H/hbar)`. They agree at **`t = -beta*hbar*s`**. The sign is part of the contract.

```python
import numpy as np
from src.core.formulas import finite_gibbs_clock

clock = finite_gibbs_clock(
    hamiltonian=np.diag([0., 2.]), observable=np.array([[0., 1.], [1., 0.]]),
    beta=.4, hbar=1.3, modular_time=.7,
)
print(clock["physical_time"], clock["comparison_residual"])
```

The report returns density eigenvalues, matrix logarithm, both unitaries and evolved observables, plus comparison, trace-normalization, matrix-log and unitarity residuals. Energy shifting stabilizes Gibbs weights without changing density or observable evolution. Tiny anti-Hermitian roundoff within `64*eps*max(1,||H||_F)` is symmetrized and reported. Larger violations are refused. The spectral resolution floor `64*dimension*eps` deliberately refuses cases whose positive Gibbs eigenvalues cannot be reliably distinguished from numerical rank loss. This is conservative: some mathematically faithful states are outside the numerical diagnostic's supported domain.

These residuals are observations of floating arithmetic, **not certified error bounds**. The exact mathematical comparisons are `FiniteGibbsClock.modular_eq_heisenberg` and `matrixLog_gibbs`. The finite theorem does not certify the eigensolver, device Hamiltonian, physical interpretation of a clock, or a horizon identification. Degenerate energies, scalar Hamiltonians and scalar energy shifts are included; singular states are not silently treated as faithful.
