# Calibrated memory inference and temporal approximation

Status: complete and locally accepted after independent review and substrate gating. Builds on the accepted sampling increment at `147aea7f`. Root owns integration and the machine-local notebook. Public development and reviewed integration remain local on `codex/memory-calibration-coarse`; public main and remotes are unchanged.

## Objective and sequence

1. Justify reset and observation budgets from a specified fixed-sample calibration protocol and include calibration failure in the overall statistical guarantee. State what preparation, measurement stability and structural assumptions remain external. Basis measurements alone must not be represented as quantum state tomography.
2. Supply exact rational CPU calculations and reproducible cases using the same contract. Preserve earlier experiment records and provenance. Statistical decisions must distinguish an insufficient margin, inadequate confidence and unsupported assumptions.
3. Prove a temporal approximation bound with a concrete finite physical model. Identify both a regime in which old history can be discarded with bounded prediction error and a regime where forgetting is unjustified. Include operational binary measurement consequences and explicit resource accounting without claiming computational advantage.
4. Home accepted results in D9 through the existing publication mapping and absorption process. Map precise claims to proof and computation evidence, and leave existing manuscript deficiencies and submission readiness outside this increment.

## Acceptance

Scientific statements receive independent review before proof dispatch. Lean work uses admitted ADR-008 slots and the MCP proof loop; no project axioms, sorry, native_decide or heartbeat overrides may be shipped. Python physics calculations belong in `src/core/formulas.py` with actual Lean references. Root performs authoritative aggregate builds, complete new-declaration axiom audit, canonical count/atlas sync, focused tests and substrate gating. Independent integrated review checks assumptions, non-vacuity, exact decision boundaries, existing-result preservation and documentation.

Use fixed protocols and sample sizes. Adaptive selection, optional stopping, unknown drift, arbitrary devices, quantum advantage, clock dynamics and horizon applications are not consequences of this increment. CPU remains the implementation target; CUDA is triggered only by a required simulation exceeding approximately ten hours.

## Work packages

- C1: calibrated statistical and physical contract, proofs, exact arithmetic and scientific review.
- C2: reproducible count-based examples and evidence-use documentation.
- G1: temporal approximation theorem, explicit forgetting model and obstruction/control.
- G2: exact CPU model comparison, error and operation-count examples.
- P1: D9 claim/evidence mapping and queued absorption, without manuscript readiness inflation.
- A1: independent integrated review, required gates and durable acceptance record.

C1, C2, G1, G2 and P1 are implemented and independently reviewed. A1 is complete: authoritative aggregate build, full new-declaration audit, canonical sync, 305 focused tests and substrate gate passed. Evidence is recorded in [the acceptance audit](../../audits/2026-09-10-memory-calibration-coarse.md) and the local notebook.

## C1 reviewed contract

Use a stable classical binary readout law `q(x)=a*(1-x)+(1-b)*x`, with false-positive and false-negative rates `a,b` in `[0,1]`. Trusted zero/one standards and two post-reset populations supply four calibration groups. Reset states are model-established diagonal qubit states; measuring a population does not establish diagonality. The same readout law applies during calibration and main trials. Standards, stability and independent fixed trials within each group remain explicit assumptions.

For calibration proportions `A,B,C0,C1` and fixed positive radii `sa,sb,s0,s1`, define `Ua=min(1,A+sa)`, `Ub=min(1,B+sb)`, `d=max(Ua,Ub)`, and `eps_h=min(1,Ch+sh+Ub)`. Simultaneous coverage implies true reset populations are at most `eps_h`, their trace distances from the zero state are at most `eps_h`, and readout bias is at most `d`. The random comparison allowance is `Bhat=min(1,eps0+eps1)+2*d`.

The main empirical gap must strictly exceed `Bhat+rho0+rho1`. Prove directly that rejection under the common-channel null is contained in the union of the six sampling-failure events. A fixed-budget theorem cannot simply be instantiated with a data-dependent budget. Sum the six conservative dyadic tails and cap at one; no independence between groups is required. Certification additionally requires this total bound to meet the predeclared failure level.

Concrete example: `t=1/2,p=1/4,a=b=1/256`; calibration groups each have `n=81920,radius=1/128`, main groups each have `n=20480,radius=1/64`. Counts `[320,320,320,10480,80,6430]` in the order above are illustrative exact-mean counts. Each tail exponent is ten, total failure bound `3/256`, and requested level `1/64`. Prove a model-linked positive-power result as well as evaluating favorable counts. Numeric design review establishes a worst-coverage margin `13/2048`; the implementation and independent review verified it. The explicit finite binary law has power at least `253/256`.

## G1 reviewed direction

The implemented driven replacement channel `Phi_b(rho)=lambda*rho+(1-lambda)*|b><b|` is realized by the existing normalized probabilistic SWAP and partial trace. For varying retention parameters, a common suffix contracts trace distance by exactly their product; constant retention gives `lambda^L`. Proofs establish binary prediction error and operational saturation on orthogonal suffix-boundary states. Any common scalar predictor has worst-case error at least half the product over arbitrary boundary states, which need not be reachable through a fixed prefix. At `lambda=1`, old boundary information need not decay; at zero retention a collision erases it. Exact CPU examples distinguish full replay from suffix replay and count their scalar updates. This is finite-history approximation in the stated model, without arbitrary retained outputs, feedback or a general compression/speedup claim.
