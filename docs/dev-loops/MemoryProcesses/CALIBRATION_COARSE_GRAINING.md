# Calibrated memory inference and temporal approximation

Status: authorized, design review in progress. Builds on the accepted sampling increment at `147aea7f`. Root owns integration and the machine-local notebook. Public development and reviewed integration remain local on `codex/memory-calibration-coarse`; public main and remotes are unchanged.

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

The per-package statements and evidence are recorded here as design review resolves them; this document does not treat proposed formulas or workers' reports as accepted results.
