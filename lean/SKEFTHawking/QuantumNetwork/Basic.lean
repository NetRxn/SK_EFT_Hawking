import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.LinearAlgebra.Matrix.Trace

/-!
# Quantum-Network Substrate (Phase 6AA) — root module

Entry point for the verified quantum-network protocol substrate (bundle D6).
Channel models, the Bell-diagonal/Werner fidelity expression, entanglement-swapping
and distillation operations, and the parameterized envelope theorems live in the
sibling modules under `SKEFTHawking.QuantumNetwork.*`.

Architecture (Phase 6AA): metrics are expressed in the Bell-diagonal / Werner
fidelity-parameter representation — explicit real-parameter expressions, not
general density matrices — so the substrate is real-analysis on those expressions
(`norm_num` + transcendental interval bounds + `PolyQuotQ`/`QCyc`). No external
quantum-information dependency.

## Layers in this sub-package

The sub-package has outgrown the network-protocol framing above: the later phases grew a
general quantum-information substrate around it, and these layers now share it. Named here
because nothing else states the sub-package's shape as a whole (migrated from the retired
`SK_EFT_Hawking_Inventory_Index.md` §3.1, per ADR-013 D6).

* **Diamond norm** — the diamond distance on channels through its Choi and SDP-dual
  characterisations, with attainment, witnesses, a budget calculus, and the operator-norm →
  diamond conversion that turns a gate-synthesis error into a certified channel error.
* **Entropy** — von Neumann and quantum relative entropy, Klein's inequality, concavity and
  subadditivity, and the Fannes–Audenaert continuity bound up to its sharp constant.
* **Negativity / PPT** — partial transpose, negativity and log-negativity, their monotonicity
  and continuity, and the maximally-entangled / Bell / Pauli-Choi evaluations.
* **Majorization** — spectral and vector majorization with the Lidskii–Wielandt and Mirsky
  eigenvalue-perturbation bounds.
* **Rates and capacity** — network capacity and its strong duality, the PLOB and erasure rate
  bounds, secret-key and distillation rates, repeater chains, swapping and teleportation.
* **Device-characterisation envelopes** — readout-relaxation and thermal-population assignment
  floors, decay envelopes, the FDT noise floor, QEC suppression and benchmarking bounds, stated
  in the SAME universally-quantified coherence parameters that bound the gate side.
* **Fidelity** — state and gate fidelity, their data-processing and Kraus forms, the block-form
  and PSD attainment routes, and the composed-gate bounds.
* **Channels and bridges** — CPTP and named channel models, the Gaussian moment / Wick route,
  the kernel-only transcendental enclosures, and the PhysLib transfer supplying the trace-norm
  toolbox.

Each module's own header carries its phase, wave and provenance; this list names *layers*, not
modules, so that it cannot drift as modules land. `docs/counts.json` (`lean.module_names`) is
the authority on what the sub-package actually contains.

Invariants: kernel-pure (`{propext, Classical.choice, Quot.sound}`), zero sorry,
no project-local axioms, no `maxHeartbeats` in proof bodies.
-/

namespace SKEFTHawking.QuantumNetwork

/-- Marker that the Phase-6AA substrate root compiles; replaced by real
definitions in Wave 1+. Kept trivial to avoid premature coupling. -/
theorem quantumNetwork_substrate_ready : True := trivial

end SKEFTHawking.QuantumNetwork
