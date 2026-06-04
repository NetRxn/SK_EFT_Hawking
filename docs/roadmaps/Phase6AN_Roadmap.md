# Phase 6AN — Channel-composition, network-capacity, device-fidelity, and correct-by-construction compilation substrate

**Status: PLANNED 2026-06-04.** A cluster of substrate extensions that the quantum-information / quantum-network
/ verified-compilation arcs have been consuming in *assembled* form but which are not yet present as
**reusable, kernel-pure theorems**. Each wave below makes an existing implicit composition explicit, so that
downstream constructions cite a single load-bearing lemma instead of re-deriving it. Independent of, and
complementary to, Phase 6AM (the Lieb/DPI entropy frontier); 6AM Wave 5's rate-ceiling and this phase's
composition lemmas are the two halves of a complete network error-budget calculus.

> **⚠️ CHECK PhysLib FIRST (2026-06-04).** `leanprover-community/physlib` (arXiv:2510.08672, on our Mathlib
> v4.29.1 pin) provides a complete QI substrate — see Phase 6AM. Before proving anything QI-flavored here from
> scratch, check PhysLib: **Wave 1 (channel-composition / diamond subadditivity)** overlaps PhysLib
> `QuantumInfo/Finite/Distance/*`, and **Wave 2 (network capacity)** overlaps `QuantumInfo/Finite/Capacity.lean`
> — prefer adopting/bridging (per Phase 6AM) over re-deriving. Waves 3–5 (composed coherence⊕gate-cost bound,
> FDT amplifier/detector floor, correct-by-construction compilation) are device-/compilation-specific and are
> NOT in PhysLib — those stand as written.

**Standing invariants:** kernel-pure `{propext, Classical.choice, Quot.sound}`; no new project-local axioms
(Invariant #15); no `native_decide`; no `maxHeartbeats` in proof bodies; decompose-before-asserting-walls;
never push. Reachability verdicts recorded honestly per wave.

---

## Wave 1 — channel-composition diamond-distance subadditivity

- **Goal:** `diamondDist (Φ₂ ∘ Φ₁) (Ψ₂ ∘ Ψ₁) ≤ diamondDist Φ₂ Ψ₂ + diamondDist Φ₁ Ψ₁` (and the sequential
  single-target form `diamondDist (Φ∘Ψ) (Φ'∘Ψ') ≤ …`). **Verdict: reachable — standard, toeholds present.**
- **Why:** turns a multi-stage pipeline's end-to-end error into a *provably composed* budget of per-stage
  errors — the kernel-pure lemma under any concatenated-channel error-budget reasoning.
- **Toeholds:** `QuantumNetwork/DiamondNorm*`, `DiamondBudget`, `DiamondSDP*` modules; CPTP-contractivity
  (`traceNorm_krausMap_le`).
- **Gate:** `diamondDist_compose_le` kernel-pure + a worked 2-stage instance.

## Wave 2 — multipath entanglement-distribution network capacity

- **Goal:** generalize single-path bottleneck capacity (`composite = min-cut over a path`) to a **network**:
  the max achievable end-to-end capacity over a graph equals the min-cut over all source–sink cuts
  (max-flow-min-cut for entanglement-distribution capacities). **Verdict: reachable-moderate** — graph-theoretic;
  check Mathlib for an existing max-flow-min-cut (likely partial) and build the capacity-specialization.
- **Why:** lifts routing/capacity reasoning from a single path to a real network topology.
- **Bricks:** capacity-weighted graph; cut/flow definitions; max-flow-min-cut (port/build); specialize to the
  per-link repeaterless capacity.
- **Gate:** `network_capacity_eq_minCut` (or the achievable lower + converse upper bounds) kernel-pure.

## Wave 3 — composed average-gate-fidelity bound (coherence ⊕ gate-error)

- **Goal:** an average-gate-fidelity (or diamond-distance) bound for a physical gate that **composes** the
  coherence-limited contribution (Phase 6AK.1 `avgGateFidelity_coherenceChannel`) with an explicit
  control/gate-error contribution, yielding a single bound as a function of `(T₁, T₂, t_gate, ε_ctrl)`.
  **Verdict: reachable — device-physics composition over existing bounds.**
- **Why:** the coherence ceiling alone is non-binding when control error dominates; the composed bound is the
  one that actually constrains realizable fidelity across operating regimes.
- **Bricks:** model the realized channel as `coherenceChannel ∘ (control-error channel)`; apply Wave 1
  composition + the 6AK.1 closed form; bound the control-error term.
- **Gate:** `avgGateFidelity_composed_bound` kernel-pure + a worked regime where coherence binds and one where
  control error binds.

## Wave 4 — FDT-bound amplifier / detector noise figure-of-merit

- **Goal:** make the fluctuation-dissipation-theorem noise floor for a linear amplifier / detector operating
  point an explicit kernel-pure bound (Johnson/quantum-limited noise as a function of operating parameters),
  building on the existing `GloriosoLiu` / `QuantumCrooks` / `LDPLinearResponse` substrate. **Verdict:
  reachable — specialize existing FDT/Crooks/LDP machinery.**
- **Why:** completes the verifiable-operating-point-bound substrate for linear-response devices; the
  rare-event-tail (Crooks/LDP) and FDT-floor pieces become a single citable certificate-grade bound.
- **Bricks:** specialize `IsLDPRateFunction` + W-form Gallavotti–Cohen to the linear-amplifier noise current;
  the FDT floor as a positivity/monotonicity bound on the operating point.
- **Gate:** `fdt_noise_floor_bound` (+ rare-event-tail companion) kernel-pure; worked amplifier + detector
  operating points.

## Wave 5 — correct-by-construction compilation *(large sub-program; may spin to its own phase)*

- **Goal:** lift the verified-compilation arc (bundle D8: Solovay–Kitaev / Ross–Selinger / Clifford+T /
  Clifford+CCZ density + length bounds) from **per-output certification** to **correct-by-construction**: prove
  the *compilation algorithm itself* correct, so every output provably meets its ε/length spec ("CompCert for
  the gate compiler"). **Verdict: large but in-wheelhouse — the SK quantitative density/length bounds already
  shipped are the load-bearing foundation.**
- **Why:** a verified *compiler* (algorithm proven once) is a categorically stronger guarantee than per-output
  checking, and the quantitative-SK substrate (`solovayKitaev_dawson_nielsen_quantitative_*`,
  `SkApproxCSuperQuadraticBound_holds`, the generic-SU(d) cascade) is the hard half already done.
- **Bricks (sketch — warrants dedicated planning, likely Phase 6AO):** formalize the compiler as a function on
  the gate alphabet; prove the loop invariant (each refinement step preserves the approximation/length
  contract); discharge termination + the final ε/length bound from the existing quantitative theorems.
- **Gate:** a `compile`-function-level correctness theorem for at least one alphabet (Clifford+T) such that the
  output's ε/length bound is a theorem about the algorithm, not a per-instance check.

---

## Sequencing
W1 (composition lemma — small, unblocks everything else) → W3 (device bound, builds on W1) → W2 (network
capacity) → W4 (FDT floor) → W5 (the compiler-correctness sub-program; schedule its own phase when reached).
W1 is the highest-leverage small win (one lemma under many downstream constructions).
