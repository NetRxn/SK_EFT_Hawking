# Phase 6AA — Verified Quantum-Network Substrate

**Status:** OPEN (seeded 2026-06-01). Bundle-target: **D6** ("Formally Verified Fault-Tolerant Quantum Computation Substrate"; extends D6 §6 where `WStateQFT`/Wave 6v.6 already lives — the sibling-bundle-vs-extend-D6 question is a Stage-1 call).

**Trigger.** The Kyoto/Hiroshima 2025-09 single-shot projective W-state measurement (cyclic-shift symmetry → QFT on `Z_N`) is already formalized as a `Q(ζ_N)` cyclotomic decomposition in `SKEFTHawking.FaultTolerance.WStateQFT` (Wave 6v.6, D6 §6). Phase 6AA extends that point result to a **protocol-level verified-envelope substrate** for entanglement-based quantum networks: machine-checked bounds on the metrics network operators care about (entanglement-swapping fidelity, distillation yield, end-to-end fidelity under loss + decoherence).

**Headline goal.** Ship kernel-pure, parameterized **"metric ∈ [lo, hi]" envelope theorems**: given channel/protocol parameters, the end-to-end network metric provably lies in a certified interval. These are the first verified quantum-network-protocol bounds in any prover.

## Architectural decisions (pinned at phase open; do not re-litigate)

- **Toolchain/pin:** `leanprover/lean4:v4.29.1`, Mathlib `5e932f97`. Fixed; load-bearing for the existing library.
- **No external QI dependency.** Mathlib-at-pin provides the substrate (`Matrix.PosSemidef`, `Matrix.PosSemidef.kronecker` in `Mathlib.Analysis.Matrix.Order`, `Matrix.kroneckerMap`, Loewner order, C*-`cfc`) but **lacks** `traceNorm`, `partialTrace`, fidelity, trace distance, CPTP/Kraus, entropy, diamond norm (verified absent by direct `lean_loogle` probe 2026-06-01). The Lean-QuantumInfo library has these but pins v4.28.0 — two minors behind, and this repo is deliberately zero-extra-deps. **Native-build the focused primitives we need; borrow Lean-QuantumInfo's conventions only as reference.**
- **Bell-diagonal / Werner parameterization.** Repeater-network metrics (swapping fidelity, DEJMPS/BBPSSW purification, end-to-end fidelity under loss/decoherence) are, in the standard Briegel-Dür model, explicit polynomial/rational/transcendental expressions in a few real parameters — **not** general density matrices. So the envelope substrate is real-analysis on explicit expressions (`norm_num` + transcendental interval bounds + `PolyQuotQ`/`QCyc` for algebraic pieces). General density-matrix fidelity / trace distance / diamond norm are **out of scope** (return only for arbitrary-state certification, post-phase).
- **Unit discipline:** fiber attenuation is always carried with an explicit unit (neper/km vs dB/km); no defaulted convention (avoids the silent unit trap).

## Wave catalog

| Wave | Content | DR input | Module |
|---|---|---|---|
| **W0** | This roadmap + substrate root module (skeleton, builds clean) | — | `QuantumNetwork/Basic.lean` |
| **W1** | Channel models: fiber loss `exp(−αL)`, memory decoherence `e^{−t/T₂}`, heralding success; composition + monotone fidelity-decay lemmas | DR-SIM, DR-FORM | `QuantumNetwork/Channels.lean` |
| **W2** | Transcendental interval bounds: two-sided `norm_num`-checkable bounds on `Real.exp(−x)` / `Real.log` at device parameters | DR-INT | `QuantumNetwork/IntervalBounds.lean` |
| **W3** | Entanglement-swapping fidelity composition + DEJMPS/BBPSSW purification + W-state random-party distillation-rate (composes with `WStateQFT`) | DR-FORM | `QuantumNetwork/{Swapping,Distillation,WStateRate}.lean` |
| **W4** | Bell-diagonal/Werner fidelity as explicit real-parameter expression: range `[0,1]`, monotone decay, composition (no `partialTrace`/`traceNorm`/Uhlmann) | DR-FORM | `QuantumNetwork/Fidelity.lean` |
| **W5** | General parameterized envelope theorems (metric ∈ [lo,hi]) + D6 §6 absorption + Stage-13 review + bridging arXiv preprint | all | `QuantumNetwork/Envelope.lean` |

**Sequencing.** W0 → W1 → W2 → W3 → W4 → W5 (dependency order). Ship per-wave: `lake build` clean, zero sorry, kernel-pure `{propext, Classical.choice, Quot.sound}`, no `maxHeartbeats` in proof bodies, no new project-local axioms. Apply the preemptive-strengthening checklist before each theorem statement. The four Phase-6AA deep-research dossiers in `../../Lit-Search/Phase-6AA/` are advisory inputs — **verify every Mathlib lemma directly via lean-lsp before relying on a DR version-claim.**

**Stage-13.** Bundle-level adversarial review runs after W5 (last D6-contributing wave); precedes any D6 preprint refresh.

## Invariants (Phase 6AA)
- Kernel-pure; zero sorry; zero new project-local axioms; no `maxHeartbeats` in proof bodies (decompose instead).
- All metrics carry explicit physical units; every numerical bound is `norm_num`-backed and falsifiable.
- Substrate is self-contained under `SKEFTHawking.QuantumNetwork.*`; no external QI dependency.
