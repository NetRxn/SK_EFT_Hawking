# Phase 6AB — Verified Quantum-Network Substrate II (decay-inclusive envelope + breadth)

**Status:** OPEN (2026-06-01). Bundle-target D6 §6. Builds on **Phase 6AA** (DONE, Stage-13 GREEN — see `Phase6AA_Roadmap.md` for the inherited decisions D1–D3, Tier discipline, and the shipped `SKEFTHawking.QuantumNetwork.*` substrate). Extends the idealized memoryless swap-chain envelope to realistic + broader verified envelopes.

**Inherited (do NOT re-litigate):** pin v4.29.1/5e932f97; native-build on bare Mathlib (no LQI/native_decide/LeanCert); Bell-diagonal/Werner real-parameter representation (no density matrices/traceNorm); model-independent FIDELITY target; Pauli-error basis; dB-primitive attenuation; kernel-only NumericalBounds squeeze. **Stage-9 wiring (root import + counts regen) is part of shipping each wave** (the 6AA REQUIRED miss). **Leak:** never write the hyphenated private-repo directory name in public files (literal pre-commit grep).

## Wave catalog
| Wave | Content | Status |
|---|---|---|
| **W2 (FLAGSHIP)** | Decay-inclusive end-to-end envelope: `memoryDegradedFidelity` + `memoryDegraded_wernerParam` (multiplies Werner param by e^(−2t/τ)) + range + `decayInclusive_fidelity_envelope` (k-swap chain of memory-degraded links, F∈[1/4,1], t≥0, τ>0 ⟹ end-to-end ∈[1/4,1]) + antitone-in-t | ✅ DONE (`3518344f`, `DecayEnvelope.lean`, kernel-pure; counts 760 mod / 9992 thm) |
| **W1** | NumericalBounds macro layer: exp_squeeze/log_squeeze over Real.exp_bound/expNear + precision table (DR-INT §3) → arbitrary-operating-point exp(−x) bounds in 1–3 LoC | PENDING |
| **W3** | General Bell-diagonal: Klein-4 (ℤ₂×ℤ₂) convolution swap map (exact-formulas DR S1.2a–d) + fidelity/range envelope beyond Werner | PENDING |
| **W4** | Repeater breadth: BDCZ nested recursion at explicit N + secret-key-rate-style lower bound (real-parameter only) | PENDING |
| **W5** | Packaging: extend D6 §6 `sec:wstate:envelope` (LaTeX compile gate) + update preprint + fresh-context Stage-13 review → FULLY CLEAN | PENDING |

**OUT (not required for DONE):** Horodecki teleportation (Haar-integral lemma, research risk — optional W6); general density-matrix/trace-distance/diamond-norm layer (pre-demand: do NOT build); any private/product content (PUBLIC only).

**DONE:** W1–W5 kernel-clean; decay-inclusive + general-Bell-diagonal envelope + repeater-recursion/SKR proven; all new modules root-imported + counts regenerated; D6 §6 extended (compile-clean) + preprint updated; Stage-13 FULLY CLEAN.
