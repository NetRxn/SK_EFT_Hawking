# Phase 6AB — Verified Quantum-Network Substrate II (decay-inclusive envelope + breadth)

**Status:** OPEN (2026-06-01). Bundle-target D6 §6. Builds on **Phase 6AA** (DONE, Stage-13 GREEN — see `Phase6AA_Roadmap.md` for the inherited decisions D1–D3, Tier discipline, and the shipped `SKEFTHawking.QuantumNetwork.*` substrate). Extends the idealized memoryless swap-chain envelope to realistic + broader verified envelopes.

**Inherited (do NOT re-litigate):** pin v4.29.1/5e932f97; native-build on bare Mathlib (no LQI/native_decide/LeanCert); Bell-diagonal/Werner real-parameter representation (no density matrices/traceNorm); model-independent FIDELITY target; Pauli-error basis; dB-primitive attenuation; kernel-only NumericalBounds squeeze. **Stage-9 wiring (root import + counts regen) is part of shipping each wave** (the 6AA REQUIRED miss). **Leak:** never write the hyphenated private-repo directory name in public files (literal pre-commit grep).

## Wave catalog
| Wave | Content | Status |
|---|---|---|
| **W2 (FLAGSHIP)** | Decay-inclusive end-to-end envelope: `memoryDegradedFidelity` + `memoryDegraded_wernerParam` (multiplies Werner param by e^(−2t/τ)) + range + `decayInclusive_fidelity_envelope` (k-swap chain of memory-degraded links, F∈[1/4,1], t≥0, τ>0 ⟹ end-to-end ∈[1/4,1]) + antitone-in-t | ✅ DONE (`3518344f`, `DecayEnvelope.lean`, kernel-pure; counts 760 mod / 9992 thm) |
| **W1** | NumericalBounds tight Taylor-squeeze: `expNeg046_tight` via degree-5 `Real.exp_bound` + precision-table pattern (DR-INT §3) | ✅ DONE (`2b706dcb`) |
| **W3** | General Bell-diagonal Klein-4 swap map (`bellDiagSwapA/B/C/D`) + normalization + nonneg + `bellDiagSwapA_mem` envelope + `bellDiagSwapA_werner` bridge | ✅ DONE (`3332b438`, `BellDiagonalSwap.lean`) |
| **W4** | Repeater breadth: `endToEndFidelity_nest_double` (BDCZ) + `endToEnd_teleportation_useful` (F_e2e>1/2 ⟺ w^k>1/3) + `endToEndQBER` range/monotonicity (SKR threshold parametric) | ✅ DONE (`ca2a80c6`, `RepeaterChain.lean`) |
| **W5** | Packaging: D6 §6 extended (compile-clean) + preprint §3a + fresh-context Stage-13 → FULLY CLEAN (`bbaf7d8a`; review `docs/audits/stage13_phase6AB_2026-06-01.md`) | ✅ DONE |

**Counts:** 762 modules / 10,001 theorems / 0 sorry (11 QuantumNetwork modules, all kernel-pure).

## 🎯🎯 PHASE 6AB DONE (2026-06-01)
All DONE gates met: W1–W5 shipped kernel-clean; decay-inclusive envelope (`decayInclusive_fidelity_envelope`) + general-Bell-diagonal envelope (`bellDiagSwapA_mem`) + repeater-recursion/QBER (`endToEndFidelity_nest_double`, `endToEnd_teleportation_useful`, `endToEndQBER_*`) proven; all new modules root-imported + counts regenerated; D6 §6 extended (LaTeX compile-clean) + preprint updated; **Stage-13 GREEN — FULLY CLEAN, no findings**. Held-out (not required): Horodecki teleportation (Haar lemma), general density-matrix layer.

**OUT (not required for DONE):** Horodecki teleportation (Haar-integral lemma, research risk — optional W6); general density-matrix/trace-distance/diamond-norm layer (pre-demand: do NOT build); any private/product content (PUBLIC only).

**DONE:** W1–W5 kernel-clean; decay-inclusive + general-Bell-diagonal envelope + repeater-recursion/SKR proven; all new modules root-imported + counts regenerated; D6 §6 extended (compile-clean) + preprint updated; Stage-13 FULLY CLEAN.
