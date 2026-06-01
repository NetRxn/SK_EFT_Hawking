# Phase 6AD — Quantum-Network Substrate: reference-richness closure (Bucket 3)

**Status:** OPEN (2026-06-01). Bundle-target **D6 §6**. Closes the three "best-case reference richness" items deferred across Phases 6AA–6AC (the Bucket-3 list from the 2026-06-01 public-delivery gap assessment). Builds on 6AA/6AB/6AC (all DONE, Stage-13 GREEN).

**Inherited (do NOT re-litigate):** pin v4.29.1/5e932f97; native-build on bare Mathlib; Bell-diagonal/Werner real-parameter representation (no density matrices/traceNorm/diamond-norm); kernel-pure `{propext, Classical.choice, Quot.sound}`; no `maxHeartbeats`; no new project-local axioms. Per-wave Stage-9 (root import + counts regen). Leak discipline.

## Wave catalog
| Wave | Content | Status |
|---|---|---|
| **3.1** | Discharge the Horodecki Haar–Pauli integral `∫_{S²}(⟨ψ|σ_k|ψ⟩)²dμ=1/3` → teleportation **unconditional** | ✅ DONE (`HaarPauli.lean`, kernel-pure) |
| **3.2** | W1′ Tier-1 anchors: Calsamiglia–Lütkenhaus linear-optics BSM 50% bound + physics-only link rate `τ=L/(c·p_link)` | ⏳ PENDING |
| **3.3** | DEJMPS general-Bell-diagonal convergence (Macchiavello 1998), beyond the shipped Werner restriction | ⏳ PENDING |

## Progress log
- **3.1 — DONE** (`QuantumNetwork/HaarPauli.lean`, kernel-pure): proved the analytic bottleneck of the Horodecki proof entirely in Mathlib, density-matrix-free. `cosSq_mul_sin_integral` (`∫₀^π cos²θ·sinθ = 2/3`, via FTC `integral_eq_sub_of_hasDerivAt` with antiderivative `−cos³θ/3`); `blochKet`/`pauliZ`/`pauliExpZ` + **`pauliExpZ_blochKet`** (`⟨ψ|σ_z|ψ⟩ = cos θ`, the spinor expectation = Bloch z-coordinate, via `exp·conj exp=1` + `Real.cos_two_mul'`); `haarPauliBlochAverage`/`_eq` (`(1/4π)∫₀^{2π}∫₀^π cos²θ·sinθ = 1/3`); **`haarPauliZSqAverage`/`_eq`** (the genuine `∫_{S²}(⟨ψ|σ_z|ψ⟩)²dμ = 1/3`, composing the spinor identity with the spherical integral via `simp_rw` under the integral binders). Discharges the Phase-6AC `HaarPauliConstant` tracked hypothesis: `haarPauliConstant_haarPauliZSqAverage` + the **unconditional** corollaries `teleportAvgFidelity_horodecki_unconditional` (`f_avg=(2F+1)/3`), `teleport_beats_classical_iff_unconditional` (`f_avg>2/3 ↔ F>1/2`), `teleport_useful_over_chain_unconditional`. The W3 teleportation results now hold with NO hypothesis and NO axiom. Root-imported; counts 766 mod / 10036 thm / 0 axiom / 0 sorry.
