# Stage-13 Adversarial Review — Phase 6AC (Verified Quantum-Network Substrate III)

**Date:** 2026-06-01
**Reviewer:** fresh-context adversarial agent (read-only; independently re-ran builds, axiom checks, leak greps, LaTeX compile, citation cross-check)
**Scope:** new modules `QuantumNetwork/{SecretKeyRate, MultipartiteComparison, Teleportation}.lean`; D6 §6 "Phase 6AC extensions" paragraph; bridging-preprint §3b; roadmap.

## Verdict: GREEN — FULLY CLEAN (advisory remediated)

| Check | Result |
|---|---|
| 1. Builds clean + kernel-pure (all 21 theorems' `#print axioms` ⊆ `{propext, Classical.choice, Quot.sound}`; zero sorry/native_decide/maxHeartbeats/axiom; `HaarPauliConstant` confirmed a `def : Prop`, not an axiom) | PASS |
| 2. No overclaiming / formula correctness (BB84 crossover proven via IVT `bb84_crossover_exists`, NOT hardcoded 0.11; W2 GHZ advantage honestly a cited modeling input, substantive content reduces to real inequality; Fortescue–Lo optimality conjecture explicitly not claimed; W3 Haar `1/3` is a tracked hypothesis, not an axiom; `(2F+1)/3`, `2/3 ↔ F>1/2` correct) | PASS |
| 3. No fabricated references (Fortescue–Lo, D'Hondt–Panangaden, Smolin–Verstraete–Winter, Horodecki PRA 60 1888, Massar–Popescu PRL 74 1259 all DR-backed; **Shor–Preskill PRL 85, 441 (2000)** now cited explicitly in D6 paragraph, preprint §3b, module docstring, and roadmap — advisory remediated) | PASS |
| 4. Stage-9 integration (3 modules root-imported in `SKEFTHawking.lean`; counts **765 mod / 10025 thm / 0 axiom / 0 sorry**, +3 modules over 6AB baseline) | PASS |
| 5. Leak discipline (zero private-sibling-repo identifier; zero product-framing terms `oracle/harness/cert/customer/product` in any public artifact) | PASS |
| 6. Scope honesty (no densityMatrix/traceNorm/partialTrace/diamond-norm; D6 LaTeX compiles, exit 0, no undefined refs) | PASS |

**Advisory (provenance) — REMEDIATED.** The reviewer flagged that the Shor–Preskill BB84 key-rate formula (`r=1−2h₂(e)`) lacked an explicit primary citation (the other five 6AC citations are DR-backed). Fixed by adding **Shor & Preskill, Phys. Rev. Lett. 85, 441 (2000)** to the D6 §6 paragraph, the preprint §3b, the `SecretKeyRate.lean` module docstring, and a new "Citations (primary sources)" block in the roadmap. No code change required for correctness.

Phase 6AC is complete: BB84 secret-key rate (crossover proven, not hardcoded), W₃-vs-GHZ₃ randomization-advantage comparison (Fortescue–Lo Thm 3.5), and Horodecki teleportation fidelity (probe-gated → tracked hypothesis, zero new axioms) — all kernel-pure, pipeline-tracked, D6 §6 + preprint updated.
