# Wave 6w.3 — LDP-controlled classical-simulability (A1a headline)

**Phase:** 6w (Classical Simulability & Quantum Advantage in Analog Hawking — Tensor-Network Substrate)
**Wave:** 6w.3 (LDP saddle-point characterization of BP convergence; former A1a follow-up)
**Current status — 2026-10-18:** genuine continuous Bernoulli loop-density/Legendre source retained; actual headline `fourCycleFree_nonneg_iff_ldp_rate_zero` is a combinatorial screen, not BP dynamics or complexity. Historical May26 source/build/kernel reports remain dated receipts. The [forest-rank/exact-marginal construction](../../audits/2026-10-17-publication-substance-construction/B2_FOREST_RANK_EXACT_MARGINALS.md), with [full independent review](../../audits/2026-10-17-publication-substance-construction/reviews/B2_FOREST_RANK_EXACT_MARGINALS.md), is independently accepted manual mathematics: all-pairs finite-forest ranks, horizon<=max(1,n), and exact normalized marginals for local nonnegative factors with Z>0, preserving q^(|V|-scope) constants. The five-node initial2 witness needs five sweeps at diameter four. Native/physical tensor-readout/precision-complexity and genuine Chern remain BUILD.
**Bundle target:** D1 cross-bridge to LDP/ + new I-bundle section (later D7 candidate)
**LoE:** ~2 sessions per Phase6w_Roadmap.md

---

## Goal

Ship the substantive headline theorem `bp_convergence_iff_ldp_below_threshold`
in a new Lean module `lean/SKEFTHawking/BPLDPSimulability.lean`,
combining the Wave 6w.2 BP-on-TN substrate (`BeliefPropagation.lean`)
with the existing LDP framework (`LDP/`) into a biconditional
characterization of BP classical-simulability.

The Tindall-Sels physics: BP convergence on a PEPS tensor network is
governed by the LDP rate function of the loop-correction terms;
classical simulability of the underlying dynamics holds when this
rate function is below a computable threshold.

## Substantive deliverables

1. **Current source and retained physical target** `BPLDPSimulability.lean`:
   - Actual four-cycle count/density and Bernoulli MGF produce a Legendre rate `-log(1-loopDensity)`.
   - The old0/1 tree indicator and fixed1/2 threshold are not current source.
   - `fourCycleFree_nonneg_iff_ldp_rate_zero` characterizes four-cycle-freeness/nonnegative weights; a bipartite six-cycle passes while remaining loopy.
   - Ranked tree BP dynamics are separate. The accepted forest note supplies manual all-pairs ranks and conditional exact marginals, pending native integration.
   - Original physical dynamical-loop/LDP matching, convergence/error and computable simulation criterion on actual tensor/readout inputs remain BUILD. No quantum advantage follows from the screen.

2. **Pipeline integration**:
   - Add `BPLDPSimulability` to root `SKEFTHawking.lean` imports.
   - `lake build SKEFTHawking.BPLDPSimulability` clean.

## Current acceptance and historical evidence

Actual rate/Legendre source identities and historical source/kernel receipts remain credited. The [forest-rank/exact-marginal construction](../../audits/2026-10-17-publication-substance-construction/B2_FOREST_RANK_EXACT_MARGINALS.md), with [full independent review](../../audits/2026-10-17-publication-substance-construction/reviews/B2_FOREST_RANK_EXACT_MARGINALS.md), is independently accepted manual mathematics: all-pairs finite-forest ranks, horizon<=max(1,n), and exact normalized marginals for local nonnegative factors with Z>0, preserving q^(|V|-scope) constants. The five-node initial2 witness needs five sweeps at diameter four. Native/physical tensor-readout/precision-complexity and genuine Chern remain BUILD. No historical checkbox certifies a physical BP-LDP/complexity headline.

## Cross-references

- Phase 6w roadmap: `docs/roadmaps/Phase6w_Roadmap.md`
- Substrate: `lean/SKEFTHawking/BeliefPropagation.lean` (Wave 6w.2;
  IsTreeFactorGraph predicate consumed), `lean/SKEFTHawking/LDP/*`.
- Tindall-Sels: arXiv:2503.05693 / Science 392, 868 (2026), Section 3.
