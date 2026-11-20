# Wave 6w.2 — Belief propagation on tensor networks (Mathlib substrate)

**Phase:** 6w (Classical Simulability & Quantum Advantage in Analog Hawking — Tensor-Network Substrate)
**Wave:** 6w.2 (Mathlib-PR-quality substrate for BP on factor graphs)
**Current status — 2026-10-18:** genuine BP/rank source and historical May26 build/kernel receipts retained. The [forest-rank/exact-marginal construction](../../audits/2026-10-17-publication-substance-construction/B2_FOREST_RANK_EXACT_MARGINALS.md), with [full independent review](../../audits/2026-10-17-publication-substance-construction/reviews/B2_FOREST_RANK_EXACT_MARGINALS.md), is independently accepted manual mathematics: all-pairs finite-forest ranks, horizon<=max(1,n), and exact normalized marginals for local nonnegative factors with Z>0, preserving q^(|V|-scope) constants. The five-node initial2 witness needs five sweeps at diameter four. Native/physical tensor-readout/precision-complexity and genuine Chern remain BUILD. Old normalization/diameter targets below are corrected to actual current source; no new native execution is claimed.
**Bundle target:** I1 substrate; later D7 candidate.
**LoE:** ~3-4 sessions per Phase6w_Roadmap.md.

---

## Goal

Build Lean substrate for **belief propagation (BP)** on tensor-network
factor graphs. The substrate must be substantive enough for Wave 6w.3
to consume it (LDP-controlled BP convergence headline) and Wave 6w.5
to consume the categorical-graph connection (Chern-marker bridge).

Tindall, Mello, Fishman, Stoudenmire, Sels (Science 392, 868 (2026),
DOI 10.1126/science.adx2728; arXiv:2503.05693) use belief propagation
as the contraction/optimization engine on lattice-specific tensor
networks. The BP cavity-marginal computation exploits the
approximately-tree-like structure of short-range correlations; on a
PEPS tensor network, BP converges when the Bethe free energy is at a
saddle point (equivalent to a Cramér-type LDP statement on the
divergence between the BP marginal and the true marginal).

## Substantive deliverables

1. **Actual source and remaining native deliverables** `lean/SKEFTHawking/BeliefPropagation.lean`:
   - Finite factor graph, ALL-pairs messages and synchronous unnormalized updates are actual source.
   - Factor updates sum over complete assignments; scope locality is not encoded. Normalization predicates do not prove update normalization.
   - `IsBPFixedPoint_iff_all_iterates_invariant` concerns ALL iterates; two-step recurrence alone is not sufficient.
   - Update/belief positivity, factorization and Bethe-functional identities are genuine at their scope, not the old normalization/Bethe-saddle assertions.
   - `bp_converges_on_ranked_acyclic` proves stabilization at sup(rank)+1 given a BPRankCert; the real star constructor is not an all-forest construction.
   - The accepted manual all-pairs forest construction gives horizon<=max(1,n) and a five-node singleton/unitfactor/initial2 counterexample to diameter4 stabilization.
   - Next implement native components/cardinality/path/certificate and local-factor normalized marginals with nonnegative weights, Z>0 and q^(|V|-scope) multiplicities. Literal q^|V| loops have no polynomial-in-graph-size guarantee.

2. **Citation registration**:
   - YedidiaFreemanWeiss2003 (NIPS BP-Bethe paper) — primary anchor.
   - Pearl1988 (original BP) — secondary anchor.
   - Additional secondary references as needed during proof.

3. **Pipeline integration**:
   - Add `BeliefPropagation` to root `SKEFTHawking.lean` imports.
   - `lake build SKEFTHawking.BeliefPropagation` clean.

## Current acceptance and historical source receipts

The [forest-rank/exact-marginal construction](../../audits/2026-10-17-publication-substance-construction/B2_FOREST_RANK_EXACT_MARGINALS.md), with [full independent review](../../audits/2026-10-17-publication-substance-construction/reviews/B2_FOREST_RANK_EXACT_MARGINALS.md), is independently accepted manual mathematics: all-pairs finite-forest ranks, horizon<=max(1,n), and exact normalized marginals for local nonnegative factors with Z>0, preserving q^(|V|-scope) constants. The five-node initial2 witness needs five sweeps at diameter four. Native/physical tensor-readout/precision-complexity and genuine Chern remain BUILD. Historical source build/kernel receipts remain preserved, not rerun. Existing no-new-axiom and fresh independent/native acceptance requirements remain. The old five-theorem completion checkbox is not current physical scientific completion.

## Stage-by-stage execution (multi-session)

- **Stage 1 (Constants + provenance, this sub-session):** create the
  Wave roadmap (this doc), set up the module skeleton with imports
  and structure-level scaffolding.
- **Stage 2 (Formulas):** no Python formulas — BP is pure
  combinatorics + finite-alphabet algebra. Document the Yedidia-
  Freeman-Weiss formulas in the module docstring.
- **Stage 3a (Lean interactive, multi sub-session):** author each
  theorem via the MCP loop with `lean_multi_attempt`. Decompose
  each into ≤12-term `have` sub-lemmas before iterating.
  - Sub-session 2a: FactorGraph + BPMessages + bpVariableUpdate +
    bpFactorUpdate + Theorem 1.
  - Sub-session 2b: bpUpdate + Theorem 2 + Theorem 3.
  - Sub-session 2c: BetheFreeEnergy + Theorem 4.
  - Sub-session 2d: Tree characterization + Theorem 5.
- **Stage 5 (Lean build):** clean at every sub-session close.
- **Stage 6-8 (tests, validation, viz):** No Python tests.
- **Stage 13 (Adversarial review):** Deferred to Wave 6w.7
  consolidated Phase-6w sweep.

## Cross-references

- Phase 6w roadmap: `docs/roadmaps/Phase6w_Roadmap.md`
- Substrate: existing `lean/SKEFTHawking/LDP/{Cramér,Sanov,Varadhan,
  Contraction}.lean` (consumed in Wave 6w.3 LDP-controlled
  convergence headline).
- Primary external: Yedidia-Freeman-Weiss 2003 NIPS;
  Pearl 1988 Probabilistic Reasoning.
- Tindall-Sels Wave 6w.1 foundation: `lean/SKEFTHawking/KibbleZurekUnruh.lean`.
