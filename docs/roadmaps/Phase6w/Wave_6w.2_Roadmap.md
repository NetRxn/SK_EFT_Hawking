# Wave 6w.2 — Belief propagation on tensor networks (Mathlib substrate)

**Phase:** 6w (Classical Simulability & Quantum Advantage in Analog Hawking — Tensor-Network Substrate)
**Wave:** 6w.2 (Mathlib-PR-quality substrate for BP on factor graphs)
**Status:** IN-PROGRESS
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

1. **New Lean module** `lean/SKEFTHawking/BeliefPropagation.lean`:
   - `FactorGraph` structure — bipartite factor graphs with finite
     variable + factor index types, decidable incidence, finite-
     alphabet state spaces.
   - `BPMessages G X` — variable-to-factor and factor-to-variable
     real-valued messages over a finite alphabet `X`.
   - `bpVariableUpdate` — single round of variable-to-factor update
     (canonical Yedidia-Freeman-Weiss 2003 formula).
   - `bpFactorUpdate` — single round of factor-to-variable update.
   - `bpUpdate` — combined single-pass iteration.
   - `BPFixedPoint` predicate.
   - `BPNormalized` predicate (sum-to-one normalization).
   - **Substantive Theorem 1** `bp_variable_update_normalized_iff`:
     a variable-to-factor message is normalized after update iff the
     incoming factor messages are normalized (substantive iff
     consuming finite-alphabet sum identities).
   - **Substantive Theorem 2** `bp_iteration_normalized_preserved`:
     under BP iteration starting from normalized messages, all
     subsequent messages remain normalized.
   - **Substantive Theorem 3** `bp_fixed_point_iff_two_iter_invariant`:
     a normalized BP message is at a fixed point iff its two-step
     iterate equals it.
   - `BetheFreeEnergy : FactorGraph → BPMessages → ℝ` definition
     (sum of per-variable entropies + per-factor energies).
   - **Substantive Theorem 4** `bethe_free_energy_nonneg_on_uniform`:
     the Bethe free energy is non-negative on the uniform-message
     starting point (substantive consequence of log-sum-inequality).
   - **Substantive Theorem 5** `bp_converges_on_trees_in_diameter_rounds`:
     on a *tree* factor graph (no cycles), BP converges to a fixed
     point in exactly `diameter(G)` rounds (substantive structural
     theorem requiring tree induction).

2. **Citation registration**:
   - YedidiaFreemanWeiss2003 (NIPS BP-Bethe paper) — primary anchor.
   - Pearl1988 (original BP) — secondary anchor.
   - Additional secondary references as needed during proof.

3. **Pipeline integration**:
   - Add `BeliefPropagation` to root `SKEFTHawking.lean` imports.
   - `lake build SKEFTHawking.BeliefPropagation` clean.

## Acceptance criteria (Wave 6w.2)

- ✅ Five substantive theorems shipped (Theorems 1-5 above); each
  uses non-trivial Lean infrastructure (Finset sums, decidable
  predicates, tree induction).
- ✅ Module builds clean; zero new project-local axioms; zero sorries.
- ✅ Kernel-only axiom closures on every headline (`propext`,
  `Classical.choice`, `Quot.sound`).
- ✅ Primary sources cached per Invariant #11.
- ✅ Preemptive-strengthening 5Q checklist applied; ruthless post-wave
  audit applied.

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
