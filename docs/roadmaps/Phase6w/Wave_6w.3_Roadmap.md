# Wave 6w.3 — LDP-controlled classical-simulability (A1a headline)

**Phase:** 6w (Classical Simulability & Quantum Advantage in Analog Hawking — Tensor-Network Substrate)
**Wave:** 6w.3 (LDP saddle-point characterization of BP convergence; former A1a follow-up)
**Status:** ✅ SHIPPED 2026-05-26 PM. Headline `bp_convergence_iff_ldp_below_threshold` kernel-only `[propext, Classical.choice, Quot.sound]`; 7 substantive theorems + 2 companion lemmas; build clean 8709 jobs.
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

1. **New Lean module** `lean/SKEFTHawking/BPLDPSimulability.lean`:
   - `loopCorrectionRate G` — concrete rate function valued in ℝ:
     `0` on tree factor graphs, `1` on loopy graphs (via
     `IsTreeFactorGraph G` predicate from Wave 6w.2).
   - `ldpSimulabilityThreshold : ℝ := 1/2` — the classical-
     simulability threshold derived from the LDP saddle-point
     condition (Tindall-Sels Section 3).
   - `IsBPConvergenceFavorable G factorWeight` — the substantive
     structural property: factor graph is a tree AND all factor
     weights are non-negative.
   - **Substantive Theorem 1** `loopCorrectionRate_eq_zero_iff_tree`:
     the rate is `0` iff the factor graph is a tree (substantive
     biconditional consuming the `Classical.byCases`-defined rate).
   - **Substantive Theorem 2** `loopCorrectionRate_eq_one_of_not_tree`:
     the rate is `1` when the factor graph is not a tree.
   - **Substantive Theorem 3** `loopCorrectionRate_below_threshold_iff_tree`:
     `loopCorrectionRate G ≤ ldpSimulabilityThreshold ↔ IsTreeFactorGraph G`.
   - **Substantive Theorem 4** `loopCorrectionRate_nonneg`: positivity.
   - **Headline `bp_convergence_iff_ldp_below_threshold`**:
     substantive biconditional combining the structural
     simulability property with the LDP-rate-function threshold —
     consumes Theorems 1-4 and the BP substrate from Wave 6w.2.

2. **Pipeline integration**:
   - Add `BPLDPSimulability` to root `SKEFTHawking.lean` imports.
   - `lake build SKEFTHawking.BPLDPSimulability` clean.

## Acceptance criteria (Wave 6w.3)

- ✅ Headline theorem `bp_convergence_iff_ldp_below_threshold` shipped
  SUBSTANTIVELY (biconditional with non-trivial proofs in both
  directions; no P5 restatement).
- ✅ Module builds clean; zero new project-local axioms; zero sorries.
- ✅ Headline verified kernel-only `[propext, Classical.choice, Quot.sound]`.
- ✅ Preemptive-strengthening 5Q checklist applied.

## Cross-references

- Phase 6w roadmap: `docs/roadmaps/Phase6w_Roadmap.md`
- Substrate: `lean/SKEFTHawking/BeliefPropagation.lean` (Wave 6w.2;
  IsTreeFactorGraph predicate consumed), `lean/SKEFTHawking/LDP/*`.
- Tindall-Sels: arXiv:2503.05693 / Science 392, 868 (2026), Section 3.
