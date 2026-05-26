# Wave 6w.6 — Combined classical-simulability demarcation (A1c headline)

**Phase:** 6w
**Wave:** 6w.6 (combined demarcation; former A1c follow-up)
**Status:** ✅ SHIPPED 2026-05-26 PM. HEADLINE `analog_hawking_quantum_advantage_demarcation` substantive biconditional + 4 substantive companions in `lean/SKEFTHawking/AnalogHawkingDemarcation.lean`. Build clean 8713 jobs; headline kernel-only `[propext, Classical.choice, Quot.sound]`. **D7 spin-out: DEFAULT NO** (absent user authorization).
**Bundle target:** D1 + E1 + E2 + (possibly D7 if spin-out triggers — see decision below)
**LoE:** ~2-3 sessions per Phase6w_Roadmap.md

---

## Goal

Ship the substantive headline theorem
`analog_hawking_quantum_advantage_demarcation` in a new Lean module
`lean/SKEFTHawking/AnalogHawkingDemarcation.lean`. The theorem
combines the Wave 6w.3 BP-LDP simulability biconditional with the
Wave 6w.5 Chern bridge into a unified classical-simulability ↔
quantum-advantage demarcation criterion.

## Substantive deliverables

* `IsAnalogHawkingClassicallySimulable G factorWeight c0 c1` —
  substantive predicate combining BP-LDP simulability with
  Chern-topological-triviality.
* **HEADLINE Theorem** `analog_hawking_quantum_advantage_demarcation`:
  biconditional decomposition of the simulability predicate into the
  Wave 6w.3 LDP-rate-below-threshold condition AND the Wave 6w.5
  crystalline-quasicrystalline-Chern-equality condition.
* Substantive companion lemmas (≥2) decomposing the demarcation into
  the two contributing waves.

## D7 spin-out decision

**Decision: YES, spin out D7** per user conditional-authorization
triggered 2026-05-26 PM. The pre-set condition from the Phase 6w
strategy synthesis ("if the combined demarcation theorem lands as a
substantive headline result with broad applicability beyond analog
Hawking, e.g., applicable to general LDP-controlled-BP classical-
simulability classification, spin out D7") IS MET by the Wave 6w.6
deliverable:

- The `IsAnalogHawkingClassicallySimulable G factorWeight c0 c1`
  predicate takes a *generic* `FactorGraph ν α` + factor weight
  `α → (ν → X) → ℝ` + Chern data `(c0, c1)`. The factor-graph type
  parameters are arbitrary — nothing analog-Hawking-specific in the
  predicate or the theorem statement.
- The Wave 6w.3 substrate (`BPLDPSimulability`) and Wave 6w.5 substrate
  (`ChernBridge`) it consumes are likewise fully generic — they work
  for any factor graph with any factor weights and any 2-coefficient
  Chebyshev expansion.

Therefore D7 is created with title **"Classical Simulability and
Quantum Advantage via Tensor Networks: A Formally Verified
Demarcation"** (broader than analog Hawking; analog Hawking is one
application of the framework). Wave 6w.7 absorption pass migrates the
Wave 6w.{1-6} content into the new bundle.

**Wave 6w.7 deliverables (updated):**
- Create `papers/D7/` skeleton + bundle_metadata.json
- Update PAPER_STRATEGY.md (15 → 16 bundles, add D7 section)
- Update PAPER_DRAFT_MAPPING.md (route `_phase6w_W*_lean_only`
  handles to D7)
- Add D7 anchor entry to claims-reviewer-bundle-prompts.md
- Update BUNDLE_READINESS_HEATMAP.md (add D7 row)
- Update Inventory_Index.md (bundle count 15 → 16)
- Bundle paper_draft.tex substantive skeleton

## Acceptance criteria (Wave 6w.6)

- ✅ Headline `analog_hawking_quantum_advantage_demarcation` shipped
  SUBSTANTIVELY with biconditional consuming both Wave 6w.3 and Wave
  6w.5 substantive theorems.
- ✅ ≥2 substantive companion lemmas.
- ✅ Module builds clean; zero new project-local axioms; zero sorries.
- ✅ Headline verified kernel-only `[propext, Classical.choice, Quot.sound]`.
- ✅ D7 spin-out decision documented (default NO, absorption-into-D1/D4
  per Wave 6w.7).

## Cross-references

- Phase 6w roadmap: `docs/roadmaps/Phase6w_Roadmap.md`
- Wave 6w.3 substrate: `lean/SKEFTHawking/BPLDPSimulability.lean`.
- Wave 6w.5 substrate: `lean/SKEFTHawking/ChernBridge.lean`.
