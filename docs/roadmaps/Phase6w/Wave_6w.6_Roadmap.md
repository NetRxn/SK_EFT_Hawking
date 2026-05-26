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

**Decision (default, no user authorization yet):** **DO NOT spin out
D7 in Wave 6w.6.** The combined demarcation theorem is substantive but
its applicability is captured in cross-bridges into existing bundles
D1 (analog Hawking, simulability cross-check) and D4 (TQC foundations,
Chern bridge as topological-marker substrate). Per the Phase 6w
roadmap "Default posture if undecided: absorb into D1 + E1 + E2
cross-bridges. Keep D7 as a Phase 7+ option." This default applies
absent explicit user authorization.

If a future session presents user authorization to spin out D7, the
absorption protocol of Wave 6w.7 covers the migration: `papers/D7/`
directory creation + bundle_metadata initialization + 15→16 bundle
update to PAPER_STRATEGY.md.

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
