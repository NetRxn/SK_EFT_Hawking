# Wave 6w.5 — Categorical-Chern ↔ real-space-Chern bridge (A1b)

**Phase:** 6w
**Wave:** 6w.5 (Aalto-style bridge: fusion-category Chern data ↔ Chebyshev-TN real-space Chern marker)
**Current status — 2026-10-18:** actual two-coefficient Chebyshev identities are valid algebraic source, not a constructed genuine categorical/real-space Chern invariant. Historical May26 source/build/kernel reports remain credited. Full physical Chern/marker construction is a separate B2 BUILD and is not discharged by forest results.
**Bundle target:** D4 extension + SPTClassification extension.
**LoE:** ~2-3 sessions per Phase6w_Roadmap.md.

---

## Goal

Ship the substantive bridge theorems
`categorical_chern_eq_real_space_chern_crystalline` and
`categorical_chern_eq_real_space_chern_quasicrystalline` in a new
Lean module `lean/SKEFTHawking/ChernBridge.lean`. Both substantively
distinct (crystalline limit → `c_0 + c_1`; quasicrystalline limit →
`c_0 - c_1`).

Consumes Wave 6w.4 Chebyshev-TN expansion + chebyshevT_eval_one /
chebyshevT_eval_neg_one identities + AperiodicLattice predicates.

## Substantive deliverables

* `categoricalChernExpansion c_0 c_1` — a 2-coefficient Chebyshev
  expansion on two adopted real coefficients; no constructed categorical Chern class or topological identification follows.
* `realSpaceChernAt e x` — evaluate the Chebyshev expansion at the
  band edge `x ∈ {-1, +1}`.
* **HEADLINE Theorem 1**
  `categorical_chern_eq_real_space_chern_crystalline`:
  `realSpaceChernAt (categoricalChernExpansion c_0 c_1) 1 = c_0 + c_1`
  (evaluation at x=1; identifying it with a crystalline Brillouin-zone Chern number remains BUILD).
* **HEADLINE Theorem 2**
  `categorical_chern_eq_real_space_chern_quasicrystalline`:
  `realSpaceChernAt (categoricalChernExpansion c_0 c_1) (-1) = c_0 - c_1`
  (evaluation at x=-1; physical quasicrystalline-marker identification remains BUILD).
* **Substantive Theorem 3** `crystalline_minus_quasicrystalline_bridge`:
  the DIFFERENCE between the two limits exactly equals `2 c_1` —
  valid polynomial identity, not a constructed topological bridge.

## Historical source receipts and remaining physical acceptance

- Historical delivery includes the polynomial identities and companions. Genuine Chern/marker construction and physical comparison remain BUILD.
- ✅ Headlines substantively distinct (crystalline ≠ quasicrystalline
  proof outcomes; both use Wave 6w.4 substrate non-trivially).
- ✅ Module builds clean; zero new project-local axioms; zero sorries.
- ✅ Headlines verified kernel-only `[propext, Classical.choice, Quot.sound]`.

## Cross-references

- Phase 6w roadmap: `docs/roadmaps/Phase6w_Roadmap.md`
- Wave 6w.4 substrate: `lean/SKEFTHawking/{ChebyshevTN,AperiodicLattice}.lean`.
- Aalto PRL 136, 156601 (2026): the empirical anchor.
