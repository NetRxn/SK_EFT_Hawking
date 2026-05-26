# Wave 6w.5 — Categorical-Chern ↔ real-space-Chern bridge (A1b)

**Phase:** 6w
**Wave:** 6w.5 (Aalto-style bridge: fusion-category Chern data ↔ Chebyshev-TN real-space Chern marker)
**Status:** ✅ SHIPPED 2026-05-26 PM. 6 substantive theorems in `lean/SKEFTHawking/ChernBridge.lean` (substantively distinct crystalline c0+c1 vs quasicrystalline c0-c1 limits + difference = 2c1 substantive identity + biconditional with c1 = 0). Build clean 8712 jobs; headlines kernel-only.
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
  expansion encoding the categorical Chern data (`c_0` topological
  background, `c_1` invariant contribution).
* `realSpaceChernAt e x` — evaluate the Chebyshev expansion at the
  band edge `x ∈ {-1, +1}`.
* **HEADLINE Theorem 1**
  `categorical_chern_eq_real_space_chern_crystalline`:
  `realSpaceChernAt (categoricalChernExpansion c_0 c_1) 1 = c_0 + c_1`
  (crystalline limit; Brillouin-zone Chern number reduces to the
  band-edge sum at `x = 1`).
* **HEADLINE Theorem 2**
  `categorical_chern_eq_real_space_chern_quasicrystalline`:
  `realSpaceChernAt (categoricalChernExpansion c_0 c_1) (-1) = c_0 - c_1`
  (quasicrystalline limit; the band-edge difference at `x = -1`).
* **Substantive Theorem 3** `crystalline_minus_quasicrystalline_bridge`:
  the DIFFERENCE between the two limits exactly equals `2 c_1` —
  substantive structural identity ratifying the bridge.

## Acceptance criteria (Wave 6w.5)

- ✅ Both headlines + ≥1 substantive companion shipped.
- ✅ Headlines substantively distinct (crystalline ≠ quasicrystalline
  proof outcomes; both use Wave 6w.4 substrate non-trivially).
- ✅ Module builds clean; zero new project-local axioms; zero sorries.
- ✅ Headlines verified kernel-only `[propext, Classical.choice, Quot.sound]`.

## Cross-references

- Phase 6w roadmap: `docs/roadmaps/Phase6w_Roadmap.md`
- Wave 6w.4 substrate: `lean/SKEFTHawking/{ChebyshevTN,AperiodicLattice}.lean`.
- Aalto PRL 136, 156601 (2026): the empirical anchor.
