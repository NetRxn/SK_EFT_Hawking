# Phase 5j: Fermi-Point Gauge Emergence — |N|>1 → SU(2)

## Technical Roadmap — April 2026

*Prepared 2026-04-06 | Connects to the non-Abelian gauge wall (Critical Review §2.1)*

---

## 0. Motivation

The Critical Review v3 identifies Volovik's Fermi-point scenario as the "most promising route" to non-Abelian gauge structure from fermionic condensed matter. For |N|=1 (³He-A): U(1) gauge + Weyl fermions (experimentally confirmed). For |N|=2: SU(2) gauge + spin connection co-emerges (Volovik-Zubkov 2014).

The spin-connection co-emergence at |N|=2 is exactly what ADW needs for tetrad gravity. This could bypass the spin-connection gap identified in the Wen coupling analysis (Phase 5f: G_Wen is 6000x too weak, but the spin-connection gap is the true showstopper).

**Deep research pending:** `Phase5j_fermi_point_su2_emergence.txt` (SUBMITTED)

---

## Track A: Fermi-Point Topological Charge

### Wave 1 — Topological Charge Definition
**Goal:** Formalize the winding number of a Fermi point.

- [ ] Define N = winding number of Green's function singularity on S² surrounding Fermi point
- [ ] Connect to π₂(S²) = ℤ (Mathlib has homotopy groups?)
- [ ] |N| = 1 case: U(1) gauge emergence (already formalized in Wen context)
- [ ] `lean/SKEFTHawking/FermiPointTopology.lean`

### Wave 2 — |N|=2 → SU(2) Correspondence
**Goal:** Formalize the gauge emergence theorem for doubly-degenerate Fermi points.

- [ ] Define: |N|=2 Fermi point ↔ two Weyl cones ↔ SU(2) gauge symmetry
- [ ] State: spin-connection co-emerges with SU(2) (conditional on deep research)
- [ ] Connect to ADW mechanism: co-emergent spin connection feeds into tetrad condensation

### Wave 3 — Connection to Emergent Gravity
**Goal:** Close the loop: |N|=2 Fermi points → SU(2) spin connection → ADW tetrad → Einstein-Cartan.

- [ ] State the full chain as a conditional theorem
- [ ] Identify which steps are proved, which are conjectural
- [ ] Document the |N|=3 → SU(3) question (speculative, assessment from deep research)

---

## Deep Research

| # | Topic | File | Status |
|---|-------|------|--------|
| 1 | |N|>1 Fermi-point → SU(2) emergence | Phase5j_fermi_point_su2_emergence.txt | SUBMITTED |

---

*Phase 5j roadmap. The Fermi-point scenario is the bridge from condensed matter topology to non-Abelian gauge emergence — the route the Critical Review identifies as most promising.*
