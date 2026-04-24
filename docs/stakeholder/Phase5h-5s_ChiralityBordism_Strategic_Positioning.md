# Phase 5h/5j/5n/5q/5r/5s: Chirality Wall 3+1D + Bordism Discharge — Strategic Positioning

*Last updated: 2026-04-24-1515.*

**Context:** Extends the Phase 5a Strategic Positioning memo (1+1D chirality wall) and the Phase 5b generation-constraint positioning. Covers the 3+1D extension of the chirality wall analysis plus the algebraic discharge of the bordism step in the modular generation constraint.

---

## Competitive Landscape

No competing formal-verification effort exists for the two central contributions of this arc. (1) **Lattice-chirality-wall formal analysis**: no other proof assistant has any formalization of the TPF construction, the Golterman–Shamir no-go, the Fidkowski–Kitaev 2+1D gapping, or the Villain Hamiltonian; Douglas et al. (March 2026) formalized free massive bosonic QFT in Lean 4 but touched no lattice theory, no fermions, and no chirality; PhysLean/HepLean addresses anomaly-polynomial bookkeeping at the SM level but not lattice constructions. (2) **Ext computations over Steenrod sub-algebras**: Mathlib's homological-algebra pipeline is entirely `noncomputable`; no concrete Ext group has previously been computed in any proof assistant, so the Phase 5q brute-force `native_decide` resolution is first-of-its-kind. (3) **Volovik–Zubkov Fermi-point → emergent-gauge-group formalization** has no prior formal counterpart. The window for establishing the definitive machine-checked reference on each of these fronts is open now.

---

## Publication Targets

| Work | Venue | Timeline | Status |
|------|-------|----------|--------|
| Paper 7 (Chirality formal — GS / TPF / GT) | TBD (previously positioned PRD or CPC) | TBD | Draft exists |
| Paper 8 (Chirality master — three-pillar + 3+1D + 2+1D ladder) | TBD (previously positioned CPC or RMP) | TBD | Draft exists |
| Paper 10 (Modular generation constraint, backed by Ext computation + change-of-rings) | TBD | TBD | Draft exists |
| Mathlib PR — Ext infrastructure / Steenrod sub-algebra components | Mathlib4 | TBD | Scoped (blocked on Mathlib AI-content relationship-building) |

Venues and timelines left as TBD reflect the project-wide submission posture: the per-paper readiness state machine (Phase 5v, 11 gates) gates submission, arXiv requires a voucher for first submissions, and Mathlib's AI-content policy requires substantive discussion before PR. No venue or timeline is invented here.

---

## IP and Priority

The TPF-vs-GS chirality debate is live in the lattice-QFT community, with PRL-level activity on both sides (Thorngren–Preskill–Fidkowski PRL 136, 2026; Butt–Catterall–Hasenfratz PRL 2025). This project's formal analysis is the *only* machine-checked contribution to that debate and remains so as of April 2026. The 2+1D FK machine-checked witness (`FKGappedInterface.lean`, first Fidkowski–Kitaev 2+1D Cayley-calibrated gapped-interface construction in any proof assistant) and the Ext computation over A(1) (first such computation in any proof assistant) are first-mover contributions whose priority is time-sensitive given active community discussion. The Volovik–Zubkov Fermi-point → emergent-gauge-group formalization (Phase 5j, first in any proof assistant) is likewise uncontested.

---

## Risks and Gaps

The arc does not paper over its limits. The `gapped_interface_axiom` in `SPTClassification.lean` is the project's **single remaining load-bearing axiom**, registered with eliminability tier "hard"; a proof in 3+1D or 4+1D is beyond currently known techniques, and numerical verification at 4+1D is not feasible at achievable lattice sizes. The 1+1D + 2+1D evidence ladder (Villain + FK) strengthens the axiom's tier from "1D-only evidence" to "1D + 2D proved in distinct mathematical frameworks" but does not close it. Three topological hypotheses remain for the generation-constraint chain after the Phase 5r H2 discharge: H1 (H*(ko; F₂) ≅ A ⊗_{A(1)} F₂, Adams 1974), H3 (Adams spectral sequence collapse at E₂ for ko, requires Bott periodicity — assessed as irreducibly topological, potential d₃(h₁²) → v only rulable by knowing π_*(ko)), and H4 (Anderson–Brown–Peterson splitting, 1967). Each is a standard textbook result, independently verifiable by a topologist; formalizing them would require algebraic-topology and spectrum-theory infrastructure that no proof assistant currently supports, on the order of 15–25 person-years. The Phase 5j SU(2)/SU(3) emergence claims carry explicit per-step `RigorLevel` tagging: users of that chain must respect the theorem / heuristic / speculative boundaries already encoded in the Lean source.
