# Phase 5h: Chirality Wall Phase 2 — 3+1D Formalization

## Technical Roadmap — April 2026

*Prepared 2026-04-06 | Follows Phase 5g*

**Prerequisite:** Phase 5g Mathlib PR (Wave 5) gives credibility context for publishing chirality results.

---

## 0. Motivation

The chirality wall is "cracking" (Critical Review v3). Phase 5a formalized the 1+1D analysis: TPFEvasion (12 thms), GTCommutation (10 thms), GTWeylDoublet (12 thms), ChiralityWallMaster (17 thms) — 55 theorems establishing that TPF and GS operate in genuinely different mathematical frameworks.

Phase 5h extends to 3+1D, addressing the three gaps identified by the Critical Review.

**Deep research complete:** `Phase-5h/Mapping the 3+1D chirality wall.md`
**Key finding:** Three gaps with sharply different formalizability:
1. **TPF gapped interface** — precisely statable as axiom, but untestable (no numerical evidence)
2. **GT gauging step** — deepest mathematical obstruction (non-compact + Onsager algebra)
3. **Z₁₆ cobordism** — decomposes into tractable mod 8 (done!) + hard factor of 2

---

## Track A: TPF Gapped Interface Axiomatization

### Wave 1 — SPT Type Definitions
**Goal:** Define the type-theoretic framework for stating the conjecture.

- [ ] `lean/SKEFTHawking/SPTClassification.lean` — SPTClass, FreeFermionSPT, CommutingProjectorSPT types
- [ ] Spectral gap as a typeclass
- [ ] Interface Hamiltonian structure
- [ ] Connection to existing SpinBordism.lean

### Wave 2 — Gapped Interface Axiom + Consequences
**Goal:** State the conjecture and derive consequences.

- [ ] `gapped_interface_exists` as an axiom (registered in AXIOM_METADATA)
- [ ] Derive: anomaly-free → chiral lattice gauge theory exists (conditional theorem)
- [ ] Connect to our existing Z₁₆ classification

**Deliverables:**
- `lean/SKEFTHawking/SPTClassification.lean` (~15-20 theorems)
- Paper 7/8 update with axiomatized conjecture

---

## Track B: Gauging Step Analysis

### Wave 3 — Not-On-Site Symmetry Formalization
**Goal:** Formalize the GT not-on-site U(1) and Onsager algebra action.

- [ ] Extend GTWeylDoublet.lean with the non-compact charge spectrum
- [ ] Formalize the Onsager algebra → su(2) contraction as a gauging prerequisite
- [ ] State: disentangler exists → standard gauging applies (conditional)
- [ ] Formalize the Misumi instability result as a caveat

### Wave 4 — SMG-to-Chiral Gauging
**Goal:** Formalize the gap between vector-like SMG and chiral gauge coupling.

- [ ] Define SMG phase (gapped, symmetric, no Goldstones) as a structure
- [ ] State: SMG + anomaly cancellation → chiral gauge theory (conditional)
- [ ] Document the unsolved gauging step precisely

---

## Track C: Z₁₆ Algebraic Strengthening

### Wave 5 — Serre mod 8 Extensions
**Goal:** Strengthen the algebraic side (already σ ≡ 0 mod 8, try to push further).

- [ ] Assess: is mod 16 achievable algebraically for any subclass of lattices?
- [ ] Formalize the Smith normal form computation if tractable
- [ ] Connect E8⊕E8 (σ=16, mod 16 = 0) to the topological input

---

## Deep Research

| # | Topic | File | Status |
|---|-------|------|--------|
| 1 | 3+1D chirality wall formalizability | Phase-5h/Mapping the 3+1D chirality wall.md | **COMPLETE** |
| 2 | Mathlib categorical PR process | Phase-5h/Contributing categorical infrastructure to Mathlib4.md | **COMPLETE** |

---

*Phase 5h roadmap. The chirality wall is the most actively contested frontier in lattice QFT. Our formal analysis is the only machine-checked contribution to this debate.*
