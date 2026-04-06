# Phase 5h: Chirality Wall Phase 2 — 3+1D Formalization

## Technical Roadmap — April 2026

*Prepared 2026-04-06 | Follows Phase 5g*

**Entry state:** 2023 theorems (1949 substantive + 74 placeholder), 1 axiom, 88 modules, 28 sorry. Automated counts: `uv run python scripts/update_counts.py` → `docs/counts.json`. Zero heartbeat overrides. Aristotle Batch 2 in flight.

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

### Waves 1-2 — SPT Types + Gapped Interface Axiom — **COMPLETE**
**Goal:** Define SPT type infrastructure and state the TPF conjecture as a structured axiom.

- [x] `lean/SKEFTHawking/SPTClassification.lean` — 15 theorems + 1 axiom, ZERO sorry
  - SPTPhaseData: bulk/boundary dim, classification order, anomaly index
  - FreeFermionSPT: quadratic Hamiltonian, band topology
  - CommutingProjectorSPT: commuting terms, infinite-dim rotors, on-site symmetry
  - InterfaceData: codimension-1 junction between FF and CP realizations
  - GappedInterfaceProperties: gap > 0, unique ground state, short-range entangled
- [x] `gapped_interface_axiom` as structured axiom (registered in AXIOM_METADATA, eliminability: hard)
- [x] `anomaly_free_implies_chiral_gauge`: conditional theorem from axiom
- [x] `sm_generation_gapped_interface`: SM with 16 Majorana → gapped interface exists
- [x] `sm_three_gen_gapped_interface`: 3 generations → gapped interface exists
- [x] `no_gap_implies_anomalous`: contrapositive no-go (rigorous direction)
- [x] `kapustin_fidkowski_nogo`: finite-dim CP can't have nonzero Hall conductance
- [x] Bridge theorems to SpinBordism, Z16Classification, SMGClassification, ChiralityWallMaster
- [x] `lake build` clean (8123 jobs, 18s for module)
- [ ] Paper 7/8 update with axiomatized conjecture (deferred to doc sync)

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
| 1 | 3+1D chirality wall formalizability | Lit-Search/Phase-5h/Mapping the 3+1D chirality wall.md | **COMPLETE** |
| 2 | Mathlib categorical PR process | Lit-Search/Phase-5h/Contributing categorical infrastructure to Mathlib4.md | **COMPLETE** (shared with 5g) |

---

*Phase 5h roadmap. Updated 2026-04-06 (Track A W1-2 COMPLETE: SPTClassification.lean, 15 thms + 1 axiom. Track B W3-4 NOT STARTED. Track C W5 NOT STARTED). 2023 theorems, 88 modules, 28 sorry, 1 axiom. The chirality wall is the most actively contested frontier in lattice QFT. Our formal analysis is the only machine-checked contribution to this debate.*
