# Phase 5j: Fermi-Point Gauge Emergence — |N|>1 → SU(2)

## Technical Roadmap — April 2026

*Prepared 2026-04-06 | Connects to the non-Abelian gauge wall (Critical Review §2.1)*

**Entry state:** 2232 theorems (2150 substantive + 82 placeholder), 1 axiom, 94 modules, 33 sorry. **W1 COMPLETE** (FermiPointTopology.lean, 28 thms, 0 sorry). W2-3: NOT STARTED. Deep research COMPLETE.

---

## 0. Motivation

The Critical Review v3 identifies Volovik's Fermi-point scenario as the "most promising route" to non-Abelian gauge structure from fermionic condensed matter. For |N|=1 (³He-A): U(1) gauge + Weyl fermions (experimentally confirmed). For |N|=2: SU(2) gauge + spin connection co-emerges (Volovik-Zubkov 2014).

The spin-connection co-emergence at |N|=2 is exactly what ADW needs for tetrad gravity. This could bypass the spin-connection gap identified in the Wen coupling analysis (Phase 5f: G_Wen is 6000x too weak, but the spin-connection gap is the true showstopper).

**Deep research COMPLETE:** `Lit-Search/Phase-5j/Volovik |N|>1 Fermi-Point → SU(2) Gauge Emergence.md`

**KEY CORRECTIONS from deep research:**
1. TWO distinct mechanisms conflated in literature:
   - Mechanism A (single |N|=2 node) → anisotropic Hořava fermions, NOT SU(2)
   - Mechanism B (correlated |N|=1 nodes) → correct route, Z₂ symmetry → SU(2)
2. Z₂ → SU(2) promotion is a HEURISTIC (³He-A specific), not a theorem
3. Selch-Zubkov 2025: matrix-valued vierbein DOES produce spin connection, but mixed SU(2)×SO(3,1), not standard Einstein-Cartan
4. |N|=3 → SU(3) is more speculative than assumed
5. Chirality problem unsolved: Fermi-point gives vector coupling, SM needs chiral SU(2)_L

---

## Track A: Fermi-Point Topological Charge

### Wave 1 — Topological Charge Definition — **COMPLETE**
**Goal:** Formalize the winding number of a Fermi point.

- [x] `lean/SKEFTHawking/FermiPointTopology.lean` — 28 theorems, zero sorry
- [x] Define N = winding number of Green's function singularity on S² surrounding Fermi point
- [x] Connect to π₂(S²) = ℤ (topological charge classification)
- [x] |N| = 1 case: U(1) gauge emergence (Weyl fermions)
- [x] |N| = 2 case: SU(2) gauge structure (doubly-degenerate Fermi points)
- [x] Builds clean, zero sorry, zero axioms

### Wave 2 — |N|=2 → SU(2) Correspondence — **COMPLETE**
**Goal:** Formalize the gauge emergence theorem for doubly-degenerate Fermi points.

- [x] `ChargeSplitting` structure with charge conservation (concrete examples: N=2→1+1, N=3→1+1+1)
- [x] `MultiWeylData` classification: |N|=2 (C₄), |N|=3 (C₆), |N|≥4 forbidden
- [x] Multi-Weyl semimetals are Mechanism A (PROVED: anisotropic, NOT SU(N))
- [x] `RigorLevel` enum: theorem/heuristic/speculative with DecidableEq
- [x] SU(2) emergence chain: 6 steps (3 theorem + 2 heuristic + 1 speculative) — all verified by native_decide
- [x] Vierbein decomposition: 4×2 (Selch-Zubkov), rectangular 4×5 (³He planar)
- [x] SM vielbein size: 4+8+3+1 = 16 (PROVED)

### Wave 3 — Connection to Emergent Gravity — **COMPLETE**
**Goal:** Close the loop: |N|=2 Fermi points → SU(2) spin connection → ADW tetrad → Einstein-Cartan.

- [x] `EmergenceChainStatus`: full 6-step status (theorem/heuristic/speculative per step)
- [x] `emergence_theorem_frontier`: chain is theorem-level through step 2 only (PROVED)
- [x] `adw_requires_nonperturbative`: step 5 is not theorem (PROVED)
- [x] SU(3) chain: 4 steps (2 theorem + 2 speculative), MORE speculative than SU(2) (PROVED)
- [x] Bridge theorems: EmergentGravityBounds (coupling deficit), GaugingStep (bypass), SPTClassification (alternative route)
- [x] Chirality independence: vector coupling is SEPARATE obstruction from coupling deficit
- [x] FermiPointTopology.lean: 33 theorems (up from 28), zero sorry, 3.0s build

---

## Deep Research

| # | Topic | File | Status |
|---|-------|------|--------|
| 1 | |N|>1 Fermi-point → SU(2) emergence | Lit-Search/Phase-5j/Volovik \|N\|>1 Fermi-Point → SU(2) Gauge Emergence.md | **COMPLETE** |

---

*Phase 5j roadmap. Updated 2026-04-06 (**W1-3 ALL COMPLETE**: FermiPointTopology.lean, 33 thms, 0 sorry. W2: charge splitting, multi-Weyl classification, SU(2) emergence chain with rigor tracking. W3: full emergence chain status, SU(3) more speculative, bridge theorems to EmergentGravityBounds/GaugingStep/SPTClassification. Deep research fully incorporated). The Fermi-point scenario is the bridge from condensed matter topology to non-Abelian gauge emergence — the route the Critical Review identifies as most promising.*
