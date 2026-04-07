# Phase 5n: Chirality Wall Assault — Anomaly Inflow + Gapped Interface

## Technical Roadmap — April 2026

*Prepared 2026-04-07 | The moonshot. Follows Phases 5h (chirality 3+1D) and 5a (chirality 1+1D).*

**Entry state:** Three-pillar chirality wall analysis complete (GS no-go, TPF evasion, GT positive construction). Gauging obstruction formalized (GaugingStep.lean). Z₁₆ classification proved. Gapped interface remains an AXIOM (hard eliminability). Three gaps: (1) 4+1D gapped interface, (2) gauging step, (3) full Z₁₆ cobordism.

**Prerequisite:** Deep research `Phase-5n/Anomaly inflow and gapped interface` — **COMPLETE** (2026-04-07).

**Deep research key findings:**
- Gapped interface conjecture decomposes into 3 layers: (a) topological/anomaly matching (formalizable now), (b) dynamical/spectral gap (physics, not math), (c) SRE ground state (partially formalizable)
- 1+1D 3450 model: anomaly cancellation 3^2+4^2=5^2+0^2=25 (PROVED in KMatrixAnomaly.lean)
- K-matrix formalism: anomaly-free iff Lagrangian sublattice exists (decidable via Smith normal form)
- Bordism framework: Omega^{Spin}_4 = Z, Omega^{Pin+}_4 = Z_16 (connects to our Z16Classification)
- Kapustin-Fidkowski no-go forces infinite-dim Hilbert spaces in 2+1D and higher
- Seifnashri et al. (2026) exact Villain Hamiltonian most tractable for formalization

**Layer A progress (2026-04-07):**
- [x] ChiralTheory1D structure with anomaly coefficients (KMatrixAnomaly.lean)
- [x] theory3450 anomaly-free PROVED (native_decide)
- [x] KMatrixData structure with det/trivialOrder
- [x] 3450 K-matrix det=0 PROVED
- [x] vectorlike_anomaly_free PROVED
- [x] Model3450 in SPTClassification.lean with anomaly cancellation PROVED

---

## 0. Motivation

The chirality wall is THE hardest open problem in lattice QFT. Our formal analysis is the only machine-checked contribution to this debate. Any progress — even formalizing the precise mathematical content of the conjecture, or proving it in low dimensions — would be a landmark.

**Decomposition strategy:** Don't try to solve the 3+1D problem directly. Build up through lower dimensions where everything is known, establishing the methodology and infrastructure, then attack the hard case.

---

## Track A: 1+1D Gapped Interface (Proof of Concept)

### Wave 1 — Formalize the 1+1D TPF Construction
**Goal:** Machine-check the "3450" model gapped interface that TPF solved explicitly.

- [ ] Define the 1+1D lattice model with infinite-dimensional rotor sites
- [ ] Formalize the symmetry disentangler (constant-depth circuit)
- [ ] Verify anomaly cancellation for the 3450 charge assignment
- [ ] State and prove the gapped interface exists (TPF provided the explicit Hamiltonian)

### Wave 2 — 1+1D Gauging Step
**Goal:** Formalize the gauging procedure that TPF applied in 1+1D.

- [ ] Convert not-on-site to on-site via the disentangler
- [ ] Apply standard lattice gauging to the on-site symmetry
- [ ] Verify the resulting theory is chiral (asymmetric left/right spectrum)

---

## Track B: Anomaly Inflow Infrastructure

### Wave 3 — Bordism-Anomaly Correspondence
**Goal:** Formalize the mathematical framework connecting bordism to anomalies.

- [ ] Spin bordism groups Ω^{spin}_d for d = 1,2,3,4,5 (connect to SpinBordism.lean)
- [ ] Anderson duality: Ω^{spin}_d ↔ anomaly classification
- [ ] The specific map: Ω^{spin}_5 → ℤ₁₆ (connects to our Z16Classification)
- [ ] Bulk-boundary correspondence: (d+1)-dim SPT → d-dim anomalous boundary

### Wave 4 — SPT Stacking and Interfaces
**Goal:** Formalize the mathematical content of "stacking" two SPTs and constructing an interface.

- [ ] SPT tensor product (stacking): P₁ ⊠ P₂
- [ ] Anomaly additivity: ν(P₁ ⊠ P₂) = ν(P₁) + ν(P₂) mod 16
- [ ] Interface = boundary of P₁ ⊠ P₂^{-1} (inverse SPT)
- [ ] When ν(P₁) = ν(P₂): the stack is trivial → gapped boundary EXISTS (in principle)

---

## Track C: Obstructions and Necessary Conditions

### Wave 5 — What Would Make the Gapped Interface Fail?
**Goal:** Formalize known OBSTRUCTIONS to gapped interfaces.

- [ ] H³(G, U(1)) obstruction (Lieb-Schultz-Mattis type)
- [ ] Entanglement spectrum constraints
- [ ] Connect to Kapustin-Fidkowski no-go (already in SPTClassification.lean)

---

## Dependencies

```
Track A (1+1D):    W1 → W2 (sequential, both tractable)
Track B (Inflow):  W3 → W4 (sequential, needs deep research)
Track C (Obstructions): W5 (independent)
```

Tracks A and C can proceed in parallel. Track B needs deep research results.

---

## Deep Research

| # | Topic | File | Status |
|---|-------|------|--------|
| 1 | Anomaly inflow + gapped interface | Lit-Search/Phase-5k-5l-5m-5n/Anomaly inflow... | **COMPLETE** |

---

*Phase 5n roadmap. Created 2026-04-07, updated 2026-04-07. Deep research complete. Layer A COMPLETE. **Track B W4 COMPLETE** (SPTStacking.lean: group axioms, anomaly additivity, 16-fold periodicity, SM fermion stacking, 1+1D 3450 connection). Next: Track A W1-W2 (1+1D TPF construction, needs deep research), Track B W3 (bordism-anomaly correspondence).*
