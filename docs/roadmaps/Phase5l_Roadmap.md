# Phase 5l: Topological Quantum Computation from Verified MTCs

## Technical Roadmap — April 2026

*Prepared 2026-04-07 | Follows Phase 5k (WRT TQFT)*

**Entry state:** Verified Ising + Fibonacci MTCs with complete braiding data. First (and only) verified MTC infrastructure in any proof assistant.

**Prerequisite:** Deep research `Phase-5l/Topological quantum computation from verified MTCs` — **COMPLETE** (2026-04-07).

**Deep research key findings:**
- B=F^{-1}RF formula: braiding matrices from our verified R/F data (Ising in Q(zeta_16), Fibonacci in Q(zeta_5))
- Ising braiding generates exactly the Clifford group (Microsoft Majorana hardware connection)
- Fibonacci braiding is universal for quantum computation (FLW density theorem)
- Levin-Wen string-net codes from fusion data; toric code = Vec_{Z/2} string-net (connects to our ToricCodeCenter)
- Solovay-Kitaev: any unitary epsilon-approximable by O(log^c(1/epsilon)) braids
- Industry: Microsoft Majorana 1 (Ising), Google Willow (surface code = Vec_{Z/2}), Quantinuum Helios (D4 non-abelian)
- Circle-back: TL algebra + JW idempotent infrastructure (built in 5k W0-W1) is exactly what 5l needs

---

## 0. Motivation

Topological quantum computation uses anyon braiding as quantum gates. The MTC structure determines the computational power:
- **Ising anyons** (σ): single-qubit Clifford gates (NOT universal alone, but basis for Microsoft's hardware)
- **Fibonacci anyons** (τ): UNIVERSAL for quantum computation (Freedman-Kitaev-Wang 2002)

We have the ONLY verified braiding data. This connects directly to a $50B+ industry.

---

## Track A: Anyonic Gate Sets

### Wave 1 — Braiding Matrices for n Anyons
**Goal:** Compute explicit braiding matrices for systems of n anyons.

- [ ] 2-anyon fusion space: σ⊗σ → {1, ψ} (2-dimensional, our R-matrix acts here)
- [ ] 3-anyon fusion space: σ⊗σ⊗σ → basis from fusion trees (4-dimensional)
- [ ] F-move + R-move composition → braiding gate on 3-anyon space
- [ ] Verify gates match known Clifford group generators for Ising

### Wave 2 — Fibonacci Universality
**Goal:** Prove Fibonacci anyon braiding is computationally universal.

- [ ] Compute Fibonacci braiding matrices for 3,4,5 anyons explicitly
- [ ] Show braiding generates a dense subgroup of SU(N) (N = Fibonacci numbers)
- [ ] Formalize the density argument (golden ratio irrationality → dense rotation)
- [ ] Solovay-Kitaev approximation: state that any unitary can be ε-approximated by poly(log(1/ε)) braids

### Wave 3 — Error Correction from Fusion Categories
**Goal:** Define topological error-correcting codes from our fusion data.

- [ ] Levin-Wen string-net code: code space from fusion category on a surface
- [ ] Code distance from minimum anyon separation
- [ ] Toric code as Vec_{Z/2} string-net (connection to our ToricCodeCenter.lean)

---

## Deep Research

| # | Topic | File | Status |
|---|-------|------|--------|
| 1 | TQC from verified MTCs | Lit-Search/Phase-5k-5l-5m-5n/Topological quantum... | **COMPLETE** |

---

*Phase 5l roadmap. Created 2026-04-07, updated 2026-04-07. Deep research complete. Circle-back after 5k infrastructure (TL+JW already built). Our verified Ising + Fibonacci MTCs connect directly to Microsoft/Google hardware.*
