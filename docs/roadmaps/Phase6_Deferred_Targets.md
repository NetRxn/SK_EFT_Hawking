# Phase 6+ Deferred Targets

**Purpose:** Track high-value formalization targets that require infrastructure beyond current Mathlib, but should not be abandoned. Deep research timelines assume human effort; our pipeline + Aristotle has consistently compressed months→days.

**Created:** April 4, 2026
**Context:** Identified during Phase 5b scoping from deep research in `Lit-Search/Phase-5b/`.

---

## Tier 1: High Value, Currently Blocked on Infrastructure

### Wang Three-Generation Theorem (full proof, not axiomatized)
- **Source:** Wang, arXiv:2312.14928 (PRD 110, 125028, 2024)
- **Result:** N_f ≡ 0 mod 3 (generations must be multiples of 3)
- **Requires:** 4-manifold topology (Rokhlin σ ∈ 16Z, Hirzebruch signature), cobordism theory, spin structures, index theory
- **Mathlib gap:** ~5-10% infrastructure available
- **Deep research estimate:** 80-120 theorems, 3-5 years (human)
- **Our estimate:** Probably 1-3 months once infrastructure exists, or faster with axiomatization strategy
- **Note:** The algebraic CONSEQUENCE (8N_f ≡ 0 mod 24 → N_f ≡ 0 mod 3) is trivial and included in Phase 5b as a stretch goal. The full proof through Hirzebruch + Rokhlin is the deferred target.

### Drinfeld Center Z(Vec_G) ≅ Rep(D(G)) — **COMPLETED in Phase 5b** (Waves 2-3)
- **Status:** Core complete in Phase 5b. 96 theorems across 7 modules, zero sorry.
  Remaining: abstract equivalence functor (Ring/Algebra wrapping + functor construction).
- **Completed (Phase 5b):**
  - DrinfeldCenterBridge (18 thms), VecGMonoidal (12 thms), ToricCodeCenter (25 thms),
    S3CenterAnyons (22 thms), CenterEquivalenceZ2 (10 thms), DrinfeldDoubleAlgebra (9 thms)
  - MonoidalCategory + BraidedCategory for Vec_G and Center(Vec_G) all proved
  - D(G) algebra laws (unit, associativity, basis multiplication) all proved
  - Concrete Z(Vec_{ℤ/2}) ↔ D(ℤ/2) equivalence verified
- **Remaining for Phase 6:** Ring/Algebra typeclass wrapping on DDAlg, Rep(D(G)) as ModuleCat,
  abstract functor Center(Vec_G) ⥤ Rep(D(G)), braided monoidal equivalence proof (~40-65 theorems).

### q-Onsager → Quantum Group → MTC Chain
- **Source:** Baseilhac-Belliard arXiv:0906.1215; Terwilliger arXiv:math.QA/0307016
- **Result:** O → O_q (coideal of U_q(sl₂)) → D(U_q(sl₂)) → MTC
- **Requires:** Non-commutative Hopf algebras, coalgebra/bialgebra hierarchy, quantum groups, R-matrices
- **Mathlib gap:** ~10-15% infrastructure (commutative Hopf algebras exist, nothing else)
- **Deep research estimate:** 60-100 theorems for the chain, 12-18 months (human)
- **Our estimate:** Possibly 1-2 months once Hopf algebra infra is built
- **Note:** Connects our existing Onsager algebra (24 theorems) to continuous gauge groups. The q-Dolan-Grady relations reduce to our DG_COEFF=16 at q=1.

---

## Tier 2: High Value, Requires Mathematical Breakthroughs

### Non-Abelian TPF Disentangler
- **Source:** TPF arXiv:2601.04304 lists this as open problem
- **Status:** No construction exists as of April 2026
- **Requires:** Peter-Weyl theory for L²(SU(N)), non-Abelian Gauss law, non-commutative rotor models
- **Note:** The single most important missing piece for a complete constructive Layer 1→3 pipeline. Generalized q-Onsager algebras (Baseilhac) may provide the mathematical ingredients.

### |N| = 3 Fermi-Point → SU(3) Emergence
- **Source:** Volovik arXiv:1111.4627 (2012) — speculative extrapolation from |N|=2 → SU(2)
- **Status:** No explicit proof; requires identifying the microscopic order parameter
- **Note:** Only mechanism with experimental confirmation (|N|=1 in ³He-A). SU(3) extension is the holy grail for the Fermi-point program.

### Full Z₁₆ Cobordism Proof (discharge axiom)
- **Source:** Giambalvo 1973, Freed-Hopkins 2021
- **Status:** Axiomatized in our Z16Classification.lean
- **Requires:** Atiyah-Hirzebruch spectral sequence, Adams spectral sequence, stable homotopy
- **Note:** 15-25 person-years by conventional methods. A(1) Ext computation (our SteenrodA1.lean) is the most tractable partial discharge.

---

## Tier 3: Medium Value, Long-Term

### Fermi-Point Topology Formalization
- **Requires:** K-theory in Mathlib (vector bundles exist, K-groups don't)
- **Note:** Would formalize Volovik's topological invariant N₃ and the |N|→SU(N) correspondence

### CGT Ω-Spectra Framework
- **Source:** Czajka-Geiko-Thorngren arXiv:2512.02105
- **Requires:** Stable homotopy theory — years away in any proof assistant
- **Note:** Rigorous lattice anomaly classification. Diagnostic tool, not constructive.

### Walker-Wang Bulk-Boundary Correspondence
- **Requires:** Higher category theory, 4+1D TQFT axioms
- **Note:** Would formalize how 4+1D topological phases produce 3+1D gauge theories on boundaries

---

## Tier 0: Already Scoped for Phase 6

### Verified Statistics Pipeline
- **Source:** Phase6_VerifiedStatistics_Roadmap.md
- **Phase 1:** Jackknife, bootstrap, Γ-method (1-2 years human → possibly weeks for us)
- **Phase 2:** Verified CG/multi-shift CG
- **Phase 3:** Staggered Dirac, Wilson action, HMC
- **Dependency:** Mathlib probability infrastructure

### Polariton Experimental Protocol Paper
- **Source:** Phase 5 predictions, Paris group (Bramati-Jacquet)
- **Note:** T_H ~ 1 K, 10^10× BEC. Most accessible experimental target.

### Fracton-Gravity Kerr-Schild Bootstrap
- **Source:** Phase 4, partially executed
- **Note:** Linearized gravity from fracton symmetric tensor gauge theory. Gupta-Feynman bootstrap incomplete.

---

*Deferred targets captured April 4, 2026. Review when: (a) Mathlib adds K-theory/cobordism, (b) non-Abelian disentangler is constructed, (c) Phase 5b/6 infrastructure unlocks Tier 1 items.*
