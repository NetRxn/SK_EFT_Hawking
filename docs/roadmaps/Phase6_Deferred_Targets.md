# Phase 6+ Deferred Targets

**Purpose:** Track high-value formalization targets beyond Phase 5b. Deep research timelines assume human effort; our pipeline + Aristotle has consistently compressed months→days.

**Created:** April 4, 2026
**Updated:** April 4, 2026 (post Phase 5b Waves 1-7, deep research on q-Onsager)

---

## Items PROMOTED from Phase 6 to Phase 5b (completed or in progress)

### Drinfeld Center Z(Vec_G) ≅ Rep(D(G)) — **COMPLETED** (Phase 5b Waves 2-3)
- 96+ theorems across 7 modules, zero sorry, zero axioms.
- Full algebraic core proved. Concrete Z/2 and S₃ equivalences verified.
- **Remaining for Phase 6:** Abstract categorical functor `Functor.mk` (~30-50 thms).

### Wang Three-Generation Constraint — **COMPLETED** (Phase 5b Waves 4-6)
- Algebraic consequence 24|8N_f → 3|N_f: PROVED (GenerationConstraint.lean)
- c₋ = 8N_f DERIVED from 16 Weyl fermions (WangBridge.lean)
- "24" DERIVED from Dedekind eta q-expansion (ModularInvarianceConstraint.lean)
- Rokhlin "16 convergence" and with/without ν_R analysis (RokhlinBridge.lean)
- **Remaining for Phase 6:** Full topological proof through Hirzebruch + Rokhlin + index theory.
  Requires: 4-manifold intersection forms, Arf invariant, Freedman classification.
  Mathlib gap: ~5-10% for these specific tools.

### q-Onsager: q-Numbers + U_q(sl₂) Definition — **IN PROGRESS** (Phase 5b Wave 7)
- q-numbers, q-DG relations, U_q(sl₂) via `FreeAlgebra` + `RingQuot` (zero axioms)
- First quantum group definition in any proof assistant
- **Research:** `Lit-Search/Phase-5b/Mathlib4 infrastructure audit...` (key finding:
  Mathlib has full Coalgebra → Bialgebra → HopfAlgebra hierarchy)

---

## Tier 1: High Value, Infrastructure Available (Phase 6 candidates)

### U_q(sl₂) Hopf Algebra Structure
- **Prerequisite:** Wave 7 (U_q(sl₂) as Ring via RingQuot)
- **Work:** Wire the coproduct Δ(E) = E⊗K + 1⊗E, Δ(F) = F⊗1 + K⁻¹⊗F, Δ(K) = K⊗K
  into Mathlib's `HopfAlgebra` typeclass. Counit ε and antipode S.
- **Mathlib:** `HopfAlgebra R A` EXISTS and is merged. Infrastructure is ready.
- **Estimate:** ~20-30 theorems, 1-2 sessions
- **Research:** `Lit-Search/Phase-5b/From quantum groups to gauge emergence...`

### O_q ↪ U_q(ŝl₂) Coideal Embedding
- **Key finding from research:** O_q embeds in the AFFINE quantum group U_q(ŝl₂)
  (6 generators: e₀, e₁, f₀, f₁, K₀, K₁), NOT the finite U_q(sl₂) (4 generators).
  The finite-type coideal of U_q(sl₂) under Chevalley involution is merely a
  polynomial ring — the interesting structure requires the affine extension.
- **Mathlib gap:** `FreeAlgebra` + `RingQuot` works for U_q(ŝl₂) too, but the
  Serre relations for affine type are more complex.
- **Estimate:** ~30-50 theorems, 2-3 sessions
- **Research:** `Lit-Search/Phase-5b/The q-Onsager algebra as a coideal subalgebra...`

### Rep(U_q(sl₂)) → MTC at Roots of Unity
- **Key finding:** U_q(sl₂) is already a Drinfeld double of its Borel subalgebra.
  At q = e^{2πi/(k+2)}, the semisimplified representation category gives SU(2)_k
  Chern-Simons theory — a modular tensor category (MTC).
- **Requires:** Root-of-unity specialization, tilting modules, semisimplification functor.
- **Estimate:** 12-24 months (per deep research feasibility assessment)
- **Research:** `Lit-Search/Phase-5b/From quantum groups to gauge emergence...`

### Abstract Equivalence Functor Center(Vec_G) ⥤ Rep(D(G))
- **Status:** Algebraic bijection proved (DrinfeldCenterBridge). Concrete examples verified.
  Missing: abstract `Functor.mk` with object/morphism maps between Mathlib categories.
- **Estimate:** ~30-50 theorems of deep Mathlib categorical plumbing

---

## Tier 2: High Value, Requires Mathematical Breakthroughs

### Non-Abelian TPF Disentangler
- **Source:** TPF arXiv:2601.04304 lists this as open problem
- **Status:** No construction exists as of April 2026
- **Requires:** Peter-Weyl theory for L²(SU(N)), non-Abelian Gauss law
- **Note:** Generalized q-Onsager algebras (Baseilhac) may provide ingredients —
  our q-Onsager formalization could inform this.

### |N| = 3 Fermi-Point → SU(3) Emergence
- **Source:** Volovik arXiv:1111.4627 (2012)
- **Status:** No explicit proof; speculative extrapolation from |N|=2 → SU(2)
- **Note:** Only mechanism with experimental confirmation (|N|=1 in ³He-A)

### Full Z₁₆ Cobordism Proof
- **Source:** Giambalvo 1973, Freed-Hopkins 2021
- **Requires:** Atiyah-Hirzebruch spectral sequence, Adams spectral sequence
- **Note:** 15-25 person-years by conventional methods

### Wang Full Topological Proof (Hirzebruch + Rokhlin)
- **Status:** Algebraic consequence proved (Phase 5b). Full topological proof deferred.
- **Requires:** 4-manifold intersection forms, Arf invariant, spin structures on manifolds
- **Mathlib gap:** ~5-10% for differential topology

---

## Tier 3: Medium Value, Long-Term

### Fermi-Point Topology (K-theory)
- **Requires:** K-theory in Mathlib (vector bundles exist, K-groups don't)

### CGT Ω-Spectra Framework
- **Requires:** Stable homotopy theory — years away in any proof assistant

### Walker-Wang Bulk-Boundary
- **Requires:** Higher category theory, 4+1D TQFT axioms

---

## Tier 0: Already Scoped for Phase 6

### Verified Statistics Pipeline
- Jackknife, bootstrap, Γ-method → verified CG → staggered Dirac/HMC

### Polariton Experimental Protocol Paper
- T_H ~ 1 K, 10^10× BEC. Most accessible experimental target.

### Fracton-Gravity Kerr-Schild Bootstrap
- Linearized gravity from fracton symmetric tensor gauge theory

---

*Updated April 4, 2026. Deep research supporting Phase 6 decisions in `Lit-Search/Phase-5b/` (6 files covering Mathlib infrastructure, q-DG relations, coideal embedding, MTC feasibility).*
