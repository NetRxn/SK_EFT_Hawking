# Phase 5c: Quantum Groups and Modular Tensor Categories

## Technical Roadmap — April 2026

*Prepared 2026-04-04 | Follows Phase 5b (SM anomaly, Drinfeld center, modular invariance, q-numbers, U_q(sl₂))*

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
> 1. Read CLAUDE.md, WAVE_EXECUTION_PIPELINE.md, Inventory Index
> 2. Read this roadmap for wave assignments
> 3. Read deep research: `Lit-Search/Phase-5b/` (6 files on quantum groups + MTC)

---

## 0. Entry State

**What Phase 5b established:**
- 968 theorems, 0 axioms, 0 sorry, 66 Lean modules
- U_q(sl₂) defined via FreeAlgebra + RingQuot (first quantum group in any proof assistant)
- q-integers [n]_q as Laurent polynomials, classical limit [n]_1 = n
- Full Onsager algebra (24 thms), Drinfeld center (87 thms), generation constraint chain
- Mathlib has full Coalgebra → Bialgebra → HopfAlgebra hierarchy (surprise finding)

**What Phase 5c aims to do:**
Complete the quantum group infrastructure: Hopf algebra structure on U_q(sl₂),
affine quantum group U_q(ŝl₂), coideal embedding of O_q, and push toward
the first MTC (modular tensor category) in a proof assistant.

**Research basis:**
- `Lit-Search/Phase-5b/Mathlib4 infrastructure audit...` — FreeAlgebra, RingQuot, HopfAlgebra all ready
- `Lit-Search/Phase-5b/From quantum groups to gauge emergence...` — U_q(sl₂) is its own Drinfeld double
- `Lit-Search/Phase-5b/The q-Onsager algebra as a coideal subalgebra...` — O_q ↪ U_q(ŝl₂), not U_q(sl₂)
- `Lit-Search/Tasks/submitted/MTC-Level1-restricted-quantum-group.md` — PENDING
- `Lit-Search/Tasks/submitted/MTC-Level2-SU2k-fusion-rules.md` — PENDING
- `Lit-Search/Tasks/submitted/MTC-Level3-Verlinde-and-modularity.md` — PENDING

---

## 1. Wave 1 — U_q(sl₂) Hopf Algebra Structure [~20-30 theorems]

**Goal:** Wire the coproduct, counit, and antipode into Mathlib's `HopfAlgebra` typeclass.

**Why it's feasible now:** Mathlib has `HopfAlgebra R A` with fields `comul`, `counit`,
`antipode` and all compatibility axioms. We just need to define the maps and prove
the axioms for our `Uqsl2 := RingQuot (ChevalleyRel k)`.

### Deliverables:
- [ ] `lean/SKEFTHawking/Uqsl2Hopf.lean` — ~20-30 theorems:
  - Coalgebra structure: Δ(E) = E⊗K + 1⊗E, Δ(F) = F⊗1 + K⁻¹⊗F, Δ(K) = K⊗K
  - Counit: ε(E) = ε(F) = 0, ε(K) = 1
  - Antipode: S(E) = -EK⁻¹, S(F) = -KF, S(K) = K⁻¹
  - `HopfAlgebra (LaurentPolynomial k) (Uqsl2 k)` instance
  - S² = Ad(K): the squared antipode is conjugation by K
  - Coassociativity, counit axioms, antipode axioms

### Key Aristotle targets:
- Coproduct compatibility with Chevalley relations
- Antipode axiom: μ ∘ (S ⊗ id) ∘ Δ = η ∘ ε
- These are algebraic identities — standard Aristotle territory

---

## 2. Wave 2 — U_q(ŝl₂) Affine Quantum Group [~30-50 theorems]

**Goal:** Define the affine quantum group U_q(ŝl₂) with 6 generators and the
Kac-Moody Serre relations. Then state the coideal embedding O_q ↪ U_q(ŝl₂).

**Why it's feasible:** Same `FreeAlgebra` + `RingQuot` pattern. The Serre relations
for affine A₁⁽¹⁾ are well-documented.

### Deliverables:
- [ ] `lean/SKEFTHawking/Uqsl2Affine.lean` — ~20-30 theorems:
  - 6 generators: e₀, e₁, f₀, f₁, K₀, K₁
  - Affine Chevalley relations + Serre relations
  - RingQuot definition (zero axioms)
  
- [ ] `lean/SKEFTHawking/QOnsagerEmbed.lean` — ~10-20 theorems:
  - O_q generators W₀, W₁ as elements of U_q(ŝl₂)
  - Verify q-DG relations hold for the images
  - Coideal property: Δ(W_i) ∈ O_q ⊗ U_q(ŝl₂)

**Research:** `Lit-Search/Phase-5b/The q-Onsager algebra as a coideal subalgebra...`

---

## 3. Wave 3 — SU(2)_k Fusion Rules (First MTC Chunk) [~15-25 theorems]

**Goal:** Compute explicit fusion rules for SU(2)_k at small k, following the
same pattern as ToricCodeCenter (Z/2) and S3CenterAnyons (S₃).

**Why it's feasible:** This is a CONCRETE FINITE COMPUTATION, not abstract
category theory. For k=1 (Ising, 3 objects) or k=2 (3 objects), the fusion
table is small enough for exhaustive verification by `decide`.

### Deliverables:
- [ ] `lean/SKEFTHawking/SU2kFusion.lean` — ~15-25 theorems:
  - Simple objects V_0, ..., V_k as inductive type
  - Quantum dimensions d_j (explicit for small k)
  - Fusion rules: truncated Clebsch-Gordan (explicit for k=1,2,3)
  - Global dimension D² (explicit)
  - Comparison to our FusionCategory axioms

**Research:** `Lit-Search/Tasks/submitted/MTC-Level2-SU2k-fusion-rules.md` — PENDING

---

## 4. Wave 4 — S-matrix and Verlinde Formula [~15-25 theorems]

**Goal:** Define the S-matrix for SU(2)_k, prove unitarity, and verify the
Verlinde formula N_{ij}^m = Σ S_{il}S_{jl}S_{ml}*/S_{0l}.

**Why it's feasible:** For specific k, this is a finite matrix computation.
Mathlib has `Matrix`, `det`, trigonometric functions. The Verlinde formula
can be verified entry-by-entry for k=1,2,3 using `norm_num` or `decide`.

### Deliverables:
- [ ] `lean/SKEFTHawking/SU2kSMatrix.lean` — ~15-25 theorems:
  - S_{ij} = √(2/(k+2)) sin(π(i+1)(j+1)/(k+2)) as Matrix
  - Unitarity: S * S† = I (for specific k)
  - Verlinde formula: verified for k=1,2,3
  - This makes the fusion category MODULAR

**Research:** `Lit-Search/Tasks/submitted/MTC-Level3-Verlinde-and-modularity.md` — PENDING

---

## 5. Wave 5 (stretch) — Restricted Quantum Group ū_q [~10-15 theorems]

**Goal:** Define the restricted quantum group at roots of unity as a further
quotient of U_q(sl₂).

### Deliverables:
- [ ] `lean/SKEFTHawking/RestrictedUq.lean`:
  - Additional relations: E^{k+1} = 0, F^{k+1} = 0, K^{2(k+2)} = 1
  - Finite dimensionality: dim ū_q = (k+1)³
  - Connection to SU(2)_k fusion rules

**Research:** `Lit-Search/Tasks/submitted/MTC-Level1-restricted-quantum-group.md` — PENDING

---

## 6. Assessment: What's Phase 6 vs Phase 5c?

| Item | Phase 5c? | Reason |
|------|-----------|--------|
| U_q(sl₂) Hopf algebra | YES | Infrastructure ready, natural next step |
| U_q(ŝl₂) affine | YES | Same FreeAlgebra+RingQuot pattern |
| O_q ↪ U_q(ŝl₂) | YES | Concrete algebra homomorphism |
| SU(2)_k fusion (small k) | YES | Concrete computation, like toric code |
| S-matrix + Verlinde (small k) | YES (stretch) | Finite matrix, depends on research |
| Restricted ū_q | YES (stretch) | Further quotient of existing type |
| Full MTC categorical structure | PHASE 6 | Needs ribbon category infrastructure |
| Rep(U_q(sl₂)) → Chern-Simons | PHASE 6 | Statement-level, not constructive |
| Abstract functor Center(Vec_G) ⥤ Rep(D(G)) | PHASE 6 | Deep categorical plumbing |

**Key principle:** Concrete computations (fusion tables, S-matrices, explicit quotients)
are Phase 5c. Abstract categorical wrapping is Phase 6.

---

## 7. Publication Impact

Phase 5c would give:
- **First Hopf algebra in a proof assistant** (U_q(sl₂) with coproduct/antipode)
- **First affine quantum group** (U_q(ŝl₂))
- **First MTC fusion computation from a quantum group** (SU(2)_k)
- **First coideal embedding** connecting Onsager to quantum groups

Paper framing: Paper 11 (quantum group) extended, or Paper 12 (MTC).

---

*Phase 5c roadmap. Created 2026-04-04. Research basis: Lit-Search/Phase-5b/ (6 files) + 3 pending MTC research tasks. All waves follow WAVE_EXECUTION_PIPELINE.md.*
