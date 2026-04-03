# Phase 5a: Chirality Wall Formalization — Onsager Algebra + Anomaly Matching + Z₁₆

## Technical Roadmap — April 2026

*Prepared 2026-04-03 | Follows Phase 5 (analytical completion, categorical infrastructure, RHMC production)*

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
> 1. Read [`/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/CLAUDE.md`](../../../CLAUDE.md) — project conventions, build commands, mandatory references
> 2. Read [`/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/docs/WAVE_EXECUTION_PIPELINE.md`](../WAVE_EXECUTION_PIPELINE.md) — 12-stage execution process, pipeline invariants, no skipping
> 3. Read [`/Users/johnroehm/Programming/PythonEnvironments/Physics/Fluid-Based-Physics-Research/SK_EFT_Hawking/SK_EFT_Hawking_Inventory_Index.md`](../../SK_EFT_Hawking_Inventory_Index.md) — module map, Lean map, current counts
> 4. Read this roadmap for your specific wave assignment
> 5. Read the relevant deep research results in `Lit-Search/Phase-5a/` for your wave

---

## 0. Entry State

**What Phase 5 established (verified 2026-04-03):**
- 588 theorems + 2 axioms (zero sorry, 233 Aristotle-proved across 30+ runs)
- 1245 tests, 47 Python modules, 38 Lean modules, 64 figures, 7 papers, 20 notebooks
- Chirality wall: 55 theorems across 3 modules (LatticeHamiltonian, GoltermanShamir, TPFEvasion)
  - 7/9 GS conditions substantive, 2/9 well-typed physics axioms
  - 5 TPF violations proved, master synthesis `tpf_outside_gs_scope_main`
- Layer 1 categorical: 116 theorems across 7 modules (KLinearCategory through GaugeEmergence)
  - First-ever PivotalCategory, SphericalCategory, FusionCategory in any proof assistant
  - Gauge emergence Z(Vec_G) ≅ Rep(D(G)) proved, chirality limitation c ≡ 0 (mod 8)
- Vestigial: analytical susceptibility proved (G_ves < G_c whenever u_g > 0), RHMC production in flight

**What Phase 5a aims to do:**
1. Formalize the Onsager algebra — the universal structure connecting integrability, lattice chiral symmetry, and fusion categories
2. Formalize the Gioia-Thorngren construction — explicit lattice Hamiltonians with exact chiral symmetries evading Nielsen-Ninomiya
3. Build the Z₁₆ axiomatized framework — connect cobordism to super-modular categories and the chirality wall
4. Unify all three into a formalized Chirality Wall Master Theorem with three pillars

**What moves to Phase 6 (requires HPC, collaboration, or breakthrough):**
- Spectral gap proof for SMG (Yang-Mills mass gap difficulty)
- Full Z₁₆ cobordism formalization (15-25 person-years of algebraic topology)
- Verified MC statistical pipeline (5-10 person-years of formalized statistics)
- Fidkowski-Kitaev 1D Z₈ full construction

**Research basis:** All 6 deep research files in `Lit-Search/Phase-5a/` (complete).

**Execution priority (decided 2026-04-03):**
- **Waves 1 + 3A start immediately** — zero dependencies on anything in flight
- **L=8 RHMC running in parallel** (~3d est.) — results don't affect Phase 5a work
- **When L=8 lands:** one focused session for Wave 6D/7D (Paper 6 update), then resume Phase 5a
- **Wave 8 (4D ATRG) is CONDITIONAL** on L=8 results — if sign problem, Wave 8 preempts Phase 5a; if clean, Wave 8 deferred to Phase 6
- **Remaining Phase 5 cleanup** (backreaction.py Invariant 2 fix, orphan citations, PAPER_DEPENDENCIES stale entries) batched with paper submission prep, not blocking Phase 5a

**Parallel non-blocking tracks (John):**
- L=8 RHMC monitoring (running, checkpoint/resume)
- Deep research task execution (Lit-Search/Tasks/)
- Paper submission review + human parameter verification (provenance dashboard)

---

## 1. Wave 1 — Onsager Algebra Formalization [Lean + Aristotle]

**Research basis:** `Lit-Search/Phase-5a/The Onsager algebra- from lattice integrability to chiral fermions and fusion categories.md`

**Why this is first:** The Onsager algebra appears in 4 of 6 deep research documents. It connects lattice chiral symmetry (Gioia-Thorngren), integrability (Ising, XXZ), fusion categories (via q-deformation), and anomaly matching. Its formalization is the single highest-value near-term deliverable. No formalization exists in any proof assistant.

### 1A. Dolan-Grady Definition + Davies Isomorphism [Pipeline: Stages 1-5]

**Goal:** Define the Onsager algebra O via the Dolan-Grady presentation as a quotient of `FreeLieAlgebra C (Fin 2)` by the cubic Dolan-Grady ideal, then prove the Davies isomorphism to the infinite-generator {A_m, G_n} presentation.

**The construction:**
1. Define generators A₀, A₁ ∈ FreeLieAlgebra ℂ (Fin 2)
2. Define Dolan-Grady relations: [A₀, [A₀, [A₀, A₁]]] = 16[A₀, A₁] (and symmetric)
3. OnsagerAlgebra := FreeLieAlgebra ℂ (Fin 2) ⧸ DG_ideal
4. Define infinite generators: A_m := (1/2)[A_{m-1}, [A_{m-2}, A₁]] recursively, G_n similarly
5. Davies isomorphism: the {A_m, G_n} satisfy [A_m, A_n] = 4G_{m-n}, [G_m, A_n] = 2A_{n+m} - 2A_{n-m}, [G_m, G_n] = 0
6. Prove O embeds into the loop algebra L(sl₂) as the fixed-point subalgebra under Chevalley involution

**Mathlib infrastructure needed:** `FreeLieAlgebra` (exists), quotient construction (standard), sl₂ Lie algebra (exists as `LieAlgebra.sl2Triple`).

**Deliverables:**
- [ ] `lean/SKEFTHawking/OnsagerAlgebra.lean` — ~15-25 theorems:
  - `DolanGradyIdeal` definition, `OnsagerAlgebra` quotient
  - Davies isomorphism (bijection between presentations)
  - Chevalley involution embedding into L(sl₂)
  - Infinite-dimensionality, center structure
- [ ] Formulas in `formulas.py`: onsager_dg_relation, onsager_commutator, onsager_dimension
- [ ] Constants in `constants.py`: ONSAGER_ALGEBRA parameters
- [ ] Tests in `tests/test_onsager.py`
- [ ] Aristotle: submit sorry stubs
- [ ] Document sync

**Estimated LOE:** Medium (2-4 weeks). Dolan-Grady definition is straightforward. Davies isomorphism is the main proof effort.
**Risk:** Low. All building blocks exist in Mathlib. Publishable as first formalization of Onsager algebra in any proof assistant.

---

### 1B. Contraction to su(2) and Anomaly Encoding [Pipeline: Stages 1-5]

**Goal:** Prove the Onsager algebra contracts to su(2) in the continuum limit — this is the mechanism by which Gioia-Thorngren's lattice chiral symmetry recovers the standard Witten anomaly in the IR.

**The construction:**
1. Define contraction parameter ε → 0: rescale generators A_m → ε·A_m, G_n → ε²·G_n
2. In the ε → 0 limit: [A₀, A₁] → [σ₊, σ₋] ∝ σ_z (standard su(2) relations)
3. The two U(1) charges in the Onsager presentation generate su(2) in the IR
4. This contraction is the formal mechanism encoding the Witten anomaly on the lattice

**Deliverables:**
- [ ] `lean/SKEFTHawking/OnsagerContraction.lean` — ~10-15 theorems:
  - Contraction limit definition
  - Recovery of su(2) commutation relations
  - Charge algebra structure
- [ ] Tests, formulas, document sync

**Estimated LOE:** Medium. Algebraic computation in a well-understood framework.
**Risk:** Low-Medium. The contraction is a standard Inönü-Wigner construction.

---

## 2. Wave 2 — Gioia-Thorngren Lattice Chiral Symmetry [Lean + Aristotle]

**Research basis:** `Lit-Search/Phase-5a/Formalizing Gioia-Thorngren anomaly matching in Lean 4.md`

**Prerequisites:** Wave 1 (Onsager algebra).

### 2A. CAR Algebra and BdG Hamiltonian Framework [Pipeline: Stages 1-5]

**Goal:** Build the lattice operator framework needed for the GT construction. This extends the existing LatticeHamiltonian infrastructure (Wave 3A of Phase 5) with fermionic creation/annihilation operators.

**The construction:**
1. CAR algebra: {c_x, c_y†} = δ_{xy}, {c_x, c_y} = 0 — via Mathlib's `ExteriorAlgebra` (already used for C2)
2. BdG Hamiltonian: H = Σ_{x,y} (h_{xy} c_x† c_y + Δ_{xy} c_x† c_y† + h.c.)
3. Locality classification: finite-range, not-on-site, non-compact
4. Chiral symmetry: Q_A commutes with H but is not on-site

**Deliverables:**
- [ ] `lean/SKEFTHawking/CARAlgebra.lean` — ~15-20 theorems:
  - Creation/annihilation operators on ExteriorAlgebra
  - Anti-commutation relations
  - Number operator, particle-hole symmetry
- [ ] `lean/SKEFTHawking/BdGHamiltonian.lean` — ~15-20 theorems:
  - BdG structure, locality classification
  - Spectrum, particle-hole symmetry of BdG spectrum
- [ ] Tests, formulas, document sync

**Estimated LOE:** High (4-8 weeks). Functional analysis gaps (operator norms, spectral theory) may require axiomatization.
**Risk:** Medium. The gap between ExteriorAlgebra as a vector space and ExteriorAlgebra as an operator algebra is nontrivial.

---

### 2B. GT Model Formalization [Pipeline: Stages 1-5]

**Goal:** Formalize the two GT models: (1) single Weyl fermion with non-compact U(1) chiral symmetry, (2) Weyl doublet with Onsager algebra chiral symmetry contracting to SU(2) in IR.

**Prerequisites:** 2A (CAR algebra, BdG framework), Wave 1 (Onsager algebra).

**The construction:**
1. Define GT Model 1: H = Σ_k h(k) with specific dispersion on BrillouinZone 3 (3+1D)
2. Define chiral charge Q_A as non-compact, not-on-site lattice operator
3. Prove [H, Q_A] = 0 exactly (at the Hamiltonian level, not just in IR)
4. Prove Q_A is NOT on-site (violates GS condition I2/I3)
5. Define GT Model 2: H_doublet with Onsager algebra charges (A₀, A₁)
6. Prove [H_doublet, A₀] = [H_doublet, A₁] = 0

**Key theorem:** GT models evade Nielsen-Ninomiya by using non-compact, not-on-site symmetries — exactly the conditions our Phase 5 formalization proved the GS no-go requires.

**Deliverables:**
- [ ] `lean/SKEFTHawking/GioiaThorngrenModel.lean` — ~20-30 theorems:
  - Model 1 Hamiltonian + chiral symmetry proof
  - Model 2 Hamiltonian + Onsager symmetry proof
  - Nielsen-Ninomiya evasion: explicit violation identification
  - Connection to existing TPFEvasion.lean results
- [ ] `src/chirality/gioia_thorngren.py` — GT model computations
- [ ] Tests, formulas, document sync

**Estimated LOE:** High (6-12 weeks). The explicit Hamiltonian proofs are technically demanding.
**Risk:** Medium-High. Proving [H, Q_A] = 0 rigorously in Lean requires spectral theory infrastructure that may need axiomatization.

---

## 3. Wave 3 — Z₁₆ Axiomatized Framework [Lean + Axioms]

**Research basis:**
- `Lit-Search/Phase-5a/Formalizing Ω₄^{Pin⁺} = ℤ₁₆ in Lean 4- a feasibility assessment.md`
- `Lit-Search/Phase-5a/Formalizing the chirality wall- a Lean 4 feasibility assessment.md`

### 3A. Z₁₆ Axiom + Conditional Chirality Theorems [Pipeline: Stages 1-5]

**Goal:** Axiomatize the Z₁₆ classification of 4D Pin⁺ bordism and derive conditional theorems connecting it to the chirality wall. The full proof is 15-25 person-years away, but the axiomatized route is immediately tractable.

**The construction:**
1. `axiom z16_classification : Ω₄^{Pin⁺} ≅ ℤ₁₆` — axiomatized (cobordism = open problem)
2. Define super-modular categories (extending existing FusionCategory)
3. State the 16-fold way conjecture (Bruillard-Galindo-Rowell-Wang): modular categories classified mod 16 by central charge
4. Derive: `z16_classification → chirality_limitation_strengthened` — connecting Pin⁺ bordism to our c ≡ 0 (mod 8) result
5. Derive: `z16_classification → smg_phase_classification` — connecting Z₁₆ to SMG phase structure

**Key connection:** Our existing `chirality_limitation_vecG` (GaugeEmergence.lean) proves c ≡ 0 (mod 8) for string-net models. Z₁₆ refines this to c ≡ 0 (mod 16) — a strictly stronger constraint.

**Deliverables:**
- [ ] `lean/SKEFTHawking/Z16Classification.lean` — ~15-20 theorems + 1 axiom:
  - Z₁₆ axiom
  - Super-modular category definition (extends FusionCategory)
  - 16-fold way conditional theorem
  - Chirality wall strengthening: c ≡ 0 (mod 16) from Z₁₆
  - SMG phase classification conditional theorem
- [ ] Formulas, constants, tests, document sync

**Estimated LOE:** Medium (3-6 weeks). Builds directly on existing categorical infrastructure.
**Risk:** Low. Axiomatization is clean. The categorical definitions extend naturally from Wave 4 of Phase 5.

---

### 3B. A(1) Ext Computation — Partial Axiom Discharge [Pipeline: Stages 1-5]

**Goal:** Machine-check the finite computation at the heart of Z₁₆: the Ext group computation over A(1) (the first Steenrod algebra subalgebra) in degree 4. This is an 8-dimensional F₂-algebra computation — the most tractable piece of the cobordism proof to partially discharge.

**The construction:**
1. Define A(1) = ⟨Sq¹, Sq²⟩ as an 8-dimensional F₂-algebra (explicit multiplication table)
2. Compute Ext_{A(1)}(F₂, F₂) in degrees 0-4 via a resolution
3. Read off: Ext⁴ ≅ ℤ₁₆ (this IS the cobordism computation for the Pin⁺ case)
4. This discharges one layer of the Z₁₆ axiom: the abstract topology becomes concrete algebra

**Deliverables:**
- [ ] `lean/SKEFTHawking/SteenrodA1.lean` — ~15-25 theorems:
  - A(1) as F₂-algebra with explicit multiplication table
  - Free resolution construction
  - Ext computation in low degrees
  - Ext⁴ ≅ ℤ₁₆ as a `native_decide`-amenable computation
- [ ] Tests, document sync

**Estimated LOE:** Medium-High (4-8 weeks). The algebra is finite and bounded, but the resolution construction is technically involved.
**Risk:** Medium. `native_decide` should handle the finite algebra, but constructing the resolution in Lean requires careful engineering. This would be the **first formalized stable homotopy computation**.

---

## 4. Wave 4 — Chirality Wall Master Theorem [Lean Synthesis]

**Research basis:** `Lit-Search/Phase-5a/Formalizing the chirality wall- a Lean 4 feasibility assessment.md`

**Prerequisites:** Waves 1-3 complete.

### 4A. Three-Pillar Synthesis [Pipeline: Stages 1-12]

**Goal:** Unify Waves 1-3 into the Chirality Wall Master Theorem — a single Lean structure encoding the three complementary attacks on the chirality wall.

**The construction:**
```
structure ChiralityWallMasterTheorem where
  -- Pillar 1: Golterman-Shamir no-go (Phase 5, extended in Phase 5a)
  gs_nogo : GSConditionsBundle → VectorLikeSpectrum
  tpf_evasion : TPFConstruction → ¬GSConditionsBundle
  -- Pillar 2: Gioia-Thorngren anomaly matching (Wave 2)
  gt_chiral_symmetry : GTModel → ∃ Q, [H, Q] = 0 ∧ ¬OnSite Q
  onsager_contraction : OnsagerAlgebra → su₂  -- IR limit
  -- Pillar 3: Z₁₆ cobordism (Wave 3, axiomatized)
  z16_axiom : Ω₄_PinPlus ≅ Z₁₆  -- axiom
  sixteen_fold_way : z16_axiom → ChiralityCentralCharge_mod_16
  -- Bridge theorems
  gs_tpf_gt_connection : TPFEvasion ↔ GTChiralSymmetry  -- same mechanism
  categorical_z16_bridge : ChiralityLimitation_mod_8 → strengthens_to_mod_16 z16_axiom
```

**Deliverables:**
- [ ] `lean/SKEFTHawking/ChiralityWallMaster.lean` — ~15-25 theorems:
  - Master structure definition
  - Bridge theorems connecting three pillars
  - Current status assessment: what is proved, what is axiomatized, what is conditional
- [ ] Paper 8 draft: `papers/paper8_chirality_master/paper_draft.tex` — comprehensive chirality wall paper
  - First formal verification survey of the chirality wall
  - Three-pillar structure with machine-checked proofs
  - Publication target: Reviews of Modern Physics or Computer Physics Communications
- [ ] Notebooks: `Phase5a_ChiralityMaster_Technical.ipynb` + `_Stakeholder.ipynb`
- [ ] Full document sync (Stages 8-12)

**Estimated LOE:** Medium (2-4 weeks for synthesis, once Waves 1-3 complete).
**Risk:** Low. This is a packaging wave — the hard work is in Waves 1-3.

---

## 5. Wave 5 — Spectral Gap Landscape + Verified Statistics Scoping

**Research basis:**
- `Lit-Search/Phase-5a/Spectral gaps for symmetric mass generation- a rigorous landscape assessment.md`
- `Lit-Search/Phase-5a/Formal verification meets lattice Monte Carlo- a feasibility assessment for SMG.md`

These are research-only waves. No implementation — they produce deep research tasks and Phase 6 roadmap items.

### 5A. SMG Spectral Gap Assessment

**Goal:** Encode the algebraic classification data (SMGSymmetryData, anomaly conditions, Altland-Zirnbauer tenfold way) and state the gapped interface conjecture formally. This is the correct axiomatize-then-discharge approach.

**Deliverables:**
- [ ] `lean/SKEFTHawking/SMGClassification.lean` — ~10-15 theorems:
  - `SMGSymmetryData` structure with anomaly conditions
  - `HasSpectralGap` type class (axiomatized)
  - Gapped interface conjecture formal statement
  - Conditional theorems: gap ∧ anomaly → SMG
- [ ] Tests, document sync

**Estimated LOE:** Low-Medium (1-2 weeks). Algebraic definitions only.
**Risk:** Low. This is definitional work — no proofs required for the analytic content.

### 5B. Verified Statistics Roadmap

**Goal:** Scope the formalized statistics pipeline for lattice MC verification. This is a Phase 6+ item but the roadmap should be written now.

**Deliverables:**
- [ ] `docs/roadmaps/Phase6_VerifiedStatistics_Roadmap.md` — detailed plan for formalized jackknife, bootstrap, Gamma-method in Lean 4
- [ ] Deep research task filed for Mathlib probability infrastructure assessment

**Estimated LOE:** Low (1 session for roadmap).

---

## 6. Conditional Items

| Item | Trigger | Status |
|------|---------|--------|
| 4D ATRG for vestigial (Phase 5 Wave 8) | L=8 RHMC shows sign problem (⟨sign⟩ → 0) | `conditional` — preempts Phase 5a if triggered; otherwise deferred to Phase 6 |
| Phase 5 Wave 6D/7D (Paper 6 + doc sync) | L=8 RHMC data available | `blocked` — one focused session when L=8 lands |
| Phase 5 remaining cleanup (backreaction.py, orphan citations) | Paper submission prep | `deferred` — batch with submission, not blocking Phase 5a |
| Full Z₁₆ cobordism proof | Algebraic topology infrastructure in Mathlib matures | `blocked` — 15-25 person-years |
| Spectral gap proof for SMG | Mathematical breakthrough | `blocked` — Millennium Prize difficulty |
| Fidkowski-Kitaev Z₈ 1D | Clifford algebra infrastructure sufficient | `conditional` — 6-12 months |

---

## 7. Deep Research Log

All results in `Lit-Search/Phase-5a/`.

| Task | File | Key Finding |
|------|------|-------------|
| SMG + lattice MC verification | `Formal verification meets lattice Monte Carlo...` | Phase 1: formalized statistics (jackknife, Gamma-method). No precedent exists. |
| Z₁₆ cobordism | `Formalizing Ω₄^{Pin⁺} = ℤ₁₆...` | Full: 15-25 py. "Poor man's": 2-6 pm via super-modular categories. A(1) Ext is bounded. |
| GT anomaly matching | `Formalizing Gioia-Thorngren anomaly matching...` | Onsager algebra via FreeLieAlgebra. ~75-115 theorems total. Phase 1 (Onsager) is independent. |
| Chirality wall unification | `Formalizing the chirality wall...` | Three-pillar structure. Algebraic layer tractable. A(1) Ext is most novel bounded target. |
| SMG spectral gaps | `Spectral gaps for symmetric mass generation...` | Yang-Mills difficulty. Axiomatize gap, prove everything conditional. Gap comparison method promising. |
| Onsager algebra survey | `The Onsager algebra- from lattice integrability...` | Universal anomaly encoding structure. 7+ physics domains. q-Onsager → fusion categories. |

---

## 8. Estimated Timeline

| Wave | Scope | LOE | Dependencies |
|------|-------|-----|-------------|
| Wave 1 | Onsager algebra | 2-6 weeks | None |
| Wave 2 | GT models | 4-12 weeks | Wave 1 |
| Wave 3A | Z₁₆ axiom + conditionals | 3-6 weeks | None (parallel with Wave 2) |
| Wave 3B | A(1) Ext computation | 4-8 weeks | Wave 3A |
| Wave 4 | Master theorem synthesis | 2-4 weeks | Waves 1-3 |
| Wave 5 | Spectral gap + statistics | 1-3 weeks | None (parallel) |

**Total estimated:** 16-39 weeks. Wave 1 + Wave 3A can start immediately in parallel.

**Estimated theorem count:** 100-180 new theorems across 6-10 new Lean modules.

---

*Phase 5a roadmap. Created 2026-04-03. Execution priority confirmed: Waves 1 + 3A start immediately (no dependencies). L=8 RHMC in parallel. Wave 8 conditional on L=8 results. All waves follow [Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md). Deep research complete.*
