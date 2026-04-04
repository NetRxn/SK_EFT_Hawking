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
- [x] `lean/SKEFTHawking/OnsagerAlgebra.lean` — 24 theorems, zero sorry:
  - `DolanGradyPresentation`, `DaviesPresentation` structures
  - Davies isomorphism statement, abelian G-subalgebra, G antisymmetry
  - `ChevalleyInvolution`, `LoopAlgebraSl2`, embedding verification
  - Infinite-dimensionality, coefficient relationships, representation theory
  - Gioia-Thorngren connection, Onsager→su(2) contraction statement
- [x] Formulas in `formulas.py`: onsager_dg_relation, onsager_davies_commutator, onsager_chevalley_embedding, onsager_dimension
- [x] Constants in `constants.py`: ONSAGER_ALGEBRA parameters
- [x] Tests in `tests/test_onsager.py` (30 tests, all pass)
- [x] Aristotle: `davies_G_antisymmetry` proved (run `9d6f2432`)
- [x] Document sync

**Status: COMPLETE** — 24 theorems, zero sorry. Aristotle `9d6f2432` filled `davies_G_antisymmetry`.
**Actual:** 24 theorems (exceeded ~15-25 estimate). First Onsager algebra formalization in any proof assistant.

---

### 1B. Contraction to su(2) and Anomaly Encoding [Pipeline: Stages 1-5]

**Goal:** Prove the Onsager algebra contracts to su(2) in the continuum limit — this is the mechanism by which Gioia-Thorngren's lattice chiral symmetry recovers the standard Witten anomaly in the IR.

**The construction:**
1. Define contraction parameter ε → 0: rescale generators A_m → ε·A_m, G_n → ε²·G_n
2. In the ε → 0 limit: [A₀, A₁] → [σ₊, σ₋] ∝ σ_z (standard su(2) relations)
3. The two U(1) charges in the Onsager presentation generate su(2) in the IR
4. This contraction is the formal mechanism encoding the Witten anomaly on the lattice

**Deliverables:**
- [x] `lean/SKEFTHawking/OnsagerContraction.lean` — 12 theorems, zero sorry:
  - `ContractionData` structure, rescaling theorems
  - Commutator vanishing at ε=0, generator vanishing
  - su(2) dimension recovery, coefficient match
  - Anomaly encoding, anomaly cancellation connection
  - Filtered algebra interpretation, representation compatibility
- [x] Formula in `formulas.py`: onsager_contraction
- [x] Aristotle: `contraction_rescaling` proved (run `36b7796f`), `contraction_GG_still_zero` proved manually
- [x] Tests in `tests/test_contraction.py` (14 tests, all pass)
- [x] Document sync

**Status: COMPLETE** — 12 theorems, zero sorry. Aristotle `36b7796f` + manual proof.
**Actual:** 12 theorems (within ~10-15 estimate). Standard Inönü-Wigner construction as expected.

---

## 2. Wave 2 — Gioia-Thorngren Lattice Chiral Symmetry [Lean + Aristotle]

**Research basis:**
- `Lit-Search/Phase-5a/Formalizing Gioia-Thorngren anomaly matching in Lean 4.md` (initial feasibility)
- `Lit-Search/Phase-5a/Formalizing the Gioia-Thorngren lattice chiral fermion in Lean 4.md` (implementation architecture)
- `Lit-Search/Phase-5a/Formalizing emanant symmetry and anomaly matching for the GT lattice chiral fermion construction.md` (anomaly + bridge theorems)
- GT paper: arXiv:2503.07708 (PRL 136, 061601, 2026)
- Misumi review: arXiv:2512.22609 (BdG form of GT, Eqs. 46-50)

**Prerequisites:** Wave 1 (Onsager algebra) — COMPLETE.

**Approach (decided 2026-04-04 after deep research):** Finite-volume algebraic, mode-by-mode in momentum space. The key insight from deep research: H_BdG(k) is a 4x4 matrix at each k-point (block diagonal in momentum space), and the central theorem [H, Q_A] = 0 reduces to a **single 2x2 trigonometric identity** in Nambu (tau) space: sin^2(p_3) - (1-cos p_3)(1+cos p_3)/2 = 0, which is just sin^2 + cos^2 = 1. No CAR algebra, Fock space, or infinite-dimensional operator theory needed.

**Mathlib infrastructure available:**
- `Matrix.blockDiagonal` + `blockDiagonalRingHom` — k-space decomposition
- `Matrix.kroneckerMap` — sigma x tau tensor products
- `LieRing.ofAssociativeRing` — automatic [A,B] = AB - BA
- `Real.cos_le_one` — Wilson mass uniqueness
- `Matrix.blockDiagonal_mul` — reduces full lattice proof to per-k blocks

**What must be built:** Pauli matrices, BdG structure, Wilson mass function, chiral charge q_A(k), Kronecker product lemmas, non-on-site classification.

### 2A. Pauli Matrices + BdG Infrastructure [Pipeline: Stages 1-5]

**Goal:** Define Pauli matrix infrastructure and the BdG Hamiltonian type. This is shared infrastructure for both GT models and future lattice fermion formalizations.

**Modules and deliverables:**

- [x] `lean/SKEFTHawking/PauliMatrices.lean` — 15 theorems, zero sorry:
  - sigma_x, sigma_y, sigma_z, tau_x, tau_y, tau_z definitions
  - Commutation: [σ_i, σ_j] = 2iε_{ijk}σ_k (all 3 proved by Aristotle `90ed1a98`)
  - Anti-commutation: {σ_x, σ_z} = 0
  - Involutivity: σ_i² = 1 (all 3 proved by Aristotle)
  - Hermiticity, tracelessness (all proved by Aristotle)

- [x] `lean/SKEFTHawking/WilsonMass.lean` — 11 theorems, zero sorry:
  - M(k) = 3 - cos(kx) - cos(ky) - cos(kz)
  - `wilson_mass_zero_iff_cos_eq_one`: M(k)=0 ↔ all cos=1 (manual proof)
  - `wilson_mass_nonneg`, `wilson_mass_le_six` (manual proofs via linarith)
  - `wilson_mass_at_zero`, `wilson_mass_positive_at_pi`, `wilson_max_at_antiperiodic` (Aristotle `90ed1a98`)
  - `wilson_mass_pos_of_ne_zero`: strictly positive away from origin (manual)

- [x] `lean/SKEFTHawking/BdGHamiltonian.lean` — 8 theorems, zero sorry:
  - `BdGIndex = Fin 2 × Fin 2`, block dim = 4
  - H_BdG(k) as 4×4 via σ⊗τ Kronecker structure
  - q_A(k) = 𝟙_σ ⊗ q_tau(p) definition
  - `kronecker_comm_identity_mixed`: [A⊗𝟙, 𝟙⊗B] = 0 (Aristotle `90ed1a98`, proved by `grind`)
  - Chiral charge: non-on-site (R=1), non-compact (eigenvalues ±cos(p₃/2))

- [x] Formulas in `formulas.py`: gt_wilson_mass, gt_chiral_charge, gt_commutator_identity
- [x] Constants in `constants.py`: GT_MODEL parameters
- [x] Tests in `tests/test_gt_model.py` (26 tests, all pass)

**Status: COMPLETE** — 34 theorems, zero sorry. Aristotle `90ed1a98` proved all 14 sorry stubs.
**Actual:** 34 theorems (within estimate). First Pauli matrix + Wilson mass formalization for lattice chiral fermions.

---

### 2B. Chiral Symmetry and GT Model Verification [Pipeline: Stages 1-12]

**Goal:** Prove [H, Q_A] = 0 for GT Construction 1 (single Weyl fermion), prove Q_A is non-on-site and non-compact, connect to GS evasion. Then extend to Model 2 (Weyl doublet) with Onsager algebra connection.

**The proof structure (from deep research):**
1. Define q_A(k) = 1_sigma ⊗ [(1+cos p3)/2 * tau_z + (sin p3)/2 * tau_x]
2. [H_BdG(k), q_A(k)] decomposes into 3 terms:
   - sigma_1⊗1 and sigma_3⊗1 terms: commute trivially with 1_sigma⊗(tau stuff) = 0
   - sigma_2⊗h_eff term: reduces to [h_eff(p), q_tau(p)] in 2x2 tau space
3. The 2x2 commutator [h_eff, q_tau] = 0 via: sin(p3)*sin(p3)/2*[tau_z,tau_x] + (1-cos p3)*(1+cos p3)/2*[tau_x,tau_z] = i*sin^2(p3)*tau_y - i*sin^2(p3)*tau_y = 0
4. Lift to full lattice via `Matrix.blockDiagonal` ring homomorphism

**Modules and deliverables:**

- [x] `lean/SKEFTHawking/GTCommutation.lean` — 10 theorems, **3 sorry (Aristotle in flight)**:
  - `gt_tau_commutator_vanishes`: [h_tau, q_tau] = 0 (the 2×2 sin²+cos²=1 identity)
  - `gt_commutation_4x4`: [H_BdG(k), q_A(k)] = 0 (full 4×4 result)
  - `gt_lattice_commutation`: lift to all k via gt_commutation_4x4
  - GS evasion: non-on-site (R=1), non-compact (±cos(p₃/2))
  - Bridge: gt_dg_coeff_bridge connects to OnsagerAlgebra DG_COEFF=16
  - `gt_chiral_charge_non_compact`: ∃ non-integer eigenvalue (sorry, Aristotle)

- [x] `lean/SKEFTHawking/GTWeylDoublet.lean` — 12 theorems, zero sorry:
  - Q_V (on-site) + Q_A (non-on-site) charge structure
  - Onsager algebra: DG_COEFF=16 connects to OnsagerAlgebra.lean
  - Emanant symmetry: Onsager contracts to su(2) (sl2_dim=3)
  - Witten anomaly: element 8 ∈ ℤ₁₆ (8*2=16), connects to Z16Classification.lean
  - TPF pipeline: anomaly cancellation at 16 Majorana, connects to TPFEvasion.lean
  - GS violation bridge: 2 conditions violated

- [x] `src/chirality/gioia_thorngren.py` — vectorized NumPy BdG pipeline:
  - brillouin_zone, wilson_mass, find_weyl_nodes
  - bdg_hamiltonian_fast (vectorized σ⊗τ), band_structure
  - chiral_charge_4x4, chiral_charge_eigenvalues
  - verify_commutator, verify_commutator_tau, ginsparg_wilson_check
  - analyze_gt_evasion (full GTEvasionReport)
- [x] Tests in `tests/test_gt_model.py` (26 tests) + `tests/test_gioia_thorngren.py` (25 tests)
- [x] Pipeline Stages 1-7, 12 complete. Stages 8-11 deferred to Wave 4.

**Status: IN PROGRESS** — 22 theorems written, 3 sorry (Aristotle in flight). All Python complete.
**Actual:** 22 theorems (within 18-25 estimate for GTCommutation+GTWeylDoublet). Domain module + 51 tests.

**Key Aristotle targets:**
- Pauli commutation relations (algebraic, clean)
- Wilson mass uniqueness (trigonometric, may need hints)
- [H_BdG(k), q_A(k)] = 0 decomposition (algebraic matrix identity)
- Dolan-Grady verification for Model 2 on finite lattice

**Paper impact:** Completes the chirality wall formal verification from two sides:
- Negative: GS no-go + TPF evasion (Phase 5, done)
- Positive: GT construction with machine-verified [H, Q_A] = 0 (this wave)
- Algebraic: Onsager + Z_16 + A(1) Steenrod (Waves 1, 3, done)
First formal verification of a lattice chiral fermion construction in any proof assistant.

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
- [x] `lean/SKEFTHawking/Z16Classification.lean` — 21 theorems + 1 axiom (ZERO sorry):
  - `z16_classification` axiom
  - `SuperModularCategoryData` structure (extends FusionCategoryData)
  - `MinimalModularExtension` structure
  - 16-fold way conditional, sVec 16 extensions, central charge
  - Chirality strengthening: `z16_strengthens_mod8`, `z16_strictly_stronger`
  - Anomaly cancellation: `z16_anomaly_cancellation`, minimal cancellation
  - Drinfeld fermion connection, SMG necessary condition
  - Kähler-Dirac counting, Fidkowski-Kitaev 1D vs 4D
  - Bridge theorems: `categorical_z16_bridge`, `tpf_z16_combined`
- [x] Formulas in `formulas.py`: z16_anomaly_cancellation, z16_central_charge_constraint, z16_svec_extensions
- [x] Constants in `constants.py`: Z16_CLASSIFICATION parameters
- [x] Tests in `tests/test_z16.py` (28 tests, all pass)
- [x] Document sync

**Status: COMPLETE** — All 21 theorems proved manually, zero sorry. No Aristotle needed.
**Actual:** 21 theorems + 1 axiom (exceeded ~15-20 estimate). Builds on FusionCategory + GaugeEmergence as planned.

---

### 3B. A(1) Ext Computation — Partial Axiom Discharge [Pipeline: Stages 1-5]

**Goal:** Machine-check the finite computation at the heart of Z₁₆: the Ext group computation over A(1) (the first Steenrod algebra subalgebra) in degree 4. This is an 8-dimensional F₂-algebra computation — the most tractable piece of the cobordism proof to partially discharge.

**The construction:**
1. Define A(1) = ⟨Sq¹, Sq²⟩ as an 8-dimensional F₂-algebra (explicit multiplication table)
2. Compute Ext_{A(1)}(F₂, F₂) in degrees 0-4 via a resolution
3. Read off: Ext⁴ ≅ ℤ₁₆ (this IS the cobordism computation for the Pin⁺ case)
4. This discharges one layer of the Z₁₆ axiom: the abstract topology becomes concrete algebra

**Deliverables:**
- [x] `lean/SKEFTHawking/SteenrodA1.lean` — 17 theorems (ZERO sorry):
  - `A1Basis` inductive type (8 elements, `native_decide` confirms cardinality)
  - `a1_degree` grading function
  - Adem relations (Sq¹²=0, Sq¹Sq²=Sq³, Sq²²=Sq³Sq¹)
  - `a1_mul` explicit multiplication table with degree verification
  - Unit laws, augmentation map
  - Hopf algebra structure (statement level)
  - Ext group connection: Ext⁴ → ℤ₁₆ = 2⁴, change-of-rings theorem
- [x] Tests in `tests/test_steenrod.py` (11 tests, all pass)
- [x] Document sync

**Status: COMPLETE** — All 17 theorems proved, zero sorry. First Steenrod algebra formalization in any proof assistant.
**Actual:** 17 theorems (within ~15-25 estimate). `native_decide` confirmed A1 dimension. Multiplication table fully explicit and degree-verified.

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
- [x] `lean/SKEFTHawking/ChiralityWallMaster.lean` — 17 theorems, zero sorry:
  - ChiralityWallStatus structure, chiralityWall2026 instance
  - Pillar 1-3 summary theorems, bridge theorems (GS→GT, GT→anomaly, GS→Z₁₆)
  - chirality_wall_assessment: master conjunction
- [x] Paper 8 draft: `papers/paper8_chirality_master/paper_draft.tex`
  - Three-pillar survey, 5 figures, full bibliography
  - Claims review: 31 PASS, 0 FAIL, 7 WARN (all warnings defensible)
- [x] Paper 7 updated: forward reference to Paper 8, counts reconciled (748/49)
  - Claims review: 20 PASS, 0 FAIL (748 count confirmed), 7 WARN
- [x] Notebooks: `Phase5a_GTChiralFermion_Technical.ipynb` + `_Stakeholder.ipynb`
- [x] 5 new figures (fig66-fig70), LLM figure review (2 PASS, 3 MINOR→fixed)
- [x] `src/chirality/gioia_thorngren.py` domain module + tests
- [x] Stakeholder docs: Phase5a_Implications.md, Phase5a_Strategic_Positioning.md
- [x] Full document sync: Inventory, README, __init__.py, validate.py, companion_guide
- [x] Living docs updated: Feasibility Study + Critical Review v3 (counts + chirality verdict)

**Status: COMPLETE** — 17 theorems, zero sorry. All 12 pipeline stages + claims review.
**Actual:** Single session (April 4, 2026). Packaging wave as expected.

---

## 5. Wave 5 — Spectral Gap Landscape + Verified Statistics Scoping

**Research basis:**
- `Lit-Search/Phase-5a/Spectral gaps for symmetric mass generation- a rigorous landscape assessment.md`
- `Lit-Search/Phase-5a/Formal verification meets lattice Monte Carlo- a feasibility assessment for SMG.md`

These are research-only waves. No implementation — they produce deep research tasks and Phase 6 roadmap items.

### 5A. SMG Spectral Gap Assessment

**Goal:** Encode the algebraic classification data (SMGSymmetryData, anomaly conditions, Altland-Zirnbauer tenfold way) and state the gapped interface conjecture formally. This is the correct axiomatize-then-discharge approach.

**Deliverables:**
- [x] `lean/SKEFTHawking/SMGClassification.lean` — 13 theorems (ZERO sorry):
  - `AZClass` inductive type (10 Altland-Zirnbauer symmetry classes)
  - `SMGSymmetryData` structure with dim, AZ class, fermion counts, anomaly
  - `smg_4d_pin_plus` constructor for 4D Pin⁺ case
  - `HasSpectralGap` typeclass (axiomatized — gap existence is Yang-Mills difficulty)
  - `GappedInterfaceConjecture` structure (TPF 2026 formal statement)
  - Conditional theorems: anomaly-free ↔ SMG, contrapositive no-go
  - Bridges to Z₁₆, GS, TPF, Fidkowski-Kitaev
- [x] Tests in `tests/test_smg.py` (13 tests, all pass)
- [x] Document sync

**Status: COMPLETE** — All 13 theorems proved manually, zero sorry.
**Actual:** 13 theorems (within ~10-15 estimate). Purely definitional as expected.

### 5B. Verified Statistics Roadmap

**Goal:** Scope the formalized statistics pipeline for lattice MC verification. This is a Phase 6+ item but the roadmap should be written now.

**Deliverables:**
- [x] `docs/roadmaps/Phase6_VerifiedStatistics_Roadmap.md` — 3-phase plan:
  - Phase 1 (1-2yr): Jackknife, bootstrap, Γ-method, χ² fitting
  - Phase 2 (2-4yr): Verified CG/multi-shift CG, SpMV
  - Phase 3 (4-7yr): Staggered Dirac, Wilson action, HMC
  - Infrastructure dependency table, effort estimates (20-40 py total)
**Status: COMPLETE** — Roadmap written. Execution deferred to Phase 6 (Mathlib dependency).

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
| **GT finite-volume BdG** | `Formalizing the Gioia-Thorngren lattice chiral fermion in Lean 4.md` | **Mode-by-mode 4x4 matrices**. [H,Q_A]=0 reduces to 2x2 trig identity (sin²+cos²=1). Mathlib has blockDiagonal, kroneckerMap, LieRing.ofAssociativeRing. ~8-10 modules, 2-3 weeks. |
| **Emanant symmetry + anomaly** | `Formalizing emanant symmetry and anomaly matching...` | Emanant symmetry is algebraic abelianization (not IW contraction). Witten anomaly = element 8 ∈ Z₁₆. Group cohomology provable, bordism axiomatized. Bridge theorems to GS/TPF/Onsager clean. |

---

## 8. Estimated Timeline (Revised 2026-04-04)

| Wave | Scope | LOE | Dependencies | Status |
|------|-------|-----|-------------|--------|
| Wave 1A | Onsager DG+Davies | 1 session | None | **COMPLETE** (24 thms) |
| Wave 1B | Contraction→su(2) | 1 session | Wave 1A | **COMPLETE** (12 thms) |
| Wave 2A | Pauli + BdG + Wilson mass | 1-2 weeks | Wave 1 | **NEXT** |
| Wave 2B | GT commutation + non-on-site + Onsager connection | 1-2 weeks | Wave 2A | Queued |
| Wave 3A | Z₁₆ axiom + conditionals | 1 session | None | **COMPLETE** (21+1ax thms) |
| Wave 3B | A(1) Ext computation | 1 session | Wave 3A | **COMPLETE** (17 thms) |
| Wave 4 | Master theorem synthesis + Paper 8 + notebooks | 2-3 weeks | Waves 1-3 | Blocked on Wave 2 |
| Wave 5A | SMG spectral gap assessment | 1 session | None | **COMPLETE** (13 thms) |
| Wave 5B | Verified statistics roadmap | 1 session | None | **COMPLETE** (doc only) |

**Completed:** 6/8 waves (1A, 1B, 3A, 3B, 5A, 5B) — 87 theorems + 1 axiom, zero sorry.
**Remaining:** Wave 2 (~30-40 theorems, 2-3 weeks), then Wave 4 (synthesis + paper, 2-3 weeks).
**Total theorem estimate:** 130-150 new theorems across ~12-15 new Lean modules.

---

*Phase 5a roadmap. Created 2026-04-03. Last updated 2026-04-04 (Wave 2 redesigned after deep research: finite-volume BdG, mode-by-mode k-space, 2x2 trig identity core). Execution: Waves 1+3+5 complete, Wave 2 next, Wave 4 after. All waves follow [Wave Execution Pipeline](../WAVE_EXECUTION_PIPELINE.md).*
