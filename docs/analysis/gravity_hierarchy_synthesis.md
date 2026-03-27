# Gravity Hierarchy Synthesis

**Phase 4, Item 4A | Prepared 2026-03-26**

---

## 1. Executive Summary

This document synthesizes all gravity results across Phases 3-4 of the SK-EFT Hawking project into a unified assessment of emergent spin-2 gravity. Three routes to emergent gravity have been investigated: the ADW tetrad condensation mechanism (Paper 5), the vestigial metric phase (Paper 6), and the fracton-gravity Kerr-Schild correspondence (item 3A). These results are organized into a three-level gravity hierarchy.

**Central finding:** The vestigial metric phase (Level 1) is the most accessible and numerically confirmed form of emergent gravity. It should be the priority target for Phase 5 deepening, while the full tetrad (Level 2) and UV-complete (Level 3) targets remain contingent on resolving structural obstacles.

---

## 2. Three Routes to Emergent Spin-2 Gravity

### 2.1 ADW Mechanism (Paper 5): Qualified Positive at Mean-Field

**What was done:** Solved the self-consistent gap equation for tetrad condensation in the Akama-Diakonov-Wetterich model using emergent Dirac fermions from Wen's string-net condensation (Level 2 test). Computed the Coleman-Weinberg effective potential V_eff(C), identified the critical coupling G_c = 8 pi^2 / (N_f Lambda^2), verified the Vergeles mode counting (16 = 6 + 4 + 2 + 4), and classified the three gravitational phases.

**Key results:**
- Second-order phase transition at G = G_c with automatically Lorentzian signature
- 2 massless spin-2 graviton polarizations as Higgs bosons (not Nambu-Goldstone bosons) of the tetrad order parameter
- Verified: 16 tetrad DOF decompose into 6 spin-connection (absorbed NG bosons) + 4 diffeomorphism (gauge) + 2 graviton (massless Higgs) + 4 massive modes
- Ginzburg-Landau analysis: isotropic "B-phase" (e^a_mu = C delta^a_mu) is the ground state, with ADW beta_i structure directly analogous to He-3 superfluid beta coefficients

**Four structural obstacles (unresolved):**

1. **Spin-connection gap:** Wen's string-net condensation produces emergent U(1) gauge fields, not the SO(3,1) spin connection required by ADW. The spin connection must emerge at the same scale as the tetrad or from a separate mechanism entirely.

2. **Grassmann-bosonic incompatibility:** The ADW construction and Vergeles's unitarity proof rely on fundamental Grassmann (anticommuting) variables. Wen's emergent fermions have a bosonic UV completion (rotor model). It is unproven that the ADW mechanism works with emergent-from-bosonic fermions rather than fundamental Grassmann fields.

3. **Nielsen-Ninomiya doubling:** Wen's emergent fermions come in non-chiral pairs (N_f = 4 Dirac fermions from 2^3 = 8 Weyl species). This is incompatible with the chiral fermion content of the Standard Model.

4. **Cosmological constant:** The ADW cosmological term generically predicts Lambda_CC ~ M_P^4, which is 120 orders of magnitude too large.

**Assessment:** The mechanism works at mean-field level with the correct mode counting and automatic Lorentzian signature. The four obstacles prevent closure of the emergent fermion bootstrap at Level 2 but none is definitively fatal.

**Code:** `src/adw/` (gap_equation.py, hubbard_stratonovich.py, fluctuations.py, wen_model.py, ginzburg_landau.py)
**Lean:** `lean/SKEFTHawking/ADWMechanism.lean`

### 2.2 Vestigial Gravity (Paper 6): Exists at Mean-Field, Euclidean Pilot Confirms

**What was done:** Extended the ADW analysis to include the composite metric correlator g_mu_nu = eta_ab <E^a_mu E^b_nu>. Built a lattice model on a 4D Euclidean hypercubic lattice with Hubbard-Stratonovich-transformed ADW interaction. Ran mean-field analysis and Monte Carlo simulation on L=4 lattices, scanning coupling ratio G/G_c from 0.3 to 3.0.

**Key results:**
- Three-phase structure confirmed by both mean-field and Monte Carlo:
  - Phase I (pre-geometric): |M_E| = 0, |M_g| ~ 0 (uncorrelated thermal noise, curvature large)
  - Phase II (vestigial metric): |M_E| = 0, |M_g| > 0 (correlated metric fluctuations, curvature small)
  - Phase III (full tetrad): |M_E| > 0, |M_g| > 0 (tetrad condensation)
- Vestigial phase identified by a curvature-based criterion: the curvature at the origin of V_eff drops below ~30% of its weak-coupling value, enabling collectively ordered metric fluctuations. Mean-field window: G/G_c ~ 0.8 to 1.0. MC shows onset at somewhat lower coupling (~0.7) due to fluctuation broadening.
- Metric eigenvalues are positive-definite (Euclidean signature) throughout the vestigial phase
- Equivalence Principle violation: bosons experience geometry, fermions do not

**Significance:** The vestigial phase is the most accessible form of emergent gravity because:
- It does not require tetrad condensation (no SSB needed)
- It does not require fermion coupling (no spin-connection gap obstacle)
- It can be studied numerically without confronting the fermion sign problem (Euclidean pilot)
- The EP violation is a distinctive, testable prediction

**Limitations:**
- Euclidean signature only (sign problem for Lorentzian)
- Small lattice (L=4); finite-size scaling needed
- Fermion determinant approximated by mean-field reweighting
- Continuum limit not established

**Code:** `src/vestigial/` (lattice_model.py, mean_field.py, monte_carlo.py, phase_diagram.py)
**Lean:** `lean/SKEFTHawking/VestigialGravity.lean`

### 2.3 Fracton-Gravity (Item 3A): Linearized Equivalence, Bootstrap Gap at Second Order

**What was done (assessment from deep research):** Investigated the Pretko (2017) correspondence between symmetric tensor gauge theory of fractons and linearized general relativity. Analyzed the Gupta-Feynman bootstrap procedure for extending linearized to nonlinear gravity.

**Key results:**
- The linearized Einstein equations can be written as the equation of motion of a symmetric tensor gauge theory with fracton gauge symmetry
- The Kerr-Schild map provides an exact correspondence for a class of solutions (including Schwarzschild in appropriate coordinates)
- The Gupta-Feynman bootstrap (iteratively coupling the spin-2 field to its own stress-energy tensor) reproduces GR at each order, but the fracton gauge structure breaks at second order
- The gap: fracton gauge symmetry (global subsystem symmetry) is fundamentally different from diffeomorphism invariance (local gauge symmetry). The bootstrap requires adding terms that violate the original fracton gauge structure.

**Bootstrap gap quantification (strengthening):** The gap is quantified by comparing cubic vertex tensor structures: GR has 5 independent Sannan structures at cubic order, while fracton theory has 8 (5 shared + 3 fracton-only). The gap magnitude is |8 - 5|/5 = 60%. The 3 excess structures are: (a) two higher-derivative vertices (4 derivatives distributed across fields, allowed by the weaker dd gauge symmetry), and (b) one parity-odd spin-1 sector vertex that causes dynamical instability with an unbounded Hamiltonian. The gap is not closable — removing the excess structures eliminates the fracton-specific DOF entirely.

**DOF gap universality (formally verified):** The fracton DOF gap (fracton_dof - graviton_dof) equals d-1 for d spatial dimensions and is positive for all d >= 2. This is verified computationally for d = 2..8 and formally proved in Lean (theorems `dof_gap_positive_2_through_8`, `dof_gap_eq_d_minus_1_check_4`, `dof_gap_eq_d_minus_1_check_5`). The gap grows with dimension, meaning the bootstrap problem gets worse, not better, in higher dimensions.

**Non-Abelian fracton route closed (item 3B):** Wang-Xu-Yau and Bulmash-Barkeshli non-Abelian fracton theories are NOT Yang-Mills compatible. Four structural obstructions: derivative order (dd vs d), field rank (tensor vs vector), gauge parameter dimension (scalar vs adjoint), and Jacobi identity structure. Formally verified: `obstructions_individually_sufficient`, `param_gap_grows`. Combined with the gauge erasure theorem (Phase 3), the only path to non-Abelian gauge structure bypasses hydro entirely.

**Fracton information retention (item 2B):** Despite gauge erasure, fracton hydro retains exponentially more UV information than standard hydro — formally verified: `fracton_exceeds_standard_general` (for all d >= 2), `binomial_strict_mono` (strict monotonicity of charge count). A concrete Z_3 gauge coarse-graining example quantifies the reconstruction fidelity: fracton CG preserves more gauge-invariant info than standard CG via dipole-moment retention.

**Assessment:** Fracton-gravity provides an intriguing linearized equivalence but faces a structural, quantified gap at nonlinear order. This is not a route to full GR. The fracton route is complementary to ADW: ADW produces full nonlinear gravity from fermion condensation, while fracton produces linearized gravity with a 60% excess in cubic vertex structures.

**Code:** `src/fracton/gravity_connection.py`, `src/fracton/non_abelian.py`, `src/fracton/information_retention.py`
**Lean:** `FractonGravity.lean`, `FractonNonAbelian.lean`, `FractonHydro.lean`
**Research:** `Lit-Search/Phase-4/The fracton-gravity route to emergent spin-2- status, obstructions, and prospects.md`

---

## 3. The Three-Level Gravity Hierarchy

### Level 1: Vestigial Metric

| Aspect | Status |
|--------|--------|
| Definition | g_mu_nu = eta_ab <E^a_mu E^b_nu> nonzero, <E^a_mu> = 0 |
| Existence | Confirmed (mean-field + Euclidean MC) |
| Signature | Positive-definite (Euclidean pilot) |
| Equivalence Principle | Violated (bosons see geometry, fermions do not) |
| Graviton modes | Not defined (no tetrad SSB, no NG bosons) |
| Spin connection | Absent (not needed for metric-only gravity) |
| Key advantage | Avoids all four ADW structural obstacles |
| Key limitation | EP violation means this is not standard GR |
| Experimental signature | Gravitational lensing of photons without matter deflection |

### Level 2: Full Tetrad (Einstein-Cartan)

| Aspect | Status |
|--------|--------|
| Definition | <E^a_mu> = C delta^a_mu nonzero, metric follows |
| Existence | Confirmed at mean-field (ADW gap equation, Paper 5) |
| Signature | Automatically Lorentzian for any real C > 0 |
| Equivalence Principle | Restored (both bosons and fermions couple to geometry) |
| Graviton modes | 2 massless spin-2 (Higgs bosons of tetrad OP) |
| Spin connection | Required but not emergent from string-net |
| Key advantage | Produces full Einstein-Cartan gravity with correct mode counting |
| Key limitation | Four structural obstacles prevent emergent fermion bootstrap |
| Accessible via | ADW mechanism (proven at mean-field, obstacles at bootstrap level) |

### Level 3: UV-Complete Emergent Gravity

| Aspect | Status |
|--------|--------|
| Definition | All structural obstacles resolved, complete emergent gravity |
| Existence | Not achieved |
| Requirements | Spin-connection emergence, Grassmann compatibility, chiral fermions, CC solution |
| Accessible via | ADW + new ingredients, OR fracton-gravity + new ingredients, OR unknown |
| Key limitation | No concrete proposal resolves all four obstacles simultaneously |

---

## 4. Cross-Connections

### 4.1 Connection to the Chirality Wall (Item 1B)

The chirality wall analysis (Phase 4, Item 1B) found a status of **conditional breach**: the Thorngren-Preskill-Fidkowski construction evades the Golterman-Shamir generalized no-go theorem by operating outside its domain (not-on-site symmetries, infinite-dimensional rotor Hilbert spaces, extra-dimensional SPT slab). The critical unproven assumption is the 4+1D gapped interface conjecture.

**Relevance to the gravity hierarchy:**

- **ADW Obstacle 3 (Nielsen-Ninomiya doubling)** is directly related to the chirality wall. If the TPF construction is proven to work, emergent chiral fermions become available, removing one of the four structural obstacles at Level 2.
- **Impact assessment:** Resolving the chirality wall would advance the gravity hierarchy from "4 obstacles" to "3 obstacles" at Level 2. This is necessary but not sufficient for UV completion.
- **The chirality wall is the most advanced of the three structural walls** (gauge, gravity, chirality). There is a concrete construction (TPF) with substantial numerical evidence (SMG in 2+1D and 3+1D). The gravity wall, by contrast, has mean-field evidence but no nonperturbative construction.

### 4.2 Connection to the Gauge Erasure Theorem (Phase 3)

The gauge erasure theorem (Paper 3, Phase 3) establishes that non-Abelian gauge degrees of freedom cannot survive standard hydrodynamization. The GKSW higher-form symmetry argument shows that codimension > 1 operators must commute, restricting hydrodynamic gauge information to Abelian (U(1)) structure.

**Relevance to the gravity hierarchy:**

- **The gauge wall is distinct from the gravity wall.** Even if the vestigial or full tetrad phase is achieved, emergent non-Abelian gauge structure (SU(2)_L, SU(3)_C) requires a separate mechanism.
- **Fracton loophole (partial).** The fracton Layer 2 assessment (Phase 4, Item 2B) identified a genuine structural loophole: subsystem symmetries are not higher-form symmetries, so the GKSW commutativity argument does not apply. Hilbert space fragmentation can protect position-dependent degeneracies. However, the loophole is only partial: the non-Abelian fracton gauge structure (Wang-Xu-Yau) sits outside the Yang-Mills paradigm.
- **Architecture implication.** A complete emergent Standard Model requires both gravity (tetrad/metric) and gauge structure (non-Abelian). The gauge erasure theorem forces these to emerge from different mechanisms or through the fracton loophole.

### 4.3 Connection to SK-EFT Dissipative Corrections (Papers 1-4)

The SK-EFT dissipative framework (Papers 1-4) operates within established gravity (the acoustic metric). The gravity hierarchy addresses the deeper question of where that metric comes from. The connection is:

- **Acoustic metric as vestigial gravity analog.** The acoustic metric g_mu_nu in a BEC is a composite of the fluid velocity and density fields, not a fundamental field. This is structurally analogous to the vestigial metric: geometry exists as a composite, not as a fundamental degree of freedom.
- **Dissipation and the gravity wall.** The SK-EFT dissipative corrections (delta_diss, delta^(2)) arise from the finite lifetime of phononic excitations. In the gravity hierarchy, the transition from Level 1 to Level 2 introduces the tetrad as a propagating degree of freedom with its own dissipative physics. An SK-EFT treatment of tetrad fluctuations near the vestigial-to-full-tetrad transition would be a natural extension.

---

## 5. Comparative Assessment: Which Route Is Most Accessible?

### Route Comparison Table

| Criterion | ADW (Paper 5) | Vestigial (Paper 6) | Fracton-Gravity (3A) |
|-----------|---------------|--------------------|--------------------|
| Graviton? | Yes (2 massless spin-2) | No (metric only) | Yes (linearized) |
| Nonlinear GR? | Yes (mean-field) | No (metric without dynamics) | No (bootstrap gap) |
| EP satisfied? | Yes | No (violated) | N/A (linearized only) |
| Numerical evidence | Mean-field only | Mean-field + MC (Euclidean) | No simulation |
| Structural obstacles | 4 (spin-conn, Grassmann, doubling, CC) | 2 (Euclidean only, small lattice) | 1 (bootstrap gap, fundamental) |
| Formal verification | Lean (6 theorems) | Lean (structural) | Deep research only |
| Publication readiness | Paper 5 drafted | Paper 6 drafted | Assessment only |
| Phase 5 deepening? | Blocked (obstacles) | Ready (finite-size, Lorentzian) | Low priority |

### Accessibility Ranking

1. **Vestigial gravity (Level 1)** -- most accessible. The Euclidean pilot confirms the phase exists. Immediate next steps are well-defined (finite-size scaling, Lorentzian pilot with sign-problem mitigation) and do not require resolving any fundamental obstruction. The EP violation provides a unique experimental signature.

2. **ADW mechanism (Level 2)** -- qualified positive but blocked. The mean-field calculation works correctly, but the four structural obstacles are genuine barriers to a complete emergent fermion bootstrap. Progress requires resolving at least the spin-connection gap and Grassmann-bosonic incompatibility, which are open problems in condensed matter theory.

3. **Fracton-gravity** -- linearized only. The Kerr-Schild correspondence is elegant but the bootstrap gap is fundamental: fracton gauge symmetry cannot reproduce full diffeomorphism invariance. This route serves as a complementary perspective rather than an independent path to emergent gravity.

---

## 6. Phase 5 Recommendation: Vestigial Gravity as Priority Target

Based on the synthesis above, the recommended Phase 5 gravity focus is:

### 6.1 Primary Target: Vestigial Phase Deepening

**Objective:** Establish the vestigial metric phase on a firm numerical footing, sufficient for a strong PRD publication.

**Concrete next steps:**
1. **Finite-size scaling.** Run Monte Carlo on L = 6, 8, 12 lattices. Determine whether the vestigial window survives the thermodynamic limit and measure the critical exponents at the phase boundaries.
2. **Lorentzian pilot.** Investigate sign-problem mitigation strategies (complex Langevin, reweighting, Lefschetz thimbles) to probe the Lorentzian signature case. Even partial results (e.g., reweighting with modest sign-problem severity) would significantly strengthen the paper.
3. **Dynamical fermions.** Replace the mean-field reweighting with exact fermion determinant computation (possible on small lattices with N_f = 4 staggered fermions). This removes the main systematic uncertainty.
4. **Metric dynamics.** Compute the correlation function <g_mu_nu(x) g_rho_sigma(y)> in the vestigial phase. Does it exhibit massless propagation (graviton-like)? Or is the metric static (non-propagating geometry)? This is the key question for Level 1 physics.
5. **EP violation quantification.** Compute the geodesic deviation between a bosonic and a fermionic test particle in the vestigial phase background. Quantify the EP violation as a function of coupling.

### 6.2 Secondary Target: ADW Obstacle Reduction

**Objective:** Reduce the number of structural obstacles from 4 to 2-3.

**Concrete next steps:**
1. **Chirality wall resolution tracking.** If the TPF gapped interface conjecture is proven (or numerically confirmed in 4+1D), Obstacle 3 (Nielsen-Ninomiya) is resolved. Monitor the TPF/Butt-Catterall-Hasenfratz program.
2. **Spin-connection from fracton.** Investigate whether the fracton symmetric tensor gauge structure can provide a precursor to the spin connection. This would connect the fracton-gravity and ADW routes.
3. **Grassmann-bosonic bridging.** The Grassmann-bosonic incompatibility is the most fundamental obstacle. A systematic study of when bosonic UV completions reproduce Grassmann path integral results at IR scales would be valuable.

### 6.3 Tertiary Target: Fracton-Gravity Formalization

**Objective:** Formalize the bootstrap gap as a structural theorem.

**Concrete next step:** Prove in Lean that fracton gauge symmetry cannot reproduce the diffeomorphism algebra beyond linearized order. This would close the fracton-gravity route definitively and redirect effort to ADW/vestigial.

---

## 7. Summary Table

| Result | Phase | Paper | Status | Key Finding |
|--------|-------|-------|--------|-------------|
| ADW gap equation | 3 (Wave 3) | Paper 5 | Complete | Qualified positive: mean-field works, 4 obstacles |
| He-3 analogy deepening | 4 (Wave 1) | Paper 5 extension | Complete | B-phase ground state, GL beta_i computed |
| Vestigial mean-field | 4 (Wave 2) | Paper 6 | Complete | Three-phase structure, vestigial window exists |
| Vestigial MC (Euclidean) | 4 (Wave 2) | Paper 6 | Complete | Confirms mean-field, positive-definite eigenvalues |
| Fracton Layer 2 | 4 (Wave 2) | Assessment doc | Complete | Partial gauge info preservation via HSF |
| Fracton-gravity bootstrap | 4 (Wave 3) | Assessment | Pending (3A) | Linearized equivalence, gap at 2nd order |
| Chirality wall analysis | 4 (Wave 1) | Analysis doc | Complete | Conditional breach (TPF evades GS) |
| Gauge erasure theorem | 3 (Wave 2) | Paper 3 | Complete | Non-Abelian DOF erased by hydrodynamization |

---

## 8. References

1. Akama, K. Prog. Theor. Phys. 60, 1900 (1978).
2. Diakonov, D. arXiv:1109.0091 (2011).
3. Wetterich, C. Phys. Rev. D 70, 105004 (2004).
4. Volovik, G. E. JETP Lett. 119, 330 (2024); arXiv:2312.09435.
5. Vladimirov, A. A. and Diakonov, D. Phys. Rev. D 86, 104019 (2012).
6. Sexty, D. and Wetterich, C. Nucl. Phys. B 867, 290 (2013).
7. Vergeles, S. N. Phys. Rev. D 112, 054509 (2025).
8. Pretko, M. Phys. Rev. D 96, 024051 (2017).
9. Fernandes, R. M., Orth, P. P., and Schmalian, J. Annu. Rev. Condens. Matter Phys. 10, 133 (2019).
10. Golterman, M. and Shamir, Y. arXiv:2406.07997 (2024-2026).
11. Thorngren, R., Preskill, J., and Fidkowski, L. (Jan 2026).
12. Glorioso, P., Huang, J., and Lucas, A. JHEP 05, 022 (2023).

---

*Gravity hierarchy synthesis produced as part of Phase 4, Item 4A of the SK-EFT Hawking project. Synthesizes results from Papers 3, 5, 6 and Phase 4 items 1B, 2A, 2B, 3A.*
