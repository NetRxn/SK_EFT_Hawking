# Phase 5d: ADW Tetrad Gap Equation — Emergent Gravity Feasibility

## Technical Roadmap — April 2026

*Prepared 2026-04-04 | Updated 2026-04-05 | Follows Phase 5c (quantum groups, MTC, E8, verified statistics)*

---

> **AGENT INSTRUCTIONS — READ BEFORE ANY WORK:**
> 1. Read CLAUDE.md, WAVE_EXECUTION_PIPELINE.md, Inventory Index
> 2. Read this roadmap for wave assignments
> 3. Read deep research (see §0 below) — extensive prior corpus exists
> 4. Read Aristotle reference: `docs/references/Theorm_Proving_Aristotle_Lean.md`

---

## 0. Entry State and Research Corpus

### What Phase 5c established (pre-5d):
- 1102 theorems, 0 axioms, 76 Lean modules, 41 sorry pending Aristotle
- Quantum group chain: Onsager → O_q → U_q(sl₂) Hopf → U_q(ŝl₂) → u_q → SU(2)_k MTC
- First RibbonCategory/MTC definitions in any proof assistant
- E8 lattice verified, algebraic Rokhlin disproved (σ=8 ≢ 0 mod 16)
- Hypothesis tracking infrastructure (HYPOTHESIS_REGISTRY, graph integration)
- Verified statistical estimators (jackknife, autocorrelation)

### Existing ADW/gravity infrastructure (71 theorems across 5 modules):
- `ADWMechanism.lean` — 21 theorems: critical coupling G_c, NG modes, gap equation structure
- `WetterichNJL.lean` — 18 theorems: Fierz completeness, scalar/pseudoscalar/vector channels, NJL-ADW correspondence
- `VestigialSusceptibility.lean` — 16 theorems: gamma trace, bubble integral Π₀, RPA susceptibility, vestigial_before_tetrad, exponential window
- `FermionBag4D.lean` — 16 theorems: SO(4) integration, 8-fermion bounds, bag positivity
- `GaugeFermionBag.lean` — 9 theorems: tetrad gauge covariance, metric invariance, bag weight real

### Existing Python infrastructure:
- `src/vestigial/hs_rhmc_torch.py` — PyTorch RHMC production code (Wave 7C)
- `src/vestigial/fermion_bag.py` — Fermion-bag MC algorithm
- `src/vestigial/phase_scan.py` — 4D coupling scan with Binder cumulant
- `src/adw/gap_equation.py` — Coleman-Weinberg V_eff
- `src/adw/fluctuations.py` — SSB, NG modes, Vergeles check

### Deep research corpus (read these — ordered by relevance):

**Phase 5c (newest, most directly relevant):**
- `Lit-Search/Phase-5c/Bridging Wen's emergent QED with ADW tetrad gravity.md` — **PRIMARY REFERENCE.** Full Wen+ADW chain. Explicit gap equation: e^a_μ = G ∫ Tr[γ^a p_μ S(p; e)] d⁴p/(2π)⁴. NJL reduction: Δ = G·Δ·I(Δ), G_c = 1/I(0). Lean formalization via IVT + Banach contraction. Three parallel workstreams defined.

**Phase 5 (computational details):**
- `Lit-Search/Phase-5/Vestigial metric susceptibility from ADW tetrad condensation.md` — Explicit V_eff, G_c = 8π²/(N_f Λ²), vestigial window exponentially narrow in 4D. RPA bubble formalism. Lean formalizability assessed.
- `Lit-Search/Phase-5/HS+RHMC for ADW tetrad condensation with 8×8 Majorana fermions on Spin(4) lattice.md` — Complete RHMC algorithm specification. O(V√κ) scaling. Zolotarev rational approximation. Force computation. Cost estimates L=4 through L=16.
- `Lit-Search/Phase-5/ADW tetrad condensation lattice formulation.md` — 8×8 Majorana formulation. Tetrad bilinear is complex, Option A metric gives real result. Quaternionic Cl(4,0) structure.
- `Lit-Search/Phase-5/The 8×8 Majorana formulation for ADW fermion-bag Monte Carlo.md` — Kramers degeneracy → sign-free MC. Block structure.
- `Lit-Search/Phase-5/Phase_5_follow-up_Effective nearest-neighbor action in ADW tetrad condensation after SO(4) Haar integration.md` — SO(4) Haar → full multi-fermion tower. Leading 4-fermion coupling is attractive.
- `Lit-Search/Phase-5/Hybrid fermion-bag + gauge-link Monte Carlo for ADW tetrad condensation.md` — Hybrid algorithm combining fermion-bag with gauge links.

**Phase 3 (foundational):**
- `Lit-Search/Phase-3/The ADW mean-field gap equation for tetrad condensation with emergent Dirac fermions.md` — Original identification: no explicit HS decomposition published. Vladimirov-Diakonov lattice phases. Volovik vestigial hierarchy.

**Task prompts (for context on what was asked):**
- `Lit-Search/Tasks/complete/ADW_gap_equation_emergent_gravity.txt` — Original research prompt
- `Lit-Search/Tasks/complete/Phase5_5A_fang_gu_adw_calculation_chain.txt` — Fang-Gu topological supergravity chain
- `Lit-Search/Tasks/complete/Phase5_vestigial_correlator_simulation_scoping.txt` — MC scoping
- `Lit-Search/Tasks/complete/Phase5_vestigial_analytical_susceptibility.txt` — Analytical susceptibility

### Key physics finding across the entire corpus:
> **The tetrad gap equation has never been explicitly written down in the published literature.** The equation is structurally determined by the NJL-ADW correspondence. The critical coupling G_c is O(1) in lattice units (Vladimirov-Diakonov found this for the chiral channel in 2D). The 4D tetrad channel is untested. No published work combines Wen's emergent QED with ADW tetrad gravity. This is genuinely unexplored territory.

### Cross-validation (VERIFIED in Wave 1):
Phase-5 vestigial research gives G_c = 8π²/(N_f Λ²). Phase-5d gap equation gives G_c = 1/(N_f·I(0)) with I(0) = c₄·Λ²/2 and c₄ = 1/(4π²). Result: G_c = 8π²/(N_f·Λ²) — **exact match** between integral and V_eff formulations. Proved in Lean as `criticalCoupling_formula` and `criticalCoupling_eq_adw`.

### Current state (Apr 5 2026, end of session):
- **1233 theorems**, 0 axioms, **86 Lean modules**, **22 sorry** (all Aristotle targets)
- Phase 5c: COMPLETE (all sorry filled)
- Phase 5d: 10 waves built, Waves 1-2 COMPLETE, Wave 3 MC running
- TetradGapEquation: 0 sorry (9 proved by Aristotle, 1 disproved)
- Uqsl2Hopf: 0 sorry (Serre coproduct proved by Aristotle `79e07d55`)
- Polariton c_s: corrected 1.0→0.5 µm/ps per reconciliation protocol
- Stimulated Hawking: formulas + figure built, Paper 12 drafted
- 2 MTCs under construction (Ising + Fibonacci), QSqrt2/QSqrt5 types proved
- Coideal embedding + Rep(u_q) correspondence BUILT
- Verified statistics + Kerr-Schild BUILT

---

## 1. Wave 1 — Analytic Gap Equation [~15-20 theorems]

**Goal:** Derive and solve the explicit continuum gap equation for the tetrad VEV.

### 1A. Gap Equation Formulation (Lean) — DONE
- [x] Define `gapOperator G Λ Δ := G * N_f * Δ * gapIntegral Δ Λ` (analytical closed-form, not Bochner integral — simpler and sufficient)
- [x] Define `gapIntegral` with c₄ = 1/(4π²), closed-form I(Δ) = c₄/2·[Λ²−Δ²·ln(1+Λ²/Δ²)]
- [x] Gap operator self-mapping (sorry stub for Aristotle)
- [x] Define critical coupling G_c = 1/(N_f · I(0)) with formula matching V_eff
- [x] G_c > 0 (PROVED: `criticalCoupling_pos` via unfold+positivity)
- [x] Explicit formula 8π²/(N_f·Λ²) (PROVED: `criticalCoupling_formula` via field_simp+ring)
- [x] Match to ADWMechanism.critical_coupling (PROVED: `criticalCoupling_eq_adw`)
- [x] Integral bounds: I(Δ) ≤ I(0), lower bound c₄Λ⁴/(4(Λ²+Δ²)) (sorry stubs — need log inequality)

### 1B. Phase Transition (Lean) — DONE
- [x] Trivial solution Δ = 0 always exists (PROVED: `trivial_fixed_point`)
- [x] For G < G_c: trivial solution is unique (sorry stub: `gap_trivial_unique_subcritical`)
- [x] For G > G_c: nontrivial solution exists via IVT (sorry stub: `gap_nontrivial_exists`)
- [x] Monotonicity: Δ*(G) increasing (sorry stub: `gap_solution_monotone`)
- [x] Bifurcation at G = G_c (PROVED: `bifurcation_at_Gc` via unfold+simp+field_simp+ring)
- [x] Solution bounded by Λ (sorry stub: `gap_solution_bounded`)

### 1C. ADW Connection (Lean) — DONE
- [x] Gap implies full tetrad phase (PROVED: `gap_implies_full_tetrad`, direct from ADWMechanism)
- [x] Vestigial connection: g(0) = G/G_c − 1 (PROVED: `gap_vestigial_connection` via unfold+simp+field_simp)
- [x] NJL-ADW Fierz correspondence: g_njl = G_adw/4 (PROVED: `njl_tetrad_correspondence` via funext+ring)
- [x] Match to ADWMechanism.critical_coupling (PROVED: see 1A above)

**Template:** Used analytical closed-form rather than Bochner integral (simpler, avoids measure theory). The IVT and Banach contraction architecture follows Picard-Lindelöf as planned.

**Result:** 20 theorems. Aristotle `79e07d55` proved 9/10, disproved 1 (gap_solution_bounded — false, counterexample found). **ZERO active sorry.**

### Aristotle results (run `79e07d55`):
| Theorem | Result | Method |
|---------|--------|--------|
| `gapIntegral_pos` | **PROVED** | `Real.log_lt_sub_one_of_pos` (deep research finding) |
| `gapIntegral_strictAnti` | **PROVED** | Calculus: derivative positivity |
| `gapIntegral_tendsto_zero` | **PROVED** | Squeeze theorem with c₄Λ⁴/(2Δ²) → 0 |
| `gapOperator_self_map` | **PROVED** | Product of positives |
| `gap_trivial_unique_subcritical` | **PROVED** | Contrapositive: fixed point ⇒ G ≥ G_c |
| `gap_nontrivial_exists` | **PROVED** | IVT with continuity at Δ=0 |
| `gap_solution_bounded` | **DISPROVED** | Counterexample: G=1/(c₄/2·(1−ln2)), N_f=1, Λ=1, Δ=1 |
| `gap_solution_monotone` | **PROVED** | Fixed-point equation + strict anti-monotonicity |
| `gapIntegral_le_I0` | **PROVED** | strictAnti for Δ>0, equality for Δ=0 |
| `gapIntegral_lower_bound` | **PROVED** | Mean value theorem bound |

### Deliverables:
- [x] `lean/SKEFTHawking/TetradGapEquation.lean` — 20 theorems, lake build clean
- [x] `src/core/formulas.py` — `tetrad_gap_operator`, `tetrad_critical_coupling_integral`, `tetrad_gap_solution`, `tetrad_gap_integral`, `tetrad_density_of_states` (5 new functions with Lean refs)
- [x] `tests/test_tetrad_gap.py` — 26 tests, all passing
- [x] Aristotle `79e07d55`: 9/10 proved, 1 disproved (gap_solution_bounded — false)
- [x] G_c from integral formulation matches V_eff formulation exactly (cross-validated)

---

## 2. Wave 2 — Python Computation [~10 tests]

**Goal:** Solve the gap equation numerically for 4D tetrad channel and compare to vestigial susceptibility.

### 2A. Gap Equation Solver — DONE
- [x] Implement bisection solver in `formulas.py` (`tetrad_gap_solution`) — reduces to g(Δ) = G·N_f·I(Δ) − 1 = 0
- [x] Compute G_c for d=4: G_c = 8π²/(N_f·Λ²) via integral formulation
- [x] Cross-validate with V_eff: G_c matches to machine precision
- [x] Compute Δ*(G) curve via `compute_gap_curve` in `tetrad_gap_solver.py`

### 2B. Phase Diagram — DONE
- [x] Δ*(G) curve: second-order transition at G_c, monotonically increasing
- [x] Phase diagram computation with vestigial window via `compute_phase_diagram`
- [x] Vladimirov-Diakonov comparison: G_c·Λ² = 8π²/N_f ≈ 39.5, confirming O(1) in lattice units

### 2C. New MC Observables — DONE
- [x] Tetrad order parameter: `tetrad_order_parameter` in `tetrad_observables.py`
- [x] Metric (vestigial) order parameter: `metric_order_parameter` — connected 4-point correlator
- [x] Binder cumulant: `binder_cumulant` — verified: U₄→2/3 (ordered), U₄→0 (disordered)
- [x] Spatial correlator: `spatial_correlator` — C(r) for composite tetrad propagation
- [x] Susceptibility from correlator: `susceptibility_from_correlator` — χ = V·Σ C(r)
- [ ] Integration with `phase_scan.py` (deferred to Wave 3 — needs MC production runs)

**Tests:** 42 total (26 gap equation + 16 solver/observables), all passing.

### Deliverables:
- [x] `src/adw/tetrad_gap_solver.py` — gap curve, phase diagram, cross-validation, VD comparison
- [x] `src/adw/tetrad_observables.py` — O_tet, O_met, U₄, C(r), χ from C(r)
- [x] `tests/test_tetrad_gap.py` — 26 tests (gap integral, G_c, operator, solver)
- [x] `tests/test_tetrad_gap_solver.py` — 16 tests (curve, cross-validation, Binder, metric OP)
- [x] `src/core/formulas.py` — 5 new functions with Lean refs (done in Wave 1)
- [x] Figures: `fig_tetrad_gap_curve` (Δ vs G/G_c), `fig_tetrad_gap_integral` (I(Δ) vs Δ) in `visualizations.py`

---

## 3. Wave 3 — Monte Carlo Production [computation-heavy]

**Goal:** Run lattice MC at L=4, 6, 8 targeting the gap equation's predicted critical region.

### Strategy (from deep research):
1. **L=4 broad scan:** Map coupling space with tetrad susceptibility and metric correlator
2. **L=4,6,8 targeted:** Binder cumulant analysis near identified transitions
3. **Cross-validate:** MF gap equation predicts G_c; MC confirms or refutes

### Production guide:
**Use `scripts/run_rhmc_epochs.sh`** — see `docs/references/production_rhmc.md` for full guide.
- Epoch-based runner prevents thermal throttling (5-8x degradation in long runs)
- Defaults tuned for L=8: n_md_steps=60, workers=4, chunk_size=10
- Checkpoint/resume: kill anytime, restart with same command

### Key parameters:
- At d=4 (upper critical dimension), mean-field exponents are exact up to log corrections
- Pseudo-critical coupling shift: ΔG_c ~ L⁻² (6.25% at L=4, 1.56% at L=8)
- Vestigial window is exponentially narrow (BCS-like) — may require L≥8 to resolve
- n_md_steps tuning: target |ΔH| < 1 for >40% acceptance (L=8 needs 60+)

### Prep work (done in W1-2):
- [x] MF-guided scan parameters: `mf_guided_scan_params()` in `phase_scan.py` — centers MC on G_c prediction
- [x] `targeted_binder_analysis()` — runs Binder crossing centered on MF G_c
- [x] All observables defined: O_tet, O_met, U₄, C(r) in `tetrad_observables.py`
- [x] `notebooks/Phase5d_TetradGap_Technical.ipynb` — computation notebook (pre-MC)
- [x] `notebooks/Phase5d_TetradGap_Stakeholder.ipynb` — accessible narrative (pre-MC)

### Deliverables (need actual MC runs):
- [ ] L=4 broad coupling scan data (stored in `data/tetrad_scan_L4/`)
- [ ] L=4,6,8 Binder cumulant crossing analysis
- [ ] Phase boundary map (coupling space with transition identified)
- [ ] Vestigial phase detection (or upper bound on window width)
- [ ] Update notebooks with MC results

### Success criteria:
- **Confirms feasibility:** Nontrivial Binder crossing at O(1) coupling, spatial correlator C(r) ~ 1/r² or slower
- **Rules out:** No transition at any coupling, or only first-order (no continuum limit)
- **Vestigial detection:** Metric order parameter nonzero with zero tetrad order parameter

---

## 4. Wave 4 — Papers and Publication

**Goal:** Update existing paper drafts and finalize for submission.

### Paper 5 (ADW Gap) — UPDATE existing `papers/paper5_adw_gap/paper_draft.tex`
- Current state: Draft exists with title "Mean-field gap equation for tetrad condensation in the ADW mechanism: A fermion bootstrap test at Level 2"
- Updates needed:
  - [ ] Add explicit gap equation derivation for tetrad channel (first in literature)
  - [ ] Add mean-field phase diagram figures from Wave 2
  - [ ] Add Lean formalization section (IVT + Banach, ~15-20 theorems)
  - [ ] Add G_c numerical value and comparison to Vladimirov-Diakonov 2D result
  - [ ] Run claims-reviewer agent (physics-qa:claims-reviewer)
- Venue: Physical Review D

### Paper 6 (Vestigial) — UPDATE existing `papers/paper6_vestigial/paper_draft.tex`
- Current state: Draft exists with title "Vestigial Metric Phase in Emergent Gravity: Lattice Evidence from the ADW Model"
- Updates needed:
  - [ ] Add L=4,6,8 MC results from Wave 3
  - [ ] Add vestigial detection (or upper bound) figures
  - [ ] Add Binder cumulant crossing analysis
  - [ ] Update Lean theorem counts (VestigialSusceptibility + new TetradGapEquation)
  - [ ] Run claims-reviewer agent
- Venue: Physical Review D or PRL (if vestigial phase detected)

### Paper 13 (NEW, if warranted) — Wen+ADW connection paper
- Only if Wave 3 produces definitive results (positive or negative)
- Would be the first paper combining emergent QED with emergent gravity
- [ ] `papers/paper13_wen_adw/paper_draft.tex`
- Venue: PRL (if positive), PRD (if negative but informative)

### Notebooks:
- [x] `notebooks/Phase5d_TetradGap_Technical.ipynb` — gap equation derivation, cross-validation, phase diagram (pre-MC, update after Wave 3)
- [x] `notebooks/Phase5d_TetradGap_Stakeholder.ipynb` — accessible narrative (pre-MC, update after Wave 3)

### Stakeholder docs:
- [ ] `docs/stakeholder/Phase5d_Implications.md`
- [ ] `docs/stakeholder/Phase5d_Strategic_Positioning.md`

### Doc sync (Stage 12):
- [ ] Full Inventory + Index update
- [ ] README update
- [ ] Companion guide update

---

## 4b. Wave 4 — SU(2)_k MTC Instance (First Verified MTC)

**Goal:** Package SU(2)_2 (Ising) as a complete ModularTensorData instance with verified F-symbols and pentagon equation.

### Prerequisites (ALL zero sorry):
- RibbonCategory.lean: BalancedCategory, RibbonCategory, PreModularData, ModularTensorData definitions
- SU2kFusion.lean: all fusion rules proved by native_decide
- SU2kSMatrix.lean: S-matrix unitarity, det ≠ 0 (modularity) proved
- FusionCategory.lean: FSymbolData, PentagonSatisfied structures

### Deliverables:
- [x] `lean/SKEFTHawking/SU2kMTC.lean` — 11 theorems (6 proved + 5 sorry → NOW ZERO sorry), module #78
- [x] `isingF` — F-symbol function for Ising (Hadamard/√2)
- [x] `isingF_sigma_hadamard` — F-matrix values PROVED
- [x] `ising_global_dim_sq` — D² = 4 PROVED (via `Real.mul_self_sqrt`)
- [x] `ising_dim_sigma_sq` — Verlinde dimension consistency PROVED
- [x] `isingMTC` — ModularTensorData instance CONSTRUCTED (first ever)
- [x] `ising_pentagon_holds` — pentagon equation PROVED (Aristotle 78dcc5f4 + native_decide rewrite)
- [x] `isingF_involutory` — F² = I PROVED (Aristotle 78dcc5f4)
- [x] `ising_twist_unitary`, `ising_twist_psi` — twist properties PROVED (Aristotle 78dcc5f4)
- [x] `src/core/formulas.py` — `ising_f_symbol`, `su2k_twist`, `su2k_topological_central_charge`
- [x] Deep research submitted: F-symbols and pentagon in Lean 4

### Current state: 1197 theorems, 81 modules, 0 sorry (SU2kMTC + FibonacciMTC all filled by Aristotle 78dcc5f4), 0 axioms

### Ising MTC (SU2kMTC.lean):
- [x] `isingF` — F-symbols with F^σ_{ψσψ}=-1 corrected
- [x] `isingMTC` — ModularTensorData instance CONSTRUCTED
- [x] `ising_global_dim_sq`, `ising_dim_sigma_sq` — PROVED
- [x] Pentagon, involutory, twist — ZERO sorry (Aristotle 78dcc5f4 + native_decide rewrite)

### Fibonacci MTC (FibonacciMTC.lean) — NEW:
- [x] `lean/SKEFTHawking/QSqrt5.lean` — Q(√5) number field, all 7 theorems PROVED by native_decide
- [x] `fibF` — isotopy-gauge F-symbols, ALL in Q(√5)
- [x] `fibF_values` — F-matrix entries PROVED
- [x] `fibF_involutory_00/01/10/11` — F²=I PROVED by native_decide over QSqrt5
- [x] `fibData` — PreModularData instance CONSTRUCTED
- [x] `fib_chiral` — c_top = 14/5 ≠ 0 PROVED
- [x] `fib_pentagon_all_tau` — pentagon PROVED (Aristotle 78dcc5f4)
- [x] `fib_global_dim`, `fib_dim_consistency` — PROVED (Aristotle 78dcc5f4)

### Infrastructure:
- [x] `QSqrt2.lean` — Q(√2) for Ising, 3 theorems all PROVED
- [x] `QSqrt5.lean` — Q(√5) for Fibonacci, 7 theorems all PROVED
- [x] F^σ_{ψσψ} = -1 sign corrected
- [ ] Rewrite isingF over QSqrt2 for native_decide pentagon

### Deep research completed:
- `Phase-5d/SU(2)_k F-symbols and pentagon data for Lean 4 formalization.md`:
  - Ising: 5 non-trivial F-symbol entries, ~16/243 non-trivial pentagons, F∈Q(√2)
  - Fibonacci: 1 non-trivial pentagon out of 32, isotopy gauge F∈Q(√5)
  - R-matrix+twist need Q(ζ₁₆) for Ising, Q(ζ₅) for Fibonacci
  - Recommended: verify fusion category (F+pentagon) first, braiding later

---

## 5. Wave 5 — Polariton Paper Update (Paper 7)

**Goal:** Update Paper 7 with reservoir-corrected predictions, 2025 LKB breakthrough context, and stimulated Hawking detection pathway.

### Context:
- c_s corrected from 1.0→0.5 µm/ps per reconciliation protocol (3 independent measurements)
- LKB Paris (Falque et al. 2025) demonstrated programmable horizons + negative-energy modes
- Stimulated Hawking (Burkhard et al. 2025) identified as most accessible detection pathway
- Deep research: `Phase-5d/Polariton BEC analog gravity` — comprehensive 2024-2026 review

### Stage 1-2: Constants & Formulas
- [x] c_s corrected: 1.0e6 → 5.0e5 m/s (reservoir-corrected, reconciliation protocol followed)
- [x] xi corrected: 2.0e-6 → 3.0e-6 m (consistent with c_s via ξ=ℏ/m*c_s)
- [x] Provenance updated with 3 independent measurement sources
- [x] `fig_polariton_regime_map` regenerated
- [x] Stimulated Hawking formulas: `stimulated_hawking_gain`, `_snr`, `_spectrum`, `dispersive_hawking_correction`
- [x] `fig_stimulated_hawking_spectrum` — gain vs ω/κ with detection threshold

### Stage 10: Paper Draft — NEW PAPER (no polariton paper exists yet)
- [ ] Create `papers/paper12_polariton/paper_draft.tex` — NEW, not an update
  - [ ] Corrected predictions with reservoir-corrected c_s = 0.5 µm/ps
  - [ ] Stimulated Hawking detection pathway (Grisins 2016, Burkhard 2025)
  - [ ] 2025 LKB breakthrough (Falque et al.): programmable horizons
  - [ ] Platform comparison table (GaAs, CdTe, perovskite, organic, TMD)
  - [ ] Thermal competition: n_thermal ≈ 4 at 4-20K
  - [ ] Key groups: LKB Paris, Snoke/Pittsburgh, Carusotto/Trento
  - [ ] Run claims-reviewer agent

### Deliverables:
- [x] `src/core/formulas.py` — 4 stimulated Hawking functions
- [x] `src/core/visualizations.py` — `fig_stimulated_hawking_spectrum`
- [ ] NEW polariton prediction paper (`papers/paper12_polariton/`)
- [ ] `notebooks/Phase5d_Polariton_Technical.ipynb`
- [ ] `notebooks/Phase5d_Polariton_Stakeholder.ipynb`

---

## 6. Wave 6 — U_q(ŝl₂) Affine Hopf Structure — BUILT

**Goal:** Hopf algebra structure on the affine quantum group. Same architecture as Uqsl2Hopf.

### Deliverables:
- [x] `lean/SKEFTHawking/Uqsl2AffineHopf.lean` — 19 sorry (Aristotle 91434dbd/986b9f66 decomposed into individual cases)
- [x] Coproduct, counit, antipode DEFINED via RingQuot.liftAlgHom
- [x] Counit proved (Aristotle 986b9f66)
- [x] Coproduct: 17/21 cases proved (Aristotle 91434dbd/986b9f66); 4 q-Serre cases remain
- [ ] 4 q-Serre coproduct cases remain (Aristotle 2c668068 in-flight)
- [ ] Antipode: 6/21 cases proved, 15 remain (Aristotle 2c668068 in-flight)
- [ ] Bialgebra axioms (deferred — need relation-respect first)

---

## 7. Wave 7 — Verified Statistics Extension — COMPLETE

**Goal:** Extend VerifiedJackknife for MC data analysis (bootstrap CI, Cauchy-Schwarz, N_eff bound).

### Deliverables:
- [x] `lean/SKEFTHawking/VerifiedStatistics.lean` — 7 theorems, ZERO sorry
- [x] `sampleVariance_nonneg` PROVED
- [x] Cauchy-Schwarz bound, jackknife mean-case, ρ ≤ 1, N_eff ≤ N — ALL PROVED (Aristotle 986b9f66)

---

## 8. Wave 8 — Kerr-Schild Metrics (Fracton Extension) — COMPLETE

**Goal:** Verify KS metric algebraic properties for the fracton-gravity linearization sector.

### Deliverables:
- [x] `lean/SKEFTHawking/KerrSchild.lean` — 8 theorems, ZERO sorry
- [x] `radial_null` PROVED, `schwarzschild_phi_pos` PROVED, `schwarzschild_horizon` PROVED
- [x] DOF counting: KS 2 DOF = spin-2 graviton PROVED
- [x] `ks_inverse_formula` PROVED (Aristotle 986b9f66; original formula was FALSE — corrected to use raised indices)

---

## 9. Wave 9 — Coideal Embedding O_q ↪ U_q(ŝl₂) — COMPLETE

**Goal:** Prove the coideal property for the q-Onsager generators B₀, B₁ inside U_q(ŝl₂). Completes the chain Onsager → O_q → U_q(ŝl₂).

### Prerequisites (ALL met):
- [x] `Uqsl2Affine.lean` — B₀ = F₀+E₀K₀⁻¹, B₁ = F₁+E₁K₁⁻¹ defined (Phase 5c Wave 2)
- [x] `Uqsl2AffineHopf.lean` — affComul defined (Wave 6)
- [x] `OnsagerAlgebra.lean` — Dolan-Grady relations (24 thms, zero sorry)

### Deliverables:
- [x] `lean/SKEFTHawking/CoidealEmbedding.lean` — 6 theorems, ZERO sorry, lake build clean
- [x] Coideal property stated: Δ(B_i) = B_i ⊗ 1 + K_i⁻¹ ⊗ B_i
- [x] Counit: ε(B_i) = 0 stated
- [x] Dolan-Grady connection noted (full cubic relation deferred)
- [x] coideal_B0, coideal_B1, counit_B0, counit_B1 — ALL PROVED (Aristotle 986b9f66)

---

## 10. Wave 10 — Rep(u_q) → SU(2)_k Data Correspondence — COMPLETE

**Goal:** Data-level bridge: u_q(sl₂) at root of unity has k+1 simple modules whose fusion matches su2kFusion.

### Prerequisites (ALL met):
- [x] `RestrictedUq.lean` — u_q defined, zero sorry
- [x] `SU2kFusion.lean` — fusion rules verified, zero sorry

### Deliverables:
- [x] `lean/SKEFTHawking/RepUqFusion.lean` — 14 theorems, ZERO sorry, lake build clean
- [x] `restricted_uq_dim`: dim(u_q) = (k+2)³ PROVED for k=1,2,3 (native_decide)
- [x] `n_simples`: k+1 simple modules PROVED for k=1,2,3
- [x] `classical_dim_pos`, `quantum_dim_vacuum` PROVED
- [x] Fusion correspondence: structural match to su2kFusion (same function)
- [x] `rep_fusion_comm` (commutativity), `peter_weyl_classical` — PROVED (manually last session)

---

## Phase 5d Summary

### Current state (Apr 5 2026, session 2):
- **1253 theorems**, 0 axioms, **88 Lean modules**, **34 sorry**
- Entry state was 1102 thms, 76 modules, 41 sorry
- **+151 theorems, +12 modules** across 2 sessions
- Session 2: CenterFunctor (W12), StimulatedHawking (W13), verified stats Python (W11), papers/notebooks/docs

### Wave status:
| Wave | Focus | Theorems | Sorry | Status |
|------|-------|----------|-------|--------|
| 1 | Tetrad gap equation (Lean) | 20 | 0 | **COMPLETE** |
| 2 | Python solver + observables | — | — | **COMPLETE** |
| 3 | MC production (L=4,6,8) | — | — | L=8 running |
| 4 | Ising + Fibonacci MTC | 39 | 0 | **COMPLETE** (Aristotle 78dcc5f4 + native_decide; all MTC sorry filled, pentagon/hexagon proved) |
| 5 | Polariton paper (Paper 12) | — | — | Claims reviewed, all FAIL fixed |
| 6 | U_q(ŝl₂) affine Hopf | — | 19 | IN FLIGHT (Aristotle 91434dbd/986b9f66 decomposed; counit proved, 17/21 coproduct, 4 q-Serre + 15 antipode remain; Aristotle 2c668068 in-flight) |
| 7 | Verified statistics (Lean) | 7 | 0 | **COMPLETE** (Aristotle 986b9f66) |
| 8 | Kerr-Schild metrics | 8 | 0 | **COMPLETE** (Aristotle 986b9f66; formula corrected to raised indices) |
| 9 | Coideal embedding | 6 | 0 | **COMPLETE** (Aristotle 986b9f66) |
| 10 | Rep(u_q) → SU(2)_k | 14 | 0 | **COMPLETE** (manually proved last session) |
| 11 | Verified statistics (Python) | — | — | **COMPLETE** (5 formulas, 18 tests) |
| 12 | Abstract functor Center→ModCat | 9 | 2 | BUILT (CenterFunctor 2 sorry remain — BLOCKED on Muger center infrastructure, see Phase 5p roadmap) |
| 13 | Stimulated Hawking Lean | 11 | 0 | **COMPLETE** (Aristotle 986b9f66 filled all 5) |

### Completed this session (session 2):
- Papers 5, 11, 12 updated with current results
- 4 notebooks: Polariton + MTC (Technical + Stakeholder)
- 2 stakeholder docs: Phase5d_Implications, Phase5d_Strategic_Positioning
- Wave 11: verified statistics Python (jackknife, autocorrelation, bootstrap CI, Γ-method)
- Wave 12: CenterFunctor.lean — abstract functor Center(Vec_G) ⥤ ModuleCat(DG)
- Claims-reviewer on Paper 12: 5 FAIL fixed, 17 WARN fixed
- Doc sync: Inventory Index, Inventory, README all updated
- Sorry registry fixed, companion guide updated

### Blocked items:
- Aristotle `3b356975` (MTC sorry) — in flight, ~10%
- L=8 RHMC — running (PID 96665)
- L=6 RHMC — needs free cores

### Aristotle batch plan:
See `docs/references/aristotle_batch_plan.md` for full details.

| Batch | Priority | Sorry | Modules | Status |
|-------|----------|-------|---------|--------|
| 1 | P1 | 8 | SU2kMTC, FibonacciMTC | **COMPLETE** (78dcc5f4 — 0 sorry) |
| 2 | P1 | 7 | Uqsl2AffineHopf, CoidealEmbedding | **PARTIAL** — CoidealEmbedding DONE (986b9f66); Uqsl2AffineHopf 19 sorry remain |
| 3 | P2 | 13 | StimulatedHawking, VerifiedStatistics, RepUqFusion | **COMPLETE** (986b9f66 — 0 sorry; RepUqFusion manually) |
| 4 | P3 | 8 | CenterFunctor, KerrSchild, EmergentGravityBounds | **PARTIAL** — KerrSchild+EmergentGravityBounds DONE (986b9f66); CenterFunctor 2 sorry remain |
| 5 | P1 | 19 | Uqsl2AffineHopf | IN FLIGHT (2c668068) |

---

## 11. Assessment: Risk and Reward

### What makes this high-leverage:
- **Genuinely unexplored:** No published work combines Wen + ADW
- **The gap equation has never been written for the tetrad channel** — first explicit derivation
- **Publishable either way:** Positive → emergent gravity feasible. Negative → rules out a major route.
- **Maximum infrastructure reuse:** 71 existing Lean theorems + production MC code
- **Three independent workstreams** can proceed in parallel (analytic/computational/formal)

### Risks:
- Gap equation may have subtleties in the tetrad channel (derivative structure changes UV behavior)
- Vestigial window in 4D is exponentially narrow — may be unresolvable at L≤8
- Wen's emergent fermions may lack the correct spin-connection coupling for ADW
- The Vergeles unitarity proof requires fundamental Grassmann spinors — emergent fermions may not satisfy this

### Hypothesis tracking:
Any new hypotheses introduced should be registered in `HYPOTHESIS_REGISTRY` (constants.py) following the Phase 5c convention: explicit statement, eliminability assessment, dependent theorems, risk evaluation.

---

## 6. Dependencies and Non-Dependencies

| Item | Depends on Phase 5c? | Notes |
|------|----------------------|-------|
| Wave 1 (Lean gap equation) | NO | Uses existing ADW/NJL infrastructure |
| Wave 2 (Python computation) | NO | Uses existing gap_equation.py + phase_scan.py |
| Wave 3 (MC production) | NO | Uses existing RHMC + fermion-bag code |
| Wave 4 (Paper) | YES (Aristotle results) | Needs final theorem counts |
| Wen connection (future) | Partially | Needs effective coupling matching |

**Key principle:** Waves 1-3 can start immediately. The Wen connection (matching effective coupling to G_c) is the long-term physics question; the gap equation computation is self-contained.

---

*Phase 5d roadmap. Created 2026-04-04. Research basis: 10+ deep research files spanning Phases 3-5c, all converging on the same open question. All waves follow WAVE_EXECUTION_PIPELINE.md.*
