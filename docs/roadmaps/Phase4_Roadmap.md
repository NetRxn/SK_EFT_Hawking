# Phase 4: Vestigial Gravity, Fracton Layer 2, and Experimental Predictions

## Technical Roadmap — March 2026

*Prepared 2026-03-25 | Follows Phase 3 (EFT completion, gauge erasure, gravity wall test)*

---

## 0. Entry State

**What Phase 3 established:**
- SK-EFT dissipative corrections through third order, parity alternation theorem
- Non-Abelian gauge erasure: universal structural theorem (Paper 3)
- Exact WKB connection formula: modified unitarity, FDR noise floor, spectral floor (Paper 4)
- ADW mean-field gap equation: qualified positive — nontrivial Lorentzian solution for G > G_c, 2 massless spin-2 graviton modes as Higgs bosons, 4 structural obstacles for emergent fermion bootstrap (Paper 5)
- 130 theorems + 1 axiom (zero sorry), 269 tests, 34 figures, 12 notebooks, 5 papers, 11 Lean modules, 2259 jobs

**What Phase 4 aims to do:**
1. Produce concrete experimental prediction packages for BEC platform engagement
2. Test vestigial gravity (Level 1) numerically via Monte Carlo
3. Formalize fracton hydrodynamics as an alternative Layer 2
4. Compute backreaction corrections extending the WKB chain
5. Synthesize the chirality wall status as original analysis
6. Deepen the ADW/He-3 structural analogy with numerical phase boundaries

**Parallel non-blocking tracks (John):**
- Paper submission review (Papers 1-5 for arXiv)
- Experimental outreach (Heidelberg K-39, Trento spin-sonic)

**Velocity reference:** Phase 3 (three waves) completed in ~10 hours. Phase 4 has four waves of comparable or lighter individual LOE, but Wave 2 is the heaviest (vestigial simulation + fracton foundation).

---

## 1. Wave 1 — Immediate Parallel Launch (Days 1-2)

### 1A. Experimental Prediction Package [LLM Pipeline]

**Goal:** Produce publication-ready tables, figures, and sensitivity requirements that experimentalists (Heidelberg, Trento, Paris polariton) can directly use to plan measurements.

**What to compute:**
- Spectral prediction tables: n(omega) for each platform at 5 representative frequencies
- Required detector sensitivity to distinguish dissipative from dispersive corrections
- Frequency range where exact WKB deviates from perturbative EFT (>1% level)
- Noise floor detection threshold: minimum measurement time to resolve n_noise above thermal background
- Critical frequency omega_max = kappa/D^(2/3) for each platform
- Summary comparison: which platform is best for which measurement

**Sources:** `src/wkb/spectrum.py` (platform_predictions), `src/core/formulas.py`, Papers 1-4

**Deliverables:**
- [ ] `src/experimental/predictions.py` — Functions computing all prediction tables
- [ ] `papers/experimental_predictions/prediction_tables.tex` — Standalone prediction document
- [ ] Figures: prediction comparison across platforms (stakeholder-friendly)
- [ ] Notebooks: Phase4a_ExperimentalPredictions_Technical.ipynb + _Stakeholder.ipynb
- [ ] Tests

**Estimated LOE:** Low-Medium (1/2 wave)
**Risk:** Low. All physics is already computed; this is packaging and presentation.
**Status:** `complete` — src/experimental/predictions.py (33 tests), fig35-38, prediction_tables.tex

---

### 1B. Chirality Wall Synthesis [LLM + Lean]

**Goal:** Produce an original analysis of the chirality wall status — not just literature review but formal analysis of whether the TPF construction's conditions evade the Golterman-Shamir no-go.

**The analysis chain:**
1. Extract the precise mathematical conditions of the GS generalized no-go (lattice translation invariance, finite-range Hamiltonian, relativistic continuum limit, complete interpolating fields)
2. Extract the precise mathematical setting of the TPF disentangler (infinite-dimensional rotor Hilbert spaces, not-on-site symmetries, ancilla DOF, extra-dimensional SPT slab)
3. Formally check: does each GS condition apply to the TPF construction?
4. Identify the 4+1D gapped interface conjecture as the critical unproven assumption
5. Assess: if the conjecture is proven, does the chirality wall fall?

**Key references:** Thorngren-Preskill-Fidkowski (Jan 2026), Golterman-Shamir (2024-2026), Butt-Catterall-Hasenfratz (PRL 2025), Hasenfratz-Witzel (Nov 2025), Gioia-Thorngren (Mar 2025), Seifnashri (Jan 2026)

**Deliverables:**
- [ ] `src/chirality/tpf_gs_analysis.py` — Formal condition extraction and compatibility check
- [ ] `lean/SKEFTHawking/ChiralityWall.lean` — Lean formalization of GS conditions and TPF evasion structure
- [ ] `docs/chirality_wall_analysis.md` — Full written analysis
- [ ] Tests

**Estimated LOE:** Low-Medium (1/2 wave)
**Risk:** Medium. The compatibility question may not have a clean formal answer — the two groups haven't engaged each other's work.
**Status:** `complete` — src/chirality/tpf_gs_analysis.py (55 tests), fig39, docs/chirality_wall_analysis.md

---

### 1C. He-3 Analogy Deepening [LLM Pipeline]

**Goal:** Extend the ADW/He-3 structural parallel from qualitative (fig31) to quantitative — compute the Ginzburg-Landau beta_i analogs for the tetrad effective potential and classify ADW phases by analogy to He-3 A-phase and B-phase.

**The calculation:**
1. Write the Ginzburg-Landau free energy for the tetrad e^a_mu near T_c (expanding V_eff)
2. Identify invariant polynomials under SO(3,1) x GL(4) (tetrad symmetry group)
3. Compute the beta_i analogs from the Coleman-Weinberg potential
4. Classify solutions: "B-phase" (isotropic, e^a_mu = C delta^a_mu), "A-phase" (anisotropic gap with nodes), others
5. Determine which phase is the ground state as a function of coupling

**Sources:** `src/adw/gap_equation.py`, deep research on He-3 gap equation (already available)

**Deliverables:**
- [ ] `src/adw/ginzburg_landau.py` — GL expansion, beta_i computation, phase classification
- [ ] Figures: GL phase diagram, beta_i comparison He-3 vs ADW
- [ ] Extension of Phase3d_ADW_Technical.ipynb
- [ ] Tests

**Estimated LOE:** Medium
**Risk:** Low-Medium. The GL expansion is standard; the invariant polynomial classification may require careful tensor algebra.
**Status:** `complete` — src/adw/ginzburg_landau.py (55 tests), fig40-41

---

### 1R. Deep Research Launch [Async]

**Goal:** Launch deep research prompts for Waves 2-3 topics. Results will be available by Wave 2 start.

**Research prompts (placed in `Lit-Search/Tasks/complete/`):**
- [x] `Phase4_1R_vestigial_lattice_hamiltonian.txt` — Lattice Hamiltonian for vestigial gravity simulation
- [x] `Phase4_1R_fracton_sk_eft_chain.txt` — String-membrane-net → fracton → SK-EFT chain mapping
- [x] `Phase4_1R_backreaction_balbinot.txt` — Balbinot et al. 2025 backreaction methods for acoustic BHs
- [x] `Phase4_1R_pretko_fracton_gravity.txt` — Pretko fracton-gravity, Kerr-Schild map, Gupta-Feynman bootstrap

**Research results (in `Lit-Search/Phase-4/`):**
- `Lattice Hamiltonian for vestigial gravity Monte Carlo simulation.md`
- `From string-nets to fracton hydrodynamics- the coarse-graining chain.md`
- `Quantum backreaction on acoustic black holes in BEC analog gravity.md`
- `The fracton-gravity route to emergent spin-2- status, obstructions, and prospects.md`

**Status:** `complete`

---

## 2. Wave 2 — Gravity Depth + Fracton Foundation (Days 3-6)

### 2A. Vestigial Metric Correlator Simulation [LLM + SciPy + Lean]

**Goal:** Numerically test Volovik's vestigial gravity by measuring the metric correlator g_mu_nu = eta_ab <E^a_mu E^b_nu> in the disordered-tetrad phase of a lattice model with ADW-type interaction.

**Prerequisites:** Deep research results from 1R (vestigial lattice Hamiltonian).
**Research:** `Lit-Search/Phase-4/Lattice Hamiltonian for vestigial gravity Monte Carlo simulation.md`

**The calculation:**

*Step 1 — Define lattice Hamiltonian:*
Start from a 3+1D cubic lattice with Grassmann-valued spinor fields at vertices and ADW-type 8-fermion interaction on plaquettes. The partition function:
Z = integral prod_sites d(psi) prod_links d(omega) exp(S[psi, omega])

Use the Vladimirov-Diakonov cavity method as a guide. Coupling constants lambda_1, lambda_2, lambda_3.

*Step 2 — Mean-field approximation:*
Before full Monte Carlo, solve the mean-field self-consistency equation for the tetrad VEV (extending Phase 3 gap equation) AND the metric correlator separately. The vestigial phase exists where <e> = 0 but <ee> != 0.

*Step 3 — Monte Carlo simulation:*
Implement Metropolis-Hastings sampling on the lattice. Measure:
- Tetrad VEV: <e^a_mu> (should be zero in vestigial phase)
- Metric correlator: g_mu_nu = eta_ab <E^a_mu E^b_nu> (should be nonzero)
- Metric signature: eigenvalues of g_mu_nu (should be Lorentzian)
- EP violation test: compare bosonic and fermionic geodesics

*Step 4 — Phase diagram:*
Scan coupling constants to map the three phases: pre-geometric, vestigial, full tetrad. Identify phase boundaries and order of transitions.

**Success criteria:**
- Vestigial phase exists in a finite region of coupling space
- Metric correlator has Lorentzian signature in this phase
- Phase boundaries are second-order (continuous transition)
- If vestigial phase does not exist → publishable negative result, redirect to fracton-gravity

**Deliverables:**
- [ ] `src/vestigial/lattice_model.py` — Lattice Hamiltonian and coupling structure
- [ ] `src/vestigial/mean_field.py` — Extended mean-field with metric correlator
- [ ] `src/vestigial/monte_carlo.py` — Metropolis-Hastings sampler
- [ ] `src/vestigial/phase_diagram.py` — Coupling scan and phase classification
- [ ] `lean/SKEFTHawking/VestigialGravity.lean` — Structural theorems
- [ ] `papers/paper6_vestigial/paper_draft.tex` — Paper draft (positive or negative)
- [ ] Tests, figures, notebooks (Technical + Stakeholder)

**Estimated LOE:** High (heaviest item in Phase 4)
**Risk:** High. The lattice model must be chosen carefully; Monte Carlo convergence may be slow; the vestigial phase window may be too narrow to detect numerically.
**Status:** `complete` — src/vestigial/ (4 modules, 42 tests), Euclidean pilot with mean-field + MC

---

### 2B. Fracton Hydrodynamics Layer 2 [LLM + Lean + Aristotle]

**Goal:** Formalize the string-membrane-net → fracton → SK-EFT chain as a rigorous alternative Layer 2, and quantify how much more UV information it preserves compared to standard Navier-Stokes hydrodynamics.

**Prerequisites:** Deep research results from 1R (fracton SK-EFT chain).
**Research:** `Lit-Search/Phase-4/From string-nets to fracton hydrodynamics- the coarse-graining chain.md`

**The calculation:**

*Step 1 — String-membrane-net to fracton:*
Formalize the coarse-graining map from Wen's string-membrane-net topological order to type-I fracton phases. Identify conserved quantities: charge, dipole moment, higher multipoles.

*Step 2 — Fracton SK-EFT:*
Write the Schwinger-Keldysh effective field theory for fracton hydrodynamics following Glorioso et al. (JHEP 2023). Identify the transport coefficients and their physical meaning.

*Step 3 — Information retention comparison:*
Quantify UV information preserved:
- Standard NS hydro: conserves energy, momentum, particle number → O(d+2) charges
- Fracton hydro: conserves charge + dipole + higher multipoles → O(infinity) charges
- Hilbert space fragmentation: exponentially more initial states distinguishable

*Step 4 — Gauge information test:*
Can fracton hydro carry non-Abelian gauge information indirectly (via fragmentation patterns, multipole structure, or non-Abelian fracton variants)?

**Deliverables:**
- [ ] `src/fracton/sk_eft.py` — Fracton SK-EFT transport coefficients and symmetry structure
- [ ] `src/fracton/information_retention.py` — UV information comparison: fracton vs standard hydro
- [ ] `lean/SKEFTHawking/FractonHydro.lean` — Structural theorems (conservation laws, information bounds)
- [ ] Tests, figures, notebooks
- [ ] Assessment document: `docs/fracton_layer2_assessment.md`

**Estimated LOE:** High
**Risk:** Medium. The fracton SK-EFT exists in the literature (Glorioso et al.); our contribution is the formalization and information comparison.
**Status:** `complete` — src/fracton/ (2 modules, 88 tests), docs/fracton_layer2_assessment.md

---

### 2C. Backreaction Calculation [LLM Pipeline]

**Goal:** Extend the WKB chain with backreaction corrections. Acoustic black holes cool and approach extremality (opposite of Schwarzschild). Compute the backreaction timescale and connect to Balbinot et al. 2025.

**Prerequisites:** Deep research results from 1R (Balbinot methods).
**Research:** `Lit-Search/Phase-4/Quantum backreaction on acoustic black holes in BEC analog gravity.md`

**The calculation:**
1. Compute energy flux through the acoustic horizon from the exact WKB spectrum
2. Backreaction: dn/dt ~ -(energy flux) modifies the background flow
3. Temperature evolution: T_H(t) decreases as the BH loses energy
4. Extremality approach: surface gravity kappa → 0 asymptotically
5. Timescale estimate for each BEC platform

**Deliverables:**
- [ ] `src/wkb/backreaction.py` — Energy flux, temperature evolution, extremality approach
- [ ] Extension of Paper 4 or standalone section
- [ ] Figures: T_H(t) evolution for three platforms
- [ ] Tests

**Estimated LOE:** Medium
**Risk:** Low-Medium. The physics is well-understood; connecting to the specific Balbinot framework requires careful matching.
**Status:** `complete` — src/wkb/backreaction.py (76 tests), acoustic BH cooling toward extremality

---

## 3. Wave 3 — Extensions + Cross-Connections (Days 7-10)

### 3A. Fracton-Gravity Kerr-Schild [LLM + Lean + Aristotle]

**Goal:** Investigate whether linearized gravity can emerge from fracton symmetric tensor gauge theory via the Kerr-Schild map and Gupta-Feynman bootstrap, and formalize the gap to full diffeomorphism invariance.

**Prerequisites:** 2B (fracton Layer 2 formalization), 1R(iv) deep research
**Research:** `Lit-Search/Phase-4/The fracton-gravity route to emergent spin-2- status, obstructions, and prospects.md`

**The calculation:**
1. Write the symmetric tensor gauge theory of Pretko (2017): A_ij gauge field with fracton gauge symmetry
2. Show that the linearized equation of motion matches linearized Einstein gravity
3. Execute the Gupta-Feynman bootstrap: iteratively add nonlinear corrections
4. Identify where the bootstrap breaks down (the gap to full diffeomorphism invariance)
5. Compare to the ADW route: which path to spin-2 gravity is more accessible?

**Deliverables:**
- [ ] `src/fracton/gravity_connection.py` — Kerr-Schild map, bootstrap analysis, gap assessment
- [ ] `lean/SKEFTHawking/FractonGravity.lean` — Structural theorems (linearized equivalence, bootstrap obstruction)
- [ ] Tests, figures

**Estimated LOE:** Medium-High
**Risk:** Medium. The linearized equivalence is established; the bootstrap gap assessment is the novel contribution.
**Status:** `complete` — src/fracton/gravity_connection.py, bootstrap gap at 2nd order

---

### 3B. Non-Abelian Fracton Hydrodynamics [LLM + Lean]

**Goal:** Investigate Wang-Xu-Yau non-Abelian tensor gauge theories and determine whether they are compatible with Yang-Mills algebra or represent a fundamentally different structure.

**Prerequisites:** 2B (fracton Layer 2 formalization)

**The key question:** Can non-Abelian fracton gauge theories produce emergent SU(N) gauge structure? Or is the algebra necessarily different from standard Yang-Mills?

**Deliverables:**
- [ ] `src/fracton/non_abelian.py` — Non-Abelian fracton gauge structure analysis
- [ ] `lean/SKEFTHawking/FractonNonAbelian.lean` — Structural theorems (algebra comparison, obstruction or construction)
- [ ] Assessment: compatible with Yang-Mills → viable Layer 2 route; incompatible → formalize the obstruction

**Estimated LOE:** Medium
**Risk:** High. This may produce a negative result — the algebra may be incompatible.
**Status:** `complete` — NEGATIVE RESULT. Non-Abelian fracton NOT Yang-Mills compatible. 4 obstructions formalized.

---

### 3C. Vestigial Gravity Paper [LLM Pipeline]

**Goal:** If 2A succeeded, write the full paper with numerical evidence for vestigial gravity. If 2A produced a negative result, write the negative result paper.

**Prerequisites:** 2A results

**Deliverables:**
- [ ] `papers/paper6_vestigial/paper_draft.tex` — PRD format
- [ ] Figures from 2A, copied to paper directory
- [ ] Notebooks: Phase4b_Vestigial_Technical.ipynb + _Stakeholder.ipynb

**Estimated LOE:** Medium
**Risk:** Low (paper writing on completed results)
**Status:** `complete` — papers/paper6_vestigial/paper_draft.tex (PRD format)

---

## 4. Wave 4 — Synthesis (Days 11-12)

### 4A. Unified Gravity Hierarchy Paper [LLM Pipeline]

**Goal:** Synthesize all gravity results — ADW (Paper 5), vestigial (Paper 6/3C), fracton-gravity (3A) — into a unified assessment of all paths to emergent spin-2 gravity. Compare Level 1 (vestigial), Level 2 (ADW), and fracton alternatives.

**Deliverables:**
- [ ] `docs/gravity_hierarchy_synthesis.md` — Full written synthesis
- [ ] Update Critical Review to v4 with Phase 4 results
- [ ] Update Feasibility Study with Phase 4 results

**Estimated LOE:** Medium
**Status:** `complete` — docs/gravity_hierarchy_synthesis.md

---

### 4B. Lean Formalization Audit [Lean + Aristotle]

**Goal:** Verify all new Phase 4 results are properly formalized, fill any theorem gaps, run Aristotle on remaining sorrys. Update theorem counts across all documents.

**Deliverables:**
- [ ] All Lean modules build clean (zero sorry)
- [ ] Theorem counts verified from filesystem (per feedback_verify_counts memory)
- [ ] All documents synced per Document Sync Checklist

**Estimated LOE:** Low-Medium
**Status:** `complete` — 130+1 axiom (zero sorry), 737 tests, 44 figures, all validation passing

---

## 5. Phase 4 Summary

### Timeline

```
Wave 1 (Days 1-2):
  John:  Paper review + outreach (parallel, non-blocking)
  LLM:   1A (prediction package) + 1B (chirality) + 1C (He-3 deepening)
  Async: 1R (deep research for Waves 2-3)

Wave 2 (Days 3-6):
  LLM:   2A (vestigial simulation) — heaviest item
  LLM:   2B (fracton Layer 2) — in parallel during 2A MC runs
  LLM:   2C (backreaction) — fills gaps
  Aristotle: 2B theorem proofs while 2A simulation runs

Wave 3 (Days 7-10):
  LLM:   3A (fracton-gravity) + 3B (non-Abelian fracton) — parallel
  LLM:   3C (vestigial paper) — depends on 2A results

Wave 4 (Days 11-12):
  LLM:   4A (synthesis) + 4B (Lean audit)
```

### Expected outputs

| Paper | Format | Content | Theorems | Figures |
|-------|--------|---------|----------|---------|
| Prediction package | Standalone tables | Platform-specific spectral predictions | — | ~4 |
| Paper 6 (3C) | PRD | Vestigial gravity simulation (+ or -) | TBD | TBD |
| Chirality analysis | Internal doc | TPF vs GS compatibility analysis | TBD | — |
| Fracton assessment | Internal doc | Layer 2 information comparison | TBD | TBD |
| Gravity synthesis | Internal doc | Unified gravity hierarchy | — | — |

### Decision points

| After... | If... | Then... |
|----------|-------|---------|
| Wave 2 (2A) | Vestigial phase exists with Lorentzian metric | Write Paper 6 (positive), proceed to fracton comparison |
| Wave 2 (2A) | Vestigial phase does not exist or is non-Lorentzian | Write negative result paper, redirect to fracton-gravity as primary route |
| Wave 3 (3B) | Non-Abelian fracton is Yang-Mills compatible | Major breakthrough: alternative to gauge erasure obstruction |
| Wave 3 (3B) | Non-Abelian fracton is fundamentally different algebra | Formalize the obstruction, close this route |
| Wave 3 (3A) | Fracton-gravity bootstrap gap is closable | Alternative spin-2 gravity route without fermions |
| Wave 3 (3A) | Bootstrap gap is structural | ADW remains the only spin-2 route |

---

## 6. Wave 5 — Quality Hardening (added 2026-03-26)

Phase 4 Waves 1-4 were executed by subagents with context loss between orchestrator and workers. A systematic audit (2026-03-26) found: physically absurd shot count calculations (27 vs 982 billion from two code paths), hallucinated feasibility narratives contradicted by computed data, Lean theorem registry name mismatches, missing Paper 6 figures, and a mean-field phase classification bug. The validation suite (11 checks) caught structural issues but missed physical nonsense.

Wave 5 hardens everything before Phase 4 can be called complete.

**Entry state (Wave 5 start, 2026-03-26):**
- 821 tests pass, 14/14 validation checks pass (3 new checks added: physical_bounds, cross_path_consistency, paper_provenance)
- Shot count bug fixed (spectrum.py now uses delta_diss at T_H, not divergent max_deviation)
- ARISTOTLE_THEOREMS registry cleaned (54 entries, all match actual Lean theorem names)
- formulas.py Lean references corrected (12 wrong names fixed)
- Notebook viz-ref tags fixed (27 mismatches resolved)
- Experimental predictions narrative corrected (no more "within reach" claims)
- Papers 3-6 "formally verified" claims updated with per-paper Lean module + theorem counts

**What remains:**

### 5A. Lean Theorem Quality Audit [Lean + Aristotle]

**Goal:** Verify all 162 manually-proved theorems are non-trivial (no vacuous proofs from total division), and strengthen any that Aristotle can improve.

**The problem:** Lean 4's total division convention (`0/0 = 0`) means theorems with division in the conclusion can be proved trivially when the denominator is zero. Phase 2 Round 5 caught this for 3 WKB theorems and added strengthened variants. The remaining 162 manual proofs across 16 modules have not been audited for this issue.

**The calculation:**

*Step 1 — Identify suspect theorems:*
Grep all theorems for patterns where the conclusion involves division (`/`), and the hypotheses include positivity constraints (`0 < κ`, `c_s ≠ 0`, `Γ > 0`). These are candidates for vacuous total-division proofs.

*Step 2 — Submit to Aristotle for strengthening:*
For each suspect theorem, submit to Aristotle with `--target <name> --integrate`. Aristotle may find a shorter or stronger proof. If it does, verify the new proof actually exercises the hypotheses (not just `simp` or `trivial`).

*Step 3 — Audit Phase 4 modules specifically:*
Phase 4 added 5 new Lean modules (ChiralityWall, VestigialGravity, FractonHydro, FractonGravity, FractonNonAbelian) with 86 theorems total. These were written by subagents and have not been Aristotle-tested. Submit all 86 theorems as `--target` one-by-one to confirm they are at maximum strength.

*Step 4 — Document results:*
Produce a theorem quality report listing: which theorems were strengthened, which Aristotle couldn't improve (already optimal), which have known total-division vacuity with explanation of why it's acceptable.

**Success criteria:**
- Every theorem either passes Aristotle strengthening or has documented justification for its current form
- No trivially-true theorems remain (conclusions that hold regardless of hypotheses)
- Theorem quality report written to `docs/validation/lean_quality_audit.md`

**Deliverables:**
- [ ] `scripts/audit_lean_quality.py` — Script to identify suspect theorems
- [ ] Aristotle submissions for all Phase 4 manual proofs (86 theorems)
- [ ] Updated Lean files with any strengthened proofs
- [ ] `docs/validation/lean_quality_audit.md` — Quality report
- [ ] Updated `ARISTOTLE_THEOREMS` in constants.py if new run IDs obtained
- [ ] Updated `SorryGap` entries in aristotle_interface.py

**Estimated LOE:** Medium-High (86 Aristotle submissions, review of each result)
**Risk:** Low — worst case is Aristotle times out on hard theorems, which is documented not failed
**Status:** `pending`

---

### 5B. Vestigial Mean-Field Phase Classification Fix [Python + Lean]

**Goal:** Fix the mean-field metric correlator calculation so that the three-phase structure (pre-geometric → vestigial → full tetrad) produces physically correct phase boundaries.

**The problem:** `src/vestigial/mean_field.py:mean_field_metric_correlator()` line 152 computes `metric_fluct = d² * T_eff / curvature` which gives M_g ≈ 10.8 even at G/G_c = 0.3 (very weak coupling). This means EVERY coupling below G_c gets classified as "vestigial" — there is no pre-geometric phase in the current model. The issue: the formula doesn't include volume scaling (1/V factor) or a proper threshold distinguishing thermal noise from genuine vestigial ordering.

**The physics:**

In the thermodynamic limit (V → ∞), the fluctuation contribution to the metric correlator is:

⟨e^a_μ e^b_ν⟩_fluct = δ^{ab} × (d² × T_eff) / (V × |∂²V_eff/∂C²|_{C=0})

The critical point is that M_g scales as **1/V** in the pre-geometric phase (intensive fluctuations → 0 per site) but as **V^0** (extensive order) in the vestigial phase. The current code omits the 1/V factor entirely.

*Step 1 — Add volume scaling to the fluctuation formula:*
The mean-field metric correlator should be: `metric_fluct = d² * T_eff / (V * curvature)` where V is the lattice volume (L^d). For the mean-field analysis, V represents the correlation volume — the number of sites over which fluctuations are correlated.

*Step 2 — Define vestigial ordering criterion:*
The vestigial phase exists when `metric_fluct × V > threshold` — i.e., the total (not per-site) metric correlator is macroscopic. This is the standard condensed-matter criterion for vestigial order (Fernandes et al. 2019).

*Step 3 — Recompute phase diagram:*
With the corrected formula, rescan G/G_c and verify:
- G/G_c << 1: pre-geometric (M_g ~ 1/V → 0)
- G/G_c near 1 (from below): vestigial (M_g diverges as curvature → 0)
- G/G_c > 1: full tetrad (M_E > 0)

*Step 4 — Update all downstream artifacts:*
Paper 6 figures, both Vestigial notebooks, visualizations.py fig_vestigial_phase_diagram.

**Success criteria:**
- Phase diagram shows three distinct regions with physically correct ordering
- Pre-geometric phase occupies G/G_c << 1 (weak coupling)
- Vestigial window is finite and near G_c
- Paper 6 Figure 2 reflects corrected phase diagram
- Vestigial notebook narrative matches corrected figure

**Deliverables:**
- [ ] Fix `src/vestigial/mean_field.py:mean_field_metric_correlator()` — add volume scaling
- [ ] Fix `src/vestigial/phase_diagram.py:classify_phase()` — update threshold logic
- [ ] Update tests in `tests/test_vestigial.py` — test correct phase ordering
- [ ] Regenerate `figures/fig42_vestigial_phase_diagram.png`
- [ ] Update `papers/paper6_vestigial/figures/fig2_phase_diagram.png`
- [ ] Update both Vestigial notebooks (Phase4b_Vestigial_Technical + _Stakeholder)
- [ ] Verify: `validate.py` all 14 checks pass after fix

**Estimated LOE:** Medium
**Risk:** Medium — the thermodynamic limit may not cleanly separate the phases in mean-field; may need Monte Carlo confirmation
**Status:** `pending`

---

### 5C. Paper 6 Native Figures [Python Pipeline]

**Goal:** Generate Paper 6 figures from the vestigial module's own computations, not borrowed from Paper 5.

**The problem:** Paper 6 Figure 1 is currently a copy of `fig28_adw_effective_potential.png` (from Paper 5 / ADW module). Paper 6 should have its own figure showing V_eff at the three coupling ratios mentioned in its text (G/G_c = 0.5, 0.9, 1.5). Figures 2+3 were merged into one — the paper originally described 3 distinct figures.

**Deliverables (following Wave Execution Pipeline stages 8-10):**
- [ ] Add `fig_vestigial_effective_potential()` to `src/core/visualizations.py` — V_eff at G/G_c = 0.5, 0.9, 1.5 using `src/adw/gap_equation.py` with vestigial-specific labels
- [ ] Add `fig_vestigial_order_parameters()` to `src/core/visualizations.py` — M_E and M_g vs G/G_c showing mean-field + MC comparison (if MC data is meaningful after 5B fix)
- [ ] Register both in `scripts/review_figures.py`
- [ ] Run LLM figure review agent → fix any FAIL/MINOR → re-run until all PASS
- [ ] Copy PNGs to `papers/paper6_vestigial/figures/`
- [ ] Update `paper_draft.tex` to use native figures with correct `\includegraphics` refs
- [ ] Update `paper_draft.tex` to restore 3-figure structure if warranted by 5B results

**Depends on:** 5B (mean-field fix) — must be done first so figures reflect corrected physics
**Estimated LOE:** Low-Medium
**Status:** `blocked` by 5B

---

### 5D. LLM Figure Review for Phase 4 Figures [Review Pipeline]

**Goal:** Run the figure review agent on all Phase 4 figures (fig35-fig44) that were not reviewed at the correct pipeline stage during Wave 1-4 execution.

**The problem:** The Wave Execution Pipeline mandates LLM figure review as a gate (Stage 9) before papers and notebooks. During Wave 1-4, subagents may have skipped or missequenced this step.

**Deliverables:**
- [ ] Run `uv run python scripts/review_figures.py` — confirm all 44 PNGs generate
- [ ] Run LLM figure review agent on all figures, focusing on fig35-fig44 (Phase 4)
- [ ] Fix any FAIL or MINOR issues in `visualizations.py`
- [ ] Regenerate PNGs, re-review until all PASS
- [ ] Save report to `figures/figure_review_report.json`

**Estimated LOE:** Low
**Status:** `pending`

---

### 5E. Notebook Narrative Consistency Audit [Manual Review]

**Goal:** Verify all Phase 3-4 notebook narrative text is consistent with computed values. No hallucinated feasibility claims, no hardcoded numbers that contradict formulas.py output, no vague claims unsupported by computation.

**The problem:** ExperimentalPredictions notebooks had "within reach" text contradicted by 10^12 shot requirements. Vestigial notebook had wrong phase ordering description. Other Phase 3-4 notebooks have not been audited for similar issues.

**Notebooks to audit:**
- [ ] Phase3a_ThirdOrder_Technical + _Stakeholder
- [ ] Phase3b_GaugeErasure_Technical + _Stakeholder
- [ ] Phase3c_WKBConnection_Technical + _Stakeholder
- [ ] Phase3d_ADW_Technical + _Stakeholder
- [ ] Phase4b_Vestigial_Technical (text sections, after 5B fix)

**For each notebook, verify:**
1. Every numerical claim in markdown matches the code cell output above/below it
2. No feasibility claims without supporting computation
3. No "formally verified" claims without specific theorem names
4. Color descriptions in text match actual figure colors
5. Phase/wave attribution is correct

**Deliverables:**
- [ ] Per-notebook audit notes (can be inline comments or a summary doc)
- [ ] Fixes to any incorrect narrative text found
- [ ] `validate.py` all 14 checks pass after fixes

**Estimated LOE:** Medium
**Status:** `pending` (partially done for ExperimentalPredictions + Vestigial)

---

### 5F. Paper Numerical Claims Audit [Validation Pipeline]

**Goal:** Extend CHECK 14 (paper_provenance) to extract and verify ALL numerical values in paper tables, not just theorem refs and figure presence.

**The problem:** Current CHECK 14 verifies theorem names exist in Lean and figures aren't placeholders, but doesn't compare numerical table values against computed results. Papers 4-6 have numerical claims that haven't been traced back to `formulas.py`.

**Papers to audit:**

*Paper 1 (first-order):* Table 1 values already checked by CHECK 4 (paper_table). ✓

*Paper 2 (second-order):* Table with δ^(2) values at three platforms. Verify against `formulas.second_order_correction()`.

*Paper 4 (WKB connection):* Platform parameters table. Verify against `wkb/spectrum.py` platform functions.

*Paper 5 (ADW gap):* Critical coupling G_c value. Verify against `formulas.adw_critical_coupling()`.

*Paper 6 (vestigial):* Phase boundaries. Verify against corrected `vestigial/phase_diagram.py` (after 5B).

**Deliverables:**
- [ ] Extend `check_paper_provenance()` in `scripts/validate.py` to parse numerical values from each paper's tables
- [ ] Add computed-vs-claimed comparisons at 0.5% tolerance
- [ ] Fix any discrepancies found
- [ ] All 14 checks pass

**Depends on:** 5B (for Paper 6 values)
**Estimated LOE:** Medium
**Status:** `pending`

---

### 5G. Top-Level Document Update [Document Sync]

**Goal:** Update Feasibility Study and Critical Review v3 with corrected Phase 4 results, honest feasibility framing, and current counts.

**Deliverables:**
- [x] Update `docs/Fluid-Based...Feasibility Study.md` — SK-EFT row with Phase 4 results (done Wave 5)
- [x] Update `docs/Fluid-Based...Critical Review v3.md` — SK-EFT row, experimental evidence (done Wave 5)
- [x] Update `docs/stakeholder/Phase4_Implications.md` — content + counts verified (done Wave 5)
- [x] Update `docs/stakeholder/Phase4_Strategic_Positioning.md` — verified (done Wave 5)
- [x] Verify all counts consistent across all docs — Stage 12 complete (done Wave 5)

**Estimated LOE:** Low-Medium
**Status:** `pending`

---

### Wave 5 Summary

```
5A: Lean theorem quality audit         — pending (86 Aristotle submissions)
5B: Vestigial mean-field fix           — pending (volume scaling in fluctuation formula)
5C: Paper 6 native figures             — blocked by 5B
5D: LLM figure review (Phase 4 figs)  — pending
5E: Notebook narrative audit           — pending (partial: ExperimentalPredictions done)
5F: Paper numerical claims audit       — pending (partial: CHECK 14 exists but incomplete)
5G: Top-level document update          — pending
```

**Execution order:**
1. 5A (Lean audit) + 5D (figure review) — can run in parallel, no dependencies
2. 5B (mean-field fix) — blocks 5C and part of 5F
3. 5C (Paper 6 figures) — after 5B
4. 5E (notebook narrative audit) — after 5B (for Vestigial), otherwise independent
5. 5F (paper claims audit) — after 5B (for Paper 6)
6. 5G (top-level docs) — last, after all other fixes stabilize counts

**Exit criteria for Phase 4 COMPLETE:**
- [ ] All 14 validation checks pass with zero warnings on new checks
- [ ] All 822+ tests pass
- [ ] Lean builds clean (zero sorry)
- [ ] LLM figure review: all figures PASS (no FAIL, no MINOR)
- [ ] Every paper numerical claim verified within 0.5% of computed value
- [ ] Every Lean theorem either Aristotle-strengthened or documented as optimal
- [ ] Vestigial phase diagram shows physically correct three-phase structure
- [ ] No narrative text contradicts computed values
- [ ] All counts consistent across all documents
- [ ] Wave Execution Pipeline (`docs/WAVE_EXECUTION_PIPELINE.md`) followed for all fixes

---

## 7. Infrastructure

**All infrastructure is now defined in `docs/WAVE_EXECUTION_PIPELINE.md`.** That document is the single authoritative reference for:

- The 12-stage wave execution sequence with gates
- The 7 pipeline invariants
- Build, validation, Aristotle, figure review, and document sync procedures
- All conventions and key commands

The pipeline document supersedes the scattered infrastructure sections in Phase 3 and earlier Phase 4 roadmaps. Any future wave of work MUST follow the pipeline stages in order.

### Quick Reference

```bash
cd SK_EFT_Hawking
uv run python -m pytest tests/ -v                    # 822 tests
uv run python scripts/validate.py                    # 14 checks
uv run python scripts/review_figures.py              # 45 PNGs + structural checks
cd lean && lake build                                 # zero sorry
```

### Current Counts (Wave 5 entry)

| Metric | Count |
|--------|-------|
| Lean theorems | 216 + 1 axiom |
| Lean modules | 16 |
| Aristotle-proved | 56 (run IDs in constants.py) |
| Manual proofs | 160 |
| Python tests | 822 |
| Validation checks | 14/14 pass |
| Pipeline figures | 45 |
| Papers | 6 + prediction tables |
| Notebooks | 16 (8 Technical + 8 Stakeholder) |

### Handoff Documents

- Phase 3: `temporary/Phase3_Complete_Handoff_2026_03_25.md`
- Phase 4 quality audit: This roadmap (Wave 5 section)

---

*Phase 4 roadmap prepared 2026-03-25. Wave 5 (quality hardening) added 2026-03-26 after systematic audit. Infrastructure now defined in `docs/WAVE_EXECUTION_PIPELINE.md`.*
