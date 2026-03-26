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
- [ ] Notebooks: ExperimentalPredictions_Technical.ipynb + _Stakeholder.ipynb
- [ ] Tests

**Estimated LOE:** Low-Medium (1/2 wave)
**Risk:** Low. All physics is already computed; this is packaging and presentation.
**Status:** `pending`

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
**Status:** `pending`

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
- [ ] Extension of ADW_Technical.ipynb
- [ ] Tests

**Estimated LOE:** Medium
**Risk:** Low-Medium. The GL expansion is standard; the invariant polynomial classification may require careful tensor algebra.
**Status:** `pending`

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
**Status:** `pending`

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
**Status:** `pending`

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
**Status:** `pending`

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
**Status:** `pending`

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
**Status:** `pending`

---

### 3C. Vestigial Gravity Paper [LLM Pipeline]

**Goal:** If 2A succeeded, write the full paper with numerical evidence for vestigial gravity. If 2A produced a negative result, write the negative result paper.

**Prerequisites:** 2A results

**Deliverables:**
- [ ] `papers/paper6_vestigial/paper_draft.tex` — PRD format
- [ ] Figures from 2A, copied to paper directory
- [ ] Notebooks: Vestigial_Technical.ipynb + _Stakeholder.ipynb

**Estimated LOE:** Medium
**Risk:** Low (paper writing on completed results)
**Status:** `pending`

---

## 4. Wave 4 — Synthesis (Days 11-12)

### 4A. Unified Gravity Hierarchy Paper [LLM Pipeline]

**Goal:** Synthesize all gravity results — ADW (Paper 5), vestigial (Paper 6/3C), fracton-gravity (3A) — into a unified assessment of all paths to emergent spin-2 gravity. Compare Level 1 (vestigial), Level 2 (ADW), and fracton alternatives.

**Deliverables:**
- [ ] `docs/gravity_hierarchy_synthesis.md` — Full written synthesis
- [ ] Update Critical Review to v4 with Phase 4 results
- [ ] Update Feasibility Study with Phase 4 results

**Estimated LOE:** Medium
**Status:** `pending`

---

### 4B. Lean Formalization Audit [Lean + Aristotle]

**Goal:** Verify all new Phase 4 results are properly formalized, fill any theorem gaps, run Aristotle on remaining sorrys. Update theorem counts across all documents.

**Deliverables:**
- [ ] All Lean modules build clean (zero sorry)
- [ ] Theorem counts verified from filesystem (per feedback_verify_counts memory)
- [ ] All documents synced per Document Sync Checklist

**Estimated LOE:** Low-Medium
**Status:** `pending`

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

## 6. Infrastructure Notes

### Build & Validation

```bash
cd SK_EFT_Hawking
uv sync                                          # Install/sync dependencies
uv run python -m pytest tests/ -v                # 269/269 tests (Phase 3 exit)
uv run python scripts/validate.py                # 11/11 cross-layer checks + archive
uv run python scripts/review_figures.py          # 34 PNGs + structural checks + manifest
cd lean && ~/.elan/bin/lake build                 # 2259 jobs, clean (Phase 3 exit)
```

**Validation checks (11 total):**
1. `formulas` — Python formulas reference valid Lean theorems
2. `numerical` — Experimental parameters match reference values
3. `identities` — Mathematical identities and boundary conditions
4. `paper_table` — Paper Table 1 values match solver output
5. `theorems` — Theorem registry has expected entries and is self-consistent
6. `notebooks` — Notebooks import physics from src.core, no re-implementation (forbidden set)
7. `lean_source` — Key theorem names found in Lean source files
8. `cgl_fdr` — CGL FDR derivation produces correct results
9. `lean_build` — Lean project builds cleanly (requires lake)
10. `viz_consistency` — Notebook viz uses imported physics, consistent style
11. `notebook_exec` — All notebooks execute without errors (runs all cells via nbclient)

### Figure Review Pipeline

```bash
# Generate all PNGs + run automated structural checks:
uv run python scripts/review_figures.py

# LLM visual review (requires Claude Code session):
# Option A: Use the physics-figure-review plugin agent (after /reload-plugins):
#   Agent tool with subagent_type="physics-figure-review:figure-reviewer"
# Option B: Use a general-purpose agent with the review prompt from the agent file
# Both read PNGs from figures/ + review_manifest.json
# Report: figures/figure_review_report.json
```

**Plugin location:** `.claude/plugins/physics-figure-review/` (registered in `installed_plugins.json` as `physics-figure-review@local`). Contains agent `figure-reviewer` that reads PNGs + manifest and produces structured JSON report.

**Figure count at Phase 3 exit:** 34 total (12 Phase 1+2, 9 Phase 3 Wave 1, 6 Phase 3 Wave 2, 7 Phase 3 Wave 3). All registered in `scripts/review_figures.py` with corresponding functions in `src/core/visualizations.py`.

### PR Submission Checklist (REQUIRED)

Before creating a PR for any wave, ALL of the following must pass:

- [ ] `uv run python -m pytest tests/ -v` — all tests pass
- [ ] `uv run python scripts/validate.py` — all cross-layer checks pass
- [ ] `cd lean && ~/.elan/bin/lake build` — Lean builds cleanly (zero sorry)
- [ ] All notebooks execute cleanly (`nbclient`)
- [ ] **`uv run python scripts/review_figures.py`** — all PNGs generated, structural checks pass
- [ ] **LLM figure review agent** — run, fix ALL issues (FAIL and MINOR), re-run until all PASS
- [ ] No evaluative print statements in notebook code cells (commentary in markdown only)
- [ ] README, `src/__init__.py`, roadmap updated with current counts

**The figure review step is a GATE — do not skip it.**

### Pre-Commit Hook

```bash
ln -sf ../../scripts/pre-commit-notebooks.sh .git/hooks/pre-commit
```

### Aristotle Workflow

```bash
export ARISTOTLE_API_KEY=$(grep ARISTOTLE_API_KEY .env | cut -d= -f2)
uv run python scripts/submit_to_aristotle.py --priority 1
uv run python scripts/submit_to_aristotle.py --retrieve <ID> --integrate
```

### Deep Research

```bash
# Place prompts in:
Lit-Search/Tasks/<prompt_name>.txt
# Results appear in:
Lit-Search/Phase-4/<result_name>.md
```

### Working Documents

```
temporary/working-docs/specs/    # Design specs (if needed)
temporary/working-docs/plans/    # Implementation plans (if needed)
```

### Visualization Workflow (Figures-First)

**Build figures BEFORE notebooks/papers.** This prevents cleanup work.

```
Step 1: Implement figure functions in src/core/visualizations.py
Step 2: Register in scripts/review_figures.py (FigureSpec + func_map)
Step 3: Run LLM figure review agent, fix ALL issues (FAIL + MINOR)
Step 4: Copy publication-ready PNGs to paper figures/ directories
Step 5: Write/update paper draft (.tex)
Step 6: Create Technical notebook to match paper
Step 7: Create Stakeholder notebook for wider audience
```

### Key Conventions

- **Constants & formulas:** Single source of truth in `src/core/constants.py` and `src/core/formulas.py`
- **Visualizations:** Plotly only. Use blue/amber (not red/green) for binary classifications (colorblind accessibility).
- **Formula provenance:** Every formula references its Lean theorem and Aristotle run ID
- **Lean Mathlib:** Pinned to commit `8f9d9cff`. Do not update without coordinating with Aristotle.
- **New modules:** Follow existing patterns — `src/<domain>/`, `tests/test_<domain>.py`, `lean/SKEFTHawking/<Module>.lean`

### Document Sync Checklist

When modifying physics results or proof counts, these must stay synced:

| Category | Files |
|----------|-------|
| **Code** | `src/core/constants.py`, `src/__init__.py`, `scripts/validate.py`, `src/core/formulas.py` |
| **Papers** | `papers/paper1_first_order/paper_draft.tex` through `papers/paper5_adw_gap/paper_draft.tex` (+ paper6 when created) |
| **Notebooks** | All `.ipynb` files |
| **Stakeholder docs** | `docs/stakeholder/*.md` |
| **Roadmaps** | `docs/roadmaps/Phase3_Roadmap.md`, `docs/roadmaps/Phase4_Roadmap.md` |
| **Root** | `SK_EFT_Hawking_Inventory.md`, `README.MD` |
| **Top-level** | `README.md`, `CLAUDE.md`, `Fluid-Based Approach to Fundamental Physics  Feasibility Study.md`, `Fluid-Based Approach to Fundamental Physics- Consolidated Critical Review v3.md` |

### Handoff Documents

Phase 3 handoff: `temporary/Phase3_Complete_Handoff_2026_03_25.md`

---

*Phase 4 roadmap prepared 2026-03-25. Builds on Phase 3 completion (same day). Infrastructure section carries forward from Phase 3 with updated counts.*
