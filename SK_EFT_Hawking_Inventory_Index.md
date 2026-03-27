# SK-EFT Hawking Inventory Index

**Purpose:** LLM-friendly quick reference for the full inventory (`SK_EFT_Hawking_Inventory.md`). Read this first; consult the full inventory for details.

**Last synced:** March 27, 2026 (Wave 5)

---

## Counts (ground truth — update atomically)

| Item | Count | Source of truth |
|------|-------|-----------------|
| Lean theorems | 216 + 1 axiom | `grep -c "^theorem" lean/SKEFTHawking/*.lean` |
| Aristotle-proved | 56 | `src/core/constants.py:ARISTOTLE_PROVED_COUNT` |
| Manual proofs | 160 | 216 - 56 |
| Lean modules | 16 | `ls lean/SKEFTHawking/*.lean` |
| Python source modules | 30 | `find src/ -name "*.py" ! -name "__init__.py"` |
| Test files | 16 | `find tests/ -name "test_*.py"` |
| Test count | 822 | `pytest tests/ -q` |
| Figures | 45 | `grep -c "^def fig_" src/core/visualizations.py` |
| Notebooks | 16 | `ls notebooks/*.ipynb` |
| Papers | 6 + tables | `ls papers/*/paper_draft.tex` |
| Validation checks | 14 | `python scripts/validate.py --list` |
| Stakeholder docs | 11 | See Section 9 of inventory |
| Aristotle runs | 18 | `constants.py:ARISTOTLE_THEOREMS` unique values |

---

## Inventory Sections → What to update

| Section | Covers | When to update |
|---------|--------|----------------|
| 1. Python Source | All `src/` modules with purpose + line counts | New module added or module purpose changes |
| 2. Lean Verification | 16-module table: lines, theorem count, key results | Theorem added/removed, module added |
| 3. Aristotle | Run table with dates + theorem counts | New Aristotle submission |
| 4. Notebooks | 16-notebook table: phase, topic | Notebook added or topic changes |
| 5. Papers | 7-paper table: format, lines, topic, key claims | Paper content changes |
| 6. Tests | 16-file table: test counts, coverage | Test file added or count changes |
| 7. Scripts | 3-script table | Script added or purpose changes |
| 8. Configuration | Dependency table | Dependency added |
| 9. Documentation | Reference, roadmap, stakeholder, analysis tables | Doc added/moved/content changes |
| 10. Key Formulas | Physics formulas with Lean refs | Formula added to formulas.py |
| Summary Table | All counts | Any count changes (run verification commands above) |

---

## Source module map (module → purpose, one line each)

### Core (`src/core/`)
- `constants.py` — Physical constants, experimental params, Aristotle registry
- `formulas.py` — Canonical physics formulas with Lean refs (19 functions)
- `transonic_background.py` — 1D BEC transonic flow solver
- `visualizations.py` — All 42 Plotly figure functions + COLORS palette
- `aristotle_interface.py` — Aristotle API + 56 sorry gap registry

### Phase 1-2 (`src/second_order/`)
- `enumeration.py` — Transport coefficient counting: count(N) = floor((N+1)/2)+1
- `coefficients.py` — Second-order data structures + action constructors
- `wkb_analysis.py` — WKB mode analysis, frequency-dependent Bogoliubov
- `cgl_derivation.py` — CGL dynamical KMS → FDR at arbitrary order

### Phase 3 (`src/gauge_erasure/`, `src/wkb/`, `src/adw/`)
- `gauge_erasure/erasure_theorem.py` — Non-Abelian gauge erasure → U(1) survives
- `wkb/connection_formula.py` — Exact WKB through complex turning point
- `wkb/bogoliubov.py` — Modified unitarity, decoherence
- `wkb/spectrum.py` — Full Hawking spectrum with corrections + noise
- `wkb/backreaction.py` — Acoustic BH cooling toward extremality
- `adw/wen_model.py` — Wen's lattice QED (UV completion)
- `adw/hubbard_stratonovich.py` — HS decomposition → composite tetrad
- `adw/gap_equation.py` — Coleman-Weinberg V_eff, G_c
- `adw/fluctuations.py` — SSB, NG modes (2 gravitons in 4D), Vergeles check
- `adw/ginzburg_landau.py` — GL expansion, He-3 analogy

### Phase 4 (`src/experimental/`, `src/chirality/`, `src/fracton/`, `src/vestigial/`)
- `experimental/predictions.py` — Platform prediction tables, shot counts
- `chirality/tpf_gs_analysis.py` — TPF vs GS no-go: 2/4 conditions evaded
- `fracton/sk_eft.py` — Fracton SK-EFT, binomial charge counting
- `fracton/information_retention.py` — Fracton retains exponentially more UV info
- `fracton/gravity_connection.py` — Kerr-Schild bootstrap, DOF gap
- `fracton/non_abelian.py` — Non-Abelian fracton obstruction (negative result)
- `vestigial/mean_field.py` — Curvature-based 3-phase classification
- `vestigial/lattice_model.py` — Euclidean lattice formulation
- `vestigial/monte_carlo.py` — Metropolis MC for lattice model
- `vestigial/phase_diagram.py` — Phase diagram from MF + MC
- `vestigial/finite_size.py` — Finite-size scaling analysis

---

## Lean module map (module → theorem count, key result)

| Module | Thms | Key Result |
|--------|------|------------|
| Basic | 0 | Type definitions |
| AcousticMetric | 8 | det(g)=-ρ², T_H formula |
| SKDoubling | 9 | Uniqueness, FDR, zeroTemp_nontrivial |
| HawkingUniversality | 9 | Universality theorem |
| SecondOrderSK | 19 | Counting formula, positivity constraint |
| WKBAnalysis | 15 | Damping biconditionals, turning point |
| CGLTransform | 7 | CGL FDR, Einstein relation |
| ThirdOrderSK | 14 | Parity alternation (general N) |
| GaugeErasure | 11+1ax | Erasure theorem, U(1) survival |
| WKBConnection | 17 | Decoherence, noise floor, unitarity |
| ADWMechanism | 21 | Critical coupling, NG modes |
| ChiralityWall | 17 | GS no-go requires all, TPF evasion |
| VestigialGravity | 18 | Phase hierarchy, EP violation |
| FractonHydro | 17 | Binomial monotonicity, erasure universal |
| FractonGravity | 20 | Bootstrap divergence, DOF gap |
| FractonNonAbelian | 14 | YM incompatibility |

---

## Pipeline invariants (from WAVE_EXECUTION_PIPELINE.md)

1. `formulas.py` is canonical — only place physics formulas live
2. `constants.py` is canonical — only place constants + Aristotle registry live
3. `visualizations.py` is canonical — only place figure functions live
4. Every formula has a Lean theorem (zero sorry)
5. Every computed quantity has bounds (CHECK 12)
6. Every paper claim traces to computation (CHECK 14)
7. Narrative derives from data (feasibility claims need computed support)
