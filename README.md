# Dissipative EFT Corrections to Analog Hawking Radiation

Computation and formal verification connecting Schwinger-Keldysh dissipative EFT
to acoustic Hawking radiation in BEC analog gravity. Three papers in a unified codebase:

- **Paper 1 (first-order):** Two transport coefficients (γ₁, γ₂), frequency-independent
  δ_diss = Γ_H/κ correction. PRL format, submission-ready.
- **Paper 2 (second-order):** Two additional coefficients (γ_{2,1}, γ_{2,2}),
  frequency-dependent ω³ spectral distortion, WKB mode analysis, CGL FDR derivation.
- **Paper 3 (gauge erasure):** Universal structural theorem — non-Abelian gauge DOF
  erased by hydrodynamization, U(1) survives (photonization). PRL format.

**Lean 4 formalization:** 72 theorems (40 Aristotle + 32 manual), zero sorry.
Lean 4.28.0, Mathlib commit `8f9d9cff`.

## Project Structure

```
SK_EFT_Hawking/
├── lean/                              # Lean 4 formalization (40/40, zero sorry)
│   ├── lakefile.toml                  # Lake build config (pinned Mathlib)
│   ├── lean-toolchain                 # Lean 4 v4.28.0
│   ├── SKEFTHawking.lean              # Root module (imports all 9)
│   └── SKEFTHawking/
│       ├── Basic.lean                 # Shared types and definitions
│       ├── AcousticMetric.lean        # Structure A: acoustic metric (5 theorems)
│       ├── SKDoubling.lean            # Structure B: SK doubling + KMS (7 theorems)
│       ├── HawkingUniversality.lean   # Structure C: universality + κ-crossing + spin-sonic (9 theorems)
│       ├── SecondOrderSK.lean         # Phase 2: second-order counting + stress tests (19 theorems)
│       ├── WKBAnalysis.lean           # Phase 2: WKB + Bogoliubov bound (15 theorems)
│       ├── CGLTransform.lean          # Phase 2: CGL FDR derivation (7 theorems)
│       ├── ThirdOrderSK.lean          # Phase 3: third-order EFT + parity alternation (14 theorems)
│       └── GaugeErasure.lean          # Phase 3: gauge erasure theorem (11 theorems + 1 axiom)
│
├── src/
│   ├── core/                          # Shared infrastructure
│   │   ├── transonic_background.py    # 1D BEC transonic flow solver + δ_diss estimates
│   │   ├── aristotle_interface.py     # Aristotle API + sorry-gap registry (40/40 filled)
│   │   └── visualizations.py          # Plotly figures + interactive dashboard
│   ├── first_order/                   # Phase 1 specific analysis
│   └── second_order/                  # Phase 2 analysis (absorbed from SK_EFT_Phase2)
│       ├── enumeration.py             # Transport coefficient counting at arbitrary order
│       ├── coefficients.py            # Second-order data structures + action constructors
│       └── wkb_analysis.py            # WKB mode analysis through the dissipative horizon
│
├── papers/
│   ├── paper1_first_order/            # PRL submission
│   │   └── paper_draft.tex
│   └── paper2_second_order/           # PRD / companion paper
│       └── paper_draft.tex
│
├── notebooks/
│   ├── Phase1_Technical.ipynb         # Full paper computation (23 cells, 6 Plotly figs)
│   ├── Phase1_Stakeholder.ipynb       # Lay-person version (20 cells)
│   ├── Phase2_Technical.ipynb         # Second-order computation (30 cells, 9+ Plotly figs)
│   └── Phase2_Stakeholder.ipynb       # Lay-person version (19 cells)
│
├── docs/
│   ├── roadmaps/                      # Phase 1 + Phase 2 technical roadmaps
│   ├── stakeholder/                   # Implications, strategic positioning, companion guides
│   ├── aristotle_results/             # All 13 Aristotle run archives
│   └── archive/                       # Superseded artifacts
│
├── tests/                             # pytest suite
│   ├── test_transonic_background.py   # Physics validation (12/12)
│   ├── test_second_order.py           # Enumeration + WKB tests
│   └── test_lean_integrity.py         # Module structure + sorry-gap regression
│
├── figures/                           # Interactive HTML dashboards
├── scripts/
│   └── submit_to_aristotle.py         # Aristotle submission + integration script
├── pyproject.toml                     # Unified Python dependencies
└── .env                               # Aristotle API key (not committed)
```

## Quick Start

### Python
```bash
cd SK_EFT_Hawking
uv sync                                    # Install dependencies
python -m pytest tests/ -v                 # Run all tests
python -m src.second_order.enumeration     # Print transport coefficient counting table
```

### Lean
```bash
cd SK_EFT_Hawking/lean
lake build                                 # ~2252 jobs, should be clean
```

### Aristotle
```bash
cd SK_EFT_Hawking
python scripts/submit_to_aristotle.py --priority 1    # Submit sorry gaps
python scripts/submit_to_aristotle.py --retrieve <ID>  # Retrieve results
```

## Main Physics Results

### Phase 1: First-Order Correction (Frequency-Independent)

T_eff = T_H(1 + δ_disp + δ_diss + δ_cross)

- δ_disp = (κξ/c_s)² — dispersive, known (Corley-Jacobson)
- δ_diss = Γ_H/κ — **dissipative, our result**
- Γ_H = 1.1 · γ_Bel where γ_Bel = √(na_s³) · κ²/c_s
- Spin-sonic enhancement: ×(c_density/c_spin)² ≈ 100
- FirstOrderKMS: Aristotle discovered the correct KMS structure constraining all 9 coefficients → 2 free parameters

| Experiment | ξ [μm] | c_s [mm/s] | T_H [nK] | D | δ_disp | δ_diss |
|---|---|---|---|---|---|---|
| Steinhauer ⁸⁷Rb | 0.64 | 1.15 | 0.03 | 0.013 | 1.8e-4 | 6.5e-5 |
| Heidelberg ³⁹K | 0.42 | 3.92 | 0.12 | 0.012 | 1.4e-4 | 1.8e-3 |
| Trento ²³Na (spin) | 1.26 | 2.19 | 0.03 | 0.014 | 1.9e-4 | 1.6e-5 |

### Phase 2: Second-Order Correction (Frequency-Dependent)

- Counting formula: count(N) = ⌊(N+1)/2⌋ + 1 at EFT order N
- Two new coefficients at second order, both requiring broken spatial parity
- δ^(2)(ω) ∝ ω³ — spectral distortion absent at first order
- Positivity constraint: (γ_{2,1} + γ_{2,2})² ≤ 4·γ₂·γ_x·β
- Formally verified logical chain: firstOrderCorrection = 0 ↔ dampingRate = 0 ↔ all γᵢ = 0

## Theorem Inventory (40/40 — Zero Sorry)

| Module | Phase | Theorems | Aristotle Runs |
|---|---|---|---|
| AcousticMetric.lean | 1 | 5 | 082e6776, a87f425a, 88cf2000 |
| SKDoubling.lean | 1 | 7 | 082e6776, 638c5ff3, 270e77a0, 20556034 |
| HawkingUniversality.lean | 1 | 3 | d65e3bba, 657fcd6a, 416fb432 |
| SecondOrderSK.lean | 2 | 19 | d61290fd, c4d73ca8, 3eedcabb |
| WKBAnalysis.lean | 2 | 12 | d61290fd, c4d73ca8, 3eedcabb, 518636d7 |

## Build Environment

- **Lean:** 4.28.0 with Mathlib (commit 8f9d9cff6bd728b17a24e163c9402775d9e6a365)
- **Python:** ≥3.11, managed via uv. Key deps: numpy, scipy, sympy, mpmath, plotly, aristotlelib.
- **Visualization:** Plotly (not matplotlib). Color scheme: #2E86AB steel blue, #A23B72 berry, #F18F01 amber.

## References

See `docs/roadmaps/Phase1_Roadmap.md` and `docs/roadmaps/Phase2_Roadmap.md` for full technical context and reference lists.
