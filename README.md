# Dissipative EFT Corrections to Analog Hawking Radiation

Computation and formal verification for the paper connecting Schwinger-Keldysh
dissipative EFT to acoustic Hawking radiation in BEC analog gravity.

**Target:** PRL (4 pages + supplement) or PRD Rapid Communication

## Project Structure

```
SK_EFT_Hawking_Paper/
├── lean/                          # Lean 4 formalization (blueprint+sorry)
│   ├── lakefile.lean              # Lake build config (Mathlib dependency)
│   ├── lean-toolchain             # Lean 4 v4.16.0
│   ├── SKEFTHawking.lean          # Root module
│   └── SKEFTHawking/
│       ├── Basic.lean             # Shared types: FluidBackground, SonicHorizon, EFT params
│       ├── AcousticMetric.lean    # Structure A: Unruh-Visser acoustic metric theorem
│       ├── SKDoubling.lean        # Structure B: SK doubling constraint uniqueness
│       └── HawkingUniversality.lean # Structure C: T_H universality with dissipation
├── src/                           # Python computation layer
│   ├── transonic_background.py    # 1D BEC transonic flow solver + δ_diss estimates
│   └── aristotle_interface.py     # Aristotle API for Lean sorry-filling
├── tests/
│   └── test_transonic_background.py  # Physics validation tests (12/12 passing)
├── docs/
│   ├── SK_EFT_Hawking_Paper_Roadmap.md  # Full technical roadmap
│   └── references/                # Reference documents
├── pyproject.toml                 # Python dependencies (aristotlelib, numpy, scipy)
└── .env                           # Aristotle API key (not committed)
```

## Quick Start

### Python (computation)
```bash
cd SK_EFT_Hawking_Paper
source .venv/bin/activate        # or: uv venv && uv sync
python -m src.transonic_background   # Run background solver for all 3 BEC experiments
python -m pytest tests/ -v           # Run physics tests
python -m src.aristotle_interface    # Print sorry gap summary
```

### Lean (formalization)
```bash
cd SK_EFT_Hawking_Paper/lean
lake build                       # Build with Mathlib (first build fetches deps)
```

### Aristotle (sorry-filling)
```bash
cd SK_EFT_Hawking_Paper
source .venv/bin/activate
export ARISTOTLE_API_KEY=$(grep ARISTOTLE_API_KEY .env | cut -d= -f2)
aristotle submit "Fill all priority-1 sorries" --project-dir ./lean --wait
```

## Key Physics Results (Numerical Estimates)

| Experiment | ξ [μm] | c_s [mm/s] | T_H [nK] | D | δ_disp | δ_diss |
|---|---|---|---|---|---|---|
| Steinhauer ⁸⁷Rb | 0.64 | 1.15 | 0.03 | 0.013 | 1.8e-4 | 6.5e-5 |
| Heidelberg ³⁹K | 0.42 | 3.92 | 0.12 | 0.012 | 1.4e-4 | 1.8e-3 |
| Trento ²³Na (spin) | 1.26 | 2.19 | 0.03 | 0.014 | 1.9e-4 | 1.6e-5 |

## Sorry Gap Summary

| Priority | Count | Description | Aristotle Prospects |
|---|---|---|---|
| 1 (algebraic) | 4 | Determinants, matrix inverse, inequalities | Likely fillable |
| 2 (moderate) | 3 | EFT expansion, monomial counting | Partially fillable |
| 3 (analysis) | 5 | WKB, Heun equation, FDR | Likely remains sorry |
| **Total** | **12** | | |

## References

See `docs/SK_EFT_Hawking_Paper_Roadmap.md` §10 for the complete reference list.
