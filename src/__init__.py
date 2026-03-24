"""SK-EFT Hawking: Dissipative EFT Corrections to Analog Hawking Radiation.

A unified project encompassing:
  - Phase 1 (first-order): Two transport coefficients (γ₁, γ₂),
    frequency-independent δ_diss = Γ_H/κ correction.
  - Phase 2 (second-order): Two additional coefficients (γ_{2,1}, γ_{2,2}),
    frequency-dependent ω³ spectral distortion, WKB mode analysis.

Lean 4 formalization: 35/35 theorems proved via Aristotle, zero sorry.

Subpackages:
    src.core          — Shared infrastructure (transonic solver, Aristotle, viz)
    src.first_order   — First-order specific analysis
    src.second_order  — Second-order enumeration, coefficients, WKB
"""
