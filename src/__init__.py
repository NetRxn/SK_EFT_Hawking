"""SK-EFT Hawking: Dissipative EFT Corrections to Analog Hawking Radiation.

A unified project encompassing:
  - Phase 1 (first-order): Two transport coefficients (γ₁, γ₂),
    frequency-independent δ_diss = Γ_H/κ correction.
  - Phase 2 (second-order): Two additional coefficients (γ_{2,1}, γ_{2,2}),
    frequency-dependent ω³ spectral distortion, WKB mode analysis.
  - Phase 3 (third-order + gauge erasure):
    * Third-order EFT extension: 3 new coefficients (γ_{3,1}, γ_{3,2}, γ_{3,3}),
      parity alternation theorem, Bogoliubov k⁴ connection.
    * Non-Abelian gauge erasure theorem: universal structural result that
      non-Abelian gauge DOF cannot survive hydrodynamization (U(1) exception).

Lean 4 formalization: 40 Aristotle-proved + 32 manual = 72 theorems, zero sorry.

Subpackages:
    src.core          — Shared infrastructure (transonic solver, Aristotle, viz)
    src.first_order   — First-order specific analysis
    src.second_order  — Second-order enumeration, coefficients, WKB
    src.gauge_erasure — Non-Abelian gauge erasure theorem
"""
