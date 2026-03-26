"""SK-EFT Hawking: Dissipative EFT Corrections to Analog Hawking Radiation.

A unified project encompassing:
  - Phase 1 (first-order): Two transport coefficients (γ₁, γ₂),
    frequency-independent δ_diss = Γ_H/κ correction.
  - Phase 2 (second-order): Two additional coefficients (γ_{2,1}, γ_{2,2}),
    frequency-dependent ω³ spectral distortion, WKB mode analysis.
  - Phase 3 Wave 1 (third-order + gauge erasure):
    * Third-order EFT extension: 3 new coefficients (γ_{3,1}, γ_{3,2}, γ_{3,3}),
      parity alternation theorem, Bogoliubov k⁴ connection.
    * Non-Abelian gauge erasure theorem: universal structural result that
      non-Abelian gauge DOF cannot survive hydrodynamization (U(1) exception).
  - Phase 3 Wave 2 (exact WKB connection formula):
    * Modified unitarity: |α|² - |β|² = 1 - δ_k (decoherence parameter).
    * FDR noise floor: n_noise = δ_k/2 (KMS-mandated spectral floor).
    * Platform-specific predictions for Steinhauer/Heidelberg/Trento BECs.
  - Phase 3 Wave 3 (ADW mean-field gap equation):
    * Tests the gravity wall via Akama-Diakonov-Wetterich tetrad condensation.
    * Critical coupling G_c = 8π²/(N_f Λ²), nontrivial Lorentzian solution for G > G_c.
    * Vergeles mode counting: 16 = 6 + 4 + 2 + 4, gravitons as Higgs bosons.
    * Four structural obstacles for emergent fermion bootstrap.

Lean 4 formalization: 40 Aristotle-proved + 90 manual = 130 theorems + 1 axiom, zero sorry.

Subpackages:
    src.core          — Shared infrastructure (transonic solver, Aristotle, viz)
    src.first_order   — First-order specific analysis
    src.second_order  — Second-order enumeration, coefficients, WKB (perturbative)
    src.gauge_erasure — Non-Abelian gauge erasure theorem
    src.wkb           — Exact WKB connection formula (non-perturbative)
    src.adw           — ADW mean-field gap equation (tetrad condensation)
"""
