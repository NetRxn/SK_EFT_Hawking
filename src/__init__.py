"""SK-EFT Hawking: Dissipative EFT Corrections to Analog Hawking Radiation.

A unified project encompassing:
  - Phase 1 (first-order): Two transport coefficients (gamma_1, gamma_2),
    frequency-independent delta_diss = Gamma_H/kappa correction.
  - Phase 2 (second-order): Two additional coefficients (gamma_{2,1}, gamma_{2,2}),
    frequency-dependent omega^3 spectral distortion, WKB mode analysis.
  - Phase 3 (third-order + gauge erasure + exact WKB + ADW gravity):
    * Third-order EFT with parity alternation theorem.
    * Non-Abelian gauge erasure theorem (universal structural result).
    * Exact WKB connection formula (modified unitarity, FDR noise floor).
    * ADW mean-field gap equation (qualified positive: 2 massless gravitons).
  - Phase 4 (experimental predictions + vestigial gravity + fracton + backreaction):
    * Platform-specific spectral prediction tables for 3 BEC experiments.
    * Vestigial gravity numerically confirmed (mean-field + Euclidean MC).
    * Fracton hydrodynamics as alternative Layer 2 (exponentially more UV info).
    * Backreaction: acoustic BHs cool toward extremality (opposite Schwarzschild).
    * Chirality wall: conditional breach (TPF evades 2/4 GS conditions).
    * GL phase classification: B-phase ground state, A-phase unstabilizable.
    * Routes closed: non-Abelian fracton (4 obstructions), fracton-gravity
      bootstrap (60% gap), both formally verified.

Lean 4 formalization: 216 theorems + 1 axiom, zero sorry, 16 modules.
Aristotle automated theorem prover: 13 Phase 4 theorems verified.

Subpackages:
    src.core          -- Shared infrastructure (transonic solver, Aristotle, viz)
    src.first_order   -- First-order specific analysis
    src.second_order  -- Second-order enumeration, coefficients, WKB (perturbative)
    src.gauge_erasure -- Non-Abelian gauge erasure theorem
    src.wkb           -- Exact WKB connection formula + backreaction
    src.adw           -- ADW gap equation + Ginzburg-Landau phase classification
    src.experimental  -- Platform-specific experimental prediction package
    src.chirality     -- Chirality wall synthesis (TPF vs GS analysis)
    src.vestigial     -- Vestigial gravity lattice simulation (MC + mean-field)
    src.fracton       -- Fracton hydrodynamics, gravity connection, non-Abelian
"""
