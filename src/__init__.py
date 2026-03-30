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

  - Phase 5 (analytical completion + chirality wall + Layer 1 formalization):
    * Kappa-scaling test predictions for all BEC platforms.
    * Polariton Tier 1 predictions (10^10× hotter T_H).
    * 4D fermion-bag MC production: split transition detected at L=6,8.
    * Chirality wall: GS 9 conditions formalized, TPF evasion machine-verified.
    * Lattice Hamiltonian framework: BZ compact, ℓ²(ℤ) ∞-dim, round discontinuous.
    * Layer 1 categorical infrastructure: PivotalCategory, SphericalCategory,
      SemisimpleCategory, FusionCategory (first-ever in any proof assistant).
    * First fusion category formalization: Vec_G, Rep(S₃), Fibonacci verified.
    * First Drinfeld double formalization: D(G), gauge emergence, chirality limitation.

Lean 4 formalization: 429 theorems + 2 axioms, 30 modules.
  Waves 1-4B: ZERO sorry. Wave 4C: 8 sorry stubs pending Aristotle.
Aristotle automated theorem prover: 91 theorems proved across 25 runs.

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
