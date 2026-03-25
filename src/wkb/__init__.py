"""Exact WKB connection formula for dissipative analog Hawking radiation.

This module implements the full WKB derivation connecting SK-EFT transport
coefficients to observable Hawking spectrum modifications. It goes beyond the
perturbative treatment in src/second_order/wkb_analysis.py in three ways:

1. **Modified unitarity**: |alpha|^2 - |beta|^2 = 1 - delta_k, where delta_k
   is the decoherence parameter encoding probability loss to the environment
   during horizon crossing.

2. **FDR/KMS noise floor**: The fluctuation-dissipation relation mandates a
   thermal noise floor n_noise(omega) that provides a minimum occupation number
   independent of the Hawking process.

3. **Non-perturbative structure**: The exact connection formula includes
   exponential UV suppression above the critical frequency omega_max and
   the full frequency dependence of the EFT corrections through third order.

Submodules:
    connection_formula: Complex turning point, Stokes geometry, exact
        WKB connection formula with dissipation-shifted turning point.
    bogoliubov: Modified Bogoliubov coefficients with broken unitarity,
        decoherence parameter, and FDR noise floor.
    spectrum: Observable Hawking spectrum, platform-specific predictions,
        and comparison with perturbative EFT results.

References:
    - Coutant, Parentani, Finazzi, PRD 85, 024021 (2012) — dispersive WKB
    - Belgiorno, Cacciatori, Trevisan, Universe 10, 412 (2024) — Stokes matrices
    - Robertson, Parentani, PRD 92, 044043 (2015) — dissipative numerics
    - Jana, Loganayagam, Rangamani, JHEP (2020) — SK-EFT + KMS completion

Lean formalization: WKBConnection.lean
"""
