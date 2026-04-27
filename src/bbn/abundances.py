"""BBN observational constants — Phase 6b Wave 1.

Mirrors `lean/SKEFTHawking/BBN.lean` §1. All values + 1σ uncertainties
are from published primary sources (DOIs verified in
`CITATION_REGISTRY`).
"""

from __future__ import annotations

# --- Planck 2020 (A&A 641, A6) ---
#: Planck 2020 best-fit baryon density (`Ω_B h²`).
OMEGA_B_H2_CENTRAL: float = 0.02242
#: Planck 2020 1σ uncertainty on `Ω_B h²`.
OMEGA_B_H2_SIGMA: float = 0.00014

#: Planck 2020 effective relativistic species count `N_eff`.
N_EFF_CENTRAL: float = 2.99
#: Planck 2020 1σ uncertainty on `N_eff`.
N_EFF_SIGMA: float = 0.17
#: Planck 2σ slack on `ΔN_eff` (= 2 × N_EFF_SIGMA = 0.34). Threshold
#: any DM candidate's contribution to N_eff must respect.
N_EFF_2SIGMA_SLACK: float = 2.0 * N_EFF_SIGMA

# --- PDG 2022 BBN review ---
#: PDG 2022 primordial Helium-4 mass fraction `Y_p`.
Y_P_CENTRAL: float = 0.245
#: PDG 2022 1σ uncertainty on `Y_p`.
Y_P_SIGMA: float = 0.003

# --- Cooke et al. 2018 (ApJ 855, 102) ---
#: Cooke et al. 2018 deuterium-to-hydrogen ratio.
D_OVER_H_CENTRAL: float = 2.547e-5
#: Cooke et al. 2018 1σ uncertainty on D/H.
D_OVER_H_SIGMA: float = 0.025e-5

# --- Sbordone et al. 2010 (A&A 522, A26) ---
#: Sbordone et al. 2010 lithium-7-to-hydrogen ratio (the "lithium
#: problem" reference value, factor ~3 below Standard-BBN prediction).
LI7_OVER_H_CENTRAL: float = 1.6e-10
#: Sbordone et al. 2010 1σ uncertainty on Li-7/H.
LI7_OVER_H_SIGMA: float = 0.3e-10
