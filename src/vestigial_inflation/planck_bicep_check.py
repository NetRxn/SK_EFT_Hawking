"""Planck 2018 + BICEP/Keck 2021 admissibility region for (n_s, r).

Anchors:
    n_s = 0.9649 ± 0.0042   (Planck 2018 TT,TE,EE+lowE+lensing — N_S_PLANCK)
    r   < 0.036 at 95% CL   (BICEP/Keck 2021)
    N_e ∈ [50, 65]          (canonical slow-roll e-fold window)
"""

import dataclasses


@dataclasses.dataclass(frozen=True)
class PlanckBICEPRegion:
    n_s_central: float = 0.9649
    n_s_sigma: float = 0.0042
    r_upper_95: float = 0.036
    N_e_min: float = 50.0
    N_e_max: float = 65.0

    def n_s_band(self, k_sigma: float = 2.0):
        return (
            self.n_s_central - k_sigma * self.n_s_sigma,
            self.n_s_central + k_sigma * self.n_s_sigma,
        )


def is_admissible(n_s, r, N_e=None, k_sigma_ns: float = 2.0,
                  region: PlanckBICEPRegion | None = None) -> bool:
    """Is (n_s, r [, N_e]) inside the Planck/BICEP admissible region?"""
    if region is None:
        region = PlanckBICEPRegion()
    lo, hi = region.n_s_band(k_sigma_ns)
    if not (lo <= n_s <= hi):
        return False
    if not (0.0 <= r <= region.r_upper_95):
        return False
    if N_e is not None and not (region.N_e_min <= N_e <= region.N_e_max):
        return False
    return True
