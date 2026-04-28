"""Phase 6e Wave 3: Nonlinear diffeomorphism invariance (path-b).

Numerical companion to ``lean/SKEFTHawking/NonlinearDiffInvariance.lean``.

Path-(b) direct check that the Seeley-DeWitt heat-kernel effective
Lagrangian is **diffeomorphism-invariant order-by-order** in the
asymptotic expansion at orders ``a_0, a_2, a_4``.

For a scalar density ``L`` built from polynomial scalar curvature
invariants, the variation under ``x^μ → x^μ + ξ^μ`` is a total
divergence, so the action ``∫ √g L`` is diff-invariant on closed
manifolds (Wald 1984 §E.1).  The "anomaly residual" at order ``n`` is
the algebraic mismatch between the same density expressed in two
equivalent scalar-invariant bases — for the Wave 1 Christensen-Duff
Dirac coefficient bundle this residual vanishes identically (Wave 2
main theorem ``a4_density_eq_a4_density_in_RC2GB_basis``).

Submodules:

- ``variational_check`` — order-by-order anomaly-residual evaluators
  + canonical / perturbed coefficient bundles
- ``anomaly_hunt`` — automated parameter-grid scan for diff-anomalies
  at ``a_4``; falsifier with deliberately broken bundle

Correctness-push: at SM-relevant fermion counts ``N_f ∈ [1, 27]`` and
realistic curvature inputs, the Wave 1 Christensen-Duff Dirac bundle
satisfies path-b diff invariance to machine precision.  A
deliberately perturbed bundle (single coefficient shifted by an
arbitrary ``δ``) is detected as non-invariant.
"""

from src.diff_invariance.variational_check import (
    EffectiveLagrangianBundle,
    dirac_coefficient_bundle,
    perturbed_coefficient_bundle,
    pathB_residual_at_order,
    diff_invariant_at_order,
    diff_invariant_order_by_order,
)
from src.diff_invariance.anomaly_hunt import (
    parameter_grid_scan_a4,
    anomaly_hunt_dirac_passes,
    anomaly_hunt_perturbed_fails,
    max_residual_over_grid,
)

__all__ = [
    "EffectiveLagrangianBundle",
    "dirac_coefficient_bundle",
    "perturbed_coefficient_bundle",
    "pathB_residual_at_order",
    "diff_invariant_at_order",
    "diff_invariant_order_by_order",
    "parameter_grid_scan_a4",
    "anomaly_hunt_dirac_passes",
    "anomaly_hunt_perturbed_fails",
    "max_residual_over_grid",
]
