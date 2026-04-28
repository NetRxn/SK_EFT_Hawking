"""Order-by-order path-b diff-invariance anomaly evaluators.

Mirrors the Lean ``EffectiveLagrangianCoefs`` bundle and
``pathB_residual_*`` family in
``lean/SKEFTHawking/NonlinearDiffInvariance.lean``.  Numerical checks
agree to machine precision for the Christensen-Duff Dirac bundle at
all canonical orders (0, 2, 4); perturbed bundles flag non-zero
residuals as expected.
"""

from __future__ import annotations
from dataclasses import dataclass


@dataclass(frozen=True)
class EffectiveLagrangianBundle:
    """5-coefficient bundle for the Seeley-DeWitt effective Lagrangian
    through order ``a_4``.

    Mirrors ``EffectiveLagrangianCoefs`` in Lean.

    Fields:
    - ``a0`` — constant scalar density piece
    - ``a2_R`` — coefficient of ``R``
    - ``a4_R_sq`` — coefficient of ``R²``
    - ``a4_Ricci_sq`` — coefficient of ``R_μν R^μν``
    - ``a4_Riemann_sq`` — coefficient of ``R_μνρσ R^μνρσ``
    """
    a0: float
    a2_R: float
    a4_R_sq: float
    a4_Ricci_sq: float
    a4_Riemann_sq: float

    def density_a4(self, R_sq: float, Ricci_sq: float,
                    Riemann_sq: float) -> float:
        """Order-``a_4`` density in the natural ``{R², R_μν², R_μνρσ²}``
        basis.

        Lean: EffectiveLagrangianCoefs.density_a4
        """
        return (self.a4_R_sq * float(R_sq)
                + self.a4_Ricci_sq * float(Ricci_sq)
                + self.a4_Riemann_sq * float(Riemann_sq))


def dirac_coefficient_bundle(N_f: float) -> EffectiveLagrangianBundle:
    """Canonical Christensen-Duff Dirac bundle for ``N_f`` species.

    Each coefficient is a *named call* into Wave 1's ``formulas.py``
    API — drift-protection per ``feedback_python_lean_refs_drift.md``.

    Lean: NonlinearDiffInvariance.diracCoefBundle
    """
    from src.core.formulas import (
        seeley_dewitt_a0,
        seeley_dewitt_a2_R_coefficient,
        higher_curvature_R_sq_coefficient,
        higher_curvature_Ricci_sq_coefficient,
        higher_curvature_Riemann_sq_coefficient,
    )
    return EffectiveLagrangianBundle(
        a0=float(seeley_dewitt_a0(N_f)),
        a2_R=float(seeley_dewitt_a2_R_coefficient(N_f)),
        a4_R_sq=float(higher_curvature_R_sq_coefficient(N_f)),
        a4_Ricci_sq=float(higher_curvature_Ricci_sq_coefficient(N_f)),
        a4_Riemann_sq=float(higher_curvature_Riemann_sq_coefficient(N_f)),
    )


def perturbed_coefficient_bundle(N_f: float,
                                   delta: float) -> EffectiveLagrangianBundle:
    """Non-admissible bundle: Dirac bundle with R²-channel shifted by
    ``delta``.  For nonzero ``delta`` this bundle violates the Wave 2
    basis-change identity at order ``a_4``.

    Lean: NonlinearDiffInvariance.perturbedCoefBundle
    """
    base = dirac_coefficient_bundle(N_f)
    return EffectiveLagrangianBundle(
        a0=base.a0,
        a2_R=base.a2_R,
        a4_R_sq=base.a4_R_sq + float(delta),
        a4_Ricci_sq=base.a4_Ricci_sq,
        a4_Riemann_sq=base.a4_Riemann_sq,
    )


def pathB_residual_at_order(order: int, bundle: EffectiveLagrangianBundle,
                              N_f: float, R: float, R_sq: float,
                              Ricci_sq: float, Riemann_sq: float) -> float:
    """Path-b anomaly residual at order ``n ∈ {0, 2, 4}``.

    - ``n = 0``: definitionally 0 (constant scalar)
    - ``n = 2``: definitionally 0 (single scalar invariant ``R``)
    - ``n = 4``: ``bundle.density_a4 - a4_density_in_RC2GB_basis(...)``
      where the Stelle representation uses ``(α(N_f), β(N_f), γ(N_f))``
      from Wave 2.

    For a Dirac bundle the n=4 residual vanishes by Wave 2's main
    theorem ``a4_density_eq_a4_density_in_RC2GB_basis``.  For a
    perturbed bundle the residual is generically nonzero (linear in
    ``delta`` at the R²-channel falsifier).

    Lean: NonlinearDiffInvariance.pathB_residual_a0/a2/a4
    """
    n = int(order)
    if n == 0:
        return 0.0
    if n == 2:
        # R argument is exercised but residual is definitionally 0
        _ = float(R) * float(bundle.a2_R)
        return 0.0
    if n == 4:
        from src.higher_curvature.curvature_basis import (
            a4_density_in_RC2GB_basis,
        )
        return float(bundle.density_a4(R_sq, Ricci_sq, Riemann_sq)
                     - a4_density_in_RC2GB_basis(N_f, R_sq, Ricci_sq,
                                                   Riemann_sq))
    from src.core.constants import DIFF_INVARIANCE_PARAMS
    raise ValueError(
        f"Order {n} is outside the canonical Wave 3 order list "
        f"{DIFF_INVARIANCE_PARAMS['ORDER_LIST']}."
    )


def diff_invariant_at_order(order: int, bundle: EffectiveLagrangianBundle,
                              N_f: float, R: float, R_sq: float,
                              Ricci_sq: float, Riemann_sq: float) -> bool:
    """Boolean: path-b residual at this order is below tolerance.

    Lean: NonlinearDiffInvariance.DiffInvariantAt
    """
    from src.core.constants import DIFF_INVARIANCE_PARAMS
    tol = float(DIFF_INVARIANCE_PARAMS['PATH_B_RESIDUAL_TOLERANCE'])
    residual = abs(pathB_residual_at_order(
        order, bundle, N_f, R, R_sq, Ricci_sq, Riemann_sq))
    return bool(residual < tol)


def diff_invariant_order_by_order(bundle: EffectiveLagrangianBundle,
                                    N_f: float, R: float, R_sq: float,
                                    Ricci_sq: float,
                                    Riemann_sq: float) -> bool:
    """Wave 3 correctness-push: order-by-order diff invariance at all
    canonical orders ``DIFF_INVARIANCE_PARAMS['ORDER_LIST'] = (0, 2, 4)``.

    Lean: NonlinearDiffInvariance.H_NonlinearDiffInvariance
    """
    from src.core.constants import DIFF_INVARIANCE_PARAMS
    return all(
        diff_invariant_at_order(n, bundle, N_f, R, R_sq, Ricci_sq, Riemann_sq)
        for n in DIFF_INVARIANCE_PARAMS['ORDER_LIST']
    )
