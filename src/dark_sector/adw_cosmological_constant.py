"""Phase 5x Wave 3: ADW-Derived Cosmological Constant.

Computational companion to ``lean/SKEFTHawking/CosmologicalConstant.lean``.

Implements:

- **Volovik de Sitter double-temperature relation** — T_dS = 2 × T_GH, where
  T_GH = H/(2π) is Gibbons-Hawking and T_dS = H/π is the Volovik
  de Sitter temperature governing local KMS processes.
- **Magnitude status** — independent magnitude uncomputed. Optional supplied
  scales permit input arithmetic only. CMB thermal energy, local de Sitter
  temperature and vacuum-density fourth root are distinct physical scales.
- **KV model scope** — separate the 2008 dynamical four-form equilibrium
  and perturbed-chemical-potential branches from the later stepwise plateau
  scenario considered by the original W1b assessment. No branch is selected
  implicitly, and no CPL fit or KV-versus-DESI likelihood is computed here.
- **Comparative context** — QCD alternatives require independent provenance;
  this report does not establish or rank their DESI compatibility.

Physics references
------------------
- Volovik, arXiv:2312.02292v16, Eq22/§VI — distinct vacuum/matter scales
- Volovik, arXiv:2011.06466v9 (2021), §XI/XII — tetrad equilibrium and 4+0 construction
- Klinkhamer–Volovik, PRD 78, 063528 (2008), arXiv:0806.2805v7, §V
- Stepwise relaxation scenario, arXiv:1102.3152v4, §5/6 and Fig1
- Van Waerbeke-Zhitnitsky 2025, arXiv:2506.14182 — QCD topological DE
- Planck 2018 + DESI DR2 — observed ρ_Λ ~ (2.3 meV)⁴, evolving-DE
  tension 2.8-4.2σ

Lean anchors
------------
- CosmologicalConstant.T_dS_double_TGH
- CosmologicalConstant.T_dS_pos / T_GH_pos / T_dS_gt_T_GH
- CosmologicalConstant.quartic_CW_critical_point
- CosmologicalConstant.lambda_magnitude_ratio
"""

from __future__ import annotations

import math
from dataclasses import dataclass, field
from enum import Enum

#: Legacy illustrative scale (meV), not an independently derived prediction.
#: Historical name/value retained for compatibility; never a default input.
T_ADW_PREDICTED_meV = 2.8

#: Legacy reference energy scale (meV), not T_CMB or local T_dS.
#: This value does not construct or validate an independent prediction.
T_OBSERVED_meV = 2.3

#: Legacy illustrative fourth-power ratio, not a model result or accuracy grade.
LAMBDA_RATIO_ADW_OBSERVED = (T_ADW_PREDICTED_meV / T_OBSERVED_meV) ** 4


def gibbons_hawking_temperature(H: float) -> float:
    """Gibbons-Hawking temperature arithmetic, T_GH = H/(2*pi).

    Natural units hbar=c=k_B=1 with consistent H units. No conversion of a
    measured Hubble rate to Kelvin or a density fourth root is performed.
    Lean: ``CosmologicalConstant.gibbons_hawking_temperature``.
    """
    return H / (2.0 * math.pi)


def de_sitter_temperature_volovik(H: float) -> float:
    """Local de Sitter temperature arithmetic, T_dS = H/pi.

    Natural units hbar=c=k_B=1; arXiv:2312.02292v16 §III. This differs
    from horizon temperature, CMB thermal energy and rho_vac**(1/4).
    Restoring physical units requires explicit unit factors.
    Lean: ``CosmologicalConstant.de_sitter_temperature_volovik``.
    """
    return H / math.pi


def volovik_gh_ratio() -> float:
    """Exact ratio T_dS / T_GH = 2.

    Lean: ``CosmologicalConstant.T_dS_double_TGH``.
    """
    return 2.0


def lambda_magnitude_ratio(T_predicted_meV: float, T_observed_meV: float) -> float:
    """Fourth-power ratio of supplied positive energy scales in matching units.

    Historical argument names do not identify the scales as temperatures.
    This algebra establishes neither input provenance nor an ADW prediction.
    Lean: ``CosmologicalConstant.lambda_magnitude_ratio``.
    """
    if T_predicted_meV <= 0 or T_observed_meV <= 0:
        raise ValueError(
            "Both T_predicted_meV and T_observed_meV must be positive"
        )
    return (T_predicted_meV / T_observed_meV) ** 4


def lambda_energy_density_meV4(T_meV: float) -> float:
    """Fourth power of a supplied energy scale, in (meV)^4.

    The historical argument name does not identify this scale as a temperature.
    Multiply the result by 1e-12 for (eV)^4: (1 meV)^4 = 1e-12 (eV)^4.
    This metric prefix is not an SI J/m^3 conversion; a physical density
    conversion requires explicit hbar/c unit conventions.
    """
    if T_meV <= 0:
        raise ValueError("T_meV must be positive")
    return T_meV**4


class KlinkhamerVolovikBranch(str, Enum):
    """Model/regime selectors, not fitted cosmological models or CPL pairs."""

    UNSELECTED = "unselected"
    DYNAMIC_2008_EQUILIBRIUM = "dynamic_2008_equilibrium_mu0"
    DYNAMIC_2008_PERTURBED = "dynamic_2008_perturbed_chemical_potential"
    STEPWISE_2011_PLATEAU = "stepwise_2011_plateau"


@dataclass(frozen=True)
class KlinkhamerVolovikPrediction:
    """Branch-scoped source report; the historical public name is retained.

    For arXiv:0806.2805v7 §V A/C/E, bare-F w=-1 differs from the
    equilibrium coupled F+G asymptotic homogeneous w=0; clustering is open.
    A perturbed chemical potential can give late de Sitter expansion.
    The stepwise scenario (arXiv:1102.3152v4 §5/6, pp5–9 and Fig1)
    describes locally approximately vacuum-like plateaux (w approximately -1),
    with schematic transitions and a conditional neutrino-remnant proposal.
    It is distinct from the 2008 equilibrium CDM asymptotics; an ideal exact
    constant plateau would be an additional assumption, not a fitted result.

    No CPL parameters, calibrated SI period or model likelihood are computed.
    Legacy numerical attributes remain readable as None and cannot be supplied
    through this constructor. A supplied number must not impersonate a fit.
    """

    branch: KlinkhamerVolovikBranch = KlinkhamerVolovikBranch.UNSELECTED
    source_arxiv: str | None = field(default=None, init=False)
    bare_field_w: float | None = field(default=None, init=False)
    w_effective_time_averaged: float | None = field(default=None, init=False)
    w0: float | None = field(default=None, init=False)
    wa: float | None = field(default=None, init=False)
    oscillation_period_seconds: float | None = field(default=None, init=False)
    desi_dr2_exclusion_sigma_pantheon_plus: float | None = field(default=None, init=False)
    desi_dr2_exclusion_sigma_desy5: float | None = field(default=None, init=False)
    desi_fit_status: str = field(default="not_computed", init=False)
    clustering_status: str = field(default="not_established", init=False)

    def __post_init__(self) -> None:
        # Validate direct construction as well as factory calls.
        branch = KlinkhamerVolovikBranch(self.branch)
        object.__setattr__(self, "branch", branch)
        if branch in (
            KlinkhamerVolovikBranch.DYNAMIC_2008_EQUILIBRIUM,
            KlinkhamerVolovikBranch.DYNAMIC_2008_PERTURBED,
        ):
            object.__setattr__(self, "source_arxiv", "0806.2805v7")
            object.__setattr__(self, "bare_field_w", -1.0)
        elif branch is KlinkhamerVolovikBranch.STEPWISE_2011_PLATEAU:
            object.__setattr__(self, "source_arxiv", "1102.3152v4")
        if branch is KlinkhamerVolovikBranch.DYNAMIC_2008_EQUILIBRIUM:
            object.__setattr__(self, "w_effective_time_averaged", 0.0)


def klinkhamer_volovik_prediction(
    *, branch: KlinkhamerVolovikBranch = KlinkhamerVolovikBranch.UNSELECTED,
) -> KlinkhamerVolovikPrediction:
    """Report a chosen source model/regime with an uncomputed DESI fit.

    No-argument calls retain the public API but select no physical branch.
    Bare-field, effective homogeneous, and plateau equations of state are not
    interchangeable with a finite-redshift dark-energy CPL fit.
    """
    return KlinkhamerVolovikPrediction(branch=branch)


def adw_predicted_vs_observed_energy_ratio(
    *, candidate_scale_meV: float | None = None,
    reference_scale_meV: float | None = None,
) -> float | None:
    """Compare explicit inputs; no independent ADW magnitude is computed.

    The historical name/no-argument call remain, but omitted inputs return
    None. Supplied values give arithmetic only, not predictive accuracy.
    """
    if candidate_scale_meV is None and reference_scale_meV is None:
        return None
    if candidate_scale_meV is None or reference_scale_meV is None:
        raise ValueError("Supply both candidate and reference energy scales")
    if not math.isfinite(candidate_scale_meV) or not math.isfinite(reference_scale_meV):
        raise ValueError("Supplied energy scales must be finite")
    return lambda_magnitude_ratio(candidate_scale_meV, reference_scale_meV)


def quartic_CW_critical_point(A: float, B: float) -> tuple[float, float]:
    """Critical point of the quartic Coleman-Weinberg potential.

    For `V_CW(C) = -A·C² + B·C⁴` with A, B > 0, returns the pair
    (C₀, V_eff(C₀)) where C₀² = A/(2B) and V_eff(C₀) = -A²/(4B).

    Algebraic backbone of the ADW effective-potential minimum;
    the specific ADW identity `V_eff(C₀) = -Λ⁴/(4e)` at
    `C₀ = Λ·e^(-1/4)` requires fitting the full one-loop
    logarithmic potential to this quartic form, which is deferred.

    Lean: ``CosmologicalConstant.quartic_CW_critical_point``.
    """
    if A <= 0 or B <= 0:
        raise ValueError("A and B must both be positive")
    C0 = math.sqrt(A / (2.0 * B))
    V0 = -(A**2) / (4.0 * B)
    return C0, V0


@dataclass(frozen=True)
class CosmologicalConstantAssessment:
    """Unknown prediction, optional supplied-input arithmetic and preserved KV scope.

    Legacy ratio/accuracy fields are readonly and None by default. Accuracy
    means supplied-scale deviation, never model accuracy. Supplied inputs do
    not create an independent adw_prediction_meV or a KV fit.

    Explicit inputs must be an exact two-element tuple of builtin int/float
    values (excluding bool), both finite and positive. Accepted values are
    stored as an immutable float tuple before arithmetic. Mutable containers,
    other shapes/types and explicit None elements are rejected with ValueError;
    only the omitted None sentinel means no supplied comparison.
    """

    kv_prediction: KlinkhamerVolovikPrediction
    surviving_hook_notes: tuple[str, ...]
    magnitude_inputs_meV: tuple[float, float] | None = None
    lambda_ratio_adw_observed: float | None = field(default=None, init=False)
    lambda_accuracy_percent: float | None = field(default=None, init=False)
    magnitude_status: str = field(default="not_computed", init=False)
    adw_prediction_meV: float | None = field(default=None, init=False)
    kv_explains_desi: bool | None = field(default=None, init=False)
    kv_desi_fit_status: str = field(default="not_computed", init=False)

    def __post_init__(self) -> None:
        if self.magnitude_inputs_meV is None:
            return
        inputs = self.magnitude_inputs_meV
        if type(inputs) is not tuple or len(inputs) != 2:
            raise ValueError("Magnitude inputs must be a two-element tuple")
        if any(type(value) not in (int, float) for value in inputs):
            raise ValueError("Magnitude input elements must be builtin int or float")
        try:
            candidate, reference = (float(value) for value in inputs)
        except (OverflowError, ValueError) as exc:
            raise ValueError("Magnitude input elements must be finite and positive") from exc
        if not all(math.isfinite(value) and value > 0.0 for value in (candidate, reference)):
            raise ValueError("Magnitude input elements must be finite and positive")
        object.__setattr__(self, "magnitude_inputs_meV", (candidate, reference))
        ratio = adw_predicted_vs_observed_energy_ratio(
            candidate_scale_meV=candidate, reference_scale_meV=reference,
        )
        object.__setattr__(self, "lambda_ratio_adw_observed", ratio)
        object.__setattr__(self, "lambda_accuracy_percent",
                           abs(candidate - reference) / reference * 100.0)
        object.__setattr__(self, "magnitude_status", "supplied_input_comparison")


def assess_cosmological_constant_status(
    *, branch: KlinkhamerVolovikBranch = KlinkhamerVolovikBranch.UNSELECTED,
    magnitude_inputs_meV: tuple[float, float] | None = None,
) -> CosmologicalConstantAssessment:
    """Report unknown magnitude, optional supplied inputs and selected KV scope.

    Inputs are (candidate energy scale, reference energy scale), both meV.
    No physical scale map, magnitude model, CPL fit or likelihood is computed.
    """
    kv = klinkhamer_volovik_prediction(branch=branch)
    if kv.branch is KlinkhamerVolovikBranch.DYNAMIC_2008_EQUILIBRIUM:
        branch_note = (
            "At mu=mu0 near equilibrium and asymptotically late times, the "
            "coupled F+G homogeneous expansion is CDM-like (effective w=0); "
            "bare-field w=-1 is distinct and clustering is not established."
        )
    elif kv.branch is KlinkhamerVolovikBranch.DYNAMIC_2008_PERTURBED:
        branch_note = (
            "A perturbation of the equilibrium chemical potential can yield "
            "late de Sitter expansion, not a computed finite-redshift CPL fit."
        )
    elif kv.branch is KlinkhamerVolovikBranch.STEPWISE_2011_PLATEAU:
        branch_note = (
            "The 2011 stepwise scenario describes locally approximately vacuum-like "
            "plateaux (w approximately -1), schematic transitions and conditional "
            "remnants. It is not the 2008 equilibrium CDM branch or an exact "
            "constant-plateau CPL prediction; no fit or likelihood is computed."
        )
    else:
        branch_note = "No KV model/regime has been selected."
    return CosmologicalConstantAssessment(
        kv_prediction=kv,
        magnitude_inputs_meV=magnitude_inputs_meV,
        surviving_hook_notes=(
            "No independent ADW magnitude is computed. Optional supplied scales "
            "give input arithmetic only, not predictive accuracy.",
            branch_note,
            "The 2008 dynamical source discusses microscopic oscillations; "
            "no calibrated period in seconds is supplied here.",
            "KV forward model, CPL fit and DESI likelihood are not computed; "
            "no KV exclusion significance is established.",
            "ADW magnitude and QCD topological dark-energy claims require "
            "independent provenance and numerical validation.",
        ),
    )
