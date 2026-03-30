#!/usr/bin/env python3
"""
SK-EFT Hawking — Figure Review Pipeline
========================================

Generates publication figures, runs automated structural checks,
and produces a review manifest for LLM visual review.

Usage
-----
    # Generate PNGs + manifest (default):
    python scripts/review_figures.py

    # Generate only, skip structural checks:
    python scripts/review_figures.py --generate

    # Run structural checks on existing PNGs:
    python scripts/review_figures.py --check

    # Produce manifest only (for LLM agent):
    python scripts/review_figures.py --manifest

Exit Codes
----------
    0 — all structural checks passed (or --generate/--manifest only)
    1 — one or more structural checks failed
"""

from __future__ import annotations

import argparse
import json
import os
import sys
import traceback
from dataclasses import dataclass, field, asdict
from datetime import datetime, timezone
from pathlib import Path
from typing import Any

# Path setup
SCRIPT_DIR = Path(__file__).resolve().parent
PROJECT_ROOT = SCRIPT_DIR.parent
sys.path.insert(0, str(PROJECT_ROOT))

FIGURES_DIR = PROJECT_ROOT / "figures"

# ═══════════════════════════════════════════════════════════════════════
# Figure registry — what each figure should contain
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class FigureSpec:
    """Expected properties for a single figure."""
    name: str
    function: str       # Function name in visualizations.py
    caption: str
    needs_experiments: bool  # Does the function require experiments dict?
    expected_traces: int     # Minimum number of Plotly traces
    expected_axes: dict      # {"xaxis": "label substring", "yaxis": "..."}
    physics_checks: list     # List of physics assertions to verify
    color_keys: list         # COLORS keys that should appear


FIGURE_REGISTRY: list[FigureSpec] = [
    FigureSpec(
        name="fig1_transonic_profiles",
        function="fig_transonic_profiles",
        caption="Transonic BEC background profiles for three experimental setups.",
        needs_experiments=True,
        expected_traces=9,   # 3 experiments × 3 panels (v, c_s, mach, density minus shared)
        expected_axes={"xaxis3": "ξ", "yaxis": "Velocity"},
        physics_checks=["all_densities_positive", "mach_crosses_one"],
        color_keys=["Rb87", "K39", "Na23"],
    ),
    FigureSpec(
        name="fig2_correction_hierarchy",
        function="fig_correction_hierarchy",
        caption="Correction hierarchy: δ_disp, δ_diss, δ_cross on log scale.",
        needs_experiments=True,
        expected_traces=3,   # 3 bar groups
        expected_axes={"yaxis": "Correction"},
        physics_checks=["all_corrections_positive", "diss_smaller_than_disp_for_Rb87"],
        color_keys=["dispersive", "dissipative", "cross"],
    ),
    FigureSpec(
        name="fig3_parameter_space",
        function="fig_parameter_space",
        caption="2D parameter space: D vs γ/κ with experimental points.",
        needs_experiments=False,
        expected_traces=4,   # contour + 3 experiment markers
        expected_axes={"xaxis": "Adiabaticity", "yaxis": "Dissipation"},
        physics_checks=["eft_boundary_at_D_equals_1"],
        color_keys=["Rb87", "K39", "Na23"],
    ),
    FigureSpec(
        name="fig4_spin_sonic_enhancement",
        function="fig_spin_sonic_enhancement",
        caption="Spin-sonic enhancement: δ_diss × (c_dens/c_spin)².",
        needs_experiments=False,
        expected_traces=1,   # main curve (+ markers added separately)
        expected_axes={"xaxis": "ratio", "yaxis": "δ"},
        physics_checks=["enhancement_monotonic"],
        color_keys=["dissipative"],
    ),
    FigureSpec(
        name="fig5_temperature_decomposition",
        function="fig_temperature_decomposition",
        caption="Temperature decomposition: T_eff = T_H(1 + δ_disp + δ_diss + δ_cross).",
        needs_experiments=True,
        expected_traces=3,   # one bar per experiment
        expected_axes={"yaxis": "Temperature"},
        physics_checks=["T_H_dominates"],
        color_keys=["horizon", "dispersive", "dissipative", "cross"],
    ),
    FigureSpec(
        name="fig6_kappa_scaling",
        function="fig_kappa_scaling",
        caption="Scaling: δ_disp ~ κ² vs δ_diss ~ 1/κ with crossing point.",
        needs_experiments=False,
        expected_traces=2,   # two curves (+ crossing marker)
        expected_axes={"xaxis": "κ", "yaxis": "Correction"},
        physics_checks=["curves_cross"],
        color_keys=["dispersive", "dissipative"],
    ),
    # Phase 2 figures
    FigureSpec(
        name="fig7_cgl_fdr_pattern",
        function="fig_cgl_fdr_pattern",
        caption="CGL FDR monomial counting at each EFT order N.",
        needs_experiments=False,
        expected_traces=4,   # 3 bar groups + formula line
        expected_axes={"xaxis": "Order", "yaxis": "terms"},
        physics_checks=["noise_count_even_orders_only"],
        color_keys=["dissipative", "dispersive"],
    ),
    FigureSpec(
        name="fig8_even_vs_odd_kernel",
        function="fig_even_vs_odd_kernel",
        caption="K_R decomposition: even-ω (conservative) vs odd-ω (dissipative).",
        needs_experiments=False,
        expected_traces=4,   # 4 subplot traces
        expected_axes={"xaxis": "ω"},
        physics_checks=["even_part_symmetric", "noise_from_odd_only"],
        color_keys=["dispersive", "dissipative"],
    ),
    FigureSpec(
        name="fig9_boundary_term_suppression",
        function="fig_boundary_term_suppression",
        caption="IBP boundary correction is O(D) for all experiments.",
        needs_experiments=False,
        expected_traces=1,   # main curve (+ experiment markers)
        expected_axes={"xaxis": "Adiabaticity", "yaxis": "correction"},
        physics_checks=["all_experiments_below_2_percent"],
        color_keys=["dissipative", "Rb87", "K39", "Na23"],
    ),
    FigureSpec(
        name="fig10_positivity_constraint",
        function="fig_positivity_constraint",
        caption="SK positivity constraint: strict γ_{2,1}+γ_{2,2}=0 and relaxed bound.",
        needs_experiments=False,
        expected_traces=2,   # constraint line + contour
        expected_axes={"xaxis": "γ", "yaxis": "γ"},
        physics_checks=["strict_line_passes_through_origin"],
        color_keys=["horizon"],
    ),
    FigureSpec(
        name="fig11_on_shell_vanishing",
        function="fig_on_shell_vanishing",
        caption="δ^(2) vanishes at k = ω/c_s (acoustic shell), nonzero off-shell.",
        needs_experiments=False,
        expected_traces=1,   # main curve
        expected_axes={"xaxis": "k", "yaxis": "δ"},
        physics_checks=["zero_crossing_at_k_equals_omega_over_cs"],
        color_keys=["dissipative"],
    ),
    FigureSpec(
        name="fig12_einstein_relation",
        function="fig_einstein_relation",
        caption="Einstein relation σ = γT: simplest FDR from CGL.",
        needs_experiments=False,
        expected_traces=3,   # 3 gamma values
        expected_axes={"xaxis": "Temperature", "yaxis": "Noise"},
        physics_checks=["linear_in_T", "proportional_to_gamma"],
        color_keys=["dissipative"],
    ),
    # ─── Phase 3 Wave 1: Third-order + Gauge Erasure ─────────────────
    FigureSpec(
        name="fig13_parity_alternation",
        function="fig_parity_alternation",
        caption="Parity alternation: universal (odd N) vs flow-only (even N) monomials.",
        needs_experiments=False,
        expected_traces=1,
        expected_axes={"xaxis": "m", "yaxis": "N"},
        physics_checks=[],
        color_keys=["dispersive", "dissipative"],
    ),
    FigureSpec(
        name="fig14_parity_alternation_stakeholder",
        function="fig_parity_alternation_stakeholder",
        caption="Parity alternation bar chart: count per order, colored by type.",
        needs_experiments=False,
        expected_traces=2,
        expected_axes={"xaxis": "Order", "yaxis": "coefficient"},
        physics_checks=[],
        color_keys=["dispersive", "dissipative"],
    ),
    FigureSpec(
        name="fig15_damping_rate_third_order",
        function="fig_damping_rate_third_order",
        caption="Damping rate convergence: orders 1, 2, 3 for Steinhauer.",
        needs_experiments=True,
        expected_traces=3,
        expected_axes={"xaxis": "k", "yaxis": "Gamma"},
        physics_checks=[],
        color_keys=["dispersive", "dissipative", "cross"],
    ),
    FigureSpec(
        name="fig16_spectral_correction_comparison",
        function="fig_spectral_correction_comparison",
        caption="Spectral parity: delta^(2) odd in omega vs delta^(3) even in omega.",
        needs_experiments=True,
        expected_traces=2,
        expected_axes={"xaxis": "omega"},
        physics_checks=[],
        color_keys=["dispersive", "dissipative"],
    ),
    FigureSpec(
        name="fig17_kappa_crossing",
        function="fig_kappa_crossing_phase3",
        caption="kappa-crossing: dispersive vs dissipative correction crossing point.",
        needs_experiments=True,
        expected_traces=6,
        expected_axes={"xaxis": "κ", "yaxis": "Correction"},
        physics_checks=[],
        color_keys=["Steinhauer", "Heidelberg", "Trento"],
    ),
    FigureSpec(
        name="fig18_spin_sonic_phase3",
        function="fig_spin_sonic_enhancement_phase3",
        caption="Spin-sonic enhancement with sensitivity thresholds.",
        needs_experiments=True,
        expected_traces=3,
        expected_axes={"xaxis": "ratio", "yaxis": "δ"},
        physics_checks=[],
        color_keys=["dissipative"],
    ),
    FigureSpec(
        name="fig19_bogoliubov_connection",
        function="fig_bogoliubov_connection",
        caption="Bogoliubov connection: acoustic vs full dispersion and k^4 deviation.",
        needs_experiments=True,
        expected_traces=3,
        expected_axes={"xaxis": "k"},
        physics_checks=[],
        color_keys=["dispersive", "horizon"],
    ),
    FigureSpec(
        name="fig20_sm_scorecard",
        function="fig_sm_scorecard",
        caption="Standard Model gauge erasure scorecard: SU(3)/SU(2)/U(1).",
        needs_experiments=False,
        expected_traces=1,
        expected_axes={"yaxis": "Group"},
        physics_checks=[],
        color_keys=["Steinhauer", "Trento"],
    ),
    FigureSpec(
        name="fig21_erasure_survey",
        function="fig_erasure_survey",
        caption="Erasure survey across gauge groups: SU(N), SO(N), U(1).",
        needs_experiments=False,
        expected_traces=1,
        expected_axes={},
        physics_checks=[],
        color_keys=[],
    ),
    # ─── Phase 3 Wave 2: WKB Connection ──────────────────────────────
    FigureSpec(
        name="fig22_complex_turning_point",
        function="fig_complex_turning_point",
        caption="Complex turning point shift vs frequency for three BEC platforms.",
        needs_experiments=False,
        expected_traces=3,
        expected_axes={"xaxis": "ω", "yaxis": "δx"},
        physics_checks=[],
        color_keys=["Steinhauer", "Heidelberg", "Trento"],
    ),
    FigureSpec(
        name="fig23_effective_surface_gravity",
        function="fig_effective_surface_gravity",
        caption="Effective surface gravity decomposition: dispersive + dissipative.",
        needs_experiments=False,
        expected_traces=6,
        expected_axes={"xaxis": "ω"},
        physics_checks=[],
        color_keys=["dispersive", "dissipative"],
    ),
    FigureSpec(
        name="fig24_decoherence_and_noise",
        function="fig_decoherence_and_noise",
        caption="Decoherence parameter and FDR noise floor vs frequency.",
        needs_experiments=False,
        expected_traces=6,
        expected_axes={"xaxis": "ω"},
        physics_checks=[],
        color_keys=["Steinhauer", "Heidelberg", "Trento"],
    ),
    FigureSpec(
        name="fig25_hawking_spectrum_exact",
        function="fig_hawking_spectrum_exact",
        caption="Full Hawking spectrum with exact WKB corrections (3 platforms).",
        needs_experiments=False,
        expected_traces=9,
        expected_axes={"xaxis": "ω"},
        physics_checks=[],
        color_keys=["dissipative", "noise"],
    ),
    FigureSpec(
        name="fig26_hawking_spectrum_stakeholder",
        function="fig_hawking_spectrum_exact_stakeholder",
        caption="Hawking spectrum overlay: all platforms on one plot.",
        needs_experiments=False,
        expected_traces=6,
        expected_axes={"xaxis": "ω"},
        physics_checks=[],
        color_keys=["Steinhauer", "Heidelberg", "Trento"],
    ),
    FigureSpec(
        name="fig27_exact_vs_perturbative",
        function="fig_exact_vs_perturbative",
        caption="Fractional difference between exact WKB and perturbative EFT.",
        needs_experiments=False,
        expected_traces=3,
        expected_axes={"xaxis": "ω", "yaxis": "difference"},
        physics_checks=[],
        color_keys=["Steinhauer", "Heidelberg", "Trento"],
    ),
    # ─── Phase 3 Wave 3: ADW Gap Equation ───
    FigureSpec(
        name="fig28_adw_effective_potential",
        function="fig_adw_effective_potential",
        caption="Coleman-Weinberg effective potential for tetrad condensation at three coupling ratios.",
        needs_experiments=False,
        expected_traces=3,
        expected_axes={"xaxis": "C", "yaxis": "V"},
        physics_checks=[],
        color_keys=[],
    ),
    FigureSpec(
        name="fig29_adw_phase_diagram",
        function="fig_adw_phase_diagram",
        caption="Phase diagram: tetrad VEV vs coupling ratio G/G_c.",
        needs_experiments=False,
        expected_traces=1,
        expected_axes={"xaxis": "G", "yaxis": "C"},
        physics_checks=[],
        color_keys=[],
    ),
    FigureSpec(
        name="fig30_adw_ng_modes",
        function="fig_adw_ng_mode_decomposition",
        caption="Vergeles mode counting: tetrad DOF decomposition in 4D.",
        needs_experiments=False,
        expected_traces=1,
        expected_axes={"xaxis": "Mode"},
        physics_checks=[],
        color_keys=[],
    ),
    FigureSpec(
        name="fig31_adw_he3_analogy",
        function="fig_adw_he3_analogy",
        caption="Structural analogy between ADW tetrad and superfluid He-3 order parameter.",
        needs_experiments=False,
        expected_traces=10,
        expected_axes={},
        physics_checks=[],
        color_keys=[],
    ),
    FigureSpec(
        name="fig32_adw_obstacles",
        function="fig_adw_structural_obstacles",
        caption="Four structural obstacles for emergent fermion bootstrap with severity.",
        needs_experiments=False,
        expected_traces=1,
        expected_axes={"xaxis": "Severity"},
        physics_checks=[],
        color_keys=[],
    ),
    FigureSpec(
        name="fig33_adw_coupling_scan",
        function="fig_adw_coupling_scan",
        caption="Coupling scan: V_eff depth and tetrad VEV for N_f = 2, 4, 8.",
        needs_experiments=False,
        expected_traces=6,
        expected_axes={"xaxis": "G"},
        physics_checks=[],
        color_keys=["Steinhauer", "Heidelberg", "Trento"],
    ),
    FigureSpec(
        name="fig34_adw_coupling_scan_stakeholder",
        function="fig_adw_coupling_scan_stakeholder",
        caption="Coupling scan for wider audience: simplified labels.",
        needs_experiments=False,
        expected_traces=6,
        expected_axes={"xaxis": "G"},
        physics_checks=[],
        color_keys=["Steinhauer", "Heidelberg", "Trento"],
    ),
    # Phase 4 Wave 1: Experimental Predictions
    FigureSpec(
        name="fig35_prediction_table_comparison",
        function="fig_prediction_table_comparison",
        caption="Spectral deviation from Planckian for all three BEC platforms.",
        needs_experiments=False,
        expected_traces=3,
        expected_axes={"xaxis": "\u03c9"},
        physics_checks=[],
        color_keys=["Steinhauer", "Heidelberg", "Trento"],
    ),
    FigureSpec(
        name="fig36_detector_requirements",
        function="fig_detector_requirements",
        caption="Detector requirements: shots needed for three measurement goals.",
        needs_experiments=False,
        expected_traces=3,
        expected_axes={"xaxis": "goal"},
        physics_checks=[],
        color_keys=["Steinhauer", "Heidelberg", "Trento"],
    ),
    FigureSpec(
        name="fig37_kappa_scaling",
        function="fig_kappa_scaling_phase4",
        caption="Kappa-scaling test: dispersive (D^2) vs dissipative corrections.",
        needs_experiments=False,
        expected_traces=3,
        expected_axes={"xaxis": "D"},
        physics_checks=[],
        color_keys=["dispersive", "dissipative"],
    ),
    FigureSpec(
        name="fig38_noise_floor_crossover",
        function="fig_noise_floor_crossover",
        caption="Noise floor crossover: where FDR noise exceeds Hawking signal.",
        needs_experiments=False,
        expected_traces=6,
        expected_axes={"xaxis": "\u03c9"},
        physics_checks=[],
        color_keys=["Steinhauer", "Heidelberg", "Trento"],
    ),
    # Phase 5 Wave 1A: Physical kappa-scaling
    FigureSpec(
        name="fig46_kappa_scaling_physical",
        function="fig_kappa_scaling_physical",
        caption="Physical kappa-scaling: EFT corrections vs surface gravity for all platforms.",
        needs_experiments=False,
        expected_traces=6,
        expected_axes={"xaxis": "κ"},
        physics_checks=[],
        color_keys=["Steinhauer", "Heidelberg", "Trento"],
    ),
    # Phase 4 Wave 1B: Chirality wall
    FigureSpec(
        name="fig39_chirality_wall_status",
        function="fig_chirality_wall_status",
        caption="Chirality wall: GS conditions vs TPF evasion.",
        needs_experiments=False,
        expected_traces=1,
        expected_axes={},
        physics_checks=[],
        color_keys=["Steinhauer", "Trento"],
    ),
    # Phase 4 Wave 1C: GL phase diagram
    FigureSpec(
        name="fig40_gl_phase_diagram",
        function="fig_gl_phase_diagram",
        caption="Ginzburg-Landau phase diagram: B-phase, A-phase, polar phases.",
        needs_experiments=False,
        expected_traces=4,
        expected_axes={"xaxis": "G"},
        physics_checks=[],
        color_keys=["Steinhauer", "Heidelberg", "Trento"],
    ),
    FigureSpec(
        name="fig41_he3_comparison_table",
        function="fig_he3_comparison_table",
        caption="He-3 vs ADW structural comparison table.",
        needs_experiments=False,
        expected_traces=1,
        expected_axes={},
        physics_checks=[],
        color_keys=[],
    ),
    # Phase 4 Wave 2
    FigureSpec(
        name="fig45_vestigial_effective_potential",
        function="fig_vestigial_effective_potential",
        caption="Paper 6 native V_eff at three coupling ratios.",
        needs_experiments=False,
        expected_traces=3,
        expected_axes={"xaxis": "C"},
        physics_checks=[],
        color_keys=[],
    ),
    FigureSpec(
        name="fig42_vestigial_phase_diagram",
        function="fig_vestigial_phase_diagram",
        caption="Vestigial gravity mean-field phase diagram.",
        needs_experiments=False,
        expected_traces=3,
        expected_axes={"xaxis": "G"},
        physics_checks=[],
        color_keys=["Steinhauer", "Trento"],
    ),
    FigureSpec(
        name="fig43_backreaction_cooling",
        function="fig_backreaction_cooling",
        caption="Acoustic BH cooling toward extremality.",
        needs_experiments=False,
        expected_traces=3,
        expected_axes={"xaxis": "\u03c4"},
        physics_checks=[],
        color_keys=["Steinhauer", "Heidelberg", "Trento"],
    ),
    FigureSpec(
        name="fig44_information_retention",
        function="fig_information_retention",
        caption="Fracton vs standard hydro information retention.",
        needs_experiments=False,
        expected_traces=3,
        expected_axes={"xaxis": "dimension"},
        physics_checks=[],
        color_keys=["Steinhauer", "Trento"],
    ),
    # Phase 5 Wave 2A: Grassmann TRG
    FigureSpec(
        name="fig48_grassmann_trg_2d_phase",
        function="fig_grassmann_trg_2d_phase",
        caption="2D ADW phase diagram from Grassmann TRG: free energy and specific heat vs coupling.",
        needs_experiments=False,
        expected_traces=2,
        expected_axes={"xaxis": "g"},
        physics_checks=[],
        color_keys=["Steinhauer", "Trento"],
    ),
    # Phase 5 Wave 2B: 4D fermion-bag MC
    FigureSpec(
        name="fig49_fermion_bag_4d_binder",
        function="fig_fermion_bag_4d_binder",
        caption="4D Binder cumulants (tetrad vs metric) from fermion-bag MC.",
        needs_experiments=False,
        expected_traces=2,
        expected_axes={"xaxis": "g"},
        physics_checks=[],
        color_keys=["Steinhauer", "Trento"],
    ),
    FigureSpec(
        name="fig50_fermion_bag_4d_phase_diagram",
        function="fig_fermion_bag_4d_phase_diagram",
        caption="4D ADW phase diagnostics: metric correlator and acceptance rate.",
        needs_experiments=False,
        expected_traces=2,
        expected_axes={"xaxis": "g"},
        physics_checks=[],
        color_keys=["Steinhauer", "Trento"],
    ),
    # Phase 5 Wave 5D — comprehensive figure suite
    FigureSpec(
        name="fig51_vestigial_binder_crossing",
        function="fig_vestigial_binder_crossing",
        caption="Vestigial MC Binder cumulants at L=4,6,8.",
        needs_experiments=False, expected_traces=6,
        expected_axes={"xaxis": "g"}, physics_checks=[], color_keys=["Steinhauer", "Heidelberg", "Trento"],
    ),
    FigureSpec(
        name="fig52_vestigial_susceptibility_split",
        function="fig_vestigial_susceptibility_split",
        caption="Split transition: susceptibility peaks at different couplings.",
        needs_experiments=False, expected_traces=2,
        expected_axes={}, physics_checks=[], color_keys=["Steinhauer", "Heidelberg"],
    ),
    FigureSpec(
        name="fig53_gs_condition_formalization",
        function="fig_gs_condition_formalization",
        caption="GS no-go conditions: formalization status and TPF violation.",
        needs_experiments=False, expected_traces=1,
        expected_axes={}, physics_checks=[], color_keys=[],
    ),
    FigureSpec(
        name="fig54_lean_theorem_summary",
        function="fig_lean_theorem_summary",
        caption="Phase 5 Lean verification: manual vs Aristotle proofs per module.",
        needs_experiments=False, expected_traces=2,
        expected_axes={}, physics_checks=[], color_keys=["Steinhauer", "Trento"],
    ),
    FigureSpec(
        name="fig55_category_hierarchy",
        function="fig_category_hierarchy",
        caption="Categorical infrastructure: Mathlib existing vs new.",
        needs_experiments=False, expected_traces=3,
        expected_axes={}, physics_checks=[], color_keys=["Steinhauer", "Heidelberg", "Trento"],
    ),
    FigureSpec(
        name="fig56_fusion_rules_comparison",
        function="fig_fusion_rules_comparison",
        caption="Fusion rules: total multiplicity for Vec_Z2, Rep_S3, Fibonacci.",
        needs_experiments=False, expected_traces=3,
        expected_axes={}, physics_checks=[], color_keys=[],
    ),
    FigureSpec(
        name="fig57_fibonacci_f_matrix",
        function="fig_fibonacci_f_matrix",
        caption="Fibonacci F-matrix with golden ratio entries.",
        needs_experiments=False, expected_traces=1,
        expected_axes={}, physics_checks=[], color_keys=[],
    ),
    FigureSpec(
        name="fig58_drinfeld_anyon_spectrum",
        function="fig_drinfeld_anyon_spectrum",
        caption="Drinfeld double anyon spectrum and algebra dimension.",
        needs_experiments=False, expected_traces=2,
        expected_axes={}, physics_checks=[], color_keys=["Steinhauer", "Heidelberg", "Trento"],
    ),
    FigureSpec(
        name="fig59_layer123_bridge",
        function="fig_layer123_bridge",
        caption="Three-layer architecture with formal verification at each level.",
        needs_experiments=False, expected_traces=3,
        expected_axes={}, physics_checks=[], color_keys=["Steinhauer", "Heidelberg", "Trento"],
    ),
    FigureSpec(
        name="fig60_tpf_evasion_architecture",
        function="fig_tpf_evasion_architecture",
        caption="TPF evasion: 5 GS conditions violated.",
        needs_experiments=False, expected_traces=1,
        expected_axes={}, physics_checks=[], color_keys=[],
    ),
    FigureSpec(
        name="fig61_fock_exterior_algebra",
        function="fig_fock_exterior_algebra",
        caption="Fermionic Fock space dimension: ExteriorAlgebra dim = 2^k.",
        needs_experiments=False, expected_traces=2,
        expected_axes={}, physics_checks=[], color_keys=["Steinhauer", "Trento"],
    ),
    FigureSpec(
        name="fig62_vestigial_phase_diagram_mc",
        function="fig_vestigial_phase_diagram_mc",
        caption="Mean-field phase diagram with MC susceptibility peaks overlaid.",
        needs_experiments=False, expected_traces=2,
        expected_axes={}, physics_checks=[], color_keys=["Steinhauer", "Trento"],
    ),
]


# ═══════════════════════════════════════════════════════════════════════
# Figure generation
# ═══════════════════════════════════════════════════════════════════════

def generate_figures() -> dict[str, Path]:
    """Generate all figures as PNG. Returns {name: path}."""
    from src.core.visualizations import (
        fig_transonic_profiles, fig_correction_hierarchy,
        fig_parameter_space, fig_spin_sonic_enhancement,
        fig_temperature_decomposition, fig_kappa_scaling,
        fig_cgl_fdr_pattern, fig_even_vs_odd_kernel,
        fig_boundary_term_suppression, fig_positivity_constraint,
        fig_on_shell_vanishing, fig_einstein_relation,
        # Phase 3 Wave 1
        fig_parity_alternation, fig_damping_rate_third_order,
        fig_spectral_correction_comparison, fig_kappa_crossing_phase3,
        fig_spin_sonic_enhancement_phase3, fig_bogoliubov_connection,
        fig_sm_scorecard, fig_erasure_survey,
        # Phase 3 Wave 2
        fig_complex_turning_point, fig_effective_surface_gravity,
        fig_decoherence_and_noise, fig_hawking_spectrum_exact,
        fig_exact_vs_perturbative,
        # Phase 3 Wave 3
        fig_adw_effective_potential, fig_adw_phase_diagram,
        fig_adw_ng_mode_decomposition, fig_adw_he3_analogy,
        fig_adw_structural_obstacles, fig_adw_coupling_scan,
        # Phase 4 Wave 1
        fig_prediction_table_comparison, fig_detector_requirements,
        fig_kappa_scaling_phase4, fig_noise_floor_crossover,
        # Phase 5 Wave 1A
        fig_kappa_scaling_physical,
        # Phase 4 Wave 1B/1C
        fig_chirality_wall_status, fig_gl_phase_diagram,
        fig_he3_comparison_table,
        # Phase 4 Wave 2
        fig_vestigial_effective_potential,
        fig_vestigial_phase_diagram, fig_backreaction_cooling,
        fig_information_retention,
        # Phase 5 Wave 2A
        fig_grassmann_trg_2d_phase,
        # Phase 5 Wave 2B
        fig_fermion_bag_4d_binder,
        fig_fermion_bag_4d_phase_diagram,
        # Phase 5 Wave 5D
        fig_vestigial_binder_crossing,
        fig_vestigial_susceptibility_split,
        fig_gs_condition_formalization,
        fig_lean_theorem_summary,
        fig_category_hierarchy,
        fig_fusion_rules_comparison,
        fig_fibonacci_f_matrix,
        fig_drinfeld_anyon_spectrum,
        fig_layer123_bridge,
        fig_tpf_evasion_architecture,
        fig_fock_exterior_algebra,
        fig_vestigial_phase_diagram_mc,
    )
    from src.core.transonic_background import (
        steinhauer_Rb87, heidelberg_K39, trento_spin_sonic,
        solve_transonic_background,
    )

    FIGURES_DIR.mkdir(exist_ok=True)

    # Build experiments dict
    experiments = {}
    for label, param_fn in [
        ("⁸⁷Rb (Steinhauer)", steinhauer_Rb87),
        ("³⁹K (Heidelberg)", heidelberg_K39),
        ("²³Na spin-sonic (Trento)", trento_spin_sonic),
    ]:
        params = param_fn()
        bg = solve_transonic_background(params)
        experiments[label] = (params, bg)

    func_map = {
        "fig_transonic_profiles": fig_transonic_profiles,
        "fig_correction_hierarchy": fig_correction_hierarchy,
        "fig_parameter_space": fig_parameter_space,
        "fig_spin_sonic_enhancement": fig_spin_sonic_enhancement,
        "fig_temperature_decomposition": fig_temperature_decomposition,
        "fig_kappa_scaling": fig_kappa_scaling,
        "fig_cgl_fdr_pattern": fig_cgl_fdr_pattern,
        "fig_even_vs_odd_kernel": fig_even_vs_odd_kernel,
        "fig_boundary_term_suppression": fig_boundary_term_suppression,
        "fig_positivity_constraint": fig_positivity_constraint,
        "fig_on_shell_vanishing": fig_on_shell_vanishing,
        "fig_einstein_relation": fig_einstein_relation,
        # Phase 3 Wave 1
        "fig_parity_alternation": fig_parity_alternation,
        "fig_parity_alternation_stakeholder": lambda: fig_parity_alternation(stakeholder=True),
        "fig_damping_rate_third_order": fig_damping_rate_third_order,
        "fig_spectral_correction_comparison": fig_spectral_correction_comparison,
        "fig_kappa_crossing_phase3": fig_kappa_crossing_phase3,
        "fig_spin_sonic_enhancement_phase3": fig_spin_sonic_enhancement_phase3,
        "fig_bogoliubov_connection": fig_bogoliubov_connection,
        "fig_sm_scorecard": fig_sm_scorecard,
        "fig_erasure_survey": fig_erasure_survey,
        # Phase 3 Wave 2
        "fig_complex_turning_point": fig_complex_turning_point,
        "fig_effective_surface_gravity": fig_effective_surface_gravity,
        "fig_decoherence_and_noise": fig_decoherence_and_noise,
        "fig_hawking_spectrum_exact": fig_hawking_spectrum_exact,
        "fig_hawking_spectrum_exact_stakeholder": lambda: fig_hawking_spectrum_exact(stakeholder=True),
        "fig_exact_vs_perturbative": fig_exact_vs_perturbative,
        # Phase 3 Wave 3
        "fig_adw_effective_potential": fig_adw_effective_potential,
        "fig_adw_phase_diagram": fig_adw_phase_diagram,
        "fig_adw_ng_mode_decomposition": fig_adw_ng_mode_decomposition,
        "fig_adw_he3_analogy": fig_adw_he3_analogy,
        "fig_adw_structural_obstacles": fig_adw_structural_obstacles,
        "fig_adw_coupling_scan": fig_adw_coupling_scan,
        "fig_adw_coupling_scan_stakeholder": lambda: fig_adw_coupling_scan(stakeholder=True),
        # Phase 4 Wave 1
        "fig_prediction_table_comparison": fig_prediction_table_comparison,
        "fig_detector_requirements": fig_detector_requirements,
        "fig_kappa_scaling_phase4": fig_kappa_scaling_phase4,
        "fig_noise_floor_crossover": fig_noise_floor_crossover,
        # Phase 5 Wave 1A
        "fig_kappa_scaling_physical": fig_kappa_scaling_physical,
        # Phase 4 Wave 1B/1C
        "fig_chirality_wall_status": fig_chirality_wall_status,
        "fig_gl_phase_diagram": fig_gl_phase_diagram,
        "fig_he3_comparison_table": fig_he3_comparison_table,
        # Phase 4 Wave 2
        "fig_vestigial_effective_potential": fig_vestigial_effective_potential,
        "fig_vestigial_phase_diagram": fig_vestigial_phase_diagram,
        "fig_backreaction_cooling": fig_backreaction_cooling,
        "fig_information_retention": fig_information_retention,
        # Phase 5 Wave 2A
        "fig_grassmann_trg_2d_phase": fig_grassmann_trg_2d_phase,
        # Phase 5 Wave 2B
        "fig_fermion_bag_4d_binder": fig_fermion_bag_4d_binder,
        "fig_fermion_bag_4d_phase_diagram": fig_fermion_bag_4d_phase_diagram,
        # Phase 5 Wave 5D
        "fig_vestigial_binder_crossing": fig_vestigial_binder_crossing,
        "fig_vestigial_susceptibility_split": fig_vestigial_susceptibility_split,
        "fig_gs_condition_formalization": fig_gs_condition_formalization,
        "fig_lean_theorem_summary": fig_lean_theorem_summary,
        "fig_category_hierarchy": fig_category_hierarchy,
        "fig_fusion_rules_comparison": fig_fusion_rules_comparison,
        "fig_fibonacci_f_matrix": fig_fibonacci_f_matrix,
        "fig_drinfeld_anyon_spectrum": fig_drinfeld_anyon_spectrum,
        "fig_layer123_bridge": fig_layer123_bridge,
        "fig_tpf_evasion_architecture": fig_tpf_evasion_architecture,
        "fig_fock_exterior_algebra": fig_fock_exterior_algebra,
        "fig_vestigial_phase_diagram_mc": fig_vestigial_phase_diagram_mc,
    }

    paths = {}
    for spec in FIGURE_REGISTRY:
        func = func_map.get(spec.function)
        if not func:
            print(f"  SKIP {spec.name}: function {spec.function} not found")
            continue

        try:
            fig = func(experiments) if spec.needs_experiments else func()
            png_path = FIGURES_DIR / f"{spec.name}.png"
            fig.write_image(str(png_path), format="png",
                           width=1200, height=800, scale=2)
            paths[spec.name] = png_path
            print(f"  ✓ {spec.name}.png")

            # Also export HTML for interactive inspection
            html_path = FIGURES_DIR / f"{spec.name}.html"
            fig.write_html(str(html_path), include_plotlyjs="cdn")
        except Exception as e:
            print(f"  ✗ {spec.name}: {e}")
            traceback.print_exc()

    return paths


# ═══════════════════════════════════════════════════════════════════════
# Structural checks (Layer A — no LLM needed)
# ═══════════════════════════════════════════════════════════════════════

@dataclass
class CheckIssue:
    """Single issue found during structural check."""
    figure: str
    severity: str   # "error" | "warning"
    check: str
    message: str


def run_structural_checks() -> list[CheckIssue]:
    """Run automated structural checks on generated figures."""
    from src.core.visualizations import (
        fig_transonic_profiles, fig_correction_hierarchy,
        fig_parameter_space, fig_spin_sonic_enhancement,
        fig_temperature_decomposition, fig_kappa_scaling,
        fig_cgl_fdr_pattern, fig_even_vs_odd_kernel,
        fig_boundary_term_suppression, fig_positivity_constraint,
        fig_on_shell_vanishing, fig_einstein_relation,
        # Phase 3 Wave 1
        fig_parity_alternation, fig_damping_rate_third_order,
        fig_spectral_correction_comparison, fig_kappa_crossing_phase3,
        fig_spin_sonic_enhancement_phase3, fig_bogoliubov_connection,
        fig_sm_scorecard, fig_erasure_survey,
        # Phase 3 Wave 2
        fig_complex_turning_point, fig_effective_surface_gravity,
        fig_decoherence_and_noise, fig_hawking_spectrum_exact,
        fig_exact_vs_perturbative,
        # Phase 3 Wave 3
        fig_adw_effective_potential, fig_adw_phase_diagram,
        fig_adw_ng_mode_decomposition, fig_adw_he3_analogy,
        fig_adw_structural_obstacles, fig_adw_coupling_scan,
        # Phase 4 Wave 1
        fig_prediction_table_comparison, fig_detector_requirements,
        fig_kappa_scaling_phase4, fig_noise_floor_crossover,
        # Phase 5 Wave 1A
        fig_kappa_scaling_physical,
        # Phase 4 Wave 1B/1C
        fig_chirality_wall_status, fig_gl_phase_diagram,
        fig_he3_comparison_table,
        # Phase 4 Wave 2
        fig_vestigial_effective_potential,
        fig_vestigial_phase_diagram, fig_backreaction_cooling,
        fig_information_retention,
        # Phase 5 Wave 2A
        fig_grassmann_trg_2d_phase,
        # Phase 5 Wave 2B
        fig_fermion_bag_4d_binder,
        fig_fermion_bag_4d_phase_diagram,
        # Phase 5 Wave 5D — comprehensive figure suite
        fig_vestigial_binder_crossing,
        fig_vestigial_susceptibility_split,
        fig_gs_condition_formalization,
        fig_lean_theorem_summary,
        fig_category_hierarchy,
        fig_fusion_rules_comparison,
        fig_fibonacci_f_matrix,
        fig_drinfeld_anyon_spectrum,
        fig_layer123_bridge,
        fig_tpf_evasion_architecture,
        fig_fock_exterior_algebra,
        fig_vestigial_phase_diagram_mc,
        COLORS,
    )
    from src.core.transonic_background import (
        steinhauer_Rb87, heidelberg_K39, trento_spin_sonic,
        solve_transonic_background,
    )

    experiments = {}
    for label, param_fn in [
        ("⁸⁷Rb (Steinhauer)", steinhauer_Rb87),
        ("³⁹K (Heidelberg)", heidelberg_K39),
        ("²³Na spin-sonic (Trento)", trento_spin_sonic),
    ]:
        params = param_fn()
        bg = solve_transonic_background(params)
        experiments[label] = (params, bg)

    func_map = {
        "fig_transonic_profiles": fig_transonic_profiles,
        "fig_correction_hierarchy": fig_correction_hierarchy,
        "fig_parameter_space": fig_parameter_space,
        "fig_spin_sonic_enhancement": fig_spin_sonic_enhancement,
        "fig_temperature_decomposition": fig_temperature_decomposition,
        "fig_kappa_scaling": fig_kappa_scaling,
        "fig_cgl_fdr_pattern": fig_cgl_fdr_pattern,
        "fig_even_vs_odd_kernel": fig_even_vs_odd_kernel,
        "fig_boundary_term_suppression": fig_boundary_term_suppression,
        "fig_positivity_constraint": fig_positivity_constraint,
        "fig_on_shell_vanishing": fig_on_shell_vanishing,
        "fig_einstein_relation": fig_einstein_relation,
        # Phase 3 Wave 1
        "fig_parity_alternation": fig_parity_alternation,
        "fig_parity_alternation_stakeholder": lambda: fig_parity_alternation(stakeholder=True),
        "fig_damping_rate_third_order": fig_damping_rate_third_order,
        "fig_spectral_correction_comparison": fig_spectral_correction_comparison,
        "fig_kappa_crossing_phase3": fig_kappa_crossing_phase3,
        "fig_spin_sonic_enhancement_phase3": fig_spin_sonic_enhancement_phase3,
        "fig_bogoliubov_connection": fig_bogoliubov_connection,
        "fig_sm_scorecard": fig_sm_scorecard,
        "fig_erasure_survey": fig_erasure_survey,
        # Phase 3 Wave 2
        "fig_complex_turning_point": fig_complex_turning_point,
        "fig_effective_surface_gravity": fig_effective_surface_gravity,
        "fig_decoherence_and_noise": fig_decoherence_and_noise,
        "fig_hawking_spectrum_exact": fig_hawking_spectrum_exact,
        "fig_hawking_spectrum_exact_stakeholder": lambda: fig_hawking_spectrum_exact(stakeholder=True),
        "fig_exact_vs_perturbative": fig_exact_vs_perturbative,
        # Phase 3 Wave 3
        "fig_adw_effective_potential": fig_adw_effective_potential,
        "fig_adw_phase_diagram": fig_adw_phase_diagram,
        "fig_adw_ng_mode_decomposition": fig_adw_ng_mode_decomposition,
        "fig_adw_he3_analogy": fig_adw_he3_analogy,
        "fig_adw_structural_obstacles": fig_adw_structural_obstacles,
        "fig_adw_coupling_scan": fig_adw_coupling_scan,
        "fig_adw_coupling_scan_stakeholder": lambda: fig_adw_coupling_scan(stakeholder=True),
        # Phase 4 Wave 1
        "fig_prediction_table_comparison": fig_prediction_table_comparison,
        "fig_detector_requirements": fig_detector_requirements,
        "fig_kappa_scaling_phase4": fig_kappa_scaling_phase4,
        "fig_noise_floor_crossover": fig_noise_floor_crossover,
        # Phase 5 Wave 1A
        "fig_kappa_scaling_physical": fig_kappa_scaling_physical,
        # Phase 4 Wave 1B/1C
        "fig_chirality_wall_status": fig_chirality_wall_status,
        "fig_gl_phase_diagram": fig_gl_phase_diagram,
        "fig_he3_comparison_table": fig_he3_comparison_table,
        # Phase 4 Wave 2
        "fig_vestigial_effective_potential": fig_vestigial_effective_potential,
        "fig_vestigial_phase_diagram": fig_vestigial_phase_diagram,
        "fig_backreaction_cooling": fig_backreaction_cooling,
        "fig_information_retention": fig_information_retention,
        # Phase 5 Wave 2A
        "fig_grassmann_trg_2d_phase": fig_grassmann_trg_2d_phase,
        # Phase 5 Wave 2B
        "fig_fermion_bag_4d_binder": fig_fermion_bag_4d_binder,
        "fig_fermion_bag_4d_phase_diagram": fig_fermion_bag_4d_phase_diagram,
        # Phase 5 Wave 5D — comprehensive figure suite
        "fig_vestigial_binder_crossing": fig_vestigial_binder_crossing,
        "fig_vestigial_susceptibility_split": fig_vestigial_susceptibility_split,
        "fig_gs_condition_formalization": fig_gs_condition_formalization,
        "fig_lean_theorem_summary": fig_lean_theorem_summary,
        "fig_category_hierarchy": fig_category_hierarchy,
        "fig_fusion_rules_comparison": fig_fusion_rules_comparison,
        "fig_fibonacci_f_matrix": fig_fibonacci_f_matrix,
        "fig_drinfeld_anyon_spectrum": fig_drinfeld_anyon_spectrum,
        "fig_layer123_bridge": fig_layer123_bridge,
        "fig_tpf_evasion_architecture": fig_tpf_evasion_architecture,
        "fig_fock_exterior_algebra": fig_fock_exterior_algebra,
        "fig_vestigial_phase_diagram_mc": fig_vestigial_phase_diagram_mc,
    }

    issues: list[CheckIssue] = []

    for spec in FIGURE_REGISTRY:
        func = func_map.get(spec.function)
        if not func:
            issues.append(CheckIssue(spec.name, "error", "function_exists",
                                     f"{spec.function} not found"))
            continue

        try:
            fig = func(experiments) if spec.needs_experiments else func()
        except Exception as e:
            issues.append(CheckIssue(spec.name, "error", "generation",
                                     f"Failed to generate: {e}"))
            continue

        fig_dict = fig.to_dict()

        # Check 1: minimum trace count
        n_traces = len(fig_dict.get("data", []))
        if n_traces < spec.expected_traces:
            issues.append(CheckIssue(
                spec.name, "warning", "trace_count",
                f"Expected ≥{spec.expected_traces} traces, got {n_traces}"))

        # Check 2: axes labels present
        layout = fig_dict.get("layout", {})
        for axis_key, expected_substr in spec.expected_axes.items():
            axis = layout.get(axis_key, {})
            title = axis.get("title", {})
            title_text = title.get("text", "") if isinstance(title, dict) else str(title)
            if expected_substr.lower() not in title_text.lower():
                issues.append(CheckIssue(
                    spec.name, "warning", "axis_label",
                    f"{axis_key} title '{title_text}' missing expected '{expected_substr}'"))

        # Check 3: no NaN/Inf in trace data
        for i, trace in enumerate(fig_dict.get("data", [])):
            for coord in ("x", "y", "z"):
                data = trace.get(coord)
                if data is None:
                    continue
                try:
                    import numpy as np
                    arr = np.array(data, dtype=float)
                    if np.any(np.isnan(arr)):
                        issues.append(CheckIssue(
                            spec.name, "error", "nan_data",
                            f"Trace {i} has NaN in {coord}"))
                    if np.any(np.isinf(arr)):
                        issues.append(CheckIssue(
                            spec.name, "warning", "inf_data",
                            f"Trace {i} has Inf in {coord}"))
                except (ValueError, TypeError):
                    pass  # String data (categorical axes) — skip

        # Check 4: color palette consistency
        for trace in fig_dict.get("data", []):
            line = trace.get("line", {})
            marker = trace.get("marker", {})
            for color_field in [line.get("color"), marker.get("color")]:
                if isinstance(color_field, str) and color_field.startswith("#"):
                    if color_field not in COLORS.values():
                        issues.append(CheckIssue(
                            spec.name, "warning", "color_palette",
                            f"Color {color_field} not in COLORS dict"))

    return issues


# ═══════════════════════════════════════════════════════════════════════
# Review manifest (for LLM agent)
# ═══════════════════════════════════════════════════════════════════════

def produce_manifest(png_paths: dict[str, Path]) -> Path:
    """Write review_manifest.json for LLM visual review."""
    manifest = {
        "generated": datetime.now(timezone.utc).isoformat(),
        "project": str(PROJECT_ROOT),
        "figures_dir": str(FIGURES_DIR),
        "figures": [],
    }

    for spec in FIGURE_REGISTRY:
        png_path = png_paths.get(spec.name)
        entry = {
            "name": spec.name,
            "function": spec.function,
            "caption": spec.caption,
            "png_path": str(png_path) if png_path else None,
            "html_path": str(FIGURES_DIR / f"{spec.name}.html") if png_path else None,
            "expected_traces": spec.expected_traces,
            "expected_axes": spec.expected_axes,
            "physics_checks": spec.physics_checks,
            "color_keys": spec.color_keys,
            "review_criteria": [
                "Axes labels readable and correct",
                "Legend entries present and clear",
                "Data ranges physically reasonable",
                "Color palette consistent with project conventions",
                "No rendering artifacts or clipping",
                "Caption accurately describes content",
                "Experimental points correctly positioned",
            ],
        }
        manifest["figures"].append(entry)

    manifest_path = FIGURES_DIR / "review_manifest.json"
    with open(manifest_path, "w") as f:
        json.dump(manifest, f, indent=2)

    return manifest_path


# ═══════════════════════════════════════════════════════════════════════
# CLI
# ═══════════════════════════════════════════════════════════════════════

def main() -> int:
    parser = argparse.ArgumentParser(
        description="SK-EFT Hawking figure review pipeline",
        formatter_class=argparse.RawDescriptionHelpFormatter,
    )
    parser.add_argument("--generate", action="store_true",
                        help="Generate PNGs only (skip checks)")
    parser.add_argument("--check", action="store_true",
                        help="Run structural checks only (no generation)")
    parser.add_argument("--manifest", action="store_true",
                        help="Produce manifest only (for LLM agent)")
    args = parser.parse_args()

    # Default: do everything
    do_all = not (args.generate or args.check or args.manifest)

    png_paths = {}

    if args.generate or do_all:
        print("Generating figures...")
        png_paths = generate_figures()
        print(f"  {len(png_paths)} figures generated in {FIGURES_DIR}")

    if args.manifest or do_all:
        if not png_paths:
            # Check for existing PNGs
            for spec in FIGURE_REGISTRY:
                p = FIGURES_DIR / f"{spec.name}.png"
                if p.exists():
                    png_paths[spec.name] = p
        manifest_path = produce_manifest(png_paths)
        print(f"\nManifest: {manifest_path}")

    if args.check or do_all:
        print("\nRunning structural checks...")
        issues = run_structural_checks()

        errors = [i for i in issues if i.severity == "error"]
        warnings = [i for i in issues if i.severity == "warning"]

        for issue in issues:
            sym = "✗" if issue.severity == "error" else "⚠"
            print(f"  {sym} [{issue.figure}] {issue.check}: {issue.message}")

        if not issues:
            print("  ✓ All structural checks passed")

        print(f"\n  Summary: {len(errors)} error(s), {len(warnings)} warning(s)")

        # Write check results alongside manifest
        results_path = FIGURES_DIR / "structural_checks.json"
        with open(results_path, "w") as f:
            json.dump({
                "timestamp": datetime.now(timezone.utc).isoformat(),
                "issues": [asdict(i) for i in issues],
                "summary": {"errors": len(errors), "warnings": len(warnings)},
            }, f, indent=2)

        return 1 if errors else 0

    return 0


if __name__ == "__main__":
    sys.exit(main())
