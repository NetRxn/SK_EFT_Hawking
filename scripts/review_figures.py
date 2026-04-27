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
    # Phase 5 Wave 6: Analytical Vestigial Susceptibility
    FigureSpec(
        name="fig63_vestigial_susceptibility",
        function="fig_vestigial_susceptibility",
        caption="RPA metric susceptibility vs G/G_c for multiple u_g values.",
        needs_experiments=False, expected_traces=4,
        expected_axes={}, physics_checks=[], color_keys=[],
    ),
    FigureSpec(
        name="fig64_vestigial_window",
        function="fig_vestigial_window",
        caption="Vestigial window G_ves/G_c vs u_g showing exponential narrowness.",
        needs_experiments=False, expected_traces=2,
        expected_axes={}, physics_checks=[], color_keys=[],
    ),
    FigureSpec(
        name="fig65_vestigial_phase_diagram_analytical",
        function="fig_vestigial_phase_diagram_analytical",
        caption="ADW analytical phase diagram: pre-geometric / vestigial / Einstein-Cartan.",
        needs_experiments=False, expected_traces=3,
        expected_axes={}, physics_checks=[], color_keys=[],
    ),
    # Phase 5a Wave 4: GT Lattice Chiral Fermion + Chirality Wall Master
    FigureSpec(
        name="fig66_gt_band_structure",
        function="fig_gt_band_structure",
        caption="GT BdG band structure showing single gapless Weyl node at Gamma.",
        needs_experiments=False, expected_traces=4,
        expected_axes={"yaxis": "Energy"}, physics_checks=[], color_keys=["Rb87", "K39"],
    ),
    FigureSpec(
        name="fig67_wilson_mass_bz",
        function="fig_wilson_mass_bz",
        caption="Wilson mass M(kx,ky,0) heatmap: zero only at origin (Weyl node).",
        needs_experiments=False, expected_traces=1,
        expected_axes={}, physics_checks=[], color_keys=["dissipative"],
    ),
    FigureSpec(
        name="fig68_chiral_charge_spectrum",
        function="fig_chiral_charge_spectrum",
        caption="GT chiral charge eigenvalues ±cos(p3/2): non-compact spectrum.",
        needs_experiments=False, expected_traces=2,
        expected_axes={}, physics_checks=[], color_keys=["Rb87", "K39"],
    ),
    FigureSpec(
        name="fig69_gt_commutator_verification",
        function="fig_gt_commutator_verification",
        caption="Numerical verification [H,Q_A]=0 at L=8: machine epsilon everywhere.",
        needs_experiments=False, expected_traces=1,
        expected_axes={"yaxis": "commutator"}, physics_checks=[], color_keys=["Rb87"],
    ),
    FigureSpec(
        name="fig70_chirality_wall_three_pillars",
        function="fig_chirality_wall_three_pillars",
        caption="Three-pillar chirality wall formal verification: no-go + GT + anomaly.",
        needs_experiments=False, expected_traces=0,
        expected_axes={}, physics_checks=[], color_keys=[],
    ),
    # Phase 5b: SM Anomaly
    FigureSpec(
        name="fig71_sm_fermion_z16_anomaly",
        function="fig_sm_fermion_z16_anomaly",
        caption="SM fermion anomaly contributions in Z16: 16 Weyl with nu_R, 15 without.",
        needs_experiments=False, expected_traces=6,
        expected_axes={"xaxis": "component"}, physics_checks=[], color_keys=["Rb87", "Na23"],
    ),
    FigureSpec(
        name="fig72_sm_generation_anomaly",
        function="fig_sm_generation_anomaly",
        caption="Z16 anomaly index vs generation count: with and without nu_R.",
        needs_experiments=False, expected_traces=2,
        expected_axes={"xaxis": "generation", "yaxis": "anomaly"}, physics_checks=[], color_keys=["Rb87", "dissipative"],
    ),
    FigureSpec(
        name="fig73_sm_generation_constraint",
        function="fig_sm_generation_constraint",
        caption="Generation constraint c_minus = 8 N_f mod 24: N_f must be multiple of 3.",
        needs_experiments=False, expected_traces=1,
        expected_axes={"xaxis": "generation", "yaxis": "central"}, physics_checks=[], color_keys=["dispersive"],
    ),
    FigureSpec(
        name="fig74_drinfeld_equivalence_structure",
        function="fig_drinfeld_equivalence_structure",
        caption="Drinfeld center equivalence Z(Vec_G) = Rep(D(G)): anyon content for Z/2 (toric code) and S3 (non-abelian).",
        needs_experiments=False, expected_traces=2,
        expected_axes={"xaxis": "anyon", "yaxis": "dimension"}, physics_checks=[], color_keys=["Rb87", "Na23", "K39"],
    ),
    # Phase 5q: Ext computation over A(1)
    FigureSpec(
        name="fig_ext_chart",
        function="fig_ext_chart",
        caption="Ext chart for A(1): E2 page of the Adams spectral sequence for ko. Machine-checked dims 1,2,2,2,3,4.",
        needs_experiments=False, expected_traces=3,
        expected_axes={"xaxis": "stem", "yaxis": "filtration"}, physics_checks=[], color_keys=["steinhauer", "trento"],
    ),
    FigureSpec(
        name="fig_a1_resolution_structure",
        function="fig_a1_resolution_structure",
        caption="Minimal free resolution of F2 over A(1): bidiagonal pattern, ranks 1,2,2,2,3,4.",
        needs_experiments=False, expected_traces=7,
        expected_axes={}, physics_checks=[], color_keys=["steinhauer"],
    ),
    # Phase 5s: FK gapped interface
    FigureSpec(
        name="fig_fk_spectrum",
        function="fig_fk_spectrum",
        caption="FK 8-Majorana spectrum: eigenvalues -7,-5,-1,+1,+3 with multiplicities 1,1,4,7,3. Gap Delta=2.",
        needs_experiments=False, expected_traces=5,
        expected_axes={"yaxis": "energy"}, physics_checks=[], color_keys=["dissipative"],
    ),
    # Phase 5x Wave 5: SFDM cluster-merger money plot (two panels)
    FigureSpec(
        name="fig_sfdm_velocity_threshold_step",
        function="fig_sfdm_velocity_threshold_step",
        caption="Paper 17 money plot (left) — DM-galaxy offset vs v_infall/c_s. SFDM step function at M=1 vs SIDM smooth rise vs CDM null. 5 canonical mergers overlaid.",
        needs_experiments=False, expected_traces=4,
        expected_axes={"xaxis": "mach", "yaxis": "offset"},
        physics_checks=[], color_keys=["steel_blue", "amber", "dissipative"],
    ),
    FigureSpec(
        name="fig_sfdm_stacked_kappa_profile",
        function="fig_sfdm_stacked_kappa_profile",
        caption="Paper 17 money plot (right) — stacked S/N vs N mergers for Euclid + Roman. 3σ and 5σ thresholds marked. First 3σ ~2028.",
        needs_experiments=False, expected_traces=2,
        expected_axes={"xaxis": "N", "yaxis": "snr"},
        physics_checks=[], color_keys=["steel_blue", "amber"],
    ),
    # Phase 5x Wave 8/9: Paper 17 candidate-matrix and empirical-hook ranking
    FigureSpec(
        name="fig_phase5x_candidate_viability_matrix",
        function="fig_phase5x_candidate_viability_matrix",
        caption="Paper 17 §4/§8 — Five emergent-gravity DM candidates classified by basic viability. 4/5 viable; FG torsion obstructed at tree-level EoS. Lean: phase5x_candidates_viability_matrix.",
        needs_experiments=False, expected_traces=1,
        expected_axes={"xaxis": "viability", "yaxis": "candidate"},
        physics_checks=[], color_keys=["steel_blue", "dissipative"],
    ),
    FigureSpec(
        name="fig_phase5x_empirical_hook_ranking",
        function="fig_phase5x_empirical_hook_ranking",
        caption="Paper 17 §9 — Five empirical hooks ranked by Phase 5x detectability + timeline. Merger sonic boom top; direct nuclear recoil last (all candidates invisible). Lean: empirical_hook_ranking_strict.",
        needs_experiments=False, expected_traces=1,
        expected_axes={"xaxis": "priority", "yaxis": "hook"},
        physics_checks=[], color_keys=["steel_blue", "amber"],
    ),
    FigureSpec(
        name="fig_doublon_gate_spectrum",
        function="fig_doublon_gate_spectrum",
        caption="Phase 5t W9 — Fermi-Hubbard dimer singlet-sector spectrum vs U (Δ=0) plus direct-vs-superexchange scaling. Left: three eigenvalues (E_plus, E_minus, U) cross-verified by numpy eigh vs Lean closed-form (W7l charpoly factorization). Right: superexchange gap J(t,U) with 4t²/U asymptote and the Lean W7i bound envelope ±16t⁴/U³.",
        needs_experiments=False, expected_traces=5,
        expected_axes={"xaxis": "U", "yaxis": "Eigenvalue"},
        physics_checks=[], color_keys=["steel_blue", "dissipative", "cross"],
    ),
    FigureSpec(
        name="fig_higgs_mass_parameter_scan",
        function="fig_higgs_mass_parameter_scan",
        caption=(
            "Phase 5z Wave 1 — microscopic Higgs-mass prediction over the "
            "(Λ_UV, G_c) plane at fiducial N_f=15 and λ_4=0.13. Heatmap shows "
            "log₁₀ m_H [GeV] from the schematic Wetterich scalar-channel gap "
            "equation. Gold contour: the m_H = 125.25 GeV target with the "
            "EW.M_H_MATCH_TOLERANCE = 50% band overlay. Any region within "
            "the gold band activates Gate Z.1 GO (quantitative scalar-rung "
            "EWSB); absence over a wide natural range is the structural-only "
            "Gate Z.1 NO-GO verdict. Lean: scalar_rung_quantitative_EWSB_iff_m_H_matches."
        ),
        needs_experiments=False, expected_traces=3,
        expected_axes={"xaxis": "Λ_UV", "yaxis": "G_c"},
        physics_checks=[], color_keys=["amber"],
    ),
    FigureSpec(
        name="fig_ew_transition_phase_diagram",
        function="fig_ew_transition_phase_diagram",
        caption=(
            "Phase 5z Wave 3 — EW phase transition. Left panel: V_T(φ) "
            "at three temperatures (T = 0 broken phase, T = T_c/2, "
            "T = 1.5 T_c symmetric phase) at the SM benchmark "
            "(m_H = 125 GeV, λ = 0.13, c_T = 0.4, E = 0.01); "
            "T_c ≈ 139 GeV. Curves normalized to unit max-abs for clarity. "
            "Right panel: first-order vs crossover partition over the "
            "(m_H, E) plane: shaded region (E > 0) is first-order; "
            "white line at E = 0 is crossover. Star: SM benchmark "
            "(m_H = 125.20, E = 0.01). Vertical dashed line at m_H = 72 GeV "
            "(Kajantie-Laine-Rummukainen-Shaposhnikov 1996 lattice "
            "crossover threshold). Lean: thermalMassSq_neg_below_T_c, "
            "first_order_and_crossover_disjoint, "
            "crossover_excludes_baryogenesis."
        ),
        needs_experiments=False, expected_traces=5,
        expected_axes={"xaxis": "φ", "yaxis": "V_T"},
        physics_checks=[], color_keys=["amber", "steel_blue", "cross"],
    ),
    FigureSpec(
        name="fig_bhl_bilocal_correction",
        function="fig_bhl_bilocal_correction",
        caption=(
            "Phase 5z Wave 1b — BHL gap problem and Hill 2025 bilocal "
            "correction. Left panel: bilocal-corrected m_H = (φ(0)/φ(∞)) "
            "√2 m_t versus dilution at the BHL benchmark m_t = 220 GeV. "
            "BHL minimal (dilution = 1) overshoots PDG (125.20 GeV) by "
            "~2.5×; Hill 2025 dilution ≈ 0.402 recovers PDG within 1 GeV. "
            "Right panel: required dilution to match PDG m_H as function "
            "of m_t. BHL benchmark m_t = 220 GeV (dashed cross) vs. "
            "PDG m_t = 172.57 GeV (dotted amber) frame the natural BHL "
            "dilution range. Lean: bhl_minimal_overshoots_pdg, "
            "bilocal_correction_can_match_pdg."
        ),
        needs_experiments=False, expected_traces=4,
        expected_axes={"xaxis": "dilution", "yaxis": "m_H"},
        physics_checks=[], color_keys=["steel_blue", "amber", "cross"],
    ),
    FigureSpec(
        name="fig_seesaw_y_m_r_band",
        function="fig_seesaw_y_m_r_band",
        caption=(
            "Phase 5z Wave 2 — Type-I seesaw (y, M_R) plane. Three diagonal "
            "contours mark fixed light-neutrino masses m_ν via "
            "m_ν = y² v² / M_R: m₃ ≈ 0.0501 eV (atmospheric anchor, NO), "
            "m₂ ≈ 8.61 meV (solar anchor), and m_ν = 0.1 eV (cosmology cap). "
            "Shaded band: natural seesaw region between m₃ and the 0.1 eV cap. "
            "Star: top-Yukawa anchor at GUT scale (canonical seesaw point). "
            "Diamond: Wave-2 lower scan anchor (Y_NU_LOWER × M_R_LOWER_BOUND). "
            "Lean: MajoranaRung.seesawNeutrinoMass_strictMono_inv_M_R."
        ),
        needs_experiments=False, expected_traces=6,
        expected_axes={"xaxis": "y", "yaxis": "M_R"},
        physics_checks=[], color_keys=["amber", "steel_blue", "cross"],
    ),
    FigureSpec(
        name="fig_m_beta_beta_vs_m_lightest",
        function="fig_m_beta_beta_vs_m_lightest",
        caption=(
            "Phase 5z Wave 2 — m_ββ vs m_lightest 'lobster plot' at NuFit-6.0 "
            "best-fit angles. Both NO and IO bands shown, swept over the full "
            "Majorana-phase Monte Carlo. Horizontal bands: KamLAND-Zen 800 "
            "current bound (28-122 meV at 90% CL, NME spread) and LEGEND-1000 "
            "projected discovery reach (9-21 meV). Wave-2 conclusion (deep "
            "research §4): IO is fully discoverable by LEGEND-1000; most of "
            "NO is out of reach. Embedding-agnostic across I/II/III. "
            "Lean: NeutrinoMixing.PMNSMatrix."
        ),
        needs_experiments=False, expected_traces=2,
        expected_axes={"xaxis": "m_lightest", "yaxis": "m_ββ"},
        physics_checks=[], color_keys=["amber", "steel_blue", "cross"],
    ),
    FigureSpec(
        name="fig_G_N_emerg_parameter_scan",
        function="fig_G_N_emerg_parameter_scan",
        caption=(
            "Phase 6a Wave 1 — emergent Newton constant from ADW microscopic "
            "theory. Heatmap shows log₁₀(G_N^emerg / G_N^obs) over the "
            "(Λ_UV, α_ADW) plane at fiducial N_f = 15 (SM Weyl per generation, "
            "no ν_R), with G_N^emerg = α_ADW · 12π / (N_f · Λ²) (Sakharov-Adler "
            "form, Adler RMP 54, 729 (1982) Eq. 3.3). Gold contour: exact match "
            "G_N^emerg = G_N^obs = 6.71 × 10⁻³⁹ GeV⁻²; dotted gold: ±50% "
            "tolerance band. Vertical dashed: GUT (10¹⁶ GeV) and Planck-mass "
            "(1.221 × 10¹⁹ GeV) cutoffs. Stars: Planck-anchor matching α* = "
            "N_f/(12π) for N_f ∈ {15, 16, 45, 48}; α* falls between 0.40 and "
            "1.27, all inside the natural range [0.1, 10]. Lean: "
            "LinearizedEFE.G_N_emerg_match_locus, "
            "G_N_emerg_match_at_planck_anchor."
        ),
        needs_experiments=False, expected_traces=3,
        expected_axes={"xaxis": "Λ_UV", "yaxis": "α_ADW"},
        physics_checks=[], color_keys=["amber"],
    ),
    FigureSpec(
        name="fig_c_GW_vs_ligo_constraint",
        function="fig_c_GW_vs_ligo_constraint",
        caption=(
            "Phase 6a Wave 2 — gravitational-wave propagation speed deviation "
            "Δc/c = √χ_vest − 1 across the natural vestigial-susceptibility "
            "range, vs the GW170817 multi-messenger bound (Abbott et al. ApJL "
            "848, L13 (2017), Eq. (5)): |Δc/c| ≤ 3 × 10⁻¹⁵. The Volovik "
            "vestigial-second-sound graviton identification produces "
            "Δc/c ∈ [−0.68, +2.16] over the natural χ_vest range "
            "[0.1, 10] — failing the GW170817 cap by 14+ orders of "
            "magnitude. The GW170817-compatible χ_vest window is "
            "[(1 − 3e-15)², (1 + 3e-15)²] — fine-tuning to within "
            "3 × 10⁻¹⁵ of unity. Lean: "
            "GravitationalWaves.vestigial_natural_range_violates_ligo, "
            "c_GW_match_iff_chi_close_to_one."
        ),
        needs_experiments=False, expected_traces=3,
        expected_axes={"xaxis": "χ_vest", "yaxis": "Δc/c"},
        physics_checks=[], color_keys=["amber", "steel_blue"],
    ),
    FigureSpec(
        name="fig_entropy_coefficient_vs_spectrum",
        function="fig_entropy_coefficient_vs_spectrum",
        caption=(
            "Phase 6a Wave 3 — Bekenstein-Hawking leading-coefficient κ_leading(γ) "
            "as a function of the Immirzi tuning γ. The 1/4 prefactor in S = A/(4G_N) "
            "is structurally a TUNING (not a derivation): distinct counting "
            "prescriptions produce distinct γ values that 'tune' to 1/4 under their "
            "own normalizations. Domagala-Lewandowski γ ≈ 0.2375 (gr-qc/0407051) "
            "and Meissner γ ≈ 0.2739 (gr-qc/0407052) are both shown. The MTC zoo "
            "in the right panel records log d_max for Fibonacci, Ising, D(S₃), "
            "and toric code (the abelian falsifier with log d_max = 0 ⇒ F2 fail). "
            "Lean: BHEntropyMicroscopic.HorizonMTCBC.γ_immirzi field; "
            "BHEntropyMicroscopic.kaul_majumdar_log_coefficient."
        ),
        needs_experiments=False, expected_traces=3,
        expected_axes={"xaxis": "γ", "yaxis": "κ_leading"},
        physics_checks=[], color_keys=["amber", "steel_blue"],
    ),
    FigureSpec(
        name="fig_log_correction_signature",
        function="fig_log_correction_signature",
        caption=(
            "Phase 6a Wave 3 — log-correction coefficient signature across "
            "schemes. The Kaul-Majumdar SU(2)_k value c_log = −3/2 "
            "decomposes structurally as (−1/2 from the Gaussian saddle) + "
            "(−1 from the SU(2)-singlet projection via the I₀ − I₁ cancellation, "
            "Kaul-Majumdar Eq. (15)). The Sen 4D Schwarzschild heat-kernel result "
            "(arXiv:1205.0971) gives c_log = +(212/45 − 3) ≈ +1.71, explicitly "
            "DISAGREEING with the −3/2 anchor — universality fails outside the "
            "Cardy-saddle subfamily. Per the Wave 3 deep-research return, no "
            "published derivation pins c_log for Fibonacci, Ising, or D(S₃) "
            "(Outcome-3 conjectural). Toric code fails F2 (abelian, log d_max = 0). "
            "Lean: BHEntropyMicroscopic.sen_4d_disagrees_with_kaul_majumdar; "
            "BHEntropyMicroscopic.kaul_majumdar_log_decomposition."
        ),
        needs_experiments=False, expected_traces=1,
        expected_axes={"xaxis": "scheme", "yaxis": "c_log"},
        physics_checks=[], color_keys=["amber", "steel_blue"],
    ),
    FigureSpec(
        name="fig_T_H_evolution_regime_partition",
        function="fig_T_H_evolution_regime_partition",
        caption=(
            "Phase 6a Wave 5 — BCH four-laws regime-partition profile under "
            "Hawking-radiation backreaction. Left: T_H(t) under evaporation in "
            "the Schwarzschild regime (M > M_c, dT_H/dt > 0, heats as "
            "evaporates, finite t-evap; Hawking 1975) and the BEC-acoustic "
            "regime (M < M_c, dT_H/dt < 0, cools toward asymptotic "
            "extremality at infinite time; Balbinot, Fagnocchi, Fabbri, "
            "Procopio, PRD 71, 064019 (2005), gr-qc/0405098, Eq. Tsonic). "
            "The genuine regime partition is the sign-flip of dT_H/dt "
            "during evaporation; the critical mass M_c = (N_f · Λ_UV) / "
            "(12π · α_ADW) is project-original ansatz (Wave 5 deep-research "
            "§3 dimensional analysis). Right: substrate-response coefficient "
            "ansatz δ_ADW = (α_ADW − 1)·Λ_UV (deep-research §9), vanishing "
            "at α_ADW = 1 (bare Sakharov-Adler limit) and sign-determined by "
            "α_ADW ⋛ 1. Lean: BHThermodynamicsFourLaws.regime_partition_criterion; "
            "BHThermodynamicsFourLaws.delta_ADW_nonzero_iff_alpha_ADW_ne_one."
        ),
        needs_experiments=False, expected_traces=3,
        expected_axes={"xaxis": "Time", "yaxis": "T_H"},
        physics_checks=[], color_keys=["amber", "steel_blue"],
    ),
    FigureSpec(
        name="fig_ep_violation_matrix",
        function="fig_ep_violation_matrix",
        caption=(
            "Phase 6c Wave 3 — Equivalence-Principle classification of six "
            "Phase 5x DM-related mechanisms. Left: 6×3 mechanism × EP-level "
            "matrix (WEP / EEP / SEP) showing two violators (both vestigial-"
            "phase phenomena: differential coupling at η = 1 maximal, ruled "
            "out at any current EP precision; relics at η ~ 10⁻¹⁸ STEP-class "
            "satellite-detectable per W8 §5 ranking line 3) and four non-"
            "violators (FangGu torsion DM, fracton subdiffusion, SFDM "
            "Thomas-Fermi, hidden-sector ℤ₁₆ singlet). The structural "
            "punchline: EP violation is *vestigial-only* in the project's "
            "current dark-sector landscape. Right: η-scale comparison bar "
            "chart (log₁₀ scale) showing vestigial-phase η_max = 1, the "
            "MICROSCOPE bound η < 10⁻¹⁵ (Touboul et al., PRL 119, 231101, "
            "2017) as a horizontal reference, vestigial-relics η ~ 10⁻¹⁸, "
            "and the STEP-class satellite target η ~ 10⁻¹⁸. Lean: "
            "EquivalencePrinciple.violatesAt + ep_violation_is_vestigial_only "
            "+ vestigial_microscope_violation_consistent."
        ),
        needs_experiments=False, expected_traces=2,
        expected_axes={"xaxis": "level", "yaxis": "log10_eta"},
        physics_checks=[], color_keys=["amber", "steel_blue"],
    ),
    FigureSpec(
        name="fig_zhitnitsky_de_theta_scan",
        function="fig_zhitnitsky_de_theta_scan",
        caption=(
            "Phase 6c Wave 1 — Zhitnitsky topological dark-energy "
            "prediction (Van Waerbeke-Zhitnitsky 2025, arXiv:2506.14182) "
            "vs observed ρ_DE. Left: ρ_DE = Λ_QCD⁶/M_P² scan over "
            "Λ_QCD ∈ [1 MeV, 1 GeV] on log-log axes; observed band "
            "(2.3 meV)⁴ ≈ 2.8e-11 eV⁴ from Planck 2018 + DESI DR2 "
            "shown as amber stripe; PDG Λ_QCD ≈ 100 MeV vertical "
            "reference shows the no-free-parameter Zhitnitsky "
            "prediction sits ~240× above observed (within 3 orders). "
            "Right: cosmological-constant-problem suppression bar chart "
            "comparing Planck-natural M_P⁴ ≈ 10¹¹² eV⁴, Zhitnitsky "
            "QCD-topological prediction ≈ 7e-9 eV⁴, and observed "
            "≈ 3e-11 eV⁴ — Zhitnitsky realizes ~120 orders of magnitude "
            "of the hierarchy suppression. Lean: "
            "StrongCPTopologicalDE.zhitnitsky_DE_at_lambda_qcd_within_3_orders "
            "+ zhitnitsky_DE_far_below_planck + "
            "combined_zhitnitsky_qtheory_exceeds_observation."
        ),
        needs_experiments=False, expected_traces=2,
        expected_axes={"xaxis": "Λ_QCD", "yaxis": "ρ_DE"},
        physics_checks=[], color_keys=["steel_blue", "amber"],
    ),
    FigureSpec(
        name="fig_cfl_z3_center_bridge",
        function="fig_cfl_z3_center_bridge",
        caption=(
            "Phase 6d Wave 3 — CFL emergent ℤ_3 (Hirono-Tanizaki) ≡ "
            "QCD center ℤ_3 (W1) correctness-push identification. "
            "Left: cube roots of unity {1, ω, ω²} on the complex unit "
            "circle, with the CFL emergent generator (Hirono-Tanizaki "
            "JHEP 12, 2018) and the QCD center generator from "
            "CenterSymmetryConfinement.Z3 BOTH at the same point ω = "
            "exp(2πi/3). The sum rule 1 + ω + ω² = 0 is the algebraic "
            "fingerprint distinguishing ℤ_3 from ℤ_2. Right: bar chart "
            "showing the three ℤ_3 charges (0, 1, 2) plus the "
            "out-of-range 3, classified by Hirono-Tanizaki topological-"
            "order-beyond-Landau-Ginzburg sector. Charge 0 (vacuum) "
            "and charge 3 (out of ℤ_3) are falsifiers; charges 1, 2 "
            "are the topologically ordered sectors. Lean: "
            "CFLChiralLagrangian.CFL_emergent_Z3_matches_QCD_center_Z3 "
            "+ emergentZ3_pow_3 + emergentZ3_sum_cube_roots + "
            "H_TopologicalOrderBeyondLG_witness/falsifier_trivial."
        ),
        needs_experiments=False, expected_traces=3,
        expected_axes={"xaxis": "Re", "yaxis": "Im"},
        physics_checks=[], color_keys=["steel_blue", "amber"],
    ),
    FigureSpec(
        name="fig_gmor_relation_verification",
        function="fig_gmor_relation_verification",
        caption=(
            "Phase 6d Wave 2 — GMOR relation `m_π² · f_π² = "
            "−2 m_q · ⟨q̄q⟩` numerical verification at PDG/FLAG "
            "central values. Left: side-by-side bars at LHS ≈ "
            "1.589e-4 GeV⁴ and RHS ≈ 1.589e-4 GeV⁴ — visually "
            "indistinguishable, confirming GMOR holds to ~1 part in "
            "10⁴ (|LHS − RHS| ≈ 4e-8 GeV⁴). Right: relative residual "
            "|LHS − RHS|/LHS as the input quark mass m_q is swept; "
            "the residual minimum at m_q ≈ 3.5 MeV (PDG average u+d) "
            "confirms the GMOR-consistent point. Sources: Gell-Mann-"
            "Oakes-Renner PR 175 (1968); FLAG 2021 ⟨q̄q⟩ ≈ −0.0227 "
            "GeV³ (EPJC 81); PDG 2022 m_π = 0.137 GeV, f_π = 0.092 "
            "GeV. Lean: ChiralSSB_QCD.gmor_pdg_match + "
            "gmor_rhs_pos_of_quark_mass_pos + "
            "chiral_unbroken_violates_gmor."
        ),
        needs_experiments=False, expected_traces=2,
        expected_axes={"xaxis": "m_q", "yaxis": "residual"},
        physics_checks=[], color_keys=["steel_blue", "amber"],
    ),
    FigureSpec(
        name="fig_code_distance_vs_fusion_spectrum",
        function="fig_code_distance_vs_fusion_spectrum",
        caption=(
            "Phase 6c Wave 4 — Hayden-Preskill structural QEC across "
            "MTC spectra. Left: code-distance proxy d_C := log d_max "
            "for Fibonacci (d_τ = φ ≈ 1.618; d_C ≈ 0.481), Ising "
            "(d_σ = √2; d_C ≈ 0.347), SU(3)_k=2 Fibonacci sub-sector, "
            "and trivial-abelian (d_max = 1; d_C = 0 — falsifies the "
            "W4 admissibility criterion). The W4 quantitative theorem "
            "fibonacci_HPCode_codeDistance_lt_log_two locates Fibonacci "
            "below log 2 ≈ 0.693, the minimal non-abelian threshold. "
            "Right: scrambling-time bound t_scr := log D² for the "
            "same substrates, demonstrating the W4 correctness-push "
            "(positive code distance ⇒ positive scrambling time via "
            "D² ≥ d_max² > 1). Trivial-abelian has t_scr = 0, the "
            "vacuum scrambling-time falsifier. Sources: Hayden-Preskill "
            "JHEP 2007/9/120 (arXiv:0708.4025); Almheiri-Dong-Harlow "
            "JHEP 2015/4/163 (arXiv:1411.7041); Pastawski-Yoshida-"
            "Harlow-Preskill JHEP 2015/6/149 (arXiv:1503.06237). Lean: "
            "QECHolographyBridge.codeDistance_pos_iff_non_abelian + "
            "code_distance_scaling_matches_anyonic_fusion_iff_fusion_in_admissible_class "
            "+ fibonacci_HPCode_codeDistance_lt_log_two + "
            "fibonacci_HPCode_scramblingTimeBound_pos + "
            "trivialAbelian_violates_admissibility."
        ),
        needs_experiments=False, expected_traces=2,
        expected_axes={"xaxis": "MTC spectrum", "yaxis": "d_C / t_scr"},
        physics_checks=[], color_keys=["steel_blue", "sage", "amber", "carmine"],
    ),
    FigureSpec(
        name="fig_polyakov_loop_deconfinement",
        function="fig_polyakov_loop_deconfinement",
        caption=(
            "Phase 6d Wave 1 — Polyakov-loop order parameter and "
            "Walker-Wang transport window. Left: |P| vs T/T_c showing "
            "the deconfinement transition for Z_2 (Ising) and Z_3 "
            "(3-state Potts) Svetitsky-Yaffe universality classes "
            "with ν = 0.6299 and 0.5 respectively (Pelissetto-Vicari "
            "Phys. Rep. 368, 2002; Kos-Poland-Simmons-Duffin JHEP 03, "
            "2016). Confining phase has |P| = 0; deconfining |P| > 0. "
            "Right: KSS bound η/s ≥ 1/(4π) ≈ 0.0796 (Kovtun-Son-"
            "Starinets PRL 94, 2005) with the Walker-Wang transport "
            "correctness-push window [KSS, 2·KSS]. Both numerical "
            "falsifiers (η/s = 0 and η/s = 1) lie outside the window. "
            "Lean: CenterSymmetryConfinement.confining_iff_magnitude_zero "
            "+ deconfining_implies_magnitude_positive + ising_nu_gt_potts_nu "
            "+ KSS_bound_below_0_08 + walker_wang_zero_eta_violator "
            "+ walker_wang_unit_eta_violator."
        ),
        needs_experiments=False, expected_traces=3,
        expected_axes={"xaxis": "T/T_c", "yaxis": "|P|"},
        physics_checks=[], color_keys=["steel_blue", "amber"],
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
        # Phase 5 Wave 6
        fig_vestigial_susceptibility,
        fig_vestigial_window,
        fig_vestigial_phase_diagram_analytical,
        # Phase 5a Wave 4: GT + Chirality Wall
        fig_gt_band_structure,
        fig_wilson_mass_bz,
        fig_chiral_charge_spectrum,
        fig_gt_commutator_verification,
        fig_chirality_wall_three_pillars,
        # Phase 5b: SM Anomaly
        fig_sm_fermion_z16_anomaly,
        fig_sm_generation_anomaly,
        fig_sm_generation_constraint,
        fig_drinfeld_equivalence_structure,
        # Phase 5q: Ext computation
        fig_ext_chart,
        fig_a1_resolution_structure,
        fig_fk_spectrum,
        # Phase 5x Wave 5: SFDM merger money plot
        fig_sfdm_velocity_threshold_step,
        fig_sfdm_stacked_kappa_profile,
        # Phase 5x Wave 8/9: Paper 17 synthesis figures
        fig_phase5x_candidate_viability_matrix,
        fig_phase5x_empirical_hook_ranking,
        # Phase 5t Wave 9: doublon-gate spectrum + scaling
        fig_doublon_gate_spectrum,
        # Phase 5z Wave 1: scalar-rung Higgs-mass parameter scan
        fig_higgs_mass_parameter_scan,
        # Phase 5z Wave 1b: BHL gap problem + Hill bilocal correction
        fig_bhl_bilocal_correction,
        # Phase 5z Wave 3: EW phase transition phase diagram
        fig_ew_transition_phase_diagram,
        # Phase 5z Wave 2: Majorana-rung seesaw + m_ββ
        fig_seesaw_y_m_r_band,
        fig_m_beta_beta_vs_m_lightest,
        # Phase 6a Wave 1: emergent G_N from ADW microscopic theory
        fig_G_N_emerg_parameter_scan,
        # Phase 6a Wave 2: gravitational waves vs GW170817
        fig_c_GW_vs_ligo_constraint,
        # Phase 6a Wave 3: BH entropy from MTC counting
        fig_entropy_coefficient_vs_spectrum,
        fig_log_correction_signature,
        # Phase 6a Wave 5: BH thermodynamics regime partition
        fig_T_H_evolution_regime_partition,
        # Phase 6c Wave 3: EP-violation matrix
        fig_ep_violation_matrix,
        # Phase 6d Wave 1: Polyakov-loop deconfinement + Walker-Wang
        fig_polyakov_loop_deconfinement,
        # Phase 6d Wave 2: GMOR PDG verification
        fig_gmor_relation_verification,
        # Phase 6d Wave 3: CFL Z_3 ↔ QCD center Z_3 correctness-push
        fig_cfl_z3_center_bridge,
        # Phase 6c Wave 1: Zhitnitsky topological DE
        fig_zhitnitsky_de_theta_scan,
        # Phase 6c Wave 4: Hayden-Preskill QEC code-distance / scrambling
        fig_code_distance_vs_fusion_spectrum,
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
        # Phase 5 Wave 6
        "fig_vestigial_susceptibility": fig_vestigial_susceptibility,
        "fig_vestigial_window": fig_vestigial_window,
        "fig_vestigial_phase_diagram_analytical": fig_vestigial_phase_diagram_analytical,
        # Phase 5a Wave 4: GT + Chirality Wall
        "fig_gt_band_structure": fig_gt_band_structure,
        "fig_wilson_mass_bz": fig_wilson_mass_bz,
        "fig_chiral_charge_spectrum": fig_chiral_charge_spectrum,
        "fig_gt_commutator_verification": fig_gt_commutator_verification,
        "fig_chirality_wall_three_pillars": fig_chirality_wall_three_pillars,
        # Phase 5b
        "fig_sm_fermion_z16_anomaly": fig_sm_fermion_z16_anomaly,
        "fig_sm_generation_anomaly": fig_sm_generation_anomaly,
        "fig_sm_generation_constraint": fig_sm_generation_constraint,
        "fig_drinfeld_equivalence_structure": fig_drinfeld_equivalence_structure,
        "fig_ext_chart": fig_ext_chart,
        "fig_a1_resolution_structure": fig_a1_resolution_structure,
        "fig_fk_spectrum": fig_fk_spectrum,
        "fig_sfdm_velocity_threshold_step": fig_sfdm_velocity_threshold_step,
        "fig_sfdm_stacked_kappa_profile": fig_sfdm_stacked_kappa_profile,
        "fig_phase5x_candidate_viability_matrix": fig_phase5x_candidate_viability_matrix,
        "fig_phase5x_empirical_hook_ranking": fig_phase5x_empirical_hook_ranking,
        "fig_doublon_gate_spectrum": fig_doublon_gate_spectrum,
        "fig_higgs_mass_parameter_scan": fig_higgs_mass_parameter_scan,
        "fig_bhl_bilocal_correction": fig_bhl_bilocal_correction,
        "fig_ew_transition_phase_diagram": fig_ew_transition_phase_diagram,
        "fig_seesaw_y_m_r_band": fig_seesaw_y_m_r_band,
        "fig_m_beta_beta_vs_m_lightest": fig_m_beta_beta_vs_m_lightest,
        "fig_G_N_emerg_parameter_scan": fig_G_N_emerg_parameter_scan,
        "fig_c_GW_vs_ligo_constraint": fig_c_GW_vs_ligo_constraint,
        "fig_entropy_coefficient_vs_spectrum": fig_entropy_coefficient_vs_spectrum,
        "fig_log_correction_signature": fig_log_correction_signature,
        "fig_T_H_evolution_regime_partition": fig_T_H_evolution_regime_partition,
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
        # Phase 5 Wave 6
        fig_vestigial_susceptibility,
        fig_vestigial_window,
        fig_vestigial_phase_diagram_analytical,
        # Phase 5a Wave 4: GT + Chirality Wall
        fig_gt_band_structure,
        fig_wilson_mass_bz,
        fig_chiral_charge_spectrum,
        fig_gt_commutator_verification,
        fig_chirality_wall_three_pillars,
        # Phase 5b: SM Anomaly
        fig_sm_fermion_z16_anomaly,
        fig_sm_generation_anomaly,
        fig_sm_generation_constraint,
        fig_drinfeld_equivalence_structure,
        # Phase 5q: Ext computation
        fig_ext_chart,
        fig_a1_resolution_structure,
        # Phase 5s: FK gapped interface
        fig_fk_spectrum,
        # Phase 5x Wave 5: SFDM merger money plot
        fig_sfdm_velocity_threshold_step,
        fig_sfdm_stacked_kappa_profile,
        # Phase 5x Wave 8/9: Paper 17 synthesis figures
        fig_phase5x_candidate_viability_matrix,
        fig_phase5x_empirical_hook_ranking,
        # Phase 5t Wave 9: doublon-gate spectrum + scaling
        fig_doublon_gate_spectrum,
        # Phase 5z Wave 1: scalar-rung Higgs-mass parameter scan
        fig_higgs_mass_parameter_scan,
        # Phase 5z Wave 1b: BHL gap problem + Hill bilocal correction
        fig_bhl_bilocal_correction,
        # Phase 5z Wave 3: EW phase transition phase diagram
        fig_ew_transition_phase_diagram,
        # Phase 5z Wave 2: Majorana-rung seesaw + m_ββ
        fig_seesaw_y_m_r_band,
        fig_m_beta_beta_vs_m_lightest,
        # Phase 6a Wave 1: emergent G_N from ADW microscopic theory
        fig_G_N_emerg_parameter_scan,
        # Phase 6a Wave 2: gravitational waves vs GW170817
        fig_c_GW_vs_ligo_constraint,
        # Phase 6a Wave 3: BH entropy from MTC counting
        fig_entropy_coefficient_vs_spectrum,
        fig_log_correction_signature,
        # Phase 6a Wave 5: BH thermodynamics regime partition
        fig_T_H_evolution_regime_partition,
        # Phase 6c Wave 3: EP-violation matrix
        fig_ep_violation_matrix,
        # Phase 6d Wave 1: Polyakov-loop deconfinement + Walker-Wang
        fig_polyakov_loop_deconfinement,
        # Phase 6d Wave 2: GMOR PDG verification
        fig_gmor_relation_verification,
        # Phase 6d Wave 3: CFL Z_3 ↔ QCD center Z_3 correctness-push
        fig_cfl_z3_center_bridge,
        # Phase 6c Wave 1: Zhitnitsky topological DE
        fig_zhitnitsky_de_theta_scan,
        # Phase 6c Wave 4: Hayden-Preskill QEC code-distance / scrambling
        fig_code_distance_vs_fusion_spectrum,
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
        # Phase 5 Wave 6
        "fig_vestigial_susceptibility": fig_vestigial_susceptibility,
        "fig_vestigial_window": fig_vestigial_window,
        "fig_vestigial_phase_diagram_analytical": fig_vestigial_phase_diagram_analytical,
        # Phase 5a Wave 4: GT + Chirality Wall
        "fig_gt_band_structure": fig_gt_band_structure,
        "fig_wilson_mass_bz": fig_wilson_mass_bz,
        "fig_chiral_charge_spectrum": fig_chiral_charge_spectrum,
        "fig_gt_commutator_verification": fig_gt_commutator_verification,
        "fig_chirality_wall_three_pillars": fig_chirality_wall_three_pillars,
        # Phase 5b
        "fig_sm_fermion_z16_anomaly": fig_sm_fermion_z16_anomaly,
        "fig_sm_generation_anomaly": fig_sm_generation_anomaly,
        "fig_sm_generation_constraint": fig_sm_generation_constraint,
        "fig_drinfeld_equivalence_structure": fig_drinfeld_equivalence_structure,
        "fig_ext_chart": fig_ext_chart,
        "fig_a1_resolution_structure": fig_a1_resolution_structure,
        "fig_fk_spectrum": fig_fk_spectrum,
        "fig_sfdm_velocity_threshold_step": fig_sfdm_velocity_threshold_step,
        "fig_sfdm_stacked_kappa_profile": fig_sfdm_stacked_kappa_profile,
        "fig_phase5x_candidate_viability_matrix": fig_phase5x_candidate_viability_matrix,
        "fig_phase5x_empirical_hook_ranking": fig_phase5x_empirical_hook_ranking,
        "fig_doublon_gate_spectrum": fig_doublon_gate_spectrum,
        "fig_higgs_mass_parameter_scan": fig_higgs_mass_parameter_scan,
        "fig_bhl_bilocal_correction": fig_bhl_bilocal_correction,
        "fig_ew_transition_phase_diagram": fig_ew_transition_phase_diagram,
        "fig_seesaw_y_m_r_band": fig_seesaw_y_m_r_band,
        "fig_m_beta_beta_vs_m_lightest": fig_m_beta_beta_vs_m_lightest,
        "fig_G_N_emerg_parameter_scan": fig_G_N_emerg_parameter_scan,
        "fig_c_GW_vs_ligo_constraint": fig_c_GW_vs_ligo_constraint,
        "fig_entropy_coefficient_vs_spectrum": fig_entropy_coefficient_vs_spectrum,
        "fig_log_correction_signature": fig_log_correction_signature,
        "fig_T_H_evolution_regime_partition": fig_T_H_evolution_regime_partition,
        "fig_ep_violation_matrix": fig_ep_violation_matrix,
        "fig_polyakov_loop_deconfinement": fig_polyakov_loop_deconfinement,
        "fig_gmor_relation_verification": fig_gmor_relation_verification,
        "fig_cfl_z3_center_bridge": fig_cfl_z3_center_bridge,
        "fig_zhitnitsky_de_theta_scan": fig_zhitnitsky_de_theta_scan,
        "fig_code_distance_vs_fusion_spectrum": fig_code_distance_vs_fusion_spectrum,
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
