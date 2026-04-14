"""
Aristotle API Interface for Lean Sorry-Filling

Submits the SK-EFT Hawking Lean project to Aristotle for automated
theorem proving. Manages project submission, status polling, and
result retrieval.

Usage:
    from src.aristotle_interface import AristotleRunner
    runner = AristotleRunner()
    result = runner.submit_and_wait("Fill all sorry gaps in the acoustic metric module")

Design decisions:
    - We use the aristotlelib CLI wrapper rather than raw HTTP to match
      the documented API surface.
    - Each sorry gap is tagged with a priority level and a brief description
      to guide Aristotle's proof search.
    - Results are saved to docs/aristotle_results/ with timestamps for
      reproducibility tracking.

References:
    - Aristotle API docs: https://aristotle.harmonic.fun/dashboard/docs/api
    - aristotlelib PyPI: https://pypi.org/project/aristotlelib/
"""

import json
import os
import subprocess
import sys
from dataclasses import dataclass, field
from datetime import datetime
from pathlib import Path
from typing import Optional


# Project paths (relative to the project root)
# src/core/aristotle_interface.py → parent.parent.parent = project root
PROJECT_ROOT = Path(__file__).parent.parent.parent
LEAN_DIR = PROJECT_ROOT / "lean"
RESULTS_DIR = PROJECT_ROOT / "docs" / "aristotle_results"


@dataclass
class SorryGap:
    """A documented sorry gap in the Lean formalization.

    Each sorry gap has:
    - module: which Lean file contains it
    - name: the theorem/def name
    - priority: 1 (algebraic, likely fillable) to 3 (requires deep analysis)
    - description: what the sorry is about
    - strategy_hint: suggested proof approach for Aristotle

    Priority levels:
        1 = Pure algebra/linear algebra (determinant computation, matrix inverse)
            → Aristotle should handle these readily
        2 = Algebraic + inequality reasoning (positivity, bounds)
            → Aristotle may need guidance
        3 = Analysis/PDE (WKB, asymptotics, complex turning points)
            → Likely remains sorry; documents the mathematical gap
    """
    module: str
    name: str
    priority: int  # 1 = most tractable, 3 = hardest
    description: str
    strategy_hint: str = ""
    filled: bool = False  # True if Aristotle (or manual proof) has filled this sorry


# Registry of all sorry gaps across the three structures
SORRY_GAPS: list[SorryGap] = [
    # Structure A: Acoustic Metric
    SorryGap(
        module="SKEFTHawking.AcousticMetric",
        name="acousticMetric_det",
        priority=1,
        description="2x2 determinant of the acoustic metric equals -ρ²",
        strategy_hint="Expand the 2x2 determinant using Fin 2 cases, simplify algebraically",
        filled=True,  # Filled by Aristotle run 082e6776 (2026-03-23)
    ),
    SorryGap(
        module="SKEFTHawking.AcousticMetric",
        name="acousticMetric_inv_correct",
        priority=1,
        description="Inverse acoustic metric is correct: g · g⁻¹ = I",
        strategy_hint="Matrix multiplication of 2x2 matrices, simplify each component",
        filled=True,  # Filled by Aristotle run 082e6776 (2026-03-23)
    ),
    SorryGap(
        module="SKEFTHawking.AcousticMetric",
        name="acoustic_metric_theorem",
        priority=2,
        description="Phonon EOM from L=P(X) equals □_g π = 0 on acoustic metric",
        strategy_hint="Expand P(X) to quadratic order, compute Euler-Lagrange, match coefficients",
        filled=True,  # Filled by Aristotle run a87f425a (2026-03-23)
    ),
    SorryGap(
        module="SKEFTHawking.AcousticMetric",
        name="acoustic_metric_lorentzian",
        priority=1,
        description="Acoustic metric has negative determinant (Lorentzian signature)",
        strategy_hint="Use acousticMetric_det and rho > 0",
        filled=True,  # Filled by Aristotle run 082e6776 (2026-03-23)
    ),
    SorryGap(
        module="SKEFTHawking.AcousticMetric",
        name="dAlembertian",
        priority=3,
        description="Definition of d'Alembertian requires partial derivative infrastructure",
        strategy_hint="Needs Mathlib's multivariate calculus; may remain sorry",
        filled=True,  # Filled by Aristotle run 88cf2000 (2026-03-23): partialT/partialX + flux decomposition
    ),

    # Structure B: SK Doubling
    SorryGap(
        module="SKEFTHawking.SKDoubling",
        name="firstOrder_positivity",
        priority=1,
        description="Im I_SK ≥ 0 from γ₁,γ₂ ≥ 0 and β > 0",
        strategy_hint="Product of non-negative reals is non-negative, x² ≥ 0",
        filled=True,  # Filled by Aristotle run 082e6776 (2026-03-23)
    ),
    SorryGap(
        module="SKEFTHawking.SKDoubling",
        name="firstOrder_uniqueness",
        priority=3,
        description="First-order SK action uniquely parameterized by (γ₁, γ₂): "
                    "any action satisfying normalization + positivity + KMS equals "
                    "firstOrderDissipativeAction for some coefficients",
        strategy_hint="Enumerate 9 order-1 monomials, impose normalization (≥1 ψ_a factor), "
                      "positivity (Im part positive-semidefinite), KMS (fixes Re from Im via β). "
                      "Remaining free params = 2 → (γ₁, γ₂). Finite-dim linear algebra.",
        filled=True,  # Filled by Aristotle run 270e77a0 (2026-03-23): found original KMSSymmetry
                       # too weak (counterexample c=⟨0,0,0,0,0,0,0,1,0⟩), introduced FirstOrderKMS
                       # with algebraic FDR constraints, proved with γ₁=-c.r2, γ₂=c.r1+c.r2
    ),
    SorryGap(
        module="SKEFTHawking.SKDoubling",
        name="candidateTermCount",
        priority=2,
        description="Count of candidate SK terms at each derivative order",
        strategy_hint="Combinatorial counting of monomials with derivative constraints",
        filled=True,  # Filled by Aristotle run a87f425a (2026-03-23)
    ),
    SorryGap(
        module="SKEFTHawking.SKDoubling",
        name="fdr_from_kms",
        priority=3,
        description="FDR: Im part of firstOrderDissipativeAction equals (γ₁/β)·ψ_a² + (γ₂/β)·(∂_t ψ_a)² "
                    "for all field configurations. Direct computation by unfolding the definition.",
        strategy_hint="Unfold firstOrderDissipativeAction.lagrangian, extract .2 (Im part), "
                      "show it equals the RHS by simp + ring. This is a definitional equality.",
        filled=True,  # Filled by Aristotle run 638c5ff3 (2026-03-23): fun f => rfl
    ),

    # Structure B (continued): Per-sector FDR decomposition
    SorryGap(
        module="SKEFTHawking.SKDoubling",
        name="fdr_from_kms_gamma1",
        priority=1,
        description="Per-sector FDR for γ₁: Im part at pure ψ_a point equals γ₁/β. "
                    "Evaluates firstOrderDissipativeAction at ⟨0,1,0,0,0,0,0,0,0⟩.",
        strategy_hint="Unfold firstOrderDissipativeAction.lagrangian at the structured literal, "
                      "extract .2 (Im part), simplify 0^2→0, 1^2→1, then ring. "
                      "Alternative: instantiate fdr_from_kms at this field config and simplify.",
        filled=True,  # Filled by Aristotle run 20556034 (2026-03-23): unfold + aesop
    ),
    SorryGap(
        module="SKEFTHawking.SKDoubling",
        name="fdr_from_kms_gamma2",
        priority=1,
        description="Per-sector FDR for γ₂: Im part at pure ∂_t ψ_a point equals γ₂/β. "
                    "Evaluates firstOrderDissipativeAction at ⟨0,0,0,0,1,0,0,0,0⟩.",
        strategy_hint="Unfold firstOrderDissipativeAction.lagrangian at the structured literal, "
                      "extract .2 (Im part), simplify 0^2→0, 1^2→1, then ring. "
                      "Alternative: instantiate fdr_from_kms at this field config and simplify.",
        filled=True,  # Filled by Aristotle run 20556034 (2026-03-23): simp [firstOrderDissipativeAction]
    ),

    # Structure C: Hawking Universality
    SorryGap(
        module="SKEFTHawking.HawkingUniversality",
        name="dispersive_correction_bound",
        priority=3,
        description="Dispersive correction: ∃ nonzero δ_disp with |δ_disp| ≤ C·D² "
                    "(strengthened with δ_disp ≠ 0 to prevent trivial witness)",
        strategy_hint="PROVIDED SOLUTION in docstring: witness δ_disp := -(π/6)·D², C := π/6 + 1. "
                      "Verify |-(π/6)·D²| ≤ (π/6+1)·D² and -(π/6)·D² ≠ 0 from hD_pos.",
        filled=True,  # Filled by Aristotle run d65e3bba (2026-03-23): concrete witness, bound + nonzero
    ),
    SorryGap(
        module="SKEFTHawking.HawkingUniversality",
        name="dissipative_correction_existence",
        priority=3,
        description="Dissipative correction: ∃ δ_diss, vanishes iff γ₁=γ₂=0, nonzero otherwise "
                    "(strengthened with bidirectional property)",
        strategy_hint="PROVIDED SOLUTION in docstring: witness δ_diss := -(γ₁+γ₂)/(2κ). "
                      "Forward: γ₁=γ₂=0 → numerator 0. Reverse: γ_i > 0 → sum > 0 → δ ≠ 0.",
        filled=True,  # Filled by Aristotle run 657fcd6a (2026-03-23): concrete witness, bidirectional
    ),
    SorryGap(
        module="SKEFTHawking.HawkingUniversality",
        name="hawking_universality",
        priority=3,
        description="Combined universality: ∃ EffectiveTemperature with T_H = ℏκ/2π, "
                    "bidirectional δ_diss, nonzero δ_disp with O(D²) bound, "
                    "and cross-term vanishes when γ→0. "
                    "Strengthened: requires δ_disp ≠ 0 and (γ>0 → δ_diss ≠ 0) "
                    "to prevent trivial all-zeros witness.",
        strategy_hint="PROVIDED SOLUTION in docstring: construct EffectiveTemperature with "
                      "T_H := hawkingTemp κ, delta_disp := -(π/6)·D², "
                      "delta_diss := -(γ₁+γ₂)/(2κ), delta_cross := 0. "
                      "Verify six conjuncts: rfl, simp, div_ne_zero+linarith, "
                      "positivity+nlinarith, neg_ne_zero+mul_ne_zero, simp.",
        filled=True,  # Filled by Aristotle run 416fb432 (2026-03-23): structural witnesses, all 6 conjuncts
    ),

    # Structure B (Phase 2): Second-Order SK-EFT
    SorryGap(
        module="SKEFTHawking.SecondOrderSK",
        name="transport_coefficient_count",
        priority=1,
        description="General counting formula: number of (m,n) pairs with m+n=N+1, m even, "
                    "equals ⌊(N+1)/2⌋+1. Combinatorial identity on Finset.Icc.",
        strategy_hint="Filter Finset.Icc (0,0) (N+1,N+1) by p.1+p.2=N+1 ∧ p.1%2=0, "
                      "then show card = (N+1)/2 + 1. For small N, decide; "
                      "for general N, induction on N with case split on parity.",
        filled=True,  # Filled by Aristotle run d61290fd (2026-03-24): bijection with Finset.range
    ),
    SorryGap(
        module="SKEFTHawking.SecondOrderSK",
        name="firstOrder_count",
        priority=1,
        description="At order 1 (L=2): exactly 2 free transport coefficients. "
                    "Card of filter on Finset.Icc (0,0) (2,2) = 2.",
        strategy_hint="Finite decidable computation: enumerate pairs in Icc, "
                      "filter by sum=2 and even first component, count. Should be native_decide or decide.",
        filled=True,  # Filled by Aristotle run d61290fd (2026-03-24): native_decide
    ),
    SorryGap(
        module="SKEFTHawking.SecondOrderSK",
        name="secondOrder_count",
        priority=1,
        description="At order 2 (L=3): exactly 2 new transport coefficients. "
                    "Card of filter on Finset.Icc (0,0) (3,3) = 2.",
        strategy_hint="Finite decidable computation: enumerate pairs in Icc, "
                      "filter by sum=3 and even first component, count. Should be native_decide or decide.",
        filled=True,  # Filled by Aristotle run d61290fd (2026-03-24): native_decide
    ),
    SorryGap(
        module="SKEFTHawking.SecondOrderSK",
        name="secondOrder_count_with_parity",
        priority=1,
        description="With spatial parity (m even AND n even), ZERO new coefficients at order 2. "
                    "Card of filter on Finset.Icc (0,0) (3,3) with sum=3, m%2=0, n%2=0 = 0.",
        strategy_hint="Finite decidable: no (m,n) with m+n=3 and both even exists "
                      "(odd total precludes both even). native_decide or decide.",
        filled=True,  # Filled by Aristotle run d61290fd (2026-03-24): native_decide
    ),

    # Structure B (Phase 2): Full Second-Order Strong Uniqueness
    SorryGap(
        module="SKEFTHawking.SecondOrderSK",
        name="fullSecondOrder_uniqueness",
        priority=2,
        description="Strong uniqueness: any FullSecondOrderCoeffs satisfying positivity + "
                    "FullSecondOrderKMS is determined by 4 transport coefficients "
                    "(CombinedDissipativeCoeffs). Analog of Phase 1 firstOrder_uniqueness.",
        strategy_hint="Construct CombinedDissipativeCoeffs with γ₁=-c.r2, γ₂=c.r1+c.r2, "
                      "γ_{2,1}=c.s1, γ_{2,2}=c.s3. Non-negativity from positivity at "
                      "specific field configs + FDR. Lagrangian equality by field_simp/ring.",
        filled=True,  # Proved by Aristotle run c4d73ca8 (March 24, 2026)
    ),
    SorryGap(
        module="SKEFTHawking.SecondOrderSK",
        name="combined_positivity_constraint",
        priority=2,
        description="Positivity forces γ_{2,1}+γ_{2,2}=0 at this truncation. "
                    "The 3×3 imaginary quadratic form has zero (3,3) entry, "
                    "so the off-diagonal cross-term must vanish for PSD.",
        strategy_hint="By contradiction: if c = γ_{2,1}+γ_{2,2} ≠ 0, construct field config "
                      "with dt_ψ_a=1, dx_ψ_a=-(γ₂+1)/c making Im part = -1/β < 0.",
        filled=True,  # Proved by Aristotle run c4d73ca8 (March 24, 2026)
    ),

    # Direction A (Phase 2): WKB Analysis
    SorryGap(
        module="SKEFTHawking.WKBAnalysis",
        name="turning_point_shift",
        priority=3,
        description="Dissipation shifts the WKB turning point into the complex plane: "
                    "∃ tp, tp.x_imag = dampingRate / (κ·c_s). Complex WKB analysis.",
        strategy_hint="Pure witness construction: "
                      "exact ⟨⟨0, ddr.dampingRate k_horizon omega / (kappa * ddr.cs)⟩, rfl⟩",
        filled=True,  # Proved by Aristotle run c4d73ca8 (March 24, 2026)
    ),
    SorryGap(
        module="SKEFTHawking.WKBAnalysis",
        name="dampingRate_firstOrder_nonneg",
        priority=1,
        description="Damping rate is non-negative at first order (γ_{2,1}=γ_{2,2}=0): "
                    "γ₁·k² + γ₂·ω²/c_s² ≥ 0 from γ₁≥0, γ₂≥0.",
        strategy_hint="After rewriting h21, h22 to zero the second-order terms, "
                      "add_nonneg of (mul_nonneg gamma_nonneg sq_nonneg) for each term. "
                      "May need div_nonneg for the ω²/c_s² term.",
        filled=True,  # Proven inline in WKBAnalysis.lean (not sorry)
    ),
    # ============================================================
    # Phase 3: Stress Test Suite (bulletproofing)
    # ============================================================
    # SecondOrderSK.lean stress tests
    SorryGap(
        module="SKEFTHawking.SecondOrderSK",
        name="altFDR_uniqueness_test",
        priority=2,
        description="Stress test: does uniqueness hold under WRONG FDR j_tx·β = s1-s3? "
                    "Expected: COUNTEREXAMPLE proving the FDR sign matters.",
        strategy_hint="Try constructing c with s1=1, s3=0, j_tx = 1/beta (from s1-s3=1). "
                      "The combinedDissipativeAction uses (s1+s3)/beta for j_tx, so the "
                      "Lagrangians won't match. Construct explicit counterexample.",
        filled=True,  # Proved (NEGATION) by Aristotle run 3eedcabb (March 24, 2026)
                      # Counterexample: c=⟨1,-1,0,0,0,0,1,0,0,1,0,1,0,0⟩, β=1
    ),
    SorryGap(
        module="SKEFTHawking.SecondOrderSK",
        name="relaxed_uniqueness_test",
        priority=2,
        description="Stress test: with nonzero i3 (relaxed KMS), does uniqueness hold "
                    "with 5 free params (including spatial noise coefficient)?",
        strategy_hint="Construct CombinedDissipativeCoeffs_relaxed with gamma_x = c.i3. "
                      "Same approach as fullSecondOrder_uniqueness but with extra parameter.",
        filled=True,  # Proved by Aristotle run 3eedcabb (March 24, 2026)
                      # 5-param witness with γ_x = c.i3
    ),
    SorryGap(
        module="SKEFTHawking.SecondOrderSK",
        name="relaxed_positivity_weakens",
        priority=2,
        description="With nonzero i3/gamma_x, positivity constraint relaxes from "
                    "(γ_{2,1}+γ_{2,2})=0 to (γ_{2,1}+γ_{2,2})²≤4·γ₂·γ_x·β.",
        strategy_hint="The 3x3 matrix PSD condition: 2x2 minor det ≥ 0 gives the "
                      "inequality. Proof by contradiction: if violated, construct "
                      "field config making Im < 0.",
        filled=True,  # Proved by Aristotle run 3eedcabb (March 24, 2026)
                      # PSD bound (γ_{2,1}+γ_{2,2})²≤4·γ₂·γ_x·β by contradiction
    ),
    SorryGap(
        module="SKEFTHawking.SecondOrderSK",
        name="thirdOrder_count",
        priority=1,
        description="count(3) = 3: Finset cardinality of third-order monomials "
                    "equals (3+1)/2+1 = 3.",
        strategy_hint="native_decide on Finset.Icc filter (same pattern as "
                      "firstOrder_count, secondOrder_count)",
        filled=True,  # Proved by Aristotle run 3eedcabb (March 24, 2026)
                      # native_decide
    ),
    SorryGap(
        module="SKEFTHawking.SecondOrderSK",
        name="cumulative_count_through_3",
        priority=1,
        description="Total transport coefficients through order 3 = 2+2+3 = 7. "
                    "Now stated as pure arithmetic on (N+1)/2+1 values.",
        strategy_hint="norm_num (no sorry remaining — proved inline)",
        filled=True,  # Proved by norm_num (March 24, 2026)
    ),
    # SKDoubling.lean stress tests
    SorryGap(
        module="SKEFTHawking.SKDoubling",
        name="firstOrder_KMS_optimal",
        priority=2,
        description="FirstOrderKMS + positivity ↔ i1≥0 ∧ i2≥0. Tests whether "
                    "FirstOrderKMS is the optimal first-order constraint.",
        strategy_hint="Forward: positivity at pure-psi_a and pure-dt_psi_a configs. "
                      "Backward: i1≥0,i2≥0 + KMS constraints → sum of nonneg squares.",
        filled=True,  # Proved by Aristotle run 3eedcabb (March 24, 2026)
                      # Biconditional: positivity ↔ i1≥0 ∧ i2≥0
    ),
    SorryGap(
        module="SKEFTHawking.SKDoubling",
        name="firstOrder_altSign_uniqueness_test",
        priority=2,
        description="Stress test: does uniqueness hold with WRONG FDR sign "
                    "i1·β = +r2 instead of -r2? Expected: COUNTEREXAMPLE.",
        strategy_hint="Counterexample: c = ⟨1,-1,0,0,0,0,-1/β,(0)/β,0⟩ satisfies "
                      "alt-FDR but not the real DissipativeCoeffs structure (gamma_1 "
                      "would be +r2 = -1 < 0, violating non-negativity).",
        filled=True,  # Proved (NEGATION) by Aristotle run 3eedcabb (March 24, 2026)
                      # Counterexample: c=⟨1,1,0,0,0,0,1,2,0⟩, β=1
    ),
    # WKBAnalysis.lean stress tests
    SorryGap(
        module="SKEFTHawking.WKBAnalysis",
        name="no_dissipation_zero_damping",
        priority=1,
        description="When γ₁=γ₂=γ_{2,1}=γ_{2,2}=0, dampingRate(k,ω)=0 for all k,ω. "
                    "(Aristotle corrected: all 4 gammas needed, not just 2.)",
        strategy_hint="Unfold dampingRate, substitute h1-h4 to zero all terms, ring.",
        filled=True,  # Proved by Aristotle run 3eedcabb (March 24, 2026)
                      # Signature corrected to require h3, h4 for γ_{2,1}, γ_{2,2}
    ),
    SorryGap(
        module="SKEFTHawking.WKBAnalysis",
        name="turning_point_no_shift",
        priority=1,
        description="When γ₁=γ₂=γ_{2,1}=γ_{2,2}=0, the turning point shift is zero. "
                    "(Aristotle corrected: all 4 gammas needed.)",
        strategy_hint="Use no_dissipation_zero_damping with h1-h4, then simp.",
        filled=True,  # Proved by Aristotle run 3eedcabb (March 24, 2026)
    ),
    SorryGap(
        module="SKEFTHawking.WKBAnalysis",
        name="firstOrder_correction_zero_iff_no_dissipation",
        priority=1,
        description="When γ₁=γ₂=γ_{2,1}=γ_{2,2}=0, firstOrderCorrection=0. "
                    "(Aristotle corrected: all 4 gammas needed.)",
        strategy_hint="Unfold firstOrderCorrection, use no_dissipation_zero_damping with h1-h4, simp.",
        filled=True,  # Proved by Aristotle run 3eedcabb (March 24, 2026)
    ),
    # ============================================================
    # Phase 4: Total-Division Strengthening (Round 5)
    # ============================================================
    # These theorems close the gap where hk : 0 < kappa was unused
    # in Round 4 proofs due to Lean's total division (0/0 = 0).
    # Each genuinely requires κ > 0 or c_s ≠ 0 in the proof.
    SorryGap(
        module="SKEFTHawking.WKBAnalysis",
        name="turning_point_shift_nonzero",
        priority=2,
        description="Nonzero damping rate → nonzero turning point shift, given κ>0 and c_s>0. "
                    "Exercises hk that was unused in turning_point_no_shift.",
        strategy_hint="div_ne_zero from mul_ne_zero (ne_of_gt hk) (ne_of_gt hcs), "
                      "paired with hrate.",
        filled=True,  # Proved by Aristotle run 518636d7 (March 24, 2026)
                      # One-liner: div_ne_zero hrate (mul_ne_zero hk.ne' hcs.ne')
    ),
    SorryGap(
        module="SKEFTHawking.WKBAnalysis",
        name="firstOrder_correction_zero_iff",
        priority=2,
        description="firstOrderCorrection = 0 ↔ dampingRate = 0, given κ>0. "
                    "True biconditional completing the forward-only Round 4 theorem. "
                    "Backward direction needs κ≠0 to invert Γ_H/κ = 0.",
        strategy_hint="Forward: unfold, div_eq_zero_iff, use ne_of_gt hk. "
                      "Backward: unfold, rewrite, simp.",
        filled=True,  # Proved by Aristotle run 518636d7 (March 24, 2026)
                      # unfold + div_eq_iff hk.ne' + aesop
    ),
    SorryGap(
        module="SKEFTHawking.WKBAnalysis",
        name="dampingRate_eq_zero_iff",
        priority=2,
        description="dampingRate = 0 for all (k,ω) ↔ all 4 gammas = 0, given c_s≠0. "
                    "Closes the chain: correction=0 ↔ damping=0 ↔ no dissipation.",
        strategy_hint="Backward: no_dissipation_zero_damping. Forward: evaluate at "
                      "(k=1,ω=0), (k=2,ω=0) to get γ₁=0, γ_{2,1}=0; then (k=0,ω=1) "
                      "for γ₂=0; then (k=1,ω=1) for γ_{2,2}=0. Needs c_s≠0 for the "
                      "ω²/c_s² and ω²k/c_s² terms.",
        filled=True,  # Proved by Aristotle run 518636d7 (March 24, 2026)
                      # Forward: evaluate at 4 points to isolate each γᵢ
                      # Backward: unfold + aesop
    ),

    # ── Direction D: CGL Dynamical KMS Derivation ──
    SorryGap(
        module="SKEFTHawking.CGLTransform",
        name="cgl_fdr_general",
        priority=2,
        description="General-order CGL FDR: noise at level 2n paired with "
                    "odd-ω dissipation at level 2n+1 via the generalized Einstein relation.",
        strategy_hint="Fourier-space computation: build K_R with odd-m coefficient, "
                      "apply K_N = −i·[K_R(ω) − K_R(−ω)]/(β₀ω), match coefficients of "
                      "ω^{2j_t}·k^{2j_x}. See PROVIDED SOLUTION in the theorem docstring.",
        filled=True,  # Proved by Aristotle run 2ca3e7e6 (March 24, 2026)
                      # Strengthened: now encodes actual noise=-b/β formula (was trivial True)
    ),
    SorryGap(
        module="SKEFTHawking.CGLTransform",
        name="cgl_fdr_spatial",
        priority=2,
        description="CGL FDR for spatial dissipative monomials: same structure as "
                    "cgl_fdr_general but parameterized by (j_t, j_x).",
        strategy_hint="rw [← h_fdr, mul_div_cancel_right₀ _ hb.ne']",
        filled=True,  # Proved by Aristotle run 2ca3e7e6 (March 24, 2026)
    ),
    SorryGap(
        module="SKEFTHawking.CGLTransform",
        name="cgl_implies_secondOrderKMS",
        priority=2,
        description="CGL FDR + T-reversal + model identification → j_tx·β = s₁+s₃. "
                    "Full chain connecting CGL to FullSecondOrderKMS.",
        strategy_hint="linarith on the 5 linear hypotheses",
        filled=True,  # Proved by Aristotle run 2ca3e7e6 (March 24, 2026)
    ),
    SorryGap(
        module="SKEFTHawking.CGLTransform",
        name="einstein_relation",
        priority=1,
        description="Einstein relation from CGL: σ·β = −b_{1,0}. The simplest FDR: "
                    "level 0 noise paired with level 1 friction.",
        strategy_hint="From h_fdr: noise.sigma = -diss.b_10 / beta. Use eq_div_iff hb.ne'.",
        filled=True,  # Proved by Aristotle run dab8cfc1 (March 24, 2026)
                      # Proof: rw [← h_fdr, mul_div_cancel_right₀ _ hb.ne']
    ),
    SorryGap(
        module="SKEFTHawking.CGLTransform",
        name="secondOrder_cgl_fdr",
        priority=1,
        description="Second-order CGL FDR: i_{0,1}·β = −b_{1,2} and i_{1,0}·β = −b_{3,0}. "
                    "Two noise bilinears paired with two odd-ω dissipative terms at level 3.",
        strategy_hint="From hypotheses h_fdr_01 and h_fdr_10, use eq_div_iff hb.ne' to solve "
                      "for noise.i_01 and noise.i_10 in terms of diss coefficients and beta.",
        filled=True,  # Proved by Aristotle run dab8cfc1 (March 24, 2026)
                      # Proof: exact ⟨eq_div_of_mul_eq hb.ne' h_fdr_01, eq_div_of_mul_eq hb.ne' h_fdr_10⟩
    ),

    # ── Phase 3: ADWMechanism.lean (1 theorem) ──────────────────────────
    SorryGap(module="SKEFTHawking.ADWMechanism", name="curvature_zero_at_Gc",
             priority=1, description="V_eff curvature vanishes at critical coupling G_c",
             strategy_hint="one_div_div + sub_self",
             filled=True),  # Proved by Aristotle run f8de66d1 (March 25, 2026)

    # ── Phase 4: Aristotle batch b1ea2eb7 (13 theorems) ────────────────
    SorryGap(module="SKEFTHawking.FractonHydro", name="fracton_exceeds_standard_general",
             priority=1, description="Fracton charges exceed standard hydro at all orders",
             strategy_hint="Induction on multipole order", filled=True),
    SorryGap(module="SKEFTHawking.FractonHydro", name="fracton_ratio_grows_3d",
             priority=1, description="Fracton/standard charge ratio grows with order in 3D",
             strategy_hint="Binomial monotonicity", filled=True),
    SorryGap(module="SKEFTHawking.FractonHydro", name="binomial_strict_mono",
             priority=1, description="Binomial coefficient strict monotonicity lemma",
             strategy_hint="Nat.choose properties", filled=True),
    SorryGap(module="SKEFTHawking.FractonGravity", name="dof_gap_eq_d_minus_1_check_4",
             priority=1, description="DOF gap = d-1 at d=4", strategy_hint="native_decide", filled=True),
    SorryGap(module="SKEFTHawking.FractonGravity", name="dof_gap_eq_d_minus_1_check_5",
             priority=1, description="DOF gap = d-1 at d=5", strategy_hint="native_decide", filled=True),
    SorryGap(module="SKEFTHawking.FractonGravity", name="dof_gap_positive_2_through_8",
             priority=1, description="DOF gap positive for d=2..8", strategy_hint="native_decide", filled=True),
    SorryGap(module="SKEFTHawking.VestigialGravity", name="phase_levels_distinct",
             priority=1, description="Three gravity levels are distinct phases", strategy_hint="constructive", filled=True),
    SorryGap(module="SKEFTHawking.VestigialGravity", name="phase_levels_ordered",
             priority=1, description="Phase levels form ordered hierarchy", strategy_hint="constructive", filled=True),
    SorryGap(module="SKEFTHawking.VestigialGravity", name="metric_dof_equals_gr",
             priority=1, description="Metric DOF count matches GR prediction", strategy_hint="native_decide", filled=True),
    SorryGap(module="SKEFTHawking.ChiralityWall", name="evading_one_breaks_nogo",
             priority=1, description="Evading one GS condition breaks the no-go", strategy_hint="constructive", filled=True),
    SorryGap(module="SKEFTHawking.ChiralityWall", name="tpf_evasion_margin",
             priority=1, description="TPF evasion margin quantified", strategy_hint="arithmetic", filled=True),
    SorryGap(module="SKEFTHawking.FractonNonAbelian", name="obstructions_individually_sufficient",
             priority=1, description="Each obstruction individually sufficient to block YM compatibility",
             strategy_hint="case analysis", filled=True),
    SorryGap(module="SKEFTHawking.FractonGravity", name="param_gap_grows",
             priority=1, description="Parameter gap grows with dimension", strategy_hint="monotonicity", filled=True),

    # Wave 5 quality audit — strengthened from vacuous conclusions (2026-03-26)
    SorryGap(module="SKEFTHawking.ChiralityWall", name="gs_nogo_requires_all",
             priority=1,
             description="GS no-go: applicable_count = 2 ∧ applicable_count < length. "
                         "Strengthened from vacuous `true` conclusion.",
             strategy_hint="native_decide on concrete gs_conditions list",
             filled=True),
    SorryGap(module="SKEFTHawking.SKDoubling", name="zeroTemp_nontrivial",
             priority=1,
             description="Dissipative action non-trivial at any T: ∃ f, 0 < Im(L(f)). "
                         "Strengthened from vacuous `True` conclusion.",
             strategy_hint="Witness ψ_a=1 gives Im = γ₁/β > 0 when γ₁ > 0. "
                           "Witness ∂_t ψ_a=1 gives Im = γ₂/β > 0 when γ₂ > 0. "
                           "Use div_pos.",
             filled=True),

    # Phase 5 Wave 1A — KappaScaling.lean
    SorryGap(module="SKEFTHawking.KappaScaling", name="kappa_scaling_dispersive_quadratic",
             priority=1,
             description="Dispersive correction factors as A·κ² with A = -(π/6)(ξ/c_s)²",
             strategy_hint="unfold dispersiveCorrection, ring",
             filled=True),
    SorryGap(module="SKEFTHawking.KappaScaling", name="kappa_scaling_dissipative_linear",
             priority=1,
             description="Dissipative correction factors as B·κ with B = (γ₁+γ₂)/c_s²",
             strategy_hint="unfold dissipativeCorrection, ring",
             filled=True),
    SorryGap(module="SKEFTHawking.KappaScaling", name="dispersive_nonpos",
             priority=1,
             description="Dispersive correction is non-positive for all κ",
             strategy_hint="unfold, mul_nonpos_of_nonpos_of_nonneg with pi_pos and sq_nonneg",
             filled=True),
    SorryGap(module="SKEFTHawking.KappaScaling", name="dissipative_nonneg",
             priority=1,
             description="Dissipative correction is non-negative for κ ≥ 0",
             strategy_hint="unfold, div_nonneg with add_nonneg, mul_nonneg, sq_nonneg",
             filled=True),
    SorryGap(module="SKEFTHawking.KappaScaling", name="dispersive_neg",
             priority=1,
             description="Dispersive correction is strictly negative for κ > 0",
             strategy_hint="unfold, mul_neg_of_neg_of_pos with pi_pos and sq_pos_of_pos",
             filled=True),
    SorryGap(module="SKEFTHawking.KappaScaling", name="crossover_nonneg",
             priority=1,
             description="Crossover kappa is non-negative",
             strategy_hint="unfold, div_nonneg with mul_nonneg, add_nonneg, sq_nonneg, pi_pos",
             filled=True),
    SorryGap(module="SKEFTHawking.KappaScaling", name="kappa_scaling_crossover_balance",
             priority=1,
             description="At κ_cross, |δ_disp| = δ_diss exactly — key prediction",
             strategy_hint="abs_of_nonpos, unfold, field_simp",
             filled=True),
    SorryGap(module="SKEFTHawking.KappaScaling", name="dissipative_dominates_below",
             priority=2,
             description="For κ < κ_cross, dissipative correction dominates",
             strategy_hint="abs_of_nonpos, div_lt_iff₀, field_simp, gcongr",
             filled=True),
    SorryGap(module="SKEFTHawking.KappaScaling", name="dispersive_dominates_above",
             priority=2,
             description="For κ > κ_cross, dispersive correction dominates",
             strategy_hint="abs_of_nonpos, div_lt_iff₀, ring_nf, nlinarith",
             filled=True),
    SorryGap(module="SKEFTHawking.KappaScaling", name="crossover_unique",
             priority=2,
             description="κ_cross is the unique positive value where corrections balance",
             strategy_hint="abs_of_nonpos, eq_div_iff, field_simp, mul_div_cancel_right₀",
             filled=True),

    # Phase 5 Wave 2A — SU2PseudoReality.lean (all manual, zero sorry)
    SorryGap(module="SKEFTHawking.SU2PseudoReality", name="one_link_factor_pos",
             priority=1,
             description="One-link integral factor 1/dim is positive",
             strategy_hint="div_pos one_pos Nat.cast_pos",
             filled=True),
    SorryGap(module="SKEFTHawking.SU2PseudoReality", name="su2_one_link_normalization",
             priority=1,
             description="SU(2) one-link factor equals 1/2",
             strategy_hint="unfold, rw, norm_num",
             filled=True),
    SorryGap(module="SKEFTHawking.SU2PseudoReality", name="effective_coupling_nonneg",
             priority=1,
             description="Effective coupling is non-negative",
             strategy_hint="div_nonneg with Nat.cast_nonneg",
             filled=True),
    SorryGap(module="SKEFTHawking.SU2PseudoReality", name="effective_coupling_positive",
             priority=1,
             description="Effective coupling is positive when g_EH > 0",
             strategy_hint="div_pos with Nat.cast_pos",
             filled=True),
    SorryGap(module="SKEFTHawking.SU2PseudoReality", name="effective_coupling_su2",
             priority=1,
             description="SU(2) effective coupling = g_EH/2",
             strategy_hint="unfold, rw, norm_num",
             filled=True),
    SorryGap(module="SKEFTHawking.SU2PseudoReality", name="lattice_volume_pos",
             priority=1,
             description="Lattice volume L² is positive for L > 0",
             strategy_hint="Nat.mul_pos",
             filled=True),
    SorryGap(module="SKEFTHawking.SU2PseudoReality", name="binder_cumulant_ordered_limit",
             priority=1,
             description="Binder cumulant = 2/3 in ordered phase (m⁴ = m²²)",
             strategy_hint="field_simp, ring",
             filled=True),
    SorryGap(module="SKEFTHawking.SU2PseudoReality", name="binder_cumulant_gaussian",
             priority=1,
             description="Binder cumulant = 0 for Gaussian fluctuations (m⁴ = 3m²²)",
             strategy_hint="field_simp, ring",
             filled=True),
    SorryGap(module="SKEFTHawking.SU2PseudoReality", name="free_energy_well_defined",
             priority=1,
             description="Free energy density is well-defined for V > 0",
             strategy_hint="rfl",
             filled=True),
    SorryGap(module="SKEFTHawking.SU2PseudoReality", name="free_energy_extensive",
             priority=1,
             description="Free energy is extensive: f·2V = -2·ln_Z",
             strategy_hint="field_simp",
             filled=True),

    # Phase 5 Wave 2B — FermionBag4D.lean (all manual, zero sorry)
    SorryGap(module="SKEFTHawking.FermionBag4D", name="so4_one_link_factor",
             priority=1,
             description="SO(4) one-link factor = 1/4",
             strategy_hint="subst; norm_num",
             filled=True),
    SorryGap(module="SKEFTHawking.FermionBag4D", name="so4_effective_coupling_pos",
             priority=1,
             description="Effective coupling positive when g_EH > 0",
             strategy_hint="div_pos",
             filled=True),
    SorryGap(module="SKEFTHawking.FermionBag4D", name="so4_effective_coupling_smaller",
             priority=1,
             description="SO(4) eff coupling < SU(2) eff coupling",
             strategy_hint="nlinarith",
             filled=True),
    SorryGap(module="SKEFTHawking.FermionBag4D", name="eight_fermion_weight_full_occ",
             priority=1,
             description="exp(-g_cosmo) > 0",
             strategy_hint="exp_pos",
             filled=True),
    SorryGap(module="SKEFTHawking.FermionBag4D", name="eight_fermion_weight_le_one",
             priority=1,
             description="exp(-g) ≤ 1 when g ≥ 0",
             strategy_hint="exp_le_exp_of_le",
             filled=True),
    SorryGap(module="SKEFTHawking.FermionBag4D", name="eight_fermion_weight_bounds",
             priority=1,
             description="0 < exp(-g) ≤ 1 for g ≥ 0",
             strategy_hint="And.intro",
             filled=True),
    SorryGap(module="SKEFTHawking.FermionBag4D", name="fermion_bag_weight_positive",
             priority=1,
             description="Product of positive weights is positive",
             strategy_hint="mul_pos",
             filled=True),
    SorryGap(module="SKEFTHawking.FermionBag4D", name="bond_weight_positive",
             priority=1,
             description="Bond weight exp(-g_eff * n) > 0",
             strategy_hint="exp_pos",
             filled=True),
    SorryGap(module="SKEFTHawking.FermionBag4D", name="metric_correlator_nonneg",
             priority=1,
             description="m4 - m2² ≥ 0 (Cauchy-Schwarz)",
             strategy_hint="linarith",
             filled=True),
    SorryGap(module="SKEFTHawking.FermionBag4D", name="vestigial_phase_splitting",
             priority=1,
             description="Metric Binder > tetrad Binder implies splitting",
             strategy_hint="linarith",
             filled=True),
    SorryGap(module="SKEFTHawking.FermionBag4D", name="vestigial_window_bounded",
             priority=1,
             description="Vestigial window bounded by scan range",
             strategy_hint="linarith",
             filled=True),
    SorryGap(module="SKEFTHawking.FermionBag4D", name="fermion_bag_weight_bounded",
             priority=1,
             description="Full bag weight positive and ≤ 1 (no sign problem)",
             strategy_hint="mul_pos, exp_le_exp_of_le",
             filled=True),
    SorryGap(module="SKEFTHawking.FermionBag4D", name="binder_cumulant_nonneg",
             priority=1,
             description="U_L ≥ 0 when m4 ≤ 3m2² (Cauchy-Schwarz)",
             strategy_hint="div_le_one, sub_nonneg",
             filled=True),
    SorryGap(module="SKEFTHawking.FermionBag4D", name="binder_cumulant_le_two_thirds",
             priority=1,
             description="U_L ≤ 2/3 when m4 ≥ m2² (Jensen)",
             strategy_hint="div_le_div_of_nonneg_right, field_simp",
             filled=True),
    SorryGap(module="SKEFTHawking.FermionBag4D", name="free_energy_extensive_4d",
             priority=1,
             description="Free energy extensivity in 4D",
             strategy_hint="field_simp",
             filled=True),
    SorryGap(module="SKEFTHawking.FermionBag4D", name="partition_function_log_finite",
             priority=1,
             description="Z > 0 implies ln(Z) exists",
             strategy_hint="exp_log",
             filled=True),

    # Phase 5 Wave 3A — LatticeHamiltonian.lean (7 sorry gaps)
    SorryGap(module="SKEFTHawking.LatticeHamiltonian", name="translation_invariant_double_shift",
             description="Double shift equals single: H(x+a+b) = H(x) from TranslationInvariant",
             priority=1,
             strategy_hint="Apply hti twice: H(x+a+b) = H((x+a)+b) = H(x+a) = H(x)",
             filled=True),
    SorryGap(module="SKEFTHawking.LatticeHamiltonian", name="finite_range_bloch_is_finite_sum",
             description="Finite range implies Bloch Hamiltonian is a finite sum",
             priority=1,
             strategy_hint="Unpack FiniteRange to get ∃ R, ... and provide it directly",
             filled=True),
    SorryGap(module="SKEFTHawking.LatticeHamiltonian", name="rotor_hilbert_not_finite_dim",
             description="ℓ²(ℤ,ℂ) is not finite-dimensional (TPF violates GS I3)",
             priority=1,
             strategy_hint="If FiniteDimensional, then ℤ is Finite (module basis finite), contradicting Int.infinite",
             filled=True),
    SorryGap(module="SKEFTHawking.LatticeHamiltonian", name="round_not_continuous_at_half",
             description="round(x) : ℝ → ℤ is discontinuous at x = 1/2 (TPF violates GS C1)",
             priority=2,
             strategy_hint="round(1/2)=1, but for ε>0 small, round(1/2-ε)=0, so |f(x)-f(1/2)|=1 for x arbitrarily close",
             filled=True),
    SorryGap(module="SKEFTHawking.LatticeHamiltonian", name="integers_not_finite",
             description="ℤ is not finite (supports rotor_hilbert_not_finite_dim)",
             priority=1,
             strategy_hint="The map ℕ → ℤ is injective and ℕ is infinite, or use Int.infinite",
             filled=True),
    SorryGap(module="SKEFTHawking.LatticeHamiltonian", name="hermitian_diagonal_real",
             description="Diagonal entries of Hermitian matrix are real: star(A_ii) = A_ii",
             priority=1,
             strategy_hint="From IsHermitian: star(A j i) = A i j. Set j = i.",
             filled=True),
    SorryGap(module="SKEFTHawking.LatticeHamiltonian", name="hermitian_trace_real",
             description="Trace of Hermitian matrix is real: star(tr A) = tr A",
             priority=1,
             strategy_hint="tr(A) = Σ A_ii. Each A_ii is real by hermitian_diagonal_real. Sum of reals is real.",
             filled=True),

    # Phase 5 Wave 3B — GoltermanShamir.lean (3 sorry gaps)
    SorryGap(module="SKEFTHawking.GoltermanShamir", name="tpf_violates_C2",
             description="TPF local dim exceeds any C2 finite dim: ∃ N > c.local_dim_finite",
             priority=1,
             strategy_hint="Use tpf.local_dim_unbounded c.local_dim_finite to get ∃ k > local_dim_finite",
             filled=True),
    SorryGap(module="SKEFTHawking.GoltermanShamir", name="tpf_outside_gs_scope",
             description="TPF dimension unbounded → exceeds any GSConditionsBundle.local_dim",
             priority=1,
             strategy_hint="Use tpf.local_dim_unbounded h.local_dim to get ∃ k > local_dim",
             filled=True),
    SorryGap(module="SKEFTHawking.GoltermanShamir", name="c1_implies_i2",
             description="C1_smooth_bloch includes FiniteRange, which is I2_local",
             priority=1,
             strategy_hint="C1_smooth_bloch M = TranslationInvariant ∧ FiniteRange. I2_local M = FiniteRange. Use h.2.",
             filled=True),
    # Phase 5 Wave 3B+ — GoltermanShamir.lean strengthening (3 sorry gaps)
    SorryGap(module="SKEFTHawking.GoltermanShamir", name="c2_fock_dim_power_of_two",
             description="C2 dim is 2^k ∧ 2^k ≥ 1 (strengthened from just dim ≥ 1)",
             priority=1,
             strategy_hint="obtain ⟨k, hk⟩ := c.is_fermionic; exact ⟨k, hk, by positivity⟩ or Nat.one_le_pow",
             filled=True),
    SorryGap(module="SKEFTHawking.GoltermanShamir", name="tpf_escapes_by_bosonic_and_infinite",
             description="TPF has bosonic_fields = true AND ∃ k > local_dim (synthesis)",
             priority=1,
             strategy_hint="exact ⟨tpf.bosonic_fields_present, tpf.local_dim_unbounded h.local_dim⟩",
             filled=True),
    SorryGap(module="SKEFTHawking.GoltermanShamir", name="tpf_bosonic_exceeds_fock",
             description="TPF bosonic ∧ dim=2^k ∧ ∃N>dim (all three load-bearing properties)",
             priority=1,
             strategy_hint="exact ⟨tpf.bosonic_fields_present, c.is_fermionic, tpf.local_dim_unbounded c.local_dim_finite⟩",
             filled=True),
    # Phase 5 Wave 3C — GoltermanShamir.lean condition strengthening (1 sorry gap)
    SorryGap(module="SKEFTHawking.GoltermanShamir", name="fock_space_finite_dim",
             description="ExteriorAlgebra ℂ (Fin k → ℂ) is Module.Finite — proved via graded decomposition + truncated direct sum",
             priority=3,
             strategy_hint="GradedAlgebra decomposition + ⋀^n V = 0 for n > finrank V + finite direct sum of finite modules",
             filled=True),
    # Phase 5 Wave 3C — TPFEvasion.lean (2 sorry gaps)
    SorryGap(module="SKEFTHawking.TPFEvasion", name="two_violations_proved",
             description="Conjunction of I3 and C1 violations: both already proved individually",
             priority=1,
             strategy_hint="exact ⟨violation_I3, violation_C1⟩",
             filled=True),
    SorryGap(module="SKEFTHawking.TPFEvasion", name="tpf_outside_gs_scope_main",
             description="Master conjunction: I3 ∧ ℤ_infinite ∧ C1 ∧ extra_dim ∧ nogo_fails",
             priority=1,
             strategy_hint="exact ⟨violation_I3, violation_Z_infinite, violation_C1, rfl, by norm_num⟩",
             filled=True),
    # Phase 5 Wave 4A — KLinearCategory.lean (4 sorry gaps → all filled)
    SorryGap(module="SKEFTHawking.KLinearCategory", name="tensor_preserves_nonzero",
             description="In rigid category with simple unit, tensoring preserves nonzero morphisms",
             priority=2, filled=True,
             strategy_hint="Use rigidity: apply evaluation/coevaluation to detect nonzero on one side"),
    SorryGap(module="SKEFTHawking.KLinearCategory", name="unit_totalDim_one",
             description="Unit object has multiplicity 1 in one simple class, 0 elsewhere",
             priority=2, filled=True,
             strategy_hint="Unit is simple → decomposition is a single copy of the unit class"),
    SorryGap(module="SKEFTHawking.KLinearCategory", name="simples_nonempty",
             description="Category with a simple object has nonempty simple index",
             priority=1, filled=True,
             strategy_hint="Use the hypothesis to exhibit an element"),
    SorryGap(module="SKEFTHawking.KLinearCategory", name="simple_indecomposable",
             description="Simple objects cannot decompose as nontrivial biproduct",
             priority=2, filled=True,
             strategy_hint="The biproduct inclusions are mono → one must be iso (simple), other zero"),
    # Phase 5 Wave 4A — SphericalCategory.lean (7 sorry gaps → all filled)
    SorryGap(module="SKEFTHawking.SphericalCategory", name="quantum_dim_unit",
             description="Quantum dimension of unit object is identity endomorphism",
             priority=1, filled=True,
             strategy_hint="Unfold quantumDim, use CategoricalTrace.tr_unit"),
    SorryGap(module="SKEFTHawking.SphericalCategory", name="quantum_dim_tensor",
             description="Quantum dimension is multiplicative: d(X⊗Y) = d(X)·d(Y)",
             priority=2, filled=True,
             strategy_hint="Use SphericalCategory.tr_tensor with f=id_X, g=id_Y"),
    SorryGap(module="SKEFTHawking.SphericalCategory", name="quantum_dim_dual",
             description="Quantum dimension of dual equals original: d(X*) = d(X)",
             priority=2, filled=True,
             strategy_hint="Use pivotal isomorphism + trace naturality"),
    SorryGap(module="SKEFTHawking.SphericalCategory", name="trace_smul",
             description="Trace of scalar multiple is scalar times trace",
             priority=1, filled=True,
             strategy_hint="Unfold trace, use linearity of composition"),
    SorryGap(module="SKEFTHawking.SphericalCategory", name="trace_zero",
             description="Trace of zero morphism is zero",
             priority=1, filled=True,
             strategy_hint="Follows from trace_smul with n=0, or directly from preadditive"),
    SorryGap(module="SKEFTHawking.SphericalCategory", name="double_mate_comp",
             description="Double adjoint mate is covariant: (f≫g)ᘁᘁ = fᘁᘁ≫gᘁᘁ",
             priority=1, filled=True,
             strategy_hint="Apply rightAdjointMate_comp twice, noting double contravariance"),
    SorryGap(module="SKEFTHawking.SphericalCategory", name="golden_ratio_eq",
             description="Golden ratio satisfies φ² = φ + 1 where φ = (1+√5)/2",
             priority=1, filled=True,
             strategy_hint="Expand (1+√5)²/4, use Real.sq_sqrt, field_simp, ring"),
    # Phase 5 Wave 4B — FusionExamples.lean (7 sorry gaps)
    SorryGap(module="SKEFTHawking.FusionExamples", name="vecZ2_assoc", filled=True,
             description="Associativity of ℤ/2 fusion rules: Σ_m N_{ij}^m N_{mk}^l = Σ_m N_{jk}^m N_{im}^l",
             priority=1,
             strategy_hint="Finite sum over ZMod 2, use decide or fin_cases"),
    SorryGap(module="SKEFTHawking.FusionExamples", name="vecZ3_assoc", filled=True,
             description="Associativity of ℤ/3 fusion rules",
             priority=1,
             strategy_hint="Finite sum over ZMod 3, use decide or fin_cases"),
    SorryGap(module="SKEFTHawking.FusionExamples", name="repS3_assoc", filled=True,
             description="Associativity of Rep(S₃) fusion rules",
             priority=1,
             strategy_hint="Finite sum over RepS3Simple (3 elements), use cases + simp"),
    SorryGap(module="SKEFTHawking.FusionExamples", name="fib_assoc", filled=True,
             description="Associativity of Fibonacci fusion rules",
             priority=1,
             strategy_hint="Finite sum over FibSimple (2 elements), use cases + simp"),
    SorryGap(module="SKEFTHawking.FusionExamples", name="fib_F_involutory", filled=True,
             description="Fibonacci F-matrix entries satisfy (1/φ)² + (1/√φ)² = 1",
             priority=1,
             strategy_hint="Use hφ2: φ²=φ+1, field_simp, Real.sq_sqrt"),
    SorryGap(module="SKEFTHawking.FusionExamples", name="fib_is_chiral", filled=True,
             description="Fibonacci central charge 14/5 is not a multiple of 8",
             priority=1,
             strategy_hint="norm_num on 14/5 mod 8"),
    SorryGap(module="SKEFTHawking.FusionExamples", name="fibonacci_dim_not_integer", filled=True,
             description="Golden ratio (1+√5)/2 is not an integer",
             priority=2,
             strategy_hint="Use irrationality of √5, or bound: 1 < φ < 2"),
    # Phase 5 Wave 4C — VecG.lean (6 sorry gaps)
    SorryGap(module="SKEFTHawking.VecG", name="day_unit_left", filled=True,
             description="Day convolution unit law: 𝟙 ⊗ V = V",
             priority=1,
             strategy_hint="Expand dayConvolution, dayUnit; sum collapses at g=1"),
    SorryGap(module="SKEFTHawking.VecG", name="day_unit_right", filled=True,
             description="Day convolution right unit: V ⊗ 𝟙 = V",
             priority=1,
             strategy_hint="Expand dayConvolution, dayUnit; use group inv properties"),
    SorryGap(module="SKEFTHawking.VecG", name="day_assoc", filled=True,
             description="Day convolution associativity",
             priority=2,
             strategy_hint="Both sides = Σ_{h₁h₂h₃=g} V_{h₁}·W_{h₂}·X_{h₃}; Fubini on finite sums"),
    SorryGap(module="SKEFTHawking.VecG", name="simple_tensor", filled=True,
             description="Tensor of simples: k_g ⊗ k_h = k_{gh}",
             priority=1,
             strategy_hint="Expand dayConvolution, simpleGraded; sum collapses to Kronecker"),
    SorryGap(module="SKEFTHawking.VecG", name="day_dim_multiplicative", filled=True,
             description="Total dim is multiplicative under Day convolution",
             priority=2,
             strategy_hint="Exchange sum order, factor; uses Finset.sum_mul_sum"),
    SorryGap(module="SKEFTHawking.VecG", name="simpleGraded_invertible", filled=True,
             description="k_g ⊗ k_{g⁻¹} = k_e = 𝟙",
             priority=1,
             strategy_hint="Follows from simple_tensor with h = g⁻¹"),
    # Phase 5 Wave 4C — DrinfeldDouble.lean (2 sorry gaps)
    SorryGap(module="SKEFTHawking.DrinfeldDouble", name="ddMul_one_left", filled=True,
             description="D(G) left unit: 1 · a = a",
             priority=1,
             strategy_hint="Expand ddMul, ddOne, conjAction; simp with one_mul, mul_one"),
    SorryGap(module="SKEFTHawking.DrinfeldDouble", name="ddMul_one_right", filled=True,
             description="D(G) right unit: a · 1 = a",
             priority=1,
             strategy_hint="Expand ddMul, ddOne, conjAction; simp with mul_one, inv_one"),
    # Phase 5 Section 9C — SO4Weingarten.lean (15 sorry gaps, rewritten for Aristotle)
    SorryGap(module="SKEFTHawking.SO4Weingarten", name="weingarten_2nd_factor", filled=True,
             description="0 < 1/4 (SO(4) second-moment factor positive)",
             priority=1, strategy_hint="norm_num"),
    SorryGap(module="SKEFTHawking.SO4Weingarten", name="weingarten_2nd_so4", filled=True,
             description="1/4 = 1/4 (identity)",
             priority=1, strategy_hint="rfl"),
    SorryGap(module="SKEFTHawking.SO4Weingarten", name="weingarten_4th_so4_pair", filled=True,
             description="1/72 > 0",
             priority=1, strategy_hint="norm_num"),
    SorryGap(module="SKEFTHawking.SO4Weingarten", name="weingarten_epsilon_so4", filled=True,
             description="1/24 > 0",
             priority=1, strategy_hint="norm_num"),
    SorryGap(module="SKEFTHawking.SO4Weingarten", name="adjoint_channel_suppressed", filled=True,
             description="1/72 < 1/4 (adjoint suppressed vs fundamental)",
             priority=1, strategy_hint="norm_num"),
    SorryGap(module="SKEFTHawking.SO4Weingarten", name="fundamental_channel_nonneg", filled=True,
             description="(1/4)(n_x/N)(n_y/N) >= 0 for non-negative inputs",
             priority=1, strategy_hint="mul_nonneg, div_nonneg"),
    SorryGap(module="SKEFTHawking.SO4Weingarten", name="adjoint_channel_nonneg", filled=True,
             description="(1/24)(n_x/N)^2(n_y/N)^2 >= 0 for non-negative inputs",
             priority=1, strategy_hint="mul_nonneg, sq_nonneg"),
    SorryGap(module="SKEFTHawking.SO4Weingarten", name="total_bond_nonneg", filled=True,
             description="Sum of fundamental + adjoint channels >= 0",
             priority=1, strategy_hint="add_nonneg from component nonnegativity"),
    SorryGap(module="SKEFTHawking.SO4Weingarten", name="attractive_bond_action_nonpos", filled=True,
             description="g * (nonneg sum) <= 0 when g <= 0",
             priority=1, strategy_hint="mul_nonpos_of_nonpos_of_nonneg"),
    SorryGap(module="SKEFTHawking.SO4Weingarten", name="so4_fundamental_dim", filled=True,
             description="2 * 2 = 4",
             priority=2, strategy_hint="norm_num"),
    SorryGap(module="SKEFTHawking.SO4Weingarten", name="so4_tensor_product_decomp", filled=True,
             description="1 + 3 + 3 + 9 = 16",
             priority=2, strategy_hint="norm_num"),
    SorryGap(module="SKEFTHawking.SO4Weingarten", name="planck_nonneg", filled=True,
             description="1/(exp(x)-1) > 0 for x > 0",
             priority=2, strategy_hint="exp_pos, sub_pos, div_pos"),
    SorryGap(module="SKEFTHawking.SO4Weingarten", name="exp_gt_one_of_pos", filled=True,
             description="exp(x) > 1 for x > 0",
             priority=2, strategy_hint="Real.add_one_le_exp, or exp_pos + monotonicity"),
    SorryGap(module="SKEFTHawking.SO4Weingarten", name="planck_monotone", filled=True,
             description="1/(exp(x2)-1) < 1/(exp(x1)-1) when x1 < x2",
             priority=2, strategy_hint="exp monotone → denominator larger → fraction smaller"),
    # Phase 5 Section 9C-1 — FractonFormulas.lean (45 gaps — ALL FILLED by Aristotle 4528aa2b)
    SorryGap(module="SKEFTHawking.FractonFormulas", name="symmetric_tensor_components", filled=True, description="C(n+d-1,n) = C(n+d-1,d-1)", priority=2, strategy_hint="Nat.choose_symm_diff"),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="charge_scalar_one_component", filled=True, description="C(d-1,0)=1", priority=2, strategy_hint="Nat.choose_zero_right"),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="dipole_d_components", filled=True, description="C(d,1)=d", priority=2, strategy_hint="Nat.choose_one_right"),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="quadrupole_3d_six_components", filled=True, description="C(4,2)=6", priority=2, strategy_hint="decide"),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="hockey_stick_charge_count", filled=True, description="Hockey Stick identity for charge counting", priority=1, strategy_hint="induction on N"),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="charge_count_at_least_linear", filled=True, description="C(N+d,d) >= N+1", priority=1, strategy_hint=""),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="total_conserved_with_momentum_energy", filled=True, description="Total charges > standard hydro", priority=1, strategy_hint=""),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="dipole_quadratic_dispersion", filled=True, description="dispersion_power 1 = 2", priority=2, strategy_hint="rfl"),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="dipole_k4_damping", filled=True, description="damping_power 1 = 4", priority=2, strategy_hint="rfl"),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="standard_linear_dispersion", filled=True, description="dispersion_power 0 = 1", priority=2, strategy_hint="rfl"),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="damping_twice_dispersion", filled=True, description="damping = 2 * dispersion", priority=2, strategy_hint="ring"),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="dispersion_power_strict_mono", filled=True, description="Higher multipole → slower dynamics", priority=2, strategy_hint="omega"),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="subdiffusive_relaxation", filled=True, description="Relaxation ~ lambda^{2(n+1)}", priority=2, strategy_hint="ring"),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="ucd_standard", filled=True, description="d_c(0) = 2", priority=2, strategy_hint="decide"),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="ucd_dipole", filled=True, description="d_c(1) = 2", priority=2, strategy_hint="decide"),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="ucd_quadrupole", filled=True, description="d_c(2) = 6", priority=2, strategy_hint="decide"),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="ucd_unbounded", filled=True, description="d_c grows without bound", priority=1, strategy_hint=""),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="ucd_grows_even", filled=True, description="d_c monotone for even n >= 2", priority=2, strategy_hint=""),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="transport_count_total", filled=True, description="4+2+4=10 transport params", priority=2, strategy_hint="norm_num"),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="positivity_constrains_dissipative", filled=True, description="Positivity constrains 4 of 10", priority=2, strategy_hint=""),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="retention_ratio_exceeds_one", filled=True, description="Fracton retains more than standard", priority=1, strategy_hint=""),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="retention_ratio_diverges", filled=True, description="Retention ratio diverges with N", priority=1, strategy_hint=""),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="fragmentation_bits_positive", filled=True, description="Fragmentation bits > 0", priority=1, strategy_hint=""),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="standard_hydro_info_constant", filled=True, description="Standard hydro info = d+2", priority=2, strategy_hint=""),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="xcube_grows_linearly", filled=True, description="X-Cube: 6L-3 logical qubits", priority=2, strategy_hint="ring"),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="fragmentation_dominates_standard_1d", filled=True, description="Fragmentation > standard in 1D", priority=2, strategy_hint=""),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="fracton_dof_4d_spacetime", filled=True, description="Fracton DOF in 4D = 8", priority=2, strategy_hint="decide"),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="graviton_dof_4d_is_2", filled=True, description="Graviton DOF in 4D = 2", priority=2, strategy_hint="decide"),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="extra_dof_4d", filled=True, description="Extra DOF = 8-2 = 6", priority=2, strategy_hint="norm_num"),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="dof_gap_equals_d_minus_1", filled=True, description="DOF gap = d-1", priority=2, strategy_hint=""),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="dof_gap_always_positive", filled=True, description="DOF gap > 0 for d >= 2", priority=1, strategy_hint="omega"),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="bootstrap_diverges_all_high_orders", filled=True, description="Bootstrap diverges for order >= 2", priority=1, strategy_hint=""),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="five_bootstrap_obstructions", filled=True, description="5 obstructions", priority=2, strategy_hint="decide"),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="bootstrap_gap_is_structural", filled=True, description=">= 3 independent obstructions", priority=2, strategy_hint=""),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="spin1_instability_at_cubic", filled=True, description="Spin-1 instability", priority=2, strategy_hint=""),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="commutator_order_mismatch", filled=True, description="Commutator order mismatch", priority=1, strategy_hint=""),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="commutator_order_ratio", filled=True, description="Ratio = 2", priority=2, strategy_hint=""),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="param_gap_quadratic_growth", filled=True, description="Param gap quadratic in N", priority=2, strategy_hint=""),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="param_mismatch_general", filled=True, description="SU(N) params > fracton for N >= 2", priority=1, strategy_hint=""),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="ym_four_independent_obstructions", filled=True, description="4 independent YM obstructions", priority=2, strategy_hint=""),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="no_fracton_ym_compatibility", filled=True, description="No fracton-YM compatibility", priority=1, strategy_hint=""),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="wxy_scalar_not_vector", filled=True, description="WXY scalar not vector", priority=2, strategy_hint=""),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="dispersion_matches_charge_scaling", filled=True, description="Cross-check: dispersion matches FractonHydro", priority=2, strategy_hint=""),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="dof_gap_cross_check", filled=True, description="Cross-check: DOF gap matches FractonGravity", priority=2, strategy_hint=""),
    SorryGap(module="SKEFTHawking.FractonFormulas", name="obstruction_counts_distinct", filled=True, description="Cross-check: obstruction count matches FractonNonAbelian", priority=2, strategy_hint=""),
    # Phase 5 Section 9C-3 — WetterichNJL.lean (18 gaps — ALL FILLED by Aristotle 4528aa2b)
    SorryGap(module="SKEFTHawking.WetterichNJL", name="fierz_completeness", filled=True, description="1+1+4+4+6=16", priority=2, strategy_hint="norm_num"),
    SorryGap(module="SKEFTHawking.WetterichNJL", name="fierz_equals_spinor_sq", filled=True, description="16 = 4^2", priority=2, strategy_hint="norm_num"),
    SorryGap(module="SKEFTHawking.WetterichNJL", name="fierz_channel_count", filled=True, description="5 Fierz channels", priority=2, strategy_hint="decide"),
    SorryGap(module="SKEFTHawking.WetterichNJL", name="fierz_channel_dims_positive", filled=True, description="All channel dims > 0", priority=1, strategy_hint="decide"),
    SorryGap(module="SKEFTHawking.WetterichNJL", name="njl_scalar_nonneg", filled=True, description="Scalar channel >= 0 for g >= 0", priority=1, strategy_hint="positivity"),
    SorryGap(module="SKEFTHawking.WetterichNJL", name="njl_scalar_monotone", filled=True, description="Scalar monotone in occupation", priority=2, strategy_hint=""),
    SorryGap(module="SKEFTHawking.WetterichNJL", name="njl_scalar_upper_bound", filled=True, description="Scalar <= g for f in [0,1]", priority=2, strategy_hint=""),
    SorryGap(module="SKEFTHawking.WetterichNJL", name="njl_pseudoscalar_half_filling_zero", filled=True, description="Pseudoscalar vanishes at half-filling", priority=2, strategy_hint="ring"),
    SorryGap(module="SKEFTHawking.WetterichNJL", name="chirality_factor_bounded", filled=True, description="|1-2f| <= 1 for f in [0,1]", priority=2, strategy_hint="abs_le"),
    SorryGap(module="SKEFTHawking.WetterichNJL", name="njl_pseudoscalar_sign_at_empty", filled=True, description="Pseudoscalar at empty = -g", priority=2, strategy_hint="ring"),
    SorryGap(module="SKEFTHawking.WetterichNJL", name="njl_bond_weight_decomposition", filled=True, description="Total = scalar + pseudoscalar", priority=2, strategy_hint="ring"),
    SorryGap(module="SKEFTHawking.WetterichNJL", name="njl_total_at_half_filling", filled=True, description="Total at half-filling = g/4", priority=2, strategy_hint="ring"),
    SorryGap(module="SKEFTHawking.WetterichNJL", name="njl_bond_weight_symmetric", filled=True, description="S(n_x,n_y) = S(n_y,n_x)", priority=2, strategy_hint="ring"),
    SorryGap(module="SKEFTHawking.WetterichNJL", name="njl_vector_nonneg", filled=True, description="Vector channel >= 0 for f in [0,1]", priority=1, strategy_hint="positivity"),
    SorryGap(module="SKEFTHawking.WetterichNJL", name="vector_variance_bound", filled=True, description="f(1-f) <= 1/4", priority=2, strategy_hint="nlinarith [sq_nonneg (f - 1/2)]"),
    SorryGap(module="SKEFTHawking.WetterichNJL", name="njl_adw_correspondence", filled=True, description="NJL scalar limit matches ADW g_eff", priority=2, strategy_hint="ring"),
    SorryGap(module="SKEFTHawking.WetterichNJL", name="njl_adw_positivity", filled=True, description="NJL→ADW preserves positivity", priority=1, strategy_hint=""),
    SorryGap(module="SKEFTHawking.WetterichNJL", name="njl_to_g_EH", filled=True, description="g_EH = 16 * g_njl", priority=2, strategy_hint="ring"),

    # Phase 5 Wave 6 — VestigialSusceptibility.lean (16 gaps — ALL FILLED by Aristotle 9e2251cd)
    SorryGap(module="SKEFTHawking.VestigialSusceptibility", name="gamma_trace_metric_positive", filled=True, description="4×2 > 0", priority=1, strategy_hint="norm_num"),
    SorryGap(module="SKEFTHawking.VestigialSusceptibility", name="gamma_trace_lorentz_negative", filled=True, description="4×(-1) < 0", priority=1, strategy_hint="norm_num"),
    SorryGap(module="SKEFTHawking.VestigialSusceptibility", name="metric_dominates_lorentz", filled=True, description="8 > |−4|", priority=1, strategy_hint="grind +revert"),
    SorryGap(module="SKEFTHawking.VestigialSusceptibility", name="u_g_positive", filled=True, description="u_g > 0 from positive factors", priority=2, strategy_hint="positivity"),
    SorryGap(module="SKEFTHawking.VestigialSusceptibility", name="u_g_positive_adw", filled=True, description="u_g > 0 for N_f=2, D=4", priority=2, strategy_hint="norm_num + log_pos"),
    SorryGap(module="SKEFTHawking.VestigialSusceptibility", name="bubble_integral_monotone", filled=True, description="Π₀ decreasing in r_e", priority=2, strategy_hint="log monotone"),
    SorryGap(module="SKEFTHawking.VestigialSusceptibility", name="bubble_integral_diverges", filled=True, description="Π₀ → ∞ as r_e → 0⁺", priority=3, strategy_hint="filter tendsto composition"),
    SorryGap(module="SKEFTHawking.VestigialSusceptibility", name="bubble_integral_positive", filled=True, description="Π₀ > 0 when r_e < Λ²/e", priority=2, strategy_hint="log_pos + div_pos"),
    SorryGap(module="SKEFTHawking.VestigialSusceptibility", name="susceptibility_diverges", filled=True, description="∃ r_e* with χ_g⁻¹ = 0 (IVT)", priority=3, strategy_hint="constructive witness"),
    SorryGap(module="SKEFTHawking.VestigialSusceptibility", name="vestigial_before_tetrad", filled=True, description="G_ves < G_c when u_g > 0", priority=2, strategy_hint="div_lt + add_pos"),
    SorryGap(module="SKEFTHawking.VestigialSusceptibility", name="vestigial_r_e_star_pos", filled=True, description="r_e* > 0", priority=1, strategy_hint="mul_pos + exp_pos"),
    SorryGap(module="SKEFTHawking.VestigialSusceptibility", name="vestigial_window_exponential", filled=True, description="smaller u_g → smaller r_e*", priority=2, strategy_hint="exp monotonicity"),
    SorryGap(module="SKEFTHawking.VestigialSusceptibility", name="vestigial_window_vanishes", filled=True, description="r_e* → 0 as u_g → 0⁺", priority=3, strategy_hint="exp∘(−∞) → 0"),
    SorryGap(module="SKEFTHawking.VestigialSusceptibility", name="trace_channel_multiplicity", filled=True, description="2×4² = 32", priority=1, strategy_hint="norm_num"),
    SorryGap(module="SKEFTHawking.VestigialSusceptibility", name="traceless_channel_multiplicity", filled=True, description="2×4 = 8", priority=1, strategy_hint="norm_num"),
    SorryGap(module="SKEFTHawking.VestigialSusceptibility", name="vestigial_ordering_sufficient", filled=True, description="u_g > 0 suffices for vestigial ordering", priority=2, strategy_hint="vestigial_r_e_star_pos + div_lt"),

    # Phase 5 Wave 7A — QuaternionGauge.lean (10 gaps — ALL FILLED by Aristotle fb657b4d)
    SorryGap(module="SKEFTHawking.QuaternionGauge", name="quaternion_norm_mul", filled=True, description="unit quaternion product has unit norm", priority=2, strategy_hint="nlinarith + h1 h2"),
    SorryGap(module="SKEFTHawking.QuaternionGauge", name="quaternion_left_identity", filled=True, description="(1,0,0,0) is left identity", priority=1, strategy_hint="ring"),
    SorryGap(module="SKEFTHawking.QuaternionGauge", name="quaternion_conjugate_inverse", filled=True, description="q·q* = 1 for unit q", priority=2, strategy_hint="nlinarith + h"),
    SorryGap(module="SKEFTHawking.QuaternionGauge", name="so4_dimension", filled=True, description="dim SO(4) = 6", priority=1, strategy_hint="norm_num"),
    SorryGap(module="SKEFTHawking.QuaternionGauge", name="su2_su2_dimension", filled=True, description="3+3=6", priority=1, strategy_hint="norm_num"),
    SorryGap(module="SKEFTHawking.QuaternionGauge", name="plaquette_trace_bound", filled=True, description="|Tr(U_P)/4| ≤ 1", priority=1, strategy_hint="abs_div + abs_le"),
    SorryGap(module="SKEFTHawking.QuaternionGauge", name="plaquette_action_nonneg", filled=True, description="1 - Tr/4 ≥ 0", priority=1, strategy_hint="linarith"),
    SorryGap(module="SKEFTHawking.QuaternionGauge", name="plaquette_action_identity", filled=True, description="S_P = 0 at identity", priority=1, strategy_hint="norm_num"),
    SorryGap(module="SKEFTHawking.QuaternionGauge", name="heatbath_weight_integrable", filled=True, description="exp(cx)√(1-x²) ≥ 0", priority=1, strategy_hint="mul_nonneg + exp_nonneg + sqrt_nonneg"),
    SorryGap(module="SKEFTHawking.QuaternionGauge", name="heatbath_detailed_balance", filled=True, description="π(q)·P(q→q') symmetric", priority=1, strategy_hint="field_simp + ring"),

    # Phase 5 Wave 7B — GaugeFermionBag.lean (9 gaps — ALL FILLED by Aristotle fb657b4d)
    SorryGap(module="SKEFTHawking.GaugeFermionBag", name="tetrad_gauge_covariant", filled=True, description="E transforms with Ω", priority=2, strategy_hint="field_simp + ring"),
    SorryGap(module="SKEFTHawking.GaugeFermionBag", name="metric_gauge_invariant", filled=True, description="(-E)² = E²", priority=1, strategy_hint="ring"),
    SorryGap(module="SKEFTHawking.GaugeFermionBag", name="metric_from_tetrad_sq", filled=True, description="E² ≥ 0", priority=1, strategy_hint="sq_nonneg"),
    SorryGap(module="SKEFTHawking.GaugeFermionBag", name="bag_weight_real", filled=True, description="det ∈ ℝ (trivial)", priority=1, strategy_hint="rfl"),
    SorryGap(module="SKEFTHawking.GaugeFermionBag", name="determinant_rank1_update", filled=True, description="det ratio formula", priority=1, strategy_hint="field_simp"),
    SorryGap(module="SKEFTHawking.GaugeFermionBag", name="vestigial_implies_nonzero_variance", filled=True, description="⟨E²⟩>0, ⟨E⟩=0 → Var>0", priority=1, strategy_hint="linarith + h_tetrad"),
    SorryGap(module="SKEFTHawking.GaugeFermionBag", name="metric_nonneg", filled=True, description="Σ E_a² ≥ 0", priority=1, strategy_hint="positivity"),
    SorryGap(module="SKEFTHawking.GaugeFermionBag", name="binder_gaussian", filled=True, description="U₄ = 0 at Gaussian", priority=1, strategy_hint="field_simp"),
    SorryGap(module="SKEFTHawking.GaugeFermionBag", name="binder_ordered", filled=True, description="U₄ = 2/3 at ordered", priority=1, strategy_hint="field_simp + norm_num"),
    # Wave 7B-fix: Vector Binder cumulant for d-component order parameters
    SorryGap(
        module="SKEFTHawking.MajoranaKramers",
        name="binder_vector_gaussian",
        priority=1,
        description="Vector Binder U₄ = 0 for d-component Gaussian: m4 = (1+2/d)*m2²",
        strategy_hint="unfold binderCumulantVector; field_simp; ring",
        filled=True,  # Filled by Aristotle run cc257137 (2026-04-01)
    ),
    SorryGap(
        module="SKEFTHawking.MajoranaKramers",
        name="binder_vector_ordered",
        priority=1,
        description="Vector Binder U₄ = 2/(d+2) in ordered phase: m4 = m2²",
        strategy_hint="unfold binderCumulantVector; field_simp; ring",
        filled=True,  # Filled by Aristotle run cc257137 (2026-04-01)
    ),
    # HubbardStratonovichRHMC.lean — 22 theorems, all manual proofs (2026-04-02)
    SorryGap(
        module="SKEFTHawking.HubbardStratonovichRHMC",
        name="hs_gaussian_identity_zero",
        priority=1,
        description="HS field at identity gives zero action contribution",
        strategy_hint="simp [hsGaussianAction]",
        filled=True,  # Manual proof (2026-04-02)
    ),
    SorryGap(
        module="SKEFTHawking.HubbardStratonovichRHMC",
        name="hs_gaussian_action_nonneg",
        priority=1,
        description="HS Gaussian action S[φ] ≥ 0 for all field configurations",
        strategy_hint="positivity",
        filled=True,  # Manual proof (2026-04-02)
    ),
    SorryGap(
        module="SKEFTHawking.HubbardStratonovichRHMC",
        name="su2_closed_form_exp",
        priority=1,
        description="SU(2) matrix exponential in closed form via quaternions",
        strategy_hint="ext <;> simp [Matrix.mul_apply]",
        filled=True,  # Manual proof (2026-04-02)
    ),
    SorryGap(
        module="SKEFTHawking.HubbardStratonovichRHMC",
        name="su2_exp_unit_quaternion_identity",
        priority=1,
        description="exp(iθ·σ) produces unit quaternion: det = 1",
        strategy_hint="simp [det_fin_two]; ring",
        filled=True,  # Manual proof (2026-04-02)
    ),
    SorryGap(
        module="SKEFTHawking.HubbardStratonovichRHMC",
        name="omelyan_second_order_symplectic",
        priority=1,
        description="Omelyan 2MN integrator is second-order symplectic",
        strategy_hint="unfold omelyanStep; ring",
        filled=True,  # Manual proof (2026-04-02)
    ),
    SorryGap(
        module="SKEFTHawking.HubbardStratonovichRHMC",
        name="omelyan_time_reversible",
        priority=1,
        description="Omelyan integrator satisfies time-reversal symmetry",
        strategy_hint="simp [omelyanStep, Function.comp]",
        filled=True,  # Manual proof (2026-04-02)
    ),
    SorryGap(
        module="SKEFTHawking.HubbardStratonovichRHMC",
        name="zolotarev_exponential_convergence",
        priority=1,
        description="Zolotarev rational approximation converges exponentially in degree",
        strategy_hint="exact zolotarev_error_bound",
        filled=True,  # Manual proof (2026-04-02)
    ),
    SorryGap(
        module="SKEFTHawking.HubbardStratonovichRHMC",
        name="partial_fraction_positivity",
        priority=1,
        description="Zolotarev partial fraction coefficients are all positive",
        strategy_hint="positivity",
        filled=True,  # Manual proof (2026-04-02)
    ),
    SorryGap(
        module="SKEFTHawking.HubbardStratonovichRHMC",
        name="rhmc_hamiltonian_nonneg",
        priority=1,
        description="RHMC Hamiltonian H(U,π,φ) ≥ 0",
        strategy_hint="positivity",
        filled=True,  # Manual proof (2026-04-02)
    ),
    SorryGap(
        module="SKEFTHawking.HubbardStratonovichRHMC",
        name="rhmc_detailed_balance",
        priority=1,
        description="RHMC Metropolis step satisfies detailed balance",
        strategy_hint="exact detailed_balance_of_metropolis",
        filled=True,  # Manual proof (2026-04-02)
    ),
    SorryGap(
        module="SKEFTHawking.HubbardStratonovichRHMC",
        name="hs_fermion_matrix_antisymmetric",
        priority=1,
        description="HS-transformed fermion matrix A is antisymmetric",
        strategy_hint="ext <;> simp [Matrix.transpose_apply]",
        filled=True,  # Manual proof (2026-04-02)
    ),
    SorryGap(
        module="SKEFTHawking.HubbardStratonovichRHMC",
        name="kramers_holds_hs_matrix",
        priority=1,
        description="Kramers degeneracy holds for HS fermion matrix",
        strategy_hint="exact kramers_of_antisymmetric",
        filled=True,  # Manual proof (2026-04-02)
    ),
    SorryGap(
        module="SKEFTHawking.HubbardStratonovichRHMC",
        name="multishift_cg_shared_krylov",
        priority=1,
        description="Multi-shift CG shares single Krylov subspace across all shifts",
        strategy_hint="induction n <;> simp",
        filled=True,  # Manual proof (2026-04-02)
    ),
    SorryGap(
        module="SKEFTHawking.HubbardStratonovichRHMC",
        name="bipartite_nearest_neighbor_zero_diagonal",
        priority=1,
        description="On bipartite graph, nearest-neighbor antisymmetric A has D_ee=D_oo=0",
        strategy_hint="constructor <;> assumption",
        filled=True,  # Manual proof (2026-04-02)
    ),
    SorryGap(
        module="SKEFTHawking.HubbardStratonovichRHMC",
        name="ata_block_diag",
        priority=1,
        description="A†A block-diagonalizes: even block = M·Mᵀ, odd block = Mᵀ·M",
        strategy_hint="constructor <;> assumption",
        filled=True,  # Manual proof (2026-04-02)
    ),
    SorryGap(
        module="SKEFTHawking.HubbardStratonovichRHMC",
        name="even_odd_spectrum_identical",
        priority=1,
        description="σ(M·Mᵀ) = σ(Mᵀ·M): κ unchanged by even-odd decomposition",
        strategy_hint="rw [h_max, h_min]",
        filled=True,  # Manual proof (2026-04-02)
    ),
    SorryGap(
        module="SKEFTHawking.HubbardStratonovichRHMC",
        name="even_odd_cg_equivalence",
        priority=1,
        description="CG on (M·Mᵀ+σ)ψ_e=φ_e produces correct even-sector solution",
        strategy_hint="exact h_solve",
        filled=True,  # Manual proof (2026-04-02)
    ),
    SorryGap(
        module="SKEFTHawking.HubbardStratonovichRHMC",
        name="multishift_krylov_shift_invariance",
        priority=1,
        description="K_n(A+σI,b) = K_n(A,b): Krylov subspace shift-invariance",
        strategy_hint="ring",
        filled=True,  # Manual proof (2026-04-02)
    ),
    SorryGap(
        module="SKEFTHawking.HubbardStratonovichRHMC",
        name="multishift_residual_collinearity",
        priority=2,
        description="ζ recurrence preserves r_k = ζ_k·r collinearity across CG iterations",
        strategy_hint="split_ifs <;> [simp; field_simp]",
        filled=True,  # Manual proof (2026-04-02)
    ),
    SorryGap(
        module="SKEFTHawking.HubbardStratonovichRHMC",
        name="even_odd_force_equivalence",
        priority=1,
        description="Force from even-sector CG solutions equals full-lattice force",
        strategy_hint="exact h_equiv",
        filled=True,  # Manual proof (2026-04-02)
    ),
    SorryGap(
        module="SKEFTHawking.HubbardStratonovichRHMC",
        name="complex_pseudofermion_pfaffian",
        priority=1,
        description="Complex pseudofermion integral reproduces Pfaffian: ∫dφ e^{-φ†(A†A)^{-1/2}φ} = Pf(A)",
        strategy_hint="exact pfaffian_gaussian_integral",
        filled=True,  # Manual proof (2026-04-02)
    ),
    SorryGap(
        module="SKEFTHawking.HubbardStratonovichRHMC",
        name="heatbath_a_trick_covariance",
        priority=1,
        description="Heat-bath A-trick produces correct covariance: ⟨φφ†⟩ = (A†A)^{1/2}",
        strategy_hint="exact heatbath_covariance_eq",
        filled=True,  # Manual proof (2026-04-02)
    ),
    # Phase 5a Wave 1A: OnsagerAlgebra.lean
    SorryGap(
        module="SKEFTHawking.OnsagerAlgebra",
        name="davies_G_antisymmetry",
        priority=1,
        description="G_{m-n} = -G_{n-m}: antisymmetry of G generators from Lie bracket antisymmetry and Davies AA relation",
        strategy_hint="Rewrite using AA_comm to express both sides as Lie brackets, then use lie_skew and smul injectivity",
        filled=True,  # Aristotle run 9d6f2432 (2026-04-03)
    ),
    # Phase 5a Wave 1B: OnsagerContraction.lean
    SorryGap(
        module="SKEFTHawking.OnsagerContraction",
        name="contraction_rescaling",
        priority=1,
        description="[ε·A_m, ε·A_n] = ε²·4·G_{m-n}: bilinearity of Lie bracket + Davies AA relation",
        strategy_hint="Use smul_lie and lie_smul to factor out ε, then rewrite with AA_comm and simplify ε·ε = ε²",
        filled=True,
    ),
    SorryGap(
        module="SKEFTHawking.OnsagerContraction",
        name="contraction_GG_still_zero",
        priority=1,
        description="[ε²·G_m, ε²·G_n] = 0: bilinearity + abelian G-subalgebra",
        strategy_hint="Use smul_lie and lie_smul to factor out ε², then rewrite with GG_comm and smul_zero",
        filled=True,
    ),
    # Phase 5a Wave 2A: PauliMatrices.lean
    SorryGap(
        module="SKEFTHawking.PauliMatrices",
        name="σ_x_sq",
        priority=1,
        description="σ_x² = 1: 2x2 matrix identity [[0,1],[1,0]]² = I",
        strategy_hint="ext i j; fin_cases i <;> fin_cases j <;> simp [σ_x, mul_apply, Fin.sum_univ_two]",
        filled=True,
    ),
    SorryGap(
        module="SKEFTHawking.PauliMatrices",
        name="σ_z_sq",
        priority=1,
        description="σ_z² = 1: 2x2 matrix identity [[1,0],[0,-1]]² = I",
        strategy_hint="ext i j; fin_cases i <;> fin_cases j <;> simp [σ_z, mul_apply, Fin.sum_univ_two]",
        filled=True,
    ),
    SorryGap(
        module="SKEFTHawking.PauliMatrices",
        name="σ_y_sq",
        priority=1,
        description="σ_y² = 1: 2x2 matrix identity [[0,-i],[i,0]]² = I",
        strategy_hint="ext i j; fin_cases i <;> fin_cases j <;> simp [σ_y, mul_apply, Fin.sum_univ_two, Complex.I_sq]",
        filled=True,
    ),
    SorryGap(
        module="SKEFTHawking.PauliMatrices",
        name="comm_σ_x_σ_y",
        priority=1,
        description="[σ_x, σ_y] = 2i·σ_z: Pauli commutation relation",
        strategy_hint="ext i j; fin_cases i <;> fin_cases j <;> simp [σ_x, σ_y, σ_z, mul_apply, Fin.sum_univ_two]; ring",
        filled=True,
    ),
    SorryGap(
        module="SKEFTHawking.PauliMatrices",
        name="comm_σ_y_σ_z",
        priority=1,
        description="[σ_y, σ_z] = 2i·σ_x: Pauli commutation relation",
        strategy_hint="ext i j; fin_cases i <;> fin_cases j <;> simp [σ_y, σ_z, σ_x, mul_apply, Fin.sum_univ_two]; ring",
        filled=True,
    ),
    SorryGap(
        module="SKEFTHawking.PauliMatrices",
        name="comm_σ_z_σ_x",
        priority=1,
        description="[σ_z, σ_x] = 2i·σ_y: Pauli commutation relation — key for GT [H, Q_A] = 0",
        strategy_hint="ext i j; fin_cases i <;> fin_cases j <;> simp [σ_z, σ_x, σ_y, mul_apply, Fin.sum_univ_two]; ring",
        filled=True,
    ),
    SorryGap(
        module="SKEFTHawking.PauliMatrices",
        name="anticomm_σ_x_σ_z",
        priority=1,
        description="{σ_x, σ_z} = 0: Pauli anti-commutation",
        strategy_hint="ext i j; fin_cases i <;> fin_cases j <;> simp [σ_x, σ_z, mul_apply, Fin.sum_univ_two]; ring",
        filled=True,
    ),
    SorryGap(
        module="SKEFTHawking.PauliMatrices",
        name="σ_x_trace",
        priority=1,
        description="tr(σ_x) = 0: Pauli matrices are traceless",
        strategy_hint="simp [Matrix.trace, σ_x, Fin.sum_univ_two]",
        filled=True,
    ),
    SorryGap(
        module="SKEFTHawking.PauliMatrices",
        name="σ_y_trace",
        priority=1,
        description="tr(σ_y) = 0: Pauli matrices are traceless",
        strategy_hint="simp [Matrix.trace, σ_y, Fin.sum_univ_two]",
        filled=True,
    ),
    SorryGap(
        module="SKEFTHawking.PauliMatrices",
        name="σ_z_trace",
        priority=1,
        description="tr(σ_z) = 0: Pauli matrices are traceless",
        strategy_hint="simp [Matrix.trace, σ_z, Fin.sum_univ_two]",
        filled=True,
    ),
    # Phase 5a Wave 2A: WilsonMass.lean
    SorryGap(
        module="SKEFTHawking.WilsonMass",
        name="wilson_mass_at_zero",
        priority=1,
        description="M(0,0,0) = 0: Wilson mass vanishes at origin via cos(0)=1",
        strategy_hint="unfold wilsonMass; simp [Real.cos_zero]",
        filled=True,
    ),
    SorryGap(
        module="SKEFTHawking.WilsonMass",
        name="wilson_mass_positive_at_pi",
        priority=1,
        description="M(π,0,0) > 0: doubler is gapped via cos(π)=-1, cos(0)=1",
        strategy_hint="unfold wilsonMass; simp [Real.cos_zero, Real.cos_pi]; norm_num",
        filled=True,
    ),
    SorryGap(
        module="SKEFTHawking.WilsonMass",
        name="wilson_max_at_antiperiodic",
        priority=1,
        description="M(π,π,π) = 6: maximum Wilson mass via cos(π)=-1",
        strategy_hint="unfold wilsonMass; simp [Real.cos_pi]; ring",
        filled=True,
    ),
    # Phase 5a Wave 2A: BdGHamiltonian.lean
    SorryGap(
        module="SKEFTHawking.BdGHamiltonian",
        name="kronecker_comm_identity_mixed",
        priority=1,
        description="[A⊗𝟙, 𝟙⊗B] = 0 for 2x2 matrices: Kronecker product commutator identity",
        strategy_hint="ext ⟨sr, tr⟩ ⟨sc, tc⟩; simp [Matrix.mul_apply, Fin.sum_univ_two]; ring",
        filled=True,
    ),
    # Phase 5a Wave 2B: GTCommutation.lean
    SorryGap(
        module="SKEFTHawking.GTCommutation",
        name="gt_tau_commutator_vanishes",
        priority=1,
        description="[h_tau(p3), q_tau(p3)] = 0: the 2x2 Nambu-space identity, heart of GT construction",
        strategy_hint="Unfold h_tau q_tau σ_z σ_x, ext i j, fin_cases, simp [mul_apply], use sin_sq_add_cos_sq or ring",
        filled=True,
    ),
    SorryGap(
        module="SKEFTHawking.GTCommutation",
        name="gt_commutation_4x4",
        priority=1,
        description="[H_BdG(k), q_A(k)] = 0: full 4x4 commutation via Kronecker decomposition + tau identity",
        strategy_hint="Decompose H_BdG into 3 terms. σ_i⊗1 terms commute with 1⊗q_tau. σ₂⊗h_eff reduces to gt_tau_commutator_vanishes.",
        filled=True,
    ),
    SorryGap(
        module="SKEFTHawking.GTCommutation",
        name="gt_chiral_charge_non_compact",
        priority=1,
        description="∃ p3, cos(p3/2) ∉ {0, ±1}: non-integer eigenvalue exists",
        strategy_hint="Use p3 = 1. cos(1/2) ≈ 0.877 is not 0, 1, or -1. Need Real.cos_pos_of_mem_Ioo for positivity, then contradiction with exact values.",
        filled=True,
    ),
    # Phase 5b: SMFermionData.lean (2 sorrys)
    SorryGap(
        module="SKEFTHawking.SMFermionData",
        name="z4_charge_is_integer",
        priority=1,
        description="All SM fermion Z4 charges are integers: ∃ n : ℤ, X(f) = n for all f",
        strategy_hint="cases f, then simp [z4ChargeRaw, bMinusL, hyperchargeY], then provide witness for each case",
        filled=True,  # Manual proof: explicit witnesses per constructor
    ),
    SorryGap(
        module="SKEFTHawking.SMFermionData",
        name="sm_z4_all_odd",
        priority=1,
        description="All SM fermion Z4 charges are odd: ∃ k, X(f) = 2k+1 for all f",
        strategy_hint="cases f, then simp [z4ChargeRaw, bMinusL, hyperchargeY]; use specific k values (0, 0, -2, -2, 0, 2)",
        filled=True,  # Manual proof: explicit witnesses (0, 0, -2, -2, 0, 2)
    ),
    # Phase 5b: Z16AnomalyComputation.lean (2 sorrys)
    SorryGap(
        module="SKEFTHawking.Z16AnomalyComputation",
        name="generation_anomaly_period",
        priority=1,
        description="16 | 15n ↔ 16 | n: anomaly periodicity (15 coprime to 16)",
        strategy_hint="Use Nat.Coprime.dvd_of_dvd_mul_right with coprimality of 15 and 16, or Int version",
        filled=True,  # Manual proof: omega-based forward/backward direction
    ),
    SorryGap(
        module="SKEFTHawking.Z16AnomalyComputation",
        name="hidden_sector_required",
        priority=1,
        description="a ≠ 0 in ZMod 16 → ∃ b ≠ 0 with a + b = 0: hidden sector existence",
        strategy_hint="Use b = -a. Then a + (-a) = 0. Need -a ≠ 0 from a ≠ 0 (neg_ne_zero or ZMod.neg_ne_zero).",
        filled=True,  # Manual proof: ⟨-a, neg_ne_zero.mpr ha, add_neg_cancel a⟩
    ),
    # Phase 5b: GenerationConstraint.lean (6 sorrys)
    SorryGap(
        module="SKEFTHawking.GenerationConstraint",
        name="generation_mod3_constraint",
        priority=1,
        description="24 | 8*N_f → 3 | N_f: generation constraint from modular invariance",
        strategy_hint="From 24 | 8n: write 8n = 24k, so n = 3k. Use Nat.dvd_of_mul_dvd_mul_left or omega.",
        filled=True,  # Aristotle run a1dfcbde: obtain + omega + exact_mod_cast
    ),
    SorryGap(
        module="SKEFTHawking.GenerationConstraint",
        name="div_24_8n_implies_div_3_n",
        priority=1,
        description="24 | 8n → 3 | n (natural number version)",
        strategy_hint="8n = 24k implies n = 3k. Or: gcd(8,24) = 8, so 24/gcd | n, i.e., 3 | n.",
        filled=True,  # Manual proof: obtain ⟨k, hk⟩ := h; omega
    ),
    SorryGap(
        module="SKEFTHawking.GenerationConstraint",
        name="div_3_n_implies_div_24_8n",
        priority=1,
        description="3 | n → 24 | 8n (converse direction)",
        strategy_hint="If n = 3k then 8n = 24k. obtain ⟨k, hk⟩ := h; exact ⟨k, by linarith⟩ or omega.",
        filled=True,  # Manual proof: obtain ⟨k, hk⟩ := h; ⟨k, by omega⟩
    ),
    SorryGap(
        module="SKEFTHawking.GenerationConstraint",
        name="generation_constraint_iff",
        priority=1,
        description="3 | n ↔ 24 | 8n (biconditional)",
        strategy_hint="Combine div_24_8n_implies_div_3_n and div_3_n_implies_div_24_8n.",
        filled=True,  # Manual proof: term-mode Iff.intro combining the two
    ),
    SorryGap(
        module="SKEFTHawking.GenerationConstraint",
        name="generation_minimal_nontrivial",
        priority=1,
        description="3 | 3 and 3 is minimal positive multiple of 3",
        strategy_hint="constructor; exact dvd_refl 3; intros m hm hd; exact Nat.le_of_dvd hm hd.",
        filled=True,  # Manual proof: dvd_refl + Nat.le_of_dvd
    ),
    SorryGap(
        module="SKEFTHawking.GenerationConstraint",
        name="generation_next_solution",
        priority=1,
        description="3 | 6 and 6 is the next multiple of 3 after 3",
        strategy_hint="constructor; norm_num; intros m hm hd; omega or interval_cases with 3 < m.",
        filled=True,  # Manual proof: norm_num + omega
    ),
    # Phase 5b Wave 2: DrinfeldCenterBridge + VecGMonoidal (0 sorrys in Bridge, 1 in Monoidal)
    SorryGap(
        module="SKEFTHawking.VecGMonoidal",
        name="vecG_braided",
        priority=1,
        description="BraidedCategory instance for GradedObject (Additive G) (ModuleCat k) — Lean performance issue",
        strategy_hint="Use @GradedObject.braidedCategory with explicit args, or construct BraidedCategory manually from GradedObject.Monoidal.braiding + hexagon lemmas. All prerequisites synthesize individually.",
        filled=True,  # Aristotle run 48493889: CommGroup G in separate section resolves diamond
    ),
    # Phase 5b Wave 3: DrinfeldDoubleRing (13 sorrys — Ring/Algebra typeclass plumbing)
    SorryGap(
        module="SKEFTHawking.DrinfeldDoubleRing",
        name="DG_ring_algebra",
        priority=1,
        description="Ring + Algebra k instances on DG wrapper for D(G). 13 sorrys: zsmul_succ'/neg', left/right_distrib, zero/mul_zero, algebraMap fields, commutes', smul_def', basis_mul",
        strategy_hint="AddCommGroup axioms: ext + Pi pointwise. Distrib: unfold ddAlgMul, mul_add/add_mul + sum_add_distrib. Zero_mul/mul_zero: Pi.zero_apply + sum_const_zero. AlgebraMap: Finset.sum_eq_single 1 for convolution with unit. See PROVIDED SOLUTION hints in file.",
        filled=True,  # Aristotle run 52992d6a: all 13 sorrys filled
    ),
    # Phase 5b Wave 5: ModularInvarianceConstraint (4 sorrys — complex exponential)
    SorryGap(
        module="SKEFTHawking.ModularInvarianceConstraint",
        name="modular_invariance_sorrys",
        priority=1,
        description="4 sorrys: zeta24_pow_24, zeta24_ne_one, zeta24_primitive, qParam_integer_invariant, plus backward direction of framing_anomaly_constraint. All complex exponential arithmetic.",
        strategy_hint="zeta24^24: unfold zeta24, use exp_nat_mul or exp_add repeatedly, reduce to cexp(2πi)=1. zeta24_ne_one: cexp(2πi/24)=1 would mean 2πi/24=2πik, contradiction. zeta24_primitive: exp_eq_one_iff + divisibility. qParam_integer_invariant: cexp(2πi(z+1))=cexp(2πiz)*cexp(2πi)=cexp(2πiz)*1. See PROVIDED SOLUTION hints in file.",
        filled=True,  # Aristotle run b54f9611: all sorrys filled
    ),
    # Phase 5b Wave 6: RokhlinBridge (1 sorry — ZMod arithmetic)
    SorryGap(
        module="SKEFTHawking.RokhlinBridge",
        name="z16_anomaly_without_nu_R",
        priority=1,
        description="15*N_f ≡ 0 mod 16 ↔ 16|N_f. ZMod arithmetic: 15 ≡ -1 mod 16, so -N_f ≡ 0 iff 16|N_f.",
        strategy_hint="15 ≡ -1 mod 16 (by decide). So 15*N_f = -N_f in ZMod 16. Then -N_f = 0 iff N_f = 0 iff 16|N_f. Use ZMod.natCast_zmod_eq_zero_iff_dvd.",
        filled=True,  # Aristotle run b54f9611: sorry filled
    ),
    # Phase 5b Wave 7: QNumber (5 sorrys — Laurent polynomial evaluation)
    SorryGap(
        module="SKEFTHawking.QNumber",
        name="qnumber_eval",
        priority=2,
        description="5 sorrys: evalAtOne construction (LaurentPolynomial → k algebra hom), evalAtOne_T, qInt_classical_limit, qInt_two_pow4_classical, qInt_three_classical. All Laurent polynomial evaluation.",
        strategy_hint="evalAtOne: use LaurentPolynomial.eval₂ or the universal property. evalAtOne_T: T m evaluates to 1^m = 1. qInt_classical_limit: map_sum + evalAtOne_T + card_range. See PROVIDED SOLUTION hints.",
        filled=True,
    ),
    # Phase 5b Wave 7: Uqsl2 (6 sorrys — RingQuot relation proofs)
    SorryGap(
        module="SKEFTHawking.Uqsl2",
        name="uqsl2_relations",
        priority=2,
        description="6 sorrys: uq_K_mul_Kinv, uq_Kinv_mul_K, uqK_unit, uq_KE, uq_KF, uq_serre. All are RingQuot.mkAlgHom_rel applications with ChevalleyRel constructors.",
        strategy_hint="Unfold uqK/uqE/etc to uqsl2Mk applied to generators. Use ← map_mul / ← map_one to combine. Then RingQuot.mkAlgHom_rel _ ChevalleyRel.KKinv etc. For KE/KF/Serre: also need map_algebraMap or Algebra.algebraMap_eq_smul_one.",
        filled=True,
    ),
    # Phase 5c Wave 1: Uqsl2Hopf — Hopf algebra structure (22 sorrys)
    SorryGap(
        module="SKEFTHawking.Uqsl2Hopf",
        name="uqsl2_hopf_structure",
        priority=1,
        description="22 sorrys: comulFreeAlg_respects_rel (5 relation checks), counitFreeAlg_respects_rel (5 checks), antipodeFreeAlg_respects_rel (5 checks), 4 comul_gen + 4 counit_gen + 4 antipode_gen (unfolding liftAlgHom), coassociativity, 2 counitality, 2 antipode axioms, S^2=Ad(K), counit_comp_antipode. First Hopf algebra in a proof assistant.",
        strategy_hint="Generator-level: unfold comulUq/counitUq/antipodeUq to liftAlgHom, apply liftAlgHom_mkAlgHom_apply, then lift_ι_apply. Relation compatibility: intro/cases on ChevalleyRel, compute on tensor products using map_mul/map_add. Coalgebra axioms: AlgHom equality by ext, reduce to generator checks. Antipode axioms: LinearMap ext, reduce to generators. See PROVIDED SOLUTION hints in each theorem.",
        filled=True,
    ),

    # ════════════════════════════════════════════════════════════════════
    # Phase 5d-5f sorry gaps — registered for priority-batched submission
    # Batch 1 (in flight): SU2kMTC + FibonacciMTC (Aristotle 3b356975)
    # Batch 2 (Priority 1): Uqsl2AffineHopf + CoidealEmbedding — unblocks affine Hopf
    # Batch 3 (Priority 2): StimulatedHawking + VerifiedStatistics + RepUqFusion — paper verification
    # Batch 4 (Priority 3): CenterFunctor + KerrSchild + EmergentGravityBounds — hard/less urgent
    # ════════════════════════════════════════════════════════════════════

    # --- Batch 1 (IN FLIGHT — Aristotle 3b356975) ---
    SorryGap(
        module="SKEFTHawking.SU2kMTC",
        name="su2k_mtc_pentagon_twist",
        priority=1,
        description="5 sorry: isingF_involutory (2 entries), ising_pentagon, ising_twist_unitary, ising_twist_psi. F-symbol and twist verification for Ising MTC.",
        strategy_hint="RESOLVED: All proved via native_decide over QSqrt2. Convention bug fixed (Kitaev 2006). Pentagon + twist + involutory all zero sorry.",
        filled=True,
    ),
    SorryGap(
        module="SKEFTHawking.FibonacciMTC",
        name="fibonacci_mtc_pentagon_dim",
        priority=1,
        description="3 sorry: fib_pentagon_all_tau, fib_global_dim, fib_dim_consistency. Pentagon over Q(sqrt5) F-symbols and Real.sqrt arithmetic.",
        strategy_hint="RESOLVED: All proved via native_decide over QSqrt5. Pentagon convention fixed. D² and φ²=1+φ proved over both Q(√5) and ℝ.",
        filled=True,
    ),

    # --- Batch 2 (Priority 1 — unblocks Phase 5e Track C) ---
    SorryGap(
        module="SKEFTHawking.Uqsl2AffineHopf",
        name="affine_hopf_relation_respect",
        priority=1,
        description="3 sorry: affComul_respects_rel, affCounit_respects_rel, affAntipode_respects_rel. Coproduct/counit/antipode compatibility with 11 Chevalley+Serre relations on 8 generators.",
        strategy_hint="Per-relation factoring (see deep research Phase-5e/affine Hopf strategy). Counit: trivial (all E/F map to 0). K-invertibility: easy. KE/KF commutation: moderate. EF: hard. Serre coproduct: very hard (64 terms). Use 4-phase tactic: unfold→expand→rewrite→collect. set_option maxHeartbeats 800000.",
        filled=False,
    ),
    SorryGap(
        module="SKEFTHawking.CoidealEmbedding",
        name="coideal_embedding_proofs",
        priority=1,
        description="4 sorry: coideal_B0, coideal_B1, counit_B0, counit_B1. Coideal property Δ(Bi)=Bi⊗1+Ki⁻¹⊗Bi and counit ε(Bi)=0.",
        strategy_hint="Expand Bi = Fi + EiKi⁻¹, apply linearity of Δ. Use affComul on Fi, Ei, Ki⁻¹. Multiply out (Ei⊗Ki + 1⊗Ei)(Ki⁻¹⊗Ki⁻¹). Apply KiKi⁻¹=1. Counit: ε(Fi)=0, ε(Ei)=0, ε(Ki⁻¹)=1 → ε(Bi)=0+0·1=0.",
        filled=True,
    ),

    # --- Batch 3 (Priority 2 — completes paper verification) ---
    SorryGap(
        module="SKEFTHawking.StimulatedHawking",
        name="stimulated_hawking_analysis",
        priority=2,
        description="7 sorry: boseEinstein_strictAnti, stimGain_anti_omega, boseEinstein_tendsto_zero, boseEinstein_lower_bound, snr_sqrt_scaling, dispersiveCorrection_in_unit_interval, detection_threshold. Real analysis: exp monotonicity, limits, sqrt properties. 5 of 7 proved by Aristotle run 986b9f66; snr_sqrt_scaling, detection_threshold remain.",
        strategy_hint="strictAnti: 1/(exp(x)-1) has strictly decreasing numerator 1 and strictly increasing denominator. tendsto_zero: squeeze with exp(-x). lower_bound: exp(x)≤1+2x for x≤1 (Taylor). sqrt_scaling: Real.sqrt_mul properties. dispersive: D²<1/c₁ → c₁D²<1 via field_simp. detection: sqrt(n)·G≥5 from n≥25/G².",
        filled=False,
    ),
    SorryGap(
        module="SKEFTHawking.VerifiedStatistics",
        name="verified_statistics_bounds",
        priority=2,
        description="4 sorry: autocovariance_bounded (Cauchy-Schwarz), jackknife_mean_case (s²/n identity), normalizedAutocorr_le_one (ρ≤1), effectiveSampleSize_le_n (N_eff≤N).",
        strategy_hint="autocovariance_bounded: Finset.inner_mul_le_norm_mul_sq (Cauchy-Schwarz). jackknife_mean_case: Fin.sum_univ_succAbove for delete-one, then field_simp+ring. normalizedAutocorr: use autocovariance_bounded + div_le_one. effectiveSampleSize: use intAutocorrTime_ge_half + div_le_div.",
        filled=True,
    ),
    SorryGap(
        module="SKEFTHawking.RepUqFusion",
        name="rep_uq_fusion_algebraic",
        priority=2,
        description="2 sorry: rep_fusion_comm (fusion commutativity), peter_weyl_classical (sum of squares = (k+1)(k+2)(2k+3)/6).",
        strategy_hint="rep_fusion_comm: unfold su2kFusion, the min/max/abs in the truncated CG rule are symmetric in i,j. May need Nat.min_comm + Nat.sub_comm. peter_weyl: induction on k, sum of first n squares formula.",
        filled=False,
    ),

    # --- Batch 4 (Priority 3 — hard/less urgent) ---
    SorryGap(
        module="SKEFTHawking.CenterFunctor",
        name="center_functor_equivalence",
        priority=3,
        description="5 sorry: functor_exists, functor_faithful, functor_full, functor_essSurj, center_dg_equivalence. Abstract categorical functor Center(Vec_G) ⥤ ModuleCat(DG).",
        strategy_hint="Path B: ofFullyFaithfullyEssSurj. obj: total space with DG-action from half-braiding. map: same linear map. Faithful: Center.Hom.ext. Full: extract graded components from DG-linearity. EssSurj: decompose DG-module into eigenspaces of k^G idempotents. Deep research: Phase-5c/Ribbon/Building a Drinfeld center-module equivalence.",
        filled=False,
    ),
    SorryGap(
        module="SKEFTHawking.KerrSchild",
        name="kerr_schild_inverse",
        priority=3,
        description="1 sorry: ks_inverse_formula (Sherman-Morrison 4×4 matrix inverse for Kerr-Schild metric).",
        strategy_hint="Sherman-Morrison: (η+φl⊗l)⁻¹ = η-φ/(1+φ·l·η·l)·l⊗l. For null l (l·η·l=0): simplifies to η-φ·l⊗l. Expand 4×4 sum, use nullity hypothesis, close with ring.",
        filled=True,
    ),
    SorryGap(
        module="SKEFTHawking.EmergentGravityBounds",
        name="emergent_gravity_coupling_bounds",
        priority=3,
        description="2 sorry: coupling_deficit (G₄f < G_c/1000 for α≤0.2), coupling_ratio_small (ratio < 1/1000 for α=0.2, N_f=4). coupling_deficit proved by Aristotle run 986b9f66; coupling_ratio_small remains.",
        strategy_hint="Both need Real.pi bounds: π > 3.14. Then 32π³ > 32·31 = 992. α²·N_f/(32π³) < 0.04·4/992 < 1/1000. Use Real.pi_gt_three or pi_gt_3141592.",
        filled=False,
    ),
    # Phase 5i: U_q(sl₃) — definition (Uqsl3.lean) ALL 21 relations PROVED manually
    # Quantum Serre relations proved via simp [map_mul, map_add, AlgHom.commutes] at h ⊢
    # Zero sorry in Uqsl3.lean
    # ═══════════════════════════════════════════════════════════════
    # Phase 5i Wave 2: U_q(sl₃) Hopf algebra (Uqsl3Hopf.lean) — 4 sorry
    # ═══════════════════════════════════════════════════════════════
    SorryGap(
        module="SKEFTHawking.Uqsl3Hopf",
        name="comulFreeAlg3_respects_rel",
        priority=2,
        description="Coproduct respects all 21 Chevalley relations of U_q(sl₃). The 4 Serre Δ-compatibility proofs are the hardest (24 terms each).",
        strategy_hint="Factor into per-relation cases. K-invertibility: Δ(KK⁻¹)=Δ(K)Δ(K⁻¹)=(K⊗K)(K⁻¹⊗K⁻¹)=1⊗1. KE: use tmul_mul_tmul + uq3_K1E1. Serre: expand 3 cubic monomials into 24 tensor terms, group by bidegree, cancel using Serre relation + K-E commutation. Same pattern as Uqsl2Hopf (which Aristotle proved in run 79e07d55).",
        filled=False,
    ),
    SorryGap(
        module="SKEFTHawking.Uqsl3Hopf",
        name="counitFreeAlg3_respects_rel",
        priority=2,
        description="Counit respects all 21 relations. All E,F map to 0, all K to 1.",
        strategy_hint="Every relation is trivially satisfied: ε kills E,F. Factor into per-relation cases, each is 1-2 lines via simp [counitOnGen3, FreeAlgebra.lift_ι_apply, map_mul, map_add].",
        filled=False,
    ),
    SorryGap(
        module="SKEFTHawking.Uqsl3Hopf",
        name="antipodeFreeAlg3_respects_rel",
        priority=2,
        description="Antipode (anti-hom) respects all 21 relations.",
        strategy_hint="S reverses products. K-invertibility: S(KK⁻¹)=S(K⁻¹)S(K)=K·K⁻¹=1. Serre: hardest, needs derived commutation identities. Same approach as Uqsl2Hopf antipode proofs.",
        filled=False,
    ),
    SorryGap(
        module="SKEFTHawking.Uqsl3Hopf",
        name="uq3_antipode_squared",
        priority=2,
        description="S² = Ad(K₁²K₂²) on all 8 generators (conjugation by K_{2ρ}).",
        strategy_hint="Check each generator. S²(K_i)=K_i (K⁻¹→K). S²(E_i)=K_iE_iK_i⁻¹=q²·E_i. Ad(K₁²K₂²) gives q²·E_i via K-E conjugation applied twice. Note: original claim Ad(K₁K₂) was mathematically wrong (gave q·E_i not q²·E_i).",
        filled=False,
    ),
]


@dataclass
class AristotleResult:
    """Result from an Aristotle submission.

    Tracks which sorries were filled, which remain, and any errors.

    Status semantics (from Aristotle API docs):
        COMPLETE             — all work finished successfully
        COMPLETE_WITH_ERRORS — finished but some theorems failed
        FAILED               — submission itself errored out
        OUT_OF_BUDGET        — ran out of allocated compute budget;
                               partial results may be available.
                               To resume: download partial output via
                               `aristotle result <id> --destination partial.tar.gz`,
                               extract, and resubmit the project.
    """
    project_id: str
    timestamp: str
    prompt: str
    status: str = "UNKNOWN"  # COMPLETE | COMPLETE_WITH_ERRORS | FAILED | OUT_OF_BUDGET | UNKNOWN
    sorries_filled: list[str] = field(default_factory=list)
    sorries_remaining: list[str] = field(default_factory=list)
    errors: list[str] = field(default_factory=list)
    raw_output: str = ""

    @property
    def is_out_of_budget(self) -> bool:
        """True if Aristotle ran out of compute budget (partial results may exist)."""
        return self.status == "OUT_OF_BUDGET"

    @property
    def is_complete(self) -> bool:
        """True if Aristotle finished (possibly with some errors)."""
        return self.status in ("COMPLETE", "COMPLETE_WITH_ERRORS")

    @property
    def has_partial_results(self) -> bool:
        """True if there are usable results (complete or partial from budget exhaustion)."""
        return self.status in ("COMPLETE", "COMPLETE_WITH_ERRORS", "OUT_OF_BUDGET")


class AristotleRunner:
    """Interface to the Aristotle API for Lean sorry-filling.

    Manages submission of the Lean project, polling for results,
    and integration of filled proofs back into the codebase.

    The API key is read from the .env file in the project root.
    """

    def __init__(self, project_root: Optional[Path] = None):
        self.project_root = project_root or PROJECT_ROOT
        self.lean_dir = self.project_root / "lean"
        self.results_dir = self.project_root / "docs" / "aristotle_results"
        self.results_dir.mkdir(parents=True, exist_ok=True)

        # Load API key from .env
        env_file = self.project_root / ".env"
        self.api_key = self._load_api_key(env_file)

    @staticmethod
    def _load_api_key(env_file: Path) -> str:
        """Load ARISTOTLE_API_KEY from .env file.

        Falls back to environment variable if .env doesn't exist.
        Raises ValueError if no key is found.
        """
        if env_file.exists():
            for line in env_file.read_text().splitlines():
                if line.startswith("ARISTOTLE_API_KEY="):
                    return line.split("=", 1)[1].strip()

        key = os.environ.get("ARISTOTLE_API_KEY")
        if key:
            return key

        raise ValueError(
            "No ARISTOTLE_API_KEY found. Set it in .env or as an environment variable. "
            "Get your key at https://aristotle.harmonic.fun/dashboard/api-keys"
        )

    def submit_and_wait(
        self,
        prompt: str = "Fill in all sorries in this Lean project",
        timeout_seconds: int = 3600,
    ) -> AristotleResult:
        """Submit the Lean project to Aristotle and wait for results.

        Args:
            prompt: The instruction for Aristotle (what to prove).
            timeout_seconds: Maximum time to wait for completion.

        Returns:
            AristotleResult with filled/remaining sorries and any errors.

        The submission uses the aristotle CLI:
            aristotle submit "<prompt>" --project-dir ./lean --wait

        Results are saved to docs/aristotle_results/ for reproducibility.
        """
        timestamp = datetime.now().strftime("%Y%m%d_%H%M%S")

        # Save patched files to a timestamped directory for review
        # NOTE: --destination must be a FILE path (for the tar.gz), not a directory.
        # Aristotle CLI calls destination.write_bytes() on the response.
        dest_dir = self.results_dir / f"patched_{timestamp}"
        dest_dir.mkdir(parents=True, exist_ok=True)
        destination_file = dest_dir / "result.tar.gz"

        cmd = [
            "aristotle",
            "submit", prompt,
            "--project-dir", str(self.lean_dir),
            "--wait",
            "--destination", str(destination_file),
            "--api-key", self.api_key,
        ]

        try:
            result = subprocess.run(
                cmd,
                capture_output=True,
                text=True,
                timeout=timeout_seconds,
                cwd=str(self.project_root),
            )

            aristotle_result = AristotleResult(
                project_id=f"run_{timestamp}",
                timestamp=timestamp,
                prompt=prompt,
                raw_output=result.stdout + result.stderr,
            )

            # Parse output to identify filled vs remaining sorries
            # (Aristotle returns a tar.gz with the modified project)
            if result.returncode == 0:
                aristotle_result = self._parse_result(aristotle_result, result.stdout)
            else:
                aristotle_result.errors.append(
                    f"Aristotle returned exit code {result.returncode}: {result.stderr}"
                )

        except subprocess.TimeoutExpired:
            aristotle_result = AristotleResult(
                project_id=f"run_{timestamp}",
                timestamp=timestamp,
                prompt=prompt,
                errors=[f"Timed out after {timeout_seconds}s"],
            )

        # Save result for reproducibility
        self._save_result(aristotle_result)
        return aristotle_result

    def submit_targeted(
        self,
        sorry_gap: SorryGap,
        timeout_seconds: int = 300,
    ) -> AristotleResult:
        """Submit a targeted request for a specific sorry gap.

        More focused than submit_and_wait: tells Aristotle exactly
        which theorem to prove and gives a strategy hint.

        Args:
            sorry_gap: The specific sorry to fill.
            timeout_seconds: Maximum wait time.

        Returns:
            AristotleResult for this specific gap.
        """
        prompt = (
            f"In module {sorry_gap.module}, prove the theorem/definition "
            f"'{sorry_gap.name}'. {sorry_gap.description}. "
            f"Strategy: {sorry_gap.strategy_hint}"
        )
        return self.submit_and_wait(prompt, timeout_seconds)

    def submit_priority_batch(
        self,
        max_priority: int = 1,
        timeout_seconds: int = 3600,
    ) -> AristotleResult:
        """Submit all sorry gaps up to a given priority level.

        Priority 1 = most tractable (pure algebra).
        Priority 2 = moderate (algebra + inequalities).
        Priority 3 = hardest (analysis, may remain sorry).

        Args:
            max_priority: Maximum priority level to attempt (1, 2, or 3).
            timeout_seconds: Maximum wait time.

        Returns:
            AristotleResult summarizing the batch.
        """
        gaps = [g for g in SORRY_GAPS if g.priority <= max_priority and not g.filled]
        gap_descriptions = "\n".join(
            f"- {g.module}.{g.name}: {g.description}" for g in gaps
        )

        prompt = (
            f"Fill in the following sorry gaps (priority ≤ {max_priority}):\n"
            f"{gap_descriptions}\n\n"
            f"For each, the strategy hint is provided in the Lean comments. "
            f"Focus on algebraic and linear algebra proofs first."
        )
        return self.submit_and_wait(prompt, timeout_seconds)

    def _parse_result(self, result: AristotleResult, output: str) -> AristotleResult:
        """Parse Aristotle output to identify filled vs remaining sorries.

        Detects status from CLI output, including OUT_OF_BUDGET which indicates
        partial results are available and the submission can be resumed.

        This is a best-effort parse of the CLI output. The definitive
        check is whether the returned Lean files compile without sorry.
        """
        result.raw_output = output
        upper_output = output.upper()

        # Detect status from output
        # Aristotle CLI prints status in various formats; check for known statuses
        known_statuses = ["OUT_OF_BUDGET", "COMPLETE_WITH_ERRORS", "COMPLETE", "FAILED"]
        for status in known_statuses:
            if status in upper_output:
                result.status = status
                break
        else:
            # If no explicit status found but exit code was 0, assume COMPLETE
            result.status = "COMPLETE"

        # Look for project ID in output
        for line in output.splitlines():
            if "project" in line.lower() and ("id" in line.lower() or ":" in line):
                # Extract UUID-like strings from the line
                import re
                uuid_match = re.search(
                    r'[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}',
                    line
                )
                if uuid_match:
                    result.project_id = uuid_match.group(0)
                else:
                    result.project_id = line.strip()
                break

        # Log actionable guidance for OUT_OF_BUDGET
        if result.is_out_of_budget:
            result.errors.append(
                f"OUT_OF_BUDGET: Aristotle exhausted its compute budget. "
                f"Partial results may be available. To resume:\n"
                f"  1. aristotle result {result.project_id} --destination partial.tar.gz\n"
                f"  2. Extract and inspect partial progress\n"
                f"  3. Resubmit the (partially-filled) project"
            )

        return result

    def _save_result(self, result: AristotleResult) -> Path:
        """Save the Aristotle result to docs/aristotle_results/ as JSON.

        Returns the path to the saved file.
        """
        filepath = self.results_dir / f"{result.project_id}.json"
        filepath.write_text(json.dumps({
            "project_id": result.project_id,
            "timestamp": result.timestamp,
            "prompt": result.prompt,
            "status": result.status,
            "sorries_filled": result.sorries_filled,
            "sorries_remaining": result.sorries_remaining,
            "errors": result.errors,
            "raw_output": result.raw_output[:5000],  # Truncate large outputs
        }, indent=2))
        return filepath

    def list_sorry_gaps(self, max_priority: int = 3, include_filled: bool = False) -> list[SorryGap]:
        """List all documented sorry gaps up to a priority level.

        Args:
            max_priority: Maximum priority level to include.
            include_filled: If True, include already-filled gaps. Default: False.

        Useful for understanding what remains to be proved.
        """
        return [g for g in SORRY_GAPS
                if g.priority <= max_priority and (include_filled or not g.filled)]

    def print_sorry_summary(self) -> None:
        """Print a human-readable summary of all sorry gaps by priority."""
        for priority in (1, 2, 3):
            gaps = [g for g in SORRY_GAPS if g.priority == priority]
            if gaps:
                label = {1: "Algebraic (likely fillable)", 2: "Moderate", 3: "Analysis (likely remains sorry)"}
                filled_count = sum(1 for g in gaps if g.filled)
                print(f"\n{'='*60}")
                print(f"Priority {priority}: {label[priority]} ({filled_count}/{len(gaps)} filled)")
                print(f"{'='*60}")
                for g in gaps:
                    status = "✓ FILLED" if g.filled else "○ OPEN"
                    print(f"  [{status}] [{g.module}] {g.name}")
                    print(f"    {g.description}")
                    if g.strategy_hint and not g.filled:
                        print(f"    Strategy: {g.strategy_hint}")


if __name__ == "__main__":
    runner = AristotleRunner()
    print("SK-EFT Hawking Paper: Sorry Gap Summary")
    print("=" * 60)
    runner.print_sorry_summary()
    filled = [g for g in SORRY_GAPS if g.filled]
    remaining = [g for g in SORRY_GAPS if not g.filled]
    print(f"\nTotal gaps: {len(SORRY_GAPS)} ({len(filled)} filled, {len(remaining)} remaining)")
    for p in (1, 2, 3):
        total_p = len([g for g in SORRY_GAPS if g.priority == p])
        filled_p = len([g for g in SORRY_GAPS if g.priority == p and g.filled])
        label = {1: "algebraic", 2: "moderate", 3: "analysis"}
        print(f"  Priority {p} ({label[p]}): {filled_p}/{total_p} filled")
