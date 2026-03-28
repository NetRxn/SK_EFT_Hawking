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
