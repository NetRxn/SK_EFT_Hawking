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


# Project paths (relative to the SK_EFT_Hawking_Paper root)
PROJECT_ROOT = Path(__file__).parent.parent
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
