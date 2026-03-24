"""
Pytest wrapper for the cross-layer validation suite.

This allows `pytest` to run the same checks as `scripts/validate.py`,
so validation is part of the normal test suite and CI pipeline.

Usage:
    pytest tests/test_cross_validation.py -v
    pytest tests/ -v   # runs alongside unit tests
"""

import sys
from pathlib import Path

import pytest

# Ensure project root is importable
PROJECT_ROOT = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(PROJECT_ROOT))

# Import the validation check functions
sys.path.insert(0, str(PROJECT_ROOT / "scripts"))
from validate import (
    check_formulas_to_theorems,
    check_numerical_consistency,
    check_formula_identities,
    check_paper_table_consistency,
    check_theorem_count,
    check_notebook_isolation,
    check_lean_source,
)


class TestCrossValidation:
    """Cross-layer consistency checks (mirrors scripts/validate.py)."""

    def test_formulas_reference_lean_theorems(self):
        """Every Python physics function references a valid Lean theorem."""
        result = check_formulas_to_theorems()
        failures = [d for d in result.details if not d.passed]
        assert result.passed, f"Formula-theorem mapping failures: {failures}"

    def test_numerical_consistency(self):
        """Solver output matches reference experimental values."""
        result = check_numerical_consistency()
        failures = [d for d in result.details if not d.passed]
        assert result.passed, f"Numerical mismatches: {failures}"

    def test_formula_identities(self):
        """Mathematical identities and boundary conditions hold."""
        result = check_formula_identities()
        failures = [d for d in result.details if not d.passed]
        assert result.passed, f"Identity failures: {failures}"

    def test_paper_table_consistency(self):
        """Paper 1 Table 1 values are reproducible from code."""
        result = check_paper_table_consistency()
        failures = [d for d in result.details if not d.passed]
        assert result.passed, f"Paper-code mismatches: {failures}"

    def test_theorem_count(self):
        """Theorem registry has 35 entries and is self-consistent."""
        result = check_theorem_count()
        assert result.passed

    def test_notebook_isolation(self):
        """Notebooks import physics from src.core, no re-implementation."""
        result = check_notebook_isolation()
        failures = [d for d in result.details if not d.passed]
        assert result.passed, f"Notebooks with inline physics: {failures}"

    def test_lean_source_references(self):
        """Key theorem names appear in Lean source files."""
        result = check_lean_source()
        failures = [d for d in result.details if not d.passed]
        assert result.passed, f"Missing Lean identifiers: {failures}"
