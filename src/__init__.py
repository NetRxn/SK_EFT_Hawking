"""
SK-EFT Hawking Paper: Python Computation Layer

This package provides:
1. Symbolic computation of the SK-EFT action expansion around a transonic background
2. Numerical evaluation of the dissipative correction δ_diss for BEC parameters
3. Interface to the Aristotle API for Lean sorry-filling

The Lean formalization (in ../lean/) provides the formal verification backbone.
This Python layer provides the computational engine that drives the physics.

Package structure:
- transonic_background: Solve the 1D Euler+continuity for a step potential
- sk_action: SK-EFT action construction and expansion to quadratic order
- greens_functions: Retarded and Keldysh propagator computation
- aristotle_interface: Submit Lean projects to Aristotle for sorry-filling
- experimental_params: BEC parameter sets (Steinhauer, Heidelberg, Trento)
"""
