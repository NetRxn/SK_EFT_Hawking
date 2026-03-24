import SKEFTHawking.Basic
import SKEFTHawking.AcousticMetric
import SKEFTHawking.SKDoubling
import SKEFTHawking.SecondOrderSK
import SKEFTHawking.HawkingUniversality
import SKEFTHawking.WKBAnalysis

/-!
# SK-EFT Hawking Paper: Lean Formalization

Formal verification of mathematical structures underlying the paper
"Dissipative EFT Corrections to Analog Hawking Radiation."

## Three Structures

- **Structure A (AcousticMetric):** The acoustic metric theorem — for a barotropic,
  irrotational, inviscid fluid, the linearized phonon EOM is equivalent to the
  massless Klein-Gordon equation on a curved background with metric determined
  algebraically by (v, c_s, ρ).

- **Structure B (SKDoubling):** The Schwinger-Keldysh doubling structure — given
  an action with global U(1) symmetry, the SK doubled action satisfying the
  three axioms (normalization, positivity, KMS) is uniquely determined at each
  derivative order up to transport coefficients.

- **Structure C (HawkingUniversality):** Hawking temperature universality — for
  any UV modification of the phonon dispersion satisfying adiabaticity, the
  effective temperature satisfies T_eff = T_H(1 + O(T_H/Λ)²).

## Methodology

Blueprint+sorry: algebraic identities are fully formalized; PDE well-posedness,
asymptotic analysis, and derivative expansion convergence are left as `sorry`.
The `sorry` gaps are documented and flagged for Aristotle automated filling.
-/
