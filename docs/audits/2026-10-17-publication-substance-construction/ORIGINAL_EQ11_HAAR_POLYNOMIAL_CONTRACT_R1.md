# L1 finite quaternion polynomial transfer

Parent acceptance is the original anchored Haar monomial at c6c80cc88 and its
exact source transport at 3f48b1fa8. The scientific target is the executable
Haar contraction of the original finite polynomial for subsequent Eq11
coefficient assembly.

Use the existing Variables and Symbolic types in FiniteDiracQuaternionSpecialization.
Variables splits into auxiliary, source and anchored quaternion indices.
The original Python coframe constructor uses L/R and the existing Lean
map uses false/true. Factor a supported exponent into its restrictions on these three arms.
Use the existing Mathlib evaluation expansion over the support and
MeasureTheory.integral_finsetSum. Each summand is integrable under linkHaar:
anchoredCoordinate is continuous, and compactness of the original Links and
the finite Haar measure give the same route used by link_coefficient_integrable.
Factor out the complex scalar, auxiliary and source powers and apply
linkHaar_monomial_complex once to the entire joint quaternion monomial.

Expose the coefficient operation as a linear contraction over the finite
monomial support. Its output retains auxiliary and source indices. Distinct
monomials that collapse to the same residual exponent must sum and may cancel.
Do not use a multiplicative map. The executable's shared-link contraction
of q times q is 1/4 even though each factor integrates to zero. A valid
product corollary contracts after joint multiplication, including repeated
anchors. Preserve the original site, direction and chiral labels until
after grouping. The production executable's pure-q cache can exploit
permutation invariance only after each full group has been assembled.

The executable Polynomial also preserves arbitrary non-q symbols,
including a separately tagged conjugated source. The existing Lean
Variables type has one holomorphic source arm. State an exact typed
embedding for the original h/J/q constructors and verify the actual Eq11
producer stays within it. For generic executable keys use a parameterized
residual type or explicitly preserve the conjugated source as a distinct
residual label. A generic correspondence must not silently identify J
with its conjugate. The checked production API examples in controls.json
distinguish this boundary. They also cover exact complex accumulation,
collision cancellation and same-group versus distinct-group moments.

Revalidate the dependency epoch after native absorption and search by
statement and type in the actual pinned import context. Existing declaration
leads above are based on source inspection. Kernel confirmation of the
proposed composition remains pending. Require standard axioms and independent
review for the exact polynomial bridge, then separately verify how executable
determinant, source and auxiliary factors feed it.
