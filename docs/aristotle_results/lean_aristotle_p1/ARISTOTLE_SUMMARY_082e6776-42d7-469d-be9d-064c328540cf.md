# Summary of changes
Successfully filled all four requested sorry gaps:

1. **`acousticMetric_det`** (AcousticMetric.lean): Proved that the 2×2 determinant of the acoustic metric equals −ρ² by expanding via `Matrix.det_fin_two`, normalizing, and using `ring`/`norm_num` with the hypothesis `cs ≠ 0`.

2. **`acousticMetric_inv_correct`** (AcousticMetric.lean): Proved that g · g⁻¹ = I by unfolding both matrix definitions, using `ext` + `fin_cases` to check all four entries, then `ring_nf` and `aesop` for the algebraic simplifications.

3. **`acoustic_metric_lorentzian`** (AcousticMetric.lean): Proved that the acoustic metric has negative determinant (Lorentzian signature) by rewriting with `acousticMetric_det` and using `aesop` to close the negativity goal from `rho > 0`.

4. **`firstOrder_positivity`** (SKDoubling.lean): Proved Im I_SK ≥ 0 by showing the imaginary part `(γ₁/β)·ψ_a² + (γ₂/β)·(∂_t ψ_a)²` is nonneg using `add_nonneg`, `mul_nonneg`, `div_nonneg`, and `sq_nonneg` with the hypotheses γ₁ ≥ 0, γ₂ ≥ 0, β > 0.

The project builds successfully with all four proofs verified.