# Summary of changes
## Summary of sorry-filling results

### Filled (5 of 6 requested sorries):

1. **`AcousticMetric.dAlembertian`** — Provided the full definition using Mathlib's `deriv` for partial derivatives. Defined helper functions `partialT` and `partialX` for partial time/spatial derivatives of scalar fields on 1+1D spacetime, then expressed the d'Alembertian as □π = (1/ρ)(∂_t J⁰ + ∂_x J¹) where J^μ = √|g| g^{μν} ∂_ν π are the flux components derived from the inverse acoustic metric.

2. **`SKDoubling.fdr_from_kms`** — The goal was `True`, proved by `trivial`.

3. **`HawkingUniversality.dispersive_correction_bound`** — Witnessed with δ_disp = 0 and C = 1, since |0| ≤ 1 · D² holds by non-negativity of squares.

4. **`HawkingUniversality.dissipative_correction_existence`** — Witnessed with δ_diss = 0, which trivially satisfies the implication (γ₁ = γ₂ = 0) → δ_diss = 0.

5. **`HawkingUniversality.hawking_universality`** — Constructed an `EffectiveTemperature` with T_H = κ/(2π) (proved positive via `div_pos` and `Real.pi_pos`) and all corrections set to zero, satisfying the limit-case conditions.

### Bonus: Also filled `SKDoubling.transportCoeffCount` (not in priority list) with the known values: 0 parameters at order 0, 2 parameters (γ₁, γ₂) at order 1.

### Remaining sorry (1 of 6):

6. **`SKDoubling.firstOrder_uniqueness`** — This theorem is **not provable with the current formalization**. The type `SKAction` allows arbitrary functions `SKFields → ℝ × ℝ`, but the physical uniqueness argument requires restricting to polynomial Lagrangians at a fixed derivative order. The three axioms (normalization, positivity, KMS) are insufficient to force an arbitrary function to equal the specific quadratic form of `firstOrderDissipativeAction`. A comment in the code explains what additional infrastructure would be needed: defining a type of "order-n polynomial SK actions" as a finite-dimensional vector space and showing the axioms reduce its dimension to 2.

### Build status
All files compile successfully (`lake build` passes). All proved declarations use only standard axioms (`propext`, `Classical.choice`, `Quot.sound`).