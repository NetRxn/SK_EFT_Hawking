/-
# Phase 5q.F brick 6c — singular excision: Lebesgue smallness → small chains

The capstone of the barycentric-subdivision engine. `SingularSubdivision` built the singular `Sd` as a
chain map with the chain homotopy `∂D+D∂ = 1−Sd` (so `Sdᵐ` is chain-homotopic to the identity), and
`SingularSubdivisionDiameter` proved the affine subdivision contracts diameter by `n/(n+1)`. This file
joins them: via the iterate connection `Sdᵐ[σ] = σ_#((Sd_aff)ᵐ ιₙ)` a piece of `Sdᵐσ` is `σ` composed
with an affine sub-simplex of arbitrarily small diameter, so — by uniform continuity of `σ` on the
compact `Δⁿ` and a Lebesgue number for an open cover — enough subdivisions make every simplex of a chain
"small" (subordinate to the cover). With the chain homotopy this gives **excision**.

This is the engine for the local homology `Hₙ(M, M∖x) ≅ ℤ/2` (brick 6d), hence the ℤ/2 fundamental class
(6e) and the Poincaré-duality datum `PoincareDual4Mid` (6f). Kernel-pure.
-/
import Mathlib
import SKEFTHawking.SingularSubdivision
import SKEFTHawking.SingularSubdivisionDiameter
import SKEFTHawking.SingularRelativeHomologyMod2

namespace SKEFTHawking.SingularExcision

open CategoryTheory Opposite
open SKEFTHawking.SingularExcisionMod2 SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularExcisionPushforward SKEFTHawking.SingularSubdivisionConvex
open SKEFTHawking.SingularSubdivision SKEFTHawking.SingularSubdivisionDiameter

/-- The standard `n`-simplex's vertices `eᵢ = Pi.single i 1` have all pairwise sup-norm distances `≤ 1`
(`(eᵢ − eₖ) l ∈ {−1, 0, 1}`), so the identity affine chain `ιₙ` has diameter `≤ 1`. The seed the
iterated-subdivision shrinkage acts on. -/
theorem idChain_diamLe (n : ℕ) : diamLe (1 : ℝ) (idChain n) := by
  rw [idChain]
  refine diamLe_single (fun i k => ?_)
  rw [pi_norm_le_iff_of_nonneg zero_le_one]
  intro l
  simp only [Pi.sub_apply, Pi.single_apply, Real.norm_eq_abs]
  split_ifs <;> norm_num

/-- **Arbitrarily fine subdivision of the model simplex**: for any `ε > 0`, enough barycentric
subdivisions make every affine sub-simplex of `ιₙ` have diameter `< ε` (the contraction factor
`(n/(n+1))ᵐ → 0`). The geometric smallness input the Lebesgue-number step consumes. -/
theorem exists_iterate_idChain_diamLe (n : ℕ) {ε : ℝ} (hε : 0 < ε) :
    ∃ m, diamLe ε ((⇑(linSubdiv n))^[m] (idChain n)) :=
  exists_iterate_diamLe (idChain_diamLe n) hε

end SKEFTHawking.SingularExcision
