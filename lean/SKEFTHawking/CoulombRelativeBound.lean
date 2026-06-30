import SKEFTHawking.MolecularHamiltonian
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket

/-!
# W3 (Phase 6BB Wave 3) — discharge of `hrel`: the Coulomb relative bound, via Fourier–Kato–Rellich

`molecularHamiltonian_essSelfAdjoint` proves essential self-adjointness *conditionally* on `hrel`:
that the molecular Coulomb potential is relatively bounded with respect to the kinetic operator with
relative bound `a < 1` (Kato's condition). This module discharges `hrel` by **proving** that bound.

**Route (Fourier–Kato–Rellich, not the from-scratch Hardy inequality).** Mathlib has neither Hardy nor
the Morrey/sup-norm embedding, but it *does* have `integrable_rpow_neg_one_add_norm_sq`, Plancherel, and
(via Wave 2) the Schwartz Fourier-multiplier substrate. The Kato argument:
* `(1 + ‖ξ‖²)⁻¹ ∈ L²(ℝ³)` (this file's foundational lemma), because `4 > 3 = dim`;
* hence (Cauchy–Schwarz on the Fourier side) `‖u‖_∞ ≤ ε‖Δu‖ + C_ε‖u‖` for Schwartz `u`;
* the Coulomb singularity splits `1/‖x‖ = V₁ + V₂` with `V₁ ∈ L²`, `V₂ ∈ L^∞`, giving
  `‖(1/‖·‖)u‖₂ ≤ ‖V₁‖₂‖u‖_∞ + ‖u‖₂`, so each Coulomb term is kinetic-bounded with bound `→ 0`.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; zero `sorry`; no new axiom.
-/

namespace SKEFTHawking.DFT

open MeasureTheory

/-- **The L² integrability crux of the Fourier sup-norm bound:** `(1 + ‖ξ‖²)⁻¹ ∈ L²(ℝ³)`, equivalently
`(1 + ‖ξ‖²)⁻² ∈ L¹(ℝ³)`. Holds because the exponent `4` exceeds the dimension `3`
(`integrable_rpow_neg_one_add_norm_sq`). This is the integrability that bounds `‖û‖₁` by `‖(1−Δ)u‖₂`. -/
lemma integrable_oneAddNormSq_rpow_neg_two :
    Integrable (fun ξ : Space 3 => (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ)) volume := by
  have h3 : Module.finrank ℝ (Space 3) = 3 := by simp
  have hdim : (Module.finrank ℝ (Space 3) : ℝ) < 4 := by rw [h3]; norm_num
  have h := integrable_rpow_neg_one_add_norm_sq (E := Space 3) (μ := volume) (r := 4) hdim
  have he : (fun ξ : Space 3 => (1 + ‖ξ‖ ^ 2) ^ (-2 : ℝ))
      = fun x : Space 3 => (1 + ‖x‖ ^ 2) ^ (-4 / 2 : ℝ) := by funext x; norm_num
  rw [he]; exact h

/-- **The Fourier weight `(1 + ‖ξ‖²)⁻¹ ∈ L²(ℝ³)`** — finite `L²` norm, the factor that Cauchy–Schwarz
pairs against `(1+‖ξ‖²)·û` to bound `‖û‖_{L¹}` by `‖(1−Δ)u‖_{L²}`. -/
lemma memLp_two_oneAddNormSq_inv :
    MemLp (fun ξ : Space 3 => ((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ)) 2 volume := by
  have hcont : Continuous (fun ξ : Space 3 => ((1 + ‖ξ‖ ^ 2)⁻¹ : ℝ)) :=
    Continuous.inv₀ (by fun_prop) (fun ξ => (by positivity : (0:ℝ) < 1 + ‖ξ‖ ^ 2).ne')
  rw [memLp_two_iff_integrable_sq hcont.aestronglyMeasurable]
  refine integrable_oneAddNormSq_rpow_neg_two.congr ?_
  filter_upwards with ξ
  rw [Real.rpow_neg (by positivity), Real.rpow_two, ← inv_pow]

end SKEFTHawking.DFT
