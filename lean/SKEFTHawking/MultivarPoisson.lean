/-
Phase 5q.B: foundations for [Θ1] — multivariate (`ℤᵈ`) Poisson summation.

[Θ1] is the analytic engine of the definite-case input [Θ] (`ThetaModularity.lean`): for a Schwartz function
`F : (d → ℝ) → ℂ`, `∑_{m ∈ ℤᵈ} F m = ∑_{n ∈ ℤᵈ} 𝓕F n`. The proof mirrors Mathlib's 1-D
`SchwartzMap.tsum_eq_tsum_fourier` in `d` dimensions, using the **`d`-torus Fourier series engine** that already
exists in Mathlib under the namespace `UnitAddTorus` (file `Mathlib/Analysis/Fourier/AddCircleMulti.lean`).

NOTE — corrects a stale reference: the engine is `UnitAddTorus.hasSum_mFourier_series_apply_of_summable`, **not**
`AddCircleMulti.hasSum_mFourier_series_of_summable` (the *file* is `AddCircleMulti`, the *namespace* is
`UnitAddTorus`). Verified API surface (Mathlib v4.29.1):
  • `UnitAddTorus d := d → UnitAddCircle`;  `mFourier (n : d → ℤ) : C(UnitAddTorus d, ℂ)`,
    `mFourier n x = ∏ i, fourier (n i) (x i)`.
  • `mFourierCoeff f n = ∫ t, mFourier (-n) t • f t`;  `mFourierCoeff_eq_integral` rewrites it as an integral
    over the fundamental domain `∏ i, (aᵢ, aᵢ+1]` (`integral_preimage`).
  • `hasSum_mFourier_series_apply_of_summable (h : Summable (mFourierCoeff f)) (x) :`
    `HasSum (fun i ↦ mFourierCoeff f i • mFourier i x) (f x)` — the pointwise Fourier inversion.

This module ships the first complete brick: evaluating that inversion at the torus origin `0`. Since
`mFourier i 0 = ∏ i, fourier _ 0 = 1`, the Fourier series at `0` collapses to the bare sum of coefficients,
giving `∑_{n} mFourierCoeff f n = f 0`. For Poisson one takes `f` = the `ℤᵈ`-periodisation of a Schwartz `F`;
then `f 0 = ∑_m F m` and (the remaining crux, the `d`-dim analog of `Real.fourierCoeff_tsum_comp_add`)
`mFourierCoeff f n = 𝓕F n`, whence Poisson. The crux periodisation lemma + its summability side conditions are
the substantial analytic builds that remain; this file pins the engine and the origin-collapse step.

VERIFIED ASSEMBLY RECIPE for the remaining crux `mFourierCoeff F♯ n = 𝓕F n` (every step a *named* Mathlib
lemma — so [Θ1] is reachable, NOT "multi-year / no substrate"):
  1. `mFourierCoeff F♯ n = ∫_{∏(0,1]} mFourier(-n)(x) · F♯(x)`  — `mFourierCoeff_eq_integral` (fundamental-domain
     integral over `{x | ∀ i, xᵢ ∈ Ioc 0 1}`).
  2. unfold `F♯(x) = ∑_{γ:ℤᵈ} F(x+γ)` and swap `∑`/`∫` — Tonelli/`tsum`-integral swap under Schwartz
     summability (analog of `intervalIntegral.tsum_intervalIntegral_eq_of_summable_norm`).
  3. ✅ SHIPPED (`integral_eq_tsum_zspan` below): glue translated cubes into all of `ℝᵈ` —
     `MeasureTheory.IsAddFundamentalDomain.integral_eq_tsum` (`∫_{ℝᵈ} g = ∑'_{γ} ∫_{γ+ᵥs} g`) with
     `s = ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d))` (`= [0,1)ᵈ`), fundamental-domain fact
     `ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ (Fin d))`, and `measurePreserving_add_left.setIntegral_image_emb`
     to pull each `∫_{γ+ᵥs}` back to `∫_s (·+γ)` (NB: instances passed positionally to dodge a `VAdd` diamond).
  4. ✅ SHIPPED (`latFourier` + `latFourier_eq_tsum` below): recognise the `ℝᵈ` Fourier integral. Using the
     direct on-`Fin d → ℝ` character integral `latFourier F n = ∫ exp(2πi·∑(-nᵢ)xᵢ)·F` (dodges the
     `EuclideanSpace` inner-product-space bridge), steps 3+4 combine into the right-hand reassembly
     `latFourier F n = ∑'_{g:Λ} ∫_{[0,1)ᵈ} exp(2πi·∑(-nᵢ)xᵢ)·F(↑g+x)` (`integral_eq_tsum_zspan` +
     `latChar_periodic`).
The Schwartz decay supplies all summability/integrability side conditions (`SchwartzMap` API +
`Real.fourierIntegral` of Schwartz is Schwartz). The anisotropic Gaussian `F = exp(-π xᵀAx)` (the [Θ2] target)
is Schwartz, so it feeds this engine directly.

REMAINING for full multivariate Poisson `∑_{γ} F γ = ∑_{n} latFourier F n`: the LEFT-hand side, steps 1+2 —
define the torus descent `F♯ : UnitAddTorus d → ℂ` of the periodisation `∑_γ F(·+γ)` (continuity + summable
Fourier coefficients from Schwartz decay), show `F♯ 0 = ∑_γ F γ`, and `mFourierCoeff F♯ n = latFourier F n` via
`mFourierCoeff_eq_integral` + the Tonelli `∫_cube ∑_γ = ∑_γ ∫_cube` swap (then `latFourier_eq_tsum`, modulo the
measure-zero `Ioc`-vs-`Ico` cube-boundary identification). Combined with `hasSum_mFourierCoeff_at_zero` (the
`∑_n mFourierCoeff F♯ n = F♯ 0` origin collapse) this yields Poisson.

All proofs are kernel-pure (`propext`/`Classical.choice`/`Quot.sound` only); no `native_decide`, no
`maxHeartbeats`, no axiom.
-/

import Mathlib

namespace SKEFTHawking

open UnitAddTorus MeasureTheory
open scoped Real

/-- **`ℤᵈ`-lattice integral unfolding** (recipe step 3): for an integrable `f : (Fin d → ℝ) → ℂ`, the integral
over `ℝᵈ` is the sum, over the standard integer lattice `Λ = span ℤ (range (Pi.basisFun))`, of the integrals of
the translates `x ↦ f (γ + x)` over the half-open unit cube `ZSpan.fundamentalDomain`. This is the multivariate
analog of the 1-D `Integrable.hasSum_intervalIntegral_comp_add_int`, assembled from
`MeasureTheory.IsAddFundamentalDomain.integral_eq_tsum` (`ZSpan.isAddFundamentalDomain`) plus the
measure-preserving left translation `measurePreserving_add_left`. The lattice-action `MeasurableConstVAdd` /
`VAddInvariantMeasure` instances are supplied explicitly (passed positionally to `integral_eq_tsum`) to dodge a
`VAdd` typeclass diamond on the submodule action. -/
theorem integral_eq_tsum_zspan {d : ℕ} {f : (Fin d → ℝ) → ℂ} (hf : Integrable f) :
    ∫ x, f x = ∑' (g : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d))))),
      ∫ x in ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d)), f ((g : Fin d → ℝ) + x) := by
  haveI hmcv : MeasurableConstVAdd (↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d))))) (Fin d → ℝ) := by
    constructor; intro c; exact measurable_const_add (c : Fin d → ℝ)
  haveI hvim :
      VAddInvariantMeasure (↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d))))) (Fin d → ℝ) volume := by
    constructor; intro c s hs; exact measure_preimage_add volume (c : Fin d → ℝ) s
  rw [@IsAddFundamentalDomain.integral_eq_tsum _ (Fin d → ℝ) ℂ _ _ _ _
        (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d))) volume hmcv hvim _ _
        (ZSpan.isAddFundamentalDomain (Pi.basisFun ℝ (Fin d)) volume) f hf]
  refine tsum_congr fun g => ?_
  have hmp := measurePreserving_add_left (volume : Measure (Fin d → ℝ)) (g : Fin d → ℝ)
  have hemb := measurableEmbedding_addLeft (G := Fin d → ℝ) (g : Fin d → ℝ)
  exact hmp.setIntegral_image_emb hemb f (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d)))

/-- The multivariate exponential monomial is `1` at the torus origin: `mFourier i 0 = ∏ fourier _ 0 = 1`. -/
theorem mFourier_eval_zero {d : Type*} [Fintype d] (i : d → ℤ) :
    mFourier i (0 : UnitAddTorus d) = 1 := by
  simp only [mFourier, ContinuousMap.coe_mk]
  exact Finset.prod_eq_one fun k _ => by simp

/-- **Origin-collapse of the `d`-torus Fourier series.** If the Fourier coefficients of a continuous function
`f` on the `d`-torus are summable, their sum is the value of `f` at the origin: `∑_n mFourierCoeff f n = f 0`.
This is the step that, applied to the `ℤᵈ`-periodisation of a Schwartz function, yields the right-hand side
`∑_m F m` of the multivariate Poisson summation formula. -/
theorem hasSum_mFourierCoeff_at_zero {d : Type*} [Fintype d] {f : C(UnitAddTorus d, ℂ)}
    (h : Summable (mFourierCoeff f)) : HasSum (mFourierCoeff f) (f 0) := by
  have key := hasSum_mFourier_series_apply_of_summable h (0 : UnitAddTorus d)
  simp only [mFourier_eval_zero, smul_eq_mul, mul_one] at key
  exact key

/-- `tsum` form of `hasSum_mFourierCoeff_at_zero`: `∑' n, mFourierCoeff f n = f 0`. -/
theorem tsum_mFourierCoeff_at_zero {d : Type*} [Fintype d] {f : C(UnitAddTorus d, ℂ)}
    (h : Summable (mFourierCoeff f)) : ∑' n, mFourierCoeff f n = f 0 :=
  (hasSum_mFourierCoeff_at_zero h).tsum_eq

/-- A point of the standard integer lattice `Λ = span ℤ (range (Pi.basisFun ℝ (Fin d)))` has integer
coordinates: `(↑g) i = (k : ℝ)` for some `k : ℤ`. (Recipe-step-1+2 helper for the Tonelli unfold.) -/
theorem zspan_coord_int {d : ℕ} (g : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d))))) (i : Fin d) :
    ∃ k : ℤ, (g : Fin d → ℝ) i = (k : ℝ) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp g.2
  refine ⟨c i, ?_⟩
  have h : (g : Fin d → ℝ) = ∑ j, c j • (Pi.basisFun ℝ (Fin d)) j := hc.symm
  rw [h]; simp [Pi.basisFun_apply, Pi.single_apply, mul_ite]

/-- **Lattice-periodicity of the pulled-back torus character.** The character `x ↦ ∏ᵢ fourier(-nᵢ)(xᵢ)` — the
pullback to `ℝᵈ` of the torus monomial `mFourier (-n)` — is invariant under translation by a point `g` of the
standard integer lattice, because integer coordinates vanish in `ℝ/ℤ`. This is the character-periodicity step of
the multivariate Poisson crux: in `mFourierCoeff F♯ n = ∫_{∏(0,1]} mFourier(-n)·F♯`, after the Tonelli unfold
the character on each translate `↑g + x` collapses to the character on `x`, so the lattice sum of
fundamental-domain integrals reassembles (via `integral_eq_tsum_zspan`) into the full `ℝᵈ` Fourier integral. -/
theorem mFourier_pullback_lattice_periodic {d : ℕ} (n : Fin d → ℤ)
    (g : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d))))) (x : Fin d → ℝ) :
    (∏ i, (fourier (-(n i)) ((((g : Fin d → ℝ) + x) i : ℝ) : UnitAddCircle)))
    = ∏ i, (fourier (-(n i)) ((x i : ℝ) : UnitAddCircle)) := by
  refine Finset.prod_congr rfl fun i _ => ?_
  obtain ⟨k, hk⟩ := zspan_coord_int g i
  have hxi : (((g : Fin d → ℝ) + x) i : ℝ) = x i + (k : ℝ) := by simp [hk]; ring
  rw [hxi]
  congr 1
  have h0 : ((k : ℝ) : AddCircle (1:ℝ)) = 0 := by
    rw [AddCircle.coe_eq_zero_iff]; exact ⟨k, by rw [zsmul_eq_mul]; ring⟩
  rw [AddCircle.coe_add, h0, add_zero]

/-- The lattice sum `∑ᵢ (-nᵢ)·(↑g)ᵢ` of a lattice point `g` is an integer (its coordinates are integers). -/
theorem latticeSum_int {d : ℕ} (n : Fin d → ℤ)
    (g : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d))))) :
    ∃ M : ℤ, (∑ i, (-(n i) : ℝ) * (g : Fin d → ℝ) i) = (M : ℝ) := by
  obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℤ).mp g.2
  have hcoord : ∀ i, (g : Fin d → ℝ) i = (c i : ℝ) := by
    intro i
    have h : (g : Fin d → ℝ) = ∑ j, c j • (Pi.basisFun ℝ (Fin d)) j := hc.symm
    rw [h]; simp [Pi.basisFun_apply, Pi.single_apply, mul_ite]
  refine ⟨∑ i, -(n i) * c i, ?_⟩
  push_cast
  exact Finset.sum_congr rfl fun i _ => by rw [hcoord i]

/-- **Exponential-form lattice character periodicity.** The explicit ℝᵈ character `x ↦ exp(2πi·∑ᵢ(-nᵢ)xᵢ)` is
invariant under translation by a lattice point `g` (its phase shifts by an integer multiple of `2πi`). The
`Complex.exp` companion of `mFourier_pullback_lattice_periodic`, used directly with `latFourier` below. -/
theorem latChar_periodic {d : ℕ} (n : Fin d → ℤ)
    (g : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d))))) (x : Fin d → ℝ) :
    Complex.exp (2 * π * Complex.I * (∑ i, (-(n i) : ℝ) * ((g : Fin d → ℝ) + x) i))
    = Complex.exp (2 * π * Complex.I * (∑ i, (-(n i) : ℝ) * x i)) := by
  obtain ⟨M, hM⟩ := latticeSum_int n g
  have hsplit : (∑ i, (-(n i) : ℝ) * ((g : Fin d → ℝ) + x) i)
      = (∑ i, (-(n i) : ℝ) * (g : Fin d → ℝ) i) + (∑ i, (-(n i) : ℝ) * x i) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [Pi.add_apply]; ring
  rw [hsplit, hM]; push_cast
  rw [mul_add, Complex.exp_add,
      show 2 * (π : ℂ) * Complex.I * (M : ℂ) = (M : ℂ) * (2 * (π : ℂ) * Complex.I) by ring,
      Complex.exp_int_mul_two_pi_mul_I, one_mul]

/-- The **lattice Fourier integral** of `F : (Fin d → ℝ) → ℂ` at `n : ℤᵈ`, written directly on `Fin d → ℝ`
(standard `2π` convention, character `exp(2πi·∑ᵢ(-nᵢ)xᵢ)`). Stated on `Fin d → ℝ` rather than
`EuclideanSpace ℝ (Fin d)` to match the lattice/`ZSpan` substrate without an inner-product-space type bridge;
on `ℤᵈ` lattice points it agrees with Mathlib's `Real.fourierIntegral`. -/
noncomputable def latFourier {d : ℕ} (F : (Fin d → ℝ) → ℂ) (n : Fin d → ℤ) : ℂ :=
  ∫ x, Complex.exp (2 * π * Complex.I * (∑ i, (-(n i) : ℝ) * x i)) * F x

/-- **Lattice Fourier integral as a lattice sum of fundamental-domain integrals** (Poisson recipe steps 3+4,
right-hand reassembly): `latFourier F n = ∑'_{g:Λ} ∫_{[0,1)ᵈ} exp(2πi·∑ᵢ(-nᵢ)xᵢ)·F(↑g+x)`. Combines the cube
unfold (`integral_eq_tsum_zspan`) with character lattice-periodicity (`latChar_periodic`, which lets the
character on each translate `↑g+x` collapse to the character on `x`). This is exactly the right-hand side that
the periodised-Fourier-coefficient computation `mFourierCoeff F♯ n` (the remaining left-hand step, via Tonelli)
must equal — so once that lands, `mFourierCoeff F♯ n = latFourier F n`, the Poisson crux. -/
theorem latFourier_eq_tsum {d : ℕ} (F : (Fin d → ℝ) → ℂ) (n : Fin d → ℤ)
    (hF : Integrable (fun x => Complex.exp (2 * π * Complex.I * (∑ i, (-(n i) : ℝ) * x i)) * F x)) :
    latFourier F n = ∑' (g : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d))))),
      ∫ x in ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d)),
        Complex.exp (2 * π * Complex.I * (∑ i, (-(n i) : ℝ) * x i)) * F ((g : Fin d → ℝ) + x) := by
  rw [latFourier, integral_eq_tsum_zspan hF]
  refine tsum_congr fun g => ?_
  congr 1
  funext x
  rw [latChar_periodic]

/-- The **periodisation** of `F : (Fin d → ℝ) → ℂ`: `x ↦ ∑'_{γ∈Λ} F(x + ↑γ)`, summed over the standard
integer lattice `Λ`. This is the function that descends to the torus as `F♯`; its torus Fourier coefficients are
the values `latFourier F n` (the Poisson crux), and its value at `0` is `∑_γ F γ` (the Poisson LHS). -/
noncomputable def periodisation {d : ℕ} (F : (Fin d → ℝ) → ℂ) (x : Fin d → ℝ) : ℂ :=
  ∑' (γ : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d))))), F (x + (γ : Fin d → ℝ))

/-- **Lattice-periodicity of the periodisation** (the descent-enabling property): `periodisation F` is invariant
under translation by any lattice point `g₀`, since the lattice sum reindexes by the bijection `γ ↦ g₀ + γ`. This
is what lets `periodisation F` descend to a function `F♯ : UnitAddTorus d → ℂ` on the `d`-torus `ℝᵈ/ℤᵈ`.
(Continuity of `F♯` — the remaining descent ingredient needed to invoke `hasSum_mFourierCoeff_at_zero` — requires
locally-uniform summability of the family `γ ↦ F(·+ ↑γ)` on the compact torus, which `continuous_tsum`'s global
uniform bound does NOT supply; it follows instead from Schwartz/Gaussian decay, the next analytic step.) -/
theorem periodisation_lattice_periodic {d : ℕ} (F : (Fin d → ℝ) → ℂ)
    (g₀ : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d))))) (x : Fin d → ℝ) :
    periodisation F (x + (g₀ : Fin d → ℝ)) = periodisation F x := by
  unfold periodisation
  conv_rhs => rw [← Equiv.tsum_eq (Equiv.addLeft g₀)]
  refine tsum_congr fun γ => ?_
  congr 1
  simp only [Equiv.coe_addLeft]
  exact add_assoc x _ _

/-- **The continuous periodisation** of a continuous `F : C(Fin d → ℝ, ℂ)` as a bundled continuous map
`∑'_{γ∈Λ} F(· + ↑γ)`, built via `ContinuousMap.tsum` of the translates `F.comp (addRight ↑γ)`. As a bundled
`ContinuousMap` it is automatically continuous; under the locally-uniform summability hypothesis (next lemma)
its values are the periodisation `∑'_γ F(x+↑γ)`. This is the continuity ingredient of the torus descent
(`continuous_tsum`'s global uniform bound fails for periodisations; `ContinuousMap.summable_of_locally_summable_norm`
supplies the locally-uniform — compact-open — convergence that does hold). -/
noncomputable def periodisationCM {d : ℕ} (F : C(Fin d → ℝ, ℂ)) : C(Fin d → ℝ, ℂ) :=
  ∑' γ : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d)))),
    F.comp (ContinuousMap.addRight (γ : Fin d → ℝ))

/-- **Value of the continuous periodisation.** Given locally-uniform (compact-open) summability of the lattice
family of translates `γ ↦ F(· + ↑γ)` (the hypothesis `hF`, dischargeable from Schwartz/Gaussian decay), the
bundled continuous periodisation evaluates to the pointwise periodisation `∑'_{γ∈Λ} F(x + ↑γ)` (= `periodisation
(⇑F) x`). Together with `periodisation_lattice_periodic` (ℤᵈ-periodicity) this packages the continuous,
ℤᵈ-periodic function that descends to `F♯ : C(UnitAddTorus d, ℂ)` for the Poisson Fourier-series argument. -/
theorem periodisationCM_apply {d : ℕ} (F : C(Fin d → ℝ, ℂ))
    (hF : ∀ K : TopologicalSpace.Compacts (Fin d → ℝ),
      Summable fun γ : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d)))) =>
        ‖(F.comp (ContinuousMap.addRight (γ : Fin d → ℝ))).restrict K‖) (x : Fin d → ℝ) :
    periodisationCM F x
      = ∑' γ : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d)))), F (x + (γ : Fin d → ℝ)) := by
  rw [periodisationCM, ← ContinuousMap.tsum_apply (ContinuousMap.summable_of_locally_summable_norm hF) x]
  exact tsum_congr fun γ => rfl

/-- **The Poisson crux computation (Tonelli), torus-free.** The fundamental-domain integral of the character
against the periodisation equals the lattice Fourier integral:
`∫_{[0,1)ᵈ} exp(2πi·∑(-nᵢ)xᵢ)·(∑'_{γ} F(x+↑γ)) dx = latFourier F n`. Proof: pull the character inside the
lattice sum (`tsum_mul_left`, unconditional), swap integral and sum (`MeasureTheory.integral_tsum` under the
`L¹` summability `hLsum`), then reassemble via `latFourier_eq_tsum` (`add_comm` matches `F(x+↑γ)` to
`F(↑γ+x)`). This is the substantive heart of the multivariate Poisson formula — it needs NO torus descent; the
torus enters only to read the left side as `mFourierCoeff F♯ n` and to invoke Fourier inversion. The hypotheses
(`hFint` integrability, `hmeas` measurability of each translate, `hLsum` `L¹`-summability over the lattice) are
all discharged by Schwartz/Gaussian decay at application time. -/
theorem cube_integral_char_periodisation {d : ℕ} (F : (Fin d → ℝ) → ℂ) (n : Fin d → ℤ)
    (hFint : Integrable (fun x => Complex.exp (2 * π * Complex.I * (∑ i, (-(n i) : ℝ) * x i)) * F x))
    (hmeas : ∀ γ : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d)))),
      AEStronglyMeasurable
        (fun x => Complex.exp (2 * π * Complex.I * (∑ i, (-(n i) : ℝ) * x i)) * F (x + (γ : Fin d → ℝ)))
        (volume.restrict (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d)))))
    (hLsum : ∑' γ : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d)))),
        ∫⁻ x in ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d)),
          ‖Complex.exp (2 * π * Complex.I * (∑ i, (-(n i) : ℝ) * x i)) * F (x + (γ : Fin d → ℝ))‖ₑ ≠ ⊤) :
    (∫ x in ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d)),
        Complex.exp (2 * π * Complex.I * (∑ i, (-(n i) : ℝ) * x i)) * periodisation F x)
      = latFourier F n := by
  have hstep : (∫ x in ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d)),
        Complex.exp (2 * π * Complex.I * (∑ i, (-(n i) : ℝ) * x i)) * periodisation F x)
      = ∑' γ : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d)))),
        ∫ x in ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d)),
          Complex.exp (2 * π * Complex.I * (∑ i, (-(n i) : ℝ) * x i)) * F (x + (γ : Fin d → ℝ)) := by
    rw [← integral_tsum hmeas hLsum]
    refine setIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet _) fun x _ => ?_
    rw [periodisation, tsum_mul_left]
  rw [hstep, latFourier_eq_tsum F n hFint]
  refine tsum_congr fun γ => ?_
  refine setIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet _) fun x _ => ?_
  rw [add_comm (x : Fin d → ℝ) (γ : Fin d → ℝ)]

/-- **The `d`-torus covering map `(Fin d → ℝ) → UnitAddTorus (Fin d)` is an open quotient map.** It is the
`Pi.map` of the coordinatewise `AddCircle` quotient `↑ : ℝ → AddCircle 1` (each `QuotientAddGroup.isOpenQuotientMap
_mk`), and a finite product of open quotient maps is an open quotient map (`IsOpenQuotientMap.piMap`). This is the
descent vehicle: a continuous `ℤᵈ`-periodic function on `ℝᵈ` (e.g. `periodisationCM F`) descends through it to a
continuous `F♯ : C(UnitAddTorus (Fin d), ℂ)`. -/
theorem torus_isOpenQuotientMap {d : ℕ} :
    IsOpenQuotientMap (Pi.map (fun (_ : Fin d) => ((↑) : ℝ → AddCircle (1 : ℝ)))) :=
  IsOpenQuotientMap.piMap (fun _ => QuotientAddGroup.isOpenQuotientMap_mk)

/-- **Fiber characterization of the torus covering map**: two points of `ℝᵈ` with the same image on the torus
differ by an integer in each coordinate. Combined with `periodisation_lattice_periodic` (`ℤᵈ`-periodicity) this
gives fiber-constancy of the periodisation — the hypothesis for descending it through `torus_isOpenQuotientMap`. -/
theorem torus_fiber_coord {d : ℕ} (x y : Fin d → ℝ)
    (h : Pi.map (fun (_ : Fin d) => ((↑) : ℝ → AddCircle (1 : ℝ))) x
       = Pi.map (fun (_ : Fin d) => ((↑) : ℝ → AddCircle (1 : ℝ))) y) (i : Fin d) :
    ∃ k : ℤ, x i - y i = (k : ℝ) := by
  have hi : ((x i : ℝ) : AddCircle (1:ℝ)) = ((y i : ℝ) : AddCircle (1:ℝ)) := congrFun h i
  have hz : ((x i - y i : ℝ) : AddCircle (1:ℝ)) = 0 := by
    rw [AddCircle.coe_sub, hi, sub_self]
  rw [AddCircle.coe_eq_zero_iff] at hz
  obtain ⟨k, hk⟩ := hz
  exact ⟨k, by rw [← hk, zsmul_eq_mul]; ring⟩

/-- **Fiber-constancy of the continuous periodisation.** Under the locally-uniform summability hypothesis `hF`,
`periodisationCM F` takes equal values on points with the same torus image (`q x = q y`): they differ by an
integer vector `c` (`torus_fiber_coord`), which lies in the lattice `Λ` (`= ∑ cᵢ • basisFunᵢ`), so the values
agree by `periodisation_lattice_periodic` (after `periodisationCM_apply`). This is the descent hypothesis for
lifting through `torus_isOpenQuotientMap`. -/
theorem periodisationCM_fiber_const {d : ℕ} (F : C(Fin d → ℝ, ℂ))
    (hF : ∀ K : TopologicalSpace.Compacts (Fin d → ℝ),
      Summable fun γ : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d)))) =>
        ‖(F.comp (ContinuousMap.addRight (γ : Fin d → ℝ))).restrict K‖)
    (x y : Fin d → ℝ)
    (h : Pi.map (fun (_ : Fin d) => ((↑) : ℝ → AddCircle (1 : ℝ))) x
       = Pi.map (fun (_ : Fin d) => ((↑) : ℝ → AddCircle (1 : ℝ))) y) :
    periodisationCM F x = periodisationCM F y := by
  choose c hc using torus_fiber_coord x y h
  have hmem : (fun i => (c i : ℝ)) ∈ Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d))) := by
    rw [Submodule.mem_span_range_iff_exists_fun]
    exact ⟨c, by funext i; simp [Pi.basisFun_apply, Pi.single_apply, mul_ite]⟩
  set g₀ : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d)))) := ⟨fun i => (c i : ℝ), hmem⟩ with hg₀
  have hxy : x = y + (g₀ : Fin d → ℝ) := by
    funext i
    have hi : x i - y i = (c i : ℝ) := hc i
    simp only [hg₀, Pi.add_apply]
    show x i = y i + (c i : ℝ)
    linarith
  rw [periodisationCM_apply F hF x, periodisationCM_apply F hF y, hxy]
  exact periodisation_lattice_periodic (fun z => F z) g₀ y

/- The torus descent `F♯ : C(UnitAddTorus (Fin d), ℂ)` of the periodisation is built in the companion module
`SKEFTHawking.MultivarPoissonDescent` (which imports this one), so that `periodisationCM` is opaque there — its
`coe`-`rfl` apply lemma would otherwise unfold the heavy in-file `tsum` and blow the heartbeat limit. -/

end SKEFTHawking
