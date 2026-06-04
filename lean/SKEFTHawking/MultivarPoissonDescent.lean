/-
Phase 5q.B: the torus descent `F♯` for the multivariate Poisson summation formula.

This is the structural companion to `MultivarPoisson` (which holds the analytic content). The continuous,
`ℤᵈ`-periodic periodisation `periodisationCM F` descends through the open quotient (covering) map
`q : (Fin d → ℝ) → UnitAddTorus (Fin d)` to a continuous function `F♯ = torusDescent F _` on the `d`-torus —
the `C(UnitAddTorus (Fin d), ℂ)` consumed by the torus Fourier inversion `hasSum_mFourierCoeff_at_zero`.

It lives in a separate module ON PURPOSE: here `periodisationCM` is *imported* (hence opaque to the elaborator),
so the descent's `coe`-`rfl` apply lemma (`torusDescent_apply`) is cheap. In the defining module `periodisationCM`
is transparent and the same `rfl` unfolds the heavy `tsum`, blowing the heartbeat limit (which we may not raise,
Pipeline invariant #10). Two further engineering points: the section is the *concrete* `Ioc`-representative
(`AddCircle.equivIoc`), not `Function.surjInv` (whose reduction over the `piMap` quotient is also too heavy); and
the continuity hypothesis is an *explicit/atomic* argument to `torusDescent` (embedding the proof term in the def
body reintroduces the defeq blowup).

All proofs are kernel-pure (`propext`/`Classical.choice`/`Quot.sound` only); no `native_decide`, no
`maxHeartbeats`, no axiom.
-/

import Mathlib
import SKEFTHawking.MultivarPoisson

namespace SKEFTHawking

open UnitAddTorus MeasureTheory
open scoped Real

/-- The **concrete section** of the torus covering map: the `Ioc`-representative in each coordinate
(`AddCircle.equivIoc`). Used to bundle the descent without `Function.surjInv`. -/
noncomputable def torusRep {d : ℕ} (t : UnitAddTorus (Fin d)) : Fin d → ℝ :=
  fun i => (AddCircle.equivIoc (1 : ℝ) 0 (t i) : ℝ)

/-- **The torus descent `F♯`** of `F`: the continuous function on `UnitAddTorus (Fin d)` obtained by descending
the continuous, `ℤᵈ`-periodic `periodisationCM F` through the covering map. The continuity hypothesis `hc` is an
explicit/atomic argument (discharge with `torusDescent_continuous F hF`), keeping the apply lemma a cheap `rfl`. -/
noncomputable def torusDescent {d : ℕ} (F : C(Fin d → ℝ, ℂ))
    (hc : Continuous (periodisationCM F ∘ torusRep)) : C(UnitAddTorus (Fin d), ℂ) :=
  ⟨periodisationCM F ∘ torusRep, hc⟩

/-- Value of the descent on a representative: `F♯ t = periodisationCM F (torusRep t)`. -/
theorem torusDescent_apply {d : ℕ} (F : C(Fin d → ℝ, ℂ))
    (hc : Continuous (periodisationCM F ∘ torusRep)) (t : UnitAddTorus (Fin d)) :
    torusDescent F hc t = periodisationCM F (torusRep t) := rfl

/-- `torusRep` is a section of the covering map `q`: `q (torusRep t) = t`. -/
theorem q_torusRep {d : ℕ} (t : UnitAddTorus (Fin d)) :
    Pi.map (fun (_ : Fin d) => ((↑) : ℝ → AddCircle (1 : ℝ))) (torusRep t) = t := by
  funext i
  simp only [Pi.map_apply, torusRep]
  have h := (AddCircle.equivIoc (1 : ℝ) 0).symm_apply_apply (t i)
  rw [AddCircle.equivIoc, QuotientAddGroup.equivIocMod_symm_apply] at h
  exact h

/-- Continuity of `periodisationCM F ∘ torusRep`: by the quotient-map criterion
(`isQuotientMap.continuous_iff`), the composite with `q` equals the continuous `periodisationCM F`
(fiber-constancy via `periodisationCM_fiber_const` and the section identity `q_torusRep`). -/
theorem torusDescent_continuous {d : ℕ} (F : C(Fin d → ℝ, ℂ))
    (hF : ∀ K : TopologicalSpace.Compacts (Fin d → ℝ),
      Summable fun γ : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d)))) =>
        ‖(F.comp (ContinuousMap.addRight (γ : Fin d → ℝ))).restrict K‖) :
    Continuous (periodisationCM F ∘ torusRep) := by
  rw [torus_isOpenQuotientMap.isQuotientMap.continuous_iff]
  have hcomp : (periodisationCM F ∘ torusRep)
        ∘ (Pi.map (fun (_ : Fin d) => ((↑) : ℝ → AddCircle (1 : ℝ)))) = periodisationCM F := by
    funext x
    exact periodisationCM_fiber_const F hF _ x (by rw [q_torusRep])
  rw [hcomp]
  exact (periodisationCM F).continuous

/-- **Defining property of the descent**: `F♯ (q x) = periodisationCM F x` for the covering map `q`
(fiber-constancy collapses `torusRep (q x)` back to `x`). -/
theorem torusDescent_comp {d : ℕ} (F : C(Fin d → ℝ, ℂ))
    (hc : Continuous (periodisationCM F ∘ torusRep))
    (hF : ∀ K : TopologicalSpace.Compacts (Fin d → ℝ),
      Summable fun γ : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d)))) =>
        ‖(F.comp (ContinuousMap.addRight (γ : Fin d → ℝ))).restrict K‖) (x : Fin d → ℝ) :
    torusDescent F hc
        (Pi.map (fun (_ : Fin d) => ((↑) : ℝ → AddCircle (1 : ℝ))) x) = periodisationCM F x := by
  rw [torusDescent_apply]
  exact periodisationCM_fiber_const F hF _ x (by rw [q_torusRep])

/-- The covering map sends `0` to `0`. -/
theorem q_zero {d : ℕ} :
    Pi.map (fun (_ : Fin d) => ((↑) : ℝ → AddCircle (1 : ℝ))) (0 : Fin d → ℝ)
      = (0 : UnitAddTorus (Fin d)) := by
  funext i; simp [Pi.map_apply]

/-- **Poisson LHS — value of the descent at the torus origin**: `F♯ 0 = ∑'_{γ∈Λ} F(↑γ)`. Since `0 = q 0`,
`torusDescent_comp` gives `periodisationCM F 0 = ∑'_γ F(0 + ↑γ) = ∑'_γ F(↑γ)`. The `∑'_n mFourierCoeff F♯ n`
(Fourier inversion at the origin, `hasSum_mFourierCoeff_at_zero`) equals this — the left-hand side of the
multivariate Poisson summation formula. -/
theorem torusDescent_at_zero {d : ℕ} (F : C(Fin d → ℝ, ℂ))
    (hc : Continuous (periodisationCM F ∘ torusRep))
    (hF : ∀ K : TopologicalSpace.Compacts (Fin d → ℝ),
      Summable fun γ : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d)))) =>
        ‖(F.comp (ContinuousMap.addRight (γ : Fin d → ℝ))).restrict K‖) :
    torusDescent F hc (0 : UnitAddTorus (Fin d))
      = ∑' γ : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d)))), F (γ : Fin d → ℝ) := by
  rw [← q_zero, torusDescent_comp F hc hF, periodisationCM_apply F hF]
  refine tsum_congr fun γ => ?_
  rw [zero_add]

/-- The torus monomial pulled back along the covering map is the explicit `ℝᵈ` character:
`mFourier (-n) (q x) = exp(2πi·∑ᵢ(-nᵢ)xᵢ)` (each `fourier (-nᵢ) (↑xᵢ) = exp(2πi(-nᵢ)xᵢ)` via `fourier_coe_apply`,
multiplied over coordinates). Bridges the `UnitAddTorus` Fourier coefficient `mFourierCoeff (torusDescent F hc) n`
to the lattice Fourier integral `latFourier F n`. -/
theorem mFourier_q_eq_char {d : ℕ} (n : Fin d → ℤ) (x : Fin d → ℝ) :
    mFourier (-n) (Pi.map (fun (_ : Fin d) => ((↑) : ℝ → AddCircle (1 : ℝ))) x)
      = Complex.exp (2 * π * Complex.I * (∑ i, (-(n i) : ℝ) * x i)) := by
  simp only [mFourier, ContinuousMap.coe_mk, Pi.map_apply, Pi.neg_apply]
  rw [Complex.ofReal_sum, Finset.mul_sum, Complex.exp_sum]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [fourier_coe_apply]
  push_cast
  ring_nf

/-- **The torus Fourier coefficient of the descent equals the lattice Fourier integral** (Poisson recipe
LHS, steps 1+2): `mFourierCoeff (torusDescent F hc) n = latFourier F n`. Chains five bricks:
`mFourierCoeff_eq_integral` (the coefficient as an integral over the half-open cube `∏ᵢ(0,1]`), the
`Ioc`↔`Ico` cube reconciliation (the two cubes differ only on a finite union of measure-zero coordinate
hyperplanes — `ae_eq_set_pi` lifts the 1-D `Ico_ae_eq_Ioc` to the product, and `setIntegral_congr_set`
swaps the domain to the `ZSpan` fundamental domain `∏ᵢ[0,1)`), the character/torus-monomial bridge
`mFourier_q_eq_char`, the descent's defining property `torusDescent_comp`, and the Tonelli crux
`cube_integral_char_periodisation`. Together with `hasSum_mFourierCoeff_at_zero` (Fourier inversion at the
origin) and `torusDescent_at_zero` (the Poisson LHS) this closes the multivariate Poisson summation formula
`∑_{γ∈ℤᵈ} F(↑γ) = ∑_{n∈ℤᵈ} latFourier F n` (see `multivar_poisson` below). -/
theorem mFourierCoeff_torusDescent {d : ℕ} (F : C(Fin d → ℝ, ℂ))
    (hc : Continuous (periodisationCM F ∘ torusRep))
    (hF : ∀ K : TopologicalSpace.Compacts (Fin d → ℝ),
      Summable fun γ : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d)))) =>
        ‖(F.comp (ContinuousMap.addRight (γ : Fin d → ℝ))).restrict K‖)
    (n : Fin d → ℤ)
    (hFint : Integrable
      (fun x => Complex.exp (2 * π * Complex.I * (∑ i, (-(n i) : ℝ) * x i)) * (F : (Fin d → ℝ) → ℂ) x))
    (hmeas : ∀ γ : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d)))),
      AEStronglyMeasurable
        (fun x => Complex.exp (2 * π * Complex.I * (∑ i, (-(n i) : ℝ) * x i))
          * (F : (Fin d → ℝ) → ℂ) (x + (γ : Fin d → ℝ)))
        (volume.restrict (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d)))))
    (hLsum : ∑' γ : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d)))),
        ∫⁻ x in ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d)),
          ‖Complex.exp (2 * π * Complex.I * (∑ i, (-(n i) : ℝ) * x i))
            * (F : (Fin d → ℝ) → ℂ) (x + (γ : Fin d → ℝ))‖ₑ ≠ ⊤) :
    mFourierCoeff (torusDescent F hc) n = latFourier (F : (Fin d → ℝ) → ℂ) n := by
  rw [mFourierCoeff_eq_integral (torusDescent F hc) n 0]
  simp only [Pi.zero_apply, zero_add]
  have hset : {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}
      =ᵐ[volume] ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d)) := by
    rw [ZSpan.fundamentalDomain_pi_basisFun]
    have hL : {x : Fin d → ℝ | ∀ i, x i ∈ Set.Ioc (0 : ℝ) 1}
        = Set.pi Set.univ (fun _ : Fin d => Set.Ioc (0 : ℝ) 1) := by
      ext x; simp only [Set.mem_setOf_eq, Set.mem_univ_pi]
    rw [hL, volume_pi]
    exact Measure.ae_eq_set_pi (fun i _ => Ico_ae_eq_Ioc.symm)
  rw [setIntegral_congr_set hset,
    ← cube_integral_char_periodisation (F : (Fin d → ℝ) → ℂ) n hFint hmeas hLsum]
  refine setIntegral_congr_fun (ZSpan.fundamentalDomain_measurableSet _) fun x _ => ?_
  show mFourier (-n) (Pi.map (fun (_ : Fin d) => ((↑) : ℝ → AddCircle (1 : ℝ))) x)
      • torusDescent F hc (Pi.map (fun (_ : Fin d) => ((↑) : ℝ → AddCircle (1 : ℝ))) x) = _
  rw [mFourier_q_eq_char, torusDescent_comp F hc hF, periodisationCM_apply F hF, smul_eq_mul,
    periodisation]

/-- **The multivariate Poisson summation formula.** For `F : C(Fin d → ℝ, ℂ)` whose periodisation descends
to the torus (`hc`, `hF`), whose torus Fourier coefficients are summable (`hsum`), and which satisfies the
per-frequency analytic side conditions (`hFint` integrability, `hmeas` measurability of each lattice
translate, `hLsum` `L¹`-summability over the lattice — all discharged from Schwartz/Gaussian decay at
application time):

> `∑_{γ∈ℤᵈ} F(↑γ) = ∑_{n∈ℤᵈ} latFourier F n`

where `latFourier F n = ∫_{ℝᵈ} exp(2πi·∑ᵢ(-nᵢ)xᵢ)·F(x)` is the `ℝᵈ` Fourier integral (the `2π`-convention
Fourier transform at the integer frequency `n`). Proof: Fourier inversion of the torus descent `F♯` at the
origin (`hasSum_mFourierCoeff_at_zero`) reads the right side as `F♯ 0`, which is the lattice sum
(`torusDescent_at_zero`); each Fourier coefficient is the lattice Fourier integral
(`mFourierCoeff_torusDescent`). This is `[Θ1]` of the spectra-free van der Blij route: applied to the
Gaussian `F(x) = exp(iπτ·xᵀAx)` it yields the theta S-transformation, whence the modular-weight argument
forces `8 ∣ rank` for definite even unimodular lattices. -/
theorem multivar_poisson {d : ℕ} (F : C(Fin d → ℝ, ℂ))
    (hc : Continuous (periodisationCM F ∘ torusRep))
    (hF : ∀ K : TopologicalSpace.Compacts (Fin d → ℝ),
      Summable fun γ : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d)))) =>
        ‖(F.comp (ContinuousMap.addRight (γ : Fin d → ℝ))).restrict K‖)
    (hsum : Summable (mFourierCoeff (torusDescent F hc)))
    (hFint : ∀ n : Fin d → ℤ, Integrable
      (fun x => Complex.exp (2 * π * Complex.I * (∑ i, (-(n i) : ℝ) * x i)) * (F : (Fin d → ℝ) → ℂ) x))
    (hmeas : ∀ n : Fin d → ℤ, ∀ γ : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d)))),
      AEStronglyMeasurable
        (fun x => Complex.exp (2 * π * Complex.I * (∑ i, (-(n i) : ℝ) * x i))
          * (F : (Fin d → ℝ) → ℂ) (x + (γ : Fin d → ℝ)))
        (volume.restrict (ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d)))))
    (hLsum : ∀ n : Fin d → ℤ,
        ∑' γ : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d)))),
          ∫⁻ x in ZSpan.fundamentalDomain (Pi.basisFun ℝ (Fin d)),
            ‖Complex.exp (2 * π * Complex.I * (∑ i, (-(n i) : ℝ) * x i))
              * (F : (Fin d → ℝ) → ℂ) (x + (γ : Fin d → ℝ))‖ₑ ≠ ⊤) :
    ∑' γ : ↥(Submodule.span ℤ (Set.range ⇑(Pi.basisFun ℝ (Fin d)))),
        (F : (Fin d → ℝ) → ℂ) (γ : Fin d → ℝ)
      = ∑' n : Fin d → ℤ, latFourier (F : (Fin d → ℝ) → ℂ) n := by
  have hHS := hasSum_mFourierCoeff_at_zero (f := torusDescent F hc) hsum
  rw [torusDescent_at_zero F hc hF] at hHS
  rw [← hHS.tsum_eq]
  exact tsum_congr fun n =>
    mFourierCoeff_torusDescent F hc hF n (hFint n) (hmeas n) (hLsum n)

end SKEFTHawking
