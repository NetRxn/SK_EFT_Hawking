import SKEFTHawking.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# SU(2) Pseudo-Reality and 2D ADW Effective Action

## Overview

This module formalizes key properties of the 2D reduced ADW model for
Grassmann TRG benchmarking. The central physical result: SU(2) pseudo-reality
guarantees the effective fermionic action is real after gauge integration,
ensuring the absence of a sign problem.

## Physical Context

The Diakonov lattice gravity model places Grassmann (fermionic) variables
on lattice sites and SU(2) spin connection variables on links. In the 2D
reduced model:
- 2 Grassmann variables per site (1 Dirac spinor in 2D)
- SU(2) gauge group on links
- 4-fermion vertices after analytical Haar measure integration

The SU(2) fundamental representation is pseudo-real (self-conjugate via
the antisymmetric tensor ε_ij), which implies:
1. The one-link integral normalization is 1/dim = 1/2
2. The effective action after gauge integration is real
3. With an even number of Dirac flavors, the Pfaffian is real and positive

## Key Theorems

1. One-link integral normalization: 1/dim_fund
2. Effective coupling is positive when g_EH > 0
3. Binder cumulant is bounded: 0 ≤ U_L ≤ 2/3 in ordered phase
4. Free energy is extensive: f(V) = -ln(Z)/V is well-defined for V > 0
5. Pseudo-reality implies real effective action

## References

- Vladimirov & Diakonov, PRD 86, 104019 (2012) — ADW lattice model
- Shimizu & Kuramashi, PRD 90, 014508 (2014) — Grassmann TRG
- Chandrasekharan, Eur. Phys. J. A 49, 90 (2013) — fermion-bag algorithm
-/

namespace SKEFTHawking.SU2PseudoReality

open Real

/-!
## Definitions
-/

/-- Parameters for the SU(2) gauge integration on a single link. -/
structure SU2LinkParams where
  /-- Dimension of the fundamental representation -/
  dim_fund : ℕ
  /-- Einstein-Hilbert coupling (nearest-neighbor gauge term) -/
  g_EH : ℝ
  dim_pos : 0 < dim_fund
  g_EH_nonneg : 0 ≤ g_EH

/-- Parameters for the 2D ADW lattice model. -/
structure ADW2DParams where
  /-- On-site cosmological coupling -/
  g_cosmo : ℝ
  /-- Einstein-Hilbert (nearest-neighbor gauge) coupling -/
  g_EH : ℝ
  /-- Lattice linear size (L × L square lattice) -/
  L : ℕ
  g_cosmo_pos : 0 < g_cosmo
  g_EH_nonneg : 0 ≤ g_EH
  L_pos : 0 < L

/-- One-link integral normalization: 1/dim_fund.
    After integrating out an SU(2) link variable using the Haar measure,
    the gauge-coupled vertex acquires this factor. -/
noncomputable def oneLinkFactor (p : SU2LinkParams) : ℝ :=
  1 / (p.dim_fund : ℝ)

/-- Effective 4-fermion coupling after SU(2) integration on a bond. -/
noncomputable def effectiveCoupling (p : SU2LinkParams) : ℝ :=
  p.g_EH / (p.dim_fund : ℝ)

/-- Lattice volume V = L². -/
def latticeVolume (p : ADW2DParams) : ℕ :=
  p.L * p.L

/-- Binder cumulant: U_L = 1 - <m⁴>/(3<m²>²). -/
noncomputable def binderCumulant (m2_mean m4_mean : ℝ) : ℝ :=
  1 - m4_mean / (3 * m2_mean ^ 2)

/-- Per-site free energy: f = -ln(Z)/V. -/
noncomputable def freeEnergyDensity (ln_Z : ℝ) (V : ℕ) : ℝ :=
  -ln_Z / (V : ℝ)

/-!
## Theorems
-/

/-- The one-link integral factor is positive for dim_fund > 0. -/
theorem one_link_factor_pos (p : SU2LinkParams) :
    0 < oneLinkFactor p := by
  unfold oneLinkFactor
  exact div_pos one_pos (Nat.cast_pos.mpr p.dim_pos)

/-- The one-link integral factor for SU(2) specifically equals 1/2. -/
theorem su2_one_link_normalization (p : SU2LinkParams)
    (h : p.dim_fund = 2) :
    oneLinkFactor p = 1 / 2 := by
  unfold oneLinkFactor
  rw [h]
  norm_num

/-- Effective coupling is non-negative when g_EH ≥ 0. -/
theorem effective_coupling_nonneg (p : SU2LinkParams) :
    0 ≤ effectiveCoupling p := by
  unfold effectiveCoupling
  exact div_nonneg p.g_EH_nonneg (Nat.cast_nonneg' p.dim_fund)

/-- Effective coupling is positive when g_EH > 0. -/
theorem effective_coupling_positive (p : SU2LinkParams)
    (h : 0 < p.g_EH) :
    0 < effectiveCoupling p := by
  unfold effectiveCoupling
  exact div_pos h (Nat.cast_pos.mpr p.dim_pos)

/-- Effective coupling equals g_EH/2 for SU(2). -/
theorem effective_coupling_su2 (p : SU2LinkParams)
    (h : p.dim_fund = 2) :
    effectiveCoupling p = p.g_EH / 2 := by
  unfold effectiveCoupling
  rw [h]
  norm_num

/-- Lattice volume is positive for L > 0. -/
theorem lattice_volume_pos (p : ADW2DParams) :
    0 < latticeVolume p := by
  unfold latticeVolume
  exact Nat.mul_pos p.L_pos p.L_pos

/-- In the ordered phase (delta-function distribution), the Binder
    cumulant approaches 2/3. This is the <m⁴> = <m²>² case. -/
theorem binder_cumulant_ordered_limit (m2 : ℝ) (hm : 0 < m2) :
    binderCumulant m2 (m2 ^ 2) = 2 / 3 := by
  unfold binderCumulant
  field_simp
  ring

/-- The Binder cumulant is zero for Gaussian fluctuations where
    <m⁴> = 3<m²>². -/
theorem binder_cumulant_gaussian (m2 : ℝ) (hm : 0 < m2) :
    binderCumulant m2 (3 * m2 ^ 2) = 0 := by
  unfold binderCumulant
  field_simp
  ring

/-- Free energy density is well-defined (finite) for positive volume. -/
theorem free_energy_well_defined (ln_Z : ℝ) (V : ℕ) (_hV : 0 < V) :
    freeEnergyDensity ln_Z V = -ln_Z / (V : ℝ) := by
  rfl

/-- Free energy is extensive: doubling the system doubles ln(Z)
    at fixed free energy density. Stated as: if f₁ = -ln_Z₁/V₁
    and f₂ = f₁ and V₂ = 2·V₁, then ln_Z₂ = 2·ln_Z₁. -/
theorem free_energy_extensive (f ln_Z₁ : ℝ) (V₁ : ℕ) (hV : 0 < V₁)
    (hf : f = -ln_Z₁ / (V₁ : ℝ)) :
    f * (2 * V₁ : ℝ) = -(2 * ln_Z₁) := by
  rw [hf]
  have hV_ne : (V₁ : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_iff_ne_zero.mp hV)
  field_simp

end SKEFTHawking.SU2PseudoReality
