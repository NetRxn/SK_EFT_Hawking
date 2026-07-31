import Mathlib
import SKEFTHawking.TopologicalBand.PrincipalBranch
import SKEFTHawking.TopologicalBand.FiniteTorus

/-!
# D11-FHS Q1–Q2 — Fukui–Hatsugai–Suzuki lattice Chern number (exact integrality + gauge)

The exact, gauge-invariant FHS **lattice** Chern invariant for arbitrary `Circle`-valued link
fields on the finite torus `ZMod N₁ × ZMod N₂`, built on the `PrincipalBranch` spike spine.

## Scope (honest — this file is purely finite/data-level)

Everything here is a **finite** algebraic identity over a periodic grid. No Hamiltonian,
eigenvector, band gap, continuum limit, or Berry curvature is used. In particular the `latticeChern`
integer is **not** claimed equal to any continuum first Chern class (that comparison is a separate
deferred analytic program). The two headline results are:

* `sum_plaquetteArg_eq_two_pi_mul_latticeChern` — exact integrality:
  `∑ₖ plaquetteArg = 2π · latticeChern`, with `latticeChern : ℤ` unconditional.
* `latticeChern_gaugeInvariant` — invariance under vertex `Circle` gauge transformations.

## Frozen conventions (Q0)

* **Plaquette orientation** (counterclockwise): `U₀(k)·U₁(k+ê₀)·U₀(k+ê₁)⁻¹·U₁(k)⁻¹`.
* **Branch index** `branchIndex = +toIocDiv two_pi_pos (-π)` (the definitional `PrincipalBranch`
  choice, so `principal θ + 2π·branchIndex θ = θ`).
* **Lattice Chern** `latticeChern = −∑ₖ plaquetteBranch`, the sign fixed so the headline reads
  `∑ plaquetteArg = 2π · latticeChern` (matching the FHS `c̃ = (1/2π)∑ F̃₁₂`).
-/

open Complex Real
open scoped BigOperators

-- This file interleaves pointwise lemmas (no `NeZero` needed) with grid-sum lemmas (which need
-- `Fintype`, hence `NeZero`); disable the section-variable linter rather than split the block.
set_option linter.unusedSectionVars false

namespace SKEFTHawking.TopologicalBand

variable (N₁ N₂ : ℕ) [NeZero N₁] [NeZero N₂]

/-- A `U(1)`/`Circle`-valued link field: an oriented phase on each of the two links leaving a
vertex of the finite grid. -/
abbrev LinkField : Type := Fin 2 → Torus N₁ N₂ → Circle

/-- The oriented plaquette product around the elementary square at `k` (frozen counterclockwise
orientation `U₀(k)·U₁(k+ê₀)·U₀(k+ê₁)⁻¹·U₁(k)⁻¹`). -/
noncomputable def plaquette (U : LinkField N₁ N₂) (k : Torus N₁ N₂) : Circle :=
  U 0 k * U 1 (shift N₁ N₂ 0 k) * (U 0 (shift N₁ N₂ 1 k))⁻¹ * (U 1 k)⁻¹

/-- The principal argument of a single link phase. -/
noncomputable def linkArg (U : LinkField N₁ N₂) (μ : Fin 2) (k : Torus N₁ N₂) : ℝ :=
  Complex.arg (U μ k : ℂ)

/-- The **raw lattice curl** `A₀(k) + A₁(k+ê₀) − A₀(k+ê₁) − A₁(k)`: the (unreduced) sum of the four
oriented link arguments around the plaquette. -/
noncomputable def rawCurl (U : LinkField N₁ N₂) (k : Torus N₁ N₂) : ℝ :=
  linkArg N₁ N₂ U 0 k + linkArg N₁ N₂ U 1 (shift N₁ N₂ 0 k)
    - linkArg N₁ N₂ U 0 (shift N₁ N₂ 1 k) - linkArg N₁ N₂ U 1 k

/-- The **FHS lattice field strength**: the principal argument of the plaquette product, i.e. the
raw curl reduced into `(-π, π]`. -/
noncomputable def plaquetteArg (U : LinkField N₁ N₂) (k : Torus N₁ N₂) : ℝ :=
  Complex.arg (plaquette N₁ N₂ U k : ℂ)

/-- The integer branch correction of a plaquette, `branchIndex (rawCurl)` — how many full turns the
raw curl is above the principal branch. Each is one of `{-2,-1,0,1,2}`. -/
noncomputable def plaquetteBranch (U : LinkField N₁ N₂) (k : Torus N₁ N₂) : ℤ :=
  branchIndex (rawCurl N₁ N₂ U k)

/-- The **FHS lattice Chern number**: the (signed) sum of plaquette branch corrections. An exact
integer topological invariant of the link field. -/
noncomputable def latticeChern (U : LinkField N₁ N₂) : ℤ :=
  - ∑ k, plaquetteBranch N₁ N₂ U k

/-- **Field-strength ↔ raw-curl principal reduction on the torus.** The FHS lattice field strength
is the principal reduction of the raw lattice curl. This is the direct consumer of the spike
headline `arg_plaquette_eq_principal_rawCurl`, with the `Circle` links supplying nonvanishing. -/
theorem plaquetteArg_eq_principal_rawCurl (U : LinkField N₁ N₂) (k : Torus N₁ N₂) :
    plaquetteArg N₁ N₂ U k = principal (rawCurl N₁ N₂ U k) := by
  unfold plaquetteArg plaquette rawCurl linkArg
  simp only [Circle.coe_mul, Circle.coe_inv]
  exact arg_plaquette_eq_principal_rawCurl _ _ _ _
    (Circle.coe_ne_zero _) (Circle.coe_ne_zero _) (Circle.coe_ne_zero _) (Circle.coe_ne_zero _)

/-- **Torus telescoping.** The raw curl sums to zero over the whole grid: it is a difference of two
forward differences, each of which telescopes to zero by shift invariance.

Rewritten 2026-07-31 (D11 Stage-13 round-7 finding 5.9) to go through
`sum_forwardDiff_eq_zero` rather than applying `sum_shift` twice directly. The paper describes
that lemma as the torus's single load-bearing property, and it had zero consumers — the description
was true of `sum_shift`, one link further down. Exhibiting the curl as a difference of two forward
differences and discharging each by the named lemma makes the paper's account of the dependency the
one the kernel checks. -/
theorem sum_rawCurl_eq_zero (U : LinkField N₁ N₂) :
    ∑ k, rawCurl N₁ N₂ U k = 0 := by
  have hpt : ∀ k, rawCurl N₁ N₂ U k
      = (linkArg N₁ N₂ U 1 (shift N₁ N₂ 0 k) - linkArg N₁ N₂ U 1 k)
        - (linkArg N₁ N₂ U 0 (shift N₁ N₂ 1 k) - linkArg N₁ N₂ U 0 k) := by
    intro k; unfold rawCurl; ring
  simp only [hpt]
  rw [Finset.sum_sub_distrib,
    sum_forwardDiff_eq_zero N₁ N₂ 0 (linkArg N₁ N₂ U 1),
    sum_forwardDiff_eq_zero N₁ N₂ 1 (linkArg N₁ N₂ U 0), sub_zero]

/-- **THE INTEGRALITY THEOREM.** The exact FHS identity: the sum of the lattice field strengths over
the torus equals `2π` times an integer, the lattice Chern number. Unconditional; finite/data-level;
no spectral or continuum hypothesis. -/
theorem sum_plaquetteArg_eq_two_pi_mul_latticeChern (U : LinkField N₁ N₂) :
    ∑ k, plaquetteArg N₁ N₂ U k = 2 * Real.pi * (latticeChern N₁ N₂ U : ℝ) := by
  have hpt : ∀ k, plaquetteArg N₁ N₂ U k
      = rawCurl N₁ N₂ U k - 2 * Real.pi * (plaquetteBranch N₁ N₂ U k : ℝ) := by
    intro k
    have hb := principal_add_branch (rawCurl N₁ N₂ U k)
    rw [plaquetteArg_eq_principal_rawCurl]
    simp only [plaquetteBranch]
    linarith
  calc ∑ k, plaquetteArg N₁ N₂ U k
      = ∑ k, (rawCurl N₁ N₂ U k - 2 * Real.pi * (plaquetteBranch N₁ N₂ U k : ℝ)) :=
        Finset.sum_congr rfl (fun k _ => hpt k)
    _ = (∑ k, rawCurl N₁ N₂ U k) - 2 * Real.pi * ∑ k, (plaquetteBranch N₁ N₂ U k : ℝ) := by
        rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
    _ = 2 * Real.pi * (latticeChern N₁ N₂ U : ℝ) := by
        rw [sum_rawCurl_eq_zero]
        simp only [latticeChern]
        push_cast
        ring

/-! ### Vertex gauge transformations -/

/-- A vertex `Circle` gauge transformation of the link field:
`Uμ(k) ↦ g(k)⁻¹ · Uμ(k) · g(k + êμ)`. -/
noncomputable def gaugeTransform (g : Torus N₁ N₂ → Circle) (U : LinkField N₁ N₂) :
    LinkField N₁ N₂ :=
  fun μ k => (g k)⁻¹ * U μ k * g (shift N₁ N₂ μ k)

/-- **Plaquette gauge invariance.** The plaquette product is unchanged by a vertex gauge
transformation: the `g` factors cancel telescopically around the loop (using commutativity of
`Circle` and the commutation of the two shifts). -/
theorem plaquette_gaugeTransform (g : Torus N₁ N₂ → Circle) (U : LinkField N₁ N₂)
    (k : Torus N₁ N₂) :
    plaquette N₁ N₂ (gaugeTransform N₁ N₂ g U) k = plaquette N₁ N₂ U k := by
  have hcomm : shift N₁ N₂ 1 (shift N₁ N₂ 0 k) = shift N₁ N₂ 0 (shift N₁ N₂ 1 k) :=
    shift_comm N₁ N₂ 1 0 k
  refine Circle.coe_injective ?_
  have hg : ∀ x, (g x : ℂ) ≠ 0 := fun x => Circle.coe_ne_zero (g x)
  have hgk := hg k
  have hg0 := hg (shift N₁ N₂ 0 k)
  have hg1 := hg (shift N₁ N₂ 1 k)
  have hg01 := hg (shift N₁ N₂ 0 (shift N₁ N₂ 1 k))
  have hU0 : (U 0 (shift N₁ N₂ 1 k) : ℂ) ≠ 0 := Circle.coe_ne_zero _
  have hU1 : (U 1 k : ℂ) ≠ 0 := Circle.coe_ne_zero _
  unfold plaquette gaugeTransform
  rw [hcomm]
  simp only [Circle.coe_mul, Circle.coe_inv]
  field_simp

/-- **Lattice-Chern gauge invariance.** The FHS lattice Chern number is invariant under vertex gauge
transformations — a consequence of pointwise plaquette invariance and the integrality identity. -/
theorem latticeChern_gaugeInvariant (g : Torus N₁ N₂ → Circle) (U : LinkField N₁ N₂) :
    latticeChern N₁ N₂ (gaugeTransform N₁ N₂ g U) = latticeChern N₁ N₂ U := by
  have hsum : ∑ k, plaquetteArg N₁ N₂ (gaugeTransform N₁ N₂ g U) k
      = ∑ k, plaquetteArg N₁ N₂ U k := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    unfold plaquetteArg
    rw [plaquette_gaugeTransform]
  have h1 := sum_plaquetteArg_eq_two_pi_mul_latticeChern N₁ N₂ (gaugeTransform N₁ N₂ g U)
  have h2 := sum_plaquetteArg_eq_two_pi_mul_latticeChern N₁ N₂ U
  rw [hsum, h2] at h1
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have hcast : (latticeChern N₁ N₂ U : ℝ) = (latticeChern N₁ N₂ (gaugeTransform N₁ N₂ g U) : ℝ) :=
    mul_left_cancel₀ hpi h1
  exact_mod_cast hcast.symm

end SKEFTHawking.TopologicalBand
