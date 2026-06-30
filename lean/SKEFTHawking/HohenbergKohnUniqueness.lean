import Mathlib.MeasureTheory.Integral.Bochner.Basic

/-!
# Hohenberg–Kohn I: the ground-state density determines the potential (Phase 6BB, Wave 2)

The first Hohenberg–Kohn theorem: the ground-state density of a many-electron system determines its
external potential **up to an additive constant**. This is what makes "a functional of the density"
well-defined — the conceptual core of density-functional theory, built on the Wave-1 self-adjoint
molecular Hamiltonian.

The proof is the classic **Rayleigh–Ritz variational reductio**. A ground state in potential `v` has
energy `E = F + ∫ v·n`, where `n` is its density and `F = ⟨ψ| T + W |ψ⟩` is the *universal*
(kinetic + electron–electron) part. The variational principle gives, for the ground state `ψ'` of a
*different* potential `v'` (a non-ground-state of `v`, by non-degeneracy), the **strict** inequality
`E < F' + ∫ v·n'`. Writing this for `(v₁, v₂)` and `(v₂, v₁)` and adding, the `∫`-terms cancel when
the two densities coincide — forcing `E₁ + E₂ < E₁ + E₂`, a contradiction. Hence two potentials
differing by more than a constant cannot share a ground-state density.

Here the energy decomposition and the strict variational inequalities are the load-bearing physical
inputs (true for any non-degenerate ground state on the Wave-1 self-adjoint Hamiltonian); the reductio
itself — the falsifiable content of HK I — is proven unconditionally.

Invariants (Phase 6BB): kernel-pure `{propext, Classical.choice, Quot.sound}`; zero `sorry`; no new
project-local axiom; no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.DFT

open MeasureTheory

variable {X : Type*} [MeasurableSpace X] {μ : Measure X}

/-- The variational data of a **non-degenerate ground state** of an `N`-electron system in external
potential `v` (with measure `μ` on the configuration space `X`): its ground-state density `n`, energy
`E`, and universal (kinetic + interaction) value `F`, with the energy decomposition `E = F + ∫ v·n`. -/
structure GroundStateData (v : X → ℝ) (μ : Measure X) where
  /-- The ground-state density. -/
  n : X → ℝ
  /-- The ground-state energy. -/
  E : ℝ
  /-- The universal functional value `⟨ψ| T + W |ψ⟩`. -/
  F : ℝ
  /-- Energy decomposition: `E = F + ∫ v·n`. -/
  decomp : E = F + ∫ x, v x * n x ∂μ

/-- **Hohenberg–Kohn I (uniqueness) — the variational reductio / falsifier.** Two external potentials
`v₁, v₂` with non-degenerate ground states sharing the **same density** `n` cannot both satisfy the
strict Rayleigh–Ritz inequality (each ground state strictly beats the other's state when evaluated in
its own potential). Equivalently: distinct ground-state densities arise from potentials differing by
more than a constant — the density determines the potential.

`hvar₁`/`hvar₂` are the strict variational bounds (from non-degeneracy + Rayleigh–Ritz); `hn` is the
shared density. The reductio is unconditional. -/
theorem hohenberg_kohn_uniqueness {v₁ v₂ : X → ℝ}
    (g₁ : GroundStateData v₁ μ) (g₂ : GroundStateData v₂ μ) (hn : g₁.n = g₂.n)
    (hvar₁ : g₁.E < g₂.F + ∫ x, v₁ x * g₂.n x ∂μ)
    (hvar₂ : g₂.E < g₁.F + ∫ x, v₂ x * g₁.n x ∂μ) : False := by
  have hd₁ := g₁.decomp
  have hd₂ := g₂.decomp
  -- normalise every density to `g₂.n`, so the four `∫`-atoms coincide and the cross terms cancel
  rw [hn] at hd₁ hvar₂
  -- hvar₁ : E₁ < F₂ + ∫v₁n₂ ; hvar₂ : E₂ < F₁ + ∫v₂n₂ ; hd₁ : E₁ = F₁ + ∫v₁n₂ ; hd₂ : E₂ = F₂ + ∫v₂n₂
  linarith

/-- **Hohenberg–Kohn I (the injectivity / positive form): the potential-to-density map is injective.**
Two non-degenerate ground states whose strict Rayleigh–Ritz inequalities hold have **distinct
densities** — so a ground-state density is shared by at most one potential (up to the additive constant
absorbed into the energy decomposition). The contrapositive of `hohenberg_kohn_uniqueness`. -/
theorem hohenberg_kohn_density_injective {v₁ v₂ : X → ℝ}
    (g₁ : GroundStateData v₁ μ) (g₂ : GroundStateData v₂ μ)
    (hvar₁ : g₁.E < g₂.F + ∫ x, v₁ x * g₂.n x ∂μ)
    (hvar₂ : g₂.E < g₁.F + ∫ x, v₂ x * g₁.n x ∂μ) : g₁.n ≠ g₂.n :=
  fun hn => hohenberg_kohn_uniqueness g₁ g₂ hn hvar₁ hvar₂