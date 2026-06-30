import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Data.Real.Archimedean

/-!
# Levy–Lieb constrained-search functional (Phase 6BB, Wave 4)

The Levy–Lieb functional turns the Hohenberg–Kohn universal functional into a **constructive** object,
defined on *every* `N`-representable density (not just the v-representable ones):

  `F_LL[n] = inf_{ψ ↦ n} ⟨ψ| T + V_ee |ψ⟩`,

the infimum of the kinetic-plus-interaction energy over all antisymmetric states `ψ` whose density is
`n` (the *constrained search* over the density fiber). Two facts pin it down:

* **Lower bound (the functional).** Every state with density `n` has energy `≥ F_LL[n]` — it is the
  infimum of the fiber (`ciInf_le`).
* **Agreement with Hohenberg–Kohn on v-representable densities.** When `n` is the ground-state density
  of some external potential, its ground state `ψ₀` both lies in the fiber and minimises `T + V_ee`
  within it, so `F_LL[n] = ⟨ψ₀| T + V_ee |ψ₀⟩ = F_HK[n]` (`le_antisymm`: the fiber-infimum equals the
  value at the minimiser).

The fiber-semiboundedness (so the constrained infimum exists) is a **disclosed structural hypothesis**
— expected to follow from the Wave-1 self-adjoint, semibounded `T + V_ee` and the Wave-2/3
Hohenberg–Kohn density↔potential correspondence in a future bridging wave, but not formally connected
to those modules here (this file does not import them). Same disclosure discipline as Wave 1.

Invariants (Phase 6BB): kernel-pure `{propext, Classical.choice, Quot.sound}`; zero `sorry`; no new
project-local axiom; no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.DFT

variable {Ψ X : Type*}

/-- Data for the Levy–Lieb constrained search: the kinetic-plus-interaction energy `T + V_ee` of a
state (`TW`), the density of a state (`density`), and the fact that each density fiber is bounded below
in energy (from the Wave-1 semibounded Hamiltonian) — so the constrained infimum exists. -/
structure LevyLiebData (Ψ X : Type*) where
  /-- The kinetic-plus-interaction energy `⟨ψ| T + V_ee |ψ⟩`. -/
  TW : Ψ → ℝ
  /-- The single-particle density of a state. -/
  density : Ψ → (X → ℝ)
  /-- Each density fiber is bounded below in energy (disclosed hypothesis; expected from Wave-1
  semiboundedness). -/
  fiber_bddBelow : ∀ n : X → ℝ, BddBelow (Set.range fun ψ : {ψ // density ψ = n} => TW ψ.1)

/-- The **Levy–Lieb functional** `F_LL[n] = inf_{ψ ↦ n} ⟨ψ| T + V_ee |ψ⟩`. -/
noncomputable def LevyLiebData.F_LL (D : LevyLiebData Ψ X) (n : X → ℝ) : ℝ :=
  ⨅ ψ : {ψ // D.density ψ = n}, D.TW ψ.1

/-- **The Levy–Lieb functional is a lower bound** for the kinetic-plus-interaction energy of every
state with the given density: `⟨ψ| T + V_ee |ψ⟩ ≥ F_LL[n]`. (`F_LL[n]` is the infimum of the fiber.) -/
theorem levyLieb_functional (D : LevyLiebData Ψ X) (n : X → ℝ) (ψ : Ψ) (hψ : D.density ψ = n) :
    D.F_LL n ≤ D.TW ψ :=
  ciInf_le (D.fiber_bddBelow n) ⟨ψ, hψ⟩

/-- **Levy–Lieb agrees with Hohenberg–Kohn on v-representable densities.** If `n` is the ground-state
density of some potential, witnessed by a state `ψ₀ ↦ n` that minimises `T + V_ee` within the fiber
(so `⟨ψ₀| T + V_ee |ψ₀⟩ = F_HK[n]`), then `F_LL[n] = ⟨ψ₀| T + V_ee |ψ₀⟩` — the constrained-search
functional equals the Hohenberg–Kohn universal functional there. -/
theorem levyLieb_eq_HK_on_vrep (D : LevyLiebData Ψ X) (n : X → ℝ) (ψ₀ : Ψ) (hψ₀ : D.density ψ₀ = n)
    (hmin : ∀ ψ : {ψ // D.density ψ = n}, D.TW ψ₀ ≤ D.TW ψ.1) : D.F_LL n = D.TW ψ₀ := by
  haveI : Nonempty {ψ // D.density ψ = n} := ⟨⟨ψ₀, hψ₀⟩⟩
  exact le_antisymm (ciInf_le (D.fiber_bddBelow n) ⟨ψ₀, hψ₀⟩) (le_ciInf hmin)

end SKEFTHawking.DFT
