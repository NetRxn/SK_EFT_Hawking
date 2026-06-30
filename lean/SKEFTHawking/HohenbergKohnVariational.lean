import Mathlib.Order.ConditionallyCompleteLattice.Indexed
import Mathlib.Data.Real.Archimedean

/-!
# Hohenberg–Kohn II: the density variational principle (Phase 6BB, Wave 3)

The second Hohenberg–Kohn theorem makes density-functional theory **computable**: for a fixed external
potential `v`, the energy functional `E_v[n] = F[n] + ∫ v·n` is bounded below by the true ground-state
energy `E₀`, with equality **iff** `n` is the true ground-state density `n₀`:

  `E_v[n] ≥ E₀`,    `E_v[n] = E₀ ↔ n = n₀`.

This is the Rayleigh–Ritz variational principle, transcribed to the density. By the Wave-1
self-adjointness (real spectrum, bounded below) the ground-state energy is the infimum of the energy
expectation over admissible states — equivalently, by the HK-I (Wave 2) density↦potential bijection,
the infimum of `E_v[·]` over admissible densities:

  `E₀ = ⨅ₙ E_v[n]`.

The lower bound `E_v[n] ≥ E₀` is then exactly that an infimum is a lower bound (`ciInf_le`,
conditionally-complete-order theory over `ℝ`). The equality characterisation uses non-degeneracy: the
infimum is attained only at the true ground-state density.

The `BddBelow` field (the energy functional is semibounded) is a **disclosed structural hypothesis** —
expected to follow from the Wave-1 self-adjoint, semibounded Hamiltonian in a future bridging wave, but
not yet formally connected to `molecularHamiltonian_essSelfAdjoint` here (this module does not import
Wave 1). Same disclosure discipline as the Wave-1 tracked-Props.

Invariants (Phase 6BB): kernel-pure `{propext, Classical.choice, Quot.sound}`; zero `sorry`; no new
project-local axiom; no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.DFT

variable {X : Type*}

/-- The density-variational data for a fixed external potential: the energy functional `E_v[·]` over
admissible densities (`Ev`), the true ground-state density `n₀`, and the facts that `E_v[·]` is bounded
below, attains its infimum at `n₀`, and (by non-degeneracy) **only** at `n₀`. The ground-state energy
is `E₀ = ⨅ E_v[n]`. -/
structure DensityVariational (X : Type*) where
  /-- The energy functional `E_v[n]` over admissible densities. -/
  Ev : (X → ℝ) → ℝ
  /-- The true ground-state density. -/
  n₀ : X → ℝ
  /-- `E_v[·]` is bounded below (disclosed hypothesis; expected from Wave-1 semiboundedness). -/
  bddBelow : BddBelow (Set.range Ev)
  /-- The ground state attains the infimum: `E_v[n₀] = E₀`. -/
  ground : Ev n₀ = ⨅ n, Ev n
  /-- Non-degeneracy: the infimum is attained only at the true ground-state density. -/
  nondegen : ∀ n, Ev n = ⨅ m, Ev m → n = n₀

/-- The ground-state energy `E₀ = ⨅ₙ E_v[n]`. -/
noncomputable def DensityVariational.E₀ (D : DensityVariational X) : ℝ := ⨅ n, D.Ev n

/-- **Hohenberg–Kohn II (variational principle).** For any admissible density `n`, the energy
functional is bounded below by the ground-state energy, `E_v[n] ≥ E₀`, with equality **iff** `n` is the
true ground-state density. The lower bound is the Rayleigh-extremal fact that an infimum is a lower
bound; the equality characterisation is the (load-bearing) non-degeneracy of the ground state. -/
theorem hohenberg_kohn_variational (D : DensityVariational X) (n : X → ℝ) :
    D.E₀ ≤ D.Ev n ∧ (D.Ev n = D.E₀ ↔ n = D.n₀) := by
  refine ⟨ciInf_le D.bddBelow n, D.nondegen n, ?_⟩
  rintro rfl
  exact D.ground

end SKEFTHawking.DFT
