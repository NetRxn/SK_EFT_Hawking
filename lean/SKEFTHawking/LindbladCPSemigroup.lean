import SKEFTHawking.LindbladSemigroup
import Mathlib.Topology.Instances.Matrix

/-!
# GKSL CP-semigroup theorem (Phase 6BC Wave 5 / D10 Discharge W4) — discharge of `hreal`

`LindbladSemigroup.lean` proved trace-distance contractivity of the GKSL dynamical map
`Λ_t = e^{tℒ}` *conditionally* on a disclosed hypothesis `hreal`: that `Λ_t` is realized by a Kraus
channel (its complete positivity, the physical content of the GKSL theorem). This module discharges
`hreal` by **proving** that `Λ_t` is completely positive — hence (finite-dimensional Choi/Kraus
theorem) a Kraus channel — so the contraction becomes unconditional.

The route (Lie–Trotter): `ℒ = ℒ_jump + ℒ_drift` with `ℒ_jump` the dissipator (completely positive,
`lindblad_generator_CP`) and `ℒ_drift(ρ) = Gρ + ρG†` a conjugation generator (so `e^{sℒ_drift}` is
conjugation by `e^{sG}`, completely positive). Each Trotter factor `e^{(t/n)ℒ_drift} e^{(t/n)ℒ_jump}`
is CP; `e^{tℒ} = lim_n (e^{(t/n)ℒ_drift} e^{(t/n)ℒ_jump})^n` (matrix Lie–Trotter — built from scratch,
absent from Mathlib); CP is closed under limits (Choi matrix PSD, and the PSD cone is closed). Hence
`e^{tℒ}` is CP.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`; zero `sorry`; no new axiom;
no `maxHeartbeats`; no `native_decide`.
-/

namespace SKEFTHawking.OpenSystems

open scoped Matrix ComplexOrder
open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

omit [Fintype n] [DecidableEq n] in
/-- **The positive-semidefinite cone is closed.** A limit of positive-semidefinite matrices is
positive semidefinite — the topological input to "complete positivity is closed under limits". -/
lemma posSemidef_of_tendsto {A : ℕ → Matrix n n ℂ} {L : Matrix n n ℂ}
    (hA : Filter.Tendsto A Filter.atTop (nhds L)) (hpsd : ∀ k, (A k).PosSemidef) :
    L.PosSemidef := by
  refine ⟨?_, fun x => ?_⟩
  · have hconj : Filter.Tendsto (fun k => (A k)ᴴ) Filter.atTop (nhds Lᴴ) :=
      (Continuous.tendsto (f := fun B : Matrix n n ℂ => Bᴴ) (by fun_prop) L).comp hA
    rw [show (fun k => (A k)ᴴ) = A from funext fun k => (hpsd k).1] at hconj
    exact tendsto_nhds_unique hconj hA
  · have hcont : Continuous (fun B : Matrix n n ℂ =>
        x.sum fun i xi => x.sum fun j xj => star xi * B i j * xj) := by
      simp only [Finsupp.sum]
      exact continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => by fun_prop
    exact ge_of_tendsto' ((hcont.tendsto L).comp hA) fun k => (hpsd k).2 x

end SKEFTHawking.OpenSystems
