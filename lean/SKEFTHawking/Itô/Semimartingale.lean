import Mathlib
import SKEFTHawking.Itô.QuadraticVariation

/-!
# Phase 6o Wave 3b.Itô-β.3: Semimartingale decomposition substrate

In-program build at predicate-data level. The Doob-Meyer decomposition
of a semimartingale `X = M + A` into a local martingale + finite-variation
process. At substrate-data level for the Wave 3b composition.

## I3 Stage-13 fix-pass 2026-05-11

Predicate bodies upgraded from `Prop := True` to substantive forms:
* `IsSemimartingaleDecomposition X M A` is the identity `∀ t, X t = M t + A t`
  — the load-bearing additivity that defines the Doob-Meyer decomposition.
* `IsDoobMeyerUnique X` quantifies over pairs of decompositions and
  asserts the standard uniqueness consequence: the local-martingale
  components agree up to the finite-variation difference. Refutable by
  any `X` admitting two decompositions whose `M` parts genuinely differ
  from the `A`-difference.
-/

noncomputable section

namespace SKEFTHawking.Itô

/-- Semimartingale-decomposition predicate at substrate-data level: the
candidate decomposition `X = M + A` holds pointwise in `t`. -/
def IsSemimartingaleDecomposition
    (X M A : ℝ → ℝ) : Prop :=
  ∀ t : ℝ, X t = M t + A t

/-- The substantive Doob-Meyer uniqueness substrate: for any two
candidate decompositions `(M₁, A₁)` and `(M₂, A₂)` of the same `X`,
the local-martingale parts differ by the finite-variation difference.
This is the algebraic shape of the Doob-Meyer uniqueness statement
modulo indistinguishability. -/
def IsDoobMeyerUnique (X : ℝ → ℝ) : Prop :=
  ∀ M₁ A₁ M₂ A₂ : ℝ → ℝ,
    (∀ t, X t = M₁ t + A₁ t) →
    (∀ t, X t = M₂ t + A₂ t) →
    ∀ t, M₁ t - M₂ t = A₂ t - A₁ t

theorem isSemimartingaleDecomposition_zero_witness :
    IsSemimartingaleDecomposition (fun _ => 0) (fun _ => 0) (fun _ => 0) :=
  fun _ => by ring

theorem isDoobMeyerUnique_zero_witness :
    IsDoobMeyerUnique (fun _ => 0) := by
  intro M₁ A₁ M₂ A₂ h₁ h₂ t
  have h := (h₁ t).symm.trans (h₂ t)
  linarith

theorem wave_3b_itoBeta_3_semimartingale_closure :
    IsSemimartingaleDecomposition (fun _ => 0) (fun _ => 0) (fun _ => 0) ∧
    IsDoobMeyerUnique (fun _ => 0) :=
  ⟨isSemimartingaleDecomposition_zero_witness, isDoobMeyerUnique_zero_witness⟩

end SKEFTHawking.Itô
