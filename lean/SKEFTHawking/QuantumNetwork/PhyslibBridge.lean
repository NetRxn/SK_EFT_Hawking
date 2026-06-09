import SKEFTHawking.QuantumNetwork.CPTPChannel
import QuantumInfo.Finite.CPTPMap.CPTP
import QuantumInfo.Finite.Entropy.DPI

/-!
# Phase 6AM Wave 2 — Kraus ↔ MState / CPTPMap bridge to PhysLib

A **faithful** bridge connecting the repo's concrete Kraus-family quantum-information substrate
(`krausMap`, `IsKrausChannel`, `IsDensityOperator` on `Matrix ι ι ℂ`) to PhysLib's bundled
`MState` / `CPTPMap` representation (arXiv:2510.08672), so the repo's objects can be fed to
PhysLib's data-processing / strong-subadditivity / entropy theorems and the results read back as
statements about the repo's representation.

* `toMState ρ hρ : MState ι`                 — repo density operator → PhysLib `MState`
* `toCPTPMap K hK : CPTPMap ι ι`             — repo Kraus channel → PhysLib `CPTPMap`
* `toCPTPMap_apply_m`                         — **faithful round-trip** on the FULL Kraus class:
    `(toCPTPMap K hK (toMState ρ hρ)).m = krausMap K ρ` (channel → CPTPMap → repo = `id`)
* `toCPTPMap_apply_eq`                        — the round-trip lifted to `MState` equality
* `krausMap_sandwichedRenyi_DPI`              — **transfer witness**: the repo's Kraus channels
    inherit PhysLib's data-processing inequality for the sandwiched Rényi relative entropy. The
    PhysLib FQN `PhysLib's `sandwichedRenyiEntropy_DPI` (`QuantumInfo/Finite/Entropy/DPI.lean`)` is *invoked in the proof body*
    (CLAUDE.md P6), so `#print axioms` shows the PhysLib closure.

The channel bridge is a faithful *identification* rather than a Choi reconstruction: PhysLib's
`MatrixMap.of_kraus K K = ∑ₖ Kₖ · X · Kₖᴴ` coincides definitionally with the repo's `krausMap K`,
and PhysLib's `CPTPMap.of_kraus_CPTPMap` takes exactly the repo's trace-preservation hypothesis
`IsKrausChannel K = (∑ₖ Kₖᴴ Kₖ = 1)`.

Invariants: kernel-pure `{propext, Classical.choice, Quot.sound}`, zero project-local axioms,
no `maxHeartbeats`. Does NOT depend on PhysLib `Relative.lean`'s single sorried declaration
(`qRelativeEnt_joint_convexity`) — verified by `#print axioms`.
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder

variable {m : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- **State bridge.** A repo density operator (`PosSemidef ∧ trace = 1`) becomes a PhysLib
`MState` (a `HermitianMat` that is `0 ≤ ·` with real trace `1`). -/
noncomputable def toMState (ρ : Matrix ι ι ℂ) (hρ : IsDensityOperator ρ) : MState ι where
  M := ⟨ρ, hρ.1.isHermitian⟩
  nonneg := by rw [HermitianMat.zero_le_iff]; exact hρ.1
  tr := by rw [HermitianMat.trace_eq_re_trace, HermitianMat.mat_mk, hρ.2]; simp

@[simp] theorem toMState_m (ρ : Matrix ι ι ℂ) (hρ : IsDensityOperator ρ) :
    (toMState ρ hρ).m = ρ := rfl

/-- **Channel bridge.** A repo Kraus channel (`krausMap K` with `IsKrausChannel K`) becomes a
PhysLib `CPTPMap`. The trace-preservation hypothesis `IsKrausChannel K = (∑ₖ Kₖᴴ Kₖ = 1)` is
*exactly* the hypothesis `CPTPMap.of_kraus_CPTPMap` requires. -/
noncomputable def toCPTPMap (K : Fin m → Matrix ι ι ℂ) (hK : IsKrausChannel K) : CPTPMap ι ι :=
  CPTPMap.of_kraus_CPTPMap K hK

omit [DecidableEq ι] in
/-- PhysLib's `MatrixMap.of_kraus K K` (the map `X ↦ ∑ₖ Kₖ X Kₖᴴ`) agrees pointwise with the
repo's `krausMap K`. This is the definitional heart of the channel bridge. -/
theorem krausMap_eq_of_kraus (K : Fin m → Matrix ι ι ℂ) (X : Matrix ι ι ℂ) :
    krausMap K X = MatrixMap.of_kraus K K X := by
  simp only [krausMap, MatrixMap.of_kraus, LinearMap.coe_sum, Finset.sum_apply,
    LinearMap.coe_mk, AddHom.coe_mk]

/-- **Faithful round-trip (matrix level).** Bridging a repo Kraus channel to a PhysLib `CPTPMap`,
applying it to a bridged density operator, and reading the result back as a matrix recovers the
repo channel's action `krausMap K ρ` — on the FULL Kraus-channel class, not a trivial subclass. -/
theorem toCPTPMap_apply_m (K : Fin m → Matrix ι ι ℂ) (hK : IsKrausChannel K)
    (ρ : Matrix ι ι ℂ) (hρ : IsDensityOperator ρ) :
    (toCPTPMap K hK (toMState ρ hρ)).m = krausMap K ρ := by
  rw [toCPTPMap, CPTPMap.mat_coe_eq_apply_mat, toMState_m, krausMap_eq_of_kraus]
  rfl

/-- **Round-trip (`MState` level).** The bridged channel output equals the bridge of the repo
channel's output density operator. -/
theorem toCPTPMap_apply_eq (K : Fin m → Matrix ι ι ℂ) (hK : IsKrausChannel K)
    (ρ : Matrix ι ι ℂ) (hρ : IsDensityOperator ρ) :
    toCPTPMap K hK (toMState ρ hρ)
      = toMState (krausMap K ρ) (krausMap_isDensityOperator hK hρ) := by
  refine MState.ext_m ?_
  rw [toMState_m]
  exact toCPTPMap_apply_m K hK ρ hρ

/-- **Transfer witness (P6-faithful).** The repo's Kraus channels inherit PhysLib's
**data-processing inequality** for the sandwiched Rényi relative entropy: for `α ≥ 1` and density
operators `ρ, σ`, the entropy between the channel *outputs* `krausMap K ρ`, `krausMap K σ` is at
most the entropy between the *inputs*. The bound is `PhysLib's `sandwichedRenyiEntropy_DPI` (`QuantumInfo/Finite/Entropy/DPI.lean`)`
invoked in the proof body, transported across the Wave-2 round-trip so the statement is phrased on
the repo's `krausMap`. -/
theorem krausMap_sandwichedRenyi_DPI {α : ℝ} (hα : 1 ≤ α)
    (K : Fin m → Matrix ι ι ℂ) (hK : IsKrausChannel K)
    (ρ σ : Matrix ι ι ℂ) (hρ : IsDensityOperator ρ) (hσ : IsDensityOperator σ) :
    SandwichedRelRentropy α (toMState (krausMap K ρ) (krausMap_isDensityOperator hK hρ))
        (toMState (krausMap K σ) (krausMap_isDensityOperator hK hσ))
      ≤ SandwichedRelRentropy α (toMState ρ hρ) (toMState σ hσ) := by
  have hdpi := sandwichedRenyiEntropy_DPI hα (toMState ρ hρ) (toMState σ hσ) (toCPTPMap K hK)
  rwa [toCPTPMap_apply_eq, toCPTPMap_apply_eq] at hdpi

end SKEFTHawking.QuantumNetwork
