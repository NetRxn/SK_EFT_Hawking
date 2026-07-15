/-
# Phase 5q.H W-A arm 4 — THE addClosure CLOSER: `WAdmPinned.add` + `ofCylinderEngineClosed`

The final wiring of the disjoint-union `addClosure`. `WAdmPinned.add` produces a pinned
W-admissibility datum on `b₁.add b₂` from those on `b₁`, `b₂`: it feeds the two summands' pinned
Lefschetz–Wu data into `PoincareLefschetzWuBlockAssembly.exists_wuAdmPinned_sum` (with the concrete
`sumRelFundClass` block-sum relative fundamental class), obtaining a pinned pair with `w₂ = 0` on the
disjoint-union pair `(A ⊔ B, S₁ ⊔ S₂)`, then transports it onto `∂(b₁.add b₂)` along the
`ModelWithCorners.boundary_disjointUnion` set equality (carrier `TopCat.of (b₁.add b₂).W` is defeq to
the sum space; the boundary set differs propositionally — `datumTransport` carries the pinned data).

`ofCylinderEngineClosed` then closes the carrier's abstract provider entirely: it supplies
`WAdmPinned.add` as the `addClosure` argument of `ofCylinderEngine`, so a `CharPairWProviderPerOp` is
inhabited from ONLY the concrete Track-2 cylinder residual `∀ s, CharPairStrBundled I s → CylWAdmData s`
— the whole `addClosure` residual is discharged.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusCharPairWProviderTransport
import SKEFTHawking.PoincareLefschetzRelFundClassSumGen

open scoped Manifold
open SKEFTHawking.BordismTheory
open SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.PoincareLefschetzWuBlockAssembly
open SKEFTHawking.PoincareLefschetzRelFundClassSumGen
open SKEFTHawking.SingularCohomologyDisjointSum
open SKEFTHawking.SingularRelativeCohomologyDisjointSum
open SKEFTHawking.PinPlusWAdmPinned
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairWProviderTransport
open SKEFTHawking.PinPlusCharPairBorTethered

namespace SKEFTHawking.PinPlusWAdmPinned

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]

/-- **THE `add`-CLOSURE** — a pinned W-admissibility datum on the disjoint-union bordism `b₁.add b₂`
from those on `b₁`, `b₂`. Assembles the block-sum pinned Lefschetz–Wu pair
(`exists_wuAdmPinned_sum` + `sumRelFundClass`) on `(A ⊔ B, S₁ ⊔ S₂)` and transports it onto
`∂(b₁.add b₂)` via `boundary_disjointUnion` (the datum-transport of `sumSet = ∂(b₁.add b₂)`). -/
def WAdmPinned.add {s₁ t₁ s₂ t₂ : SingularManifold.{0} PUnit.{1} k I}
    {b₁ : Bordism (I.prod (𝓡∂ 1)) s₁ t₁} {b₂ : Bordism (I.prod (𝓡∂ 1)) s₂ t₂}
    (w₁ : WAdmPinned b₁) (w₂ : WAdmPinned b₂) : WAdmPinned (b₁.add b₂) := by
  have hsum := exists_wuAdmPinned_sum (A := TopCat.of b₁.W) (B := TopCat.of b₂.W)
    (S₁ := (I.prod (𝓡∂ 1)).boundary b₁.W) (S₂ := (I.prod (𝓡∂ 1)).boundary b₂.W)
    sumRelFundClass w₁.pin14 w₁.pin23 w₂.pin14 w₂.pin23 w₁.wadm.hwu w₂.wadm.hwu
  have hbdry : sumSet (TopCat.of b₁.W) (TopCat.of b₂.W) ((I.prod (𝓡∂ 1)).boundary b₁.W)
      ((I.prod (𝓡∂ 1)).boundary b₂.W) = (I.prod (𝓡∂ 1)).boundary (b₁.add b₂).W := by
    rw [sumSet]
    exact (ModelWithCorners.boundary_disjointUnion (I := I.prod (𝓡∂ 1))
      (M := b₁.W) (M' := b₂.W)).symm
  exact
    { wadm :=
        { P14 := datumTransport hbdry hsum.choose
          P23 := datumTransport hbdry hsum.choose_spec.choose
          hwu := datumTransport_hwu hbdry hsum.choose hsum.choose_spec.choose
            hsum.choose_spec.choose_spec.2.2 }
      pin14 := datumTransport_pin14 hbdry hsum.choose hsum.choose_spec.choose_spec.1
      pin23 := datumTransport_pin23 hbdry hsum.choose_spec.choose
        hsum.choose_spec.choose_spec.2.1 }

end

end SKEFTHawking.PinPlusWAdmPinned

/-! ## THE CLOSER — `CharPairWProviderPerOp.ofCylinderEngineClosed`. -/

namespace SKEFTHawking.PinPlusCharPairBorTethered

open SKEFTHawking.BordismTheory
open SKEFTHawking.PinPlusWAdmPinned
open SKEFTHawking.PinPlusCharPairWProviderTransport

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]

/-- **THE FULLY-CLOSED PROVIDER** — a `CharPairWProviderPerOp I k` from ONLY the concrete Track-2
cylinder residual: the abstract `addClosure` field is discharged by `WAdmPinned.add` (the
disjoint-union Lefschetz–Wu assembly closed by `sumRelFundClass`). This is the document of record for
the provider inhabitation: the sole remaining hypothesis row is
`cylData : ∀ {s} (σ : CharPairStrBundled I s), CylWAdmData s` (the σ-threaded, honest-inhabitable
concrete-cylinder residual). -/
def CharPairWProviderPerOp.ofCylinderEngineClosed
    (cylData : ∀ {s : SingularManifold.{0} PUnit.{1} k I},
      CharPairStrBundled I s → CylWAdmData s) :
    CharPairWProviderPerOp I k :=
  CharPairWProviderPerOp.ofCylinderEngine cylData WAdmPinned.add

end

end SKEFTHawking.PinPlusCharPairBorTethered
