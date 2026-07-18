import Mathlib
import SKEFTHawking.SingularRelativeCapHomology

/-!
# The relative (2,3,5) cup–cap adjunction — foundation for P23 `nondeg`'s `hcompat`

The cohomology-class specialization of the relative descended cap–cup adjunction
(`SingularRelativeCapHomology.relKroneckerH_relCupRightGeneralH`) at the degrees the
`SphereProdP23Nondeg` intertwining needs: an **absolute** left factor `a ∈ H²(X)`, a **relative**
right factor `b ∈ H³(X, S)`, and a **relative** class `z ∈ H₅(X, S)`:

  `⟨a ∪ b, z⟩ = ⟨b, a ⌢ z⟩`   with   `a ∪ b = relCupH23 a b ∈ H⁵(X,S)`,
  `a ⌢ z = capRelH 2 2 a z ∈ H₃(X,S)`.

The general adjunction is already banked chain-descended, but stated through the
cocycle-representative left cup `relCupRightGeneralH a` (`a` a chosen cocycle in `ker δ₂`). This
module lifts it to the named `(2,3)` relative cup `relCupH23`, whose left argument is a full
cohomology **class** `H²(X)` — the exact shape `hcompat`'s `⟨relCupH23 a b, [W,∂W]⟩` cup-Fubini step
consumes. It is the relative-pair `(X, S)` mirror of the closed-surface
`SingularSurfaceIntersectionForm.intersectionForm_eq_kronecker_cap`.

The `(1,4,5)` sibling `relKroneckerH_relCupH14` (`relCupH14`, the other named relative cup, `H¹×H⁴`)
is included: same one-line descent, a general reusable foundation for relative Poincaré–Lefschetz.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`. A clean (co)homology-level port — no fresh chain identity required (the chain-level
`SingularCapChainIncl.kronecker_cup_cap` already carries all the content, via the banked generic).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativePairing
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.SingularRelativeCapHomology

namespace SKEFTHawking.SingularRelativeCupCap23

variable {X : TopCat} {S : Set X}

/-- **The relative `(2,3,5)` cup–cap adjunction** `⟨a ∪ b, z⟩ = ⟨b, a ⌢ z⟩` for `a ∈ H²(X)`,
`b ∈ H³(X, S)`, `z ∈ H₅(X, S)`. The cohomology-class form of the banked
`relKroneckerH_relCupRightGeneralH` with the named relative cup `relCupH23` on the left and the
relative cap `capRelH 2 2` on the right — the foundation `SphereProdP23Nondeg`'s `hcompat`
cup-Fubini step rests on. Relative-pair mirror of `intersectionForm_eq_kronecker_cap`. -/
theorem relKroneckerH_relCupH23 (a : Cohomology X 2) (b : RelativeCohomology S 3)
    (z : RelativeHomology S 5) :
    relKroneckerH S (relCupH23 a b) z = relKroneckerH S b (capRelH 2 2 a z) := by
  obtain ⟨fc, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  exact relKroneckerH_relCupRightGeneralH fc b z

/-- **The relative `(1,4,5)` cup–cap adjunction** `⟨a ∪ b, z⟩ = ⟨b, a ⌢ z⟩` for `a ∈ H¹(X)`,
`b ∈ H⁴(X, S)`, `z ∈ H₅(X, S)` — the `relCupH14` sibling of `relKroneckerH_relCupH23`; a general
reusable foundation for relative Poincaré–Lefschetz. -/
theorem relKroneckerH_relCupH14 (a : Cohomology X 1) (b : RelativeCohomology S 4)
    (z : RelativeHomology S 5) :
    relKroneckerH S (relCupH14 a b) z = relKroneckerH S b (capRelH 1 3 a z) := by
  obtain ⟨fc, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  exact relKroneckerH_relCupRightGeneralH fc b z

end SKEFTHawking.SingularRelativeCupCap23
