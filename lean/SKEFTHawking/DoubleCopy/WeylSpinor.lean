import Mathlib
import SKEFTHawking.DoubleCopy.PetrovD

/-!
# Phase 6o Wave 1b.4: Weyl curvature-spinor double-copy — precondition + gap

## Goal (R-02 remediation, 2026-07-20)

The Newman-Penrose curvature-spinor reformulation of the Kerr-Schild double
copy states that for a Petrov-D vacuum spacetime the Weyl curvature spinor
factorizes as `Ψ_ABCD = Φ_(AB Φ_CD) / S`, where `Φ_AB` is the Maxwell spinor
of the single copy (Luna-Monteiro-Nicholson-O'Connell arXiv:1810.08183).

## What is verified vs. gapped (honest scope)

* **Verified (Mathlib-checkable):** the *precondition* for the Weyl double copy
  — the metric satisfies the Kerr-Schild algebraically-special criterion
  (`IsPetrovD`, a nonzero null KS congruence) and admits the exact single-copy
  reconstruction (`PetrovD.kerrSchild_exact_inverse`). `IsWeylDoubleCopy` records
  this precondition.
* **Documented gap (NOT verified):** the curvature-spinor identity
  `Ψ_ABCD = Φ_(AB Φ_CD)/S` itself. This requires a Newman-Penrose /
  curvature-spinor formalism (2-spinor `SL(2,ℂ)` index calculus, the Weyl
  spinor `Ψ_ABCD`, symmetrized products) that is **not present in Mathlib**
  (CK-Duality DR §8.2: "no spinor-helicity formalisation"; PhysLean's tensor
  index notation arXiv:2411.07667 does not ship the NP framework). Encoding the
  spinor identity is a substantial future build; Lean does not assert it here.

`IsWeylDoubleCopy` is therefore deliberately the *precondition predicate*, not
the spinor-formula theorem — the honest statement of what the substrate
verifies (cf. CK-Duality DR §7.2, which lists this as GO *conditional on* a
spinor formalism).

## References

- Luna-Monteiro-Nicholson-O'Connell, arXiv:1810.08183 (Type D + Weyl DC).
- Twistor-space derivation: arXiv:2103.16441 (all Petrov types).
- CK-Duality DR §7.2 + §8.2.
-/

noncomputable section

namespace SKEFTHawking.DoubleCopy

/-- The **precondition** for the Weyl curvature-spinor double copy: the metric
satisfies the Kerr-Schild algebraically-special (Petrov-D) criterion. The
curvature-spinor identity `Ψ = Φ_(AB Φ_CD)/S` itself is a documented gap (needs
NP spinor formalism absent from Mathlib) — see the module docstring. -/
def IsWeylDoubleCopy (m : AnalogMetric) : Prop :=
  IsPetrovD m

theorem isWeylDoubleCopy_all (m : AnalogMetric) :
    IsWeylDoubleCopy m :=
  ⟨admitsKerrSchildForm_all m, ksNull_ne_zero m⟩

/-- Wave 1b.4 deliverable: all three program substrates satisfy the Weyl
double-copy *precondition* (Petrov-D Kerr-Schild criterion). The curvature-spinor
identity is a documented gap. -/
theorem wave_1b_4_weylSpinor_closure :
    ∀ m : AnalogMetric, IsWeylDoubleCopy m := isWeylDoubleCopy_all

end SKEFTHawking.DoubleCopy
