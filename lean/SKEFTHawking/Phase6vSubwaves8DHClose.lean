/-
# `lean/SKEFTHawking/Phase6vSubwaves8DHClose.lean` — Phase 6v
Sub-waves 8.D-8.H cumulative closure

**Cumulative closure theorem** rolling up the five strengthening
sub-waves into a single Lean theorem-level witness. Per ADV-3 of
the Sub-wave 8.D-8.H final adversarial review (2026-05-26 PM): the
architectural coherence of the strengthening pass should be visible
at the Lean level, not just in commit messages.

This module ships ONE theorem aggregating the five sub-wave closures
and demonstrating the cumulative architecture is coherent:

  • 8.D substrate (`Matrix.pfaffianFin4` algebraic properties).
  • 8.E Hamiltonian bridge (TRS-conjugation consistency at Γ).
  • 8.F Z₁₆ Rokhlin cross-bridge (universally over DIII-topological).
  • 8.G integer-winding-surrogate parity correspondence.
  • 8.H generic-`Fintype T` TRIM-enumeration acceptance.

## Zero new project-local axioms

Pipeline Invariant #15. Kernel-only
`[propext, Classical.choice, Quot.sound]`.
-/
import SKEFTHawking.MathlibAux.Pfaffian
import SKEFTHawking.BdGHamiltonianNbRe
import SKEFTHawking.CrossBridges.NbReDIIIToPinPlusZ16
import SKEFTHawking.NbReWindingNumber
import SKEFTHawking.TRIMParameterization

namespace SKEFTHawking.Phase6vSubwaves8DHClose

open SKEFTHawking SKEFTHawking.NbReTripletSPT

/-- **Phase 6v Sub-waves 8.D through 8.H cumulative substantive closure.**

Single aggregated witness: each sub-wave's closure bundle is invoked
as a conjunct, demonstrating the strengthening-pass architecture
holds simultaneously at the Lean theorem level. -/
theorem subwaves_8_D_through_H_cumulative_closure :
    -- Sub-wave 8.D: general Pfaffian substrate algebraic properties
    (∀ {R : Type*} [CommRing R] (a b c d e f : R),
      MathlibAux.Matrix.pfaffianFin4 (MathlibAux.Matrix.antisymMatrix4 a b c d e f) =
        a * f - b * e + c * d) ∧
    -- Sub-wave 8.E: Hamiltonian bridge substantive closure
    BdGHamiltonianNbRe.Theta.transpose = -BdGHamiltonianNbRe.Theta ∧
    BdGHamiltonianNbRe.Theta * BdGHamiltonianNbRe.Theta = -1 ∧
    BdGHamiltonianNbRe.sewingMatrixDerivedAtGamma nbReParameters 0 2 = -1 ∧
    BdGHamiltonianNbRe.sewingMatrixDerivedAtGamma elementalNbParameters 0 2 = 1 ∧
    -- Sub-wave 8.F: Z₁₆ Rokhlin cross-bridge universal claim
    (∀ sc : SCParameters,
      IsDIIITopologicalSuperconductor sc →
      CrossBridges.NbReDIIIToPinPlusZ16.diiiBdGToZ16 sc = 1) ∧
    -- Sub-wave 8.G: surrogate-winding parity correspondence
    (∀ sc : SCParameters,
      NbReWindingNumber.windingNumberSurrogate sc = 0 ↔ sc.centrosymmetric = true) ∧
    -- Sub-wave 8.H: universal generic-Fintype trivial-pattern theorem
    (∀ {T : Type*} [Fintype T] (pfSignAt : T → ℤ),
      (∀ k : T, pfSignAt k = 1) → TRIMParameterization.genericFuKaneInvariant pfSignAt = 1) :=
  ⟨@MathlibAux.Matrix.pfaffianFin4_antisymMatrix4,
   BdGHamiltonianNbRe.Theta_transpose,
   BdGHamiltonianNbRe.Theta_sq,
   BdGHamiltonianNbRe.nbRe_sewingMatrixDerivedAtGamma_entry_0_2,
   BdGHamiltonianNbRe.elementalNb_sewingMatrixDerivedAtGamma_entry_0_2,
   CrossBridges.NbReDIIIToPinPlusZ16.diiiBdGToZ16_eq_one_of_DIII_topological,
   NbReWindingNumber.windingNumberSurrogate_eq_zero_iff,
   @TRIMParameterization.genericFuKaneInvariant_trivial_of_all_pos⟩

end SKEFTHawking.Phase6vSubwaves8DHClose
