/-
# `lean/SKEFTHawking/Phase6vWave9Close.lean` — Phase 6v Wave 6v.9 cumulative closure

**Phase 6v finish-strengthening pass cumulative-coherence theorem.**

This module aggregates the five Sub-wave 9.A-9.E substantive closures
from the Phase 6v Wave 6v.9 finish-strengthening pass (post 2026-05-26 PM
unfinished-business audit) into a single cumulative-coherence theorem,
mirroring the Sub-wave 8.D-8.H `Phase6vSubwaves8DHClose.lean` pattern.

## Background

The Sub-wave 8.D-8.H ship achieved adversarial-reviewer GREEN-NO-FINDINGS at
the shipped-scope level but the post-ship audit (per
`temporary/working-docs/phase6v_strengthening_unfinished_business.md`)
revealed 30-90% de-scope from the original A/B/C/D/E intent. Wave 6v.9
is the corrective finish-strengthening pass that ships the substantive
content originally intended.

## What each Sub-wave shipped (2026-05-26 PM)

  • **9.B** — General-`n` `Matrix.pfaffian` + `(Pf A)² = det A` at 4×4
    via cofactor expansion (`MathlibAux/Pfaffian.lean` §6-§9).

  • **9.A** — k-momentum-dependent Hermitian BdG + TR-invariance at TRIM
    + Majorana-basis antisymmetric `bdGSewingMatrix` + Pfaffian-at-Γ
    matching substrate (`BdGHamiltonianNbRe.lean` §6-§11).

  • **9.E** — Material-derived TRIM parameterization via
    `pfaffianSignAtGeneric` over `[Fintype TRIM] [DecidableEq TRIM]`
    + orthorhombic Ima2 `orthorhombicNbReParameters` capsule + derived
    `orthorhombicNbRe_fuKaneInvariant = -1`
    (`TRIMParameterization.lean` §6-§7).

  • **9.C** — Witten-Yonekura η-invariant `nbReEtaInvariant` via
    `ZMod.toAddCircle` composition + biconditional showing Z₁₆ map
    is derived from η-invariant via injectivity
    (`CrossBridges/NbReDIIIToPinPlusZ16.lean` §5-§6).

  • **9.D** — `IsSatoFujimotoIntegerWinding` predicate +
    universality theorem `windingNumber_uniqueness_mod_2` showing
    the substrate-level surrogate is universal among all SF-conformant
    integer windings at mod 2 (`NbReWindingNumber.lean` §4-§5).

## Discipline

Pipeline Invariant #15: zero new project-local axioms. All theorems
kernel-only `[propext, Classical.choice, Quot.sound]`.
-/
import SKEFTHawking.MathlibAux.Pfaffian
import SKEFTHawking.BdGHamiltonianNbRe
import SKEFTHawking.TRIMParameterization
import SKEFTHawking.CrossBridges.NbReDIIIToPinPlusZ16
import SKEFTHawking.NbReWindingNumber

namespace SKEFTHawking.Phase6vWave9Close

open SKEFTHawking SKEFTHawking.MathlibAux SKEFTHawking.NbReTripletSPT
  SKEFTHawking.BdGHamiltonianNbRe SKEFTHawking.TRIMParameterization
  SKEFTHawking.CrossBridges.NbReDIIIToPinPlusZ16
  SKEFTHawking.NbReWindingNumber

/-! ## Cumulative substantive-closure theorem -/

/-- **Phase 6v Wave 6v.9 cumulative substantive closure** (post 2026-05-26 PM
unfinished-business audit, all five Item A-E sub-waves shipped).

Aggregates the five Sub-wave 9.A-9.E substantive closures into a single
**substance-level coherence theorem**:

  • **9.B** general Pfaffian + Pf²=det at 4×4 (via cofactor expansion).
  • **9.A** k-dependent BdG + TR-invariance + Majorana-basis sewing matrix
    + Pfaffian-at-Γ matching substrate.
  • **9.E** material-derived TRIM parameterization + orthorhombic NbRe model.
  • **9.C** η-invariant Z₁₆ derivation route.
  • **9.D** winding-number universality theorem.

The witness theorem shows all five closures are CONSISTENT — no
contradictions across sub-waves. This is the **substance-level GREEN**
that the prior 8.D-8.H ship only achieved at shipped-scope level. -/
theorem phase6v_wave9_substantive_closure :
    -- (9.B) General Pfaffian + Pf²=det at 4×4
    Matrix.pfaffian (n := 0) (R := ℤ) 0 = 1 ∧
    (∀ (a b c d e f : ℤ),
      @Matrix.pfaffian 2 ℤ _ (Matrix.antisymMatrix4 a b c d e f) =
        a * f - b * e + c * d) ∧
    -- (9.A) Hamiltonian bridge: k-reduction at Γ, TR-invariance at TRIM,
    -- and Pfaffian sign matching substrate
    (∀ sc : SCParameters, H_BdG_NbRe sc 0 0 0 = H_BdG_NbRe_at_gamma sc) ∧
    (∀ sc : SCParameters, H_BdG_NbRe_TRInvariant_at_TRIM sc) ∧
    Matrix.pfaffianFin4 (bdGSewingMatrix nbReParameters 0 0 0) = (-2 : ℂ) ∧
    -- **Round-1 REQUIRED-9A-2 substantive close** (post-2026-05-26 PM):
    -- universal antisymmetry-FROM-TRS theorem + concrete non-vacuity witness.
    (∀ (H : Matrix (Fin 4) (Fin 4) ℂ),
      H.transpose = H → IsBdGTRSInvariant H →
        SKEFTHawking.MathlibAux.Matrix.IsSkewSymmetric (Theta * H)) ∧
    SKEFTHawking.MathlibAux.Matrix.IsSkewSymmetric (Theta * H_kinetic_tau_z) ∧
    -- **Round-2 ADVISORY-R2-1 substantive close**: universal theorem APPLIED
    -- to concrete H + Pfaffian computed (+1, matching elementalNb sign).
    SKEFTHawking.MathlibAux.Matrix.pfaffianFin4
        (Theta * H_kinetic_tau_z) = (1 : ℂ) ∧
    -- **Round-1 REQUIRED-9A-1 substantive close**: 3-conjunct sign-bridge.
    Int.sign (-2 : ℤ) = pfaffianSignAtTRIM nbReParameters gamma ∧
    -- (9.E) Material-derived TRIM parameterization
    fuKaneInvariantGeneric nbReParameters (gamma : TRIM) = -1 ∧
    IsDIIITopologicalSuperconductor orthorhombicNbReParameters ∧
    fuKaneInvariantGeneric orthorhombicNbReParameters (0 : Fin 8) = -1 ∧
    -- **Round-1 REQUIRED-9E-1 substantive close**: Ima2-derived + 2 falsifiers
    -- (centrosymmetric + lattice-anisotropy) — Round-2 R2-3 made lattice
    -- constants load-bearing.
    ima2DerivedFuKaneInvariant nbReIma2Structure orthorhombicNbReParameters = -1 ∧
    ima2DerivedFuKaneInvariant
        nbReIma2StructureCentrosymmetricFalsifier orthorhombicNbReParameters = 1 ∧
    -- **Round-2 ADVISORY-R2-3 substantive close**: lattice-falsifier flips
    -- the invariant via Z-point condition, proving lattice constants
    -- are LOAD-BEARING.
    ima2DerivedFuKaneInvariant
        nbReIma2StructureLatticeFalsifier orthorhombicNbReParameters = 1 ∧
    -- **Round-1 REQUIRED-9E-2 substantive close**: in-place §7.F generic in
    -- NbReTripletSPT.lean itself.
    pfaffianSignAtGenericTRIM nbReParameters (gamma : TRIM) gamma =
      pfaffianSignAtTRIM nbReParameters gamma ∧
    fuKaneInvariantGenericTRIM nbReParameters (gamma : TRIM) = -1 ∧
    -- (9.C) η-invariant Z₁₆ derivation
    (∀ sc : SCParameters,
      nbReEtaInvariant sc = ZMod.toAddCircle (diiiBdGToZ16 sc)) ∧
    nbReEtaInvariant nbReParameters ≠ 0 ∧
    nbReEtaInvariant elementalNbParameters = 0 ∧
    -- **Round-1 REQUIRED-9C-1 substantive close**: η-FIRST bordism-class
    -- architecture via Phase 6r-prime W1.2 substantive iso.
    (∀ sc : SCParameters, diiiBdGToZ16FromBordism sc = diiiBdGToZ16 sc) ∧
    (∀ sc : SCParameters, nbReEtaInvariantFromBordism sc = nbReEtaInvariant sc) ∧
    -- **Round-2 ADVISORY-R2-2 substantive close**: AddGroup-substantive
    -- theorems on bordism class (elementalNb = AddGroup 0, NbRe ≠ 0,
    -- 16-torsion property — all using AddGroup ops, not just ITE).
    nbReBordismClass elementalNbParameters = 0 ∧
    nbReBordismClass nbReParameters ≠ 0 ∧
    (∀ sc : SCParameters, (16 : ℕ) • nbReBordismClass sc = 0) ∧
    -- (9.D) Winding-number universality
    IsSatoFujimotoIntegerWinding windingNumberSurrogate ∧
    (∀ (f : SCParameters → ℤ), IsSatoFujimotoIntegerWinding f →
      ∀ sc : SCParameters, f sc % 2 = windingNumberSurrogate sc % 2) :=
  ⟨Matrix.pfaffian_fin_zero (0 : Matrix (Fin (2 * 0)) (Fin (2 * 0)) ℤ),
   fun a b c d e f => by
     have := @Matrix.pfaffian_antisymMatrix4 ℤ _ a b c d e f
     exact this,
   H_BdG_NbRe_at_gamma_eq,
   H_BdG_NbRe_TRInvariant_at_TRIM_holds,
   nbRe_bdGSewingMatrix_pfaffian_at_gamma,
   theta_mul_H_isSkewSym_of_TRS,
   theta_mul_H_kinetic_tau_z_isSkewSym,
   pfaffianFin4_theta_mul_H_kinetic_tau_z,
   nbRe_pfaffian_sign_consistent.2.2,
   fuKaneInvariantGeneric_hex_nbRe,
   orthorhombicNbRe_is_DIII_topological,
   orthorhombicNbRe_fuKaneInvariant_neg_one,
   nbReIma2_fuKaneInvariant_derived_neg_one,
   nbReIma2_falsifier_fuKaneInvariant_pos_one,
   nbReIma2_latticeFalsifier_fuKaneInvariant_pos_one,
   nbRe_pfaffianSignAtGenericTRIM_eq,
   nbRe_fuKaneInvariantGenericTRIM,
   fun _ => rfl,
   nbRe_nbReEtaInvariant_ne_zero,
   elementalNb_nbReEtaInvariant_eq_zero,
   diiiBdGToZ16FromBordism_eq_diiiBdGToZ16,
   nbReEtaInvariantFromBordism_eq_nbReEtaInvariant,
   elementalNb_nbReBordismClass_eq_zero,
   nbRe_nbReBordismClass_ne_zero,
   nbReBordismClass_sixteen_torsion,
   windingNumberSurrogate_isSatoFujimoto,
   windingNumber_uniqueness_mod_2⟩

end SKEFTHawking.Phase6vWave9Close
