/-
# Phase 5q.H close-out GATE ROUND 13 (fresh-context attack on the post-round-12 shape frontier)

[HEADER TO BE FINALIZED ON COMPLETION — verdicts, specs, fork proposals]
-/
import Mathlib
import SKEFTHawking.PinPlusResidualGate
import SKEFTHawking.PinPlusKTNovikovTowerInstantiate
import SKEFTHawking.PinPlusTraceSeamResidualNarrow
import SKEFTHawking.PinPlusKTCollapseDischarge

open scoped Manifold
open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.T2TangentialBordism SKEFTHawking.TangentialDataBordism
open SKEFTHawking.BordismTheory
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.PinPlusKTKernelSector
open SKEFTHawking.PinPlusKTSpinSigmaNovikovRealSubstrate
open SKEFTHawking.PinPlusKTNovikovTowerInstantiate
open SKEFTHawking.SingularRelativeRealBaseChange
open SKEFTHawking.PinPlusResidualGate
open SKEFTHawking.PinPlusKTSectorGeometricReduce
open SKEFTHawking.PinPlusKTCollapseDischarge

namespace SKEFTHawking.PinPlusRoundThirteenGate

/-! ## §1. G13-1 — the Novikov "genuine-tower" carrier is conclusion-fakeable: the field row of
`NovikovGeometricPairLESData` sits at EXACTLY substrate (= σ-agreement = `hbord`) strength. -/

/-- **THE ROUND-13 REVERSE MAP** — the substrate rebuilds the "genuine-tower" carrier: from any
`NovikovRealPairLES Bd` (in particular a SYNTHETIC one — `ofLagrangian`'s quotient fabrication) and
the symmetry of `Bd`, all nine fields of `NovikovGeometricPairLESData Bd` are inhabited with ZERO
new geometry: the same `H2W`/`H3rel`/`rest2`/`delta`, `pairing := ½·pairing` (un-absorbing the
polarization factor), and `hadjDot` DERIVED from the substrate's `hadj` via
`polarBilin_toQuadraticMap'_isSymm`. Composed with `ofLagrangian`, the carrier is populated from a
bare half-dimensional isotropic subspace — no bordism `W`, no pair-LES tower. -/
noncomputable def novikovGeometricPairLESDataOfRealPairLES {n : ℕ}
    {Bd : Matrix (Fin n) (Fin n) ℤ} (hsymm : Bd.IsSymm) (N : NovikovRealPairLES Bd) :
    NovikovGeometricPairLESData Bd where
  H2W := N.H2W
  H3rel := N.H3rel
  rest2 := N.rest2
  delta := N.delta
  pairing := (2⁻¹ : ℝ) • N.pairing
  hexact := N.hexact
  hnondeg := fun x hx => N.hnondeg x fun a => by
    have h := hx a
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left (by norm_num)
  hbdnd := N.hbdnd
  hsymm := hsymm
  hadjDot := fun a v => by
    have h := N.hadj a v
    rw [polarBilin_toQuadraticMap'_isSymm _ (hsymm.map _)] at h
    rw [LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul, ← h]
    ring

/-- **The carrier and the substrate are inhabitation-EQUIVALENT** (for symmetric `Bd`): forward is
the banked honest reduction `ofGeometricPairLESData`; backward is the round-13 reverse map. The
carrier's field row therefore adds ZERO statement strength over `NovikovRealPairLES`. -/
theorem nonempty_novikovGeometricPairLESData_iff_realPairLES {n : ℕ}
    {Bd : Matrix (Fin n) (Fin n) ℤ} (hsymm : Bd.IsSymm) :
    Nonempty (NovikovGeometricPairLESData Bd) ↔ Nonempty (NovikovRealPairLES Bd) :=
  ⟨fun ⟨D⟩ => ⟨NovikovRealPairLES.ofGeometricPairLESData D⟩,
   fun ⟨N⟩ => ⟨novikovGeometricPairLESDataOfRealPairLES hsymm N⟩⟩

/-- **THE ROUND-13 σ-TIE (headline)** — at a boundary block pair the "genuine-tower" carrier is
inhabited EXACTLY when the signatures agree: `Nonempty (NovikovGeometricPairLESData
(blockDiag A (−B))) ↔ σ(A) = σ(B)`. Forward is the banked `latticeSig_eq` consumer (#196 §5);
backward is the round-12 Witt step (`exists_lagrangian_of_latticeSig_eq_zero`) feeding the synthetic
`ofLagrangian` substrate through the round-13 reverse map — ZERO bordism geometry. Consequence: the
`hadjDot`/`hexact`/`hnondeg` field row does NOT force genuine tower data; a "carrier populated"
claim is fork-20-compliant progress ONLY if `rest2`/`delta`/`pairing` are the ⊗ℝ base-changes of an
actual bounding `W`'s pair-LES maps, checked by DATA INSPECTION — the statement shape can never
enforce it (round-13 spec 1). -/
theorem nonempty_novikovGeometricPairLESData_iff_sig_eq {r s : ℕ}
    (A : Matrix (Fin r) (Fin r) ℤ) (B : Matrix (Fin s) (Fin s) ℤ)
    (hA : IsEvenUnimodular A) (hB : IsEvenUnimodular B) :
    Nonempty (NovikovGeometricPairLESData (blockDiag A (-B)))
      ↔ latticeSig A = latticeSig B := by
  constructor
  · rintro ⟨D⟩
    exact NovikovGeometricPairLESData.latticeSig_eq A B hA hB D
  · intro hsig
    have hnegB := isEvenUnimodular_neg _ hB
    have hbd_eu := isEvenUnimodular_blockDiag A (-B) hA hnegB
    have hsymmZ : (blockDiag A (-B)).IsSymm := hbd_eu.1
    have hsig0 : latticeSig (blockDiag A (-B)) = 0 := by
      rw [latticeSig_blockDiag A (-B) hA hnegB, latticeSig_neg]
      omega
    obtain ⟨L, hdim, hiso⟩ :=
      exists_lagrangian_of_latticeSig_eq_zero _ hbd_eu.radical_eq_bot hsig0
    exact ⟨novikovGeometricPairLESDataOfRealPairLES hsymmZ
      (NovikovRealPairLES.ofLagrangian _ hbd_eu.radical_eq_bot L hdim hiso)⟩

/-- **The soundness half survives** (the PASS component of the verdict): the carrier still FORCES
σ-agreement — it is empty across σ-grades, so no degenerate population can launder a σ-jump. The
carrier is a genuine constraint; it is just not MORE than the σ-agreement conclusion. -/
theorem isEmpty_novikovGeometricPairLESData_of_sig_ne {r s : ℕ}
    (A : Matrix (Fin r) (Fin r) ℤ) (B : Matrix (Fin s) (Fin s) ℤ)
    (hA : IsEvenUnimodular A) (hB : IsEvenUnimodular B)
    (hne : latticeSig A ≠ latticeSig B) :
    IsEmpty (NovikovGeometricPairLESData (blockDiag A (-B))) :=
  ⟨fun D => hne (NovikovGeometricPairLESData.latticeSig_eq A B hA hB D)⟩

/-- **The diagonal degenerate model reaches the carrier** — at any matrix-equal pair the
"genuine-tower" carrier is inhabited with zero geometry (the round-12 diagonal exhibit, lifted
through the reverse map). The sharpest per-pair form of the fake. -/
theorem nonempty_novikovGeometricPairLESData_diag {r : ℕ} (A : Matrix (Fin r) (Fin r) ℤ)
    (heu : IsEvenUnimodular A) :
    Nonempty (NovikovGeometricPairLESData (blockDiag A (-A))) :=
  (nonempty_novikovGeometricPairLESData_iff_sig_eq A A heu heu).mpr rfl

/-! ## §4. G13-3 — the rank-0 collapse datum sits at EXACTLY per-object conclusion strength. -/

section CollapseDatum

variable {prov : CharPairWProviderPerOp (𝓡 4) 0}

/-- **The collapse datum is the Skolemized per-object conclusion** — `Nonempty (RankZeroCollapseDatum
prov p)` is EQUIVALENT to the collapse Prop's body at `p`. Forward: project the datum's fields.
Backward: repackage the `IsT2DataBordant` witness. The datum's field row (`hemp`/`b`/`hT2`/`hBor`)
adds NAMING and per-field inspectability, but ZERO statement strength: nothing in the shape pins `b`
to the genuine membrane-kill trace. (`target_spinSector` is DERIVED from `hemp`, not an independent
anti-laundering conjunct.) A datum-supply discharge is therefore audited by DATA INSPECTION — the
round-9 freeze / round-12 spec 4 obligation transfers verbatim to the datum (round-13 spec 3). -/
theorem nonempty_rankZeroCollapseDatum_iff
    (p : StrMfd (pinPlusCharPairData prov).toTangentialData) :
    Nonempty (RankZeroCollapseDatum prov p) ↔
      ∃ p' : StrMfd (pinPlusCharPairData prov).toTangentialData,
        IsEmpty p'.2.surf.M ∧ IsT2DataBordant (pinPlusCharPairData prov) p p' := by
  constructor
  · rintro ⟨d⟩
    exact ⟨d.p', d.hemp, d.isT2DataBordant⟩
  · rintro ⟨p', hemp, b, hT2, hBor⟩
    exact ⟨⟨p', hemp, b, hT2, hBor⟩⟩

/-- **The ∀-datum supply is EXACTLY the collapse atom** — `RankZeroCollapsesToEmptySurf prov ↔
(∀ rank-0 p, Nonempty (RankZeroCollapseDatum prov p))`. The #199 reduction
(`rankZeroCollapsesToEmptySurf_of_datumSupply`) is therefore an honest RENAMING of the dC overhang,
not a strengthening or weakening — the locating theorem the consumption spec hangs on. -/
theorem rankZeroCollapsesToEmptySurf_iff_datumSupply :
    RankZeroCollapsesToEmptySurf prov ↔
      ∀ p : StrMfd (pinPlusCharPairData prov).toTangentialData,
        IsSpinSectorStr prov p → Nonempty (RankZeroCollapseDatum prov p) := by
  constructor
  · intro h p hp
    exact (nonempty_rankZeroCollapseDatum_iff p).mpr (h p hp)
  · intro H p hp
    exact (nonempty_rankZeroCollapseDatum_iff p).mp (H p hp)

end CollapseDatum

end SKEFTHawking.PinPlusRoundThirteenGate
