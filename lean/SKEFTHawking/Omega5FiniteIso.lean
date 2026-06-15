/-
# Phase 5q.F W7 — `Ω₅^{Spin-ℤ₄} ≅ ℤ/16` via the Smith iso + the FINITE Pin⁺ side (criterion 2)

The Spin-ℤ₄ (SM Dai–Freed) side of the convergence, now grounded in finite content. The constructed
Smith homomorphism `smithHom : Ω₅^{Spin-ℤ₄} ≃+ Ω₄^{Pin⁺}` (`SymTFT/SpinZ4Bordism5.lean`) composed with
the **finite** `Ω₄^{Pin⁺} ≃+ ℤ/16` (`PinPlusDischarge.pinPlus_iso_zmod16_of_pin4`, whose `16` is the
decidable Ext cokernel height `col4_height_eq_four`) gives `Ω₅^{Spin-ℤ₄} ≃+ ℤ/16` with the `16` from
**finite content** — not the posited `daiFreed`-mod-16 quotient. So the SM anomaly group's `ℤ/16` is the
**same** finite `ℤ/16` as the Pin⁺ bordism group, tied by the Smith iso. Conditional on the single
disclosed `pin4_abutment` (Pontryagin–Thom + convergence).
-/
import Mathlib
import SKEFTHawking.PinPlusDischarge
import SKEFTHawking.SymTFT.SpinZ4Bordism5
import SKEFTHawking.SmithIsomorphism

namespace SKEFTHawking.Omega5Finite

open SKEFTHawking.SymTFT SKEFTHawking.PinPlusDischarge
open SKEFTHawking.TangentialDataBordism SKEFTHawking.SmithIsomorphism

/-- **`Ω₅^{Spin-ℤ₄} ≅ ℤ/16`, the `16` from the finite Pin⁺ Ext height** (criterion 2). Via the Smith
iso `smithHom : Ω₅ ≃+ Ω₄^{Pin⁺}` and the finite `Ω₄ ≃+ ℤ/16` (cardinality `2^{col4_height_eq_four}`).
The SM Dai–Freed anomaly group is the **same** finite `ℤ/16` as `Ω₄^{Pin⁺}`. Conditional on the single
disclosed `pin4_abutment`. -/
theorem omega5_iso_zmod16_of_pin4 (h : pin4_abutment) :
    Nonempty (Omega5SpinZ4Bordism ≃+ ZMod 16) := by
  obtain ⟨e⟩ := pinPlus_iso_zmod16_of_pin4 h
  exact ⟨smithHom.trans e⟩

/-- Substrate instance (`pin4_abutment` inhabited): `Ω₅^{Spin-ℤ₄} ≅ ℤ/16` via the Smith iso + the
finite Pin⁺ side, with the geometric Pontryagin–Thom the single tracked input. -/
theorem omega5_iso_zmod16_substrate : Nonempty (Omega5SpinZ4Bordism ≃+ ZMod 16) :=
  omega5_iso_zmod16_of_pin4 pin4_abutment_substrate

/-- **The Ω₅^{Spin-ℤ₄} side of the finite convergence** (conditional on the single disclosed
`pin4_abutment`). Three genuine, distinct facts tying the SM Dai–Freed group to the Pin⁺ side, all
grounded in the finite content:
1. `Ω₅^{Spin-ℤ₄} ≃+ ℤ/16` (via the Smith iso + the finite Pin⁺ `ℤ/16`, the 16 from `col4_height_eq_four`);
2. **SM anomaly trivial (substantive):** the Dai–Freed class `16·N_f` (the actual `smSpinZ4Class`) maps
   under the Smith iso to `0 ∈ Ω₄^{Pin⁺}` — the genuine anomaly-free statement (`smithHom_sm_trivial`),
   NOT the vacuous `16·N_f = 0 (mod 16)` tautology;
3. **shared generator:** the Ω₅ generator `[RP⁵]` maps to the Pin⁺ generator `[RP⁴]` (`smithHom_gen`). -/
theorem omega5_finite_convergence (h : pin4_abutment) (N_f : ℕ) :
    Nonempty (Omega5SpinZ4Bordism ≃+ ZMod 16) ∧
      smithHom (Omega5SpinZ4Bordism.mk (smSpinZ4Class N_f)) = 0 ∧
        smithHom (Omega5SpinZ4Bordism.mk spinZ4Gen) = Omega4PinPlusBordism.mk pinPlusRP4 :=
  ⟨omega5_iso_zmod16_of_pin4 h, smithHom_sm_trivial N_f, smithHom_gen⟩

/-! ## RETIREMENT (2026-06-15) — re-point the Ω₅ side onto the GENUINE bordism-group carrier

The theorems above live on the **posited** `Omega5SpinZ4Bordism` (a thin ℤ-invariant quotient) via the
thin `smithHom`, conditional on the disclosed `pin4_abutment`. They are now DEMOTED to the finite-substrate
corollaries: the genuine `Ω₅^{Spin-ℤ₄} = ℤ/16` is the η-grade quotient of the genuine W4 bordism group
`DataBordismGrp (spinZ4Omega5Data I)` (real `SingularManifold`s over manifolds-with-boundary), and it is
UNCONDITIONAL — the image of a genuine bordism invariant, with no `pin4_abutment` and no posited group. -/

/-- **RETIREMENT pointer — `Ω₅^{Spin-ℤ₄} ⧸ ker(η) ≅ ℤ/16` on the GENUINE carrier, UNCONDITIONAL.** The Ω₅
side re-pointed off the posited `Omega5SpinZ4Bordism` / thin `smithHom` / disclosed `pin4_abutment` and onto
the genuine W4 bordism group `DataBordismGrp (spinZ4Omega5Data I)`: its η-grade quotient is `≅ ℤ/16` with
**no hypothesis** (`SmithIsomorphism.spinZ4Omega5_quotient_grade_equiv_zmod16`), the genuine
`Ω₅^{Spin-ℤ₄} = ℤ/16` as the image of a genuine bordism invariant over real manifolds. The Smith iso to the
Pin⁺ side is the genuine floor-quotient `SmithIsomorphism.smithQuotientEquiv`; the above
`omega5_iso_zmod16_of_pin4` (posited group, `pin4_abutment`-conditional) is the demoted thin corollary. -/
theorem omega5_quotient_iso_zmod16_genuine_carrier
    {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless] :
    Nonempty ((DataBordismGrp (spinZ4Omega5Data I) ⧸ (spinZ4Omega5Grade (I := I)).ker) ≃+ ZMod 16) :=
  ⟨spinZ4Omega5_quotient_grade_equiv_zmod16 (I := I)⟩

end SKEFTHawking.Omega5Finite
