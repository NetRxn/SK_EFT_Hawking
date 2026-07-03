import Mathlib
import SKEFTHawking.PinPlusFaithfulData
import SKEFTHawking.SmithIsomorphism

/-!
# Phase 5q.G (G5) — the sixteen-convergence capstone on the FAITHFUL carriers, binder-free

The common-origin bundle recast with **no `SmithInflow`, no `pin4_abutment`, no
`PinPlusBordismLandmark` binder, and no `Omega4PinPlusBordism`/`adamsAbutment` carrier**:

* the Pin⁺ `ℤ/16` — the unconditional ABK quotient of the **faithful** (w₂-certified) carrier;
* the `Ω₅^{Spin-ℤ₄}` `ℤ/16` — the unconditional η-grade quotient of the genuine W4 carrier;
* the **Smith sandwich** between the two genuine quotients (`smithFaithfulQuotientEquiv`);
* the SM Dai–Freed anomaly facet — `16·N_f`-graded classes die in the faithful quotient;
* the Guillou–Marin relation — supplied by the **genuine** `β(ℝP²) = 1` Gauss-sum;
* the generator's full order 16 — derived from the odd-bit lemma, no posited `signature = 1`.

**Scope caveat (self-contained hedging):** `faithfulGenerator` is carried by the vacuously
certified EMPTY manifold — its order 16 is an algebraic fact about a grade-1 class pulled back
through the ABK surjection, and the geometric identification with `[ℝP⁴]` is Landmark-level
content, NOT proven here (see `PinPlusFaithfulData` §4).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.TangentialDataBordism SKEFTHawking.BordismTheory
open SKEFTHawking.PinPlusFaithfulData SKEFTHawking.SmithIsomorphism

namespace SKEFTHawking.FaithfulSixteenCapstone

universe u

variable {E H : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
  {E₄ : Type} [NormedAddCommGroup E₄] [NormedSpace ℝ E₄] [FiniteDimensional ℝ E₄]
  (I₄ : ModelWithCorners ℝ E₄ (EuclideanSpace ℝ (Fin (2 + 2)))) [I₄.Boundaryless]

/-- **The Smith sandwich onto the FAITHFUL Pin⁺ carrier**: the genuine `Ω₅^{Spin-ℤ₄}` η-grade
quotient is isomorphic to the faithful Pin⁺ ABK quotient — both are `ℤ/16` by their unconditional
grade-quotient isos. Binder-free. -/
noncomputable def smithFaithfulQuotientEquiv :
    (DataBordismGrp.{u} (spinZ4Omega5Data I) ⧸ (spinZ4Omega5Grade (I := I)).ker) ≃+
      (DataBordismGrp.{u} (pinPlusFaithfulData I₄) ⧸ (abkFaithfulGrade (I := I₄)).ker) :=
  (spinZ4Omega5_quotient_grade_equiv_zmod16.{u} (I := I)).trans
    (dataBordismFaithful_quotient_abk_equiv_zmod16 (I := I₄)).symm

/-- The faithful Smith sandwich, read into `ZMod 16` on the Pin⁺ side, is the source η-grade
quotient iso — the identity on `ℤ/16` through the two quotient identifications. -/
theorem smithFaithfulQuotientEquiv_eq_zmod16
    (x : DataBordismGrp.{u} (spinZ4Omega5Data I) ⧸ (spinZ4Omega5Grade (I := I)).ker) :
    dataBordismFaithful_quotient_abk_equiv_zmod16 (I := I₄)
        (smithFaithfulQuotientEquiv I₄ x)
      = spinZ4Omega5_quotient_grade_equiv_zmod16.{u} (I := I) x := by
  show dataBordismFaithful_quotient_abk_equiv_zmod16 (I := I₄)
      ((dataBordismFaithful_quotient_abk_equiv_zmod16 (I := I₄)).symm
        (spinZ4Omega5_quotient_grade_equiv_zmod16 (I := I) x)) = _
  rw [AddEquiv.apply_symm_apply]

/-- **The SM Dai–Freed anomaly facet on the faithful carrier**: any `16·N_f`-multiple of the
faithful generator is killed by the ABK grade — the anomaly-free statement, with no posited
carrier. -/
theorem sm_anomaly_faithful (N_f : ℕ) :
    abkFaithfulGrade ((16 * N_f) • faithfulGenerator (I := I₄)) = 0 := by
  rw [map_nsmul, abkFaithfulGrade_faithfulGenerator, nsmul_eq_mul, mul_one]
  rw [show ((16 * N_f : ℕ) : ZMod 16) = (16 : ZMod 16) * (N_f : ℕ) from by push_cast; ring,
    show (16 : ZMod 16) = 0 from by decide, zero_mul]

/-- **G5 — the sixteen-convergence capstone on the FAITHFUL carriers.** All facets bundled with
NO `SmithInflow` / `pin4_abutment` / `PinPlusBordismLandmark` binder and no posited carrier:

1. the Pin⁺ `ℤ/16` — the unconditional faithful ABK quotient;
2. the `Ω₅` `ℤ/16` — the unconditional genuine η-grade quotient;
3. the SM anomaly facet — `16·N_f`-graded classes are grade-trivial;
4. the Guillou–Marin relation for the generator — the genuine `β(ℝP²)`;
5. the generator's exact order 16 — derived, not posited (the generator carried by ∅;
   the `[ℝP⁴]`-identification is Landmark-level, not proven here). -/
theorem sixteen_convergence_faithful_carrier (N_f : ℕ) :
    Nonempty ((DataBordismGrp.{u} (pinPlusFaithfulData I₄) ⧸ (abkFaithfulGrade (I := I₄)).ker)
        ≃+ ZMod 16) ∧
      Nonempty ((DataBordismGrp.{u} (spinZ4Omega5Data I) ⧸ (spinZ4Omega5Grade (I := I)).ker)
        ≃+ ZMod 16) ∧
      abkFaithfulGrade ((16 * N_f) • faithfulGenerator (I := I₄)) = 0 ∧
      SKEFTHawking.GuillouMarin.reduce16to8 (abkFaithfulGrade (faithfulGenerator (I := I₄)))
        = (SKEFTHawking.Brown.Z4Quadratic.stdQuadratic 1).brown ∧
      (∀ k : ℕ, 0 < k → k < 16 → (k : ℕ) • (faithfulGenerator (I := I₄)) ≠ 0) :=
  ⟨⟨dataBordismFaithful_quotient_abk_equiv_zmod16 (I := I₄)⟩,
    ⟨spinZ4Omega5_quotient_grade_equiv_zmod16.{u} (I := I)⟩,
    sm_anomaly_faithful I₄ N_f,
    faithfulGenerator_hGM,
    faithfulGenerator_order16⟩

end SKEFTHawking.FaithfulSixteenCapstone
