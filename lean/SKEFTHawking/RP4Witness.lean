import Mathlib
import SKEFTHawking.RP4PointSet
import SKEFTHawking.PinPlusTiedData

/-!
# Phase 5q.G (B-arc, B4d-0) — the `ℝP⁴` witness bundle and THE REDUCTION

`RP4` (B4a–B4b) assembles into a `C⁰` singular manifold `rp4SM : SingularManifold PUnit 0 (𝓡 4)`
— the `IsManifold (𝓡 4) 0` and `BoundarylessManifold` instances fire automatically from the
charted structure (the `k`-generalization B4c making `k = 0` admissible). On it, the grade-`1`
tied structure exists **given exactly two singular-cohomology computations on `ℝP⁴`**:

* `hcert : PinPlusCertK (𝓡 4) rp4SM` — the admissibility `wuW2(ℝP⁴) = 0` (B4d-1);
* `htie : swNumberW14 RP4 = 1` — the Stiefel–Whitney number `w₁⁴[ℝP⁴] = 1` (B4d-2).

`dataBordismTied_equiv_zmod16_of_rp4` is **the reduction**: the tied carrier's full `ℤ/16`
from those two computations — the entire residual geometry of the B-checkpoint, isolated.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.RP4PointSet SKEFTHawking.PinPlusTiedData SKEFTHawking.SingularSWNumber
open scoped Manifold

namespace SKEFTHawking.RP4Witness

/-- The charted instance re-keyed at the `Fin (2 + 2)` spelling the Wu tower uses (defeq to the
`Fin 4` instance; instance search is syntactic on the model key). -/
noncomputable instance : ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) RP4 :=
  inferInstanceAs (ChartedSpace (EuclideanSpace ℝ (Fin 4)) RP4)

/-- **`ℝP⁴` as a `C⁰` singular manifold over `PUnit`** — the tied datum's witness carrier. -/
noncomputable def rp4SM : SingularManifold PUnit 0 (𝓡 4) where
  M := RP4
  f := fun _ => PUnit.unit
  hf := continuous_const

/-- The grade-`1` tied structure on `ℝP⁴`, given the two cohomology computations. -/
noncomputable def rp4TiedStr (hcert : PinPlusCertK (𝓡 4) rp4SM)
    (htie : swNumberW14 RP4 = 1) : TiedStr (𝓡 4) rp4SM where
  grade := ((1 : ZMod 16), 0)
  t2 := inferInstanceAs (T2Space RP4)
  cert := hcert
  tie := by
    rw [swTotalNe, dif_pos (inferInstanceAs (Nonempty RP4))]
    show reduce16to2 (1 : ZMod 16) = swNumberW14 RP4
    rw [htie]
    decide

/-- The witness class has an odd grade. -/
theorem rp4Witness_odd (hcert : PinPlusCertK (𝓡 4) rp4SM) (htie : swNumberW14 RP4 = 1) :
    reduce16to2 (abkTiedGrade (I := 𝓡 4) (k := 0)
      (SKEFTHawking.TangentialDataBordism.DataBordismGrp.mk _
        ⟨rp4SM, rp4TiedStr hcert htie⟩)) = 1 := by
  show reduce16to2 (1 : ZMod 16) = 1
  decide

/-- **THE REDUCTION — the tied `ℤ/16` from two `ℝP⁴` computations**: given `wuW2(ℝP⁴) = 0`
(admissibility) and `w₁⁴[ℝP⁴] = 1` (the tie), the parity-tied Pin⁺ carrier's ABK quotient is
the whole `ZMod 16`. The residual geometry of the B-checkpoint, reduced to two singular
cohomology facts about one manifold. -/
noncomputable def dataBordismTied_equiv_zmod16_of_rp4
    (hcert : PinPlusCertK (𝓡 4) rp4SM) (htie : swNumberW14 RP4 = 1) :
    (SKEFTHawking.TangentialDataBordism.DataBordismGrp (pinPlusTiedData (k := 0) (𝓡 4)) ⧸
      ((abkTiedGrade (I := 𝓡 4) (k := 0)) :
        SKEFTHawking.TangentialDataBordism.DataBordismGrp (pinPlusTiedData (k := 0) (𝓡 4))
          →+ ZMod 16).ker) ≃+ ZMod 16 :=
  dataBordismTied_quotient_equiv_zmod16_of_odd
    ⟨SKEFTHawking.TangentialDataBordism.DataBordismGrp.mk _ ⟨rp4SM, rp4TiedStr hcert htie⟩,
      rp4Witness_odd hcert htie⟩

end SKEFTHawking.RP4Witness
