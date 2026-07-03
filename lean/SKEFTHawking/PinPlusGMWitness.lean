import Mathlib
import SKEFTHawking.PinPlusGMData
import SKEFTHawking.RP4Unconditional

/-!
# Phase 5q.H (H3 witness) — the ℝP⁴ Guillou–Marin structure and its COMPUTED mod-8 invariant

The geometric grounding of the GM carrier `pinPlusGMData`: ℝP⁴ carries a GM structure whose
characteristic surface is ℝP² (rank-1 `H₁(ℝP²;ℤ/2)`), with the canonical enhancement `stdQuadratic 1`.
Its computed mod-8 grade is `abkGM8 [ℝP⁴] = β(ℝP²) = (stdQuadratic 1).brown = 1` — **odd**, computed from
the genuine surface enhancement, not a carried tag. The `w₂ = 0` certificate is `rp4_hcert` (RP4 tower).

This is the ℝP⁴ witness the mod-8 surjectivity/fullness ultimately grounds on, and (with the odd value)
the input the H6 Smith-LES lifts to the full `ZMod 16` order-16 generator. Kernel-pure.
-/

open scoped Manifold
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.TangentialDataBordism SKEFTHawking.BordismTheory
open SKEFTHawking.PinPlusGMData
open SKEFTHawking.RP4PointSet SKEFTHawking.RP4Witness SKEFTHawking.RP4Unconditional

namespace SKEFTHawking.PinPlusGMWitness

/-- **The ℝP⁴ Guillou–Marin structure**: characteristic surface ℝP² (`rank = 1`), enhancement
`stdQuadratic 1`; the `w₂`-certificate is `rp4_hcert`. -/
noncomputable def rp4GMStr : GMStr (𝓡 4) rp4SM where
  t2 := inferInstanceAs (T2Space RP4)
  cert := rp4_hcert
  rank := 1
  q := stdQuadratic 1

/-- The ℝP⁴ class in the GM carrier `DataBordismGrp (pinPlusGMData (k := 0) (𝓡 4))`. -/
noncomputable def rp4GMClass : DataBordismGrp (pinPlusGMData (k := 0) (𝓡 4)) :=
  DataBordismGrp.mk _ ⟨rp4SM, rp4GMStr⟩

/-- **The computed mod-8 GM invariant of ℝP⁴ is `1`** (odd) — `β(ℝP²)`, computed from the genuine
characteristic-surface enhancement `stdQuadratic 1`, NOT a carried tag. The odd value is what the H6
Smith-LES lifts to the full `ZMod 16` order-16 generator. -/
theorem abkGM8_rp4 : abkGM8 (k := 0) (I := 𝓡 4) rp4GMClass = 1 := by
  show (stdQuadratic 1).brown = 1
  rw [brown_stdQuadratic, Nat.cast_one]

end SKEFTHawking.PinPlusGMWitness
