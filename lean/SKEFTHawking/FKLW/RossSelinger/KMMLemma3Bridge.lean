/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F (M4) — bridge: KMM Algorithm 2 (residues) ↔ `ZOmega`

`KMMLemma3.lean` proves KMM Lemma 3 over the residue ring `ℤ[ω]/(2³)` (`Coord4`,
the coordinates `mod 8`). To use it for the actual reduction on `ZOmega`/
`ZOmegaSqrt2` elements we must connect the residue-level `Pform`/`Qform`/`gde`
to the genuine `ZOmega.normSq` and `gdePeel`.

This file ships the **foundational ring identities** of that bridge: the residue
quadratic forms are the `mod 8` reductions of the squared-modulus coordinates,

  `Pform (coordOf x) = (normSq x).d   (mod 8)`     (the rational part of `|x|²`)
  `Qform (coordOf x) = (normSq x).c   (mod 8)`     (the `√2`-part of `|x|²`)

and the residue `ω`-action `mulOmega` is the `mod 8` reduction of `ZOmega`
multiplication by `ω`. These are pure coordinate ring identities (`simp` + `ring`
+ `push_cast`); the remaining gde-value bridge (`Coord4.gde (coordOf x) =
min 4 (gde(|x|², √2))`, via KMM Prop 1) builds on top.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected.

-/

import SKEFTHawking.FKLW.RossSelinger.KMMLemma3
import SKEFTHawking.FKLW.RossSelinger.NormSqGde

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace ZOmega

/-- The `ℤ[ω]/(2³)` residue of a `ZOmega` element: its four coordinates `mod 8`. -/
def coordOf (x : ZOmega) : KMM.Coord4 :=
  ((x.a : ZMod 8), (x.b : ZMod 8), (x.c : ZMod 8), (x.d : ZMod 8))

/-- **`normSq` constant coordinate is the `P`-form**: `(|x|²).d = a²+b²+c²+d²`. -/
theorem normSq_d (x : ZOmega) :
    (normSq x).d = x.a ^ 2 + x.b ^ 2 + x.c ^ 2 + x.d ^ 2 := by
  simp only [normSq, mul_d, conj_a, conj_b, conj_c, conj_d]; ring

/-- **`normSq` `ω`-coordinate is the `Q`-form**: `(|x|²).c = ab+bc+cd−ad`. -/
theorem normSq_c (x : ZOmega) :
    (normSq x).c = x.a * x.b + x.b * x.c + x.c * x.d - x.a * x.d := by
  simp only [normSq, mul_c, conj_a, conj_b, conj_c, conj_d]; ring

/-- **`Pform` of the residue is `(|x|²).d mod 8`.** -/
theorem Pform_coordOf (x : ZOmega) :
    KMM.Coord4.Pform (coordOf x) = ((normSq x).d : ZMod 8) := by
  rw [normSq_d, KMM.Coord4.Pform, coordOf]; push_cast; ring

/-- **`Qform` of the residue is `(|x|²).c mod 8`.** -/
theorem Qform_coordOf (x : ZOmega) :
    KMM.Coord4.Qform (coordOf x) = ((normSq x).c : ZMod 8) := by
  rw [normSq_c, KMM.Coord4.Qform, coordOf]; push_cast; ring

/-- **The residue `ω`-action is `mod 8` of `ZOmega` multiplication by `ω`**:
`coordOf (ω * x) = mulOmega (coordOf x)` — both send `⟨a,b,c,d⟩ ↦ ⟨b,c,d,−a⟩`. -/
theorem coordOf_omega_mul (x : ZOmega) :
    coordOf (ω * x) = KMM.Coord4.mulOmega (coordOf x) := by
  have ha : (ω * x).a = x.b := by simp [mul_a]
  have hb : (ω * x).b = x.c := by simp [mul_b]
  have hc : (ω * x).c = x.d := by simp [mul_c]
  have hd : (ω * x).d = -x.a := by simp [mul_d]
  simp only [coordOf, KMM.Coord4.mulOmega, ha, hb, hc, hd]
  push_cast
  rfl

end ZOmega

end SKEFTHawking.RossSelinger
