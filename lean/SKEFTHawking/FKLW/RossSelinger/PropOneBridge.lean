/-
Copyright (c) 2026 John Roehm. All rights reserved.

# Phase 6x Tier-2 Item F (M4) — the gde-value bridge (KMM Prop 1, mod-`8` form)

`KMMLemma3.lean` proves KMM Lemma 3 over the residue ring `ℤ[ω]/(2³)` using the
residue-level `Coord4.gde` (`= min 4 (2·min(v₂P, v₂Q) + [v₂P > v₂Q])`, read off the
coordinates `mod 8`). To *apply* Lemma 3 to genuine `ZOmega` elements we need the
**gde-value bridge**: the residue gde equals the true `√2`-gde of the squared
modulus (capped at `4`),

  `KMM.Coord4.gde (coordOf x) = gdePeel (normSq x) 4`.

This is the mod-`8` form of **KMM Proposition 1** (arXiv:1206.5236 p. 12): for a
real element `A + √2·B`, `gde = 2·min(v₂A, v₂B) + [v₂A > v₂B]`, and — capped at
`4` — that value is determined by `(A, B) mod 8`.

## Proof architecture (validated 0-mismatch by `scripts/kmm_zomega_reference_oracle.py`)

  1. `gdePeel (normSq x) 4 = peelN (normSq x).d (normSq x).c 4`
     (`gdePeel_real_eq_peelN`, since `|x|²` is real — `PropOne.lean`).
  2. `peelN A B 4` is **periodic mod `8`** in each argument
     (`peelN_four_periodic`): the fuel-`4` peel reads only `A, B mod 4 ⊆ mod 8`.
  3. On the `64` integer representatives `{0,…,7}²`, `peelN a b 4` agrees with the
     residue formula `gdeFromPQ (a mod 8) (b mod 8)` — a finite `decide`
     (`peelN_four_eq_gdeFromPQ_repr`).
  4. `KMM.Coord4.gde x = gdeFromPQ (Pform x) (Qform x)` (`rfl`), and
     `Pform (coordOf x) = (normSq x).d mod 8`, `Qform (coordOf x) = (normSq x).c
     mod 8` (`KMMLemma3Bridge.lean`).

Composing gives the bridge. Together with KMM Lemma 3 (`kmm_lemma3_alg2`) this lets
the residue-level reduction existence be read back as a genuine `gde(|x+ωᵏy|²)`
statement on `ZOmega` columns — the fuel-sufficiency input for the `kmmReduce`
discharge.

## Pipeline invariants

- **#10** (no `maxHeartbeats`): respected.
- **#15** (no new project-local axioms): respected. `decide` (kernel) over the
  `64` representatives; no `decide` here.

-/

import SKEFTHawking.FKLW.RossSelinger.PropOne
import SKEFTHawking.FKLW.RossSelinger.KMMLemma3Bridge
import Mathlib.Tactic.IntervalCases

set_option autoImplicit false

namespace SKEFTHawking.RossSelinger

namespace KMM.Coord4

/-- `gde(|·|², √2)` capped at `4`, computed directly from the `(P, Q)` residues
(the `Pform`/`Qform` of a `Coord4`). Definitionally `Coord4.gde x = gdeFromPQ
(Pform x) (Qform x)` (`gde_eq_gdeFromPQ`). -/
def gdeFromPQ (P Q : ZMod 8) : ℕ :=
  min 4 (2 * min (vtwo P) (vtwo Q) + (if vtwo P > vtwo Q then 1 else 0))

/-- **`Coord4.gde` factors through `(Pform, Qform)`**: it depends on a residue
only via its two quadratic-form values. -/
theorem gde_eq_gdeFromPQ (x : Coord4) : gde x = gdeFromPQ (Pform x) (Qform x) := rfl

end KMM.Coord4

namespace ZOmega

open KMM.Coord4 (gdeFromPQ vtwo)

/-- **`peelN _ _ 4` is periodic mod `8`** in each argument: a fuel-`4` peel reads
only the parities of `A, B, A/2, B/2` — i.e. `A, B mod 4 ⊆ mod 8` — so reducing
the arguments mod `8` does not change it. -/
theorem peelN_four_periodic (A B : ℤ) : peelN A B 4 = peelN (A % 8) (B % 8) 4 := by
  simp only [peelN]
  split_ifs <;> omega

/-- **Cast of an integer into `ZMod 8` factors through `mod 8`.** -/
theorem intCast_emod8 (A : ℤ) : (A : ZMod 8) = ((A % 8 : ℤ) : ZMod 8) := by
  rw [ZMod.intCast_eq_intCast_iff]
  show A % (8 : ℤ) = (A % 8) % (8 : ℤ)
  omega

/-- **The `64`-representative core of KMM Prop 1 (mod `8`)**: on `{0,…,7}²`,
`peelN a b 4` equals the residue formula `gdeFromPQ`. A finite kernel `decide`. -/
theorem peelN_four_eq_gdeFromPQ_repr (a b : ℤ)
    (ha0 : 0 ≤ a) (ha8 : a < 8) (hb0 : 0 ≤ b) (hb8 : b < 8) :
    peelN a b 4 = gdeFromPQ (a : ZMod 8) (b : ZMod 8) := by
  interval_cases a <;> interval_cases b <;> decide

/-- **KMM Prop 1 (mod-`8` form), integer version**: `peelN A B 4 = gdeFromPQ (A
mod 8) (B mod 8)` for all integers `A, B`. Reduce each argument mod `8`
(`peelN_four_periodic`, `intCast_emod8`) and apply the `64`-case core. -/
theorem peelN_four_eq_gdeFromPQ (A B : ℤ) :
    peelN A B 4 = gdeFromPQ (A : ZMod 8) (B : ZMod 8) := by
  have h := peelN_four_eq_gdeFromPQ_repr (A % 8) (B % 8)
    (Int.emod_nonneg A (by norm_num)) (Int.emod_lt_of_pos A (by norm_num))
    (Int.emod_nonneg B (by norm_num)) (Int.emod_lt_of_pos B (by norm_num))
  rw [peelN_four_periodic, h, ← intCast_emod8, ← intCast_emod8]

/-- **The gde-value bridge (KMM Proposition 1)**: the residue-level `Coord4.gde`
of a `ZOmega` element's coordinates equals the genuine `√2`-gde of its squared
modulus, capped at `4`:

  `KMM.Coord4.gde (coordOf x) = gdePeel (normSq x) 4`.

This is the connector that lets `kmm_lemma3_alg2` (stated over `Coord4.gde`) be
applied to actual `ZOmega` columns. Proof: `|x|²` is real, so its `gdePeel` is the
integer `peelN` of its `ℤ[√2]`-coordinates (`gdePeel_real_eq_peelN`); those
coordinates reduce mod `8` to `Pform`/`Qform` of `coordOf x`
(`Pform_coordOf`/`Qform_coordOf`); and `peelN _ _ 4` matches `gdeFromPQ` of the
residues (`peelN_four_eq_gdeFromPQ`). -/
theorem coord4_gde_coordOf (x : ZOmega) :
    KMM.Coord4.gde (coordOf x) = gdePeel (normSq x) 4 := by
  rw [KMM.Coord4.gde_eq_gdeFromPQ, Pform_coordOf, Qform_coordOf,
    gdePeel_real_eq_peelN (isReal_normSq x) 4, peelN_four_eq_gdeFromPQ]

end ZOmega

end SKEFTHawking.RossSelinger
