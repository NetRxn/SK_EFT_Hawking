/-
# Phase 5q.H — the sixteen boundary `S³` classes of `T⁴°` ARE ℤ-linearly dependent (unconditional)

`KummerK3OrientFromSeamKernel` reduced the `K3` orientation atom (`orientInput`'s only consumer) to a
single existential on the `Q` side:

> some nonzero `v ∈ ℤ¹⁶` has `qSeamCoord3 v = 0` — one ℤ-linear relation among the sixteen boundary
> `ℝP³` classes of `∂Q` inside `H₃(Q;ℤ)`.

This module proves the **exact mirror of that statement on the double cover**, unconditionally and
with no new geometry — only the banked `T⁴ = thickA ∪ ballsV` Mayer–Vietoris cover:

> **`exists_nonzero_seam_relation`** — some nonzero `v ∈ ℤ¹⁶` has `thickSeamCoord3 v = 0`, i.e. the
> sixteen boundary `S³` classes of `T⁴°` satisfy a nontrivial ℤ-linear relation in `H₃(T⁴°;ℤ)`.

## Route (three banked facts, no new construction)

    H₄(thickA) ⊕ H₄(ballsV) --Σ₄--> H₄(T⁴) --∂₃--> H₃(thickA ∩ ballsV) --Δ₃--> H₃(thickA) ⊕ H₃(ballsV)

* `KummerPunctureTopVanish.thickA_homology_high 4` : `H₄(thickA;ℤ) = 0`;
* `KummerPuncturedMV.ballsV_homology_eq_zero 3` : `H₄(ballsV;ℤ) = 0` (sixteen discs);
so `ker ∂₃ = im Σ₄ = 0` and **`∂₃` is injective** (`puncDelta3_injective`, §1 — a fact the
`KummerPunctureH3Saturation` module defines `puncDelta3` for but never records).
* `KummerHomologyT4Full.torusFourFundamentalClass_ne_zero` : `H₄(T⁴;ℤ) ≅ ℤ` has a nonzero element.

Hence `∂₃[T⁴] ≠ 0`, and by exactness at the seam (`KummerPunctureH3.puncInter3_exact`) it dies under
`Δ₃` — in particular under its `thickA` component. Read through the banked coordinatisation
`KummerPunctureH3.interH3EquivEIndex : H₃(thickA ∩ ballsV;ℤ) ≅ ℤ¹⁶` that is exactly one nontrivial
relation among the sixteen seam classes. Geometrically it is `Σᵢ[Sᵢ³] = ∂[T⁴]`: the sixteen boundary
spheres jointly bound the complement of the sixteen balls.

## What this does and does NOT give the `K3` residual

It gives the *whole* argument on the covering side and isolates the residual to **one transport
statement**, now the only missing link in the chain:

> the `T⁴°`-side seam coordinatisation `KummerPunctureH3.interH3EquivEIndex` and the `K3`-side seam
> coordinatisation `KummerK7MVAssembly.interH3EquivInt` are intertwined by the free `ℤ/2` covering
> `T⁴° → Q` — concretely, `p_*` carries the `S³` seam basis to (twice) the `ℝP³` seam basis.

That transport does not exist in tree in any form: there is no lemma identifying the outer face of
`annPiece c` with `chartSphere c` / `boundarySphere c`, and `KummerQuotientTransferInt`'s
`transferChainInt` has **no** naturality lemma with respect to inclusions of subspaces. This module
deliberately asserts none of it, and claims no `K3`-side conclusion. Note also that once the
transport is available, `KummerQTopVanish.h3Q_twoTorsionFree` (unconditional) upgrades the
`p_*`-image relation `2 · qSeamCoord3 v = 0` to `qSeamCoord3 v = 0` for free — so the degree-2 defect
of the covering is not an obstacle to the transport, only the seam identification is.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.KummerPunctureH3Saturation
import SKEFTHawking.KummerPunctureTopVanish
import SKEFTHawking.KummerHomologyT4Full

namespace SKEFTHawking.KummerPunctureSeamRelation

open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularFunctorialityInt (Homology.mapInt)
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularMayerVietorisLES (subIncl)
open SKEFTHawking.SingularMayerVietorisLESInt
open SKEFTHawking.KummerK3Base (TorusFour)
open SKEFTHawking.KummerWeld (EIndex)
open SKEFTHawking.KummerPunctureBalls (thickA ballsV punc_hcov)
open SKEFTHawking.KummerPunctureH3 (interH3EquivEIndex puncInter3_exact)
open SKEFTHawking.KummerPunctureH3Saturation (puncDelta3)
open SKEFTHawking.KummerHomologyT4Full (torusFourFundamentalClass
  torusFourFundamentalClass_ne_zero)

noncomputable section

/-! ## §1. The degree-3 connecting map of the puncture cover is injective -/

/-- **`∂₃ : H₄(T⁴;ℤ) → H₃(thickA ∩ ballsV;ℤ)` is INJECTIVE, unconditionally.** Its kernel is the
image of `Σ₄` (`mv_exact_ambientInt`), and both degree-4 summands of the puncture cover vanish:
`H₄(thickA;ℤ) = 0` (`KummerPunctureTopVanish.thickA_homology_high`) and `H₄(ballsV;ℤ) = 0` (sixteen
discs, `KummerPuncturedMV.ballsV_homology_eq_zero`). The `T⁴`-side counterpart of the banked
`KummerQTopVanish.k7Delta3Coord_injective`. -/
theorem puncDelta3_injective : Function.Injective puncDelta3 := by
  intro a b hab
  have h : puncDelta3 (a - b) = 0 := by rw [map_sub, hab, sub_self]
  obtain ⟨u, hu⟩ := (mv_exact_ambientInt (X := TopCat.of TorusFour) thickA ballsV 3 punc_hcov
    (a - b)).mp h
  have hu0 : u = 0 :=
    Prod.ext (SKEFTHawking.KummerPunctureTopVanish.thickA_homology_high 4 (by omega) u.1)
      (SKEFTHawking.KummerPuncturedMV.ballsV_homology_eq_zero 3 u.2)
  rw [hu0, map_zero] at hu
  exact sub_eq_zero.mp hu.symm

/-- **`∂₃[T⁴] ≠ 0`** — the seam class of the torus fundamental class is nonzero, by §1's injectivity
and `KummerHomologyT4Full.torusFourFundamentalClass_ne_zero` (`H₄(T⁴;ℤ) ≅ ℤ`). This is the one place
the argument uses that the *ambient* `T⁴` has nonvanishing top homology — i.e. is orientable. -/
theorem puncDelta3_torusFourFundamentalClass_ne_zero :
    puncDelta3 torusFourFundamentalClass ≠ 0 := by
  intro h
  exact torusFourFundamentalClass_ne_zero (puncDelta3_injective (by rw [h, map_zero]))

/-! ## §2. The seam relation, in `H₃(seam;ℤ)` -/

/-- **A nonzero seam class killed by the Mayer–Vietoris diagonal.** Exactness at the seam
(`KummerPunctureH3.puncInter3_exact`, `ker Δ₃ = im ∂₃`) plus §1's nonvanishing. -/
theorem exists_ne_zero_mem_ker_puncDiag3 :
    ∃ w : Homology (sub (X := TopCat.of TorusFour) (thickA ∩ ballsV)) 3,
      w ≠ 0 ∧ mvHomDiagInt (X := TopCat.of TorusFour) thickA ballsV 3 w = 0 :=
  ⟨puncDelta3 torusFourFundamentalClass, puncDelta3_torusFourFundamentalClass_ne_zero,
    (puncInter3_exact _).mpr ⟨torusFourFundamentalClass, rfl⟩⟩

/-! ## §3. The relation in the sixteen seam coordinates -/

/-- **The `T⁴°`-side seam map `ℤ¹⁶ → H₃(T⁴°;ℤ)`** — the sixteen boundary `S³` classes of `∂T⁴°`, read
through the banked coordinatisation `KummerPunctureH3.interH3EquivEIndex`. The exact structural
analogue of `KummerK3H3SeamWindow.qSeamCoord3` on the double cover: same shape (a seam
coordinatisation composed with the inclusion-induced map), different carrier. -/
abbrev seamToThick3 : Homology (sub (X := TopCat.of TorusFour) (thickA ∩ ballsV)) 3 →ₗ[ℤ]
    Homology (sub (X := TopCat.of TorusFour) thickA) 3 :=
  Homology.mapInt (subIncl (Set.inter_subset_left (s := thickA) (t := ballsV))) 3

/-- The seam coordinates of `T⁴°`, `ℤ¹⁶ →ₗ[ℤ] H₃(thickA;ℤ)`. -/
abbrev thickSeamCoord3 : (EIndex → ℤ) →ₗ[ℤ] Homology (sub (X := TopCat.of TorusFour) thickA) 3 :=
  seamToThick3 ∘ₗ interH3EquivEIndex.symm.toLinearMap

/-- The `thickA` component of the Mayer–Vietoris diagonal IS the inclusion-induced map. -/
theorem mvHomDiagInt_fst (w : Homology (sub (X := TopCat.of TorusFour) (thickA ∩ ballsV)) 3) :
    (mvHomDiagInt (X := TopCat.of TorusFour) thickA ballsV 3 w).1 = seamToThick3 w := rfl

/-- **THE SIXTEEN BOUNDARY `S³` CLASSES OF `T⁴°` ARE ℤ-LINEARLY DEPENDENT — UNCONDITIONALLY.**

There is a nonzero integer vector `v ∈ ℤ¹⁶` with `thickSeamCoord3 v = 0`. Geometrically: the sixteen
`S³` boundary components of the punctured torus jointly bound (their sum is `∂[T⁴]`), so they cannot
be independent in `H₃(T⁴°;ℤ)`.

This is the covering-side mirror of the single remaining `K3` residual
(`KummerK3OrientFromSeamKernel.nonempty_intOrientation_of_seam_relation`'s hypothesis), proved here
with nothing but the banked puncture cover. -/
theorem exists_nonzero_seam_relation : ∃ v : EIndex → ℤ, v ≠ 0 ∧ thickSeamCoord3 v = 0 := by
  obtain ⟨w, hw0, hwker⟩ := exists_ne_zero_mem_ker_puncDiag3
  refine ⟨interH3EquivEIndex w,
    fun hv => hw0 ((LinearEquiv.map_eq_zero_iff interH3EquivEIndex).mp hv), ?_⟩
  · show seamToThick3 (interH3EquivEIndex.symm (interH3EquivEIndex w)) = 0
    rw [interH3EquivEIndex.symm_apply_apply, ← mvHomDiagInt_fst, hwker]
    exact Prod.fst_zero

/-- **`ker thickSeamCoord3 ≠ ⊥`** — the submodule phrasing of the headline, matching the shape of the
`K3`-side hypothesis `LinearMap.ker qSeamCoord3 ≠ ⊥` that
`KummerK3OrientFromSeamKernel.nonempty_intOrientation_of_ker_ne_bot` consumes. -/
theorem ker_thickSeamCoord3_ne_bot : LinearMap.ker thickSeamCoord3 ≠ ⊥ := by
  obtain ⟨v, hv, h0⟩ := exists_nonzero_seam_relation
  intro hbot
  refine hv ?_
  have hmem : v ∈ LinearMap.ker thickSeamCoord3 := LinearMap.mem_ker.mpr h0
  rw [hbot, Submodule.mem_bot] at hmem
  exact hmem

end

end SKEFTHawking.KummerPunctureSeamRelation
