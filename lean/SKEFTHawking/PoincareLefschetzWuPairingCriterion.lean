/-
# Phase 5q.H (W-A arm 4) — the pairing-perfection CRITERIA for the Poincaré–Lefschetz Wu datum

The `nondeg` field of `PoincareLefschetzWu5.LefschetzWuDatum` is the **left non-degeneracy** of the
Lefschetz pairing `B := cup.compr₂ μ : H^k(W) →ₗ H^{nk}(W,∂W) →ₗ ℤ/2`, i.e. injectivity of the induced
map `H^k(W) → (H^{nk}(W,∂W))*`, `a ↦ (b ↦ μ(a ∪ b))`. This module supplies the two route-independent
CRITERIA for discharging such an injectivity — pure finite-dimensional linear algebra over a field,
reusable for ANY project pairing of this `compr₂` shape:

* **§1 — the adjoint (transpose) criterion.** `injective_iff_flip_injective`: for a bilinear pairing
  `B : V →ₗ W →ₗ F` between finite-dimensional `F`-spaces with `dim V = dim W`, the LEFT map `B` is
  injective **iff** the RIGHT map `B.flip` is injective. (`B.flip = B.dualMap ∘ eval`, `eval` is an iso
  in finite dimension, `dualMap` injective ⟺ `B` surjective ⟺ — equal finrank — `B` injective.) This is
  the honest content of "perfect ⟺ the induced map to the dual is bijective ⟺ injective in equal
  finrank": the dimension side (`dim V = dim W`) is the DONE input (the pair-suspension Betti count),
  and the criterion converts left↔right non-degeneracy freely. It does NOT manufacture non-degeneracy
  from nothing — it transports it between the two sides.

* **§2 — the iso-transport criterion.** `injective_of_pairing_congr`: if a pairing `B` is intertwined
  with a base pairing `B'` through linear equivalences on both arguments
  (`B a b = B' (α a) (β b)`), then `B` inherits `B'`'s left non-degeneracy. This is the route that
  reduces a compound pairing's perfectness to a KNOWN base pairing's perfectness — the mechanism a
  Poincaré–Lefschetz cylinder pairing uses to inherit its base manifold's Poincaré-duality pairing
  perfectness, once the intertwining (α, β, compatibility) is available.

Both criteria are stated generically (any field, any finite-dimensional spaces) and specialised to a
`LefschetzWuDatum`'s pairing at the end. Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`, no new project axiom, no `native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzWu5

namespace SKEFTHawking.PoincareLefschetzWuPairingCriterion

open SKEFTHawking.PoincareLefschetzWu5

/-! ## §1. The adjoint (transpose) criterion — left ⟺ right non-degeneracy at equal finrank -/

section Adjoint

variable {F V W : Type*} [Field F] [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]

/-- The right (flipped) map of a pairing factors through the transpose: `B.flip = B.dualMap ∘ eval`.
For `w : W`, `B.flip w = (v ↦ B v w)` and `B.dualMap (eval w) = eval w ∘ B = (v ↦ (B v) w)`. -/
theorem flip_eq_dualMap_comp_eval (B : V →ₗ[F] W →ₗ[F] F) :
    B.flip = B.dualMap.comp (Module.Dual.eval F W) := by
  ext w v
  rfl

variable [FiniteDimensional F V] [FiniteDimensional F W]

/-- One direction of the adjoint criterion: if the LEFT map `B` is injective and `dim V = dim W`, the
RIGHT (flipped) map `B.flip` is injective. Chain: `B` injective → (equal finrank) surjective →
`B.dualMap` injective (`dualMap_injective_iff`) → `B.flip = B.dualMap ∘ eval` injective (`eval` is
injective over a field). -/
theorem flip_injective_of_injective (B : V →ₗ[F] W →ₗ[F] F)
    (hdim : Module.finrank F V = Module.finrank F W) (hB : Function.Injective ⇑B) :
    Function.Injective ⇑B.flip := by
  have hdimVW' : Module.finrank F V = Module.finrank F (Module.Dual F W) := by
    rw [hdim, Subspace.dual_finrank_eq]
  have hsurj : Function.Surjective ⇑B :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank hdimVW').mp hB
  have hdual : Function.Injective ⇑B.dualMap := LinearMap.dualMap_injective_iff.mpr hsurj
  rw [flip_eq_dualMap_comp_eval, LinearMap.coe_comp]
  exact hdual.comp (Module.eval_apply_injective F (V := W))

/-- **The adjoint criterion.** For a bilinear pairing `B : V →ₗ W →ₗ F` between finite-dimensional
`F`-spaces of EQUAL dimension, the LEFT map is injective iff the RIGHT (flipped) map is injective.
The dimension equality is the sole input; the criterion transports non-degeneracy left↔right (the
honest content of "perfect ⟺ bijective ⟺ injective in equal finrank"). Backward direction: apply the
forward direction to `B.flip` (whose flip is `B`, `LinearMap.flip_flip`). -/
theorem injective_iff_flip_injective (B : V →ₗ[F] W →ₗ[F] F)
    (hdim : Module.finrank F V = Module.finrank F W) :
    Function.Injective ⇑B ↔ Function.Injective ⇑B.flip := by
  refine ⟨flip_injective_of_injective B hdim, fun h => ?_⟩
  have := flip_injective_of_injective B.flip hdim.symm h
  rwa [LinearMap.flip_flip] at this

end Adjoint

/-! ## §2. The iso-transport criterion — inherit a base pairing's non-degeneracy through equivalences -/

section Transport

variable {F V W V' W' : Type*} [Field F]
  [AddCommGroup V] [Module F V] [AddCommGroup W] [Module F W]
  [AddCommGroup V'] [Module F V'] [AddCommGroup W'] [Module F W']

/-- **The iso-transport criterion.** If a pairing `B : V →ₗ W →ₗ F` is intertwined with a base pairing
`B' : V' →ₗ W' →ₗ F` through linear equivalences `α : V ≃ V'`, `β : W ≃ W'` on both arguments
(`B a b = B' (α a) (β b)` for all `a, b`), then `B` inherits `B'`'s LEFT non-degeneracy: `B'` injective
⟹ `B` injective. No finite-dimensionality needed — pure transport of injectivity through the
equivalences. -/
theorem injective_of_pairing_congr (B : V →ₗ[F] W →ₗ[F] F) (B' : V' →ₗ[F] W' →ₗ[F] F)
    (α : V ≃ₗ[F] V') (β : W ≃ₗ[F] W')
    (hcompat : ∀ (a : V) (b : W), B a b = B' (α a) (β b))
    (hB' : Function.Injective ⇑B') :
    Function.Injective ⇑B := by
  rw [injective_iff_map_eq_zero]
  intro a ha
  -- `B a = 0` ⟹ for all `b`, `B' (α a) (β b) = 0` ⟹ (β surjective) `B' (α a) = 0` ⟹ `α a = 0`.
  have hzero : B' (α a) = 0 := by
    ext w'
    obtain ⟨b, rfl⟩ := β.surjective w'
    show B' (α a) (β b) = 0
    rw [← hcompat a b]
    show B a b = 0
    rw [ha, LinearMap.zero_apply]
  have haa : α a = 0 := by
    rw [injective_iff_map_eq_zero] at hB'
    exact hB' _ hzero
  exact α.map_eq_zero_iff.mp haa

end Transport

/-! ## §3. Specialisation to the `LefschetzWuDatum` pairing shape `cup.compr₂ μ` -/

section Datum

open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2

variable {X : TopCat} {S : Set ↑X} {k nk n : ℕ}

/-- **The adjoint criterion for a Wu-datum pairing.** The Lefschetz pairing `cup.compr₂ μ` (the shape of
`LefschetzWuDatum.nondeg`) is LEFT-injective iff it is RIGHT-injective, given the datum's own finite-
dimensionality (`findimAbs`, `findimRel`) and Betti equality (`dimeq`). So the `nondeg` field may be
supplied from EITHER side of the pairing. -/
theorem lefschetzPairing_injective_iff_flip
    (mu : RelativeCohomology S n →ₗ[ZMod 2] ZMod 2)
    (cup : Cohomology X k →ₗ[ZMod 2] RelativeCohomology S nk →ₗ[ZMod 2] RelativeCohomology S n)
    (findimAbs : FiniteDimensional (ZMod 2) (Cohomology X k))
    (findimRel : FiniteDimensional (ZMod 2) (RelativeCohomology S nk))
    (dimeq : Module.finrank (ZMod 2) (Cohomology X k)
           = Module.finrank (ZMod 2) (RelativeCohomology S nk)) :
    Function.Injective ⇑(cup.compr₂ mu) ↔ Function.Injective ⇑(cup.compr₂ mu).flip := by
  haveI := findimAbs
  haveI := findimRel
  exact injective_iff_flip_injective (cup.compr₂ mu) dimeq

/-- **The iso-transport criterion for a Wu-datum pairing.** If the datum's Lefschetz pairing
`cup.compr₂ μ` is intertwined with a base pairing `B'` through cohomology equivalences `α`, `β` on both
arguments (`μ (cup a b) = B' (α a) (β b)`), then it inherits `B'`'s left non-degeneracy. This is the
route by which a Poincaré–Lefschetz pairing inherits its base manifold's Poincaré-duality pairing
perfectness, once the intertwining `(α, β, compat)` is available. -/
theorem lefschetzPairing_injective_of_congr {V' W' : Type*}
    [AddCommGroup V'] [Module (ZMod 2) V'] [AddCommGroup W'] [Module (ZMod 2) W']
    (mu : RelativeCohomology S n →ₗ[ZMod 2] ZMod 2)
    (cup : Cohomology X k →ₗ[ZMod 2] RelativeCohomology S nk →ₗ[ZMod 2] RelativeCohomology S n)
    (B' : V' →ₗ[ZMod 2] W' →ₗ[ZMod 2] ZMod 2)
    (α : Cohomology X k ≃ₗ[ZMod 2] V') (β : RelativeCohomology S nk ≃ₗ[ZMod 2] W')
    (hcompat : ∀ (a : Cohomology X k) (b : RelativeCohomology S nk),
      mu (cup a b) = B' (α a) (β b))
    (hB' : Function.Injective ⇑B') :
    Function.Injective ⇑(cup.compr₂ mu) :=
  injective_of_pairing_congr (cup.compr₂ mu) B' α β (fun a b => hcompat a b) hB'

end Datum

end SKEFTHawking.PoincareLefschetzWuPairingCriterion
