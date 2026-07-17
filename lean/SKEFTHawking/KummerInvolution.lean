/-
# Phase 5q.H — the Kummer K3 generator, bricks K1–K3 (the involution, its 16 fixed points, `II(T⁴)=3H`)

Continues `KummerK3Base.lean` (K0 = the smooth closed 4-manifold `TorusFour = (S¹)⁴`). Read that
module's §A decomposition dossier first — it maps the whole Kummer program to a brick sequence. This
module ships the next three bricks, UNCONDITIONALLY (kernel-pure `{propext, Classical.choice,
Quot.sound}`; no `sorry`/`native_decide`/`maxHeartbeats`/axiom):

**K2 — the involution `τ(w) = −w` on `T⁴`.** On the multiplicative circle `Circle ⊂ ℂ`, additive
negation `w ↦ −w` is the group inverse `z ↦ z⁻¹` (`= z̄` on the unit circle). So `τ` on `T⁴ = (S¹)⁴`
is the per-factor inverse, which is exactly the product group inverse `x ↦ x⁻¹`. We ship `τ` as an
explicit concrete map (`torusFourInvolution`), prove it a smooth (`C^ω`) involution (`τ ∘ τ = id`,
`Continuous`, `ContMDiff`), identify it with the group inverse (`torusFourInvolution_eq_inv`), and
package it as a group homomorphism (`torusFourInvolutionHom`, `= invMonoidHom`, valid because `T⁴` is
abelian). Falsifiable pins: `Function.Involutive` (`τ² = id`) and the smoothness at analytic order.

**K3 — the 16 fixed points `{±1}⁴`.** `Fix(τ) = {x | x⁻¹ = x}`: on each `Circle` factor
`z⁻¹ = z ⟺ z² = 1 ⟺ z ∈ {1, negOne}` (the two square-roots of unity, `circle_inv_self_iff`), a
2-element set; the 4-fold product has `2⁴ = 16` points. Falsifiable pin:
`Nat.card {x : TorusFour // τ x = x} = 16` (a genuine `= 16`, via a per-factor product equivalence
and `Set.ncard_pair`). These 16 points are the 2-torsion of `T⁴` — the sites of the 16 `A₁` orbifold
singularities that the Kummer resolution (K4–K6) replaces by `(−2)`-spheres.

**K1 — `H₂(T⁴;ℤ) ≅ ℤ⁶`, intersection form `= 3H` (three hyperbolic planes, σ = 0, even unimodular).**
`H₂(T⁴;ℤ)` has rank `C(4,2) = 6` (the flat torus's homology is the exterior algebra on 4 generators),
and the cup product pairs complementary 2-forms `dxᵢ∧dxⱼ` with `dxₖ∧dxₗ` into hyperbolic blocks, giving
`3H`. **This module ships the arithmetic/lattice half** — the direct analogue of the already-proven
`SpinSigmaRoute.k3Form` arithmetic half (`k3Form_latticeSig`, `k3Form_isEvenUnimodular`): the concrete
`3H` integer form `torusFourForm = H ⊕ H ⊕ H : Matrix (Fin 6) (Fin 6) ℤ`, proven even unimodular
(`torusFourForm_isEvenUnimodular`), of signature `0` (`torusFourForm_latticeSig`), and congruent to the
hyperbolic normal form (`torusFourForm_isHyperbolic`, via `exists_hyperbolic_congr`). The rank-6 type
`Fin 6` is the falsifiable `C(4,2) = 6` pin; the hyperbolic-normal-form congruence is the `= 3H` pin.
Reuses the S²×S²-template lattice engine (`blockDiag`, `isEvenUnimodular_blockDiag`,
`latticeSig_blockDiag`, `Hyp`) exactly as `k3Form`'s `3H` sub-block is built.

**Honest boundary (K1 geometric half — a deferred multi-brick sub-arc, NOT shipped here).** The
*geometric* identity — the singular-homology computation `H₂(T⁴;ℤ) ≅ ℤ⁶` and the cup-form Gram identity
`II(T⁴) ≅ torusFourForm` — is a 4-fold Künneth over `T⁴ = (S¹)⁴`. Mathlib has no Künneth / cup-product
on a product basis for singular homology; the S²×S² analogue (`SphereProdHTwoInt` +
`SphereWitnessTowerInt`, a 5-task arc) was custom-built for that single case only. Building the `T⁴`
product-homology analog (per-factor `H_*(S¹)` + iterated Künneth + the cup Gram computation) is the
open sub-arc that would bridge `torusFourForm` (arithmetic) to the actual `H₂(T⁴)` (geometry) — the same
disclosed-geometric-atom posture the dossier records for K1/K7/K8.
-/
import Mathlib
import SKEFTHawking.KummerK3Base
import SKEFTHawking.SpinSigmaGenerator

namespace SKEFTHawking.KummerInvolution

open scoped Manifold ContDiff
open SKEFTHawking.KummerK3Base
open SKEFTHawking.SpinSigmaRoute

/-! ## K2 — the involution `τ(w) = −w` on `T⁴` -/

/-- The circle element `−1 ∈ Circle ⊂ ℂ` (`‖−1‖ = 1`). Together with `1` it is one of the two
square-roots of unity — the two real points of the circle. -/
noncomputable def negOne : Circle := ⟨-1, by simp [Submonoid.unitSphere]⟩

@[simp] lemma coe_negOne : ((negOne : Circle) : ℂ) = -1 := rfl

/-- `1 ≠ −1` in `Circle` — pushed to `ℂ` where `norm_num` decides it. Ensures the per-factor fixed set
`{1, negOne}` genuinely has 2 elements (not 1). -/
lemma one_ne_negOne : (1 : Circle) ≠ negOne := by
  intro h
  have : ((1 : Circle) : ℂ) = ((negOne : Circle) : ℂ) := by rw [h]
  norm_num at this

/-- **The Kummer involution `τ(w) = −w` on `T⁴`**, realized on `TorusFour = (S¹)⁴` as the per-factor
multiplicative inverse `z ↦ z⁻¹` (on the unit circle, `z⁻¹ = z̄`, which is additive negation on
`ℝ/ℤ`). Ships as an explicit concrete map; `torusFourInvolution_eq_inv` identifies it with the ambient
product-group inverse, unlocking the Lie-group inversion API for smoothness. -/
noncomputable def torusFourInvolution : TorusFour → TorusFour :=
  fun p => (p.1⁻¹, p.2.1⁻¹, p.2.2.1⁻¹, p.2.2.2⁻¹)

/-- `τ` **is the product-group inverse** `x ↦ x⁻¹` (definitionally: `Prod.inv` unfolds to the tuple of
factor inverses). This is the bridge to Mathlib's Lie-group inversion lemmas. -/
theorem torusFourInvolution_eq_inv (x : TorusFour) : torusFourInvolution x = x⁻¹ := rfl

/-- **`τ` is an involution** (`τ ∘ τ = id`): per-factor `(z⁻¹)⁻¹ = z` (`inv_inv`). The falsifiable
`τ² = id` pin — `τ` is a genuine ℤ/2 action, the quotient by which is the Kummer orbifold `T⁴/±1`. -/
theorem torusFourInvolution_involutive : Function.Involutive torusFourInvolution := by
  intro x; simp only [torusFourInvolution, inv_inv]

/-- `τ ∘ τ = id`, the composed form of `torusFourInvolution_involutive`. -/
theorem torusFourInvolution_comp_self : torusFourInvolution ∘ torusFourInvolution = id :=
  funext torusFourInvolution_involutive

/-- **`τ` is smooth (`C^ω`)** as a self-map of the analytic manifold `T⁴` — from the Lie-group
inversion `contMDiff_inv` (`T⁴` is a Lie group, `KummerK3Base.torusFour_lieGroup`). Smoothness of `τ`
is required for the quotient `T⁴/τ` to be an orbifold (smooth away from the fixed points). -/
theorem torusFourInvolution_contMDiff :
    ContMDiff ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1))))
      ((𝓡 1).prod ((𝓡 1).prod ((𝓡 1).prod (𝓡 1)))) ω torusFourInvolution :=
  contMDiff_inv _ ω

/-- `τ` is continuous (a corollary of smoothness). -/
theorem torusFourInvolution_continuous : Continuous torusFourInvolution :=
  torusFourInvolution_contMDiff.continuous

/-- **`τ` as a group homomorphism** `T⁴ →* T⁴` — the inverse map is a monoid hom precisely because
`T⁴ = (S¹)⁴` is abelian (`invMonoidHom`). (An `AddMonoid.End`/group endomorphism in the multiplicative
presentation.) -/
noncomputable def torusFourInvolutionHom : TorusFour →* TorusFour := invMonoidHom

/-- The hom `torusFourInvolutionHom` acts as `τ`. -/
theorem torusFourInvolutionHom_apply (x : TorusFour) :
    torusFourInvolutionHom x = torusFourInvolution x := rfl

/-! ## K3 — the 16 fixed points `{±1}⁴` -/

/-- **The per-factor 2-torsion characterization**: on the circle, `z⁻¹ = z ⟺ z² = 1 ⟺ z ∈ {1, −1}`.
The fixed points of `w ↦ −w` on each `S¹` are exactly the two square-roots of unity. -/
lemma circle_inv_self_iff (z : Circle) : z⁻¹ = z ↔ z = 1 ∨ z = negOne := by
  have hz : (z : ℂ) ≠ 0 := Circle.coe_ne_zero z
  rw [← Circle.coe_inj, Circle.coe_inv]
  constructor
  · intro h
    have hzz : (z : ℂ) * z = 1 := by field_simp at h ⊢; linear_combination -h
    rcases mul_self_eq_one_iff.mp hzz with h1 | h1
    · exact Or.inl (Circle.coe_inj.mp (by simpa using h1))
    · exact Or.inr (Circle.coe_inj.mp (by simpa using h1))
  · rintro (rfl | rfl) <;> simp

/-- **The per-factor fixed set has exactly 2 points**: `Nat.card {z : Circle // z⁻¹ = z} = 2`, the two
square-roots of unity `{1, negOne}`. The `= 2` that raises to `2⁴ = 16` across the four factors. -/
lemma perFactor_fixedPoints_card : Nat.card {z : Circle // z⁻¹ = z} = 2 := by
  have hset : {z : Circle | z⁻¹ = z} = {1, negOne} := by
    ext z; simp [circle_inv_self_iff]
  have h2 : Nat.card {z : Circle // z⁻¹ = z} = ({1, negOne} : Set Circle).ncard := by
    rw [← hset]; exact Nat.card_coe_set_eq _
  rw [h2, Set.ncard_pair one_ne_negOne]

/-- **The fixed set of `τ` is the 4-fold product of the per-factor fixed sets**: `x` is fixed iff each
of its four coordinates is fixed (`x⁻¹ = x` componentwise). Packaged as an equivalence to the product
of the four per-factor 2-torsion subtypes. -/
noncomputable def fixedPointsEquiv :
    {x : TorusFour // torusFourInvolution x = x} ≃
      ({z : Circle // z⁻¹ = z} × {z : Circle // z⁻¹ = z} ×
        {z : Circle // z⁻¹ = z} × {z : Circle // z⁻¹ = z}) where
  toFun x :=
    ⟨⟨x.1.1, congrArg Prod.fst x.2⟩,
     ⟨x.1.2.1, congrArg (Prod.fst ∘ Prod.snd) x.2⟩,
     ⟨x.1.2.2.1, congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) x.2⟩,
     ⟨x.1.2.2.2, congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) x.2⟩⟩
  invFun y :=
    ⟨(y.1.1, y.2.1.1, y.2.2.1.1, y.2.2.2.1), by
      simp only [torusFourInvolution]
      rw [y.1.2, y.2.1.2, y.2.2.1.2, y.2.2.2.2]⟩
  left_inv x := by ext <;> rfl
  right_inv y := by ext <;> rfl

/-- **K3 — the 16 fixed points**: `τ` on `T⁴` has exactly `2⁴ = 16` fixed points, `{±1}⁴ ⊂ (S¹)⁴` (the
2-torsion of `T⁴`). The falsifiable `= 16` pin: obtained from the per-factor `= 2`
(`perFactor_fixedPoints_card`) via the product equivalence `fixedPointsEquiv` and `Nat.card_prod`.
These 16 points are the singular loci of the Kummer orbifold `T⁴/τ`. -/
theorem torusFourInvolution_fixedPoints_card :
    Nat.card {x : TorusFour // torusFourInvolution x = x} = 16 := by
  rw [Nat.card_congr fixedPointsEquiv, Nat.card_prod, Nat.card_prod, Nat.card_prod,
    perFactor_fixedPoints_card]

/-! ## K1 — `H₂(T⁴;ℤ) ≅ ℤ⁶`, intersection form `= 3H` (arithmetic/lattice half)

The concrete `3H` intersection form and its lattice invariants, mirroring the `SpinSigmaRoute.k3Form`
arithmetic half. See the module docstring for the honest boundary: the *geometric* singular-homology
`H₂(T⁴)=ℤ⁶` + cup-form Gram identity is a deferred 4-fold-Künneth sub-arc. -/

/-- **The `T⁴` intersection form `II(T⁴) = 3H`** — three hyperbolic planes, `H ⊕ H ⊕ H`, as a concrete
`6 × 6` integer matrix (`rank = C(4,2) = 6`). Built with the same `blockDiag`/`Hyp` engine as
`k3Form`'s `3H` sub-block. -/
noncomputable def torusFourForm : Matrix (Fin 6) (Fin 6) ℤ :=
  blockDiag (blockDiag Hyp Hyp) Hyp

/-- **`II(T⁴) = 3H` is even unimodular** — a genuine (spin) intersection form: even diagonal,
`det = ±1`. From `isEvenUnimodular_hyp` through two `blockDiag` sums. -/
theorem torusFourForm_isEvenUnimodular : IsEvenUnimodular torusFourForm := by
  have h4 : IsEvenUnimodular (blockDiag Hyp Hyp) :=
    isEvenUnimodular_blockDiag _ _ isEvenUnimodular_hyp isEvenUnimodular_hyp
  exact isEvenUnimodular_blockDiag _ _ h4 isEvenUnimodular_hyp

/-- **`latticeSig (II(T⁴)) = 0`** — signature `0`, from `σ(H) = 0` summed over the three hyperbolic
blocks (block additivity `latticeSig_blockDiag`). The falsifiable numeric pin distinguishing `3H`
(σ = 0) from the K3 form (σ = −16). -/
theorem torusFourForm_latticeSig : latticeSig torusFourForm = 0 := by
  have h4 : IsEvenUnimodular (blockDiag Hyp Hyp) :=
    isEvenUnimodular_blockDiag _ _ isEvenUnimodular_hyp isEvenUnimodular_hyp
  show latticeSig (blockDiag (blockDiag Hyp Hyp) Hyp) = 0
  rw [latticeSig_blockDiag _ _ h4 isEvenUnimodular_hyp,
    latticeSig_blockDiag _ _ isEvenUnimodular_hyp isEvenUnimodular_hyp,
    hyp_latticeSig]
  norm_num

/-- **`II(T⁴)` is the hyperbolic normal form `3H`** — it is `IntCongr` to a hyperbolic-standard form
(a reindexed block-sum of `H`'s). Since the witness `N` has rank `6` and `IsHyperbolicForm`, it is
exactly `3` hyperbolic planes (`IsHyperbolicForm.two_dvd_rank`: `2 ∣ 6`, so `6/2 = 3` summands). The
`= 3H` congruence pin, from `exists_hyperbolic_congr` on the even-unimodular signature-0 form. -/
theorem torusFourForm_isHyperbolic :
    ∃ N : Matrix (Fin 6) (Fin 6) ℤ, IsHyperbolicForm N ∧ IntCongr torusFourForm N :=
  exists_hyperbolic_congr torusFourForm torusFourForm_isEvenUnimodular torusFourForm_latticeSig

end SKEFTHawking.KummerInvolution
