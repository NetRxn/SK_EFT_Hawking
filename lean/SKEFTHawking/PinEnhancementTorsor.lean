/-
# Phase 5q.H (E2) — the pin⁻ enhancement torsor is SIMPLY TRANSITIVE: the missing substrate, built

`CharSurfaceFKVacuity` §3 named the substrate that a general-`σ` `[FK]` layer is missing: the
enhancement `Q` must be *produced* from the characteristic surface's pin⁻ normal data, and "that is
the `H¹(F;ℤ/2)`-torsor of pin⁻ structures". `GMPinTorsorCeiling` then measured the ambiguity from
below and above along the `shift` action. But **neither module proves the torsor claim itself** —
both only show that shifts *give* ambiguity (`⊆`), never that shifts are *all* the ambiguity (`=`).
Without that, "the substrate must record the pin⁻ class" is a hope, not a theorem: some enhancement
of the same polar form could in principle be unreachable by any shift, and then recording the class
would not suffice.

This module closes it. `exists_shift_of_B_eq` + `shift_left_injective` give

> **`shift_simply_transitive`** — for enhancements `Q₁, Q₂` of the SAME polar form there is a
> **unique** `w ∈ H₁(F;ℤ/2) ≅ H¹(F;ℤ/2)` with `Q₁.shift w = Q₂`.

so the fibre of `Q ↦ Q.B` through any point is *exactly* one `shift`-orbit, freely and transitively
acted on. Consequences, all now theorems rather than expectations:

* `gmResidue_eq_of_B_eq_of_q_eq` — the Guillou–Marin residue of a characteristic surface is a
  **function of `(B, w)` and nothing else**: the polar form the substrate already records, plus one
  class. This is the exact, complete specification of the missing field.
* `gmrelation_shift_iff` — `[FK]` at general `σ`, re-typed as a condition on that class:
  `GMrelation σ F (Q.shift w) ↔ 4·q(w) = 2β(Q) − (σ − F·F)`. Its hypothesis is a predicate on the
  pin⁻ class, **not** on `σ`'s residue, so it passes the intensional admissibility criterion of
  `GMTripleLayerForcing` — unlike `GMrelation σ 0 C.Q` (a σ-arithmetic Prop once the wire's leaves
  force `F·F = 0`, `β = 0`) and unlike triple-level bordism generation.
* `exists_shift_gmrelation_iff` — exactly when a pin⁻ structure realizing a prescribed `(σ, F·F)`
  exists at all: the constructive counterpart of `CharSurfaceFKVacuity`'s `∃`-vacuity finding,
  which now has a sharp criterion instead of a free choice.

The proof of transitivity is the perfect-pairing argument: two enhancements of the same `B` differ
by `q₂ − q₁`, which is additive and 2-torsion-valued, hence `embed2 ∘ g` for a `ZMod 2`-linear
functional `g`; nondegeneracy of `B` makes `w ↦ B(w, ·)` injective, hence (finite domain) bijective,
so `g = B(w, ·)` for a unique `w`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.GMPinTorsorCeiling

namespace SKEFTHawking.PinTorsor

open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic SKEFTHawking.GuillouMarin
open SKEFTHawking.GMTorsor

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## §1. The polar form is a perfect pairing on `H₁(F;ℤ/2)` -/

/-- `B` is `ZMod 2`-linear in its left slot (from symmetry plus right-linearity). -/
lemma B_smul_left (Q : Z4Quadratic ι) (a : ZMod 2) (w v : ι → ZMod 2) :
    Q.B (a • w) v = a * Q.B w v := by
  rw [Q.B_symm, Q.B_smul_right, Q.B_symm]

/-- `B(w, ·)` as an additive map — the functional the pairing assigns to `w`. -/
def BRight (Q : Z4Quadratic ι) (w : ι → ZMod 2) : (ι → ZMod 2) →+ ZMod 2 where
  toFun v := Q.B w v
  map_zero' := Q.B_zero_right w
  map_add' := Q.B_add_right w

/-- Two additive functionals on `ι → ZMod 2` agreeing on the standard basis agree everywhere. -/
lemma addHom_ext_single {M : Type*} [AddCommGroup M] (f g : (ι → ZMod 2) →+ M)
    (h : ∀ i, f (Pi.single i 1) = g (Pi.single i 1)) (v : ι → ZMod 2) : f v = g v := by
  classical
  have hv : v = ∑ i, Pi.single i (v i) := (Finset.univ_sum_single v).symm
  rw [hv, map_sum, map_sum]
  refine Finset.sum_congr rfl (fun i _ => ?_)
  rcases (by decide : ∀ a : ZMod 2, a = 0 ∨ a = 1) (v i) with h0 | h1
  · rw [h0]
    simp
  · rw [h1]; exact h i

/-- The polar form in coordinates: `w ↦ (i ↦ B(w, eᵢ))`. -/
def polarMatrix (Q : Z4Quadratic ι) : (ι → ZMod 2) →ₗ[ZMod 2] (ι → ZMod 2) where
  toFun w := fun i => Q.B w (Pi.single i 1)
  map_add' w w' := by funext i; exact Q.B_add_left w w' _
  map_smul' a w := by funext i; exact B_smul_left Q a w _

/-- **Nondegeneracy in coordinates**: a class pairing to zero against every basis vector is zero. -/
lemma polarMatrix_injective (Q : Z4Quadratic ι) : Function.Injective (polarMatrix Q) := by
  rw [injective_iff_map_eq_zero]
  intro w hw
  refine Q.nondeg w (fun v => ?_)
  have hb : ∀ i, BRight Q w (Pi.single i 1) = (0 : (ι → ZMod 2) →+ ZMod 2) (Pi.single i 1) :=
    fun i => congrFun hw i
  exact addHom_ext_single (BRight Q w) 0 hb v

/-- **The polar form is a PERFECT pairing** (new): every additive `ZMod 2`-functional on
`H₁(F;ℤ/2)` is `B(w, ·)` for some `w`. Injectivity is nondegeneracy; surjectivity is finiteness. -/
theorem exists_B_eq (Q : Z4Quadratic ι) (g : (ι → ZMod 2) →+ ZMod 2) :
    ∃ w, ∀ v, Q.B w v = g v := by
  obtain ⟨w, hw⟩ :=
    (Finite.injective_iff_surjective.mp (polarMatrix_injective Q)) (fun i => g (Pi.single i 1))
  refine ⟨w, fun v => ?_⟩
  exact addHom_ext_single (BRight Q w) g (fun i => congrFun hw i) v

/-! ## §2. The enhancement torsor is simply transitive -/

/-- The inverse of `embed2` on its image, the 2-torsion subgroup `{0, 2} ⊆ ZMod 4`. -/
def half (a : ZMod 4) : ZMod 2 := if a = 2 then 1 else 0

lemma embed2_half {a : ZMod 4} (h : a + a = 0) : embed2 (half a) = a := by
  revert h; revert a; decide

/-- **Transitivity** (new): two enhancements of the same polar form differ by a `shift`. The
difference `q₂ − q₁` is additive (both refine the same `B`) and 2-torsion-valued, hence `embed2 ∘ g`
for a `ZMod 2`-functional `g`; the perfect pairing realizes `g` as `B(w, ·)`. -/
theorem exists_shift_of_B_eq {Q₁ Q₂ : Z4Quadratic ι} (hB : Q₁.B = Q₂.B) :
    ∃ w, Q₁.shift w = Q₂ := by
  classical
  have hadd : ∀ x y, Q₂.q (x + y) - Q₁.q (x + y)
      = (Q₂.q x - Q₁.q x) + (Q₂.q y - Q₁.q y) := by
    intro x y
    rw [Q₁.refine' x y, Q₂.refine' x y, hB]
    ring
  have hself : ∀ v : ι → ZMod 2, v + v = 0 := by
    intro v; funext i
    exact (by decide : ∀ a : ZMod 2, a + a = 0) (v i)
  have h2 : ∀ v, (Q₂.q v - Q₁.q v) + (Q₂.q v - Q₁.q v) = 0 := by
    intro v
    have h := hadd v v
    rw [hself v, Q₁.q_zero, Q₂.q_zero] at h
    linear_combination -h
  have hg : ∀ v, embed2 (half (Q₂.q v - Q₁.q v)) = Q₂.q v - Q₁.q v :=
    fun v => embed2_half (h2 v)
  have hgadd : ∀ x y, half (Q₂.q (x + y) - Q₁.q (x + y))
      = half (Q₂.q x - Q₁.q x) + half (Q₂.q y - Q₁.q y) := by
    intro x y
    apply embed2_injective
    rw [embed2_add, hg, hg, hg, hadd]
  let gHom : (ι → ZMod 2) →+ ZMod 2 :=
    { toFun := fun v => half (Q₂.q v - Q₁.q v)
      map_zero' := by
        apply embed2_injective
        rw [hg, Q₁.q_zero, Q₂.q_zero]
        decide
      map_add' := hgadd }
  obtain ⟨w, hw⟩ := exists_B_eq Q₁ gHom
  refine ⟨w, Z4Quadratic.ext (funext fun v => ?_)⟩
  show Q₁.q v + embed2 (Q₁.B w v) = Q₂.q v
  rw [hw v]
  show Q₁.q v + embed2 (half (Q₂.q v - Q₁.q v)) = Q₂.q v
  rw [hg v]
  ring

/-- **Freeness** (new): the torsor action is free — a shift class is determined by its effect. -/
theorem shift_left_injective (Q : Z4Quadratic ι) : Function.Injective Q.shift := by
  intro w w' h
  have hq : ∀ v, embed2 (Q.B w v) = embed2 (Q.B w' v) := by
    intro v
    have := congrArg (fun R : Z4Quadratic ι => R.q v) h
    simpa [Z4Quadratic.shift_q] using this
  have hB : ∀ v, Q.B (w + w') v = 0 := by
    intro v
    rw [Q.B_add_left]
    have := embed2_injective (hq v)
    rw [this]
    exact (by decide : ∀ a : ZMod 2, a + a = 0) _
  have hww : w + w' = 0 := Q.nondeg _ hB
  have : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
  funext i
  exact this (w i) (w' i) (congrFun hww i)

/-- **The pin⁻ enhancement torsor is SIMPLY TRANSITIVE** (new — the theorem the vacuity analysis
assumed). For enhancements of one and the same polar form there is a *unique* class
`w ∈ H₁(F;ℤ/2) ≅ H¹(F;ℤ/2)` carrying one to the other. So the fibre of `Q ↦ Q.B` is exactly one
free `shift`-orbit: recording the polar form **and** one class records the enhancement completely,
and nothing less does. -/
theorem shift_simply_transitive {Q₁ Q₂ : Z4Quadratic ι} (hB : Q₁.B = Q₂.B) :
    ∃! w, Q₁.shift w = Q₂ := by
  obtain ⟨w, hw⟩ := exists_shift_of_B_eq hB
  exact ⟨w, hw, fun w' hw' => shift_left_injective Q₁ (hw'.trans hw.symm)⟩

/-! ## §3. The complete specification of the missing substrate field -/

/-- **The Guillou–Marin residue is a function of `(B, w)` and of nothing else** (new). Given the
polar form — the only surface datum the `PinCharSurface` substrate records — the residue `2·β` is
determined by one class `w ∈ H¹(F;ℤ/2)`, via `2·β(Q₀.shift w) = 2·β(Q₀) − 4·q₀(w)`. Together with
`GMPinTorsorCeiling.doubleBrown_stdShift3_injective` (four classes, four distinct residues) this is
the exact, complete specification of the field the substrate is missing: **one `H¹(F;ℤ/2)`-class,
carrying exactly `ℤ/4`.** -/
theorem gmResidue_determined_by_shift_class {Q₁ Q₂ : Z4Quadratic ι} (hB : Q₁.B = Q₂.B) :
    ∃! w, Q₁.shift w = Q₂ ∧
      doubleBrown Q₂ = doubleBrown Q₁ - 4 * (((Q₁.q w).val : ℕ) : ZMod 16) := by
  obtain ⟨w, hw, huniq⟩ := shift_simply_transitive hB
  exact ⟨w, ⟨hw, by rw [← hw, doubleBrown_shift]⟩, fun w' hw' => huniq w' hw'.1⟩

/-- **`[FK]` at general `σ`, re-typed as a condition on the pin⁻ CLASS** (new — the admissible
statement layer). Guillou–Marin for the enhancement the normal data selects is exactly
`4·q₀(w) = 2β(Q₀) − (σ − F·F)`: a predicate on the class `w ∈ H¹(F;ℤ/2)` and the base enhancement,
**not** on `σ`'s residue class. It therefore passes the intensional admissibility criterion of
`GMTripleLayerForcing` — discharging it requires computing the membrane index that selects `w`
(the blueprint's `[G2]`/`[Q1]`), not knowing `σ mod 16` in advance. -/
theorem gmrelation_shift_iff (Q : Z4Quadratic ι) (w : ι → ZMod 2) (σ F : ℤ) :
    GMrelation σ F (Q.shift w) ↔
      4 * (((Q.q w).val : ℕ) : ZMod 16) = doubleBrown Q - ((σ - F : ℤ) : ZMod 16) := by
  constructor
  · intro h
    have e : ((σ - F : ℤ) : ZMod 16) = doubleBrown (Q.shift w) := h
    rw [doubleBrown_shift] at e
    linear_combination e
  · intro h
    show ((σ - F : ℤ) : ZMod 16) = doubleBrown (Q.shift w)
    rw [doubleBrown_shift]
    linear_combination h

/-- **When a realizing pin⁻ structure exists at all** (new — the sharp criterion replacing the free
choice of `CharSurfaceFKVacuity`'s `∃`-vacuity witness). A pin⁻ structure on the given
characteristic surface satisfying Guillou–Marin for a prescribed `(σ, F·F)` exists precisely when
the required shift `2β(Q₀) − (σ − F·F)` is `4·q₀(w)` for some class `w` — so realizability is a
genuine constraint on `(σ, F·F)`, not a free parameter. -/
theorem exists_shift_gmrelation_iff (Q : Z4Quadratic ι) (σ F : ℤ) :
    (∃ w, GMrelation σ F (Q.shift w)) ↔
      ∃ w : ι → ZMod 2,
        4 * (((Q.q w).val : ℕ) : ZMod 16) = doubleBrown Q - ((σ - F : ℤ) : ZMod 16) :=
  exists_congr (fun w => gmrelation_shift_iff Q w σ F)

end SKEFTHawking.PinTorsor
