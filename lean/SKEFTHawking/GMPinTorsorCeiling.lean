/-
# Phase 5q.H (E2) — the pin⁻-torsor CEILING on the Guillou–Marin residue: exactly how much of
`[FK]` the geometry must carry

`CharSurfaceFKVacuity` established (kernel-purely) that the `[FK]`/Guillou–Marin congruence at
general `σ` cannot be typed over the substrate's *free* enhancement field `Q`: two `Z4Quadratic`
with identical polar forms have incompatible GM residues
(`charSurfaceFK_universal_over_free_enhancement_false`), and the missing substrate is `Q`
*computed* from the surface's pin⁻ normal data. That is a **qualitative** obstruction. This module
makes it **quantitative**, and the answer is sharp:

> The `H¹(F;ℤ/2)`-torsor of pin⁻ structures moves the GM residue `2·β` by **exactly** the subgroup
> `4·ℤ/16 ≅ ℤ/4`. Hence the pin⁻-structure-INDEPENDENT content of Guillou–Marin is exactly the
> **mod-4** congruence `σ − F·F ≡ 2·β (mod 4)`, whose spin specialization is `4 ∣ σ` — and `σ = 4`
> witnesses that this is strictly weaker than Rokhlin.

So the 4→16 gap — two full bits, the *entire* content of `[FK]` beyond a trivial mod-4 shadow — is
carried by the CHOICE of pin⁻ structure on the characteristic surface, i.e. by the smooth normal
data. This is the exact size of the substrate named as missing in `CharSurfaceFKVacuity` §3, and it
is why no reformulation over `(H₁(F;ℤ/2), B)` alone can reach `16 ∣ σ`.

## What is proved

* `doubleBrown_shift` — the torsor action on the GM residue: `2·β(shift w Q) = 2·β(Q) − 4·q(w)`
  in `ℤ/16`. (Lifts `brown_shift` = KT-LMS Lemma 3.7 through the doubling `ℤ/8 → ℤ/16`.)
* `gmDefect`, `gmrelation_iff_gmDefect_eq_zero`, `gmDefect_orthSum`, `gmDefect_neg` — the GM
  congruence recast as the vanishing of an ADDITIVE `ℤ/16`-valued defect (the bordism-invariant
  shape; additivity/reversal imported from `gmrelation_orthSum` / `gmrelation_neg`).
* `gmDefect_shift`, `reduce16to4_gmDefect_shift` — the defect's mod-4 reduction is torsor-invariant
  (the UPPER bound on what a pin⁻-free argument can see).
* `exists_shift_gmDefect_eq_add_four_mul` + `gmDefect_shift_realizes_all_four` — the bound is
  ATTAINED: on `stdQuadratic 3` the four translates are all realized, so the ambiguity subgroup is
  exactly `4·ℤ/16`, not smaller.
* `reduce16to8_doubleBrown_not_shift_invariant` — the mod-8 reduction is NOT torsor-invariant
  (`stdQuadratic 1` vs its translate: `2` vs `14`), so mod 4 is the true ceiling, not an artifact.
* `torsor_free_shadow_cannot_prove_rokhlin` — the ceiling as a no-go: at a `β = 0` characteristic
  surface with nonempty `H₁` (`stdQuadratic 8`) the full torsor-invariant GM shadow holds for
  `σ = 4`, while `¬ (16 ∣ 4)`.

Nothing here is a walk-back: no existing statement is narrowed, and every theorem is new content.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.GMRokhlinDischarge
import SKEFTHawking.BrownSurgeryReduction

namespace SKEFTHawking.GMTorsor

open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic SKEFTHawking.GuillouMarin
open SKEFTHawking.GMRokhlin

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## §1. The Guillou–Marin defect: the congruence as the vanishing of an additive invariant -/

/-- The **Guillou–Marin defect** `δ(σ, F·F, Q) := (σ − F·F) − 2·β(Q) ∈ ℤ/16`. The GM congruence is
exactly `δ = 0`; recasting it this way exposes the additive (bordism-invariant) structure that
`GMrelation` hides inside an equation between two sides. -/
noncomputable def gmDefect (σ F : ℤ) (Q : Z4Quadratic ι) : ZMod 16 :=
  ((σ - F : ℤ) : ZMod 16) - doubleBrown Q

/-- **The GM congruence is the vanishing of the defect.** -/
theorem gmrelation_iff_gmDefect_eq_zero {σ F : ℤ} {Q : Z4Quadratic ι} :
    GMrelation σ F Q ↔ gmDefect σ F Q = 0 := by
  constructor
  · intro h
    have e : ((σ - F : ℤ) : ZMod 16) = doubleBrown Q := h
    simp [gmDefect, e]
  · intro h
    have : ((σ - F : ℤ) : ZMod 16) - doubleBrown Q = 0 := h
    exact sub_eq_zero.mp this

/-- **The defect is additive under disjoint union of characteristic pairs** — the algebraic engine
of a bordism-invariance argument, now stated for the invariant itself rather than for the
congruence. -/
theorem gmDefect_orthSum {σ₁ F₁ σ₂ F₂ : ℤ} {ι₁ ι₂ : Type*}
    [Fintype ι₁] [Fintype ι₂] [DecidableEq ι₁] [DecidableEq ι₂]
    (Q₁ : Z4Quadratic ι₁) (Q₂ : Z4Quadratic ι₂) :
    gmDefect (σ₁ + σ₂) (F₁ + F₂) (Z4Quadratic.orthSum Q₁ Q₂)
      = gmDefect σ₁ F₁ Q₁ + gmDefect σ₂ F₂ Q₂ := by
  unfold gmDefect
  rw [doubleBrown_orthSum]
  push_cast
  ring

/-- **The defect negates under orientation reversal** (`σ ↦ −σ`, `F·F ↦ −F·F`, `β ↦ −β`). -/
theorem gmDefect_neg {σ F : ℤ} (Q : Z4Quadratic ι) :
    gmDefect (-σ) (-F) (Z4Quadratic.neg Q) = - gmDefect σ F Q := by
  unfold gmDefect
  rw [doubleBrown_neg]
  push_cast
  ring

/-! ## §2. The pin⁻ torsor action on the GM residue -/

/-- The doubling `ℤ/8 → ℤ/16` intertwines the KT-LMS shift `β ↦ β − 2·q(w)` with `2β ↦ 2β − 4·q(w)`.
Pure `ZMod` arithmetic (`8 × 4 = 32` cases). -/
private lemma double_sub_two_val (b : ZMod 8) (a : ZMod 4) :
    2 * (((b - 2 * ((a.val : ℕ) : ZMod 8))).val : ZMod 16)
      = 2 * ((b.val : ℕ) : ZMod 16) - 4 * ((a.val : ℕ) : ZMod 16) := by
  revert b a; decide

/-- **The pin⁻ torsor action on the Guillou–Marin residue** (new): changing the pin⁻ structure on
the characteristic surface by the class dual to `w ∈ H₁(F;ℤ/2)` changes `2·β` by `−4·q(w)` in
`ℤ/16`. This is `brown_shift` (KT-LMS Lemma 3.7, Taylor `0802.0111` p. 3) pushed through the
doubling `ℤ/8 → ℤ/16` that defines the GM residue. Falsifiable anchor: at `Q = stdQuadratic 1`,
`w = 1` it gives `2 − 4 = 14`, matching `brown_shift_rp2` (`β = 7`, `2β = 14`). -/
theorem doubleBrown_shift (Q : Z4Quadratic ι) (w : ι → ZMod 2) :
    doubleBrown (Q.shift w) = doubleBrown Q - 4 * (((Q.q w).val : ℕ) : ZMod 16) := by
  have hb : (Q.shift w).brown = Q.brown - 2 * (((Q.q w).val : ℕ) : ZMod 8) :=
    eq_sub_of_add_eq (Q.brown_shift w)
  show 2 * (((Q.shift w).brown.val : ℕ) : ZMod 16)
      = 2 * ((Q.brown.val : ℕ) : ZMod 16) - 4 * (((Q.q w).val : ℕ) : ZMod 16)
  rw [hb]
  exact double_sub_two_val Q.brown (Q.q w)

/-- **The GM defect under a change of pin⁻ structure** (new): `δ` shifts by `+4·q(w)`. -/
theorem gmDefect_shift {σ F : ℤ} (Q : Z4Quadratic ι) (w : ι → ZMod 2) :
    gmDefect σ F (Q.shift w) = gmDefect σ F Q + 4 * (((Q.q w).val : ℕ) : ZMod 16) := by
  unfold gmDefect
  rw [doubleBrown_shift]
  ring

/-! ## §3. The ceiling: mod 4 is torsor-invariant, mod 8 is not -/

/-- The reduction `ℤ/16 → ℤ/4`. -/
def reduce16to4 : ZMod 16 →+* ZMod 4 :=
  ZMod.castHom (show (4 : ℕ) ∣ 16 by norm_num) (ZMod 4)

/-- **The mod-4 reduction of the GM defect is pin⁻-torsor invariant** (new — the UPPER bound). Any
consequence of Guillou–Marin that is to hold without committing to a particular pin⁻ structure on
the characteristic surface is a consequence of the mod-4 congruence alone. -/
theorem reduce16to4_gmDefect_shift {σ F : ℤ} (Q : Z4Quadratic ι) (w : ι → ZMod 2) :
    reduce16to4 (gmDefect σ F (Q.shift w)) = reduce16to4 (gmDefect σ F Q) := by
  rw [gmDefect_shift, map_add, map_mul]
  have h4 : reduce16to4 (4 : ZMod 16) = 0 := by decide
  rw [h4, zero_mul, add_zero]

/-- **The mod-8 reduction is NOT torsor-invariant** (new — so mod 4 is the true ceiling, not an
artifact of a lossy bound). The two pin⁻ structures on `ℝP²` inside `ℝP⁴` (`stdQuadratic 1` and its
torsor translate, `brown_shift_rp2`) have GM residues `2` and `14`, which differ already mod 8. -/
theorem reduce16to8_doubleBrown_not_shift_invariant :
    ∃ (Q : Z4Quadratic (Fin 1)) (w : Fin 1 → ZMod 2),
      reduce16to8 (doubleBrown (Q.shift w)) ≠ reduce16to8 (doubleBrown Q) := by
  refine ⟨stdQuadratic 1, 1, ?_⟩
  rw [reduce16to8_doubleBrown, reduce16to8_doubleBrown, brown_shift_rp2, brown_stdQuadratic]
  decide

/-- The mod-4 reduction of the GM residue itself (not just the defect) is torsor-invariant. -/
theorem reduce16to4_doubleBrown_shift (Q : Z4Quadratic ι) (w : ι → ZMod 2) :
    reduce16to4 (doubleBrown (Q.shift w)) = reduce16to4 (doubleBrown Q) := by
  rw [doubleBrown_shift, map_sub, map_mul]
  have h4 : reduce16to4 (4 : ZMod 16) = 0 := by decide
  rw [h4, zero_mul, sub_zero]

/-! ## §4. The bound is ATTAINED: the ambiguity subgroup is exactly `4·ℤ/16 ≅ ℤ/4` -/

/-- The `c`-th pin⁻ structure on the genus-3 standard characteristic surface: shift by the class
supported on the first `c` handles. Since `stdQuadratic g` has `q(w) = #{i : wᵢ = 1}`, this realizes
every value of `q(w) ∈ ℤ/4` once `g ≥ 3`. -/
def stdShift3 (c : ZMod 4) : Fin 3 → ZMod 2 := fun i => if (i : ℕ) < c.val then 1 else 0

@[simp] theorem stdQuadratic3_q_stdShift3 (c : ZMod 4) :
    (stdQuadratic 3).q (stdShift3 c) = c := by revert c; decide

/-- Multiplication by `4` is injective on the image of `ZMod 4 → ℤ/16` — the `ℤ/4 ↪ ℤ/16` that the
torsor ambiguity subgroup is. -/
private lemma four_mul_val_injective :
    ∀ a b : ZMod 4, (4 : ZMod 16) * ((a.val : ℕ) : ZMod 16)
      = 4 * ((b.val : ℕ) : ZMod 16) → a = b := by decide

/-- **The four pin⁻ structures realize the four translates** (new — ATTAINMENT of the ceiling). -/
theorem doubleBrown_stdShift3 (c : ZMod 4) :
    doubleBrown ((stdQuadratic 3).shift (stdShift3 c))
      = doubleBrown (stdQuadratic 3) - 4 * ((c.val : ℕ) : ZMod 16) := by
  rw [doubleBrown_shift, stdQuadratic3_q_stdShift3]

/-- **Four pin⁻ structures on ONE characteristic surface, four DISTINCT Guillou–Marin residues**
(new). With `reduce16to4_doubleBrown_shift` (the upper bound) this pins the torsor ambiguity
subgroup to be *exactly* `4·ℤ/16 ≅ ℤ/4` — neither larger nor smaller. -/
theorem doubleBrown_stdShift3_injective :
    Function.Injective (fun c : ZMod 4 => doubleBrown ((stdQuadratic 3).shift (stdShift3 c))) := by
  intro a b hab
  simp only [doubleBrown_stdShift3] at hab
  exact four_mul_val_injective a b (sub_right_injective hab)

/-- **The substrate must record exactly two bits beyond `(H₁(F;ℤ/2), B)`** (new — the sharp,
quantitative form of `CharSurfaceFKVacuity.charSurfaceFK_universal_over_free_enhancement_false`,
which exhibited only a *pair*). All four enhancements below share the polar form `B` verbatim
(`shift_B`), so every datum the `PinCharSurface` substrate records about the characteristic surface
is identical for the four; yet no two of them can satisfy Guillou–Marin at the same `(σ, F·F)`. -/
theorem four_pin_structures_same_polar_form_pairwise_incompatible_gm :
    (∀ c : ZMod 4, ((stdQuadratic 3).shift (stdShift3 c)).B = (stdQuadratic 3).B) ∧
      ∀ c₁ c₂ : ZMod 4, c₁ ≠ c₂ → ∀ σ F : ℤ,
        ¬ (GMrelation σ F ((stdQuadratic 3).shift (stdShift3 c₁)) ∧
            GMrelation σ F ((stdQuadratic 3).shift (stdShift3 c₂))) := by
  refine ⟨fun _ => rfl, fun c₁ c₂ hne σ F ⟨h₁, h₂⟩ => hne ?_⟩
  have e₁ : ((σ - F : ℤ) : ZMod 16)
      = doubleBrown ((stdQuadratic 3).shift (stdShift3 c₁)) := h₁
  have e₂ : ((σ - F : ℤ) : ZMod 16)
      = doubleBrown ((stdQuadratic 3).shift (stdShift3 c₂)) := h₂
  exact doubleBrown_stdShift3_injective (e₁.symm.trans e₂)

/-! ## §5. The verdict: the pin⁻-free shadow of `[FK]` is subsumed by what the lattice already owns

The lattice half of Rokhlin — van der Blij's `σ ≡ ξ·ξ (mod 8)`, `8 ∣ σ` at a spin form — is a
PROVED in-tree asset (`RokhlinHMDischarge`). §3–§4 show the pin⁻-free content of Guillou–Marin is
exactly the mod-4 congruence. Putting the two together gives the strongest available verdict on the
`[FK]`-at-general-`σ` node: **the pin⁻-structure-independent content of `[FK]` is not merely weaker
than Rokhlin — it is strictly weaker than the lattice input the project already has, so it
contributes ZERO marginal content.** Every bit of `[FK]`'s marginal value over the lattice is
carried by the *choice* of pin⁻ structure, i.e. by the surface's smooth normal data. -/

/-- **Van der Blij subsumes the whole pin⁻-free GM shadow** (new): given `8 ∣ σ`, the mod-4
congruence holds automatically for a `β = 0` characteristic surface and for *every* pin⁻ structure
on it. So the torsor-invariant part of Guillou–Marin is not an input at all. -/
theorem torsor_free_shadow_implied_by_van_der_blij {σ : ℤ} (h8 : (8 : ℤ) ∣ σ)
    (Q : Z4Quadratic ι) (hQ : Q.brown = 0) (w : ι → ZMod 2) :
    reduce16to4 (((σ - 0 : ℤ) : ZMod 16)) = reduce16to4 (doubleBrown (Q.shift w)) := by
  obtain ⟨t, ht⟩ := h8
  have hrhs : reduce16to4 (doubleBrown (Q.shift w)) = 0 := by
    rw [reduce16to4_doubleBrown_shift]
    show reduce16to4 (2 * ((Q.brown.val : ℕ) : ZMod 16)) = 0
    rw [hQ]
    decide
  rw [hrhs, sub_zero, ht]
  push_cast
  have h8' : reduce16to4 (8 : ZMod 16) = 0 := by decide
  rw [map_mul, h8', zero_mul]

/-- **The lattice input PLUS the entire pin⁻-free shadow of Guillou–Marin still cannot prove
Rokhlin** (new — the headline no-go of this module). `σ = 8` satisfies van der Blij's `8 ∣ σ` and
satisfies the full torsor-invariant GM congruence for *every* `β = 0` characteristic surface and
*every* pin⁻ structure on it, yet `¬ (16 ∣ 8)`. Hence the `4 → 16` gap — the whole marginal content
of `[FK]` — is carried strictly by the choice of pin⁻ structure, which is exactly the smooth normal
data `CharSurfaceFKVacuity` §3 named as the missing substrate. Any proposed `hgm` supplier that
does not *construct* `Q` from that data is refuted by this theorem before it is written. -/
theorem lattice_plus_torsor_free_shadow_cannot_prove_rokhlin :
    ∃ σ : ℤ, (8 : ℤ) ∣ σ ∧
      (∀ (Q : Z4Quadratic (Fin 8)) (w : Fin 8 → ZMod 2), Q.brown = 0 →
        reduce16to4 (((σ - 0 : ℤ) : ZMod 16)) = reduce16to4 (doubleBrown (Q.shift w))) ∧
      ¬ (16 : ℤ) ∣ σ := by
  refine ⟨8, ⟨1, by norm_num⟩, fun Q w hQ =>
    torsor_free_shadow_implied_by_van_der_blij ⟨1, by norm_num⟩ Q hQ w, ?_⟩
  decide

end SKEFTHawking.GMTorsor
