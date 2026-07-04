import Mathlib
import SKEFTHawking.BrownInvariant
import SKEFTHawking.ArfInvariant
import SKEFTHawking.PinPlusGMData

/-!
# Phase 5q.H (H8, the geometric Rokhlin discharge) — even `ZMod 4`-quadratic forms and the Arf reduction

The unconditional close of 5q.H reduces to discharging the single project-wide tracked hypothesis
`SmoothSpinManifold4.topo : 2 ∣ σ/8` — the geometric Guillou–Marin / Freedman–Kirby Arf-vanishing on a
characteristic surface. It is irreducible at the *lattice* level (E₈: `σ/8 = 1`), so it must be discharged
at the *manifold* level via the genuine characteristic surface + its `ZMod 4`-quadratic enhancement.

**This file is the algebraic foundation of that program.** For an **oriented** characteristic surface the
enhancement `q` is *even* (values in `2·ℤ/2 ⊂ ℤ/4`), and the Guillou–Marin congruence specialises to
`σ ≡ Σ·Σ + 8·Arf(q) mod 16` with the surface's Brown invariant `β = 4·Arf`. So the mod-16 story on an
oriented surface is carried by the ℤ/2 **Arf** invariant: `brown` is `2`-torsion (`∈ {0,4}`), and the
`2 ∣ σ/8` factor is `Arf = 0`. This module establishes the `2`-torsion of `brown` on even forms — the first
brick toward the geometric Arf-vanishing. Kernel-pure `{propext, Classical.choice, Quot.sound}`.
-/

open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic

namespace SKEFTHawking.Brown.Z4Quadratic

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A `ZMod 4`-quadratic form is **even** when every value lies in `2·ℤ/2 ⊂ ℤ/4` (`{0, 2}`) — the case of
an **oriented** characteristic surface (the enhancement `q` reduces to a genuine `ZMod 2`-quadratic form). -/
def IsEven (Q : Z4Quadratic ι) : Prop := ∀ x, ∃ b : ZMod 2, Q.q x = embed2 b

/-- On an even form the Gauss sum `∑ i^{q x}` has each summand `i^{even} = ±1`, hence is a **real**
integer: `gaussSum4 Q.q = ((∑ x, chi2 (b x)) : ℤ)` for the `ZMod 2`-reduction `b`. -/
lemma gaussSum4_even_isReal (Q : Z4Quadratic ι) (hE : IsEven Q) :
    (gaussSum4 Q.q).im = 0 := by
  have him : (gaussSum4 Q.q).im
      = ∑ x, (zeta4 (Q.q x)).im :=
    map_sum ({ toFun := Zsqrtd.im, map_zero' := rfl, map_add' := fun _ _ => rfl } :
      GaussianInt →+ ℤ) _ _
  rw [him]
  refine Finset.sum_eq_zero (fun x _ => ?_)
  obtain ⟨b, hb⟩ := hE x
  rw [hb, zeta4_embed2]
  unfold chi2
  split <;> decide

/-- The **ℤ/2-reduction** of a form: `toZ2 Q x = (q x).val / 2 ∈ ZMod 2`. On an *even* form it is the
genuine `ZMod 2`-quadratic form underneath (`embed2 (toZ2 Q x) = q x`), the Arf datum of an oriented surface. -/
def toZ2 (Q : Z4Quadratic ι) : (ι → ZMod 2) → ZMod 2 := fun x => (((Q.q x).val / 2 : ℕ) : ZMod 2)

/-- On an even form, `embed2 ∘ toZ2 = q` — the reduction is a genuine section (`embed2` is injective). -/
lemma embed2_toZ2_of_even (Q : Z4Quadratic ι) (hE : IsEven Q) (x : ι → ZMod 2) :
    embed2 (toZ2 Q x) = Q.q x := by
  obtain ⟨b, hb⟩ := hE x
  unfold toZ2
  rw [hb]
  clear hb
  revert b
  decide

/-- **The Gauss-sum bridge**: on an even form, the `ℤ[i]` Gauss sum `gaussSum4` is the integer cast of the
`±1` Arf Gauss sum `SKEFTHawking.Arf.gaussSum` of the `ZMod 2`-reduction `toZ2 Q`. This ties `brown` to the
`ArfInvariant` machinery (whence `brown = 4·Arf` on oriented surfaces). -/
lemma gaussSum4_even_eq_gaussSum (Q : Z4Quadratic ι) (hE : IsEven Q) :
    gaussSum4 Q.q = ((SKEFTHawking.Arf.gaussSum (toZ2 Q) : ℤ) : GaussianInt) := by
  unfold gaussSum4 SKEFTHawking.Arf.gaussSum
  push_cast
  refine Finset.sum_congr rfl (fun x _ => ?_)
  rw [← embed2_toZ2_of_even Q hE x, zeta4_embed2]
  generalize toZ2 Q x = b
  revert b
  decide

/-- On an even form `neg Q` has the same Gauss sum as `Q` (since `-q = q` pointwise: `-embed2 = embed2`),
because the (real) Gauss sum is `star`-fixed. -/
lemma gaussSum4_neg_even (Q : Z4Quadratic ι) (hE : IsEven Q) :
    gaussSum4 (neg Q).q = gaussSum4 Q.q := by
  rw [gaussSum4_neg]
  have him := gaussSum4_even_isReal Q hE
  apply Zsqrtd.ext <;> simp [him]

/-- **`brown` is `2`-torsion on even forms** (`2·brown = 0`, i.e. `brown ∈ {0,4}`): `neg Q` has the same
`brown` as `Q` (same Gauss sum, `gaussSum4_neg_even`), but `brown_neg` gives `brown(neg Q) = -brown Q`, so
`brown Q = -brown Q`. This is the oriented-surface `β = 4·Arf` statement (the mod-16 story is 2-torsion). -/
lemma brown_even_two_torsion (Q : Z4Quadratic ι) (hE : IsEven Q) : 2 * brown Q = 0 := by
  have hbU : (neg Q).brownUnit = Q.brownUnit := by
    have h1 := (neg Q).gaussSum4_eq_brownUnit
    rw [gaussSum4_neg_even Q hE, Q.gaussSum4_eq_brownUnit] at h1
    exact (zeta4_mul_pow_right_inj h1).symm
  have hbrown : brown (neg Q) = brown Q := by unfold brown; rw [hbU]
  have hneg := brown_neg Q
  rw [hbrown] at hneg
  rw [two_mul]
  nth_rewrite 1 [hneg]
  exact neg_add_cancel _

end SKEFTHawking.Brown.Z4Quadratic
