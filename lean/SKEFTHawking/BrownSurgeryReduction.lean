/-
# Phase 5q.H (E2 · enhanced-circle layer) — the SURGERY move at the enhancement level

The per-circle algebra Taylor's Theorem 1.1 proof needs (`Lit-Search/Phase-5qH/
ABK_injectivity_routes_lemma_DAG_20260703.md` items A2/A4/A5; `GM_structure_ABK_invariant_
normalizations_20260703.md` §1/§2), all DERIVED kernel-pure — no freeze required at this level:

* **Polarization arithmetic** (DR §1: *"q(x) ≡ x•x mod 2 follows from the axiom with y = x"*):
  `embed2_B_self` (`embed2 (B x x) = 2·q x`), `embed2` injectivity, and `Z4Quadratic.ext`
  (the enhancement determines its polar form).
* **The torsor action** `shift` (KT-LMS §3 / DG Thm 3.12: *"q_γ(x) = q(x) + 2γ(x)"*), with the
  acting `H¹`-functional expressed through the nondegenerate polar form as `B w ·` — `w` is the
  Poincaré dual `y ∩ [F]` of **KT-LMS Lemma 3.7** (Taylor `0802.0111` p. 3, verbatim: *"if the
  Pin⁻-structure is changed by y ∈ H¹(F;ℤ/2), then β changes by 2·q(y ∩ [F])"*). Because the
  `∩[F]` ingredient IS expressible here, Lemma 3.7 needs no statement freeze: `brown_shift` PROVES
  it (in this project's GL/FK β-sign, dual to KT's: `β(shift w Q) + 2·q(w) = β(Q)`).
* **The surgery move** (Taylor `0802.0111` Lemma 1.2's extendable case `q(S¹) = 0`): passing to the
  isotropic reduction. `pairComplement` is the `B`-complement `W` of the surgery pair `(x, z)`
  (`B x z = 1`); `gaussSum4_eq_two_mul` is the 2-dim split-piece computation `gaussSum(H) = 2`
  (`H = span{x,z}`, `q x = 0`, any partner value); `SurgeryReduction` is the reduction datum; and
  `brown_surgeryReduction` — **the Brown invariant is unchanged by a single isotropic reduction** —
  is the algebra core of Taylor Theorem 1.1's surgery induction. `surgeryPiece` is the concrete
  2-dim model (Gauss sum `2`, `brown = 0` for every partner value `c`).

Sign/convention anchors (falsifiability): `brown_shift_rp2` — shifting the `ℝP²` generator form by
the generator class exchanges the two enhancements (`q(gen): 1 ↦ 3`) and sends `β = 1 ↦ 7 = -1`
(DG Example 3.17; the §5 reversal on `ℝP²`, matching the in-tree `brown_neg`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.BrownInvariant
import SKEFTHawking.BrownMetabolic

namespace SKEFTHawking.Brown.Z4Quadratic

open SKEFTHawking.Brown
open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι] (Q : Z4Quadratic ι)

/-! ## Polarization arithmetic -/

/-- `embed2 : ZMod 2 → ZMod 4` (`{0,1} ↦ {0,2}`) is injective. -/
lemma embed2_injective : Function.Injective embed2 := by decide

/-- The image of `embed2` is 2-torsion: `embed2 b + embed2 b = 0` in `ZMod 4`. -/
lemma embed2_add_self (b : ZMod 2) : embed2 b + embed2 b = 0 := by revert b; decide

/-- **`q(x) ≡ x•x (mod 2)`** (DR §1, derived from the enhancement axiom at `y = x`):
`embed2 (B x x) = 2·q(x)`. The self-pairing is the mod-2 shadow of the enhancement value. -/
lemma embed2_B_self (x : ι → ZMod 2) : embed2 (Q.B x x) = 2 * Q.q x := by
  have hxx : x + x = 0 := by
    funext i
    have h2 : ∀ a : ZMod 2, a + a = 0 := by decide
    exact h2 (x i)
  have h := Q.refine' x x
  rw [hxx, Q.q_zero] at h
  have key : ∀ a b : ZMod 4, (0 : ZMod 4) = a + a + b → b = 2 * a := by decide
  exact key _ _ h

/-- A class with vanishing enhancement value is `B`-isotropic (Lemma 1.2's trivial-normal-bundle
shadow: `q(S¹) = 0 ⟹ S¹•S¹ = 0`). -/
lemma B_self_eq_zero_of_q_eq_zero {x : ι → ZMod 2} (hx : Q.q x = 0) : Q.B x x = 0 :=
  embed2_injective (by rw [Q.embed2_B_self x, hx, mul_zero]; decide)

/-- **The enhancement determines the whole datum**: two `Z4Quadratic`s with the same `q` are equal
(the polar form is recovered by polarization, `embed2` injectivity; the axioms are proofs). -/
protected theorem ext {Q₁ Q₂ : Z4Quadratic ι} (h : Q₁.q = Q₂.q) : Q₁ = Q₂ := by
  have hB : Q₁.B = Q₂.B := by
    funext v w
    apply embed2_injective
    have e₁ : embed2 (Q₁.B v w) = Q₁.q (v + w) - Q₁.q v - Q₁.q w := by rw [Q₁.refine' v w]; ring
    have e₂ : embed2 (Q₂.B v w) = Q₂.q (v + w) - Q₂.q v - Q₂.q w := by rw [Q₂.refine' v w]; ring
    rw [e₁, e₂, h]
  cases Q₁; cases Q₂
  cases h; cases hB
  rfl

/-! ## The torsor action `shift` and KT-LMS Lemma 3.7 (PROVEN) -/

/-- **The enhancement torsor action** (KT-LMS §3 / DG Thm 3.12: `q_γ(x) = q(x) + 2γ(x)`): change
the Pin⁻ structure by the `H¹(F;ℤ/2)`-class whose Poincaré dual (through the nondegenerate
intersection form — every functional is `B w ·` for a unique `w`) is `w`. The polar form is
unchanged; `w` plays the role of `y ∩ [F]` in KT-LMS Lemma 3.7. -/
def shift (w : ι → ZMod 2) : Z4Quadratic ι where
  q v := Q.q v + embed2 (Q.B w v)
  B := Q.B
  refine' x y := by
    show Q.q (x + y) + embed2 (Q.B w (x + y))
        = Q.q x + embed2 (Q.B w x) + (Q.q y + embed2 (Q.B w y)) + embed2 (Q.B x y)
    rw [Q.refine', Q.B_add_right, embed2_add]
    ring
  B_add_left := Q.B_add_left
  B_symm := Q.B_symm
  nondeg := Q.nondeg

@[simp] lemma shift_q (w v : ι → ZMod 2) : (Q.shift w).q v = Q.q v + embed2 (Q.B w v) := rfl

@[simp] lemma shift_B (w : ι → ZMod 2) : (Q.shift w).B = Q.B := rfl

/-- Shifting by the zero class is the identity (torsor unit). -/
@[simp] lemma shift_zero : Q.shift 0 = Q :=
  Z4Quadratic.ext (funext fun v => by
    rw [shift_q, Q.B_zero_left, show embed2 (0 : ZMod 2) = 0 from by decide, add_zero])

/-- Shifting twice by the same class returns the original enhancement (the `H¹(F;ℤ/2)`-torsor is
2-torsion). -/
@[simp] lemma shift_shift (w : ι → ZMod 2) : (Q.shift w).shift w = Q :=
  Z4Quadratic.ext (funext fun v => by
    rw [shift_q, shift_q, shift_B, add_assoc, embed2_add_self, add_zero])

/-- The Gauss sum of the shifted enhancement: `G(q + 2·B(w,·)) = ζ₄^{3·q(w)} · G(q)` (shift-reindex
by `w`; the cross terms cancel by 2-torsion and `embed2 (B w w) = 2·q(w)`). -/
lemma gaussSum4_shift (w : ι → ZMod 2) :
    gaussSum4 (Q.shift w).q = zeta4 (3 * Q.q w) * gaussSum4 Q.q := by
  unfold gaussSum4
  have hre : ∑ v, zeta4 ((Q.shift w).q v) = ∑ u, zeta4 ((Q.shift w).q (u + w)) :=
    (Equiv.sum_comp (Equiv.addRight w) (fun v => zeta4 ((Q.shift w).q v))).symm
  rw [hre, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun u _ => ?_)
  rw [← zeta4_add]
  congr 1
  rw [shift_q, Q.refine' u w, Q.B_add_right, embed2_add, Q.B_symm w u]
  linear_combination embed2_add_self (Q.B u w) + Q.embed2_B_self w

/-- The Brown-phase unit of the shifted enhancement: `brownUnit(shift w Q) = brownUnit(Q) + 3·q(w)`. -/
lemma brownUnit_shift (w : ι → ZMod 2) :
    (Q.shift w).brownUnit = Q.brownUnit + 3 * Q.q w := by
  have h := (Q.shift w).gaussSum4_eq_brownUnit
  rw [gaussSum4_shift, Q.gaussSum4_eq_brownUnit, ← mul_assoc, ← zeta4_add] at h
  have h2 := zeta4_mul_pow_right_inj h
  rw [← h2]; ring

/-- **KT-LMS Lemma 3.7, PROVEN at the enhancement level** (Taylor `0802.0111` p. 3, verbatim: *"if
the Pin⁻-structure is changed by y ∈ H¹(F;ℤ/2), then β changes by 2·q(y ∩ [F])"*). Here `w` is the
Poincaré dual `y ∩ [F]` (expressible because `B` is nondegenerate), and this project's β-sign is
GL/FK — dual to KT's (`β_KT = -β`, documented convention hazard, GM-normalizations report §2) — so
the change enters as `β(shift w Q) + 2·q(w) = β(Q)`. Falsifiable anchor: `brown_shift_rp2`. -/
theorem brown_shift (w : ι → ZMod 2) :
    (Q.shift w).brown + 2 * ((Q.q w).val : ZMod 8) = Q.brown := by
  unfold brown
  rw [Q.brownUnit_shift w]
  generalize Q.brownUnit = bU
  generalize Q.q w = a
  generalize ((Fintype.card ι : ℕ) : ZMod 8) = d
  revert bU a d; decide

/-- **The two `ℝP²` enhancements are torsor translates** (DG Example 3.17): shifting the generator
form (`q(gen) = 1`, `β = 1`) by the generator class gives the other enhancement (`q(gen) = 3`),
with `β = 7 = -1` — the §5 reversal on `ℝP²`, consistent with `brown_neg`. -/
theorem brown_shift_rp2 : ((stdQuadratic 1).shift 1).brown = 7 := by
  have h := (stdQuadratic 1).brown_shift 1
  rw [brown_stdQuadratic] at h
  have hq : (stdQuadratic 1).q 1 = 1 := by decide
  rw [hq, show (((1 : ZMod 4)).val : ZMod 8) = 1 from by decide] at h
  rw [eq_sub_of_add_eq h]
  decide

/-! ## The surgery pair complement and the split Gauss-sum computation -/

/-- `B x 0 = 0` (right zero, from symmetry and left additivity). -/
lemma B_zero_right (x : ι → ZMod 2) : Q.B x 0 = 0 := by
  rw [Q.B_symm]; exact Q.B_zero_left x

/-- **The surgery-pair complement** `W = {v | B x v = 0 ∧ B z v = 0}`: the `B`-orthogonal
complement of the surgery pair `(x, z)` (circle class and transverse partner, `B x z = 1`). The
ambient space splits as `W ⊥ span{x,z}`, and `W` is the enhancement space of the SURGERED surface
(Taylor Lemma 1.2's isotropic reduction). -/
def pairComplement (x z : ι → ZMod 2) : Submodule (ZMod 2) (ι → ZMod 2) where
  carrier := {v | Q.B x v = 0 ∧ Q.B z v = 0}
  add_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    exact ⟨by rw [Q.B_add_right, ha1, hb1, add_zero],
      by rw [Q.B_add_right, ha2, hb2, add_zero]⟩
  zero_mem' := ⟨Q.B_zero_right x, Q.B_zero_right z⟩
  smul_mem' := by
    intro c v hv
    have hc : c = 0 ∨ c = 1 := by revert c; decide
    rcases hc with rfl | rfl
    · rw [zero_smul]; exact ⟨Q.B_zero_right x, Q.B_zero_right z⟩
    · rw [one_smul]; exact hv

@[simp] lemma mem_pairComplement {x z v : ι → ZMod 2} :
    v ∈ Q.pairComplement x z ↔ Q.B x v = 0 ∧ Q.B z v = 0 := Iff.rfl

instance (x z : ι → ZMod 2) : DecidablePred (· ∈ Q.pairComplement x z) := fun v =>
  decidable_of_iff (Q.B x v = 0 ∧ Q.B z v = 0) (Q.mem_pairComplement).symm

/-- `ζ₄² = -1`. -/
lemma zeta4_two : zeta4 2 = -1 := by decide

/-- **The split Gauss-sum computation** (the 2-dim split-piece `gaussSum(H) = 2` in intrinsic
form): for an isotropic class `x` (`q x = 0`) with a transverse partner `z` (`B x z = 1`),
`G(Q) = 2 · ∑_{w ∈ W} ζ₄^{q(w)}` over the pair complement `W`. Proof: the fiber `B x v = 1` is
killed by the sign-flipping involution `v ↦ v + x` (`q(v+x) = q(v) + 2` there), and on the kernel
fiber the same involution is a value-preserving bijection between `B z v = 1` and `W`. -/
theorem gaussSum4_eq_two_mul {x z : ι → ZMod 2} (hx : Q.q x = 0) (hxz : Q.B x z = 1) :
    gaussSum4 Q.q = 2 * ∑ w : Q.pairComplement x z, zeta4 (Q.q w) := by
  classical
  have hBxx : Q.B x x = 0 := Q.B_self_eq_zero_of_q_eq_zero hx
  -- q is invariant under `· + x` on the kernel fiber, and shifts by 2 off it
  have hqshift : ∀ v : ι → ZMod 2, Q.q (v + x) = Q.q v + embed2 (Q.B x v) := by
    intro v
    rw [Q.refine' v x, hx, add_zero, Q.B_symm v x]
  -- Step B: the fiber `B x v = 1` sums to zero
  have hT : ∑ v ∈ Finset.univ.filter (fun v => Q.B x v = 1), zeta4 (Q.q v) = 0 := by
    set T := Finset.univ.filter (fun v => Q.B x v = 1) with hTdef
    set S := ∑ v ∈ T, zeta4 (Q.q v) with hS
    have hmem : ∀ v : ι → ZMod 2, v ∈ T ↔ v + x ∈ T := by
      intro v
      simp only [hTdef, Finset.mem_filter, Finset.mem_univ, true_and, Q.B_add_right, hBxx,
        add_zero]
    have key : S = -S := by
      calc S = ∑ v ∈ T, zeta4 (Q.q (v + x)) :=
            (Finset.sum_equiv (Equiv.addRight x) (fun v => by
                simpa [Equiv.coe_addRight] using hmem v)
              (fun v hv => by simp [Equiv.coe_addRight])).symm
        _ = ∑ v ∈ T, -zeta4 (Q.q v) := by
            refine Finset.sum_congr rfl (fun v hv => ?_)
            have hv1 : Q.B x v = 1 := by
              simpa [hTdef, Finset.mem_filter] using hv
            rw [hqshift v, hv1, show embed2 (1 : ZMod 2) = 2 from by decide, zeta4_add,
              zeta4_two]
            ring
        _ = -S := by rw [hS, Finset.sum_neg_distrib]
    have h2 : (2 : GaussianInt) * S = 0 := by linear_combination key
    rcases mul_eq_zero.mp h2 with h | h
    · exact absurd h (by decide)
    · exact h
  -- Step C/D: on the kernel fiber, `· + x` is a value-preserving bijection S2 ≃ W
  have hS2 : ∑ v ∈ Finset.univ.filter (fun v => Q.B x v = 0 ∧ Q.B z v = 1), zeta4 (Q.q v)
      = ∑ v ∈ Finset.univ.filter (fun v => Q.B x v = 0 ∧ Q.B z v = 0), zeta4 (Q.q v) := by
    refine Finset.sum_equiv (Equiv.addRight x) (fun v => ?_) (fun v hv => ?_)
    · simp only [Equiv.coe_addRight, Finset.mem_filter, Finset.mem_univ, true_and,
        Q.B_add_right, hBxx, add_zero, Q.B_symm z x, hxz]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨h1, by rw [h2]; decide⟩
      · rintro ⟨h1, h2⟩
        refine ⟨h1, ?_⟩
        have : ∀ a : ZMod 2, a + 1 = 0 → a = 1 := by decide
        exact this _ h2
    · have hv0 : Q.B x v = 0 := by
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv
        exact hv.1
      simp only [Equiv.coe_addRight]
      rw [hqshift v, hv0, show embed2 (0 : ZMod 2) = 0 from by decide, add_zero]
  -- assemble
  have hsplit : gaussSum4 Q.q
      = (∑ v ∈ Finset.univ.filter (fun v => Q.B x v = 0), zeta4 (Q.q v))
        + ∑ v ∈ Finset.univ.filter (fun v => Q.B x v = 1), zeta4 (Q.q v) := by
    unfold gaussSum4
    rw [← Finset.sum_filter_add_sum_filter_not Finset.univ (fun v => Q.B x v = 0)]
    congr 1
    refine Finset.sum_congr (Finset.filter_congr (fun v _ => ?_)) (fun _ _ => rfl)
    constructor
    · intro h; revert h; generalize Q.B x v = b; revert b; decide
    · intro h; rw [h]; decide
  have hsplitK : ∑ v ∈ Finset.univ.filter (fun v => Q.B x v = 0), zeta4 (Q.q v)
      = (∑ v ∈ Finset.univ.filter (fun v => Q.B x v = 0 ∧ Q.B z v = 0), zeta4 (Q.q v))
        + ∑ v ∈ Finset.univ.filter (fun v => Q.B x v = 0 ∧ Q.B z v = 1), zeta4 (Q.q v) := by
    rw [← Finset.sum_filter_add_sum_filter_not
      (Finset.univ.filter (fun v => Q.B x v = 0)) (fun v => Q.B z v = 0), Finset.filter_filter,
      Finset.filter_filter]
    congr 1
    refine Finset.sum_congr (Finset.filter_congr (fun v _ => ?_)) (fun _ _ => rfl)
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      revert h2; generalize Q.B z v = b; revert b; decide
    · rintro ⟨h1, h2⟩
      exact ⟨h1, by rw [h2]; decide⟩
  have hW : ∑ v ∈ Finset.univ.filter (fun v => Q.B x v = 0 ∧ Q.B z v = 0), zeta4 (Q.q v)
      = ∑ w : Q.pairComplement x z, zeta4 (Q.q w) := by
    refine Finset.sum_subtype _ (fun v => ?_) (fun v => zeta4 (Q.q v))
    simp [Q.mem_pairComplement]
  rw [hsplit, hsplitK, hT, add_zero, hS2, hW]
  ring

/-! ## The surgery reduction datum and the headline invariance -/

/-- **An isotropic-reduction (surgery) datum** at the class `x`: a transverse partner `z`
(`B x z = 1`), a reduced enhancement `R` on an index type `κ`, and a linear identification `e` of
`R`'s space with the pair complement `W` under which the enhancement values agree. This is Taylor
Lemma 1.2's surgery move at the enhancement level — the Pin⁻ descent to the surgered surface. The
isotropy `q x = 0` is deliberately NOT a field: the splitting exists for any transverse pair, and
the Brown invariance (`brown_surgeryReduction`) consumes isotropy as a hypothesis, keeping Lemma
1.2's `q(S¹) = 0 ⟺` content falsifiable rather than baked in. -/
structure SurgeryReduction (x : ι → ZMod 2) where
  /-- The transverse partner of the surgered circle class. -/
  z : ι → ZMod 2
  /-- Transversality: `B x z = 1` (exists for any `x ≠ 0` by nondegeneracy). -/
  pairing : Q.B x z = 1
  /-- Index type of the reduced enhancement's basis. -/
  κ : Type
  [fκ : Fintype κ]
  [dκ : DecidableEq κ]
  /-- The reduced (surgered) enhancement. -/
  R : Z4Quadratic κ
  /-- The reduced space IS the pair complement. -/
  e : (κ → ZMod 2) ≃ₗ[ZMod 2] ↥(Q.pairComplement x z)
  /-- The enhancement descends: values agree through `e`. -/
  agree : ∀ u, R.q u = Q.q (e u)

attribute [instance] SurgeryReduction.fκ SurgeryReduction.dκ

/-- The reduced polar form agrees through `e` as well (derived — the polar form is determined by
the enhancement, so `agree` on `q` forces agreement on `B`). -/
lemma SurgeryReduction.agree_B {x : ι → ZMod 2} (S : Q.SurgeryReduction x) (u u' : S.κ → ZMod 2) :
    S.R.B u u' = Q.B (S.e u) (S.e u') := by
  apply embed2_injective
  have e₁ : embed2 (S.R.B u u') = S.R.q (u + u') - S.R.q u - S.R.q u' := by
    rw [S.R.refine' u u']; ring
  have e₂ : embed2 (Q.B (S.e u) (S.e u')) =
      Q.q ((S.e u : ι → ZMod 2) + (S.e u' : ι → ZMod 2))
        - Q.q (S.e u) - Q.q (S.e u') := by
    rw [Q.refine' (S.e u) (S.e u')]; ring
  rw [e₁, e₂, S.agree, S.agree, S.agree, map_add]
  norm_cast

/-- The Gauss sum halves across an isotropic reduction: `G(Q) = 2 · G(R)`. -/
theorem gaussSum4_surgeryReduction {x : ι → ZMod 2} (S : Q.SurgeryReduction x)
    (hx : Q.q x = 0) : gaussSum4 Q.q = 2 * gaussSum4 S.R.q := by
  rw [Q.gaussSum4_eq_two_mul hx S.pairing]
  congr 1
  exact (Fintype.sum_equiv S.e.toEquiv (fun u => zeta4 (S.R.q u))
    (fun w => zeta4 (Q.q w))
    (fun u => by simp only [LinearEquiv.coe_toEquiv]; rw [S.agree u])).symm

/-- The dimension drops by exactly `2` across an isotropic reduction (from the Gauss-sum norms). -/
lemma card_surgeryReduction {x : ι → ZMod 2} (S : Q.SurgeryReduction x) (hx : Q.q x = 0) :
    Fintype.card ι = Fintype.card S.κ + 2 := by
  have hnorm := Q.norm_gaussSum4
  rw [show gaussSum4 Q.q = 2 * gaussSum4 S.R.q from Q.gaussSum4_surgeryReduction S hx,
    Zsqrtd.norm_mul, S.R.norm_gaussSum4, show (2 : GaussianInt).norm = 4 from by decide] at hnorm
  have hnat : (2 : ℤ) ^ (Fintype.card S.κ + 2) = 2 ^ Fintype.card ι := by
    rw [← hnorm]; ring
  have h2 : (2 : ℕ) ^ (Fintype.card S.κ + 2) = 2 ^ Fintype.card ι := by exact_mod_cast hnat
  exact (Nat.pow_right_injective (le_refl 2) h2).symm

/-- The Brown-phase unit across an isotropic reduction: `brownUnit(Q) = brownUnit(R) + 3`
(`2 = ζ₄³·(1+i)²`). -/
lemma brownUnit_surgeryReduction {x : ι → ZMod 2} (S : Q.SurgeryReduction x) (hx : Q.q x = 0) :
    Q.brownUnit = S.R.brownUnit + 3 := by
  have h := Q.gaussSum4_eq_brownUnit
  rw [show gaussSum4 Q.q = 2 * gaussSum4 S.R.q from Q.gaussSum4_surgeryReduction S hx,
    S.R.gaussSum4_eq_brownUnit, Q.card_surgeryReduction S hx,
    show (2 : GaussianInt) = zeta4 3 * (1 + I) ^ 2 from by decide] at h
  have hL : zeta4 3 * (1 + I) ^ 2 * (zeta4 S.R.brownUnit * (1 + I) ^ Fintype.card S.κ)
      = zeta4 (S.R.brownUnit + 3) * (1 + I) ^ (Fintype.card S.κ + 2) := by
    rw [zeta4_add, pow_add]; ring
  rw [hL] at h
  exact (zeta4_mul_pow_right_inj h).symm

/-- **The Brown invariant is unchanged by a single isotropic reduction** — the algebra core of
Taylor `0802.0111` Theorem 1.1's surgery induction: surgering the surface along a circle with
`q(S¹) = 0` (Lemma 1.2's extendable case) descends the enhancement to the pair complement and
preserves `β`. With `BrownMetabolic.brown_eq_zero_of_metabolic` (the terminal case) this is the
complete algebra half of the bounding argument. Falsifiable: a reduction at a NON-isotropic class
shifts the Gauss-sum phase (`gaussSum4_shift` at `w = x` scales by `ζ₄^{3·q(x)} ≠ 1`), so the
isotropy hypothesis is load-bearing. -/
theorem brown_surgeryReduction {x : ι → ZMod 2} (S : Q.SurgeryReduction x) (hx : Q.q x = 0) :
    Q.brown = S.R.brown := by
  unfold brown
  rw [Q.brownUnit_surgeryReduction S hx, Q.card_surgeryReduction S hx]
  rw [show ((Fintype.card S.κ + 2 : ℕ) : ZMod 8)
    = ((Fintype.card S.κ : ℕ) : ZMod 8) + 2 from by push_cast; ring]
  generalize S.R.brownUnit = bU
  generalize ((Fintype.card S.κ : ℕ) : ZMod 8) = d
  revert bU d; decide

/-! ## The concrete 2-dimensional surgery piece -/

/-- **The 2-dimensional surgery piece** `H = span{x, z}`: the enhanced form on the surgery pair —
`q(e₀) = 0` (the isotropic circle class), `q(e₁) = c` (the partner, arbitrary value), transverse
pairing `B(e₀,e₁) = 1`, self-pairings forced by polarization (`B(e₁,e₁) = c mod 2`). -/
def surgeryPiece (c : ZMod 4) : Z4Quadratic (Fin 2) where
  q v := (v 1).val • c + embed2 (v 0 * v 1)
  B v w := v 0 * w 1 + v 1 * w 0 + (ZMod.castHom (by norm_num : (2 : ℕ) ∣ 4) (ZMod 2) c)
    * (v 1 * w 1)
  refine' := by revert c; decide
  B_add_left := by revert c; decide
  B_symm := by revert c; decide
  nondeg := by revert c; decide

/-- The surgery piece's Gauss sum is `2` for EVERY partner value `c`:
`1 + 1 + i^c + i^{c+2} = 2` (the isotropic direction kills the partner's phase). -/
theorem gaussSum4_surgeryPiece (c : ZMod 4) : gaussSum4 (surgeryPiece c).q = 2 := by
  revert c; decide

/-- The surgery piece's Brown-phase unit is `3` (`2 = ζ₄³·(1+i)²`). -/
lemma brownUnit_surgeryPiece (c : ZMod 4) : (surgeryPiece c).brownUnit = 3 := by
  have h := (surgeryPiece c).gaussSum4_eq_brownUnit
  rw [gaussSum4_surgeryPiece, Fintype.card_fin,
    show (2 : GaussianInt) = zeta4 3 * (1 + I) ^ 2 from by decide] at h
  exact (zeta4_mul_pow_right_inj h).symm

/-- **The surgery piece carries no Brown invariant**: `β(H) = 0` for every partner value. -/
theorem brown_surgeryPiece (c : ZMod 4) : (surgeryPiece c).brown = 0 := by
  unfold brown
  rw [brownUnit_surgeryPiece, Fintype.card_fin]
  decide

/-- **Split-model brown-invariance**: adjoining a surgery piece orthogonally never changes the
Brown invariant — the split-model form of `brown_surgeryReduction` (via `brown_orthSum`). -/
theorem brown_orthSum_surgeryPiece {κ : Type*} [Fintype κ] [DecidableEq κ]
    (c : ZMod 4) (R : Z4Quadratic κ) :
    ((surgeryPiece c).orthSum R).brown = R.brown := by
  rw [brown_orthSum, brown_surgeryPiece, zero_add]

end SKEFTHawking.Brown.Z4Quadratic
