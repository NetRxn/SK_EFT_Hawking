import Mathlib
import SKEFTHawking.BrownInvariant

/-!
# Phase 5q.H (H3 enhancement algebra) — reindexing a `ZMod 4`-quadratic form along a domain equivalence

The first 5q.H enhancement-algebra brick toward the Guillou–Marin carrier `pinPlusGMData`. The carrier's
`sumStr` composes two characteristic-surface enhancements by `orthSum` (over `Fin m ⊕ Fin n`) but the
carrier fixes the enhancement domain to a single `Fin (m+n)`; `Z4Quadratic.reindex` transports the form
along `Fin m ⊕ Fin n ≃ Fin (m+n)`, and `reindex_brown` shows the Brown invariant is unchanged (the Gauss
sum is invariant under a domain bijection, and `Fintype.card` is preserved by the equivalence).

Kernel-pure `{propext, Classical.choice, Quot.sound}` — pure `Z4Quadratic` algebra over `BrownInvariant`.
-/

open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic

namespace SKEFTHawking.Brown.Z4Quadratic

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- **Reindexing a `ZMod 4`-quadratic form along a domain equivalence** `e : ι ≃ κ`. The form on
`κ → ZMod 2` is `x ↦ Q.q (x ∘ e)`; all axioms transport, since `x ↦ x ∘ e` is a bijection of
`κ → ZMod 2` with `ι → ZMod 2`. -/
def reindex (Q : Z4Quadratic ι) (e : ι ≃ κ) : Z4Quadratic κ where
  q := fun x => Q.q (fun i => x (e i))
  B := fun x y => Q.B (fun i => x (e i)) (fun i => y (e i))
  refine' := fun x y => Q.refine' _ _
  B_add_left := fun x y z => Q.B_add_left _ _ _
  B_symm := fun x y => Q.B_symm _ _
  nondeg := fun x hx => by
    have h0 : (fun i => x (e i)) = 0 := Q.nondeg _ (fun y => by
      have := hx (fun k => y (e.symm k))
      simpa [Equiv.apply_symm_apply] using this)
    funext k
    have := congrFun h0 (e.symm k)
    simpa [Equiv.apply_symm_apply] using this

/-- The Gauss sum is invariant under reindexing (a domain bijection permutes the sum). -/
lemma gaussSum4_reindex (Q : Z4Quadratic ι) (e : ι ≃ κ) :
    gaussSum4 (Q.reindex e).q = gaussSum4 Q.q :=
  (Fintype.sum_equiv (Equiv.arrowCongr e (Equiv.refl (ZMod 2)))
    (fun x' => zeta4 (Q.q x')) (fun x => zeta4 ((Q.reindex e).q x))
    (fun x' => by simp [reindex, Equiv.arrowCongr_apply, Equiv.symm_apply_apply])).symm

/-- The Brown-phase unit is invariant under reindexing. -/
lemma brownUnit_reindex (Q : Z4Quadratic ι) (e : ι ≃ κ) :
    (Q.reindex e).brownUnit = Q.brownUnit := by
  have hcard : Fintype.card κ = Fintype.card ι := (Fintype.card_congr e).symm
  have h := (Q.reindex e).gaussSum4_eq_brownUnit
  rw [gaussSum4_reindex, Q.gaussSum4_eq_brownUnit, hcard] at h
  exact (zeta4_mul_pow_right_inj h).symm

/-- **The Brown invariant is invariant under reindexing** — the enhancement's ABK value depends only on
the isometry class of the form, not on the chosen basis/index of `H₁(Σ;ℤ/2)`. -/
@[simp] lemma reindex_brown (Q : Z4Quadratic ι) (e : ι ≃ κ) :
    (Q.reindex e).brown = Q.brown := by
  have hcard : Fintype.card κ = Fintype.card ι := (Fintype.card_congr e).symm
  simp only [brown, brownUnit_reindex, hcard]

end SKEFTHawking.Brown.Z4Quadratic
