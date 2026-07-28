/-
# The repair of the `IntOrientation` scale defect: a PRIMITIVE fundamental class

`IntOrientationScaling` showed that `IntOrientation` is too weak to be a fundamental class:
`redCompat` admits `n • [M]` for every odd `n`, and the scaled classes destroy every nondegeneracy
statement (`not_forall_intOrientation_isUnimodular`). That is not a defect one routes around — it
means **the orientation an in-tree producer hands you might be `3 • [K3]`, for which integral
Poincaré duality is simply FALSE.** Pinning the orientation (`KummerK3E1Repair` §2) fixes the
quantifier; it does not fix the datum. This module fixes the datum.

## The added field

    IsPrimitiveClass c  :=  ∀ (k : ℤ) (d), c = k • d → IsUnit k

`IntOrientationPrimitive M` is `IntOrientation M` plus `IsPrimitiveClass fundClass`. Primitivity is
the standard "is not a proper multiple" condition, and it is exactly what the scale defect violates:

* `not_isPrimitiveClass_smulOdd` — `n • c` is never primitive for `|n| ≥ 2`, so
  `IntOrientation.smulOdd` **does not lift** to this structure. The repair bites.
* `IntOrientationPrimitive.reverse` — reversal **does** lift. The sign ambiguity is a real feature of
  orientations and survives, exactly as it should; a strengthening that killed it would be wrong.

## It costs nothing to produce

The degree-4 producer already picks a **basis vector** of the free module `H₄(M;ℤ)`, and a basis
vector is primitive for the same coordinate-comparison reason that made it non-2-divisible
(`exists_isPrimitiveClass` generalizes `IntOrientationFreeTopHomology.exists_not_two_smul` from `2`
to arbitrary `k`). So `nonempty_intOrientationPrimitive_of_free_nontrivial` has *precisely* the
hypotheses of the unstrengthened `nonempty_intOrientation_of_free_nontrivial`: free and nontrivial
top integral homology on a closed connected charted 4-manifold. Nothing was given away by shipping
the weaker structure, and nothing is owed for the stronger one.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.IntOrientationScaling
import SKEFTHawking.IntOrientationFreeTopHomology

namespace SKEFTHawking.IntOrientationPrimitive

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.IntOrientationReverse
open SKEFTHawking.IntOrientationScaling
open SKEFTHawking.IntOrientationFreeTopHomology

/-! ## §1. Primitivity -/

/-- **A class is PRIMITIVE when it is not a proper multiple.** The standard condition; `c = 1 • c`
makes it non-vacuous, and it forces `c ≠ 0` (else `c = 2 • 0`). -/
def IsPrimitiveClass {N : Type*} [AddCommGroup N] (c : N) : Prop :=
  ∀ (k : ℤ) (d : N), c = k • d → IsUnit k

theorem IsPrimitiveClass.ne_zero {N : Type*} [AddCommGroup N] {c : N} (h : IsPrimitiveClass c) :
    c ≠ 0 := by
  intro hc
  have := h 2 0 (by simp [hc])
  rw [Int.isUnit_iff] at this
  omega

/-- **Primitive ⟹ not 2-divisible** — the input the degree-4 orientation route consumes. -/
theorem IsPrimitiveClass.not_two_smul {N : Type*} [AddCommGroup N] {c : N}
    (h : IsPrimitiveClass c) (d : N) : c ≠ (2 : ℤ) • d := by
  intro hd
  have := h 2 d hd
  rw [Int.isUnit_iff] at this
  omega

/-- **THE SCALE DEFECT IS CLOSED.** For `|k| ≥ 2`, `k • d` is never primitive — witnessed by itself.
So `IntOrientation.smulOdd` at `n = 3` (the construction that refutes every `∀ o` unimodularity
claim) does **not** lift to `IntOrientationPrimitive`. -/
theorem not_isPrimitiveClass_smul {N : Type*} [AddCommGroup N] {k : ℤ} (hk : 2 ≤ k.natAbs)
    (d : N) : ¬ IsPrimitiveClass (k • d) := by
  intro h
  have := h k d rfl
  rw [Int.isUnit_iff] at this
  omega

/-- **A nontrivial free `ℤ`-module has a primitive element** — a basis vector. If `b i = k • d`,
comparing `i`-th coordinates gives `1 = k * (b.repr d) i`, so `k` is a unit. Generalizes
`IntOrientationFreeTopHomology.exists_not_two_smul` from `k = 2` to every `k`. -/
theorem exists_isPrimitiveClass {N : Type*} [AddCommGroup N] [Module.Free ℤ N] [Nontrivial N] :
    ∃ c : N, IsPrimitiveClass c := by
  classical
  set b := Module.Free.chooseBasis ℤ N with hb
  obtain ⟨x, hx⟩ := exists_ne (0 : N)
  have hrx : b.repr x ≠ 0 := fun h => hx (by simpa using congrArg b.repr.symm h)
  obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hrx
  refine ⟨b i, fun k d hd => ?_⟩
  have hcoord := congrArg (fun y => (b.repr y) i) hd
  simp only [Module.Basis.repr_self, Finsupp.single_eq_same, map_smul, Finsupp.smul_apply,
    smul_eq_mul] at hcoord
  exact Int.isUnit_iff.mpr (Int.eq_one_or_neg_one_of_mul_eq_one hcoord.symm)

/-! ## §2. The strengthened orientation datum -/

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]

/-- **AN INTEGRAL ORIENTATION WHOSE FUNDAMENTAL CLASS IS PRIMITIVE.** The datum `IntOrientation` was
supposed to be — `redCompat` alone lets in every odd multiple. -/
structure IntOrientationPrim (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M]
    [Nonempty M] [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M] extends IntOrientation M where
  /-- The fundamental class is not a proper multiple. -/
  primitive : IsPrimitiveClass toIntOrientation.fundClass

/-- **Reversal LIFTS.** `−c = k • d ⟹ c = k • (−d)`, so primitivity is sign-symmetric — the
orientation-reversal ambiguity is genuine and is *not* removed by this strengthening (it must not be:
a closed orientable manifold really does have two orientations). -/
noncomputable def IntOrientationPrim.reverse (o : IntOrientationPrim M) :
    IntOrientationPrim M where
  toIntOrientation := IntOrientation.reverse o.toIntOrientation
  primitive := by
    intro k d hd
    refine o.primitive k (-d) ?_
    have : -o.fundClass = k • d := hd
    rw [smul_neg, ← this, neg_neg]

@[simp] theorem reverse_fundClass (o : IntOrientationPrim M) :
    (IntOrientationPrim.reverse o).toIntOrientation.fundClass = -o.toIntOrientation.fundClass := rfl

/-- **Scaling does NOT lift** — the concrete form of `not_isPrimitiveClass_smul` at the construction
that broke `∀ o`. -/
theorem not_isPrimitiveClass_smulOdd (o : IntOrientation M) {n : ℤ} (hn : Odd n)
    (hn2 : 2 ≤ n.natAbs) :
    ¬ IsPrimitiveClass (IntOrientation.smulOdd o hn).fundClass :=
  not_isPrimitiveClass_smul hn2 o.fundClass

/-! ## §3. The producer — same hypotheses as the unstrengthened one -/

variable [PreconnectedSpace M]

/-- **THE STRENGTHENED DEGREE-4 ORIENTATION CRITERION.** Free, nontrivial `H₄(M;ℤ)` on a closed
connected charted 4-manifold produces an orientation whose fundamental class is **primitive** — the
same hypotheses as `IntOrientationFreeTopHomology.nonempty_intOrientation_of_free_nontrivial`,
because that proof was already choosing a basis vector. -/
theorem nonempty_intOrientationPrim_of_free_nontrivial
    [Module.Free ℤ (Homology (TopCat.of M) 4)] [Nontrivial (Homology (TopCat.of M) 4)] :
    Nonempty (IntOrientationPrim M) := by
  obtain ⟨c, hc⟩ := exists_isPrimitiveClass (N := Homology (TopCat.of M) 4)
  exact ⟨{ fundClass := c
           redCompat := eq_fundamentalClass_of_ne_zero (m := 2)
             (redHomology_ne_zero_of_not_two_smul (X := TopCat.of M) 3 c hc.not_two_smul)
           primitive := hc }⟩

end SKEFTHawking.IntOrientationPrimitive
