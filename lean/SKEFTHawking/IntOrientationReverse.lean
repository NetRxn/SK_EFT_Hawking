/-
# Orientation reversal is an `IntOrientation`, and what that costs a `∀ o` hypothesis

`IntOrientation M` carries exactly two fields: the integral fundamental class `[M] ∈ H₄(M;ℤ)` and
`redCompat`, tying its mod-2 reduction to the canonical (orientation-free) mod-2 class.

**`redCompat` does NOT pin a sign.** Reduction is additive and the target has characteristic 2, so
`red(−[M]) = −red([M]) = red([M])`. Hence `−[M]` satisfies `redCompat` whenever `[M]` does, and
`IntOrientation.reverse` below is a genuine second orientation on the same manifold.

## Why this matters for `∀ o`-quantified geometric hypotheses

The intersection form is **linear in the fundamental class** (`interFormInt fc a b = fc.eval (a ∪ b)`
and `intFundamentalClassOfHomology` is `⟨·, zM⟩`), so reversal negates it. Therefore a hypothesis of
the shape

    ∀ o : IntOrientation M, ∃ v, ∀ i j, interFormInt (fundClass o) (v i) (v j) = G i j

applied at `o` **and** at `o.reverse` yields, *from the single orientation `o`*, families realizing
both `G` and `−G` (`exists_family_neg_of_forall_orientation`). For a `G` that is not equivalent to
`−G` — e.g. a definite or mixed-signature Gram whose negative has a different signature — that is a
strong constraint on the shape, and it is invisible until the reversal is written down.

⚠ **SCOPE — stated precisely.** This module proves the *consequence*, not unsatisfiability. Deriving
an actual contradiction for a specific `G` needs a signature/rank argument about the ambient form,
which is **not** done here. What is proved is that the `∀ o` form silently demands `−G` too.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.IntFundamentalClassOrientation
import SKEFTHawking.SingularIntersectionFormInt

namespace SKEFTHawking.IntOrientationReverse

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularCohomologyInt

noncomputable section

/-- **Mod-2 reduction cannot see a sign.** The target is a `ZMod 2`-module, so `−x = x`. -/
theorem neg_eq_self_mod2 {M : Type} [TopologicalSpace M]
    (x : SKEFTHawking.SingularHomologyMod2.Homology (TopCat.of M) 4) : -x = x := by
  rw [← neg_one_smul (ZMod 2) x, show (-1 : ZMod 2) = 1 from by decide, one_smul]

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]

/-- **THE REVERSED ORIENTATION.** `−[M]` satisfies `redCompat` because reduction is additive and the
mod-2 target has characteristic 2. So `IntOrientation M` is never a subsingleton once inhabited by a
class with `[M] ≠ −[M]`. -/
def IntOrientation.reverse (o : IntOrientation M) : IntOrientation M where
  fundClass := -o.fundClass
  redCompat := by
    rw [map_neg, o.redCompat, neg_eq_self_mod2]

@[simp] theorem reverse_fundClass (o : IntOrientation M) :
    (IntOrientation.reverse o).fundClass = -o.fundClass := rfl

/-- **Reversal negates the intersection form.** Immediate from linearity of the Kronecker pairing in
the homology slot. -/
theorem interFormInt_reverse_orientation (o : IntOrientation M) (a b : Cohomology (TopCat.of M) 2) :
    interFormInt (intFundamentalClassOfIntOrientation (IntOrientation.reverse o)) a b
      = - interFormInt (intFundamentalClassOfIntOrientation o) a b := by
  show ((kroneckerHInt 4).flip (-o.fundClass)) (cupH24 a b)
      = - ((kroneckerHInt 4).flip o.fundClass) (cupH24 a b)
  simp only [LinearMap.flip_apply, map_neg, LinearMap.neg_apply]

/-- **THE COST OF `∀ o`.** A Gram-realization hypothesis quantified over *all* orientations delivers,
from the single orientation `o`, a family realizing `−G` as well. Anything asserting `∀ o` a fixed
`G` is therefore silently asserting that `−G` is realizable too. -/
theorem exists_family_neg_of_forall_orientation {ι : Type*} {G : ι → ι → ℤ}
    (hfam : ∀ o : IntOrientation M, ∃ v : ι → Cohomology (TopCat.of M) 2,
      ∀ i j, interFormInt (intFundamentalClassOfIntOrientation o) (v i) (v j) = G i j)
    (o : IntOrientation M) :
    ∃ v : ι → Cohomology (TopCat.of M) 2,
      ∀ i j, interFormInt (intFundamentalClassOfIntOrientation o) (v i) (v j) = -G i j := by
  obtain ⟨v, hv⟩ := hfam (IntOrientation.reverse o)
  refine ⟨v, fun i j => ?_⟩
  have := hv i j
  rw [interFormInt_reverse_orientation] at this
  omega

/-- **The diagonal form of the same cost**, in the shape the `⟨−2⟩¹⁶` block uses: a `∀ o` hypothesis
pinning a diagonal entry to `d` also pins it to `−d`. Instantiated at `d = −2` this is exactly the
E-block's tension. -/
theorem exists_diag_neg_of_forall_orientation {ι : Type*} {G : ι → ι → ℤ}
    (hfam : ∀ o : IntOrientation M, ∃ v : ι → Cohomology (TopCat.of M) 2,
      ∀ i j, interFormInt (intFundamentalClassOfIntOrientation o) (v i) (v j) = G i j)
    (o : IntOrientation M) (i : ι) :
    ∃ v : ι → Cohomology (TopCat.of M) 2,
      interFormInt (intFundamentalClassOfIntOrientation o) (v i) (v i) = -G i i := by
  obtain ⟨v, hv⟩ := exists_family_neg_of_forall_orientation hfam o
  exact ⟨v, hv i i⟩

end

end SKEFTHawking.IntOrientationReverse
