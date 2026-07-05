import Mathlib
import SKEFTHawking.IntOrientationSection
import SKEFTHawking.SingularGoodCompactInt

/-!
# The oriented integral fundamental-class existence framework (brick 18c)

The induction target for the ℤ chart-cover construction of the fundamental class `[M]` (Hatcher
3.27(b), oriented version). Where the mod-2 `SingularFundamentalClass.hasFundClass` needs no sign
data (`H₄(M|x;ℤ/2)≅ℤ/2` has a unique generator), the integral version threads an **orientation
section** `orient : M → ℤ` (valued in `{±1}`): a class `α ∈ Hₙ(M|K;ℤ)` restricts, at each `x ∈ K`,
to the ORIENTED local generator `orientedLocalGenerator x (orient x)` (brick 17c) rather than to
"the" generator. This is the honest ℤ replacement of the mod-2 `x + x = 0` collapse.

* `restrictsToOrientedGeneratorInt orient α` — the per-point oriented-generator condition on `α`.
* `hasOrientedFundClassInt orient K` — existence of such an `α` on `Hₙ(M|K;ℤ)`.
* `restrictsToOrientedGeneratorInt_relInclInt` — the sub-restriction factoring (via brick-18a
  `restrictToPointInt_relInclInt`): a witness on `K` restricts to a witness on any `K' ⊆ K`, the
  monotonicity the finite-union induction's cons step rides on.

The chart-cover induction (chartBall base → MV union → biUnion → univ) that INHABITS
`hasOrientedFundClassInt orient univ`, and the packaging into `IntOrientationData`, are downstream
bricks: the base case consumes the (in-flight) convex good-compactness + brick-18b chart transport;
the union step consumes the (in-flight) integral relative Mayer–Vietoris. This module fixes the
target's TYPE and proves the MV-free monotonicity.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.IntOrientationSection
  (orientedLocalGenerator restrictToPointInt relInclInt)

namespace SKEFTHawking.SingularIntFundamentalClassExist

variable {M : Type} [TopologicalSpace M] [T1Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]

/-- **`α` restricts to the oriented local generator on `K`** w.r.t. an orientation section `orient`:
`restrictToPointInt hx 4 α = orientedLocalGenerator x (orient x)` at every `x ∈ K`. The integral,
orientation-aware mirror of `SingularFundamentalClass.restrictsToGenerator`. -/
def restrictsToOrientedGeneratorInt (orient : M → ℤ) {K : Set M}
    (α : RelHomologyInt (X := TopCat.of M) (Kᶜ : Set ↑(TopCat.of M)) 4) : Prop :=
  ∀ (x : M) (hx : x ∈ K),
    restrictToPointInt (X := TopCat.of M) hx 4 α = orientedLocalGenerator x (orient x)

/-- **`Hₙ(M|K;ℤ)` has an oriented fundamental class** w.r.t. `orient`: some class restricts to the
oriented local generator at every point of `K`. For `K = univ` this is the oriented `[M]`. The
integral mirror of `SingularFundamentalClass.hasFundClass`. -/
def hasOrientedFundClassInt (orient : M → ℤ) (K : Set M) : Prop :=
  ∃ α : RelHomologyInt (X := TopCat.of M) (Kᶜ : Set ↑(TopCat.of M)) 4,
    restrictsToOrientedGeneratorInt orient α

/-- **Oriented-generator witnesses restrict along `K' ⊆ K`**: if `α` restricts to the oriented
generator at every point of `K`, then its `relInclInt` push to `Hₙ(M|K';ℤ)` (over `Kᶜ ⊆ K'ᶜ`)
restricts to the oriented generator at every point of `K'`. The MV-free monotonicity the finite-union
cons step consumes; proved by the brick-18a factoring lemma `restrictToPointInt_relInclInt`. -/
theorem restrictsToOrientedGeneratorInt_relInclInt (orient : M → ℤ) {K K' : Set M} (hK'K : K' ⊆ K)
    {α : RelHomologyInt (X := TopCat.of M) (Kᶜ : Set ↑(TopCat.of M)) 4}
    (hα : restrictsToOrientedGeneratorInt orient α) :
    restrictsToOrientedGeneratorInt orient
      (relInclInt (Set.compl_subset_compl.mpr hK'K) 4 α) := by
  intro x hx
  rw [SKEFTHawking.SingularGoodCompactInt.restrictToPointInt_relInclInt hK'K hx 4 α]
  exact hα x (hK'K hx)

end SKEFTHawking.SingularIntFundamentalClassExist
