import Mathlib
import SKEFTHawking.IntOrientationSection

/-!
# The integral "good compact" property (Hatcher 3.27, ℤ coefficients) — foundation (brick 18a)

The ℤ analog of the mod-2 `SKEFTHawking.SingularGoodCompact.goodCompact`. A compact `K ⊆ M` is
**good** (in degree `n`) when it is homologically well-behaved as a support: the local homology
`Hᵢ(M|K;ℤ) = Hᵢ(M, Kᶜ; ℤ)` vanishes above `n` (`vanishAboveInt`) and a degree-`n` class is
**determined by its point-restrictions** (`determinedByPointsInt`). Both halves are the exact integer
mirrors of the mod-2 definitions in `SingularManifoldFundamentalClass`; the point-restriction map is the
`restrictToPointInt` built in brick 17c (`IntOrientationSection`).

This module carries the MV-**independent** core: the three definitions and the point-restriction
factoring lemma (`restrictToPointInt_relInclInt`, the ℤ mirror of `restrictToPoint_relIncl`). The
union-closure `goodCompactInt_union`/`_biUnion` — which needs the integral relative Mayer–Vietoris
diagonal-injectivity — is a downstream brick built on the integral relative-MV foundation.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.IntOrientationSection (relInclInt relInclInt_trans restrictToPointInt)

namespace SKEFTHawking.SingularGoodCompactInt

variable {X : TopCat}

/-- **Integral high-degree vanishing**: `Hᵢ(M|K;ℤ) = 0` for every `i > n`. The ℤ mirror of
`SingularManifoldFundamentalClass.vanishAbove`. -/
def vanishAboveInt (n : ℕ) (K : Set ↑X) : Prop :=
  ∀ i, n < i → ∀ x : RelHomologyInt Kᶜ i, x = 0

/-- **Integral determined-by-points**: a degree-`n` relative class `α ∈ Hₙ(M|K;ℤ)` whose restriction
to the local homology at every point of `K` vanishes is itself `0`. The ℤ mirror of
`SingularManifoldFundamentalClass.determinedByPoints`, using the integral point-restriction
`restrictToPointInt`. -/
def determinedByPointsInt (n : ℕ) (K : Set ↑X) : Prop :=
  ∀ α : RelHomologyInt Kᶜ n,
    (∀ (x : ↑X) (hx : x ∈ K), restrictToPointInt hx n α = 0) → α = 0

/-- **The integral good-compact property** (Hatcher 3.27, ℤ): both high-degree vanishing and
determined-by-points in the top degree `n`. The ℤ mirror of `SingularGoodCompact.goodCompact`. -/
def goodCompactInt (n : ℕ) (K : Set ↑X) : Prop :=
  vanishAboveInt n K ∧ determinedByPointsInt n K

/-- **Integral restriction factors through a sub-restriction**: for `K' ⊆ K` and `x ∈ K'`, restricting
a class on `Hₙ(M|K;ℤ)` first to `Hₙ(M|K';ℤ)` (via `relInclInt` over `Kᶜ ⊆ K'ᶜ`) and then to the point
`x` equals restricting it directly to `x`. The ℤ mirror of `restrictToPoint_relIncl`; the naturality the
determined-by-points union step rides on. -/
theorem restrictToPointInt_relInclInt {K K' : Set ↑X} (hKK' : K' ⊆ K) {x : ↑X} (hx : x ∈ K') (n : ℕ)
    (α : RelHomologyInt Kᶜ n) :
    restrictToPointInt hx n (relInclInt (Set.compl_subset_compl.mpr hKK') n α)
      = restrictToPointInt (hKK' hx) n α := by
  rw [restrictToPointInt, restrictToPointInt, relInclInt_trans]

end SKEFTHawking.SingularGoodCompactInt
