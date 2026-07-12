import Mathlib
import SKEFTHawking.SingularCohomologyFunctorialityInt
import SKEFTHawking.SphereProdHFourInt

/-!
# Phase 5q.H · slice-5→6 — the S²×S² Gram DIAGONAL vanishing (α²=0, β²=0)

The next slice toward the S²×S² Gram pin `interMatrix sphereProdIntFundClassHonest B = H`
(`= ![![0,1],![1,0]]`). By `SphereProdHFourInt.interMatrix_honest_apply`, every Gram entry against
the honest fundamental class is the `H⁴`-coordinate of a cup product `cupH24 (Bᵢ) (Bⱼ)`. This module
discharges the **two DIAGONAL entries' mechanism**: a class pulled back from a single 2-sphere factor
squares to zero, because its square is the pullback of a cup product living in `H⁴(S²;ℤ) = 0`.

Headline results (kernel-pure `{propext, Classical.choice, Quot.sound}`):
* `Subsingleton (Cohomology (Sph 2) 4)` — `H⁴(S²;ℤ) = 0` (UCT flip of `H₄(S²;ℤ) = H₃(S²;ℤ) = 0`).
* `cupH24_cohomologyPullbackInt_factor_eq_zero` — ABSTRACT: for any `f : W → Z` with
  `H⁴(Z;ℤ) = 0`, `(f*x) ∪ (f*y) = 0` (cup-pullback naturality + the target vanishing).
* `interFormInt_honest_factor_self_eq_zero` — the honest intersection form vanishes on classes
  pulled back from a single S² factor: `⟨f*x ∪ f*y, [S²×S²]⟩ = 0`. Instantiated at the two factor
  projections `prodFst` / `sndCM` (`interFormInt_honest_fst_eq_zero`, `..._snd_eq_zero`): the
  geometric `α∪α = 0`, `β∪β = 0`.

**What remains of the Gram pin** (reported, not silently dropped): (i) the *basis identification*
`Bᵢ = (projᵢ)* gen` — needs the `deltaGen` factor-projection lemmas (`mapInt prodFst deltaGen = 0`,
`mapInt sndCM deltaGen = [S²]`), deferred by `SphereProdHTwoInt §5`; and (ii) the two CROSS entries
`α∪β = ±[S²×S²]-gen`, the Künneth/cross-product (`= ±1`), needing an Eilenberg–Zilber cross product
NOT yet in-tree. This module lands the diagonal mechanism, which is unconditional and reusable.
-/

open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularHomologyInt (Homology)
open SKEFTHawking.SingularCohomologyFunctorialityInt
open SKEFTHawking.SingularSphereAcyclic (Sph)
open SKEFTHawking.SingularSphereHighDegreeInt (sphere_homology_high)
open SKEFTHawking.SingularProdContractibleInt (prodFst)
open SKEFTHawking.SphereWitnessTowerInt (SphereProdT cohomology_subsingleton_of_homology)
open SKEFTHawking.SphereProdHFourInt (sphereProdIntFundClassHonest sphereProdCohomFourEquivInt
  interFormInt_honest)
open SKEFTHawking.SphereProdHTwoInt (SphSph sndCM)

namespace SKEFTHawking.SphereProdGramInt

/-! ## §1. `H⁴(S²;ℤ) = 0` -/

/-- **`H₃(S²;ℤ) = 0`** — high-degree vanishing (`3 > 2`). -/
instance : Subsingleton (Homology (Sph 2) 3) :=
  subsingleton_of_forall_eq 0 (sphere_homology_high 2 3 (by norm_num))

/-- **`H₄(S²;ℤ) = 0`** — high-degree vanishing (`4 > 2`). -/
instance : Subsingleton (Homology (Sph 2) 4) :=
  subsingleton_of_forall_eq 0 (sphere_homology_high 2 4 (by norm_num))

/-- `H₃(S²;ℤ) = 0` is free (the UCT `Ext`-input). -/
instance : Module.Free ℤ (Homology (Sph 2) 3) := Module.Free.of_subsingleton ℤ _

/-- **`H⁴(S²;ℤ) = 0`** — the absolute integral UCT flip of `H₄(S²;ℤ) = 0` over `H₃(S²;ℤ) = 0` free.
The single-factor top cohomology vanishes: this is what forces a factor-pullback square to zero. -/
instance : Subsingleton (Cohomology (Sph 2) 4) :=
  haveI : Module.Free ℤ (Homology (Sph 2) (2 + 1)) :=
    inferInstanceAs (Module.Free ℤ (Homology (Sph 2) 3))
  haveI : Subsingleton (Homology (Sph 2) (2 + 2)) :=
    inferInstanceAs (Subsingleton (Homology (Sph 2) 4))
  cohomology_subsingleton_of_homology (Sph 2) 2

/-! ## §2. The abstract factor-pullback-square-vanishing lemma -/

/-- **A factor-pullback square is zero** — ABSTRACT: for a continuous `f : W → Z` into a space `Z`
whose top-degree integral cohomology `H⁴(Z;ℤ)` vanishes, any two `H²(Z;ℤ)` classes pulled back to
`W` cup to zero. Proof: cup-pullback multiplicativity `(f*x) ∪ (f*y) = f*(x ∪ y)`, and `x ∪ y = 0`
in `H⁴(Z;ℤ) = 0`. This is the mechanism behind `α∪α = 0` on a product: `α` is pulled back from one
2-sphere factor, whose `H⁴` is zero. -/
theorem cupH24_cohomologyPullbackInt_factor_eq_zero {W Z : TopCat}
    [Subsingleton (Cohomology Z 4)] (f : C(↑W, ↑Z)) (x y : Cohomology Z 2) :
    cupH24 (cohomologyPullbackInt f 2 x) (cohomologyPullbackInt f 2 y) = 0 := by
  rw [← cohomologyPullbackInt_cupH24, Subsingleton.elim (cupH24 x y) 0, map_zero]

/-! ## §3. The honest S²×S² intersection form vanishes on factor pullbacks -/

/-- **The honest intersection form vanishes on same-factor pullbacks** — `⟨(f*x) ∪ (f*y), [S²×S²]⟩ = 0`
for any `f : S²×S² → S²`. Via `interFormInt_honest` (the entry is the `H⁴`-coordinate of the cup)
and the abstract factor-vanishing lemma. This is the honest-`fc` diagonal-vanishing content: the
self-intersection of a factor class is zero (`α²=0`). -/
theorem interFormInt_honest_factor_self_eq_zero (f : C(↑SphereProdT, ↑(Sph 2)))
    (x y : Cohomology (Sph 2) 2) :
    interFormInt sphereProdIntFundClassHonest
        (cohomologyPullbackInt f 2 x) (cohomologyPullbackInt f 2 y) = 0 := by
  rw [interFormInt_honest, cupH24_cohomologyPullbackInt_factor_eq_zero, map_zero]

/-- **`α∪α = 0`** — the honest intersection form vanishes on classes pulled back from the FIRST
2-sphere factor (`prodFst : S²×S² → S²`). The first diagonal Gram entry's mechanism. -/
theorem interFormInt_honest_fst_eq_zero (x y : Cohomology (Sph 2) 2) :
    interFormInt sphereProdIntFundClassHonest
        (cohomologyPullbackInt (prodFst (Sph 2) (Sph 2)) 2 x)
        (cohomologyPullbackInt (prodFst (Sph 2) (Sph 2)) 2 y) = 0 :=
  interFormInt_honest_factor_self_eq_zero (prodFst (Sph 2) (Sph 2)) x y

/-- **`β∪β = 0`** — the honest intersection form vanishes on classes pulled back from the SECOND
2-sphere factor (`sndCM : S²×S² → S²`). The second diagonal Gram entry's mechanism. -/
theorem interFormInt_honest_snd_eq_zero (x y : Cohomology (Sph 2) 2) :
    interFormInt sphereProdIntFundClassHonest
        (cohomologyPullbackInt sndCM 2 x) (cohomologyPullbackInt sndCM 2 y) = 0 :=
  interFormInt_honest_factor_self_eq_zero sndCM x y

end SKEFTHawking.SphereProdGramInt
