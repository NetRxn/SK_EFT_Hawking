/-
# Phase 5q.H · Kummer K1-b — the T⁴ intersection-form DIAGONAL vanishing (isotropic factor block)

The K1-b entry of the `KummerK3Base` dossier: the integral intersection form of `T⁴ = Circle⁴` on
`H²(T⁴;ℤ)`. The full Gram is `3H` (three hyperbolic planes); its `6×6` matrix in the pair basis
`{e_{ij}}` (`{i,j} ⊂ {1,2,3,4}`) has `±1` exactly on complementary pairs (`{12}↔{34}`, `{13}↔{24}`,
`{14}↔{23}`) and `0` everywhere else — 30 of 36 entries vanish.

This module lands the **vanishing mechanism** for the diagonal / non-complementary block, exactly
mirroring the banked S²×S² arc (`SphereProdGramInt`): a class pulled back from a single lower-dim
factor `T³` squares to zero, because its square is the pullback of a cup product living in
`H⁴(T³;ℤ) = 0`. On the step carrier `T⁴ = Tor (Tor TwoTorus) = T³ × S¹` the factor projection
`prodFst : T⁴ → T³` realizes the isotropic 3-dim subspace `⟨e_{12}, e_{13}, e_{23}⟩` (the classes
pulled back from the first `T³`), on which the honest intersection form vanishes identically.

Headline results (kernel-pure `{propext, Classical.choice, Quot.sound}`; no `sorry`/`native_decide`/
`maxHeartbeats`/axiom):
* `Subsingleton (Cohomology (Tor TwoTorus) 4)` — `H⁴(T³;ℤ) = 0` (UCT flip of `H₄(T³;ℤ) = 0` over
  `H₃(T³;ℤ)` free), the vanishing input.
* the honest fundamental class `[T⁴]` on the step carrier + the intersection-form reduction
  `interFormInt fc a b = ⟨a ∪ b, [T⁴]⟩`-coordinate (`interFormInt_honest_t4`), built from the DONE
  `fourStepH4EquivInt : H₄(T⁴;ℤ) ≅ ℤ`.
* `cupH24_prodFst_factor_eq_zero` / `interFormInt_honest_t4_fst_eq_zero` — classes pulled back from
  the `T³` factor cup to zero, and the honest intersection form vanishes on them (`e_{ij}∪e_{kl}=0`
  for pairs sharing the dropped coordinate's complement — the isotropic block).

**What remains of the full `3H` Gram** (reported, not silently dropped): (i) the *basis
identification* `e_{ij} = (proj)* gen` tying the six homology generators to factor pullbacks (needs
the `deltaGen` factor-projection lemmas, deferred even for S²×S² by `SphereProdHTwoInt §5`); (ii) the
extension of the vanishing to the other `T³` sub-factors (re-association homeomorphisms); and (iii)
the six complementary CROSS entries `e_{ij}∪e_{kl} = ±1` — the top-degree `T²×T²` cross product,
which is the genuine Eilenberg–Zilber wall (NO cross-product / EZ machinery is in-tree; see the
re-triage note). Routes (a) `T²×T²` template, (b) Künneth-ring ladder, and (c) coordinate-pair
sections all reduce, at these six entries, to that same `T²×T²` cross product.
-/
import Mathlib
import SKEFTHawking.SphereProdGramInt
import SKEFTHawking.KummerHomologyT4Full

open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularHomologyInt (Homology intFundamentalClassOfHomology)
open SKEFTHawking.SingularCohomologyFunctorialityInt (cohomologyPullbackInt)
open SKEFTHawking.SingularAbsoluteUCInt (ucIntEquivOfFree)
open SKEFTHawking.SphereWitnessTowerInt (cohomology_subsingleton_of_homology)
open SKEFTHawking.SphereProdGramInt (cupH24_cohomologyPullbackInt_factor_eq_zero)
open SKEFTHawking.SingularProdContractibleInt (prodFst)
open SKEFTHawking.SingularSphereAcyclic (Sph)
open SKEFTHawking.KummerTorusStep (Tor)
open SKEFTHawking.KummerHomologyT2 (TwoTorus)
open SKEFTHawking.KummerHomologyT4Full (threeTorus_three_free_finite threeTorus_four_free_finite
  fourStepH4EquivInt)

namespace SKEFTHawking.KummerT4GramDiagonal

/-! ## §1. `H⁴(T³;ℤ) = 0` -/

/-- **`H₄(T³;ℤ) = 0`** — free finite rank `0` (`threeTorus_four_free_finite`), hence subsingleton. -/
instance : Subsingleton (Homology (Tor TwoTorus) 4) := by
  have h := threeTorus_four_free_finite
  haveI := h.1
  haveI := h.2.1
  exact (Module.finrank_zero_iff (R := ℤ)).mp h.2.2

/-- `H₃(T³;ℤ)` is free (the UCT `Ext`-input; `threeTorus_three_free_finite`). -/
instance : Module.Free ℤ (Homology (Tor TwoTorus) 3) := threeTorus_three_free_finite.1

/-- **`H⁴(T³;ℤ) = 0`** — the absolute integral UCT flip of `H₄(T³;ℤ) = 0` over `H₃(T³;ℤ)` free.
The `T³`-factor top cohomology vanishes: this is what forces a factor-pullback square to zero. -/
instance : Subsingleton (Cohomology (Tor TwoTorus) 4) :=
  haveI : Module.Free ℤ (Homology (Tor TwoTorus) (2 + 1)) :=
    inferInstanceAs (Module.Free ℤ (Homology (Tor TwoTorus) 3))
  haveI : Subsingleton (Homology (Tor TwoTorus) (2 + 2)) :=
    inferInstanceAs (Subsingleton (Homology (Tor TwoTorus) 4))
  cohomology_subsingleton_of_homology (Tor TwoTorus) 2

/-! ## §2. The honest fundamental class `[T⁴]` and the intersection-form reduction -/

/-- **The integral fundamental class `[T⁴] ∈ H₄(T⁴;ℤ)`** on the step carrier — the generator
`fourStepH4EquivInt.symm 1` of the DONE `H₄(T⁴;ℤ) ≅ ℤ`. Canonical up to the sign convention pinned
by its coordinate value `1`. -/
noncomputable def t4FundClassInt : Homology (Tor (Tor TwoTorus)) 4 :=
  fourStepH4EquivInt.symm 1

/-- **The HONEST `IntFundamentalClass` datum at `T⁴`** — `eval := ⟨·, [T⁴]⟩`, the integral Kronecker
pairing against the computed fundamental class `t4FundClassInt` (not an arbitrary functional). -/
noncomputable def t4IntFundClassHonest : IntFundamentalClass (Tor (Tor TwoTorus)) :=
  intFundamentalClassOfHomology t4FundClassInt

/-- **`H⁴(T⁴;ℤ) ≅ ℤ`** — the absolute-UCT flip of `H₄(T⁴;ℤ) ≅ ℤ` over `H₃(T⁴;ℤ)` free
(`ucIntEquivOfFree` at `M = 2`, dualized through the computed top iso and `(ℤ)* ≅ ℤ`). -/
noncomputable def t4CohomFourEquivInt : Cohomology (Tor (Tor TwoTorus)) 4 ≃ₗ[ℤ] ℤ :=
  haveI : Module.Free ℤ (Homology (Tor (Tor TwoTorus)) (2 + 1)) :=
    inferInstanceAs (Module.Free ℤ (Homology (Tor (Tor TwoTorus)) 3))
  (ucIntEquivOfFree (Tor (Tor TwoTorus)) 2).trans
    ((fourStepH4EquivInt.symm.dualMap).trans (LinearMap.ringLmapEquivSelf ℤ ℤ ℤ))

/-- **The honest `eval` is the `H⁴`-coordinate** — the honest datum's evaluation functional is
exactly the UCT iso's underlying map (definitional readout: both are `⟨·, [T⁴]⟩`). -/
theorem t4IntFundClassHonest_eval (ω : Cohomology (Tor (Tor TwoTorus)) 4) :
    t4IntFundClassHonest.eval ω = t4CohomFourEquivInt ω := rfl

/-- **The intersection form against the honest `[T⁴]` is the `H⁴`-coordinate of the cup product** —
`interFormInt fc a b = (a ∪ b)`-coordinate under `H⁴(T⁴;ℤ) ≅ ℤ`. Every Gram computation reduces
through this to integral cup-product data. -/
theorem interFormInt_honest_t4 (a b : Cohomology (Tor (Tor TwoTorus)) 2) :
    interFormInt t4IntFundClassHonest a b = t4CohomFourEquivInt (cupH24 a b) := by
  rw [interFormInt_apply]
  exact t4IntFundClassHonest_eval (cupH24 a b)

/-! ## §3. The isotropic factor block: `T³`-pullback classes cup to zero -/

/-- **A `T³`-factor pullback square is zero** — for the factor projection
`prodFst : T⁴ = T³ × S¹ → T³`, any two `H²(T³;ℤ)` classes pulled back to `T⁴` cup to zero in
`H⁴(T⁴;ℤ)`: their cup is the pullback of a class in `H⁴(T³;ℤ) = 0` (§1). The cup-level mechanism
behind `e_{ij} ∪ e_{kl} = 0` for pairs supported in the first `T³` factor. -/
theorem cupH24_prodFst_factor_eq_zero (x y : Cohomology (Tor TwoTorus) 2) :
    cupH24 (cohomologyPullbackInt (prodFst (Tor TwoTorus) (Sph 1)) 2 x)
        (cohomologyPullbackInt (prodFst (Tor TwoTorus) (Sph 1)) 2 y) = 0 :=
  cupH24_cohomologyPullbackInt_factor_eq_zero (prodFst (Tor TwoTorus) (Sph 1)) x y

/-- **The honest `T⁴` intersection form vanishes on `T³`-factor pullbacks** —
`⟨(p*x) ∪ (p*y), [T⁴]⟩ = 0` for the factor projection `p = prodFst : T⁴ → T³`. The isotropic
subspace of `H²(T⁴;ℤ)` pulled back from the first `T³` (spanning `⟨e_{12}, e_{13}, e_{23}⟩` once the
basis identification is made): the honest intersection form is identically zero on it — every
diagonal and within-first-`T³` off-diagonal Gram entry vanishes, with no Eilenberg–Zilber input. -/
theorem interFormInt_honest_t4_fst_eq_zero (x y : Cohomology (Tor TwoTorus) 2) :
    interFormInt t4IntFundClassHonest
        (cohomologyPullbackInt (prodFst (Tor TwoTorus) (Sph 1)) 2 x)
        (cohomologyPullbackInt (prodFst (Tor TwoTorus) (Sph 1)) 2 y) = 0 := by
  rw [interFormInt_honest_t4, cupH24_prodFst_factor_eq_zero, map_zero]

end SKEFTHawking.KummerT4GramDiagonal
