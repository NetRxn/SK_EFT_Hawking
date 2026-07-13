/-
# Phase 5q.H · slice-6 — the S²×S² Gram OFF-DIAGONAL entry: assembly modulo the disclosed
# Eilenberg–Zilber cross-product value

`SphereProdGramInt` discharged the S²×S² Gram pin's two DIAGONAL entries (`α∪α=0`, `β∪β=0`, for
`α, β` any classes pulled back from a single `S²` factor along `prodFst`/`sndCM`). The remaining
wall is the OFF-diagonal cross entry `⟨α∪β,[S²×S²]⟩ = ±1` — the Eilenberg–Zilber/Künneth
cross-product fact. Reconnaissance (this module's recon gate) confirms this is a **genuine,
currently-unbuilt** piece of infrastructure, not a routine tactic gap:

* **No Mathlib shortcut.** At the pinned Mathlib commit (`5e932f97`, v4.29.1) there is no Künneth
  theorem, Eilenberg–Zilber map, or cross product for singular (co)homology (`grep -rli
  "kunneth|künneth|eilenberg.zilber"` over `Mathlib/` returns zero hits; `AlgebraicTopology`'s own
  singular-homology functor (`Mathlib.AlgebraicTopology.SingularHomology.Basic`) is a bare
  category-theoretic construction with no cup/cross product built on it). This project's entire cup
  product (`SingularCupInt.cup`/`cupH24`) and cap product (`IntCapProductInt.capInt`/`capHInt`) were
  built FROM SCRATCH on the custom `TopCat.toSSet`-based cochain model precisely because Mathlib
  lacks this layer — so there is no adapter to port a cross product from.
* **Two possible routes, both genuinely deep — neither closable in one MCP proof-loop session:**
  (a) an actual Eilenberg–Zilber (shuffle) cross-product map for this cochain model, at the same
  combinatorial depth as `SingularCupInt`'s signed Leibniz rule / `cupOne22` Steenrod product (a
  multi-hundred-line new combinatorial development); or (b) a geometric "cap of a factor-pullback =
  pushed-forward fundamental class of the OTHER factor" projection-formula argument tied to the
  SPECIFIC Mayer–Vietoris construction of `[S²×S²]` (`SphereProdHFourInt.sphereProdFundClassInt`,
  built via the degree-4 connecting map `hFourToInt`) — itself comparable in depth to a from-scratch
  Poincaré-duality argument for this one manifold, and no such projection-formula naturality lemma
  exists in `IntCapProductInt` today.
* **A THIRD open piece, independent of the cross-product value**: the "basis-ID" — showing
  `{α, β}` actually form a `Module.Basis` of `H²(S²×S²;ℤ)` (independence + SPANNING), which routes
  through `SphereProdHTwoInt.deltaGen`'s projections under `prodFst`/`sndCM`. That module's own
  docstring already flags this ("canonical exactly modulo generator 1 — the split choice"):
  `deltaGen` is an `Exists.choose`-derived section, pinned only up to adding any multiple of
  `sumInto`, so its factor-projections are NOT forced by the existing characterization
  (`deltaGen_spec`) without further normalization — a separate wall from the cross-product value.
* **Matches the project's own recorded status**: `docs/dev-loops/Phase5qH/PHASE5QH_EXECUTION_MAP.md`
  already lists this exact item as "OFF critical path (deferred): S²×S² 2nd witness (needs an
  Eilenberg–Zilber cross-product build; leg already demonstrated via S⁴)". The σ÷16 Rokhlin leg is
  independently, unconditionally demonstrated via the FIRST witness (S⁴,
  `sixteen_dvd_latticeSig_sphere4_unconditional`), so this second witness does not gate that result.

**What THIS module ships** (kernel-pure, no new gap introduced): the exact ASSEMBLY the wall blocks
— given the single remaining cross-product value as a bare hypothesis (matching the project's
established "disclosed geometric fact as an explicit theorem hypothesis" pattern, e.g.
`SphereWitnessTowerInt.sphereProd_interMatrix_evenUnimodular_of_gram (hgram : ...)`), the full 2×2
Gram matrix on `![α, β]` equals the hyperbolic pin `Hyp` exactly. This connects ALL FOUR entries
(two already-proven diagonal zeros, symmetry, and the one disclosed cross value) into the literal
target matrix, isolating the wall to the smallest possible single remaining fact.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`.
-/
import Mathlib
import SKEFTHawking.SphereProdGramInt
import SKEFTHawking.SphereProductBounding

open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularCohomologyFunctorialityInt
open SKEFTHawking.SingularSphereAcyclic (Sph)
open SKEFTHawking.SingularProdContractibleInt (prodFst)
open SKEFTHawking.SphereWitnessTowerInt (SphereProdT)
open SKEFTHawking.SphereProdHFourInt (sphereProdIntFundClassHonest)
open SKEFTHawking.SphereProdHTwoInt (sndCM)
open SKEFTHawking.SphereProdGramInt (interFormInt_honest_fst_eq_zero interFormInt_honest_snd_eq_zero)
open SKEFTHawking.SpinSigmaRoute (sphereProdFormDatum)

namespace SKEFTHawking.SphereProdCrossInt

/-- The pullback of an `S²` degree-2 class along the FIRST factor projection — the `α`-shape class
the S²×S² Gram computation's first basis vector refers to. -/
noncomputable def alphaOf (x : Cohomology (Sph 2) 2) : Cohomology SphereProdT 2 :=
  cohomologyPullbackInt (prodFst (Sph 2) (Sph 2)) 2 x

/-- The pullback of an `S²` degree-2 class along the SECOND factor projection — the `β`-shape
class. -/
noncomputable def betaOf (x : Cohomology (Sph 2) 2) : Cohomology SphereProdT 2 :=
  cohomologyPullbackInt sndCM 2 x

/-- The two-element family `![α, β]` at a chosen class `x : Cohomology (Sph 2) 2` — the SHAPE of
the geometric basis the Gram pin refers to. NOT yet packaged as a `Module.Basis`: independence and
spanning are the separate "basis-ID" open question this module's docstring isolates from the
cross-product value. -/
noncomputable def crossFamily (x : Cohomology (Sph 2) 2) : Fin 2 → Cohomology SphereProdT 2 :=
  ![alphaOf x, betaOf x]

/-- **The full 2×2 Gram matrix on `![α,β]` equals the hyperbolic pin `Hyp`, GIVEN the single
remaining cross-product value.** Assembles the two diagonal entries (`α²=0`, `β²=0`, DONE in
`SphereProdGramInt`), the disclosed off-diagonal value `⟨α∪β,[M]⟩ = 1` (`hcross` — the
Eilenberg–Zilber/Künneth fact this from-scratch singular-cochain substrate does not yet construct;
see the module docstring), and symmetry (`interFormInt_symm`, from `cupH24_symm`) for the mirrored
entry. Every entry of the target matrix `sphereProdFormDatum = Hyp` is now accounted for by a named,
isolated fact — three already proven on main, one disclosed here as an explicit hypothesis. -/
theorem crossFamily_gram_eq_hyp (x : Cohomology (Sph 2) 2)
    (hcross : interFormInt sphereProdIntFundClassHonest (alphaOf x) (betaOf x) = 1) :
    (Matrix.of fun i j => interFormInt sphereProdIntFundClassHonest
        (crossFamily x i) (crossFamily x j)) = sphereProdFormDatum := by
  have hαα : interFormInt sphereProdIntFundClassHonest (alphaOf x) (alphaOf x) = 0 :=
    interFormInt_honest_fst_eq_zero x x
  have hββ : interFormInt sphereProdIntFundClassHonest (betaOf x) (betaOf x) = 0 :=
    interFormInt_honest_snd_eq_zero x x
  have hβα : interFormInt sphereProdIntFundClassHonest (betaOf x) (alphaOf x) = 1 := by
    rw [interFormInt_symm]; exact hcross
  ext i j
  fin_cases i <;> fin_cases j <;>
    (show interFormInt sphereProdIntFundClassHonest _ _ = sphereProdFormDatum _ _
     simp [crossFamily, sphereProdFormDatum, Hyp, hαα, hββ, hcross, hβα])

end SKEFTHawking.SphereProdCrossInt
