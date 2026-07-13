/-
# Phase 5q.H (W-A.1e, item 3) — the `CharPairWProvider` connection note

A standalone compatibility statement, read-only against `PinPlusCharPairData` (that file is never
modified): the `(1,4)`/`(2,3)` Lefschetz–Wu data assembled by the datum-assembly seam
(`PoincareLefschetzWuAssembly.LefschetzWuDatum.ofRelFund14` / `.ofRelFund23`), together with the
Wu-formula admissibility `wuW2 = 0`, inhabit EXACTLY the shape `PinPlusCharPairData.WAdm b` consumes
— `mkWAdm` is the literal shape match (`WAdm`'s three fields are `P14`, `P23`, `hwu`); `mkWAdmOfRelFund`
composes this through the datum-assembly seam, so a family of `RelFundClassDatum`s (one per bordism,
with the residual finite-dimensionality/non-degeneracy/Betti trio for both legs, and `wuW2 = 0`)
inhabits `PinPlusCharPairData.CharPairWProvider`'s discharge obligation `WAdm`, bordism by bordism.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzWuAssembly
import SKEFTHawking.PinPlusCharPairData

namespace SKEFTHawking.PoincareLefschetzWuAssembly

open scoped Manifold
open SKEFTHawking.PoincareLefschetzWu5 SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.BordismTheory
open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativeCup

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]

/-- **A `(1,4)`/`(2,3)` Lefschetz–Wu datum pair with `w₂(W) = 0` assembles a `WAdm`.** The literal
shape match: `WAdm b`'s three fields are exactly `P14`, `P23`, `hwu`. -/
def mkWAdm {s t : SingularManifold PUnit k I} (b : Bordism (I.prod (𝓡∂ 1)) s t)
    (P14 : LefschetzWuDatum (TopCat.of b.W) ((I.prod (𝓡∂ 1)).boundary b.W) 1 4 5)
    (P23 : LefschetzWuDatum (TopCat.of b.W) ((I.prod (𝓡∂ 1)).boundary b.W) 2 3 5)
    (hwu : wuW2 P14 P23 = 0) : WAdm b where
  P14 := P14
  P23 := P23
  hwu := hwu

/-- **`ofRelFund14`/`.ofRelFund23` compose directly into `WAdm`**: given a `RelFundClassDatum` on a
set `S` EQUAL to `∂W` (`X := TopCat.of b.W`) plus the residual finite-dimensionality/non-degeneracy/
Betti trio for BOTH legs, and the Wu-formula admissibility `wuW2 = 0` for the assembled pair,
`WAdm b` follows — the composed form of `mkWAdm` through the datum-assembly seam. `S` is threaded as
a free generic `Set` variable (with the boundary identification `hS` substituted only once, at the
very end, via `subst`) rather than the compound boundary expression repeated at every hypothesis
field, to keep elaboration of the eight independent hypothesis fields cheap (the fresh whnf-index
friction: repeating a heavy manifold-instance term many times blows the elaborator's `isDefEq`
heartbeat budget — a term-architecture fix, never `maxHeartbeats`). -/
noncomputable def mkWAdmOfRelFund {s t : SingularManifold PUnit k I}
    (b : Bordism (I.prod (𝓡∂ 1)) s t) {S : Set (TopCat.of b.W)}
    (hS : S = (I.prod (𝓡∂ 1)).boundary b.W)
    (D : PoincareLefschetzRelFundClass.RelFundClassDatum (m := 3) S)
    (findimAbs14 : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of b.W) 1))
    (findimRel14 : FiniteDimensional (ZMod 2) (RelativeCohomology S 4))
    (nondeg14 : Function.Injective ⇑((relCupH14 (X := TopCat.of b.W) (S := S)).compr₂ D.mu))
    (dimeq14 : Module.finrank (ZMod 2) (Cohomology (TopCat.of b.W) 1)
             = Module.finrank (ZMod 2) (RelativeCohomology S 4))
    (findimAbs23 : FiniteDimensional (ZMod 2) (Cohomology (TopCat.of b.W) 2))
    (findimRel23 : FiniteDimensional (ZMod 2) (RelativeCohomology S 3))
    (nondeg23 : Function.Injective ⇑((relCupH23 (X := TopCat.of b.W) (S := S)).compr₂ D.mu))
    (dimeq23 : Module.finrank (ZMod 2) (Cohomology (TopCat.of b.W) 2)
             = Module.finrank (ZMod 2) (RelativeCohomology S 3))
    (hwu : wuW2 (LefschetzWuDatum.ofRelFund14 D findimAbs14 findimRel14 nondeg14 dimeq14)
                (LefschetzWuDatum.ofRelFund23 D findimAbs23 findimRel23 nondeg23 dimeq23) = 0) :
    WAdm b := by
  subst hS
  exact mkWAdm b (LefschetzWuDatum.ofRelFund14 D findimAbs14 findimRel14 nondeg14 dimeq14)
    (LefschetzWuDatum.ofRelFund23 D findimAbs23 findimRel23 nondeg23 dimeq23) hwu

end SKEFTHawking.PoincareLefschetzWuAssembly
