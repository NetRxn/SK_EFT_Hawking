import Mathlib
import SKEFTHawking.SingularRelativeDisjointUnionFundClass
import SKEFTHawking.PoincareLefschetzRelFundClassCylinder

/-!
# Phase 5q.H — THE COMPONENT-LOCAL `D` (route (b): the disconnected cylinder datum via the engine)

The disconnected residual `DisconnectedCylCoreND M = {D, nd14, nd23, hwu}` (predecessor) is
bottlenecked on `D : RelFundClassDatum ((cylModel 2).boundary (cylW M))` — the connected engine's
`hasRelFundClass_cylGen` fails for disconnected `M` at the punctured-top-vanishing. This module builds
`D` for disconnected `M` **via the relative clopen-split engine**, with NO homeomorphism transport
(the standing wall).

`cylW M = M × [0,1]`; a clopen `C ⊆ M` gives a clopen cylinder piece `C × [0,1] ⊆ cylW M`
(`isClopen_cylPiece`). For a clopen piece `U`, the engine's folded assembly
(`hasRelFundClass_of_clopen_split_folded`) builds the disconnected `HasRelFundClass (∂W) cylGen` from a
per-piece detection on each side (a `RestrictsToRelGenOn` predicate against `cylGen` over the ambient);
at every interior point the off-piece summand dies (the engine's local projection), so detection
localizes to the piece containing the point — exactly route (b)'s component-local reduction. Feeding
that witness into the connected `cylinderRelFundClassDatum` (whose `gen`/`ε`/Wall-2 machinery is
connectedness-free) yields the full disconnected `D` — `cylinderRelFundClassDatum_of_clopenSplit`.

The per-piece detection is packaged in the **folded** `RestrictsToRelGenOn` predicate deliberately: the
detection equation `restrictBd ((cylModel 2).boundary (cylW M)) hx α = (cylGen x hx).symm 1` written
explicitly whnf-loops on the `ModelWithCorners.boundary` reduction (the same wall `cylGen` is sealed
against); under a definitional wrapper it does not.

## The isolated residual (named, not faked)

The two per-piece detection witnesses `hdetU`/`hdetUc` — each the *connected* cylinder fundamental
class of a clopen piece, detected against `cylGen` over the ambient. The engine has discharged
everything else: the clopen additivity, the off-piece vanishing, the `gen`/`ε`/Wall-2 packaging. This
is the sharpest honest reduction of the disconnected `D`: from "the whole disconnected fundamental
class" to "per-clopen-piece detection", **without** a homeomorphism transport.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no
`native_decide`, no `maxHeartbeats`.
-/

open scoped Manifold
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularExcisionIso
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.SingularRelativeDisjointUnionFundClass

namespace SKEFTHawking.PinPlusCylDataDischargeDisconnectedD

noncomputable section

variable {m' : ℕ} {M : Type} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M]

/-- **A clopen base subset gives a clopen cylinder piece**: for clopen `C ⊆ M`, the slab
`C × [0,1] ⊆ cylW M = M × [0,1]` is clopen (product of clopen sets; the interval factor is `univ`).
The bridge from "`M` disconnected" (a clopen component union `C`) to "`cylW M` has a clopen split". -/
theorem isClopen_cylPiece {C : Set M} (hC : IsClopen C) :
    IsClopen (C ×ˢ (Set.univ : Set (Set.Icc (0 : ℝ) 1)) : Set (cylW M)) :=
  hC.prod isClopen_univ

variable [T1Space (cylW M)]

/-- **The disconnected cylinder relative-fundamental-class datum `D`, via the engine.** For a clopen
piece `U ⊆ cylW M`, given per-piece classes `αU`, `αUᶜ` each detecting the interior generator on its
own piece (the folded `RestrictsToRelGenOn` predicate against `cylGen`), the folded engine assembly
`hasRelFundClass_of_clopen_split_folded` builds `HasRelFundClass (∂W) cylGen` — the off-piece summand
dies at every interior point — and `cylinderRelFundClassDatum` packages the full `RelFundClassDatum`.
The disconnected `D` **without** a homeomorphism transport: only the engine's clopen additivity + local
projection + the connectedness-free `gen`/`ε`/Wall-2 packaging. -/
def cylinderRelFundClassDatum_of_clopenSplit
    {U : Set ↑(TopCat.of (cylW M))} (hU : IsClopen U)
    (αU : RelativeHomology (restr ((cylModel m').boundary (cylW M)) U) (m' + 1 + 2))
    (αUc : RelativeHomology (restr ((cylModel m').boundary (cylW M)) Uᶜ) (m' + 1 + 2))
    (hdetU : RestrictsToRelGenOn (X := TopCat.of (cylW M)) (m := m' + 1)
      ((cylModel m').boundary (cylW M)) (cylGen (M := M) (m' := m')) (· ∈ U)
      (excisionMap ((cylModel m').boundary (cylW M)) U (m' + 1 + 2) αU))
    (hdetUc : RestrictsToRelGenOn (X := TopCat.of (cylW M)) (m := m' + 1)
      ((cylModel m').boundary (cylW M)) (cylGen (M := M) (m' := m')) (· ∈ Uᶜ)
      (excisionMap ((cylModel m').boundary (cylW M)) Uᶜ (m' + 1 + 2) αUc)) :
    RelFundClassDatum (X := TopCat.of (cylW M)) (m := m' + 1)
      ((cylModel m').boundary (cylW M)) :=
  cylinderRelFundClassDatum
    (hasRelFundClass_of_clopen_split_folded hU ((cylModel m').boundary (cylW M))
      (cylGen (M := M) (m' := m')) αU αUc hdetU hdetUc)

end

end SKEFTHawking.PinPlusCylDataDischargeDisconnectedD
