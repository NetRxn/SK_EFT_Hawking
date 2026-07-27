/-
# Phase 5q.H (N1a) — the Freeze-A vacuity finding, LANDED ON THE GENUINE SPIN CARRIER

`HandleTradeAtomVacuity.lean` proves that the Freeze-A handle-trace primitive
`SpinSigmaPresentation.HandleTradeCobordism` is satisfiable with **zero geometric input** on *any*
tangential datum `ξ`, for any distinguished slot with a nonempty carrier. A reasonable objection is
that this might be an artefact of abstract `ξ` — the same objection the project has previously
answered with "…not the toy `trivialPresentation`, which satisfies neither the atoms nor the freeze".

This module closes that objection: it instantiates the dodge at the **genuine in-tree `Ω₄^{Spin}`
carrier** `PinPlusKTSpinForgetPhi.spinEmptyData prov`, with the distinguished slot the **genuine
`S²×S²` spin element** `SphereProdSpinElement.sphereProdSpinElement prov` (product of two Mathlib
spheres, empty characteristic surface — the same element whose Freeze-B class is unconditionally
`0`). The nonempty-carrier side condition is discharged by `Nonempty SphereProd`.

So on the real carrier, with the real `S²×S²` in the `s2s2` slot, primitive (1) is discharged by the
**unit cylinder** and nothing else. The `constRankTwoPresentation` companion likewise makes primitive
(2) vacuous there. Neither degenerate presentation survives `FaithfulRank`.

Additive module (imports `HandleTradeAtomVacuity.lean` + `SphereProdSpinElement.lean`); modifies
nothing. Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.HandleTradeAtomVacuity
import SKEFTHawking.SphereProdSpinElement

namespace SKEFTHawking.HandleTradeAtomVacuityConcrete

open scoped Manifold
open SKEFTHawking.SpinSigmaRoute SKEFTHawking.SphereProdSpinElement
open SKEFTHawking.PinPlusKTSpinForgetPhi SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.TangentialDataBordism SKEFTHawking.BordismTheory

variable {k : WithTop ℕ∞}

/-- The genuine `S²×S²` spin element has a **nonempty** underlying carrier (`S² × S²`) — the single
side condition the zero-geometry dodge needs. -/
theorem nonempty_sphereProdSpinElement_carrier (prov : CharPairWProviderPerOp (𝓡 4) k) :
    Nonempty (sphereProdSpinElement (k := k) prov).1.M :=
  inferInstanceAs (Nonempty SphereProd)

/-- **The rank-collapsed presentation ON THE GENUINE SPIN CARRIER**, with the genuine `S²×S²` spin
element in the `s2s2` slot. -/
noncomputable def collapsedSphereProdPresentation (prov : CharPairWProviderPerOp (𝓡 4) k) :
    SpinSigmaPresentation (spinEmptyData prov) :=
  collapsedPresentation (spinEmptyData prov) (sphereProdSpinElement prov)

/-- **PRIMITIVE (1) IS DISCHARGED BY A CYLINDER ON THE GENUINE CARRIER.** The raw handle-trace
cobordism `HandleTradeCobordism` — the phase's designated remaining manifold-surgery primitive —
holds for the rank-collapsed presentation over the in-tree `Ω₄^{Spin}` datum `spinEmptyData prov`
whose `s2s2` slot is the genuine `S²×S²` spin element. No handle, no surgery: the only cobordism in
the proof is the unit cylinder `(mapCylinder (sumEmpty …)).symm`.

Consequence for the route: a future E1 manifold-surgery foundation that *proved*
`HandleTradeCobordism` for some presentation would have proved nothing — the statement does not pin
the geometry. Only a presentation constrained to be `rank`-faithful can carry the Benedetti content
(see `HandleTradeAtomVacuity.SpinSigmaPresentation.FaithfulRank`). -/
theorem collapsedSphereProd_handleTradeCobordism (prov : CharPairWProviderPerOp (𝓡 4) k) :
    (collapsedSphereProdPresentation (k := k) prov).HandleTradeCobordism :=
  collapsedPresentation_handleTradeCobordism (spinEmptyData prov) (sphereProdSpinElement prov)
    (nonempty_sphereProdSpinElement_carrier prov)

/-- … and hence the two statement layers above it (`HandleTradeSplit`, `HyperbolicPeel`) on the
genuine carrier as well. -/
theorem collapsedSphereProd_hyperbolicPeel (prov : CharPairWProviderPerOp (𝓡 4) k) :
    (collapsedSphereProdPresentation (k := k) prov).HyperbolicPeel :=
  collapsedPresentation_hyperbolicPeel (spinEmptyData prov) (sphereProdSpinElement prov)
    (nonempty_sphereProdSpinElement_carrier prov)

/-- **The dodge is not ∀-vacuous on the genuine carrier either**: the handle-trade antecedent
genuinely fires at the `S²×S²` slot. -/
theorem collapsedSphereProd_hypothesis_fires (prov : CharPairWProviderPerOp (𝓡 4) k) :
    ∃ E : Fin 2 ⊕ Fin 0 ≃
        Fin ((collapsedSphereProdPresentation (k := k) prov).rank (sphereProdSpinElement prov)),
      IntCongr ((collapsedSphereProdPresentation (k := k) prov).form (sphereProdSpinElement prov))
        (Matrix.reindex E E (Matrix.fromBlocks Hyp 0 0 (0 : Matrix (Fin 0) (Fin 0) ℤ))) :=
  collapsedPresentation_hypothesis_fires (spinEmptyData prov) (sphereProdSpinElement prov)

/-- **The repair bites on the genuine carrier**: the rank-collapsed presentation over
`spinEmptyData` is refuted by `FaithfulRank` (additivity of `b₂` forces `b₂(S²×S² ⊔ S²×S²) = 4`,
which the collapsed rank cannot produce). -/
theorem collapsedSphereProd_not_faithfulRank (prov : CharPairWProviderPerOp (𝓡 4) k) :
    ¬ (collapsedSphereProdPresentation (k := k) prov).FaithfulRank :=
  collapsedPresentation_not_faithfulRank (spinEmptyData prov) (sphereProdSpinElement prov)

/-- **Primitive (2) is vacuous on the genuine carrier too**: over `spinEmptyData prov`, the
constant-rank-2 presentation (slot = the genuine `S²×S²` element) satisfies `HyperbolicBase` with no
manifold bounding anything, since it has no rank-`0` manifold at all. -/
theorem constRankTwoSphereProd_hyperbolicBase (prov : CharPairWProviderPerOp (𝓡 4) k) :
    (constRankTwoPresentation (spinEmptyData prov)
      (sphereProdSpinElement (k := k) prov)).HyperbolicBase :=
  constRankTwoPresentation_hyperbolicBase (spinEmptyData prov) (sphereProdSpinElement prov)

end SKEFTHawking.HandleTradeAtomVacuityConcrete
