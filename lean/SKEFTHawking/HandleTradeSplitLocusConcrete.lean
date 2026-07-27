/-
# Phase 5q.H (N1a) — the constrained Freeze-A presentation, ON THE GENUINE SPIN CARRIER

`HandleTradeAtomVacuityConcrete.lean` landed the *negative* result on the genuine carrier: over
`PinPlusKTSpinForgetPhi.spinEmptyData prov`, with the genuine `S²×S²` spin element
`SphereProdSpinElement.sphereProdSpinElement prov` in the `s2s2` slot, the Freeze-A primitive
`HandleTradeCobordism` is discharged by a **unit cylinder**
(`collapsedSphereProd_handleTradeCobordism`).

This module lands the *positive* counterpart on the same carrier: the constrained presentation type
`FaithfulSpinSigmaPresentation` of `HandleTradeSplitLocus.lean` — on which the re-scoped primitive
`BordantToSplitLocus` lives — is **inhabited over the genuine `Ω₄^{Spin}` carrier**, with the genuine
`S²×S²` manifold and its genuine spin structure in the `s2s2` slot, and with **unbounded rank** (so it
is not confined to the Sylvester-excluded `rank ≤ 2` region where both zero-geometry dodges live).

Why this matters: §7 of `HandleTradeSplitLocus.lean` states the whole re-scoped Freeze-A chain as
theorems *conditional on* a `FaithfulSpinSigmaPresentation`. Were that type empty over the genuine
carrier, the chain would be vacuous. It is not.

**Honest scope (do not over-read).** The witness's `rank` is a *declared* additive `b₂`-label
(`SpinSigmaRoute.rankGraded`), not one computed from the manifold — pinning `rank` to the true `b₂` is
E1's `interMatrix` job at instantiation. What is established here is (i) the constrained type is
non-empty over the genuine carrier, (ii) the carrier's bordism group is untouched by the decoration
(`rankGraded_equiv`), and (iii) the witness cannot discharge the re-scoped primitive for free —
`genuine_subsingleton_of_bordantToSplitLocus` shows that doing so would collapse the genuine
`Ω₄^{Spin}` carrier itself.

Additive module (imports `HandleTradeSplitLocus.lean` + `HandleTradeAtomVacuityConcrete.lean`);
modifies nothing. Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.HandleTradeSplitLocus
import SKEFTHawking.HandleTradeAtomVacuityConcrete

namespace SKEFTHawking.HandleTradeSplitLocusConcrete

open scoped Manifold
open SKEFTHawking.SpinSigmaRoute SKEFTHawking.SphereProdSpinElement
open SKEFTHawking.HandleTradeAtomVacuityConcrete
open SKEFTHawking.PinPlusKTSpinForgetPhi SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.TangentialDataBordism SKEFTHawking.BordismTheory

variable {k : WithTop ℕ∞}

/-- **A faithful (constrained) σ-presentation over the genuine `Ω₄^{Spin}` carrier**, with the
genuine `S²×S²` spin element — the product of two Mathlib spheres carrying its genuine spin
structure — in the distinguished `s2s2` slot, labelled `b₂ = 2`. The `rank`-faithfulness fields
(`b₂ = 0` on an empty carrier, `b₂` additive under disjoint union) hold by construction. -/
noncomputable def genuineFaithfulPresentation (prov : CharPairWProviderPerOp (𝓡 4) k) :
    FaithfulSpinSigmaPresentation (rankGraded (spinEmptyData prov)) :=
  gradedPresentation (spinEmptyData prov) (sphereProdSpinElement prov).1
    (nonempty_sphereProdSpinElement_carrier prov) (sphereProdSpinElement prov).2

/-- **The decoration does not change the carrier's bordism group.** `Ω^(rankGraded (spinEmptyData
prov)) ≃+ Ω^(spinEmptyData prov)` — the genuine `Ω₄^{Spin}` carrier of the phase. So the constrained
presentation above is not over a toy: it is over the genuine group, with a declared additive `b₂`
riding along. -/
noncomputable def genuine_equiv (prov : CharPairWProviderPerOp (𝓡 4) k) :
    DataBordismGrp (rankGraded (spinEmptyData prov)) ≃+ DataBordismGrp (spinEmptyData prov) :=
  rankGraded_equiv (spinEmptyData prov)

/-- **The constrained type over the genuine carrier is NOT rank-bounded** — `n` copies of the
genuine `S²×S²` have rank `2n`. Contrast the two zero-geometry dodges of the vacuity audit, both of
which are rank-`≤ 2` and therefore, by `no_generator_of_rank_le_two`, cannot host the route's
`σ = −16` generator at all. -/
theorem genuine_rank_nsum_s2s2 (prov : CharPairWProviderPerOp (𝓡 4) k) (n : ℕ) :
    (genuineFaithfulPresentation (k := k) prov).rank
      (StrMfd.nsum (genuineFaithfulPresentation (k := k) prov).s2s2 n) = 2 * n :=
  FaithfulSpinSigmaPresentation.rank_nsum_s2s2 _ n

/-- … hence the genuine-carrier witness escapes the Sylvester-excluded region entirely. -/
theorem genuine_not_rank_le_two (prov : CharPairWProviderPerOp (𝓡 4) k) :
    ¬ ∀ p, (genuineFaithfulPresentation (k := k) prov).rank p ≤ 2 :=
  FaithfulSpinSigmaPresentation.not_rank_le_two _

/-- **The `s2s2` slot's carrier is nonempty — derived on the genuine carrier too.** In the vacuity
audit this was an explicit side condition of the zero-geometry discharge
(`collapsedPresentation_handleTradeCobordism`'s `hp₀`); on the constrained type it is a theorem, so
the split locus `q ⊔ S²×S²` cannot degenerate into a unit cylinder. -/
theorem genuine_s2s2_carrier_nonempty (prov : CharPairWProviderPerOp (𝓡 4) k) :
    Nonempty (genuineFaithfulPresentation (k := k) prov).s2s2.1.M :=
  FaithfulSpinSigmaPresentation.s2s2_carrier_nonempty _

/-- **The genuine-carrier witness does not dodge the re-scoped primitive.** Its signature hom is the
zero map, so discharging `BordantToSplitLocus` together with the rank-0 base and the `S²×S²` bounding
freeze would force the **genuine** `Ω₄^{Spin}` carrier `DataBordismGrp (spinEmptyData prov)` to be
trivial. This is the exact regression the audit demands of any newly-stated primitive: the
inhabitation witness that proves the constrained type non-empty must not simultaneously make the
primitive free — and it does not. -/
theorem genuine_subsingleton_of_bordantToSplitLocus (prov : CharPairWProviderPerOp (𝓡 4) k)
    (h : (genuineFaithfulPresentation (k := k) prov).BordantToSplitLocus)
    (hBase : (genuineFaithfulPresentation (k := k) prov).toSpinSigmaPresentation.HyperbolicBase)
    (hB : (genuineFaithfulPresentation (k := k) prov).toSpinSigmaPresentation.SphereProductBounds)
    (y : DataBordismGrp (spinEmptyData prov)) : y = 0 :=
  FaithfulSpinSigmaPresentation.gradedPresentation_subsingleton_of_bordantToSplitLocus
    (spinEmptyData prov) (sphereProdSpinElement prov).1
    (nonempty_sphereProdSpinElement_carrier prov) (sphereProdSpinElement prov).2 h hBase hB y

end SKEFTHawking.HandleTradeSplitLocusConcrete
