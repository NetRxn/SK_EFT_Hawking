/-
# Phase 5q.H W-A arm 4 — STAGE 3: the REALIZED + PINNED characteristic-pair bordism datum.

Carrier surgery stages 1–2 (predecessor) built the DERIVED-BASIS realization datum
`GeoRealizationTied` (its `H₁`-boundary bases pinned to the ends' carried cohomology bases, the F2
fix) and the honest cylinder inhabitant `cylRealizationTied` with the geometric kernel identity
`transportedBInc = cylBd ⟹ L = cylLagrangian` (F1 discharged on the cylinder). The admissibility PIN
layer (`PinPlusWAdmPinned`) built the substrate-pinned Lefschetz–Wu certificates
`LefschetzWuPinned14/23` and the pinned provider `CharPairWProviderPinned` (the F3 fix).

**This module assembles the two fixes into ONE `Bor` shape** — `CharPairBorRealized` — the datum whose
membrane comes through `GeoRealizationTied.toMembrane` (ends' realizations instantiated at the two
`CharPairStrBundled`s' `surf`/`basis`) AND whose `P14`/`P23` carry the pin certificates, with the
admissibility drawn from a `CharPairWProviderPinned`. This is the building block the Stage-4 swap
consumes: it is the realized+pinned refinement of `CharPairBorTied`, so:

* the **anti-collapse `brown_eq` descends** unchanged (`CharPairBorRealized.brown_eq`) — the engine is
  L-agnostic and the computed kernel is still `(real.toMembrane).L`;
* it **forgets** to the tied form (`toTied`) — every realized+pinned datum IS a tied datum, so the
  realized carrier is a genuine sub-shape of the current one (registry-backing direction);
* the discriminating **cylinder op** `cylBorRealized` instantiates it end-to-end through the honest
  cylinder realization (`cylRealizationTied`), whose computed kernel is the geometric anti-diagonal
  `cylLagrangian` — never a free/synthetic submodule. The synthetic-`bInc` exploit
  (`doubleKillerBInc`, kernel = the e₈ graph) has NO `GeoRealizationTied` source, so it cannot inhabit
  this shape.

The membrane's END data live at `CharPairStr` level (n, q); the realization needs the BUNDLE (surf,
basis). The realized Bor is therefore indexed by the BUNDLES `σ τ : CharPairStrBundled`, and its
`real` field references `σ.surf`/`σ.basis` (resp. τ) directly — exactly the (n, q, surf) basis tie
the round-5 gate demanded.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusCharPairCylRealization
import SKEFTHawking.PinPlusCharPairNegRealization
import SKEFTHawking.PinPlusWAdmPinnedCore

open scoped Manifold
open SKEFTHawking.Brown SKEFTHawking.Brown.Z4Quadratic
open SKEFTHawking.BordismTheory SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairMembraneGeoRealization
open SKEFTHawking.PinPlusCharPairRealizationTied
open SKEFTHawking.PinPlusCharPairCylRealization
open SKEFTHawking.PinPlusCharPairNegRealization
open SKEFTHawking.PinPlusWAdmPinned

namespace SKEFTHawking.PinPlusCharPairBorRealized

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]

/-! ## §1. The realized + pinned `Bor` structure -/

/-- **The REALIZED + PINNED characteristic-pair bordism datum** (Stage 3a). Indexed by the two ends'
BUNDLES `σ τ : CharPairStrBundled` (the realization needs `surf`/`basis`). Refines `CharPairBorTied`:

* item 0/1 identical (`hWT2`, `P14`, `P23`, `hwu`) — but now `P14`/`P23` carry the SUBSTRATE PINS
  (`pin14`/`pin23`), so `hwu` is the HONEST `w₂(W) = 0`, not a free-`sqOp` artefact (F3 fix);
* the membrane is `real.toMembrane σ.q τ.q` of a genuine derived-basis realization `real`
  (`GeoRealizationTied` at the two ends' `surf`/`basis`), so the Taylor-leg submodule
  `L = ker (transportedBInc real.toData)` is a REALIZED geometric fold-kernel — never a free or
  synthetic `bInc` (F1/F2 fix). -/
structure CharPairBorRealized {s t : SingularManifold.{0} PUnit.{1} k I}
    (b : Bordism (I.prod (𝓡∂ 1)) s t) (σ : CharPairStrBundled I s) (τ : CharPairStrBundled I t) where
  /-- item 0: the bordism carrier is Hausdorff. -/
  hWT2 : T2Space b.W
  /-- item 1: the `(1,4)` Lefschetz–Wu datum. -/
  P14 : LefschetzWuDatum (TopCat.of b.W) ((I.prod (𝓡∂ 1)).boundary b.W) 1 4 5
  /-- item 1: the `(2,3)` Lefschetz–Wu datum. -/
  P23 : LefschetzWuDatum (TopCat.of b.W) ((I.prod (𝓡∂ 1)).boundary b.W) 2 3 5
  /-- item 1: W-admissibility `w₂(W) = 0`. -/
  hwu : wuW2 P14 P23 = 0
  /-- **the `(1,4)` pin** — `μ`, `cup`, `sqOp` are the substrate operations (honest `w₂` filter). -/
  pin14 : LefschetzWuPinned14 P14
  /-- **the `(2,3)` pin**. -/
  pin23 : LefschetzWuPinned23 P23
  /-- **THE REALIZATION** — a derived-basis membrane realization at the two ends' `surf`/`basis`. -/
  real : GeoRealizationTied (TopCat.of σ.surf.M) (TopCat.of τ.surf.M) σ.basis τ.basis
  /-- item 4: the τ-end-negated joint enhancement vanishes on the REALIZED kernel. -/
  htaylor : TaylorLegVanishes σ.q τ.q (real.toMembrane σ.q τ.q).L
  /-- the realized kernel is Lagrangian for the joint polar form. -/
  hlag : JointLagrangian σ.q τ.q (real.toMembrane σ.q τ.q).L

/-- **The realized `Bor` STILL forces grade equality of the ends** — the anti-collapse engine descends
UNCHANGED onto the realized computed kernel `(real.toMembrane).L`. The realized/pinned refinement costs
nothing in honesty: the computed grade `abk8 := brown ∘ q` remains a bordism invariant. -/
theorem CharPairBorRealized.brown_eq {s t : SingularManifold.{0} PUnit.{1} k I}
    {b : Bordism (I.prod (𝓡∂ 1)) s t} {σ : CharPairStrBundled I s} {τ : CharPairStrBundled I t}
    (β : CharPairBorRealized b σ τ) : σ.q.brown = τ.q.brown :=
  brown_eq_of_taylorLeg_lagrangian σ.q τ.q (β.real.toMembrane σ.q τ.q).L β.htaylor β.hlag

/-- **Forget the realization and pins**: a realized+pinned datum IS a tied datum (its membrane is the
concrete `real.toMembrane`). The registry-backing direction — the realized carrier is a genuine
sub-shape of the current tied one. -/
noncomputable def CharPairBorRealized.toTied {s t : SingularManifold.{0} PUnit.{1} k I}
    {b : Bordism (I.prod (𝓡∂ 1)) s t} {σ : CharPairStrBundled I s} {τ : CharPairStrBundled I t}
    (β : CharPairBorRealized b σ τ) : CharPairBorTied b σ.toCharPairStr τ.toCharPairStr :=
  ⟨β.hWT2, β.P14, β.P23, β.hwu, β.real.toMembrane σ.q τ.q, β.htaylor, β.hlag⟩

/-! ## §2. The assembly helper — item 1 (pinned) drawn from a `CharPairWProviderPinned` -/

/-- Assemble a `CharPairBorRealized` from the concretely-buildable data (T2 of `W`, the realization,
the exact Taylor leg, the Lagrangian) + item 1 (P14/P23/hwu AND the substrate pins) drawn from a
PINNED provider. -/
noncomputable def mkCharPairBorRealized (prov : CharPairWProviderPinned I k)
    {s t : SingularManifold.{0} PUnit.{1} k I} (b : Bordism (I.prod (𝓡∂ 1)) s t)
    {σ : CharPairStrBundled I s} {τ : CharPairStrBundled I t}
    (hWT2 : T2Space b.W)
    (real : GeoRealizationTied (TopCat.of σ.surf.M) (TopCat.of τ.surf.M) σ.basis τ.basis)
    (htaylor : TaylorLegVanishes σ.q τ.q (real.toMembrane σ.q τ.q).L)
    (hlag : JointLagrangian σ.q τ.q (real.toMembrane σ.q τ.q).L) :
    CharPairBorRealized b σ τ where
  hWT2 := hWT2
  P14 := (prov.wadm b).wadm.P14
  P23 := (prov.wadm b).wadm.P23
  hwu := (prov.wadm b).wadm.hwu
  pin14 := (prov.wadm b).pin14
  pin23 := (prov.wadm b).pin23
  real := real
  htaylor := htaylor
  hlag := hlag

/-! ## §3. The discriminating cylinder op — the honest realization's kernel is the anti-diagonal -/

/-- **`cylBor` instantiates on the realized+pinned form** — the reflexive cylinder over `s` carries the
BUNDLE `σ` to itself, its membrane the honest cylinder realization `cylRealizationTied` of the end
surface `Σ_σ = σ.surf` at `σ.basis`, whose COMPUTED kernel is the geometric anti-diagonal
`cylLagrangian σ.n` (`cylRealizationTied_toMembrane_L`). The synthetic-`bInc` e₈ exploit cannot
inhabit this: it has no `GeoRealizationTied` source. -/
noncomputable def cylBorRealized (prov : CharPairWProviderPinned I k)
    {s : SingularManifold.{0} PUnit.{1} k I} (σ : CharPairStrBundled I s) :
    CharPairBorRealized (reflCylinder s) σ σ :=
  haveI := σ.surfT2
  mkCharPairBorRealized prov (reflCylinder s)
    (by haveI := σ.t2; exact inferInstanceAs (T2Space (s.M × Set.Icc (0 : ℝ) 1)))
    (cylRealizationTied (TopCat.of σ.surf.M) σ.basis)
    (by rw [cylRealizationTied_toMembrane_L]; exact taylorLeg_cyl σ.q)
    (by rw [cylRealizationTied_toMembrane_L]; exact lagrangian_cyl σ.q)

/-! ## §4. `revBor` — end-reversal transports with the SAME realization -/

/-- **`revBor` instantiates on the realized+pinned form** — end-reversal (`charPairBundledRevStr` on
both ends) keeps the SAME surface/basis (`revStr` negates only the enhancement `q`), so the realization
`β.real` transports UNCHANGED; the Taylor leg survives (`jointEnhancement_neg_q`, `−0 = 0`) and the
Lagrangian is literally unchanged (`jointEnhancement_neg_B`). The pins are the same `W`'s, unchanged. -/
noncomputable def revBorRealized {s t : SingularManifold.{0} PUnit.{1} k I}
    {b : Bordism (I.prod (𝓡∂ 1)) s t} {σ : CharPairStrBundled I s} {τ : CharPairStrBundled I t}
    (β : CharPairBorRealized b σ τ) :
    CharPairBorRealized b (charPairBundledRevStr σ) (charPairBundledRevStr τ) where
  hWT2 := β.hWT2
  P14 := β.P14
  P23 := β.P23
  hwu := β.hwu
  pin14 := β.pin14
  pin23 := β.pin23
  real := β.real
  htaylor := by
    -- convert both the goal's realized kernel and β.htaylor's to the PROVEN `toMembrane_L` map
    -- form (q-independent), sidestepping the whnf/keyed-match wall on the bundle-reindexed ends.
    have h := β.htaylor
    rw [β.real.toMembrane_L σ.q τ.q] at h
    show TaylorLegVanishes (neg σ.q) (neg τ.q)
      ((β.real.toMembrane (neg σ.q) (neg τ.q)).L)
    rw [β.real.toMembrane_L (neg σ.q) (neg τ.q)]
    intro l hl
    show (jointEnhancement (neg σ.q) (neg τ.q)).q l = 0
    rw [jointEnhancement_neg_q, h l hl, neg_zero]
  hlag := by
    have h := β.hlag
    rw [β.real.toMembrane_L σ.q τ.q] at h
    show JointLagrangian (neg σ.q) (neg τ.q) ((β.real.toMembrane (neg σ.q) (neg τ.q)).L)
    rw [β.real.toMembrane_L (neg σ.q) (neg τ.q)]
    intro v hv
    refine h v (fun l hl => ?_)
    have hvl := hv l hl
    rwa [show (jointEnhancement (neg σ.q) (neg τ.q)).B
        = (jointEnhancement σ.q τ.q).B from jointEnhancement_neg_B σ.q τ.q] at hvl

/-! ## §5. `negBor` — the doubling op on the realized+pinned form -/

/-- **`negBor` instantiates on the realized+pinned form** — the honest inverse law
`(M,σ̄) ⊔ (M,σ) → ∅` with the membrane REALIZED: the doubling realization
(`doublingRealizationTied`, Stage 3b) is the SAME cylinder `Σ_σ × [0,1]` with both ends grouped onto
the σ-side (`U = univ`) and the EMPTY τ-end, whose computed kernel is EXACTLY
`ker (negBorBInc σ.n)` — the reindexed anti-diagonal (`doublingRealizationTied_transportedBInc`) —
on which the τ-end-negated joint form is metabolic (the same `diag_metabolic … .reindex … .orthSum`
chain as the tied `charPairNegBorTied`). The synthetic-`bInc` e₈ exploit cannot inhabit this: it has
no `GeoRealizationTied` source. -/
noncomputable def negBorRealized (prov : CharPairWProviderPinned I k)
    {s : SingularManifold.{0} PUnit.{1} k I} (σ : CharPairStrBundled I s) :
    CharPairBorRealized (doublingBordism s)
      (charPairBundledSumStr (charPairBundledRevStr σ) σ) charPairBundledEmpty :=
  haveI := σ.surfT2
  haveI : IsEmpty ((charPairBundledEmpty
      : CharPairStrBundled I (emptySM : SingularManifold.{0} PUnit.{1} k I)).surf.M) :=
    inferInstanceAs (IsEmpty PEmpty)
  have hSe : IsMetabolic (Z4Quadratic.neg (stdQuadratic 0))
      (⊤ : Submodule (ZMod 2) (Fin 0 → ZMod 2)) :=
    ⟨fun l _ => by rw [Subsingleton.elim l 0]; exact (Z4Quadratic.neg (stdQuadratic 0)).q_zero,
     fun _ _ => Submodule.mem_top⟩
  have hSs : IsMetabolic (charPairSumStr (charPairRevStr σ.toCharPairStr) σ.toCharPairStr).q
      ((cylLagrangian σ.n).comap (LinearMap.funLeft (ZMod 2) (ZMod 2) finSumFinEquiv)) :=
    (diag_metabolic (neg σ.q) σ.q (fun a => neg_add_cancel _) rfl).reindex finSumFinEquiv
  have hmeta := hSs.orthSum hSe
  mkCharPairBorRealized prov (doublingBordism s)
    (by haveI := σ.t2; exact inferInstanceAs (T2Space (s.M × Set.Icc (0 : ℝ) 1)))
    (doublingRealizationTied (TopCat.of σ.surf.M) σ.basis
      (TopCat.of (charPairBundledEmpty (I := I) (k := k)).surf.M)
      (charPairBundledEmpty (I := I) (k := k)).basis)
    (by
      show TaylorLegVanishes _ _ (LinearMap.ker (transportedBInc
        (doublingRealizationTied (TopCat.of σ.surf.M) σ.basis
          (TopCat.of (charPairBundledEmpty (I := I) (k := k)).surf.M)
          (charPairBundledEmpty (I := I) (k := k)).basis).toData))
      rw [doublingRealizationTied_transportedBInc]
      show TaylorLegVanishes _ _ (LinearMap.ker (negBorBInc σ.n))
      rw [negBorBInc_ker]
      exact hmeta.1)
    (by
      show JointLagrangian _ _ (LinearMap.ker (transportedBInc
        (doublingRealizationTied (TopCat.of σ.surf.M) σ.basis
          (TopCat.of (charPairBundledEmpty (I := I) (k := k)).surf.M)
          (charPairBundledEmpty (I := I) (k := k)).basis).toData))
      rw [doublingRealizationTied_transportedBInc]
      show JointLagrangian _ _ (LinearMap.ker (negBorBInc σ.n))
      rw [negBorBInc_ker]
      exact hmeta.2)

/-! ## §6. `symmBor` — bordism reversal on the realized+pinned form -/

/-- **`symmBor` instantiates on the realized+pinned form** — bordism reversal swaps the ends; the
realization transports by the END-SWAP `GeoRealizationTied.swap` (same geometry, complemented clopen
split), whose transported boundary-inclusion is the original precomposed with the `Sum.swap`
regrouping (`transportedBInc_swap`), so the swapped membrane's computed kernel is the honest comap —
exactly the tied `charPairSymmBorTied` membrane shape, from which the Taylor leg + Lagrangian
descend. `b.symm.W = b.W`, so item 1 AND the substrate pins are inherited unchanged. -/
noncomputable def symmBorRealized {s t : SingularManifold.{0} PUnit.{1} k I}
    {b : Bordism (I.prod (𝓡∂ 1)) s t} {σ : CharPairStrBundled I s} {τ : CharPairStrBundled I t}
    (β : CharPairBorRealized b σ τ) : CharPairBorRealized b.symm τ σ where
  hWT2 := β.hWT2
  P14 := β.P14
  P23 := β.P23
  hwu := β.hwu
  pin14 := β.pin14
  pin23 := β.pin23
  real := β.real.swap
  htaylor := by
    show TaylorLegVanishes _ _ (LinearMap.ker (transportedBInc β.real.swap.toData))
    rw [GeoRealizationTied.transportedBInc_swap]
    exact (charPairSymmBorTied β.toTied).htaylor
  hlag := by
    show JointLagrangian _ _ (LinearMap.ker (transportedBInc β.real.swap.toData))
    rw [GeoRealizationTied.transportedBInc_swap]
    exact (charPairSymmBorTied β.toTied).hlag

end SKEFTHawking.PinPlusCharPairBorRealized
