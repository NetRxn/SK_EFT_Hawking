/-
# Phase 5q.H (W-A arm 4) — the CROSS-candidate restriction, reduced to a single ℤ/2 nonvanishing

The interior-local-Künneth residual `cylFundClassCandidate_restricts` (the last `hcls` hole of the
concrete cylinder `[W,∂W] = [M] × [I,∂I]`) is `RestrictsToRelGen ∂W cylGen cylFundClassCandidate`:
the cross-product candidate must restrict to the interior chart generator `cylGen x hx` at every
interior point `x ∉ ∂W`. Because the interior local homology `Hₘ'₊₃(W, W∖x)` is the **two-element**
group `ℤ/2` (that is exactly what the iso `cylGen x hx : … ≃ₗ ℤ/2` asserts), the equality
`restrictBd … candidate = (cylGen x hx).symm 1` is — by `eq_symm_one_iff_ne_zero` — *equivalent* to
the single non-vanishing `restrictBd … candidate ≠ 0`. This is the exact reduction the interval
factor used (`SingularIntervalPairClass.intervalPairClass_restricts` via `restrictBd_zGen_ne_zero`),
transported to the product: it converts the `RestrictsToRelGen` obligation of
`hasRelFundClass_of_candidate_restricts` into the sharpest possible form — nonvanishing of ONE
explicit prism class in a `ℤ/2`.

The residual crux then is the honest interior local-Künneth: the cross of the base local generator
`[M]|ₓ` (nonzero, `SingularFundamentalClass.fundamentalClass_restricts`) with the interval local
generator `[I,∂I]|ₜ` (nonzero, `SingularIntervalPairClass.restrictBd_zGen_ne_zero`) is the nonzero
product local generator — stated here as the named nonvanishing `CrossCandidateRestrictsNeZero`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderCross
import SKEFTHawking.SingularIntervalPairClass

open scoped Manifold
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeMV
open SKEFTHawking.SingularRelativeFunctoriality
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCross

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossRestrict

noncomputable section

variable {m' : ℕ}
  {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m' + 2))) M]

/-! ## §1. The reduction of the candidate's `RestrictsToRelGen` to a single ℤ/2 nonvanishing

`cylGen x hx : Hₘ'₊₃(W, W∖x) ≅ ℤ/2` witnesses the interior local homology is the two-element group.
So `α = (cylGen x hx).symm 1 ↔ α ≠ 0` (`eq_symm_one_iff_ne_zero`), and `RestrictsToRelGen` for the
cross candidate collapses to "the restriction is nonzero at every interior point". -/

/-- **The candidate's `RestrictsToRelGen`, in nonvanishing form.** IF the cross-product candidate
`[M] × [I, ∂I]` restricts to a **nonzero** class at every interior point `x ∉ ∂W` (`hne`), THEN it
restricts to the interior chart generator `cylGen x hx` there — because `Hₘ'₊₃(W, W∖x) ≅ ℤ/2` has a
*unique* nonzero element, forced to be the generator (`eq_symm_one_iff_ne_zero`). The
`RestrictsToRelGen` obligation and the nonvanishing obligation are equivalent. -/
theorem restrictsToRelGen_candidate_of_ne_zero [T1Space (cylW M)]
    (hne : ∀ (x : ↑(TopCat.of (cylW M))) (hx : x ∉ (cylModel m').boundary (cylW M)),
      restrictBd (X := TopCat.of (cylW M)) ((cylModel m').boundary (cylW M)) hx (m' + 1 + 2)
        (cylFundClassCandidate (M := M) (m' := m')) ≠ 0) :
    RestrictsToRelGen (X := TopCat.of (cylW M)) (m := m' + 1)
      ((cylModel m').boundary (cylW M)) (cylGen (M := M) (m' := m'))
      (cylFundClassCandidate (M := M) (m' := m')) :=
  fun x hx =>
    (SKEFTHawking.SingularIntervalPairClass.eq_symm_one_iff_ne_zero
      (cylGen (M := M) (m' := m') x hx)).mpr (hne x hx)

/-- **The concrete cylinder `HasRelFundClass` existence, reduced to a single ℤ/2 nonvanishing.** With
the cross-product candidate `[M] × [I, ∂I]` restricting to a nonzero class at every interior point,
the cylinder's `HasRelFundClass` existence hole `hcls` is filled *by it*. This is the sharpest form of
the residual `cylFundClassCandidate_restricts`: the sole remaining obligation is that ONE explicit
prism class is nonzero in the two-element interior local homology. -/
theorem hasRelFundClass_of_candidate_ne_zero [T1Space (cylW M)]
    (hne : ∀ (x : ↑(TopCat.of (cylW M))) (hx : x ∉ (cylModel m').boundary (cylW M)),
      restrictBd (X := TopCat.of (cylW M)) ((cylModel m').boundary (cylW M)) hx (m' + 1 + 2)
        (cylFundClassCandidate (M := M) (m' := m')) ≠ 0) :
    HasRelFundClass (X := TopCat.of (cylW M)) ((cylModel m').boundary (cylW M))
      (cylGen (M := M) (m' := m')) :=
  hasRelFundClass_of_candidate_restricts (restrictsToRelGen_candidate_of_ne_zero hne)

/-- **The concrete cylinder datum, reduced to the single ℤ/2 nonvanishing.** With the candidate's
restriction nonzero at every interior point, the whole `RelFundClassDatum` — hence the `μ` functional
feeding the Poincaré–Lefschetz Wu tower — is available for the concrete cross-product class
`[W, ∂W] = [M] × [I, ∂I]`. -/
def cylinderRelFundClassDatum_of_candidate_ne_zero [T1Space (cylW M)]
    (hne : ∀ (x : ↑(TopCat.of (cylW M))) (hx : x ∉ (cylModel m').boundary (cylW M)),
      restrictBd (X := TopCat.of (cylW M)) ((cylModel m').boundary (cylW M)) hx (m' + 1 + 2)
        (cylFundClassCandidate (M := M) (m' := m')) ≠ 0) :
    RelFundClassDatum (X := TopCat.of (cylW M)) (m := m' + 1) ((cylModel m').boundary (cylW M)) :=
  cylinderRelFundClassDatum (hasRelFundClass_of_candidate_ne_zero hne)

/-! ## §2. The chain-level restriction identity — the candidate restricts to the concrete prism chain

Exposing the crux geometrically: the restriction of `[M] × [I, ∂I]` at an interior point `x` is the
class of the SAME prism chain `crossChain (m'+2) z` (`= prismOp graphHom z` for a cycle
representative `z` of `[M]`), now viewed relative to the puncture `W ∖ x`. This is the product
analogue of the interval factor's `SingularIntervalPairClass.restrictBd_zGen` (which exposed
`bdPathChain`). Restriction is the identity on chains (`relIncl_mk`), so the identity is essentially
definitional at the cycle level: `restrictBd` reinterprets the same relative cycle under the larger
subspace `{x}ᶜ ⊇ ∂W`. -/

/-- **The candidate's restriction is the class of the prism chain rel the puncture.** For any cycle
representative `z` of `[M]` (`hz`), the restriction of the cross-product candidate at an interior
point `x` is `[crossRelCycle z]` reinterpreted rel `{x}ᶜ` (via `relCyclesMap` of the identity — the
same underlying prism chain `crossChain (m'+2) z`). The crux `restrictBd … candidate ≠ 0` is thus
exactly "the prism of a fundamental cycle is nonzero rel the puncture" — the honest interior
local-Künneth nonvanishing. -/
theorem restrictBd_cylFundClassCandidate
    (x : ↑(TopCat.of (cylW M))) (hx : x ∉ (cylModel m').boundary (cylW M))
    (z : cycles (TopCat.of M) (m' + 2))
    (hz : SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := M)
      = Homology.mk (TopCat.of M) (m' + 2) z) :
    restrictBd (X := TopCat.of (cylW M)) ((cylModel m').boundary (cylW M)) hx (m' + 1 + 2)
        (cylFundClassCandidate (M := M) (m' := m'))
      = RelativeHomology.mk (X := TopCat.of (cylW M)) ({x}ᶜ) (m' + 1 + 2)
          (relCyclesMap (ContinuousMap.id ↑(TopCat.of (cylW M)))
            (fun _ hmem => Set.subset_compl_singleton_iff.mpr hx hmem) (m' + 1 + 2)
            (crossRelCycle (slice_one_mapsTo (M := M) (m' := m'))
              (slice_zero_mapsTo (M := M) (m' := m')) (m' + 1) z)) := by
  show restrictBd (X := TopCat.of (cylW M)) ((cylModel m').boundary (cylW M)) hx (m' + 1 + 2)
      (crossH (M := TopCat.of M) (slice_one_mapsTo (M := M) (m' := m'))
        (slice_zero_mapsTo (M := M) (m' := m')) (m' + 1)
        (SKEFTHawking.SingularFundamentalClass.fundamentalClass (m := m') (M := M))) = _
  rw [hz, crossH_mk, restrictBd, relIncl_mk]

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossRestrict
