/-
# Phase 5q.H close-out (#208) — THE S²×D³ COHOMOLOGY PACK: three of the six `hBbord` atoms.

#206 (`PinPlusKTSphereProdWAdm`) sharpened the sole `hBbord` residual to six atoms for a
`W = S²×D³`-type coboundary `b`. The `(1,4)` Wu leg is SETTLED-FREE (`degenerateP14`); the residual
is `{a T2 coboundary b · RelFundClassDatum D · Subsingleton (Cohomology W 1) ·
Subsingleton (RelativeCohomology ∂W 4) · the pinned (2,3) datum P23 · wuClass P23 = 0}`. This module
attacks the three cohomology atoms:

1. `Subsingleton (Cohomology W 1)` — `H¹(W;ℤ/2) = 0` (`W ≃ S²`).
2. `Subsingleton (RelativeCohomology ∂W 4)` — `H⁴(W,∂W;ℤ/2) = 0`.
3. `RelFundClassDatum` — `[W,∂W] ∈ H₅(W,∂W;ℤ/2)`.

## Concrete-model-vs-abstract decision (recorded).

The three atoms quantify over the coboundary's abstract carrier `b.W`. For a *fully generic* `b.W`
they are NOT theorems — a torus `W` falsifies atom 1. So they are intrinsically homotopy-type
obligations on `b.W`, and full deletion for abstract `b.W` is impossible; the #206 pattern keeps `b`
abstract and consumes the atoms as hypotheses. The honest, maximal narrowing therefore **reduces each
cohomological atom to its sharpest, most primitive, W-INDEPENDENT homological sub-atom** via in-tree
machinery (universal coefficients + the relative-cohomology pair LES), so the eventual geometric
coboundary provider discharges strictly simpler obligations, AND demonstrates that the reductions
bottom out at TRUE facts on the concrete `Sph 2` sphere bank. Each reduction is a genuine narrowing
(a cohomology-subsingleton becomes a homology-subsingleton or a lower-degree cohomology-subsingleton),
not a repackaging.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SingularUniversalCoeff
import SKEFTHawking.SingularKroneckerEquiv
import SKEFTHawking.SingularRelativeKroneckerEquiv
import SKEFTHawking.PinPlusKTSphereProdWAdm
import SKEFTHawking.PinPlusTraceRelFundReduce

open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularKroneckerEquiv SKEFTHawking.SingularRelativeKroneckerEquiv

namespace SKEFTHawking.PinPlusKTSphereProdCohomology

/-! ## §1. Atom 1 — `H¹(W;ℤ/2) = 0` reduced to `H₁(W;ℤ/2) = 0` (universal coefficients). -/

variable {X : TopCat}

/-- **Atom 1, W-independent reduction.** Over the field `ℤ/2` the Kronecker pairing is a perfect
duality `Hᵏ(X) ≅ (Hₖ(X))^*` (`kroneckerHEquiv`), so a vanishing homology group forces a vanishing
cohomology group: `Subsingleton (Homology X (N+1)) → Subsingleton (Cohomology X (N+1))`. For
`N = 0`, `X = W ≃ S²`, this is `H¹(W;ℤ/2) = 0` from `H₁(W;ℤ/2) = 0` — the sharpest sub-atom of the
`Subsingleton (Cohomology W 1)` atom. -/
theorem subsingleton_cohomology_of_homology (N : ℕ) [Subsingleton (Homology X (N + 1))] :
    Subsingleton (Cohomology X (N + 1)) := by
  haveI : Subsingleton (Homology X (N + 1) →ₗ[ZMod 2] ZMod 2) :=
    ⟨fun f g => LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
  exact (kroneckerHEquiv (X := X) N).toEquiv.subsingleton

/-! ## §2. Atom 2 — `H⁴(W,∂W;ℤ/2) = 0` reduced to `H₄(W,∂W;ℤ/2) = 0` (relative universal
coefficients). -/

/-- **Atom 2, W-independent reduction.** The relative Kronecker pairing is a perfect duality
`Hᵏ(X,S) ≅ (Hₖ(X,S))^*` over `ℤ/2` (`relKroneckerHEquiv`), so a vanishing relative homology group
forces a vanishing relative cohomology group:
`Subsingleton (RelativeHomology S (N+1)) → Subsingleton (RelativeCohomology S (N+1))`. For `N = 3`,
`S = ∂W`, this is `H⁴(W,∂W;ℤ/2) = 0` from `H₄(W,∂W;ℤ/2) = 0` (Poincaré–Lefschetz `≅ H¹(W) = 0`) —
the sharpest sub-atom of the `Subsingleton (RelativeCohomology ∂W 4)` atom. The exact relative twin
of `subsingleton_cohomology_of_homology`. -/
theorem subsingleton_relativeCohomology_of_relativeHomology (S : Set ↑X) (N : ℕ)
    [Subsingleton (RelativeHomology S (N + 1))] : Subsingleton (RelativeCohomology S (N + 1)) := by
  haveI : Subsingleton (RelativeHomology S (N + 1) →ₗ[ZMod 2] ZMod 2) :=
    ⟨fun f g => LinearMap.ext fun x => by rw [Subsingleton.elim x 0, map_zero, map_zero]⟩
  exact (relKroneckerHEquiv S N).toEquiv.subsingleton

/-! ## §3. Atom 3 — the `[W,∂W]` datum reduced to the class-existence witness `HasRelFundClass`. -/

open SKEFTHawking.PoincareLefschetzRelFundClass SKEFTHawking.PoincareLefschetzRelFundClassGeom
open SKEFTHawking.PinPlusTraceRelFundReduce (εtrace)
open SKEFTHawking.BordismTheory
open scoped Manifold

section Atom3

variable {k : WithTop ℕ∞} {s t : SingularManifold.{0} PUnit.{1} k (𝓡 4)}

/-- **Atom 3, reduced to the single class-existence witness.** For a `W = S²×D³`-type coboundary
`b : Bordism ((𝓡 4).prod (𝓡∂ 1)) s t`, the carrier-agnostic provider `relFundClassDatumOf` (canonical
`εtrace : E⁴×E¹ ≃L E⁵`, interior generators constructed from the trace model) reduces the
`RelFundClassDatum` atom to exactly the class-existence witness `HasRelFundClass` (the relative
Hatcher-3.27(b) MV-cover existence of `[W,∂W]` restricting to the interior generator family). The `T1`
separation certificate is FREE from the T2 the coboundary already carries. This strips atom 3 from a
bundled datum to a single existence proposition. -/
noncomputable def relFundDatum_ofHasClass (b : Bordism ((𝓡 4).prod (𝓡∂ 1)) s t)
    (hWT2 : T2Space b.W)
    (hasClass : letI := hWT2.t1Space
      HasRelFundClass (X := TopCat.of b.W) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W)
        (interiorGenFamily (W := b.W) ((𝓡 4).prod (𝓡∂ 1)) εtrace)) :
    RelFundClassDatum (X := TopCat.of b.W) (m := 3) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W) :=
  letI := hWT2.t1Space
  relFundClassDatumOf (W := b.W) ((𝓡 4).prod (𝓡∂ 1)) εtrace hasClass

end Atom3

/-! ## §4. The narrowing wiring — `SphereProdCoboundaryWAdm` (hence `hBbord`) from the reduced atoms. -/

open SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.PoincareLefschetzWuAssembly
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.PinPlusWAdmPinned
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.PinPlusCharPairRealizationTied
open SKEFTHawking.PinPlusKTSpinForgetPhi
open SKEFTHawking.PinPlusCharPairEmptySourceRealization
open SKEFTHawking.PinPlusKTSphereProdBordism
open SKEFTHawking.PinPlusKTSphereProdWAdm
open SKEFTHawking.PinPlusKTAssemblyResiduals
open SKEFTHawking.PinPlusKTSpinPresentationRow
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.PinPlusKTExtension
open SKEFTHawking.PinPlusKTKernelSector
open SKEFTHawking.PinPlusKTKernelSpinRoute
open SKEFTHawking.PinPlusCharPairSurfaceTie
open SKEFTHawking.PinPlusKTKerPhiDoubles
open SKEFTHawking.PinPlusKTSectorGeometricReduce
open SKEFTHawking.PinPlusTraceCapstoneResidualRow
open SKEFTHawking.PinPlusKTBinderDischarge
open SKEFTHawking.PinPlusKTCollapseDischarge
open SKEFTHawking.PinPlusKTFreezeDischarge
open SKEFTHawking.T2TangentialBordism SKEFTHawking.TangentialDataBordism

section Wiring

/-- **`SphereProdCoboundaryWAdm` from the REDUCED cohomology atoms.** The #206 residual
`sphereProdCoboundaryWAdm_of_degenerate14` consumed three cohomology atoms — `RelFundClassDatum D`,
`Subsingleton (Cohomology W 1)`, `Subsingleton (RelativeCohomology ∂W 4)`. This narrows them to their
sharpest sub-atoms:
* atom 3 `RelFundClassDatum` → `hasClass : HasRelFundClass …` (the single class-existence witness;
  interior generators + `T1` free, via `relFundDatum_ofHasClass`),
* atom 1 `Subsingleton (Cohomology W 1)` → `Subsingleton (Homology W 1)` (universal coefficients),
* atom 2 `Subsingleton (RelativeCohomology ∂W 4)` → `Subsingleton (RelativeHomology ∂W 4)` (relative
  universal coefficients).

The `(2,3)` Poincaré–Lefschetz half (`P23`/`pin23`) and the spin condition `v₂ = 0` (`hv2`) are the
untouched residual (not this block's lane). -/
theorem sphereProdCoboundaryWAdm_of_reducedAtoms {k : WithTop ℕ∞}
    (prov : CharPairWProviderPerOp (𝓡 4) k) (p : StrMfd (spinEmptyData prov))
    (b : Bordism ((𝓡 4).prod (𝓡∂ 1)) p.1 (emptySM (X := PUnit) (k := k) (I := 𝓡 4)))
    (hWT2 : T2Space b.W)
    (hasClass : letI := hWT2.t1Space
      HasRelFundClass (X := TopCat.of b.W) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W)
        (interiorGenFamily (W := b.W) ((𝓡 4).prod (𝓡∂ 1)) εtrace))
    [Subsingleton (Homology (TopCat.of b.W) 1)]
    [Subsingleton (RelativeHomology (X := TopCat.of b.W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary b.W) 4)]
    (P23 : LefschetzWuDatum (TopCat.of b.W) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W) 2 3 5)
    (pin23 : LefschetzWuPinned23 P23) (hv2 : wuClass P23 = 0) :
    SphereProdCoboundaryWAdm prov p := by
  haveI : Subsingleton (Cohomology (TopCat.of b.W) 1) :=
    subsingleton_cohomology_of_homology (X := TopCat.of b.W) 0
  haveI : Subsingleton (RelativeCohomology (X := TopCat.of b.W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary b.W) 4) :=
    subsingleton_relativeCohomology_of_relativeHomology
      (X := TopCat.of b.W) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W) 3
  exact sphereProdCoboundaryWAdm_of_degenerate14 prov p b hWT2
    (relFundDatum_ofHasClass b hWT2 hasClass) P23 pin23 hv2

/-- **`hBbord` from the reduced atoms** — the empty-membrane collapse (`hBbord_of_coboundary`, #203)
composed with the reduced coboundary atom. Discharges the `hBbord` obligation from the class-existence
witness + the two homology subsingletons + the `(2,3)` half + `v₂ = 0`. -/
theorem isDataBordant_empty_of_reducedAtoms {k : WithTop ℕ∞}
    (prov : CharPairWProviderPerOp (𝓡 4) k) (p : StrMfd (spinEmptyData prov))
    (b : Bordism ((𝓡 4).prod (𝓡∂ 1)) p.1 (emptySM (X := PUnit) (k := k) (I := 𝓡 4)))
    (hWT2 : T2Space b.W)
    (hasClass : letI := hWT2.t1Space
      HasRelFundClass (X := TopCat.of b.W) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W)
        (interiorGenFamily (W := b.W) ((𝓡 4).prod (𝓡∂ 1)) εtrace))
    [Subsingleton (Homology (TopCat.of b.W) 1)]
    [Subsingleton (RelativeHomology (X := TopCat.of b.W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary b.W) 4)]
    (P23 : LefschetzWuDatum (TopCat.of b.W) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W) 2 3 5)
    (pin23 : LefschetzWuPinned23 P23) (hv2 : wuClass P23 = 0) :
    IsDataBordant (spinEmptyData prov) p ⟨emptySM, (spinEmptyData prov).emptyStr⟩ :=
  hBbord_of_coboundary prov p
    (sphereProdCoboundaryWAdm_of_reducedAtoms prov p b hWT2 hasClass P23 pin23 hv2)

/-- **THE REDUCED-ATOMS WIRING** — the finest-grain KT ≅ ℤ/16 assembly with the Freeze-B geometric
hypothesis at `row.R.s2s2` given by the SHARPENED-AND-REDUCED residual: a T2 coboundary `b` with the
class-existence witness `hasClass` (atom 3 → `HasRelFundClass`), the two HOMOLOGY subsingletons (atoms
1,2 → their homological twins via universal coefficients), a pinned `(2,3)` Poincaré–Lefschetz datum
`P23`, and `v₂ = 0`. Every OTHER consumer shape (`H`, `row`, `hCob`/`hBase`, `hcolD`, `hker`, `hΦg`) is
fixed. This is the honest headline: the whole `S²×S² = ∂(S²×D³)` bordism content is discharged EXCEPT
the `(2,3)` half + `v₂ = 0` + the three sub-atoms `{HasRelFundClass, H₁(W;ℤ/2)=0, H₄(W,∂W;ℤ/2)=0}` —
the cohomological atoms are no longer atoms, only their homological/existence roots remain. -/
theorem kt_equiv_zmod16_of_residuals_freezeAtoms_ofReducedAtoms
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (row : SpinPresentationRow residualProv)
    (hCob : row.R.HandleTradeCobordism) (hBase : row.R.HyperbolicBase)
    (b : Bordism ((𝓡 4).prod (𝓡∂ 1)) row.R.s2s2.1 (emptySM (X := PUnit) (k := 0) (I := 𝓡 4)))
    (hWT2 : T2Space b.W)
    (hasClass : letI := hWT2.t1Space
      HasRelFundClass (X := TopCat.of b.W) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W)
        (interiorGenFamily (W := b.W) ((𝓡 4).prod (𝓡∂ 1)) εtrace))
    [Subsingleton (Homology (TopCat.of b.W) 1)]
    [Subsingleton (RelativeHomology (X := TopCat.of b.W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary b.W) 4)]
    (P23 : LefschetzWuDatum (TopCat.of b.W) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W) 2 3 5)
    (pin23 : LefschetzWuPinned23 P23) (hv2 : wuClass P23 = 0)
    (hcolD : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        IsSpinSectorStr residualProv p → RankZeroCollapseDatum residualProv p)
    (hker : KerPhiSubDoubles residualProv)
    (hΦg : spinForgetPhi residualProv
        (DataBordismGrp.mk (spinEmptyData residualProv) row.g) = ktKernelRep residualProv) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData residualProv) ≃+ ZMod 16) :=
  kt_equiv_zmod16_of_residuals_freezeAtoms_ofCoboundary H row hCob hBase
    (sphereProdCoboundaryWAdm_of_reducedAtoms residualProv row.R.s2s2 b hWT2 hasClass P23 pin23 hv2)
    hcolD hker hΦg

/-- **The Rokhlin-16 twin of the reduced-atoms wiring** — `Nat.card Ω₄^{Pin⁺} = 16` from the row with
Freeze B at the reduced residual. Pure transport; introduces no new residual atom. -/
theorem rokhlin_sixteen_of_residuals_freezeAtoms_ofReducedAtoms
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (row : SpinPresentationRow residualProv)
    (hCob : row.R.HandleTradeCobordism) (hBase : row.R.HyperbolicBase)
    (b : Bordism ((𝓡 4).prod (𝓡∂ 1)) row.R.s2s2.1 (emptySM (X := PUnit) (k := 0) (I := 𝓡 4)))
    (hWT2 : T2Space b.W)
    (hasClass : letI := hWT2.t1Space
      HasRelFundClass (X := TopCat.of b.W) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W)
        (interiorGenFamily (W := b.W) ((𝓡 4).prod (𝓡∂ 1)) εtrace))
    [Subsingleton (Homology (TopCat.of b.W) 1)]
    [Subsingleton (RelativeHomology (X := TopCat.of b.W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary b.W) 4)]
    (P23 : LefschetzWuDatum (TopCat.of b.W) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W) 2 3 5)
    (pin23 : LefschetzWuPinned23 P23) (hv2 : wuClass P23 = 0)
    (hcolD : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        IsSpinSectorStr residualProv p → RankZeroCollapseDatum residualProv p)
    (hker : KerPhiSubDoubles residualProv)
    (hΦg : spinForgetPhi residualProv
        (DataBordismGrp.mk (spinEmptyData residualProv) row.g) = ktKernelRep residualProv) :
    Nat.card (T2DataBordismGrp (pinPlusCharPairData residualProv)) = 16 :=
  rokhlin_sixteen_of_residuals_freezeAtoms_ofCoboundary H row hCob hBase
    (sphereProdCoboundaryWAdm_of_reducedAtoms residualProv row.R.s2s2 b hWT2 hasClass P23 pin23 hv2)
    hcolD hker hΦg

end Wiring

/-! ## §5. Non-vacuity — atom 1's reduction terminates at a TRUE fact on the concrete 2-sphere. -/

/-- **The atom-1 reduction is non-vacuous**: on the concrete 2-sphere `Sph 2` it produces
`Subsingleton (Cohomology (Sph 2) 1)` (`H¹(S²;ℤ/2) = 0`) from the banked mod-2 `H₁(S²;ℤ/2) = 0`
(`SingularSphereMiddle.sphere_homology_one`), witnessing that the homological sub-atom the narrowing
leaves for the geometric provider bottoms out at a genuine sphere computation, not a vacuous
hypothesis. (`W = S²×D³ ≃ S²`, so `H¹(W;ℤ/2) = H¹(S²;ℤ/2)`; the retraction transport to the coboundary
carrier is the provider's remaining step.) -/
example : Subsingleton (Cohomology (SKEFTHawking.SingularSphereAcyclic.Sph 2) 1) := by
  haveI : Subsingleton (Homology (SKEFTHawking.SingularSphereAcyclic.Sph 2) 1) :=
    subsingleton_of_forall_eq 0 (SKEFTHawking.SingularSphereMiddle.sphere_homology_one 2 le_rfl)
  exact subsingleton_cohomology_of_homology (X := SKEFTHawking.SingularSphereAcyclic.Sph 2) 0

end SKEFTHawking.PinPlusKTSphereProdCohomology
