/-
# Phase 5q.H close-out — THE WELDED MEMBRANE ROW: HAW/hW discharged FREE on the constructed capstone

`PinPlusTraceCapstoneInhabit.lean`'s `TraceMembraneLeaves.ofCapstone` reduces the trace membrane row on
the constructed capstone to eleven geometric atoms, of which the Hausdorff separation `hWT2` is already
discharged FREE. This module discharges the **carrier-presentation pair** `HAW`/`hW` FREE as well (the
`#150` observation, now cashed): the constructed capstone carrier `(capstoneB …).W` is DEFINITIONALLY
the handle-attachment carrier `(ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier`, so

* `HAW := ktHandleAttachment s.M D5 S hS φ hφ hφinj` (the SAME handle attachment the carrier is built
  from — the tether then welds the membrane into the ACTUAL carrier, respecting the
  untethered-membrane fence: the weld still supplies the presentation), and
* `hW := Homeomorph.refl _` (the identity presentation — no re-homeomorphising).

The remaining nine atoms (`real`/`htaylor`/`hlag`/`HAQ`/`weld`/`hQ`/`glueσ`/`glueτ`/`chartQ`) stay the
honest open geometric residual. `TraceMembraneLeaves.ofCapstoneWelded` is the narrowed constructor;
`CapstoneAmbientSupplyWelded` is the narrowed per-`p` supply row (two atoms fewer than
`CapstoneAmbientSupply`), and `kernelReducesToSpin_of_capstoneWeldedSupply` re-fires the KT §5
kernel-null binder from it. The glue equations are stated in their welded form (`hW.symm` collapsed to
the identity), so the supply row's σ/τ boundary factorisations read directly against the carrier's own
boundary map `(capstoneB …).e`.

**Dimension discipline.** `W = (ktHandleAttachment …).carrier` is the 5-dim glued surgery trace; the
membrane `Q = real.Q` welded into it via `weld : Weld HAQ HAW` is the 3-dim `Σ×[0,½] ∪ handle ∪
Σ′×[½,1]`; the ends are 4-dim. `HAW.B = s.M × Icc 0 1`, `HAW.Ha = D5`.

**Fences respected.** `real` is `GeoRealizationTied … σ.basis τ.basis` (DERIVED bases, no free gauge);
the tether is the mandatory weld-supplied closed embedding welding into the ACTUAL carrier (never an
untethered variant); the membrane kernel is the computed `(real.toMembrane …).L`. The `htaylor`/`hlag`
kernel conditions FORCE `brown(q_σ) = brown(q_τ)` (Brown fence), so any inhabitant is same-grade by
construction.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusTraceCapstoneInhabit

open scoped Manifold
open Topology
open SKEFTHawking.BordismTheory
open SKEFTHawking.SurgeryFoundation
open SKEFTHawking.SurgeryFoundation.HandleAttachment
open SKEFTHawking.DiskChartGeneric (D5)
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularCohomologyPairRestrict
open SKEFTHawking.PinPlusCharPairMembraneGeoRealization
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.PinPlusCharPairRealizationTied
open SKEFTHawking.PinPlusTraceRelFundReduce
open SKEFTHawking.PinPlusWAdmPinned
open SKEFTHawking.PinPlusTraceMembranePresented
open SKEFTHawking.PinPlusKTSurgeryTrace
open SKEFTHawking.PinPlusKTSurgeryTraceConsumers
open SKEFTHawking.PinPlusKTKernelSector
open SKEFTHawking.T2TangentialBordism SKEFTHawking.TangentialDataBordism
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassGeom
open SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.PoincareLefschetzWuAssembly
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.PinPlusTraceCapstoneInhabit

namespace SKEFTHawking.PinPlusTraceCapstoneMembraneWeld

noncomputable section

variable (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)
  (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
  (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
  (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)

/-- **The capstone carrier IS a handle-attachment carrier — FREE.** `(capstoneB …).W` reduces
definitionally to `(ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier`, so the identity is a
homeomorphism between them. This discharges the `hW` field of `TraceMembraneLeaves` on the constructed
carrier with `HAW := ktHandleAttachment …` (the `#150` free reduction). -/
def capstoneHW :
    (capstoneB s t S hS φ hφ hφinj cd hseam d).W ≃ₜ
      (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier :=
  Homeomorph.refl _

variable (σ : CharPairStrBundled (𝓡 4) s) (τ : CharPairStrBundled (𝓡 4) t)

/-- **`TraceMembraneLeaves` inhabited on the capstone with `HAW`/`hW` discharged FREE.** The narrowed
constructor: the handle-attachment carrier presentation is the SAME `ktHandleAttachment` the capstone is
built from (`HAW`), with the identity presentation (`hW`). The membrane weld `weld : Weld HAQ HAW` thus
welds the membrane into the ACTUAL carrier (respecting the untethered-membrane fence). The remaining
nine atoms — `real` (DERIVED bases), `htaylor`/`hlag` (the Brown-fence kernel conditions), `HAQ`, the
`weld`, `hQ`, the two glue factorisations (in their `hW`-collapsed welded form, reading directly against
`(capstoneB …).e`), and `chartQ` — are the honest open geometric residual. -/
def TraceMembraneLeaves.ofCapstoneWelded
    (real : GeoRealizationTied (TopCat.of σ.surf.M) (TopCat.of τ.surf.M) σ.basis τ.basis)
    (htaylor : TaylorLegVanishes σ.q τ.q (real.toMembrane σ.q τ.q).L)
    (hlag : JointLagrangian σ.q τ.q (real.toMembrane σ.q τ.q).L)
    (HAQ : HandleAttachment.{0, 0})
    (weld : HandleAttachment.Weld HAQ (ktHandleAttachment s.M D5 S hS φ hφ hφinj))
    (hQ : (↑real.Q : Type) ≃ₜ HAQ.carrier)
    (glueσ : ∀ x : ↑(sub real.U),
        weld.carrierMap (hQ (real.ι (subInclCM real.U x)))
          = (capstoneB s t S hS φ hφ hφinj cd hseam d).e (Sum.inl (σ.emb (real.homσ x))))
    (glueτ : ∀ x : ↑(sub real.Uᶜ),
        weld.carrierMap (hQ (real.ι (subInclCM real.Uᶜ x)))
          = (capstoneB s t S hS φ hφ hφinj cd hseam d).e (Sum.inr (τ.emb (real.homτ x))))
    (chartQ : ChartedSpace MembraneModel ↑real.Q) :
    TraceMembraneLeaves (capstoneB s t S hS φ hφ hφinj cd hseam d) σ τ :=
  TraceMembraneLeaves.ofCapstone s t S hS φ hφ hφinj cd hseam d σ τ
    real htaylor hlag HAQ (ktHandleAttachment s.M D5 S hS φ hφ hφinj) weld hQ
    (capstoneHW s t S hS φ hφ hφinj cd hseam d) glueσ glueτ chartQ

end

/-! ## §2. The narrowed KRS seam — `AmbientSurgeryDatum` with `HAW`/`hW` discharged FREE. -/

noncomputable section

variable {prov : CharPairWProviderPerOp (𝓡 4) 0}

/-- **`AmbientSurgeryDatum` on the constructed capstone with `HAW`/`hW` FREE.** Delegates to
`ambientSurgeryDatum_of_capstone`, supplying the carrier presentation `HAW := ktHandleAttachment …` and
`hW := capstoneHW …` (both free), so the caller supplies only the narrowed membrane residual: `HAQ`, the
`weld` (into the actual carrier), `hQ`, the welded-form glue factorisations, and `chartQ`. The relFund
numerics (`findim…`/`nondeg…`/`dimeq…`/`hwu`) and the algebraic surgery data are forwarded unchanged. -/
def ambientSurgeryDatum_of_capstoneWelded
    {p : StrMfd (pinPlusCharPairData prov).toTangentialData}
    (x : Fin p.2.n → ZMod 2) (hx0 : x ≠ 0) (hxq : p.2.q.q x = 0)
    (p' : StrMfd (pinPlusCharPairData prov).toTangentialData) (hrank : p'.2.n + 2 = p.2.n)
    (hsT2 : T2Space p'.1.M)
    (S : Set D5) (hS : IsClosed S) (φ : ↥S → p'.1.M × Set.Icc (0 : ℝ) 1)
    (hφ : Continuous φ) (hφinj : Function.Injective φ)
    (cd : SeamCollarDatum (ktHandleAttachment p'.1.M D5 S hS φ hφ hφinj).carrier)
    (hseam : (ktHandleAttachment p'.1.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
    (d : SurgeredEndDatum p'.1 p.1 S hS φ hφ hφinj cd hseam)
    (hasClass :
      letI := hsT2
      letI := capstone_t1Space p'.1 p.1 S hS φ hφ hφinj cd hseam d
      HasRelFundClass (X := TopCat.of (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)
        (interiorGenFamily (W := (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)
          ((𝓡 4).prod (𝓡∂ 1)) εtrace))
    (findimAbs14 : letI := hsT2
      FiniteDimensional (ZMod 2)
        (Cohomology (TopCat.of (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W) 1))
    (findimRel14 : letI := hsT2
      FiniteDimensional (ZMod 2)
        (RelativeCohomology (X := TopCat.of (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W) 4))
    (nondeg14 : letI := hsT2
      Function.Injective
        ⇑((relCupH14 (X := TopCat.of (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)
          (S := ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)).compr₂
          (TraceRelFundLeaves.ofCapstone p'.1 p.1 S hS φ hφ hφinj cd hseam d
            hasClass).toRelFundClassDatum.mu))
    (dimeq14 : letI := hsT2
      Module.finrank (ZMod 2)
          (Cohomology (TopCat.of (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W) 1)
        = Module.finrank (ZMod 2)
          (RelativeCohomology (X := TopCat.of (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)
            (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W) 4))
    (findimAbs23 : letI := hsT2
      FiniteDimensional (ZMod 2)
        (Cohomology (TopCat.of (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W) 2))
    (findimRel23 : letI := hsT2
      FiniteDimensional (ZMod 2)
        (RelativeCohomology (X := TopCat.of (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W) 3))
    (nondeg23 : letI := hsT2
      Function.Injective
        ⇑((relCupH23 (X := TopCat.of (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)
          (S := ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)).compr₂
          (TraceRelFundLeaves.ofCapstone p'.1 p.1 S hS φ hφ hφinj cd hseam d
            hasClass).toRelFundClassDatum.mu))
    (dimeq23 : letI := hsT2
      Module.finrank (ZMod 2)
          (Cohomology (TopCat.of (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W) 2)
        = Module.finrank (ZMod 2)
          (RelativeCohomology (X := TopCat.of (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)
            (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W) 3))
    (hwu : letI := hsT2
      wuW2
        (LefschetzWuDatum.ofRelFund14 (TraceRelFundLeaves.ofCapstone p'.1 p.1 S hS φ hφ hφinj cd hseam d
          hasClass).toRelFundClassDatum findimAbs14 findimRel14 nondeg14 dimeq14)
        (LefschetzWuDatum.ofRelFund23 (TraceRelFundLeaves.ofCapstone p'.1 p.1 S hS φ hφ hφinj cd hseam d
          hasClass).toRelFundClassDatum findimAbs23 findimRel23 nondeg23 dimeq23) = 0)
    (real : letI := hsT2
      GeoRealizationTied (TopCat.of p'.2.surf.M) (TopCat.of p.2.surf.M) p'.2.basis p.2.basis)
    (htaylor : TaylorLegVanishes p'.2.q p.2.q (real.toMembrane p'.2.q p.2.q).L)
    (hlag : JointLagrangian p'.2.q p.2.q (real.toMembrane p'.2.q p.2.q).L)
    (HAQ : HandleAttachment.{0, 0})
    (weld : letI := hsT2
      HandleAttachment.Weld HAQ (ktHandleAttachment p'.1.M D5 S hS φ hφ hφinj))
    (hQ : (↑real.Q : Type) ≃ₜ HAQ.carrier)
    (glueσ : letI := hsT2
      ∀ y : ↑(sub real.U),
        weld.carrierMap (hQ (real.ι (subInclCM real.U y)))
          = (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).e (Sum.inl (p'.2.emb (real.homσ y))))
    (glueτ : letI := hsT2
      ∀ y : ↑(sub real.Uᶜ),
        weld.carrierMap (hQ (real.ι (subInclCM real.Uᶜ y)))
          = (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).e (Sum.inr (p.2.emb (real.homτ y))))
    (chartQ : ChartedSpace MembraneModel ↑real.Q) :
    AmbientSurgeryDatum prov p :=
  letI := hsT2
  ambientSurgeryDatum_of_capstone x hx0 hxq p' hrank hsT2 S hS φ hφ hφinj cd hseam d
    hasClass findimAbs14 findimRel14 nondeg14 dimeq14 findimAbs23 findimRel23 nondeg23 dimeq23 hwu
    real htaylor hlag HAQ (ktHandleAttachment p'.1.M D5 S hS φ hφ hφinj) weld hQ
    (capstoneHW p'.1 p.1 S hS φ hφ hφinj cd hseam d) glueσ glueτ chartQ

end

/-! ## §3. The narrowed per-`p` supply row and the KRS firing (two atoms fewer). -/

noncomputable section

variable {prov : CharPairWProviderPerOp (𝓡 4) 0}

/-- **The narrowed per-representative capstone atom supply** — `CapstoneAmbientSupply` with the carrier
presentation pair `HAW`/`hW` REMOVED (discharged FREE: the carrier is the `ktHandleAttachment` it is
built from, presented by the identity). Every other atom is retained: the algebraic surgery data, the
source-Hausdorff certificate, the constructed-capstone inputs, the relFund existence witness + Lefschetz
numerics, and the membrane realization/kernel/weld/glue/chart atoms — the `weld` now welding into the
actual carrier, the glue factorisations in their welded form (reading directly against the carrier's own
boundary map). No field is a completeness Prop. -/
structure CapstoneAmbientSupplyWelded (prov : CharPairWProviderPerOp (𝓡 4) 0)
    (p : StrMfd (pinPlusCharPairData prov).toTangentialData) where
  /-- the isotropic class to surger. -/
  x : Fin p.2.n → ZMod 2
  /-- the class is nonzero. -/
  hx0 : x ≠ 0
  /-- the framing obstruction vanishes. -/
  hxq : p.2.q.q x = 0
  /-- the surgered representative. -/
  p' : StrMfd (pinPlusCharPairData prov).toTangentialData
  /-- the KT surgery drops the enhancement rank by exactly 2. -/
  hrank : p'.2.n + 2 = p.2.n
  /-- **the source manifold is Hausdorff** (a closed 4-manifold; genuine geometric atom). -/
  hsT2 : T2Space p'.1.M
  /-- the attaching region `S ⊆ D⁵`. -/
  S : Set D5
  /-- `S` is closed. -/
  hS : IsClosed S
  /-- the attaching map `φ : S → M × I`. -/
  φ : ↥S → p'.1.M × Set.Icc (0 : ℝ) 1
  /-- `φ` is continuous. -/
  hφ : Continuous φ
  /-- `φ` is injective. -/
  hφinj : Function.Injective φ
  /-- the seam-collar datum. -/
  cd : SeamCollarDatum (ktHandleAttachment p'.1.M D5 S hS φ hφ hφinj).carrier
  /-- the seam containment. -/
  hseam : (ktHandleAttachment p'.1.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd
  /-- the surgered-end datum. -/
  d : SurgeredEndDatum p'.1 p.1 S hS φ hφ hφinj cd hseam
  /-- **the relFund existence witness** (relative Hatcher-3.27(b) MV atom; `hWT1` discharged free). -/
  hasClass :
    letI := hsT2
    letI := capstone_t1Space p'.1 p.1 S hS φ hφ hφinj cd hseam d
    HasRelFundClass (X := TopCat.of (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)
      (interiorGenFamily (W := (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)
        ((𝓡 4).prod (𝓡∂ 1)) εtrace)
  /-- `H¹(W;ℤ/2)` finite-dimensional. -/
  findimAbs14 : letI := hsT2
    FiniteDimensional (ZMod 2)
      (Cohomology (TopCat.of (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W) 1)
  /-- `H⁴(W,∂W;ℤ/2)` finite-dimensional. -/
  findimRel14 : letI := hsT2
    FiniteDimensional (ZMod 2)
      (RelativeCohomology (X := TopCat.of (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W) 4)
  /-- `(1,4)` Lefschetz non-degeneracy. -/
  nondeg14 : letI := hsT2
    Function.Injective
      ⇑((relCupH14 (X := TopCat.of (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)
        (S := ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)).compr₂
        (TraceRelFundLeaves.ofCapstone p'.1 p.1 S hS φ hφ hφinj cd hseam d
          hasClass).toRelFundClassDatum.mu)
  /-- `(1,4)` Betti equality. -/
  dimeq14 : letI := hsT2
    Module.finrank (ZMod 2)
        (Cohomology (TopCat.of (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W) 1)
      = Module.finrank (ZMod 2)
        (RelativeCohomology (X := TopCat.of (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W) 4)
  /-- `H²(W;ℤ/2)` finite-dimensional. -/
  findimAbs23 : letI := hsT2
    FiniteDimensional (ZMod 2)
      (Cohomology (TopCat.of (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W) 2)
  /-- `H³(W,∂W;ℤ/2)` finite-dimensional. -/
  findimRel23 : letI := hsT2
    FiniteDimensional (ZMod 2)
      (RelativeCohomology (X := TopCat.of (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W) 3)
  /-- `(2,3)` Lefschetz non-degeneracy. -/
  nondeg23 : letI := hsT2
    Function.Injective
      ⇑((relCupH23 (X := TopCat.of (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)
        (S := ((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)).compr₂
        (TraceRelFundLeaves.ofCapstone p'.1 p.1 S hS φ hφ hφinj cd hseam d
          hasClass).toRelFundClassDatum.mu)
  /-- `(2,3)` Betti equality. -/
  dimeq23 : letI := hsT2
    Module.finrank (ZMod 2)
        (Cohomology (TopCat.of (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W) 2)
      = Module.finrank (ZMod 2)
        (RelativeCohomology (X := TopCat.of (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W)
          (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W) 3)
  /-- the Wu obstruction vanishes (`w₂(W) = 0`, the pin⁺ spin condition). -/
  hwu : letI := hsT2
    wuW2
      (LefschetzWuDatum.ofRelFund14 (TraceRelFundLeaves.ofCapstone p'.1 p.1 S hS φ hφ hφinj cd hseam d
        hasClass).toRelFundClassDatum findimAbs14 findimRel14 nondeg14 dimeq14)
      (LefschetzWuDatum.ofRelFund23 (TraceRelFundLeaves.ofCapstone p'.1 p.1 S hS φ hφ hφinj cd hseam d
        hasClass).toRelFundClassDatum findimAbs23 findimRel23 nondeg23 dimeq23) = 0
  /-- the DERIVED-basis membrane realization. -/
  real : letI := hsT2
    GeoRealizationTied (TopCat.of p'.2.surf.M) (TopCat.of p.2.surf.M) p'.2.basis p.2.basis
  /-- the membrane kernel is Taylor-leg-vanishing. -/
  htaylor : TaylorLegVanishes p'.2.q p.2.q (real.toMembrane p'.2.q p.2.q).L
  /-- the membrane kernel is jointly Lagrangian. -/
  hlag : JointLagrangian p'.2.q p.2.q (real.toMembrane p'.2.q p.2.q).L
  /-- the membrane presented as a handle attachment. -/
  HAQ : HandleAttachment.{0, 0}
  /-- **the membrane weld into the ACTUAL carrier** (`HAW` no longer a field — it is the
  `ktHandleAttachment` the carrier is built from). -/
  weld : letI := hsT2
    HandleAttachment.Weld HAQ (ktHandleAttachment p'.1.M D5 S hS φ hφ hφinj)
  /-- the membrane presentation homeomorphism. -/
  hQ : (↑real.Q : Type) ≃ₜ HAQ.carrier
  /-- glue (σ-end), welded form (`hW` collapsed to the identity). -/
  glueσ : letI := hsT2
    ∀ y : ↑(sub real.U),
      weld.carrierMap (hQ (real.ι (subInclCM real.U y)))
        = (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).e (Sum.inl (p'.2.emb (real.homσ y)))
  /-- glue (τ-end), welded form. -/
  glueτ : letI := hsT2
    ∀ y : ↑(sub real.Uᶜ),
      weld.carrierMap (hQ (real.ι (subInclCM real.Uᶜ y)))
        = (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).e (Sum.inr (p.2.emb (real.homτ y)))
  /-- `Q` charts over the 3-dim membrane model. -/
  chartQ : ChartedSpace MembraneModel ↑real.Q

/-- **The narrowed capstone supply discharges the KRS-consumer datum.** Applies
`ambientSurgeryDatum_of_capstoneWelded` to the bundled atoms — the whole `AmbientSurgeryDatum` from the
constructed capstone, with the carrier presentation `HAW`/`hW` discharged free. -/
def CapstoneAmbientSupplyWelded.toAmbientSurgeryDatum
    {p : StrMfd (pinPlusCharPairData prov).toTangentialData}
    (D : CapstoneAmbientSupplyWelded prov p) : AmbientSurgeryDatum prov p :=
  ambientSurgeryDatum_of_capstoneWelded D.x D.hx0 D.hxq D.p' D.hrank D.hsT2 D.S D.hS D.φ D.hφ D.hφinj
    D.cd D.hseam D.d D.hasClass D.findimAbs14 D.findimRel14 D.nondeg14 D.dimeq14
    D.findimAbs23 D.findimRel23 D.nondeg23 D.dimeq23 D.hwu D.real D.htaylor D.hlag
    D.HAQ D.weld D.hQ D.glueσ D.glueτ D.chartQ

/-- **THE KRS-SUPPLY FIRES from the narrowed capstone row** (the wave headline). A ∀-`p` supply of the
NARROWED capstone atom row — one `CapstoneAmbientSupplyWelded prov p` per non-spin brown-0
representative, TWO atoms fewer than `CapstoneAmbientSupply` (the carrier presentation `HAW`/`hW`
discharged free) — discharges the deep KT §5 kernel-null binder `KernelReducesToSpin prov` via the
banked `kernelReducesToSpin_of_ambientDatumSupply`. So the whole `∀ x ∈ ker` direction reduces to a
∀-`p` supply of a transparent named row of geometric atoms on the CONSTRUCTED carrier, with the
separation certificates AND the carrier presentation discharged free. -/
theorem kernelReducesToSpin_of_capstoneWeldedSupply
    (H : ∀ p : StrMfd (pinPlusCharPairData prov).toTangentialData,
      charPairBrown prov (T2DataBordismGrp.mk (pinPlusCharPairData prov) p) = 0 →
      0 < p.2.n → CapstoneAmbientSupplyWelded prov p) :
    KernelReducesToSpin prov :=
  kernelReducesToSpin_of_ambientDatumSupply
    (fun p hbrown hpos => (H p hbrown hpos).toAmbientSurgeryDatum)

end

end SKEFTHawking.PinPlusTraceCapstoneMembraneWeld
