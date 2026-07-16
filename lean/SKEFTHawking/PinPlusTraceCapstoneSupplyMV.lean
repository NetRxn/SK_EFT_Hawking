/-
# Phase 5q.H close-out — THE SUPPLY ROW SHRINKS: the four cohomology finiteness atoms of the
# welded capstone supply collapse into the single MV-cover datum.

`CapstoneAmbientSupplyWelded` (`PinPlusTraceCapstoneMembraneWeld.lean`) carries four numeric
finite-dimensionality atoms on the constructed capstone (`findimAbs14`/`findimRel14`/
`findimAbs23`/`findimRel23`). `CapstoneCohomologyMVDatum`
(`PinPlusTraceCapstoneCohomologyMV.lean`) discharges ALL FOUR from one transparent geometric row —
the two-piece Mayer–Vietoris cover with per-piece all-degree homology finiteness (which in turn
falls to four comparison homeomorphisms via `CapstoneMVTransferRow`,
`PinPlusTraceCapstoneMVPieces.lean`). This module performs the row substitution:

* **`CapstoneAmbientSupplyWeldedMV`** — the welded supply row with the four findim fields REPLACED
  by the single `mv : CapstoneCohomologyMVDatum …` field (three atoms fewer). The Wu field's type
  carries the substitution (`mv.toFindim…` witnesses in the `LefschetzWuDatum` assemblies —
  well-typed by proof irrelevance of the `FiniteDimensional` Prop-class).
* **`CapstoneAmbientSupplyWeldedMV.toWelded`** — the row substitution is conservative: the MV'd
  row rebuilds the full welded supply, the four numeric atoms discharged by the MV projections.
* **`kernelReducesToSpin_of_capstoneWeldedMVSupply`** — THE KRS SUPPLY FIRES from the MV'd row: a
  ∀-`p` supply of `CapstoneAmbientSupplyWeldedMV` discharges the deep KT §5 kernel-null binder
  `KernelReducesToSpin prov`.
* **`CapstoneAmbientSupplyWeldedMV.brown_eq`** — the Brown fence persists at the MV'd grade: no
  instantiation can launder a Brown-violating surgery step.

**The remaining shape of the row** (post-substitution): the algebraic surgery data
(`x`/`hx0`/`hxq`/`p'`/`hrank`), the source-Hausdorff atom, the constructed-capstone inputs
(`S`…`d`), the relFund existence witness `hasClass`, the MV cover row `mv` (= geometry via the
transfer row), the two Lefschetz nondegeneracies + two Betti equalities + the Wu vanishing (the
class-driven numerics residual), and the membrane realization/weld/glue/chart atoms.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusTraceCapstoneMembraneWeld
import SKEFTHawking.PinPlusTraceCapstoneCohomologyMV

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
open SKEFTHawking.PinPlusTraceCapstoneCohomologyMV
open SKEFTHawking.PinPlusTraceCapstoneMembraneWeld

namespace SKEFTHawking.PinPlusTraceCapstoneSupplyMV

noncomputable section

variable {prov : CharPairWProviderPerOp (𝓡 4) 0}

/-! ## §1. The MV'd per-`p` supply row (three atoms fewer). -/

/-- **The MV'd per-representative capstone atom supply** — `CapstoneAmbientSupplyWelded` with the
four cohomology finite-dimensionality atoms REPLACED by the single Mayer–Vietoris cover row `mv`
(three atoms fewer). Every other atom is retained verbatim; the Wu vanishing now reads its findim
witnesses off the MV projections (well-typed by proof irrelevance). No field is a completeness
Prop; `mv` itself reduces to four comparison homeomorphisms via `CapstoneMVTransferRow`. -/
structure CapstoneAmbientSupplyWeldedMV (prov : CharPairWProviderPerOp (𝓡 4) 0)
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
  /-- **the Mayer–Vietoris cover row** — the two-piece cover + per-piece all-degree homology
  finiteness, replacing all four cohomology finite-dimensionality atoms. -/
  mv : letI := hsT2
    CapstoneCohomologyMVDatum p'.1 p.1 S hS φ hφ hφinj cd hseam d
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
  /-- the Wu obstruction vanishes (`w₂(W) = 0`, the pin⁺ spin condition) — findim witnesses read
  off the MV projections. -/
  hwu : letI := hsT2
    wuW2
      (LefschetzWuDatum.ofRelFund14 (TraceRelFundLeaves.ofCapstone p'.1 p.1 S hS φ hφ hφinj cd hseam d
        hasClass).toRelFundClassDatum
        (CapstoneCohomologyMVDatum.toFindimAbs14 p'.1 p.1 S hS φ hφ hφinj cd hseam d mv)
        (CapstoneCohomologyMVDatum.toFindimRel14 p'.1 p.1 S hS φ hφ hφinj cd hseam d mv)
        nondeg14 dimeq14)
      (LefschetzWuDatum.ofRelFund23 (TraceRelFundLeaves.ofCapstone p'.1 p.1 S hS φ hφ hφinj cd hseam d
        hasClass).toRelFundClassDatum
        (CapstoneCohomologyMVDatum.toFindimAbs23 p'.1 p.1 S hS φ hφ hφinj cd hseam d mv)
        (CapstoneCohomologyMVDatum.toFindimRel23 p'.1 p.1 S hS φ hφ hφinj cd hseam d mv)
        nondeg23 dimeq23) = 0
  /-- the DERIVED-basis membrane realization. -/
  real : letI := hsT2
    GeoRealizationTied (TopCat.of p'.2.surf.M) (TopCat.of p.2.surf.M) p'.2.basis p.2.basis
  /-- the membrane kernel is Taylor-leg-vanishing. -/
  htaylor : TaylorLegVanishes p'.2.q p.2.q (real.toMembrane p'.2.q p.2.q).L
  /-- the membrane kernel is jointly Lagrangian. -/
  hlag : JointLagrangian p'.2.q p.2.q (real.toMembrane p'.2.q p.2.q).L
  /-- the membrane presented as a handle attachment. -/
  HAQ : HandleAttachment.{0, 0}
  /-- the membrane weld into the actual carrier. -/
  weld : letI := hsT2
    HandleAttachment.Weld HAQ (ktHandleAttachment p'.1.M D5 S hS φ hφ hφinj)
  /-- the membrane presentation homeomorphism. -/
  hQ : (↑real.Q : Type) ≃ₜ HAQ.carrier
  /-- glue (σ-end), welded form. -/
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

/-! ## §2. The substitution is conservative: the MV'd row rebuilds the welded supply. -/

/-- **The MV'd row rebuilds the full welded supply** — the four cohomology finiteness atoms
discharged by the MV projections, everything else verbatim. -/
def CapstoneAmbientSupplyWeldedMV.toWelded
    {p : StrMfd (pinPlusCharPairData prov).toTangentialData}
    (D : CapstoneAmbientSupplyWeldedMV prov p) : CapstoneAmbientSupplyWelded prov p where
  x := D.x
  hx0 := D.hx0
  hxq := D.hxq
  p' := D.p'
  hrank := D.hrank
  hsT2 := D.hsT2
  S := D.S
  hS := D.hS
  φ := D.φ
  hφ := D.hφ
  hφinj := D.hφinj
  cd := D.cd
  hseam := D.hseam
  d := D.d
  hasClass := D.hasClass
  findimAbs14 :=
    letI := D.hsT2
    CapstoneCohomologyMVDatum.toFindimAbs14 D.p'.1 p.1 D.S D.hS D.φ D.hφ D.hφinj D.cd D.hseam
      D.d D.mv
  findimRel14 :=
    letI := D.hsT2
    CapstoneCohomologyMVDatum.toFindimRel14 D.p'.1 p.1 D.S D.hS D.φ D.hφ D.hφinj D.cd D.hseam
      D.d D.mv
  nondeg14 := D.nondeg14
  dimeq14 := D.dimeq14
  findimAbs23 :=
    letI := D.hsT2
    CapstoneCohomologyMVDatum.toFindimAbs23 D.p'.1 p.1 D.S D.hS D.φ D.hφ D.hφinj D.cd D.hseam
      D.d D.mv
  findimRel23 :=
    letI := D.hsT2
    CapstoneCohomologyMVDatum.toFindimRel23 D.p'.1 p.1 D.S D.hS D.φ D.hφ D.hφinj D.cd D.hseam
      D.d D.mv
  nondeg23 := D.nondeg23
  dimeq23 := D.dimeq23
  hwu := D.hwu
  real := D.real
  htaylor := D.htaylor
  hlag := D.hlag
  HAQ := D.HAQ
  weld := D.weld
  hQ := D.hQ
  glueσ := D.glueσ
  glueτ := D.glueτ
  chartQ := D.chartQ

/-! ## §3. The KRS firing and the Brown fence at the MV'd grade. -/

/-- **THE KRS SUPPLY FIRES from the MV'd capstone row.** A ∀-`p` supply of the MV'd atom row —
one `CapstoneAmbientSupplyWeldedMV prov p` per non-spin brown-0 representative, THREE atoms fewer
than `CapstoneAmbientSupplyWelded` (the four cohomology finiteness numerics collapsed into the
single geometric MV cover row) — discharges the deep KT §5 kernel-null binder
`KernelReducesToSpin prov`. -/
theorem kernelReducesToSpin_of_capstoneWeldedMVSupply
    (H : ∀ p : StrMfd (pinPlusCharPairData prov).toTangentialData,
      charPairBrown prov (T2DataBordismGrp.mk (pinPlusCharPairData prov) p) = 0 →
      0 < p.2.n → CapstoneAmbientSupplyWeldedMV prov p) :
    KernelReducesToSpin prov :=
  kernelReducesToSpin_of_capstoneWeldedSupply
    (fun p hbrown hpos => (H p hbrown hpos).toWelded)

/-- **The Brown fence persists at the MV'd grade** — no instantiation of the MV'd supply can
launder a Brown-violating surgery step (the KT surgery preserves the mod-8 Brown/ABK grade). -/
theorem CapstoneAmbientSupplyWeldedMV.brown_eq
    {p : StrMfd (pinPlusCharPairData prov).toTangentialData}
    (D : CapstoneAmbientSupplyWeldedMV prov p) :
    D.p'.2.q.brown = p.2.q.brown :=
  D.toWelded.brown_eq

end

end SKEFTHawking.PinPlusTraceCapstoneSupplyMV
