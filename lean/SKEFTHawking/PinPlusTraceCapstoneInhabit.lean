/-
# Phase 5q.H close-out — THE TRACE-ROW INHABITATION WAVE: the leaf rows on the CONSTRUCTED capstone

The trace bordism's tethered-`Bor` + W-admissibility obligations are three gated leaf rows
(`TraceRelFundLeaves`, `TraceWAdmLeaves`, `TraceMembraneLeaves`). Round 11 froze their supply specs.
This module INHABITS them on the CONSTRUCTED capstone bordism
(`ambientTraceBordism_capstone_ofSurgeredEnd`, `SingularSurgeryTraceCapstone.lean`) — discharging the
FREE fields and reducing every remaining field to a genuine, transparently-named geometric atom (the
`#138`/`#140`/`#143` honest-named-reduction pattern), never a completeness Prop.

**What is genuinely discharged (the inhabitation win, §1).** On the constructed carrier
`W = (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier` the separation certificates are FREE: the
carrier is a `HandleAttachment.carrier`, a quotient of a compact Hausdorff space by a closed relation
(`HandleAttachment.instT2SpaceCarrier`, via `t2Space_quotient_of_isClosed_rel`,
`SingularSurgeryFoundation.lean`), so `T2Space W` holds by instance and `T1Space W` follows. These are
the exact `hWT1` (`TraceRelFundLeaves`) and `hWT2` (`TraceMembraneLeaves`) fields the abstract rows
carry as unresolved separation atoms — on the constructed carrier they are no longer carried.

**The honest reductions (§2–§3).** `TraceRelFundLeaves.ofCapstone` supplies `hWT1` free, leaving the
single existence atom `hasClass` (the relative Hatcher-3.27(b) MV witness — a pure geometric residual,
NOT a completeness Prop). `TraceMembraneLeaves.ofCapstone` supplies `hWT2` free, leaving exactly the
realization/kernel/weld/glue/chart atoms. Neither the numerics (`TraceWAdmLeaves`) nor these atoms are
dissolved — they are the honest open geometric content, left as typed leaves.

**The KRS seam (§4).** `CapstoneAmbientSupply prov p` bundles, per non-spin brown-0 representative, the
constructed-capstone inputs + the residual geometric atoms (separations excluded);
`ambientSurgeryDatum_of_capstoneSupply` fires `ambientSurgeryDatum_of_traceLeaves` on the constructed
`b`; `kernelReducesToSpin_of_capstoneSupply` fires the banked
`kernelReducesToSpin_of_ambientDatumSupply` — so the deep KT §5 kernel-null binder
`KernelReducesToSpin` is reduced to a ∀-`p` supply of a transparent named row of geometric atoms on the
constructed carrier, with the separation certificates discharged.

**Round-11 spec compliance.** The KRS unit stays the ∀-`p` supply (spec 4); the membrane row respects
the Brown fence (`traceLeaves_brown_eq` fires from `htaylor`/`hlag`, so the inhabitant is same-grade by
construction — never a cross-grade fabrication); the inhabitant is the NON-empty constructed carrier
(the empty degenerate world is inert). The COLLAR FORK ruling is respected: the capstone carries its
`[W,∂W]`/collar data BY CONSTRUCTION (the provider pattern), never the general collar theorem.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SingularSurgeryTraceCapstone
import SKEFTHawking.PinPlusTraceRelFundReduce
import SKEFTHawking.PinPlusTraceMembranePresented

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

namespace SKEFTHawking.PinPlusTraceCapstoneInhabit

noncomputable section

variable (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)
  (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
  (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
  (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)

/-- **The constructed capstone bordism** (abbreviation for the inhabitation statements) — the
`ambientTraceBordism_capstone_ofSurgeredEnd` produced from the attaching data `S`/`φ`, the seam-collar
datum `cd`/`hseam`, and the surgered-end datum `d`. Its carrier `W` reduces definitionally to
`(ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier`. -/
abbrev capstoneB : Bordism ((𝓡 4).prod (𝓡∂ 1)) s t :=
  ambientTraceBordism_capstone_ofSurgeredEnd s t S hS φ hφ hφinj cd hseam d

/-! ## §1. The FREE separation certificates on the constructed capstone carrier. -/

/-- **The capstone carrier is Hausdorff — FREE.** `(capstoneB …).W` reduces definitionally to
`(ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier`, a quotient of a compact Hausdorff space by a
closed relation, so its `T2Space` is the `HandleAttachment.carrier` instance. This is the `hWT2` field
of `TraceMembraneLeaves`, discharged on the constructed carrier. -/
theorem capstone_t2Space : T2Space (capstoneB s t S hS φ hφ hφinj cd hseam d).W := by
  show T2Space (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier
  infer_instance

/-- **The capstone carrier is T1 — FREE** (from Hausdorff). This is the `hWT1` field of
`TraceRelFundLeaves`, discharged on the constructed carrier. -/
theorem capstone_t1Space : T1Space (capstoneB s t S hS φ hφ hφinj cd hseam d).W := by
  letI := capstone_t2Space s t S hS φ hφ hφinj cd hseam d
  infer_instance

/-! ## §2. `TraceRelFundLeaves` on the capstone — `hWT1` free, the MV existence witness the atom. -/

/-- **`TraceRelFundLeaves` inhabited on the constructed capstone.** The T1 separation certificate
`hWT1` is discharged FREE (`capstone_t1Space`); the sole residual is the class-existence witness
`hasClass` — the relative Hatcher-3.27(b) Mayer–Vietoris existence obligation for the canonical
interior generator family, a genuine geometric atom (NOT a completeness Prop). The interior generators
are canonically constructed from the trace model + `εtrace` (never a free basis gauge). -/
def TraceRelFundLeaves.ofCapstone
    (hasClass :
      letI := capstone_t1Space s t S hS φ hφ hφinj cd hseam d
      HasRelFundClass (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
        (interiorGenFamily (W := (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
          ((𝓡 4).prod (𝓡∂ 1)) εtrace)) :
    TraceRelFundLeaves (capstoneB s t S hS φ hφ hφinj cd hseam d) where
  hWT1 := capstone_t1Space s t S hS φ hφ hφinj cd hseam d
  hasClass := hasClass

/-! ## §3. `TraceMembraneLeaves` on the capstone — `hWT2` free, the membrane atoms explicit. -/

variable (σ : CharPairStrBundled (𝓡 4) s) (τ : CharPairStrBundled (𝓡 4) t)

/-- **`TraceMembraneLeaves` inhabited on the constructed capstone.** The Hausdorff separation
certificate `hWT2` is discharged FREE (`capstone_t2Space`); the residuals are exactly the
realization/kernel/weld/glue/chart atoms — each a genuine geometric atom, none a completeness Prop.
`real` is `GeoRealizationTied … σ.basis τ.basis` (DERIVED bases, no free gauge); the membrane kernel
`L = (real.toMembrane …).L` is the computed kernel; the tether is the mandatory weld-supplied closed
embedding. The `htaylor`/`hlag` kernel conditions FORCE `brown(q_σ) = brown(q_τ)` (Brown fence,
spec 4) — so this inhabitant is same-Brown-grade by construction, never a cross-grade fabrication. -/
def TraceMembraneLeaves.ofCapstone
    (real : GeoRealizationTied (TopCat.of σ.surf.M) (TopCat.of τ.surf.M) σ.basis τ.basis)
    (htaylor : TaylorLegVanishes σ.q τ.q (real.toMembrane σ.q τ.q).L)
    (hlag : JointLagrangian σ.q τ.q (real.toMembrane σ.q τ.q).L)
    (HAQ HAW : HandleAttachment.{0, 0})
    (weld : HandleAttachment.Weld HAQ HAW)
    (hQ : (↑real.Q : Type) ≃ₜ HAQ.carrier)
    (hW : (capstoneB s t S hS φ hφ hφinj cd hseam d).W ≃ₜ HAW.carrier)
    (glueσ : ∀ x : ↑(sub real.U),
        hW.symm (weld.carrierMap (hQ (real.ι (subInclCM real.U x))))
          = (capstoneB s t S hS φ hφ hφinj cd hseam d).e (Sum.inl (σ.emb (real.homσ x))))
    (glueτ : ∀ x : ↑(sub real.Uᶜ),
        hW.symm (weld.carrierMap (hQ (real.ι (subInclCM real.Uᶜ x))))
          = (capstoneB s t S hS φ hφ hφinj cd hseam d).e (Sum.inr (τ.emb (real.homτ x))))
    (chartQ : ChartedSpace MembraneModel ↑real.Q) :
    TraceMembraneLeaves (capstoneB s t S hS φ hφ hφinj cd hseam d) σ τ where
  hWT2 := capstone_t2Space s t S hS φ hφ hφinj cd hseam d
  real := real
  htaylor := htaylor
  hlag := hlag
  HAQ := HAQ
  HAW := HAW
  weld := weld
  hQ := hQ
  hW := hW
  glueσ := glueσ
  glueτ := glueτ
  chartQ := chartQ

end

/-! ## §4. The KRS seam — `AmbientSurgeryDatum` on the constructed capstone, and the KRS firing. -/

noncomputable section

variable {prov : CharPairWProviderPerOp (𝓡 4) 0}

/-- **`AmbientSurgeryDatum` on the constructed capstone, from the residual atoms** (separations FREE).
Composes `ambientSurgeryDatum_of_traceLeaves` on the constructed `b = capstoneB p'.1 p.1 …` with the
two `ofCapstone` leaf rows: `TraceWAdmLeaves` from the reduced relFund row
(`TraceRelFundLeaves.ofCapstone hasClass`, `hWT1` free) plus the compact-manifold numerics, and
`TraceMembraneLeaves.ofCapstone` (`hWT2` free) plus the membrane atoms. The whole KRS-consumer datum
bottoms out in: the algebraic surgery data, the source-Hausdorff certificate `hsT2`, the constructed
capstone inputs, and the residual geometric atoms — no separation certificate on the carrier, no
completeness Prop. -/
def ambientSurgeryDatum_of_capstone
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
    (HAQ HAW : HandleAttachment.{0, 0})
    (weld : HandleAttachment.Weld HAQ HAW)
    (hQ : (↑real.Q : Type) ≃ₜ HAQ.carrier)
    (hW : letI := hsT2
      (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W ≃ₜ HAW.carrier)
    (glueσ : letI := hsT2
      ∀ x : ↑(sub real.U),
        hW.symm (weld.carrierMap (hQ (real.ι (subInclCM real.U x))))
          = (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).e (Sum.inl (p'.2.emb (real.homσ x))))
    (glueτ : letI := hsT2
      ∀ x : ↑(sub real.Uᶜ),
        hW.symm (weld.carrierMap (hQ (real.ι (subInclCM real.Uᶜ x))))
          = (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).e (Sum.inr (p.2.emb (real.homτ x))))
    (chartQ : ChartedSpace MembraneModel ↑real.Q) :
    AmbientSurgeryDatum prov p :=
  letI := hsT2
  ambientSurgeryDatum_of_traceLeaves x hx0 hxq p' hrank
    (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d)
    (TraceWAdmLeaves.ofRelFundLeaves
      (TraceRelFundLeaves.ofCapstone p'.1 p.1 S hS φ hφ hφinj cd hseam d hasClass)
      findimAbs14 findimRel14 nondeg14 dimeq14 findimAbs23 findimRel23 nondeg23 dimeq23 hwu)
    (TraceMembraneLeaves.ofCapstone p'.1 p.1 S hS φ hφ hφinj cd hseam d p'.2 p.2
      real htaylor hlag HAQ HAW weld hQ hW glueσ glueτ chartQ)

/-- **The per-representative capstone atom supply** — every input `ambientSurgeryDatum_of_capstone`
consumes, bundled per non-spin brown-0 representative `p` as a single named row of geometric/algebraic
atoms. The separation certificates `hWT1`/`hWT2` are NOT fields (discharged FREE inside the `ofCapstone`
reductions); the row carries the algebraic surgery data, the source-Hausdorff certificate, the
constructed-capstone inputs, and the residual geometric atoms (the relFund existence witness, the
compact-manifold numerics, the membrane realization/weld/glue atoms). No field is a completeness Prop. -/
structure CapstoneAmbientSupply (prov : CharPairWProviderPerOp (𝓡 4) 0)
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
  /-- the bordism carrier presented as a handle attachment. -/
  HAW : HandleAttachment.{0, 0}
  /-- the membrane weld. -/
  weld : HandleAttachment.Weld HAQ HAW
  /-- the membrane presentation homeomorphism. -/
  hQ : (↑real.Q : Type) ≃ₜ HAQ.carrier
  /-- the carrier presentation homeomorphism. -/
  hW : letI := hsT2
    (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).W ≃ₜ HAW.carrier
  /-- glue (σ-end). -/
  glueσ : letI := hsT2
    ∀ y : ↑(sub real.U),
      hW.symm (weld.carrierMap (hQ (real.ι (subInclCM real.U y))))
        = (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).e (Sum.inl (p'.2.emb (real.homσ y)))
  /-- glue (τ-end). -/
  glueτ : letI := hsT2
    ∀ y : ↑(sub real.Uᶜ),
      hW.symm (weld.carrierMap (hQ (real.ι (subInclCM real.Uᶜ y))))
        = (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d).e (Sum.inr (p.2.emb (real.homτ y)))
  /-- `Q` charts over the 3-dim membrane model. -/
  chartQ : ChartedSpace MembraneModel ↑real.Q

/-- **The capstone atom supply discharges the KRS-consumer datum.** Applies
`ambientSurgeryDatum_of_capstone` to the bundled atoms — the whole `AmbientSurgeryDatum` from the
constructed capstone, separations free. -/
def CapstoneAmbientSupply.toAmbientSurgeryDatum
    {p : StrMfd (pinPlusCharPairData prov).toTangentialData}
    (D : CapstoneAmbientSupply prov p) : AmbientSurgeryDatum prov p :=
  ambientSurgeryDatum_of_capstone D.x D.hx0 D.hxq D.p' D.hrank D.hsT2 D.S D.hS D.φ D.hφ D.hφinj
    D.cd D.hseam D.d D.hasClass D.findimAbs14 D.findimRel14 D.nondeg14 D.dimeq14
    D.findimAbs23 D.findimRel23 D.nondeg23 D.dimeq23 D.hwu D.real D.htaylor D.hlag
    D.HAQ D.HAW D.weld D.hQ D.hW D.glueσ D.glueτ D.chartQ

/-- **THE KRS-SUPPLY FIRES from the constructed capstone** (the wave headline). A ∀-`p` supply of the
capstone atom row — one `CapstoneAmbientSupply prov p` per non-spin brown-0 representative — discharges
the deep KT §5 kernel-null binder `KernelReducesToSpin prov` via the banked
`kernelReducesToSpin_of_ambientDatumSupply`. So the whole `∀ x ∈ ker` direction reduces to a ∀-`p`
supply of a transparent named row of geometric atoms on the CONSTRUCTED carrier, with the separation
certificates discharged free. The KRS unit is the ∀-`p` supply (round-11 spec 4); each supply is the
NON-empty constructed capstone (the empty degenerate world is inert). -/
theorem kernelReducesToSpin_of_capstoneSupply
    (H : ∀ p : StrMfd (pinPlusCharPairData prov).toTangentialData,
      charPairBrown prov (T2DataBordismGrp.mk (pinPlusCharPairData prov) p) = 0 →
      0 < p.2.n → CapstoneAmbientSupply prov p) :
    KernelReducesToSpin prov :=
  kernelReducesToSpin_of_ambientDatumSupply
    (fun p hbrown hpos => (H p hbrown hpos).toAmbientSurgeryDatum)

end

end SKEFTHawking.PinPlusTraceCapstoneInhabit
