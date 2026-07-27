/-
# Phase 5q.H — hcolD bricks **B5 + B6**: the rank-zero collapse row's membrane leg, CLOSED.

The `hcol`/`hcolD` row item of the 16-convergence assembly
(`PinPlusKTAssemblyResiduals.kt_equiv_zmod16_of_residuals_ofKRS_phig`, hypothesis 6) is the
terminal-KT collapse: every rank-0 structured manifold is bordant to one with a LITERALLY empty
characteristic surface. `PinPlusKTCollapseDischarge` reduced it to the per-object
`RankZeroCollapseDatum`; `PinPlusKTRankZeroBounding` (B1) froze the geometric membrane interface and
composed it through B4 into the membrane leaf row `TraceMembraneLeaves`. **This module closes the
remaining packaging** — B5 (leaf rows ⟹ tethered `Bor`) and B6 (reverse + package) — so that the
whole collapse row bottoms out in ONE named row of geometric atoms on the CONSTRUCTED capstone
carrier, exactly as `PinPlusTraceCapstoneInhabit.CapstoneAmbientSupply` did for the KRS lane.

## What lands GREEN here.

* **§1 (B5)** `rankZeroTethered` — the B1a bounding datum + the B1b weld anchor + the trace's
  W-admissibility leaf row `TraceWAdmLeaves` produce a genuine `CharPairBorRealizedTethered` on the
  capstone `s ⇝ t` (empty-Σ source, rank-0 target). Pure composition of `traceTethered_of_leaves`
  with `RankZeroSurfaceWeldAnchor.toLeaves`; no transport lemma, no new atom.
* **§2 (B6)** `rankZeroCollapseDatum_ofWeldAnchor` — reverses the capstone with `symmBorTethered`
  (`b.symm.W = b.W`, so the Hausdorff certificate and the membrane tether are reused verbatim) and
  packages the result as `RankZeroCollapseDatum prov ⟨t, τ⟩` with collapse endpoint `⟨s, σ⟩`. This
  is the FIRST in-tree construction of a `RankZeroCollapseDatum` from geometric inputs — until now
  the datum was only ever consumed.
* **§3** `RankZeroCollapseSupply prov p` — the per-object row bundling every input of §2 for a
  rank-0 representative `p`: the collapse endpoint `p'` with its emptiness witness, the D⁵
  attaching/collar/surgered-end capstone data, the W-admissibility leaf row, and the B1a/B1b
  bounding + weld data. Mirrors `CapstoneAmbientSupply` field-for-field in spirit. The Hausdorff
  certificates on BOTH ends are derived (`CharPairStr.t2`), not carried — they are not atoms.
* **§4** the assembly wirings: a `∀`-`p` supply discharges `hcolD`, hence `hcol`, hence the
  16-convergence headlines with the collapse row replaced by the geometric supply — including
  **the assembly of record** (`kt_equiv_zmod16_of_residuals_ofKRS_collapseSupply`, at `k = 0`) and
  the two-row finest-grain form that ALSO carries the `#206` degenerate-`(1,4)` Freeze-B residual.
* **§5** anti-vacuity: the supply delivers the pin⁻ spin-kill atom (`B.membraneSpinKill`, the
  irreducible content the mod-2 intersection form cannot see) and the class-level collapse
  `GeometricSpinRepresentable (mk p)`.
* **§6** demand narrowing: the already-empty-Σ fibre of the collapse row is FREE (reflexive
  cylinder), so the honest residual is confined to rank-0 representatives with NONEMPTY surface.
* **§7** the B2 wall, kernel-encoded: a carrier admitting a Wu witness (`μ(a₀ ⌣ a₀) ≠ 0`) carries NO
  characteristic-pair structure with an empty surface, and every collapse endpoint is necessarily
  Wu-null — so on that sector the terminal move is FORCED to change the carrier.

## What is NOT discharged here (say it loudly).

`RankZeroCollapseSupply` is an INTERFACE, not an inhabitation. Its two genuinely open fields are:

1. **B2 — the terminal characteristic extension.** Supplying `p'`/`S`/`φ`/`cd`/`d` means producing
   KT §5's empty-surface endpoint together with the combined Pin⁺ trace realising it. Kirby–Taylor's
   move is a characteristic-pair bordism to a DIFFERENT 4-manifold (whose `w₁`-dual has trivial
   normal bundle), not a cap in `M × I`; when `v₂(M) ≠ 0` a same-carrier cap is impossible outright
   (`[Σ]_M = 0 ⟺ v₂(M) = 0`). No framing/normal-Euler hypothesis is available, so the
   "one sphere, one index-3 handle" shortcut is unsound in the required generality. THIS IS THE
   WALL.
2. **B3 — `TraceWAdmLeaves` on the collapse trace.** The Poincaré–Lefschetz/Wu row of the pair
   `(W, ∂W)` for the collapse trace. `PinPlusKTSphereProdWAdm`'s degenerate-`(1,4)` collapse does
   NOT apply here (it needs `H¹(W) = 0`, true for `S² × D³`, absent for a general collapse trace).

Everything BETWEEN those two — the membrane realization, the kernel conditions, the weld, the glue,
the tether, the reversal, the packaging — is now closed.

**Circularity audit (by proof inspection).** Every declaration is term-level composition of
`traceTethered_of_leaves`, `RankZeroSurfaceWeldAnchor.toLeaves`, `symmBorTethered`,
`RankZeroCollapseDatum.isT2DataBordant` and `rankZeroCollapsesToEmptySurf_of_datumSupply`. No
`k₀`/`KTNonSplit`-strength fact, no `÷32`, no output of the `kt_equiv_zmod16` assembly is consumed.
CLEAN.

Grade: `k = 0` throughout — the capstone stack (`ktHandleAttachment`, `SurgeredEndDatum`,
`capstoneB`) is `C⁰` by construction, exactly like the sibling KRS row `CapstoneAmbientSupply`.
Nothing is transported from `k = 0` to `k ≥ 1` (fork `k0-to-k1-transport-refuted`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.PinPlusKTRankZeroBounding
import SKEFTHawking.PinPlusKTCollapseDischarge
import SKEFTHawking.PinPlusKTWuSectorSplit
import SKEFTHawking.PinPlusKTSphereProdWAdm

open scoped Manifold
open Topology
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.T2TangentialBordism SKEFTHawking.TangentialDataBordism
open SKEFTHawking.BordismTheory
open SKEFTHawking.SurgeryFoundation
open SKEFTHawking.SurgeryFoundation.HandleAttachment
open SKEFTHawking.DiskChartGeneric (D5)
open SKEFTHawking.PinPlusWAdmPinned
open SKEFTHawking.PinPlusTraceMembranePresented
open SKEFTHawking.PinPlusTraceCapstoneInhabit
open SKEFTHawking.PinPlusCharPairEmptySourceRealization
open SKEFTHawking.PinPlusKTRankZeroBounding
open SKEFTHawking.PinPlusKTExtension
open SKEFTHawking.PinPlusKTKernelSector
open SKEFTHawking.PinPlusKTStepGate
open SKEFTHawking.PinPlusKTSpinForgetPhi
open SKEFTHawking.PinPlusKTSpinPresentationRow
open SKEFTHawking.PinPlusKTKerPhiDoubles
open SKEFTHawking.PinPlusKTSectorGeometricReduce
open SKEFTHawking.PinPlusTraceCapstoneResidualRow
open SKEFTHawking.PinPlusKTAssemblyResiduals
open SKEFTHawking.PinPlusKTCollapseDischarge
open SKEFTHawking.PinPlusKTWuSectorSplit
open SKEFTHawking.PinPlusKTSphereProdWAdm
open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularPD4Instances SKEFTHawking.PoincareDualityWu
open SKEFTHawking.PoincareLefschetzWu5 SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzWuAssembly

namespace SKEFTHawking.PinPlusKTRankZeroCollapseSupply

/-! ## §0. Rank-zero index emptiness — how the collapse sector supplies `IsEmpty (Fin n)`. -/

variable {k : WithTop ℕ∞}

/-- **The spin-sector predicate empties the enhancement index.** `IsSpinSectorStr prov p` is
literally `p.2.n = 0`, so `Fin p.2.n` is empty — the instance the rank-zero membrane constructors
(`TauMembraneWeldDatum.ofRankZero`, `RankZeroSurfaceWeldAnchor.toLeaves`) take. -/
theorem isEmpty_fin_of_spinSector {prov : CharPairWProviderPerOp (𝓡 4) k}
    {p : StrMfd (pinPlusCharPairData prov).toTangentialData} (hp : IsSpinSectorStr prov p) :
    IsEmpty (Fin p.2.n) := by
  rw [show p.2.n = 0 from hp]; infer_instance

/-- **An empty characteristic surface empties the enhancement index.** Composes the banked
`spinSector_of_isEmpty_surf` (empty `Σ` ⟹ rank 0, through the carried basis equiv) with §0's
index reading — the instance the collapse ENDPOINT `p'` must supply. -/
theorem isEmpty_fin_of_isEmpty_surf {prov : CharPairWProviderPerOp (𝓡 4) k}
    {p : StrMfd (pinPlusCharPairData prov).toTangentialData} (h : IsEmpty p.2.surf.M) :
    IsEmpty (Fin p.2.n) :=
  isEmpty_fin_of_spinSector (spinSector_of_isEmpty_surf prov p h)

/-! ## §1. B5 — the two leaf rows produce the tethered `Bor` on the collapse capstone. -/

noncomputable section

variable {s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)} [T2Space s.M] [T2Space t.M]

/-- **B5: the collapse trace IS a tethered `Bor` witness.** For the capstone `s ⇝ t` with an
EMPTY-Σ source `σ` and a rank-0 target `τ`, the B1b weld anchor's membrane leaf row
(`RankZeroSurfaceWeldAnchor.toLeaves`, itself the B1a bounding datum composed through B4) together
with the trace's W-admissibility leaf row `wl` discharge the full
`CharPairBorRealizedTethered` via the banked `traceTethered_of_leaves`. The tether's closed
embedding `Q ↪ W` is weld-supplied; no untethered variant is rebuilt. -/
def rankZeroTethered
    {S : Set D5} {hS : IsClosed S} {φ : ↥S → s.M × Set.Icc (0 : ℝ) 1}
    {hφ : Continuous φ} {hφinj : Function.Injective φ}
    {cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier}
    {hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd}
    {d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam}
    {σ : CharPairStrBundled (𝓡 4) s} {τ : CharPairStrBundled (𝓡 4) t}
    [IsEmpty σ.surf.M] [IsEmpty (Fin σ.n)] [IsEmpty (Fin τ.n)]
    {B : RankZeroSurfaceBoundingDatum τ}
    (A : RankZeroSurfaceWeldAnchor s t S hS φ hφ hφinj cd hseam d σ τ B)
    (wl : TraceWAdmLeaves (capstoneB s t S hS φ hφ hφinj cd hseam d)) :
    CharPairBorRealizedTethered (capstoneB s t S hS φ hφ hφinj cd hseam d) σ τ :=
  traceTethered_of_leaves wl A.toLeaves

/-! ## §2. B6 — reversal and packaging as the per-object collapse datum. -/

/-- **B6: the rank-zero collapse datum, CONSTRUCTED.** The capstone runs empty-Σ source `⇝` rank-0
target; the collapse datum needs the OPPOSITE direction, supplied by `symmBorTethered` (bordism
reversal keeps the carrier — `b.symm.W = b.W` — so the Hausdorff certificate `capstone_t2Space` and
the membrane tether `ιW` are reused verbatim, only the two glue equations transpose). The result is
a genuine `RankZeroCollapseDatum prov ⟨t, τ⟩` whose target `⟨s, σ⟩` has a LITERALLY empty
characteristic surface — the terminal-KRS bounding datum in the shape hypothesis 6 consumes. -/
def rankZeroCollapseDatum_ofWeldAnchor (prov : CharPairWProviderPerOp (𝓡 4) 0)
    {S : Set D5} {hS : IsClosed S} {φ : ↥S → s.M × Set.Icc (0 : ℝ) 1}
    {hφ : Continuous φ} {hφinj : Function.Injective φ}
    {cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier}
    {hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd}
    {d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam}
    {σ : CharPairStrBundled (𝓡 4) s} {τ : CharPairStrBundled (𝓡 4) t}
    [IsEmpty σ.surf.M] [IsEmpty (Fin σ.n)] [IsEmpty (Fin τ.n)]
    {B : RankZeroSurfaceBoundingDatum τ}
    (A : RankZeroSurfaceWeldAnchor s t S hS φ hφ hφinj cd hseam d σ τ B)
    (wl : TraceWAdmLeaves (capstoneB s t S hS φ hφ hφinj cd hseam d)) :
    RankZeroCollapseDatum prov ⟨t, τ⟩ where
  p' := ⟨s, σ⟩
  hemp := inferInstance
  b := (capstoneB s t S hS φ hφ hφinj cd hseam d).symm
  hT2 := capstone_t2Space s t S hS φ hφ hφinj cd hseam d
  hBor := ⟨symmBorTethered (rankZeroTethered A wl)⟩

end

/-! ## §3. The per-object collapse supply row. -/

/-- **THE RANK-ZERO COLLAPSE SUPPLY at `p`** — every input `rankZeroCollapseDatum_ofWeldAnchor`
consumes, bundled per rank-0 representative `p` as one named row (the collapse lane's counterpart of
`CapstoneAmbientSupply`). The Hausdorff certificates on both ends are DERIVED from the carried
structures (`CharPairStr.t2`), never fields — they are not atoms. Every remaining field is:

* `p'`/`hemp` — the KT §5 empty-surface endpoint (**B2**, the wall);
* `S`/`hS`/`φ`/`hφ`/`hφinj`/`cd`/`hseam`/`d` — the D⁵ attaching, seam-collar and surgered-end data
  building the combined trace `W` (**B2**, the wall);
* `wl` — the trace's Poincaré–Lefschetz/Wu leaf row (**B3**; itself a named row of geometric atoms,
  reducible on the constructed carrier through `TraceRelFundLeaves.ofCapstone` with `hWT1` free);
* `B`/`A` — the B1a bounding datum (compact `MembraneModel`-charted `Q` with `range e = ∂Q`, the
  pin⁻ spin-bit compatibility, the interior `H₁` coordinates) and the B1b capstone weld anchor.

No field is a completeness `Prop`; the row is Type-valued and per-object, exactly the gate-blessed
`AmbientSurgeryDatum`/`CapstoneAmbientSupply` shape. The rank-zero hypothesis on `p` is deliberately
NOT a parameter (no field needs it — the fields are rank-agnostic, as `PinPlusKTRankZeroBounding`
records for the bounding datum); it enters only at consumption, in `toCollapseDatum`. -/
structure RankZeroCollapseSupply (prov : CharPairWProviderPerOp (𝓡 4) 0)
    (p : StrMfd (pinPlusCharPairData prov).toTangentialData) where
  /-- the collapse endpoint (KT §5's orientable/spin end). -/
  p' : StrMfd (pinPlusCharPairData prov).toTangentialData
  /-- **THE COLLAPSE**: the endpoint's characteristic surface is LITERALLY empty. -/
  hemp : IsEmpty p'.2.surf.M
  /-- the attaching region `S ⊆ D⁵`. -/
  S : Set D5
  /-- `S` is closed. -/
  hS : IsClosed S
  /-- the attaching map `φ : S → M' × I`. -/
  φ : letI := p'.2.toCharPairStr.t2
    ↥S → p'.1.M × Set.Icc (0 : ℝ) 1
  /-- `φ` is continuous. -/
  hφ : letI := p'.2.toCharPairStr.t2; Continuous φ
  /-- `φ` is injective. -/
  hφinj : letI := p'.2.toCharPairStr.t2; Function.Injective φ
  /-- the seam-collar datum on the handle carrier. -/
  cd : letI := p'.2.toCharPairStr.t2
    SeamCollarDatum (ktHandleAttachment p'.1.M D5 S hS φ hφ hφinj).carrier
  /-- the seam containment. -/
  hseam : letI := p'.2.toCharPairStr.t2
    (ktHandleAttachment p'.1.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd
  /-- the surgered-end datum presenting `p.1` as the trace's far end. -/
  d : letI := p'.2.toCharPairStr.t2
    SurgeredEndDatum p'.1 p.1 S hS φ hφ hφinj cd hseam
  /-- **B3**: the trace's W-admissibility leaf row (relative fundamental class, the two
  Poincaré–Lefschetz halves, the Betti equalities, `w₂(W) = 0`). -/
  wl : letI := p'.2.toCharPairStr.t2
    TraceWAdmLeaves (capstoneB p'.1 p.1 S hS φ hφ hφinj cd hseam d)
  /-- **B1a**: the rank-zero surface bounding datum for the target's characteristic surface. -/
  B : letI := p.2.toCharPairStr.t2; RankZeroSurfaceBoundingDatum p.2
  /-- **B1b**: the capstone weld anchor binding `B`'s membrane into the fixed trace carrier. -/
  A : letI := p'.2.toCharPairStr.t2; letI := p.2.toCharPairStr.t2
    letI := hemp; letI := isEmpty_fin_of_isEmpty_surf hemp
    RankZeroSurfaceWeldAnchor p'.1 p.1 S hS φ hφ hφinj cd hseam d p'.2 p.2 B

namespace RankZeroCollapseSupply

variable {prov : CharPairWProviderPerOp (𝓡 4) 0}
  {p : StrMfd (pinPlusCharPairData prov).toTangentialData}

/-- **The supply discharges the per-object collapse datum** — §2 applied to the bundled fields.
The rank-zero hypothesis `hp` is consumed HERE (it is what `toLeaves` needs to dissolve the target's
bounding-kernel conditions), not carried by the row. Note `⟨p.1, p.2⟩ = p` definitionally (`Sigma`
eta), so no transport is needed. -/
noncomputable def toCollapseDatum (D : RankZeroCollapseSupply prov p)
    (hp : IsSpinSectorStr prov p) :
    RankZeroCollapseDatum prov p :=
  letI := D.p'.2.toCharPairStr.t2
  letI := p.2.toCharPairStr.t2
  letI := D.hemp
  letI := isEmpty_fin_of_isEmpty_surf D.hemp
  letI := isEmpty_fin_of_spinSector hp
  rankZeroCollapseDatum_ofWeldAnchor prov D.A D.wl

end RankZeroCollapseSupply

/-! ## §4. The assembly wirings — `hcol` and the two 16-convergence headlines. -/

variable {prov : CharPairWProviderPerOp (𝓡 4) 0}

/-- **THE COLLAPSE ROW FROM THE GEOMETRIC SUPPLY** — a `∀`-`p` (over the rank-0 sector) supply of
the collapse row discharges hypothesis 6 of the 16-convergence assembly. The `∀` lives only in the
supply hypothesis; the row itself is per-object and Type-valued. -/
theorem rankZeroCollapsesToEmptySurf_of_collapseSupply
    (H : ∀ p : StrMfd (pinPlusCharPairData prov).toTangentialData,
      IsSpinSectorStr prov p → RankZeroCollapseSupply prov p) :
    RankZeroCollapsesToEmptySurf prov :=
  rankZeroCollapsesToEmptySurf_of_datumSupply (fun p hp => (H p hp).toCollapseDatum hp)

/-- **THE ASSEMBLY OF RECORD, collapse row replaced by the geometric supply.** The seven-hypothesis
row `kt_equiv_zmod16_of_residuals_ofKRS_phig` with its sixth item `hcol` supplied by the §3
geometric row instead of being posited. Stated at `k = 0` — NOT k-generic: the capstone stack
(`ktHandleAttachment` / `SurgeredEndDatum` / `capstoneB`) that `RankZeroCollapseSupply` rests on is
`C⁰` by construction, and nothing here is transported to `k ≥ 1`. The other six hypotheses are
untouched, so this is a drop-in refinement of the assembly of record at that grade. -/
theorem kt_equiv_zmod16_of_residuals_ofKRS_collapseSupply
    (prov : CharPairWProviderPerOp (𝓡 4) 0)
    (hKRS : KernelReducesToSpin prov)
    (row : SpinPresentationRow prov)
    (hA : row.R.RealizesSphereProducts) (hB : row.R.SphereProductBounds)
    (hcolS : ∀ p : StrMfd (pinPlusCharPairData prov).toTangentialData,
      IsSpinSectorStr prov p → RankZeroCollapseSupply prov p)
    (hker : KerPhiSubDoubles prov)
    (hΦg : spinForgetPhi prov (DataBordismGrp.mk (spinEmptyData prov) row.g)
        = ktKernelRep prov) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData prov) ≃+ ZMod 16) :=
  kt_equiv_zmod16_of_residuals_ofKRS_phig prov hKRS row hA hB
    (rankZeroCollapsesToEmptySurf_of_collapseSupply hcolS) hker hΦg

/-- **The Rokhlin-16 twin of the assembly-of-record wiring** — `Nat.card Ω₄^{Pin⁺} = 16` from the
same row. Pure transport of `Nat.card (ZMod 16) = 16` across the additive equivalence. -/
theorem rokhlin_sixteen_of_residuals_ofKRS_collapseSupply
    (prov : CharPairWProviderPerOp (𝓡 4) 0)
    (hKRS : KernelReducesToSpin prov)
    (row : SpinPresentationRow prov)
    (hA : row.R.RealizesSphereProducts) (hB : row.R.SphereProductBounds)
    (hcolS : ∀ p : StrMfd (pinPlusCharPairData prov).toTangentialData,
      IsSpinSectorStr prov p → RankZeroCollapseSupply prov p)
    (hker : KerPhiSubDoubles prov)
    (hΦg : spinForgetPhi prov (DataBordismGrp.mk (spinEmptyData prov) row.g)
        = ktKernelRep prov) :
    Nat.card (T2DataBordismGrp (pinPlusCharPairData prov)) = 16 := by
  obtain ⟨e⟩ := kt_equiv_zmod16_of_residuals_ofKRS_collapseSupply prov hKRS row hA hB hcolS hker hΦg
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, ZMod.card]

/-- **THE COLLAPSE-SUPPLY WIRING** — the 16-convergence headline with the collapse row at its
finest geometric grain: `hcol`/`hcolD` replaced by a `∀`-`p` supply of `RankZeroCollapseSupply`,
whose only open fields are the B2 terminal characteristic extension and the B3 Poincaré–Lefschetz/Wu
row of the resulting trace. Everything else in the collapse row — membrane, kernel conditions, weld,
glue, tether, reversal — is discharged inside. -/
theorem kt_equiv_zmod16_of_residuals_collapseSupply
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (row : SpinPresentationRow residualProv)
    (hA : row.R.RealizesSphereProducts) (hB : row.R.SphereProductBounds)
    (hcolS : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        IsSpinSectorStr residualProv p → RankZeroCollapseSupply residualProv p)
    (hker : KerPhiSubDoubles residualProv)
    (hΦg : spinForgetPhi residualProv
        (DataBordismGrp.mk (spinEmptyData residualProv) row.g) = ktKernelRep residualProv) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData residualProv) ≃+ ZMod 16) :=
  kt_equiv_zmod16_of_residuals_collapseDatum H row hA hB
    (fun p hp => (hcolS p hp).toCollapseDatum hp) hker hΦg

/-- **The Rokhlin-16 twin of the collapse-supply wiring** — `Nat.card Ω₄^{Pin⁺} = 16` from the same
row. Pure transport; introduces no new residual atom. -/
theorem rokhlin_sixteen_of_residuals_collapseSupply
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (row : SpinPresentationRow residualProv)
    (hA : row.R.RealizesSphereProducts) (hB : row.R.SphereProductBounds)
    (hcolS : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        IsSpinSectorStr residualProv p → RankZeroCollapseSupply residualProv p)
    (hker : KerPhiSubDoubles residualProv)
    (hΦg : spinForgetPhi residualProv
        (DataBordismGrp.mk (spinEmptyData residualProv) row.g) = ktKernelRep residualProv) :
    Nat.card (T2DataBordismGrp (pinPlusCharPairData residualProv)) = 16 :=
  rokhlin_sixteen_of_residuals_collapseDatum H row hA hB
    (fun p hp => (hcolS p hp).toCollapseDatum hp) hker hΦg

/-- **THE TWO-ROW FINEST-GRAIN HEADLINE** — the 16-convergence assembly with BOTH sharpened row
items simultaneously: the Freeze-B geometric slot `row.R.s2s2` at the `#206` degenerate-`(1,4)`
residual (a T2 coboundary with relative fundamental class, the two subsingleton facts, a pinned
`(2,3)` Poincaré–Lefschetz datum and `v₂ = 0` — the whole `(1,4)` Wu leg free), AND the collapse row
at the §3 geometric supply (B2 + B3 open, everything between them closed). Every other consumer
shape (`H`, `row`, `hCob`/`hBase`, `hker`, `hΦg`) is unchanged. -/
theorem kt_equiv_zmod16_of_residuals_degenerate14_collapseSupply
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (row : SpinPresentationRow residualProv)
    (hCob : row.R.HandleTradeCobordism) (hBase : row.R.HyperbolicBase)
    (b : Bordism ((𝓡 4).prod (𝓡∂ 1)) row.R.s2s2.1 (emptySM (X := PUnit) (k := 0) (I := 𝓡 4)))
    (hWT2 : T2Space b.W)
    (Drel : RelFundClassDatum (X := TopCat.of b.W) (m := 3)
      (((𝓡 4).prod (𝓡∂ 1)).boundary b.W))
    [Subsingleton (Cohomology (TopCat.of b.W) 1)]
    [Subsingleton (RelativeCohomology (X := TopCat.of b.W) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W) 4)]
    (P23 : LefschetzWuDatum (TopCat.of b.W) (((𝓡 4).prod (𝓡∂ 1)).boundary b.W) 2 3 5)
    (pin23 : LefschetzWuPinned23 P23) (hv2 : wuClass P23 = 0)
    (hcolS : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        IsSpinSectorStr residualProv p → RankZeroCollapseSupply residualProv p)
    (hker : KerPhiSubDoubles residualProv)
    (hΦg : spinForgetPhi residualProv
        (DataBordismGrp.mk (spinEmptyData residualProv) row.g) = ktKernelRep residualProv) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData residualProv) ≃+ ZMod 16) :=
  kt_equiv_zmod16_of_residuals_freezeAtoms_ofDegenerate14 H row hCob hBase b hWT2 Drel P23 pin23 hv2
    (fun p hp => (hcolS p hp).toCollapseDatum hp) hker hΦg

/-! ## §5. Anti-vacuity — what the supply's geometric fields actually cost. -/

/-- **The supply delivers the pin⁻ spin-kill atom.** The B1a datum's `pinCompat` field upgrades
(through the banked `membraneSpinKill_of_kernelSpinVanishing`) to the geometric `MembraneSpinKill`
on the bounding package — the irreducible pin⁻ content the mod-2 intersection form cannot see. A
purely homological "membrane" cannot satisfy it, so the field is genuinely load-bearing. -/
theorem RankZeroCollapseSupply.membraneSpinKill
    {p : StrMfd (pinPlusCharPairData prov).toTangentialData}
    (D : RankZeroCollapseSupply prov p) :
    letI := p.2.toCharPairStr.t2; D.B.bound.MembraneSpinKill :=
  letI := p.2.toCharPairStr.t2
  D.B.membraneSpinKill

/-- **The supply collapses `p`'s class geometrically.** `mk p = mk p'` with `p'` carrying a
LITERALLY empty characteristic surface — i.e. `GeometricSpinRepresentable` holds at `p`'s class.
This is exactly the dC-leaf content the collapse row exists to supply, delivered per object rather
than as a class-level `∃`. -/
theorem RankZeroCollapseSupply.geometricSpinRepresentable
    {p : StrMfd (pinPlusCharPairData prov).toTangentialData}
    (D : RankZeroCollapseSupply prov p) (hp : IsSpinSectorStr prov p) :
    GeometricSpinRepresentable prov (T2DataBordismGrp.mk (pinPlusCharPairData prov) p) :=
  ⟨D.p', D.hemp,
    (T2DataBordismGrp.mk_eq_of_bordant _ (D.toCollapseDatum hp).isT2DataBordant).symm⟩

/-! ## §6. DEMAND NARROWING — the already-empty fibre of the collapse row is FREE.

`RankZeroCollapsesToEmptySurf` quantifies over EVERY rank-0 representative, but the sub-fibre whose
characteristic surface is already empty needs no geometry at all: such a representative collapses to
ITSELF along the reflexive cylinder, whose `Bor` is the carrier's own `cylBor` and whose total space
`M × [0,1]` is Hausdorff from the structure's `t2` field. So the honest residual — the thing B2 must
actually construct — is confined to rank-0 representatives with a **nonempty** characteristic
surface. -/

/-- **The already-empty collapse datum is FREE.** A representative whose characteristic surface is
already empty is its own collapse endpoint, via the reflexive cylinder (`reflCylinder`, `cylBor`).
No capstone, no membrane, no weld. -/
noncomputable def rankZeroCollapseDatum_of_isEmpty_surf
    {prov : CharPairWProviderPerOp (𝓡 4) k}
    (p : StrMfd (pinPlusCharPairData prov).toTangentialData) (h : IsEmpty p.2.surf.M) :
    RankZeroCollapseDatum prov p where
  p' := p
  hemp := h
  b := reflCylinder p.1
  hT2 := by
    haveI := p.2.toCharPairStr.t2
    exact inferInstanceAs (T2Space (p.1.M × Set.Icc (0 : ℝ) 1))
  hBor := ⟨(pinPlusCharPairData prov).cylBor p.2⟩

/-- **THE NARROWED COLLAPSE DEMAND** — `RankZeroCollapsesToEmptySurf` follows from a datum supply
that is only required on rank-0 representatives with a **NONEMPTY** characteristic surface; the
already-empty fibre is discharged by the reflexive cylinder. Strictly weaker hypothesis than
`rankZeroCollapsesToEmptySurf_of_datumSupply`, so every downstream consumer of the collapse row
inherits the narrower demand. -/
theorem rankZeroCollapsesToEmptySurf_of_nonemptySurfSupply
    {prov : CharPairWProviderPerOp (𝓡 4) k}
    (H : ∀ p : StrMfd (pinPlusCharPairData prov).toTangentialData,
      IsSpinSectorStr prov p → Nonempty p.2.surf.M → RankZeroCollapseDatum prov p) :
    RankZeroCollapsesToEmptySurf prov := by
  intro p hp
  rcases isEmpty_or_nonempty p.2.surf.M with he | hne
  · exact ⟨p, he, (rankZeroCollapseDatum_of_isEmpty_surf p he).isT2DataBordant⟩
  · exact ⟨(H p hp hne).p', (H p hp hne).hemp, (H p hp hne).isT2DataBordant⟩

/-! ## §7. THE B2 WALL, KERNEL-ENCODED — a Wu-witnessed carrier admits NO empty-Σ structure.

The one place where the collapse row's residual is not merely "unbuilt" but *structurally forced to
change the carrier*. Combining B0's Wu-sector split with the emptiness of `H₂(∅)`: if the carrier
`s.M` admits a single cohomology class `a₀` with `μ(a₀ ⌣ a₀) ≠ 0` (i.e. `v₂(s.M) ≠ 0`), then NO
`CharPairStrBundled` on `s` can have an empty characteristic surface. Consequences for hcolD:

* the terminal collapse of such a representative can NEVER be realised on the same carrier — in
  particular not by a cap inside `M × I`, and not by the reflexive-cylinder shortcut of §6;
* so B2 must genuinely produce a DIFFERENT 4-manifold (KT §5's characteristic extension, whose
  `w₁`-dual acquires a trivial normal bundle), exactly as the route dossier concluded;
* and §6's narrowing is sharp on that sector: those representatives are precisely the nonempty-Σ
  ones the supply must still serve. -/

/-- **THE CARRIER-CHANGE FORCING.** On a carrier admitting a Wu witness `a₀` (`μ(a₀ ⌣ a₀) ≠ 0`,
i.e. `v₂ ≠ 0`) there is NO characteristic-pair structure with an empty characteristic surface: an
empty surface has `surfClass = 0` (subsingleton `H₂(∅)`), which by B0's split
(`surfClass_pushforward_witness`) contradicts the witness. Falsifiable and non-vacuous: the witness
hypothesis is exactly the `ℝP⁴`-type condition, and the conclusion rules out an entire class of
proposed collapse endpoints. -/
theorem no_isEmpty_surf_of_wu_witness
    {s : SingularManifold.{0} PUnit.{1} k (𝓡 4)} [T2Space s.M] [Nonempty s.M]
    (str : CharPairStrBundled (𝓡 4) s)
    (a₀ : Cohomology (TopCat.of s.M) 2)
    (ha₀ : (poincareDual4Mid_of_closed (M := s.M)).mu (cupH24 a₀ a₀) ≠ 0) :
    ¬ IsEmpty str.surf.M := by
  intro hemp
  haveI := hemp
  exact surfClass_pushforward_witness str a₀ ha₀ (Subsingleton.elim _ _)

/-- **The collapse endpoint is necessarily Wu-null.** Every `RankZeroCollapseDatum`'s endpoint has
an empty characteristic surface, hence (B0, `wuNull_of_surfClass_eq_zero`) a carrier whose Wu
functional vanishes identically. Read against §7's forcing: a datum at a Wu-witnessed `p` must land
on a carrier that is NOT Wu-witnessed — the terminal KT move is topology-changing, never a
same-carrier cap. -/
theorem RankZeroCollapseDatum.endpoint_wuNullCarrier
    {prov : CharPairWProviderPerOp (𝓡 4) k}
    {p : StrMfd (pinPlusCharPairData prov).toTangentialData} (D : RankZeroCollapseDatum prov p)
    [Nonempty D.p'.1.M] :
    letI := D.p'.2.toCharPairStr.t2; WuNullCarrier D.p'.2 :=
  letI := D.p'.2.toCharPairStr.t2
  haveI := D.hemp
  wuNull_of_surfClass_eq_zero D.p'.2 (Subsingleton.elim _ _)

end SKEFTHawking.PinPlusKTRankZeroCollapseSupply
