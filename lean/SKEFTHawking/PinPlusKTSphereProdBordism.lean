/-
# Phase 5q.H close-out (#203) — THE S²×S² BOUNDING BORDISM: the coboundary WAdmPinned isolated.

This module attacks the Freeze-B geometric atom of the current sharpest end-to-end assembly
(`PinPlusKTFreezeDischarge.kt_equiv_zmod16_of_residuals_freezeAtoms`):

    hBbord : IsDataBordant (spinEmptyData residualProv) row.R.s2s2
               ⟨emptySM, (spinEmptyData residualProv).emptyStr⟩

the geometric witness that the distinguished `s2s2` slot bounds (the `S²×S² = ∂(S²×D³)` content).

## The gap inventory (kernel-checked) — where the #200 triage was superseded.

The #200 Freeze triage held `hBbord` at the raw bordism grain, believing the concrete route was
gated behind the Mathlib-absent **closed-ball atlas** (`SphereDiskSmoothData`). That gap is BANKED:

* **The closed-ball `Dⁿ` `IsManifold` instance** and the **change-of-model transport** (the two frozen
  `SphereDiskSmoothData` fields of `SphereProductBounding`) are both discharged in `SphereDiskFreezeB`
  (`sphereDiskSmoothData`, on the re-associated `J5` collar atlas of `SphereDiskJ5` — `isManifold_J5`,
  `smooth_incl_J5`, `boundary_J5_eq`). So on the `I4 = (𝓡 2).prod (𝓡 2)` / `trivialData` carrier the
  concrete Freeze-B `[S²×S²] = 0` is already GREEN (`trivialSpherePresentation_freezeB`).
* **The empty-membrane realization** — every `StrMfd (spinEmptyData prov)` has Σ = ∅ BY CONSTRUCTION
  (`spinEmptyData.Mfd := {σ // IsEmpty σ.surf.M}`), so the whole membrane-realization / Taylor-leg /
  Lagrangian / tether apparatus of a spin-carrier bordism witness COLLAPSES via the #171 empty-source
  machinery (`emptySourceRealizationTied`, `taylorLegVanishes_emptySource`, `jointLagrangian_emptySource`).

What genuinely stands between the banked package and firing `hBbord` on the SPIN carrier
`spinEmptyData residualProv` (NOT the `trivialData` carrier, where `Bor ≡ PUnit`) is the **one deep
input a spin-carrier bordism witness needs and the op-provider does not supply**:

* **`WAdmPinned b` for the `S²×D³` coboundary** — the substrate-pinned Lefschetz–Wu `w₂(W) = 0` tower
  (rel-Poincaré–Lefschetz duality + Steenrod squares) on the 5-manifold-with-boundary `W = S²×D³`.
  `CharPairBorRealizedTethered` (which `spinEmptyData.Bor` requires) is assembled ONLY through
  `mkCharPairBorRealizedTethered`, whose FIRST argument is a `WAdmPinned b` (even the surgery-trace
  path `borTetheredOfWeld` takes it as an input). The per-op provider `residualProv` supplies
  `WAdmPinned` for the cylinder/doubling/mapCylinder/add op family ONLY; the `S²×D³` coboundary is not
  in that family, and its Lefschetz–Wu tower needs manifold cohomology Mathlib lacks (the same
  Künneth / EZ-cross-product gap `SphereProdGramPin` records as off-critical-path/deferred).

## What lands GREEN here (an honest reduction — NO minted completeness `Prop`, NO consumed assembly output).

`isDataBordant_empty_of_wadm` — for ANY spin-carrier element `p` and ANY coboundary bordism `b : p.1 ↝ ∅`
with `T2Space b.W` and `WAdmPinned b`, the empty-membrane collapse (via #171) assembles the tethered
witness and yields `IsDataBordant (spinEmptyData prov) p ⟨emptySM, emptyStr⟩`. This DISCHARGES every
non-`WAdmPinned` obligation of `hBbord` — the membrane, the tether, the T2, the quotient — leaving the
coboundary `WAdmPinned` (Lefschetz–Wu `w₂ = 0` tower) as the SOLE named geometric atom. The atom
`SphereProdCoboundaryWAdm` packages it existentially; `kt_equiv_zmod16_of_residuals_freezeAtoms_ofCoboundary`
(+ Rokhlin twin) is the conditional wiring: the finest-grain assembly with `hBbord` replaced by the
coboundary atom, every OTHER consumer shape (`H`, `row`, `hCob`, `hBase`, `hcolD`, `hker`, `hΦg`) fixed.

**Circularity audit (by proof inspection)**: `isDataBordant_empty_of_wadm` is pure term/tactic wiring of
the #171 empty-source realization + `mkCharPairBorRealizedTethered` into the `IsDataBordant` existential;
the wiring theorems compose it into the #199-audited `kt_equiv_zmod16_of_residuals_freezeAtoms`. NO
`k₀`/`KTNonSplit`-strength fact, NO `÷32`, NO output of the assembly is consumed; the `WAdmPinned` atom is
a genuine load-bearing geometric statement (the `w₂ = 0` filter the whole tethered apparatus turns on),
not a fabricated grade. CLEAN.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`. No new leaf `Prop` needing gate review is minted.
-/
import Mathlib
import SKEFTHawking.PinPlusKTFreezeDischarge
import SKEFTHawking.PinPlusCharPairEmptySourceRealization

open scoped Manifold
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.PinPlusCharPairRealizationTied
open SKEFTHawking.PinPlusWAdmPinned
open SKEFTHawking.PinPlusCharPairEmptySourceRealization
open SKEFTHawking.T2TangentialBordism SKEFTHawking.TangentialDataBordism
open SKEFTHawking.BordismTheory
open SKEFTHawking.SpinSigmaRoute
open SKEFTHawking.PinPlusKTExtension
open SKEFTHawking.PinPlusKTKernelSector
open SKEFTHawking.PinPlusKTKernelSpinRoute
open SKEFTHawking.PinPlusKTSpinForgetPhi
open SKEFTHawking.PinPlusCharPairSurfaceTie
open SKEFTHawking.PinPlusKTSpinPresentationRow
open SKEFTHawking.PinPlusKTKerPhiDoubles
open SKEFTHawking.PinPlusKTSectorGeometricReduce
open SKEFTHawking.PinPlusTraceCapstoneResidualRow
open SKEFTHawking.PinPlusKTAssemblyResiduals
open SKEFTHawking.PinPlusKTBinderDischarge
open SKEFTHawking.PinPlusKTCollapseDischarge
open SKEFTHawking.PinPlusKTFreezeDischarge

namespace SKEFTHawking.PinPlusKTSphereProdBordism

/-! ## §1. Empty surface forces algebraic rank 0. -/

/-- **An empty characteristic surface forces the enhancement rank to 0.** The bundle's `basis` is a
`ZMod 2`-linear equivalence `H¹(Σ;ℤ/2) ≃ (Fin n → ℤ/2)`; for `Σ = ∅` the left side is a subsingleton
(`subsingleton_cohomology`), so `Fin n → ℤ/2` is a subsingleton, and since `ℤ/2` is nontrivial this
forces `Fin n` empty. -/
theorem isEmpty_fin_n_of_isEmpty_surf {s : SingularManifold PUnit 0 (𝓡 4)}
    (σ : CharPairStrBundled (𝓡 4) s) [IsEmpty σ.surf.M] : IsEmpty (Fin σ.n) := by
  haveI := subsingleton_cohomology (M := σ.surf.M) 1
  haveI : Subsingleton (Fin σ.n → ZMod 2) := σ.basis.symm.toEquiv.subsingleton
  by_contra h
  rw [not_isEmpty_iff] at h
  obtain ⟨i⟩ := h
  have hcon : (fun _ : Fin σ.n => (0 : ZMod 2)) = (fun _ => 1) := Subsingleton.elim _ _
  have : (0 : ZMod 2) = 1 := congrFun hcon i
  exact absurd this (by decide)

/-! ## §2. The empty-membrane tethered bordism witness from a coboundary `WAdmPinned`. -/

/-- **The both-ends-empty membrane realization** (`Q = Σ_τ = ∅`) — the #171 empty-source realization
specialised to an empty target surface: the membrane `Q` is the (empty) target surface itself, the
boundary inclusion the identity, the interior basis the trivial rank-0 equivalence. Every certificate is
honest per-object topology on empty spaces. -/
noncomputable def emptyEndsReal {s t : SingularManifold.{0} PUnit.{1} 0 (𝓡 4)}
    (σ : CharPairStrBundled (𝓡 4) s) (τ : CharPairStrBundled (𝓡 4) t)
    [IsEmpty σ.surf.M] [IsEmpty τ.surf.M] :
    GeoRealizationTied (TopCat.of σ.surf.M) (TopCat.of τ.surf.M) σ.basis τ.basis :=
  haveI := τ.surfT2
  haveI : CompactSpace τ.surf.M := compactSpace_of_isEmpty
  emptySourceRealizationTied (TopCat.of σ.surf.M) (TopCat.of τ.surf.M) σ.basis τ.basis
    (TopCat.of τ.surf.M) (ContinuousMap.id _) Topology.IsClosedEmbedding.id 0
    (LinearEquiv.ofSubsingleton _ _)

/-- **The tethered characteristic-pair bordism witness for BOTH ends empty.** When both boundary
characteristic surfaces are empty (Σ = ∅), the entire membrane apparatus of a
`CharPairBorRealizedTethered` collapses via the #171 empty-source machinery: the realization is
`emptyEndsReal` on the empty membrane `Q = ∅`, the Taylor leg / Lagrangian dissolve to the vacuous
single-surface conditions, and the tether `ιW`/glue are vacuous. The ONLY genuine input is the
substrate-pinned Lefschetz–Wu datum `WAdmPinned b`. -/
noncomputable def charPairBorTethered_empty {s t : SingularManifold.{0} PUnit.{1} 0 (𝓡 4)}
    (σ : CharPairStrBundled (𝓡 4) s) (τ : CharPairStrBundled (𝓡 4) t)
    [IsEmpty σ.surf.M] [IsEmpty τ.surf.M] [IsEmpty (Fin σ.n)] [IsEmpty (Fin τ.n)]
    (b : Bordism ((𝓡 4).prod (𝓡∂ 1)) s t) (hWT2 : T2Space b.W) (wadmP : WAdmPinned b) :
    CharPairBorRealizedTethered b σ τ := by
  haveI := τ.surfT2
  haveI hQe : IsEmpty (↑(emptyEndsReal σ τ).Q) := inferInstanceAs (IsEmpty τ.surf.M)
  haveI : CompactSpace (↑(emptyEndsReal σ τ).Q) := compactSpace_of_isEmpty
  haveI hbdry : IsEmpty (↑(emptyEndsReal σ τ).bdry) :=
    inferInstanceAs (IsEmpty (σ.surf.M ⊕ τ.surf.M))
  haveI hsubU : IsEmpty (↑(SingularRelativeHomologyMod2.sub (emptyEndsReal σ τ).U)) :=
    ⟨fun x => isEmptyElim x.1⟩
  haveI hsubUc : IsEmpty (↑(SingularRelativeHomologyMod2.sub (emptyEndsReal σ τ).Uᶜ)) :=
    ⟨fun x => isEmptyElim x.1⟩
  haveI : T2Space b.W := hWT2
  refine mkCharPairBorRealizedTethered wadmP hWT2 (emptyEndsReal σ τ)
    (taylorLegVanishes_emptySource (TopCat.of σ.surf.M) (TopCat.of τ.surf.M) σ.basis τ.basis
      (TopCat.of τ.surf.M) (ContinuousMap.id _) Topology.IsClosedEmbedding.id 0
      (LinearEquiv.ofSubsingleton _ _) σ.q τ.q
      (fun v _ => by rw [Subsingleton.elim v 0]; exact τ.q.q_zero))
    (jointLagrangian_emptySource (TopCat.of σ.surf.M) (TopCat.of τ.surf.M) σ.basis τ.basis
      (TopCat.of τ.surf.M) (ContinuousMap.id _) Topology.IsClosedEmbedding.id 0
      (LinearEquiv.ofSubsingleton _ _) σ.q τ.q
      (fun v _ => by rw [Subsingleton.elim v 0]; exact Submodule.zero_mem _))
    ⟨fun x => isEmptyElim x, continuous_of_isEmpty _⟩
    ((continuous_of_isEmpty _).isClosedEmbedding (fun x => isEmptyElim x))
    (fun x => isEmptyElim x) (fun x => isEmptyElim x)
    (ChartedSpace.empty MembraneModel (↑(emptyEndsReal σ τ).Q))

/-! ## §3. THE REDUCTION — the empty-membrane collapse reduces `hBbord` to the coboundary `WAdmPinned`. -/

/-- **The empty-membrane spin-carrier bordism witness from a coboundary `WAdmPinned`.** For any
spin-carrier element `p` (Σ = ∅ by construction) and any coboundary bordism `b : p.1 ↝ ∅` with a
Hausdorff carrier and a substrate-pinned Lefschetz–Wu `w₂ = 0` datum `WAdmPinned b`, the tethered
characteristic-pair bordism witness assembles (its membrane realization, Taylor leg, Lagrangian and
tether all collapse via the #171 empty-source machinery), so `p` is `spinEmptyData`-bordant to the
empty manifold. This discharges every non-`WAdmPinned` obligation of the `hBbord` atom. -/
theorem isDataBordant_empty_of_wadm (prov : CharPairWProviderPerOp (𝓡 4) 0)
    (p : StrMfd (spinEmptyData prov))
    (b : Bordism ((𝓡 4).prod (𝓡∂ 1)) p.1 (emptySM (X := PUnit) (k := 0) (I := 𝓡 4)))
    (hWT2 : T2Space b.W) (wadmP : WAdmPinned b) :
    IsDataBordant (spinEmptyData prov) p ⟨emptySM, (spinEmptyData prov).emptyStr⟩ := by
  refine ⟨b, ⟨⟨?_, hWT2⟩⟩⟩
  haveI hps : IsEmpty p.2.1.surf.M := p.2.2
  haveI : IsEmpty (Fin p.2.1.n) := isEmpty_fin_n_of_isEmpty_surf _
  haveI hτs : IsEmpty ((⟨emptySM, (spinEmptyData prov).emptyStr⟩ :
      StrMfd (spinEmptyData prov)).2.1).surf.M := inferInstanceAs (IsEmpty PEmpty)
  haveI : IsEmpty (Fin ((⟨emptySM, (spinEmptyData prov).emptyStr⟩ :
      StrMfd (spinEmptyData prov)).2.1).n) := isEmpty_fin_n_of_isEmpty_surf _
  exact charPairBorTethered_empty _ _ b hWT2 wadmP

/-- **The TWO-END spin-carrier bordism witness from a `WAdmPinned` bordism (the R0 adapter,
2026-07-20 row-side dossier).** The general-`q` form of `isDataBordant_empty_of_wadm`: for ANY two
spin-carrier elements `p q` (both Σ = ∅ by construction) and any bordism `b : p.1 ↝ q.1` with a
Hausdorff carrier and a substrate-pinned Lefschetz–Wu datum `WAdmPinned b`, the tethered witness
assembles by the same #171 empty-source collapse (`charPairBorTethered_empty` is already two-end
generic). This is the reusable current-carrier adapter the `hCob`/`hBase` geometric bricks consume:
a handle-trade trace to `S²×S² ⊔ p'` (A2) or a rank-zero coboundary (A3) needs only the raw
bordism + `T2` + `WAdmPinned` — every membrane/tether obligation is discharged here. -/
theorem isDataBordant_of_wadm (prov : CharPairWProviderPerOp (𝓡 4) 0)
    (p q : StrMfd (spinEmptyData prov))
    (b : Bordism ((𝓡 4).prod (𝓡∂ 1)) p.1 q.1)
    (hWT2 : T2Space b.W) (wadmP : WAdmPinned b) :
    IsDataBordant (spinEmptyData prov) p q := by
  refine ⟨b, ⟨⟨?_, hWT2⟩⟩⟩
  haveI hps : IsEmpty p.2.1.surf.M := p.2.2
  haveI : IsEmpty (Fin p.2.1.n) := isEmpty_fin_n_of_isEmpty_surf _
  haveI hqs : IsEmpty q.2.1.surf.M := q.2.2
  haveI : IsEmpty (Fin q.2.1.n) := isEmpty_fin_n_of_isEmpty_surf _
  exact charPairBorTethered_empty _ _ b hWT2 wadmP

/-! ## §4. The named finest-grain atom — the coboundary Lefschetz–Wu `w₂ = 0` tower. -/

/-- **The `S²×S²` bounding-bordism atom, at its finest manifold-surgery grain.** For the distinguished
slot `p` (in the final row, the concrete stock `S²×S²`), the SOLE geometric content that `hBbord` bottoms
out at: a coboundary bordism `b : p.1 ↝ ∅` (`W = S²×D³`) whose carrier is Hausdorff and which carries a
substrate-pinned Lefschetz–Wu `w₂(W) = 0` tower (`WAdmPinned b` — the rel-Poincaré–Lefschetz duality +
Steenrod squares on the 5-manifold-with-boundary). This is EXACTLY the deep input the op-provider does
not supply and current Mathlib lacks the manifold cohomology to build; everything else in `hBbord`
(the empty-membrane realization, the tether, the T2, the quotient) is discharged by
`isDataBordant_empty_of_wadm`. -/
def SphereProdCoboundaryWAdm (prov : CharPairWProviderPerOp (𝓡 4) 0)
    (p : StrMfd (spinEmptyData prov)) : Prop :=
  ∃ b : Bordism ((𝓡 4).prod (𝓡∂ 1)) p.1 (emptySM (X := PUnit) (k := 0) (I := 𝓡 4)),
    T2Space b.W ∧ Nonempty (WAdmPinned b)

/-- **`hBbord` from the coboundary atom** — the honest reduction: the `S²×S²` bounding-bordism geometric
witness (`hBbord`) follows from the single named atom `SphereProdCoboundaryWAdm` via the empty-membrane
collapse of `isDataBordant_empty_of_wadm`. -/
theorem hBbord_of_coboundary (prov : CharPairWProviderPerOp (𝓡 4) 0)
    (p : StrMfd (spinEmptyData prov)) (h : SphereProdCoboundaryWAdm prov p) :
    IsDataBordant (spinEmptyData prov) p ⟨emptySM, (spinEmptyData prov).emptyStr⟩ := by
  obtain ⟨b, hWT2, hwadm⟩ := h
  obtain ⟨wadmP⟩ := hwadm
  exact isDataBordant_empty_of_wadm prov p b hWT2 wadmP

/-! ## §5. The conditional wiring — the finest-grain assembly with `hBbord` at the coboundary atom. -/

/-- **THE COBOUNDARY-ATOM WIRING** (`kt_equiv_zmod16_of_residuals_freezeAtoms_ofCoboundary`) — the finest-
grain assembly `kt_equiv_zmod16_of_residuals_freezeAtoms`, with the Freeze-B geometric hypothesis
`hBbord` REPLACED by the strictly-smaller coboundary Lefschetz–Wu atom `SphereProdCoboundaryWAdm` at the
distinguished slot `row.R.s2s2`. Every OTHER consumer shape (`H`, `row`, the Freeze-A atoms `hCob`/`hBase`,
`hcolD`, `hker`, `hΦg`) is fixed. Pure wiring: `hBbord_of_coboundary` recovers `hBbord` from the atom, then
the finest-grain assembly fires. This is the honest form of "`hBbord` deleted-for-the-stock-row": the whole
`S²×S² = ∂(S²×D³)` bordism content is discharged EXCEPT the coboundary `w₂ = 0` tower. -/
theorem kt_equiv_zmod16_of_residuals_freezeAtoms_ofCoboundary
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (row : SpinPresentationRow residualProv)
    (hCob : row.R.HandleTradeCobordism) (hBase : row.R.HyperbolicBase)
    (hBco : SphereProdCoboundaryWAdm residualProv row.R.s2s2)
    (hcolD : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        IsSpinSectorStr residualProv p → RankZeroCollapseDatum residualProv p)
    (hker : KerPhiSubDoubles residualProv)
    (hΦg : spinForgetPhi residualProv
        (DataBordismGrp.mk (spinEmptyData residualProv) row.g) = ktKernelRep residualProv) :
    Nonempty (T2DataBordismGrp (pinPlusCharPairData residualProv) ≃+ ZMod 16) :=
  kt_equiv_zmod16_of_residuals_freezeAtoms H row hCob hBase
    (hBbord_of_coboundary residualProv row.R.s2s2 hBco) hcolD hker hΦg

/-- **The Rokhlin-16 twin of the coboundary-atom wiring** (`rokhlin_sixteen_of_residuals_freezeAtoms_ofCoboundary`):
`Nat.card Ω₄^{Pin⁺} = 16` from the row with Freeze B at the coboundary Lefschetz–Wu atom. Pure transport
across the additive equivalence; introduces no new residual atom. -/
theorem rokhlin_sixteen_of_residuals_freezeAtoms_ofCoboundary
    (H : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        charPairBrown residualProv (T2DataBordismGrp.mk (pinPlusCharPairData residualProv) p) = 0 →
        0 < p.2.n → KRSResidualRow residualProv p)
    (row : SpinPresentationRow residualProv)
    (hCob : row.R.HandleTradeCobordism) (hBase : row.R.HyperbolicBase)
    (hBco : SphereProdCoboundaryWAdm residualProv row.R.s2s2)
    (hcolD : ∀ p : StrMfd (pinPlusCharPairData residualProv).toTangentialData,
        IsSpinSectorStr residualProv p → RankZeroCollapseDatum residualProv p)
    (hker : KerPhiSubDoubles residualProv)
    (hΦg : spinForgetPhi residualProv
        (DataBordismGrp.mk (spinEmptyData residualProv) row.g) = ktKernelRep residualProv) :
    Nat.card (T2DataBordismGrp (pinPlusCharPairData residualProv)) = 16 :=
  rokhlin_sixteen_of_residuals_freezeAtoms H row hCob hBase
    (hBbord_of_coboundary residualProv row.R.s2s2 hBco) hcolD hker hΦg

end SKEFTHawking.PinPlusKTSphereProdBordism
