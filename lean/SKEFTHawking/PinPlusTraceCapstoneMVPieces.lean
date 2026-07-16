/-
# Phase 5q.H close-out — INHABITING THE CAPSTONE COHOMOLOGY MV DATUM: the piece-transfer row
# (the intended-target finiteness stock + the generic four-piece homeo row)

`CapstoneCohomologyMVDatum` (`PinPlusTraceCapstoneCohomologyMV.lean`) carries the two-piece MV
cover `W = A ∪ B` and FOUR all-degree homology finiteness facts (`hA`/`hB`/`hAB`/`hBd`). This
module reduces those four numeric obligations to GEOMETRY — four homeomorphisms of the constructed
pieces onto standard finite-homology comparison spaces — by banking:

**§1 The intended-target stock** (all-degree, hypothesis-minimal):
* `finiteDimensional_homology_of_closed_all` — a closed charted 4-manifold has finite mod-2
  homology in EVERY degree (`H₀` joined covers; `H₁–H₃` the PD windows; `H₄` the component-wise
  point restriction, connectedness-free; `H_{>4}` the `goodCompact` vanishing; the empty carrier
  degenerately). The cyl-side base + the boundary-ends stock.
* `finiteDimensional_homology_cyl_all` — the cylinder `M × I` has all-degree finite homology
  (the product-with-contractible transfer over the interval contraction + the joined-cover export).
  The `A ≃ (ktHandleAttachment …).B` piece's stock.
* `finiteDimensional_homology_D5_all` — the closed disk `D⁵` has all-degree finite homology
  (convex all-degree). The `B ≃ Ha = D⁵` piece's stock.
* `finiteDimensional_homology_of_two_closed_ends` — a carrier clopen-split into two pieces each
  homeomorphic to a closed charted 4-manifold has all-degree finite homology. The
  `∂W = M ⊔ M′` brick.

**§2 The piece-transfer row** `CapstoneMVTransferRow`: the cover `A`/`B`/`hcov` plus four
`(Y, e, hY)` comparison triples — a comparison space, a homeomorphism of the constructed piece
onto it, and its all-degree finiteness. `toMVDatum` discharges the whole
`CapstoneCohomologyMVDatum` from the row via the homeomorphism transfer. So the four capstone
cohomology finiteness atoms become: *name four comparison homeos* — every numeric field falls.

**§3 The pinned constructor** `CapstoneMVTransferRow.ofPieces`: the intended instantiation —
`YA := (ktHandleAttachment …).B` (the cylinder, stock §1), `YB := D⁵` (stock §1), the overlap
triple and the boundary homeo left as the named geometric residual (the seam's finiteness is a
genuine input: `S ⊆ D⁵` is an arbitrary closed attaching region until the concrete surgery pins
it). Inputs are spelled over `ktHandleAttachment` (the construction the piece homeos come from),
conclusions over `capstoneB` — the binding-lane discipline.

**Fences.** THE COLLAR FORK is respected: the cover pieces are DATA (the constructed
handle-attachment's own two-piece structure, thickened by the instantiator), never a general
collar theorem. The sealed heavy carrier term appears only in field/binder TYPES, never
re-elaborated inside a constructed term.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new project axiom, no
`native_decide`, no `maxHeartbeats`.
-/
import Mathlib
import SKEFTHawking.SingularHomologyFiniteAll
import SKEFTHawking.SingularClosedHomologyFinite
import SKEFTHawking.PinPlusCylDataDischargeDisconnectedComponents
import SKEFTHawking.PinPlusTraceCapstoneCohomologyMV

open scoped Manifold
open SKEFTHawking.BordismTheory
open SKEFTHawking.SurgeryFoundation
open SKEFTHawking.SurgeryFoundation.HandleAttachment
open SKEFTHawking.DiskChartGeneric (D5)
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularHomologyFiniteAll
open SKEFTHawking.SingularHomologyFiniteTransfer
open SKEFTHawking.SingularClosedHomologyFinite
open SKEFTHawking.SingularH0Finite
open SKEFTHawking.SingularFundamentalClass
open SKEFTHawking.PinPlusCylDataDischargeDisconnectedComponents
open SKEFTHawking.PinPlusTraceCapstoneInhabit
open SKEFTHawking.PinPlusTraceCapstoneCohomologyMV

namespace SKEFTHawking.PinPlusTraceCapstoneMVPieces

noncomputable section

/-! ## §1. The intended-target all-degree finiteness stock. -/

/-- **A closed charted 4-manifold has finite mod-2 homology in every degree** — `H₀` by the
joined-cover argument, `H₁–H₃` by the fundamental-duality windows, `H₄` by the component-wise
point restriction (connectedness-free), `H_{>4}` by the `goodCompact` above-dimension vanishing;
the empty carrier degenerately. No `Nonempty`/`PreconnectedSpace` hypotheses. -/
theorem finiteDimensional_homology_of_closed_all {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M] (n : ℕ) :
    FiniteDimensional (ZMod 2) (Homology (TopCat.of M) n) := by
  rcases isEmpty_or_nonempty M with hM | hM
  · haveI : IsEmpty ↑(TopCat.of M) := hM
    exact finiteDimensional_homology_of_isEmpty n
  · haveI := hM
    match n with
    | 0 => exact finiteDimensional_h0
    | 1 => exact (finiteDimensional_homology_of_closed (M := M)).1
    | 2 => exact (finiteDimensional_homology_of_closed (M := M)).2.1
    | 3 => exact (finiteDimensional_homology_of_closed (M := M)).2.2.1
    | 4 => exact topHomology_finite M
    | (n + 5) =>
      haveI : Subsingleton (Homology (TopCat.of M) (n + 5)) :=
        ⟨fun a b => (homology_vanish_above (m := 2) (n + 5) (by omega) a).trans
          (homology_vanish_above (m := 2) (n + 5) (by omega) b).symm⟩
      exact finiteDimensional_of_subsingleton

/-- **The cylinder `M × I` over a closed charted 4-manifold has finite mod-2 homology in every
degree** — degree `0` from the finite joined-cover export (product paths through the interval
contraction), degrees `≥ 1` from the product-with-contractible homotopy transfer onto
`finiteDimensional_homology_of_closed_all`. -/
theorem finiteDimensional_homology_cyl_all {M : Type} [TopologicalSpace M] [T2Space M]
    [CompactSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M] (n : ℕ) :
    FiniteDimensional (ZMod 2) (Homology (TopCat.of (M × Set.Icc (0 : ℝ) 1)) n) := by
  classical
  cases n with
  | zero =>
    obtain ⟨t, hcov⟩ := exists_finite_joinedCover (M := M)
    exact finiteDimensional_h0_prodContractible (TopCat.of M) (TopCat.of unitInterval) 0
      iccContraction slice_iccContraction_zero slice_iccContraction_one t
      (fun p => (p : ↑(TopCat.of M))) hcov
  | succ n =>
    exact finiteDimensional_homology_prodContractible_succ (TopCat.of M)
      (TopCat.of unitInterval) 0 iccContraction slice_iccContraction_zero
      slice_iccContraction_one n (finiteDimensional_homology_of_closed_all (n + 1))

/-- **The closed disk `D⁵` has finite mod-2 homology in every degree** — the convex all-degree
brick at the closed unit ball of `E⁵`. -/
theorem finiteDimensional_homology_D5_all (k : ℕ) :
    FiniteDimensional (ZMod 2) (Homology (TopCat.of D5) k) :=
  finiteDimensional_homology_convexSub_all (n := 4 + 1)
    (convex_closedBall (0 : EuclideanSpace ℝ (Fin (4 + 1))) 1)
    (Metric.mem_closedBall_self zero_le_one) k

/-- **A carrier clopen-split into two closed-4-manifold ends has finite mod-2 homology in every
degree** — the `∂W = M ⊔ M′` brick: transfer each end's `closed_all` stock across its comparison
homeomorphism, then fire the clopen split. -/
theorem finiteDimensional_homology_of_two_closed_ends {X : TopCat} {U : Set ↑X}
    (hU : IsClopen U)
    {M₁ : Type} [TopologicalSpace M₁] [T2Space M₁] [CompactSpace M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M₁]
    {M₂ : Type} [TopologicalSpace M₂] [T2Space M₂] [CompactSpace M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M₂]
    (e₁ : ↑(sub U) ≃ₜ M₁) (e₂ : ↑(sub Uᶜ) ≃ₜ M₂) (n : ℕ) :
    FiniteDimensional (ZMod 2) (Homology X n) :=
  finiteDimensional_homology_of_clopen_split hU
    (fun k => finiteDimensional_homology_of_homeomorph
      (Y := TopCat.of M₁) e₁ k (finiteDimensional_homology_of_closed_all k))
    (fun k => finiteDimensional_homology_of_homeomorph
      (Y := TopCat.of M₂) e₂ k (finiteDimensional_homology_of_closed_all k))
    n

variable (s t : SingularManifold.{0} PUnit.{1} (0 : WithTop ℕ∞) (𝓡 4)) [T2Space s.M]
  (S : Set D5) (hS : IsClosed S) (φ : ↥S → s.M × Set.Icc (0 : ℝ) 1)
  (hφ : Continuous φ) (hφinj : Function.Injective φ)
  (cd : SeamCollarDatum (ktHandleAttachment s.M D5 S hS φ hφ hφinj).carrier)
  (hseam : (ktHandleAttachment s.M D5 S hS φ hφ hφinj).seamRegion ⊆ cd.seamNbhd)
  (d : SurgeredEndDatum s t S hS φ hφ hφinj cd hseam)

/-! ## §2. The piece-transfer row: four comparison homeos discharge the four numeric atoms. -/

/-- **The capstone MV piece-transfer row** — the two-piece cover `A`/`B`/`hcov` plus four
comparison triples `(Y, e, hY)`: a comparison space, a homeomorphism of the constructed piece
onto it, and its all-degree mod-2 homology finiteness. The four numeric obligations of
`CapstoneCohomologyMVDatum` reduce to the four GEOMETRIC homeomorphism fields; the finiteness
fields for the intended targets (`M × I`, `D⁵`, two closed ends) are §1 stock. -/
structure CapstoneMVTransferRow where
  /-- the cyl-side piece of the MV cover (intended: `range fromCyl`, thickened). -/
  A : Set ↑(TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
  /-- the handle-side piece of the MV cover (intended: `range fromHandle`, thickened). -/
  B : Set ↑(TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
  /-- the interiors of `A`, `B` cover `W`. -/
  hcov : (⋃ U ∈ ({A, B} : Set (Set ↑(TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W))),
      interior U) = Set.univ
  /-- the cyl-side comparison space (intended: the cylinder `(ktHandleAttachment …).B`). -/
  YA : TopCat
  /-- the cyl-side comparison homeomorphism. -/
  eA : ↑(sub A) ≃ₜ ↑YA
  /-- the cyl-side comparison finiteness (intended: `finiteDimensional_homology_cyl_all`). -/
  hYA : ∀ n, FiniteDimensional (ZMod 2) (Homology YA n)
  /-- the handle-side comparison space (intended: `D⁵`). -/
  YB : TopCat
  /-- the handle-side comparison homeomorphism. -/
  eB : ↑(sub B) ≃ₜ ↑YB
  /-- the handle-side comparison finiteness (intended: `finiteDimensional_homology_D5_all`). -/
  hYB : ∀ n, FiniteDimensional (ZMod 2) (Homology YB n)
  /-- the overlap comparison space (intended: the seam `S_att × collar`). -/
  YAB : TopCat
  /-- the overlap comparison homeomorphism. -/
  eAB : ↑(sub (A ∩ B)) ≃ₜ ↑YAB
  /-- the overlap comparison finiteness (a genuine geometric input until the concrete surgery
  pins the attaching region). -/
  hYAB : ∀ n, FiniteDimensional (ZMod 2) (Homology YAB n)
  /-- the boundary comparison space (intended: the two closed ends `M ⊔ M′`). -/
  YBd : TopCat
  /-- the boundary comparison homeomorphism. -/
  eBd : ↑(sub (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)) ≃ₜ ↑YBd
  /-- the boundary comparison finiteness (intended:
  `finiteDimensional_homology_of_two_closed_ends`). -/
  hYBd : ∀ n, FiniteDimensional (ZMod 2) (Homology YBd n)

/-- **The transfer row inhabits the capstone cohomology MV datum** — each numeric field falls to
the homeomorphism transfer from its comparison triple. -/
def CapstoneMVTransferRow.toMVDatum
    (R : CapstoneMVTransferRow s t S hS φ hφ hφinj cd hseam d) :
    CapstoneCohomologyMVDatum s t S hS φ hφ hφinj cd hseam d where
  A := R.A
  B := R.B
  hcov := R.hcov
  hA := fun n => finiteDimensional_homology_of_homeomorph R.eA n (R.hYA n)
  hB := fun n => finiteDimensional_homology_of_homeomorph R.eB n (R.hYB n)
  hAB := fun n => finiteDimensional_homology_of_homeomorph R.eAB n (R.hYAB n)
  hBd := fun n => finiteDimensional_homology_of_homeomorph R.eBd n (R.hYBd n)

/-! ## §3. The pinned constructor: cyl/disk targets pinned, their stock auto-discharged. -/

/-- **The intended instantiation of the transfer row** — the cyl-side comparison target pinned to
the construction's own cylinder `(ktHandleAttachment …).B = s.M × I` and the handle side to
`Ha = D⁵`, with their all-degree finiteness auto-discharged from §1 stock; the boundary pinned to
a two-closed-ends split. What remains geometric: the cover `A`/`B`/`hcov`, the three piece homeos
`eA`/`eB`/`eAB`, the boundary clopen split data, and the overlap comparison triple. -/
def CapstoneMVTransferRow.ofPieces
    (A B : Set ↑(TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W))
    (hcov : (⋃ U ∈ ({A, B} : Set (Set ↑(TopCat.of
        (capstoneB s t S hS φ hφ hφinj cd hseam d).W))), interior U) = Set.univ)
    (eA : ↑(sub A) ≃ₜ (ktHandleAttachment s.M D5 S hS φ hφ hφinj).B)
    (eB : ↑(sub B) ≃ₜ (ktHandleAttachment s.M D5 S hS φ hφ hφinj).Ha)
    (YAB : TopCat) (eAB : ↑(sub (A ∩ B)) ≃ₜ ↑YAB)
    (hYAB : ∀ n, FiniteDimensional (ZMod 2) (Homology YAB n))
    (YBd : TopCat)
    (eBd : ↑(sub (X := TopCat.of (capstoneB s t S hS φ hφ hφinj cd hseam d).W)
      (((𝓡 4).prod (𝓡∂ 1)).boundary (capstoneB s t S hS φ hφ hφinj cd hseam d).W)) ≃ₜ ↑YBd)
    (U : Set ↑YBd) (hU : IsClopen U)
    {M₁ : Type} [TopologicalSpace M₁] [T2Space M₁] [CompactSpace M₁]
    [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M₁]
    {M₂ : Type} [TopologicalSpace M₂] [T2Space M₂] [CompactSpace M₂]
    [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M₂]
    (e₁ : ↑(sub U) ≃ₜ M₁) (e₂ : ↑(sub Uᶜ) ≃ₜ M₂) :
    CapstoneMVTransferRow s t S hS φ hφ hφinj cd hseam d where
  A := A
  B := B
  hcov := hcov
  YA := TopCat.of (s.M × Set.Icc (0 : ℝ) 1)
  eA := eA
  hYA := fun n => by
    haveI : ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) s.M :=
      inferInstanceAs (ChartedSpace (EuclideanSpace ℝ (Fin 4)) s.M)
    exact finiteDimensional_homology_cyl_all n
  YB := TopCat.of D5
  eB := eB
  hYB := finiteDimensional_homology_D5_all
  YAB := YAB
  eAB := eAB
  hYAB := hYAB
  YBd := YBd
  eBd := eBd
  hYBd := finiteDimensional_homology_of_two_closed_ends hU e₁ e₂

end

end SKEFTHawking.PinPlusTraceCapstoneMVPieces
