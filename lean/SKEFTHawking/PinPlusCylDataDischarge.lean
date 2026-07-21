import Mathlib
import SKEFTHawking.SingularClosedHomologyFinite
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderCapNorm
import SKEFTHawking.PinPlusCharPairWProviderTransport
import SKEFTHawking.PinPlusKTLeafGate

/-!
# Phase 5q.H — THE `cylData` DISCHARGE (M-finiteness + basePD discharged; the sharp per-M Wu leaf)

Track-2's terminal engine `CylinderWAdmPinned.ofClosedPDSuspIntertwineNorm` consumes, on the base `M`,
the row `{findimM1, findimM2, hM2, hM3, hM4, basePD, hwu}`. This module discharges the six
finiteness/duality inputs FROM the closed-manifold stock and isolates the ONE genuine residual, `hwu`.

## The six discharged inputs (`SingularClosedHomologyFinite` + `SingularPD4Instances`)

* `findimM1/findimM2` = `finiteDimensional_cohomology_of_closed` (5q.G, degrees 1,2);
* `hM2/hM3` = `finiteDimensional_homology_of_closed` (the `P₄`-window transport of the cohomology
  findims onto the homology side);
* `hM4` = `finiteDimensional_topHomology_of_closed_connected` (the single-point-restriction injectivity
  into local homology `≅ ℤ/2`, connected `M`);
* `basePD` (`finrank H₁ = finrank H₃`) = the homology-side Poincaré duality of
  `finiteDimensional_homology_of_closed` (the window transports `dimeq_of_closed`).

## The one residual (`CylinderWuResidual`): the cylinder Wu obstruction

After the six are discharged, the ONLY remaining input is the cylinder Wu obstruction
`wuW2 (cylinderP14 …) (cylinderP23 …) = 0` — honestly `w₂(M × I) = 0` in the cylinder's relative-pairing
form. Connecting it to `M`'s own `w₂ = 0` (the bundle certificate `σ.cert`,
`wuW2 (poincareDual4Mid_of_closed M) (poincareDual4Lo_of_closed M) = 0`) is the **Steenrod-square
SUSPENSION naturality** `Sq ∘ susp = susp ∘ Sq` (`Hᵏ(W,∂W) ≅ Hᵏ⁻¹(M)`), the sharp missing brick named
(not faked) by `…CylinderWAdmPinnedTriage`: `SingularRelativeSteenrodSq2` provides only the
pair-restriction naturality `relToAbs_relSq2`, NOT the product/suspension naturality. This module
packages that residual as the per-M leaf `CylinderWuResidual` (the nondeg legs are `Prop`-quantified —
proof-irrelevant, so the leaf unifies against the engine's internally-built intertwine data).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/

open scoped Manifold
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.PoincareLefschetzWu5
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderWu
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspension
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalAlphaU
open SKEFTHawking.PinPlusWAdmPinned
open SKEFTHawking.PinPlusCylinderWAdmPinned
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCapNorm
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.PinPlusCharPairWProviderTransport
open SKEFTHawking.SingularClosedHomologyFinite
open SKEFTHawking.SingularPD4Instances

namespace SKEFTHawking.PinPlusCylDataDischarge

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {k : WithTop ℕ∞}
variable {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]

/-! ## §1. The sharp per-M cylinder-Wu residual. -/

variable (M : Type) [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M] [PreconnectedSpace M] [T1Space (cylW M)]

/-- **The sharp per-M cylinder Wu residual** — the ONLY input to Track-2's terminal engine that is
NOT discharged from the closed-manifold stock. Its honest content is `w₂(M × I) = 0` in the cylinder's
relative-pairing form; the missing brick that would derive it from `M`'s own `w₂ = 0` (`σ.cert`) is the
Steenrod-square suspension naturality (`…Triage`). The two non-degeneracy legs are `Prop`-quantified so
the leaf unifies (proof-irrelevantly) against the intertwine data the engine builds internally. -/
def CylinderWuResidual : Prop :=
  ∀ (nd14 : Function.Injective
      ⇑((relCupH14 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂
        (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu))
    (nd23 : Function.Injective
      ⇑((relCupH23 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M))).compr₂
        (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu)),
    wuW2
      (cylinderP14 (hasRelFundClass_cylGen (m' := 2) (M := M))
        (cylinder_findimAbs14 (finiteDimensional_cohomology_of_closed (M := M)).1)
        (cylinder_findimRel14 (cylinder_findimRelHom14_of_base
          (finiteDimensional_topHomology_of_closed_connected (M := M))
          (finiteDimensional_homology_of_closed (M := M)).2.2.1))
        nd14
        (cylinder_dimeq14_of_basePD (finiteDimensional_homology_of_closed (M := M)).2.2.1
          (finiteDimensional_homology_of_closed (M := M)).2.2.2))
      (cylinderP23 (hasRelFundClass_cylGen (m' := 2) (M := M))
        (cylinder_findimAbs23 (finiteDimensional_cohomology_of_closed (M := M)).2.1)
        (cylinder_findimRel23 (cylinder_findimRelHom23_of_base
          (finiteDimensional_homology_of_closed (M := M)).2.2.1
          (finiteDimensional_homology_of_closed (M := M)).2.1))
        nd23
        (cylinder_dimeq23_holds (finiteDimensional_homology_of_closed (M := M)).2.1)) = 0

/-! ## §2. The nonempty-connected assembler — M-finiteness and basePD discharged. -/

/-- **THE DISCHARGE**: for a closed CONNECTED charted 4-manifold `M`, `CylinderWAdmPinned M` follows
from the single sharp residual `CylinderWuResidual M` — every finiteness/duality input of the terminal
engine is discharged from the closed-manifold stock (`SingularClosedHomologyFinite` +
`finiteDimensional_cohomology_of_closed`). The residual's nondeg legs unify against the engine's
internal intertwine data (proof-irrelevance). -/
def cylinderWAdmPinned_of_wuResidual (hRes : CylinderWuResidual M) : CylinderWAdmPinned M :=
  CylinderWAdmPinned.ofClosedPDSuspIntertwineNorm
    (finiteDimensional_cohomology_of_closed (M := M)).1
    (finiteDimensional_cohomology_of_closed (M := M)).2.1
    (finiteDimensional_homology_of_closed (M := M)).2.1
    (finiteDimensional_homology_of_closed (M := M)).2.2.1
    (finiteDimensional_topHomology_of_closed_connected (M := M))
    (finiteDimensional_homology_of_closed (M := M)).2.2.2
    (hRes _ _)

/-! ## §3. The bundled `CylWAdmData` for a nonempty-connected carrier. -/

/-- **`CylWAdmData s` for a nonempty CONNECTED bundled carrier, from the sharp Wu leaf.** The `T2Space`
instance is supplied by the bundle's `σ.t2` at the call site; the ambient `CompactSpace`/`ChartedSpace`
are `SingularManifold` instances. Everything except the Wu leaf is discharged from stock
(`cylinderWAdmPinned_of_wuResidual`), then bridged to the concrete residual bundle by
`CylinderWAdmPinned.toCylWAdmData`. -/
def cylWAdmData_of_wuResidual {s : SingularManifold.{0} PUnit.{1} k I}
    [T2Space s.M] [Nonempty s.M] [PreconnectedSpace s.M] [T1Space (cylW s.M)]
    (hRes : CylinderWuResidual s.M) : CylWAdmData s :=
  CylinderWAdmPinned.toCylWAdmData (cylinderWAdmPinned_of_wuResidual s.M hRes)

/-! ## §4. The EMPTY case discharged — the degenerate datum on the empty cylinder. -/

section Empty

open SKEFTHawking.PinPlusCharPairSurfaceTie
open SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeBockstein SKEFTHawking.SingularRelativeSteenrodSq2

/-- Relative cohomology of an `IsEmpty` carrier is subsingleton (the relative cochains are a submodule
of the trivial singular cochains). -/
instance subsingleton_relativeCohomology_of_isEmpty {M : Type} [TopologicalSpace M] [IsEmpty M]
    (S : Set ↑(TopCat.of M)) (n : ℕ) : Subsingleton (RelativeCohomology S n) := by
  haveI := isEmpty_simplex (M := M) n
  haveI : Subsingleton (SingularCochain (TopCat.of M) n) := inferInstance
  haveI : Subsingleton (LinearMap.ker (relCoboundaryₗ S n)) := inferInstance
  exact (Submodule.Quotient.mk_surjective _).subsingleton

/-- Relative homology of an `IsEmpty` carrier is subsingleton (the relative chains are a quotient of
the trivial singular chains). -/
instance subsingleton_relativeHomology_of_isEmpty {M : Type} [TopologicalSpace M] [IsEmpty M]
    (S : Set ↑(TopCat.of M)) (n : ℕ) : Subsingleton (RelativeHomology S n) := by
  haveI := isEmpty_simplex (M := M) n
  haveI : Subsingleton (SingularChain (TopCat.of M) n) := inferInstance
  haveI : Subsingleton (RelativeChain S n) := (Submodule.Quotient.mk_surjective _).subsingleton
  haveI : Subsingleton (relCycles S n) := inferInstance
  exact (Submodule.Quotient.mk_surjective _).subsingleton

variable {s : SingularManifold.{0} PUnit.{1} k I} [IsEmpty s.M]

/-- The degenerate relative fundamental-class datum on the EMPTY cylinder: everything vanishes
(`cls = 0`), and the interior local-iso family + restriction obligation are vacuous (no points). -/
def emptyRelFundDatum :
    RelFundClassDatum (X := TopCat.of (cylW s.M)) (m := 3)
      ((cylModel 2).boundary (cylW s.M)) where
  cls := 0
  gen := fun x _ => isEmptyElim x
  restricts := fun _ _ => Subsingleton.elim _ _

/-- The degenerate `(1,4)` Lefschetz–Wu datum on the empty cylinder — all groups subsingleton. -/
def emptyP14 : LefschetzWuDatum (TopCat.of (cylW s.M))
    ((cylModel 2).boundary (cylW s.M)) 1 4 5 where
  mu := (emptyRelFundDatum (s := s)).mu
  cup := relCupH14
  sqOp := relSq1 (n := 3)
  findimAbs := inferInstance
  findimRel := inferInstance
  nondeg := fun a b _ => Subsingleton.elim a b
  dimeq := by rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton]

/-- The degenerate `(2,3)` Lefschetz–Wu datum on the empty cylinder. -/
def emptyP23 : LefschetzWuDatum (TopCat.of (cylW s.M))
    ((cylModel 2).boundary (cylW s.M)) 2 3 5 where
  mu := (emptyRelFundDatum (s := s)).mu
  cup := relCupH23
  sqOp := relSq2
  findimAbs := inferInstance
  findimRel := inferInstance
  nondeg := fun a b _ => Subsingleton.elim a b
  dimeq := by rw [Module.finrank_zero_of_subsingleton, Module.finrank_zero_of_subsingleton]

/-- **The EMPTY-cylinder `CylWAdmData`** — the degenerate residual bundle, all cohomology being
subsingleton: the pins hold (`mu = D.mu`, `cup = relCupH14/23`, `sqOp = relSq1/2` by construction) and
`hwu` is forced (`wuW2 ∈ H²(∅×I)` subsingleton). Discharges the `IsEmpty` branch of `cylData`. -/
def cylWAdmData_empty : CylWAdmData s where
  P14 := emptyP14
  P23 := emptyP23
  pin14 := ⟨⟨emptyRelFundDatum (s := s), rfl⟩, rfl, rfl⟩
  pin23 := ⟨⟨emptyRelFundDatum (s := s), rfl⟩, rfl, rfl⟩
  hwu := Subsingleton.elim _ _

end Empty

/-! ## §5. THE FIRE — the provider inhabits, the G8-1 / G10-1 rider dies.

The full `cylData : ∀ {s}, CharPairStrBundled I s → CylWAdmData s` splits by the carrier's topology:

* **empty** `s.M` — DISCHARGED unconditionally by `cylWAdmData_empty` (all cohomology `Subsingleton`);
* **nonempty CONNECTED** `s.M` — discharged from stock modulo the ONE sharp per-M residual
  `CylinderWuResidual s.M` (the Steenrod-suspension Wu leaf), via `cylWAdmData_of_wuResidual`;
* **nonempty DISCONNECTED** `s.M` — the ONLY residual not covered by the connected fundamental-class
  route (the cylinder's relative fundamental class `hasRelFundClass_cylGen` needs `PreconnectedSpace`);
  the disjoint-union `⊔`-tower (`PoincareLefschetzWuBlock`) closes it — carried as the honest residual
  `hdisc`.

Given the Wu leaf + the disconnected supply, `nonempty_provider_of_cylData` fires: the sole inhabitation
dependency `cylData` is met, so `Nonempty (CharPairWProviderPerOp (𝓡 4) k)` — the G8-1/G10-1 provider
rider dies, and every per-`prov` W-D statement (`ktSurgeryReduces_of_tetherSupply`,
`dualSpinForwardDatum_iff_ktNonSplit`, `kt_equiv_zmod16_of_two_leaves`, …) acquires a live instance. -/
theorem nonempty_provider_of_wuLeaf_and_disconnected
    (hwu : ∀ {s : SingularManifold.{0} PUnit.{1} k I} (_σ : CharPairStrBundled I s)
      [T2Space s.M] [Nonempty s.M] [PreconnectedSpace s.M] [T1Space (cylW s.M)],
      CylinderWuResidual s.M)
    (hdisc : ∀ {s : SingularManifold.{0} PUnit.{1} k I}, CharPairStrBundled I s →
      Nonempty s.M → ¬ PreconnectedSpace s.M → CylWAdmData s) :
    Nonempty (CharPairWProviderPerOp I k) := by
  refine SKEFTHawking.PinPlusKTLeafGate.nonempty_provider_of_cylData (fun {s} σ => ?_)
  by_cases hne : Nonempty s.M
  · by_cases hpc : PreconnectedSpace s.M
    · haveI := hne
      haveI := hpc
      haveI : T2Space s.M := σ.t2
      haveI : T2Space (cylW s.M) := inferInstance
      haveI : T1Space (cylW s.M) := inferInstance
      exact cylWAdmData_of_wuResidual (hwu σ)
    · exact hdisc σ hne hpc
  · haveI : IsEmpty s.M := not_nonempty_iff.mp hne
    exact cylWAdmData_empty

end

end SKEFTHawking.PinPlusCylDataDischarge
