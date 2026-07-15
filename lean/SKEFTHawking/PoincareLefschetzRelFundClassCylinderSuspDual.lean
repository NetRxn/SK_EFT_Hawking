/-
# Phase 5q.H Track 2 — the `β`-PINNED cup-suspension constructor: `hcompat` reduced to a
# single relative-Kronecker cap-cross projection value (`ofCapCross`)

`…CylinderIntertwine` reduced each non-degeneracy leg to the datum `(β, hcompat)` — a FREE suspension
equivalence `β` plus the cup-cross **Fubini** identity `⟨a ∪ b, [W,∂W]⟩ = ⟨α a ∪ β b, [M]⟩`. This
module TIGHTENS that residual by PINNING `β` to the canonical geometric suspension — the Kronecker-dual
`crossHDualEquivOfBij` of the honest homology cross `crossH` (`× [I,∂I]`, `…SingularRelativeCrossProduct`)
built in `…SingularRelativeCrossProductDual`. Two payoffs:

1. **The free `β` field is eliminated** (no "choose any equivalence" gauge freedom): `β` is now the
   Kronecker-dual of the geometric cross, and the sole remaining `β`-input is that `crossH` is an ISO in
   the relevant suspension degree (`hbij` — the geometrically-transparent pair-suspension Künneth input).
   This is the same "no free-`sqOp`/`β` gaming" discipline the `…BaseWu` spin constructor applies.

2. **`hcompat` collapses to a pure relative-Kronecker pairing value.** With `β` pinned, the Fubini RHS
   `fundamentalFunctional (cupH24 (α a) (β b))` rewrites — through the in-tree cap–cup adjunction
   (`fundamentalFunctional_cupH24`/`_cupH13`) and the dual-suspension pairing identity
   (`crossHDualEquivOfBij_pairing`) — to `⟨b, crossH (α a ⌢ [M])⟩` (`§1`, `rhsReduce{23,14}`). So the
   residual per leg is exactly the **cap-cross projection value** `hproj`:

     `⟨a ∪ b, [W,∂W]⟩ = ⟨b, crossH (α a ⌢ [M])⟩`   (`= ⟨(α a) ⌢ [M] "×" [I,∂I]` paired against `b`).

   No `cupH24`/`fundamentalFunctional` wrapping remains on the right: the honest Fubini value is now a
   single relative-Kronecker pairing against the explicit class `crossH (α a ⌢ [M])`. Discharging it is
   the cap-cross projection formula `a ⌢ [W,∂W] = crossH (α a ⌢ [M])` (with `[W,∂W] = crossH [M]`) — a
   named homology identity, the next arc.

`ofCapCross` (`§2`) is the `CylinderSuspIntertwineData` builder consuming `(hbij23, hbij14)` +
`(hproj23, hproj14)`, so downstream constructors (`…CylinderIntertwine.ofClosedPDSuspIntertwine`) accept
the pinned-`β` residual in place of the free `(β, hcompat)` pair.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderIntertwine
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderCross
import SKEFTHawking.SingularRelativeCrossProductDual
import SKEFTHawking.PoincareDualityConstruct
import SKEFTHawking.SingularPD4Instances

open scoped Manifold
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderWu
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCross
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalAlphaU
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderIntertwine
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativePairing
open SKEFTHawking.SingularManifoldFundamentalClass
open SKEFTHawking.SingularFundamentalClass
open SKEFTHawking.PoincareDualityConstruct
open SKEFTHawking.SingularPD4Instances
open SKEFTHawking.SingularCapHomology
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularRelativeCrossProductDual

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspDual

noncomputable section

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]

/-! ## §1. The cylinder-specialized homology cross and its Kronecker-dual `β`

The generic `crossH`/`crossHDualEquivOfBij` live over `SKEFTHawking.SingularRelativeCrossProduct.cyl
(TopCat.of M)`; the consumer spells the same space `TopCat.of (cylW M)`. The two are defeq, but mixing
`(cylModel 2).boundary (cylW M)` — whose *natural* type sits in the consumer spelling — with a
`crossH`-typed class re-triggers an expensive TopCat-instance `isDefEq`. `cylBd` PINS the subspace to
the `cyl (TopCat.of M)` spelling once, so every reduction lemma below carries a single, consistent
spelling and no reconciliation cost; the `cyl ↔ cylW` bridge to the consumer is a named residual. -/

/-- **The cylinder boundary `∂W`**, pinned to the `cyl (TopCat.of M)` spelling `crossH` uses. -/
def cylBd : Set ↑(cyl (TopCat.of M)) := (cylModel 2).boundary (cylW M)

/-- **The cylinder homology cross** `× [I,∂I] : Hₚ₊₁(M) → Hₚ₊₂(W, ∂W)` at degree `p`. -/
def cylCrossH (p : ℕ) :
    Homology (TopCat.of M) (p + 1) →ₗ[ZMod 2] RelativeHomology (cylBd (M := M)) (p + 1 + 1) :=
  crossH (M := TopCat.of M) (S := cylBd (M := M))
    (slice_one_mapsTo (M := M) (m' := 2)) (slice_zero_mapsTo (M := M) (m' := 2)) p

/-- **The cylinder suspension `β`** `Hₚ₊₂(W,∂W) ≃ Hₚ₊₁(M)`, the Kronecker-dual of `cylCrossH`, from the
pair-suspension iso witness `hbij` (`cylCrossH` bijective). -/
def cylBeta (p : ℕ) (hbij : Function.Bijective (cylCrossH (M := M) p)) :
    RelativeCohomology (cylBd (M := M)) (p + 1 + 1) ≃ₗ[ZMod 2] Cohomology (TopCat.of M) (p + 1) :=
  crossHDualEquivOfBij (M := TopCat.of M) (S := cylBd (M := M))
    (slice_one_mapsTo (M := M) (m' := 2)) (slice_zero_mapsTo (M := M) (m' := 2)) p hbij

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- **The pairing identity for the cylinder suspension** `⟨β b, x⟩_M = ⟨b, cylCrossH x⟩_{(W,∂W)}`. -/
theorem cylBeta_pairing (p : ℕ) (hbij : Function.Bijective (cylCrossH (M := M) p))
    (b : RelativeCohomology (cylBd (M := M)) (p + 1 + 1)) (x : Homology (TopCat.of M) (p + 1)) :
    kroneckerH (X := TopCat.of M) (p + 1) (cylBeta p hbij b) x
      = relKroneckerH (cylBd (M := M)) b (cylCrossH (M := M) p x) :=
  crossHDualEquivOfBij_pairing (M := TopCat.of M) (S := cylBd (M := M))
    (slice_one_mapsTo (M := M) (m' := 2)) (slice_zero_mapsTo (M := M) (m' := 2)) p hbij b x

/-! ## §2. The Fubini-RHS reduction: `⟨α a ∪ β b, [M]⟩ = ⟨b, cylCrossH (α a ⌢ [M])⟩` with `β` pinned -/

/-- **The `(2,3)` Fubini-RHS reduction.** With `β = cylBeta` (the Kronecker-dual of `cylCrossH` at
`p = 1`), the Poincaré-duality RHS `⟨u ∪ β b, [M]⟩` collapses to `⟨b, cylCrossH (u ⌢ [M])⟩`: the cap–cup
adjunction against `[M]` (`fundamentalFunctional_cupH24`) turns `u ∪ β b` into `⟨β b, u ⌢ [M]⟩`, and the
dual-suspension pairing (`cylBeta_pairing`) turns that into the relative pairing of `b` against
`cylCrossH (u ⌢ [M])`. Generic in the base class `u : H²(M)`. -/
theorem rhsReduce23 (hbij : Function.Bijective (cylCrossH (M := M) 1))
    (u : Cohomology (TopCat.of M) 2) (b : RelativeCohomology (cylBd (M := M)) 3) :
    fundamentalFunctional (m := 2) (M := M) (cupH24 u (cylBeta 1 hbij b))
      = relKroneckerH (cylBd (M := M)) b
          (cylCrossH (M := M) 1 (capH 2 1 u (fundamentalClass (m := 2) (M := M)))) := by
  rw [fundamentalFunctional_cupH24, cylBeta_pairing]

/-- **The `(1,4)` Fubini-RHS reduction.** The `(1,3)`-degree mirror of `rhsReduce23`: `β = cylBeta` at
`p = 2`, `fundamentalFunctional_cupH13` supplies the cap–cup adjunction, giving
`⟨u ∪ β b, [M]⟩ = ⟨b, cylCrossH (u ⌢ [M])⟩` for `u : H¹(M)`. -/
theorem rhsReduce14 (hbij : Function.Bijective (cylCrossH (M := M) 2))
    (u : Cohomology (TopCat.of M) 1) (b : RelativeCohomology (cylBd (M := M)) 4) :
    fundamentalFunctional (m := 2) (M := M) (cupH13 u (cylBeta 2 hbij b))
      = relKroneckerH (cylBd (M := M)) b
          (cylCrossH (M := M) 2 (capH 1 2 u (fundamentalClass (m := 2) (M := M)))) := by
  rw [fundamentalFunctional_cupH13, cylBeta_pairing]

/-! ## §3. The `β`-pinned `CylinderSuspIntertwineData` builder `ofCapCross`

Assembles the downstream `…CylinderIntertwine.CylinderSuspIntertwineData M` — the two-leg residual the
cylinder Poincaré–Lefschetz non-degeneracy consumes — with `β` PINNED to `cylBeta` (no free
equivalence). The two free `β` fields are replaced by two pair-suspension iso witnesses `hbij{23,14}`
(`cylCrossH` bijective in the two suspension degrees), and each `hcompat` Fubini identity by the single
**cap-cross projection value** `hproj{23,14}`:

  `⟨a ∪ b, [W,∂W]⟩ = ⟨b, cylCrossH ((α a) ⌢ [M])⟩`

— the honest relative-Kronecker pairing of `b` against the explicit class `cylCrossH ((α a) ⌢ [M])`, with
NO `cupH`/`fundamentalFunctional` wrapping. `hcompat` is discharged from `hproj` by `rhsReduce{23,14}`. -/

/-- **The `β`-pinned intertwining-data builder.** Produces a `CylinderSuspIntertwineData M` from the two
pair-suspension iso witnesses and the two cap-cross projection values, pinning each `β` to the
geometric Kronecker-dual suspension `cylBeta`. Downstream (`ofClosedPDSuspIntertwine`) then consumes the
pinned-`β` residual in place of the free `(β, hcompat)` pair. -/
def CylinderSuspIntertwineData.ofCapCross [PreconnectedSpace M]
    (hbij23 : Function.Bijective (cylCrossH (M := M) 1))
    (hbij14 : Function.Bijective (cylCrossH (M := M) 2))
    (hproj23 : ∀ (a : Cohomology (TopCat.of (cylW M)) 2)
        (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 3),
        (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu
            (relCupH23 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M)) a b)
          = relKroneckerH (cylBd (M := M)) b
              (cylCrossH (M := M) 1 (capH 2 1 (cylCollapse2 a) (fundamentalClass (m := 2) (M := M)))))
    (hproj14 : ∀ (a : Cohomology (TopCat.of (cylW M)) 1)
        (b : RelativeCohomology (X := TopCat.of (cylW M)) ((cylModel 2).boundary (cylW M)) 4),
        (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu
            (relCupH14 (X := TopCat.of (cylW M)) (S := (cylModel 2).boundary (cylW M)) a b)
          = relKroneckerH (cylBd (M := M)) b
              (cylCrossH (M := M) 2 (capH 1 2 (cylCollapse1 a) (fundamentalClass (m := 2) (M := M))))) :
    CylinderSuspIntertwineData M where
  β23 := cylBeta 1 hbij23
  hcompat23 := fun a b => (hproj23 a b).trans (rhsReduce23 hbij23 (cylCollapse2 a) b).symm
  β14 := cylBeta 2 hbij14
  hcompat14 := fun a b => (hproj14 a b).trans (rhsReduce14 hbij14 (cylCollapse1 a) b).symm

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspDual
