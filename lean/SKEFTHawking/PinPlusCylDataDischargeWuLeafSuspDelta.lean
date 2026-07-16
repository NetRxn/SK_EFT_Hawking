/-
# Phase 5q.H close-out (#148, part 2) — THE Sq-SUSPENSION STABILITY ATOMS DISCHARGED:
# `hsusp23`/`hsusp14` proved via the δ-image calculus; the Wu leaf closes unconditionally

`PinPlusCylDataDischargeWuLeafSusp` isolated the last Wu-leaf content in the two sharp atoms

  `(hsusp23)  μ_W(relSq² b) = ⟨(β b) ∪ (β b), [M]⟩`   (`b ∈ H³(W,∂W)`, `β b ∈ H²(M)`)
  `(hsusp14)  μ_W(relSq¹ b) = ⟨Sq¹ (β b), [M]⟩`       (`b ∈ H⁴(W,∂W)`, `β b ∈ H³(M)`)

— the Steenrod-suspension stability, previously walled twice (#145): the prism route cannot reach
`relSq² b = b′ ⌣₁ b′` (neither factor a pullback), and the raw cup-i route is blocked by the
Kronecker-dual (non-cochain) definition of `β`. This module goes BETWEEN the two walls with the
classical δ-route, made light by the annihilator model (`SingularRelativeCohomDelta`):

1. **Every `b` is a δ-image** (`relToAbs_eq_zero_of_cyl`): the pair restriction
   `j* : Hᵏ(W,∂W) → Hᵏ(W)` VANISHES for `k ≥ 1`, because a relative cochain pulls back to the
   literal zero cochain along an end inclusion `e_r : M → W` (image inside `∂W`), while
   `π* : Hᵏ(M) ≅ Hᵏ(W)` (contractible interval factor) forces `e_r*` injective. So `b = [δz]`.
2. **The squares commute with δ** (`relSq2_deltaRelH`/`relSq1_deltaRelH`, part 1):
   `relSq² [δz] = [δ(z ⌣ z)]` (Hirsch shift) and `relSq¹ [δz] = [δ(sq1Defect z)]` (Bockstein defect).
3. **δ-images are evaluated at the ends** (`relKroneckerH_deltaRelH_crossH`): against ANY cross
   class, `⟨[δy], x × [I,∂I]⟩ = ⟨e₁* y, x⟩ + ⟨e₀* y, x⟩` — the prism boundary formula
   `∂(prismOp x) = end₁ x + end₀ x` under the Kronecker adjunction `⟨δy, c⟩ = ⟨y, ∂c⟩`. Linear and
   per-class in `x` (no connectedness). Hence:
   * `β [δz] = [e₁* z] + [e₀* z]` (`cylBeta_deltaRelH` — the pairing pins `β` on δ-images);
   * `μ_W [δy] = ⟨[e₁* y], [M]⟩ + ⟨[e₀* y], [M]⟩` (`cylinderDatum_mu_deltaRelH`, via
     `[W,∂W] = crossH [M]`, the ClsIdent arc).
4. **The end values assemble** (`endClass_cup_self`/`endClass_sq1Defect`): the end pullback is
   multiplicative on `z ⌣ z` and carries `sq1Defect` to the Bockstein of the end restriction; the
   mod-2 additivity of the cup square (`cupSquare2_add`) and linearity of `Sq¹` absorb the two-end
   sum. Both sides of each atom equal the same two-end expression. ∎

**Payoff:** `CylV2Desuspend`/`CylV1Desuspend` hold UNCONDITIONALLY per connected closed `M`
(`CylV2Desuspend_holds`/`CylV1Desuspend_holds`), so the Wu-leaf row of the provider closes: the
provider inhabitation reduces to the disconnected core alone
(`nonempty_provider_of_disconnectedCoreND`).

**Connectedness entry-points** (for the disconnected twins `DiscCylV{1,2}Desuspend`): §1–§3 above
are connectedness-free and per-class (the δ-calculus is generic in `(X,S)`; the end evaluation is
linear in the paired homology class). Connectedness enters ONLY through (i) the connected datum
`hasRelFundClass_cylGen` whose class is `crossH [M]` (a disconnected datum with class a sum of
component crosses aggregates through the same linear evaluation), (ii) the `fundamentalClass` /
`fundamentalFunctional` objects in the atom statements, and (iii) the duality numerics
(`finiteDimensional_topHomology_of_closed_connected` at the `(1,4)` leg).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`.
-/
import Mathlib
import SKEFTHawking.SingularRelativeCohomDelta
import SKEFTHawking.PinPlusCylDataDischargeWuLeafSusp
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderCapCrossProj
-- (imports pinned)

open scoped Manifold
open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativePairing
open SKEFTHawking.SingularRelativeCup
open SKEFTHawking.SingularRelativeSteenrodSq2
open SKEFTHawking.SingularBockstein SKEFTHawking.SingularRelativeBockstein
open SKEFTHawking.SingularRelativeAbsCompat
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularCohomologyFunctoriality
open SKEFTHawking.SingularCohomologyHomotopy
open SKEFTHawking.SingularProdContractibleInt
open SKEFTHawking.SingularHomotopyInvariance (slice)
open SKEFTHawking.SingularPrism
open SKEFTHawking.SingularHomotopyInvariance (endMap_eq_mapChain)
open SKEFTHawking.SingularKroneckerEquiv
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularRelativeCohomDelta
open SKEFTHawking.SingularManifoldFundamentalClass
open SKEFTHawking.SingularFundamentalClass
open SKEFTHawking.SingularClosedHomologyFinite
open SKEFTHawking.PoincareDualityConstruct
open SKEFTHawking.SingularPD4Instances
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.PoincareLefschetzRelFundClassCylinder
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderWu
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderNumerics
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCross
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCrossLocalAlphaU
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspDual
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderSuspBij
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderCapCrossProj
open SKEFTHawking.PinPlusCharPairData
open SKEFTHawking.PinPlusCharPairBorTethered
open SKEFTHawking.PinPlusCylDataDischargeWuLeaf
open SKEFTHawking.PinPlusCylDataDischargeWuLeafSusp
open SKEFTHawking.PinPlusCylDataDischargeDisconnectedComponents

namespace SKEFTHawking.PinPlusCylDataDischargeWuLeafSuspDelta

noncomputable section

variable {M : Type} [TopologicalSpace M] [T2Space M] [CompactSpace M] [Nonempty M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (2 + 2))) M]

/-! ## §1. The end classes of a δ-image cochain -/

/-- The end pullback of a cochain `y` with `δy` relative is a COCYCLE of `M`: `δ(e_r* y) = e_r*(δy)`
vanishes pointwise (relative cochain, end image inside `∂W`). -/
def endCocycle (r : unitInterval)
    (hr : Set.MapsTo (slice (graphHom (TopCat.of M)) r) (Set.univ : Set ↑(TopCat.of M))
      (cylBd (M := M)))
    {n : ℕ} (y : SingularCochain (cyl (TopCat.of M)) n)
    (h : coboundaryₗ (cyl (TopCat.of M)) n y ∈ relCochains (cylBd (M := M)) (n + 1)) :
    LinearMap.ker (coboundaryₗ (TopCat.of M) n) :=
  ⟨cochainPullback (slice (graphHom (TopCat.of M)) r) n y, by
    rw [LinearMap.mem_ker]
    show coboundary (TopCat.of M) n _ = 0
    rw [coboundary_cochainPullback]
    exact cochainPullback_eq_zero_of_mapsTo _ (fun x => hr (Set.mem_univ x)) ⟨_, h⟩⟩

/-- **The end class** `[e_r* y] ∈ Hⁿ(M)` of a δ-image cochain. -/
def endClass (r : unitInterval)
    (hr : Set.MapsTo (slice (graphHom (TopCat.of M)) r) (Set.univ : Set ↑(TopCat.of M))
      (cylBd (M := M)))
    {n : ℕ} (y : SingularCochain (cyl (TopCat.of M)) n)
    (h : coboundaryₗ (cyl (TopCat.of M)) n y ∈ relCochains (cylBd (M := M)) (n + 1)) :
    Cohomology (TopCat.of M) n :=
  Cohomology.mk (TopCat.of M) n (endCocycle r hr y h)

/-! ## §2. The end evaluation of δ-images against cross classes (the prism boundary formula) -/

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- **The δ-image/cross evaluation** — per-class, linear, connectedness-free:
`⟨[δy], x × [I,∂I]⟩ = ⟨[e₁* y], x⟩ + ⟨[e₀* y], x⟩` for every `x ∈ Hₚ₊₁(M)`. The Kronecker
adjunction moves `δ` to the prism boundary `∂(prismOp x) = end₁ x + end₀ x`
(`prism_chainHomotopy`), and each end push is the slice pullback (`kronecker_cochainPullback`). -/
theorem relKroneckerH_deltaRelH_crossH (p : ℕ)
    (y : SingularCochain (cyl (TopCat.of M)) (p + 1))
    (h : coboundaryₗ (cyl (TopCat.of M)) (p + 1) y ∈ relCochains (cylBd (M := M)) (p + 1 + 1))
    (x : Homology (TopCat.of M) (p + 1)) :
    relKroneckerH (cylBd (M := M)) (deltaRelH y h) (cylCrossH (M := M) p x)
      = kroneckerH (X := TopCat.of M) (p + 1)
          (endClass 1 (slice_one_mapsTo (M := M) (m' := 2)) y h) x
        + kroneckerH (X := TopCat.of M) (p + 1)
            (endClass 0 (slice_zero_mapsTo (M := M) (m' := 2)) y h) x := by
  obtain ⟨zx, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hx : cylCrossH (M := M) p (Submodule.Quotient.mk zx)
      = RelativeHomology.mk (cylBd (M := M)) (p + 1 + 1)
          (crossRelCycle (slice_one_mapsTo (M := M) (m' := 2))
            (slice_zero_mapsTo (M := M) (m' := 2)) p zx) :=
    crossH_mk _ _ p zx
  rw [hx, deltaRelH]
  rw [relKroneckerH_mk_mk]
  show kronecker (coboundaryₗ (cyl (TopCat.of M)) (p + 1) y)
      (crossChain (p + 1) (zx : SingularChain (TopCat.of M) (p + 1))) = _
  have hbdry : chainBoundary (cyl (TopCat.of M)) (p + 1)
      (prismOp (graphHom (TopCat.of M)) (p + 1) (zx : SingularChain (TopCat.of M) (p + 1)))
      = endMap (graphHom (TopCat.of M)) 1 (p + 1) (zx : SingularChain (TopCat.of M) (p + 1))
        + endMap (graphHom (TopCat.of M)) 0 (p + 1) (zx : SingularChain (TopCat.of M) (p + 1)) := by
    have hkey := prism_chainHomotopy (graphHom (TopCat.of M))
      (zx : SingularChain (TopCat.of M) (p + 1))
    rw [LinearMap.mem_ker.mp zx.2, map_zero, add_zero] at hkey
    exact hkey
  rw [show kronecker (coboundaryₗ (cyl (TopCat.of M)) (p + 1) y)
        (crossChain (p + 1) (zx : SingularChain (TopCat.of M) (p + 1)))
      = kronecker (coboundary (cyl (TopCat.of M)) (p + 1) y)
        (crossChain (p + 1) (zx : SingularChain (TopCat.of M) (p + 1))) from rfl,
    kronecker_coboundary_chainBoundary, crossChain, hbdry, kronecker_add_right,
    endMap_eq_mapChain, endMap_eq_mapChain, ← kronecker_cochainPullback,
    ← kronecker_cochainPullback]
  rfl

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- **`β` on δ-images** — the Kronecker-dual suspension evaluates as the sum of the two end
classes: `β [δz] = [e₁* z] + [e₀* z]`. Pairing-level (`cylBeta_pairing` + the end evaluation) plus
the perfectness of the absolute Kronecker pairing (`kroneckerH_injective`). -/
theorem cylBeta_deltaRelH (p : ℕ) (hbij : Function.Bijective (cylCrossH (M := M) p))
    (z : SingularCochain (cyl (TopCat.of M)) (p + 1))
    (h : coboundaryₗ (cyl (TopCat.of M)) (p + 1) z ∈ relCochains (cylBd (M := M)) (p + 1 + 1)) :
    cylBeta (M := M) p hbij (deltaRelH z h)
      = endClass 1 (slice_one_mapsTo (M := M) (m' := 2)) z h
        + endClass 0 (slice_zero_mapsTo (M := M) (m' := 2)) z h := by
  apply kroneckerH_injective (X := TopCat.of M) p
  ext x
  rw [cylBeta_pairing, relKroneckerH_deltaRelH_crossH, map_add]
  rfl

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- `cylBeta_deltaRelH` at the `(2,3)` suspension degree, literal-degree spelling. -/
theorem cylBeta_deltaRelH₂ (hbij : Function.Bijective (cylCrossH (M := M) 1))
    (z : SingularCochain (cyl (TopCat.of M)) 2)
    (h : coboundaryₗ (cyl (TopCat.of M)) 2 z ∈ relCochains (cylBd (M := M)) (2 + 1)) :
    cylBeta (M := M) 1 hbij (deltaRelH (n := 2) z h)
      = endClass 1 (slice_one_mapsTo (M := M) (m' := 2)) z h
        + endClass 0 (slice_zero_mapsTo (M := M) (m' := 2)) z h :=
  cylBeta_deltaRelH 1 hbij z h

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- `cylBeta_deltaRelH` at the `(1,4)` suspension degree, literal-degree spelling. -/
theorem cylBeta_deltaRelH₃ (hbij : Function.Bijective (cylCrossH (M := M) 2))
    (z : SingularCochain (cyl (TopCat.of M)) 3)
    (h : coboundaryₗ (cyl (TopCat.of M)) 3 z ∈ relCochains (cylBd (M := M)) (3 + 1)) :
    cylBeta (M := M) 2 hbij (deltaRelH (n := 3) z h)
      = endClass 1 (slice_one_mapsTo (M := M) (m' := 2)) z h
        + endClass 0 (slice_zero_mapsTo (M := M) (m' := 2)) z h :=
  cylBeta_deltaRelH 2 hbij z h

/-! ## §3. `μ_W` on δ-images (via `[W,∂W] = crossH [M]`, the ClsIdent arc) -/

section Mu

variable [PreconnectedSpace M] [T1Space (cylW M)]

/-- **`μ_W` on δ-images**: `μ_W [δy] = ⟨[e₁* y], [M]⟩ + ⟨[e₀* y], [M]⟩` — the end evaluation at
`x := [M]`, through the datum-class identification `[W,∂W] = crossH [M]`. This is where the
CONNECTED datum enters (`hasRelFundClass_cylGen`); a disconnected datum whose class is a sum of
component crosses aggregates through the same linear evaluation. -/
theorem cylinderDatum_mu_deltaRelH
    (y : SingularCochain (cyl (TopCat.of M)) 4)
    (h : coboundaryₗ (cyl (TopCat.of M)) 4 y ∈ relCochains (cylBd (M := M)) 5) :
    (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu (deltaRelH y h)
      = fundamentalFunctional (m := 2) (M := M)
          (endClass 1 (slice_one_mapsTo (M := M) (m' := 2)) y h)
        + fundamentalFunctional (m := 2) (M := M)
            (endClass 0 (slice_zero_mapsTo (M := M) (m' := 2)) y h) := by
  rw [cylinderDatum_mu_eq_funct]
  show relKroneckerH (cylBdW (M := M)) (deltaRelH y h) (cylFundClassCandidate (M := M) (m' := 2))
    = _
  rw [cylFundClassCandidate_eq_cylCrossH]
  exact relKroneckerH_deltaRelH_crossH 3 y h (fundamentalClass (m := 2) (M := M))

end Mu

/-! ## §4. The end classes of the δ-naturality images -/

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- The end class of `z ⌣ z` is the cup SQUARE of the end class of `z` (the cochain pullback is
multiplicative, `cochainPullback_cup`). -/
theorem endClass_cup_self (r : unitInterval)
    (hr : Set.MapsTo (slice (graphHom (TopCat.of M)) r) (Set.univ : Set ↑(TopCat.of M))
      (cylBd (M := M)))
    (z : SingularCochain (cyl (TopCat.of M)) 2)
    (h : coboundaryₗ (cyl (TopCat.of M)) 2 z ∈ relCochains (cylBd (M := M)) 3) :
    endClass r hr (n := 4) (cup z z) (coboundary_cup_self_mem_relCochains z h)
      = cupSquare2 (endClass r hr z h) := by
  show Submodule.Quotient.mk (endCocycle r hr (cup z z) (coboundary_cup_self_mem_relCochains z h))
    = cupH24 (Submodule.Quotient.mk (endCocycle r hr z h))
        (Submodule.Quotient.mk (endCocycle r hr z h))
  rw [SingularCohomologyMod2.cupH24_mk_mk]
  exact congrArg (Submodule.Quotient.mk (p := (coboundaryRange (TopCat.of M) 4).submoduleOf _))
    (Subtype.ext (cochainPullback_cup _ z z))

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- The end class of `sq1Defect z` is `Sq¹` of the end class of `z`
(`cochainPullback_sq1Defect`). -/
theorem endClass_sq1Defect (r : unitInterval)
    (hr : Set.MapsTo (slice (graphHom (TopCat.of M)) r) (Set.univ : Set ↑(TopCat.of M))
      (cylBd (M := M)))
    (z : SingularCochain (cyl (TopCat.of M)) 3)
    (h : coboundaryₗ (cyl (TopCat.of M)) 3 z ∈ relCochains (cylBd (M := M)) 4) :
    endClass r hr (n := 4) (sq1Defect z) (coboundary_sq1Defect_mem_relCochains z h)
      = Sq1 (n := 2) (endClass r hr z h) := by
  show Cohomology.mk (TopCat.of M) 4 _ = Sq1 (Submodule.Quotient.mk (endCocycle r hr z h))
  rw [Sq1_apply]
  exact congrArg (Submodule.Quotient.mk (p := (coboundaryRange (TopCat.of M) 4).submoduleOf _))
    (Subtype.ext (cochainPullback_sq1Defect _ (fun x => hr (Set.mem_univ x)) z h))

/-! ## §5. Every relative class of the cylinder pair is a δ-image (`j* = 0` in degrees `≥ 1`) -/

omit [T2Space M] [CompactSpace M] [Nonempty M] in
/-- **The pair restriction vanishes on the cylinder** in every degree `≥ 1`: a relative cochain
pulls back to the literal zero cochain along the end `e₀ : M → W`, while `e₀*` is injective on
`Hᵏ(W)` because `π* : Hᵏ(M) → Hᵏ(W)` is surjective (contractible interval factor) with
`e₀* ∘ π* = id`. Connectedness-free. -/
theorem relToAbs_eq_zero_of_cyl {n : ℕ}
    (b : RelativeCohomology (cylBd (M := M)) (n + 1)) :
    relToAbs b = 0 := by
  have hsurj : Function.Surjective
      (cohomologyPullback (prodFst (TopCat.of M) (TopCat.of unitInterval)) (n + 1)) :=
    (prodFst_cohomology_bijective (TopCat.of M) (TopCat.of unitInterval) ⊥ iccContraction
      slice_iccContraction_zero slice_iccContraction_one n).2
  obtain ⟨u, hu⟩ := hsurj (relToAbs b)
  have hcomp : (prodFst (TopCat.of M) (TopCat.of unitInterval)).comp
      (slice (graphHom (TopCat.of M)) 0) = ContinuousMap.id ↑(TopCat.of M) :=
    ContinuousMap.ext fun x => rfl
  have hpull : cohomologyPullback (slice (graphHom (TopCat.of M)) 0) (n + 1) (relToAbs b) = u := by
    rw [← hu, ← LinearMap.comp_apply, ← cohomologyPullback_comp, hcomp, cohomologyPullback_id,
      LinearMap.id_apply]
  have hzero : cohomologyPullback (slice (graphHom (TopCat.of M)) 0) (n + 1) (relToAbs b) = 0 := by
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ b
    rw [show (Submodule.Quotient.mk a : RelativeCohomology (cylBd (M := M)) (n + 1))
        = RelativeCohomology.mk (cylBd (M := M)) (n + 1) a from rfl, relToAbs_mk,
      cohomologyPullback_mk]
    refine (Submodule.Quotient.mk_eq_zero _).mpr ?_
    rw [Submodule.submoduleOf, Submodule.mem_comap, Submodule.coe_subtype]
    show cochainPullback (slice (graphHom (TopCat.of M)) 0) (n + 1)
        ((relToAbsCocycleₗ a : LinearMap.ker (coboundaryₗ (cyl (TopCat.of M)) (n + 1))) :
          SingularCochain (cyl (TopCat.of M)) (n + 1)) ∈ coboundaryRange (TopCat.of M) (n + 1)
    rw [relToAbsCocycleₗ_coe, cochainPullback_eq_zero_of_mapsTo _
      (fun x => slice_zero_mapsTo (M := M) (m' := 2) (Set.mem_univ x)) a.1]
    exact Submodule.zero_mem _
  rw [← hu, hpull.symm.trans hzero, map_zero]

/-! ## §6. THE TWO ATOMS -/

section Atoms

variable [PreconnectedSpace M] [T1Space (cylW M)]

/-- **`hsusp23` HOLDS** — the `(2,3)` Sq-suspension stability: `μ_W(relSq² b) = ⟨(β b)², [M]⟩` for
every `b ∈ H³(W,∂W)` and any pair-suspension iso witness. Proof: `b = [δz]` (§5); `relSq²` carries
`[δz]` to `[δ(z ⌣ z)]` (Hirsch shift, part 1); both `μ_W` and `β` evaluate δ-images at the two ends
(§2–§3); the end pullback is multiplicative and the mod-2 cup square is additive
(`cupSquare2_add`), so the two two-end expressions coincide. -/
theorem cyl_sqSusp23 (hbij : Function.Bijective (cylCrossH (M := M) 1))
    (b : RelativeCohomology (cylBd (M := M)) 3) :
    (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu
        (relSq2 (S := cylBd (M := M)) b)
      = fundamentalFunctional (m := 2) (M := M) (cupSquare2 (cylBeta (M := M) 1 hbij b)) := by
  obtain ⟨z, h, rfl⟩ := exists_deltaRelH_of_relToAbs_eq_zero b
    (relToAbs_eq_zero_of_cyl (M := M) (n := 2) b)
  rw [relSq2_deltaRelH z h]
  refine (cylinderDatum_mu_deltaRelH (cup z z)
    (coboundary_cup_self_mem_relCochains z h)).trans ?_
  rw [cylBeta_deltaRelH₂ hbij z h, cupSquare2_add, map_add, endClass_cup_self, endClass_cup_self]

/-- **`hsusp14` HOLDS** — the `(1,4)` Sq¹-suspension stability: `μ_W(relSq¹ b) = ⟨Sq¹(β b), [M]⟩`
for every `b ∈ H⁴(W,∂W)` and any pair-suspension iso witness. The `(1,4)` mirror through the
explicit Bockstein defect (`sq1Defect`, part 1) and the linearity of `Sq¹`. -/
theorem cyl_sqSusp14 (hbij : Function.Bijective (cylCrossH (M := M) 2))
    (b : RelativeCohomology (cylBd (M := M)) 4) :
    (cylinderDatum (hasRelFundClass_cylGen (m' := 2) (M := M))).mu
        (relSq1 (S := cylBd (M := M)) (n := 3) b)
      = fundamentalFunctional (m := 2) (M := M) (Sq1 (n := 2) (cylBeta (M := M) 2 hbij b)) := by
  obtain ⟨z, h, rfl⟩ := exists_deltaRelH_of_relToAbs_eq_zero b
    (relToAbs_eq_zero_of_cyl (M := M) (n := 3) b)
  rw [relSq1_deltaRelH_three z h]
  refine (cylinderDatum_mu_deltaRelH (sq1Defect z)
    (coboundary_sq1Defect_mem_relCochains z h)).trans ?_
  rw [cylBeta_deltaRelH₃ hbij z h, map_add, map_add, endClass_sq1Defect, endClass_sq1Defect]

/-! ## §7. The Wu-leaf desuspension atoms close unconditionally; the provider row -/

/-- **`CylV2Desuspend` holds unconditionally** for every connected closed 4-manifold `M` — the
`(2,3)` desuspension atom of the Wu leaf is a THEOREM: the prism-discharged form
(`CylV2Desuspend_of_sqSusp_prism`) with `hsusp23` supplied by `cyl_sqSusp23`. -/
theorem CylV2Desuspend_holds : CylV2Desuspend (M := M) :=
  CylV2Desuspend_of_sqSusp_prism
    (finiteDimensional_homology_of_closed (M := M)).2.1
    (finiteDimensional_homology_of_closed (M := M)).2.2.1
    (fun b => cyl_sqSusp23 _ b)

/-- **`CylV1Desuspend` holds unconditionally** for every connected closed 4-manifold `M` — the
`(1,4)` desuspension atom of the Wu leaf is a THEOREM. -/
theorem CylV1Desuspend_holds : CylV1Desuspend (M := M) :=
  CylV1Desuspend_of_sqSusp_prism
    (finiteDimensional_homology_of_closed (M := M)).2.2.1
    (finiteDimensional_topHomology_of_closed_connected (M := M))
    (fun b => cyl_sqSusp14 _ b)

end Atoms

/-- **THE PROVIDER ON THE DISCONNECTED CORE ALONE.** With both Wu-leaf desuspension atoms now
theorems (`CylV2Desuspend_holds`/`CylV1Desuspend_holds`), the char-pair `W`-provider inhabitation
needs ONLY the disconnected core: the `hA`/`hB` inputs of
`nonempty_provider_of_desuspendLeaves_and_disconnectedCoreND` are discharged in-tree. -/
theorem nonempty_provider_of_disconnectedCoreND
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {k : WithTop ℕ∞} {I : ModelWithCorners ℝ E (EuclideanSpace ℝ (Fin (2 + 2)))} [I.Boundaryless]
    (hdiscCoreND : ∀ {s : SingularManifold.{0} PUnit.{1} k I} (_σ : CharPairStrBundled I s)
      [T2Space s.M] [Nonempty s.M], ¬ PreconnectedSpace s.M → DisconnectedCylCoreND s.M) :
    Nonempty (CharPairWProviderPerOp I k) :=
  nonempty_provider_of_desuspendLeaves_and_disconnectedCoreND
    (fun {_s} _σ => CylV2Desuspend_holds) (fun {_s} _σ => CylV1Desuspend_holds) hdiscCoreND

end

end SKEFTHawking.PinPlusCylDataDischargeWuLeafSuspDelta
