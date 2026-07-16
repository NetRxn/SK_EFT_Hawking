/-
# Phase 5q.H close-out — THE CONCRETE SPHERE-4 CYCLE `zS` (hasClass's LAST concrete object)

`PinPlusTraceDiskCorePair.betaClass` is the nonzero generator of `H₄(∂D⁵; ℤ/2)`, built by
transporting the top sphere generator back along the boundary homeomorphism. It is a homology
*class*, not a *cycle*. This module produces the missing concrete object: a singular 4-cycle
`zS` on the boundary sphere `{‖v‖ = 1} = ∂D⁵` whose class is nonzero (equivalently, the
fundamental generator `betaClass`).

**The route (the pair-LES connecting engine, ZERO new geometry).** `D⁵` is acyclic
(`disk_homology_zero`: `H₅(D⁵) = 0`, `H₄(D⁵) = 0`), so the pair-LES connecting map
`∂ : H₅(D⁵, S⁴) → H₄(S⁴)` is an isomorphism (`connecting_bijective_of_acyclic`). The banked disk
detecting chain `diskDetectChain` is a relative `5`-cycle (its boundary lands in the sphere by
`diskDetectChain_hc`); its relative class is nonzero because it detects the interior generator at
the center point `0` (`diskDetectChain_hdet`). Extracting the boundary to the sphere gives the
cycle `zS := boundaryExtract diskDetectChain`, whose class is `connecting α`; the injective
connecting map carries `α ≠ 0` to `[zS] ≠ 0`.

All the connecting-map work runs over the simple predicate set `{‖v‖ = 1}` — never the
whnf-hostile `ModelWithCorners.boundary D⁵` — and the interior-point detection is proof-irrelevant
over that set, so the concrete `D⁵`/`closedBall`/`WithLp` stack is never forced.

So `zS` is `∂cHa`-as-a-cycle: the boundary of the disk detecting chain, exposed as an honest
sphere 4-cycle with the nonzero (fundamental) class — the last concrete object `hasClass` needs.

Additive module. Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no
`sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PinPlusTraceDiskCorePair

open scoped Manifold
open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularMayerVietoris
open SKEFTHawking.SingularRelativeCoverMV
open SKEFTHawking.SingularPairLES
open SKEFTHawking.SingularManifoldFundamentalClass
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.DiskChartGeneric (D5)

namespace SKEFTHawking.PinPlusTraceDiskSphereCycle

noncomputable section

/-- The boundary sphere set `{‖v‖ = 1}` — `= ∂D⁵` (`boundary_D5`), but the simple predicate form
that `diskDetectChain_hc`/`diskDetectChain_hdet` use natively (whnf-safe). -/
abbrev Ssph : Set (D5) := {v : D5 | ‖(v : EuclideanSpace ℝ (Fin 5))‖ = 1}

/-- **`diskDetectChain`'s boundary lands in the sphere `{‖v‖ = 1}`** — `diskDetectChain_hc`. The
single shared membership proof reused below. -/
theorem dc_hc :
    chainBoundary (TopCat.of D5) 4 PinPlusTraceDiskCorePair.diskDetectChain
      ∈ subspaceChains (X := TopCat.of D5) Ssph 4 :=
  PinPlusTraceDiskCorePair.diskDetectChain_hc

/-- **`diskDetectChain` is a relative `5`-cycle over `{‖v‖ = 1}`.** -/
theorem diskDetectChain_mem_relCycleLift :
    PinPlusTraceDiskCorePair.diskDetectChain ∈ relCycleLift (X := TopCat.of D5) Ssph 4 :=
  dc_hc

/-- The bundled relative-cycle lift of `diskDetectChain`. -/
def dcLift : relCycleLift (X := TopCat.of D5) Ssph 4 :=
  ⟨PinPlusTraceDiskCorePair.diskDetectChain, dc_hc⟩

/-- **`zS` — the concrete sphere-4 cycle.** The boundary of the disk detecting chain, extracted to
the sphere `{‖v‖ = 1}` and packaged as a cycle. -/
def zS : cycles (sub (X := TopCat.of D5) Ssph) 4 :=
  ⟨boundaryExtract (X := TopCat.of D5) Ssph 4 dcLift,
    boundaryExtract_mem_cycles (X := TopCat.of D5) Ssph 4 dcLift⟩

/-- **The class of `zS`** in `H₄({‖v‖ = 1}; ℤ/2) = H₄(∂D⁵; ℤ/2)`. -/
def zSclass : Homology (sub (X := TopCat.of D5) Ssph) 4 :=
  Homology.mk (sub (X := TopCat.of D5) Ssph) 4 zS

/-- The disk has an interior (off-sphere) point — the center `0` (norm `0 ≠ 1`). -/
theorem exists_interior_point : ∃ y : D5, y ∉ Ssph :=
  ⟨⟨0, by simp⟩, by
    show ¬ ‖((⟨0, by simp⟩ : D5) : EuclideanSpace ℝ (Fin 5))‖ = 1
    show ¬ ‖(0 : EuclideanSpace ℝ (Fin 5))‖ = 1
    simp⟩

/-- **A `.choose`-hidden interior point** — the witness of `exists_interior_point`. The `.choose`
wrapper keeps `{intPt}ᶜ` from unfolding the concrete `⟨0, …⟩ : D⁵` value (which whnf-blows the
`WithLp`/`closedBall` stack during the detection unification). -/
def intPt : D5 := exists_interior_point.choose

theorem intPt_not_mem_sphere : intPt ∉ Ssph := exists_interior_point.choose_spec

/-- **A relative class detecting the local generator at one interior point is nonzero** (abstract,
ambient-`X`). If `relClassOf {x}ᶜ c ≠ 0` at some `x ∉ S`, then `relClassOf S c ≠ 0` — its
`restrictBd` at `x` is exactly the nonzero local class (`restrictBd_relClassOf`). Proven abstractly
so the `restrictBd` rewrite is checked over an abstract `X`, never forcing the whnf-hostile concrete
`D⁵` stack. -/
theorem relClassOf_ne_zero_of_detects {X : TopCat} {m : ℕ} (S : Set ↑X)
    (c : SingularChain X (m + 2)) (hc : chainBoundary X (m + 1) c ∈ subspaceChains S (m + 1))
    (x : ↑X) (hx : x ∉ S)
    (hdet : relClassOf ({x}ᶜ) m c
        (subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hx) (m + 1) hc) ≠ 0) :
    relClassOf S m c hc ≠ 0 := by
  intro h0
  apply hdet
  rw [← restrictBd_relClassOf S hx m c hc, h0, map_zero]

/-- **`α ≠ 0`** — the relative class of the disk detecting chain is nonzero. Its restriction to the
center point `0` is `relClassOf {0}ᶜ diskDetectChain`, nonzero by `diskDetectChain_hdet`. -/
theorem relClassOf_diskDetectChain_ne_zero :
    relClassOf (X := TopCat.of D5) Ssph 3 PinPlusTraceDiskCorePair.diskDetectChain dc_hc ≠ 0 :=
  relClassOf_ne_zero_of_detects (X := TopCat.of D5) (m := 3) Ssph
    PinPlusTraceDiskCorePair.diskDetectChain dc_hc intPt intPt_not_mem_sphere
    (PinPlusTraceDiskCorePair.diskDetectChain_hdet intPt intPt_not_mem_sphere)

/-- **`relCycleToHom` is `relClassOf`** (abstract): the relative-homology class of a lift-chain
is the almost-cycle class of the underlying chain. -/
theorem relCycleToHom_eq_relClassOf {X : TopCat} {m : ℕ} (S : Set ↑X) (c : relCycleLift S (m + 1)) :
    relCycleToHom S (m + 1) c = relClassOf S m (c : SingularChain X (m + 2)) c.2 := by
  rw [relCycleToHom_apply, relClassOf]; rfl

/-- **The connecting map carries a nonzero relative class to a nonzero boundary class** (abstract,
ambient-`X` acyclic). If the ambient `X` is acyclic in degrees `m+2` and `m+1`, the pair-LES
connecting map `∂ : Hₘ₊₂(X, S) → Hₘ₊₁(S)` is injective (`connecting_bijective_of_acyclic`), so the
extracted boundary class `connectingLift c = ∂[c]` of a relative cycle `c` with nonzero relative
class is nonzero. Proven abstractly so `connecting_bijective_of_acyclic` is never re-elaborated at
the whnf-hostile concrete `D⁵` (the documented `SingularConvexRestrictionIso` hazard). -/
theorem connectingLift_ne_zero_of_relClassOf_ne_zero {X : TopCat} {m : ℕ} (S : Set ↑X)
    (h1 : ∀ x : Homology X (m + 2), x = 0) (h0 : ∀ x : Homology X (m + 1), x = 0)
    (c : relCycleLift S (m + 1))
    (hne : relClassOf S m (c : SingularChain X (m + 2)) c.2 ≠ 0) :
    connectingLift S (m + 1) c ≠ 0 := by
  have hinj : Function.Injective (connecting S (m + 1)) :=
    (connecting_bijective_of_acyclic S (m + 1) h1 h0).injective
  rw [← connecting_relCycleToHom]
  intro hcon
  apply hne
  rw [← relCycleToHom_eq_relClassOf]
  exact hinj (by rw [hcon, map_zero])

/-- **`[zS] ≠ 0`.** `[zS] = connectingLift dcLift = ∂α`, and the connecting map is injective over the
acyclic disk, carrying `α ≠ 0` (`relClassOf_diskDetectChain_ne_zero`) to `[zS] ≠ 0`. -/
theorem zSclass_ne_zero : zSclass ≠ 0 :=
  connectingLift_ne_zero_of_relClassOf_ne_zero (X := TopCat.of D5) (m := 3) Ssph
    (PinPlusTraceDiskRelFundReduce.disk_homology_zero 4)
    (PinPlusTraceDiskRelFundReduce.disk_homology_zero 3)
    dcLift relClassOf_diskDetectChain_ne_zero

end

end SKEFTHawking.PinPlusTraceDiskSphereCycle
