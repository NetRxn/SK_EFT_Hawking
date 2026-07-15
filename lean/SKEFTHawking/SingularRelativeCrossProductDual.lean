/-
# Phase 5q.H Track 2 — the COHOMOLOGY-side cross-product: the suspension `β` as the
# Kronecker-DUAL of the homology cross with `[I, ∂I]`

The two remaining Track-2 walls (`hcompat` in `…CylinderIntertwine`, `hwu`'s `M`-intrinsic
reduction in `…BaseWu`) both need the COHOMOLOGY-side of the cross product `[W,∂W] = [M] × [I,∂I]`.
The HOMOLOGY prism engine already exists — `SingularRelativeCrossProduct.crossH`, the map
`× [I,∂I] : Hₚ₊₁(M) → Hₚ₊₂(M×I, S)`. What is missing is the SUSPENSION iso on cohomology,
`β : Hᵏ(M×I, S) → Hᵏ⁻¹(M)`.

**No shuffle product is built.** Rather than construct a cochain-level cross/Eilenberg–Zilber map
from scratch (the "multi-hundred-line combinatorial development" the substrate recon flagged), this
module DUALIZES the existing `crossH`. The Kronecker pairings are perfect over `ℤ/2`
(`kroneckerHEquiv` absolute, `relKroneckerHEquiv` relative, both finite-dim-free), so:

  `crossHDual b := (kroneckerHEquiv).symm (φ ↦ ⟨b, crossH φ⟩)`

is the cohomology class whose pairing against `x ∈ Hₚ₊₁(M)` is `⟨b, crossH x⟩` — the transpose of
`crossH` through the two perfect pairings. Its defining property (`crossHDual_pairing`)

  `⟨crossHDual b, x⟩_M = ⟨b, crossH x⟩_{(M×I,S)}`

is EXACTLY the load-bearing "suspension compatibility of the Kronecker pairing" the Fubini residual
needs: it turns a relative pairing on `(M×I,S)` into an absolute pairing on `M`, transporting the
`b`-argument across the suspension without any face-shuffle bookkeeping.

When `crossH` is a linear ISO (the pair-suspension iso — a Künneth-level input tracked as a
hypothesis, geometrically transparent for the reflexive cylinder), `crossHDualEquiv` upgrades this to
the honest suspension EQUIVALENCE `β`, again with the pairing identity — so the `β` free field of the
downstream `CylinderSuspIntertwineData` reduces to the single hypothesis "`crossH` is an iso".

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
new `axiom`.
-/
import Mathlib
import SKEFTHawking.SingularRelativeCrossProduct
import SKEFTHawking.SingularKroneckerEquiv
import SKEFTHawking.SingularRelativeKroneckerEquiv

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativePairing
open SKEFTHawking.SingularKroneckerEquiv
open SKEFTHawking.SingularRelativeKroneckerEquiv
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularHomotopyInvariance (slice)

namespace SKEFTHawking.SingularRelativeCrossProductDual

noncomputable section

variable {M : TopCat}

/-! ## §1. The cohomology-suspension map `crossHDual` (the Kronecker-dual of `crossH`) -/

/-- **The cohomology-level cross/suspension** `Hᵖ⁺²(M×I, S) → Hᵖ⁺¹(M)`, the Kronecker-DUAL of the
homology cross `crossH : Hₚ₊₁(M) → Hₚ₊₂(M×I, S)`. Built as the transpose through the two perfect
pairings: `b ↦ (kroneckerHEquiv).symm (⟨b, crossH ·⟩)`. No shuffle product — an existing map dualized. -/
def crossHDual {S : Set ↑(cyl M)}
    (h1 : Set.MapsTo (slice (graphHom M) 1) (Set.univ : Set ↑M) S)
    (h0 : Set.MapsTo (slice (graphHom M) 0) (Set.univ : Set ↑M) S)
    (p : ℕ) :
    RelativeCohomology S (p + 1 + 1) →ₗ[ZMod 2] Cohomology M (p + 1) :=
  (kroneckerHEquiv (X := M) p).symm.toLinearMap.comp
    ((crossH h1 h0 p).dualMap.comp (relKroneckerHEquiv S (p + 1)).toLinearMap)

/-- **The defining pairing identity of `crossHDual`** — the suspension compatibility of the Kronecker
pairing: `⟨crossHDual b, x⟩_M = ⟨b, crossH x⟩_{(M×I,S)}`. Transports the `b`-argument across the
suspension with no face-shuffle bookkeeping. This is the load-bearing identity the Fubini residual
consumes. -/
theorem crossHDual_pairing {S : Set ↑(cyl M)}
    (h1 : Set.MapsTo (slice (graphHom M) 1) (Set.univ : Set ↑M) S)
    (h0 : Set.MapsTo (slice (graphHom M) 0) (Set.univ : Set ↑M) S)
    (p : ℕ) (b : RelativeCohomology S (p + 1 + 1)) (x : Homology M (p + 1)) :
    kroneckerH (X := M) (p + 1) (crossHDual h1 h0 p b) x
      = relKroneckerH S b (crossH h1 h0 p x) := by
  rw [crossHDual, LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe,
    kroneckerH_symm, LinearMap.dualMap_apply, LinearEquiv.coe_coe, relKroneckerHEquiv_apply]

/-! ## §2. The suspension EQUIVALENCE `β` (when `crossH` is an iso) -/

/-- **The cohomology-suspension EQUIVALENCE** `β : Hᵖ⁺²(M×I, S) ≃ Hᵖ⁺¹(M)`, from a linear-ISO
witness `crossHE` for the homology cross `crossH` (the pair-suspension iso — a Künneth-level input,
geometrically transparent for the reflexive cylinder, tracked as this single hypothesis). Built as
the composite of perfect-pairing duals `Hᵖ⁺²(M×I,S) ≃ (Hₚ₊₂(M×I,S))^* ≃ (Hₚ₊₁(M))^* ≃ Hᵖ⁺¹(M)`. -/
def crossHDualEquiv {S : Set ↑(cyl M)} (p : ℕ)
    (crossHE : Homology M (p + 1) ≃ₗ[ZMod 2] RelativeHomology S (p + 1 + 1)) :
    RelativeCohomology S (p + 1 + 1) ≃ₗ[ZMod 2] Cohomology M (p + 1) :=
  (relKroneckerHEquiv S (p + 1)).trans (crossHE.dualMap.trans (kroneckerHEquiv (X := M) p).symm)

/-- **`crossHDualEquiv` computes as `crossHDual`** when the iso witness `crossHE` agrees with the
homology cross `crossH`: the equivalence is the same underlying transpose map, so it inherits every
value identity of `crossHDual` (in particular the pairing identity `crossHDualEquiv_pairing`). -/
theorem crossHDualEquiv_eq_crossHDual {S : Set ↑(cyl M)}
    (h1 : Set.MapsTo (slice (graphHom M) 1) (Set.univ : Set ↑M) S)
    (h0 : Set.MapsTo (slice (graphHom M) 0) (Set.univ : Set ↑M) S)
    (p : ℕ) (crossHE : Homology M (p + 1) ≃ₗ[ZMod 2] RelativeHomology S (p + 1 + 1))
    (hE : (crossHE : Homology M (p + 1) →ₗ[ZMod 2] RelativeHomology S (p + 1 + 1))
      = crossH h1 h0 p)
    (b : RelativeCohomology S (p + 1 + 1)) :
    crossHDualEquiv p crossHE b = crossHDual h1 h0 p b := by
  rw [crossHDualEquiv, crossHDual, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    relKroneckerHEquiv_apply, LinearMap.comp_apply, LinearMap.comp_apply,
    LinearEquiv.coe_coe, LinearEquiv.coe_coe, relKroneckerHEquiv_apply]
  congr 1
  ext y
  rw [LinearEquiv.dualMap_apply, LinearMap.dualMap_apply]
  exact congrArg _ (LinearMap.congr_fun hE y)

/-- **The pairing identity for the suspension equivalence** `⟨β b, x⟩_M = ⟨b, crossH x⟩_{(M×I,S)}`:
`β = crossHDualEquiv` carries the same suspension compatibility of the Kronecker pairing as
`crossHDual` (they are the same underlying map when `crossHE = crossH`). -/
theorem crossHDualEquiv_pairing {S : Set ↑(cyl M)}
    (h1 : Set.MapsTo (slice (graphHom M) 1) (Set.univ : Set ↑M) S)
    (h0 : Set.MapsTo (slice (graphHom M) 0) (Set.univ : Set ↑M) S)
    (p : ℕ) (crossHE : Homology M (p + 1) ≃ₗ[ZMod 2] RelativeHomology S (p + 1 + 1))
    (hE : (crossHE : Homology M (p + 1) →ₗ[ZMod 2] RelativeHomology S (p + 1 + 1))
      = crossH h1 h0 p)
    (b : RelativeCohomology S (p + 1 + 1)) (x : Homology M (p + 1)) :
    kroneckerH (X := M) (p + 1) (crossHDualEquiv p crossHE b) x
      = relKroneckerH S b (crossH h1 h0 p x) := by
  rw [crossHDualEquiv_eq_crossHDual h1 h0 p crossHE hE, crossHDual_pairing]

/-- **The suspension equivalence from a bijectivity witness** — the geometrically-transparent form of
the pair-suspension iso: `crossH` (the honest `× [I,∂I]`) being BIJECTIVE is the single Künneth-level
input, and `β` is its Kronecker-dual packaged as an equivalence. -/
def crossHDualEquivOfBij {S : Set ↑(cyl M)}
    (h1 : Set.MapsTo (slice (graphHom M) 1) (Set.univ : Set ↑M) S)
    (h0 : Set.MapsTo (slice (graphHom M) 0) (Set.univ : Set ↑M) S)
    (p : ℕ) (hbij : Function.Bijective (crossH h1 h0 p)) :
    RelativeCohomology S (p + 1 + 1) ≃ₗ[ZMod 2] Cohomology M (p + 1) :=
  crossHDualEquiv p (LinearEquiv.ofBijective (crossH h1 h0 p) hbij)

/-- **The pairing identity for `crossHDualEquivOfBij`** `⟨β b, x⟩_M = ⟨b, crossH x⟩_{(M×I,S)}`. -/
theorem crossHDualEquivOfBij_pairing {S : Set ↑(cyl M)}
    (h1 : Set.MapsTo (slice (graphHom M) 1) (Set.univ : Set ↑M) S)
    (h0 : Set.MapsTo (slice (graphHom M) 0) (Set.univ : Set ↑M) S)
    (p : ℕ) (hbij : Function.Bijective (crossH h1 h0 p))
    (b : RelativeCohomology S (p + 1 + 1)) (x : Homology M (p + 1)) :
    kroneckerH (X := M) (p + 1) (crossHDualEquivOfBij h1 h0 p hbij b) x
      = relKroneckerH S b (crossH h1 h0 p x) :=
  crossHDualEquiv_pairing h1 h0 p (LinearEquiv.ofBijective (crossH h1 h0 p) hbij) rfl b x

end

end SKEFTHawking.SingularRelativeCrossProductDual
