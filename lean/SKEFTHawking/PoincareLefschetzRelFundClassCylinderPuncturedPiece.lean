/-
# Phase 5q.H (W-A arm 4) — the MV piece `H_*(M×I, (M∖σ)×I) ≅ H_*(M, M∖σ)`

Route-B infrastructure for the punctured-product local homology. Of the two pieces of the MV cover
of `{x}ᶜ` (`PoincareLefschetzRelFundClassCylinderPuncturedCover`), the `M`-punctured piece
`puncV x = (M∖σ) × I` has **computable** relative homology: the pair `(M×I, (M∖σ)×I)` is homotopy
equivalent to `(M, M∖σ)` by contracting the interval factor, so

  `H_{n+1}(M×I, (M∖σ)×I) ≅ H_{n+1}(M, M∖σ)`  —  the local homology of the *base*.

The homotopy equivalence of pairs is the bottom inclusion `f : a ↦ (a,0)` against the projection
`g : (a,s) ↦ a`, with `g∘f = id` (constant homotopy) and `f∘g ≃ id` via `Hfg((a,s),u) = (a, u·s)`
(interval scaling), both respecting the `(M∖σ)`-subspace since they never move the base coordinate.
Fed to the in-tree pair homotopy-equivalence iso
`SingularRelativeHomotopyInvariance.RelativeHomology.map_bijective_of_homotopyEquiv_pair`.

## What this banks (all kernel-pure, no `sorry`/axiom)

* **§1 — the homotopy-equivalence data** `cylBot`, `cylProj`, `cylHgf`, `cylHfg` and the six
  homotopy/`MapsTo` conditions at the cover's `puncV`.
* **§2 — the piece iso** `puncVPieceEquiv x n : H_{n+1}(M, {σ}ᶜ) ≃ₗ H_{n+1}(M×I, puncV x)` — the MV
  piece identified with the base local homology, the bottom-inclusion pushforward made an
  isomorphism.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedCover
import SKEFTHawking.SingularRelativeHomotopyInvariance

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularRelativeCrossProduct
open SKEFTHawking.SingularHomotopyInvariance (slice)
open SKEFTHawking.SingularRelativeFunctoriality
open SKEFTHawking.SingularRelativeHomotopyInvariance
open SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedCover

namespace SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedPiece

noncomputable section

variable {N : TopCat}

/-! ## §1. The interval-contraction homotopy-equivalence of pairs `(M×I, (M∖σ)×I) ≃ (M, M∖σ)` -/

/-- The **bottom inclusion** `f : M → M×I`, `a ↦ (a, 0)`. -/
def cylBot : C(↑N, ↑(cyl N)) := ⟨fun a => (a, 0), by fun_prop⟩

/-- The **projection** `g : M×I → M`, `(a,s) ↦ a`. -/
def cylProj : C(↑(cyl N), ↑N) := ⟨Prod.fst, continuous_fst⟩

/-- The (constant) homotopy `g∘f ≃ id_M`; since `g∘f = id` already, `Hgf(a,u) = a`. -/
def cylHgf : C(↑N × unitInterval, ↑N) := ⟨fun p => p.1, continuous_fst⟩

/-- The homotopy `f∘g ≃ id_{M×I}`: `Hfg((a,s),u) = (a, u·s)` (interval scaling of the second
coordinate from `0` at `u=0` to `s` at `u=1`). -/
def cylHfg : C(↑(cyl N) × unitInterval, ↑(cyl N)) :=
  ⟨fun p => (p.1.1, p.2 * p.1.2),
    Continuous.prodMk continuous_fst.fst
      (((continuous_subtype_val.comp continuous_snd).mul
        (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))).subtype_mk _)⟩

/-- `cylBot` carries `{σ}ᶜ` into `puncV x` (the bottom slice avoids the `σ`-fiber). -/
theorem cylBot_mapsTo (x : ↑(cyl N)) :
    Set.MapsTo (cylBot (N := N)) ({x.1}ᶜ : Set ↑N) (puncV x) :=
  fun _ ha => ha

/-- `cylProj` carries `puncV x` into `{σ}ᶜ` (projection of the punctured product). -/
theorem cylProj_mapsTo (x : ↑(cyl N)) :
    Set.MapsTo (cylProj (N := N)) (puncV x) ({x.1}ᶜ : Set ↑N) :=
  fun _ hp => hp

/-! ## §2. The piece iso `H_{n+1}(M, {σ}ᶜ) ≃ H_{n+1}(M×I, puncV x)` -/

/-- **The MV piece is the base local homology.** The bottom-inclusion pushforward
`RelativeHomology.map cylBot : H_{n+1}(M, {σ}ᶜ) → H_{n+1}(M×I, (M∖σ)×I)` is an isomorphism, its
inverse induced by the projection — the interval factor contracts. This computes the `puncV` piece of
the punctured-product MV cover as the local homology of the base. -/
def puncVPieceEquiv (x : ↑(cyl N)) (n : ℕ) :
    RelativeHomology (X := N) ({x.1}ᶜ : Set ↑N) (n + 1) ≃ₗ[ZMod 2]
      RelativeHomology (X := cyl N) (puncV x) (n + 1) :=
  LinearEquiv.ofBijective (RelativeHomology.map cylBot (cylBot_mapsTo x) (n + 1))
    (RelativeHomology.map_bijective_of_homotopyEquiv_pair
      cylBot (cylBot_mapsTo x) cylProj (cylProj_mapsTo x)
      cylHgf (fun _ ha _ => ha)
      (ContinuousMap.ext fun _ => rfl) (ContinuousMap.ext fun _ => rfl)
      cylHfg (fun _ hb _ => hb)
      (ContinuousMap.ext fun b => Prod.ext rfl (zero_mul b.2))
      (ContinuousMap.ext fun b => Prod.ext rfl (one_mul b.2)) n)

end

end SKEFTHawking.PoincareLefschetzRelFundClassCylinderPuncturedPiece
