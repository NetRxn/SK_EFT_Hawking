/-
# Phase 5q.H (E1 CSC-PD tower) — seam-transport of `boundaryExtract` to the ambient (integral, brick 6e-c3)

The seam-transport bricks for the seam-match: `seamI`/`seamHomologyEquivInt` are `Homology.mapInt` of the
seam homeomorphisms (`subSeamHomeo`/`seamHomeo`, identity-on-`X` reassociations), so the seam-transported
`boundaryExtract` class realizes, on `chainIncl` to the ambient, to `∂(chainIncl B w)`:
  `chainIncl_S (subSeam# (seam# (boundaryExtract w))) = chainIncl_S (∂(chainIncl_B w))`.
Integral ports of the mod-2 `chainIncl_mapChain_*` (one-line `rw` via `mapChainInt_ambIncl` +
`mapChainInt_comp` functoriality). The LHS is exactly the ambient realization of the positive-form
`hmatch`'s LHS (`seamI(seamHom[∂zB])`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularConvexRadialBaseInt
import SKEFTHawking.SingularSubHomologyMVInt
import SKEFTHawking.SingularMayerVietorisLESInt

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.SingularSubHomologyMV (subSeamHomeo)
open SKEFTHawking.SingularMayerVietorisLES (seamHomeo)
open SKEFTHawking.SingularFunctorialityInt (mapChainInt mapChainInt_comp)
open SKEFTHawking.SingularConvexRadialBaseInt (mapChainInt_ambIncl)

namespace SKEFTHawking.SingularSeamTransportInt

variable {X : TopCat}

/-- **(c-3a)** Seam-transport `chainIncl` compatibility (subSeamHomeo), integral. -/
theorem chainIncl_mapChain_subSeamHomeoInt {S : Set ↑X} {R : Set ↑(sub S)} {T : Set ↑X} (hTS : T ⊆ S)
    (hmem : ∀ p : ↥(sub S), p ∈ R ↔ (p : ↑X) ∈ T) {n : ℕ} (x : SingularChainInt (sub R) n) :
    chainIncl T n (mapChainInt ⟨subSeamHomeo hTS hmem, (subSeamHomeo hTS hmem).continuous⟩ n x)
      = chainIncl S n (chainIncl R n x) := by
  rw [← mapChainInt_ambIncl, ← mapChainInt_ambIncl, ← mapChainInt_ambIncl,
    ← mapChainInt_comp, ← mapChainInt_comp]
  rfl

/-- **(c-3b)** Seam-transport `chainIncl` compatibility (seamHomeo), integral. -/
theorem chainIncl_mapChain_seamHomeoInt {Y : TopCat} (A B : Set ↑Y) {n : ℕ}
    (x : SingularChainInt (sub (restr A B)) n) :
    chainIncl (A ∩ B) n (mapChainInt ⟨seamHomeo A B, (seamHomeo A B).continuous⟩ n x)
      = chainIncl B n (chainIncl (restr A B) n x) := by
  rw [← mapChainInt_ambIncl, ← mapChainInt_ambIncl, ← mapChainInt_ambIncl,
    ← mapChainInt_comp, ← mapChainInt_comp]
  rfl

/-- **(c-3c)** The double-seam-transported `boundaryExtract` realizes to the ambient boundary of the
`chainIncl B`-lift (integral). Chains (c-3a)+(c-3b)+`chainIncl_boundaryExtract`+`chainIncl_chainBoundary`. -/
theorem chainIncl_seam_boundaryExtractInt {S : Set ↑X} {A B : Set ↑(sub S)} {T : Set ↑X}
    (hTS : T ⊆ S) (hmem : ∀ p : ↥(sub S), p ∈ A ∩ B ↔ (p : ↑X) ∈ T) {n : ℕ}
    (w : relCycleLift (restr A B) n) :
    chainIncl T n (mapChainInt ⟨subSeamHomeo hTS hmem, (subSeamHomeo hTS hmem).continuous⟩ n
        (mapChainInt ⟨seamHomeo A B, (seamHomeo A B).continuous⟩ n
          (boundaryExtract (restr A B) n w)))
      = chainIncl S n (chainBoundary (sub S) n
          (chainIncl B (n + 1) (w : SingularChainInt (sub B) (n + 1)))) := by
  rw [chainIncl_mapChain_subSeamHomeoInt, chainIncl_mapChain_seamHomeoInt,
    chainIncl_boundaryExtract, chainIncl_chainBoundary]

end SKEFTHawking.SingularSeamTransportInt
