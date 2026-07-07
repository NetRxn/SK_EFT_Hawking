/-
# Phase 5q.H (E1 CSC-PD tower) — the M2-direct hcore closure skeleton (integral, non-circular)

Integral mirror of `SingularConnSquareCloseM2`. The connecting-square per-`K` cycle core `hcore`
`subHomConnectingInt U V (p+1) (legW K g) = openDuality (legδ K g)` closed by the **M2-direct route** —
reducing the LHS to the same explicit seam-transported `[∂zB]` class via the bottom-row MV cover-partition
chain action, **without** routing through the Kronecker-pairing / UC-non-degeneracy adjunction (which is
FIELD-dead over ℤ). The remaining geometric content is the seam-match `hmatch` (discharged by the direct
torsion-safe cap-Leibniz `capInt_leibniz` at the consumer).

Builds the seam-injectivity reduction `seam_eq_iffInt` (both seams are `LinearEquiv`s — coefficient-agnostic),
the M2-direct reduction `subHomConnecting_legW_eq_legW_of_mvConnectingInt`, and the `hmv` discharge from a
cover-partition + a seam-match `mvConnecting_eq_seamRHS_of_partitionInt`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularConnSquareLHSExplicitInt
import SKEFTHawking.SingularMvDeltaPartitionInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.SingularSubHomologyMVInt (subHomConnectingInt seamI)
open SKEFTHawking.SingularMayerVietorisLESInt (mvConnectingInt seamHomologyEquivInt)
open SKEFTHawking.SingularSubHomologyMV (cover_preimage)
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularCompactlySupportedOpenInt
open SKEFTHawking.SingularOpenDualityInt
open SKEFTHawking.SingularConnSquareLHSExplicitInt (subHomConnecting_legWInt)

namespace SKEFTHawking.SingularConnSquareCloseM2Int

variable {X : TopCat} [T2Space ↑X]

/-- **Seam-injectivity reduction of the connecting-square equation** (integral). Both seam maps `seamI`,
`seamHomologyEquivInt` are `LinearEquiv`s, so `seamI (seamHom cL) = seamI (seamHom cR) ↔ cL = cR` — the
connecting-square equation reduces to an equation in the doubly-nested seam representation. Coefficient-
agnostic (pure `LinearEquiv` injectivity — NO field/UC). -/
theorem seam_eq_iffInt (U V : Set ↑X) (n : ℕ)
    (cL cR : Homology (sub (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V))) n) :
    seamI U V n
        (seamHomologyEquivInt (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) n cL)
      = seamI U V n
          (seamHomologyEquivInt (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) n cR)
    ↔ cL = cR := by
  rw [(seamI U V n).injective.eq_iff,
    (seamHomologyEquivInt (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) n).injective.eq_iff]

/-- **M2-direct `hcore` reduction to the seam-transported `mvConnecting` identity** (integral). The
connecting-square per-`K` core `subHomConnectingInt (legW K g) = R` holds **iff** the bottom-row MV
connecting map of `legW K g` equals the double-seam-transport of `R`. Rewrites the LHS by the M2-direct
`subHomConnecting_legWInt` (= `seamI ∘ seamHom ∘ mvConnectingInt`) and applies the seam equivs. Non-circular
(through `mvConnectingInt`, **never** the Kronecker/UC route). -/
theorem subHomConnecting_legW_eq_legW_of_mvConnectingInt (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V)
    {k p : ℕ} (z₀ : SingularChainInt X (k + p + 1)) (hz₀ : chainBoundary X (k + p) z₀ = 0)
    (K : CompactsIn (U ∪ V)) (g : cohomGWInt (U ∪ V) k K) (R : Homology (sub (U ∩ V)) p)
    (hmv : mvConnectingInt (X := sub (U ∪ V)) (Subtype.val ⁻¹' U) (Subtype.val ⁻¹' V) p
          (cover_preimage U V hU hV) (legW (m := p) (hU.union hV) z₀ hz₀ K g)
        = (seamHomologyEquivInt (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) p).symm
            ((seamI U V p).symm R)) :
    subHomConnectingInt U V hU hV p (legW (m := p) (hU.union hV) z₀ hz₀ K g) = R := by
  rw [subHomConnecting_legWInt U V hU hV z₀ hz₀ K g, hmv, LinearEquiv.apply_symm_apply,
    LinearEquiv.apply_symm_apply]

/-- **M2-direct `hmv` discharge from a cover-partition + a seam-match** (integral). The `mvConnectingInt`
identity required by `subHomConnecting_legW_eq_legW_of_mvConnectingInt` is discharged from a cover-partition
`hw` of the class + the seam-match `hmatch` (the explicit `mvConnectingInt` of that partition — the `[∂zB]`
class — equals the double-seam-transport of `R`). The `[∂zB]` class enters only as a proof term (dodging the
`whnf` wall). The genuine remaining geometric content is `hmatch`. -/
theorem mvConnecting_eq_seamRHS_of_partitionInt (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ)
    (w : Homology (sub (U ∪ V)) (n + 1)) (R : Homology (sub (U ∩ V)) n)
    (zA : SingularChainInt (sub (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V)))) (n + 1))
    (zB : SingularChainInt (sub (Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V)))) (n + 1))
    (hz_cyc : chainIncl (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (n + 1) zA
        + chainIncl (Subtype.val ⁻¹' V) (n + 1) zB ∈ cycles (sub (U ∪ V)) (n + 1))
    (hw : w = Homology.mk (sub (U ∪ V)) (n + 1) ⟨_, hz_cyc⟩)
    (c : Homology (sub (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V))) n)
    (hcZ : mvConnectingInt (X := sub (U ∪ V)) (Subtype.val ⁻¹' U) (Subtype.val ⁻¹' V) n
          (cover_preimage U V hU hV) (Homology.mk (sub (U ∪ V)) (n + 1) ⟨_, hz_cyc⟩) = c)
    (hmatch : c
        = (seamHomologyEquivInt (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) n).symm
            ((seamI U V n).symm R)) :
    mvConnectingInt (X := sub (U ∪ V)) (Subtype.val ⁻¹' U) (Subtype.val ⁻¹' V) n
        (cover_preimage U V hU hV) w
      = (seamHomologyEquivInt (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) n).symm
          ((seamI U V n).symm R) := by
  subst hw
  rw [hcZ, hmatch]

end SKEFTHawking.SingularConnSquareCloseM2Int
