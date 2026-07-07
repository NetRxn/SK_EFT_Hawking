/-
# Phase 5q.H (E1 CSC-PD tower) — the M2-direct LHS of the integral connecting square (core skeleton)

Integral mirror of `SingularConnSquareLHSExplicit` (core factorisations + skeleton). The LHS of the
integral Poincaré-duality connecting square is `subHomConnectingInt U V hU hV (p+1) (legW K g) ∈
Homology (sub (U ∩ V)) (p+1)`. This file expresses it explicitly through the bottom-row Mayer–Vietoris
cover-partition chain action (the **M2-direct route**), so it can be matched chain-level against the
relative-MV (RHS) leg via cap-Leibniz — the torsion-safe integral route (NOT the mod-2 field-UC route).

Builds the definitional factorisations `subHomConnectingInt = seamI ∘ mvDeltaInt = seamI ∘
seamHomologyEquivInt ∘ mvConnectingInt`, the M2-direct skeleton `subHomConnecting_cover_partitionInt`
(carrying the `[∂zB]`-class abstractly as `c` with the M2 equation as a hypothesis — dodging the `whnf`
wall), and the per-compact `subHomConnecting_legWInt`. The cover-fine subdivision-invariance tools + the
concrete `hmatch` cap-Leibniz assembly are deferred to the consumer site.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularSubHomologyMVInt
import SKEFTHawking.SingularMvDeltaPartitionInt
import SKEFTHawking.SingularOpenDualityInt

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularExcisionIso (restr)
open SKEFTHawking.SingularSubHomologyMVInt (subHomConnectingInt seamI)
open SKEFTHawking.SingularMayerVietorisLESInt (mvDeltaInt mvConnectingInt seamHomologyEquivInt)
open SKEFTHawking.SingularSubHomologyMV (cover_preimage)
open SKEFTHawking.SingularCompactsInOpen
open SKEFTHawking.SingularCompactlySupportedOpenInt
open SKEFTHawking.SingularOpenDualityInt

namespace SKEFTHawking.SingularConnSquareLHSExplicitInt

variable {X : TopCat} [T2Space ↑X]

/-- The bottom-row integral MV connecting map `subHomConnectingInt = seamI ∘ mvDeltaInt` (definitional). -/
theorem subHomConnecting_eq_seamI_mvDeltaInt (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ)
    (w : Homology (sub (U ∪ V)) (n + 1)) :
    subHomConnectingInt U V hU hV n w
      = seamI U V n
          (mvDeltaInt (X := sub (U ∪ V)) (Subtype.val ⁻¹' U) (Subtype.val ⁻¹' V) n
            (cover_preimage U V hU hV) w) := rfl

/-- `subHomConnectingInt = seamI ∘ seamHomologyEquivInt ∘ mvConnectingInt` (unfold `mvDeltaInt`;
definitional). The pre-seam form exposing `mvConnectingInt`, whose cover-partition chain action is
`mvConnecting_cover_partition` — the chain-level handle on the `[∂zB]`-class. -/
theorem subHomConnecting_eq_seamI_seamHom_mvConnectingInt (U V : Set ↑X) (hU : IsOpen U)
    (hV : IsOpen V) (n : ℕ) (w : Homology (sub (U ∪ V)) (n + 1)) :
    subHomConnectingInt U V hU hV n w
      = seamI U V n
          (seamHomologyEquivInt (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) n
            (mvConnectingInt (X := sub (U ∪ V)) (Subtype.val ⁻¹' U) (Subtype.val ⁻¹' V) n
              (cover_preimage U V hU hV) w)) := rfl

/-- **M2-direct LHS skeleton** (integral). On the class of a cover-partitioned cycle `z = chainIncl
(val⁻¹U) zA + chainIncl (val⁻¹V) zB` of `sub (U ∪ V)`, `subHomConnectingInt` equals `seamI` of
`seamHomologyEquivInt` of the `[∂zB]`-class `c` (carried abstractly with the M2 equation
`mvDelta_cover_partition` as `hc` — binds the doubly-nested subspace as a unification variable, dodging
the `whnf` wall). -/
theorem subHomConnecting_cover_partitionInt (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) (n : ℕ)
    (zA : SingularChainInt (sub (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V)))) (n + 1))
    (zB : SingularChainInt (sub (Subtype.val ⁻¹' V : Set ↑(sub (U ∪ V)))) (n + 1))
    (hz_cyc : chainIncl (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (n + 1) zA
        + chainIncl (Subtype.val ⁻¹' V) (n + 1) zB ∈ cycles (sub (U ∪ V)) (n + 1))
    (c : Homology (sub (restr (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V))) n)
    (hc : mvDeltaInt (X := sub (U ∪ V)) (Subtype.val ⁻¹' U) (Subtype.val ⁻¹' V) n
          (cover_preimage U V hU hV) (Homology.mk (sub (U ∪ V)) (n + 1) ⟨_, hz_cyc⟩)
        = seamHomologyEquivInt (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) n c) :
    subHomConnectingInt U V hU hV n (Homology.mk (sub (U ∪ V)) (n + 1) ⟨_, hz_cyc⟩)
      = seamI U V n
          (seamHomologyEquivInt (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) n c) := by
  rw [subHomConnecting_eq_seamI_mvDeltaInt, hc]

/-- **M2-direct LHS for the per-compact duality leg** (integral). The bottom-row MV connecting map
applied to `legW K g` (the LHS of the connecting square) factors as `seamI ∘ seamHomologyEquivInt ∘
mvConnectingInt` of `legW K g`. -/
theorem subHomConnecting_legWInt (U V : Set ↑X) (hU : IsOpen U) (hV : IsOpen V) {k p : ℕ}
    (z₀ : SingularChainInt X (k + p + 1)) (hz₀ : chainBoundary X (k + p) z₀ = 0)
    (K : CompactsIn (U ∪ V)) (g : cohomGWInt (U ∪ V) k K) :
    subHomConnectingInt U V hU hV p (legW (m := p) (hU.union hV) z₀ hz₀ K g)
      = seamI U V p
          (seamHomologyEquivInt (Subtype.val ⁻¹' U : Set ↑(sub (U ∪ V))) (Subtype.val ⁻¹' V) p
            (mvConnectingInt (X := sub (U ∪ V)) (Subtype.val ⁻¹' U) (Subtype.val ⁻¹' V) p
              (cover_preimage U V hU hV) (legW (m := p) (hU.union hV) z₀ hz₀ K g))) :=
  subHomConnecting_eq_seamI_seamHom_mvConnectingInt U V hU hV p (legW (m := p) (hU.union hV) z₀ hz₀ K g)

end SKEFTHawking.SingularConnSquareLHSExplicitInt
