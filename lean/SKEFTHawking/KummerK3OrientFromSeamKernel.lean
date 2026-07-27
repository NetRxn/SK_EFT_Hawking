/-
# Phase 5q.H — `orientInput` REPLACED: the `K3` orientation atom from ONE seam relation

`KummerK3E1Package.KummerK3H3TwoTorsionFree` (`orientInput`) never mattered for its own sake — its
*only* consumer is `nonempty_intOrientation_kummerK3`, i.e. it exists to produce the `orient` field
`IntOrientation KummerK3`. This module produces that field from a **completely different and much
weaker-looking** input, bypassing `orientInput` entirely:

> the sixteen seam `ℝP³` classes are ℤ-linearly DEPENDENT in `H₃(Q;ℤ)`
> (`LinearMap.ker qSeamCoord3 ≠ ⊥`)  ⟹  `Nonempty (IntOrientation KummerK3)`.

## Why this is the right reduction

Three unconditional in-tree facts line up exactly:

1. `KummerQTopVanish.h4K3EquivKerQSeamCoord3 : H₄(K3;ℤ) ≃ₗ[ℤ] ker qSeamCoord3` — the degree-4/3 MV
   window of the weld with both degree-4 pieces dead, so the seam kernel **computes** `H₄(K3;ℤ)`.
2. `KummerQTopVanish.k3_h4_free : Module.Free ℤ (H₄(K3;ℤ))`.
3. `KummerWeldConnected.instPreconnectedKummerK3` — the welded carrier is connected, so
   `H₄(K3;ℤ/2) ≅ ℤ/2` (`SingularFundamentalClass.localDegree_bijective`).

Feeding (1)+(2)+(3) into the ambient-generic
`IntOrientationFreeTopHomology.nonempty_intOrientation_of_free_nontrivial` — a basis vector of a free
nontrivial `H₄(M;ℤ)` is not 2-divisible, hence survives mod 2, hence IS `[M]₂`, hence `[M]₂` lifts —
gives the atom. Nothing about `H₃` is used anywhere in the chain.

## What this changes about the residual

The old residual was a **2-saturation** statement about `im qSeamCoord3` (equivalently, by
`KummerK3H3SeamWindow`, that `H₃(K3;ℤ)` has no 2-torsion). The new residual is a single
**existential**: one nonzero integer vector `v ∈ ℤ¹⁶` with `qSeamCoord3 v = 0`. Geometrically the
expected witness is `v = (1,…,1)`: the sixteen boundary `ℝP³`s of the compact 4-manifold `Q` jointly
bound, `Σᵢ[∂ᵢQ] = ∂[Q,∂Q] = 0`. §3 records that phrasing directly.

The two are not comparable a priori and neither implies the other formally here; what is claimed is
only that **either** produces the `orient` atom, and that the existential form is the one a
`Q`-side or `T⁴°`-side geometric computation can hit. (The `T⁴°` mirror of exactly this existential
— the sixteen boundary `S³`s of `T⁴°` are ℤ-linearly dependent — is proved unconditionally in
`KummerPunctureSeamRelation`.)

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/
axiom.
-/
import Mathlib
import SKEFTHawking.IntOrientationFreeTopHomology
import SKEFTHawking.KummerWeldConnected
import SKEFTHawking.KummerQTopVanish
import SKEFTHawking.KummerK3SeamWindingParity

namespace SKEFTHawking.KummerK3OrientFromSeamKernel

open scoped SKEFTHawking.KummerK3E1Package
open SKEFTHawking.SingularHomologyInt (Homology IntOrientation)
open SKEFTHawking.KummerK7Opener (KummerK3top)
open SKEFTHawking.KummerWeld (KummerK3 EIndex)
open SKEFTHawking.KummerK3H3SeamWindow (qSeamCoord3)
open SKEFTHawking.KummerQTopVanish (h4K3EquivKerQSeamCoord3 k3_h4_free)

/-! ## §1. A nontrivial seam kernel is a nontrivial `H₄(K3;ℤ)` -/

/-- **`ker qSeamCoord3 ≠ ⊥ ⟹ H₄(K3;ℤ)` nontrivial** — transport along the banked
`h4K3EquivKerQSeamCoord3`, the isomorphism that makes the sixteen seam coordinates *compute* the top
integral homology of the weld. -/
theorem nontrivial_h4K3_of_ker_ne_bot (h : LinearMap.ker qSeamCoord3 ≠ ⊥) :
    Nontrivial (Homology KummerK3top 4) := by
  haveI : Nontrivial (LinearMap.ker qSeamCoord3) := Submodule.nontrivial_iff_ne_bot.mpr h
  exact h4K3EquivKerQSeamCoord3.toEquiv.nontrivial

/-! ## §2. The orientation atom -/

/-- **THE `orient` ATOM OF THE WELDED `K3`, WITHOUT `orientInput`.** One nonzero element of
`ker qSeamCoord3` produces the integral fundamental class with its mod-2 compatibility.

The chain, all unconditional except the hypothesis: the seam kernel computes `H₄(K3;ℤ)`
(`h4K3EquivKerQSeamCoord3`), which is free (`k3_h4_free`), so it has a non-2-divisible basis vector,
whose mod-2 reduction is therefore nonzero; the weld is connected
(`KummerWeldConnected.instPreconnectedKummerK3`) so `H₄(K3;ℤ/2) ≅ ℤ/2` has a *unique* nonzero class,
namely `[K3]₂`; hence `[K3]₂` is in the range of `redHomology 4`, which by
`IntOrientationMod2Lift.nonempty_intOrientation_iff_mem_range` IS the datum. -/
theorem nonempty_intOrientation_of_ker_ne_bot (h : LinearMap.ker qSeamCoord3 ≠ ⊥) :
    Nonempty (IntOrientation KummerK3) := by
  haveI := k3_h4_free
  haveI := nontrivial_h4K3_of_ker_ne_bot h
  exact SKEFTHawking.IntOrientationFreeTopHomology.nonempty_intOrientation_of_free_nontrivial

/-- **The converse** — the orientation atom forces a nontrivial seam kernel. `IntOrientation` carries
`fundClass ≠ 0` (its reduction is `[K3]₂ ≠ 0`), and the seam kernel computes `H₄(K3;ℤ)`. -/
theorem ker_ne_bot_of_nonempty_intOrientation (h : Nonempty (IntOrientation KummerK3)) :
    LinearMap.ker qSeamCoord3 ≠ ⊥ := by
  haveI : Nontrivial (Homology KummerK3top 4) :=
    SKEFTHawking.IntOrientationFreeTopHomology.nontrivial_h4_of_nonempty_intOrientation h
  exact Submodule.nontrivial_iff_ne_bot.mp h4K3EquivKerQSeamCoord3.toEquiv.symm.nontrivial

/-- **THE RESIDUAL, LOSSLESSLY.** The `K3` orientation atom exists **iff** the sixteen seam `ℝP³`
classes are ℤ-linearly dependent in `H₃(Q;ℤ)`. Nothing is given away by §2's sufficient form: the
degree-4 route is not an over-approximation but the exact content of the datum on this carrier
(freeness of `H₄(K3;ℤ)` and connectedness of the weld are both unconditional in tree, so the generic
`↔` of `IntOrientationFreeTopHomology.nonempty_intOrientation_iff_nontrivial_h4` applies with no
hypotheses left over). -/
theorem nonempty_intOrientation_iff_ker_ne_bot :
    Nonempty (IntOrientation KummerK3) ↔ LinearMap.ker qSeamCoord3 ≠ ⊥ :=
  ⟨ker_ne_bot_of_nonempty_intOrientation, nonempty_intOrientation_of_ker_ne_bot⟩

/-! ## §3. The geometric phrasing: ONE relation among the sixteen seam classes -/

/-- **The `orient` atom from a single explicit seam relation.** If some nonzero integer vector
`v ∈ ℤ¹⁶` has `qSeamCoord3 v = 0` — i.e. the sixteen boundary-`ℝP³` classes of `∂Q` satisfy one
nontrivial ℤ-linear relation in `H₃(Q;ℤ)` — the orientation atom follows. The expected witness is
`v = (1,…,1)`, the relation `Σᵢ [∂ᵢQ] = 0` coming from the sixteen boundary components jointly
bounding `Q`. -/
theorem nonempty_intOrientation_of_seam_relation (v : EIndex → ℤ) (hv : v ≠ 0)
    (h0 : qSeamCoord3 v = 0) : Nonempty (IntOrientation KummerK3) := by
  refine nonempty_intOrientation_of_ker_ne_bot (fun hbot => hv ?_)
  have hmem : v ∈ LinearMap.ker qSeamCoord3 := LinearMap.mem_ker.mpr h0
  rw [hbot, Submodule.mem_bot] at hmem
  exact hmem

/-! ## §4. The E1 atom triple with `orientInput` removed -/

open SKEFTHawking.KummerK3E1Package
open SKEFTHawking.SingularCohomologyInt (IntPoincareDuality)
open SKEFTHawking.SingularHomologyInt (intFundamentalClassOfIntOrientation)

/-- **The `K3` E1 atom triple from the seam kernel plus Poincaré duality.** The `orientInput` slot of
`KummerK3E1Package.kummerK3E1Atoms_of_residuals` is gone: §2 supplies the `orient` field, `h1Free` is
already unconditional (`KummerK3SeamWindingParity.free_h1K3_uncond`), and only the duality
(unimodularity) atom remains a hypothesis. This is the `orientInput`-free replacement for
`KummerK3SeamWindingParity.nonempty_kummerK3E1Atoms_of_orient_pd`. -/
theorem nonempty_kummerK3E1Atoms_of_ker_pd (hker : LinearMap.ker qSeamCoord3 ≠ ⊥)
    (pdInput : ∀ o : IntOrientation KummerK3,
      Nonempty (IntPoincareDuality (intFundamentalClassOfIntOrientation o))) :
    Nonempty KummerK3E1Atoms := by
  haveI := SKEFTHawking.KummerK3SeamWindingParity.free_h1K3_uncond
  obtain ⟨o⟩ := nonempty_intOrientation_of_ker_ne_bot hker
  obtain ⟨pd⟩ := pdInput o
  exact ⟨⟨o, kummerK3IntH2Basis, pd, rfl⟩⟩

end SKEFTHawking.KummerK3OrientFromSeamKernel
