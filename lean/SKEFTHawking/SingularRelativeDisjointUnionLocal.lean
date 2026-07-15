import Mathlib
import SKEFTHawking.SingularRelativeDisjointUnionHn
import SKEFTHawking.SingularRelativeMV
import SKEFTHawking.SingularMayerVietoris
import SKEFTHawking.PoincareLefschetzRelFundClass

/-!
# Phase 5q.H — THE ENGINE'S LOCAL PROJECTION (route (b) mechanism: off-piece classes die)

The relative clopen-split engine (`SingularRelativeDisjointUnionHn`) decomposes
`Hₙ(X, S) ≅ Hₙ(U, S∩U) × Hₙ(Uᶜ, S∩Uᶜ)`. This module proves the **local** counterpart that the
disconnected `[W, ∂W]` detection needs: at an interior point `x` lying in the clopen piece `U`, the
local restriction `restrictBd` kills every class coming from the *other* piece `Uᶜ`.

The reason is elementary and needs no clopen hypothesis, only `x ∉ B`: a class `excisionMap S B b`
is represented by a `B`-valued chain, and `B ⊆ {x}ᶜ`, so that chain becomes a **subspace chain** of
`{x}ᶜ` — hence `0` in the local relative homology `Hₙ(X, X∖x)`. Consequently the detection of the
disconnected class at `x` reduces to the piece `U` containing `x` (`restrictBd_relSplitHn`): the
off-component summands vanish, exactly the "the OTHER components' classes die under the clopen
restriction (the engine's projection)" step of route (b).

* `relIncl_mk_eq_zero_of_relMapZero` — a relative class whose `id`-pushforward into the enlarging
  subspace `T` is `0` dies under `relIncl (S ⊆ T)`.
* `restrictBd_excisionMap_eq_zero` — the off-piece vanishing under local restriction.
* `restrictBd_relSplitHn` — the detection at `x ∈ U` reduces to the `U`-summand.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no
`native_decide`, no `maxHeartbeats`.
-/

open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularRelativeFunctoriality
open SKEFTHawking.SingularRelativeMV
open SKEFTHawking.SingularExcisionIso
open SKEFTHawking.SingularMayerVietoris
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.SingularRelativeDisjointUnionHn

namespace SKEFTHawking.SingularRelativeDisjointUnionLocal

variable {X : TopCat}

/-- **A relative class with vanishing `id`-pushforward dies under `relIncl`.** If the `id`-induced
relative-chain pushforward of `(z : RelativeChain S n)` into the enlarging subspace `T` is `0`, then
including `Hₙ(X, S) → Hₙ(X, T)` sends `[z]` to `0`. -/
theorem relIncl_mk_eq_zero_of_relMapZero {S T : Set ↑X} (h : S ⊆ T) (n : ℕ) (z : relCycles S n)
    (hz : relMapChain (ContinuousMap.id ↑X) (fun _ hx => h hx) n (z : RelativeChain S n) = 0) :
    relIncl h n (RelativeHomology.mk S n z) = 0 := by
  rw [relIncl, show RelativeHomology.mk S n z = Submodule.Quotient.mk z from rfl,
    RelativeHomology.map_mk]
  have hz0 : relCyclesMap (ContinuousMap.id ↑X) (fun _ hx => h hx) n z = 0 := by
    refine Subtype.ext ?_
    rw [relCyclesMap_coe, ZeroMemClass.coe_zero]; exact hz
  rw [hz0]
  exact Submodule.Quotient.mk_zero _

/-- **Off-piece classes die under local restriction.** For a subspace `B ⊆ X` and an interior point
`x ∉ B` (with `x ∉ S`), the local restriction `restrictBd` at `x` annihilates every image
`excisionMap S B b`: the `B`-valued representing chain lies in `{x}ᶜ` (`B ⊆ {x}ᶜ`), so it is `0` in
`Hₙ(X, X∖x)`. This is the engine's projection killing the off-component classes in the disconnected
`[W, ∂W]` detection. -/
theorem restrictBd_excisionMap_eq_zero {S B : Set ↑X} {x : ↑X} (hxS : x ∉ S) (hxB : x ∉ B) (n : ℕ)
    (b : RelativeHomology (restr S B) n) :
    restrictBd S hxS n (excisionMap S B n b) = 0 := by
  obtain ⟨zb, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  obtain ⟨cb, hcb⟩ := Submodule.Quotient.mk_surjective _ (zb : RelativeChain (restr S B) n)
  rw [show (Submodule.Quotient.mk zb : RelativeHomology (restr S B) n)
      = RelativeHomology.mk (restr S B) n zb from rfl, excisionMap_mk,
    show restrictBd S hxS n = relIncl (Set.subset_compl_singleton_iff.mpr hxS) n from rfl]
  refine relIncl_mk_eq_zero_of_relMapZero (Set.subset_compl_singleton_iff.mpr hxS) n _ ?_
  -- the underlying relative chain is `relChainIncl S B n ↑zb = mk S (chainIncl B cb)`
  have hchain : relChainIncl S B n (zb : RelativeChain (restr S B) n)
      = RelativeChain.mk S n (chainIncl B n cb) := by
    rw [← hcb]; exact relChainIncl_mk S B n cb
  show relMapChain (ContinuousMap.id ↑X) _ n
      (relChainIncl S B n (zb : RelativeChain (restr S B) n)) = 0
  rw [hchain, relMapChain_mk, mapChain_id, RelativeChain.mk_eq_zero_iff]
  exact subspaceChains_mono (Set.subset_compl_singleton_iff.mpr hxB) n ⟨cb, rfl⟩

/-- **The detection at `x ∈ U` reduces to the `U`-summand.** For a clopen `U` and an interior point
`x ∈ U` (so `x ∉ Uᶜ`, `x ∉ S`), the local restriction of the split class `relSplitHn U S n (a, b)`
equals that of its `U`-part alone — the `Uᶜ`-part dies (`restrictBd_excisionMap_eq_zero`). This is the
route-(b) reduction "the detection reduces to the `C(σ)`-local one". -/
theorem restrictBd_relSplitHn {S U : Set ↑X} {x : ↑X} (hxS : x ∉ S) (hxU : x ∈ U) (n : ℕ)
    (a : RelativeHomology (restr S U) n) (b : RelativeHomology (restr S Uᶜ) n) :
    restrictBd S hxS n (relSplitHn U S n (a, b)) = restrictBd S hxS n (excisionMap S U n a) := by
  have hxUc : x ∉ Uᶜ := by simpa using hxU
  rw [relSplitHn_apply, map_add, restrictBd_excisionMap_eq_zero hxS hxUc n b, add_zero]

end SKEFTHawking.SingularRelativeDisjointUnionLocal
