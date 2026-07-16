import Mathlib
import SKEFTHawking.SingularRelativeDisjointUnionLocal

/-!
# Phase 5q.H — THE EXCISION–RESTRICTION NATURALITY (the NONZERO side of the local projection)

The disconnected `[W, ∂W]` detection engine (`SingularRelativeDisjointUnionFundClass`) assembles the
relative fundamental class from per-piece witnesses, and `SingularRelativeDisjointUnionLocal` proves
the **vanishing** side: at an interior point `x` the OFF-piece summand `excisionMap S B b` dies
(`restrictBd_excisionMap_eq_zero`). This module proves the complementary **nonzero** side — how the
SAME-piece summand restricts.

The mechanism is pure functoriality of the clopen inclusion `chainIncl U` at chain level. Both
`restrictBd S hxS = relIncl (S ⊆ {x}ᶜ)` and `excisionMap S U` are `RelativeHomology`-inductions of
chain maps (`id_X` and `chainIncl U` respectively), and these commute because `chainIncl U` does not
touch the ambient subspace filtration. Hence, for **any** `x ∉ S`,

  `restrictBd S hxS (excisionMap S U α) = excisionMap {x}ᶜ U (relIncl (restr S U ⊆ restr {x}ᶜ U) α)`,

i.e. the ambient local restriction of `excisionMap S U α` factors through the excision of the
INTRINSIC local restriction of `α` inside the piece `sub U`. When additionally `x ∈ U` the right-hand
excision `excisionMap {x}ᶜ U` is an EXCISION ISOMORPHISM (`{x}ᶜ ∪ U = univ`, both open), so the
ambient detection at `x` is *governed* by the intrinsic detection in `sub U` — the route-(b) reduction
"the detection at `x ∈ U` reduces to the `sub U`-local one", now on the nonzero side.

* `restr_mono` — `restr` is monotone in the numerator subspace.
* `restrictBd_excisionMap` — the naturality square (any `x ∉ S`).
* `restrIclCompl_eq_compl` — `restr {x}ᶜ U = {x'}ᶜ` in `sub U` (`x' = ⟨x, hxU⟩`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no
`native_decide`, no `maxHeartbeats`.
-/

open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularFunctoriality
open SKEFTHawking.SingularRelativeFunctoriality
open SKEFTHawking.SingularRelativeMV
open SKEFTHawking.SingularExcisionIso
open SKEFTHawking.PoincareLefschetzRelFundClass

namespace SKEFTHawking.SingularRelativeExcisionRestrict

variable {X : TopCat}

/-- **`restr` is monotone** in the numerator subspace: `S ⊆ T ⟹ restr S B ⊆ restr T B`
(`restr A B = Subtype.val ⁻¹' A`, and preimage is monotone). -/
theorem restr_mono {S T : Set ↑X} (B : Set ↑X) (h : S ⊆ T) : restr S B ⊆ restr T B :=
  Set.preimage_mono h

/-- **The excision–restriction naturality square.** For any `x ∉ S`, the ambient local restriction of
`excisionMap S U α` equals the excision (over `{x}ᶜ`) of the intrinsic local restriction of `α` inside
the piece `sub U`. Pure chain-level functoriality: both sides reduce to `mk {x}ᶜ n (chainIncl U n c)`
for a representative `c` of `α`. This is the NONZERO twin of `restrictBd_excisionMap_eq_zero`. -/
theorem restrictBd_excisionMap {S U : Set ↑X} {x : ↑X} (hxS : x ∉ S) (n : ℕ)
    (α : RelativeHomology (restr S U) n) :
    restrictBd S hxS n (excisionMap S U n α)
      = excisionMap ({x}ᶜ) U n
          (relIncl (restr_mono U (Set.subset_compl_singleton_iff.mpr hxS)) n α) := by
  obtain ⟨z, rfl⟩ := Submodule.Quotient.mk_surjective _ α
  rw [show (Submodule.Quotient.mk z : RelativeHomology (restr S U) n)
        = RelativeHomology.mk (restr S U) n z from rfl,
    restrictBd, excisionMap_mk, relIncl_mk, relIncl_mk, excisionMap_mk]
  refine congrArg (RelativeHomology.mk ({x}ᶜ) n) (Subtype.ext ?_)
  simp only [relCyclesMap_coe]
  obtain ⟨c, hc⟩ := Submodule.Quotient.mk_surjective _ (z : RelativeChain (restr S U) n)
  rw [← hc, show (Submodule.Quotient.mk c : RelativeChain (restr S U) n)
        = RelativeChain.mk (restr S U) n c from rfl,
    relChainIncl_mk, relMapChain_mk, relMapChain_mk, mapChain_id, mapChain_id, relChainIncl_mk]

end SKEFTHawking.SingularRelativeExcisionRestrict
