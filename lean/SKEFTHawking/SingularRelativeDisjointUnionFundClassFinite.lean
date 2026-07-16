import Mathlib
import SKEFTHawking.SingularRelativeDisjointUnionFundClass

/-!
# Phase 5q.H — THE FINITE-PARTITION ASSEMBLY (route (b), the `k`-component generalization)

The binary clopen-split engine (`SingularRelativeDisjointUnionFundClass.hasRelFundClass_of_clopen_split`)
assembles the disconnected relative fundamental class from a TWO-piece clopen split `X = U ⊔ Uᶜ`. This
module generalizes it to a **finite clopen partition** `X = ⊔_{i : ι} U i` (ι a `Fintype`): given a
per-piece class `α i` on each clopen piece, each detecting the interior generator on *its own* piece
(the folded `RestrictsToRelGenOn` predicate against the ambient `gen`), the SUM
`∑ i, excisionMap S (U i) (α i)` restricts to the generator at **every** interior point.

The mechanism is identical to the binary case, applied `Finset.sum`-wise: at an interior point `x` lying
in the (unique, by disjointness) piece `U j`, `restrictBd` is additive (`map_sum`), every off-piece
summand dies (`restrictBd_excisionMap_eq_zero`, needing only `x ∉ U i`), and the surviving `U j`-summand
detects the generator by `hdet j`. Connectedness-free; no homeomorphism transport.

This is what the disconnected cylinder `D` field needs: `cylW M = ⊔_{c : ConnectedComponents M} (C_c × I)`
is a finite clopen partition (compact charted ⟹ finitely many components, each clopen), and each piece's
detection witness is the excision-bridge keystone `restrictsToRelGenOn_component` on the connected
component `C_c` — so the `k`-component `D` assembles with NO disconnected-specific posit.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no
`native_decide`, no `maxHeartbeats`.
-/

open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularExcisionIso
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.SingularRelativeDisjointUnionLocal
open SKEFTHawking.SingularRelativeDisjointUnionFundClass

namespace SKEFTHawking.SingularRelativeDisjointUnionFundClassFinite

variable {X : TopCat}

/-- **The engine assembles the disconnected relative fundamental class from a finite clopen partition.**
For a finite family of clopen pieces `U : ι → Set X` that COVER `X` and are pairwise DISJOINT, and
per-piece classes `α i` each detecting the interior generator on its own piece (the folded
`RestrictsToRelGenOn` predicate over the ambient `gen`), the sum `∑ i, excisionMap S (U i) (α i)`
restricts to the generator at **every** interior point — hence `HasRelFundClass S gen`. At each interior
point `x` (lying in the unique piece `U j`) every off-piece summand dies
(`restrictBd_excisionMap_eq_zero`, from `x ∉ U i` for `i ≠ j`), leaving the `U j`-detection. The
`k`-component analogue of `hasRelFundClass_of_clopen_split_folded`; connectedness-free, no homeo
transport. -/
theorem hasRelFundClass_of_finite_clopen_partition {ι : Type*} [Fintype ι] {m : ℕ}
    (U : ι → Set ↑X) (_hU : ∀ i, IsClopen (U i))
    (hdisj : ∀ i j, i ≠ j → Disjoint (U i) (U j)) (hcover : ∀ x : ↑X, ∃ i, x ∈ U i)
    (S : Set ↑X)
    (gen : ∀ x : ↑X, x ∉ S → (RelativeHomology ({x}ᶜ) (m + 2) ≃ₗ[ZMod 2] ZMod 2))
    (α : ∀ i, RelativeHomology (restr S (U i)) (m + 2))
    (hdet : ∀ i, RestrictsToRelGenOn S gen (· ∈ U i) (excisionMap S (U i) (m + 2) (α i))) :
    HasRelFundClass S gen := by
  refine ⟨∑ i, excisionMap S (U i) (m + 2) (α i), ?_⟩
  intro x hx
  obtain ⟨j, hj⟩ := hcover x
  rw [map_sum, Finset.sum_eq_single j]
  · exact hdet j x hx hj
  · intro i _ hij
    refine restrictBd_excisionMap_eq_zero hx ?_ (m + 2) (α i)
    intro hxUi
    exact (hdisj i j hij).ne_of_mem hxUi hj rfl
  · intro h
    exact absurd (Finset.mem_univ j) h

end SKEFTHawking.SingularRelativeDisjointUnionFundClassFinite
