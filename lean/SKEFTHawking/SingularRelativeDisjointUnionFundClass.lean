import Mathlib
import SKEFTHawking.SingularRelativeDisjointUnionLocal

/-!
# Phase 5q.H — THE ENGINE ASSEMBLES THE DISCONNECTED `HasRelFundClass` (route (b) assembly)

Combining the relative clopen-split engine (`SingularRelativeDisjointUnionHn`) with its local
projection (`SingularRelativeDisjointUnionLocal`): for a clopen decomposition `X = U ⊔ Uᶜ`, a
relative fundamental class of the pair `(X, S)` **assembles from per-piece classes**. Given
`αU ∈ Hₙ(U, S∩U)` and `αUᶜ ∈ Hₙ(Uᶜ, S∩Uᶜ)` each detecting the interior generator on *its own* piece
(phrased over the ambient via `excisionMap`), the sum `excisionMap S U αU + excisionMap S Uᶜ αUᶜ`
restricts to the generator at **every** interior point: at `x ∈ U` the `Uᶜ`-summand dies
(`restrictBd_excisionMap_eq_zero`), leaving the `U`-detection, and symmetrically at `x ∈ Uᶜ`.

This is the connectedness-free heart of route (b): the disconnected `[W, ∂W]` is the sum of the
per-component classes, and the detection at any interior point localizes to the single clopen piece
containing it — **no homeomorphism transport**, only the engine's clopen additivity + local
projection. The residual it isolates is the per-piece detection hypothesis (`hdetU`/`hdetUc`) — the
connected fundamental class of each clopen piece, which the connected in-tree machinery supplies for
each component.

* `hasRelFundClass_of_clopen_split` — the binary assembly (either interior point lands in one piece).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`, no new axiom, no
`native_decide`, no `maxHeartbeats`.
-/

open SKEFTHawking.SingularHomologyMod2
open SKEFTHawking.SingularRelativeHomologyMod2
open SKEFTHawking.SingularExcisionIso
open SKEFTHawking.PoincareLefschetzRelFundClass
open SKEFTHawking.SingularRelativeDisjointUnionHn
open SKEFTHawking.SingularRelativeDisjointUnionLocal

namespace SKEFTHawking.SingularRelativeDisjointUnionFundClass

variable {X : TopCat}

/-- **The engine assembles the disconnected relative fundamental class.** For a clopen `U ⊆ X` and a
subspace `S`, if `αU` detects the interior generator on `U` and `αUᶜ` detects it on `Uᶜ` (each phrased
over the ambient via `excisionMap`), then the sum `excisionMap S U αU + excisionMap S Uᶜ αUᶜ`
restricts to the generator at **every** interior point — hence `HasRelFundClass S gen`. At each
interior point the off-piece summand dies (`restrictBd_excisionMap_eq_zero`), so the detection
localizes to the piece containing the point. Connectedness-free; no homeomorphism transport. -/
theorem hasRelFundClass_of_clopen_split {m : ℕ} {U : Set ↑X} (_hU : IsClopen U) (S : Set ↑X)
    (gen : ∀ x : ↑X, x ∉ S → (RelativeHomology ({x}ᶜ) (m + 2) ≃ₗ[ZMod 2] ZMod 2))
    (αU : RelativeHomology (restr S U) (m + 2))
    (αUc : RelativeHomology (restr S Uᶜ) (m + 2))
    (hdetU : ∀ (x : ↑X) (hx : x ∉ S), x ∈ U →
      restrictBd S hx (m + 2) (excisionMap S U (m + 2) αU) = (gen x hx).symm 1)
    (hdetUc : ∀ (x : ↑X) (hx : x ∉ S), x ∈ Uᶜ →
      restrictBd S hx (m + 2) (excisionMap S Uᶜ (m + 2) αUc) = (gen x hx).symm 1) :
    HasRelFundClass S gen := by
  refine ⟨excisionMap S U (m + 2) αU + excisionMap S Uᶜ (m + 2) αUc, ?_⟩
  intro x hx
  by_cases hxU : x ∈ U
  · rw [map_add, restrictBd_excisionMap_eq_zero hx (by simpa using hxU) (m + 2) αUc, add_zero]
    exact hdetU x hx hxU
  · rw [map_add, restrictBd_excisionMap_eq_zero hx hxU (m + 2) αU, zero_add]
    exact hdetUc x hx hxU

end SKEFTHawking.SingularRelativeDisjointUnionFundClass
