import Mathlib
import SKEFTHawking.SingularDualityFinrank
import SKEFTHawking.SingularRelativeUCSurj

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD6f-b1) — the perfect-pairing Kronecker `LinearEquiv`

Over the field `ℤ/2` the relative Kronecker pairing
`relKroneckerH S : Hᵏ(M,S) → (Hₖ(M,S))^*` is a **bijection** — injective by universal coefficients
(`SingularDualityFinrank.relKroneckerH_injective`, finite-dim-free UC) and surjective by the finite-dim-free
field surjectivity (`SingularRelativeUCSurj.relKroneckerH_surjective_field`). This packages the two halves
into a `LinearEquiv`
  `relKroneckerHEquiv S N : Hᵏ(M,S) ≃ₗ (Hₖ(M,S))^*`,
the perfect pairing that carries the **homology** Mayer–Vietoris long exact sequence to the **cohomology**
side by `dualMap`-conjugation (`SingularRelativeCohomologyMVConnecting` builds the cohomology connecting
map this way — no contravariant excision, no finite-dimensionality).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularRelativePairing SKEFTHawking.SingularDualityFinrank
  SKEFTHawking.SingularRelativeUCSurj

namespace SKEFTHawking.SingularRelativeKroneckerEquiv

variable {X : TopCat}

/-- **The perfect-pairing Kronecker isomorphism** `Hᵏ(M,S) ≃ (Hₖ(M,S))^*` over `ℤ/2` (`k = N+1`):
injective (UC) + surjective (field UC), both finite-dim-free. -/
noncomputable def relKroneckerHEquiv (S : Set X) (N : ℕ) :
    RelativeCohomology S (N + 1) ≃ₗ[ZMod 2] (RelativeHomology S (N + 1) →ₗ[ZMod 2] ZMod 2) :=
  LinearEquiv.ofBijective (relKroneckerH S (N := N))
    ⟨relKroneckerH_injective S, relKroneckerH_surjective_field S⟩

@[simp] theorem relKroneckerHEquiv_apply (S : Set X) (N : ℕ) (ω : RelativeCohomology S (N + 1)) :
    relKroneckerHEquiv S N ω = relKroneckerH S (N := N) ω :=
  rfl

/-- The defining round-trip of the symm direction in `relKroneckerH` form: `⟨(symm φ), ·⟩ = φ`. The
load-bearing identity for the cohomology-MV connecting-map adjunction. -/
theorem relKroneckerH_symm (S : Set X) (N : ℕ)
    (φ : RelativeHomology S (N + 1) →ₗ[ZMod 2] ZMod 2) :
    relKroneckerH S (N := N) ((relKroneckerHEquiv S N).symm φ) = φ := by
  rw [← relKroneckerHEquiv_apply, LinearEquiv.apply_symm_apply]

end SKEFTHawking.SingularRelativeKroneckerEquiv
