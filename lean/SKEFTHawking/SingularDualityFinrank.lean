import Mathlib
import SKEFTHawking.SingularRelativeUC

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD5b-perf) — the finite-dimensional perfect pairing

In **finite dimensions** the relative Kronecker pairing `relKroneckerH` is a *perfect* pairing: the map
`relKroneckerH S : Hᵏ(M,S) → (Hₙ(M,S))^*` (`ω ↦ ⟨ω,·⟩`) is not only injective (universal coefficients,
`SingularRelativeUC`) but **surjective** — every functional on the relative homology is realized by a
relative cohomology class. Over the field `ℤ/2`, with `Hₙ(M,S)` finite-dimensional, this follows from the
two universal-coefficients injections plus a dimension count: `Hᵏ ↪ (Hₙ)^*` and `Hₙ ↪ (Hᵏ)^*` force
`dim Hᵏ = dim Hₙ`, and an injective endomorphism-shaped map between equal finite dimensions is bijective.

This is the finite-dimension-dependent half of the cohomology MV exactness duality-transfer
(`SingularDualityMVAdjoint`): the realization lets a functional built from `(α,β) ∈ ann(ker relMvHomSum)`
be promoted to a class `γ` with `relCohomMvDiag γ = (α,β)`. The finite-dimensionality is supplied by the
Poincaré-duality induction's `Hⁿ(M|x) ≅ ℤ/2`-built pieces.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
open SKEFTHawking.SingularRelativePairing SKEFTHawking.SingularRelativeUC

namespace SKEFTHawking.SingularDualityFinrank

variable {X : TopCat}

/-- `relKroneckerH S` is **injective** (universal coefficients, cohomology side): `⟨ω,·⟩ = 0 ⟹ ω = 0`. -/
theorem relKroneckerH_injective (S : Set X) {N : ℕ} :
    Function.Injective (relKroneckerH S (N := N)) := by
  rw [injective_iff_map_eq_zero]
  intro ω hω
  exact relCohomology_eq_zero_of_relKroneckerH S ω
    (fun β => (LinearMap.congr_fun hω β).trans (LinearMap.zero_apply β))

/-- `(relKroneckerH S).flip` is **injective** (universal coefficients, homology side): `⟨·,β⟩ = 0 ⟹ β = 0`. -/
theorem relKroneckerH_flip_injective (S : Set X) {N : ℕ} :
    Function.Injective ((relKroneckerH S (N := N)).flip) := by
  rw [injective_iff_map_eq_zero]
  intro β hβ
  refine relHomology_eq_zero_of_relKroneckerH S β (fun ω => ?_)
  have := LinearMap.congr_fun hβ ω
  rwa [LinearMap.flip_apply, LinearMap.zero_apply] at this

/-- **The relative Kronecker pairing is a perfect pairing in finite dimensions**: if `Hₙ(M,S)` is
finite-dimensional, then `relKroneckerH S : Hᵏ(M,S) → (Hₙ(M,S))^*` is **surjective** — every functional on
the relative homology is `⟨ω,·⟩` for some cohomology class `ω`. From the two universal-coefficients
injections (`SingularRelativeUC`) plus `dim Hᵏ = dim Hₙ` and injective-between-equal-finite-dims-is-onto. -/
theorem relKroneckerH_surjective (S : Set X) {N : ℕ}
    [FiniteDimensional (ZMod 2) (RelativeHomology S (N + 1))] :
    Function.Surjective (relKroneckerH S (N := N)) := by
  -- `Hᵏ ↪ (Hₙ)^*` (finite-dim) ⟹ `Hᵏ` finite-dim and `dim Hᵏ ≤ dim Hₙ`.
  haveI : FiniteDimensional (ZMod 2) (RelativeCohomology S (N + 1)) :=
    FiniteDimensional.of_injective (relKroneckerH S (N := N)) (relKroneckerH_injective S)
  have h1 : Module.finrank (ZMod 2) (RelativeCohomology S (N + 1))
      ≤ Module.finrank (ZMod 2) (RelativeHomology S (N + 1)) := by
    calc Module.finrank (ZMod 2) (RelativeCohomology S (N + 1))
        ≤ Module.finrank (ZMod 2) (RelativeHomology S (N + 1) →ₗ[ZMod 2] ZMod 2) :=
          (relKroneckerH S (N := N)).finrank_le_finrank_of_injective (relKroneckerH_injective S)
      _ = Module.finrank (ZMod 2) (RelativeHomology S (N + 1)) := Subspace.dual_finrank_eq
  -- `Hₙ ↪ (Hᵏ)^*` ⟹ `dim Hₙ ≤ dim Hᵏ`.
  have h2 : Module.finrank (ZMod 2) (RelativeHomology S (N + 1))
      ≤ Module.finrank (ZMod 2) (RelativeCohomology S (N + 1)) := by
    calc Module.finrank (ZMod 2) (RelativeHomology S (N + 1))
        ≤ Module.finrank (ZMod 2) (RelativeCohomology S (N + 1) →ₗ[ZMod 2] ZMod 2) :=
          (relKroneckerH S (N := N)).flip.finrank_le_finrank_of_injective (relKroneckerH_flip_injective S)
      _ = Module.finrank (ZMod 2) (RelativeCohomology S (N + 1)) := Subspace.dual_finrank_eq
  -- equal dims + injective ⟹ surjective.
  exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
    ((le_antisymm h1 h2).trans Subspace.dual_finrank_eq.symm)).mp (relKroneckerH_injective S)

end SKEFTHawking.SingularDualityFinrank
