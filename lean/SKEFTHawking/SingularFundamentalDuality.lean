import Mathlib
import SKEFTHawking.SingularCohomologyColimit
import SKEFTHawking.SingularRelativeDuality

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD5-DM) — the compactly-supported duality map `D_M`

The Poincaré-duality map at the level of the whole compactly-supported cohomology,
  `D_M : Hᵏ_c(M) → H_{m+1}(M)`,    `[a]_K ↦ [a ⌢ z]`,
for a fixed **absolute** fundamental cycle `z` (`∂z = 0`, degree `k+m+1 = dim M`). It is the filtered
colimit (`Module.DirectLimit.lift`) of the per-compact fixed-target duality maps
`SingularRelativeDuality.relativeDuality (Kᶜ) z : Hᵏ(M|K) → H_{m+1}(M)`. The colimit is **well-defined**
because capping the *same* global cycle `z` commutes with the relative-cohomology restriction
(`relCohomRestrict` preserves the underlying absolute cochain, `relCochainRestrict_coe`), so the family is
compatible. At `K = univ` (the `⊤` endpoint) `relativeDuality ∅ z = capH · [M]`, so under the endpoint iso
`SingularCompactlySupportedTop.compactlySupportedTopEquiv` (`Hᵏ_c(M) ≅ Hᵏ(M)`) `D_M` reads off as the cap
`capH · [M] : Hᵏ(M) → H_{m+1}(M)` whose injectivity is the `PoincareDual4Mid.nondeg` target.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2
  SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyRestrict
  SKEFTHawking.SingularRelativeDuality SKEFTHawking.SingularCohomologyColimit

namespace SKEFTHawking.SingularFundamentalDuality

variable {M : TopCat}

/-- **Compatibility of the fixed-target duality with restriction**: capping the same global cycle `z`
commutes with `relCohomRestrict` — both sides are `[a ⌢ z]` for the *same* underlying absolute cochain
`a` (`relCohomRestrict` preserves it, `relCocycleRestrict_coe` / `relCochainRestrict_coe`). This is the
`DirectLimit.lift` compatibility making `D_M` well-defined. -/
theorem relativeDuality_restrict_compat {k m : ℕ} (z : SingularChain M (k + m + 1))
    {S T : Set ↑M} (h : S ⊆ T) (hzS : chainBoundary M (k + m) z ∈ subspaceChains S (k + m))
    (hzT : chainBoundary M (k + m) z ∈ subspaceChains T (k + m))
    (x : RelativeCohomology T k) :
    relativeDuality S k m z hzS (relCohomRestrict h k x)
      = relativeDuality T k m z hzT x := by
  obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  have hx : (Submodule.Quotient.mk a : RelativeCohomology T k) = RelativeCohomology.mk T k a := rfl
  rw [hx, relCohomRestrict_mk, relativeDuality_mk, relativeDuality_mk]
  -- Both homology classes are `[a ⌢ z]` for the same underlying absolute cochain
  -- (`relCohomRestrict` preserves it, `relCocycleRestrict_coe`), so the representatives agree.
  have hcoe : (↑↑(relCocycleRestrict h k a) : SingularCochain M k) = ↑↑a := by
    rw [relCocycleRestrict_coe, relCochainRestrict_coe]
  have hcap : cap (m := m + 1) (↑↑(relCocycleRestrict h k a) : SingularCochain M k) z
      = cap (m := m + 1) (↑↑a : SingularCochain M k) z := by
    rw [hcoe]
  exact congrArg (Homology.mk M (m + 1)) (Subtype.ext hcap)

/-- **The compactly-supported duality map** `D_M : Hᵏ_c(M) → H_{m+1}(M)`, the colimit of the
fixed-target `relativeDuality (Kᶜ) z` over the compacts, for an absolute fundamental cycle `z`
(`∂z = 0`). -/
noncomputable def fundamentalDuality (k m : ℕ) (z : SingularChain M (k + m + 1))
    (hz : chainBoundary M (k + m) z = 0) :
    CompactlySupportedCohomology (M := M) k →ₗ[ZMod 2] Homology M (m + 1) :=
  Module.DirectLimit.lift (ZMod 2) (TopologicalSpace.Compacts ↑M) (cohomG k) (cohomF k)
    (fun K => relativeDuality ((↑K : Set ↑M)ᶜ) k m z (by rw [hz]; exact Submodule.zero_mem _))
    (fun K K' h x => relativeDuality_restrict_compat z
      (Set.compl_subset_compl.mpr h) (by rw [hz]; exact Submodule.zero_mem _)
      (by rw [hz]; exact Submodule.zero_mem _) x)

end SKEFTHawking.SingularFundamentalDuality
