import Mathlib
import SKEFTHawking.SingularCohomologyColimit
import SKEFTHawking.SingularDirectLimitTop
import SKEFTHawking.SingularRelativeCohomologyEmpty

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD5-cohend) — the compactly-supported cohomology endpoint `Hᵏ_c(M)=Hᵏ(M)`

For a **compact** manifold `M`, `univ` is the greatest compact, so the filtered colimit
`Hᵏ_c(M) = colim_K Hᵏ(M|K)` collapses onto its value at `⊤`
(`SingularDirectLimitTop.of_top_bijective`): `Hᵏ_c(M) ≅ Hᵏ(M|univ) = Hᵏ(M, ∅) = Hᵏ(M)`
(`SingularRelativeCohomologyEmpty.relCohomologyEmptyEquiv`).

This is the **top endpoint** of the Poincaré-duality ladder: at `K = M` the abstract compactly-supported
cohomology is the ordinary cohomology, so the assembled duality `D : Hᵏ_c(M) → H_{n-k}(M)` reads off as
`capH · [M] : Hᵏ(M) → H_{n-k}(M)`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularCohomologyColimit SKEFTHawking.SingularDirectLimitTop
  SKEFTHawking.SingularRelativeCohomologyEmpty

namespace SKEFTHawking.SingularCompactlySupportedTop

variable {M : TopCat}

/-- **Relative-cohomology congruence along a set equality** `S = T`: `Hᵏ(M, S) ≃ₗ Hᵏ(M, T)` (a `subst`
of the underlying set; the directional cast `RelativeCohomology Sᶜ → RelativeCohomology ∅`). -/
noncomputable def relCohomSetCongr {S T : Set ↑M} (h : S = T) (n : ℕ) :
    RelativeCohomology S n ≃ₗ[ZMod 2] RelativeCohomology T n := by
  subst h; exact LinearEquiv.refl _ _

/-- **The compactly-supported cohomology of a compact manifold is the ordinary cohomology**:
`Hᵏ_c(M) ≅ Hᵏ(M)`. `univ` is the top compact (`of_top_bijective`), so the colimit collapses onto
`cohomG k ⊤ = Hᵏ(M, univᶜ) = Hᵏ(M, ∅)`, which `relCohomologyEmptyEquiv` identifies with `Hᵏ(M)`. -/
noncomputable def compactlySupportedTopEquiv (k : ℕ) [CompactSpace ↑M] :
    CompactlySupportedCohomology (M := M) k ≃ₗ[ZMod 2] Cohomology M k :=
  (LinearEquiv.ofBijective
        (Module.DirectLimit.of (ZMod 2) (TopologicalSpace.Compacts ↑M) (cohomG k) (cohomF k) ⊤)
        (of_top_bijective (cohomG k) (cohomF k))).symm.trans
    ((relCohomSetCongr (show (↑(⊤ : TopologicalSpace.Compacts ↑M) : Set ↑M)ᶜ = (∅ : Set ↑M) by
        rw [TopologicalSpace.Compacts.coe_top, Set.compl_univ]) k).trans
      (relCohomologyEmptyEquiv k))

end SKEFTHawking.SingularCompactlySupportedTop
