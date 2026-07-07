/-
# Phase 5q.H (E1 CSC-PD tower) — integral compactly-supported cohomology endpoint `Hᵏ_c(M;ℤ)=Hᵏ(M;ℤ)`

For a **compact** manifold `M`, `univ` is the greatest compact, so the filtered colimit
`Hᵏ_c(M;ℤ) = colim_K Hᵏ(M|K;ℤ)` collapses onto its value at `⊤`
(`SingularDirectLimitTop.of_top_bijective`): `Hᵏ_c(M;ℤ) ≅ Hᵏ(M|univ;ℤ) = Hᵏ(M,∅;ℤ) ≅ Hᵏ(M;ℤ)`
(`relCohomologyEmptyEquivInt`). Integral mirror of `SingularCompactlySupportedTop`.

This is the **top endpoint** of the integral Poincaré-duality ladder: at `K = M` the abstract
compactly-supported cohomology is the ordinary cohomology, so the assembled duality
`D : Hᵏ_c(M;ℤ) → H_{n-k}(M;ℤ)` reads off as `capHInt · [M] : Hᵏ(M;ℤ) → H_{n-k}(M;ℤ)`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularCohomologyColimitInt
import SKEFTHawking.SingularDirectLimitTop
import SKEFTHawking.SingularRelativeCohomologyEmptyInt

open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularCohomologyColimitInt
open SKEFTHawking.SingularDirectLimitTop
open SKEFTHawking.SingularRelativeCohomologyEmptyInt

namespace SKEFTHawking.SingularCompactlySupportedTopInt

variable {M : TopCat}

/-- **Relative-cohomology congruence along a set equality** `S = T` (integral): `Hᵏ(M, S;ℤ) ≃ₗ
Hᵏ(M, T;ℤ)` (a `subst` of the underlying set; the directional cast `RelativeCohomologyInt Sᶜ →
RelativeCohomologyInt ∅`). -/
noncomputable def relCohomSetCongrInt {S T : Set ↑M} (h : S = T) (n : ℕ) :
    RelativeCohomologyInt S n ≃ₗ[ℤ] RelativeCohomologyInt T n := by
  subst h; exact LinearEquiv.refl _ _

/-- **The integral compactly-supported cohomology of a compact manifold is the ordinary cohomology**:
`Hᵏ_c(M;ℤ) ≅ Hᵏ(M;ℤ)`. `univ` is the top compact (`of_top_bijective`), so the colimit collapses onto
`cohomGInt k ⊤ = Hᵏ(M, univᶜ;ℤ) = Hᵏ(M, ∅;ℤ)`, which `relCohomologyEmptyEquivInt` identifies with
`Hᵏ(M;ℤ)`. -/
noncomputable def compactlySupportedTopEquivInt (k : ℕ) [CompactSpace ↑M] :
    CompactlySupportedCohomologyInt (M := M) k ≃ₗ[ℤ] Cohomology M k :=
  (LinearEquiv.ofBijective
        (Module.DirectLimit.of ℤ (TopologicalSpace.Compacts ↑M) (cohomGInt k) (cohomFInt k) ⊤)
        (of_top_bijective (cohomGInt k) (cohomFInt k))).symm.trans
    ((relCohomSetCongrInt (show (↑(⊤ : TopologicalSpace.Compacts ↑M) : Set ↑M)ᶜ = (∅ : Set ↑M) by
        rw [TopologicalSpace.Compacts.coe_top, Set.compl_univ]) k).trans
      (relCohomologyEmptyEquivInt k))

end SKEFTHawking.SingularCompactlySupportedTopInt
