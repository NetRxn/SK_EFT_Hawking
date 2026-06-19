import Mathlib
import SKEFTHawking.SingularHomologyColimit
import SKEFTHawking.SingularDirectLimitTop
import SKEFTHawking.SingularHomologyHomeo

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD5-homend) — the homology colimit endpoint `colim_K H_n(sub K) = H_n(M)`

For a **compact** manifold `M`, `univ` is the greatest compact, so `colim_K H_n(sub K)` collapses
(`of_top_bijective`) onto `homG n ⊤ = H_n(sub univ)`, which the universal-set homeomorphism
`↥univ ≃ₜ M` identifies with `H_n(M)` (`homologyHomeoEquiv`). The **bottom endpoint** of the
Poincaré-duality ladder, dual to `SingularCompactlySupportedTop.compactlySupportedTopEquiv`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
  SKEFTHawking.SingularHomologyColimit SKEFTHawking.SingularDirectLimitTop
  SKEFTHawking.SingularHomologyHomeo

namespace SKEFTHawking.SingularHomologyColimitTop

variable {M : TopCat}

/-- The homeomorphism `↥(↑(⊤ : Compacts)) ≃ₜ ↑M` for compact `M`: `↑⊤ = univ` (`Compacts.coe_top`,
via `Homeomorph.setCongr`) then `↥univ ≃ₜ ↑M` (`Homeomorph.Set.univ`). -/
noncomputable def topCompactHomeo [CompactSpace ↑M] :
    ↥(↑(⊤ : TopologicalSpace.Compacts ↑M) : Set ↑M) ≃ₜ ↑M :=
  (Homeomorph.setCongr TopologicalSpace.Compacts.coe_top).trans (Homeomorph.Set.univ ↑M)

/-- **The homology colimit of a compact manifold is the ordinary homology**: `colim_K H_n(sub K) ≅ H_n(M)`. -/
noncomputable def homologyColimitTopEquiv (n : ℕ) [CompactSpace ↑M] :
    HomologyColimit (M := M) n ≃ₗ[ZMod 2] Homology M n :=
  (LinearEquiv.ofBijective
        (Module.DirectLimit.of (ZMod 2) (TopologicalSpace.Compacts ↑M) (homG n) (homF n) ⊤)
        (of_top_bijective (homG n) (homF n))).symm.trans
    (homologyHomeoEquiv (X := sub (↑(⊤ : TopologicalSpace.Compacts ↑M) : Set ↑M)) (Y := M)
      topCompactHomeo n)

end SKEFTHawking.SingularHomologyColimitTop
