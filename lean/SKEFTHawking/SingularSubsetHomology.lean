import Mathlib
import SKEFTHawking.SingularFunctoriality
import SKEFTHawking.SingularRelativeHomologyMod2

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD5-homdir) — the homology directed system of subspaces

For `K ⊆ K'` the subspace inclusion `sub K ↪ sub K'` (`Set.inclusion`, continuous) induces a `ℤ/2`-linear
map on singular homology
  `homOfSubset : H_n(sub K) → H_n(sub K')`,
**functorial** in `K`: `homOfSubset (K ⊆ K) = id` (`homOfSubset_id`) and
`homOfSubset (K ⊆ K'') = homOfSubset (K' ⊆ K'') ∘ homOfSubset (K ⊆ K')` (`homOfSubset_trans`). This is
the homology side of the duality directed system: combined with `exists_compact_support`
(`SingularCompactSupport`) it presents `H_n(U) ≅ colim_{K ⊆ U compact} H_n(sub K)`, the **bottom row** of
the compactly-supported-cohomology Poincaré-duality ladder (Hatcher 3.36 over open covers). The
cohomology side is `SingularRelativeCohomologyRestrict.relCohomRestrict` (contravariant via the
complements `Kᶜ' ⊆ Kᶜ`).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularRelativeHomologyMod2
  SKEFTHawking.SingularFunctoriality

namespace SKEFTHawking.SingularSubsetHomology

variable {X : TopCat}

/-- The subspace inclusion `sub K ↪ sub K'` (for `K ⊆ K'`) as a continuous map `C(↥K, ↥K')`. -/
def subInclCM {K K' : Set ↑X} (h : K ⊆ K') : C(↥K, ↥K') :=
  ⟨Set.inclusion h, continuous_inclusion h⟩

/-- **The homology directed-system map** `H_n(sub K) → H_n(sub K')` for `K ⊆ K'`, induced by the
subspace inclusion. -/
noncomputable def homOfSubset {K K' : Set ↑X} (h : K ⊆ K') (n : ℕ) :
    Homology (sub K) n →ₗ[ZMod 2] Homology (sub K') n :=
  Homology.map (subInclCM h) n

/-- **Identity law** `homOfSubset (K ⊆ K) = id` (the subspace self-inclusion is the identity). -/
theorem homOfSubset_id {K : Set ↑X} (n : ℕ) :
    homOfSubset (subset_refl K) n = LinearMap.id := by
  have hcm : subInclCM (subset_refl K) = ContinuousMap.id ↥K := by
    ext x; rfl
  rw [homOfSubset, hcm, Homology.map_id]

/-- **Composition law** `homOfSubset (K ⊆ K'') = homOfSubset (K' ⊆ K'') ∘ homOfSubset (K ⊆ K')` (the
subspace inclusions compose) — the functoriality making `(H_n(sub K))_K` a directed system. -/
theorem homOfSubset_trans {K K' K'' : Set ↑X} (h1 : K ⊆ K') (h2 : K' ⊆ K'') (n : ℕ) :
    homOfSubset (h1.trans h2) n = (homOfSubset h2 n).comp (homOfSubset h1 n) := by
  have hcm : subInclCM (h1.trans h2) = (subInclCM h2).comp (subInclCM h1) := by
    ext x; rfl
  rw [homOfSubset, homOfSubset, homOfSubset, hcm]
  exact Homology.map_comp (X := sub K) (Y := sub K') (Z := sub K'') (subInclCM h2) (subInclCM h1) n

end SKEFTHawking.SingularSubsetHomology
