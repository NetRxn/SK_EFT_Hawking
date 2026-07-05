/-
# Phase 5q.H (E1 integral topology) — the integral homology directed system of subspaces

Integral (`ZMod 2 → ℤ`) mirror of `SingularSubsetHomology`. For `K ⊆ K'` the subspace inclusion
`sub K ↪ sub K'` (`Set.inclusion`, continuous) induces a ℤ-linear map on integral singular homology
  `homOfSubsetInt : H_n(sub K; ℤ) → H_n(sub K'; ℤ)`,
**functorial** in `K` (`homOfSubsetInt_id` / `homOfSubsetInt_trans`), over the on-main integral absolute
homology functoriality `Homology.mapInt`. This is the homology side of the integral duality directed
system — the **bottom row** of the compactly-supported-cohomology Poincaré-duality ladder; the
cohomology side is `SingularRelativeCohomologyRestrictInt.relCohomRestrictInt`. Consumed by the D_K
support-enlargement naturality rung `SingularLocalDualityKMonoInt`.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularFunctorialityInt
import SKEFTHawking.SingularRelativeHomologyMod2

open SKEFTHawking.SingularHomologyInt
open SKEFTHawking.SingularRelativeHomologyMod2 (sub)
open SKEFTHawking.SingularFunctorialityInt

namespace SKEFTHawking.SingularSubsetHomologyInt

variable {X : TopCat}

/-- The subspace inclusion `sub K ↪ sub K'` (for `K ⊆ K'`) as a continuous map `C(↥K, ↥K')`. -/
def subInclCM {K K' : Set ↑X} (h : K ⊆ K') : C(↥K, ↥K') :=
  ⟨Set.inclusion h, continuous_inclusion h⟩

/-- **The integral homology directed-system map** `H_n(sub K; ℤ) → H_n(sub K'; ℤ)` for `K ⊆ K'`,
induced by the subspace inclusion (via the on-main `Homology.mapInt`). -/
noncomputable def homOfSubsetInt {K K' : Set ↑X} (h : K ⊆ K') (n : ℕ) :
    Homology (sub K) n →ₗ[ℤ] Homology (sub K') n :=
  Homology.mapInt (subInclCM h) n

/-- **Identity law** `homOfSubsetInt (K ⊆ K) = id`. -/
theorem homOfSubsetInt_id {K : Set ↑X} (n : ℕ) :
    homOfSubsetInt (subset_refl K) n = LinearMap.id := by
  have hcm : subInclCM (subset_refl K) = ContinuousMap.id ↥K := by ext x; rfl
  rw [homOfSubsetInt, hcm, Homology.mapInt_id]

/-- **Composition law** `homOfSubsetInt (K ⊆ K'') = homOfSubsetInt (K' ⊆ K'') ∘ homOfSubsetInt (K ⊆
K')` — the functoriality making `(H_n(sub K; ℤ))_K` a directed system. -/
theorem homOfSubsetInt_trans {K K' K'' : Set ↑X} (h1 : K ⊆ K') (h2 : K' ⊆ K'') (n : ℕ) :
    homOfSubsetInt (h1.trans h2) n = (homOfSubsetInt h2 n).comp (homOfSubsetInt h1 n) := by
  have hcm : subInclCM (h1.trans h2) = (subInclCM h2).comp (subInclCM h1) := by ext x; rfl
  rw [homOfSubsetInt, homOfSubsetInt, homOfSubsetInt, hcm]
  exact Homology.mapInt_comp (X := sub K) (Y := sub K') (Z := sub K'') (subInclCM h2) (subInclCM h1) n

end SKEFTHawking.SingularSubsetHomologyInt
