import Mathlib
import SKEFTHawking.SingularRelativeCohomologyRestrict

/-!
# Phase 5q.F (w₂-foundation, brick 72c-PD5b) — relative cohomology Mayer–Vietoris (the maps)

The cohomology dual of `SingularRelativeMV.relMvHomDiag/relMvHomSum`. With `Hᵏ(M|A) := Hᵏ(M, M∖A)` and
opens `U = M∖A`, `V = M∖B` (so `U∩V = M∖(A∪B)`, `U∪V = M∖(A∩B)`), cohomology is **contravariant**, so the
MV diagonal restricts FROM the union and the MV sum restricts TO the intersection:
  `Hᵏ(M|A∪B) --Δ--> Hᵏ(M|A) ⊕ Hᵏ(M|B) --Σ--> Hᵏ(M|A∩B)`
built from the restriction maps `SingularRelativeCohomologyRestrict.relCohomRestrict`. The cochain-complex
condition `Σ ∘ Δ = 0` holds because both routes `(M, U∪V) → (M, U∩V)` are the single restriction, so over
`ℤ/2` the sum is `c + c = 0` (`relCohomRestrict_trans` + `ZModModule.add_self`). With the connecting map
(next brick) this becomes the relative cohomology MV long exact sequence — the top row of the
Poincaré-duality `5`-lemma ladder.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open SKEFTHawking.SingularRelativeCohomologyMod2 SKEFTHawking.SingularRelativeCohomologyRestrict

namespace SKEFTHawking.SingularRelativeCohomologyMV

variable {M : TopCat}

/-- **Relative cohomology MV diagonal** `Hᵏ(M|A∪B) → Hᵏ(M|A) ⊕ Hᵏ(M|B)`, the two restrictions
`U∪V ↠ U`, `U∪V ↠ V` (contravariant — restrict FROM the union). -/
noncomputable def relCohomMvDiag (U V : Set ↑M) (n : ℕ) :
    RelativeCohomology (U ∪ V) n →ₗ[ZMod 2] RelativeCohomology U n × RelativeCohomology V n :=
  (relCohomRestrict Set.subset_union_left n).prod (relCohomRestrict Set.subset_union_right n)

@[simp] theorem relCohomMvDiag_apply (U V : Set ↑M) (n : ℕ) (ω : RelativeCohomology (U ∪ V) n) :
    relCohomMvDiag U V n ω
      = (relCohomRestrict Set.subset_union_left n ω, relCohomRestrict Set.subset_union_right n ω) :=
  rfl

/-- **Relative cohomology MV sum** `Hᵏ(M|A) ⊕ Hᵏ(M|B) → Hᵏ(M|A∩B)`, the difference (over `ℤ/2`) of the
restrictions `U ↠ U∩V`, `V ↠ U∩V` (contravariant — restrict TO the intersection). -/
noncomputable def relCohomMvSum (U V : Set ↑M) (n : ℕ) :
    RelativeCohomology U n × RelativeCohomology V n →ₗ[ZMod 2] RelativeCohomology (U ∩ V) n :=
  (relCohomRestrict Set.inter_subset_left n).coprod (relCohomRestrict Set.inter_subset_right n)

@[simp] theorem relCohomMvSum_apply (U V : Set ↑M) (n : ℕ)
    (x : RelativeCohomology U n) (y : RelativeCohomology V n) :
    relCohomMvSum U V n (x, y)
      = relCohomRestrict Set.inter_subset_left n x + relCohomRestrict Set.inter_subset_right n y :=
  rfl

/-- **Relative cohomology MV cochain-complex condition** `Σ ∘ Δ = 0`: both routes `(M, U∪V) → (M, U∩V)`
equal the single restriction `U∩V ⊆ U∪V`, so over `ℤ/2` the sum is `c + c = 0`. The dual of
`SingularRelativeMV.relMvHomSum_relMvHomDiag`. -/
theorem relCohomMvSum_relCohomMvDiag (U V : Set ↑M) (n : ℕ) (ω : RelativeCohomology (U ∪ V) n) :
    relCohomMvSum U V n (relCohomMvDiag U V n ω) = 0 := by
  rw [relCohomMvDiag_apply, relCohomMvSum_apply, relCohomRestrict_trans, relCohomRestrict_trans]
  exact ZModModule.add_self _

end SKEFTHawking.SingularRelativeCohomologyMV
