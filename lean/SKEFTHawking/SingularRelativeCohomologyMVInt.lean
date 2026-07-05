/-
# Phase 5q.H (E1 integral topology) — relative cohomology Mayer–Vietoris (the maps, integral)

Integral (`ZMod 2 → ℤ`) mirror of `SingularRelativeCohomologyMV` (the maps). With `Hᵏ(M|A;ℤ) := Hᵏ(M,
M∖A; ℤ)` and opens `U = M∖A`, `V = M∖B`, cohomology is contravariant, so the MV diagonal restricts FROM
the union and the MV sum restricts TO the intersection:
  `Hᵏ(M|A∪B;ℤ) --Δ--> Hᵏ(M|A;ℤ) ⊕ Hᵏ(M|B;ℤ) --Σ--> Hᵏ(M|A∩B;ℤ)`
built from `relCohomRestrictInt`. The cochain-complex condition `Σ ∘ Δ = 0` holds because both routes
`(M, U∪V) → (M, U∩V)` are the single restriction — over ℤ the sum is the honest DIFFERENCE `c − c = 0`
(mod-2 `coprod` + `ZModModule.add_self` → ℤ `coprod (−·)` + `sub_self`).

**Note (strategic — see the DECISIONS entry):** only the MAPS are built here. The relative-cohomology MV
**exactness** (`Middle`) will NOT mirror the mod-2, which dualizes the homology MV via the universal
coefficient theorem (field-dependent: `SingularUniversalCoeff`/`SingularDualityFinrank` work over the FIELD
ℤ/2). Over ℤ the exactness is built **directly** by dualizing the degreewise-split relative-homology MV
chain SES via `Hom(−, ℤ)` (the splitting is chain-level, preserved — no UC, no finrank, no torsion issue).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularRelativeCohomologyRestrictInt

open SKEFTHawking.SingularEuclideanCapIsoInt SKEFTHawking.SingularRelativeCohomologyRestrictInt

namespace SKEFTHawking.SingularRelativeCohomologyMVInt

variable {M : TopCat}

/-- **Integral relative cohomology MV diagonal** `Hᵏ(M|A∪B;ℤ) → Hᵏ(M|A;ℤ) ⊕ Hᵏ(M|B;ℤ)`, the two
restrictions `U∪V ↠ U`, `U∪V ↠ V`. -/
noncomputable def relCohomMvDiagInt (U V : Set ↑M) (n : ℕ) :
    RelativeCohomologyInt (U ∪ V) n →ₗ[ℤ] RelativeCohomologyInt U n × RelativeCohomologyInt V n :=
  (relCohomRestrictInt Set.subset_union_left n).prod (relCohomRestrictInt Set.subset_union_right n)

@[simp] theorem relCohomMvDiagInt_apply (U V : Set ↑M) (n : ℕ) (ω : RelativeCohomologyInt (U ∪ V) n) :
    relCohomMvDiagInt U V n ω
      = (relCohomRestrictInt Set.subset_union_left n ω,
          relCohomRestrictInt Set.subset_union_right n ω) :=
  rfl

/-- **Integral relative cohomology MV sum** `Hᵏ(M|A;ℤ) ⊕ Hᵏ(M|B;ℤ) → Hᵏ(M|A∩B;ℤ)`, the honest
DIFFERENCE (over ℤ) of the restrictions `U ↠ U∩V`, `V ↠ U∩V`. -/
noncomputable def relCohomMvSumInt (U V : Set ↑M) (n : ℕ) :
    RelativeCohomologyInt U n × RelativeCohomologyInt V n →ₗ[ℤ] RelativeCohomologyInt (U ∩ V) n :=
  (relCohomRestrictInt Set.inter_subset_left n).coprod
    (-relCohomRestrictInt Set.inter_subset_right n)

@[simp] theorem relCohomMvSumInt_apply (U V : Set ↑M) (n : ℕ)
    (x : RelativeCohomologyInt U n) (y : RelativeCohomologyInt V n) :
    relCohomMvSumInt U V n (x, y)
      = relCohomRestrictInt Set.inter_subset_left n x
        - relCohomRestrictInt Set.inter_subset_right n y := by
  rw [relCohomMvSumInt, LinearMap.coprod_apply, LinearMap.neg_apply, sub_eq_add_neg]

/-- **Integral relative cohomology MV cochain-complex condition** `Σ ∘ Δ = 0`: both routes equal the
single restriction `U∩V ⊆ U∪V`, so over ℤ the difference is `c − c = 0`. -/
theorem relCohomMvSumInt_relCohomMvDiagInt (U V : Set ↑M) (n : ℕ)
    (ω : RelativeCohomologyInt (U ∪ V) n) :
    relCohomMvSumInt U V n (relCohomMvDiagInt U V n ω) = 0 := by
  rw [relCohomMvDiagInt_apply, relCohomMvSumInt_apply, relCohomRestrictInt_trans,
    relCohomRestrictInt_trans, sub_self]

end SKEFTHawking.SingularRelativeCohomologyMVInt
