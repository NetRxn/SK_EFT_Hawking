/-
# Phase 5q.H (E1 integral topology) — the relative cohomology MV connecting map δ (torsion-safe)

Integral (`ZMod 2 → ℤ`) construction of the relative cohomology Mayer–Vietoris connecting map + the two
remaining exactness spots — the **torsion-safe** route (the mod-2 `SingularRelativeCohomologyMVConnecting`
dualizes the homology connecting through the PERFECT Kronecker pairing `relKroneckerHEquiv`, field-only; see
the DECISIONS entry). Here the connecting map is the **snake of the cochain-level MV SES**
`0 → C*(M,U∪V) --Δ--> C*(M,U)⊕C*(M,V) --Σ--> C*(M,U∩V) → 0`, whose exactness is the field-UC-free
`SingularRelativeCochainMVExactInt.mvCochain_dual_exact`.

This module (brick 1) builds the **cochain-level MV maps** `relCochainMvDiagInt` (`Δ`, the restriction from
`U∪V`; injective — restriction is the antitone *inclusion* `relCochainsInt(U∪V) ↪ relCochainsInt(U)`) and
`relCochainMvSumInt` (`Σ`, the honest ℤ-difference of the restrictions to `U∩V`; surjective via the explicit
indicator split `relCochainMvSum_surjectiveInt`), plus the cochain-complex condition `Σ ∘ Δ = 0`. These are
the top/bottom of the snake; the connecting map + exactness follow.

Kernel-pure (`{propext, Classical.choice, Quot.sound}`); no `sorry`/`native_decide`/`maxHeartbeats`/axiom.
-/
import Mathlib
import SKEFTHawking.SingularRelativeCohomologyRestrictInt
import SKEFTHawking.SingularRelativeCochainMVSurjInt

open SKEFTHawking.SingularCohomologyInt
open SKEFTHawking.SingularEuclideanCapIsoInt
open SKEFTHawking.SingularRelativeCohomologyRestrictInt
open SKEFTHawking.SingularRelativeCochainMVSurjInt

namespace SKEFTHawking.SingularRelativeCohomologyMVConnectingInt

variable {M : TopCat}

/-- **The cochain-level relative MV diagonal** `Δ : Cⁿ(M,U∪V;ℤ) → Cⁿ(M,U;ℤ) ⊕ Cⁿ(M,V;ℤ)`, the pair of
cochain restrictions `U∪V ↠ U`, `U∪V ↠ V`. -/
noncomputable def relCochainMvDiagInt (U V : Set ↑M) (n : ℕ) :
    relCochainsInt (U ∪ V) n →ₗ[ℤ] relCochainsInt U n × relCochainsInt V n :=
  (relCochainRestrictInt Set.subset_union_left n).prod (relCochainRestrictInt Set.subset_union_right n)

/-- **The cochain-level relative MV sum** `Σ : Cⁿ(M,U;ℤ) ⊕ Cⁿ(M,V;ℤ) → Cⁿ(M,U∩V;ℤ)`, the honest
ℤ-DIFFERENCE of the restrictions `U ↠ U∩V`, `V ↠ U∩V`. -/
noncomputable def relCochainMvSumInt (U V : Set ↑M) (n : ℕ) :
    relCochainsInt U n × relCochainsInt V n →ₗ[ℤ] relCochainsInt (U ∩ V) n :=
  (relCochainRestrictInt Set.inter_subset_left n).coprod
    (-relCochainRestrictInt Set.inter_subset_right n)

@[simp] theorem relCochainMvSumInt_apply (U V : Set ↑M) (n : ℕ)
    (x : relCochainsInt U n) (y : relCochainsInt V n) :
    relCochainMvSumInt U V n (x, y)
      = relCochainRestrictInt Set.inter_subset_left n x
        - relCochainRestrictInt Set.inter_subset_right n y := by
  rw [relCochainMvSumInt, LinearMap.coprod_apply, LinearMap.neg_apply, sub_eq_add_neg]

@[simp] theorem relCochainMvDiagInt_apply (U V : Set ↑M) (n : ℕ) (f : relCochainsInt (U ∪ V) n) :
    relCochainMvDiagInt U V n f
      = (relCochainRestrictInt Set.subset_union_left n f,
          relCochainRestrictInt Set.subset_union_right n f) :=
  rfl

/-- **`Δ` is injective**: its first component `relCochainRestrictInt (U ⊆ U∪V)` is the antitone submodule
inclusion, itself injective (identity on the underlying cochain). -/
theorem relCochainMvDiagInt_injective (U V : Set ↑M) (n : ℕ) :
    Function.Injective (relCochainMvDiagInt U V n) := by
  intro f g h
  apply Subtype.ext
  have h1 := congrArg Prod.fst h
  simpa only [relCochainMvDiagInt_apply, relCochainRestrictInt_coe] using congrArg Subtype.val h1

/-- **`Σ` is surjective**: every `g : Cⁿ(M,U∩V;ℤ)` is `gU − gV` (the explicit indicator split
`relCochainMvSum_surjectiveInt`). -/
theorem relCochainMvSumInt_surjective (U V : Set ↑M) (n : ℕ) :
    Function.Surjective (relCochainMvSumInt U V n) := by
  intro g
  obtain ⟨gU, gV, hg⟩ := relCochainMvSum_surjectiveInt U V n g
  refine ⟨(gU, gV), ?_⟩
  apply Subtype.ext
  rw [relCochainMvSumInt_apply, AddSubgroupClass.coe_sub, relCochainRestrictInt_coe,
    relCochainRestrictInt_coe, hg]

/-- **The cochain-complex condition `Σ ∘ Δ = 0`**: both routes `(M,U∪V) → (M,U∩V)` are the single
restriction, so the ℤ-difference is `c − c = 0`. -/
theorem relCochainMvSumInt_relCochainMvDiagInt (U V : Set ↑M) (n : ℕ)
    (f : relCochainsInt (U ∪ V) n) :
    relCochainMvSumInt U V n (relCochainMvDiagInt U V n f) = 0 := by
  apply Subtype.ext
  rw [relCochainMvDiagInt_apply, relCochainMvSumInt_apply, ZeroMemClass.coe_zero,
    AddSubgroupClass.coe_sub]
  simp only [relCochainRestrictInt_coe]
  rw [sub_self]

end SKEFTHawking.SingularRelativeCohomologyMVConnectingInt
