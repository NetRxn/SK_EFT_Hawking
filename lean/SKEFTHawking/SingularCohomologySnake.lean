import Mathlib
import SKEFTHawking.SingularRelativeCohomologyMod2
import SKEFTHawking.SingularExcisionIso

/-!
# Phase 5q.F (w₂-foundation, PD6f-c4-S0) — the cochain MV split (explicit cohomology snake δ, brick 1)

Toward the **explicit cohomology Mayer–Vietoris connecting map** `snakeδ` (which the connecting-square
seam-match needs — `relCohomMvConnecting` is only the UC-dual, with no chain action). The cochain MV split
is **function-level** (no subdivision, since cochains are functions): for `ω ∈ relCochains (U ∩ V)` the
`U`-part `φ σ := if σ supported in U then 0 else ω σ` lies in `relCochains U`; symmetrically `ω - φ` lies in
`relCochains V`; `φ + (ω - φ) = ω`. Then `snakeδ ω := [δφ]` (subsequent brick).

Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/

open CategoryTheory Opposite
open SKEFTHawking.SingularHomologyMod2 SKEFTHawking.SingularCohomologyMod2
  SKEFTHawking.SingularRelativeHomologyMod2 SKEFTHawking.SingularRelativeCohomologyMod2
  SKEFTHawking.SingularExcision SKEFTHawking.SingularExcisionIso

namespace SKEFTHawking.SingularCohomologySnake

variable {X : TopCat}

open Classical in
/-- **The `S`-part of a relative cochain**: keep `ω σ` on simplices *not* supported in `S`, zero on
`S`-simplices. By construction it vanishes on `S`-simplices, hence lies in `relCochains S`. -/
noncomputable def cochainSplit (S : Set ↑X) (n : ℕ) (ω : SingularCochain X n) : SingularCochain X n :=
  fun σ => if (∃ τ, simplexIncl S n τ = σ) then 0 else ω σ

/-- The `S`-part vanishes on `S`-chains, hence is a relative `S`-cochain. -/
theorem cochainSplit_mem_relCochains (S : Set ↑X) (n : ℕ) (ω : SingularCochain X n) :
    cochainSplit S n ω ∈ relCochains S n := by
  rw [mem_relCochains]
  intro c hc
  rw [subspaceChains, LinearMap.mem_range] at hc
  obtain ⟨d, rfl⟩ := hc
  induction d using Finsupp.induction_linear with
  | zero => rw [map_zero, kronecker_apply, Finsupp.sum_zero_index]
  | add d e hd he => rw [map_add, kronecker_add_right, hd, he, add_zero]
  | single τ s =>
      rw [chainIncl_single, kronecker_single]
      have hz : cochainSplit S n ω (simplexIncl S n τ) = 0 := if_pos ⟨τ, rfl⟩
      rw [hz, mul_zero]

/-- **The complementary part `ω - φ` is a relative `V`-cochain**, when `ω ∈ relCochains (U ∩ V)`.
On a `V`-simplex `σ` it vanishes: if `σ` is *also* a `U`-simplex it is a `U∩V`-simplex (so `ω σ = 0`);
otherwise `φ σ = ω σ` so `(ω - φ) σ = 0`. -/
theorem cochainSplit_compl_mem_relCochains (U V : Set ↑X) (n : ℕ) (ω : SingularCochain X n)
    (hω : ω ∈ relCochains (U ∩ V) n) :
    ω - cochainSplit U n ω ∈ relCochains V n := by
  rw [mem_relCochains]
  intro c hc
  rw [subspaceChains, LinearMap.mem_range] at hc
  obtain ⟨d, rfl⟩ := hc
  induction d using Finsupp.induction_linear with
  | zero => rw [map_zero, kronecker_apply, Finsupp.sum_zero_index]
  | add d e hd he => rw [map_add, kronecker_add_right, hd, he, add_zero]
  | single τ s =>
      rw [chainIncl_single, kronecker_single]
      have hψ : (ω - cochainSplit U n ω) (simplexIncl V n τ) = 0 := by
        show ω (simplexIncl V n τ) - cochainSplit U n ω (simplexIncl V n τ) = 0
        by_cases hin : ∃ τ'', simplexIncl U n τ'' = simplexIncl V n τ
        · have hcU : cochainSplit U n ω (simplexIncl V n τ) = 0 := if_pos hin
          rw [hcU, sub_zero]
          obtain ⟨τ'', hτ''⟩ := hin
          have hsubV : Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) (simplexIncl V n τ)) ⊆ V := by
            rw [simplexIncl_range_subset_iff V V τ]; exact fun x _ => x.2
          have hsubU : Set.range (X.toSSetObjEquiv (op (SimplexCategory.mk n)) (simplexIncl V n τ)) ⊆ U := by
            rw [← hτ'', simplexIncl_range_subset_iff U U τ'']; exact fun x _ => x.2
          have hmem : Finsupp.single (simplexIncl V n τ) (1 : ZMod 2) ∈ subspaceChains (U ∩ V) n :=
            single_mem_subspaceChains_of_subordinate (Set.subset_inter hsubU hsubV)
          have hzero := (mem_relCochains (U ∩ V) n ω).mp hω _ hmem
          rw [kronecker_single, one_mul] at hzero
          exact hzero
        · have hcU : cochainSplit U n ω (simplexIncl V n τ) = ω (simplexIncl V n τ) := if_neg hin
          rw [hcU, sub_self]
      rw [hψ, mul_zero]

/-- The split reconstitutes `ω`: `φ + (ω - φ) = ω`. -/
theorem cochainSplit_add_compl (U : Set ↑X) (n : ℕ) (ω : SingularCochain X n) :
    cochainSplit U n ω + (ω - cochainSplit U n ω) = ω := by abel

/-! ## §2. The split coboundary is a **cover-complex cocycle** (snake brick S1)

`δφ` lies in the cover complex `relCochains U ∩ relCochains V`: the `U`-membership is unconditional (`φ`
is a relative `U`-cochain, and the coboundary preserves relative cochains); the `V`-membership holds when
`ω` is a cocycle (`δω = 0 ⟹ δφ = δψ` over `ℤ/2`, and `ψ = ω - φ` is a relative `V`-cochain). This is the
function-level (subdivision-free) Mayer–Vietoris cohomology connecting datum *at the cover level* — where
`δφ` is a genuine cochain rep (the union-level rep would need the dual small-simplices iso, which the cap
against an overlap cycle sidesteps via cap-naturality w.r.t. the cover↪union inclusion). -/

/-- **`δφ ∈ relCochains U`** (unconditional): the coboundary of the `U`-part is a relative `U`-cochain. -/
theorem cochainSplit_coboundary_mem_U (U : Set ↑X) (n : ℕ) (ω : SingularCochain X n) :
    coboundary X n (cochainSplit U n ω) ∈ relCochains U (n + 1) :=
  coboundary_mem_relCochains U n _ (cochainSplit_mem_relCochains U n ω)

/-- **`δφ ∈ relCochains V`** when `ω` is a cocycle: from `δ(φ + (ω - φ)) = δω = 0` over `ℤ/2`,
`δφ = -δ(ω - φ)`, and `ω - φ ∈ relCochains V` (S0) with the coboundary preserving relative cochains. -/
theorem cochainSplit_coboundary_mem_V (U V : Set ↑X) (n : ℕ) (ω : SingularCochain X n)
    (hω : ω ∈ relCochains (U ∩ V) n) (hcoc : coboundary X n ω = 0) :
    coboundary X n (cochainSplit U n ω) ∈ relCochains V (n + 1) := by
  have hδψ : coboundary X n (ω - cochainSplit U n ω) ∈ relCochains V (n + 1) :=
    coboundary_mem_relCochains V n _ (cochainSplit_compl_mem_relCochains U V n ω hω)
  have hsum : coboundary X n (cochainSplit U n ω) + coboundary X n (ω - cochainSplit U n ω) = 0 := by
    have h := congrArg (coboundaryₗ X n) (cochainSplit_add_compl U n ω)
    rw [map_add] at h
    simpa only [coboundaryₗ, LinearMap.coe_mk, AddHom.coe_mk, hcoc] using h
  rw [eq_neg_of_add_eq_zero_left hsum]
  exact (relCochains V (n + 1)).neg_mem hδψ

end SKEFTHawking.SingularCohomologySnake
