/-
# Phase 5q.F (w₂-foundation, brick 6c-c8.3): the barycentric-subdivision diameter estimate

The analytic heart of excision: barycentric subdivision shrinks simplices geometrically. The key
metric fact is the **barycenter-to-vertex bound** — in a normed `ℝ`-space, the barycenter of a simplex
is within `(n/(n+1))·d` of each of its vertices (`d` = the diameter), because the `i=j` term of
`barycenter v − vⱼ = (n+1)⁻¹ ∑ᵢ(vᵢ−vⱼ)` vanishes. The factor `n/(n+1) < 1` is what drives
`diam(Sdᵐ pieces) → 0`. Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularExcisionMod2

namespace SKEFTHawking.SingularSubdivisionDiameter

open SKEFTHawking.SingularExcisionMod2

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- `barycenter v − vⱼ = (n+1)⁻¹ ∑ᵢ (vᵢ − vⱼ)` (the centered form; the `i=j` term is `0`). -/
theorem barycenter_sub_vertex {n : ℕ} (v : Fin (n + 1) → V) (j : Fin (n + 1)) :
    barycenter v - v j = ((n : ℝ) + 1)⁻¹ • ∑ i, (v i - v j) := by
  have hne : ((n : ℝ) + 1) ≠ 0 := by positivity
  rw [barycenter, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    smul_sub, sub_right_inj, ← Nat.cast_smul_eq_nsmul ℝ, Nat.cast_add, Nat.cast_one, smul_smul,
    inv_mul_cancel₀ hne, one_smul]

/-- **Barycenter-to-vertex bound**: `‖barycenter v − vⱼ‖ ≤ (n/(n+1))·d` when `‖vᵢ − vⱼ‖ ≤ d` for all `i`.
The `(n/(n+1)) < 1` factor that makes barycentric subdivision contract. -/
theorem norm_barycenter_sub_vertex_le {n : ℕ} (v : Fin (n + 1) → V) (j : Fin (n + 1)) {d : ℝ}
    (hd : ∀ i, ‖v i - v j‖ ≤ d) :
    ‖barycenter v - v j‖ ≤ ((n : ℝ) / ((n : ℝ) + 1)) * d := by
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hsum : ‖∑ i, (v i - v j)‖ ≤ (n : ℝ) * d := by
    calc ‖∑ i, (v i - v j)‖ ≤ ∑ i, ‖v i - v j‖ := norm_sum_le _ _
      _ = ∑ i ∈ Finset.univ.erase j, ‖v i - v j‖ := by
          rw [Finset.sum_erase _ (by rw [sub_self, norm_zero])]
      _ ≤ (Finset.univ.erase j).card • d :=
          Finset.sum_le_card_nsmul _ _ _ (fun i _ => hd i)
      _ = (n : ℝ) * d := by
          rw [Finset.card_erase_of_mem (Finset.mem_univ j), Finset.card_univ, Fintype.card_fin,
            Nat.add_sub_cancel, nsmul_eq_mul]
  rw [barycenter_sub_vertex, norm_smul, norm_inv, Real.norm_of_nonneg hpos.le]
  calc ((n : ℝ) + 1)⁻¹ * ‖∑ i, (v i - v j)‖
      ≤ ((n : ℝ) + 1)⁻¹ * ((n : ℝ) * d) := mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ((n : ℝ) / ((n : ℝ) + 1)) * d := by field_simp

/-- **Convexity distance bound**: a fixed point `b` is within `δ` of *any* point of the affine simplex
on `w` whenever it is within `δ` of every vertex `wₖ` (`b − ∑ tₖwₖ = ∑ tₖ(b − wₖ)`, `∑ tₖ = 1`). Used
in the sub-simplex diameter bound: the subdivision vertices lie in the parent faces. -/
theorem norm_sub_affineSimplex_le {n : ℕ} (b : V) (w : Fin (n + 1) → V)
    (t : stdSimplex ℝ (Fin (n + 1))) {δ : ℝ} (h : ∀ k, ‖b - w k‖ ≤ δ) :
    ‖b - affineSimplex w t‖ ≤ δ := by
  have hnn : ∀ k, (0 : ℝ) ≤ (t : Fin (n + 1) → ℝ) k := t.2.1
  have hs1 : ∑ k, (t : Fin (n + 1) → ℝ) k = 1 := t.2.2
  have hb : b = ∑ k, (t : Fin (n + 1) → ℝ) k • b := by
    rw [← Finset.sum_smul, hs1, one_smul]
  rw [affineSimplex_apply, hb, ← Finset.sum_sub_distrib]
  calc ‖∑ k, ((t : Fin (n + 1) → ℝ) k • b - (t : Fin (n + 1) → ℝ) k • w k)‖
      ≤ ∑ k, ‖(t : Fin (n + 1) → ℝ) k • b - (t : Fin (n + 1) → ℝ) k • w k‖ := norm_sum_le _ _
    _ = ∑ k, (t : Fin (n + 1) → ℝ) k * ‖b - w k‖ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [← smul_sub, norm_smul, Real.norm_of_nonneg (hnn k)]
    _ ≤ ∑ k, (t : Fin (n + 1) → ℝ) k * δ :=
        Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_left (h k) (hnn k)
    _ = δ := by rw [← Finset.sum_mul, hs1, one_mul]

end SKEFTHawking.SingularSubdivisionDiameter
