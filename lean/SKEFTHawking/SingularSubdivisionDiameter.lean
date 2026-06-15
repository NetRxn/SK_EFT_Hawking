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

end SKEFTHawking.SingularSubdivisionDiameter
