/-
# Phase 5q.F (w₂-foundation, brick 6c) — barycentric subdivision and excision (ℤ/2)

The excision engine for singular ℤ/2 homology: the **barycentric subdivision operator** `Sd` and the
natural **chain homotopy** `T` with `∂T + T∂ = 1 − Sd`, whose iterate `Sdᵐ` shrinks simplices into any
open cover (the small-simplices theorem) ⟹ excision `Hₙ(X,A) ≅ Hₙ(X∖Z, A∖Z)`. Needed to compute the
local homology `Hₙ(ℝⁿ, ℝⁿ∖0) ≅ ℤ/2` → the ℤ/2 fundamental class → Poincaré duality. Mathlib has none of
this (verified 2026-06-15: no subdivision/excision/sphere-homology), but has the convex/affine geometry
(`stdSimplex` convexity, convex combinations) the construction runs on.

This first sub-brick (c1) builds the **affine (linear) singular simplices** `[v₀,…,vₙ] : Δⁿ → V`
(`t ↦ ∑ tᵢ vᵢ`) and the **cone operator** foundation — the geometric atoms of the subdivision (Hatcher
§2.1). Kernel-pure (`{propext, Classical.choice, Quot.sound}`).
-/
import Mathlib
import SKEFTHawking.SingularHomologyMod2

namespace SKEFTHawking.SingularExcisionMod2

open CategoryTheory Opposite

variable {V : Type*} [AddCommGroup V] [Module ℝ V] [TopologicalSpace V]
  [ContinuousAdd V] [ContinuousSMul ℝ V]

/-- The **affine `n`-simplex** `[v₀, …, vₙ] : Δⁿ → V` on vertices `v : Fin (n+1) → V`: the convex-affine
map `t ↦ ∑ᵢ tᵢ • vᵢ` from the topological standard simplex `stdSimplex ℝ (Fin (n+1))`. The basic atom of
the barycentric subdivision. -/
noncomputable def affineSimplex {n : ℕ} (v : Fin (n + 1) → V) :
    C(stdSimplex ℝ (Fin (n + 1)), V) where
  toFun t := ∑ i, (t : Fin (n + 1) → ℝ) i • v i
  continuous_toFun := by
    refine continuous_finset_sum _ (fun i _ => ?_)
    exact (continuous_apply i |>.comp continuous_subtype_val).smul continuous_const

@[simp] theorem affineSimplex_apply {n : ℕ} (v : Fin (n + 1) → V) (t : stdSimplex ℝ (Fin (n + 1))) :
    affineSimplex v t = ∑ i, (t : Fin (n + 1) → ℝ) i • v i := rfl

/-- The value of an affine simplex on a vertex `e_j` of `Δⁿ` is the corresponding vertex `v_j`
(`∑ᵢ δᵢⱼ vᵢ = v_j`). -/
theorem affineSimplex_vertex {n : ℕ} (v : Fin (n + 1) → V) (j : Fin (n + 1)) :
    affineSimplex v ⟨Pi.single j 1, by
      constructor
      · intro i; rcases eq_or_ne i j with h | h
        · subst h; simp
        · simp [Pi.single_eq_of_ne h]
      · simp⟩ = v j := by
  simp only [affineSimplex_apply]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi; simp [Pi.single_eq_of_ne hi]
  · intro h; exact absurd (Finset.mem_univ j) h

end SKEFTHawking.SingularExcisionMod2
