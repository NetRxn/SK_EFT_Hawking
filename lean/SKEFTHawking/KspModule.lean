import Mathlib

/-!
# The `ksp` `A(1)`-module `K` (the cleanest Pin⁺ upper-bound module)

Phase 5q.F, W4b. The cleanest single module realizing the degree-4 `2⁴ = 16` of `|Ω₄^{Pin⁺}| ≤ 16`
(`Lit-Search/Phase-5qF/A1_Ext_upper_bound.md` §2.4f, §3.4): the 3-dimensional

  `K = A(1)/(A(1)·Sq¹ + A(1)·Sq²Sq¹Sq²)`,   basis `{k₀, k₂, k₃}` in degrees `0,2,3`,   `p_K = 1+t²+t³`,
  `K ≅ Σ⁻⁴ H*(ko⟨4⟩) = H*(ksp)`  (Mills [2306.17709] §3, Cor 3.6).

Because `ko⟨4⟩` has "no cells above degree 4," the relevant `Ext_{A(1)}(K,𝔽₂)` column is a **height-4
`h₀`-tower** `→ ℤ/16` (the upper bound; the convergence rides as disclosed Props in the `ExtBordismBridge`
H1–H4 style). This module is the foundation for that resolution.

**The `A(1)`-action (re-derived + verified):** `Sq² k₀ = k₂`, `Sq¹ k₂ = k₃`, all else `0`. Verified below
to satisfy the defining Adem relations `Sq¹² = 0` and `Sq²² = Sq¹Sq²Sq¹` (both act as `0` on `K`). Matrices
act on column vectors (`mulVec`): `M i j = 1` means `kⱼ ↦ kᵢ` (basis index `k₀=0, k₂=1, k₃=2`).
-/

namespace SKEFTHawking.Ksp

abbrev F2 := ZMod 2

/-- The action of `Sq¹` on `K`: `k₂ ↦ k₃` (`Sq¹ k₀ = Sq¹ k₃ = 0`). -/
def rhoSq1 : Matrix (Fin 3) (Fin 3) F2 :=
  !![0, 0, 0;
     0, 0, 0;
     0, 1, 0]

/-- The action of `Sq²` on `K`: `k₀ ↦ k₂` (`Sq² k₂ = Sq² k₃ = 0`). -/
def rhoSq2 : Matrix (Fin 3) (Fin 3) F2 :=
  !![0, 0, 0;
     1, 0, 0;
     0, 0, 0]

/-- **Adem `Sq¹² = 0`** on `K`. -/
theorem rho_Sq1_sq : rhoSq1 * rhoSq1 = 0 := by decide

/-- **Adem `Sq²² = Sq¹Sq²Sq¹`** on `K` — both act as `0` (`Sq²k₂ = 0` and `Sq¹k₀ = 0`), confirming
`(rhoSq1, rhoSq2)` extend to a genuine `A(1)`-module structure on `K`. -/
theorem rho_Sq2_sq : rhoSq2 * rhoSq2 = rhoSq1 * rhoSq2 * rhoSq1 := by decide

/-- `Sq¹` kills the generator `k₀` (the relation `A(1)·Sq¹`). -/
theorem Sq1_kills_generator : ∀ i, rhoSq1 i 0 = 0 := by decide

/-- `Sq²Sq¹Sq²` kills the generator `k₀` (the relation `A(1)·Sq²Sq¹Sq²`): `Sq²k₀=k₂, Sq¹k₂=k₃, Sq²k₃=0`. -/
theorem Sq2Sq1Sq2_kills_generator : ∀ i, (rhoSq2 * rhoSq1 * rhoSq2) i 0 = 0 := by decide

/-- **`k₀` generates `K`**: `1, Sq², Sq¹Sq²` send `k₀` to `k₀, k₂, k₃` — so `A(1)·k₀ = K`, giving the
cyclic presentation `K = A(1)/(A(1)Sq¹ + A(1)Sq²Sq¹Sq²)`, the start of the minimal free resolution. -/
theorem ksp_cyclic :
    (1 : Matrix (Fin 3) (Fin 3) F2) 0 0 = 1 ∧ rhoSq2 1 0 = 1 ∧ (rhoSq1 * rhoSq2) 2 0 = 1 := by decide

end SKEFTHawking.Ksp
