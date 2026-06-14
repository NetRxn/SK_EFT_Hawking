/-
# `M = A(1)//A(0)` minimal resolution + `Ext_{A(1)}(M, F₂) = F₂[h₀]` (the prototype `h₀`-tower)

Phase 5q.F, W4h. `M = A(1)/(A(1)Sq¹)` (`MModule.lean`) has the **single-generator, single-`Sq¹`** minimal
free resolution `M ← A(1) ← Σ¹A(1) ← Σ²A(1) ← …`, every differential `dₛ = R(Sq¹)` (Campbell eq. (5.9);
BC18 (4.4.1)). Hence `Ext_{A(1)}(M, F₂) = F₂[h₀]` — the **single infinite `h₀`-tower** in column `t−s = 0`
(BC18 Ex. 4.5.5, change-of-rings to `Ext_{A(0)}(F₂,F₂)`). This is the prototype tower whose **height-4
truncation** (via the Campbell `δ = ·h₀` cokernel of `0 → Σ¹F₂ → Σ¹H*RP^∞₋₁ → M → 0`, eq. 6.17-6.18)
gives the Pin⁺ `t−s=4` column → `ℤ/2⁴ = ℤ/16`. So `Ext(M)` is the substrate of the **finite** upper-bound
δ-cokernel computation (Phase-5qF roadmap W4; syzygy note §4.2/§5(B)).

Reuses the `A(1)` right-regular rep `Rsq1 = R(Sq¹)` from `KspResolution.lean`.
-/
import Mathlib
import SKEFTHawking.KspResolution
import SKEFTHawking.MModule

namespace SKEFTHawking.MRes

open Matrix SKEFTHawking.KspRes

/-! ## §1. The minimal free resolution `M ← A(1) ← Σ¹A(1) ← …`, all differentials `R(Sq¹)` -/

/-- The augmentation `ε : P₀ = A(1) ↠ M`. Rows `m₀,m₂,m₃,m₅` pick the reps `e₀,e₂,e₃,e₆`
(`= 1, Sq², Sq³, Sq⁵+Sq⁴Sq¹`); the ideal `A(1)Sq¹ = {e₁,e₄,e₅,e₇}` (`= ker ε`) maps to `0`. -/
def epsM : Matrix (Fin 4) (Fin 8) F2 :=
  !![1,0,0,0,0,0,0,0;
     0,0,1,0,0,0,0,0;
     0,0,0,1,0,0,0,0;
     0,0,0,0,0,0,1,0]

/-- Every differential of `M`'s minimal resolution is `R(Sq¹) = Rsq1` (single `Sq¹`-tower). -/
def dM : Matrix (Fin 8) (Fin 8) F2 := Rsq1

/-- **Chain property at `P₀`:** `ε ∘ d₁ = 0`. The relation `Sq¹` lands in the ideal `A(1)Sq¹ = ker ε`. -/
theorem epsM_dM_zero : epsM * dM = 0 := by decide

/-- **Minimality**: `d`'s `e₀`-row (row 0) is zero (`Sq¹` is positive-degree). -/
theorem dM_minimal : ∀ j, dM 0 j = 0 := by decide

/-- **Chain property `dₛ ∘ dₛ₊₁ = 0`** at every stage: `R(Sq¹)·R(Sq¹) = R(Sq¹Sq¹) = 0`. So
`M ← A(1) ←^{Sq¹} Σ¹A(1) ←^{Sq¹} Σ²A(1) ← …` is a genuine (minimal) free resolution. -/
theorem dM_dM_zero : dM * dM = 0 := by decide

/-- `im d₁ = ker ε` (the ideal `A(1)Sq¹`, 4-dim): `d₁ = R(Sq¹)` hits each ideal generator
`e₁ (=1·Sq¹), e₄ (=Sq²·Sq¹), e₅ (=Sq³·Sq¹), e₇ (=(Sq⁵+Sq⁴Sq¹)·Sq¹ = Sq⁵Sq¹)`. -/
theorem dM_hits_ideal : dM 1 0 = 1 ∧ dM 4 2 = 1 ∧ dM 5 3 = 1 ∧ dM 7 6 = 1 := by decide

/-! ## §2. `Ext^s(M) = F₂` for all `s` — the single `h₀`-tower (`Ext(M) = F₂[h₀]`)

The dualized resolution has dual coboundary `δˢ(k,j) = dₛ₊₁(8j, 8k) = R(Sq¹)(8j, 8k) = 0` (minimality:
`R(Sq¹)`'s augmentation row vanishes), so `dim Ext^s(M) = rank P_s = 1` at every `s`. -/

/-- `δˢ : Hom(Pₛ,F₂) = F₂¹ → Hom(Pₛ₊₁,F₂) = F₂¹`, augmentation-extracted from `dₛ₊₁ = R(Sq¹)`. -/
def deltaM : Matrix (Fin 1) (Fin 1) F2 :=
  Matrix.of fun k j => dM ⟨8 * j.val, by have := j.isLt; omega⟩ ⟨8 * k.val, by have := k.isLt; omega⟩

/-- `δˢ = 0` — minimality of `R(Sq¹)`. -/
theorem deltaM_eq_zero : deltaM = 0 := by decide

/-- **`dim Ext^s_{A(1)}(M, F₂) = 1` at every `s`** (the single `h₀`-tower `Ext(M) = F₂[h₀]`). Since the
resolution is the constant `R(Sq¹)`-tower, every `δˢ = δᴹ = 0`, so `Ext^s = ker δˢ = F₂¹`. We record the
generic stage `Ext^s = ker δᴹ`, finrank 1 — the prototype tower the Pin⁺ δ-truncation caps at height 4. -/
theorem MExt_dim : Module.finrank F2 (LinearMap.ker (mulVecLin deltaM)) = 1 := by
  rw [show LinearMap.ker (mulVecLin deltaM) = ⊤ by rw [deltaM_eq_zero]; simp, finrank_top]
  simp

end SKEFTHawking.MRes
