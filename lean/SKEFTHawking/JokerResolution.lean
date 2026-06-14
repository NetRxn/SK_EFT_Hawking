import Mathlib
import SKEFTHawking.KspResolution

/-!
# Minimal free `A(1)`-resolution of the joker module `J` — steps 1–2

Phase 5q.F, W4d. The joker `J = A(1)/(A(1)·Sq³)` (`JokerModule.lean`) is the **direct** Pin⁺ Adams-`E₂`
input — the bottom-cell module of `H*(MTPin⁺)` (Campbell [1708.04264] Ex. 3.6) — whereas `K = ksp`
(`KspResolution.lean`) is the cleaner `Σ⁻⁴ko⟨4⟩` carrier. This builds the start of `J`'s minimal free
resolution as concrete `F₂` matrices, per `Lit-Search/Phase-5qF/A1_resolution_higher_syzygies.md` §3.3
(Campbell eq. (5.10), re-derived + verified generator-for-generator), reusing the `A(1)` right-regular
representations from `KspResolution` (`Rsq1 = R(Sq¹)`, `Re6 = R(Sq²Sq¹Sq² = Sq⁵+Sq⁴Sq¹)`,
`Rsq3 = R(Sq³) = Rsq2·Rsq1`).

  `J ← A(1) ← Σ³A(1) ← Σ⁴A(1) ⊕ Σ⁸A(1) ← …`,   `d₁ = R(Sq³)`,   `d₂ = [R(Sq¹) | R(Sq⁵+Sq⁴Sq¹)]`.

The left ideal `A(1)·Sq³ = span{Sq³, Sq⁵+Sq⁴Sq¹, Sq⁵Sq¹} = {e₃, e₆, e₇}` (3-dim) is `ker ε`; the reps
`{e₀,e₁,e₂,e₄,e₅} = {1, Sq¹, Sq², Sq²Sq¹, Sq³Sq¹}` (degrees `0,1,2,3,4`) are `j₀,…,j₄`. (As with
`chain_d1_d2`, chain properties are verified via the A(1)-monomial block identities, kernel `decide`.)
-/

namespace SKEFTHawking.JokerRes

open SKEFTHawking.KspRes

/-- The augmentation `ε : P₀ = A(1) ↠ J`. Rows `j₀..j₄` pick the reps `e₀,e₁,e₂,e₄,e₅`; the ideal
generators `e₃ (= Sq³), e₆ (= Sq⁵+Sq⁴Sq¹), e₇ (= Sq⁵Sq¹)` map to `0`. -/
def epsJ : Matrix (Fin 5) (Fin 8) F2 :=
  !![1,0,0,0,0,0,0,0;
     0,1,0,0,0,0,0,0;
     0,0,1,0,0,0,0,0;
     0,0,0,0,1,0,0,0;
     0,0,0,0,0,1,0,0]

/-- The first differential `d₁ : P₁ = Σ³A(1) → P₀ = A(1)` is right multiplication by the single
relation `Sq³`, i.e. `R(Sq³) = Rsq3` (`= Rsq2·Rsq1`, from `KspResolution`). -/
def d1J : Matrix (Fin 8) (Fin 8) F2 := Rsq3

/-- **Chain property at `P₀`:** `ε ∘ d₁ = 0`. The relation `Sq³` lands in the ideal `A(1)Sq³ = ker ε`
(`{e₃,e₆,e₇}`: `1·Sq³=e₃`, `Sq²·Sq³=e₆`, `Sq³·Sq³=e₇`), so `ε` annihilates `im d₁`. -/
theorem epsJ_d1J_zero : epsJ * d1J = 0 := by decide

/-- **Minimality** of `d₁`: no unit (`e₀`) component — its `e₀`-row (row 0) is zero (`Sq³` is
positive-degree). -/
theorem d1J_minimal : ∀ j, d1J 0 j = 0 := by decide

/-- `im d₁ = ker ε` (the ideal `A(1)Sq³`, 3-dim): `d₁` hits each ideal generator —
`e₃ (= 1·Sq³)`, `e₆ (= Sq²·Sq³)`, `e₇ (= Sq³·Sq³)`. -/
theorem d1J_hits_ideal : d1J 3 0 = 1 ∧ d1J 6 2 = 1 ∧ d1J 7 3 = 1 := by decide

/-- The second differential `d₂ : P₂ = Σ⁴A(1) ⊕ Σ⁸A(1) → P₁ = A(1)` is `[R(Sq¹) | R(Sq⁵+Sq⁴Sq¹)]` —
the two minimal syzygies of `Sq³`: `Sq¹` (degree-4 generator) and `Sq⁵+Sq⁴Sq¹ = e₆` (degree-8). -/
def d2J : Matrix (Fin 8) (Fin 16) F2 :=
  Matrix.of fun k i => if h : i.val < 8 then Rsq1 k ⟨i.val, h⟩ else Re6 k ⟨i.val - 8, by omega⟩

/-- **Chain property `d₁ ∘ d₂ = 0`**, block-decomposed (`R(y)·R(x) = R(x·y)`, right multiplication):
* gen 0 `(Sq¹)`: `R(Sq³)·R(Sq¹) = R(Sq¹·Sq³) = R(0) = 0` (Adem `Sq¹Sq³ = 0`);
* gen 1 `(e₆)`: `R(Sq³)·R(e₆) = R(e₆·Sq³) = R(0) = 0` (degree `5+3 = 8 > 6`, above `A(1)`'s top class).
So both syzygy generators lie in `ker d₁`. -/
theorem chain_d1J_d2J : Rsq3 * Rsq1 = 0 ∧ Rsq3 * Re6 = 0 := by
  refine ⟨by decide, by decide⟩

/-- **Minimality** of `d₂`: no unit (`e₀`) component — its `e₀`-row (row 0) is zero (both syzygies
`Sq¹` and `Sq⁵+Sq⁴Sq¹` are positive-degree). -/
theorem d2J_minimal : ∀ j, d2J 0 j = 0 := by decide

end SKEFTHawking.JokerRes
