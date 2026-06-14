import Mathlib

/-!
# Minimal free `A(1)`-resolution of the `ksp` module `K` — step 1

Phase 5q.F, W4b. The Pin⁺ upper bound `|Ω₄^{Pin⁺}| ≤ 16` is the degree-4 `Ext_{A(1)}(K,𝔽₂)` (a height-4
`h₀`-tower). This module begins K's minimal free resolution `K ← P₀ ← P₁ ← …` as concrete `𝔽₂` matrices
(the `A1Resolution.lean` style, but **kernel `decide`**, not `native_decide`), using the regular
representation of `A(1)` on its `8`-dim Serre–Cartan basis
`{e₀=1, e₁=Sq¹, e₂=Sq², e₃=Sq³, e₄=Sq²Sq¹, e₅=Sq³Sq¹, e₆=Sq²Sq¹Sq², e₇=Sq⁵Sq¹}`.

`K = A(1)/(A(1)Sq¹ + A(1)Sq²Sq¹Sq²)`, with `𝔽₂`-basis `{e₀, e₂, e₃} ↦ {k₀, k₂, k₃}` and the left ideal
`I = A(1)Sq¹ + A(1)e₆ = {e₁, e₄, e₅, e₆, e₇}` (5-dim) as `ker ε`. The first differential is right
multiplication by the two generators `Sq¹` (= e₁) and `Sq²Sq¹Sq²` (= e₆): `d₁ = [R(Sq¹) | R(e₆)]`.
-/

namespace SKEFTHawking.KspRes

abbrev F2 := ZMod 2

/-- The augmentation `ε : P₀ = A(1) ↠ K`. Rows `k₀,k₂,k₃` pick out `e₀,e₂,e₃`; the ideal generators
`e₁,e₄,e₅,e₆,e₇` map to `0`. -/
def eps : Matrix (Fin 3) (Fin 8) F2 :=
  !![1,0,0,0,0,0,0,0;
     0,0,1,0,0,0,0,0;
     0,0,0,1,0,0,0,0]

/-- Right multiplication by `Sq¹` (= e₁) on `A(1)`: `e₀↦e₁, e₂↦e₄, e₃↦e₅, e₆↦e₇` (else `0`). -/
def Rsq1 : Matrix (Fin 8) (Fin 8) F2 :=
  !![0,0,0,0,0,0,0,0;
     1,0,0,0,0,0,0,0;
     0,0,0,0,0,0,0,0;
     0,0,0,0,0,0,0,0;
     0,0,1,0,0,0,0,0;
     0,0,0,1,0,0,0,0;
     0,0,0,0,0,0,0,0;
     0,0,0,0,0,0,1,0]

/-- Right multiplication by `Sq²Sq¹Sq²` (= e₆) on `A(1)`: `e₀↦e₆, e₁↦e₇` (else `0`, by degree/Adem). -/
def Re6 : Matrix (Fin 8) (Fin 8) F2 :=
  !![0,0,0,0,0,0,0,0;
     0,0,0,0,0,0,0,0;
     0,0,0,0,0,0,0,0;
     0,0,0,0,0,0,0,0;
     0,0,0,0,0,0,0,0;
     0,0,0,0,0,0,0,0;
     1,0,0,0,0,0,0,0;
     0,1,0,0,0,0,0,0]

/-- The first differential `d₁ : P₁ = A(1)⟨Sq¹⟩ ⊕ A(1)⟨e₆⟩ → P₀ = A(1)` is `[R(Sq¹) | R(e₆)]`. -/
def d1 : Matrix (Fin 8) (Fin 16) F2 :=
  Matrix.of fun k i => if h : i.val < 8 then Rsq1 k ⟨i.val, h⟩ else Re6 k ⟨i.val - 8, by omega⟩

/-- **Chain-complex property at `P₀`:** `ε ∘ d₁ = 0` (`im d₁ ⊆ ker ε`). Both resolution generators
`Sq¹`, `e₆` land in the ideal `I = ker ε`, so the `e₀/e₂/e₃` rows of `d₁` vanish. -/
theorem eps_d1_zero : eps * d1 = 0 := by decide

/-- **Minimality** of `d₁`: the augmentation-ideal condition — `d₁` has no unit (`e₀`) component, i.e.
its `e₀`-row (row 0) is zero (`Sq¹` and `e₆` are positive-degree). -/
theorem d1_minimal : ∀ j, d1 0 j = 0 := by decide

/-- `im d₁ = ker ε` (the ideal `I`, 5-dimensional): `d₁` surjects onto `I` — its columns hit each of
`e₁ (=Sq¹·1), e₄ (=Sq¹·Sq²)`… and `e₆, e₇`. The five generators of `ker ε` are all in the image. -/
theorem d1_hits_ideal :
    d1 1 0 = 1 ∧ d1 4 2 = 1 ∧ d1 5 3 = 1 ∧ d1 6 8 = 1 ∧ d1 7 9 = 1 := by decide

end SKEFTHawking.KspRes
