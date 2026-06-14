/-
# Machine-checked `Ext^s_{A(1)}(J, F₂)` dimensions for the joker module `J` (s = 0,1,2)

Phase 5q.F, W4f. Mirrors `KspExt.lean` / `A1ExtSubstantive.lean` for the **joker** `J = A(1)/(A(1)·Sq³)`
— the *direct* Pin⁺ Adams-`E₂` module (the bottom-cell module of `H*(MTPin⁺)`, Campbell Ex. 3.6),
whereas `K = ksp` is the cleaner `Σ⁻⁴ko⟨4⟩` carrier. The dual coboundary maps `δˢ` of `J`'s dualized
minimal resolution (`JokerResolution.lean`) are augmentation-extracted from the certified `d₁ = R(Sq³)`,
`d₂ = [R(Sq¹) | R(Sq⁵+Sq⁴Sq¹)]` and **vanish by minimality**, so `dim Ext^s_{A(1)}(J, F₂) = rank P_s`:

  `Ext⁰(J) = 1`,   `Ext¹(J) = 1`,   `Ext²(J) = 2`   (= ranks of `P₀ = A(1)`, `P₁ = Σ³A(1)`,
  `P₂ = Σ⁴A(1) ⊕ Σ⁸A(1)`).

These match Campbell's joker Adams chart being a **truncation of the `A(1)` chart** (BC18 Ex. 4.6.6,
Fig. 29): `Ext⁰,¹` are `𝔽₂` (the bottom cell), `Ext²` is `𝔽₂²`. Genuine `Module.finrank`, not `cols/8`.

## Honest scope (same disclosed gap as `KspExt`/`PinPlusExtBound`)

The degree-4 column (the Pin⁺ `ℤ/16` `h₀`-tower) appears only at `s ≥ 4` (Campbell's `δ`-truncation of
the `M`-tower), which needs `d₃, d₄` as full matrices and — for the height-4 **cap** giving `16` — the
topological assembly (Pontryagin–Thom / ABP / the spectrum-level `δ`), absent from Mathlib. This module
ships the directly-certified `Ext⁰,¹,²(J)` (the `E₂`-page base); the cap stays the disclosed Prop.
-/
import Mathlib
import SKEFTHawking.JokerResolution

namespace SKEFTHawking.JokerExt

open Matrix SKEFTHawking.JokerRes SKEFTHawking.KspRes

/-! ## §1. Dual coboundary maps `δˢ` (augmentation-extracted from `d_{s+1}`) -/

/-- `δ⁰ : Hom(P₀,F₂) = F₂¹ → Hom(P₁,F₂) = F₂¹`, from `d₁ = R(Sq³)`. -/
def delta0J : Matrix (Fin 1) (Fin 1) F2 :=
  Matrix.of fun k j => d1J ⟨8 * j.val, by have := j.isLt; omega⟩ ⟨8 * k.val, by have := k.isLt; omega⟩

/-- `δ¹ : F₂¹ → F₂²`, from `d₂ = [R(Sq¹) | R(Sq⁵+Sq⁴Sq¹)]`. -/
def delta1J : Matrix (Fin 2) (Fin 1) F2 :=
  Matrix.of fun k j => d2J ⟨8 * j.val, by have := j.isLt; omega⟩ ⟨8 * k.val, by have := k.isLt; omega⟩

/-! ## §2. The dual coboundaries vanish (minimality ⟹ `Ext = Hom`) -/

/-- `δ⁰ = 0` — minimality of `d₁` (`Sq³` positive-degree: augmentation row vanishes). -/
theorem delta0J_eq_zero : delta0J = 0 := by decide

/-- `δ¹ = 0` — minimality of `d₂` (both syzygies positive-degree). -/
theorem delta1J_eq_zero : delta1J = 0 := by decide

/-! ## §3. The `Ext^s(J)` dimensions as genuine `F₂`-vector-space finranks -/

/-- The `Hom`-space at degree `s` has `F₂`-dimension `r` (genuine `finrank`). -/
theorem hom_space_finrank (r : ℕ) : Module.finrank F2 (Fin r → F2) = r := by simp

/-- **`dim Ext⁰_{A(1)}(J, F₂) = 1`** — `H⁰ = ker δ⁰ = ⊤`, `finrank = rank P₀ = 1`. -/
theorem jokerExt0_dim : Module.finrank F2 (LinearMap.ker (mulVecLin delta0J)) = 1 := by
  rw [show LinearMap.ker (mulVecLin delta0J) = ⊤ by rw [delta0J_eq_zero]; simp, finrank_top]
  exact hom_space_finrank 1

/-- **`dim Ext¹_{A(1)}(J, F₂) = 1`** — `H¹ = F₂¹/im δ⁰`, `im δ⁰ = ⊥`, `finrank = rank P₁ = 1`. -/
theorem jokerExt1_dim :
    Module.finrank F2 ((Fin 1 → F2) ⧸ LinearMap.range (mulVecLin delta0J)) = 1 := by
  rw [show LinearMap.range (mulVecLin delta0J) = ⊥ by rw [delta0J_eq_zero]; simp,
    (Submodule.quotEquivOfEqBot _ rfl).finrank_eq]
  exact hom_space_finrank 1

/-- **`dim Ext²_{A(1)}(J, F₂) = 2`** — `H² = F₂²/im δ¹`, `im δ¹ = ⊥`, `finrank = rank P₂ = 2`. -/
theorem jokerExt2_dim :
    Module.finrank F2 ((Fin 2 → F2) ⧸ LinearMap.range (mulVecLin delta1J)) = 2 := by
  rw [show LinearMap.range (mulVecLin delta1J) = ⊥ by rw [delta1J_eq_zero]; simp,
    (Submodule.quotEquivOfEqBot _ rfl).finrank_eq]
  exact hom_space_finrank 2

/-- **The dual coboundaries vanish + the first three joker `Ext` dimensions** (`1, 1, 2`) — the
machine-checked `Ext_{A(1)}(J, F₂)` `E₂`-page base for the *direct* Pin⁺ module (a truncation of the
`A(1)` chart; the degree-4 `ℤ/16` `h₀`-tower at `s ≥ 4` stays the disclosed topological cap). -/
theorem joker_ext_dims :
    delta0J = 0 ∧ delta1J = 0 ∧
      Module.finrank F2 (LinearMap.ker (mulVecLin delta0J)) = 1 ∧
        Module.finrank F2 ((Fin 1 → F2) ⧸ LinearMap.range (mulVecLin delta0J)) = 1 ∧
          Module.finrank F2 ((Fin 2 → F2) ⧸ LinearMap.range (mulVecLin delta1J)) = 2 :=
  ⟨delta0J_eq_zero, delta1J_eq_zero, jokerExt0_dim, jokerExt1_dim, jokerExt2_dim⟩

end SKEFTHawking.JokerExt
