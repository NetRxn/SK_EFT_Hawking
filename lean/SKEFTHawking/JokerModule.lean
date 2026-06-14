import Mathlib

/-!
# The joker `A(1)`-module `J` (the Pin⁺ Adams-`E₂` input)

Phase 5q.F, W4 (A(1)-Ext upper bound) foundation. By Pontryagin–Thom + the Anderson–Brown–Peterson
reduction, the Pin⁺ upper bound `|Ω₄^{Pin⁺}| ≤ 16` is the `A(1)`-Ext of the Thom-class module
`H*(MTPin⁺)`, whose bottom cell generates the **joker** `J` (Campbell [1708.04264] Ex. 3.6;
`Lit-Search/Phase-5qF/A1_Ext_upper_bound.md` §2.3–2.4). The existing project Ext machinery
(`A1Ring`/`A1Resolution`/`A1Ext`) computes `Ext_{A(1)}(𝔽₂,𝔽₂)` (the Spin/ko route); the Pin⁺ `ℤ/16`
needs this **joker** module, whose degree-4 Ext is the height-4 `h₀`-tower `= 2⁴ = 16`.

`J` is 5-dimensional, basis `{j₀,j₁,j₂,j₃,j₄}` in degrees `0,1,2,3,4`, Poincaré series `1+t+t²+t³+t⁴`.

**The `A(1)`-action (re-derived and verified here — the DR's §2.4d action was inconsistent: it had both
`Sq¹ j₂ = j₃` and `Sq¹ j₃ = j₄`, forcing `Sq¹²j₂ = j₄ ≠ 0`, contradicting `Sq¹²=0`).** The correct joker:

  `Sq¹ : j₀ ↦ j₁,  j₃ ↦ j₄`   (the two "ends"; `Sq¹ j₁ = Sq¹ j₂ = Sq¹ j₄ = 0`)
  `Sq² : j₀ ↦ j₂,  j₁ ↦ j₃,  j₂ ↦ j₄`   (the long curves; `Sq² j₃ = Sq² j₄ = 0`)

verified below to satisfy the defining Adem relations `Sq¹² = 0` and `Sq²² = Sq¹Sq²Sq¹` (= `Sq³Sq¹`),
hence to extend to a genuine `A(1)`-module. (Margolis: `H(J;Q₀) = H(J;Q₁) = 0` in the interior — `J` is
the non-free joker.) Matrices act on column vectors (`mulVec`): `M i j = 1` means `jⱼ ↦ jᵢ`.
-/

namespace SKEFTHawking.Joker

abbrev F2 := ZMod 2

/-- The action of `Sq¹` on the joker `J`: `j₀ ↦ j₁`, `j₃ ↦ j₄`. -/
def rhoSq1 : Matrix (Fin 5) (Fin 5) F2 :=
  !![0, 0, 0, 0, 0;
     1, 0, 0, 0, 0;
     0, 0, 0, 0, 0;
     0, 0, 0, 0, 0;
     0, 0, 0, 1, 0]

/-- The action of `Sq²` on the joker `J`: `j₀ ↦ j₂`, `j₁ ↦ j₃`, `j₂ ↦ j₄`. -/
def rhoSq2 : Matrix (Fin 5) (Fin 5) F2 :=
  !![0, 0, 0, 0, 0;
     0, 0, 0, 0, 0;
     1, 0, 0, 0, 0;
     0, 1, 0, 0, 0;
     0, 0, 1, 0, 0]

/-- **Adem relation `Sq¹² = 0`** holds on `J`. -/
theorem rho_Sq1_sq : rhoSq1 * rhoSq1 = 0 := by decide

/-- **Adem relation `Sq²² = Sq¹Sq²Sq¹` (= `Sq³Sq¹`)** holds on `J` — both send `j₀ ↦ j₄`, else `0`.
Together with `Sq¹²=0` this is the defining-relation check that `(rhoSq1, rhoSq2)` extend to a genuine
`A(1)`-module structure on `J`. -/
theorem rho_Sq2_sq : rhoSq2 * rhoSq2 = rhoSq1 * rhoSq2 * rhoSq1 := by decide

/-- `Sq²` is *not* nilpotent of order 2 alone, but `Sq²·Sq²·Sq²` resp. the degree-bound kills `J` above
degree 4: `Sq²` cubed is `0` (no room — `J` tops at degree 4, and `3·2 = 6 > 4`). -/
theorem rho_Sq2_cubed : rhoSq2 * rhoSq2 * rhoSq2 = 0 := by decide

/-- The top class `j₄` is annihilated by both squares (column 4 is zero) — the Poincaré-duality top. -/
theorem rho_top_killed : (∀ i, rhoSq1 i 4 = 0) ∧ (∀ i, rhoSq2 i 4 = 0) := by
  constructor <;> decide

/-- `J` is 5-dimensional over `𝔽₂`. -/
theorem joker_dim : Module.finrank F2 (Fin 5 → F2) = 5 := by simp

/-! ### The cyclic presentation `J = A(1)/(A(1)·Sq³)` (the minimal-resolution start)

`J` is cyclic on `j₀`, and `Sq³ = Sq¹Sq²` kills `j₀` (`Sq³·j₀ = Sq¹·(Sq²j₀) = Sq¹ j₂ = 0`). So
`A(1) ↠ J`, `1 ↦ j₀`, has kernel the left ideal `A(1)·Sq³` — the first step of the minimal free
resolution whose degree-4 Ext is the height-4 `h₀`-tower `= 16` (W4b: build the higher syzygies). -/

/-- `Sq³ = Sq¹Sq²` acts on `J` as `j₁ ↦ j₄` (and `0` elsewhere). -/
theorem rho_Sq3_eq :
    rhoSq1 * rhoSq2 = !![0,0,0,0,0; 0,0,0,0,0; 0,0,0,0,0; 0,0,0,0,0; 0,1,0,0,0] := by decide

/-- **`Sq³` kills the generator `j₀`** — the defining relation of `J = A(1)/(A(1)·Sq³)`. -/
theorem Sq3_kills_generator : ∀ i, (rhoSq1 * rhoSq2) i 0 = 0 := by decide

/-- **`j₀` generates `J`**: the operators `1, Sq¹, Sq², Sq²Sq¹, Sq³Sq¹` send `j₀` to the five basis
vectors `j₀,…,j₄` (their column-0 entries are the standard basis), so `A(1)·j₀ = J`. -/
theorem joker_cyclic :
    (1 : Matrix (Fin 5) (Fin 5) F2) 0 0 = 1 ∧ rhoSq1 1 0 = 1 ∧ rhoSq2 2 0 = 1 ∧
      (rhoSq2 * rhoSq1) 3 0 = 1 ∧ (rhoSq2 * rhoSq2) 4 0 = 1 := by decide

end SKEFTHawking.Joker
