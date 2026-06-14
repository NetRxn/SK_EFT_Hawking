import Mathlib

/-!
# The `M = A(1)//A(0)` module — the prototype `h₀`-tower (the δ-truncation substrate)

Phase 5q.F, W4g. `M = A(1)//A(0) = A(1)/(A(1)·Sq¹)` is the module whose `Ext_{A(1)}(M, F₂) = F₂[h₀]`
is the **single infinite `h₀`-tower** in column `t−s = 0` (Campbell [1708.04264] Ex. 5.6; BC18
Ex. 4.5.5, change-of-rings to `Ext_{A(0)}(F₂,F₂)`). It is the substrate of the **Pin⁺ δ-truncation**:
in the SES `0 → Σ¹F₂ → Σ¹H*(RP^∞₋₁) → M → 0` (Campbell eq. 6.17), the `t−s = 4` column of the assembled
Pin⁺ chart is a *shifted copy* of this `M`-tower, which the connecting map `δ = ·h₀` (eq. 6.18) caps at
height 4 → `ℤ/2⁴ = ℤ/16`. Building `M` is the first concrete brick of that δ-LES program.

`M` is 4-dimensional, basis `{m₀, m₂, m₃, m₅}` in degrees `0, 2, 3, 5`, Poincaré series `1+t²+t³+t⁵`.

**The `A(1)`-action (re-derived as a true quotient — `A1_resolution_higher_syzygies.md` §2/§7 item 1
corrects the earlier doc's false "`Sq¹ = 0` throughout"):**

  `Sq¹ : m₂ ↦ m₃`   (the edge the old module diagram missed; `Sq¹ m₀ = Sq¹ m₃ = Sq¹ m₅ = 0`)
  `Sq² : m₀ ↦ m₂,  m₃ ↦ m₅`   (`Sq² m₂ = Sq² m₅ = 0`)

verified below to satisfy the defining Adem relations `Sq¹² = 0` and `Sq²² = Sq¹Sq²Sq¹` (both act as `0`
on `M` — `Sq²²` since `Sq²m₂ = Sq²m₅ = 0`, and `Sq¹Sq²Sq¹` since `Sq¹m₀=0` kills the only entry). Matrices
act on column vectors: `M i j = 1` means `mⱼ ↦ mᵢ` (basis index `m₀=0, m₂=1, m₃=2, m₅=3`).
-/

namespace SKEFTHawking.MMod

abbrev F2 := ZMod 2

/-- The action of `Sq¹` on `M`: `m₂ ↦ m₃` (the edge the old `A(1)//A(0)` diagram missed). -/
def rhoSq1 : Matrix (Fin 4) (Fin 4) F2 :=
  !![0, 0, 0, 0;
     0, 0, 0, 0;
     0, 1, 0, 0;
     0, 0, 0, 0]

/-- The action of `Sq²` on `M`: `m₀ ↦ m₂`, `m₃ ↦ m₅`. -/
def rhoSq2 : Matrix (Fin 4) (Fin 4) F2 :=
  !![0, 0, 0, 0;
     1, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 1, 0]

/-- **Adem `Sq¹² = 0`** on `M`. -/
theorem rho_Sq1_sq : rhoSq1 * rhoSq1 = 0 := by decide

/-- **Adem `Sq²² = Sq¹Sq²Sq¹`** on `M` — both act as `0` (`Sq²m₂ = Sq²m₅ = 0`, and `Sq¹m₀ = 0` kills the
chain), confirming `(rhoSq1, rhoSq2)` extend to a genuine `A(1)`-module structure on `M`. -/
theorem rho_Sq2_sq : rhoSq2 * rhoSq2 = rhoSq1 * rhoSq2 * rhoSq1 := by decide

/-- `Sq¹` kills the generator `m₀` (the relation `A(1)·Sq¹` defining `M = A(1)/(A(1)Sq¹)`). -/
theorem Sq1_kills_generator : ∀ i, rhoSq1 i 0 = 0 := by decide

/-- **`m₀` generates `M`**: `1, Sq², Sq¹Sq², Sq²Sq¹Sq²` send `m₀` to `m₀, m₂, m₃, m₅` — so `A(1)·m₀ = M`,
the cyclic presentation `M = A(1)/(A(1)Sq¹)`. (`Sq²Sq¹Sq² = Sq⁵+Sq⁴Sq¹` sends `m₀ ↦ m₅`.) -/
theorem m_cyclic :
    (1 : Matrix (Fin 4) (Fin 4) F2) 0 0 = 1 ∧ rhoSq2 1 0 = 1 ∧ (rhoSq1 * rhoSq2) 2 0 = 1 ∧
      (rhoSq2 * rhoSq1 * rhoSq2) 3 0 = 1 := by decide

end SKEFTHawking.MMod
