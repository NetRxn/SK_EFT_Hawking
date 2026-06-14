/-
# Machine-checked `Ext^s_{A(1)}(K, F₂)` dimensions for the ksp module `K` (s = 0,1,2)

Phase 5q.F, W4e. Mirrors `A1ExtSubstantive.lean` (the Spin/`F₂` route) for `K = ksp = Σ⁻⁴ko⟨4⟩`: the
dual coboundary maps `δˢ` of the `Hom_{A(1)}(P_•, F₂)`-dualized minimal resolution
(`KspResolution.lean`) are **augmentation-extracted** from the certified differentials and **vanish by
minimality** (`d₁_minimal`, `d₂_minimal`: the augmentation rows are zero), so
`dim Ext^s_{A(1)}(K, F₂) = rank P_s` — a genuine `Module.finrank` of an `F₂`-vector space (NOT a
`cols/8` arithmetic proxy):

  `Ext⁰(K) = 1`,   `Ext¹(K) = 2`,   `Ext²(K) = 3`   (= ranks of `P₀, P₁, P₂`).

## Honest scope (`Lit-Search/Phase-5qF/A1_resolution_higher_syzygies.md` §4.3)

These are the **total** `Ext^s` dimensions from `d₁, d₂` (the differentials built as full matrices, with
minimality proven). The degree-4 `h₀`-tower class sits *inside* `Ext²` (the `Σ⁶` generator of `P₂`,
internal degree `6 = 2 + 4`); the `t−s = 4` column is **4-periodic-INFINITE** (a class at every `s ≥ 1`
via the `w ∈ Ext^{4,12}` periodicity), so this is the machine-checked `E₂`-page **substrate** — NOT the
height-4 cap (that is the disclosed Campbell δ-truncation, `PinPlusExtBound.lean`, and is a topological
assembly statement, NOT an `Ext_{A(1)}(K)` property). `Ext³⁺` would need `d₃, d₄` as full matrices (only
their block chain properties `chain_d2_d3`/`chain_d3_d4` are built); the first three dimensions are the
directly-certified part. This is the algebraic-layer substantiation; the categorical `Ext` via Mathlib's
`ProjectiveResolution.isoExt` is the same deferred wave as `A1ExtSubstantive`'s.
-/
import Mathlib
import SKEFTHawking.KspResolution

namespace SKEFTHawking.KspExt

open Matrix SKEFTHawking.KspRes

/-! ## §1. Dual coboundary maps `δˢ` (augmentation-extracted from `d_{s+1}`)

`δˢ(k, j) = d_{s+1}(8j, 8k)`: the `8·_` indices land on the unit-component (augmentation) rows/columns
of each `A(1)`-block (`j` indexes `P_s` generators, `k` indexes `P_{s+1}` generators). -/

/-- `δ⁰ : Hom(P₀,F₂) = F₂¹ → Hom(P₁,F₂) = F₂²`, from `d₁`. -/
def delta0 : Matrix (Fin 2) (Fin 1) F2 :=
  Matrix.of fun k j => d1 ⟨8 * j.val, by have := j.isLt; omega⟩ ⟨8 * k.val, by have := k.isLt; omega⟩

/-- `δ¹ : F₂² → F₂³`, from `d₂`. -/
def delta1 : Matrix (Fin 3) (Fin 2) F2 :=
  Matrix.of fun k j => d2 ⟨8 * j.val, by have := j.isLt; omega⟩ ⟨8 * k.val, by have := k.isLt; omega⟩

/-! ## §2. The dual coboundaries vanish (minimality ⟹ `Ext = Hom`) -/

/-- `δ⁰ = 0` — minimality of `d₁` (its augmentation row vanishes), extracted from the certified matrix. -/
theorem delta0_eq_zero : delta0 = 0 := by decide

/-- `δ¹ = 0` — minimality of `d₂` (its augmentation rows vanish). -/
theorem delta1_eq_zero : delta1 = 0 := by decide

/-! ## §3. The `Ext^s(K)` dimensions as genuine `F₂`-vector-space finranks -/

/-- The `Hom`-space at degree `s` has `F₂`-dimension `r` (genuine `finrank`). -/
theorem hom_space_finrank (r : ℕ) : Module.finrank F2 (Fin r → F2) = r := by simp

/-- **`dim Ext⁰_{A(1)}(K, F₂) = 1`** — `H⁰ = ker δ⁰ = ⊤` (`δ⁰ = 0`), so `finrank = rank P₀ = 1`. -/
theorem kspExt0_dim : Module.finrank F2 (LinearMap.ker (mulVecLin delta0)) = 1 := by
  rw [show LinearMap.ker (mulVecLin delta0) = ⊤ by rw [delta0_eq_zero]; simp, finrank_top]
  exact hom_space_finrank 1

/-- **`dim Ext¹_{A(1)}(K, F₂) = 2`** — `H¹ = F₂²/im δ⁰`, `im δ⁰ = ⊥`, so `finrank = rank P₁ = 2`. -/
theorem kspExt1_dim :
    Module.finrank F2 ((Fin 2 → F2) ⧸ LinearMap.range (mulVecLin delta0)) = 2 := by
  rw [show LinearMap.range (mulVecLin delta0) = ⊥ by rw [delta0_eq_zero]; simp,
    (Submodule.quotEquivOfEqBot _ rfl).finrank_eq]
  exact hom_space_finrank 2

/-- **`dim Ext²_{A(1)}(K, F₂) = 3`** — `H² = F₂³/im δ¹`, `im δ¹ = ⊥`, so `finrank = rank P₂ = 3`. The
degree-4 `h₀`-tower class is one of the three (the `Σ⁶` generator of `P₂`, internal degree `6`). -/
theorem kspExt2_dim :
    Module.finrank F2 ((Fin 3 → F2) ⧸ LinearMap.range (mulVecLin delta1)) = 3 := by
  rw [show LinearMap.range (mulVecLin delta1) = ⊥ by rw [delta1_eq_zero]; simp,
    (Submodule.quotEquivOfEqBot _ rfl).finrank_eq]
  exact hom_space_finrank 3

/-- **The dual coboundaries vanish + the first three `Ext` dimensions** (`1, 2, 3 = rank P₀,P₁,P₂`) —
the machine-checked `Ext_{A(1)}(K, F₂)` `E₂`-page substrate (total `Ext^s`; the `t−s=4` `h₀`-tower
class sits inside `Ext²`; the full column is disclosed-infinite, capped only by the topological
δ-truncation). -/
theorem ksp_ext_dims :
    delta0 = 0 ∧ delta1 = 0 ∧
      Module.finrank F2 (LinearMap.ker (mulVecLin delta0)) = 1 ∧
        Module.finrank F2 ((Fin 2 → F2) ⧸ LinearMap.range (mulVecLin delta0)) = 2 ∧
          Module.finrank F2 ((Fin 3 → F2) ⧸ LinearMap.range (mulVecLin delta1)) = 3 :=
  ⟨delta0_eq_zero, delta1_eq_zero, kspExt0_dim, kspExt1_dim, kspExt2_dim⟩

end SKEFTHawking.KspExt
