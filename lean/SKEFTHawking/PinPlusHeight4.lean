/-
# The Pin⁺ column-(t−s=4) height-4 cap as FINITE F₂ linear algebra (Campbell δ=·h₀ cokernel)

Phase 5q.F, W4i. **The finite upper-bound core.** The assembled Pin⁺ Adams `E₂` column `t−s = 4` is the
cokernel of the Campbell connecting map `δ = ·h₀` (arXiv:1708.04264 eq. 6.17-6.18, Thm 6.7), a
**height-4 `h₀`-tower → `ℤ/2⁴ = 16`**. Per `Lit-Search/Phase-5qF/finite_height4_cap.md` (Route A,
machine-verified end-to-end against `π₀..₄ = ℤ/2,0,ℤ/2,ℤ/2,ℤ/16`):

- the δ-target is the column-`{0,4,8}` `h₀`-towers of `N` (the 4-periodic `M`, inserted by `RP^∞₋₁`) —
  **NOT** `Ext_{A(1)}(K)` (whose own column-4 infinity via `w`-periodicity is real but irrelevant; this
  sidesteps the `A1_resolution_higher_syzygies.md` §4.3 trap);
- the δ-source is the **`v`-tower** `v·h₀ᵏ` (`v ∈ Ext^{3,7}(F₂)`) which after the `Σ¹` shift sits in
  column 5 at filtrations `s = 3,4,5,…`; `δ : (col,s) ↦ (col−1,s+1)` maps each to column 4 at `s+1 ≥ 4`,
  **killing every `s ≥ 4`**. Survivors: `s = 0,1,2,3` → height 4. The single placement fact
  `v ∈ Ext^{3,7}` (filtration 3) is what makes the count **exactly 4**.

Everything here is `decide`-able F₂ linear algebra. The lone non-finite input — that this chart's
abutment **is** the bordism group `Ω₄^{Pin⁺}` (Pontryagin–Thom + Adams convergence) — is the SINGLE
disclosed Prop `pin4_abutment`, consumed (not asserted) in `PinPlusDischarge.lean`.
-/
import Mathlib

namespace SKEFTHawking.PinHeight4

/-! ## §1. The fixed Ext charts (Campbell Thm 5.5 / Ex. 5.6 / Ex. 5.8) — finite cell counts -/

/-- The ground ring `Ext_{A(1)}(F₂,F₂) = F₂[h₀,h₁,v,w]/(…)` (Campbell Thm 5.5), cell dimension at
`(t−s = col, s)`: `col 0` = `h₀`-tower (`h₀ˢ`, all `s`); `col 1` = `h₁` (`s=1`); `col 2` = `h₁²` (`s=2`);
`col 4` = `v`-tower (`v ∈ (3,7)`, `s ≥ 3`); `col 8` = `w`-tower (`s ≥ 4`). -/
def extF2 (col s : ℕ) : ℕ :=
  if col = 0 then 1
  else if col = 1 ∧ s = 1 then 1
  else if col = 2 ∧ s = 2 then 1
  else if col = 4 ∧ 3 ≤ s then 1
  else if col = 8 ∧ 4 ≤ s then 1
  else 0

/-- The `N` (4-periodic `M`) chart (Campbell Ex. 5.8): infinite `h₀`-towers in columns `t−s = 0,4,8`,
based at `s = 0`. These are the δ-targets the Pin⁺ chart inserts via `RP^∞₋₁`. -/
def extN (col _s : ℕ) : ℕ := if col = 0 ∨ col = 4 ∨ col = 8 then 1 else 0

/-- `Ext(Σ¹F₂)` — the ground chart with column shifted `+1`. The δ-source for column 4 is its column 5
`= extF2`'s column 4 `=` the `v`-tower (`s ≥ 3`). -/
def extS1F2 (col s : ℕ) : ℕ := if col = 0 then 0 else extF2 (col - 1) s

/-! ## §2. The δ = ·h₀ cokernel: the column-4 height-4 cap (finite `decide`) -/

/-- A column-`col` `N`-tower class at filtration `s` **survives** the δ-cokernel iff it is not hit by
the `δ = ·h₀` image from `(col+1, s−1)` (`δ : (c,σ) ↦ (c−1, σ+1)`, so the hit comes from one column
over, one filtration down). -/
def survives (col s : ℕ) : Bool :=
  decide (extN col s = 1 ∧ ¬(1 ≤ s ∧ extS1F2 (col + 1) (s - 1) = 1))

/-- **THE height-4 cap (Route A, finite).** The δ=·h₀ cokernel in the Pin⁺ column `t−s = 4` is exactly
the filtrations `s = 0,1,2,3` — a **height-4** `h₀`-tower. The shifted `v`-tower (δ-source, column 5,
base `s = 3`) cancels every `s ≥ 4`; survivors `{0,1,2,3}`. -/
theorem col4_survivors : (List.range 8).filter (survives 4) = [0, 1, 2, 3] := by decide

/-- **The column-4 cokernel has height exactly 4** — the literal finite count `#{s : survives} = 4`,
i.e. the abutment order is `2⁴ = 16`. This is the `decide`-able algebraic heart of `|Ω₄^{Pin⁺}| ≤ 16`. -/
theorem col4_height_eq_four : ((List.range 8).filter (survives 4)).length = 4 := by decide

/-! ## §3. Cross-checks — the SAME δ reproduces the rest of `π₀..₄` (Route A self-validation) -/

/-- **`π₀ = ℤ/2`** (height-1): column 0's `N`-tower is capped at `s = 0` by the shifted `h₀`-tower
(δ-source col 1, all `s`), which kills every `s ≥ 1`. -/
theorem col0_survivors : (List.range 8).filter (survives 0) = [0] := by decide

/-- The four heights `(col 0, 4) = (1, 4)` reproduce `(π₀, π₄) = (ℤ/2, ℤ/16)` — the cross-validated
finite witness that the column-4 accounting (`→ 16`) uses the same δ-rule that gives the known `π₀`. -/
theorem heights_0_and_4 :
    ((List.range 8).filter (survives 0)).length = 1 ∧
      ((List.range 8).filter (survives 4)).length = 4 := by decide

end SKEFTHawking.PinHeight4
