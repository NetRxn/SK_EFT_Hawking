import Mathlib
import SKEFTHawking.TopologicalBand.PrincipalBranch
import SKEFTHawking.TopologicalBand.FiniteTorus
import SKEFTHawking.TopologicalBand.FHSLatticeGauge

/-!
# D11-FHS Q2 — non-vacuity witness and negative fixture

Two exact, finite/data-level computations that pin down the `latticeChern` carrier:

* `latticeChern_Uwit` — a certified **nonzero** example: a single non-trivial (`-1`) link on the
  `2 × 2` torus carries `latticeChern = 1` (a "flux quantum"). This proves the invariant is not
  identically zero.
* `latticeChern_trivial` — the **negative fixture**: the trivial (all-`1`) link field has
  `latticeChern = 0`.

Both values are proved by finite algebra (no floating-point / `native_decide`). The witness sits at
the branch-cut endpoint (each nonzero plaquette phase is exactly `π`), which is fine for the exact
**lattice** integrality here; it is *not* a claim about any continuum first Chern class.
-/

open Complex Real
open scoped BigOperators

namespace SKEFTHawking.TopologicalBand

/-! ### Branch-index values (from the `toIocDiv` uniqueness characterization) -/

theorem branchIndex_zero : branchIndex 0 = 0 := by
  rw [branchIndex, toIocDiv_eq_iff, Set.mem_Ioc]
  simp only [zero_zsmul, sub_zero]
  exact ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩

theorem branchIndex_pi : branchIndex Real.pi = 0 := by
  rw [branchIndex, toIocDiv_eq_iff, Set.mem_Ioc]
  simp only [zero_zsmul, sub_zero]
  exact ⟨by linarith [Real.pi_pos], by linarith⟩

theorem branchIndex_neg_pi : branchIndex (-Real.pi) = -1 := by
  rw [branchIndex, toIocDiv_eq_iff, Set.mem_Ioc]
  simp only [neg_one_zsmul, sub_neg_eq_add]
  exact ⟨by linarith [Real.pi_pos], le_refl _⟩

/-! ### The `-1` link phase -/

/-- The `Circle` element `-1` (`= exp(iπ)`), used as the single non-trivial link. -/
noncomputable def negC : Circle := Circle.exp Real.pi

theorem negC_coe : (negC : ℂ) = -1 := by
  rw [negC, Circle.coe_exp, Complex.exp_pi_mul_I]

theorem arg_negC : Complex.arg (negC : ℂ) = Real.pi := by
  rw [negC_coe, Complex.arg_neg_one]

/-! ### The nonzero-flux witness on the `2 × 2` torus -/

/-- The witness link field: `U₀` carries a `-1` phase on the single link at vertex `(0,1)`; every
other link is trivial. -/
noncomputable def Uwit : LinkField 2 2 :=
  fun μ k => if (μ = 0 ∧ k = ((0 : ZMod 2), (1 : ZMod 2))) then negC else 1

theorem linkArg_Uwit (μ : Fin 2) (k : Torus 2 2) :
    linkArg 2 2 Uwit μ k = if (μ = 0 ∧ k = ((0 : ZMod 2), (1 : ZMod 2))) then Real.pi else 0 := by
  unfold linkArg Uwit
  split_ifs with h
  · exact arg_negC
  · rw [Circle.coe_one, Complex.arg_one]

/-- The plaquette branch corrections of the witness, computed vertex-by-vertex on the `2 × 2` grid:
`-1` at `(0,0)` and `0` elsewhere. -/
theorem plaquetteBranch_Uwit (k : Torus 2 2) :
    plaquetteBranch 2 2 Uwit k = if k = ((0 : ZMod 2), (0 : ZMod 2)) then -1 else 0 := by
  unfold plaquetteBranch rawCurl
  rw [linkArg_Uwit, linkArg_Uwit, linkArg_Uwit, linkArg_Uwit]
  simp only [shift_apply, shiftVec, Fin.reduceEq, true_and, false_and, if_false,
    add_zero, sub_zero]
  fin_cases k <;>
  first
    | (rw [if_neg (by decide), if_pos (by decide), if_pos (by decide), zero_sub]
       exact branchIndex_neg_pi)
    | (rw [if_pos (by decide), if_neg (by decide), if_neg (by decide), sub_zero]
       exact branchIndex_pi)
    | (rw [if_neg (by decide), if_neg (by decide), if_neg (by decide), sub_zero]
       exact branchIndex_zero)

/-- **Non-vacuity witness (C = 1).** The `2 × 2` single-`-1`-link configuration carries lattice
Chern number `1` — a certified nonzero "flux quantum", proving `latticeChern` is not identically
zero. -/
theorem latticeChern_Uwit : latticeChern 2 2 Uwit = 1 := by
  unfold latticeChern
  rw [Finset.sum_congr rfl (fun k _ => plaquetteBranch_Uwit k)]
  decide

/-! ### Negative fixture -/

/-- **Negative fixture (C = 0).** The trivial (all-`1`) link field has lattice Chern number `0`. -/
theorem latticeChern_trivial : latticeChern 2 2 (fun _ _ => (1 : Circle)) = 0 := by
  have h : ∀ k, plaquetteBranch 2 2 (fun _ _ => (1 : Circle)) k = 0 := by
    intro k
    unfold plaquetteBranch rawCurl linkArg
    simp only [Circle.coe_one, Complex.arg_one]
    rw [show (0 : ℝ) + 0 - 0 - 0 = 0 by ring]
    exact branchIndex_zero
  unfold latticeChern
  rw [Finset.sum_congr rfl (fun k _ => h k)]
  simp

end SKEFTHawking.TopologicalBand
