import SKEFTHawking.QuantumNetwork.DiamondNormDual
import SKEFTHawking.QuantumNetwork.NamedChannels

/-!
# Exact diamond distance for named channels via the optimal dual witness (Phase 6AG, Ask 1 exact)
-/

namespace SKEFTHawking.QuantumNetwork

open Matrix
open scoped ComplexOrder Matrix.Norms.L2Operator

/-- A `γ`-scaled real rank-one outer product `p q ↦ γ·s(p)·s(q)` is PSD for `γ ≥ 0`
(it is `A·Aᴴ` for the single column `A p _ = √γ·s(p)`). -/
theorem posSemidef_smul_outer {ι : Type*} [Fintype ι] [DecidableEq ι] {γ : ℝ} (hγ : 0 ≤ γ)
    (s : ι → ℝ) : (Matrix.of fun p q => (γ : ℂ) * (s p : ℂ) * (s q : ℂ)).PosSemidef := by
  set A : Matrix ι (Fin 1) ℂ := Matrix.of fun p _ => (Real.sqrt γ : ℂ) * (s p : ℂ) with hA
  have hAA : A * Aᴴ = Matrix.of fun p q => (γ : ℂ) * (s p : ℂ) * (s q : ℂ) := by
    ext p q
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, hA, Matrix.of_apply,
      Fin.sum_univ_one, Complex.star_def, map_mul, Complex.conj_ofReal]
    rw [show (Real.sqrt γ : ℂ) * (s p : ℂ) * ((Real.sqrt γ : ℂ) * (s q : ℂ))
        = ((Real.sqrt γ * Real.sqrt γ : ℝ) : ℂ) * (s p : ℂ) * (s q : ℂ) by push_cast; ring,
      Real.mul_self_sqrt hγ]
  rw [← hAA]; exact Matrix.posSemidef_self_mul_conjTranspose A

/-- The Bloch vector of the optimal dephasing witness: `e₀₀ − e₁₁`. -/
def sDeph : Fin 2 × Fin 2 → ℝ := fun p => if p = (0, 0) then 1 else if p = (1, 1) then -1 else 0

/-- The optimal dual witness for the dephasing channel difference: `γ·v vᵀ` with `v = e₀₀ − e₁₁`. -/
noncomputable def dephasingWitness (γ : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  Matrix.of fun p q => (γ : ℂ) * (sDeph p : ℂ) * (sDeph q : ℂ)

theorem dephasingWitness_posSemidef {γ : ℝ} (hγ : 0 ≤ γ) : (dephasingWitness γ).PosSemidef :=
  posSemidef_smul_outer hγ sDeph

/-- `ptrace₂ (dephasingWitness γ) = γ·1`. -/
theorem ptrace2_dephasingWitness (γ : ℝ) :
    ptrace2 (dephasingWitness γ) = (γ : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [ptrace2, dephasingWitness, sDeph, Matrix.smul_apply, Fin.sum_univ_two]

/-- `W − C ≥ 0`: the witness dominates the Choi difference in the Loewner order. `W − C = γ·v' v'ᵀ`
with `v' = e₀₀ + e₁₁`. -/
theorem dephasingWitness_sub_choi_posSemidef {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    (dephasingWitness γ - (choiMatrix (krausMap (dephasingKraus γ))
      - choiMatrix (krausMap (idKrausPad 1 2)))).PosSemidef := by
  rw [dephasing_choi_diff h0 h1]
  have heq : dephasingWitness γ - (γ : ℂ) • dephasingChoiBase
      = Matrix.of fun p q => (γ : ℂ)
          * ((if p = (0, 0) then 1 else if p = (1, 1) then 1 else 0 : ℝ) : ℂ)
          * ((if q = (0, 0) then 1 else if q = (1, 1) then 1 else 0 : ℝ) : ℂ) := by
    ext p q; obtain ⟨a, y⟩ := p; obtain ⟨b, y'⟩ := q
    fin_cases a <;> fin_cases y <;> fin_cases b <;> fin_cases y' <;>
      simp only [Matrix.sub_apply, dephasingWitness, Matrix.of_apply, sDeph, Matrix.smul_apply,
        smul_eq_mul, dephasingChoiBase, Prod.mk.injEq, Fin.isValue] <;>
      norm_num <;> ring
  rw [heq]
  exact posSemidef_smul_outer h0 (fun p => if p = (0, 0) then 1 else if p = (1, 1) then 1 else 0)

/-- **Exact dephasing diamond distance:** `diamondDist (dephasingKraus γ) (id) = γ` for
`0 ≤ γ ≤ 1`. Lower bound `diamondDist_dephasing_ge`; upper bound `diamondDist_le_dual_witness` at
the optimal witness `dephasingWitness γ` (with `‖ptrace₂ W‖ = ‖γ·1‖ = γ`). The two-sided envelope
is closed — the first exact diamond distance for a named channel, with no twirl machinery. -/
theorem diamondDist_dephasing_eq {γ : ℝ} (h0 : 0 ≤ γ) (h1 : γ ≤ 1) :
    diamondDist (dephasingKraus γ) (idKrausPad 1 2) = γ := by
  refine le_antisymm ?_ (diamondDist_dephasing_ge h0 h1)
  have hub := diamondDist_le_dual_witness (isKrausChannel_dephasingKraus h0 h1)
    (isKrausChannel_idKrausPad 1 2) (dephasingWitness_posSemidef h0)
    (dephasingWitness_sub_choi_posSemidef h0 h1)
  rwa [ptrace2_dephasingWitness, norm_smul, norm_one, mul_one, Complex.norm_real,
    Real.norm_of_nonneg h0] at hub

/-! ## Depolarizing channel: exact diamond distance `= p` -/

/-- Bloch indicators for the two off-diagonal `+2/3` eigenvectors `e₀₁, e₁₀`. -/
def s01Dep : Fin 2 × Fin 2 → ℝ := fun p => if p = (0, 1) then 1 else 0
def s10Dep : Fin 2 × Fin 2 → ℝ := fun p => if p = (1, 0) then 1 else 0

/-- The optimal dual witness for depolarizing: the positive part `C₊ = (2p/3)·P₊`, written as the
sum of the three rank-one projectors onto the `+2/3` eigenspace `{e₀₁, e₁₀, (e₀₀−e₁₁)/√2}`. -/
noncomputable def depolarizingWitness (p : ℝ) : Matrix (Fin 2 × Fin 2) (Fin 2 × Fin 2) ℂ :=
  (Matrix.of fun a b => ((2 * p / 3 : ℝ) : ℂ) * (s01Dep a : ℂ) * (s01Dep b : ℂ))
  + (Matrix.of fun a b => ((2 * p / 3 : ℝ) : ℂ) * (s10Dep a : ℂ) * (s10Dep b : ℂ))
  + (Matrix.of fun a b => ((p / 3 : ℝ) : ℂ) * (sDeph a : ℂ) * (sDeph b : ℂ))

theorem depolarizingWitness_posSemidef {p : ℝ} (hp : 0 ≤ p) : (depolarizingWitness p).PosSemidef := by
  have h23 : (0 : ℝ) ≤ 2 * p / 3 := by linarith
  have h3 : (0 : ℝ) ≤ p / 3 := by linarith
  exact ((posSemidef_smul_outer h23 s01Dep).add (posSemidef_smul_outer h23 s10Dep)).add
    (posSemidef_smul_outer h3 sDeph)

theorem ptrace2_depolarizingWitness (p : ℝ) :
    ptrace2 (depolarizingWitness p) = (p : ℂ) • (1 : Matrix (Fin 2) (Fin 2) ℂ) := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [ptrace2, depolarizingWitness, s01Dep, s10Dep, sDeph, Matrix.add_apply, Matrix.smul_apply,
      Fin.sum_univ_two] <;> ring

theorem depolarizingWitness_sub_choi_posSemidef {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    (depolarizingWitness p - (choiMatrix (krausMap (depolarizingKraus p))
      - choiMatrix (krausMap (idKrausPad 3 2)))).PosSemidef := by
  rw [depolarizing_choi_diff h0 h1]
  have heq : depolarizingWitness p - (p : ℂ) • depolarizingChoiBase
      = Matrix.of fun a b => (p : ℂ)
          * ((if a = (0, 0) then 1 else if a = (1, 1) then 1 else 0 : ℝ) : ℂ)
          * ((if b = (0, 0) then 1 else if b = (1, 1) then 1 else 0 : ℝ) : ℂ) := by
    ext q r; obtain ⟨a, y⟩ := q; obtain ⟨b, y'⟩ := r
    fin_cases a <;> fin_cases y <;> fin_cases b <;> fin_cases y' <;>
      simp only [depolarizingWitness, s01Dep, s10Dep, sDeph, depolarizingChoiBase, Matrix.sub_apply,
        Matrix.add_apply, Matrix.of_apply, Matrix.smul_apply, smul_eq_mul, Prod.mk.injEq,
        Fin.isValue] <;>
      norm_num <;> ring
  rw [heq]
  exact posSemidef_smul_outer h0 (fun p => if p = (0, 0) then 1 else if p = (1, 1) then 1 else 0)

/-- **Exact depolarizing diamond distance:** `diamondDist (depolarizingKraus p) (id) = p` for
`0 ≤ p ≤ 1`. Lower bound `diamondDist_depolarizing_ge`; upper bound at the positive-part dual
witness (`ptrace₂ W = p·1`). Two-sided exact value for the second named channel. -/
theorem diamondDist_depolarizing_eq {p : ℝ} (h0 : 0 ≤ p) (h1 : p ≤ 1) :
    diamondDist (depolarizingKraus p) (idKrausPad 3 2) = p := by
  refine le_antisymm ?_ (diamondDist_depolarizing_ge h0 h1)
  have hub := diamondDist_le_dual_witness (isKrausChannel_depolarizingKraus h0 h1)
    (isKrausChannel_idKrausPad 3 2) (depolarizingWitness_posSemidef h0)
    (depolarizingWitness_sub_choi_posSemidef h0 h1)
  rwa [ptrace2_depolarizingWitness, norm_smul, norm_one, mul_one, Complex.norm_real,
    Real.norm_of_nonneg h0] at hub

end SKEFTHawking.QuantumNetwork
